/*******************************************************************************
Copyright (C) 2016 OLogN Technologies AG

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License version 2 as
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*******************************************************************************/

#include "debug.h"

#include "front-back/idl_tree.h"
#include "front-back/idl_tree_serializer.h"

using namespace std;


class DbgDumpWalker
{
public:
    FILE* os;
    bool printLocation;
    size_t offset;
    vector<string> offsets;

    DbgDumpWalker(FILE* os, bool printLocation) : os(os), printLocation(printLocation), offset(0)
    {
        offsets.push_back("");
    }

    void dbgDumpRoot(const Root* node) {
        dbgWrite("Root");
        ++offset;
        for (const auto& each : node->typedefs)
            dbgDumpTypedef(each);
        for (const auto& it : node->structures)
            dbgDumpStructure(it.get());

        --offset;
    }

private:
    static string dbgAttributesToString(const map<string, Variant>& v) {
        string tags = "( ";
        for (auto it = v.begin(); it != v.end(); ++it) {
            if (it != v.begin())
                tags += " , ";
            tags += fmt::format("{} = {}", it->first, dbgVariantToString(it->second));
        }
        tags += " )";
        return tags;
    }


    static string dbgVariantToString(const Variant& v) {

        switch (v.kind) {
        case Variant::NUMBER:
            return fmt::format("( kind=NUMBER numberValue={} )", v.numberValue);
            break;
        case Variant::STRING:
            return fmt::format("( kind=STRING stringValue={} )", v.stringValue);
            break;
        default:
            return string("( *** INVALID *** )");
        }

    }

    static string dbgCharacterSetToString(const CharacterSet& cs) {

        string result;
        for (auto it = cs.ranges.begin(); it != cs.ranges.end(); ++it) {
            if (it != cs.ranges.begin())
                result += " , ";
            if (it->from == it->to)
                result += fmt::format("{:x}", it->from);
            else
                result += fmt::format("{:x} - {:x}", it->from, it->to);
        }
        return result;
    }

    static string dbgTypeToString(const DataType& dataType) {

        switch (dataType.kind) {
        case DataType::INTEGER:

            return fmt::format("INTEGER{} {} , {} {}",
                dataType.lowLimit.inclusive ? '[' : '(', dataType.lowLimit.value,
                dataType.highLimit.value, dataType.highLimit.inclusive ? ']' : ')');
        case DataType::FIXED_POINT:

            return fmt::format("FIXED-POINT{} {} , {} , {} {}",
                dataType.lowLimit.inclusive ? '[' : '(', dataType.lowLimit.value,
                dataType.fixedPrecision,
                dataType.highLimit.value, dataType.highLimit.inclusive ? ']' : ')');
        case DataType::FLOATING_POINT:

            return fmt::format("FLOATING-POINT( {} , {} )",
                dataType.floatingSignificandBits, dataType.floatingExponentBits);
        case DataType::CHARACTER:

            return fmt::format("CHARACTER{{ {} }}",
                dbgCharacterSetToString(dataType.characterSet));
        case DataType::CHARACTER_STRING:

            return fmt::format("CHARACTER-STRING{{ {} }}[ {} , {} ]",
                dbgCharacterSetToString(dataType.characterSet),
                dataType.stringMinSize, dataType.stringMaxSize);
        case DataType::BIT_STRING:

            return fmt::format("BIT-STRING[ {} , {} ]",
                dataType.stringMinSize, dataType.stringMaxSize);
        case DataType::ENUM:
        {
            string enumValues;
            for (auto it = dataType.enumValues.begin(); it != dataType.enumValues.end(); ++it) {
                if (it != dataType.enumValues.begin())
                    enumValues += " , ";
                enumValues += fmt::format("{} = {}", it->first, it->second);
            }

            return fmt::format("ENUM {} {{ {} }}", dataType.name, enumValues);
        }
        case DataType::NAMED_TYPE:
            return dataType.name;
        case DataType::SEQUENCE:
        {
            string arg = dataType.paramType ? dbgTypeToString(*dataType.paramType) : "( *** INVALID *** )";
            if (dataType.name.empty())
                return fmt::format("SEQUENCE< {} >", arg);
            else
                return fmt::format("SEQUENCE {} < {} >", dataType.name, arg);
        }
        case DataType::DICTIONARY:
        {
            string arg0 = dataType.keyType ? dbgTypeToString(*dataType.keyType) : "*** INVALID ***";
            string arg1 = dataType.paramType ? dbgTypeToString(*dataType.paramType) : "*** INVALID ***";
            return fmt::format("DICTIONARY< {} , {} >", arg0, arg1);
        }
        case DataType::ENCODING_SPECIFIC:
        {
            string attrs = dbgAttributesToString(dataType.encodingAttrs);
            return fmt::format("ENCODING_SPECIFIC {} {}",
                               dataType.encodingName, attrs);
        }
        case DataType::MAPPING_SPECIFIC:
        {
            string attrs = dbgAttributesToString(dataType.mappingAttrs);
            return fmt::format("MAPPING_SPECIFIC {} {}",
                               dataType.mappingName, attrs);
        }
        default:
            return string("*** INVALID ***");
        }
    }

    void dbgDumpTypedef(const Typedef& node) {

        string typeStr = dbgTypeToString(node.type);

        dbgWriteWithLocation(node.location,
            fmt::format("TYPEDEF type={} name={}",
                typeStr, node.name));
    }

    void dbgDumpStructure(const Structure* node) {

        string kind = "";
        switch (node->declType) {
        case Structure::IDL:
            kind = "IDL";
            break;
        case Structure::MAPPING:
            kind = "MAPPING";
            break;
        case Structure::ENCODING:
            kind = "ENCODING";
            break;
        default:
            kind = "*** INVALID ***";
        }

        string type = "";
        switch (node->type) {
        case Structure::STRUCT:
            type = "STRUCT";
            break;
        case Structure::RPC:
            type = "RPC";
            break;
        case Structure::DISCRIMINATED_UNION:
            type = "DISCRIMINATED_UNION";
            break;
        default:
            type = "*** INVALID ***";
        }

        string tags = dbgAttributesToString(node->encodingSpecifics.attrs);
        dbgWriteWithLocation(node->location,
                             fmt::format("Structure kind={} type={} name={} inherit={} encAttrs={} discr={}",
                                         kind, type, node->name, node->inheritedFrom, tags, node->discriminant));

        ++offset;
        for (auto& it : node->members) {
            const DataMember* data = static_cast<const DataMember*>(it.get());
            dbgDumpDataMember(data);
        }
        --offset;
    }


    void dbgDumpDataMember(const DataMember* node) {

        string attr;
        if (node->extendTo)
            attr += "extendTo=true";
        if (node->defaultValue.kind != Variant::NONE)
            attr += fmt::format("defaultValue='{}'", dbgVariantToString(node->defaultValue));
        if (!node->whenDiscriminant.empty()) {
            attr += "whenDiscriminant='";
            for (auto it = node->whenDiscriminant.begin(); it != node->whenDiscriminant.end(); ++it) {
                if (it != node->whenDiscriminant.begin())
                    attr += ",";
                attr += *it;
            }
            attr += "'";
        }

        string typeStr = dbgTypeToString(node->type);
        dbgWriteWithLocation(node->location, fmt::format("DataMember name='{}' {} type='{}'", node->name, attr, typeStr));
    }

    static string dbgEncodingToString(const EncodingSpecifics& encoding) {

        return fmt::format("encName={}, encAttrs={}", encoding.name, dbgAttributesToString(encoding.attrs));
    }


    void dbgWrite(const string& text) {
        string offset = getOffset();
        fprintf(os, "%s%s\n", offset.c_str(), text.c_str());
    }

    void dbgWriteWithLocation(const Location& location, const string& text) {
        if (printLocation) {
            string offset = getOffset();
            string loc = locationToString(location);
            fprintf(os, "%s%s %s\n", offset.c_str(), text.c_str(), loc.c_str());
        }
        else
            dbgWrite(text);
    }

    void addOffset()
    {
        string r;
        for (size_t i = 0; i < offsets.size() - 1; ++i) {
            r.append("| ");
        }
        r.append("|-");
        offsets.push_back(r);
    }

    const string& getOffset()
    {
        while (offsets.size() <= offset)
            addOffset();

        return offsets[offset];
    }
};

void dbgDumpTree(const Root* root, bool printLocation, FILE* os)
{
    if (root) {
        DbgDumpWalker walker(os, printLocation);
        walker.dbgDumpRoot(root);
    }
}


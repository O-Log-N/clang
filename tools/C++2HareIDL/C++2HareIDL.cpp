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

#include <sstream>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/TargetSelect.h"

#include "front-back/idl_tree.h"
#include "front-back/idl_tree_serializer.h"
#include "front-back/raiistdiofile.h"
#include "debug.h"


using namespace clang;
using namespace clang::tooling;
using namespace llvm;
using namespace std;

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
static cl::OptionCategory myToolCategory("C++2HareIDL options");

// CommonOptionsParser declares HelpMessage with a description of the common
// command-line options related to the compilation database and input files.
// It's nice to have this help message in all tools.
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

// A help message for this specific tool can be added afterwards.
static cl::extrahelp MoreHelp("\nMore help text...");

//static cl::opt<bool> Help("h", cl::desc("Alias for -help"), cl::Hidden);

static cl::list<std::string>
FindClasses("find-class", cl::desc("Name a class to be processed.\n"
                             "Multiple classes can be processed by specifying\n"
                             "several -class-name arguments.\n"),
           cl::cat(myToolCategory));

static cl::opt<bool>
FindByAttribute("find-by-attribute", cl::desc("Process classes with attribute [[hare::mapping]].\n"),
         cl::cat(myToolCategory));

static cl::opt<std::string>
OutputFilename("o", cl::desc("Output filename"), cl::value_desc("filename"), cl::cat(myToolCategory));

static cl::opt<bool>
Print("print", cl::desc("Generate an idl tree and print to cout.\n"),
    cl::cat(myToolCategory));

static cl::opt<bool>
Serialize("serialize", cl::desc("Generate an idl tree and serialize it.\n"),
    cl::cat(myToolCategory));

static cl::opt<bool>
Dump("dump", cl::desc("Generate an idl tree and dump it.\n"),
    cl::cat(myToolCategory));

static cl::opt<bool>
Idl("idl", cl::desc("Write an idl tree.\n"),
    cl::cat(myToolCategory));

class FindNamedClassVisitor
    : public RecursiveASTVisitor<FindNamedClassVisitor> {
private:
    ASTContext *context;
    map<const Type*, string> typeMapping;
    map<const ClassTemplateDecl*, string> sequenceType;
    map<const ClassTemplateDecl*, string> dictionaryType;
    vector<pair<const CXXRecordDecl *, string> > toBeMapped; //need to keep order?
    Root root;
    ostringstream os;
    PrintingPolicy policy;


public:
    explicit FindNamedClassVisitor(ASTContext *context)
        : context(context), policy(context->getLangOpts()) {
        policy.SuppressTagKeyword = true;
    }

    void SerializeTree(FILE* ostream) {
        doMapping();

        if (Dump) {
            dbgDumpTree(&root, false, ostream ? ostream : stdout);
        }
        else if (Idl){
            string buffer = os.str();
            fwrite(buffer.c_str(), buffer.size(), 1, ostream ? ostream : stdout);
        }
        else if (Print) {
            printRoot(root);
        }
        else if (ostream) {
            OStream OS(ostream);
            serializeRoot(root, OS);
        }
        else {
            printRoot(root);
        }
    }

    //bool VisitTypeAliasDecl(TypeAliasDecl* declaration) {

    //    StringRef name = declaration->getName();
    //    if (name.substr(0, 14) == "hare_sequence_") {
    //        QualType qt = declaration->getUnderlyingType();
    //        const Type* t = qt.getCanonicalType().getTypePtrOrNull();
    //        if (t) {
    //            const TemplateSpecializationType* ts = t->getAs<TemplateSpecializationType>();
    //            QualType qt2 = ts->desugar();
    //            const Type* t2 = qt2.getCanonicalType().getTypePtrOrNull();
    //            if (t2) {
    //                t->dump();
    //                t2->dump();

    //            }
    //        }
    //    }

    //    return true;
    //}

    bool VisitTypedefNameDecl(TypedefNameDecl* declaration) {

        StringRef name = declaration->getName();
        if (name.substr(0, 14) == "hare_sequence_") {
            string n = declaration->getDeclName().getAsString().substr(14);
            QualType qt = declaration->getUnderlyingType();
            const Type* t = qt.getCanonicalType().getTypePtrOrNull();
            if (t && t->isRecordType()) {
                const RecordType *rt = t->getAs<RecordType>();
                RecordDecl* rDecl = rt->getDecl();
                ClassTemplateSpecializationDecl* ctsDecl = dyn_cast<ClassTemplateSpecializationDecl>(rDecl);
                if (ctsDecl) {
                    ClassTemplateDecl* ctDecl = ctsDecl->getSpecializedTemplate();
                    sequenceType.emplace(ctDecl, n);
                }
            }
        }
        else if (name.substr(0, 16) == "hare_dictionary_") {
            string n = declaration->getDeclName().getAsString().substr(16);
            QualType qt = declaration->getUnderlyingType();
            const Type* t = qt.getCanonicalType().getTypePtrOrNull();
            if (t && t->isRecordType()) {
                const RecordType *rt = t->getAs<RecordType>();
                RecordDecl* rDecl = rt->getDecl();
                ClassTemplateSpecializationDecl* ctsDecl = dyn_cast<ClassTemplateSpecializationDecl>(rDecl);
                if (ctsDecl) {
                    ClassTemplateDecl* ctDecl = ctsDecl->getSpecializedTemplate();
                    dictionaryType.emplace(ctDecl, n);
                }
            }
        }
        else if (name.substr(0, 5) == "hare_") {
            string n = declaration->getDeclName().getAsString().substr(5);
            QualType qt = declaration->getUnderlyingType();
            const Type* t = qt.getCanonicalType().getTypePtrOrNull();
            if (t) {
                typeMapping[t] = n;
            }
        }
        else {
            auto it = find(FindClasses.begin(), FindClasses.end(), name.str());
            if (it != FindClasses.end()) {

                QualType qt = declaration->getUnderlyingType();
                const Type* t = qt.getCanonicalType().getTypePtrOrNull();
                if (t) {
                    CXXRecordDecl * d = t->getAsCXXRecordDecl();
                    if (d) {
                        toBeMapped.emplace_back(d, name);
                    }
                }
            }
        }

        return true;
    }

    bool VisitCXXRecordDecl(CXXRecordDecl *declaration) {

        StringRef name = declaration->getName();

        auto it = find(FindClasses.begin(), FindClasses.end(), name.str());
        if (it != FindClasses.end()) {
            addMapping(declaration, name);
        }
        else if (FindByAttribute && declaration->hasAttr<HareMappingAttr>()) {
            addMapping(declaration, name);
        }
        else if (declaration->hasAttr<AnnotateAttr>()) {
            AnnotateAttr* at = declaration->getAttr<AnnotateAttr>();
            StringRef t = at->getAnnotation();
            if (t == "hare::mapping") {
                addMapping(declaration, name);
            }
        }

        return true;
    }

private:
    void doMapping() {
        for (auto each : toBeMapped)
            addMapping(each.first, each.second);
    }

    void addMapping(const CXXRecordDecl *declaration, const string& name) {
        if (Idl)
            addMappingIdl(declaration, name);
        else
            addMappingTree(declaration, name);
    }

    void addMappingTree(const CXXRecordDecl *declaration, const string& name) {

//        declaration->dump();
        unique_ptr<Structure> str(new Structure);

        str->name = name;
        str->declType = Structure::MAPPING;
        str->type = Structure::STRUCT;

        str->location = getLocation(declaration->getLocStart());

        auto bases = declaration->bases();
//        size_t sz = distance(bases.begin(), bases.end());

        if (bases.begin() != bases.end()) {
            QualType inherit = bases.begin()->getType();
            str->inheritedFrom = inherit.getCanonicalType().getAsString(policy);
        }

        string mappingArgs;
        if (declaration->hasAttr<HareMappingAttr>()) {
            HareMappingAttr* at = declaration->getAttr<HareMappingAttr>();
            StringRef ma = at->getArgument();
            if (!ma.empty()) {
                Variant val;
                val.kind = Variant::STRING;
                val.stringValue = ma.str();
                str->encodingSpecifics.attrs["Attribute"] = val;
            }
        }

        RecordDecl::field_range r = declaration->fields();
        for (auto it = r.begin(); it != r.end(); ++it) {

            unique_ptr<DataMember> dm(new DataMember);
            FieldDecl* current = *it;

            dm->location = getLocation(current->getLocStart());

            dm->name = current->getDeclName().getAsString();
            
            bool flag = processType(dm->type, current->getType());
            if(flag)
                str->members.emplace_back(dm.release());
            /*
            if (current->hasAttr<HareEncodeAsAttr>()) {
                HareEncodeAsAttr* at = current->getAttr<HareEncodeAsAttr>();
                llvm::outs() << t.getAsString() << " " << n << " " << at->getEncoding().str() << ";\n";
            }
            else if (current->hasAttr<AnnotateAttr>()) {
                AnnotateAttr* at = current->getAttr<AnnotateAttr>();
                StringRef anot = at->getAnnotation();
                if (anot.startswith("hare::encode_as(")) {
                    llvm::outs() << t.getAsString() << " " << n << " " << anot << ";\n";
                }
            }
            else
*/
        }
        root.structures.push_back(std::move(str));
    }

    bool processType(DataType& dt, QualType qt) const {

        if (qt.hasQualifiers())
            qt = qt.getUnqualifiedType();

        if (!qt.isCanonical())
            qt = qt.getCanonicalType();


        string typeName = qt.getAsString(policy);
        const Type* t = qt.getTypePtrOrNull();
        
        auto mapIt = typeMapping.find(t);
        if (mapIt != typeMapping.end()) {
            dt.kind = DataType::MAPPING_SPECIFIC;
            dt.mappingName = mapIt->second;
            return true;
        }
        else if (t->isBuiltinType()) {
            dt.kind = DataType::MAPPING_SPECIFIC;
            dt.mappingName = typeName;
            return true;
        }
        else if (t->isEnumeralType()) {

            dt.kind = DataType::ENUM;
            
            EnumDecl* ed = t->getAs<EnumType>()->getDecl();
            dt.name = ed->getName();

            auto r = ed->enumerators();
            if (r.begin() != r.end()) {
                for (auto it = r.begin(); it != r.end(); ++it) {

                    const APSInt& val = it->getInitVal();
                    typedef decltype(dt.enumValues)::value_type::second_type st;
                    if (val >= numeric_limits<st>::min() && val <= numeric_limits<st>::max()) {
                        const string& valName = it->getName();
                        dt.enumValues[valName] = static_cast<st>(val.getExtValue());
                    }
                    else {
                        errs() << "Enumeral value out of range " << val << "\n";
                        return false;
                    }
                }
            }
            return true;
        }
        else if (t->isRecordType()) {
            const RecordType *rt = t->getAs<RecordType>();
            RecordDecl* decl = rt->getDecl();

            ClassTemplateSpecializationDecl* tDecl = dyn_cast<ClassTemplateSpecializationDecl>(decl);
            if (tDecl) {
                ClassTemplateDecl* ctDecl = tDecl->getSpecializedTemplate();
                const TemplateArgumentList& args = tDecl->getTemplateInstantiationArgs();

                auto it = sequenceType.find(ctDecl);
                if (it != sequenceType.end()) {

                    dt.kind = DataType::SEQUENCE;
                    dt.name = it->second;
                    dt.mappingName = it->second;

                    dt.paramType.reset(new DataType());
                    if (!processType(*dt.paramType, args.get(0).getAsType()))
                        return false;

                    //Workaround to match previous behaviour
                    if (dt.paramType->kind == DataType::MAPPING_SPECIFIC) {
                        errs() << "Fixig paramType->kind\n";
                        dt.paramType->kind = DataType::NAMED_TYPE;
                        dt.paramType->name = dt.paramType->mappingName;
                    }

                    return true;
                }

                auto it2 = dictionaryType.find(ctDecl);
                if (it2 != dictionaryType.end()){

                    dt.kind = DataType::DICTIONARY;
                    dt.name = it2->second;
                    dt.mappingName = it2->second;

                    dt.keyType.reset(new DataType());
                    if (!processType(*dt.keyType, args.get(0).getAsType()))
                        return false;

                    dt.paramType.reset(new DataType());
                    if (!processType(*dt.paramType, args.get(1).getAsType()))
                        return false;

                    //Workaround to match previous behaviour
                    if (dt.keyType->kind == DataType::MAPPING_SPECIFIC) {
                        errs() << "Fixig keyType->kind\n";
                        dt.keyType->kind = DataType::NAMED_TYPE;
                        dt.keyType->name = dt.keyType->mappingName;
                    }

                    if (dt.paramType->kind == DataType::MAPPING_SPECIFIC) {
                        errs() << "Fixig paramType->kind\n";
                        dt.paramType->kind = DataType::NAMED_TYPE;
                        dt.paramType->name = dt.paramType->mappingName;
                    }

                    return true;
                }
            }
            else {
                dt.kind = DataType::MAPPING_SPECIFIC;
                dt.mappingName = typeName;

//                dt.mappingAttrs.emplace("className", Variant(typeName));

                return true;
            }
        }
        else if (t->isPointerType()) {
            errs() << "Unsupported pointer type " << typeName << "\n";
            return false;
        }

        errs() << "Unsupported type " << typeName << "\n";
        return false;
    }

    Location getLocation(const SourceLocation& loc) const {
        Location location;

        FullSourceLoc fullLoc = context->getFullLoc(loc);
        location.lineNumber = fullLoc.getSpellingLineNumber();
        location.fileName = fullLoc.getManager().getFilename(fullLoc).str();

        return location;
    }

    void addMappingIdl(const CXXRecordDecl *declaration, const string& name) {

        //        declaration->dump();

        FullSourceLoc fullLocation = context->getFullLoc(declaration->getLocStart());
        string fn = fullLocation.getManager().getFilename(fullLocation).str();
        unsigned int line = fullLocation.getSpellingLineNumber();
        os << "#line " << line << " \"" << fn << "\";\n";

        string mappingArgs;
        if (declaration->hasAttr<HareMappingAttr>()) {
            HareMappingAttr* at = declaration->getAttr<HareMappingAttr>();
            StringRef ma = at->getArgument();
            if (!ma.empty()) {
                mappingArgs += ", Attribute=\"";
                mappingArgs += ma;
                mappingArgs += "\" ";
            }
        }

        os << "MAPPING( FrontEnd=\"1.0\"" << mappingArgs << ") PUBLISHABLE-STRUCT " << name << " {\n";
        ++line;

        RecordDecl::field_range r = declaration->fields();
        for (auto it = r.begin(); it != r.end(); ++it) {
            FieldDecl* current = *it;
            string n = current->getDeclName().getAsString();
            //                string t = current->getType().getCanonicalType().getAsString();
            QualType qt = current->getType();

            if (qt.hasQualifiers()) {
                //TODO report error?
                qt = qt.getUnqualifiedType();
            }

            const Type* t = qt.getCanonicalType().getTypePtrOrNull();
            auto mapIt = typeMapping.find(t);
            string typeName = mapIt != typeMapping.end() ? mapIt->second : qt.getAsString(policy);

            FullSourceLoc currentLoc = context->getFullLoc(current->getLocStart());
            fixLineNumber(fn, line, currentLoc);

            //assert(t);
            if (t->isPointerType()) {
                ; //ignore
            }
            else if (t->isEnumeralType()) {
                size_t l = typeName.find_last_of(':');
                if (l != string::npos)
                    typeName = typeName.substr(l + 1);
                os << "enum " << typeName << " ";
                EnumDecl* ed = t->getAs<EnumType>()->getDecl();
                auto r = ed->enumerators();
                if (r.begin() != r.end()) {
                    os << "{";
                    for (auto it = r.begin(); it != r.end(); ++it) {
                        if (it != r.begin())
                            os << ",";

                        os << "IDENTIFIER( \"" << it->getName().str() << "\" ) = ";
                        os << it->getInitVal().toString(10);
                    }
                    os << "} ";
                }
            }
            else
                os << typeName << " ";


            os << current->getDeclName().getAsString() << ";\n";
            ++line;
            /*
            if (current->hasAttr<HareEncodeAsAttr>()) {
            HareEncodeAsAttr* at = current->getAttr<HareEncodeAsAttr>();
            llvm::outs() << t.getAsString() << " " << n << " " << at->getEncoding().str() << ";\n";
            }
            else if (current->hasAttr<AnnotateAttr>()) {
            AnnotateAttr* at = current->getAttr<AnnotateAttr>();
            StringRef anot = at->getAnnotation();
            if (anot.startswith("hare::encode_as(")) {
            llvm::outs() << t.getAsString() << " " << n << " " << anot << ";\n";
            }
            }
            else
            */
        }
        os << "};\n\n";
    }

    void fixLineNumber(string& fileName, unsigned int& line, FullSourceLoc location) {
        unsigned int currentLine = location.getSpellingLineNumber();
        StringRef currentFileName = location.getManager().getFilename(location);

        if (fileName != currentFileName) {
            fileName = currentFileName;
            line = currentLine;
            os << "#line " << line << " \"" << fileName << "\";\n";
        }
        else {

            if (currentLine != line) {
                if (currentLine > line && currentLine - line < 10) {
                    while (currentLine != line) {
                        os << "\n";
                        ++line;
                    }
                }
                else {
                    line = currentLine;
                    os << "#line " << line << ";\n";
                }
            }
        }

    }

    static bool beginsWith(const string& name, const string& prefix) {
        return name.substr(0, prefix.size()) == prefix;
    }
};

class FindNamedClassConsumer : public ASTConsumer {
private:
    FindNamedClassVisitor visitor;
    FILE* os;
public:
    explicit FindNamedClassConsumer(ASTContext *context, FILE* os)
        : visitor(context), os(os) {}

    virtual void HandleTranslationUnit(ASTContext &context) {
        visitor.TraverseDecl(context.getTranslationUnitDecl());
        visitor.SerializeTree(os);
    }
};

class FindNamedClassAction : public ASTFrontendAction {
private:
    FILE* os;
public:
    FindNamedClassAction(FILE* os) :os(os) {}
    virtual unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &compiler, StringRef inFile) {
        return unique_ptr<ASTConsumer>(new FindNamedClassConsumer(&compiler.getASTContext(), os));
    }
};

class FindNamedClassActionFactory : public FrontendActionFactory {
private:
    FILE* os;
public:
    FindNamedClassActionFactory(FILE* os) :os(os) {}
    FrontendAction *create() override { return new FindNamedClassAction(os); }
};

int main(int argc, const char **argv) {

    //    InitializeAllTargets();
    LLVMInitializeX86TargetInfo();
    LLVMInitializeX86TargetMC();
    LLVMInitializeX86AsmParser();

    CommonOptionsParser optionsParser(argc, argv, myToolCategory);

    ClangTool tool(optionsParser.getCompilations(), optionsParser.getSourcePathList());

    vector<string> extraArgs = { "-DHAREIDL_USE_CXX11_ATTRIBUTE" };

    tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(extraArgs,
        ArgumentInsertPosition::BEGIN));

    RaiiStdioFile f(!OutputFilename.empty() ? fopen(OutputFilename.c_str(), "wb") : nullptr);
    if (!OutputFilename.empty() && !f) {
        errs() << "Failed to open output file '" << OutputFilename.c_str() << "'\n";
        return 1;
    }

    return tool.run(new FindNamedClassActionFactory(f));
}

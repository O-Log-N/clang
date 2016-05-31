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

class FindNamedClassVisitor
    : public RecursiveASTVisitor<FindNamedClassVisitor> {
private:
    ASTContext *context;
    map<const Type*, string> typeMapping;
    Root root;
    ostringstream os;

public:
    explicit FindNamedClassVisitor(ASTContext *context)
        : context(context) {}

    void SerializeTree(FILE* ostream) {
        if (Print)
            printRoot(root);
        else if (Dump) {
            dbgDumpTree(&root, false, ostream);
        }
        else if (Serialize) {
            OStream OS(ostream);
            serializeRoot(root, OS);
        }
        else {
            string buffer = os.str();
            fwrite(buffer.c_str(), buffer.size(), 1, ostream);
        }
    }

    bool VisitTypedefNameDecl(TypedefNameDecl* declaration) {

        StringRef name = declaration->getName();
        if (name.substr(0, 5) == "hare_") {
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
                        addMapping(d, name);
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
    void addMapping(CXXRecordDecl *declaration, const string& name) {
        if (Print || Serialize || Dump)
            addMappingTree(declaration, name);
        else
            addMappingIdl(declaration, name);
    }

    void addMappingTree(CXXRecordDecl *declaration, const string& name) {

//        declaration->dump();
        unique_ptr<Structure> str(new Structure);
        //PrintingPolicy pol(context->getLangOpts());
        //pol.SuppressTagKeyword = true;
//        pol.SuppressTag = true;
//        pol.SuppressScope = true;
//        pol.SuppressUnwrittenScope = true;



        str->name = name;
        str->declType = Structure::MAPPING;
        str->type = Structure::STRUCT;

        str->location = getLocation(declaration->getLocStart());

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

            unique_ptr<DataMember> dm(new DataMember());
            FieldDecl* current = *it;

            dm->location = getLocation(current->getLocStart());

            dm->name = current->getDeclName().getAsString();
            
            QualType qt = current->getType();
            dm->type = std::move(processType(qt));

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

    DataType processType(QualType qt) const {

        DataType dt;

        if (qt.hasQualifiers())
            qt = qt.getUnqualifiedType();

        if (!qt.isCanonical())
            qt = qt.getCanonicalType();

        const Type* t = qt.getTypePtrOrNull();
        auto mapIt = typeMapping.find(t);
        string typeName = mapIt != typeMapping.end() ? mapIt->second : qt.getAsString();

        if (t->isEnumeralType()) {

            dt.kind = DataType::ENUM;

            EnumDecl* ed = t->getAs<EnumType>()->getDecl();
            auto r = ed->enumerators();
            if (r.begin() != r.end()) {
                for (auto it = r.begin(); it != r.end(); ++it) {

                    const APSInt& val = it->getInitVal();
                    typedef decltype(dt.enumValues)::value_type::second_type st;
                    if (val >= numeric_limits<st>::min() && val <= numeric_limits<st>::max()) {
                        dt.enumValues[it->getName()] = static_cast<st>(val.getExtValue());
                    }
                    //                        else
                    //                            reportError();
                }
            }
        }
        //            else if (t->isRecordType()) {
        else if (beginsWith(typeName, "class std::vector<")) {
            const RecordType *rt = t->getAs<RecordType>();
            RecordDecl* decl = rt->getDecl();

            ClassTemplateSpecializationDecl* tDecl = cast<ClassTemplateSpecializationDecl>(decl);
            const TemplateArgumentList& args = tDecl->getTemplateInstantiationArgs();
            const TemplateArgument& arg0 = args.get(0);
            QualType qt0 = arg0.getAsType();

            dt.kind = DataType::SEQUENCE;


            dt.paramType.reset(new DataType(processType(qt0)));
        }
        else if (beginsWith(typeName, "class std::map<")) {
            const RecordType *rt = t->getAs<RecordType>();
            RecordDecl* decl = rt->getDecl();

            ClassTemplateSpecializationDecl* tDecl = cast<ClassTemplateSpecializationDecl>(decl);
            const TemplateArgumentList& args = tDecl->getTemplateInstantiationArgs();

            QualType qt0 = args.get(0).getAsType();
            QualType qt1 = args.get(1).getAsType();

            dt.kind = DataType::DICTIONARY;

            dt.keyType.reset(new DataType(processType(qt0)));
            dt.paramType.reset(new DataType(processType(qt1)));
        }
        //else if (beginsWith(typeName, "class std::basic_string<char,")) {
        //    dt.kind = DataType::MAPPING_SPECIFIC;
        //    dt.mappingName = "string";
        //}
        else if (beginsWith(typeName, "class ")) {

            dt.kind = DataType::MAPPING_SPECIFIC;
            dt.mappingName = "class";

            dt.mappingAttrs.emplace("className", Variant(typeName.substr(6)));
        }
        else if (beginsWith(typeName, "struct ")) {

            dt.kind = DataType::MAPPING_SPECIFIC;
            dt.mappingName = "class";

            dt.mappingAttrs.emplace("className", Variant(typeName.substr(7)));
        }
        else {
            dt.kind = DataType::MAPPING_SPECIFIC;
            dt.mappingName = typeName;
        }

        return dt;
    }

    Location getLocation(const SourceLocation& loc) const {
        Location location;

        FullSourceLoc fullLoc = context->getFullLoc(loc);
        location.lineNumber = fullLoc.getSpellingLineNumber();
        location.fileName = fullLoc.getManager().getFilename(fullLoc).str();

        return location;
    }

    void addMappingIdl(CXXRecordDecl *declaration, const string& name) {

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
            string typeName = mapIt != typeMapping.end() ? mapIt->second : qt.getAsString();

            FullSourceLoc currentLoc = context->getFullLoc(current->getLocStart());
            fixLineNumber(fn, line, currentLoc);

            os << typeName << " ";
            //assert(t);
            if (t->isEnumeralType()) {
                EnumDecl* ed = t->getAs<EnumType>()->getDecl();
                auto r = ed->enumerators();
                if (r.begin() != r.end()) {
                    os << "{";
                    for (auto it = r.begin(); it != r.end(); ++it) {
                        if (it != r.begin())
                            os << ",";

                        os << it->getName().str();
                        os << "=";
                        os << it->getInitVal().toString(10);
                    }
                    os << "} ";
                }
            }

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

//    set<string> names = { "myHareSampleItem" };
    RaiiStdioFile f(!OutputFilename.empty() ? fopen(OutputFilename.c_str(), "wb") : stdout);

//    StringRef fname = !OutputFilename.empty() ? OutputFilename.c_str() : "-";

//    std::error_code EC;
//    raw_fd_ostream OS(fname, EC, sys::fs::F_None);

    //EC = sys::fs::openFileForWrite(Filename, FD, Flags);
    if (!f) {
        errs() << "Failed to open output file '" << OutputFilename.c_str() << "'\n";
        return 1;
    }

    return tool.run(new FindNamedClassActionFactory(f));
}

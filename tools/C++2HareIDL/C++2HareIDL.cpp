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


#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/TargetSelect.h"

#include "front-back/idl_tree.h"
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


class FindNamedClassVisitor
    : public RecursiveASTVisitor<FindNamedClassVisitor> {
private:
    ASTContext *context;
    map<const Type*, string> typeMapping;
    Root root;

public:
    explicit FindNamedClassVisitor(ASTContext *context)
        : context(context) {}

    void SerializeTree(raw_ostream& os) {
        dbgDumpTree(&root, true, os);
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

//        declaration->dump();
        unique_ptr<Structure> str(new Structure);

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

            string currentName = current->getDeclName().getAsString();

            dm->name = currentName;
//                string t = current->getType().getCanonicalType().getAsString();
            QualType qt = current->getType();

            if (qt.hasQualifiers()) {
                //TODO report error?
                qt = qt.getUnqualifiedType();
            }

            const Type* t = qt.getCanonicalType().getTypePtrOrNull();
            auto mapIt = typeMapping.find(t);
            string typeName = mapIt != typeMapping.end() ? mapIt->second : qt.getAsString();

            dm->type.mappingName = typeName;

            //assert(t);
            if (t->isEnumeralType()) {

                dm->type.kind = DataType::ENUM;

                EnumDecl* ed = t->getAs<EnumType>()->getDecl();
                auto r = ed->enumerators();
                if (r.begin() != r.end()) {
                    for (auto it = r.begin(); it != r.end(); ++it) {
                        
                        const APSInt& val = it->getInitVal();
                        typedef decltype(dm->type.enumValues)::value_type::second_type st;
                        if (val >= numeric_limits<st>::min() && val <= numeric_limits<st>::max()) {
                            dm->type.enumValues[it->getName()] = static_cast<st>(val.getExtValue());
                        }
//                        else
//                            reportError();
                    }
                }
            }
            else {
                dm->type.kind = DataType::MAPPING_SPECIFIC;
            }

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

    Location getLocation(const SourceLocation& loc) const {
        Location location;

        FullSourceLoc fullLoc = context->getFullLoc(loc);
        location.lineNumber = fullLoc.getSpellingLineNumber();
        location.fileName = fullLoc.getManager().getFilename(fullLoc).str();

        return location;
    }

};

class FindNamedClassConsumer : public ASTConsumer {
private:
    FindNamedClassVisitor visitor;
    raw_ostream& os;
public:
    explicit FindNamedClassConsumer(ASTContext *context, raw_ostream& os)
        : visitor(context), os(os) {}

    virtual void HandleTranslationUnit(ASTContext &context) {
        visitor.TraverseDecl(context.getTranslationUnitDecl());
        visitor.SerializeTree(os);
    }
};

class FindNamedClassAction : public ASTFrontendAction {
private:
    raw_ostream& os;
public:
    FindNamedClassAction(raw_ostream& os) :os(os) {}
    virtual unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &compiler, StringRef inFile) {
        return unique_ptr<ASTConsumer>(new FindNamedClassConsumer(&compiler.getASTContext(), os));
    }
};

class FindNamedClassActionFactory : public FrontendActionFactory {
private:
    raw_ostream& os;
public:
    FindNamedClassActionFactory(raw_ostream& os) :os(os) {}
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

    StringRef fname = !OutputFilename.empty() ? OutputFilename.c_str() : "-";

    std::error_code EC;
    raw_fd_ostream OS(fname, EC, sys::fs::F_None);

    //EC = sys::fs::openFileForWrite(Filename, FD, Flags);
    if (EC) {
        errs() << "Failed to open output file '" << fname << "'\n"
            << EC.message() << "\n";
        return 1;
    }

    return tool.run(new FindNamedClassActionFactory(OS));
}

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

static cl::opt<bool>
Dependencies("dependencies", cl::desc("Automatically process dependecy classes.\n"),
    cl::cat(myToolCategory));


void SerializeTree(FILE* ostream, Root& root) {

    if (Dump) {
    dbgDumpTree(&root, false, ostream ? ostream : stdout);
    }
    else if (Idl){
    //string buffer = os.str();
    //fwrite(buffer.c_str(), buffer.size(), 1, ostream ? ostream : stdout);
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


struct MappingData {
    map<const Type*, string> typeMapping;
    pair<const ClassTemplateSpecializationDecl*, string> vectorBool;
    map<const ClassTemplateDecl*, string> sequenceType;
    map<const ClassTemplateDecl*, string> owningPtrType;
    map<const ClassTemplateDecl*, string> dictionaryType;
};

class RecursiveMapVisitor
    : public RecursiveASTVisitor<RecursiveMapVisitor> {
private:
    ASTContext *context;
    PrintingPolicy policy;
    const MappingData& md;
    list<const CXXRecordDecl*>& toBeMapped; //better to keep order
    set<const CXXRecordDecl*> alreadyMapped;
    set<const CXXRecordDecl*> polymorphicBases;
    Root root;
    //    ostringstream os;


public:
    explicit RecursiveMapVisitor(ASTContext *context, const MappingData& md,
        list<const CXXRecordDecl*>& toBeMapped)
        : context(context), policy(context->getLangOpts()), md(md), toBeMapped(toBeMapped) {
        policy.SuppressTagKeyword = true;
        policy.Bool = true;
    }

    Root& getRoot() {
        return root;
    }

    bool VisitCXXRecordDecl(CXXRecordDecl *declaration) {

        if (declaration->hasDefinition()) {
            const CXXRecordDecl* canon = declaration->getCanonicalDecl();
            if (!isAlreadyProcessed(canon)) {
                for (auto it : polymorphicBases) {
                    if (canon->isDerivedFrom(it)) {
                        toBeMapped.emplace_back(declaration);
                    }
                }
            }
        }
        return true;
    }

    bool doMapping() {

        if (toBeMapped.empty())
            return false;

        size_t before = polymorphicBases.size();
        while (!toBeMapped.empty()) {
            alreadyMapped.insert(toBeMapped.front());
            addMapping(toBeMapped.front());
            toBeMapped.pop_front();
        }

        return before != polymorphicBases.size();
    }

private:
    bool isAlreadyProcessed(const CXXRecordDecl* declaration) {
        if (alreadyMapped.find(declaration) != alreadyMapped.end())
            return true;

        for (auto each : toBeMapped) {
            if (each == declaration)
                return true;
        }

        return false;
    }

    void addMapping(const CXXRecordDecl *declaration) {

        errs() << "Processing " << declaration->getNameAsString() << "\n";

        //declaration->dump();
        unique_ptr<Structure> str(new Structure);

        str->name = declaration->getNameAsString();
        str->declType = Structure::MAPPING;
        str->type = Structure::STRUCT;

        str->location = getLocation(declaration->getLocStart());

        auto bases = declaration->bases();
        //        size_t sz = distance(bases.begin(), bases.end());

        if (bases.begin() != bases.end()) {
            QualType inherit = bases.begin()->getType();
            str->inheritedFrom = inherit.getCanonicalType().getAsString(policy);
            const Type* t = inherit.getTypePtrOrNull();
            if (t && Dependencies) {
                const CXXRecordDecl* baseDecl = t->getAsCXXRecordDecl();
                if (baseDecl->hasDefinition()) {
                    const CXXRecordDecl* canon = baseDecl->getCanonicalDecl();
                    if (!isAlreadyProcessed(canon)) {
                        toBeMapped.emplace_back(canon);
                    }
                }
            }
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
            if (flag)
                str->members.emplace_back(dm.release());
        }
        root.structures.push_back(std::move(str));
    }

    bool processType(DataType& dt, QualType qt) {

        if (qt.hasQualifiers())
            qt = qt.getUnqualifiedType();

        if (!qt.isCanonical())
            qt = qt.getCanonicalType();


        string typeName = qt.getAsString(policy);
        const Type* t = qt.getTypePtrOrNull();

        auto mapIt = md.typeMapping.find(t);
        if (mapIt != md.typeMapping.end()) {
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
            dt.mappingName = ed->getName();

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
            //tDecl->dump();
            if (tDecl) {
                if (tDecl == md.vectorBool.first) {
                    dt.kind = DataType::SEQUENCE;
                    dt.mappingName = md.vectorBool.second;

                    dt.paramType.reset(new DataType());
                    dt.paramType->kind = DataType::MAPPING_SPECIFIC;
                    dt.paramType->mappingName = "bool";
                    return true;
                }

                ClassTemplateDecl* ctDecl = tDecl->getSpecializedTemplate();
                const TemplateArgumentList& args = tDecl->getTemplateInstantiationArgs();

                auto it = md.sequenceType.find(ctDecl);
                if (it != md.sequenceType.end()) {

                    dt.kind = DataType::SEQUENCE;
                    dt.mappingName = it->second;

                    dt.paramType.reset(new DataType());
                    if (args.size() < 1)
                        return false;

                    if (!processType(*dt.paramType, args.get(0).getAsType()))
                        return false;

                    return true;
                }

                auto it1 = md.owningPtrType.find(ctDecl);
                if (it1 != md.owningPtrType.end()) {

                    dt.kind = DataType::SEQUENCE;
                    dt.mappingName = it1->second;

                    dt.paramType.reset(new DataType());
                    if (args.size() < 1)
                        return false;

                    QualType qt0 = args.get(0).getAsType();
                    if (!processType(*dt.paramType, qt0))
                        return false;
                        
                    if (Dependencies) {
                        const Type* t0 = qt0.getTypePtrOrNull();
                        const CXXRecordDecl* pointedDecl = t0->getAsCXXRecordDecl();
                        if (pointedDecl->hasDefinition()) {
                            const CXXRecordDecl* canon0 = pointedDecl->getCanonicalDecl();
                            polymorphicBases.insert(canon0);
                        }
                    }

                    return true;
                }

                auto it2 = md.dictionaryType.find(ctDecl);
                if (it2 != md.dictionaryType.end()) {

                    if (args.size() < 2)
                        return false;

                    dt.kind = DataType::DICTIONARY;
                    dt.mappingName = it2->second;

                    dt.keyType.reset(new DataType());
                    if (!processType(*dt.keyType, args.get(0).getAsType()))
                        return false;

                    dt.paramType.reset(new DataType());
                    if (!processType(*dt.paramType, args.get(1).getAsType()))
                        return false;

                    return true;
                }
            }
            else {
                dt.kind = DataType::NAMED_TYPE;
                dt.mappingName = typeName;

                if (Dependencies) {
                    const CXXRecordDecl* namedDecl = t->getAsCXXRecordDecl();
                    if (namedDecl->hasDefinition()) {
                        const CXXRecordDecl* canon = namedDecl->getCanonicalDecl();
                        if (!isAlreadyProcessed(canon)) {
                            toBeMapped.emplace_back(canon);
                        }
                    }
                }

                return true;
            }
        }
        else if (t->isPointerType()) {
            errs() << "Unsupported pointer type " << typeName << "\n";
            return false;
        }

        errs() << "Unsupported type " << typeName << "\n";
        t->dump();
        return false;
    }

    Location getLocation(const SourceLocation& loc) const {
        Location location;

        FullSourceLoc fullLoc = context->getFullLoc(loc);
        location.lineNumber = fullLoc.getSpellingLineNumber();
        location.fileName = fullLoc.getManager().getFilename(fullLoc).str();

        return location;
    }
};


class FindNamedClassVisitor
    : public RecursiveASTVisitor<FindNamedClassVisitor> {
private:
    ASTContext *context;
    MappingData& md;
    set<string> toBeFoundAndMapped;
    list<const CXXRecordDecl*>& toBeMapped; //better to keep order


public:
    explicit FindNamedClassVisitor(ASTContext *context, MappingData& md,
        list<const CXXRecordDecl*>& toBeMapped)
        : context(context), md(md), toBeMapped(toBeMapped) {
        toBeFoundAndMapped.insert(FindClasses.begin(), FindClasses.end());
    }

    
    bool VisitTypeAliasDecl(TypeAliasDecl* declaration) {
        //if (beginsWith(declaration->getName().str(), "hare_"))
        //    declaration->dump();
        return visitTypedefOrTypeAlias(declaration);
    }

    bool VisitTypedefNameDecl(TypedefNameDecl* declaration) {
        return visitTypedefOrTypeAlias(declaration);
    }


    bool visitTypedefOrTypeAlias(TypedefNameDecl* declaration) {

        
        StringRef name = declaration->getName();
        string declName = declaration->getDeclName().getAsString();

        if (name.startswith("hare_")) {

            StringRef mapping;

            HareMappingAttr* at = declaration->getAttr<HareMappingAttr>();
            if (at) {
                mapping = at->getArgument();
            }
                
            if (name.startswith("hare_sequence")) {
                static const size_t seqLen = strlen("hare_sequence_");
                StringRef n = mapping.empty() ? name.substr(seqLen) : mapping;

                QualType qt = declaration->getUnderlyingType();
                const Type* t = qt.getCanonicalType().getTypePtrOrNull();
                if (t && t->isRecordType()) {
                    const RecordType *rt = t->getAs<RecordType>();
                    RecordDecl* rDecl = rt->getDecl();
                    ClassTemplateSpecializationDecl* ctsDecl = dyn_cast<ClassTemplateSpecializationDecl>(rDecl);
                    if (ctsDecl) {
                        ClassTemplateDecl* ctDecl = ctsDecl->getSpecializedTemplate();
                        md.sequenceType.emplace(ctDecl, n.str());
                    }
                }
            }
            else if (name.startswith("hare_owning_ptr")) {
                static const size_t ownLen = strlen("hare_owning_ptr_");
                StringRef n = mapping.empty() ? name.substr(ownLen) : mapping;

                QualType qt = declaration->getUnderlyingType();
                const Type* t = qt.getCanonicalType().getTypePtrOrNull();
                if (t && t->isRecordType()) {
                    const RecordType *rt = t->getAs<RecordType>();
                    RecordDecl* rDecl = rt->getDecl();
                    ClassTemplateSpecializationDecl* ctsDecl = dyn_cast<ClassTemplateSpecializationDecl>(rDecl);
                    if (ctsDecl) {
                        ClassTemplateDecl* ctDecl = ctsDecl->getSpecializedTemplate();
                        md.owningPtrType.emplace(ctDecl, n);
                    }
                }
            }
            else if (name.startswith("hare_dictionary_")) {
                static const size_t dictLen = strlen("hare_dictionary_");
                StringRef n = mapping.empty() ? name.substr(dictLen) : mapping;

                QualType qt = declaration->getUnderlyingType();
                const Type* t = qt.getCanonicalType().getTypePtrOrNull();
                if (t && t->isRecordType()) {
                    const RecordType *rt = t->getAs<RecordType>();
                    RecordDecl* rDecl = rt->getDecl();
                    ClassTemplateSpecializationDecl* ctsDecl = dyn_cast<ClassTemplateSpecializationDecl>(rDecl);
                    if (ctsDecl) {
                        ClassTemplateDecl* ctDecl = ctsDecl->getSpecializedTemplate();
                        md.dictionaryType.emplace(ctDecl, n.str());
                    }
                }
            }
            //Special case to handle std::vector<bool>
            else if (name.startswith("hare_vectorbool")) {
                static const size_t vectBoolLen = strlen("hare_vectorbool_");
                StringRef n = mapping.empty() ? name.substr(vectBoolLen) : mapping;

                QualType qt = declaration->getUnderlyingType();
                const Type* t = qt.getCanonicalType().getTypePtrOrNull();
                if (t->isRecordType()) {
                    const RecordType *rt = t->getAs<RecordType>();
                    const RecordDecl* decl = rt->getDecl();
                    const ClassTemplateSpecializationDecl* tDecl = dyn_cast<const ClassTemplateSpecializationDecl>(decl);
                    if (tDecl) {

                        md.vectorBool = make_pair(tDecl, n.str());
                    }
                }
            }
            else if (name.startswith("hare_mapping")) {
                static const size_t mapLen = strlen("hare_mapping_");
                StringRef n = mapping.empty() ? name.substr(mapLen) : mapping;

                QualType qt = declaration->getUnderlyingType();
                const Type* t = qt.getCanonicalType().getTypePtrOrNull();
                if (t) {
                    md.typeMapping[t] = n.str();
                }
            }
            else {
                auto it = toBeFoundAndMapped.find(name.str());
                if (it != toBeFoundAndMapped.end()) {

                    QualType qt = declaration->getUnderlyingType();
                    const Type* t = qt.getTypePtrOrNull();
                    if (t) {
                        const CXXRecordDecl* decl = t->getAsCXXRecordDecl();
                        addToBeMapped(decl);
                        toBeFoundAndMapped.erase(it);
                    }
                }
            }
        }
        return true;
    }

    bool VisitCXXRecordDecl(CXXRecordDecl *declaration) {

        StringRef name = declaration->getName();

        auto it = toBeFoundAndMapped.find(name.str());
        if (it != toBeFoundAndMapped.end()) {
            addToBeMapped(declaration);
            toBeFoundAndMapped.erase(it);
        }
        else if (FindByAttribute && declaration->hasAttr<HareMappingAttr>()) {
            addToBeMapped(declaration);
        }
        else if (declaration->hasAttr<AnnotateAttr>()) {
            AnnotateAttr* at = declaration->getAttr<AnnotateAttr>();
            StringRef t = at->getAnnotation();
            if (t == "hare::mapping") {
                addToBeMapped(declaration);
            }
        }

        return true;
    }

private:

    void addToBeMapped(const CXXRecordDecl* declaration) {
        if (declaration && declaration->hasDefinition()) {
            const CXXRecordDecl* canon = declaration->getCanonicalDecl();
            if (!findToBeMapped(canon)) {
                toBeMapped.emplace_back(canon);
            }
        }
    }

    bool findToBeMapped(const CXXRecordDecl* declaration) {
        for (auto each : toBeMapped) {
            if (each == declaration)
                return true;
        }
        return false;
    }

    static bool beginsWith(const string& name, const string& prefix) {
        return name.substr(0, prefix.size()) == prefix;
    }
};

class FindNamedClassConsumer : public ASTConsumer {
private:
    MappingData md;
    list<const CXXRecordDecl*> toBeMapped; //better to keep order
    FindNamedClassVisitor visitor1;
    RecursiveMapVisitor visitor2;
    FILE* os;
public:
    explicit FindNamedClassConsumer(ASTContext *context, FILE* os)
        : visitor1(context, md, toBeMapped), visitor2(context, md, toBeMapped), os(os)
    {}

    virtual void HandleTranslationUnit(ASTContext &context) {
        visitor1.TraverseDecl(context.getTranslationUnitDecl());

        while(visitor2.doMapping()) {
            errs() << "-----------\n";
            visitor2.TraverseDecl(context.getTranslationUnitDecl());
        }

        SerializeTree(os, visitor2.getRoot());
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

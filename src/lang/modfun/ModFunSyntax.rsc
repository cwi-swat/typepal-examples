module lang::modfun::ModFunSyntax

// Modular Functional language with declared types (an extension of Fun)

extend lang::fun::FunSyntax;

lexical ModId   = ([A-Z][a-z0-9]* !>> [a-z0-9]) \ Reserved;

keyword Reserved = "module" | "import" | "def";

start syntax ModFun 
    = ModuleDecl* modules
    ;

syntax ModuleDecl
    = "module" ModId mid  "{" Decl* decls "}"
    ;
syntax Decl
    = ImportDecl importDecl
    | VarDecl varDecl
    ;
syntax ImportDecl
    = "import" ModId mid ";"
    ;

syntax VarDecl
    = "def" Id id ":" Type tp "=" Expression expression ";"
    ;    
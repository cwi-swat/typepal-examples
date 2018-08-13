module lang::modfun::ModFunChecker

// Modular Functional language with declared types (an extension of Fun)

import lang::modfun::ModFunSyntax;
extend lang::fun::FunChecker;

// ----  IdRoles, PathLabels and AType ---------------------------------------- 
     
data AType
    = moduleType(str name)
    ;
str prettyAType(moduleType(str name)) = "module(<name>)";
    
data IdRole
    = moduleId()
    ;
    
data PathRole
    = importPath()
    ;
    
// ----  Collect facts & constraints ------------------------------------------

void collect(current: (ModuleDecl) `module <ModId mid> { <Decl* decls> }`, Collector c) {
     c.define("<mid>", moduleId(), mid, defType(moduleType("<mid>")));
     //c.enterScope(current);
        collect(decls, c);
     //c.leaveScope(current);
}

void collect(current: (ImportDecl) `import <ModId mid> ;`, Collector c){
     c.useViaPath(mid, {moduleId()}, importPath());
}

void collect(current: (VarDecl) `def <Id id> : <Type tp> = <Expression expression> ;`, Collector c)     {
     c.define("<id>", variableId(), id, defType(tp));
     c.requireEqual(tp, expression, error(current, "Expected initializing expression of type %t, found %t", expression, tp));
     collect(tp, expression, c);
}

// ----  Testing --------------------------------------------------------------

private ModFun modfunSample(str name) = parse(#ModFun, |project://typepal-examples/src/lang/modfun/<name>.modfun|);

TModel modfunTModel(str name){
   return modfunTModelFromTree(modfunSample(name), debug=true);
}

TModel modfunTModelFromTree(Tree pt, bool debug = true){
    return collectAndSolve(pt, debug=debug);
}

TModel modfunTModelFromStr(str text){
    pt = parse(#start[ModFun], text).top;
    return modfunTModelFromTree(pt);
}

list[Message] modfunCheck(str name) {
    tm = modfunTModel(name);
    return tm.messages;
}

void modfunTest() {
     runTests([|project://typepal-examples/src/lang/modfun/tests.ttl|], #ModFun, modfunTModelFromTree);
}

value main(){
    modfunTest();
    return true;
}
    
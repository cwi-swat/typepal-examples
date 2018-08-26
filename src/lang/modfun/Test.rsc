module lang::modfun::Test

import lang::modfun::Syntax;
extend lang::modfun::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Testing --------------------------------------------------------------

private ModFun modfunSample(str name) = parse(#ModFun, |project://typepal-examples/src/lang/modfun/<name>.mfun|);

TModel modfunTModel(str name){
   return modfunTModelForTree(modfunSample(name), debug=true);
}

TModel modfunTModelForTree(Tree pt, bool debug = true){
    return collectAndSolve(pt, debug=debug);
}

TModel modfunTModelFromStr(str text){
    pt = parse(#start[ModFun], text).top;
    return modfunTModelForTree(pt);
}

list[Message] modfunCheck(str name) {
    tm = modfunTModel(name);
    return tm.messages;
}

bool modfunTests()
    = runTests([|project://typepal-examples/src/lang/modfun/tests.ttl|], 
               #ModFun,
               modfunTModelForTree,
               runName = "ModFun");

value main() 
    =  modfunTests();
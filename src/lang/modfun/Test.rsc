module lang::modfun::Test

extend lang::modfun::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

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

bool modfunTests()
    = runTests([|project://typepal-examples/src/lang/modfun/tests.ttl|], #ModFun, modfunTModelFromTree);

value main() 
    =  modfunTests();
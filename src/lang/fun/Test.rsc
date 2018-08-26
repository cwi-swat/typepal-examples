module lang::fun::Test

import lang::fun::Syntax;
extend lang::fun::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Testing --------------------------------------------------------------

private Fun funSample(str name) = parse(#Fun, |project://typepal-examples/src/lang/fun/<name>.fun|);

TModel funTModel(str name){
   return funTModelForTree(funSample(name));
}

TModel funTModelForTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, debug=debug);
}

TModel funTModelFromStr(str text){
    pt = parse(#start[Fun], text).top;
    return funTModelForTree(pt);
}

list[Message] funCheck(str name) {
    tm = funTModel(name);
    return tm.messages;
}

bool funTests() 
    =  runTests([|project://typepal-examples/src/lang/fun/tests.ttl|], #Fun, funTModelForTree, runName="Fun");

value main() = funTests();

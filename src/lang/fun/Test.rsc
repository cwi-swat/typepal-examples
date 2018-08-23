module lang::fun::Test

extend lang::fun::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Testing --------------------------------------------------------------

private Fun funSample(str name) = parse(#Fun, |project://typepal-examples/src/lang/fun/<name>.fun|);

TModel funTModel(str name){
   return funTModelFromTree(funSample(name));
}

TModel funTModelFromTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, debug=debug);
}

TModel funTModelFromStr(str text){
    pt = parse(#start[Fun], text).top;
    return funTModelFromTree(pt);
}

list[Message] funCheck(str name) {
    tm = funTModel(name);
    return tm.messages;
}

bool funTests() 
    =  runTests([|project://typepal-examples/src/lang/fun/tests.ttl|], #Fun, funTModelFromTree);

value main() = funTests();

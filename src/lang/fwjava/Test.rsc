module lang::fwjava::Test

import lang::fwjava::Syntax;
extend lang::fwjava::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel fwjTModelForTree(Tree pt){
    if(pt has top) pt = pt.top;
    
    c = newCollector("FWJ checker", pt, config=fwjConfig());
    fwjPreCollectInitialization(pt, c);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel fwjTModelFromName(str mname, bool debug){
    pt = parse(#start[FWJProgram], |project://typepal-examples/src/lang/fwjava/<mname>.fwj|).top;
    return fwjTModelForTree(pt);
}

bool fwjTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/fwjava/tests.ttl|], 
                     #start[FWJProgram], 
                     TModel (Tree t) { return fwjTModelForTree(t); },
                     runName = "FwJava");
}

value main() = fwjTests();
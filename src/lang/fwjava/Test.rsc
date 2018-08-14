module lang::fwjava::Test

extend lang::fwjava::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel fwjTModelFromTree(Tree pt, bool debug){
    if(pt has top) pt = pt.top;
    
    c = newCollector("FWJ checker", pt, config=fwjConfig(), debug=debug);
    fwjPreCollectInitialization(pt, c);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel fwjTModelFromName(str mname, bool debug){
    pt = parse(#start[FWJProgram], |project://typepal-examples/src/lang/fwjava/<mname>.fwj|).top;
    return fwjTModelFromTree(pt, debug);
}

bool fwjTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/fwjava/tests.ttl|], #start[FWJProgram], TModel (Tree t) {
        return fwjTModelFromTree(t, debug);
    });
}

value main() = fwjTests();
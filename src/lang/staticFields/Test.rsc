module lang::staticFields::Test

import lang::staticFields::Syntax;

extend lang::staticFields::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel staticFieldsTModelForTree(Tree pt, bool debug){
    return collectAndSolve(pt, config=staticFieldsConfig(), debug=debug);
}

TModel staticFieldsTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/staticFields/<mname>.struct|).top;
    return staticFieldsTModelForTree(pt, debug);
}

bool staticFieldsTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/staticFields/tests.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return staticFieldsTModelForTree(t, debug); },
                    runName = "StaticFields");
}

value main()
    = staticFieldsTests();
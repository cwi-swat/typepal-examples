module lang::static_fields::Test

extend lang::static_fields::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel staticFieldsTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, config=staticFieldsConfig(), debug=debug);
}

TModel staticFieldsTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/static_fields/<mname>.struct|).top;
    return staticFieldsTModelFromTree(pt, debug);
}

bool staticFieldsTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/static_fields/tests.ttl|], #start[Program], TModel (Tree t) {
        return staticFieldsTModelFromTree(t, debug);
    });
}

value main()
    = staticFieldsTests();
module lang::struct::Test

extend lang::struct::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, config = structConfig(), debug=debug);
}

TModel structTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/struct/<mname>.struct|).top;
    return structTModelFromTree(pt, debug);
}

bool structTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/struct/tests.ttl|], #start[Program], TModel (Tree t) {
        return structTModelFromTree(t, debug);
    });
}

value main()
    = structTests();
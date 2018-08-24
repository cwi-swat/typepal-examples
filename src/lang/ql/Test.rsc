module lang::ql::Test

extend lang::ql::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel qlTModelFromName(str name, bool debug = false) {
    Tree pt = parse(#start[Form], |project://typepal-examples/src/lang/ql/examples/<name>.ql|);
    return collectAndSolve(pt, debug=debug);
}

TModel qlTModelForTree(Tree pt, bool debug = false) {
    return collectAndSolve(pt, debug=debug);
}

bool qlTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/ql/tests.ttl|], #start[Program], TModel (Tree t) {
        return qlTModelForTree(t, debug=debug);
    });
}

value main()
    = qlTests();
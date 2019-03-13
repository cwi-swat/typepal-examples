module lang::ql::Test

import lang::ql::Syntax;
extend lang::ql::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel qlTModelForName(str name) {
    Tree pt = parse(#start[Form], |project://typepal-examples/src/lang/ql/examples/<name>.ql|);
    return collectAndSolve(pt);
}

TModel qlTModelForTree(Tree pt) {
    return collectAndSolve(pt);
}

bool qlTests() {
    return runTests([|project://typepal-examples/src/lang/ql/tests.ttl|], #start[Form], 
                     TModel (Tree t) { return qlTModelForTree(t); },
                     runName = "QL");
}

value main()
    = qlTests();
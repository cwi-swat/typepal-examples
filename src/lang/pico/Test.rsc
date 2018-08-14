module lang::pico::Test

extend lang::pico::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel picoTModelFromName(str name, bool debug = false) {
    Tree pt = parse(#start[Program], |project://typepal-examples/src/pico/<name>.pico|);
    return collectAndSolve(pt, debug=debug);
}

TModel picoTModelFromTree(Tree pt, bool debug = false) {
    return collectAndSolve(pt, debug=debug);
}

bool picoTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/pico/tests.ttl|], #start[Program], TModel (Tree t) {
        return picoTModelFromTree(t, debug=debug);
    });
}

value main()
    = picoTests();
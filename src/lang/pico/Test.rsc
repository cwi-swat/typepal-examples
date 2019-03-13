module lang::pico::Test

import lang::pico::Syntax;
extend lang::pico::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel picoTModelFromName(str name) {
    Tree pt = parse(#start[Program], |project://typepal-examples/src/pico/<name>.pico|);
    return collectAndSolve(pt);
}

TModel picoTModelForTree(Tree pt) {
    return collectAndSolve(pt);
}

bool picoTests() {
    return runTests([|project://typepal-examples/src/lang/pico/tests.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return picoTModelForTree(t); },
                    runName = "Pico");
}

value main()
    = picoTests();
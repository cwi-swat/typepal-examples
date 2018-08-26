module lang::struct::Test

import lang::struct::Syntax;

extend lang::struct::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structTModelForTree(Tree pt, bool debug){
    return collectAndSolve(pt, config = structConfig(), debug=debug);
}

TModel structTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/struct/<mname>.struct|).top;
    return structTModelForTree(pt, debug);
}

bool structTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/struct/tests.ttl|], 
                    #start[Program],
                    TModel (Tree t) { return structTModelForTree(t, debug); },
                    runName = "Struct");
}

value main()
    = structTests();
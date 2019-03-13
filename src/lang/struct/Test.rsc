module lang::struct::Test

import lang::struct::Syntax;

extend lang::struct::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structTModelForTree(Tree pt){
    return collectAndSolve(pt, config = structConfig());
}

TModel structTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/struct/<mname>.struct|).top;
    return structTModelForTree(pt);
}

bool structTests() {
    return runTests([|project://typepal-examples/src/lang/struct/tests.ttl|], 
                    #start[Program],
                    TModel (Tree t) { return structTModelForTree(t); },
                    runName = "Struct");
}

value main()
    = structTests();
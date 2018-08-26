module lang::structParameters::Test

import lang::structParameters::Syntax;

extend lang::structParameters::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structParametersTModelForTree(Tree pt, bool debug){
    return collectAndSolve(pt, config = structParametersConfig(), debug=debug);
}

TModel structParametersTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/structParameters/<mname>.struct|).top;
    return structParametersTModelForTree(pt, debug);
}

bool structParametersTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/structParameters/tests.ttl|], 
                     #start[Program], 
                     TModel (Tree t) { return structParametersTModelForTree(t, debug); },
                     runName = "StructParameters");
}

value main()
    = structParametersTests();
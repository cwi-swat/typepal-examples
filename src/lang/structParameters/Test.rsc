module lang::structParameters::Test

import lang::structParameters::Syntax;

extend lang::structParameters::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structParametersTModelForTree(Tree pt){
    return collectAndSolve(pt, config = structParametersConfig());
}

TModel structParametersTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/structParameters/<mname>.struct|).top;
    return structParametersTModelForTree(pt);
}

bool structParametersTests() {
    return runTests([|project://typepal-examples/src/lang/structParameters/tests.ttl|], 
                     #start[Program], 
                     TModel (Tree t) { return structParametersTModelForTree(t); },
                     runName = "StructParameters");
}

value main()
    = structParametersTests();
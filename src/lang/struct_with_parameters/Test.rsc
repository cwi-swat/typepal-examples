module lang::struct_with_parameters::Test

extend lang::struct_with_parameters::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structWithParametersTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, config = structWithParametersConfig(), debug=debug);
}

TModel structWithParametersTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/struct_with_parameters/<mname>.struct|).top;
    return structWithParametersTModelFromTree(pt, debug);
}

bool structWithParametersTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/struct_with_parameters/tests.ttl|], #start[Program], TModel (Tree t) {
        return structWithParametersTModelFromTree(t, debug);
    });
}

value main()
    = structWithParametersTests();
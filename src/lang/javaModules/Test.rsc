module lang::javaModules::Test

import lang::javaModules::Syntax;
extend lang::javaModules::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel javaModulesTModelForTree(Tree pt){
    if(pt has top) pt = pt.top;
    
    c = newCollector("Java Modules checker", pt, config=javaModulesConfig());
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}


TModel javaModulesTModelFromName(str mname, bool debug){
    pt = parse(#start[JavaModulesProgram], |project://typepal-examples/src/lang/javaModules/<mname>.jm|).top;
    return javaModulesTModelForTree(pt);
}

bool javaModulesTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/javaModules/tests.ttl|], 
                     #start[JavaModulesProgram], 
                     TModel (Tree t) { return javaModulesTModelForTree(t); },
                     runName = "javaModules");
}

value main() = javaModulesTests();
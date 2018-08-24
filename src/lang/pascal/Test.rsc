module lang::pascal::Test

extend lang::pascal::Checker;
extend analysis::typepal::TestFramework;
import PareTree;

// ----  Examples & Tests --------------------------------

TModel pascalTModelForTree(Tree pt, bool debug){
    if(pt has top) pt = pt.top;
    
    c = newCollector("Pascal checker", pt, config=pascalConfig(), debug=debug);
    pascalPreCollectInitialization(pt, c);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel pascalTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/pascal/examples/<mname>.pascal|).top;
    return pascalTModelForTree(pt, debug);
}

list[str] examples = ["beginend", "bisect", "complex", "convert", "cosine", "egfor", "egrepeat", "egwhile", "exponentiation", "exponentiation2",
                      "fcount", "graph1", "graph2", "inflation", "insert", "matrixmul", "minmax", "minmax2", "minmax2", 
                      "parameters", "person", "primes", 
                      "recursivegcd", "roman", "setop", "sideeffect", "summing", "traversal", "with"];

bool pascalTests(bool debug = false) {
    bool ok = runTests([|project://typepal-examples/src/lang/pascal/expression-tests.ttl|,
                        |project://typepal-examples/src/lang/pascal/statement-tests.ttl|
                       ], #start[Program], TModel (Tree t) {
        return pascalTModelForTree(t, debug);
    });
    println("Executing examples");
    for(ex <- examples){
        msgs = pascalTModelFromName(ex, false).messages;
        if(isEmpty(msgs)){
            println("<ex>: ok");
        } else {
            println("<ex>:");
            println(msgs);
            ok = false;
        }
    }
    return ok;
}

value main() 
    = pascalTests();
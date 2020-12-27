var searchIndex = JSON.parse('{\
"egg":{"doc":"`egg` (e-graphs good) is a e-graph library optimized for…","i":[[3,"Id","egg","A key to identify `EClass`es within an `EGraph`.",null,null],[3,"Dot","","A wrapper for an `EGraph` that can output GraphViz for…",null,null],[3,"EClass","","An equivalence class of enodes.",null,null],[12,"id","","This eclass\'s id.",0,null],[12,"nodes","","The equivalent enodes in this equivalence class.",0,null],[12,"data","","The analysis data associated with this eclass.",0,null],[3,"EGraph","","A data structure to keep track of equalities between…",null,null],[12,"analysis","","The `Analysis` given when creating this `EGraph`.",1,null],[3,"Extractor","","Extracting a single `RecExpr` from an `EGraph`.",null,null],[3,"AstSize","","A simple `CostFunction` that counts total ast size.",null,null],[3,"AstDepth","","A simple `CostFunction` that counts maximum ast depth.",null,null],[3,"RecExpr","","A recursive expression from a user-defined `Language`.",null,null],[3,"SymbolLang","","A simple language used for testing.",null,null],[12,"op","","The operator for an enode",2,null],[12,"children","","The enode\'s children `Id`s",2,null],[3,"Pattern","","A pattern that can function as either a `Searcher` or…",null,null],[12,"ast","","The actual pattern as a `RecExpr`",3,null],[3,"SearchMatches","","The result of searching a `Searcher` over one eclass.",null,null],[12,"eclass","","The eclass id that these matches were found in.",4,null],[12,"substs","","The matches themselves.",4,null],[3,"ConditionEqual","","A `Condition` that checks if two terms are equivalent.",null,null],[12,"0","","",5,null],[12,"1","","",5,null],[3,"ConditionalApplier","","An `Applier` that checks a `Condition` before applying.",null,null],[12,"condition","","The `Condition` to `check` before calling `apply_one` on…",6,null],[12,"applier","","The inner `Applier` to call once `condition` passes.",6,null],[3,"Rewrite","","A rewrite that searches for the lefthand side and applies…",null,null],[12,"name","","The name of the rewrite.",7,null],[12,"searcher","","The searcher (left-hand side) of the rewrite.",7,null],[12,"applier","","The applier (right-hand side) of the rewrite.",7,null],[3,"Runner","","Faciliates running rewrites over an `EGraph`.",null,null],[12,"egraph","","The `EGraph` used.",8,null],[12,"iterations","","Data accumulated over each `Iteration`.",8,null],[12,"roots","","The roots of expressions added by the `with_expr` method,…",8,null],[12,"stop_reason","","Why the `Runner` stopped. This will be `None` if it hasn\'t…",8,null],[12,"hooks","","The hooks added by the `with_hook` method, in insertion…",8,null],[3,"Iteration","","Data generated by running a `Runner` one iteration.",null,null],[12,"egraph_nodes","","The number of enodes in the egraph at the start of this…",9,null],[12,"egraph_classes","","The number of eclasses in the egraph at the start of this…",9,null],[12,"applied","","A map from rule name to number of times it was newly…",9,null],[12,"hook_time","","Seconds spent running hooks.",9,null],[12,"search_time","","Seconds spent searching in this iteration.",9,null],[12,"apply_time","","Seconds spent applying rules in this iteration.",9,null],[12,"rebuild_time","","Seconds spent `rebuild`ing the egraph in this iteration.",9,null],[12,"total_time","","Total time spent in this iteration, including data…",9,null],[12,"data","","The user provided annotation for this iteration",9,null],[12,"n_rebuilds","","The number of rebuild iterations done after this iteration…",9,null],[12,"stop_reason","","If the runner stopped on this iterations, this is the reason",9,null],[3,"SimpleScheduler","","A very simple `RewriteScheduler` that runs every rewrite…",null,null],[3,"BackoffScheduler","","A `RewriteScheduler` that implements exponentional rule…",null,null],[3,"Subst","","A substitition mapping `Var`s to eclass `Id`s.",null,null],[3,"Var","","A variable for use in `Pattern`s or `Subst`s.",null,null],[3,"Symbol","","An interned string.",null,null],[4,"ENodeOrVar","","The language of `Pattern`s.",null,null],[13,"ENode","","An enode from the underlying `Language`",10,null],[13,"Var","","A pattern variable",10,null],[4,"StopReason","","Error returned by `Runner` when it stops.",null,null],[13,"Saturated","","The egraph saturated, i.e., there was an iteration where…",11,null],[13,"IterationLimit","","The iteration limit was hit. The data is the iteration…",11,null],[13,"NodeLimit","","The enode limit was hit. The data is the enode limit.",11,null],[13,"TimeLimit","","The time limit was hit. The data is the time limit in…",11,null],[13,"Other","","Some other reason to stop.",11,null],[5,"merge_if_different","","Replace the first with second value if they are different…",null,[[["partialeq",8]]]],[0,"tutorials","","A Guide-level Explanation of `egg``egg` is a e-graph…",null,null],[0,"_01_background","egg::tutorials","Concepts: e-graphs and equality saturationAn e-graph is a…",null,null],[0,"_02_getting_started","","My first `egg` 🐣This tutorial is aimed at getting you up…",null,null],[11,"to_dot","egg","Writes the `Dot` to a .dot file with the given filename.…",12,[[],["result",6]]],[11,"to_png","","Renders the `Dot` to a .png file with the given filename.…",12,[[],["result",6]]],[11,"to_svg","","Renders the `Dot` to a .svg file with the given filename.…",12,[[],["result",6]]],[11,"to_pdf","","Renders the `Dot` to a .pdf file with the given filename.…",12,[[],["result",6]]],[11,"run_dot","","Invokes `dot` with the given arguments, piping this…",12,[[],["result",6]]],[11,"run","","Invokes some program with the given arguments, piping this…",12,[[],["result",6]]],[11,"is_empty","","Returns `true` if the `eclass` is empty.",0,[[]]],[11,"len","","Returns the number of enodes in this eclass.",0,[[]]],[11,"iter","","Iterates over the enodes in this eclass.",0,[[]]],[11,"leaves","","Iterates over the childless enodes in this eclass.",0,[[]]],[11,"assert_unique_leaves","","Asserts that the childless enodes in this eclass are unique.",0,[[]]],[11,"new","","Creates a new, empty `EGraph` with the given `Analysis`",1,[[]]],[11,"classes","","Returns an iterator over the eclasses in the egraph.",1,[[]]],[11,"classes_mut","","Returns an mutating iterator over the eclasses in the…",1,[[]]],[11,"is_empty","","Returns `true` if the egraph is empty",1,[[]]],[11,"total_size","","Returns the number of enodes in the `EGraph`.",1,[[]]],[11,"total_number_of_nodes","","Iterates over the classes, returning the total number of…",1,[[]]],[11,"number_of_classes","","Returns the number of eclasses in the egraph.",1,[[]]],[11,"find","","Canonicalizes an eclass id.",1,[[["id",3]],["id",3]]],[11,"dot","","Creates a `Dot` to visualize this egraph. See `Dot`.",1,[[],["dot",3]]],[11,"add_expr","","Adds a `RecExpr` to the `EGraph`.",1,[[["recexpr",3]],["id",3]]],[11,"lookup","","Lookup the eclass of the given enode.",1,[[],[["option",4],["id",3]]]],[11,"add","","Adds an enode to the `EGraph`.",1,[[],["id",3]]],[11,"equivs","","Checks whether two `RecExpr`s are equivalent. Returns a…",1,[[["recexpr",3]],[["vec",3],["id",3]]]],[11,"check_goals","","Panic if the given eclass doesn\'t contain the given patterns",1,[[["id",3]]]],[11,"union","","Unions two eclasses given their ids.",1,[[["id",3]]]],[11,"dump","","Returns a more debug-able representation of the egraph.",1,[[]]],[11,"rebuild","","Restores the egraph invariants of congruence and enode…",1,[[]]],[11,"new","","Create a new `Extractor` given an `EGraph` and a…",13,[[["egraph",3]]]],[11,"find_best","","Find the cheapest (lowest cost) represented `RecExpr` in…",13,[[["id",3]]]],[11,"find_best_cost","","Find the cost of the term that would be extracted from…",13,[[["id",3]]]],[11,"add","","Adds a given enode to this `RecExpr`. The enode\'s children…",14,[[],["id",3]]],[11,"pretty","","Pretty print with a maximum line length.",14,[[],["string",3]]],[11,"new","","Create an enode with the given string and children",2,[[["vec",3],["id",3]]]],[11,"leaf","","Create childless enode with the given string",2,[[]]],[11,"vars","","Returns a list of the `Var`s in this pattern.",3,[[],[["var",3],["vec",3]]]],[11,"pretty","","Pretty print this pattern as a sexp with the given width",3,[[],["string",3]]],[11,"name","","Returns the name of the rewrite.",7,[[]]],[11,"new","","Create a new `Rewrite`. You typically want to use the…",7,[[],[["result",4],["string",3]]]],[11,"search","","Call `search` on the `Searcher`.",7,[[["egraph",3]],[["vec",3],["searchmatches",3]]]],[11,"apply","","Call `apply_matches` on the `Applier`.",7,[[["egraph",3]],[["vec",3],["id",3]]]],[11,"parse","","Create a ConditionEqual by parsing two pattern strings.",5,[[]]],[11,"new","","Create a new `Runner` with the given analysis and default…",8,[[]]],[11,"with_iter_limit","","Sets the iteration limit. Default: 30",8,[[]]],[11,"with_node_limit","","Sets the egraph size limit (in enodes). Default: 10,000",8,[[]]],[11,"with_time_limit","","Sets the runner time limit. Default: 5 seconds",8,[[["duration",3]]]],[11,"with_hook","","Add a hook to instrument or modify the behavior of a…",8,[[]]],[11,"with_scheduler","","Change out the `RewriteScheduler` used by this `Runner`.…",8,[[]]],[11,"with_expr","","Add an expression to the egraph to be run.",8,[[["recexpr",3]]]],[11,"with_egraph","","Replace the `EGraph` of this `Runner`.",8,[[["egraph",3]]]],[11,"run","","Run this `Runner` until it stops. After this, the field…",8,[[]]],[11,"print_report","","Prints some information about a runners run.",8,[[]]],[11,"with_initial_match_limit","","Set the initial match limit after which a rule will be…",15,[[]]],[11,"with_ban_length","","Set the initial ban length. Default: 5 iterations",15,[[]]],[11,"do_not_ban","","Never ban a particular rule.",15,[[]]],[11,"rule_match_limit","","Set the initial match limit for a rule.",15,[[]]],[11,"rule_ban_length","","Set the initial ban length for a rule.",15,[[]]],[11,"with_capacity","","Create a `Subst` with the given initial capacity",16,[[]]],[11,"insert","","Insert something, returning the old `Id` if present.",16,[[["var",3],["id",3]],[["option",4],["id",3]]]],[11,"get","","Retrieve a `Var`, returning `None` if not present.",16,[[["var",3]],[["option",4],["id",3]]]],[11,"as_str","","Get the string that this symbol represents",17,[[]]],[6,"PatternAst","","A `RecExpr` that represents a `Pattern`.",null,null],[8,"CostFunction","","A cost function that can be used by an `Extractor`.",null,null],[16,"Cost","","The `Cost` type. It only requires `PartialOrd` so you can…",18,null],[10,"cost","","Calculates the cost of an enode whose children are `Cost`s.",18,[[]]],[11,"cost_rec","","Calculates the total cost of a `RecExpr`.",18,[[["recexpr",3]]]],[8,"Language","","Trait that defines a Language whose terms will be in the…",null,null],[10,"matches","","Returns true if this enode matches another enode. This…",19,[[]]],[10,"children","","Return a slice of the children `Id`s.",19,[[]]],[10,"children_mut","","Return a mutable slice of the children `Id`s.",19,[[]]],[11,"for_each","","Runs a given function on each child `Id`.",19,[[["fnmut",8]]]],[11,"for_each_mut","","Runs a given function on each child `Id`, allowing…",19,[[["fnmut",8]]]],[11,"display_op","","Returns something that will print the operator.",19,[[],["display",8]]],[11,"from_op_str","","Given a string for the operator and the children, tries to…",19,[[["vec",3],["id",3]],[["result",4],["string",3]]]],[11,"len","","Returns the number of the children this enode has.",19,[[]]],[11,"is_leaf","","Returns true if this enode has no children.",19,[[]]],[11,"update_children","","Runs a given function to replace the children.",19,[[["fnmut",8]]]],[11,"map_children","","Creates a new enode with children determined by the given…",19,[[["fnmut",8]]]],[11,"fold","","Folds over the children, given an initial accumulator.",19,[[]]],[11,"to_recexpr","","Make a `RecExpr` converting this enodes children to…",19,[[],["recexpr",3]]],[8,"LanguageChildren","","A marker that defines acceptable children types for…",null,null],[11,"is_empty","","Checks if there are no children.",20,[[]]],[10,"len","","Returns the number of children.",20,[[]]],[10,"can_be_length","","Checks if n is an acceptable number of children for this…",20,[[]]],[10,"from_vec","","Create an instance of this type from a `Vec<Id>`, with the…",20,[[["vec",3],["id",3]]]],[10,"as_slice","","Returns a slice of the children `Id`s.",20,[[]]],[10,"as_mut_slice","","Returns a mutable slice of the children `Id`s.",20,[[]]],[8,"Analysis","","Arbitrary data associated with an `EClass`.",null,null],[16,"Data","","The per-`EClass` data for this analysis.",21,null],[10,"make","","Makes a new `Analysis` for a given enode `Analysis`.",21,[[["egraph",3]]]],[11,"pre_union","","An optional hook that allows inspection before a `union`…",21,[[["egraph",3],["id",3]]]],[10,"merge","","Defines how to merge two `Data`s when their containing…",21,[[]]],[11,"modify","","A hook that allows the modification of the `EGraph`",21,[[["egraph",3],["id",3]]]],[8,"Applier","","The righthand side of a `Rewrite`.",null,null],[11,"apply_matches","","Apply many substititions.",22,[[["egraph",3]],[["vec",3],["id",3]]]],[10,"apply_one","","Apply a single substitition.",22,[[["id",3],["subst",3],["egraph",3]],[["vec",3],["id",3]]]],[11,"vars","","Returns a list of variables that this Applier assumes are…",22,[[],[["var",3],["vec",3]]]],[8,"Condition","","A condition to check in a `ConditionalApplier`.",null,null],[10,"check","","Check a condition.",23,[[["id",3],["subst",3],["egraph",3]]]],[11,"vars","","Returns a list of variables that this Condition assumes…",23,[[],[["var",3],["vec",3]]]],[8,"Searcher","","The lefthand side of a `Rewrite`.",null,null],[10,"search_eclass","","Search one eclass, returning None if no matches can be…",24,[[["egraph",3],["id",3]],[["searchmatches",3],["option",4]]]],[11,"search","","Search the whole `EGraph`, returning a list of all the…",24,[[["egraph",3]],[["vec",3],["searchmatches",3]]]],[10,"vars","","Returns a list of the variables bound by this Searcher",24,[[],[["var",3],["vec",3]]]],[8,"RewriteScheduler","","A way to customize how a `Runner` runs `Rewrite`s.",null,null],[11,"can_stop","","Whether or not the `Runner` is allowed to say it has…",25,[[]]],[11,"search_rewrite","","A hook allowing you to customize rewrite searching…",25,[[["egraph",3],["rewrite",3]],[["vec",3],["searchmatches",3]]]],[11,"apply_rewrite","","A hook allowing you to customize rewrite application…",25,[[["egraph",3],["searchmatches",3],["vec",3],["rewrite",3]]]],[8,"IterationData","","Custom data to inject into the `Iteration`s recorded by a…",null,null],[10,"make","","Given the current `Runner`, make the data to be put in…",26,[[["runner",3]]]],[14,"define_language","","A macro to easily create a `Language`.",null,null],[14,"rewrite","","A macro to easily make `Rewrite`s.",null,null],[14,"test_fn","","Make a test function",null,null],[11,"from","","",27,[[]]],[11,"into","","",27,[[]]],[11,"to_owned","","",27,[[]]],[11,"clone_into","","",27,[[]]],[11,"to_string","","",27,[[],["string",3]]],[11,"borrow","","",27,[[]]],[11,"borrow_mut","","",27,[[]]],[11,"try_from","","",27,[[],["result",4]]],[11,"try_into","","",27,[[],["result",4]]],[11,"type_id","","",27,[[],["typeid",3]]],[11,"equivalent","","",27,[[]]],[11,"from","","",12,[[]]],[11,"into","","",12,[[]]],[11,"to_string","","",12,[[],["string",3]]],[11,"borrow","","",12,[[]]],[11,"borrow_mut","","",12,[[]]],[11,"try_from","","",12,[[],["result",4]]],[11,"try_into","","",12,[[],["result",4]]],[11,"type_id","","",12,[[],["typeid",3]]],[11,"from","","",0,[[]]],[11,"into","","",0,[[]]],[11,"to_owned","","",0,[[]]],[11,"clone_into","","",0,[[]]],[11,"borrow","","",0,[[]]],[11,"borrow_mut","","",0,[[]]],[11,"try_from","","",0,[[],["result",4]]],[11,"try_into","","",0,[[],["result",4]]],[11,"type_id","","",0,[[],["typeid",3]]],[11,"from","","",1,[[]]],[11,"into","","",1,[[]]],[11,"to_owned","","",1,[[]]],[11,"clone_into","","",1,[[]]],[11,"borrow","","",1,[[]]],[11,"borrow_mut","","",1,[[]]],[11,"try_from","","",1,[[],["result",4]]],[11,"try_into","","",1,[[],["result",4]]],[11,"type_id","","",1,[[],["typeid",3]]],[11,"from","","",13,[[]]],[11,"into","","",13,[[]]],[11,"borrow","","",13,[[]]],[11,"borrow_mut","","",13,[[]]],[11,"try_from","","",13,[[],["result",4]]],[11,"try_into","","",13,[[],["result",4]]],[11,"type_id","","",13,[[],["typeid",3]]],[11,"from","","",28,[[]]],[11,"into","","",28,[[]]],[11,"borrow","","",28,[[]]],[11,"borrow_mut","","",28,[[]]],[11,"try_from","","",28,[[],["result",4]]],[11,"try_into","","",28,[[],["result",4]]],[11,"type_id","","",28,[[],["typeid",3]]],[11,"from","","",29,[[]]],[11,"into","","",29,[[]]],[11,"borrow","","",29,[[]]],[11,"borrow_mut","","",29,[[]]],[11,"try_from","","",29,[[],["result",4]]],[11,"try_into","","",29,[[],["result",4]]],[11,"type_id","","",29,[[],["typeid",3]]],[11,"from","","",14,[[]]],[11,"into","","",14,[[]]],[11,"to_owned","","",14,[[]]],[11,"clone_into","","",14,[[]]],[11,"to_string","","",14,[[],["string",3]]],[11,"borrow","","",14,[[]]],[11,"borrow_mut","","",14,[[]]],[11,"try_from","","",14,[[],["result",4]]],[11,"try_into","","",14,[[],["result",4]]],[11,"type_id","","",14,[[],["typeid",3]]],[11,"equivalent","","",14,[[]]],[11,"from","","",2,[[]]],[11,"into","","",2,[[]]],[11,"to_owned","","",2,[[]]],[11,"clone_into","","",2,[[]]],[11,"borrow","","",2,[[]]],[11,"borrow_mut","","",2,[[]]],[11,"try_from","","",2,[[],["result",4]]],[11,"try_into","","",2,[[],["result",4]]],[11,"type_id","","",2,[[],["typeid",3]]],[11,"equivalent","","",2,[[]]],[11,"from","","",3,[[]]],[11,"into","","",3,[[]]],[11,"to_owned","","",3,[[]]],[11,"clone_into","","",3,[[]]],[11,"to_string","","",3,[[],["string",3]]],[11,"borrow","","",3,[[]]],[11,"borrow_mut","","",3,[[]]],[11,"try_from","","",3,[[],["result",4]]],[11,"try_into","","",3,[[],["result",4]]],[11,"type_id","","",3,[[],["typeid",3]]],[11,"from","","",4,[[]]],[11,"into","","",4,[[]]],[11,"borrow","","",4,[[]]],[11,"borrow_mut","","",4,[[]]],[11,"try_from","","",4,[[],["result",4]]],[11,"try_into","","",4,[[],["result",4]]],[11,"type_id","","",4,[[],["typeid",3]]],[11,"from","","",5,[[]]],[11,"into","","",5,[[]]],[11,"borrow","","",5,[[]]],[11,"borrow_mut","","",5,[[]]],[11,"try_from","","",5,[[],["result",4]]],[11,"try_into","","",5,[[],["result",4]]],[11,"type_id","","",5,[[],["typeid",3]]],[11,"from","","",6,[[]]],[11,"into","","",6,[[]]],[11,"to_owned","","",6,[[]]],[11,"clone_into","","",6,[[]]],[11,"borrow","","",6,[[]]],[11,"borrow_mut","","",6,[[]]],[11,"try_from","","",6,[[],["result",4]]],[11,"try_into","","",6,[[],["result",4]]],[11,"type_id","","",6,[[],["typeid",3]]],[11,"from","","",7,[[]]],[11,"into","","",7,[[]]],[11,"to_owned","","",7,[[]]],[11,"clone_into","","",7,[[]]],[11,"borrow","","",7,[[]]],[11,"borrow_mut","","",7,[[]]],[11,"try_from","","",7,[[],["result",4]]],[11,"try_into","","",7,[[],["result",4]]],[11,"type_id","","",7,[[],["typeid",3]]],[11,"from","","",8,[[]]],[11,"into","","",8,[[]]],[11,"borrow","","",8,[[]]],[11,"borrow_mut","","",8,[[]]],[11,"try_from","","",8,[[],["result",4]]],[11,"try_into","","",8,[[],["result",4]]],[11,"type_id","","",8,[[],["typeid",3]]],[11,"from","","",9,[[]]],[11,"into","","",9,[[]]],[11,"to_owned","","",9,[[]]],[11,"clone_into","","",9,[[]]],[11,"borrow","","",9,[[]]],[11,"borrow_mut","","",9,[[]]],[11,"try_from","","",9,[[],["result",4]]],[11,"try_into","","",9,[[],["result",4]]],[11,"type_id","","",9,[[],["typeid",3]]],[11,"from","","",30,[[]]],[11,"into","","",30,[[]]],[11,"borrow","","",30,[[]]],[11,"borrow_mut","","",30,[[]]],[11,"try_from","","",30,[[],["result",4]]],[11,"try_into","","",30,[[],["result",4]]],[11,"type_id","","",30,[[],["typeid",3]]],[11,"from","","",15,[[]]],[11,"into","","",15,[[]]],[11,"borrow","","",15,[[]]],[11,"borrow_mut","","",15,[[]]],[11,"try_from","","",15,[[],["result",4]]],[11,"try_into","","",15,[[],["result",4]]],[11,"type_id","","",15,[[],["typeid",3]]],[11,"from","","",16,[[]]],[11,"into","","",16,[[]]],[11,"to_owned","","",16,[[]]],[11,"clone_into","","",16,[[]]],[11,"borrow","","",16,[[]]],[11,"borrow_mut","","",16,[[]]],[11,"try_from","","",16,[[],["result",4]]],[11,"try_into","","",16,[[],["result",4]]],[11,"type_id","","",16,[[],["typeid",3]]],[11,"equivalent","","",16,[[]]],[11,"from","","",31,[[]]],[11,"into","","",31,[[]]],[11,"to_owned","","",31,[[]]],[11,"clone_into","","",31,[[]]],[11,"to_string","","",31,[[],["string",3]]],[11,"borrow","","",31,[[]]],[11,"borrow_mut","","",31,[[]]],[11,"try_from","","",31,[[],["result",4]]],[11,"try_into","","",31,[[],["result",4]]],[11,"type_id","","",31,[[],["typeid",3]]],[11,"equivalent","","",31,[[]]],[11,"from","","",17,[[]]],[11,"into","","",17,[[]]],[11,"to_owned","","",17,[[]]],[11,"clone_into","","",17,[[]]],[11,"to_string","","",17,[[],["string",3]]],[11,"borrow","","",17,[[]]],[11,"borrow_mut","","",17,[[]]],[11,"try_from","","",17,[[],["result",4]]],[11,"try_into","","",17,[[],["result",4]]],[11,"type_id","","",17,[[],["typeid",3]]],[11,"equivalent","","",17,[[]]],[11,"from","","",10,[[]]],[11,"into","","",10,[[]]],[11,"to_owned","","",10,[[]]],[11,"clone_into","","",10,[[]]],[11,"borrow","","",10,[[]]],[11,"borrow_mut","","",10,[[]]],[11,"try_from","","",10,[[],["result",4]]],[11,"try_into","","",10,[[],["result",4]]],[11,"type_id","","",10,[[],["typeid",3]]],[11,"equivalent","","",10,[[]]],[11,"from","","",11,[[]]],[11,"into","","",11,[[]]],[11,"to_owned","","",11,[[]]],[11,"clone_into","","",11,[[]]],[11,"borrow","","",11,[[]]],[11,"borrow_mut","","",11,[[]]],[11,"try_from","","",11,[[],["result",4]]],[11,"try_into","","",11,[[],["result",4]]],[11,"type_id","","",11,[[],["typeid",3]]],[11,"cost","","",28,[[]]],[11,"cost","","",29,[[]]],[11,"matches","","",2,[[]]],[11,"children","","",2,[[]]],[11,"children_mut","","",2,[[]]],[11,"display_op","","",2,[[],["display",8]]],[11,"from_op_str","","",2,[[["vec",3],["id",3]],[["result",4],["string",3]]]],[11,"matches","","",10,[[]]],[11,"children","","",10,[[]]],[11,"children_mut","","",10,[[]]],[11,"from_op_str","","",10,[[["vec",3],["id",3]],[["result",4],["string",3]]]],[11,"display_op","","",10,[[],["display",8]]],[11,"len","","",27,[[]]],[11,"can_be_length","","",27,[[]]],[11,"from_vec","","",27,[[["vec",3],["id",3]]]],[11,"as_slice","","",27,[[]]],[11,"as_mut_slice","","",27,[[]]],[11,"search","","",3,[[["egraph",3]],[["vec",3],["searchmatches",3]]]],[11,"search_eclass","","",3,[[["egraph",3],["id",3]],[["searchmatches",3],["option",4]]]],[11,"vars","","",3,[[],[["var",3],["vec",3]]]],[11,"apply_one","","",3,[[["subst",3],["egraph",3],["id",3]],[["vec",3],["id",3]]]],[11,"vars","","",3,[[],[["var",3],["vec",3]]]],[11,"apply_matches","","",3,[[["egraph",3]],[["vec",3],["id",3]]]],[11,"apply_one","","",6,[[["id",3],["subst",3],["egraph",3]],[["vec",3],["id",3]]]],[11,"vars","","",6,[[],[["var",3],["vec",3]]]],[11,"check","","",5,[[["id",3],["subst",3],["egraph",3]]]],[11,"vars","","",5,[[],[["var",3],["vec",3]]]],[11,"can_stop","","",15,[[]]],[11,"search_rewrite","","",15,[[["egraph",3],["rewrite",3]],[["vec",3],["searchmatches",3]]]],[11,"as_ref","","",14,[[]]],[11,"from","","",14,[[["vec",3]]]],[11,"from","","",3,[[]]],[11,"from","","",3,[[["patternast",6]]]],[11,"from","","",17,[[]]],[11,"from","","",27,[[],["id",3]]],[11,"clone","","",0,[[],["eclass",3]]],[11,"clone","","",1,[[],["egraph",3]]],[11,"clone","","",14,[[],["recexpr",3]]],[11,"clone","","",2,[[],["symbollang",3]]],[11,"clone","","",3,[[],["pattern",3]]],[11,"clone","","",10,[[],["enodeorvar",4]]],[11,"clone","","",7,[[],["rewrite",3]]],[11,"clone","","",6,[[],["conditionalapplier",3]]],[11,"clone","","",11,[[],["stopreason",4]]],[11,"clone","","",9,[[],["iteration",3]]],[11,"clone","","",31,[[],["var",3]]],[11,"clone","","",16,[[],["subst",3]]],[11,"clone","","",17,[[],["symbol",3]]],[11,"clone","","",27,[[],["id",3]]],[11,"default","","",1,[[]]],[11,"default","","",14,[[]]],[11,"default","","",8,[[]]],[11,"default","","",15,[[]]],[11,"default","","",16,[[],["subst",3]]],[11,"default","","",27,[[],["id",3]]],[11,"cmp","","",14,[[["recexpr",3]],["ordering",4]]],[11,"cmp","","",2,[[["symbollang",3]],["ordering",4]]],[11,"cmp","","",10,[[["enodeorvar",4]],["ordering",4]]],[11,"cmp","","",31,[[["var",3]],["ordering",4]]],[11,"cmp","","",16,[[["subst",3]],["ordering",4]]],[11,"cmp","","",17,[[["symbol",3]],["ordering",4]]],[11,"cmp","","",27,[[["id",3]],["ordering",4]]],[11,"eq","","",14,[[["recexpr",3]]]],[11,"ne","","",14,[[["recexpr",3]]]],[11,"eq","","",2,[[["symbollang",3]]]],[11,"ne","","",2,[[["symbollang",3]]]],[11,"eq","","",3,[[["pattern",3]]]],[11,"ne","","",3,[[["pattern",3]]]],[11,"eq","","",10,[[["enodeorvar",4]]]],[11,"ne","","",10,[[["enodeorvar",4]]]],[11,"eq","","",31,[[["var",3]]]],[11,"ne","","",31,[[["var",3]]]],[11,"eq","","",16,[[["subst",3]]]],[11,"ne","","",16,[[["subst",3]]]],[11,"eq","","",17,[[["symbol",3]]]],[11,"ne","","",17,[[["symbol",3]]]],[11,"eq","","",27,[[["id",3]]]],[11,"ne","","",27,[[["id",3]]]],[11,"partial_cmp","","",14,[[["recexpr",3]],[["ordering",4],["option",4]]]],[11,"lt","","",14,[[["recexpr",3]]]],[11,"le","","",14,[[["recexpr",3]]]],[11,"gt","","",14,[[["recexpr",3]]]],[11,"ge","","",14,[[["recexpr",3]]]],[11,"partial_cmp","","",2,[[["symbollang",3]],[["ordering",4],["option",4]]]],[11,"lt","","",2,[[["symbollang",3]]]],[11,"le","","",2,[[["symbollang",3]]]],[11,"gt","","",2,[[["symbollang",3]]]],[11,"ge","","",2,[[["symbollang",3]]]],[11,"partial_cmp","","",10,[[["enodeorvar",4]],[["ordering",4],["option",4]]]],[11,"lt","","",10,[[["enodeorvar",4]]]],[11,"le","","",10,[[["enodeorvar",4]]]],[11,"gt","","",10,[[["enodeorvar",4]]]],[11,"ge","","",10,[[["enodeorvar",4]]]],[11,"partial_cmp","","",31,[[["var",3]],[["ordering",4],["option",4]]]],[11,"lt","","",31,[[["var",3]]]],[11,"le","","",31,[[["var",3]]]],[11,"gt","","",31,[[["var",3]]]],[11,"ge","","",31,[[["var",3]]]],[11,"partial_cmp","","",16,[[["subst",3]],[["ordering",4],["option",4]]]],[11,"lt","","",16,[[["subst",3]]]],[11,"le","","",16,[[["subst",3]]]],[11,"gt","","",16,[[["subst",3]]]],[11,"ge","","",16,[[["subst",3]]]],[11,"partial_cmp","","",17,[[["symbol",3]],[["ordering",4],["option",4]]]],[11,"lt","","",17,[[["symbol",3]]]],[11,"le","","",17,[[["symbol",3]]]],[11,"gt","","",17,[[["symbol",3]]]],[11,"ge","","",17,[[["symbol",3]]]],[11,"partial_cmp","","",27,[[["id",3]],[["ordering",4],["option",4]]]],[11,"lt","","",27,[[["id",3]]]],[11,"le","","",27,[[["id",3]]]],[11,"gt","","",27,[[["id",3]]]],[11,"ge","","",27,[[["id",3]]]],[11,"fmt","","",12,[[["formatter",3]],["result",6]]],[11,"fmt","","",0,[[["formatter",3]],["result",6]]],[11,"fmt","","",1,[[["formatter",3]],["result",6]]],[11,"fmt","","",14,[[["formatter",3]],["result",6]]],[11,"fmt","","",2,[[["formatter",3]],["result",6]]],[11,"fmt","","",3,[[["formatter",3]],["result",6]]],[11,"fmt","","",10,[[["formatter",3]],["result",6]]],[11,"fmt","","",4,[[["formatter",3]],["result",6]]],[11,"fmt","","",7,[[["formatter",3]],["result",6]]],[11,"fmt","","",6,[[["formatter",3]],["result",6]]],[11,"fmt","","",11,[[["formatter",3]],["result",6]]],[11,"fmt","","",9,[[["formatter",3]],["result",6]]],[11,"fmt","","",31,[[["formatter",3]],["result",6]]],[11,"fmt","","",16,[[["formatter",3]],["result",6]]],[11,"fmt","","",17,[[["formatter",3]],["result",6]]],[11,"fmt","","",27,[[["formatter",3]],["result",6]]],[11,"fmt","","",12,[[["formatter",3]],["result",6]]],[11,"fmt","","",14,[[["formatter",3]],["result",6]]],[11,"fmt","","",3,[[["formatter",3]],["result",6]]],[11,"fmt","","",31,[[["formatter",3]],["result",6]]],[11,"fmt","","",17,[[["formatter",3]],["result",6]]],[11,"fmt","","",27,[[["formatter",3]],["result",6]]],[11,"index","","",1,[[["id",3]]]],[11,"index","","",14,[[["id",3]]]],[11,"index","","",16,[[["var",3]]]],[11,"index_mut","","",1,[[["id",3]]]],[11,"index_mut","","",14,[[["id",3]]]],[11,"hash","","",14,[[]]],[11,"hash","","",2,[[]]],[11,"hash","","",10,[[]]],[11,"hash","","",31,[[]]],[11,"hash","","",16,[[]]],[11,"hash","","",17,[[]]],[11,"hash","","",27,[[]]],[11,"try_from","","",14,[[["pattern",3]],["result",4]]],[11,"from_str","","",14,[[],["result",4]]],[11,"from_str","","",3,[[],["result",4]]],[11,"from_str","","",31,[[],["result",4]]],[11,"from_str","","",17,[[],["result",4]]],[11,"cost_rec","","Calculates the total cost of a `RecExpr`.",18,[[["recexpr",3]]]],[11,"for_each","","Runs a given function on each child `Id`.",19,[[["fnmut",8]]]],[11,"for_each_mut","","Runs a given function on each child `Id`, allowing…",19,[[["fnmut",8]]]],[11,"display_op","","Returns something that will print the operator.",19,[[],["display",8]]],[11,"from_op_str","","Given a string for the operator and the children, tries to…",19,[[["vec",3],["id",3]],[["result",4],["string",3]]]],[11,"len","","Returns the number of the children this enode has.",19,[[]]],[11,"is_leaf","","Returns true if this enode has no children.",19,[[]]],[11,"update_children","","Runs a given function to replace the children.",19,[[["fnmut",8]]]],[11,"map_children","","Creates a new enode with children determined by the given…",19,[[["fnmut",8]]]],[11,"fold","","Folds over the children, given an initial accumulator.",19,[[]]],[11,"to_recexpr","","Make a `RecExpr` converting this enodes children to…",19,[[],["recexpr",3]]],[11,"is_empty","","Checks if there are no children.",20,[[]]],[11,"pre_union","","An optional hook that allows inspection before a `union`…",21,[[["egraph",3],["id",3]]]],[11,"modify","","A hook that allows the modification of the `EGraph`",21,[[["egraph",3],["id",3]]]],[11,"search","","Search the whole `EGraph`, returning a list of all the…",24,[[["egraph",3]],[["vec",3],["searchmatches",3]]]],[11,"apply_matches","","Apply many substititions.",22,[[["egraph",3]],[["vec",3],["id",3]]]],[11,"vars","","Returns a list of variables that this Applier assumes are…",22,[[],[["var",3],["vec",3]]]],[11,"vars","","Returns a list of variables that this Condition assumes…",23,[[],[["var",3],["vec",3]]]],[11,"can_stop","","Whether or not the `Runner` is allowed to say it has…",25,[[]]],[11,"search_rewrite","","A hook allowing you to customize rewrite searching…",25,[[["egraph",3],["rewrite",3]],[["vec",3],["searchmatches",3]]]],[11,"apply_rewrite","","A hook allowing you to customize rewrite application…",25,[[["egraph",3],["searchmatches",3],["vec",3],["rewrite",3]]]]],"p":[[3,"EClass"],[3,"EGraph"],[3,"SymbolLang"],[3,"Pattern"],[3,"SearchMatches"],[3,"ConditionEqual"],[3,"ConditionalApplier"],[3,"Rewrite"],[3,"Runner"],[3,"Iteration"],[4,"ENodeOrVar"],[4,"StopReason"],[3,"Dot"],[3,"Extractor"],[3,"RecExpr"],[3,"BackoffScheduler"],[3,"Subst"],[3,"Symbol"],[8,"CostFunction"],[8,"Language"],[8,"LanguageChildren"],[8,"Analysis"],[8,"Applier"],[8,"Condition"],[8,"Searcher"],[8,"RewriteScheduler"],[8,"IterationData"],[3,"Id"],[3,"AstSize"],[3,"AstDepth"],[3,"SimpleScheduler"],[3,"Var"]]}\
}');
addSearchOptions(searchIndex);initSearch(searchIndex);
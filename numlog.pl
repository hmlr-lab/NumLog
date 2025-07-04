%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Numlog: numerical learning and reasoning using ILP %%%%%%%%%%%%%%%%%%%%%%%%
%                                           Version: 2                                                  %
%                                    Main Author: Daniel Cyrus                                          %
%                            Learning numerical data using ILP and GMM                                  % 
%                                            The HMLR lab                                               %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(numlog, [learnFromFile/3]).

:-use_foreign_library('libnumlog.so').

:-op(500, xfy, user:(±)). 
:-op(500, fx, #). 

:-op(500, xfy, =>).
:- dynamic modeh/2, modeb/2.
:- dynamic pos/1.
:- dynamic neg/1.
%---------------------------------------------------------------
%-------------------Operator---------------
checkInRange(X, Value ± Range):-
    X =< Value + Range,
    X >= Value - Range.

inRange(X,Ranges):-
    number(X),
    include(checkInRange(X),Ranges,Filtered),
    length(Filtered,L),
    L > 0.

leq(X,Value):-
    number(X),
    X =< Value.

geq(X,Value):-
    number(X),
    X >= Value.
%=====================Find relations=============================
replace_in_list(_, _, [], []).
replace_in_list(Old, New, [Old|T], [New|T2]) :-
    replace_in_list(Old, New, T, T2).

replace_in_list(Old, New, [H|T], [H|T2]) :-
    H \= Old,
    replace_in_list(Old, New, T, T2).

groupGroupedExamples([],List,List).
groupGroupedExamples([Term-A-Values|T],List,Temp):-
     ((member(Term1-A1-Values1, List),A1==A) ->
     (append([Values1],[Values],Values2),
     append([Term1],[Term],Term2),
     replace_in_list(Term1-A1-Values1, Term2-A1-Values2,List,List1));
     append(List,[Term-A-Values],List1)),
     groupGroupedExamples(T,List1,Temp).

relations([],Rel,Rel).
relations([Terms-Var-Values|T],Rel,R):-
    findRelations(Terms,Values,Rel1),
    append(Rel,[Var=>Rel1],Rel2),
    relations(T,Rel2,R).

convertRelations(A => Preds, A => Goal) :-
    NewVar = _,
    build_preds(Preds, NewVar, Calls, Vars),
    build_comparisons(Vars, Comps),
    append(Calls, Comps, AllGoals),
    list_to_conj(AllGoals, Goal1),
    Goal2 = (relations(NewVar):-Goal1),
    copy_term(Goal2,Goal).

% build_preds(+PredList, +Subject, -Calls, -Vars)
build_preds([], _, [], []).
build_preds([Pred|Rest], A, [Call|Calls], [Var|Vars]) :-
    Call =.. [Pred, A, Var],
    build_preds(Rest, A, Calls, Vars).

% build_comparisons(+Vars, -Comparisons)
build_comparisons([_], []).
build_comparisons([V1, V2 | Rest], [V1 < V2 | Comps]) :-
    build_comparisons([V2 | Rest], Comps).

generateRelationTerms([],Rel,Rel).
generateRelationTerms([Var=>Terms|T],Rel,Rel2):-
    (length(Terms,L),L>1-> convertRelations(Var=>Terms,RelTerms),append(Rel,[RelTerms],Rel1);Rel1=Rel),
    generateRelationTerms(T,Rel1,Rel2).


relations(Ex, Rel) :-
   groupGroupedExamples(Ex,[],GEx),
   relations(GEx,[],Relations),
   generateRelationTerms(Relations,[],Rel).
    
%-------------------------------------------

combination([], []).
combination([H|T], [H|Comb]) :-  
    combination(T, Comb).
combination([_|T], Comb) :-  
    combination(T, Comb).


member_in_list([], _, _) :- fail.
member_in_list([H|_], List2,Parameters) :- nth0(Index, List2, H),nth0(Index, Parameters, in), !.
%member(H, List2), !.
member_in_list([_|T], List2,Parameters) :- member_in_list(T, List2,Parameters).

getPredicate2(Ar,Bag):-
    findall(G=>Args=>Par, (modeb(L/A,Par),length(Args,A),G =..[L|Args],call(G),member_in_list(Ar, Args,Par)), Bag).

separate_pairs([], [], [],[]).
separate_pairs([G=>B=>P | Pairs], [G | Gs], [B | Bs],[P|Ps]) :-
    separate_pairs(Pairs, Gs, Bs,Ps).

not_member(_, []).
not_member(X, [H|T]) :- X \= H, not_member(X, T).

filter_not_in_list(_, [], []).
filter_not_in_list(List1, [H|T], [H|Result]) :-
    not_member(H, List1),
    filter_not_in_list(List1, T, Result).
filter_not_in_list(List1, [_|T], Result) :-
    filter_not_in_list(List1, T, Result).

bottomClause([],Predicates,Arities,Predicates,Arities).
bottomClause(Arity,Predicates,Arities,Predicates1,Arities1):-
    getPredicate2(Arity,G),
    separate_pairs(G,Gs,Bs,Ps),
    flatten(Bs, FlatList_Bs),
    flatten(Ps, FlatList_Ps),

    findall(NB, (length(FlatList_Bs,Lb),between(1,Lb,N),((nth1(N, FlatList_Ps, const),nth1(N,FlatList_Bs,(NB1)),NB=(#NB1));
                                                         (nth1(N, FlatList_Ps, out),nth1(N,FlatList_Bs,NB))
                                                         )),FlatList),
                                                         
                                                        
    append(Predicates,Gs,Per1),
    append(Arity,Arities,Ar1),
    sort(Ar1,Ar_1),
    once(filter_not_in_list(Ar_1,FlatList,NewBs)),
    bottomClause(NewBs,Per1,Ar_1,Predicates1,Arities1).

getTrueVal(L,L2,X,Val):-
    (member(#X,L)->
    Val = X;
    (number(X)->
    Val = X;
    nth0(Index,L,X),nth0(Index,L2,Val))).


add_variable([],_,_,List,List).
add_variable([H|T],List1,List2,List,NewList):-
    
    H =.. [Cl|Args],
    maplist(getTrueVal(List1,List2),Args,Vars),
    NewH =..[Cl|Vars],
    append(List,[NewH],List3),
    add_variable(T,List1,List2,List3,NewList).

generateBottomClause([],L,L).
generateBottomClause([A|T],L,L1):-
    A =.. [_|Args],
    once(bottomClause(Args,[],[],Literals,Arities)),
    length(Arities,Len),
    length(Arr,Len),
    append([A],Literals,AP),
    add_variable(AP,Arities,Arr,[],NewList),
    append(L,[NewList],L2),
    generateBottomClause(T,L2,L1).
%--------------------Recursive Check----------------------------------------------
ifRecursive(List,Pattern):-
    find_repeating_pattern(List,Pattern),
    length(List,L1),
    length(Pattern,L2),
    L1\=L2->true;fail.

find_repeating_pattern(List, Pattern) :-
        length(List, N),
        between(1, N, L),  
        0 is N mod L,      
        length(Pattern, L),
        append(Pattern, Rest, List),
        repeated_pattern(Pattern, Rest), !. 

repeated_pattern(_, []).
repeated_pattern(Pattern, List) :-
    append(Pattern, Rest, List),
    repeated_pattern(Pattern, Rest).
%------------------Generate hypothesis---------------------
%%%%%%%%%%%%%%%%%%%Subsumption%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


combinations_conjunction(List,N, Subset) :-
    combination(List, Subset),
    length(Subset, N).      

%list_to_conj([], none).               % Empty list becomes true (identity for conjunction)
list_to_conj([X], X):-!.                 % Single element stays as is
list_to_conj([H|T], (H,Rest)) :-      % Multiple elements become a conjunction
    list_to_conj(T, Rest).

member_addr(X, [Y|_]) :-
    X == Y. 
member_addr(X, [_|Ys]) :-
    member_addr(X, Ys).

ifAll([], _). 
ifAll([X|Xs], B) :-
    member_addr(X, B),  
    ifAll(Xs, B). 

getAllArgs([],A,B):-flatten(A,B).
getAllArgs([H|T],Args,A):-
   
    (H =.. [_|BArgs] ->
    append(Args,[BArgs],A1);
    A1=Args),
    getAllArgs(T,A1,A).

% flatten_conjunction((A,B), List) :-
%     !,
%     flatten_conjunction(A, ListA),
%     flatten_conjunction(B, ListB),
%     append(ListA, ListB, List).
% flatten_conjunction(A, [A]).
countSingleArgs([],_,LC,LC).
countSingleArgs([H|T],L,LC,LC1):-
   
    (member(H, L) ->
    (nth0(Index, L, H),
    nth0(Index, LC, Count),
    NewCount is Count + 1,
    replace_in_list(Count, NewCount, LC, NewLC),NewL=L);
    (append(L, [H], NewL),
    (var(H) -> append(LC, [1], NewLC);append(LC, [2], NewLC)))),
    countSingleArgs(T, NewL, NewLC,LC1).


greater_than_one(X) :- X > 1.
head_connectedness(Args,Body):-
    %flatten_conjunction(Body,Body1),
    getAllArgs(Body,[],BArgs),
    append(Args, BArgs, AllArgs),
    countSingleArgs(AllArgs,[],[],Counts),
    maplist(greater_than_one,Counts).

   

%---------------------------------------------------------
refinementBottomClauses([],_,NewBC,NewBC).
refinementBottomClauses([H|T],Filtered,NewBC,Temp):-
    (member(H, Filtered)->
    (H =.. [Cl,Var|_],
    H1 =..[Cl,Var],
    append(NewBC,[H1],NewBC1));
    append(NewBC, [H], NewBC1)),    
    refinementBottomClauses(T,Filtered,NewBC1,Temp).

groupRefinementBottomClauses([],_,NewBC,NewBC).
groupRefinementBottomClauses([H|T],Filtered,NewBC,Temp):-
    refinementBottomClauses(H,Filtered,[],NewBC1),
    append(NewBC,[NewBC1],NewBC2),
    groupRefinementBottomClauses(T,Filtered,NewBC2,Temp).

% Main predicate
cluster_vars_by_numbers(Terms, Grouped,Filtered) :-
    include(only_numbers, Terms, Filtered),     % Keep only a(_, Number) where Number is numeric
    collect_pairs(Filtered, Pairs),             % Convert to [Var-Value, ...]
    sort(0, @=<, Pairs, Ps),
    group_pairs_by_key(Ps, Grouped).

% Keep only terms with numeric values
only_numbers(T) :-
    T =.. [_, _, Value],
    number(Value).
% Turn a(Var, Val) into Var-Val
collect_pairs([], []).
collect_pairs([H|T], [Term - Var - Val|Rest]) :-
    H =.. [Term, Var, Val],  % Extract Var and Val
    collect_pairs(T, Rest).

bottomClausePrint1(Term,Copy) :-
    copy_term(Term, Copy),
    numbervars(Copy, 0, _, [singletons(true)]).

bottomClausePrint(Term, Numbered) :-
        copy_term(Term, Copy),
        numbervars(Copy, 0, _),  % Number all variables in the copy
        Numbered = Copy.                     % Return the numbered version
    

analyseNumbers(Pos,Neg,F,Relations,NewBC):-
        flatten(Pos,FlatPos),
        flatten(Neg,FlatNeg),
        cluster_vars_by_numbers(FlatPos,GroupedPos,Filtered),
        cluster_vars_by_numbers(FlatNeg,GroupedNeg,_),
        groupRefinementBottomClauses(Pos,Filtered,[],NewBC),
        %write(NewBC),nl,
         %==========relations should be somewhere here.
        relations(GroupedPos,Relations),
        %write(Relations),nl,
        extractAndProcessGMM(GroupedPos,GroupedNeg,[],F).



    inRangeStandardisation([],Ranges,Ranges).
    inRangeStandardisation([H|T],Ranges,Temp):-
            (H \= []->
            (sum_list(H, Sum),
            length(H, Len),
            min_list(H, Min),
            Mean is Sum / Len,
            Range is Mean -  Min,
            append(Ranges, [Mean ± Range], Ranges1));
            Ranges1=Ranges),
            inRangeStandardisation(T,Ranges1,Temp).
        
        
    make_list(A, B, C, D) :-
            include(nonvar, [A, B, C], D).   
    
list_to_disjunction([X], X) :- !.
list_to_disjunction([H|T], (H ; Rest)) :-
            list_to_disjunction(T, Rest).
    
extractAndProcessGMM([],_,FunctionsInvention,FunctionsInvention).    
extractAndProcessGMM([Term-Var-ValuePos|RestPos],Neg,FunctionsInvention,Rest):-
        ((nth0(Index, Neg, Term-VarNeg-_),Var==VarNeg)->
        nth0(Index, Neg, _-_-N1),
        ValueNeg=N1;
        ValueNeg=[]),
        findThresholds(ValuePos,ValueNeg,Leq,InRange,Geq),
        TermHead =.. [Term,HeadVar,NewVar],
        (Leq \= [] -> max_list(Leq, Max),ThrL = leq(NewVar,Max);ThrL=_),
        (InRange \= [[]] -> inRangeStandardisation(InRange,[],Threshold),(Threshold\=[]->ThrI = inRange(NewVar,Threshold);ThrI=_) ;ThrI=_),
        (Geq \= [] -> min_list(Geq, Min),ThrG = geq(NewVar,Min);ThrG=_),   
        make_list(ThrL, ThrI, ThrG, Body),
        (Body \= [] -> (Head =.. [Term,HeadVar],list_to_disjunction(Body,BD), FunctionsInvention1 = (Head :- TermHead,BD),copy_term(FunctionsInvention1,FunctionsInvention2),append(FunctionsInvention,[Var => FunctionsInvention2],Rest1));Rest1=FunctionsInvention),
        extractAndProcessGMM(RestPos,Neg,Rest1,Rest).
%--------------------------Hypothesis--------------------------------

entailExamples([],List,List).
entailExamples([F|NEx],Temp,List):-
    %F =.. [Head|_],
    %listing(user:Head/2),
    (call(F) ->
        %write('--->yes<---'),
        append(Temp,[F],Temp1);
        %write('no'),
        Temp1=Temp),
        entailExamples(NEx,Temp1,List).

%-------------------------------------------------      
% Entry point
restore_vars(Clause, Restored) :-
    empty_assoc(VarMap),
    restore_term(Clause, Restored, VarMap, _).

% Base case: constant or atom
restore_term(Term, Term, Map, Map) :-
    atomic(Term),
    !.

% Case: variable in form '$VAR'(N)
restore_term('$VAR'(N), Var, MapIn, MapOut) :-
    ( get_assoc(N, MapIn, Var) ->
        MapOut = MapIn
    ; put_assoc(N, MapIn, Var, MapOut)
    ).

% Case: compound term
restore_term(Term, NewTerm, MapIn, MapOut) :-
    compound(Term),
    Term =.. [F | Args],
    restore_args(Args, NewArgs, MapIn, MapOut),
    NewTerm =.. [F | NewArgs].

% Helper: restore list of arguments
restore_args([], [], Map, Map).
restore_args([H|T], [H2|T2], MapIn, MapOut) :-
    restore_term(H, H2, MapIn, MapMid),
    restore_args(T, T2, MapMid, MapOut).
    
%-------------------------------------------------

checkCoverage(Clause,InvF,Rel,Pos,Neg,Rule):-
    restore_vars(Clause, NewClause),
    %copy_term(NewClause, NewClause1),
    assertz(NewClause),
   
    entailExamples(Pos,[],PosList),
    entailExamples(Neg,[],NegList),
    retract(NewClause),
    Rule = rule(Clause, PosList, NegList,InvF,Rel).

findRelevantFunctions([],_,[]).
findRelevantFunctions([H|T],InvF,[Bag|Rest]):-
    H =.. [_|Args],
    length(Args,Len),
    (Len = 1 ->
        nth0(0,Args,A1),
        findall(C,(nth0(_,InvF,(A=>C)),A==A1),Bag);
        Bag = []),
        findRelevantFunctions(T,InvF,Rest).

get_at_indices([], _, []).
get_at_indices([I|Is], List, [Elem|Rest]) :-
    nth0(I, List, Elem),
    get_at_indices(Is, List, Rest).

generateRules(_,_,_,_,_,[],Rule,Rule).
generateRules(BCs,InvF,Exs,NExs,Relations,[H|T],Rule,Rule1):-
    %between(1,3,N),  % add max clause here
    %combinations_conjunction(Body,N,B),
    get_at_indices(H,BCs,B),
   
    BCs = [Head|_],
    Head =.. [_|HArgs],
    
    (head_connectedness(HArgs,B)-> %head_connectedness
    (
  
    list_to_conj(B, Conj),
    
    Clause = (Head:-Conj),

    findRelevantFunctions(B,InvF,FilteredInvF),
    findRelevantFunctions(B,Relations,FilteredRelF),
    flatten(FilteredInvF,FlatFilteredInvF),
    flatten(FilteredRelF,FlatFilteredRelF),
    %%write(Clause),write('-->'),write(FlatFilteredInvF),nl,
    assertAll(FlatFilteredInvF),
    assertAll(FlatFilteredRelF),
    checkCoverage(Clause,FlatFilteredInvF,FlatFilteredRelF,Exs,NExs,Rule2),
    append(Rule,[Rule2],Rule3),
    retractAll(FlatFilteredRelF),
    retractAll(FlatFilteredInvF)
    );
    Rule3=Rule),
    generateRules(BCs,InvF,Exs,NExs,Relations,T,Rule3,Rule1).


hypothesisSpace(Exs,NExs,InvF,Relations,BCs,Rules):-
    length(BCs,Len),
    combinations(Len,3,Comb),
   
    generateRules(BCs,InvF,Exs,NExs,Relations,Comb ,[],Rules).

%------------------Best rule from hypothesis space----------------

%====================================
% select_best_rule(Rules, BestRule)
% Selects the best rule from a list of rules based on:
% 1. Highest positive coverage
% 2. Lowest negative coverage
% 3. Lowest complexity
select_best_rule([Rule], Rule) :- !.
select_best_rule([Rule|Rules], BestRule) :-
    select_best_rule(Rules, BestOfRest),
    compare_rules(Rule, BestOfRest, BestRule).

% compare_rules(Rule1, Rule2, BestRule)
% Compares two rules and selects the better one based on criteria
compare_rules(Rule1, Rule2, Rule1) :-
    rule_metrics(Rule1, Pos1, Neg1, Comp1),
    rule_metrics(Rule2, Pos2, Neg2, Comp2),
  
    ( Pos1 > Pos2;
      Pos1 = Pos2, Neg1 < Neg2;
      Pos1 = Pos2, Neg1 = Neg2, Comp1 < Comp2 ), !.
compare_rules(_, Rule2, Rule2).

% rule_metrics(Rule, PosCount, NegCount, Complexity)
% Computes metrics for a rule:
% - PosCount: Number of positive examples
% - NegCount: Number of negative examples
% - Complexity: Number of literals in the body (excluding true)
rule_metrics(rule((_:-Body), Pos, Neg,_,_), PosCount, NegCount, Complexity) :-
    length(Pos, PosCount),
    length(Neg, NegCount),
    body_complexity(Body, Complexity).

% body_complexity(Body, Complexity)
% Counts the number of literals in the body, excluding 'true'
body_complexity(true, 0) :- !.
body_complexity((Literal,Rest), Complexity) :-
    !, body_complexity(Rest, RestComplexity),
    ( Literal = true -> Complexity = RestComplexity;
      Complexity is RestComplexity + 1 ).
body_complexity(Literal, 1) :-
    Literal \= true.

%----------------------------------------------------------
assertAll([]).
assertAll([H|T]):-
    assertz(H),
    assertAll(T).

retractAll([]).
retractAll([H|T]):-
    retract(H),
    retractAll(T).

learnFromFile(BKFile,ExampleFile,BiasFile):-
    
    consult(BKFile),
    consult(ExampleFile),
    consult(BiasFile),
    
    writeln('Processing file and numerical values...'),
    
    modeh(Head/HA,_),

    findall(F,(length(V,HA),F=..[Head|V],pos(F)),ArrPos),
    findall(F,(length(V,HA),F=..[Head|V],neg(F)),ArrNeg),

    generateBottomClause(ArrPos,[],BCs),
    generateBottomClause(ArrNeg,[],BCs1),
    maplist(bottomClausePrint,BCs,PBC),
    maplist(bottomClausePrint,BCs1,NBC),
    
    analyseNumbers(PBC,NBC,InventedFunctions,Relations,NewBC),
    
    maplist(hypothesisSpace(ArrPos,ArrNeg,InventedFunctions,Relations),NewBC,Hypos),
    
    flatten(Hypos,FlatHypos),
   
    select_best_rule(FlatHypos, H),
    H = rule((FinalRule),_,_,InvF,Rel),
    writeln('Final Rule:'),
    write(FinalRule),write('.'),nl,
    maplist(writeln,InvF),
    maplist(writeln,Rel).
    %maplist(bottomClausesPrint,FinalRule,FinalRule1),
    %write(FinalRule1).  



%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Numlog: numerical learning and reasoning using ILP %%%%%%%%%%%%%%%%%%%%%%%%
%                                           Version: 2                                                  %
%                                    Main Author: Daniel Cyrus                                          %
%                            Learning numerical data using ILP and GMM                                  % 
%                                            The HMLR lab                                               %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(numlog, [learnFromFile/3]).

:- use_module(library(clpfd)).
:- use_module(library(assoc)).
:- use_foreign_library('libnumlog.so').

%:-op(500, xfy, user:(±)). 
:-op(500, xfy, user:(μ)). 
:-op(500, xfy, user:(σ)). 
:-op(500, fx, #). 

:-op(500, xfy, =>).
:- dynamic modeh/2, modeb/2.
:- dynamic pos/1.
:- dynamic neg/1.
%---------------------------------------------------------------
% def gaussian_pdf(x, mean, var):
%     # Handle very small/zero variance
%     if var <= 1e-6:
%         # Fallback: distance-based score (higher when closer)
%         dist = abs(x - mean)
%         return 1.0 / (1.0 + dist)
%     else:
%         coeff = 1.0 / np.sqrt(2 * np.pi * var)
%         exponent = np.exp(-((x - mean) ** 2) / (2 * var))
%         return coeff * exponent

% # -----------------------------
% # Assign cluster to a value
% # -----------------------------
% def assign_cluster(x, clusters):
%     scores = []
%     for c in clusters:
%         score = gaussian_pdf(x, c["mean"], c["variance"])
%         scores.append((c["id"], c["polarity"], score))
%     # pick cluster with max score
%     best = max(scores, key=lambda t: t[2])
%     return best  # (id, polarity, score)
%-------------------Operator---------------
gaussian_pdf(X, (μ(Mean),σ(Var)), Score) :-
    (Var =< 1e-6 ->
        Dist is abs(X - Mean),
        Score is 1.0 / (1.0 + Dist)
    ;
        Coeff is 1.0 / sqrt(2 * pi * Var),
        Exponent is exp(-((X - Mean) ** 2) / (2 * Var)),
        Score is Coeff * Exponent
    ).

inCluster(X,pos(PosGauss),neg(NegGauss)):-
    number(X),
    maplist(gaussian_pdf(X),PosGauss,PosScors),
    maplist(gaussian_pdf(X),NegGauss,NegScors),
    max_list(PosScors,MaxPos),
    max_list(NegScors,MaxNeg),
    MaxPos > MaxNeg.

%=====================Find relations=============================
replace_in_list(_, _, [], []).
replace_in_list(Old, New, [Old|T], [New|T2]) :-
    replace_in_list(Old, New, T, T2).

replace_in_list(Old, New, [H|T], [H|T2]) :-
    not(H == Old),
    replace_in_list(Old, New, T, T2).
%%%%%%%%%%%-------------------------MAY NEED TO CHANGE HERE-----------------%%%%%%%%%%%%
groupGroupedExamples([],List,List).
groupGroupedExamples([Term-A-Values|T],List,Temp):-
     ((member(Term1-A1-Values1, List),A1==A) ->
     (
     flatten(Term1,FTerm1),
     append(Values1,[Values],Values2),
     append(FTerm1,[Term],Term2),
     replace_in_list(Term1-A1-Values1, Term2-A1-Values2,List,List1));
     append(List,[Term-A-[Values]],List1)),
     groupGroupedExamples(T,List1,Temp).



convertRelations(A => Preds, A => Goal) :-
    length(A,LA),
    length(NewVar,LA),
    %NewVar = _,
    build_preds(Preds, NewVar, Calls, Vars),
    build_comparisons(Vars, Comps),
    append(Calls, Comps, AllGoals),
    list_to_conj(AllGoals, Goal1),
    Rel =.. [relations|NewVar],
    Goal2 = (Rel:-Goal1),
    copy_term(Goal2,Goal).

build_preds([], _, [], []).
build_preds([Pred|Rest], A, [Call|Calls], [Var|Vars]) :-
    append(A,[Var],Args),
    Call =.. [Pred | Args],
    build_preds(Rest, A, Calls, Vars).

% build_comparisons(+Vars, -Comparisons)
build_comparisons([_], []).
build_comparisons([V1, V2 | Rest], [V1 < V2 | Comps]) :-
    build_comparisons([V2 | Rest], Comps).

generateRelationTerms([],Rel,Rel).
generateRelationTerms([Var=>Terms|T],Rel,Rel2):-
    (length(Terms,L),L>1-> convertRelations(Var=>Terms,RelTerms),append(Rel,[RelTerms],Rel1);Rel1=Rel),
    generateRelationTerms(T,Rel1,Rel2).

cppRelations([],Rel,Rel).
cppRelations([Terms-Var-Values|T],Rel,R):-
    maplist(transpose,Values, Transpose),
    (length(Transpose, 1)->Transpose = [FF];
    maplist(flatten,Transpose,FF)),
    findRelations(Terms,FF,Rel1),
    append(Rel,[Var=>Rel1],Rel2),
    cppRelations(T,Rel2,R).

cppRelations(Ex, Rel) :-
   groupGroupedExamples(Ex,[],GEx),
   cppRelations(GEx,[],Relations),
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
                                                         ((nth1(N, FlatList_Ps, out);nth1(N, FlatList_Ps, numeric)),nth1(N,FlatList_Bs,NB))
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
count_vars(List, AssocOut) :-
    empty_assoc(Empty),
    count_vars(List, Empty, AssocOut).

count_vars([], Assoc, Assoc).
count_vars([H|T], AssocIn, AssocOut) :-
    ( get_assoc(H, AssocIn, Count) ->
        NewCount is Count + 1,
        put_assoc(H, AssocIn, NewCount, AssocMid)
    ;
        put_assoc(H, AssocIn, 1, AssocMid)
    ),
    count_vars(T, AssocMid, AssocOut).
single_occurrence_vars(Assoc) :-
    assoc_to_list(Assoc, Pairs),
    findall(Var, (member(Var-1, Pairs), var(Var)), Vars),length(Vars,0).

% Entry point
const_to_vars(List, VarList) :-
    const_to_vars(List, [], VarList, _).

% Base case: no more elements
const_to_vars([], _, [], _).

% If the constant is already mapped, reuse its variable
const_to_vars([X|Xs], MapIn, [Var|Vars], MapOut) :-
    
    memberchk(X-Var, MapIn), !,
    const_to_vars(Xs, MapIn, Vars, MapOut).

% If it's a new constant, create a new variable and add to map
const_to_vars([X|Xs], MapIn, [Var|Vars], MapOut) :-
    \+ memberchk(X-_, MapIn),
    const_to_vars(Xs, [X-Var|MapIn], Vars, MapOut).


head_connectedness(Args,Body):-
    %flatten_conjunction(Body,Body1),
    getAllArgs(Body,[],BArgs),
    append(Args, BArgs, AllArgs),
    const_to_vars(AllArgs, VarAllArgs),
    count_vars(VarAllArgs, Assoc), single_occurrence_vars(Assoc).

   
%---------------------------------------------------------
refinementBottomClauses([],_,_,NewBC,NewBC).
refinementBottomClauses([H|T],Filtered,HasRel,NewBC,Temp):-
    (member(H, Filtered)->
    (
    H =.. [Term|Vars],
    modeb(Term/_,Modes),
    findall(Var,(nth0(Index,Modes,in),nth0(Index,Vars,Var)),Bag),
    H1 =..[Term|Bag],
    append(NewBC,[H1],NewBC_1),
    Rel =..[relations|Bag],
    ((HasRel,not(member(Rel,NewBC))) -> append(NewBC_1,[Rel],NewBC1);NewBC1= NewBC_1)
    );
    append(NewBC, [H], NewBC1)),    
    refinementBottomClauses(T,Filtered,HasRel,NewBC1,Temp).


groupRefinementBottomClauses([],_,_,NewBC,NewBC).
groupRefinementBottomClauses([H|T],Filtered,HasRel,NewBC,Temp):-
    refinementBottomClauses(H,Filtered,HasRel,[],NewBC1),
    append(NewBC,[NewBC1],NewBC2),
    groupRefinementBottomClauses(T,HasRel,Filtered,NewBC2,Temp).

% Analysis of numerical values
cluster_vars_by_numbers(Terms, Grouped,Filtered) :-
    include(only_numbers, Terms, Filtered),     % Keep only a(_, Number) where Number is numeric
    collect_pairs(Filtered, Pairs),             % Convert to [Var-Value, ...]
    sort(0, @=<, Pairs, Ps),
    group_pairs_by_key(Ps, Grouped).

checkIfNumber(Values,Index):-
    nth0(Index, Values, Value),
    number(Value).

% Keep only terms with numeric values
only_numbers(T) :-
    T =.. [T1|Values],
    modeb(T1/_,Modes),
    findall(Nums,nth0(Nums,Modes,numeric),Bag),
    length(Bag,Len),
    (Len > 0 ->
    maplist(checkIfNumber(Values),Bag);fail).
    
% Turn a(Var, Val) into Var-Val
% collect_pairs([], []).
% collect_pairs([H|T], [Term - Var - Val|Rest]) :-
%     H =.. [Term, Var, Val],  % Extract Var and Val
%     collect_pairs(T, Rest).
notNumber(X) :- \+ number(X).
collect_pairs([], []).
collect_pairs([H|T], [Term - NNs - Ns|Rest]) :-
    H =.. [Term| Var],  % Extract Var and Val
    include(number, Var, Ns),     % Ensure Val is numeric
    include(notNumber, Var, NNs), % Ensure Val is numeric
    collect_pairs(T, Rest).

bottomClausePrint1(Term,Copy) :-
    copy_term(Term, Copy),
    numbervars(Copy, 0, _, [singletons(true)]).

bottomClausePrint(Term, Numbered) :-
        copy_term(Term, Copy),
        numbervars(Copy, 0, _),  % Number all variables in the copy
        Numbered = Copy.         % Return the numbered version
    
analyseNumbers(Pos,Neg,F,Relations,NewBC):-
        flatten(Pos,FlatPos),
        flatten(Neg,FlatNeg),
        cluster_vars_by_numbers(FlatPos,GroupedPos,Filtered),
        cluster_vars_by_numbers(FlatNeg,GroupedNeg,_),
        cppRelations(GroupedPos,Relations),
        (length(Relations,LenR),LenR > 0 ->HasRel=true;HasRel=fail),
        groupRefinementBottomClauses(Pos,Filtered,HasRel,[],NewBC),
        extractAndProcessGMM(GroupedPos,GroupedNeg,[],F).

addSigns([],[]).
addSigns([H|T],[Sign|Rest]):-
    H = [Mean, StdDev],
    Sign = (μ(Mean),σ(StdDev)),
    addSigns(T,Rest).
        

list_to_disjunction([X], X) :- !.
list_to_disjunction([H|T], (H ; Rest)) :-
            list_to_disjunction(T, Rest).
    
extractAndProcessGMM([],_,FunctionsInvention,FunctionsInvention).    
extractAndProcessGMM([Term-Var-ValuePos|RestPos],Neg,FunctionsInvention,Rest):-
        ((nth0(Index, Neg, Term-VarNeg-_),Var==VarNeg)->
        nth0(Index, Neg, _-_-N1),
        ValueNeg=N1;
        ValueNeg=[]),
        
        flatten(ValuePos,FFPos),
        flatten(ValueNeg,FFNeg),
      
        findThresholds(FFPos,FFNeg,PosCluster,NegCluster),
       
        length(Var,Len),length(HeadVar,Len),append([Term],HeadVar,T),append(T,[NewVar],T1), TermHead=..T1,

        
        addSigns(PosCluster,PosSigns),
        addSigns(NegCluster,NegSigns),
        Body = inCluster(NewVar,pos(PosSigns),neg(NegSigns)),
     
       Head =.. [Term|HeadVar],
       
       FunctionsInvention1 = (Head :- TermHead,Body),copy_term(FunctionsInvention1,FunctionsInvention2),
       write(FunctionsInvention2),nl,
       append(FunctionsInvention,[Var => FunctionsInvention2],Rest1),
      
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
    findall(C,(nth0(_,InvF,(A=>C)),A==Args),Bag),
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
    writeln('------------------------------------------ '),
    writeln('Hypothesis space generated.'),
    writeln('Finding best rules...'),
    findBestRules(FlatHypos,ArrPos).
    %maplist(bottomClausesPrint,FinalRule,FinalRule1),
    %write(FinalRule1).  



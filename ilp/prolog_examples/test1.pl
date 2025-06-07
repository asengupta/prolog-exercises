:- use_module(library(prolog_stack)).
:- use_module(library(clpfd)).

edge(a,b).
edge(b,c).
edge(c,d).
edge(p,q).

instr(0,mov,ax,bx,1).
instr(1,jmp,ax,dummy,2).
instr(2,jmp,ax,dummy,2).

has(proc1,[0,1]).
has(proc2,[2]).

belongs_to_proc(PROC,instr(ID,_,_,_,_),YESNO) :- (has(PROC,INSTRS), belongs_to(PROC,instr(ID,_,_,_,_),INSTRS,BELONGS_TO), YESNO = BELONGS_TO).
belongs_to_proc(PROC,instr(_,_,_,_,_),YESNO) :- \+ has(PROC,_),YESNO = 'NO'.
belongs_to(_,instr(_,_,_,_,_),[],YESNO) :- YESNO = 'NO'.
belongs_to(PROC,instr(ID,_,_,_,_),[H_ID|T_IDS],YESNO) :- (H_ID =:= ID,YESNO = 'YES');
                                                         (belongs_to(PROC,instr(ID,_,_,_,_),T_IDS,CHILD_RESULT),YESNO = CHILD_RESULT).

affects(X) :- instr(_,mov,X,_,_).

jmps([],0).
jmps([instr(_,jmp,_,_,_) | R],SUM) :- jmps(R, NEWSUM), SUM is NEWSUM+1, write("Added one...").
jmps([instr(_,_,_,_,_) | R],SUM) :- jmps(R, SUM).
idjmps([],0).
idjmps([X|R],SUM) :- number(X),instr(X,jmp,_,_,_),idjmps(R,NEWSUM),SUM is NEWSUM+1.
idjmps([X|R],SUM) :- number(X),instr(X,_,_,_,_),idjmps(R,NEWSUM),SUM is NEWSUM.

immediately_before(ID1,ID2) :- instr(ID1,_,_,_,T1),instr(ID2,_,_,_,T2), write('Checking for immediately before...'), T1 =:= T2 - 1.
path(X,Y) :- edge(X,Y).
path(X,Y) :- edge(X,Z),path(Z,Y).

path(a,b).

append([],[],[]).
append([],[H|T],[H|T]).
append([H1|T1],L2,[H1|T3]) :- append(T1,L2,T3).

%append([a,b,c],[d,e,f],[H3|T3])
%=> append([b,c],[d,e,f],[HX|TX]) H3=a,T3=[HX|TX]
%=> append([c],[d,e,f],[HX|TX]) H3=b,T3=[HX|TX]
%=> append([],[d,e,f],[HX|TX]) H3=c,T3=[HX|TX]
%=> HX=d,TX=[e,f],H3=c,T3=[d,e,f]
%=> HX=c,TX=[d,e,f],H3=b,T3=[c,d,e,f]
%=> HX=b,TX=[c,d,e,f],H3=a,T3=[b,c,d,e,f]
%=> append([a,b,c],[d,e,f],[a|[b,c,d,e,f]])

reverse([],ACC,ACC).
reverse([H|T],ACC,R) :- reverse(T,[H|ACC],R).

%=> reverse([a|[b,c]],[],R) :- reverse([b,c],[a|[]],R)=reverse([b,c],[a],R)
%=> reverse([b|[c]],[a],R) :- reverse([c],[b|[a]],R) = reverse([c],[b,a],R)
%=> reverse([c|[]],[b,a],R) :- reverse([],[c|[b,a]],R) = reverse([],[c,b,a],R)
%=> reverse([],[c,b,a],R) :- reverse([],[c,b,a],[c,b,a])

len([],0).
len([_|T],L) :- len(T,X),L is X+1.

len2([],ACC,ACC).
len2([_|T],ACC,L) :- ACC1 is 1+ACC,len2(T,ACC1,L).

max2([],MAX,MAX).
max2([H|T],CURR_MAX,MAX) :- (H > CURR_MAX->NEWMAX=H;NEWMAX=CURR_MAX), max2(T,NEWMAX,MAX).

into2([],[]).
into2([H|T],RESULT) :- DBL is H*2, into2(T,RESULTX), RESULT=[DBL|RESULTX].

filter_even([],[]).
filter_even([H|T],R) :- filter_even(T,RESULTX), Remainder is H mod 2,(Remainder=:=0 -> R=[H|RESULTX];R=RESULTX).

double(X,Y) :- Y is X*2.
map2([],_,[]).
map2([H|T],Map_pred,[Mapped|RESULTX]) :- map2(T,Map_pred,RESULTX),call(Map_pred,H,Mapped).

isEven(X) :- 0 is X mod 2.
filter2([],_,[]).
filter2([H|T],FilterPred,[H|AlreadyFiltered]) :- call(FilterPred,H),filter2(T, FilterPred, AlreadyFiltered).
filter2([H|T],FilterPred,AlreadyFiltered) :- \+call(FilterPred,H),filter2(T, FilterPred, AlreadyFiltered).


concat([],L,L).
concat([H1|T1],B,[H1|R]) :- concat(T1,B,R).

flatten([],[]).
flatten([[H1|T1]|T],R) :- flatten([H1|T1],RESULTH),!,flatten(T,RESULTX),concat(RESULTH,RESULTX,R).
flatten([[]|T],R) :- flatten(T,R).
flatten([H|T],R) :- flatten(T,RESULTX),R=[H|RESULTX].

contains(_,[]) :- false.
contains(Search,[H|T]) :- (writeln("Comparing " + H + Search),H == Search);contains(Search,T).

uniq([],_,[]).
uniq([H|T],Seen,RESULTX) :- contains(H,Seen),uniq(T,Seen,RESULTX).
uniq([H|T],Seen,[H|RESULTX]) :- \+ contains(H,Seen),uniq(T,[H|Seen],RESULTX).

%uniq([H|T],Seen,R) :- contains(H,Seen)->(NewSeen=Seen,uniq(T,NewSeen,RESULTX),R=RESULTX);
%                                        (NewSeen=[H|Seen],uniq(T,NewSeen,RESULTX),R=[H|RESULTX]).


group_consecutive([],[]).
group_consecutive([X],[[X]]).
group_consecutive([H|T],Result) :-
        group_consecutive(T,[[GroupHead|GroupTail]|TX]), H==GroupHead, !,Result=[[H|[GroupHead|GroupTail]]|TX].
group_consecutive([H|T],Result) :-
        group_consecutive(T,[[GroupHead|GroupTail]|TX]), \+ H==GroupHead, !, Result=[[H]|[[GroupHead|GroupTail]|TX]].


rle([],[]).
rle([X],[[1,X]]).
rle([H|T],Groups) :- rle(T,[[Count,GroupType]|TC]), H==GroupType, NewCount is Count+1, Groups=[[NewCount|[GroupType]]|TC].
rle([H|T],Groups) :- rle(T,[[Count,GroupType]|TC]), \+ H==GroupType, Groups=[[1,H] | [[Count|[GroupType]]|TC]].

make([0,_],Pre,Pre).
make([Times,X],Pre,R) :- TimesMinusOne is Times-1, make([TimesMinusOne,X],Pre,Expanded),R=[X|Expanded].

rld([],[]).
rld([[Times,GroupType]],R) :- make([Times,GroupType],[],R).
rld([[Times,GroupType]|T],Decoded) :- rld(T,Expanded), make([Times,GroupType],Expanded,Decoded).

increment([],X,[[X,1]]).
increment([[Group,C]|T],X,R) :- X==Group, CountPlusOne is C+1, R=[[Group,CountPlusOne]|T].
increment([[Group,C]|T],X,R) :- \+ X==Group, increment(T,X,Rest), R=[[Group,C]|Rest].

freq([],Map,Map).
freq([H|T],Map,R) :- increment(Map,H,UpdatedMap), freq(T,UpdatedMap,R).

atLeastOnePrimitive([]) :- true.
atLeastOnePrimitive(Terms) :- atLeastOnePrimitive_(Terms,false,true).

atLeastOnePrimitive_([],ACC,ACC).
atLeastOnePrimitive_([H|T],ACC,Result) :- (H==false;H==true)->Result=true;atLeastOnePrimitive_(T,ACC,Result).

simplify(or2(true,_),true).
simplify(or2(_,true),true).
simplify(or2(false,X),R) :- simplify(X,RX), R=RX.
simplify(or2(X,false),R) :- simplify(X,RX), R=RX.
simplify(or2(X,X),R) :- simplify(X,RX),R=RX.
simplify(or2(X,Y),R) :- simplify(X,RX), simplify(Y,RY), (atLeastOnePrimitive([RX,RY])->simplify(or2(RX,RY),R);R=or2(RX,RY)).

simplify(and2(false,_),false).
simplify(and2(_,false),false).
simplify(and2(true,X),R) :- simplify(X,RX), R=RX.
simplify(and2(X,true),R) :- simplify(X,RX), R=RX.
simplify(and2(X,X),R) :- simplify(X,RX),R=RX.
simplify(and2(X,Y),R) :- simplify(X,RX), simplify(Y,RY), (atLeastOnePrimitive([RX,RY])->simplify(and2(RX,RY),R);R=and2(RX,RY)).

simplify(not2(false),true).
simplify(not2(true),false).
simplify(not2(not2(X)),R) :- simplify(X,RX), R=RX.
simplify(not2(X),not2(RX)) :- simplify(X,RX), RX \= true, RX \= false.

simplify(gt(X,Y),true) :- X>Y.
simplify(gt(X,Y),false) :- \+ X>Y.
simplify(lt(X,Y),true) :- X<Y.
simplify(lt(X,Y),false) :- \+ X<Y.

simplify(implies(true,true),true).
simplify(implies(true,false),false).
simplify(implies(false,R),true) :- member(R, [true, false]).
simplify(implies(true,X),RX) :- simplify(X,RX).
simplify(implies(X,Y),R) :- simplify(X,RX), simplify(Y,RY), ImpliesExpr=or2(not2(RX),RY), (atLeastOnePrimitive([RX,RY])->simplify(ImpliesExpr,R);R=ImpliesExpr).
simplify(X,X).


continueBasedOnFactExistence(CurrentTail,OriginalClauses,DiscoveredClauses,Goal,FactExists,implies(X,Y),AtLeastOneSimplification) :-
                                           (FactExists -> (
                                                              AtLeastOneSimplification=true,
                                                              simplify(implies(FactExists,Deduction),true),
                                                              writeln("Deduction=" + Deduction),
                                                              (Deduction==true->UpdatedClauses=[Y|DiscoveredClauses];UpdatedClauses=DiscoveredClauses),
                                                              writeln("UpdatedClauses=" + UpdatedClauses),
                                                              entails_(CurrentTail,OriginalClauses,UpdatedClauses,Goal,AtLeastOneSimplification)
                                                          );
                                                          UpdatedClauses=[implies(X,Y)|DiscoveredClauses]
                                           ),
                                           entails_(CurrentTail,OriginalClauses,UpdatedClauses,Goal,AtLeastOneSimplification).

iterate(true,_,_) :- true.
iterate(false,_,false) :- false.
iterate(false,DiscoveredClauses,Goal,true) :- writeln("Going at it again..."), entails(DiscoveredClauses,Goal).

node(node(node(empty,empty,5),node(empty,empty,6),1),node(node(empty,empty,7),node(empty,empty,8),2),3).

mirror(node(empty,empty,V),node(empty,empty,V)).
mirror(node(L,R,V),node(MirroredRight,MirroredLeft,V)) :- mirror(L,MirroredLeft),mirror(R,MirroredRight).

search2(empty,_,false).
search2(node(_,_,V),Term,true) :- V==Term.
search2(node(L,R,V),Term,Result) :- \+ V == Term,
                                                search2(L,Term,LeftSearchSucceeded),
                                                search2(R,Term,RightSearchSucceeded),
                                                simplify(or2(LeftSearchSucceeded,RightSearchSucceeded),Result).

satisfiesLowerBound(_,minusInfinity) :- true,!.
satisfiesLowerBound(V,LowerBound) :- V>LowerBound.

satisfiesUpperBound(_,plusInfinity) :- true,!.
satisfiesUpperBound(V,UpperBound) :- V<UpperBound.

withinBounds(V,[LowerBound,UpperBound]) :- satisfiesLowerBound(V,LowerBound),satisfiesUpperBound(V,UpperBound).

isBTree(empty,_,true).
isBTree(node(L,R,V),[LowerBound,UpperBound],Result) :-
                                                      (withinBounds(V,[LowerBound,UpperBound]) -> (
                                                              isBTree(L,[LowerBound,V],LeftIsBTree),
                                                              isBTree(R,[V,UpperBound],RightIsBTree),
                                                              simplify(and2(LeftIsBTree,RightIsBTree),Result)
                                                      );Result=false).


member2(_,[]) :- false.
member2(-(K,V), [(-(KX,VX))|_]) :- K==KX,V==VX.
member2(-(K,V), [_|T]) :- member2(-(K,V),T).

get2(_,[],empty).
get2(K, [(-(KX,VX))|_],VX) :- K==KX.
get2(K, [_|T],R) :- get2(K,T,R).

put2_(-(K,V),[],Replaced,R) :- Replaced->R=[];R=[-(K,V)].
put2_(-(K,V),[-(KX,_)|T],_,[-(K,V)|RX]) :- K==KX,put2_(-(K,V),T,true,RX).
put2_(-(K,V),[H|T],Replaced,[H|RX]) :- put2_(-(K,V),T,Replaced,RX).

remove2_(_,[],Acc,Acc).
remove2_(K,[-(KX,_)|T],Acc,R) :- K==KX,remove2_(K,T,Acc,R).
remove2_(K,[H|T],Acc,R) :- remove2_(K,T,[H|Acc],R).

put2(-(K,V),Map,R) :- put2_(-(K,V),Map,false,R).
remove2(K,Map,R) :- remove2_(K,Map,[],R).

merge2(Map1,[],Map1).
merge2([],Map2,Map2).
merge2([-(K,V)|T],Map2,R) :- put2(-(K,V),Map2,RX),merge2(T,RX,R).


safe_eval(Condition) :- catch(Condition,_,fail).
rewrite_direct_match([],Term,Term).
rewrite_direct_match([Rule|_],Term,RHS) :- copy_term(Rule,:(LHS=>RHS,Guard)),LHS=Term,safe_eval(Guard).
rewrite_direct_match([Rule|_],Term,RHS) :- copy_term(Rule,LHS=>RHS),LHS=Term.
rewrite_direct_match([_|T],Term,R) :- rewrite_direct_match(T,Term,R).

rewrite_args_list(_,[],[]).
rewrite_args_list([],Args,Args).
rewrite_args_list(Rules,[Term|T],R) :- rewrite_once(Rules,Term,RewrittenTerm),
                                                rewrite_args_list(Rules,T,RemainingRewrittenTerms),
                                                R=[RewrittenTerm|RemainingRewrittenTerms].


rewrite_once(Rules,Term,RewrittenTerm) :- rewrite_direct_match(Rules,Term,RewrittenTerm),
                                Term \= RewrittenTerm.
rewrite_once(_,Term,Term) :- Term =.. [_].
rewrite_once(Rules,ComplexTerm,RewrittenComplexTerm) :- ComplexTerm =.. [F|Args],
                                        rewrite_args_list(Rules,Args,RewrittenArgs),
                                        RewrittenComplexTerm=.. [F|RewrittenArgs].

rewrite_all2_(Rules,Term,empty,TraceAcc,Trace,R) :- rewrite_once(Rules,Term,RewrittenTerm),
                                    rewrite_all2_(Rules,Term,RewrittenTerm,TraceAcc,TraceX,R),
                                    Trace=[Term|[RewrittenTerm|TraceX]].

rewrite_all2_(_,Term,RewrittenTerm,TraceAcc,TraceAcc,Term) :- RewrittenTerm==Term.
rewrite_all2_(Rules,_,RewrittenTerm,TraceAcc,Trace,R) :-rewrite_once(Rules,RewrittenTerm,NewRewrittenTerm),
                                        rewrite_all2_(Rules,RewrittenTerm,NewRewrittenTerm,TraceAcc,TraceX,R),
                                        Trace=[NewRewrittenTerm|TraceX].

rewrite_all2(Rules,Term,Trace,R) :- rewrite_all2_(Rules,Term,empty,[],Trace,R).

%before(instr(_,T1),instr(_,T2)) :- T1 < T2.
%after(instr(_,T1),instr(_,T2)) :- T1 > T2.
%affects(instr(Register,_),Register).
%
%affectors([],Acc,_,Acc) :- writeln("Base case").
%affectors([instr(Register,Time)|T],Acc,Register,Mutators) :- affectors(T,[instr(Register,Time)|Acc],Register,Mutators).
%affectors([_|T],Acc,Register,Mutators) :- affectors(T,Acc,Register,Mutators).
%
%mvc(to(ToOffset,Length,ToRegister),from(offset(FromRegister,FromOffset))) :- writeln("Most general form").
%mvc(to(ToOffset,Length,ToRegister),from(FromRegister)) :- mvc(to(ToOffset,Length,ToRegister),from(offset(FromRegister,0))).
%la(ToRegister,value(Length,FromRegister)).
%
%load_advance(mvc(to(ToOffset,Length,ToRegister),from(offset(FromRegister,FromOffset))),la(ToRegister,from(Length,ToRegister))).
%load_advance(mvc(to(ToOffset,Length,ToRegister),from(FromRegister)),la(ToRegister,from(Length,ToRegister))).

execute([],ReversedHistory,ReversedHistory).
execute([mvc(reg(ToRegister),Value)|T],ReversedHistory,CompleteReversedHistory) :- execute(T,[set(reg(ToRegister),Value)|ReversedHistory],CompleteReversedHistory).
execute([_|T],ReversedHistory,CompleteReversedHistory) :- execute(T,ReversedHistory,CompleteReversedHistory).

latestValue(_,[],empty).
latestValue(reg(Variable),[set(reg(Variable),reg(From))|RemainingReversedHistory],TransitiveValue) :- latestValue(reg(From),RemainingReversedHistory,TransitiveValue).
latestValue(reg(Variable),[set(reg(Variable),Value)|_],Value).
latestValue(reg(Variable),[_|RemainingReversedHistory],FinalValueX) :- latestValue(reg(Variable),RemainingReversedHistory,FinalValueX).

update_reg(-(reg(ToRegister),reg(FromRegister)),Registers,UpdatedRegisters) :- get2(FromRegister,Registers,Value),
                                                                               update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters).
update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters) :- put2(-(ToRegister,Value),Registers,UpdatedRegisters).

exec([],Registers,_,TraceAcc,TraceAcc,Registers).
exec([mvc(reg(ToRegister),Value)|T],Registers,Flag,TraceAcc,FinalTrace,FinalRegisters) :- 
                                                        update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters),
                                                        exec(T,UpdatedRegisters,Flag,TraceAcc,RemainingTrace,FinalRegisters),
                                                        FinalTrace=[mvc(reg(ToRegister),Value)|RemainingTrace].
exec([Instr|T],Registers,Flag,TraceAcc,FinalTrace,FinalRegisters) :- 
                                                        exec(T,Registers,Flag,TraceAcc,RemainingTrace,FinalRegisters),
                                                        FinalTrace=[Instr|RemainingTrace].

simpleGet(_,Result) :- Result=xxx.

badLoop([]) :- writeln("Done").
badLoop([H|_]) :- get2(H,[1-a,2-b,3-c],Result),
                  Result==empty,
                  writeln("2) H is empty, apparently not " + H + Result).
badLoop([H|T]) :- writeln("Printing " + H),badLoop(T).

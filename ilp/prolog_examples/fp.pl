double(X, Y) :- Y is X * 2.
apply_twice(Pred, X, SecondResult) :- call(Pred,X,FirstResult),
									  call(Pred,FirstResult,SecondResult).

maplist_twice(Pred,Arr,Result) :- maplist_twice_(Pred,Arr,[],Result).

maplist_twice_(_,[],Acc,Acc) :- !.
maplist_twice_(Pred,[H|T],Acc,[Applied|ResultX]) :- apply_twice(Pred,H,Applied),maplist_twice_(Pred,T,Acc,ResultX).

append_dl(A-X,B-Y,A-Y) :- X=B.

parent(a,b).
parent(b,c).
parent(b,d).

grandparent(X,Y) :- parent(X,Z),parent(Z,Y).

inc(X,Y) :- Y is X+1.

add(X,Y,Z) :- Z is X+Y.

run_goal(X) :- call(X).
mul(X, Y, Z) :- Z is X * Y.


run_pred(PredHead,Args) :- Pred=..[PredHead|Args],call(Pred).

partial_apply2(PredHead,Arg1,P) :- P=..[PredHead,Arg1].
partial_apply3(PredHead,InitialArgs,P) :- P=..[PredHead|InitialArgs].

add3(X, Y, Z, R) :- R is X + Y + Z.
defined_predicate(Name, Arity) :- current_predicate(Name/Arity).

length([],Acc,Acc).
length([_|T],Acc,Length) :- NewAcc is Acc+1,length(T,NewAcc,Length).
safe_call(C) :- predicateExists(C),call(C).
predicateExists(C) :- C=..[H|Args],length(Args,0,Length),current_predicate(H/Length).
allGround_([],true).
allGround_([H|T],AllGround) :- ground(H) -> allGround_(T,AllGround);AllGround=false.
allGround(Atoms) :- allGround_(Atoms,true).
groundPredicate(C) :- C=..[_|Args],allGround(Args).
call_if_defined(C) :- predicateExists(C),groundPredicate(C),call(C).

foo(a, b).
bar(a, _).


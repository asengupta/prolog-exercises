double(X, Y) :- Y is X * 2.
apply_twice(Pred, X, SecondResult) :- call(Pred,X,FirstResult),
									  call(Pred,FirstResult,SecondResult).

maplist_twice(Pred,Arr,Result) :- maplist_twice_(Pred,Arr,[],Result).

maplist_twice_(_,[],Acc,Acc) :- !.
maplist_twice_(Pred,[H|T],Acc,[Applied|ResultX]) :- apply_twice(Pred,H,Applied),maplist_twice_(Pred,T,Acc,ResultX).

append_dl(A-X,B-Y,A-Y) :- X=B.

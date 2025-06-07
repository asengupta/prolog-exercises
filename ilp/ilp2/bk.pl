action(load,a,1).
action(load,b,1).
action(load,g,1).
action(load,h,2).

action(advance,a,2).
action(advance,b,2).
action(advance,f,1).
action(advance,f,2).
action(advance,h,1).


before(1, 2).

loads_at(X,T) :- action(load,X,T).
advances_at(X,T) :- action(advance,X,T).


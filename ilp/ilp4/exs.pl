pos(last([a],a)).
pos(last([a,b],b)).
pos(last([a,b,c],c)).
pos(last([1,2,3,4,5],5)).

neg(last([],a)).
neg(last([a,b,c],a)).
neg(last([a,b,c],b)).

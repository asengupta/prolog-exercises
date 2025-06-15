concat([],RHS,RHS).
concat([H|T],RHS,[H|ResultX]) :- concat(T,RHS,ResultX).

match(Left,Right,Result) :- concat(Left,Intermed,Result),concat(_,Right,Intermed),!.
contains(Segment,Result) :- concat(Segment,_,Result).
contains(Segment,Result) :- concat(_,Segment,Result).
contains(Segment,Result) :- concat(_,Rest,Result),
                            concat(Segment,_,Rest).

%match(Left,Right,Code) :- concat(_,Right,Intermed),concat(Left,Intermed,Code),!.

prefix2(Prefix,List) :- concat(Prefix,_, List).
suffix2(Suffix,List) :- concat(_,Suffix, List).
infix(Infix,List) :- concat(_,Rest,List),
                     concat(Infix,_,Rest).

split(List,Before,After,Pivot) :-concat(Before,[Pivot|After],List).

replace_segment(Old,New,List,Result) :- concat(Before,Rest,List),
                                        concat(Old,Remaining,Rest),
                                        concat(Before,New,Intermed),
                                        concat(Intermed,Remaining,Result).

surrounds(Outer,Inner) :- concat([_|_],Rest,Outer),
                          concat(Inner,[_|_],Rest).

interleave([],[],[]).
interleave([HA|TA],[HB|TB],[HA,HB|ResultX]) :- interleave(TA,TB,ResultX).

palindrome2(Original) :- palindrome2_(Original,[],Original).
palindrome2_([],Original,Original).
palindrome2_([H|T],Acc,Original) :- palindrome2_(T,[H|Acc],Original).

doubled(List) :- concat(Copy,Copy,List).

middle_element(E, List) :- concat(LeftSide,Right,List),
                           concat(Left,[E],LeftSide),
                           length(Left,N),length(Right,N).

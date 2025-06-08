member2(_,[]) :- false.
member2(-(K,V), [(-(KX,VX))|_]) :- K==KX,V==VX.
member2(-(K,V), [_|T]) :- member2(-(K,V),T).

get2(_,[],empty).
get2(K, [(-(K,VX))|_],VX) :- !.
get2(K, [_|T],R) :- get2(K,T,R).

put2_(-(K,V),[],Replaced,R) :- Replaced->R=[];R=[-(K,V)].
put2_(-(K,V),[-(K,_)|T],_,[-(K,V)|RX]) :- put2_(-(K,V),T,true,RX).
put2_(-(K,V),[H|T],Replaced,[H|RX]) :- put2_(-(K,V),T,Replaced,RX).

remove2_(_,[],Acc,Acc).
remove2_(K,[-(K,_)|T],Acc,R) :- remove2_(K,T,Acc,R).
remove2_(K,[H|T],Acc,R) :- remove2_(K,T,[H|Acc],R).

put2(-(K,V),Map,R) :- put2_(-(K,V),Map,false,R).
remove2(K,Map,R) :- remove2_(K,Map,[],R).

merge2(Map1,[],Map1).
merge2([],Map2,Map2).
merge2([-(K,V)|T],Map2,R) :- put2(-(K,V),Map2,RX),merge2(T,RX,R).

push_(V,Stack,UpdatedStack) :- UpdatedStack=[V|Stack].

pop_([],empty,[]).
pop_([H|Rest],H,Rest).

equate(LHS,LHS,0).
equate(LHS,RHS,1) :- LHS < RHS.
equate(LHS,RHS,-1) :- LHS > RHS.

update_reg(-(reg(ToRegister),reg(FromRegister)),Registers,UpdatedRegisters) :- get2(FromRegister,Registers,Value),
                                                                               update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters).
update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters) :- put2(-(ToRegister,Value),Registers,UpdatedRegisters).

instruction_pointer_map([],IPMap,_,IPMap).
instruction_pointer_map([Instr|T],IPMap,IPCounter,FinalIPMap) :- put2(-(IPCounter,Instr),IPMap,UpdatedIPMap),
                                                                 UpdatedIPCounter is IPCounter+1,
                                                                 instruction_pointer_map(T,UpdatedIPMap,UpdatedIPCounter,FinalIPMap).
label_map([],LabelMap,_,LabelMap).
label_map([label(Label)|T],LabelMap,IPCounter,FinalLabelMap) :- put2(-(label(Label),IPCounter),LabelMap,UpdatedLabelMap),
                                                                 UpdatedIPCounter is IPCounter+1,
                                                                 label_map(T,UpdatedLabelMap,UpdatedIPCounter,FinalLabelMap),
                                                                 !.
label_map([_|T],LabelMap,IPCounter,FinalLabelMap) :- UpdatedIPCounter is IPCounter+1,
                                                     label_map(T,LabelMap,UpdatedIPCounter,FinalLabelMap).

toTraceOut(X,stateIn(_,Stack,CallStack,Registers,Flag),traceOut(X,Stack,CallStack,Registers,Flag)).

exec_(reference(IPMap,LabelMap),stateIn(IP,Stack,CallStack,Registers,Flag),TraceAcc,StateOut) :- 
                                                    get2(IP,IPMap,Instr),
                                                    exec_helper(Instr,reference(IPMap,LabelMap),stateIn(IP,Stack,CallStack,Registers,Flag),TraceAcc,StateOut).

exec_helper(empty,_,StateIn,TraceAcc,TraceOut) :- toTraceOut(TraceAcc,StateIn,TraceOut).
exec_helper(hlt,_,StateIn,TraceAcc,TraceOut) :- toTraceOut(TraceAcc,StateIn,TraceOut),writeln('Halting program!!!!').
exec_helper(Instr,reference(IPMap,LabelMap),stateIn(IP,Stack,CallStack,Registers,Flag),TraceAcc,traceOut(FinalTrace,FinalStack,FinalCallStack,FinalRegisters,FinalFlag)) :-
                                                        writeln('Interpreting ' + Instr + 'StateIn is ' + stateIn(IP,Stack,CallStack,Registers,Flag)),
                                                        NextIP is IP+1,
                                                        writeln(interpret(Instr,NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedFlag))),
                                                        interpret(Instr,NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedFlag)),
                                                        write('Next IP is ' + UpdatedIP),
                                                        exec_(reference(IPMap,LabelMap),stateIn(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedFlag),TraceAcc,traceOut(RemainingTrace,FinalStack,FinalCallStack,FinalRegisters,FinalFlag)),
                                                        FinalTrace=[Instr|RemainingTrace],!.

isZero(0).
isNotZero(X) :- \+ isZero(X).
plusOne(X,PlusOne) :- PlusOne is X+1.
minusOne(X,MinusOne) :- MinusOne is X-1.

interpret_condition(_,NewIP,Flag,Condition,NewIP) :- call(Condition,Flag).
interpret_condition(OldIP,_,Flag,Condition,OldIP) :- \+ call(Condition,Flag).

interpret(mvc(reg(ToRegister),Value),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,Stack,CallStack,UpdatedRegisters,Flag)) :- 
                                                        writeln('In mvc' + ToRegister + Registers),
                                                        update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters).
interpret(cmp(reg(CmpRegister),CmpValue),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,_),stateIn(NextIP,Stack,CallStack,Registers,UpdatedFlag)) :- 
                                                        writeln('In cmp' + CmpRegister + Registers),
                                                        get2(CmpRegister,Registers,RegisterValue),
                                                        equate(RegisterValue,CmpValue,UpdatedFlag).

interpret(j(label(Label)),_,[LabelMap],stateIn(_,Stack,CallStack,Registers,Flag),stateIn(UpdatedIP,Stack,CallStack,Registers,Flag)) :- 
                                                        writeln('In jmp direct label' + Label + Registers),
                                                        get2(label(Label),LabelMap,UpdatedIP).

interpret(j(reg(JumpRegister)),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut) :- 
                                                        writeln('In jmp indirect' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(j(RegisterValue),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut).

interpret(j(JumpIP),_,_,stateIn(_,Stack,CallStack,Registers,Flag),stateIn(JumpIP,Stack,CallStack,Registers,Flag)) :- writeln('In jmp direct' + JumpIP + Registers).

interpret(jz(reg(JumpRegister)),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut) :- 
                                                        writeln('In JZ indirect reg' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jz(RegisterValue),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut).

interpret(jnz(reg(JumpRegister)),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut) :- 
                                                        writeln('In JNZ indirect reg' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jnz(RegisterValue),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut).

interpret(jz(label(Label)),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut) :- 
                                                        writeln('In JZ label' + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jz(JumpIP),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut).

interpret(jnz(label(Label)),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut) :- 
                                                        writeln('In JNZ label' + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jnz(JumpIP),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),StateOut).

interpret(jz(JumpIP),OldNextIP,_,stateIn(OldNextIP,Stack,CallStack,Registers,Flag),stateIn(UpdatedIP,Stack,CallStack,Registers,Flag)) :- interpret_condition(OldNextIP,JumpIP,Flag,isZero,UpdatedIP).
interpret(jnz(JumpIP),OldNextIP,_,stateIn(OldNextIP,Stack,CallStack,Registers,Flag),stateIn(UpdatedIP,Stack,CallStack,Registers,Flag)) :- interpret_condition(OldNextIP,JumpIP,Flag,isNotZero,UpdatedIP).

interpret(inc(reg(Register)),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,Stack,CallStack,UpdatedRegisters,Flag)) :- interpret_update_reg(reg(Register),plusOne,Registers,UpdatedRegisters).
interpret(dec(reg(Register)),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,Stack,CallStack,UpdatedRegisters,Flag)) :- interpret_update_reg(reg(Register),minusOne,Registers,UpdatedRegisters).
interpret(mul(reg(LHSRegister),reg(RHSRegister)),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,Stack,CallStack,UpdatedRegisters,Flag)) :- 
                get2(LHSRegister,Registers,LHSValue),
                get2(RHSRegister,Registers,RHSValue),
                Product is LHSValue*RHSValue,
                update_reg(-(reg(LHSRegister),Product),Registers,UpdatedRegisters).


interpret(term(String),_,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,Stack,CallStack,Registers,Flag)) :- writeln(String).
interpret(label(String),_,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,Stack,CallStack,Registers,Flag)) :- writeln('ENTER: ' + String ).

interpret(push(reg(Register)),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,UpdatedStack,CallStack,Registers,Flag)) :- 
                    get2(Register,Registers,RegisterValue),
                    push_(RegisterValue,Stack,UpdatedStack).

interpret(pop(reg(Register)),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,UpdatedStack,CallStack,UpdatedRegisters,Flag)) :- 
                                                                pop_(Stack,PoppedValue,UpdatedStack),
                                                                update_reg(-(reg(Register),PoppedValue),Registers,UpdatedRegisters).
interpret(push(V),NextIP,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,UpdatedStack,CallStack,Registers,Flag)) :- push_(V,Stack,UpdatedStack).

interpret(call(label(LabelName)),NextIP,[LabelMap],stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(CallIP,Stack,UpdatedCallStack,Registers,Flag)) :- 
                                                            get2(label(LabelName),LabelMap,CallIP),
                                                            push_(NextIP,CallStack,UpdatedCallStack),
                                                            writeln('CALL: ' + LabelName + 'Stack is ' + UpdatedCallStack).
interpret(ret,_,_,stateIn(_,Stack,CallStack,Registers,Flag),stateIn(PoppedValue,Stack,UpdatedCallStack,Registers,Flag)) :- 
                                                            pop_(CallStack,PoppedValue,UpdatedCallStack),
                                                            writeln('Returning from call...IP is ' + PoppedValue).
interpret(nop,_,_,stateIn(NextIP,Stack,CallStack,Registers,Flag),stateIn(NextIP,Stack,CallStack,Registers,Flag)).

interpret_update_reg(reg(Register),Calculation,Registers,UpdatedRegisters) :- 
                                                            get2(Register,Registers,RegisterValue),
                                                            call(Calculation,RegisterValue,Result),
                                                            update_reg(-(reg(Register),Result),Registers,UpdatedRegisters).

vm(Program,FinalTrace,FinalStack,FinalCallStack,FinalRegisters,FinalFlag) :- instruction_pointer_map(Program,[],0,IPMap),
                                                      label_map(Program,[],0,LabelMap),
                                                      writeln('IP MAP IS ' + IPMap),
                                                      writeln('LABEL MAP IS ' + LabelMap),
                                                      exec_(reference(IPMap,LabelMap),stateIn(0,[],[],[],0),[],traceOut(FinalTrace,FinalStack,FinalCallStack,FinalRegisters,FinalFlag)).

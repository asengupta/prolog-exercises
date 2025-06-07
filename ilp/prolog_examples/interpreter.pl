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

exec_(IP,IPMap,LabelMap,Stack,Registers,Flag,TraceAcc,FinalTrace,FinalStack,FinalRegisters,FinalFlag) :- 
                                                    get2(IP,IPMap,Instr),
                                                    exec_helper(IP,IPMap,LabelMap,Stack,Instr,Registers,Flag,TraceAcc,FinalTrace,FinalStack,FinalRegisters,FinalFlag).

exec_helper(_,_,_,Stack,empty,Registers,Flag,TraceAcc,TraceAcc,Stack,Registers,Flag).
exec_helper(_,_,_,Stack,hlt,Registers,Flag,TraceAcc,TraceAcc,Stack,Registers,Flag) :- writeln('Halting program!!!!').
exec_helper(IP,IPMap,LabelMap,Stack,Instr,Registers,Flag,TraceAcc,FinalTrace,FinalStack,FinalRegisters,FinalFlag) :-
                                                        writeln('Interpreting ' + Instr),
                                                        NextIP is IP+1,
                                                        interpret(Instr,NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,UpdatedIP),
                                                        write('Next IP is ' + UpdatedIP),
                                                        exec_(UpdatedIP,IPMap,LabelMap,UpdatedStack,UpdatedRegisters,UpdatedFlag,TraceAcc,RemainingTrace,FinalStack,FinalRegisters,FinalFlag),
                                                        FinalTrace=[Instr|RemainingTrace],!.

isZero(0).
isNotZero(X) :- \+ isZero(X).
plusOne(X,PlusOne) :- PlusOne is X+1.
minusOne(X,MinusOne) :- MinusOne is X-1.

interpret_condition(_,NewIP,Flag,Condition,NewIP) :- call(Condition,Flag).
interpret_condition(OldIP,_,Flag,Condition,OldIP) :- \+ call(Condition,Flag).

interpret(mvc(reg(ToRegister),Value),NextIP,_,Stack,Registers,Flag,Stack,UpdatedRegisters,Flag,NextIP) :- 
                                                        writeln('In mvc' + ToRegister + Registers),
                                                        update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters).
interpret(cmp(reg(CmpRegister),CmpValue),NextIP,_,Stack,Registers,_,Stack,Registers,UpdatedFlag,NextIP) :- 
                                                        writeln('In cmp' + CmpRegister + Registers),
                                                        get2(CmpRegister,Registers,RegisterValue),
                                                        equate(RegisterValue,CmpValue,UpdatedFlag).

interpret(j(label(Label)),_,LabelMap,Stack,Registers,Flag,Stack,Registers,Flag,UpdatedIP) :- 
                                                        writeln('In jmp direct label' + Label + Registers),
                                                        get2(label(Label),LabelMap,UpdatedIP).

interpret(j(reg(JumpRegister)),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,UpdatedIP) :- 
                                                        writeln('In jmp indirect' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(j(RegisterValue),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,UpdatedIP).

interpret(j(JumpIP),_,_,_,Registers,Flag,_,Registers,Flag,JumpIP) :- writeln('In jmp direct' + JumpIP + Registers).

interpret(jz(reg(JumpRegister)),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln('In JZ indirect reg' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jz(RegisterValue),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP).

interpret(jnz(reg(JumpRegister)),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln('In JNZ indirect reg' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jnz(RegisterValue),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP).

interpret(jz(label(Label)),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln('In JZ label' + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jz(JumpIP),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP).

interpret(jnz(label(Label)),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln('In JNZ label' + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jnz(JumpIP),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,UpdatedFlag,NewIP).

interpret(jz(JumpIP),OldNextIP,_,Stack,Registers,Flag,Stack,Registers,Flag,UpdatedIP) :- interpret_condition(OldNextIP,JumpIP,Flag,isZero,UpdatedIP).
interpret(jnz(JumpIP),OldNextIP,_,Stack,Registers,Flag,Stack,Registers,Flag,UpdatedIP) :- interpret_condition(OldNextIP,JumpIP,Flag,isNotZero,UpdatedIP).

interpret(inc(reg(Register)),NextIP,_,Stack,Registers,Flag,Stack,UpdatedRegisters,Flag,NextIP) :- interpret_update_reg(reg(Register),plusOne,Registers,UpdatedRegisters).
interpret(dec(reg(Register)),NextIP,_,Stack,Registers,Flag,Stack,UpdatedRegisters,Flag,NextIP) :- interpret_update_reg(reg(Register),minusOne,Registers,UpdatedRegisters).
interpret(mul(reg(LHSRegister),reg(RHSRegister)),NextIP,_,Stack,Registers,Flag,Stack,UpdatedRegisters,Flag,NextIP) :- 
                get2(LHSRegister,Registers,LHSValue),
                get2(RHSRegister,Registers,RHSValue),
                Product is LHSValue*RHSValue,
                update_reg(-(reg(LHSRegister),Product),Registers,UpdatedRegisters).


interpret(term(String),NextIP,_,Stack,Registers,Flag,Stack,Registers,Flag,NextIP) :- writeln(String).
interpret(label(String),NextIP,_,Stack,Registers,Flag,Stack,Registers,Flag,NextIP) :- writeln('ENTER: ' + String ).

interpret(push(reg(Register)),NextIP,_,Stack,Registers,Flag,UpdatedStack,Registers,Flag,NextIP) :- 
                    get2(Register,Registers,RegisterValue),
                    push_(RegisterValue,Stack,UpdatedStack).

interpret(pop(reg(Register)),NextIP,_,Stack,Registers,Flag,UpdatedStack,UpdatedRegisters,Flag,NextIP) :- 
                                                                pop_(Stack,PoppedValue,UpdatedStack),
                                                                update_reg(-(reg(Register),PoppedValue),Registers,UpdatedRegisters).
interpret(push(V),NextIP,_,Stack,Registers,Flag,UpdatedStack,Registers,Flag,NextIP) :- push_(V,Stack,UpdatedStack).

interpret(call(label(LabelName)),NextIP,LabelMap,Stack,Registers,Flag,UpdatedStack,Registers,Flag,CallIP) :- 
                                                            get2(label(LabelName),LabelMap,CallIP),
                                                            push_(NextIP,Stack,UpdatedStack),
                                                            writeln('CALL: ' + LabelName + 'Stack is ' + UpdatedStack).
interpret(ret,_,_,Stack,Registers,Flag,UpdatedStack,Registers,Flag,PoppedValue) :- 
                                                            pop_(Stack,PoppedValue,UpdatedStack),
                                                            writeln('Returning from call...IP is ' + PoppedValue).
interpret(nop,NextIP,_,Stack,Registers,Flag,Stack,Registers,Flag,NextIP).
interpret(nop,NextIP,_,Stack,Registers,Flag,Stack,Registers,Flag,NextIP) :- writeln('HALTING PROGRAM!!!!!!').

interpret_update_reg(reg(Register),Calculation,Registers,UpdatedRegisters) :- 
                                                            get2(Register,Registers,RegisterValue),
                                                            call(Calculation,RegisterValue,Result),
                                                            update_reg(-(reg(Register),Result),Registers,UpdatedRegisters).

vm(Program,FinalTrace,FinalStack,FinalRegisters,FinalFlag) :- instruction_pointer_map(Program,[],0,IPMap),
                                                      label_map(Program,[],0,LabelMap),
                                                      writeln('IP MAP IS ' + IPMap),
                                                      writeln('LABEL MAP IS ' + LabelMap),
                                                      exec_(0,IPMap,LabelMap,[],[],0,[],FinalTrace,FinalStack,FinalRegisters,FinalFlag).

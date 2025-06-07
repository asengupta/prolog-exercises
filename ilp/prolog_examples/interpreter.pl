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

update_reg(-(reg(ToRegister),reg(FromRegister)),Registers,UpdatedRegisters) :- get2(FromRegister,Registers,Value),
                                                                               update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters).
update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters) :- put2(-(ToRegister,Value),Registers,UpdatedRegisters).

equate(LHS,LHS,0).
equate(LHS,RHS,1) :- LHS < RHS.
equate(LHS,RHS,-1) :- LHS > RHS.

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

exec_(IP,IPMap,LabelMap,Registers,Flag,TraceAcc,FinalTrace,FinalRegisters,FinalFlag) :- 
                                                    get2(IP,IPMap,Instr),
                                                    exec_helper(IP,IPMap,LabelMap,Instr,Registers,Flag,TraceAcc,FinalTrace,FinalRegisters,FinalFlag).

exec_helper(_,_,_,empty,Registers,Flag,TraceAcc,TraceAcc,Registers,Flag).
exec_helper(IP,IPMap,LabelMap,Instr,Registers,Flag,TraceAcc,FinalTrace,FinalRegisters,FinalFlag) :-
                                                        writeln("Interpreting " + Instr),
                                                        NextIP is IP+1,
                                                        interpret(Instr,NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,UpdatedIP),
                                                        write("Next IP is " + UpdatedIP),
                                                        exec_(UpdatedIP,IPMap,LabelMap,UpdatedRegisters,UpdatedFlag,TraceAcc,RemainingTrace,FinalRegisters,FinalFlag),
                                                        FinalTrace=[Instr|RemainingTrace],!.

interpret_condition(_,NewIP,Flag,Condition,NewIP) :- call(Condition,Flag).
interpret_condition(OldIP,_,Flag,Condition,OldIP) :- \+ call(Condition,Flag).

isZero(0).
isNotZero(X) :- \+ isZero(X).
plusOne(X,PlusOne) :- PlusOne is X+1.
minusOne(X,MinusOne) :- MinusOne is X-1.

interpret(mvc(reg(ToRegister),Value),NextIP,_,Registers,Flag,UpdatedRegisters,Flag,NextIP) :- 
                                                        writeln("In mvc" + ToRegister + Registers),
                                                        update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters).
interpret(cmp(reg(CmpRegister),CmpValue),NextIP,_,Registers,_,Registers,UpdatedFlag,NextIP) :- 
                                                        writeln("In cmp" + CmpRegister + Registers),
                                                        get2(CmpRegister,Registers,RegisterValue),
                                                        equate(RegisterValue,CmpValue,UpdatedFlag).

interpret(j(label(Label)),_,LabelMap,Registers,Flag,Registers,Flag,UpdatedIP) :- 
                                                        writeln("In jmp direct label" + Label + Registers),
                                                        get2(label(Label),LabelMap,UpdatedIP).

interpret(j(reg(JumpRegister)),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,UpdatedIP) :- 
                                                        writeln("In jmp indirect" + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(j(RegisterValue),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,UpdatedIP).

interpret(j(JumpIP),_,_,Registers,Flag,Registers,Flag,JumpIP) :- writeln("In jmp direct" + JumpIP + Registers).

interpret(jz(reg(JumpRegister)),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln("In JZ indirect reg" + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jz(RegisterValue),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP).

interpret(jnz(reg(JumpRegister)),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln("In JNZ indirect reg" + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jnz(RegisterValue),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP).


interpret(jz(label(Label)),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln("In JZ label" + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jz(JumpIP),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP).

interpret(jnz(label(Label)),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP) :- 
                                                        writeln("In JNZ label" + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jnz(JumpIP),NextIP,LabelMap,Registers,Flag,UpdatedRegisters,UpdatedFlag,NewIP).


interpret(jz(JumpIP),OldNextIP,_,Registers,Flag,Registers,Flag,UpdatedIP) :- interpret_condition(OldNextIP,JumpIP,Flag,isZero,UpdatedIP).
interpret(jnz(JumpIP),OldNextIP,_,Registers,Flag,Registers,Flag,UpdatedIP) :- interpret_condition(OldNextIP,JumpIP,Flag,isNotZero,UpdatedIP).

interpret(inc(reg(Register)),NextIP,_,Registers,Flag,UpdatedRegisters,Flag,NextIP) :- interpret_update_reg(reg(Register),plusOne,Registers,UpdatedRegisters).
interpret(dec(reg(Register)),NextIP,_,Registers,Flag,UpdatedRegisters,Flag,NextIP) :- interpret_update_reg(reg(Register),minusOne,Registers,UpdatedRegisters).

interpret(term(String),NextIP,_,Registers,Flag,Registers,Flag,NextIP) :- writeln(String).
interpret(label(String),NextIP,_,Registers,Flag,Registers,Flag,NextIP) :- writeln("ENTER: " + String).


interpret_update_reg(reg(Register),Calculation,Registers,UpdatedRegisters) :- 
                                                            get2(Register,Registers,RegisterValue),
                                                            call(Calculation,RegisterValue,Result),
                                                            update_reg(-(reg(Register),Result),Registers,UpdatedRegisters).

trace(Program,FinalTrace,FinalRegisters,FinalFlag) :- instruction_pointer_map(Program,[],0,IPMap),
                                                      label_map(Program,[],0,LabelMap),
                                                      writeln("IP MAP IS " + IPMap),
                                                      writeln("LABEL MAP IS " + LabelMap),
                                                      exec_(0,IPMap,LabelMap,[],0,[],FinalTrace,FinalRegisters,FinalFlag).

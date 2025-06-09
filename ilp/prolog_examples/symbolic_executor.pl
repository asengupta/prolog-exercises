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

equate(LHS,LHS,const(0)).
equate(const(LHS),const(RHS),const(1)) :- LHS < RHS.
equate(const(LHS),const(RHS),const(-1)) :- LHS > RHS.

update_reg(-(reg(ToRegister),reg(FromRegister)),Registers,UpdatedRegisters) :- get2(FromRegister,Registers,Value),
                                                                               update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters).
update_reg(-(reg(ToRegister),Value),Registers,UpdatedRegisters) :- put2(-(ToRegister,Value),Registers,UpdatedRegisters).

instruction_pointer_map([],IPMap,_,IPMap).
instruction_pointer_map([Instr|T],IPMap,IPCounter,FinalIPMap) :- writeln('Testing'),
                                                                 put2(-(IPCounter,Instr),IPMap,UpdatedIPMap),
                                                                 plusOne(IPCounter,UpdatedIPCounter),
                                                                 instruction_pointer_map(T,UpdatedIPMap,UpdatedIPCounter,FinalIPMap).
label_map([],LabelMap,_,LabelMap).
label_map([label(Label)|T],LabelMap,IPCounter,FinalLabelMap) :- put2(-(label(Label),IPCounter),LabelMap,UpdatedLabelMap),
                                                                 plusOne(IPCounter,UpdatedIPCounter),
                                                                 label_map(T,UpdatedLabelMap,UpdatedIPCounter,FinalLabelMap),
                                                                 !.
label_map([_|T],LabelMap,IPCounter,FinalLabelMap) :- plusOne(IPCounter,UpdatedIPCounter),
                                                     label_map(T,LabelMap,UpdatedIPCounter,FinalLabelMap).

toTraceOut(Trace,vmState(IP,Stack,CallStack,Registers,VmFlags),traceOut(Trace,IP,Stack,CallStack,Registers,VmFlags)). 

exec_(vmMaps(IPMap,LabelMap),vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,StateOut) :- 
                                                    get2(IP,IPMap,Instr),
                                                    exec_helper(Instr,vmMaps(IPMap,LabelMap),
                                                        vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,StateOut).

exec_helper(empty,_,StateIn,TraceAcc,TraceOut) :- toTraceOut(TraceAcc,StateIn,TraceOut).
exec_helper(hlt,_,StateIn,TraceAcc,TraceOut) :- toTraceOut(TraceAcc,StateIn,TraceOut),writeln('Halting program!!!!').
exec_helper(Instr,VmMaps,vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,traceOut(FinalTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags)) :-
                                                        writeln('Interpreting ' + Instr + 'StateIn is ' + vmState(IP,Stack,CallStack,Registers,VmFlags)),
                                                        plusOne(IP,NextIP),
                                                        interpret(Instr,VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags)),
                                                        write('Next IP is ' + UpdatedIP),
                                                        exec_(VmMaps,vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags),TraceAcc,traceOut(RemainingTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags)),
                                                        FinalTrace=[traceEntry(Instr,vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags))|RemainingTrace],!.

isZero(const(0)).
isNotZero(X) :- \+ isZero(X).

plusOne(sym(X),inc(sym(X))).
plusOne(const(X),const(PlusOne)) :- PlusOne is X+1.

minusOne(sym(X),dec(sym(X))).

product(const(LHS),const(RHS),const(Product)) :- Product is LHS*RHS.
product(sym(LHS),sym(RHS),sym(product(sym(LHS),sym(RHS)))).
product(sym(LHS),const(RHS),sym(product(sym(LHS),const(RHS)))).
product(const(LHS),sym(RHS),sym(product(const(LHS),sym(RHS)))).

interpret_condition(_,NewIP,flags(zero(ZeroFlagValue)),Condition,NewIP) :- call(Condition,ZeroFlagValue).
interpret_condition(OldIP,_,flags(zero(ZeroFlagValue)),Condition,OldIP) :- \+ call(Condition,ZeroFlagValue).

interpret(mvc(reg(ToRegister),sym(Symbol)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags)) :- 
                                                        writeln('In mvc const' + ToRegister + Registers),
                                                        update_reg(-(reg(ToRegister),sym(Symbol)),Registers,UpdatedRegisters).
interpret(mvc(reg(ToRegister),const(ConstValue)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags)) :- 
                                                        writeln('In mvc const' + ToRegister + Registers),
                                                        update_reg(-(reg(ToRegister),const(ConstValue)),Registers,UpdatedRegisters).
interpret(mvc(reg(ToRegister),reg(FromRegister)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags)) :- 
                                                        writeln('In mvc reg' + ToRegister + Registers),
                                                        get2(FromRegister,Registers,FromValue),
                                                        update_reg(-(reg(ToRegister),FromValue),Registers,UpdatedRegisters).
interpret(cmp(reg(LHSRegister),const(ConstValue)),_,vmState(NextIP,Stack,CallStack,Registers,_),vmState(NextIP,Stack,CallStack,Registers,UpdatedVmFlags)) :- 
                                                        writeln('In cmp' + LHSRegister + Registers),
                                                        get2(LHSRegister,Registers,LHSValue),
                                                        UpdatedVmFlags=flags(zero(sym(cmp(LHSValue,const(ConstValue))))).
interpret(cmp(reg(LHSRegister),reg(RHSRegister)),_,vmState(NextIP,Stack,CallStack,Registers,_),vmState(NextIP,Stack,CallStack,Registers,UpdatedVmFlags)) :- 
                                                        writeln('In cmp' + LHSRegister + RHSRegister + Registers),
                                                        get2(LHSRegister,Registers,LHSValue),
                                                        get2(RHSRegister,Registers,RHSValue),
                                                        UpdatedVmFlags=flags(zero(sym(cmp(LHSValue,RHSValue)))).

interpret(j(label(Label)),_,VmState,VmState) :- 
                                                        writeln('In jmp direct label' + Label).

interpret(j(reg(JumpRegister)),_,VmState,VmState) :- 
                                                        writeln('In jmp indirect' + JumpRegister).

interpret(j(JumpIP),_,vmState(_,Stack,CallStack,Registers,VmFlags),vmState(JumpIP,Stack,CallStack,Registers,VmFlags)) :- writeln('In jmp direct' + JumpIP + Registers).

interpret(jz(reg(JumpRegister)),_,VmState,VmState) :- 
                                                        writeln('In JZ indirect reg' + JumpRegister).

interpret(jnz(reg(JumpRegister)),_,VmState,VmState) :- 
                                                        writeln('In JNZ indirect reg' + JumpRegister).

interpret(jz(label(Label)),_,VmState,VmState) :- 
                                                        writeln('In JZ label' + Label).

interpret(jnz(label(Label)),_,VmState,VmState) :- 
                                                        writeln('In JNZ label' + Label).

interpret(jz(_),_,VmState,VmState).
interpret(jnz(_),_,VmState,VmState).

interpret(inc(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags)) :- interpret_update_reg(reg(Register),plusOne,Registers,UpdatedRegisters).
interpret(dec(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags)) :- interpret_update_reg(reg(Register),minusOne,Registers,UpdatedRegisters).
interpret(mul(reg(LHSRegister),reg(RHSRegister)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags)) :- 
                get2(LHSRegister,Registers,LHSValue),
                get2(RHSRegister,Registers,RHSValue),
                writeln("LHS is " + LHSRegister + ":" + LHSValue),
                writeln("RHS is " + RHSRegister + ":" + RHSValue),
                product(LHSValue,RHSValue,Product),
                writeln("And result is " + Product),
                update_reg(-(reg(LHSRegister),Product),Registers,UpdatedRegisters).

interpret(term(String),_,VmState,VmState) :- writeln(String).
interpret(label(String),_,VmState,VmState) :- writeln('ENTER: ' + String ).

interpret(push(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,Registers,VmFlags)) :- 
                    get2(Register,Registers,RegisterValue),
                    push_(RegisterValue,Stack,UpdatedStack).

interpret(pop(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,UpdatedRegisters,VmFlags)) :- 
                                                                pop_(Stack,PoppedValue,UpdatedStack),
                                                                update_reg(-(reg(Register),PoppedValue),Registers,UpdatedRegisters).
interpret(push(const(X)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,Registers,VmFlags)) :- push_(const(X),Stack,UpdatedStack).

interpret(call(label(LabelName)),vmMaps(_,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(CallIP,Stack,UpdatedCallStack,Registers,VmFlags)) :- 
                                                            get2(label(LabelName),LabelMap,CallIP),
                                                            push_(NextIP,CallStack,UpdatedCallStack),
                                                            writeln('CALL: ' + LabelName + 'Stack is ' + UpdatedCallStack).
interpret(ret,_,vmState(_,Stack,CallStack,Registers,VmFlags),vmState(PoppedValue,Stack,UpdatedCallStack,Registers,VmFlags)) :- 
                                                            pop_(CallStack,PoppedValue,UpdatedCallStack),
                                                            writeln('Returning from call...IP is ' + PoppedValue).
interpret(nop,_,VmState,VmState).

interpret_update_reg(reg(Register),Calculation,Registers,UpdatedRegisters) :- 
                                                            call(Calculation,sym(reg(Register)),Result),
                                                            update_reg(-(reg(Register),Result),Registers,UpdatedRegisters).

vm(Program,FinalTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags) :- 
                                                      instruction_pointer_map(Program,[],const(0),IPMap),
                                                      label_map(Program,[],const(0),LabelMap),
                                                      writeln('IP MAP IS ' + IPMap),
                                                      writeln('LABEL MAP IS ' + LabelMap),
                                                      exec_(vmMaps(IPMap,LabelMap),vmState(const(0),[],[],[],flags(zero(0))),[],traceOut(FinalTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags)).

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
instruction_pointer_map([Instr|T],IPMap,IPCounter,FinalIPMap) :- put2(-(IPCounter,Instr),IPMap,UpdatedIPMap),
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

exec_(vmMaps(IPMap,LabelMap),vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,StateOut,Env) :- 
                                                    get2(IP,IPMap,Instr),
                                                    exec_helper(Instr,vmMaps(IPMap,LabelMap),
                                                        vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,StateOut,Env).

exec_helper(empty,_,StateIn,TraceAcc,TraceOut,_) :- toTraceOut(TraceAcc,StateIn,TraceOut).
exec_helper(hlt,_,StateIn,TraceAcc,TraceOut,env(log(_,Info,_,_))) :- toTraceOut(TraceAcc,StateIn,TraceOut),call(Info,'Halting program HAHAHAHA!!!!').
exec_helper(Instr,VmMaps,vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,traceOut(FinalTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags),env(log(Debug,Info,Warning,Error))) :-
                                                        call(Debug,'Interpreting ~w and StateIn is ~w', [Instr, vmState(IP,Stack,CallStack,Registers,VmFlags)]),
                                                        plusOne(IP,NextIP),
                                                        interpret(Instr,VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags),env(log(Debug,Info,Warning,Error))),
                                                        write('Next IP is ' + UpdatedIP),
                                                        exec_(VmMaps,vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags),TraceAcc,traceOut(RemainingTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags),env(log(Debug,Info,Warning,Error))),
                                                        FinalTrace=[traceEntry(Instr,vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags))|RemainingTrace],!.

isZero(const(0)).
isNotZero(X) :- \+ isZero(X).

plusOne(const(X),const(PlusOne)) :- PlusOne is X+1.
minusOne(const(X),const(MinusOne)) :- MinusOne is X-1.
product(const(LHS),const(RHS),const(Product)) :- Product is LHS*RHS.

interpret_condition(_,NewIP,flags(zero(ZeroFlagValue)),Condition,NewIP) :- call(Condition,ZeroFlagValue).
interpret_condition(OldIP,_,flags(zero(ZeroFlagValue)),Condition,OldIP) :- \+ call(Condition,ZeroFlagValue).

interpret(mvc(reg(ToRegister),const(ConstValue)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),_) :- 
                                                        writeln('In mvc const' + ToRegister + Registers),
                                                        update_reg(-(reg(ToRegister),const(ConstValue)),Registers,UpdatedRegisters).
interpret(mvc(reg(ToRegister),reg(FromRegister)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),_) :- 
                                                        writeln('In mvc reg' + ToRegister + Registers),
                                                        get2(FromRegister,Registers,RegisterValue),
                                                        update_reg(-(reg(ToRegister),RegisterValue),Registers,UpdatedRegisters).
interpret(cmp(reg(CmpRegister),const(ConstValue)),_,vmState(NextIP,Stack,CallStack,Registers,_),vmState(NextIP,Stack,CallStack,Registers,flags(zero(UpdatedVmFlags))),_) :- 
                                                        writeln('In cmp' + CmpRegister + Registers),
                                                        get2(CmpRegister,Registers,RegisterValue),
                                                        equate(RegisterValue,const(ConstValue),UpdatedVmFlags).
interpret(cmp(reg(LHSRegister),reg(RHSRegister)),_,vmState(NextIP,Stack,CallStack,Registers,_),vmState(NextIP,Stack,CallStack,Registers,flags(zero(UpdatedVmFlags))),_) :- 
                                                        writeln('In cmp' + LHSRegister + RHSRegister + Registers),
                                                        get2(LHSRegister,Registers,LHSRegisterValue),
                                                        get2(RHSRegister,Registers,RHSRegisterValue),
                                                        equate(LHSRegisterValue,RHSRegisterValue,UpdatedVmFlags).

interpret(j(label(Label)),vmMaps(_,LabelMap),vmState(_,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,Stack,CallStack,Registers,VmFlags),_) :- 
                                                        writeln('In jmp direct label' + Label + Registers),
                                                        get2(label(Label),LabelMap,UpdatedIP).

interpret(j(reg(JumpRegister)),VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env) :- 
                                                        writeln('In jmp indirect' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(j(RegisterValue),VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env).

interpret(j(JumpIP),_,vmState(_,Stack,CallStack,Registers,VmFlags,_),vmState(JumpIP,Stack,CallStack,Registers,VmFlags),_) :- writeln('In jmp direct' + JumpIP + Registers).

interpret(jz(reg(JumpRegister)),VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env) :- 
                                                        writeln('In JZ indirect reg' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jz(RegisterValue),VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env).

interpret(jnz(reg(JumpRegister)),VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env) :- 
                                                        writeln('In JNZ indirect reg' + JumpRegister + Registers),
                                                        get2(JumpRegister,Registers,RegisterValue),
                                                        interpret(jnz(RegisterValue),VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env).

interpret(jz(label(Label)),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env) :- 
                                                        writeln('In JZ label' + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jz(JumpIP),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env).

interpret(jnz(label(Label)),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env) :- 
                                                        writeln('In JNZ label' + Label + Registers),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jnz(JumpIP),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,Env).

interpret(jz(JumpIP),_,vmState(OldNextIP,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,Stack,CallStack,Registers,VmFlags),_) :- interpret_condition(OldNextIP,JumpIP,VmFlags,isZero,UpdatedIP).
interpret(jnz(JumpIP),_,vmState(OldNextIP,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,Stack,CallStack,Registers,VmFlags),_) :- interpret_condition(OldNextIP,JumpIP,VmFlags,isNotZero,UpdatedIP).

interpret(inc(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),_) :- interpret_update_reg(reg(Register),plusOne,Registers,UpdatedRegisters).
interpret(dec(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),_) :- interpret_update_reg(reg(Register),minusOne,Registers,UpdatedRegisters).
interpret(mul(reg(LHSRegister),reg(RHSRegister)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),_) :- 
                get2(LHSRegister,Registers,LHSValue),
                get2(RHSRegister,Registers,RHSValue),
                product(LHSValue,RHSValue,Product),
                update_reg(-(reg(LHSRegister),Product),Registers,UpdatedRegisters).

interpret(term(String),_,VmState,VmState,env(log(_,Info,_,_))) :- call(Info,String).
interpret(label(String),_,VmState,VmState,env(log(_,Info,_,_))) :- call(Info,'ENTER: ~w',[String]).

interpret(push(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,Registers,VmFlags),_) :- 
                    get2(Register,Registers,RegisterValue),
                    push_(RegisterValue,Stack,UpdatedStack).

interpret(pop(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,UpdatedRegisters,VmFlags),_) :- 
                                                                pop_(Stack,PoppedValue,UpdatedStack),
                                                                update_reg(-(reg(Register),PoppedValue),Registers,UpdatedRegisters).
interpret(push(V),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,Registers,VmFlags),_) :- push_(V,Stack,UpdatedStack).

interpret(call(label(LabelName)),vmMaps(_,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(CallIP,Stack,UpdatedCallStack,Registers,VmFlags),_) :- 
                                                            get2(label(LabelName),LabelMap,CallIP),
                                                            push_(NextIP,CallStack,UpdatedCallStack),
                                                            writeln('CALL: ' + LabelName + 'Stack is ' + UpdatedCallStack).
interpret(ret,_,vmState(_,Stack,CallStack,Registers,VmFlags),vmState(PoppedValue,Stack,UpdatedCallStack,Registers,VmFlags),_) :- 
                                                            pop_(CallStack,PoppedValue,UpdatedCallStack),
                                                            writeln('Returning from call...IP is ' + PoppedValue).
interpret(nop,_,VmState,VmState,_).

interpret_update_reg(reg(Register),Calculation,Registers,UpdatedRegisters) :- 
                                                            get2(Register,Registers,RegisterValue),
                                                            call(Calculation,RegisterValue,Result),
                                                            update_reg(-(reg(Register),Result),Registers,UpdatedRegisters).

log_with_level(LogLevel,Message) :- format('[~w]: ~w~n',[LogLevel,Message]).

debug(Message) :- log_with_level('DEBUG',Message).
debug(FormatString,Args) :- format(string(CoreMessage),FormatString,Args),log_with_level('DEBUG',CoreMessage).

info(Message) :- log_with_level('INFO',Message).
info(FormatString,Args) :- format(string(CoreMessage),FormatString,Args),log_with_level('INFO',CoreMessage).

warning(Message) :- log_with_level('WARN',Message).
warning(FormatString,Args) :- format(string(CoreMessage),FormatString,Args),log_with_level('WARN',CoreMessage).

error(Message) :- log_with_level('ERROR',Message).
error(FormatString,Args) :- format(string(CoreMessage),FormatString,Args),log_with_level('ERROR',CoreMessage).

dont_log(_).
dont_log(_,_).

vm(Program,FinalTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags) :- 
                                                      instruction_pointer_map(Program,[],const(0),IPMap),
                                                      label_map(Program,[],const(0),LabelMap),
                                                      writeln('IP MAP IS ' + IPMap),
                                                      writeln('LABEL MAP IS ' + LabelMap),
                                                      exec_(vmMaps(IPMap,LabelMap),vmState(const(0),[],[],[],flags(zero(0))),[],traceOut(FinalTrace,FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags),env(log(dont_log,info,warning,error))).

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
equate(sym(LHS),sym(RHS),sym(cmp(sym(LHS)),sym(RHS))).
equate(sym(LHS),const(RHS),sym(cmp(sym(LHS)),const(RHS))).
equate(const(LHS),sym(RHS),sym(cmp(const(LHS)),sym(RHS))).
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

toTraceOut(Trace,VmState,traceOut(Trace,VmState)).

exec_(_,vmState(IP,Stack,CallStack,Registers,flags(ZeroFlag,hlt(true),BranchFlag)),
                  TraceAcc,
                  traceOut(TraceAcc,vmState(IP,Stack,CallStack,Registers,flags(ZeroFlag,hlt(true),BranchFlag))),
                  env(log(_,Info,_,_))) :- call(Info,'EXITING PROGRAM LOOP!!!').

exec_(vmMaps(IPMap,LabelMap),vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,StateOut,Env) :- 
                                                    get2(IP,IPMap,Instr),
                                                    exec_helper(Instr,vmMaps(IPMap,LabelMap),
                                                        vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,StateOut,Env).

exec_helper(empty,VmMaps,vmState(IP,Stack,CallStack,Registers,flags(ZeroFlag,_,BranchFlag)),
                    TraceAcc,
                    traceOut(TraceAcc,ExitState),
                    env(log(Debug,Info,Warn,Error))) :- 
                            ExitState=vmState(IP,Stack,CallStack,Registers,flags(ZeroFlag,hlt(true),BranchFlag)),
                            call(Warn,'No other instruction found, but no HLT is present. Halting program.'),
                            exec_(VmMaps,ExitState,TraceAcc,traceOut(TraceAcc,ExitState),env(log(Debug,Info,Warn,Error))).

exec_helper(Instr,VmMaps,vmState(IP,Stack,CallStack,Registers,VmFlags),TraceAcc,traceOut(FinalTrace,vmState(FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags)),env(log(Debug,Info,Warning,Error))) :-
                                                        call(Debug,'Interpreting ~w and StateIn is ~w', [Instr, vmState(IP,Stack,CallStack,Registers,VmFlags)]),
                                                        plusOne(IP,NextIP),
                                                        interpret(Instr,VmMaps,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags),env(log(Debug,Info,Warning,Error))),
                                                        (shouldBranch(UpdatedVmFlags)->
                                                            (
                                                                terminateForBranch(vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags),vmState(FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags)),
                                                                FinalTrace=TraceAcc
                                                            );
                                                            (
                                                                call(Debug,'Next IP is ~w',[UpdatedIP]),
                                                                exec_(VmMaps,vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags),TraceAcc,traceOut(RemainingTrace,vmState(FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags)),env(log(Debug,Info,Warning,Error))),
                                                                FinalTrace=[traceEntry(Instr,vmState(UpdatedIP,UpdatedStack,UpdatedCallStack,UpdatedRegisters,UpdatedVmFlags))|RemainingTrace]
                                                            )
                                                        ),
                                                        !.

terminateForBranch(VmState,VmState).
shouldBranch(flags(_,_,branch(true))).

isZero(const(0)).
isNotZero(X) :- \+ isZero(X).

plusOne(sym(X),sym(inc(sym(X)))).
plusOne(const(X),const(PlusOne)) :- PlusOne is X+1.

minusOne(sym(X),sym(dec(sym(X)))).
minusOne(const(X),const(MinusOne)) :- MinusOne is X-1.

product(const(LHS),const(RHS),const(Product)) :- Product is LHS*RHS.
product(sym(LHS),sym(RHS),sym(product(sym(LHS),sym(RHS)))).
product(sym(LHS),const(RHS),sym(product(sym(LHS),const(RHS)))).
product(const(LHS),sym(RHS),sym(product(const(LHS),sym(RHS)))).

interpret_symbolic_condition(OldNextIP,_,flags(ZeroFlag,HltFlag,_),_,flags(ZeroFlag,HltFlag,branch(true)),OldNextIP).
interpret_condition(_,NewIP,flags(zero(ZeroFlagValue),HltFlag,BranchFlag),Condition,flags(zero(ZeroFlagValue),HltFlag,BranchFlag),NewIP) :- call(Condition,ZeroFlagValue).
interpret_condition(OldIP,_,flags(zero(ZeroFlagValue),HltFlag,BranchFlag),Condition,flags(zero(ZeroFlagValue),HltFlag,BranchFlag),OldIP) :- \+ call(Condition,ZeroFlagValue).

interpret(mvc(reg(ToRegister),sym(Symbol)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),env(log(Debug,_,_,_))) :- 
                                                        call(Debug,'In mvc sym: ~w and Registers are: ~w', [ToRegister,Registers]),
                                                        update_reg(-(reg(ToRegister),sym(Symbol)),Registers,UpdatedRegisters).
interpret(mvc(reg(ToRegister),const(ConstValue)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),env(log(Debug,_,_,_))) :- 
                                                        call(Debug,'In mvc const: ~w and Registers are: ~w', [ToRegister,Registers]),
                                                        update_reg(-(reg(ToRegister),const(ConstValue)),Registers,UpdatedRegisters).
interpret(mvc(reg(ToRegister),reg(FromRegister)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),env(log(Debug,_,_,_))) :- 
                                                        call(Debug,'In mvc reg: ~w and Registers are: ~w',[ToRegister,Registers]),
                                                        get2(FromRegister,Registers,FromValue),
                                                        update_reg(-(reg(ToRegister),FromValue),Registers,UpdatedRegisters).
interpret(cmp(reg(LHSRegister),const(ConstValue)),_,vmState(NextIP,Stack,CallStack,Registers,flags(_,HltFlag,BranchFlag)),StateOut,env(log(Debug,_,_,_))) :- 
                                                        call(Debug,'In cmp(reg,const): ~w and Registers are: ~w',[LHSRegister,Registers]),
                                                        get2(LHSRegister,Registers,LHSValue),
                                                        equate(LHSValue,const(ConstValue),ComparisonResult),
                                                        UpdatedVmFlags=flags(zero(ComparisonResult),HltFlag,BranchFlag),
                                                        StateOut=vmState(NextIP,Stack,CallStack,Registers,UpdatedVmFlags).
interpret(cmp(reg(LHSRegister),reg(RHSRegister)),_,vmState(NextIP,Stack,CallStack,Registers,flags(_,HltFlag,BranchFlag)),StateOut,env(log(Debug,_,_,_))) :- 
                                                        call(Debug,'In cmp(reg,reg): ~w,~w and Registers are: ~w',[LHSRegister,RHSRegister,Registers]),
                                                        get2(LHSRegister,Registers,LHSValue),
                                                        get2(RHSRegister,Registers,RHSValue),
                                                        equate(LHSValue,RHSValue,ComparisonResult),
                                                        UpdatedVmFlags=flags(zero(ComparisonResult),HltFlag,BranchFlag),
                                                        StateOut=vmState(NextIP,Stack,CallStack,Registers,UpdatedVmFlags).

interpret(j(label(Label)),vmMaps(_,LabelMap),vmState(_,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,Stack,CallStack,Registers,VmFlags),env(log(Debug,_,_,_))) :- 
                                                        call(Debug,'In jmp direct label: ~w and Registers are: ~w',[Label,Registers]),
                                                        get2(label(Label),LabelMap,UpdatedIP).

interpret(j(JumpIP),_,vmState(_,Stack,CallStack,Registers,VmFlags),vmState(JumpIP,Stack,CallStack,Registers,VmFlags),env(log(Debug,_,_,_))) :- call(Debug,'In jmp direct',[JumpIP,Registers]).

interpret(jz(label(Label)),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,env(log(Debug,Info,Warning,Error))) :- 
                                                        call(Debug,'In JZ label: ~w and Registers are: ~w',[Label,Registers]),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jz(JumpIP),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,env(log(Debug,Info,Warning,Error))).

interpret(jnz(label(Label)),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,env(log(Debug,Info,Warning,Error))) :- 
                                                        call(Debug,'In JNZ label: ~w and Registers are: ~w',[Label,Registers]),
                                                        get2(label(Label),LabelMap,JumpIP),
                                                        interpret(jnz(JumpIP),vmMaps(IPMap,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),StateOut,env(log(Debug,Info,Warning,Error))).

interpret(jz(JumpIP),_,vmState(OldNextIP,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,Stack,CallStack,Registers,UpdatedVmFlags),_) :- interpret_symbolic_condition(OldNextIP,JumpIP,VmFlags,isZero,UpdatedVmFlags,UpdatedIP).
interpret(jnz(JumpIP),_,vmState(OldNextIP,Stack,CallStack,Registers,VmFlags),vmState(UpdatedIP,Stack,CallStack,Registers,UpdatedVmFlags),_) :- interpret_symbolic_condition(OldNextIP,JumpIP,VmFlags,isNotZero,UpdatedVmFlags,UpdatedIP).

interpret(jz(_),_,VmState,VmState,_).
interpret(jnz(_),_,VmState,VmState,_).

interpret(inc(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),Env) :- interpret_update_reg(reg(Register),plusOne,Registers,UpdatedRegisters,Env).
interpret(dec(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),Env) :- interpret_update_reg(reg(Register),minusOne,Registers,UpdatedRegisters,Env).
interpret(mul(reg(LHSRegister),reg(RHSRegister)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),env(log(Debug,_,_,_))) :- 
                get2(LHSRegister,Registers,LHSValue),
                get2(RHSRegister,Registers,RHSValue),
                call(Debug,'LHS is ~w,~w',[LHSRegister,LHSValue]),
                call(Debug,'RHS is ~w,~w',[RHSRegister,RHSValue]),
                product(LHSValue,RHSValue,Product),
                call(Debug,'And result is ~w',[Product]),
                update_reg(-(reg(LHSRegister),Product),Registers,UpdatedRegisters).
interpret(mul(reg(LHSRegister),const(ConstValue)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),env(log(Debug,_,_,_))) :- 
                get2(LHSRegister,Registers,LHSValue),
                call(Debug,'LHS is ~w',[LHSRegister]),
                call(Debug,'RHS is ~w',[const(ConstValue)]),
                product(LHSValue,const(ConstValue),Product),
                call(Debug,'And result is ~w',[Product]),
                update_reg(-(reg(LHSRegister),Product),Registers,UpdatedRegisters).

interpret(mul(reg(LHSRegister),sym(Symbol)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,Stack,CallStack,UpdatedRegisters,VmFlags),env(log(Debug,_,_,_))) :- 
                get2(LHSRegister,Registers,LHSValue),
                call(Debug,'LHS is ~w',[LHSRegister]),
                call(Debug,'RHS is ~w',[sym(Symbol)]),
                product(LHSValue,sym(Symbol),Product),
                call(Debug,'And result is ~w',[Product]),
                update_reg(-(reg(LHSRegister),Product),Registers,UpdatedRegisters).

interpret(term(String),_,VmState,VmState,env(log(_,Info,_,_))) :- call(Info,String).
interpret(label(String),_,VmState,VmState,env(log(_,Info,_,_))) :- call(Info,'ENTER: ~w',[String]).

interpret(push(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,Registers,VmFlags),_) :- 
                    get2(Register,Registers,RegisterValue),
                    push_(RegisterValue,Stack,UpdatedStack).

interpret(pop(reg(Register)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,UpdatedRegisters,VmFlags),_) :- 
                                                                pop_(Stack,PoppedValue,UpdatedStack),
                                                                update_reg(-(reg(Register),PoppedValue),Registers,UpdatedRegisters).
interpret(push(const(X)),_,vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(NextIP,UpdatedStack,CallStack,Registers,VmFlags),_) :- push_(const(X),Stack,UpdatedStack).

interpret(call(label(LabelName)),vmMaps(_,LabelMap),vmState(NextIP,Stack,CallStack,Registers,VmFlags),vmState(CallIP,Stack,UpdatedCallStack,Registers,VmFlags),env(log(_,Info,_,_))) :- 
                                                            get2(label(LabelName),LabelMap,CallIP),
                                                            push_(NextIP,CallStack,UpdatedCallStack),
                                                            call(Info,'CALL: ~w and Stack is ~w', [LabelName,UpdatedCallStack]).
interpret(ret,_,vmState(_,Stack,CallStack,Registers,VmFlags),vmState(PoppedValue,Stack,UpdatedCallStack,Registers,VmFlags),env(log(_,Info,_,_))) :- 
                                                            pop_(CallStack,PoppedValue,UpdatedCallStack),
                                                            call(Info,'EXIT...Return IP is ~w',[PoppedValue]).
interpret(nop,_,VmState,VmState,_).
interpret(hlt,_,vmState(NextIP,Stack,CallStack,Registers,flags(ZeroFlag,_,BranchFlag)),vmState(NextIP,Stack,CallStack,Registers,flags(ZeroFlag,hlt(true),BranchFlag)),env(log(Debug,_,_,_))) :-
        call(Debug,'Called HLT').

interpret_update_reg(reg(Register),Calculation,Registers,UpdatedRegisters,env(log(Debug,_,_,_))) :- 
                                                            get2(Register,Registers,RegisterValue),
                                                            call(Debug,"Will decrement ~w",[RegisterValue]),
                                                            call(Calculation,RegisterValue,Result),
                                                            call(Debug,"Result is ~w",[Result]),
                                                            update_reg(-(reg(Register),Result),Registers,UpdatedRegisters).

debug(Message) :- log_with_level('DEBUG',Message,[]).
debug(FormatString,Args) :- log_with_level('DEBUG',FormatString,Args).

info(Message) :- log_with_level('INFO',Message,[]).
info(FormatString,Args) :- log_with_level('INFO',FormatString,Args).

warning(Message) :- log_with_level('WARN',Message,[]).
warning(FormatString,Args) :- log_with_level('WARN',FormatString,Args).

error(Message) :- log_with_level('ERROR',Message,[]).
error(FormatString,Args) :- log_with_level('ERROR',FormatString,Args).

dont_log(_).
dont_log(_,_).

execute_symbolic(Program,AllWorlds) :- instruction_pointer_map(Program,[],const(0),IPMap),
                                       label_map(Program,[],const(0),LabelMap),
                                       info('IP MAP IS ~w',[IPMap]),
                                       info('LABEL MAP IS ~w',[LabelMap]),
                                       StateIn=vmState(const(0),[],[],[],flags(zero(0),hlt(false),branch(false))),
                                       explore(Program,StateIn,vmMaps(IPMap,LabelMap),[const(0)],[],AllWorlds).

explore(_,_,_,[],WorldAcc,WorldAcc).
explore(Program,VmState,VmMaps,[IP|OtherIPs],WorldAcc,[WorldOut|OtherWorldOuts]) :- 
                                                    VmState=vmState(_,Stack,CallStack,Registers,flags(ZeroFlag,_,_)),
                                                    FreshState=vmState(IP,Stack,CallStack,Registers,flags(ZeroFlag,hlt(false),branch(false))),
                                                    vm(Program,FreshState,VmMaps,WorldOut),
                                                    explore(Program,VmState,VmMaps,OtherIPs,WorldAcc,OtherWorldOuts),
                                                    !.
vm(Program,StateIn,vmMaps(IPMap,LabelMap),world(StateIn,TraceOut,ChildWorlds)) :- 
                              exec_(vmMaps(IPMap,LabelMap),
                                  StateIn,[],
                                  traceOut(FinalTrace,VmStateOut),
                                  env(log(debug,info,warning,error))),
                              VmStateOut=vmState(FinalIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags),
                              minusOne(FinalIP,LastInstrIP),
                              TraceOut=traceOut(FinalTrace,vmState(LastInstrIP,FinalStack,FinalCallStack,FinalRegisters,FinalVmFlags)),
                              (shouldTerminateWorld(FinalVmFlags)->(ChildWorlds=[]);
                                (
                                  NewStartIP_One=FinalIP,
                                  branchDestination(LastInstrIP,LabelMap,IPMap,NewStartIP_Two),
                                  Branches=[NewStartIP_One,NewStartIP_Two],
                                  info("Branches are: ~w",[Branches]),
                                  explore(Program,VmStateOut,vmMaps(IPMap,LabelMap),Branches,[],ChildWorlds)
                                )
                              ).

print_worlds([],_).
print_worlds([World|OtherWorlds],Level) :-
                                          Indent is Level*2,
                                          indent(Indent),
                                          (Level==0->format('');format('└--')), 
                                          print_formatted_world(World,Level),
                                          print_worlds(OtherWorlds,Level),!.

indent(0).
indent(Times) :- write(' '),NewTimes is Times-1,indent(NewTimes).

print_formatted_world(world(vmState(StartIP,_,_,_,_),traceOut(_,vmState(EndIP,_,_,FinalRegisters,FinalVmFlags)),ChildWorlds),Level) :- format('~w-~w,~w,~w~n',[StartIP,EndIP,FinalRegisters,FinalVmFlags]),
                                                                                                                  NextLevel is Level+1,
                                                                                                                  print_worlds(ChildWorlds,NextLevel).

shouldTerminateWorld(flags(_,hlt(true),_)).
shouldSplitWorld(flags(_,hlt(false),branch(true))).

branchDestination(FinalIP,LabelMap,IPMap,NewStartIP) :- get2(FinalIP,IPMap,Instr),info("Final Instr is ~w",[Instr]),destination(Instr,LabelMap,NewStartIP).

destination(jz(label(LabelName)),LabelMap,IPOut) :- get2(label(LabelName),LabelMap,IPOut).
destination(jnz(label(LabelName)),LabelMap,IPOut) :- get2(label(LabelName),LabelMap,IPOut).
destination(jz(const(JumpIP)),_,const(JumpIP)).
destination(jnz(const(JumpIP)),_,const(JumpIP)).

eval(const(ConstValue),_,const(ConstValue)).
eval(sym(inc(Symbol)),Bindings,inc(Evaluated)) :- eval(Symbol,Bindings,Evaluated),Evaluated\=empty.
eval(sym(dec(Symbol)),Bindings,dec(Evaluated)) :- eval(Symbol,Bindings,Evaluated),Evaluated\=empty.
eval(sym(product(LHS,RHS)),Bindings,product(EvaluatedLHS, EvaluatedRHS)) :- eval(LHS,Bindings,EvaluatedLHS),
                                                                   eval(RHS,Bindings,EvaluatedRHS),
                                                                   EvaluatedLHS\=empty,
                                                                   EvaluatedRHS\=empty.
eval(sym(cmp(LHS,RHS)),Bindings,cmp(EvaluatedLHS, EvaluatedRHS)) :- eval(LHS,Bindings,EvaluatedLHS),
                                                                    eval(RHS,Bindings,EvaluatedRHS),
                                                                    EvaluatedLHS\=empty,
                                                                    EvaluatedRHS\=empty.
eval(sym(Other),Bindings,Binding) :- get2(sym(Other),Bindings,Binding),Binding\=empty.

compute(const(ConstValue),const(ConstValue)).
compute(inc(Expr),const(Result)) :- compute(Expr,const(ConstValue)),Result is ConstValue+1.
compute(dec(Expr),const(Result)) :- compute(Expr,const(ConstValue)),Result is ConstValue-1.
compute(product(LHS,RHS),const(Result)) :- compute(LHS,const(ResolvedLHS)),
                                           compute(RHS,const(ResolvedRHS)),
                                           Result is ResolvedLHS*ResolvedRHS.
compute(cmp(LHS,RHS),Result) :- compute(LHS,ResolvedLHS),
                                compute(RHS,ResolvedRHS),
                                equate(ResolvedLHS,ResolvedRHS,Result).

log_with_level(LogLevel,FormatString,Args) :- format(string(Message),FormatString,Args),format('[~w]: ~w~n',[LogLevel,Message]).

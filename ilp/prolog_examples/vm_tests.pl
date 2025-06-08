:- use_module('interpreter').
:- begin_tests(vm).

test(symbolic) :-
    Program = [
      mvc(reg(1), const(5)),
      mvc(reg(2), reg(1)),
      hlt
    ],
    vm(Program,_,_,_,_,FinalRegs,_),
    get2(1,FinalRegs,R1),
    get2(2,FinalRegs,R2),
    assertion(R1==const(5)),
    assertion(R2==const(5)).

test(incremental_symbolic_state) :-
    Program = [
      mvc(reg(1), const(2)),
      inc(reg(1)),
      inc(reg(1)),
      mvc(reg(2), reg(1)),
      hlt
    ],
    vm(Program,_,_,_,_,FinalRegs,_),
    get2(1,FinalRegs,R1),
    get2(2,FinalRegs,R2),
    assertion(R1==const(4)),
    assertion(R2==const(4)).

test(vm_factorial_of_5_is_120) :-
        factorial_program(Program),
       vm(Program,_,_,_,_,FinalRegs,_),
       get2(r1,FinalRegs,R1),
       assertion(R1==const(120)).

test(simple_move) :-
    vm([
        mvc(reg(r1), const(42)),
        hlt
    ], _, _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == const(42)).

test(addition_simulation) :-
    vm([
        mvc(reg(r1), const(40)),
        inc(reg(r1)),
        inc(reg(r1)),
        hlt
    ], _, _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == const(42)).

test(multiplication) :-
    vm([
        mvc(reg(r1), const(6)),
        mvc(reg(r2), const(7)),
        mul(reg(r1), reg(r2)),  % r1 = r1 * r2
        hlt
    ], _, _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == const(42)).

test(stack_push_pop) :-
    vm([
        mvc(reg(r1), const(99)),
        push(reg(r1)),
        mvc(reg(r1), const(0)),
        pop(reg(r2)),
        hlt
    ], _, _, _, _, Regs, _),
    get2(r2, Regs, R2),
    assertion(R2 == const(99)).

test(jump_direct) :-
    vm([
        j(label(skip)),
        mvc(reg(r1), const(999)),   % should be skipped
        label(skip),
        mvc(reg(r1), const(42)),
        hlt
    ], _, _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == const(42)).

test(jz_branch_taken) :-
    vm([
        mvc(reg(r1), const(0)),
        cmp(reg(r1), const(0)),
        jz(label(zero_case)),
        mvc(reg(r2), const(999)),   % should be skipped
        label(zero_case),
        mvc(reg(r2), const(42)),
        hlt
    ], _, _, _, _, Regs, _),
    get2(r2, Regs, R2),
    assertion(R2 == const(42)).

test(jnz_branch_taken) :-
    vm([
        mvc(reg(r1), const(1)),
        cmp(reg(r1), const(0)),
        jnz(label(non_zero_case)),
        mvc(reg(r2), const(999)),   % should be skipped
        label(non_zero_case),
        mvc(reg(r2), const(42)),
        hlt
    ], _, _, _, _, Regs, _),
    get2(r2, Regs, R2),
    assertion(R2 == const(42)).

test(nested_call_ret) :-
    vm([
        mvc(reg(r0), const(2)),
        call(label(first)),
        hlt,

        label(first),
        mvc(reg(r1), const(10)),
        call(label(second)),
        ret,

        label(second),
        mvc(reg(r2), const(20)),
        ret
    ], _, _, _, _, Regs, _),
    get2(r1, Regs, R1),
    get2(r2, Regs, R2),
    assertion(R1 == const(10)),
    assertion(R2 == const(20)).

test(call_stack_behavior) :-
    vm([
        mvc(reg(r0), const(123)),
        call(label(f)),
        hlt,

        label(f),
        ret
    ], _, _, _, CallStack, _, _),
    assertion(CallStack == []).

% Helper to define the factorial program
factorial_program([
     mvc(reg(r0),const(5)),
     mvc(reg(r1),const(1)),
     call(label(factorial)),
     push(const(30)),
     cmp(reg(r1),const(121)),
     hlt,
     label(factorial),
     cmp(reg(r0),const(0)),
     jz(label(base)),
     push(reg(r0)),
     dec(reg(r0)),
     call(label(factorial)),
     pop(reg(r0)),
     mul(reg(r1),reg(r0)),
     ret,

     label(base),
     mvc(reg(r1),const(1)),
     ret
]).

:- end_tests(vm).

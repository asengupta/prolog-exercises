:- use_module('interpreter').
:- begin_tests(vm).

test(vm_factorial_of_5_is_120) :-
        factorial_program(Program),
       vm(Program,_,_,_,FinalRegs,_),
       get2(r1,FinalRegs,R1),
       assertion(R1==120).

test(simple_move) :-
    vm([
        mvc(reg(r1), 42),
        hlt
    ], _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == 42).

test(addition_simulation) :-
    vm([
        mvc(reg(r1), 40),
        inc(reg(r1)),
        inc(reg(r1)),
        hlt
    ], _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == 42).

test(multiplication) :-
    vm([
        mvc(reg(r1), 6),
        mvc(reg(r2), 7),
        mul(reg(r1), reg(r2)),  % r1 = r1 * r2
        hlt
    ], _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == 42).

test(stack_push_pop) :-
    vm([
        mvc(reg(r1), 99),
        push(reg(r1)),
        mvc(reg(r1), 0),
        pop(reg(r2)),
        hlt
    ], _, _, _, Regs, _),
    get2(r2, Regs, R2),
    assertion(R2 == 99).

test(jump_direct) :-
    vm([
        j(label(skip)),
        mvc(reg(r1), 999),   % should be skipped
        label(skip),
        mvc(reg(r1), 42),
        hlt
    ], _, _, _, Regs, _),
    get2(r1, Regs, R1),
    assertion(R1 == 42).

test(jz_branch_taken) :-
    vm([
        mvc(reg(r1), 0),
        cmp(reg(r1), 0),
        jz(label(zero_case)),
        mvc(reg(r2), 999),   % should be skipped
        label(zero_case),
        mvc(reg(r2), 42),
        hlt
    ], _, _, _, Regs, _),
    get2(r2, Regs, R2),
    assertion(R2 == 42).

test(jnz_branch_taken) :-
    vm([
        mvc(reg(r1), 1),
        cmp(reg(r1), 0),
        jnz(label(non_zero_case)),
        mvc(reg(r2), 999),   % should be skipped
        label(non_zero_case),
        mvc(reg(r2), 42),
        hlt
    ], _, _, _, Regs, _),
    get2(r2, Regs, R2),
    assertion(R2 == 42).

test(nested_call_ret) :-
    vm([
        mvc(reg(r0), 2),
        call(label(first)),
        hlt,

        label(first),
        mvc(reg(r1), 10),
        call(label(second)),
        ret,

        label(second),
        mvc(reg(r2), 20),
        ret
    ], _, _, _, Regs, _),
    get2(r1, Regs, R1),
    get2(r2, Regs, R2),
    assertion(R1 == 10),
    assertion(R2 == 20).

test(call_stack_behavior) :-
    vm([
        mvc(reg(r0), 123),
        call(label(f)),
        hlt,

        label(f),
        ret
    ], _, _, CallStack, _, _),
    assertion(CallStack == []).

% Helper to define the factorial program
factorial_program([
    mvc(reg(r0),5),
    mvc(reg(r1),1),
    call(label(factorial)),
    hlt,
    label(factorial),
    cmp(reg(r0),0),
    jz(label(base)),
    push(reg(r0)),
    dec(reg(r0)),
    call(label(factorial)),
    pop(reg(r0)),
    mul(reg(r1),reg(r0)),
    ret,
    label(base),
    mvc(reg(r1),1),
    ret
]).

:- end_tests(vm).

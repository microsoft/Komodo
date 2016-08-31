include "ARMdef.dfy"

//-----------------------------------------------------------------------------
// Spartan Types
//-----------------------------------------------------------------------------
type sp_int = int
type sp_bool = bool
type sp_operand = operand // sp_operand is deprecated
type sp_operand_code = operand
type sp_operand_lemma = operand
type sp_cmp = obool
type sp_code = code
type sp_codes = codes
type sp_state = state

//-----------------------------------------------------------------------------
// Spartan-Verification Interface
//-----------------------------------------------------------------------------

function method sp_op(o:sp_operand_lemma):sp_operand_code { o }

predicate{:opaque} sp_eval(c:code, s:state, r:state)
{
    evalCode(c, s, r)
}

function sp_eval_op(s:state, o:operand):int
    requires ValidState(s)
    requires ValidOperand(o)
    { OperandContents(s, o) }

function sp_eval_op_addr(s:state, o:operand):int
    requires ValidState(s)
    requires ValidOperand(o)
    { sp_eval_op(s,o) }

predicate sp_eq_ops(s1:sp_state, s2:sp_state, o:operand)
{
    ValidState(s1) && ValidState(s2) && ValidOperand(o)
        && sp_eval_op(s1, o) == sp_eval_op(s2, o)
}

function sp_eval_addr(s:state, m:addr):int
    requires ValidMemState(s.m);
    requires ValidMem(m);
    ensures isUInt32(sp_eval_addr(s,m));
    { MemContents(s.m, m) }

function method sp_CNil():codes { CNil }
function sp_cHead(b:codes):code requires b.sp_CCons? { b.hd }
predicate sp_cHeadIs(b:codes, c:code) { b.sp_CCons? && b.hd == c }
predicate sp_cTailIs(b:codes, t:codes) { b.sp_CCons? && b.tl == t }

predicate sp_require(b0:codes, c1:code, s0:sp_state, sN:sp_state)
{
    sp_cHeadIs(b0, c1)
 && s0.ok
 && sp_eval(Block(b0), s0, sN)
}

predicate sp_ensure(b0:codes, b1:codes, s0:sp_state, s1:sp_state, sN:sp_state)
{
    sp_cTailIs(b0, b1)
 && s1.ok
 && sp_eval(sp_cHead(b0), s0, s1)
 && sp_eval(sp_Block(b1), s1, sN)
}

function method fromOperand(o:operand):operand { o }
function method sp_op_const(n:word):operand { OConst(n) }

function method sp_cmp_eq(o1:operand, o2:operand):obool { OCmp(OEq, o1, o2) }
function method sp_cmp_ne(o1:operand, o2:operand):obool { OCmp(ONe, o1, o2) }
function method sp_cmp_le(o1:operand, o2:operand):obool { OCmp(OLe, o1, o2) }
function method sp_cmp_ge(o1:operand, o2:operand):obool { OCmp(OGe, o1, o2) }
function method sp_cmp_lt(o1:operand, o2:operand):obool { OCmp(OLt, o1, o2) }
function method sp_cmp_gt(o1:operand, o2:operand):obool { OCmp(OGt, o1, o2) }

function method sp_Block(block:codes):code { Block(block) }
function method sp_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method sp_While(whileb:obool, whilec:code):code { While(whileb, whilec) }

function method sp_get_block(c:code):codes requires c.Block? { c.block }
function method sp_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function method sp_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function method sp_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function method sp_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function method sp_get_whileBody(c:code):code requires c.While? { c.whileBody }

//-----------------------------------------------------------------------------
// Useful invariants preserved by instructions
//-----------------------------------------------------------------------------
/*predicate AlwaysInvariant(s:state, s':state)
{
    // valid state is maintained
    ValidState(s) && ValidState(s')
}*/

predicate AllMemInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m == s'.m
}

predicate GlobalsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m.globals == s'.m.globals
}

predicate AddrMemInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m.addresses == s'.m.addresses
}

predicate SRegsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.sregs == s'.sregs && s.conf == s'.conf
}

predicate AllRegsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.regs == s'.regs && SRegsInvariant(s, s')
}

//-----------------------------------------------------------------------------
// Control Flow Lemmas
//-----------------------------------------------------------------------------

function to_state(s:sp_state):state { s }
predicate valid_state(s:sp_state) { ValidState(s) }

lemma sp_lemma_empty(s:sp_state, r:sp_state) returns(r':sp_state)
    requires sp_eval(Block(sp_CNil()), s, r)
    ensures  r.ok == s.ok
    ensures  r' == s
    ensures  to_state(r) == to_state(s)
{
    reveal_sp_eval();
    r' := s;
}

lemma evalWhile_validity(b:obool, c:code, n:nat, s:state, r:state)
    requires evalWhile(b, c, n, s, r);
    decreases c, 1, n;
    ensures  valid_state(s) && r.ok ==> valid_state(r);
{
    if valid_state(s) && r.ok && ValidOperand(b.o1) && ValidOperand(b.o2) && n > 0 {
        var s', r' :| evalGuard(s, b, s') && evalOBool(s, b) && evalCode(c, s', r') && evalWhile(b, c, n - 1, r', r);
        code_state_validity(c, s', r');
        evalWhile_validity(b, c, n - 1, r', r);
        assert valid_state(r);
    }
}

lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    ensures  !s.ok ==> !r.ok;
    decreases block;
{
    if !block.CNil? {
        var r' :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        lemma_FailurePreservedByCode(block.hd, s, r');
        lemma_FailurePreservedByBlock(block.tl, r', r);
    }
}

lemma lemma_FailurePreservedByCode(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    ensures  !s.ok ==> !r.ok;
{
    if c.Block? {
        lemma_FailurePreservedByBlock(c.block, s, r);
    }
}

lemma block_state_validity(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    requires valid_state(s);
    decreases block, 0;
    ensures  r.ok ==> valid_state(r);
{
    if block.sp_CCons? {
        var r':state :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        code_state_validity(block.hd, s, r');
        if r'.ok {
            block_state_validity(block.tl, r', r);
        }
        else {
            lemma_FailurePreservedByBlock(block.tl, r', r);
        }
    }
}

lemma code_state_validity(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    requires valid_state(s);
    decreases c, 0;
    ensures  r.ok ==> valid_state(r);
{
    if r.ok {
        if c.Ins? {
            assert valid_state(r);
        } else if c.Block? {
            block_state_validity(c.block, s, r);
        } else if c.IfElse? {
            if ValidOperand(c.ifCond.o1) && ValidOperand(c.ifCond.o2) {
                var s' :| evalGuard(s, c.ifCond, s') &&
                    if evalOBool(s, c.ifCond) then
                        evalCode(c.ifTrue, s', r)
                    else
                        evalCode(c.ifFalse, s', r);
                if evalOBool(s, c.ifCond) {
                    code_state_validity(c.ifTrue, s', r);
                } else {
                    code_state_validity(c.ifFalse, s', r);
                }
            }
            assert valid_state(r);
        } else if c.While? {
            var n:nat :| evalWhile(c.whileCond, c.whileBody, n, s, r);
            evalWhile_validity(c.whileCond, c.whileBody, n, s, r);
            assert valid_state(r);
        }
    }
}

lemma sp_lemma_block(b:codes, s0:sp_state, r:sp_state) returns(r1:sp_state, c0:code, b1:codes)
    requires b.sp_CCons?
    requires sp_eval(Block(b), s0, r)
    ensures  b == sp_CCons(c0, b1)
    ensures  ValidState(s0) && r1.ok ==> ValidState(r1);
    ensures  sp_eval(c0, s0, r1)
    ensures  sp_eval(Block(b1), r1, r)
{
    reveal_sp_eval();
    assert evalBlock(b, to_state(s0), to_state(r));
    var r':state :| evalCode(b.hd, to_state(s0), r') && evalBlock(b.tl, r', to_state(r));
    c0 := b.hd;
    b1 := b.tl;
    r1 := r';
    if ValidState(s0) {
        code_state_validity(c0, to_state(s0), to_state(r1));
    }
    assert sp_eval(c0, s0, r1);
}

lemma sp_lemma_ifElse(ifb:obool, ct:code, cf:code, s:sp_state, r:sp_state) returns(cond:bool, s':sp_state)
    requires ValidState(s) && ValidOperand(ifb.o1) && ValidOperand(ifb.o2)
    requires sp_eval(IfElse(ifb, ct, cf), s, r)
    ensures  if s.ok then
                    s'.ok
                 && ValidState(s')
                 && evalGuard(s, ifb, s')
                 && cond == evalOBool(s, ifb)
                 && (if cond then sp_eval(ct, s', r) else sp_eval(cf, s', r))
             else
                 !r.ok;
{
    reveal_sp_eval();
    assert evalIfElse(ifb, ct, cf, to_state(s), to_state(r));
    if s.ok {
        cond := evalOBool(s, ifb);
        var t:state :| evalGuard(to_state(s), ifb, t) && (if cond then evalCode(ct, t, to_state(r)) else evalCode(cf, t, to_state(r)));
        s' := t;
    }
}

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s:state, r:state)
{
    evalWhile(b, c, n, s, r)
}

predicate sp_whileInv(b:obool, c:code, n:int, r1:sp_state, r2:sp_state)
{
    n >= 0 && r1.ok && evalWhileOpaque(b, c, n, to_state(r1), to_state(r2))
}

// HACK
lemma unpack_eval_while(b:obool, c:code, s:state, r:state)
  requires evalCode(While(b, c), s, r)
  ensures  exists n:nat :: evalWhile(b, c, n, s, r)
{}

lemma sp_lemma_while(b:obool, c:code, s:sp_state, r:sp_state) returns(n:nat, r':sp_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2)
    requires sp_eval(While(b, c), s, r)
    ensures  evalWhileOpaque(b, c, n, to_state(s), to_state(r))
    //ensures  r'.ok
    ensures  ValidState(r');
    ensures  r' == s
{
    reveal_sp_eval();
    reveal_evalWhileOpaque();
    unpack_eval_while(b, c, s, r);
    n :| evalWhile(b, c, n, to_state(s), to_state(r));
    r' := s;
}

lemma sp_lemma_whileTrue(b:obool, c:code, n:sp_int, s:sp_state, r:sp_state) returns(s':sp_state, r':sp_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires n > 0
    requires evalWhileOpaque(b, c, n, to_state(s), to_state(r))
    //ensures  ValidState(s) && r'.ok ==> ValidState(r');
    ensures  s.ok && ValidState(s) ==> ValidState(s');
    ensures  if s.ok then
                    s'.ok
                 && evalGuard(s, b, s')
                 && evalOBool(s, b)
                 && sp_eval(c, s', r')
                 && evalWhileOpaque(b, c, n - 1, to_state(r'), to_state(r))
             else
                 !r.ok;
{
    reveal_sp_eval();
    reveal_evalWhileOpaque();
    assert evalWhile(b, c, n, to_state(s), to_state(r)); // TODO: Dafny reveal/opaque issue

    if !s.ok {
        return;
    }

    var s'', r'':state :| evalGuard(to_state(s), b, s'') && evalOBool(to_state(s), b) && evalCode(c, s'', r'')
        && evalWhile(b, c, n - 1, r'', to_state(r));
    if ValidState(s) {
        code_state_validity(c, s'', r'');
    }
    s' := s'';
    r' := r'';
}

lemma sp_lemma_whileFalse(b:obool, c:code, s:sp_state, r:sp_state) returns(r':sp_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires evalWhileOpaque(b, c, 0, to_state(s), to_state(r))
    ensures  if s.ok then
                    (ValidState(s) && r'.ok ==> ValidState(r'))
                 && evalGuard(s, b, r')
                 && !evalOBool(s, b)
                 && r.ok
                 && to_state(r') == to_state(r)
            else
                !r.ok;
{
    reveal_sp_eval();
    reveal_evalWhileOpaque();

    if !s.ok {
        return;
    }

    r' := r;
}

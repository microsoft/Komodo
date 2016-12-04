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

predicate {:opaque} sp_eval(c:code, s:state, r:state)
{
    s.ok ==> evalCode(c, s, r)
}

function sp_eval_op(s:state, o:operand): word
    requires ValidState(s) && ValidAnySrcOperand(s, o)
{ OperandContents(s,o) }

function sp_eval_op_addr(s:state, o:operand): word
    requires ValidState(s)
    requires ValidOperand(o)
{ sp_eval_op(s,o) }

predicate sp_eq_ops(s1:sp_state, s2:sp_state, o:operand)
{
    ValidState(s1) && ValidState(s2) && (ValidOperand(o) || 
        (ValidBankedRegOperand(s1, o) && ValidBankedRegOperand(s2,o)))
        && sp_eval_op(s1, o) == sp_eval_op(s2, o)
}

function method sp_CNil():codes { CNil }
function sp_cHead(b:codes):code requires b.sp_CCons? { b.hd }
predicate sp_cHeadIs(b:codes, c:code) { b.sp_CCons? && b.hd == c }
predicate sp_cTailIs(b:codes, t:codes) { b.sp_CCons? && b.tl == t }

predicate sp_require(b0:codes, c1:code, s0:sp_state, sN:sp_state)
{
    sp_cHeadIs(b0, c1)
 && sp_eval(Block(b0), s0, sN)
 && ValidState(s0)
}

predicate sp_ensure(b0:codes, b1:codes, s0:sp_state, s1:sp_state, sN:sp_state)
{
    sp_cTailIs(b0, b1)
// && sp_eval(sp_cHead(b0), s0, s1)
 && sp_eval(sp_Block(b1), s1, sN)
 && ValidState(s1)
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
// Spartan-to-Dafny connections needed for refined mode
//-----------------------------------------------------------------------------
function method sp_op_osp():operand { OSP }
function method sp_op_olr():operand { OLR }
function method sp_op_reg(r:ARMReg):operand { OReg(r) }
function sp_get_ok(s:state):bool { s.ok }
function sp_get_reg(r:ARMReg, s:state):word
    requires ValidRegState(s.regs)
{
    reveal_ValidRegState();
    s.regs[r]
}

function sp_get_mem(s:state):memmap
    requires ValidState(s)
    ensures ValidAddrMemStateOpaque(sp_get_mem(s))
{ reveal_ValidMemState(); reveal_ValidAddrMemStateOpaque(); s.m.addresses }

function sp_get_globals(s:state):globalsmap
    requires ValidState(s)
    ensures ValidGlobalStateOpaque(sp_get_globals(s))
{ reveal_ValidMemState(); reveal_ValidGlobalStateOpaque(); s.m.globals }

function sp_get_osp(s:state):word 
    requires ValidRegState(s.regs)
{
    reveal_ValidRegState();
    s.regs[SP(mode_of_state(s))]
}
function sp_get_olr(s:state):word 
    requires ValidRegState(s.regs)
{
    reveal_ValidRegState();
    s.regs[LR(mode_of_state(s))]
}

function sp_update_ok(sM:state, sK:state):state { sK.(ok := sM.ok, steps := sM.steps) }
function sp_update_reg(r:ARMReg, sM:state, sK:state):state 
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
    ensures ValidRegState(sp_update_reg(r, sM, sK).regs)
{
    reveal_ValidRegState();
    sK.(regs := sK.regs[r := sM.regs[r]])
}
function sp_update_mem(sM:state, sK:state):state
    requires ValidMemState(sM.m) && ValidMemState(sK.m)
    ensures ValidMemState(sp_update_mem(sM, sK).m)
    ensures ValidAddrMemStateOpaque(sp_update_mem(sM, sK).m.addresses)
{
    reveal_ValidMemState(); reveal_ValidAddrMemStateOpaque();
    sK.(m := sK.m.(addresses := sM.m.addresses))
}
function sp_update_globals(sM:state, sK:state):state
    requires ValidMemState(sM.m) && ValidMemState(sK.m)
    ensures ValidMemState(sp_update_mem(sM, sK).m)
    ensures ValidGlobalStateOpaque(sp_update_mem(sM, sK).m.globals)
{
    reveal_ValidMemState(); reveal_ValidGlobalStateOpaque();
    sK.(m := sK.m.(globals := sM.m.globals))
}
function sp_update_osp(sM:state, sK:state):state 
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
    ensures ValidRegState(sp_update_osp(sM, sK).regs)
{ 
    sp_update_reg(SP(mode_of_state(sM)), sM, sK)
}
function sp_update_olr(sM:state, sK:state):state 
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
    ensures ValidRegState(sp_update_olr(sM, sK).regs)
{ 
    sp_update_reg(LR(mode_of_state(sM)), sM, sK)
}

function sp_update(o:operand, sM:state, sK:state):state
    requires ValidRegOperand(o)
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
{
    match o
        case OReg(r) => sp_update_reg(o.r, sM, sK)
        case OLR => sp_update_reg(LR(mode_of_state(sM)), sM, sK)
        case OSP => sp_update_reg(SP(mode_of_state(sM)), sM, sK)
}

function method GetProbableReg(o:operand) : ARMReg { if o.OReg? then o.r else R0 }

predicate sp_is_src_word(o:operand) { ValidOperand(o) }
predicate sp_is_dst_word(o:operand) { ValidRegOperand(o) }

type reg = word
predicate sp_is_src_reg(o:operand) { ValidRegOperand(o) }

type snd = word
predicate sp_is_src_snd(o:operand) { ValidOperand(o) && o.OReg? }

predicate sp_is_src_symbol(g:symbol) { ValidGlobal(g) }
function sp_eval_op_symbol(s:state, g:symbol):symbol { g }

function sp_eval_op_word(s:state, o:operand):word
    requires sp_is_src_word(o);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function sp_eval_op_reg(s:state, o:operand):reg
    requires sp_is_src_reg(o);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function sp_eval_op_snd(s:state, o:operand):snd
    requires sp_is_src_snd(o);
    requires ValidState(s)
{
    OperandContents(s,o)
}

predicate sp_state_eq(s0:state, s1:state)
{
    s0.regs == s1.regs
 && s0.sregs == s1.sregs
 && s0.m == s1.m
 && s0.conf == s1.conf
 && s0.ok == s1.ok
 && s0.steps == s1.steps
}

predicate {:opaque} ValidAddrMemStateOpaque(mem: memmap)
{
    ValidAddrMemState(mem)
}

function AddrMemContents(m:memmap, a:int): word
    requires ValidAddrMemStateOpaque(m)
    requires ValidMem(a)
{
    reveal_ValidAddrMemStateOpaque();
    m[a]
}

function AddrMemUpdate(m:memmap, a:int, v:word): memmap
    requires ValidAddrMemStateOpaque(m)
    requires ValidMem(a)
    ensures ValidAddrMemStateOpaque(AddrMemUpdate(m, a, v))
{
    reveal_ValidAddrMemStateOpaque();
    m[a := v]
}

predicate {:opaque} ValidGlobalStateOpaque(globals: globalsmap)
{
    ValidGlobalState(globals)
}

function GlobalContents(gm: globalsmap, g:symbol, addr:int): word
    requires ValidGlobalStateOpaque(gm)
    requires ValidGlobalAddr(g, addr)
{
    reveal_ValidGlobalStateOpaque();
    gm[g][BytesToWords(addr - AddressOfGlobal(g))]
}

function GlobalUpdate(gm: globalsmap, g:symbol, a:int, v:word): globalsmap
    requires ValidGlobalStateOpaque(gm)
    requires ValidGlobalAddr(g, a)
    ensures ValidGlobalStateOpaque(GlobalUpdate(gm, g, a, v))
{
    reveal_ValidGlobalStateOpaque();
    gm[g := gm[g][BytesToWords(a - AddressOfGlobal(g)) := v]]
}

//-----------------------------------------------------------------------------
// Useful invariants preserved by instructions
//-----------------------------------------------------------------------------
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

predicate valid_state(s:sp_state) { ValidState(s) }

lemma sp_lemma_empty(s:sp_state, r:sp_state) returns(r':sp_state)
    requires sp_eval(Block(sp_CNil()), s, r)
    ensures  s.ok ==> r.ok
    ensures  r' == s
    ensures  s.ok ==> r == s
    ensures  forall b, s' :: sp_eval(b, r, s') ==> sp_eval(b, s, s')
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
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r);
        var r':state :| evalCode(b.hd, s0, r') && evalBlock(b.tl, r', r);
        r1 := r';
        if ValidState(s0) {
            code_state_validity(c0, s0, r1);
        }
        assert sp_eval(c0, s0, r1);
    } else {
        r1 := s0;
    }
}

lemma sp_lemma_ifElse(ifb:obool, ct:code, cf:code, s:sp_state, r:sp_state) returns(cond:bool, s':sp_state)
    requires ValidState(s) && ValidOperand(ifb.o1) && ValidOperand(ifb.o2)
    requires sp_eval(IfElse(ifb, ct, cf), s, r)
    ensures  forall c, t, t' :: sp_eval(c, t, t') == (t.ok ==> sp_eval(c, t, t'));
    ensures  if s.ok then
                    s'.ok
                 && ValidState(s')
                 && evalGuard(s, ifb, s')
                 && cond == evalOBool(s, ifb)
                 && (if cond then sp_eval(ct, s', r) else sp_eval(cf, s', r))
             else
                 true //!r.ok;
{
    reveal_sp_eval();
    if s.ok {
        assert evalIfElse(ifb, ct, cf, s, r);
        cond := evalOBool(s, ifb);
        var t:state :| evalGuard(s, ifb, t) && (if cond then evalCode(ct, t, r) else evalCode(cf, t, r));
        s' := t;
    }
}

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s:state, r:state)
{
    evalWhile(b, c, n, s, r)
}

predicate evalWhileLax(b:obool, c:code, n:nat, s:state, r:state)
{
    s.ok ==> evalWhileOpaque(b, c, n, s, r)
}

predicate sp_whileInv(b:obool, c:code, n:int, r1:sp_state, r2:sp_state)
{
    n >= 0 && ValidState(r1) && evalWhileLax(b, c, n, r1, r2)
}

lemma sp_lemma_while(b:obool, c:code, s:sp_state, r:sp_state) returns(n:nat, r':sp_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2)
    requires sp_eval(While(b, c), s, r)
    ensures  evalWhileLax(b, c, n, s, r)
    //ensures  r'.ok
    ensures  ValidState(r');
    ensures  r' == s
    ensures  forall c', t, t' :: sp_eval(c', t, t') == (t.ok ==> sp_eval(c', t, t'));
{
    reveal_sp_eval();
    reveal_evalWhileOpaque();
//    unpack_eval_while(b, c, s, r);
    if s.ok {
        assert evalCode(While(b, c), s, r);
        n :| evalWhile(b, c, n, s, r);
    } else {
        n := 0;
    }
    r' := s;
}

lemma sp_lemma_whileTrue(b:obool, c:code, n:sp_int, s:sp_state, r:sp_state) returns(s':sp_state, r':sp_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires n > 0
    requires evalWhileLax(b, c, n, s, r)
    //ensures  ValidState(s) && r'.ok ==> ValidState(r');
    ensures  ValidState(s) ==> ValidState(s');
    ensures  evalWhileLax(b, c, n-1, r', r)
    ensures  sp_eval(c, s', r');
    ensures  ValidState(s) ==> if s.ok then evalGuard(s, b, s') else s' == s;
    ensures  forall c', t, t' :: sp_eval(c', t, t') == (t.ok ==> sp_eval(c', t, t'));
    ensures  if s.ok then
                    s'.ok
                 //&& evalGuard(s, b, s')
                 && evalOBool(s, b)
                 //&& sp_eval(c, s', r')
                 //&& evalWhileOpaque(b, c, n - 1, r', r)
             else
                 true //!r.ok;
{
    reveal_sp_eval();
    reveal_evalWhileOpaque();

    if !s.ok {
        s' := s;
        r' := s;
        return;
    }
    assert evalWhile(b, c, n, s, r); // TODO: Dafny reveal/opaque issue

    if ValidState(s) {
        var s'', r'':state :| evalGuard(s, b, s'') && evalOBool(s, b) && evalCode(c, s'', r'')
            && evalWhile(b, c, n - 1, r'', r);
        code_state_validity(c, s'', r'');
        s' := s'';
        r' := r'';
    } else {
        s' := s.(ok := false);
        r' := s.(ok := false);
    }
}

lemma sp_lemma_whileFalse(b:obool, c:code, s:sp_state, r:sp_state) returns(r':sp_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires evalWhileLax(b, c, 0, s, r)
    ensures  forall c', t, t' :: sp_eval(c', t, t') == (t.ok ==> sp_eval(c', t, t'));
    ensures  if s.ok then
                    (if ValidState(s) then
                        (r'.ok ==> ValidState(r'))
                     && evalGuard(s, b, r')
                     && !evalOBool(s, b)
                     && r.ok
                     && r' == r
                     else 
                        true)
                 && r' == r
            else
                r' == s
{
    reveal_sp_eval();
    reveal_evalWhileOpaque();

    if !s.ok {
        r' := s;
        return;
    }

    r' := r;
}

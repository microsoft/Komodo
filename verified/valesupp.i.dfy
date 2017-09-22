include "ARMdef.s.dfy"

//-----------------------------------------------------------------------------
// Spartan Types
//-----------------------------------------------------------------------------
type va_int = int
type va_bool = bool
type va_operand = operand // va_operand is deprecated
type va_operand_code = operand
type va_operand_lemma = operand
type va_cmp = operand
type va_code = code
type va_codes = codes
type va_state = state

//-----------------------------------------------------------------------------
// Spartan-Verification Interface
//-----------------------------------------------------------------------------

function method va_op(o:va_operand_lemma):va_operand_code { o }

predicate {:opaque} va_eval(c:code, s:state, r:state)
{
    s.ok ==> evalCode(c, s, r)
}

/* function va_eval_operand_int(s:state, o:operand): word
    requires ValidState(s) && ValidAnySrcOperand(s, o)
{ OperandContents(s,o) } */

predicate va_eq_ops(s1:va_state, s2:va_state, o:operand)
{
    ValidState(s1) && ValidState(s2) && (ValidOperand(o) || 
        (ValidBankedRegOperand(s1, o) && ValidBankedRegOperand(s2,o)))
        && OperandContents(s1, o) == OperandContents(s2, o)
}

function method va_CNil():codes { CNil }
function va_cHead(b:codes):code requires b.va_CCons? { b.hd }
predicate va_cHeadIs(b:codes, c:code) { b.va_CCons? && b.hd == c }
predicate va_cTailIs(b:codes, t:codes) { b.va_CCons? && b.tl == t }

predicate va_require(b0:codes, c1:code, s0:va_state, sN:va_state)
{
    va_cHeadIs(b0, c1)
 && va_eval(Block(b0), s0, sN)
 && ValidState(s0)
}

predicate va_ensure(b0:codes, b1:codes, s0:va_state, s1:va_state, sN:va_state)
{
    va_cTailIs(b0, b1)
// && va_eval(va_cHead(b0), s0, s1)
 && va_eval(va_Block(b1), s1, sN)
 && ValidState(s1)
}

function method va_const_operand(n:word):operand { OConst(n) }
function method va_const_cmp(n:word):va_cmp { va_const_operand(n) }
function method va_coerce_operand_to_cmp(o:operand):operand { o }

function method va_cmp_eq(o1:operand, o2:operand):obool { OCmp(OEq, o1, o2) }
function method va_cmp_ne(o1:operand, o2:operand):obool { OCmp(ONe, o1, o2) }
function method va_cmp_le(o1:operand, o2:operand):obool { OCmp(OLe, o1, o2) }
function method va_cmp_ge(o1:operand, o2:operand):obool { OCmp(OGe, o1, o2) }
function method va_cmp_lt(o1:operand, o2:operand):obool { OCmp(OLt, o1, o2) }
function method va_cmp_gt(o1:operand, o2:operand):obool { OCmp(OGt, o1, o2) }
function method va_cmp_tst_eq(o1:operand, o2:operand):obool { OCmp(OTstEq, o1, o2) }
function method va_cmp_tst_ne(o1:operand, o2:operand):obool { OCmp(OTstNe, o1, o2) }

function method va_Block(block:codes):code { Block(block) }
function method va_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method va_While(whileb:obool, whilec:code):code { While(whileb, whilec) }

function method va_get_block(c:code):codes requires c.Block? { c.block }
function method va_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function method va_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function method va_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function method va_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function method va_get_whileBody(c:code):code requires c.While? { c.whileBody }

//-----------------------------------------------------------------------------
// Vale-to-Dafny connections needed for refined mode
//-----------------------------------------------------------------------------
function method va_op_operand_osp():operand { OSP }
function method va_op_operand_olr():operand { OLR }
function method va_op_operand_reg(r:ARMReg):operand { OReg(r) }
function method va_op_cmp_reg(r:ARMReg):operand { OReg(r) }
function method va_op_cmp_osp():operand { OSP }
function method va_op_cmp_olr():operand { OLR }
function method va_op_operand_sreg(sr:SReg):operand { OSReg(sr) }
function va_get_ok(s:state):bool { s.ok }
function va_get_reg(r:ARMReg, s:state):word
    requires ValidRegState(s.regs)
{
    reveal ValidRegState();
    s.regs[r]
}

function va_get_sreg(sr:SReg, s:state):word
    requires ValidSReg(sr) && ValidSRegState(s.sregs, s.conf)
{
    lemma_SRegDom(sr, s);
    s.sregs[sr]
}

function va_get_mem(s:state):memmap
    requires ValidState(s)
    ensures ValidAddrMemStateOpaque(va_get_mem(s))
{ reveal ValidMemState(); reveal_ValidAddrMemStateOpaque(); s.m.addresses }

//function va_get_ttbr0(s:state):TTBR { s.conf.ttbr0 }
//function va_get_tlb(s:state):bool { s.conf.tlb_consistent }

function va_get_globals(s:state):globalsmap
    requires ValidState(s)
    ensures ValidGlobalStateOpaque(va_get_globals(s))
{ reveal ValidMemState(); reveal_ValidGlobalStateOpaque(); s.m.globals }

function va_get_osp(s:state):word 
    requires ValidRegState(s.regs)
{
    reveal ValidRegState();
    s.regs[SP(mode_of_state(s))]
}
function va_get_olr(s:state):word 
    requires ValidRegState(s.regs)
{
    reveal ValidRegState();
    s.regs[LR(mode_of_state(s))]
}

function va_update_ok(sM:state, sK:state):state { sK.(ok := sM.ok) }
function va_update_reg(r:ARMReg, sM:state, sK:state):state 
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
    ensures ValidRegState(va_update_reg(r, sM, sK).regs)
{
    reveal ValidRegState();
    sK.(regs := sK.regs[r := sM.regs[r]])
}

lemma lemma_SRegDom(r:SReg, s:state)
    requires ValidSReg(r)
    requires ValidSRegState(s.sregs, s.conf)
    ensures r in s.sregs
{ reveal ValidSRegState(); }

function va_update_sreg(sr:SReg, sM:state, sK:state):state 
    requires ValidSReg(sr)
    requires ValidSRegState(sK.sregs, sK.conf) && ValidSRegState(sM.sregs, sM.conf)
    ensures ValidSRegState(va_update_sreg(sr, sM, sK).sregs, va_update_sreg(sr, sM, sK).conf)
{
    reveal ValidSRegState();
    lemma_SRegDom(sr, sM);
    var v := sM.sregs[sr];
    sK.(sregs := sK.sregs[sr := v], conf := update_config_from_sreg(sK, sr, v))
}
function va_update_mem(sM:state, sK:state):state
    requires ValidMemState(sM.m) && ValidMemState(sK.m)
    ensures ValidMemState(va_update_mem(sM, sK).m)
    ensures ValidAddrMemStateOpaque(va_update_mem(sM, sK).m.addresses)
{
    reveal ValidMemState(); reveal_ValidAddrMemStateOpaque();
    sK.(m := sK.m.(addresses := sM.m.addresses),
        conf := sK.conf.(tlb_consistent := sM.conf.tlb_consistent))
}
function va_update_globals(sM:state, sK:state):state
    requires ValidMemState(sM.m) && ValidMemState(sK.m)
    ensures ValidMemState(va_update_globals(sM, sK).m)
    ensures ValidGlobalStateOpaque(va_update_mem(sM, sK).m.globals)
{
    reveal ValidMemState(); reveal_ValidGlobalStateOpaque();
    sK.(m := sK.m.(globals := sM.m.globals))
}
function va_update_rng(sM:state, sK:state):state
{
    sK.(rng := sM.rng)
}
function va_update_osp(sM:state, sK:state):state 
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
    ensures ValidRegState(va_update_osp(sM, sK).regs)
{ 
    va_update_reg(SP(mode_of_state(sM)), sM, sK)
}
function va_update_olr(sM:state, sK:state):state 
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
    ensures ValidRegState(va_update_olr(sM, sK).regs)
{ 
    va_update_reg(LR(mode_of_state(sM)), sM, sK)
}

function va_update_operand(o:operand, sM:state, sK:state):state
    requires ValidRegOperand(o) || ValidMrsMsrOperand(sM,o) || ValidMcrMrcOperand(sM,o)
    requires ValidRegState(sK.regs) && ValidRegState(sM.regs)
    requires ValidSRegState(sK.sregs, sK.conf) && ValidSRegState(sM.sregs, sM.conf)
{
    match o
        case OReg(r) => va_update_reg(r, sM, sK)
        case OLR => va_update_reg(LR(mode_of_state(sM)), sM, sK)
        case OSP => va_update_reg(SP(mode_of_state(sM)), sM, sK)
        case OSReg(sr) => va_update_sreg(sr, sM, sK)
}

function method GetProbableReg(o:operand) : ARMReg { if o.OReg? then o.r else R0 }

predicate va_is_src_operand_word(o:operand, s:state) { ValidOperand(o) }
predicate va_is_dst_operand_word(o:operand, s:state) { ValidRegOperand(o) }

type reg = word
predicate va_is_src_operand_reg(o:operand, s:state) { ValidRegOperand(o) }
predicate va_is_dst_operand_reg(o:operand, s:state) { ValidRegOperand(o) }

type snd = word
predicate va_is_src_operand_snd(o:operand, s:state) { ValidOperand(o) && o.OReg? }

// type addr = x | isUInt32(x) && WordAligned(x)
predicate va_is_src_operand_addr(o:operand, s:state)
    { ValidRegOperand(o) && ValidState(s) && WordAligned(OperandContents(s, o)) }
predicate va_is_dst_operand_addr(o:operand, s:state)
    { ValidRegOperand(o) && ValidState(s) && WordAligned(OperandContents(s, o)) }
function va_eval_operand_addr(s:state, o:operand):word
    requires ValidOperand(o) && ValidState(s)
{ OperandContents(s, o) }

predicate va_is_src_operand_symbol(g:symbol, s:state) { ValidGlobal(g) }
function va_eval_operand_symbol(s:state, g:symbol):symbol { g }

type sreg = word
predicate va_is_src_operand_sreg(o:operand, s:state) { ValidMrsMsrOperand(s, o) }
predicate va_is_dst_operand_sreg(o:operand, s:state) { ValidMrsMsrOperand(s, o) }

type creg = word
predicate va_is_src_operand_creg(o:operand, s:state) { ValidMcrMrcOperand(s, o) }
predicate va_is_dst_operand_creg(o:operand, s:state) { ValidMcrMrcOperand(s, o) }

type constop = word
predicate va_is_src_operand_constop(o:operand, s:state) { o.OConst? }

function va_eval_operand_word(s:state, o:operand):word
    requires va_is_src_operand_word(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function va_eval_operand_reg(s:state, o:operand):reg
    requires va_is_src_operand_reg(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function va_eval_operand_snd(s:state, o:operand):snd
    requires va_is_src_operand_snd(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function va_eval_operand_sreg(s:state, o:operand):sreg
    requires va_is_src_operand_sreg(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function va_eval_operand_creg(s:state, o:operand):creg
    requires va_is_src_operand_creg(o, s);
    requires ValidState(s)
{
    OperandContents(s,o)
}
function va_eval_operand_constop(s:state, o:operand):constop
    requires va_is_src_operand_constop(o, s)
{
    o.n
}

predicate va_state_eq(s0:state, s1:state)
{
    s0.regs == s1.regs
 && s0.sregs == s1.sregs
 && s0.m == s1.m
 && s0.conf == s1.conf
 && s0.rng == s1.rng
 && s0.ok == s1.ok
}

predicate {:opaque} ValidAddrMemStateOpaque(mem: memmap)
{
    ValidAddrMemState(mem)
}

function AddrMemContents(m:memmap, a:int): word
    requires ValidAddrMemStateOpaque(m)
    requires ValidMemForRead(a) || ValidMem(a)
{
    reveal ValidAddrMemStateOpaque();
    m[a]
}

function AddrMemUpdate(m:memmap, a:int, v:word): memmap
    requires ValidAddrMemStateOpaque(m)
    requires ValidMem(a)
    ensures ValidAddrMemStateOpaque(AddrMemUpdate(m, a, v))
{
    reveal ValidAddrMemStateOpaque();
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
    reveal ValidGlobalStateOpaque();
    gm[g][BytesToWords(addr - AddressOfGlobal(g))]
}

function GlobalUpdate(gm: globalsmap, g:symbol, a:int, v:word): globalsmap
    requires ValidGlobalStateOpaque(gm)
    requires ValidGlobalAddr(g, a)
    ensures ValidGlobalStateOpaque(GlobalUpdate(gm, g, a, v))
{
    reveal ValidGlobalStateOpaque();
    gm[g := gm[g][BytesToWords(a - AddressOfGlobal(g)) := v]]
}

//-----------------------------------------------------------------------------
// Control Flow Lemmas
//-----------------------------------------------------------------------------

predicate valid_state(s:va_state) { ValidState(s) }

lemma va_lemma_empty(s:va_state, r:va_state) returns(r':va_state)
    requires va_eval(Block(va_CNil()), s, r)
    ensures  s.ok ==> r.ok
    ensures  r' == s
    ensures  s.ok ==> r == s
    ensures  forall b, s' :: va_eval(b, r, s') ==> va_eval(b, s, s')
{
    reveal va_eval();
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
    if block.va_CCons? {
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

lemma va_lemma_block(b:codes, s0:va_state, r:va_state) returns(r1:va_state, c0:code, b1:codes)
    requires b.va_CCons?
    requires va_eval(Block(b), s0, r)
    ensures  b == va_CCons(c0, b1)
    ensures  ValidState(s0) && r1.ok ==> ValidState(r1);
    ensures  va_eval(c0, s0, r1)
    ensures  va_eval(Block(b1), r1, r)
{
    reveal va_eval();
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r);
        var r':state :| evalCode(b.hd, s0, r') && evalBlock(b.tl, r', r);
        r1 := r';
        if ValidState(s0) {
            code_state_validity(c0, s0, r1);
        }
        assert va_eval(c0, s0, r1);
    } else {
        r1 := s0;
    }
}

lemma va_lemma_ifElse(ifb:obool, ct:code, cf:code, s:va_state, r:va_state) returns(cond:bool, s':va_state)
    requires ValidState(s) && ValidOperand(ifb.o1) && ValidOperand(ifb.o2)
    requires va_eval(IfElse(ifb, ct, cf), s, r)
    ensures  forall c, t, t' :: va_eval(c, t, t') == (t.ok ==> va_eval(c, t, t'));
    ensures  if s.ok then
                    s'.ok
                 && ValidState(s')
                 && evalGuard(s, ifb, s')
                 && cond == evalOBool(s, ifb)
                 && (if cond then va_eval(ct, s', r) else va_eval(cf, s', r))
             else
                 true //!r.ok;
{
    reveal va_eval();
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

predicate va_whileInv(b:obool, c:code, n:int, r1:va_state, r2:va_state)
{
    n >= 0 && ValidState(r1) && evalWhileLax(b, c, n, r1, r2)
}

lemma va_lemma_while(b:obool, c:code, s:va_state, r:va_state) returns(n:nat, r':va_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2)
    requires va_eval(While(b, c), s, r)
    ensures  evalWhileLax(b, c, n, s, r)
    //ensures  r'.ok
    ensures  ValidState(r');
    ensures  r' == s
    //ensures  forall c', t, t' :: va_eval(c', t, t') == (t.ok ==> va_eval(c', t, t'));
{
    reveal va_eval();
    reveal evalWhileOpaque();
//    unpack_eval_while(b, c, s, r);
    if s.ok {
        assert evalCode(While(b, c), s, r);
        n :| evalWhile(b, c, n, s, r);
    } else {
        n := 0;
    }
    r' := s;
}

lemma va_lemma_whileTrue(b:obool, c:code, n:va_int, s:va_state, r:va_state) returns(s':va_state, r':va_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires n > 0
    requires evalWhileLax(b, c, n, s, r)
    //ensures  ValidState(s) && r'.ok ==> ValidState(r');
    ensures  ValidState(s');
    ensures  evalWhileLax(b, c, n-1, r', r)
    ensures  va_eval(c, s', r');
    ensures  if s.ok then evalGuard(s, b, s') && s'.ok && evalOBool(s, b) else s' == s;
{
    reveal va_eval();
    reveal evalWhileOpaque();

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

lemma va_lemma_whileFalse(b:obool, c:code, s:va_state, r:va_state) returns(r':va_state)
    requires ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2);
    requires evalWhileLax(b, c, 0, s, r)
    ensures  forall c', t, t' :: va_eval(c', t, t') == (t.ok ==> va_eval(c', t, t'));
    ensures  if s.ok then
                    r.ok && r' == r && ValidState(r')
                     && evalGuard(s, b, r')
                     && !evalOBool(s, b)
            else
                r' == s
{
    reveal va_eval();
    reveal evalWhileOpaque();

    if !s.ok {
        r' := s;
        return;
    }

    r' := r;
}

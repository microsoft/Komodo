include "ARMdef.s.dfy"
include "bitvectors.i.dfy"

lemma lemma_update_psr_mode(oldpsr:word, newmode:word, f:bool, i:bool, newpsr:word)
    requires ValidPsrWord(oldpsr)
    requires ValidModeEncoding(newmode)
    requires newpsr == update_psr(oldpsr, newmode, f, i);
    ensures ValidPsrWord(newpsr)
    ensures decode_psr(newpsr).m == decode_mode(newmode)
{
    reveal update_psr();

    var maskbits := BitOr(if f then 0x40 else 0, if i then 0x80 else 0);
    assert maskbits == (
        if f && i then 0xc0
        else if f then 0x40
        else if i then 0x80
        else 0) by { reveal BitOr(); }

    assert BitsAsWord(0xffffffe0) == 0xffffffe0 && BitsAsWord(0x1f) == 0x1f
        by { reveal BitsAsWord(); }
    assert WordAsBits(0x10) == 0x10 && WordAsBits(0x1b) == 0x1b
        by { reveal WordAsBits(); }

    var newpsr := update_psr(oldpsr, newmode, f, i);
    var oldpsrb := WordAsBits(oldpsr);
    var newmodeb := WordAsBits(newmode);

    assert 0x10 <= newmodeb <= 0x1b
    by {
        assert 0x10 <= newmode <= 0x1b;
        lemma_BitCmpEquiv(0x10, newmode);
        lemma_BitCmpEquiv(0x1b, newmode);
    }

    assert newpsr == BitsAsWord(BitOr(BitAnd(oldpsrb, 0xffffffe0),
            BitOr(newmodeb, maskbits))) by { lemma_BitsAndWordConversions(); }

    calc {
        psr_mask_mode(newpsr);
        BitwiseAnd(newpsr, 0x1f);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(oldpsrb, 0xffffffe0),
            BitOr(newmodeb, maskbits)), 0x1f));
        { reveal BitAnd(); reveal_BitOr(); }
        BitsAsWord(newmodeb);
        { lemma_BitsAndWordConversions(); }
        newmode;
    }
}

lemma lemma_update_psr_f(oldpsr:word, newmode:word, f:bool, i:bool, newpsr:word)
    requires ValidPsrWord(oldpsr)
    requires ValidModeEncoding(newmode)
    requires newpsr == update_psr(oldpsr, newmode, f, i) && ValidPsrWord(newpsr)
    ensures decode_psr(newpsr).f == (f || decode_psr(oldpsr).f)
{
    var maskbits := BitOr(if f then 0x40 else 0, if i then 0x80 else 0);

    assert BitsAsWord(0xc0) == 0xc0 && BitsAsWord(0x40) == 0x40
        && BitsAsWord(0x80) == 0x80 && BitsAsWord(0xffffffe0) == 0xffffffe0
        && BitsAsWord(0x1f) == 0x1f
        by { reveal BitsAsWord(); }
    assert WordAsBits(0x10) == 0x10 && WordAsBits(0x1b) == 0x1b
        by { reveal WordAsBits(); }

    var oldpsrb := WordAsBits(oldpsr);
    var newmodeb := WordAsBits(newmode);

    calc {
        decode_psr(newpsr).f;
        BitwiseAnd(newpsr, 0x40) != 0;
        { assert newpsr == BitsAsWord(BitOr(BitAnd(oldpsrb, 0xffffffe0),
                                BitOr(newmodeb, maskbits)))
            by { reveal update_psr(); lemma_BitsAndWordConversions(); }
            lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(oldpsrb, 0xffffffe0),
            BitOr(newmodeb, maskbits)), 0x40)) != 0;
        { calc {
            BitAnd(BitOr(BitAnd(oldpsrb, 0xffffffe0),
                BitOr(newmodeb, maskbits)), 0x40);
            {
                assert 0x10 <= newmodeb <= 0x1b
                by {
                    assert 0x10 <= newmode <= 0x1b;
                    lemma_BitCmpEquiv(0x10, newmode);
                    lemma_BitCmpEquiv(0x1b, newmode);
                }
                reveal BitAnd(); reveal_BitOr();
            }
            BitAnd(BitOr(oldpsrb, maskbits), 0x40);
        } }
        BitsAsWord(BitAnd(BitOr(oldpsrb, maskbits), 0x40)) != 0;
        { lemma_BitOrAndRelation(oldpsrb, maskbits, 0x40); }
        BitsAsWord(BitOr(BitAnd(oldpsrb, 0x40), BitAnd(maskbits, 0x40))) != 0;
        {
            calc {
                decode_psr(oldpsr).f;
                BitwiseAnd(oldpsr, 0x40) != 0;
                { lemma_BitsAndWordConversions(); }
                BitAnd(oldpsrb, 0x40) != 0;
            }

            assert BitAnd(maskbits, 0x40) == if f then 0x40 else 0
            by {
                assert maskbits == (
                    if f && i then 0xc0
                    else if f then 0x40
                    else if i then 0x80
                    else 0) by { reveal BitOr(); }
                reveal BitAnd();
            }

            if f {
                assert BitAnd(maskbits, 0x40) == 0x40 by { reveal BitAnd(); }
            } else if decode_psr(oldpsr).f {
                assert BitAnd(oldpsrb, 0x40) == 0x40 by { reveal BitAnd(); }
            } else {
                assert BitAnd(maskbits, 0x40) == 0;
                assert BitAnd(oldpsrb, 0x40) == 0;
            }
            reveal BitOr();
        }
        f || decode_psr(oldpsr).f;
    }
}

lemma lemma_update_psr_i(oldpsr:word, newmode:word, f:bool, i:bool, newpsr:word)
    requires ValidPsrWord(oldpsr)
    requires ValidModeEncoding(newmode)
    requires newpsr == update_psr(oldpsr, newmode, f, i) && ValidPsrWord(newpsr)
    ensures decode_psr(newpsr).i == (i || decode_psr(oldpsr).i)
{
    var maskbits := BitOr(if f then 0x40 else 0, if i then 0x80 else 0);

    assert BitsAsWord(0xc0) == 0xc0 && BitsAsWord(0x40) == 0x40
        && BitsAsWord(0x80) == 0x80 && BitsAsWord(0xffffffe0) == 0xffffffe0
        && BitsAsWord(0x1f) == 0x1f
        by { reveal BitsAsWord(); }
    assert WordAsBits(0x10) == 0x10 && WordAsBits(0x1b) == 0x1b
        by { reveal WordAsBits(); }

    var oldpsrb := WordAsBits(oldpsr);
    var newmodeb := WordAsBits(newmode);

    calc {
        decode_psr(newpsr).i;
        BitwiseAnd(newpsr, 0x80) != 0;
        { assert newpsr == BitsAsWord(BitOr(BitAnd(oldpsrb, 0xffffffe0),
                                BitOr(newmodeb, maskbits)))
            by { reveal update_psr(); lemma_BitsAndWordConversions(); }
            lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(oldpsrb, 0xffffffe0),
            BitOr(newmodeb, maskbits)), 0x80)) != 0;
        { calc {
            BitAnd(BitOr(BitAnd(oldpsrb, 0xffffffe0),
                BitOr(newmodeb, maskbits)), 0x80);
            {
                assert 0x10 <= newmodeb <= 0x1b
                by {
                    assert 0x10 <= newmode <= 0x1b;
                    lemma_BitCmpEquiv(0x10, newmode);
                    lemma_BitCmpEquiv(0x1b, newmode);
                }
                reveal BitAnd(); reveal BitOr();
            }
            BitAnd(BitOr(oldpsrb, maskbits), 0x80);
        } }
        BitsAsWord(BitAnd(BitOr(oldpsrb, maskbits), 0x80)) != 0;
        { lemma_BitOrAndRelation(oldpsrb, maskbits, 0x80); }
        BitsAsWord(BitOr(BitAnd(oldpsrb, 0x80), BitAnd(maskbits, 0x80))) != 0;
        {
            calc {
                decode_psr(oldpsr).i;
                BitwiseAnd(oldpsr, 0x80) != 0;
                { lemma_BitsAndWordConversions(); }
                BitAnd(oldpsrb, 0x80) != 0;
            }

            assert maskbits == (
                if f && i then 0xc0
                else if f then 0x40
                else if i then 0x80
                else 0) by { reveal BitOr(); }

            assert (BitAnd(maskbits, 0x80) != 0) == i by { reveal BitAnd(); }

            if i {
                assert BitAnd(maskbits, 0x80) == 0x80 by { reveal BitAnd(); }
            } else if decode_psr(oldpsr).i {
                assert BitAnd(oldpsrb, 0x80) == 0x80 by { reveal BitAnd(); }
            } else {
                assert BitAnd(maskbits, 0x80) == 0;
                assert BitAnd(oldpsrb, 0x80) == 0;
            }
            reveal BitOr();
        }
        i || decode_psr(oldpsr).i;
    }
}

lemma lemma_update_psr(oldpsr:word, newmode:word, f:bool, i:bool)
    requires ValidPsrWord(oldpsr)
    requires ValidModeEncoding(newmode)
    ensures ValidPsrWord(update_psr(oldpsr, newmode, f, i))
    ensures decode_psr(update_psr(oldpsr, newmode, f, i))
        == var o := decode_psr(oldpsr); PSR(decode_mode(newmode), f || o.f, i || o.i)
{
    var newpsr := update_psr(oldpsr, newmode, f, i);

    lemma_update_psr_mode(oldpsr, newmode, f, i, newpsr);
    lemma_update_psr_f(oldpsr, newmode, f, i, newpsr);
    lemma_update_psr_i(oldpsr, newmode, f, i, newpsr);
}

lemma lemma_psr_of_exception(s:state, ex:exception)
    requires ValidState(s)
    ensures ValidPsrWord(psr_of_exception(s, ex))
{
    reveal ValidSRegState();
    var oldpsr := s.sregs[cpsr];
    var newmode := mode_of_exception(s.conf, ex);
    assert ValidPsrWord(oldpsr);
    assert ValidModeEncoding(encode_mode(newmode));
    lemma_update_psr(oldpsr, encode_mode(newmode),
                     ex == ExFIQ || newmode == Monitor, true);
}

lemma lemma_psr_still_valid(oldpsr:word, newpsr:word, newbits:word)
    requires ValidPsrWord(oldpsr)
    requires newpsr == BitwiseOr(LeftShift(RightShift(oldpsr, 5), 5), newbits)
    requires newbits == 0xd1 || newbits == 0x92
    ensures ValidPsrWord(newpsr)
    ensures decode_mode(psr_mask_mode(newpsr)) != Monitor
{
    assert WordAsBits(ARM_PSR_MODE_MASK) == 0x1f && WordAsBits(0xd1) == 0xd1
        && WordAsBits(0x92) == 0x92 && WordAsBits(0x11) == 0x11
        && WordAsBits(0x12) == 0x12 by { reveal WordAsBits(); }
    lemma_BitsAndWordConversions();

    var tmp := LeftShift(RightShift(oldpsr, 5), 5);
    assert psr_mask_mode(tmp) == 0
        by { reveal BitShiftLeft(); reveal_BitShiftRight(); reveal_BitAnd(); }

    calc {
        psr_mask_mode(newpsr);
        BitwiseAnd(newpsr, ARM_PSR_MODE_MASK);
        BitwiseAnd(BitwiseOr(tmp, newbits), ARM_PSR_MODE_MASK);
        BitwiseAnd(BitwiseOr(tmp, newbits), ARM_PSR_MODE_MASK);
        { lemma_BitOrAndRelation(WordAsBits(tmp), WordAsBits(newbits), WordAsBits(ARM_PSR_MODE_MASK)); }
        BitsAsWord(BitOr(BitAnd(WordAsBits(tmp), WordAsBits(ARM_PSR_MODE_MASK)), BitAnd(WordAsBits(newbits), WordAsBits(ARM_PSR_MODE_MASK))));
        BitsAsWord(BitOr(0, BitAnd(WordAsBits(newbits), WordAsBits(ARM_PSR_MODE_MASK))));
        { reveal BitOr(); }
        BitwiseAnd(newbits, ARM_PSR_MODE_MASK);
    }

    if newbits == 0xd1 {
        assert psr_mask_mode(newpsr) == encode_mode(FIQ) by { reveal BitAnd(); }
    } else if newbits == 0x92 {
        assert psr_mask_mode(newpsr) == encode_mode(IRQ) by { reveal BitAnd(); }
    }
}

lemma lemma_user_psr()
    ensures ValidPsrWord(encode_mode(User))
    ensures decode_psr(encode_mode(User)) == PSR(User, false, false)
{
    assert encode_mode(User) == 0x10;
    assert BitsAsWord(0x1f) == 0x1f && BitsAsWord(0x10) == 0x10
        && BitsAsWord(0x40) == 0x40 && BitsAsWord(0x80) == 0x80
        by { reveal BitsAsWord(); }

    calc {
        psr_mask_mode(0x10);
        BitwiseAnd(0x10, 0x1f);
        { lemma_BitsAndWordConversions(); reveal_BitAnd(); }
        0x10;
    }

    assert decode_mode(0x10) == User;

    calc {
        BitwiseAnd(0x10, ARM_PSR_FIQ);
        { lemma_BitsAndWordConversions(); reveal_BitAnd(); }
        0;
    }

    calc {
        BitwiseAnd(0x10, ARM_PSR_IRQ);
        { lemma_BitsAndWordConversions(); reveal_BitAnd(); }
        0;
    }
}

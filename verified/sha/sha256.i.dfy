// REQUIRES-ANY: TEST, SHA
// RUN: %DAFNY /compile:0 %s %DARGS

include "sha256.s.dfy"
include "Seqs.s.dfy"
include "../words_and_bytes.i.dfy"

datatype SHA256_state = SHA256_state_c(H:seq<word>, W:seq<word>, atoh:atoh_Type)

predicate PartialSHA256TraceHasCorrectWs(z:SHA256Trace)
{
       |z.W| <= |z.M|
    && forall blk {:trigger z.W[blk]} {:trigger z.M[blk]} :: 0 <= blk < |z.W| ==>
              |z.W[blk]| == 64
           && |z.M[blk]| == 16
           && forall t:word {:trigger TStep(t)} :: TStep(t) && 0 <= t < 64 ==>
                     (0 <= t <= 15 ==> z.W[blk][t] == z.M[blk][t])
                  && (16 <= t <= 63 ==> z.W[blk][t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(z.W[blk][t-2]), z.W[blk][t-7]), SSIG0(z.W[blk][t-15])), z.W[blk][t-16]))
}

predicate CorrectlyAccumulatedHsForBlock(z:SHA256Trace, blk:int)
    requires 0 <= blk < |z.atoh| && 64 < |z.atoh[blk]| && blk + 1 < |z.H|;
{
    forall j {:trigger TStep(j)}:: 0 <= j < 8 && |z.H[blk]| == |z.H[blk+1]| == 8 ==> 
        z.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z.atoh[blk][64])[j], z.H[blk][j])
}

predicate CorrectlyAccumulatedHsForAllBlocks(z:SHA256Trace)
    requires |z.H|-1 <= |z.atoh|; 
{
    forall blk {:trigger CorrectlyAccumulatedHsForBlock(z, blk)} :: 0 <= blk < |z.H|-1 ==>
        |z.atoh[blk]| == 65 && CorrectlyAccumulatedHsForBlock(z, blk)
}

predicate PartialSHA256TraceHasCorrectHs(z:SHA256Trace)
{
    |z.H| > 0 &&
    |z.H| <= |z.atoh|+1 &&
    (forall blk {:trigger z.H[blk]}:: 0 <= blk < |z.H| ==> |z.H[blk]| == 8) &&
    (forall j {:trigger InitialH_SHA256(j)}:: 0 <= j < 8 ==> z.H[0][j] == InitialH_SHA256(j)) &&
    CorrectlyAccumulatedHsForAllBlocks(z)
}

predicate PartialSHA256TraceHasCorrectatohsWf(z:SHA256Trace)
{
    |z.atoh| <= |z.H| &&
    |z.atoh| <= |z.W| &&
    (forall blk {:trigger z.atoh[blk]}:: 0 <= blk < |z.atoh|-1 ==> |z.atoh[blk]| == 65) &&
    forall blk:int {:trigger TBlk(blk)}:: 0 <= blk < |z.atoh| ==>
        |z.atoh[blk]| <= 65 &&
        |z.W[blk]| == 64 &&
        (|z.atoh[blk]| > 0 ==> |z.H[blk]| == 8 && ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk])
}

predicate{:opaque} PartialSHA256TraceHasCorrectatohsOpaque(z:SHA256Trace)
{
    |z.atoh| <= |z.H| &&
    |z.atoh| <= |z.W| &&
    (forall blk :: 0 <= blk < |z.atoh|-1 ==> |z.atoh[blk]| == 65) &&
    forall blk :: 0 <= blk < |z.atoh| ==>
        |z.atoh[blk]| <= 65 &&
        |z.W[blk]| == 64 &&
        (|z.atoh[blk]| > 0 ==> |z.H[blk]| == 8 && ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk]) &&
        forall t:word {:trigger TStep(t)} :: TStep(t) && 0 <= (t as int) < |z.atoh[blk]|-1 ==>
            var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z.atoh[blk][t].h, BSIG1(z.atoh[blk][t].e)),
                                              Ch(z.atoh[blk][t].e, z.atoh[blk][t].f, z.atoh[blk][t].g)),
                                      K_SHA256(t)),
                              z.W[blk][t]);
            var T2 := BitwiseAdd32(BSIG0(z.atoh[blk][t].a), Maj(z.atoh[blk][t].a, z.atoh[blk][t].b, z.atoh[blk][t].c));
            z.atoh[blk][t+1].h == z.atoh[blk][t].g &&
            z.atoh[blk][t+1].g == z.atoh[blk][t].f &&
            z.atoh[blk][t+1].f == z.atoh[blk][t].e &&
            z.atoh[blk][t+1].e == BitwiseAdd32(z.atoh[blk][t].d, T1) &&
            z.atoh[blk][t+1].d == z.atoh[blk][t].c &&
            z.atoh[blk][t+1].c == z.atoh[blk][t].b &&
            z.atoh[blk][t+1].b == z.atoh[blk][t].a &&
            z.atoh[blk][t+1].a == BitwiseAdd32(T1, T2)
}

predicate PartialSHA256TraceHasCorrectatohs(z:SHA256Trace)
{
    PartialSHA256TraceHasCorrectatohsWf(z) && PartialSHA256TraceHasCorrectatohsOpaque(z)
}


predicate PartialSHA256TraceIsCorrect(z:SHA256Trace)
{
       PartialSHA256TraceHasCorrectWs(z)
    && PartialSHA256TraceHasCorrectHs(z)
    && PartialSHA256TraceHasCorrectatohs(z)
    && (forall i {:trigger |z.M[i]|}:: 0 <= i < |z.M| ==> |z.M[i]| == 16)
}

predicate IsSHA256TraceReadyForStep(z:SHA256Trace, nextStep:int)
    requires 0 <= nextStep <= 64;
{
       PartialSHA256TraceIsCorrect(z)
    && |z.W| == |z.H| == |z.atoh| 
    && (forall blk {:trigger |z.atoh[blk]|}:: 0 <= blk < |z.H|-1 ==> |z.atoh[blk]| == 65)
    && |z.atoh[|z.H|-1]| == nextStep+1
}

predicate IsSHA256ReadyForStep(z:SHA256Trace, s:SHA256_state, nextStep:int)
    requires 0 <= nextStep <= 64;
{
       PartialSHA256TraceIsCorrect(z)
    && |z.W| == |z.H|
    && |z.atoh| == |z.H|
    && (forall blk {:trigger |z.atoh[blk]|}:: 0 <= blk < |z.H|-1 ==> |z.atoh[blk]| == 65)
    && |z.atoh[|z.H|-1]| == nextStep+1
    && s.H == last(z.H)
    && s.W == z.W[|z.H|-1]
    && s.atoh == z.atoh[|z.H|-1][nextStep]
}

predicate{:opaque} TheAToHsAreOK(z:SHA256Trace, blk:int, t:word)
    requires 0 <= t <= 63;
    requires 0 <= blk;
    requires |z.atoh| > blk;
    requires |z.atoh[blk]| > (t+1) as int;
    requires |z.W| > blk;
    requires |z.W[blk]| == 64;
{
    var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z.atoh[blk][t].h, BSIG1(z.atoh[blk][t].e)),
                                      Ch(z.atoh[blk][t].e, z.atoh[blk][t].f, z.atoh[blk][t].g)),
                              K_SHA256(t)),
                      z.W[blk][t]);
    var T2 := BitwiseAdd32(BSIG0(z.atoh[blk][t].a), Maj(z.atoh[blk][t].a, z.atoh[blk][t].b, z.atoh[blk][t].c));
    z.atoh[blk][t+1].h == z.atoh[blk][t].g &&
    z.atoh[blk][t+1].g == z.atoh[blk][t].f &&
    z.atoh[blk][t+1].f == z.atoh[blk][t].e &&
    z.atoh[blk][t+1].e == BitwiseAdd32(z.atoh[blk][t].d, T1) &&
    z.atoh[blk][t+1].d == z.atoh[blk][t].c &&
    z.atoh[blk][t+1].c == z.atoh[blk][t].b &&
    z.atoh[blk][t+1].b == z.atoh[blk][t].a &&
    z.atoh[blk][t+1].a == BitwiseAdd32(T1, T2)
}

lemma lemma_SHA256TransitionOKAfterSettingAtoHStep1Helper1(z:SHA256Trace, blk:int, t:word)
    requires 0 <= t <= 63;
    requires 0 <= blk;
    requires |z.atoh| > blk;
    requires |z.atoh[blk]| > (t+1) as int;
    requires |z.W| > blk;
    requires |z.W[blk]| ==  64;
    requires PartialSHA256TraceHasCorrectatohs(z);
    ensures TheAToHsAreOK(z, blk, t);
{
    assert TBlk(blk) && TStep(t);
    reveal_TheAToHsAreOK();
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
}

lemma Lemma_TheAToHsAreOKIsStable(z1:SHA256Trace, z2:SHA256Trace, blk:int, t:word)
    requires 0 <= t <= 63;
    requires 0 <= blk;
    requires |z1.atoh| == |z2.atoh| > blk as int;
    requires |z1.atoh[blk]| > (t+1) as int;
    requires |z2.atoh[blk]| > (t+1) as int;
    requires z1.atoh[blk][t+1] == z2.atoh[blk][t+1];
    requires z1.atoh[blk][t] == z2.atoh[blk][t];
    requires |z1.W| > blk as int;
    requires z1.W == z2.W;
    requires |z1.W[blk]| == 64;
    requires TheAToHsAreOK(z1, blk, t);
    ensures TheAToHsAreOK(z2, blk, t);
{
    reveal_TheAToHsAreOK();
}

lemma {:timeLimitMultiplier 2} lemma_SHA256TransitionOKAfterSettingAtoHStep1(
    z1:SHA256Trace,
    s1:SHA256_state,
    z2:SHA256Trace,
    s2:SHA256_state,
    currentStep:word
    )
    requires 0 <= currentStep <= 63;
    requires IsSHA256ReadyForStep(z1, s1, currentStep as int);
    requires TBlk(|z1.H|-1) && TBlk(|z1.H|) && TStep(currentStep) && TStep(currentStep + 1);
    requires var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(s1.atoh.h, BSIG1(s1.atoh.e)), Ch(s1.atoh.e, s1.atoh.f, s1.atoh.g)),
                                       K_SHA256(currentStep)),
                               s1.W[currentStep]);
             var T2 := BitwiseAdd32(BSIG0(s1.atoh.a), Maj(s1.atoh.a, s1.atoh.b, s1.atoh.c));
             s2.atoh.h == s1.atoh.g &&
             s2.atoh.g == s1.atoh.f &&
             s2.atoh.f == s1.atoh.e &&
             s2.atoh.e == BitwiseAdd32(s1.atoh.d, T1) &&
             s2.atoh.d == s1.atoh.c &&
             s2.atoh.c == s1.atoh.b &&
             s2.atoh.b == s1.atoh.a &&
             s2.atoh.a == BitwiseAdd32(T1, T2);
    requires s2.H == s1.H;
    requires s2.W == s1.W;
    requires z2.M == z1.M && z2.H == z1.H && z2.W == z1.W;
    requires z2.atoh == z1.atoh[..|z1.H|-1] + [z1.atoh[|z1.H|-1] + [s2.atoh]];
    requires |z2.atoh| == |z1.atoh|;
    requires forall blk :: 0 <= blk < |z1.H|-1 ==> z2.atoh[blk] == z1.atoh[blk];
    requires forall t :: 0 <= t < |z1.atoh[|z1.H|-1]| ==> z2.atoh[|z1.H|-1][t] == z1.atoh[|z1.H|-1][t];
    requires z2.atoh[|z1.H|-1][|z1.atoh[|z1.H|-1]|] == s2.atoh;
    ensures forall blk:int :: 0 <= blk < |z2.atoh| ==>
        |z2.atoh[blk]| <= |z2.W[blk]| + 1 &&
        |z2.atoh[blk]| <= 65 &&
        (|z2.atoh[blk]| > 0 ==> |z2.H[blk]| == 8 && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]) &&
        (forall t:word :: 0 <= t as int < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t));
{
    forall blk | TBlk(blk) && 0 <= blk as int < |z2.atoh|
        ensures |z2.atoh[blk]| <= |z2.W[blk]| + 1;
        ensures |z2.atoh[blk]| <= 65;
        ensures (|z2.atoh[blk]| > 0 ==> |z2.H[blk]| == 8 && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]);
        ensures forall t:word :: 0 <= t as int < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t);
    {
        assert |z2.atoh[blk]| <= |z2.W[blk]| + 1;
        assert |z2.atoh[blk]| <= 65;

        if blk as int < |z2.atoh|-1 {
            assert blk < |z1.H|-1;
            assert z2.atoh[blk] == z1.atoh[blk];
            assert (|z2.atoh[blk]| > 0 ==> |z2.H[blk]| == 8 && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]);
            forall t:word | 0 <= t as int < |z1.atoh[blk]|-1
                ensures TheAToHsAreOK(z2, blk, t);
            {
                lemma_SHA256TransitionOKAfterSettingAtoHStep1Helper1(z1, blk, t);
                Lemma_TheAToHsAreOKIsStable(z1, z2, blk, t);
            }
            assert forall t:word :: 0 <= t as int < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t);
        }
        else {
            assert blk == |z1.H|-1;
            assert (|z2.atoh[blk]| > 0 ==> |z2.H[blk]| == 8 && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]);
            forall t:word | 0 <= t as int < |z2.atoh[blk]|-1
                ensures TheAToHsAreOK(z2, blk, t);
            {
                if t as int < |z2.atoh[blk]|-2 {
                    assert t < currentStep;
                    lemma_SHA256TransitionOKAfterSettingAtoHStep1Helper1(z1, blk, t);
                    Lemma_TheAToHsAreOKIsStable(z1, z2, blk, t);
                    assert TheAToHsAreOK(z2, blk, t);
                }
                else {
                    assert t == currentStep;
                    calc { true; { reveal_TheAToHsAreOK(); } TheAToHsAreOK(z2, blk, t); }
                }
            }
        }
    }
}

lemma lemma_SHA256TransitionOKAfterSettingAtoH(
    z1:SHA256Trace,
    s1:SHA256_state,
    z2:SHA256Trace,
    s2:SHA256_state,
    currentStep:word
    )
    requires 0 <= currentStep <= 63;
    requires IsSHA256ReadyForStep(z1, s1, currentStep as int);
    requires TBlk(|z1.H|-1) && TBlk(|z1.H|) && TStep(currentStep) && TStep(currentStep + 1);
    requires var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(s1.atoh.h, BSIG1(s1.atoh.e)), Ch(s1.atoh.e, s1.atoh.f, s1.atoh.g)),
                                       K_SHA256(currentStep)),
                               s1.W[currentStep]);
             var T2 := BitwiseAdd32(BSIG0(s1.atoh.a), Maj(s1.atoh.a, s1.atoh.b, s1.atoh.c));
             s2.atoh.h == s1.atoh.g &&
             s2.atoh.g == s1.atoh.f &&
             s2.atoh.f == s1.atoh.e &&
             s2.atoh.e == BitwiseAdd32(s1.atoh.d, T1) &&
             s2.atoh.d == s1.atoh.c &&
             s2.atoh.c == s1.atoh.b &&
             s2.atoh.b == s1.atoh.a &&
             s2.atoh.a == BitwiseAdd32(T1, T2);
    requires s2.H == s1.H;
    requires s2.W == s1.W;
    requires z2 == SHA256Trace_c(z1.M, z1.H, z1.W, z1.atoh[..|z1.H|-1] + [z1.atoh[|z1.H|-1] + [s2.atoh]]);
    ensures IsSHA256ReadyForStep(z2, s2, (currentStep as int)+1);
{
    lemma_SHA256TransitionOKAfterSettingAtoHStep1(z1, s1, z2, s2, currentStep);

    assert forall blk:int :: 0 <= blk < |z2.atoh| ==>
        |z2.atoh[blk]| <= |z2.W[blk]| + 1 &&
        |z2.atoh[blk]| <= 65 &&
        (|z2.atoh[blk]| > 0 ==> |z2.H[blk]| == 8 && ConvertAtoHToSeq(z2.atoh[blk][0]) == z2.H[blk]) &&
        (forall t:word :: 0 <= t as int < |z2.atoh[blk]|-1 ==> TheAToHsAreOK(z2, blk, t));

    forall blk:int | 0 <= blk < |z2.atoh|
        ensures forall t:word {:trigger TStep(t)} :: TStep(t) && 0 <= t as int < |z2.atoh[blk]|-1 ==>
            var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z2.atoh[blk][t].h, BSIG1(z2.atoh[blk][t].e)),
                                              Ch(z2.atoh[blk][t].e, z2.atoh[blk][t].f, z2.atoh[blk][t].g)),
                                      K_SHA256(t)),
                              z2.W[blk][t]);
            var T2 := BitwiseAdd32(BSIG0(z2.atoh[blk][t].a), Maj(z2.atoh[blk][t].a, z2.atoh[blk][t].b, z2.atoh[blk][t].c));
            z2.atoh[blk][t+1].h == z2.atoh[blk][t].g &&
            z2.atoh[blk][t+1].g == z2.atoh[blk][t].f &&
            z2.atoh[blk][t+1].f == z2.atoh[blk][t].e &&
            z2.atoh[blk][t+1].e == BitwiseAdd32(z2.atoh[blk][t].d, T1) &&
            z2.atoh[blk][t+1].d == z2.atoh[blk][t].c &&
            z2.atoh[blk][t+1].c == z2.atoh[blk][t].b &&
            z2.atoh[blk][t+1].b == z2.atoh[blk][t].a &&
            z2.atoh[blk][t+1].a == BitwiseAdd32(T1, T2);
    {
        forall t:word {:trigger TStep(t)} | TStep(t) && 0 <= t as int < |z2.atoh[blk]|-1
            ensures var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z2.atoh[blk][t].h, BSIG1(z2.atoh[blk][t].e)),
                                                      Ch(z2.atoh[blk][t].e, z2.atoh[blk][t].f, z2.atoh[blk][t].g)),
                                              K_SHA256(t)),
                                      z2.W[blk][t]);
                    var T2 := BitwiseAdd32(BSIG0(z2.atoh[blk][t].a), Maj(z2.atoh[blk][t].a, z2.atoh[blk][t].b, z2.atoh[blk][t].c));
                    z2.atoh[blk][t+1].h == z2.atoh[blk][t].g &&
                    z2.atoh[blk][t+1].g == z2.atoh[blk][t].f &&
                    z2.atoh[blk][t+1].f == z2.atoh[blk][t].e &&
                    z2.atoh[blk][t+1].e == BitwiseAdd32(z2.atoh[blk][t].d, T1) &&
                    z2.atoh[blk][t+1].d == z2.atoh[blk][t].c &&
                    z2.atoh[blk][t+1].c == z2.atoh[blk][t].b &&
                    z2.atoh[blk][t+1].b == z2.atoh[blk][t].a &&
                    z2.atoh[blk][t+1].a == BitwiseAdd32(T1, T2);
        {
            assert TheAToHsAreOK(z2, blk, t);
            reveal_TheAToHsAreOK();
        }
    }
    reveal_PartialSHA256TraceHasCorrectatohsOpaque();
    assert TBlk(|z1.H|-1);
    assert TStep(currentStep);


    forall blk {:trigger CorrectlyAccumulatedHsForBlock(z2, blk)} | 0 <= blk as int < |z2.H|-1 
        ensures |z2.atoh[blk]| == 65 && CorrectlyAccumulatedHsForBlock(z2, blk);
    {
        assert CorrectlyAccumulatedHsForBlock(z1, blk);
        forall j | 0 <= j < 8 && |z1.H[blk]| == |z1.H[(blk as int)+1]| == 8
            ensures z1.H[(blk as int)+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z1.atoh[blk][64])[j], z1.H[blk][j])
        {
            assert TStep(j);
        }
        forall j | 0 <= j < 8 && |z2.H[blk]| == |z2.H[(blk as int)+1]| == 8 
            ensures z2.H[(blk as int)+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z2.atoh[blk][64])[j], z2.H[blk][j])
        {
            assert TStep(j);
        }
        assert CorrectlyAccumulatedHsForBlock(z2, blk);
    }
}


lemma lemma_SHA256DigestOneBlockHelper1(
    z:SHA256Trace,
    W:seq<word>,
    atoh:atoh_Type,
    M:seq<word>
    ) returns (
    z':SHA256Trace
    )
    requires IsCompleteSHA256Trace(z);
    requires SHA256TraceIsCorrect(z);
    requires |W| == 64;
    requires |M| == 16;
    requires forall t:word {:trigger TStep(t)} :: TStep(t) && 0 <= t < 16 ==> W[t] == M[t];
    requires forall t:word {:trigger TStep(t)} :: TStep(t) && 16 <= t <= 63 ==> W[t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(W[t-2]), W[t-7]), SSIG0(W[t-15])), W[t-16]);
    requires atoh == atoh_c(last(z.H)[0], last(z.H)[1], last(z.H)[2], last(z.H)[3], 
                            last(z.H)[4], last(z.H)[5], last(z.H)[6], last(z.H)[7]);
    ensures  z' == z.(M := z.M + [M], W := z.W + [W], atoh := z.atoh + [[atoh]]);
    ensures  IsSHA256TraceReadyForStep(z', 0);
{
    z' := z.(M := z.M + [M], W := z.W + [W[..]], atoh := z.atoh + [[atoh]]);

    forall blk {:trigger CorrectlyAccumulatedHsForBlock(z', blk)} | 0 <= blk < |z'.H|-1
        ensures |z'.atoh[blk]| == 65;
        ensures CorrectlyAccumulatedHsForBlock(z', blk);
    {
        assert TBlk(blk);
    }
    assert CorrectlyAccumulatedHsForAllBlocks(z');

    forall blk:int {:trigger TBlk(blk)} | 0 <= blk < |z'.atoh|
        ensures |z'.atoh[blk]| <= 65;
        ensures |z'.W[blk]| == 64;
        ensures (|z'.atoh[blk]| > 0 ==> |z'.H[blk]| == 8 && ConvertAtoHToSeq(z'.atoh[blk][0]) == z'.H[blk]);
    {
    }
    assert PartialSHA256TraceHasCorrectatohsWf(z');

    forall blk {:trigger z'.W[blk]} {:trigger z'.M[blk]} | 0 <= blk < |z'.W|
        ensures |z'.W[blk]| == 64;
        ensures |z'.M[blk]| == 16;
        ensures forall t {:trigger TStep(t)} :: TStep(t) && 0 <= t < 64 ==>
                     (0 <= t <= 15 ==> z'.W[blk][t] == z'.M[blk][t])
                     && (16 <= t <= 63 ==> z'.W[blk][t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(z'.W[blk][t-2]), z'.W[blk][t-7]), SSIG0(z'.W[blk][t-15])), z'.W[blk][t-16]));
    {
        assert TBlk(blk);
    }
    assert PartialSHA256TraceHasCorrectWs(z');

    reveal_PartialSHA256TraceHasCorrectatohsOpaque();

    assert IsSHA256TraceReadyForStep(z', 0);
}


lemma lemma_SHA256DigestOneBlockHelper2(
    z:SHA256Trace,
    old_H:seq<word>,
    H:seq<word>
    ) returns (
    z':SHA256Trace//,
    //processed_bytes':seq<uint8>
    )
    requires |H| == |old_H| == 8;
    requires |z.M| == |z.H| > 0;
    requires last(z.H) == old_H;
    requires IsSHA256TraceReadyForStep(z, 64);
    requires H[0] == BitwiseAdd32(last(last(z.atoh)).a, old_H[0]);
    requires H[1] == BitwiseAdd32(last(last(z.atoh)).b, old_H[1]);
    requires H[2] == BitwiseAdd32(last(last(z.atoh)).c, old_H[2]);
    requires H[3] == BitwiseAdd32(last(last(z.atoh)).d, old_H[3]);
    requires H[4] == BitwiseAdd32(last(last(z.atoh)).e, old_H[4]);
    requires H[5] == BitwiseAdd32(last(last(z.atoh)).f, old_H[5]);
    requires H[6] == BitwiseAdd32(last(last(z.atoh)).g, old_H[6]);
    requires H[7] == BitwiseAdd32(last(last(z.atoh)).h, old_H[7]);
    //requires WordSeqToBytes(ConcatenateSeqs(z.M[..|z.H|-1])) == ctx.processed_bytes;
    ensures  z' == z.(H := z.H + [H]);
    ensures  IsCompleteSHA256Trace(z');
    ensures  SHA256TraceIsCorrect(z');
    //ensures  WordSeqToBytes(ConcatenateSeqs(z'.M)) == processed_bytes';
    //ensures  processed_bytes' == ctx.processed_bytes + WordSeqToBytes(last(z.M));
//    ensures  |processed_bytes'| == |ctx.processed_bytes| + 64;
//    ensures  |processed_bytes'| % 64 == 0;
//    ensures  H == last(z'.H);
{
    z' := z.(H := z.H + [H]);
    var atoh := last(last(z.atoh));

    forall blk:int {:trigger TBlk(blk)} | TBlk(blk)
        ensures forall j :: 0 <= blk < |z'.M| && 0 <= j < 8 ==> z'.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z'.atoh[blk][64])[j], z'.H[blk][j]);
    {
        if 0 <= blk < |z.H|-1 {
            assert PartialSHA256TraceIsCorrect(z);
            assert CorrectlyAccumulatedHsForBlock(z, blk);
            forall j | 0 <= j < 8
                ensures z.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z.atoh[blk][64])[j], z.H[blk][j]);
            {
                assert TStep(j);
            }
        }
        else if blk == |z.H|-1 {
            forall j | 0 <= j < 8
                ensures z'.H[blk+1][j] == BitwiseAdd32(ConvertAtoHToSeq(z'.atoh[blk][64])[j], z'.H[blk][j]);
            {
                assert z'.atoh[blk][64] == atoh;
                assert z'.H[blk][j] == old_H[j];
                assert z'.H[blk+1][j] == H[j] as word;
                ghost var atoh_seq := ConvertAtoHToSeq(atoh);
                     if j == 0 { assert H[0] == BitwiseAdd32(atoh.a, old_H[0]); }
                else if j == 1 { assert H[1] == BitwiseAdd32(atoh.b, old_H[1]); }
                else if j == 2 { assert H[2] == BitwiseAdd32(atoh.c, old_H[2]); }
                else if j == 3 { assert H[3] == BitwiseAdd32(atoh.d, old_H[3]); }
                else if j == 4 { assert H[4] == BitwiseAdd32(atoh.e, old_H[4]); }
                else if j == 5 { assert H[5] == BitwiseAdd32(atoh.f, old_H[5]); }
                else if j == 6 { assert H[6] == BitwiseAdd32(atoh.g, old_H[6]); }
                else if j == 7 { assert H[7] == BitwiseAdd32(atoh.h, old_H[7]); }
            }
        }
    }

    forall blk | 0 <= blk < |z'.M|
        ensures ConvertAtoHToSeq(z'.atoh[blk][0]) == z'.H[blk];
        ensures forall t:word {:trigger TStep(t)} :: TStep(t) && 0 <= t <= 63 ==>
            (var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z'.atoh[blk][t].h, BSIG1(z'.atoh[blk][t].e)),
                                      Ch(z'.atoh[blk][t].e, z'.atoh[blk][t].f, z'.atoh[blk][t].g)), K_SHA256(t)),
                              z'.W[blk][t]);
            var T2 := BitwiseAdd32(BSIG0(z'.atoh[blk][t].a), Maj(z'.atoh[blk][t].a, z'.atoh[blk][t].b, z'.atoh[blk][t].c));
            z'.atoh[blk][t+1].h == z'.atoh[blk][t].g &&
            z'.atoh[blk][t+1].g == z'.atoh[blk][t].f &&
            z'.atoh[blk][t+1].f == z'.atoh[blk][t].e &&
            z'.atoh[blk][t+1].e == BitwiseAdd32(z'.atoh[blk][t].d, T1) &&
            z'.atoh[blk][t+1].d == z'.atoh[blk][t].c &&
            z'.atoh[blk][t+1].c == z'.atoh[blk][t].b &&
            z'.atoh[blk][t+1].b == z'.atoh[blk][t].a &&
            z'.atoh[blk][t+1].a == BitwiseAdd32(T1, T2))
    {
        forall t:word {:trigger TStep(t)}
            ensures TStep(t) && 0 <= t <= 63 ==>
                (var T1 := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(z'.atoh[blk][t].h, BSIG1(z'.atoh[blk][t].e)),
                                          Ch(z'.atoh[blk][t].e, z'.atoh[blk][t].f, z'.atoh[blk][t].g)), K_SHA256(t)),
                                  z'.W[blk][t]);
                var T2 := BitwiseAdd32(BSIG0(z'.atoh[blk][t].a), Maj(z'.atoh[blk][t].a, z'.atoh[blk][t].b, z'.atoh[blk][t].c));
                z'.atoh[blk][t+1].h == z'.atoh[blk][t].g &&
                z'.atoh[blk][t+1].g == z'.atoh[blk][t].f &&
                z'.atoh[blk][t+1].f == z'.atoh[blk][t].e &&
                z'.atoh[blk][t+1].e == BitwiseAdd32(z'.atoh[blk][t].d, T1) &&
                z'.atoh[blk][t+1].d == z'.atoh[blk][t].c &&
                z'.atoh[blk][t+1].c == z'.atoh[blk][t].b &&
                z'.atoh[blk][t+1].b == z'.atoh[blk][t].a &&
                z'.atoh[blk][t+1].a == BitwiseAdd32(T1, T2));
        {
            assert PartialSHA256TraceIsCorrect(z);
            assert TBlk(blk);
            assert z'.atoh[blk] == z.atoh[blk];
            reveal_PartialSHA256TraceHasCorrectatohsOpaque();
        }

        assert PartialSHA256TraceIsCorrect(z);
        assert PartialSHA256TraceHasCorrectatohsWf(z);
        assert TBlk(blk);
        assert |z.atoh[blk]| > 0;
        assert ConvertAtoHToSeq(z.atoh[blk][0]) == z.H[blk];
        assert ConvertAtoHToSeq(z'.atoh[blk][0]) == z'.H[blk];
    }

//    processed_bytes' := ctx.processed_bytes + WordSeqToBytes(last(z.M));
//    lemma_EffectOfAddingBytesOnWordSeqToBytesOfConcatenateSeqs(z.M[..|z.H|-1], ctx.processed_bytes, last(z.M), processed_bytes');
//    assert z.M[..|z.H|-1] + [last(z.M)] == z'.M;
//    lemma_AddingMultipleOfNDoesntChangeModN(|WordSeqToBytes(last(z.M))|, |ctx.processed_bytes|, 64);
}

lemma lemma_ArrayOffsetConcatenation<T>(a:seq<T>, i:int, j:int, k:int)
    requires 0 <= i <= j <= k <= |a|;
    ensures  a[i..j] + a[j..k] == a[i..k];
{
}

lemma lemma_SeqConcatenationIsAssociative<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>)
    ensures (s1 + s2) + s3 == s1 + (s2 + s3);
{
}

//After the final call, we know:
//    assert trace_out.M[SeqLength(trace_in.M)] == bswap32_seq(last_block);
//where last_block is a series of words.  This implies, more or less that:
//    trace_out.M == trace_in.M + [bswap32_seq(last_block)]
//To meet the preconditions below, we need to prove that
//WordSeqToBytes(ConcatenateSeqs(z.M)) == message + unprocessed_bytes;
//or 
//WordSeqToBytes(ConcatenateSeqs(trace_out.M)) == WordSeqToBytes(ConcatenateSeqs(trace_in.M)) + unprocessed_bytes;
//That means, we need to prove that
//WordSeqToBytes(bswap32_seq(last_block)) == unprocessed_bytes

lemma lemma_SHA256FinalHelper1(
    z:SHA256Trace,
    H:seq<word>,
    processed_bytes:seq<byte>,
    unprocessed_bytes:seq<byte>,
    message:seq<byte>
    )
    requires |H| == 8;
    requires |processed_bytes| % 64 == 0;
    requires |unprocessed_bytes| == 64;
	requires |message| % 64 == 0;
    requires IsCompleteSHA256Trace(z);
    requires SHA256TraceIsCorrect(z);
    requires WordSeqToBytes(ConcatenateSeqs(z.M)) == processed_bytes;
    requires H == last(z.H);
    requires processed_bytes == message + unprocessed_bytes;
    requires unprocessed_bytes[0] == 0x80;
    requires unprocessed_bytes[1..56] == RepeatByte(0, 55);
	requires |message| <= MaxBytesForSHA();
    requires unprocessed_bytes[56..64] == Uint64ToBytes(|message|*8);
    
    ensures  WordSeqToBytes(ConcatenateSeqs(z.M)) == 
             message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes((|message| as uint64) * 8);
{
    calc {
        55;
        55 - (|message| % 64);
        (55 - (|message| % 64)) % 64;
        (119 - (|message| % 64)) % 64;
    }

    calc {
        WordSeqToBytes(ConcatenateSeqs(z.M));
        processed_bytes;
        message + unprocessed_bytes;
            { lemma_ArrayOffsetConcatenation(unprocessed_bytes, 0, 1, 64); }
        message + ([0x80] + unprocessed_bytes[1..64]);
            { lemma_SeqConcatenationIsAssociative(message, [0x80], unprocessed_bytes[1..64]); }
        message + [0x80] + unprocessed_bytes[1..64];
            { lemma_ArrayOffsetConcatenation(unprocessed_bytes, 1, 56, 64); }
        message + [0x80] + (RepeatByte(0, 55) + unprocessed_bytes[56..64]);
            { lemma_SeqConcatenationIsAssociative(message + [0x80], RepeatByte(0, 55), unprocessed_bytes[56..64]); }
        message + [0x80] + RepeatByte(0, 55) + unprocessed_bytes[56..64];
        message + [0x80] + RepeatByte(0, 55) + Uint64ToBytes(|message| * 8);
        message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes(|message| * 8);
        message + [0x80] + RepeatByte(0, (119 - (|message| % 64)) % 64) + Uint64ToBytes((|message| as uint64) * 8);
    }
}


// TODO
// Note: This lemma already exists in words_and_bytes.i.dfy in Vale, 
//       but it relies on math libraries that haven't been ported to Komodo yet
//lemma lemma_BytesToWord_WordToBytes_inverses(b0:byte, b1:byte, b2:byte, b3:byte)
//    ensures WordToBytes(BytesToWord(b0,b1,b2,b3)) == [b0,b1,b2,b3];

// TODO
//lemma bswap32_on_byte(b:byte) 
//    ensures WordToBytes(b) == [0, 0, 0, b];
///*    
//{
//    reveal_WordToBytes();
//}
//*/

lemma convert_0x80()
    ensures WordSeqToBytes([0x80000000]) == [0x80, 0, 0, 0];
{
    calc { 
        WordSeqToBytes([0x80000000]);
        WordToBytes(0x80000000);
            { lemma_implode8_WordToBytes(0x80, 0, 0, 0); }
        [0x80, 0, 0, 0];
    }
}

// TODO
//lemma length_to_bytes(length:word)
//    ensures WordSeqToBytes(bswap32_seq([0, length])) == Uint64ToBytes(length);

lemma length_to_bytes_simple(length:word)
    ensures WordSeqToBytes([0, length]) == Uint64ToBytes(length);
{
    assert{:fuel WordSeqToBytes, 2} WordSeqToBytes([0, length]) == WordToBytes(0) + WordToBytes(length);
    lemma_implode32_Uint64ToBytes(0, length);
}


ghost method SHA_padding_words2bytes(words:seq<word>, length:word) returns (bytes:seq<byte>)
    requires |words| == 16;
    requires words[0] == 0x80000000;
    requires forall i :: 1 <= i < 15 ==> words[i] == 0;
    requires words[15] == length;
    ensures |bytes| == 64;
    ensures bytes[0] == 0x80;
    ensures bytes[1..56] == RepeatByte(0, 55);
    ensures bytes[56..64] == Uint64ToBytes(length);
    ensures WordSeqToBytes(words) == bytes;
{
    bytes := [0x80] + RepeatByte(0, 55) + Uint64ToBytes(length);
    calc {
        WordSeqToBytes(words);
        WordToBytes(words[0]) + WordSeqToBytes(words[1..]);
        WordToBytes(0x80000000) + WordSeqToBytes(words[1..]);
            { assert words[1..] == words[1..14] + words[14..]; }
        WordToBytes(0x80000000) + WordSeqToBytes(words[1..14] + words[14..]);
            { lemma_WordSeqToBytes_adds(words[1..14], words[14..]); }
        WordToBytes(0x80000000) + WordSeqToBytes(words[1..14]) + WordSeqToBytes(words[14..]);
            { WordSeqToBytes_on_zero(words[1..14]); }
        WordToBytes(0x80000000) + RepeatByte(0, 13*4) + WordSeqToBytes(words[14..]);
        WordToBytes(0x80000000) + RepeatByte(0, 52) + WordSeqToBytes(words[14..]);
        WordToBytes(0x80000000) + RepeatByte(0, 52) + WordSeqToBytes([words[14], words[15]]);
        WordToBytes(0x80000000) + RepeatByte(0, 52) + WordSeqToBytes([0, length]);
            { length_to_bytes_simple(length); }
        WordToBytes(0x80000000) + RepeatByte(0, 52) + Uint64ToBytes(length);
        WordToBytes(0x80000000) + RepeatByte(0, 52) + bytes[56..64];
            { convert_0x80(); }
        [0x80, 0, 0, 0] + RepeatByte(0, 52) + bytes[56..64];
        [0x80] + [0, 0, 0] + RepeatByte(0, 52) + bytes[56..64];
            { assert RepeatByte(0, 3) == [0, 0, 0]; }
        [0x80] + RepeatByte(0, 3) + RepeatByte(0, 52) + bytes[56..64];
            { RepeatByte_adds(0, 3, 52); }
        [0x80] + RepeatByte(0, 55) + bytes[56..64];
        [bytes[0]] + bytes[1..56] + bytes[56..64];
        bytes;
    }
}

lemma lemma_ConcatenateSeqs_M_length<T>(M:seq<seq<T>>)
    //requires IsCompleteSHA256Trace(trace);
    requires forall i :: 0 <= i < |M| ==> |M[i]| == 16;
    //requires SHA256TraceIsCorrect(trace);
    ensures  |ConcatenateSeqs(M)| == |M|*16;
{
    if |M| == 0 {
    } else {
        assert |M[0]| == 16;
        lemma_ConcatenateSeqs_M_length(M[1..]);
    }
}


//// Probably not true:    
//lemma lemma_WordSeqToBytes_is_bswap32_seq(s:seq<word>)
//    ensures WordSeqToBytes(s) == bswap32_seq(s);
//{
//	  assume false;
//    if s == [] {
//        reveal_bswap32_seq();
//    } else {
//        var bytes := WordToBytes(s[0]);
//        calc {
//            WordSeqToBytes(s);
//            WordToBytes(s[0]) + WordSeqToBytes(s[1..]);
//                { lemma_BytesToWord_WordToBytes_inverses(bytes[3], bytes[2], bytes[1], bytes[0]); }
//            [BytesToWord(bytes[3], bytes[2], bytes[1], bytes[0])] + WordSeqToBytes(s[1..]);
//            [bswap32(s[0])] + WordSeqToBytes(s[1..]);
//                { lemma_WordSeqToBytes_is_bswap32_seq(s[1..]); }
//            [bswap32(s[0])] + bswap32_seq(s[1..]);
//                { reveal_bswap32_seq(); }
//            bswap32_seq(s);
//        }
//    }
//}

lemma lemma_ConcatenateSeqs_Adds<T>(s:seq<seq<T>>, s':seq<seq<T>>)
    ensures ConcatenateSeqs(s + s') == ConcatenateSeqs(s) + ConcatenateSeqs(s'); 
{
    if s == [] {
    } else {
        calc {
            ConcatenateSeqs(s + s');
            s[0] + ConcatenateSeqs((s + s')[1..]);
                { assert (s + s')[1..] == s[1..] + s'; }
            s[0] + ConcatenateSeqs(s[1..] + s');
                { lemma_ConcatenateSeqs_Adds(s[1..], s'); }
            s[0] + ConcatenateSeqs(s[1..]) + ConcatenateSeqs(s');
            ConcatenateSeqs(s) + ConcatenateSeqs(s'); 
        }
    }
}
    
lemma lemma_Trace_stitching(M:seq<seq<word>>, M':seq<seq<word>>, words:seq<word>, bytes:seq<byte>)
    requires forall i :: 0 <= i < |M| ==> |M[i]| == 16;
    requires |M'| == |M| + 1;
    requires M'[0..|M|] == M;
    requires M'[|M|] == words;
    requires bytes == WordSeqToBytes(words); 
    ensures  WordSeqToBytes(ConcatenateSeqs(M')) == WordSeqToBytes(ConcatenateSeqs(M)) + bytes;
{
    calc {
        WordSeqToBytes(ConcatenateSeqs(M'));
            { assert M' == M + [words]; }
        WordSeqToBytes(ConcatenateSeqs(M + [words]));
            { lemma_ConcatenateSeqs_Adds(M, [words]); }
        WordSeqToBytes(ConcatenateSeqs(M) + ConcatenateSeqs([words]));
            { assert ConcatenateSeqs([words]) == words; }
        WordSeqToBytes(ConcatenateSeqs(M) + words);
            { lemma_WordSeqToBytes_adds(ConcatenateSeqs(M), words); }
        WordSeqToBytes(ConcatenateSeqs(M)) + WordSeqToBytes(words);
        WordSeqToBytes(ConcatenateSeqs(M)) + bytes;
    }
}

lemma lemma_SHA256FinalHelper1Wrapper(
    trace_in:SHA256Trace,
    trace_out:SHA256Trace,
    unprocessed_bytes:seq<byte>
    )
    requires |unprocessed_bytes| == 64;
    requires IsCompleteSHA256Trace(trace_in);
    requires SHA256TraceIsCorrect(trace_in);
    requires unprocessed_bytes[0] == 0x80;
    requires unprocessed_bytes[1..56] == RepeatByte(0, 55);
    requires |WordSeqToBytes(ConcatenateSeqs(trace_in.M))|*8 < 0x1_0000_0000_0000_0000;
    requires unprocessed_bytes[56..64] == Uint64ToBytes(|WordSeqToBytes(ConcatenateSeqs(trace_in.M))|*8);
    requires WordSeqToBytes(ConcatenateSeqs(trace_out.M)) == WordSeqToBytes(ConcatenateSeqs(trace_in.M)) + unprocessed_bytes;
    requires IsCompleteSHA256Trace(trace_out);
    requires SHA256TraceIsCorrect(trace_out);
    ensures  IsSHA256(WordSeqToBytes(ConcatenateSeqs(trace_in.M)), last(trace_out.H));
{
    var message_bytes := WordSeqToBytes(ConcatenateSeqs(trace_in.M));
    var hash := last(trace_out.H);

    calc {
        |message_bytes|;
        |WordSeqToBytes(ConcatenateSeqs(trace_in.M))|;
        |ConcatenateSeqs(trace_in.M)| * 4;
            { lemma_ConcatenateSeqs_M_length(trace_in.M); }
        |trace_in.M|*16 * 4;
        |trace_in.M|*64;
    }
    lemma_SHA256FinalHelper1(trace_out, hash, WordSeqToBytes(ConcatenateSeqs(trace_out.M)),
                             unprocessed_bytes, message_bytes);
    assert DoesTraceDemonstrateSHA256(trace_out, message_bytes, hash);
    assert IsSHA256(message_bytes, hash);
}

ghost method ComputeWs(input:seq<word>) returns (W:seq<word>)
    requires |input| == 16;
    ensures |W| == 64;
    ensures forall t:word {:trigger TStep(t)} :: TStep(t) && 0 <= t < 64 ==>
                     (0 <= t <= 15 ==> W[t] == input[t])
                  && (16 <= t <= 63 ==> W[t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(W[t-2]), 
                                                                                       W[t-7]), 
                                                                          SSIG0(W[t-15])), 
                                                             W[t-16]));
{
    W := input;
    var i := 16;
    while i < 64
        invariant 16 <= i <= 64;
        invariant |W| == i;
        invariant 
            forall t:word {:trigger TStep(t)} :: TStep(t) && 0 <= t < i ==>
                     (0 <= t <= 15 ==> W[t] == input[t])
                  && (16 <= t <= i ==> W[t] == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(W[t-2]), 
                                                                                      W[t-7]), 
                                                                          SSIG0(W[t-15])), 
                                                            W[t-16]));

    {
        var new_W := BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(SSIG1(W[i-2]), 
                                                            W[i-7]), 
                                               SSIG0(W[i-15])), 
                                 W[i-16]);
        W := W + [new_W];
        i := i + 1;
    }

}

lemma lemma_InputHelper(M:seq<seq<word>>, input:seq<word>)
    requires forall i :: 0 <= i < |M| ==> |M[i]| == 16;
    requires |input| == |M| * 16;
    requires forall i :: 0 <= i < |M| ==> M[i] == input[i*16..(i+1)*16];
    ensures  ConcatenateSeqs(M) == input;
{
    if input == [] {
    } else {
        var M', input' := M[1..], input[16..];
        assert |M'| == |M| - 1 && |input'| == |input| - 16;
        assert forall i :: 0 <= i < |M'| ==> M'[i] == input'[i*16..(i+1)*16];
        lemma_InputHelper(M', input');
    }
}

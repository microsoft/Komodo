// REQUIRES-ANY: TEST, SHA
// RUN: %DAFNY /compile:0 %s %DARGS

include "sha256.s.dfy"
include "Seqs.s.dfy"

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
    && |z.W| == |z.H|
    && |z.atoh| == |z.H|
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

lemma lemma_SHA256TransitionOKAfterSettingAtoHStep1Helper1(z:SHA256Trace, ghost blk:int, t:word)
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

lemma Lemma_TheAToHsAreOKIsStable(z1:SHA256Trace, z2:SHA256Trace, ghost blk:int, t:word)
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

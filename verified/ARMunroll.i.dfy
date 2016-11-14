// REQUIRES: TEST
// RUN: %DAFNY /compile:0 %s %DARGS
include "ARMspartan.dfy"

abstract module UnrollableCode {

import opened ARMspartan_unrollablecode = ARMspartan

//////////////////////////////////////////////////
// THINGS TO BE FILLED IN BY CONCRETE MODULE
//////////////////////////////////////////////////

type GenericConstantState
type GenericCodeParameters
type GenericAuxiliaryState

function method GenericIterationCount() : int
    ensures GenericIterationCount() >= 0;

predicate GenericFramingInvariant(sp_s0:sp_state, sp_sM:sp_state)
    requires ValidState(sp_s0);
    requires ValidState(sp_sM);
    ensures sp_s0 == sp_sM ==> GenericFramingInvariant(sp_s0, sp_sM);

lemma lemma_GenericFramingInvariantTransitivity(sp_s1:sp_state, sp_s2:sp_state, sp_s3:sp_state)
    requires ValidState(sp_s1);
    requires ValidState(sp_s2);
    requires ValidState(sp_s3);
    requires GenericFramingInvariant(sp_s1, sp_s2);
    requires GenericFramingInvariant(sp_s2, sp_s3);
    ensures  GenericFramingInvariant(sp_s1, sp_s3);

predicate GenericStateInvariant(c:GenericConstantState, s:sp_state, aux:GenericAuxiliaryState, i:int, p:GenericCodeParameters)

function method GenericCodeIteration(i:int, p:GenericCodeParameters) : code
    requires 0 <= i < GenericIterationCount();

lemma sp_lemma_GenericIterationPreservesInvariants(
    sp_b0:sp_codes,
    sp_s0:sp_state,
    sp_sN:sp_state,
    i:int,
    p:GenericCodeParameters
    ) returns (
    sp_bM:sp_codes,
    sp_sM:sp_state
    )
    requires 0 <= i < GenericIterationCount();
    requires sp_require(sp_b0, GenericCodeIteration(i, p), sp_s0, sp_sN);
    ensures  sp_ensure(sp_b0, sp_bM, sp_s0, sp_sM, sp_sN);
    ensures  forall sp_id:sp_int, c:GenericConstantState, aux0:GenericAuxiliaryState {:trigger sp_trigger_GenericUnrolledChunk(sp_id, c, aux0)} ::
                 sp_trigger_GenericUnrolledChunk(sp_id, c, aux0) ==> sp_spec_GenericUnrolledChunk(c, aux0, sp_s0, sp_sM, i, i+1, p);
    ensures  GenericFramingInvariant(sp_s0, sp_sM);

//////////////////////////////////////////////////
// DERIVED THINGS
//////////////////////////////////////////////////

function sp_trigger_GenericUnrolledChunk(
    sp_id:sp_int,
    c:GenericConstantState,
    aux:GenericAuxiliaryState
    ):sp_bool
{
    true
}

function {:opaque} sp_spec_GenericUnrolledChunk(
    c:GenericConstantState,
    aux0:GenericAuxiliaryState,
    sp_s0:sp_state,
    sp_sM:sp_state,
    i0:int,
    iM:int,
    p:GenericCodeParameters
    ):sp_bool
{
    sp_s0.ok && GenericStateInvariant(c, sp_s0, aux0, i0, p) ==> sp_sM.ok && exists auxM :: GenericStateInvariant(c, sp_sM, auxM, iM, p)
}

function method sp_code_GenericUnrolledChunk(start:int, end:int, p:GenericCodeParameters) : codes
    requires 0 <= start <= end <= GenericIterationCount();
    decreases end - start;
{
    if start == end then
        CNil()
    else
        sp_CCons(GenericCodeIteration(start, p), sp_code_GenericUnrolledChunk(start+1, end, p))
}

function method sp_code_GenericUnrolled(p:GenericCodeParameters) : code
{
    Block(sp_code_GenericUnrolledChunk(0, GenericIterationCount(), p))
}

lemma sp_lemma_GenericUnrolledChunk(
    sp_b0:sp_codes,
    sp_s0:sp_state,
    sp_sN:sp_state,
    start:int,
    end:int,
    p:GenericCodeParameters
    ) returns (
    sp_bM:sp_codes,
    sp_sM:sp_state
    )
    requires 0 <= start <= end <= GenericIterationCount();
    requires sp_require(sp_b0, Block(sp_code_GenericUnrolledChunk(start, end, p)), sp_s0, sp_sN);
    ensures  sp_ensure(sp_b0, sp_bM, sp_s0, sp_sM, sp_sN);
    ensures  forall sp_id:sp_int, c:GenericConstantState, aux0:GenericAuxiliaryState {:trigger sp_trigger_GenericUnrolledChunk(sp_id, c, aux0)} ::
                 sp_trigger_GenericUnrolledChunk(sp_id, c, aux0) ==> sp_spec_GenericUnrolledChunk(c, aux0, sp_s0, sp_sM, start, end, p);
    ensures  GenericFramingInvariant(sp_s0, sp_sM);
    decreases end - start;
{
    var sp_cM, sp_sM_preliminary;
    sp_sM_preliminary, sp_cM, sp_bM := sp_lemma_block(sp_b0, sp_s0, sp_sN);
    var sp_b1:sp_codes := sp_get_block(sp_cM);
    assert sp_eval(Block(sp_bM), sp_sM_preliminary, sp_sN);

    if start == end {
        sp_sM := sp_lemma_empty(sp_s0, sp_sM_preliminary);
        reveal_sp_spec_GenericUnrolledChunk();
        forall sp_id:sp_int, c:GenericConstantState, aux0:GenericAuxiliaryState {:trigger sp_trigger_GenericUnrolledChunk(sp_id, c, aux0)}
            | sp_trigger_GenericUnrolledChunk(sp_id, c, aux0)
            ensures sp_spec_GenericUnrolledChunk(c, aux0, sp_s0, sp_sM, start, end, p);
        {
            var auxM := aux0;
            if sp_s0.ok && GenericStateInvariant(c, sp_s0, aux0, start, p)
            {
                assert GenericStateInvariant(c, sp_sM, auxM, end, p);
            }
        }
        assert GenericFramingInvariant(sp_s0, sp_sM);
        return;
    }

    var sp_bL, sp_sL := sp_lemma_GenericIterationPreservesInvariants(sp_b1, sp_s0, sp_sM_preliminary, start, p);

    var sp_bL_expanded := Block(sp_CCons(Block(sp_bL), CNil()));
    assert sp_eval(sp_bL_expanded, sp_sL, sp_sM_preliminary) by
    {
        if sp_sL.ok {
            var sL := sp_sL;
            var sM := sp_sM_preliminary;
            reveal_sp_eval();
            assert evalCode(sp_bL_expanded.block.hd, sL, sM);
            assert evalBlock(sp_bL_expanded.block.tl, sM, sM);
            assert evalBlock(sp_bL_expanded.block, sL, sM);
        }
    }

    ghost var sp_bM';
    sp_bM', sp_sM := sp_lemma_GenericUnrolledChunk(sp_bL_expanded.block, sp_sL, sp_sM_preliminary, start+1, end, p);
    sp_sM := sp_lemma_empty(sp_sM, sp_sM_preliminary);
    assert sp_eval(Block(sp_bM), sp_sM, sp_sN);
    assert sp_ensure(sp_b0, sp_bM, sp_s0, sp_sM, sp_sN);
    lemma_GenericFramingInvariantTransitivity(sp_s0, sp_sL, sp_sM);

    reveal_sp_spec_GenericUnrolledChunk();
    forall sp_id:sp_int, c:GenericConstantState, aux0:GenericAuxiliaryState {:trigger sp_trigger_GenericUnrolledChunk(sp_id, c, aux0)}
        | sp_trigger_GenericUnrolledChunk(sp_id, c, aux0)
        ensures sp_spec_GenericUnrolledChunk(c, aux0, sp_s0, sp_sM, start, end, p);
    {
        assert sp_trigger_GenericUnrolledChunk(sp_id, c, aux0);
        if sp_s0.ok && GenericStateInvariant(c, sp_s0, aux0, start, p)
        {
            assert sp_sL.ok;
            var auxL :| GenericStateInvariant(c, sp_sL, auxL, start+1, p);
            assert sp_trigger_GenericUnrolledChunk(sp_id, c, auxL);
            assert sp_spec_GenericUnrolledChunk(c, auxL, sp_sL, sp_sM, start+1, end, p);
            assert sp_spec_GenericUnrolledChunk(c, aux0, sp_s0, sp_sM, start, end, p);
        }
    }
}

lemma sp_lemma_GenericUnrolled(
    sp_b0:sp_codes,
    sp_s0:sp_state,
    sp_sN:sp_state,
    p:GenericCodeParameters
    ) returns (
    sp_bM:sp_codes,
    sp_sM:sp_state
    )
    requires sp_require(sp_b0, sp_code_GenericUnrolled(p), sp_s0, sp_sN);
    ensures  sp_ensure(sp_b0, sp_bM, sp_s0, sp_sM, sp_sN);
    ensures  forall sp_id:sp_int, c:GenericConstantState, aux0:GenericAuxiliaryState {:trigger sp_trigger_GenericUnrolledChunk(sp_id, c, aux0)} ::
                 sp_trigger_GenericUnrolledChunk(sp_id, c, aux0) ==> sp_spec_GenericUnrolledChunk(c, aux0, sp_s0, sp_sM, 0, GenericIterationCount(), p);
    ensures  GenericFramingInvariant(sp_s0, sp_sM);
{
    sp_bM, sp_sM := sp_lemma_GenericUnrolledChunk(sp_b0, sp_s0, sp_sN, 0, GenericIterationCount(), p);
}
    
}

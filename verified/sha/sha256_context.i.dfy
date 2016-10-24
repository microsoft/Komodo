// REQUIRES-ANY: TEST, SHA
// RUN: %DAFNY /compile:0 %s %DARGS

include "sha256.i.dfy"
include "../../Collections/Seqs.i.dfy"

import opened Collections__Seqs_i_temp = Collections__Seqs_i

///////////////////////////////////
// FUNCTIONS
///////////////////////////////////

function ArrayToObject<T>(a:array<T>) : object
{
    a
}

function {:opaque} ToSeqUint8(s:seq<byte>) : seq<uint8>
    ensures var s' := ToSeqUint8(s);
            |s| == |s'|
         && forall i :: 0 <= i < |s| ==> s[i] as uint8 == s'[i]
{
    if s == [] then []
    else [s[0] as uint8] + ToSeqUint8(s[1..])
}

function {:opaque} ToSeqUint32(s:seq<uint>) : seq<uint32>
    ensures var s' := ToSeqUint32(s);
            |s| == |s'|
         && forall i :: 0 <= i < |s| ==> s[i] as uint32 == s'[i]
{
    if s == [] then []
    else [s[0] as uint32] + ToSeqUint32(s[1..])
}

///////////////////////////////////
// TYPES
///////////////////////////////////

class SHA256Context
{
    ghost var z:SHA256Trace;
    ghost var processed_bytes:seq<uint8>;
    var H:array<uint>;
    var unprocessed_bytes:array<byte>;
    var num_unprocessed_bytes:uint;
    var num_total_bytes:ulong;

    ghost var Repr:set<object>;

    function ToObject() : object
    {
        this
    }

    constructor()
        modifies this;
        ensures  fresh(this.H);
        ensures  fresh(this.unprocessed_bytes);
        ensures  Valid();
    {
        this.processed_bytes := [];
        this.H := new uint[8];
        this.unprocessed_bytes := new byte[64];
        this.num_unprocessed_bytes := 0;
        this.Repr := { ToObject(), ArrayToObject(this.H), ArrayToObject(this.unprocessed_bytes) };
    }

    predicate Valid()
        reads this;
    {
           allocated(this.H)
        && this.H.Length == 8
        && allocated(this.unprocessed_bytes)
        && this.unprocessed_bytes.Length == 64
        && this.num_unprocessed_bytes as int <= 64
        && this.Repr == { ToObject(), ArrayToObject(this.H), ArrayToObject(this.unprocessed_bytes) }
    }

    predicate ExportedInvariant()
        reads this, Repr;
    {
           Valid()
        && this.num_total_bytes as int == |this.processed_bytes| + (this.num_unprocessed_bytes as int)
        && |this.processed_bytes| % 64 == 0
        && this.num_unprocessed_bytes as int < 64
        && this.num_total_bytes as int <= MaxBytesForSHA()
        && IsCompleteSHA256Trace(this.z)
        && SHA256TraceIsCorrect(this.z)
        && WordSeqToBytes(ConcatenateSeqs(this.z.M)) == this.processed_bytes
        && ToSeqUint32(this.H[..]) == last(this.z.H) 
    }

    function BytesIncluded() : seq<uint8>
        requires Valid();
        reads    this, Repr;
    {
        this.processed_bytes + ToSeqUint8(this.unprocessed_bytes[..this.num_unprocessed_bytes])
    }
}

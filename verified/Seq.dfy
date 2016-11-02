//-----------------------------------------------------------------------------
// Sequence Utilities
//-----------------------------------------------------------------------------
module Seq {

function SeqLength<T>(s:seq<T>) : int { |s| }
function SeqDrop<T>(s:seq<T>, tail:int) : seq<T> 
    requires 0 <= tail <= |s|;                                           
    { s[..tail] }
function SeqAppendElt<T>(s:seq<T>, elt:T) : seq<T> { s + [elt] }
function SeqBuild<T>(elt:T) : seq<T> { [elt] }
function {:opaque} SeqRepeat<T>(count:nat, elt:T) : seq<T>
    ensures |SeqRepeat<T>(count, elt)| == count
    //ensures forall e :: e in SeqRepeat<T>(count, elt) ==> e == elt
    ensures forall i :: 0 <= i < count ==> SeqRepeat<T>(count, elt)[i] == elt
{
    if count == 0 then [] else [elt] + SeqRepeat<T>(count - 1, elt)
}

function {:opaque} MapSeqToSeq<T,U>(s:seq<T>, func:T->U) : seq<U>
    reads func.reads;
    requires forall i :: func.reads(i) == {};
    requires forall i :: 0 <= i < |s| ==> func.requires(s[i]);
    ensures |MapSeqToSeq(s, func)| == |s|;
    ensures forall i {:trigger func(s[i])} {:trigger MapSeqToSeq(s,func)[i]} :: 0 <= i < |s| ==> func(s[i]) == MapSeqToSeq(s,func)[i];
{
    if |s| == 0 then []
    else [func(s[0])] + MapSeqToSeq(s[1..], func)
}

function {:opaque} IMapSeqToSeq<T,U>(s:seq<T>, func:imap<T,U>) : seq<U>
    requires forall i :: 0 <= i < |s| ==> s[i] in func;
    ensures |IMapSeqToSeq(s, func)| == |s|;
    ensures forall i {:trigger func[s[i]]} {:trigger IMapSeqToSeq(s,func)[i]} :: 0 <= i < |s| ==> func[s[i]] == IMapSeqToSeq(s,func)[i];
{
    if |s| == 0 then []
    else [func[s[0]]] + IMapSeqToSeq(s[1..], func)
}

function SeqOfNumbersInRightExclusiveRange(a:int, b:int):seq<int>
    requires a <= b;
    ensures |SeqOfNumbersInRightExclusiveRange(a, b)| == b-a;
    ensures forall i | 0 <= i < b-a :: SeqOfNumbersInRightExclusiveRange(a, b)[i] == a + i
    decreases b-a;
{
    if a == b then [] else [a] + SeqOfNumbersInRightExclusiveRange(a+1, b)
}

}

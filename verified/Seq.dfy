//-----------------------------------------------------------------------------
// Sequence Utilities
//-----------------------------------------------------------------------------

function SeqLength<T>(s:seq<T>) : int { |s| }
function SeqDrop<T>(s:seq<T>, tail:int) : seq<T> 
    requires 0 <= tail <= |s|;                                           
    { s[..tail] }
function SeqAppendElt<T>(s:seq<T>, elt:T) : seq<T> { s + [elt] }
function SeqBuild<T>(elt:T) : seq<T> { [elt] }
function SeqRepeat<T>(count:nat, elt:T) : seq<T>
    ensures |SeqRepeat<T>(count, elt)| == count
    ensures forall e :: e in SeqRepeat<T>(count, elt) ==> e == elt
{
    if count == 0 then [] else [elt] + SeqRepeat<T>(count - 1, elt)
}

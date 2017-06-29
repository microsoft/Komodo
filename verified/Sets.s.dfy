// lifted from ironfleet/src/Dafny/Distributed/Common/Collections/Sets.i.dfy

function SetOfNumbersInRightExclusiveRange(a:int, b:int):set<int>
    requires a <= b;
    ensures forall opn :: a <= opn < b ==> opn in SetOfNumbersInRightExclusiveRange(a, b);
    ensures forall opn :: opn in SetOfNumbersInRightExclusiveRange(a, b) ==> a <= opn < b;
    ensures |SetOfNumbersInRightExclusiveRange(a, b)| == b-a;
    decreases b-a;
{
    if a == b then {} else {a} + SetOfNumbersInRightExclusiveRange(a+1, b)
}

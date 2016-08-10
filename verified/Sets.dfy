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

lemma ThingsIKnowAboutSubset<T>(x:set<T>, y:set<T>)
    requires x<y;
    ensures |x|<|y|;
{
    if (x!={}) {
        var e :| e in x;
        ThingsIKnowAboutSubset(x-{e}, y-{e});
    }
}

lemma SubsetCardinality<T>(x:set<T>, y:set<T>)
    ensures x<y ==> |x|<|y|;
    ensures x<=y ==> |x|<=|y|;
{
    if (x<y) {
        ThingsIKnowAboutSubset(x, y);
    }
    if (x==y) { // OBSERVE the other case
    }
}

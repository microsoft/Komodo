// lifted from ironfleet/src/Dafny/Distributed/Common/Collections/Sets.i.dfy

lemma lemma_ThingsIKnowAboutSubset<T>(x:set<T>, y:set<T>)
    requires x<y;
    ensures |x|<|y|;
{
    if (x!={}) {
        var e :| e in x;
        lemma_ThingsIKnowAboutSubset(x-{e}, y-{e});
    }
}

lemma lemma_SubsetCardinality<T>(x:set<T>, y:set<T>)
    ensures x<y ==> |x|<|y|;
    ensures x<=y ==> |x|<=|y|;
{
    if (x<y) {
        lemma_ThingsIKnowAboutSubset(x, y);
    }
    if (x==y) { // OBSERVE the other case
    }
}

lemma lemma_ItIsASingletonSet<T>(foo:set<T>, x:T)
    requires foo=={x};
    ensures |foo|==1;
{
}

lemma lemma_ThingsIKnowAboutASingletonSet<T>(foo:set<T>, x:T, y:T)
    requires |foo| == 1;
    requires x in foo;
    requires y in foo;
    ensures x==y;
    ensures foo == {x};
{
    if (x!=y) {
        assert {x} < foo;
        lemma_ThingsIKnowAboutSubset({x}, foo);
        assert |{x}| < |foo|;
        assert |foo|>1;
        assert false;
    }

    forall z | z in foo
        ensures z == x
    {
        if z != x {
            assert {x} < foo;
            lemma_ThingsIKnowAboutSubset({x}, foo);
            assert |{x}| < |foo|;
            assert |foo|>1;
            assert false;
        }
    }
}

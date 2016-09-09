datatype Maybe<T> = Nothing | Just(v: T)

function method fromJust<T>(x: Maybe<T>): T
    requires x.Just?
{
    x.v
}

// FIXME: this lemma is here only becuase it's unstable
// when proved in the context of ARMdef.dfy
lemma lemma_PageAlignedImpliesWordAligned(addr:int)
    ensures addr % 0x1000 == 0 ==> addr % 4 == 0
{
    if addr % 0x1000 == 0 {
        assert 0x1000 % 4 == 0;
        assert addr % 4 == 0;
    }
}

// FIXME: this stuff is here because it's very unstable elsewhere
module alignment_s {
lemma lemma_PageAlignedImplies1KAligned(addr:int)
    requires addr % 0x1000 == 0
    ensures addr % 0x400 == 0
{
}

lemma lemma_1KAlignedImpliesWordAligned(addr:int)
    requires addr % 0x400 == 0
    ensures addr % 4 == 0
{
    assert addr % 0x400 == 0;
    assert 0x400 % 4 == 0;
    assert addr % 4 == 0;
}

lemma lemma_PageAlignedImpliesWordAligned(addr:int)
    ensures addr % 0x1000 == 0 ==> addr % 4 == 0
{
    if addr % 0x1000 == 0 {
        lemma_PageAlignedImplies1KAligned(addr);
        lemma_1KAlignedImpliesWordAligned(addr);
    }
}
}

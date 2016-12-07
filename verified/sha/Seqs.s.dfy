// REQUIRES-ANY: TEST, COLLECTIONS
// RUN: %DAFNY /compile:0 %s %DARGS

function last<T>(s:seq<T>):T
    requires |s| > 0;
{
    s[|s|-1]
}

function all_but_last<T>(s:seq<T>):seq<T>
    requires |s| > 0;
    ensures  |all_but_last(s)| == |s| - 1;
{
    s[..|s|-1]
}

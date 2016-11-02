module Maybe {
datatype Maybe<T> = Nothing | Just(v: T)

function method fromJust<T>(x: Maybe<T>): T
    requires x.Just?
{
    x.v
}
}

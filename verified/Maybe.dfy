datatype Maybe<T> = Nothing | Just(T)

function method fromJust<T>(x: Maybe<T>): T
    requires x.Just?
{
    match x case Just(v) => v
}

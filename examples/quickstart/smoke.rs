use vstd::prelude::*;

fn main() {}

verus! {
fn smoke(x: u64) -> (y: u64)
    ensures y == x,
{
    x
}
}

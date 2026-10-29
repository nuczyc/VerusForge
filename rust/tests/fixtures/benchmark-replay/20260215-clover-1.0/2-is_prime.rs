
use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::loop_isolation(false)]

spec fn divides(factor: nat, candidate: nat) -> bool {
    candidate % factor == 0
}

spec fn is_prime(candidate: nat) -> bool {
    &&& 1 < candidate
    &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
}

proof fn not_prime_due_to_factor(candidate: nat, factor: nat)
    requires
        1 < factor,
        factor < candidate,
        divides(factor, candidate),
    ensures
        !is_prime(candidate),
{
    assert(!forall|f: nat| 1 < f && f < candidate ==> !divides(f, candidate));
    assert(exists|f: nat| 1 < f && f < candidate && divides(f, candidate));
}

fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut factor: u64 = 2;
    while factor < candidate
        invariant
            1 < candidate,
            factor > 1,
            forall|f: nat| 1 < f < factor ==> !divides(f, candidate as nat),
        decreases(candidate - factor)
    {
        if candidate % factor == 0 {
            proof {
                not_prime_due_to_factor(candidate as nat, factor as nat);
            }
            return false;
        }
        factor = factor + 1;
    }
    proof {
        assert(forall|f: nat| 1 < f < candidate ==> !divides(f, candidate as nat));
    }
    true
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True
vstd::prelude::verus! {
    use vstd::prelude::*;

    fn main() {}

    spec fn divides(factor: nat, candidate: nat) -> bool {
        candidate % factor == 0
    }

    spec fn is_prime(candidate: nat) -> bool {
        &&& 1 < candidate &&& forall | factor: nat | 1 < factor && factor < candidate ==>!divides(factor, candidate)
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
                factor <= candidate,
                2 <= factor,
                forall | f: nat | 1 < f && f < factor as nat ==> !divides(f, candidate as nat),
            decreases
                candidate - factor,
        {
            if candidate % factor == 0 {
                proof {
                    assert(divides(factor as nat, candidate as nat)) by {
                        assert(candidate as nat % factor as nat == 0);
                    }
                }
                return false;
            }
            factor = factor + 1;
        }
        proof {
            assert(is_prime(candidate as nat)) by {
                assert(1 < candidate as nat);
                assert(forall | f: nat | 1 < f && f < candidate as nat ==> !divides(f, candidate as nat));
            }
        }
        true
    }
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True


use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
     
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = s1.choose();
        let s1_without_a = s1.remove(a);

        assert(s1_without_a.len() < s1.len());
        lemma_len_intersect(s1_without_a, s2);

        if s2.contains(a) {
            assert(s1.intersect(s2).len() == s1_without_a.intersect(s2).len() + 1) by {
                lemma_intersect_with_element(s1, s2, a);
            }
        } else {
            assert(s1.intersect(s2).len() == s1_without_a.intersect(s2).len()) by {
                lemma_set_intersect_remove_element(s1, s2, a);
            }
        }
    }
}

proof fn lemma_intersect_with_element<A>(s1: Set<A>, s2: Set<A>, a: A)
    requires
        s1.finite(),
        s2.contains(a),
    ensures
        s1.intersect(s2).len() == s1.remove(a).intersect(s2).len() + 1
{
    assert(s1 === s1.remove(a).insert(a));
    assert(s1.remove(a).intersect(s2) === s1.intersect(s2).remove(a));
    assert(s1.intersect(s2).contains(a));
    assert(s1.intersect(s2).len() == s1.remove(a).intersect(s2).len() + 1);
}

proof fn lemma_set_intersect_remove_element<A>(s1: Set<A>, s2: Set<A>, a: A)
    requires
        s1.finite(),
        !s2.contains(a),
    ensures
        s1.intersect(s2).len() == s1.remove(a).intersect(s2).len()
{
    assert(!s2.contains(a));
    let intersect_with_a = s1.intersect(s2);
    // Removing the element `a` which is not in `s2` does not change the intersection
    assert(intersect_with_a === s1.remove(a).intersect(s2));
    assert(intersect_with_a.len() == s1.remove(a).intersect(s2).len());
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True

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
        let elem = s1.choose();
        let s1_minus_elem = s1.remove(elem);

        lemma_len_intersect(s1_minus_elem, s2);

        if s2.contains(elem) {
            assert(s1_minus_elem.intersect(s2).insert(elem).len() == s1_minus_elem.intersect(s2).len() + 1);
            assert(s1.intersect(s2).len() == s1_minus_elem.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_minus_elem.intersect(s2).len()) by {
                lemma_intersect_preserved(s1_minus_elem, s2, elem);
            }
        }
    }
}

proof fn lemma_intersect_preserved<A>(s1_minus_elem: Set<A>, s2: Set<A>, elem: A)
    requires
        !s2.contains(elem),
    ensures
        s1_minus_elem.intersect(s2) == s1_minus_elem.intersect(s2).remove(elem)
    decreases
        s1_minus_elem.len()
{
    assert(s1_minus_elem.intersect(s2).contains(elem) == false);
    assert(s1_minus_elem.intersect(s2).remove(elem) == s1_minus_elem.intersect(s2));
}

}


// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True
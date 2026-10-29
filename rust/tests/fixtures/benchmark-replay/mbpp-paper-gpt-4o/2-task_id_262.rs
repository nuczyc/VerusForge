
use vstd::prelude::*;
fn main() {}

verus! {

/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
     	lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::subrange(j, k), with k being the loop index. It will help prove the property of range j..k+1 of a Sequence based on the property held for range j..k of a Sequence.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(j, k as int)...,
          ...
    {
       ...
       proof{
       	  lemma_seq_subrange_ascend(s@, j, k+1);
       }
       k = k + 1;
    }

 */

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

proof fn lemma_seq_subrange_push<T>(v: Seq<T>, i: int, j: int, val: T)
    requires
        0 <= i < j < v.len(),
    ensures
        v.subrange(i, j as int).push(val) == v.subrange(i, j + 1)
{
    assert(v.subrange(i, j as int).push(val) =~= v.subrange(i, j + 1));
}

#[verifier::loop_isolation(false)]

fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
{
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l
        invariant
            0 < l < list@.len(),
            list.len() == list.len(),
            part1@ == list@.subrange(0, index as int),
            forall |k: int| 0 <= k < list.len() ==> list[k] == list[k],
        decreases (l - index)
    {
        part1.push(list[index]);
        index += 1;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        invariant
            0 < l < list@.len(),
            list.len() == list.len(),
            part2@ == list@.subrange(l as int, index as int),
            forall |k: int| 0 <= k < list.len() ==> list[k] == list[k],
        decreases (list.len() - index)
    {
        part2.push(list[index]);
        index += 1;
        proof {
            let val = list@[index - 1];
            lemma_seq_subrange_push(list@, l as int, index - 1, val);
            assert(part2@ == list@.subrange(l as int, index as int));
        }
    }
    proof {
        lemma_seq_subrange_all(list@);
    }
    (part1, part2)
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True
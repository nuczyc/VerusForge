
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

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

#[verifier::loop_isolation(false)]

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < (k - 1)
        invariant
            0 <= index <= k - 1,
            0 < k < list@.len(),
            list.len() == list.len(),
            forall |i: int| 0 <= i < list.len() ==> list[i] == list[i],
            new_list@ == list@.subrange(0, index as int),
        decreases k - 1 - index,
    {
        new_list.push(list[index]);
        index += 1;
        // Invoke lemma to establish subrange invariant
        proof {
            lemma_seq_subrange_ascend(list@, 0, (index) as int);
        }
    }
    let mut index = k;
    while index < list.len()
        invariant
            k <= index <= list.len(),
            0 < k < list@.len(),
            list.len() == list.len(),
            forall |i: int| 0 <= i < list.len() ==> list[i] == list[i],
            new_list@ == list@.subrange(0, k - 1 as int).add(list@.subrange(k as int, index as int)),
        decreases list.len() - index,
    {
        new_list.push(list[index]);
        index += 1;
        // Invoke lemma to establish subrange invariant
        proof {
            lemma_seq_subrange_ascend(list@, k as int, (index) as int);
        }
    }
    proof {
        // Use lemma to prove range includes entire list
        lemma_seq_subrange_all(list@);
        assert(
            new_list@ == list@.subrange(0, k - 1 as int).add(list@.subrange(k as int, list.len() as int))
        );
    }
    new_list
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True
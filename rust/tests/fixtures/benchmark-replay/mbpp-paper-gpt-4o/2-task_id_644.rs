
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_reverse_to_k_length_le_list_length(list_len: int, n: int, index: int)
    requires
        0 < n < list_len,
        0 <= index <= n,
    ensures
        index <= list_len
{
    assert(index <= n);
    assert(n < list_len);
    assert(index <= list_len);
}

proof fn lemma_reversed_list_length_le_list_length(reversed_list_len: nat, list_len: nat)
    requires
        reversed_list_len <= list_len as int,
    ensures
        reversed_list_len <= list_len,
{
    assert(reversed_list_len <= list_len);
}

fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    let mut reversed_list = Vec::new();
    let mut index = 0;
    while index < n
        invariant
            0 < n < list@.len(),
            list.len() == list@.len(),
            reversed_list.len() <= list.len(),
            forall |k: int| 0 <= k < list.len() ==> list@[k] == list@[k],
        decreases n - index // Added by AI
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
        proof {
            lemma_reverse_to_k_length_le_list_length(list.len() as int, n as int, index as int);
            assert(reversed_list.len() <= list.len());
        }
    }
    index = n;
    while index < list.len()
        invariant
            0 < n < list@.len(),
            list.len() == list@.len(),
            reversed_list.len() <= list.len(),
            forall |k: int| 0 <= k < list.len() ==> list@[k] == list@[k],
        decreases list.len() - index // Added by AI
    {
        reversed_list.push(list[index]);
        index += 1;
        proof {
            assert(reversed_list.len() as int <= list.len() as int); // Added by AI
            lemma_reversed_list_length_le_list_length(reversed_list.len() as nat, list.len() as nat);
            assert(reversed_list.len() <= list.len());
        }
    }
    reversed_list
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True
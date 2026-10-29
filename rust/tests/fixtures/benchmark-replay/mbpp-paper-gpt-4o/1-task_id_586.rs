use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    let mut index = n;
    while index < list.len()
        invariant
            n <= index <= list.len(),
            list.len() == list@.len(), 
            new_list@ == list@.subrange(n as int, index as int), // Added by AI
        decreases list.len() - index 
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    while index < n
        invariant
            0 <= index <= n,
            list.len() == list@.len(), 
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, index as int)), // Added by AI
        decreases n - index 
    {
        new_list.push(list[index]);
        index += 1;
    }
    proof {
        assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int))); // Added by AI
    }
    new_list
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True
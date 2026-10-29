use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut replaced_list = Vec::new();
    let first_end = first.len() - 1;
    let mut index = 0;

    while index < first_end
        invariant 
            first.len() > 0,
            index <= first_end,
            replaced_list@ == first@.subrange(0, ( index ) as int), // Added by AI
        decreases first_end - index
    {
        replaced_list.push(first[index]);
        index += 1;
    }
    index = 0;
    while index < second.len()
        invariant 
            first.len() > 0,
            index <= second.len(),
            replaced_list@ == first@.subrange(0, ( first_end ) as int).add(second@.subrange(0, ( index ) as int)), // Added by AI
        decreases second.len() - index
    {
        replaced_list.push(second[index]);
        index += 1;
    }

    proof {
        assert(replaced_list@ == first@.subrange(0, first.len() - 1).add(second@)); // Added by AI
    }

    replaced_list
}

} // verus!



// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True
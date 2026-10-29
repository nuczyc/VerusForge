fn slow_max(a: u64, b: u64) -> u64 {
    let mut x = a;
    let mut y = b;
    let mut counter: u64 = 0;
    // Loop: subtract 1 from both x and y until one reaches 0.
    // Invariants: x, y non-negative (trivially true for u64);
    // counter equals amount subtracted from each; amounts subtracted equal.
    while x > 0 && y > 0 {
        x -= 1;
        y -= 1;
        counter = counter.wrapping_add(1);
    }
    // After loop, one of x or y is 0. The original values are recovered as:
    // a = (a_original - counter) + counter, but we know:
    // if x == 0 then a == counter, and b == y + counter.
    // so max(a,b) = counter + max(0, y) = counter + y (since y could be 0 or positive)
    // if y == 0 then b == counter, and a == x + counter, so max = counter + x.
    // In both cases, result = counter + max(x, y)? Let's verify:
    // a = x + counter, b = y + counter. max(a,b) = counter + max(x,y).
    // Since one of x,y is 0, max(x,y) is the other.
    let m = if x > y { x } else { y };
    counter.wrapping_add(m)
}

fn main() {}
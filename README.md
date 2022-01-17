Similar to [rayon](https://docs.rs/rayon/latest/rayon/), `rayoff` equips iterators with additional
functionality for introducing parallelism. However, instead of using a work-stealing stategy to 
ensure threads don't starve for work, `rayoff` uses a simpler map-reduce stategy:

1. Divvy up the iterator into chunks of roughly equal size (see
[here](https://docs.rs/rayoff/latest/rayoff/trait.Divvy.html#implementation-details)
for implementation details).
2. Map each chunk to its own thread.
3. Reduce over the results of each thread's computation.

In almost all cases, [rayon](https://docs.rs/rayon/latest/rayon/) is the superior choice. However,
if your computations won't benefit from work-stealing, then `rayoff` _may_
give you better performance. Disclaimer: `rayoff` requires a nightly
compiler (`rustc 1.60.0` as of this writing) and internally uses unsafe code. Use at your own risk!

## Example
```rust
use rayoff::*;

fn check(candidate: &[u8]) -> bool {
    candidate == b"orange8"
}

let wordlist = ["apple", "orange", "pear", "banana"];
let cracked_password = wordlist.divvy_cpus().find_map_any(|&word| {
    let mut buf = [0u8; 8];
    let len = word.len();
    buf[..len].copy_from_slice(word.as_bytes());
    for i in b'0'..=b'9' {
        buf[len] = i;
        let password = &buf[..len + 1];
        if check(password) {
            return Some(password.to_vec());
        }
    }
    None
});

assert_eq!(cracked_password.unwrap(), b"orange8");
```

## License
`rayoff` is dual-licensed under the MIT and Apache 2.0 licenses (see [LICENSE-MIT](LICENSE-MIT) and [LICENSE-APACHE](LICENSE-APACHE) for details).

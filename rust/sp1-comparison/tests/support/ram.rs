//! Independent expectations for the sparse RAM export fixture.

pub const LIMIT: u64 = 1 << 48;

pub fn word(value: u64) -> Vec<u64> {
    (0..4).map(|limb| (value >> (16 * limb)) & 0xffff).collect()
}

pub fn byte(address: u64) -> u64 {
    match address {
        65536 => 17, // The first source entry wins over the later value 99.
        65543 => 171,
        131071 => 254,
        131072 => 18,
        a if a == LIMIT - 1 => 255,
        _ => 0,
    }
}

pub fn value(address: u64) -> u64 {
    (0..8)
        .map(|offset| byte(address + offset) << (8 * offset))
        .sum()
}

pub fn interval(lower: u64, upper: u64, byte: u64) -> Vec<u64> {
    [word(lower), word(upper), vec![byte]].concat()
}

pub fn intervals() -> Vec<Vec<u64>> {
    [
        (0, 65536, 0),
        (65536, 65537, 17),
        (65537, 65543, 0),
        (65543, 65544, 171),
        (65544, 131071, 0),
        (131071, 131072, 254),
        (131072, 131072, 0),
        (131072, 131073, 18),
        (131073, LIMIT - 1, 0),
        (LIMIT - 1, LIMIT, 255),
        (LIMIT, LIMIT, 0),
    ]
    .into_iter()
    .map(|(a, b, v)| interval(a, b, v))
    .collect()
}

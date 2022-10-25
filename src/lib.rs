//! A small, self-contained SHA256 and HMAC-SHA256 implementation
//! (C) Frank Denis <fdenis [at] fastly [dot] com>, public domain

#![no_std]
#![allow(
    non_snake_case,
    clippy::cast_lossless,
    clippy::eq_op,
    clippy::identity_op,
    clippy::many_single_char_names,
    clippy::unreadable_literal
)]

#[inline(always)]
fn load_be(base: &[u8], offset: usize) -> u32 {
    let addr = &base[offset..];
    (addr[3] as u32) | (addr[2] as u32) << 8 | (addr[1] as u32) << 16 | (addr[0] as u32) << 24
}

#[inline(always)]
fn store_be(base: &mut [u8], offset: usize, x: u32) {
    let addr = &mut base[offset..];
    addr[3] = x as u8;
    addr[2] = (x >> 8) as u8;
    addr[1] = (x >> 16) as u8;
    addr[0] = (x >> 24) as u8;
}

struct W([u32; 16]);

#[derive(Copy, Clone)]
struct State([u32; 8]);

impl W {
    fn new(input: &[u8]) -> Self {
        let mut w = [0u32; 16];
        for (i, e) in w.iter_mut().enumerate() {
            *e = load_be(input, i * 4)
        }
        W(w)
    }

    #[inline(always)]
    fn Ch(x: u32, y: u32, z: u32) -> u32 {
        (x & y) ^ (!x & z)
    }

    #[inline(always)]
    fn Maj(x: u32, y: u32, z: u32) -> u32 {
        (x & y) ^ (x & z) ^ (y & z)
    }

    #[inline(always)]
    fn Sigma0(x: u32) -> u32 {
        x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
    }

    #[inline(always)]
    fn Sigma1(x: u32) -> u32 {
        x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
    }

    #[inline(always)]
    fn sigma0(x: u32) -> u32 {
        x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
    }

    #[inline(always)]
    fn sigma1(x: u32) -> u32 {
        x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
    }

    #[cfg_attr(feature = "opt_size", inline(never))]
    #[cfg_attr(not(feature = "opt_size"), inline(always))]
    fn M(&mut self, a: usize, b: usize, c: usize, d: usize) {
        let w = &mut self.0;
        w[a] = w[a]
            .wrapping_add(Self::sigma1(w[b]))
            .wrapping_add(w[c])
            .wrapping_add(Self::sigma0(w[d]));
    }

    #[inline]
    fn expand(&mut self) {
        self.M(0, (0 + 14) & 15, (0 + 9) & 15, (0 + 1) & 15);
        self.M(1, (1 + 14) & 15, (1 + 9) & 15, (1 + 1) & 15);
        self.M(2, (2 + 14) & 15, (2 + 9) & 15, (2 + 1) & 15);
        self.M(3, (3 + 14) & 15, (3 + 9) & 15, (3 + 1) & 15);
        self.M(4, (4 + 14) & 15, (4 + 9) & 15, (4 + 1) & 15);
        self.M(5, (5 + 14) & 15, (5 + 9) & 15, (5 + 1) & 15);
        self.M(6, (6 + 14) & 15, (6 + 9) & 15, (6 + 1) & 15);
        self.M(7, (7 + 14) & 15, (7 + 9) & 15, (7 + 1) & 15);
        self.M(8, (8 + 14) & 15, (8 + 9) & 15, (8 + 1) & 15);
        self.M(9, (9 + 14) & 15, (9 + 9) & 15, (9 + 1) & 15);
        self.M(10, (10 + 14) & 15, (10 + 9) & 15, (10 + 1) & 15);
        self.M(11, (11 + 14) & 15, (11 + 9) & 15, (11 + 1) & 15);
        self.M(12, (12 + 14) & 15, (12 + 9) & 15, (12 + 1) & 15);
        self.M(13, (13 + 14) & 15, (13 + 9) & 15, (13 + 1) & 15);
        self.M(14, (14 + 14) & 15, (14 + 9) & 15, (14 + 1) & 15);
        self.M(15, (15 + 14) & 15, (15 + 9) & 15, (15 + 1) & 15);
    }

    #[cfg_attr(feature = "opt_size", inline(never))]
    #[cfg_attr(not(feature = "opt_size"), inline(always))]
    fn F(&mut self, state: &mut State, i: usize, k: u32) {
        let t = &mut state.0;
        t[(16 - i + 7) & 7] = t[(16 - i + 7) & 7]
            .wrapping_add(Self::Sigma1(t[(16 - i + 4) & 7]))
            .wrapping_add(Self::Ch(
                t[(16 - i + 4) & 7],
                t[(16 - i + 5) & 7],
                t[(16 - i + 6) & 7],
            ))
            .wrapping_add(k)
            .wrapping_add(self.0[i]);
        t[(16 - i + 3) & 7] = t[(16 - i + 3) & 7].wrapping_add(t[(16 - i + 7) & 7]);
        t[(16 - i + 7) & 7] = t[(16 - i + 7) & 7]
            .wrapping_add(Self::Sigma0(t[(16 - i + 0) & 7]))
            .wrapping_add(Self::Maj(
                t[(16 - i + 0) & 7],
                t[(16 - i + 1) & 7],
                t[(16 - i + 2) & 7],
            ));
    }

    fn G(&mut self, state: &mut State, s: usize) {
        const ROUND_CONSTANTS: [u32; 64] = [
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2,
        ];
        let rc = &ROUND_CONSTANTS[s * 16..];
        self.F(state, 0, rc[0]);
        self.F(state, 1, rc[1]);
        self.F(state, 2, rc[2]);
        self.F(state, 3, rc[3]);
        self.F(state, 4, rc[4]);
        self.F(state, 5, rc[5]);
        self.F(state, 6, rc[6]);
        self.F(state, 7, rc[7]);
        self.F(state, 8, rc[8]);
        self.F(state, 9, rc[9]);
        self.F(state, 10, rc[10]);
        self.F(state, 11, rc[11]);
        self.F(state, 12, rc[12]);
        self.F(state, 13, rc[13]);
        self.F(state, 14, rc[14]);
        self.F(state, 15, rc[15]);
    }
}

impl State {
    fn new() -> Self {
        const IV: [u8; 32] = [
            0x6a, 0x09, 0xe6, 0x67, 0xbb, 0x67, 0xae, 0x85, 0x3c, 0x6e, 0xf3, 0x72, 0xa5, 0x4f,
            0xf5, 0x3a, 0x51, 0x0e, 0x52, 0x7f, 0x9b, 0x05, 0x68, 0x8c, 0x1f, 0x83, 0xd9, 0xab,
            0x5b, 0xe0, 0xcd, 0x19,
        ];
        let mut t = [0u32; 8];
        for (i, e) in t.iter_mut().enumerate() {
            *e = load_be(&IV, i * 4)
        }
        State(t)
    }

    #[inline(always)]
    fn add(&mut self, x: &State) {
        let sx = &mut self.0;
        let ex = &x.0;
        sx[0] = sx[0].wrapping_add(ex[0]);
        sx[1] = sx[1].wrapping_add(ex[1]);
        sx[2] = sx[2].wrapping_add(ex[2]);
        sx[3] = sx[3].wrapping_add(ex[3]);
        sx[4] = sx[4].wrapping_add(ex[4]);
        sx[5] = sx[5].wrapping_add(ex[5]);
        sx[6] = sx[6].wrapping_add(ex[6]);
        sx[7] = sx[7].wrapping_add(ex[7]);
    }

    fn store(&self, out: &mut [u8]) {
        for (i, &e) in self.0.iter().enumerate() {
            store_be(out, i * 4, e);
        }
    }

    fn blocks(&mut self, mut input: &[u8]) -> usize {
        let mut t = *self;
        let mut inlen = input.len();
        while inlen >= 64 {
            let mut w = W::new(input);
            w.G(&mut t, 0);
            w.expand();
            w.G(&mut t, 1);
            w.expand();
            w.G(&mut t, 2);
            w.expand();
            w.G(&mut t, 3);
            t.add(self);
            self.0 = t.0;
            input = &input[64..];
            inlen -= 64;
        }
        inlen
    }
}

#[derive(Copy, Clone)]
pub struct Hash {
    state: State,
    w: [u8; 64],
    r: usize,
    len: usize,
}

impl Hash {
    pub fn new() -> Hash {
        Hash {
            state: State::new(),
            r: 0,
            w: [0u8; 64],
            len: 0,
        }
    }

    fn _update(&mut self, input: impl AsRef<[u8]>) {
        let input = input.as_ref();
        let mut n = input.len();
        self.len += n;
        let av = 64 - self.r;
        let tc = ::core::cmp::min(n, av);
        self.w[self.r..self.r + tc].copy_from_slice(&input[0..tc]);
        self.r += tc;
        n -= tc;
        let pos = tc;
        if self.r == 64 {
            self.state.blocks(&self.w);
            self.r = 0;
        }
        if self.r == 0 && n > 0 {
            let rb = self.state.blocks(&input[pos..]);
            if rb > 0 {
                self.w[..rb].copy_from_slice(&input[pos + n - rb..]);
                self.r = rb;
            }
        }
    }

    /// Absorb content
    pub fn update(&mut self, input: impl AsRef<[u8]>) {
        self._update(input)
    }

    /// Compute SHA256(absorbed content)
    pub fn finalize(mut self) -> [u8; 32] {
        let mut padded = [0u8; 128];
        padded[..self.r].copy_from_slice(&self.w[..self.r]);
        padded[self.r] = 0x80;
        let r = if self.r < 56 { 64 } else { 128 };
        let bits = self.len * 8;
        for i in 0..8 {
            padded[r - 8 + i] = (bits as u64 >> (56 - i * 8)) as u8;
        }
        self.state.blocks(&padded[..r]);
        let mut out = [0u8; 32];
        self.state.store(&mut out);
        out
    }

    /// Compute SHA256(`input`)
    pub fn hash(input: &[u8]) -> [u8; 32] {
        let mut h = Hash::new();
        h.update(input);
        h.finalize()
    }
}

impl Default for Hash {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone)]
pub struct HMAC {
    ih: Hash,
    padded: [u8; 64],
}

impl HMAC {
    /// Compute HMAC-SHA256(`input`, `k`)
    pub fn mac(input: impl AsRef<[u8]>, k: impl AsRef<[u8]>) -> [u8; 32] {
        let input = input.as_ref();
        let k = k.as_ref();
        let mut hk = [0u8; 32];
        let k2 = if k.len() > 64 {
            hk.copy_from_slice(&Hash::hash(k));
            &hk
        } else {
            k
        };
        let mut padded = [0x36; 64];
        for (p, &k) in padded.iter_mut().zip(k2.iter()) {
            *p ^= k;
        }
        let mut ih = Hash::new();
        ih.update(&padded[..]);
        ih.update(input);

        for p in padded.iter_mut() {
            *p ^= 0x6a;
        }
        let mut oh = Hash::new();
        oh.update(&padded[..]);
        oh.update(ih.finalize());
        oh.finalize()
    }

    pub fn new(k: impl AsRef<[u8]>) -> HMAC {
        let k = k.as_ref();
        let mut hk = [0u8; 32];
        let k2 = if k.len() > 64 {
            hk.copy_from_slice(&Hash::hash(k));
            &hk
        } else {
            k
        };
        let mut padded = [0x36; 64];
        for (p, &k) in padded.iter_mut().zip(k2.iter()) {
            *p ^= k;
        }
        let mut ih = Hash::new();
        ih.update(&padded[..]);
        HMAC { ih, padded }
    }

    /// Absorb content
    pub fn update(&mut self, input: impl AsRef<[u8]>) {
        self.ih.update(input);
    }

    /// Compute HMAC-SHA256 over the entire input
    pub fn finalize(mut self) -> [u8; 32] {
        for p in self.padded.iter_mut() {
            *p ^= 0x6a;
        }
        let mut oh = Hash::new();
        oh.update(&self.padded[..]);
        oh.update(self.ih.finalize());
        oh.finalize()
    }
}

pub struct HKDF;

impl HKDF {
    pub fn extract(salt: impl AsRef<[u8]>, ikm: impl AsRef<[u8]>) -> [u8; 32] {
        HMAC::mac(ikm, salt)
    }

    pub fn expand(out: &mut [u8], prk: impl AsRef<[u8]>, info: impl AsRef<[u8]>) {
        let info = info.as_ref();
        let mut counter: u8 = 1;
        assert!(out.len() < 0xff * 32);
        let mut i: usize = 0;
        while i < out.len() {
            let mut hmac = HMAC::new(&prk);
            if i != 0 {
                hmac.update(&out[i - 32..][..32]);
            }
            hmac.update(info);
            hmac.update([counter]);
            let left = core::cmp::min(32, out.len() - i);
            out[i..][..left].copy_from_slice(&hmac.finalize()[..left]);
            counter += 1;
            i += 32;
        }
    }
}

/// Wrapped `Hash` type for the `Digest` trait.
#[cfg(feature = "traits010")]
pub type WrappedHash = digest010::core_api::CoreWrapper<Hash>;

#[cfg(feature = "traits010")]
mod digest_trait010 {
    use core::fmt;

    use digest010::{
        block_buffer::Eager,
        const_oid::{AssociatedOid, ObjectIdentifier},
        consts::{U32, U64},
        core_api::{
            AlgorithmName, Block, BlockSizeUser, Buffer, BufferKindUser, FixedOutputCore,
            OutputSizeUser, Reset, UpdateCore,
        },
        FixedOutput, FixedOutputReset, HashMarker, Output, Update,
    };

    use super::Hash;

    impl AssociatedOid for Hash {
        const OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.16.840.1.101.3.4.2.1");
    }

    impl AlgorithmName for Hash {
        fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("Sha256")
        }
    }

    impl HashMarker for Hash {}

    impl BufferKindUser for Hash {
        type BufferKind = Eager;
    }

    impl BlockSizeUser for Hash {
        type BlockSize = U64;
    }

    impl OutputSizeUser for Hash {
        type OutputSize = U32;
    }

    impl UpdateCore for Hash {
        #[inline]
        fn update_blocks(&mut self, blocks: &[Block<Self>]) {
            for block in blocks {
                self._update(block);
            }
        }
    }

    impl Update for Hash {
        #[inline]
        fn update(&mut self, data: &[u8]) {
            self._update(data);
        }
    }

    impl FixedOutputCore for Hash {
        fn finalize_fixed_core(&mut self, buffer: &mut Buffer<Self>, out: &mut Output<Self>) {
            self._update(buffer.get_data());
            self.finalize_into(out);
        }
    }

    impl FixedOutput for Hash {
        fn finalize_into(self, out: &mut Output<Self>) {
            let h = self.finalize();
            out.copy_from_slice(&h);
        }
    }

    impl Reset for Hash {
        fn reset(&mut self) {
            *self = Self::new()
        }
    }

    impl FixedOutputReset for Hash {
        fn finalize_into_reset(&mut self, out: &mut Output<Self>) {
            self.finalize_into(out);
            self.reset();
        }
    }
}

#[cfg(feature = "traits09")]
mod digest_trait09 {
    use digest09::consts::{U32, U64};
    use digest09::{BlockInput, FixedOutputDirty, Output, Reset, Update};

    use super::Hash;

    impl BlockInput for Hash {
        type BlockSize = U64;
    }

    impl Update for Hash {
        fn update(&mut self, input: impl AsRef<[u8]>) {
            self._update(input)
        }
    }

    impl FixedOutputDirty for Hash {
        type OutputSize = U32;

        fn finalize_into_dirty(&mut self, out: &mut Output<Self>) {
            let h = self.finalize();
            out.copy_from_slice(&h);
        }
    }

    impl Reset for Hash {
        fn reset(&mut self) {
            *self = Self::new()
        }
    }
}

#[test]
fn main() {
    let h = HMAC::mac([], [0u8; 32]);
    assert_eq!(
        &h[..],
        &[
            182, 19, 103, 154, 8, 20, 217, 236, 119, 47, 149, 215, 120, 195, 95, 197, 255, 22, 151,
            196, 147, 113, 86, 83, 198, 199, 18, 20, 66, 146, 197, 173
        ]
    );

    let h = HMAC::mac([42u8; 69], []);
    assert_eq!(
        &h[..],
        &[
            225, 88, 35, 8, 78, 185, 165, 6, 235, 124, 28, 250, 112, 124, 159, 119, 159, 88, 184,
            61, 7, 37, 166, 229, 71, 154, 83, 153, 151, 181, 182, 72
        ]
    );

    let h = HMAC::mac([69u8; 250], [42u8; 50]);
    assert_eq!(
        &h[..],
        &[
            112, 156, 120, 216, 86, 25, 79, 210, 155, 193, 32, 120, 116, 134, 237, 14, 198, 1, 64,
            41, 124, 196, 103, 91, 109, 216, 36, 133, 4, 234, 218, 228
        ]
    );

    let mut s = HMAC::new([42u8; 50]);
    s.update([69u8; 150]);
    s.update([69u8; 100]);
    let h = s.finalize();
    assert_eq!(
        &h[..],
        &[
            112, 156, 120, 216, 86, 25, 79, 210, 155, 193, 32, 120, 116, 134, 237, 14, 198, 1, 64,
            41, 124, 196, 103, 91, 109, 216, 36, 133, 4, 234, 218, 228
        ]
    );

    let ikm = [0x0bu8; 22];
    let salt = [
        0x00u8, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
    ];
    let context = [0xf0u8, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9];
    let prk = HKDF::extract(salt, ikm);
    let mut k = [0u8; 40];
    HKDF::expand(&mut k, prk, context);
    assert_eq!(
        &k[..],
        &[
            60, 178, 95, 37, 250, 172, 213, 122, 144, 67, 79, 100, 208, 54, 47, 42, 45, 45, 10,
            144, 207, 26, 90, 76, 93, 176, 45, 86, 236, 196, 197, 191, 52, 0, 114, 8, 213, 184,
            135, 24
        ]
    );
}

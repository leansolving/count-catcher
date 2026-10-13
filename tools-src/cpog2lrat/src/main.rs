//! Native port of `scripts/cpog2lrat.py`; its docstring describes the translation. Same
//! command line, byte-identical OUT.pog, OUT.cnf and OUT.lrat for every option combination
//! without --trim, the same statistics line on stdout, the same error messages (exit code 1).
//!
//! Usage: cpog2lrat FORMULA.cnf CERT.cpog OUT [--delete] [--binary] [--trim] [--keep] [--inline]
//!
//! The passes mirror the Python script line by line:
//! pass 1 reads the declarations (OUT.pog, new IDs of the defining clauses, C2 and C4),
//! pass 2 writes OUT.cnf and the renumbered additions, pass 3 (--delete) copies the LRAT
//! file and inserts the deletion of every clause after its last use. With --binary the LRAT
//! records are written in binary directly, instead of converting a text file afterwards.
//!
//! --trim (not in the Python script; reference `scripts/lrat_trim.py`) writes only the
//! additions in the backward cone of the final step, numbered by position; OUT.pog and OUT.cnf
//! do not change. Pass 1b, between passes 1 and 2, finds the cone (see `cone`).
//!
//! --keep (implies --trim; reference `scripts/lrat_trim.py --keep`) also writes OUT.keep, the
//! mask of `fwdCnfOfSel` (lean/CountCatcherChecker/FwdSel.lean) over part B's initial clauses: one character
//! per clause of the formula (tautological ones included), per defining clause in declaration
//! order and for the negated root, '1' if a kept step or the final step cites it, else '0'
//! (always '0' for a tautology), no trailing newline. OUT.lrat then numbers the kept initial
//! clauses by position among them, and OUT.cnf holds only the kept clauses, so that OUT.cnf and
//! OUT.lrat stay checkable by an independent LRAT checker (lrat-check).
//!
//! --inline (implies --trim, combines with --keep; reference `scripts/lrat_inline.py` applied to
//! the output of `scripts/lrat_trim.py`) replaces each addition that one kept step cites, within
//! a window of the last 4096 kept additions, by its own hint list where a replay with the
//! checker's hint rule accepts that (see the --inline section comment). The keep mask and the
//! IDs of the initial clauses do not change; deletions are computed on the inlined proof.
//!
//! Clause IDs are positions among the non-tautological clauses, as in the LRAT checker of Lean
//! core (see the Python docstring): tautological input, defining and added clauses are left
//! out of OUT.cnf and OUT.lrat, hints citing them are dropped.
//!
//! Tokens and lines follow Python: `str.split()` whitespace (space, \t, \n, \v, \f, \r,
//! \x1c to \x1f), universal newlines (\n, \r, \r\n end a line), `int()` syntax (sign,
//! digits, single underscores between digits). Differences, on malformed input only:
//! negative clause IDs are rejected (Python would index its arrays from the end), numbers
//! beyond 64 bits and clause IDs of the output beyond 2^32 - 1 are rejected, a CNF without a
//! "p" line is rejected, bytes that are not UTF-8 are not rejected, non-ASCII whitespace
//! (U+0085, U+00A0, ...) does not separate tokens, and OUT.cnf is also refused when it
//! resolves (through symlinks) to the input formula.

use std::fs::{self, File};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Component, Path, PathBuf};

type Res<T> = Result<T, String>;

const RBUF: usize = 1 << 24; // read buffer, grows if one record is longer
const WBUF: usize = 1 << 22; // write buffer flush threshold

// ---------------------------------------------------------------------------------------
// Input: records, tokens, integers with Python's semantics

#[inline]
fn is_ws(b: u8) -> bool {
    b == b' ' || (9..=13).contains(&b) || (0x1c..=0x1f).contains(&b)
}

/// Length of the first line of `s` including its terminator (\n or \r), if complete.
#[inline]
fn line_len(s: &[u8]) -> Option<usize> {
    const W: usize = 32;
    let mut i = 0;
    while i + W <= s.len() {
        let c: &[u8; W] = s[i..i + W].try_into().unwrap();
        if c.iter().fold(false, |a, &b| a | (b == b'\n') | (b == b'\r')) {
            break;
        }
        i += W;
    }
    s[i..].iter().position(|&b| b == b'\n' || b == b'\r').map(|p| i + p + 1)
}

/// Length of the first binary LRAT addition record of `s` ('a', numbers, 0, numbers, 0), if
/// complete. A varint of a nonzero number has no zero byte, so zero bytes are terminators.
#[inline]
fn bin_add_len(s: &[u8]) -> Option<usize> {
    let z1 = 1 + s.get(1..)?.iter().position(|&b| b == 0)?;
    let z2 = z1 + 1 + s[z1 + 1..].iter().position(|&b| b == 0)?;
    Some(z2 + 1)
}

/// Calls `f` on every record of the file, as split by `rec_len` (record including its
/// terminator); a last record without terminator is passed as it is.
fn scan(
    path: &str,
    rec_len: impl Fn(&[u8]) -> Option<usize>,
    mut f: impl FnMut(&[u8]) -> Res<()>,
) -> Res<()> {
    let mut file = File::open(path).map_err(|e| format!("{path}: {e}"))?;
    let mut buf = vec![0u8; RBUF];
    let mut len = 0;
    loop {
        if len == buf.len() {
            buf.resize(2 * buf.len(), 0);
        }
        let n = loop {
            match file.read(&mut buf[len..]) {
                Ok(n) => break n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(format!("{path}: {e}")),
            }
        };
        len += n;
        let mut s = 0;
        while let Some(k) = rec_len(&buf[s..len]) {
            f(&buf[s..s + k])?;
            s += k;
        }
        if n == 0 {
            if s < len {
                f(&buf[s..len])?;
            }
            return Ok(());
        }
        buf.copy_within(s..len, 0);
        len -= s;
    }
}

fn for_each_line(path: &str, f: impl FnMut(&[u8]) -> Res<()>) -> Res<()> {
    scan(path, line_len, f)
}

/// `line.split()` as an iterator.
struct Tok<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Tok<'a> {
    fn new(s: &'a [u8]) -> Self {
        Tok { s, i: 0 }
    }
}

impl<'a> Iterator for Tok<'a> {
    type Item = &'a [u8];
    #[inline]
    fn next(&mut self) -> Option<&'a [u8]> {
        let s = self.s;
        let mut i = self.i;
        while i < s.len() && is_ws(s[i]) {
            i += 1;
        }
        if i == s.len() {
            self.i = i;
            return None;
        }
        let st = i;
        while i < s.len() && !is_ws(s[i]) {
            i += 1;
        }
        self.i = i;
        Some(&s[st..i])
    }
}

fn show(t: &[u8]) -> String {
    String::from_utf8_lossy(t).into_owned()
}

/// Python's `int(token)` for ASCII tokens, limited to 64 bits.
#[inline]
fn int(t: &[u8]) -> Res<i64> {
    let bad = || format!("invalid literal for int() with base 10: '{}'", show(t));
    let (neg, d) = match t.first() {
        Some(b'-') => (true, &t[1..]),
        Some(b'+') => (false, &t[1..]),
        _ => (false, t),
    };
    let mut v: i64 = 0;
    let mut digit = false; // previous character was a digit
    for &b in d {
        if b.is_ascii_digit() {
            v = v
                .checked_mul(10)
                .and_then(|v| v.checked_add((b - b'0') as i64))
                .ok_or_else(|| format!("number beyond 64 bits: '{}'", show(t)))?;
            digit = true;
        } else if b == b'_' && digit {
            digit = false;
        } else {
            return Err(bad());
        }
    }
    if !digit {
        return Err(bad());
    }
    Ok(if neg { -v } else { v })
}

fn missing(what: &str, line: &[u8]) -> String {
    format!("IndexError: {what} missing in line '{}'", show(line).trim_end())
}

/// Python's `nums[a:-1]`.
#[inline]
fn mid(nums: &[i64], a: usize) -> &[i64] {
    if nums.len() > a + 1 {
        &nums[a..nums.len() - 1]
    } else {
        &[]
    }
}

/// A clause containing a literal and its negation (Python `taut`).
fn taut(c: &[i64]) -> bool {
    if c.len() <= 16 {
        return c.iter().enumerate().any(|(i, &x)| c[i + 1..].iter().any(|&y| y == -x));
    }
    let mut v = c.to_vec();
    v.sort_unstable_by_key(|x| x.unsigned_abs());
    v.windows(2).any(|w| w[0] == -w[1])
}

/// ID map value of a tautological clause (no position in the checker).
const ABSENT: u32 = u32::MAX;
/// ID map value of an initial clause that --keep leaves out.
const DROPPED: u32 = u32::MAX - 1;

// ---------------------------------------------------------------------------------------
// ID maps: clause ID -> value, 0 = unset (the Python `ids()` arrays, 4 instead of 8 bytes)

struct IdMap(Vec<u32>);

impl IdMap {
    #[inline]
    fn get(&self, i: i64) -> u32 {
        if i > 0 && (i as u64) < self.0.len() as u64 {
            self.0[i as usize]
        } else {
            0
        }
    }

    #[inline]
    fn put(&mut self, i: i64, v: u64) -> Res<()> {
        if i < 0 {
            return Err(format!("negative clause ID {i}"));
        }
        let v = u32::try_from(v).map_err(|_| format!("clause ID {v} beyond 2^32 - 1"))?;
        let i = i as usize;
        if i >= self.0.len() {
            let n = (i + 1 + (1 << 20)).max(self.0.len() + self.0.len() / 2);
            self.0.resize(n, 0);
        }
        self.0[i] = v;
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------
// --trim: the backward cone of the final step
//
// The final step (the empty clause) cites the root unit and the negated root. An addition is
// kept if the final step depends on it: it is the root unit (the last addition [root], the
// one pass 2 picks), or a kept non-tautological addition cites it (hints of tautological
// additions are not checked, so they do not count). Hints cite earlier steps, so one backward
// pass marks the cone. Pass structure with --trim:
//   pass 1    declarations, as without --trim (also the largest clause ID, max_id)
//   pass 1b   `cone`: the certificate's lines from the last to the first, in blocks of RBUF
//             bytes; sets the bit of the root unit and of every hint of a marked
//             non-tautological addition, by old clause ID. Only additions that are marked (or
//             come after the root unit) are parsed beyond their ID.
//   pass 2    as without --trim, but an unmarked addition is not written and gets no position;
//             the kept ones are numbered by position after the initial clauses (whose IDs do
//             not change). Every addition is still validated, so the errors are those of a run
//             without --trim (pass 1b skips what it cannot parse).
//   pass 3    (--delete) unchanged; the last uses come from the kept steps only.
// Memory beyond a run without --trim: the mark bits, max_id / 8 bytes (from pass 1b to the end
// of pass 2), one bit per initial clause for the statistics, and the read buffer of pass 1b.
// Time: one more read of the certificate.
// --keep needs no further pass. Before pass 2, `new` holds only the initial clauses, so pass 1b
// also resolves each hint of a marked addition: if `new` maps it to an initial clause, that
// clause's bit in `sel` (one bit per initial clause) is set. Then OUT.keep is written from `sel`
// and the positions of the tautologies, and `new` is rewritten in place: a selected initial
// clause gets its rank among the selected ones (a rank table of 4 bytes per 64 clauses), any
// other one DROPPED. Pass 2 writes only the selected clauses to OUT.cnf. If a certificate reuses
// an initial clause's ID for an addition and a kept step cites the initial clause, pass 1b
// cannot tell the two apart: pass 2 then meets a DROPPED hint and stops with an error.

/// Bit set over clause IDs (--trim).
struct Bits(Vec<u64>);

impl Bits {
    fn new(n: u64) -> Bits {
        Bits(vec![0; (n / 64 + 1) as usize])
    }

    #[inline]
    fn get(&self, i: i64) -> bool {
        i >= 0
            && ((i / 64) as u64) < self.0.len() as u64
            && (self.0[i as usize / 64] >> (i % 64)) & 1 == 1
    }

    /// Sets bit `i` (ignored outside the set); true if it was not set before.
    #[inline]
    fn set(&mut self, i: i64) -> bool {
        if i < 0 || ((i / 64) as u64) >= self.0.len() as u64 {
            return false;
        }
        let w = &mut self.0[i as usize / 64];
        let b = 1u64 << (i % 64);
        let new = *w & b == 0;
        *w |= b;
        new
    }

    /// Sets bit `i` (i >= 0), growing the set; true if it was not set before.
    fn set_grow(&mut self, i: i64) -> bool {
        let w = i as usize / 64;
        if w >= self.0.len() {
            let n = (w + 1 + (1 << 14)).max(self.0.len() + self.0.len() / 2);
            self.0.resize(n, 0);
        }
        self.set(i)
    }

    /// Number of set bits before each word (the table of `rank`).
    fn ranks(&self) -> Vec<u32> {
        let mut acc = 0;
        self.0.iter().map(|w| { let r = acc; acc += w.count_ones(); r }).collect()
    }

    /// Number of set bits at 0 ..= i (i within the set).
    #[inline]
    fn rank(&self, ranks: &[u32], i: u64) -> u32 {
        let w = (i / 64) as usize;
        ranks[w] + (self.0[w] & (u64::MAX >> (63 - i % 64))).count_ones()
    }
}

/// Position of the last line terminator (\n or \r) of `s`.
#[inline]
fn last_term(s: &[u8]) -> Option<usize> {
    const W: usize = 32;
    let mut i = s.len();
    while i >= W {
        let c: &[u8; W] = s[i - W..i].try_into().unwrap();
        if c.iter().fold(false, |a, &b| a | (b == b'\n') | (b == b'\r')) {
            break;
        }
        i -= W;
    }
    s[..i].iter().rposition(|&b| b == b'\n' || b == b'\r')
}

/// Calls `f` on every line of the file from the last to the first, without its terminator.
/// Lines as in `for_each_line` (\n, \r, \r\n end a line; \r\n gives an extra empty line).
fn for_each_line_rev(path: &str, mut f: impl FnMut(&[u8]) -> Res<()>) -> Res<()> {
    let err = |e: io::Error| format!("{path}: {e}");
    let mut file = File::open(path).map_err(err)?;
    let mut pos = file.metadata().map_err(err)?.len();
    let mut buf: Vec<u8> = Vec::new();
    let mut carry: Vec<u8> = Vec::new(); // the block after this one up to its first terminator
    loop {
        let n = pos.min(RBUF as u64) as usize;
        pos -= n as u64;
        buf.clear();
        buf.resize(n, 0);
        file.seek(SeekFrom::Start(pos)).map_err(err)?;
        file.read_exact(&mut buf).map_err(err)?;
        buf.extend_from_slice(&carry);
        let mut end = buf.len();
        while let Some(p) = last_term(&buf[..end]) {
            f(&buf[p + 1..end])?;
            end = p;
        }
        if pos == 0 {
            return f(&buf[..end]);
        }
        carry.clear();
        carry.extend_from_slice(&buf[..end]);
    }
}

/// Pass 1b state of --inline, by old clause ID (see the --inline section comment).
struct ConeInline {
    c1: Bits, // cited by a kept step
    c2: Bits, // cited twice or more
    far: Bits,
    scanned: Bits, // additions whose line pass 1b has read
    fifo: std::collections::VecDeque<Vec<i64>>, // hint lists of the last W kept additions
    spare: Vec<Vec<i64>>,
    root_old: Option<i64>,
    max_abs: u64, // largest |literal| of the kept additions
}

impl ConeInline {
    fn new(max_id: i64) -> ConeInline {
        let n = max_id.max(0) as u64 + 1;
        ConeInline {
            c1: Bits::new(n),
            c2: Bits::new(n),
            far: Bits::new(n),
            scanned: Bits::new(n),
            fifo: std::collections::VecDeque::new(),
            spare: Vec::new(),
            root_old: None,
            max_abs: 0,
        }
    }

    /// The kept addition `old` (scanned backward) with literals `lits` and hints `hints`.
    fn kept(&mut self, old: i64, lits: &[i64], hints: &[i64], root_unit: bool) {
        while self.fifo.len() as u64 > INLINE_W {
            let hs = self.fifo.pop_front().unwrap();
            for &h in &hs {
                if !self.scanned.get(h) {
                    self.far.set(h);
                }
            }
            self.spare.push(hs);
        }
        let mut hs = self.spare.pop().unwrap_or_default();
        hs.clear();
        for &h in hints {
            if !self.c1.set(h) {
                self.c2.set(h);
            }
            hs.push(h);
        }
        self.fifo.push_back(hs);
        for &l in lits {
            self.max_abs = self.max_abs.max(l.unsigned_abs());
        }
        if root_unit {
            self.root_old = Some(old);
        }
    }
}

/// Pass 1b (--trim): the marked old clause IDs (bits 0 ..= max_id) and whether the root unit is
/// an addition; with `sel` (--keep), also the initial clauses (by new ID) that the hints of the
/// marked additions cite; with `inl` (--inline), the counts and far bits. See the section
/// comments.
fn cone(
    cpog_path: &str,
    root: i64,
    max_id: i64,
    mut sel: Option<(&IdMap, &mut Bits)>,
    mut inl: Option<&mut ConeInline>,
) -> Res<(Bits, bool)> {
    let mut mark = Bits::new(max_id.max(0) as u64 + 1);
    let mut unit = false; // the root unit has been seen
    let mut nums: Vec<i64> = Vec::new();
    for_each_line_rev(cpog_path, |line| {
        let mut t = Tok::new(line);
        let (Some(t0), Some(kind)) = (t.next(), t.next()) else { return Ok(()) };
        if t0 == b"c" || t0 == b"d" || t0 == b"r" || kind != b"a" {
            return Ok(());
        }
        let Ok(old) = int(t0) else { return Ok(()) };
        let marked = mark.get(old);
        if !marked && unit {
            if let Some(ci) = inl.as_mut() {
                ci.scanned.set(old);
            }
            return Ok(());
        }
        nums.clear();
        for x in t {
            let Ok(x) = int(x) else { return Ok(()) };
            nums.push(x);
        }
        let Some(z) = nums.iter().position(|&x| x == 0) else { return Ok(()) };
        let lits = &nums[..z];
        let root_unit = !unit && lits.len() == 1 && lits[0] == root;
        if root_unit {
            unit = true;
            mark.set(old);
        }
        if (marked || root_unit) && !taut(lits) {
            if let Some(ci) = inl.as_mut() {
                ci.kept(old, lits, mid(&nums, z + 1), root_unit); // before `old` counts as scanned
            }
            for &h in mid(&nums, z + 1) {
                mark.set(h);
                if let Some((new, sel)) = sel.as_mut() {
                    let c = new.get(h);
                    if c != 0 && c != ABSENT {
                        sel.set(c as i64);
                    }
                }
            }
        }
        if let Some(ci) = inl.as_mut() {
            ci.scanned.set(old);
        }
        Ok(())
    })?;
    Ok((mark, unit))
}

// ---------------------------------------------------------------------------------------
// --inline: single-use additions inlined into their consumer
//
// The rule is that of the reference `scripts/lrat_inline.py` (its docstring states it and the
// checker's hint rule it replays): one forward pass over the kept additions in a window of W =
// INLINE_W positions. An addition cited by exactly one kept step (`single`) and at most W
// positions before it is replaced by its own hint list, replayed in the consumer's state with
// Lean core's hint rule (cut after the hint that yields the unit, hints whose unit is already
// true and hints after the conflict dropped); a step whose own hint list does not replay keeps
// it unchanged. A step that loses its only citation is removed if it is still in the window.
// Pass structure with --inline (implies --trim):
//   pass 0    (reading the formula) also keeps the literals of the non-tautological input
//             clauses, by position.
//   pass 1    also keeps the node table: per node its kind and arguments (product: args, sum:
//             x, y) as i32, from which `InitLits::fetch` derives any defining clause; and checks
//             that every clause ID of a declaration or addition is above m and defined once (a
//             bit per ID, growing, freed after pass 1).
//   pass 1b   `cone` also counts, per old clause ID, the citations by kept steps (0, 1, 2 or
//             more: two bit sets), and sets the far bit of every clause cited by a kept step
//             more than W kept additions later: a FIFO holds the hint lists of the last W kept
//             additions scanned; a list leaving it at the kept line being read sets the bit of
//             each hint whose line has not been scanned yet (a bit per ID marks the scanned
//             addition lines), that is, of each clause at least W + 1 kept additions before the
//             citing step; the bit is final once the clause's own line is scanned. It also
//             finds the root unit's ID and the largest literal of the kept additions.
//   pass 2    resolves and validates every addition as before; a kept one enters a ring of W + 1
//             slots by kept position (`Inliner`). Before step p is read, slot p - W - 1 leaves:
//             if alive it is written with the next output ID (hints mapped through the removed
//             bits), and its literals stay in the far store if its far bit is set or it is the
//             root unit. Step p is then replayed: every clause it or a candidate's list cites is
//             an initial clause (input arena or node table), in the ring, or in the far store, or
//             the candidate is skipped (counted not_at_hand). At the end the ring is flushed.
//   pass 3    (--delete) unchanged; the last uses come from the written (inlined) steps.
// The keep mask and the numbering of the initial clauses do not change. If a certificate reuses
// clause IDs, or a literal reaches 2^28, the counts or the assignment array would not be exact or
// bounded: --inline then writes the trimmed proof unchanged (statistics field off=ids or
// off=literals; the reference sees only the renumbered proof and cannot do the same).
// Memory beyond --trim: four bits per old clause ID (counts, far, scanned) from pass 1b to the
// end of pass 2 (scanned until the end of pass 1b); 2.5 bits per kept addition (single, removed
// and the removed counts per word, which map kept positions to output IDs); the input clauses
// (8 bytes per clause and 4 per literal); the node table (8 bytes per node, 4 per argument);
// the ring (W + 1 slots with their literals and hint lists, statistics field fifo_peak in
// integers); the far store (statistics far_cited, far_lits); the assignment array, 4 bytes per
// variable. Time: one replay per kept addition (unit propagation over its hints and over each
// candidate's list), in pass 2.

const INLINE_W: u64 = 4096;
/// --inline needs every literal below this bound (the assignment array has one entry per variable).
const LIT_LIMIT: i64 = 1 << 28;

/// The (r)-th set bit of `b` (1-based), with `rk` = `b.ranks()`.
fn select(b: &Bits, rk: &[u32], r: u32) -> u64 {
    let (mut lo, mut hi) = (0usize, rk.len());
    while hi - lo > 1 {
        let m = (lo + hi) / 2;
        if rk[m] < r {
            lo = m;
        } else {
            hi = m;
        }
    }
    let mut w = b.0[lo];
    for _ in 1..r - rk[lo] {
        w &= w - 1;
    }
    lo as u64 * 64 + w.trailing_zeros() as u64
}

/// Literals of the initial clauses for the replay (--inline), by their ID in OUT.lrat.
struct InitLits<'a> {
    mk: u64,           // non-tautological input clauses, positions 1 ..= mk
    in_off: Vec<u64>,  // input clause at position p: in_lits[in_off[p - 1] .. in_off[p]]
    in_lits: Vec<i32>,
    v: i64,            // node n has the extension variable V + 1 + n
    node_off: Vec<u64>, // node n: arguments arg[node_off[n] .. node_off[n + 1]] (sum: x, y)
    node_p: Vec<bool>, // product node
    arg: Vec<i32>,
    tdef: Vec<u64>,    // indices of the tautological defining clauses (in declaration order)
    neg_root: u64,     // position of [-root]
    root: i64,
    sel: Option<(&'a Bits, &'a [u32])>, // --keep: selected positions and ranks (ID = rank)
}

impl InitLits<'_> {
    fn fetch(&self, id: u32, out: &mut Vec<i32>) {
        out.clear();
        let p = match &self.sel {
            None => id as u64,
            Some((b, rk)) => select(b, rk, id),
        };
        if p <= self.mk {
            let (a, b) = (self.in_off[p as usize - 1] as usize, self.in_off[p as usize] as usize);
            out.extend_from_slice(&self.in_lits[a..b]);
            return;
        }
        if p == self.neg_root {
            out.push(-self.root as i32);
            return;
        }
        // defining clause d (index among all defining clauses, tautologies included)
        let j = p - self.mk - 1;
        let mut t = 0u64;
        let d = loop {
            let d = j + t;
            let t2 = self.tdef.partition_point(|&x| x <= d) as u64;
            if t2 == t {
                break d;
            }
            t = t2;
        };
        // node n has n + 1 + (number of its arguments) clauses, the first at node_off[n] + n
        let (mut lo, mut hi) = (0usize, self.node_off.len() - 1);
        while hi - lo > 1 {
            let m = (lo + hi) / 2;
            if self.node_off[m] + m as u64 <= d {
                lo = m;
            } else {
                hi = m;
            }
        }
        let k = (d - (self.node_off[lo] + lo as u64)) as usize;
        let u = (self.v + 1 + lo as i64) as i32;
        let a = &self.arg[self.node_off[lo] as usize..self.node_off[lo + 1] as usize];
        if self.node_p[lo] {
            if k == 0 {
                out.push(u);
                out.extend(a.iter().map(|&x| -x));
            } else {
                out.extend([-u, a[k - 1]]);
            }
        } else {
            match k {
                0 => out.extend([-u, a[0], a[1]]),
                1 => out.extend([u, -a[0]]),
                _ => out.extend([u, -a[1]]),
            }
        }
    }
}

/// Assignment of the replay: t[var] = 2 * st + 1 if var is true in the current step, 2 * st if
/// false, anything else unassigned.
struct Asg {
    t: Vec<u32>,
    st: u32,
}

impl Asg {
    fn next(&mut self) {
        if self.st >= (u32::MAX >> 1) - 1 {
            self.t.iter_mut().for_each(|x| *x = 0);
            self.st = 0;
        }
        self.st += 1;
    }

    #[inline]
    fn val(&self, l: i32) -> u32 {
        2 * self.st + (l > 0) as u32
    }

    #[inline]
    fn is_true(&self, l: i32) -> bool {
        self.t[l.unsigned_abs() as usize] == self.val(l)
    }

    #[inline]
    fn set(&mut self, l: i32) {
        let v = self.val(l);
        self.t[l.unsigned_abs() as usize] = v;
    }

    #[inline]
    fn clear(&mut self, l: i32) {
        self.t[l.unsigned_abs() as usize] = 0;
    }

    /// Lean core's `reduce`: None if two different literals are not false, else the one that
    /// is not false (0: all false, a conflict).
    #[inline]
    fn reduce(&self, c: &[i32]) -> Option<i32> {
        let mut u = 0;
        for &l in c {
            if self.is_true(-l) {
                continue;
            }
            if u == 0 {
                u = l;
            } else if u != l {
                return None;
            }
        }
        Some(u)
    }
}

#[derive(Default)]
struct Slot {
    alive: bool,
    bad: bool,    // its own hint list did not replay: unchanged, never a candidate
    single: bool, // exactly one kept step cites it
    far: bool,    // a kept step cites it from more than W positions later
    root: bool,
    lits: Vec<i64>,
    hints: Vec<u32>, // IDs: initial clauses as in OUT.lrat, additions by kept position
}

#[derive(Default, Clone)]
struct InlineStats {
    adds_in: u64,
    adds_out: u64,
    hints_in: u64,
    hints_out: u64,
    inlined: u64,
    rejected: u64,
    not_at_hand: u64,
    invalid: u64,
    dead_removed: u64,
    dead_written: u64,
    far_cited: u64,
    far_lits: u64,
    fifo: u64,
    fifo_peak: u64,
}

/// Pass 2 of --inline: the ring of the last W kept additions, the replay, the writing.
struct Inliner {
    w: u64,
    first: u64,               // ID of the first addition (as kept position and in OUT.lrat)
    ring: Vec<Slot>,          // slot of kept position p: ring[p % (w + 1)]
    n: u64,                   // kept additions placed
    out_next: u64,            // next ID in OUT.lrat
    rem: Bits,                // kept positions removed
    blk: Vec<u32>,            // removed kept positions before each word of `rem` (words done)
    single: Bits,             // by kept position
    root_p: Option<u64>,      // kept position of the root unit
    root_out: Option<u64>,
    far: std::collections::HashMap<u32, Vec<i32>>, // far-cited additions and the root unit
    asg: Asg,
    s: InlineStats,
    cl: Vec<i32>,
    g: Vec<u32>,
    newh: Vec<u32>,
    inl: Vec<u32>,
    drops: Vec<u32>,
    kept: Vec<u32>,
    gdrops: Vec<u32>,
    trail: Vec<i32>,
    stack: Vec<u32>,
    mapped: Vec<u32>,
}

impl Inliner {
    fn new(first: u64, n_add: u64, max_lit: i64) -> Inliner {
        let w = INLINE_W;
        Inliner {
            w,
            first,
            ring: (0..=w).map(|_| Slot::default()).collect(),
            n: 0,
            out_next: first,
            rem: Bits::new(n_add),
            blk: vec![0],
            single: Bits::new(n_add),
            root_p: None,
            root_out: None,
            far: std::collections::HashMap::new(),
            asg: Asg { t: vec![0; max_lit as usize + 1], st: 0 },
            s: InlineStats::default(),
            cl: Vec::new(),
            g: Vec::new(),
            newh: Vec::new(),
            inl: Vec::new(),
            drops: Vec::new(),
            kept: Vec::new(),
            gdrops: Vec::new(),
            trail: Vec::new(),
            stack: Vec::new(),
            mapped: Vec::new(),
        }
    }

    #[inline]
    fn slot(&self, p: u64) -> usize {
        (p % (self.w + 1)) as usize
    }

    /// Literals of clause `id` into `out`, if at hand when step p is read.
    fn fetch(&self, id: u32, p: u64, init: &InitLits, out: &mut Vec<i32>) -> bool {
        if (id as u64) < self.first {
            init.fetch(id, out);
            return true;
        }
        let q = id as u64 - self.first;
        if q < p && p - q <= self.w {
            out.clear();
            out.extend(self.ring[self.slot(q)].lits.iter().map(|&l| l as i32));
            return true;
        }
        match self.far.get(&id) {
            Some(v) => {
                out.clear();
                out.extend_from_slice(v);
                true
            }
            None => false,
        }
    }

    #[inline]
    fn at_hand(&self, id: u32, p: u64) -> bool {
        let q = (id as u64).wrapping_sub(self.first);
        (id as u64) < self.first || (q < p && p - q <= self.w) || self.far.contains_key(&id)
    }

    /// ID in OUT.lrat of the kept addition at position q (written or about to be).
    #[inline]
    fn out_id(&self, q: u64) -> u64 {
        let w = (q / 64) as usize;
        let below = self.blk[w] + (self.rem.0[w] & ((1u64 << (q % 64)) - 1)).count_ones();
        self.first + q - below as u64
    }

    /// Slot of kept position q leaves the ring: written if alive.
    fn flush(&mut self, q: u64, o: &mut Out, binary: bool, last: &mut IdMap, delete: bool)
        -> Res<()> {
        let i = self.slot(q);
        let alive = self.ring[i].alive;
        let s = &self.ring[i];
        self.s.fifo -= (s.lits.len() + s.hints.len()) as u64;
        if alive {
            let id = self.out_next;
            self.out_next += 1;
            let mut mapped = std::mem::take(&mut self.mapped);
            mapped.clear();
            for &h in &s.hints {
                let a = h as u64;
                mapped.push(if a < self.first { h } else { self.out_id(a - self.first) as u32 });
            }
            write_add(o, binary, id, &s.lits, &mapped);
            if delete {
                for &c in &mapped {
                    last.put(c as i64, id)?;
                }
            }
            self.s.adds_out += 1;
            self.s.hints_out += mapped.len() as u64;
            self.mapped = mapped;
            let tid = (self.first + q) as u32;
            if s.root {
                self.root_out = Some(id);
            }
            if s.far {
                self.s.far_cited += 1;
                self.s.far_lits += s.lits.len() as u64;
            }
            if s.far || s.root {
                let v: Vec<i32> = s.lits.iter().map(|&l| l as i32).collect();
                self.far.insert(tid, v);
            }
            o.tick()?;
        } else {
            self.rem.set(q as i64);
        }
        if q % 64 == 63 {
            let w = (q / 64) as usize;
            let b = self.blk[w] + self.rem.0[w].count_ones();
            self.blk.push(b);
        }
        Ok(())
    }

    /// The single addition g lost its only citation while step p is read.
    fn dec(&mut self, g: u32, p: u64) {
        self.stack.clear();
        self.stack.push(g);
        while let Some(g) = self.stack.pop() {
            if (g as u64) < self.first {
                continue;
            }
            let q = g as u64 - self.first;
            if !self.single.get(q as i64) || self.root_p == Some(q) {
                continue;
            }
            if p - q > self.w {
                self.s.dead_written += 1;
                continue;
            }
            let i = self.slot(q);
            self.ring[i].alive = false;
            self.s.dead_removed += 1;
            let hs = std::mem::take(&mut self.ring[i].hints);
            self.stack.extend_from_slice(&hs);
            self.ring[i].hints = hs;
        }
    }

    /// Kept addition with literals `lits` and resolved hints `nh` at the next kept position.
    #[allow(clippy::too_many_arguments)]
    fn add(
        &mut self,
        lits: &[i64],
        nh: &[u32],
        single: bool,
        far: bool,
        root: bool,
        init: &InitLits,
        o: &mut Out,
        binary: bool,
        last: &mut IdMap,
        delete: bool,
    ) -> Res<()> {
        let p = self.n;
        self.n += 1;
        if p > self.w {
            self.flush(p - self.w - 1, o, binary, last, delete)?;
        }
        self.s.adds_in += 1;
        self.s.hints_in += nh.len() as u64;
        // replay
        self.asg.next();
        for &l in lits {
            self.asg.set(-(l as i32));
        }
        let mut newh = std::mem::take(&mut self.newh);
        let mut inl = std::mem::take(&mut self.inl);
        let mut drops = std::mem::take(&mut self.drops);
        let (mut cl, mut g) = (std::mem::take(&mut self.cl), std::mem::take(&mut self.g));
        newh.clear();
        inl.clear();
        drops.clear();
        let (mut done, mut ok) = (false, true);
        for &h in nh {
            if done {
                drops.push(h);
                continue;
            }
            if !self.fetch(h, p, init, &mut cl) {
                return Err(format!("internal: --inline: clause {h} not at hand at kept step {p}"));
            }
            let Some(u) = self.asg.reduce(&cl) else {
                ok = false;
                break;
            };
            if u != 0 && self.asg.is_true(u) {
                drops.push(h);
                continue;
            }
            if (h as u64) >= self.first {
                let q = h as u64 - self.first;
                let s = &self.ring[self.slot(q)];
                if p - q <= self.w && s.single && !s.root && !s.bad {
                    g.clear();
                    g.extend_from_slice(&s.hints);
                    if g.iter().all(|&x| self.at_hand(x, p)) {
                        self.kept.clear();
                        self.gdrops.clear();
                        self.trail.clear();
                        let mut stage = 0u8; // 0 run, 1 cut, 2 conflict, 3 non-unit
                        for &x in &g {
                            if stage != 0 {
                                self.gdrops.push(x);
                                continue;
                            }
                            self.fetch(x, p, init, &mut cl);
                            match self.asg.reduce(&cl) {
                                None => {
                                    stage = 3;
                                    break;
                                }
                                Some(0) => {
                                    stage = 2;
                                    self.kept.push(x);
                                }
                                Some(v) if self.asg.is_true(v) => self.gdrops.push(x),
                                Some(v) => {
                                    self.asg.set(v);
                                    self.trail.push(v);
                                    self.kept.push(x);
                                    if v == u {
                                        stage = 1;
                                    }
                                }
                            }
                        }
                        if stage == 1 || stage == 2 {
                            inl.push(h);
                            newh.extend_from_slice(&self.kept);
                            drops.extend_from_slice(&self.gdrops);
                            done = stage == 2;
                            continue;
                        }
                        for &v in &self.trail {
                            self.asg.clear(v);
                        }
                        self.s.rejected += 1;
                    } else {
                        self.s.not_at_hand += 1;
                    }
                }
            }
            newh.push(h);
            if u == 0 {
                done = true;
            } else {
                self.asg.set(u);
            }
        }
        let bad = !ok || !done;
        if bad {
            self.s.invalid += 1;
        } else {
            self.s.inlined += inl.len() as u64;
            for &h in &inl {
                let i = self.slot(h as u64 - self.first);
                self.ring[i].alive = false;
            }
            for &x in &drops {
                self.dec(x, p);
            }
        }
        let i = self.slot(p);
        let s = &mut self.ring[i];
        s.alive = true;
        s.bad = bad;
        s.single = single;
        s.far = far;
        s.root = root;
        s.lits.clear();
        s.lits.extend_from_slice(lits);
        s.hints.clear();
        s.hints.extend_from_slice(if bad { nh } else { &newh });
        self.s.fifo += (s.lits.len() + s.hints.len()) as u64;
        self.s.fifo_peak = self.s.fifo_peak.max(self.s.fifo);
        if single {
            self.single.set(p as i64);
        }
        if root {
            self.root_p = Some(p);
        }
        (self.newh, self.inl, self.drops, self.cl, self.g) = (newh, inl, drops, cl, g);
        Ok(())
    }

    /// Writes the slots still in the ring (end of pass 2).
    fn finish(&mut self, o: &mut Out, binary: bool, last: &mut IdMap, delete: bool) -> Res<()> {
        let lo = self.n.saturating_sub(self.w + 1);
        for q in lo..self.n {
            self.flush(q, o, binary, last, delete)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------
// Output

/// Decimal, as Python's `str(int)`.
#[inline]
fn push_u(buf: &mut Vec<u8>, mut u: u64) {
    let mut tmp = [0u8; 20];
    let mut p = tmp.len();
    loop {
        p -= 1;
        tmp[p] = b'0' + (u % 10) as u8;
        u /= 10;
        if u == 0 {
            break;
        }
    }
    buf.extend_from_slice(&tmp[p..]);
}

#[inline]
fn push_i(buf: &mut Vec<u8>, v: i64) {
    if v < 0 {
        buf.push(b'-');
    }
    push_u(buf, v.unsigned_abs());
}

struct Out {
    f: File,
    buf: Vec<u8>,
    path: String,
}

impl Out {
    fn create(path: &str) -> Res<Out> {
        let f = File::create(path).map_err(|e| format!("{path}: {e}"))?;
        Ok(Out { f, buf: Vec::with_capacity(WBUF + (1 << 16)), path: path.to_string() })
    }

    #[inline]
    fn b(&mut self, x: u8) {
        self.buf.push(x);
    }

    #[inline]
    fn s(&mut self, x: &[u8]) {
        self.buf.extend_from_slice(x);
    }

    #[inline]
    fn i(&mut self, v: i64) {
        push_i(&mut self.buf, v);
    }

    #[inline]
    fn u(&mut self, u: u64) {
        push_u(&mut self.buf, u);
    }

    /// Binary LRAT number: 2|x| + (x < 0) in 7-bit groups, low group first.
    #[inline]
    fn varint(&mut self, x: i64) {
        let mut u: u128 = if x >= 0 { 2 * x as u128 } else { 2 * x.unsigned_abs() as u128 + 1 };
        while u >= 128 {
            self.buf.push((u & 127) as u8 | 128);
            u >>= 7;
        }
        self.buf.push(u as u8);
    }

    #[inline]
    fn tick(&mut self) -> Res<()> {
        if self.buf.len() >= WBUF {
            self.flush()?;
        }
        Ok(())
    }

    fn flush(&mut self) -> Res<()> {
        self.f.write_all(&self.buf).map_err(|e| format!("{}: {e}", self.path))?;
        self.buf.clear();
        Ok(())
    }
}

/// One LRAT addition `id lits 0 hints 0`, text or binary.
#[inline]
fn write_add(o: &mut Out, binary: bool, id: u64, lits: &[i64], hints: &[u32]) {
    if binary {
        o.b(b'a');
        o.varint(id as i64);
        for &l in lits {
            o.varint(l);
        }
        o.b(0);
        for &h in hints {
            o.varint(h as i64);
        }
        o.b(0);
    } else {
        // " ".join([id, *lits, 0, *hints, 0]): single spaces also for empty lists
        o.u(id);
        for &l in lits {
            o.b(b' ');
            o.i(l);
        }
        o.s(b" 0");
        for &h in hints {
            o.b(b' ');
            o.u(h as u64);
        }
        o.s(b" 0\n");
    }
}

// ---------------------------------------------------------------------------------------

/// `os.path.abspath`: absolute and lexically normalized, symlinks not resolved.
fn abspath(p: &str) -> PathBuf {
    let p = Path::new(p);
    let a = if p.is_absolute() {
        p.to_path_buf()
    } else {
        std::env::current_dir().unwrap_or_default().join(p)
    };
    let mut r = PathBuf::new();
    for c in a.components() {
        match c {
            Component::ParentDir => {
                r.pop();
            }
            Component::CurDir => {}
            c => r.push(c.as_os_str()),
        }
    }
    r
}

/// With CPOG2LRAT_TIMING set, prints the wall time of each pass to stderr.
struct Clock(Option<std::time::Instant>);

impl Clock {
    fn lap(&mut self, what: &str) {
        if let Some(t) = self.0 {
            eprintln!("timing {what} {:.2} s", t.elapsed().as_secs_f64());
            self.0 = Some(std::time::Instant::now());
        }
    }
}

fn run() -> Res<String> {
    let mut clock = Clock(std::env::var_os("CPOG2LRAT_TIMING").map(|_| std::time::Instant::now()));
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let delete = argv.iter().any(|a| a == "--delete");
    let binary = argv.iter().any(|a| a == "--binary");
    let mask = argv.iter().any(|a| a == "--keep");
    let inline = argv.iter().any(|a| a == "--inline");
    let trim = mask || inline || argv.iter().any(|a| a == "--trim");
    let args: Vec<&str> = argv
        .iter()
        .map(|s| s.as_str())
        .filter(|a| !matches!(*a, "--delete" | "--binary" | "--trim" | "--keep" | "--inline"))
        .collect();
    if args.len() < 3 {
        return Err("usage: cpog2lrat FORMULA.cnf CERT.cpog OUT [--delete] [--binary] [--trim] \
            [--keep] [--inline] (--keep: OUT.keep, OUT.cnf only the kept clauses; --inline: \
            single-use additions inlined into their consumer, implies --trim)"
            .into());
    }
    let (cnf_path, cpog_path, out) = (args[0], args[1], args[2]);
    let out_cnf = format!("{out}.cnf");
    let same = abspath(&out_cnf) == abspath(cnf_path)
        || matches!((fs::canonicalize(&out_cnf), fs::canonicalize(cnf_path)), (Ok(a), Ok(b)) if a == b);
    if same {
        return Err(format!(
            "OUT.cnf would overwrite the input formula {cnf_path}; choose another OUT"
        ));
    }

    // The formula: V from the p line, m = number of clauses.
    let mut v_opt: Option<i64> = None;
    let mut m: u64 = 0;
    let mut tin: Vec<u64> = Vec::new(); // IDs of the tautological input clauses
    let mut cur: Vec<i64> = Vec::new();
    // --inline: literals of the non-tautological input clauses, largest |literal| of all clauses
    let mut in_off: Vec<u64> = vec![0];
    let mut in_lits: Vec<i32> = Vec::new();
    let mut max_abs: u64 = 0;
    for_each_line(cnf_path, |line| {
        let mut t = Tok::new(line);
        let Some(t0) = t.next() else { return Ok(()) };
        if t0 == b"c" {
            return Ok(());
        }
        if t0 == b"p" {
            t.next();
            v_opt = Some(int(t.next().ok_or_else(|| missing("V", line))?)?);
            return Ok(());
        }
        for x in std::iter::once(t0).chain(t) {
            let x = int(x)?;
            if x == 0 {
                m += 1;
                if taut(&cur) {
                    tin.push(m);
                } else if inline {
                    for &l in &cur {
                        max_abs = max_abs.max(l.unsigned_abs());
                        in_lits.push(l as i32);
                    }
                    in_off.push(in_lits.len() as u64);
                }
                cur.clear();
            } else {
                cur.push(x);
            }
        }
        Ok(())
    })?;
    let v = v_opt.ok_or("no p line in the formula")?;
    let mk = m - tin.len() as u64; // input clauses with a position
    clock.lap("cnf");

    // Pass 1: declarations. New IDs of the defining clauses, POG file, C2 and C4.
    let mut new = IdMap(Vec::new()); // old clause ID -> new ID
    let mut node_of = IdMap(Vec::new()); // defining clause ID -> node index + 1
    let mut decl_cid: Vec<i64> = Vec::new(); // node -> ID of its first defining clause
    let mut root: Option<i64> = None;
    let mut maxvar = v;
    let mut ndefs: u64 = 0;
    let mut nkept: u64 = 0; // defining clauses with a position
    let mut empty_prod: Vec<(i64, u64)> = Vec::new(); // empty product u -> new ID of [u]
    let mut tdef: Vec<u64> = Vec::new(); // positions (m + index) of tautological defining clauses
    let mut cl: Vec<i64> = Vec::new();
    let mut pog: Vec<u8> = Vec::new(); // node lines of OUT.pog
    let mut nums: Vec<i64> = Vec::new();
    let mut max_id: i64 = m as i64; // largest clause ID of the certificate (sizes `new`)
    let mut n_add: u64 = 0; // number of additions (sizes `last`)
    // --inline: node table (see InitLits) and whether the definition IDs increase strictly
    let mut node_off: Vec<u64> = vec![0];
    let mut node_p: Vec<bool> = Vec::new();
    let mut arg: Vec<i32> = Vec::new();
    let mut ids_seen = Bits(Vec::new()); // definition IDs (--inline; grows)
    let mut ids_ok = true; // every definition ID is above m and defined once
    let mut def_id = |i: i64, ok: &mut bool| {
        if i <= m as i64 || !ids_seen.set_grow(i) {
            *ok = false;
        }
    };
    for_each_line(cpog_path, |line| {
        let mut t = Tok::new(line);
        let Some(t0) = t.next() else { return Ok(()) };
        if t0 == b"c" || t0 == b"d" {
            return Ok(());
        }
        if t0 == b"r" {
            root = Some(int(t.next().ok_or_else(|| missing("root literal", line))?)?);
            return Ok(());
        }
        let kind = t.next().ok_or_else(|| missing("step kind", line))?;
        if kind == b"a" {
            // Skipped by the Python pass 1; counted here to size the maps of pass 2.
            let old = int(t0)?;
            max_id = max_id.max(old);
            n_add += 1;
            if inline {
                def_id(old, &mut ids_ok);
            }
            return Ok(());
        }
        let cid = int(t0)?;
        nums.clear();
        for x in t {
            nums.push(int(x)?);
        }
        let node = decl_cid.len() as i64;
        let (is_p, is_s) = (kind == b"p", kind == b"s");
        if !is_p && !is_s {
            return Err(format!("unsupported step kind '{}' in step {cid}", show(kind)));
        }
        let u = *nums.first().ok_or_else(|| missing("extension variable", line))?;
        if u != v + 1 + node {
            return Err(format!("C2: extension variable {u} is not V+1+{node}"));
        }
        let ncls: u64;
        if is_p {
            let args = mid(&nums, 1);
            ncls = args.len() as u64 + 1;
            // "p " + " ".join(args) + " 0"
            pog.extend_from_slice(b"p ");
            for (k, a) in args.iter().enumerate() {
                if k > 0 {
                    pog.push(b' ');
                }
                push_i(&mut pog, *a);
            }
            pog.extend_from_slice(b" 0\n");
        } else {
            if nums.len() < 3 {
                return Err(missing("sum argument", line));
            }
            let (x, y) = (nums[1], nums[2]);
            ncls = 3;
            // f"s {x} {y} " + " ".join(refs) + " 0"
            pog.extend_from_slice(format!("s {x} {y} ").as_bytes());
            for (k, &h) in mid(&nums, 3).iter().enumerate() {
                let nh = node_of.get(h) as usize;
                if nh == 0 {
                    return Err(format!(
                        "C4: exclusion hint {h} of node {u} is not a defining clause"
                    ));
                }
                if k > 0 {
                    pog.push(b' ');
                }
                pog.extend_from_slice(format!("{}:{}", nh - 1, h - decl_cid[nh - 1]).as_bytes());
            }
            pog.extend_from_slice(b" 0\n");
        }
        maxvar = maxvar.max(u);
        if inline {
            for k in 0..ncls as i64 {
                def_id(cid + k, &mut ids_ok);
            }
            let a = if is_p { mid(&nums, 1) } else { &nums[1..3] };
            max_abs = max_abs.max(u.unsigned_abs());
            for &x in a {
                max_abs = max_abs.max(x.unsigned_abs());
                arg.push(x as i32);
            }
            node_off.push(arg.len() as u64);
            node_p.push(is_p);
        }
        for k in 0..ncls {
            // defining clause k: product [u, -args] then [-u, a]; sum [-u, x, y], [u, -x], [u, -y]
            cl.clear();
            if is_p {
                let args = mid(&nums, 1);
                if k == 0 {
                    cl.push(u);
                    cl.extend(args.iter().map(|&a| -a));
                } else {
                    cl.extend([-u, args[k as usize - 1]]);
                }
            } else {
                match k {
                    0 => cl.extend([-u, nums[1], nums[2]]),
                    1 => cl.extend([u, -nums[1]]),
                    _ => cl.extend([u, -nums[2]]),
                }
            }
            if taut(&cl) {
                new.put(cid + k as i64, ABSENT as u64)?;
                tdef.push(m + ndefs + k);
            } else {
                nkept += 1;
                new.put(cid + k as i64, mk + nkept)?;
                if is_p && ncls == 1 {
                    empty_prod.push((u, mk + nkept));
                }
            }
            node_of.put(cid + k as i64, node as u64 + 1)?;
        }
        max_id = max_id.max(cid + ncls as i64 - 1);
        ndefs += ncls;
        decl_cid.push(cid);
        Ok(())
    })?;
    drop(node_of);
    drop(decl_cid);
    #[allow(clippy::drop_non_drop)]
    drop(def_id);
    drop(ids_seen);
    let root = root.ok_or("no root declaration (r line)")?;
    {
        let mut fp = Out::create(&format!("{out}.pog"))?;
        fp.s(format!("V {v}\nr {root}\n").as_bytes());
        fp.flush()?;
        fp.f.write_all(&pog).map_err(|e| format!("{}: {e}", fp.path))?;
    }
    drop(pog);
    clock.lap("pass1");
    let mut k: u64 = 0;
    let mut ti = tin.iter().peekable();
    for i in 1..=m {
        if ti.peek() == Some(&&i) {
            ti.next();
            new.put(i as i64, ABSENT as u64)?;
            k += 1;
        } else {
            new.put(i as i64, i - k)?;
        }
    }
    let mut ndrop = tin.len() as u64 + ndefs - nkept; // tautological clauses left out
    // Exact size: every ID that pass 2 writes is at most max_id (values beyond read as 0).
    new.0.resize(max_id.max(0) as usize + 1, 0);
    new.0.shrink_to_fit();
    let neg_root = mk + nkept + 1; // its ID without --keep
    if neg_root + 1 + n_add >= DROPPED as u64 {
        return Err(format!(
            "{} clauses: beyond the 32-bit ID range of this translator",
            neg_root + 1 + n_add
        ));
    }
    // Pass 1b (--trim): the cone, by old clause ID; with --keep the selected initial clauses.
    let mut sel = Bits::new(if mask { neg_root } else { 0 }); // by new ID
    let mut ci = if inline && ids_ok { Some(ConeInline::new(max_id)) } else { None };
    let (keep, unit) = if trim {
        let s = if mask { Some((&new, &mut sel)) } else { None };
        cone(cpog_path, root, max_id, s, ci.as_mut())?
    } else {
        (Bits(Vec::new()), false)
    };
    if trim {
        clock.lap("pass1b");
    }
    let mut ncited = [0u64; 3]; // initial clauses cited (--trim): input, defining, negated root
    let mut nr = neg_root; // ID of the negated root in OUT.cnf and OUT.lrat
    let mut rk_keep: Vec<u32> = Vec::new(); // --keep: ranks of `sel` (--inline)
    if mask {
        // the final step cites the root unit (if no addition: the defining clause [root]) and ¬r
        if !unit {
            if let Some(&(_, id)) = empty_prod.iter().find(|&&(u, _)| u == root) {
                sel.set(id as i64);
            }
        }
        sel.set(neg_root as i64);
        let rk = sel.ranks();
        let (a, b) = (sel.rank(&rk, mk) as u64, sel.rank(&rk, neg_root - 1) as u64);
        nr = sel.rank(&rk, neg_root) as u64;
        ncited = [a, b - a, nr - b];
        // OUT.keep: positions in order, the tautologies ('0') have no new ID
        let mut fk = Out::create(&format!("{out}.keep"))?;
        let mut tp = tin.iter().map(|&i| i - 1).chain(tdef.iter().copied()).peekable();
        let mut c: u64 = 0; // new ID of the last non-tautological position
        for p in 0..m + ndefs {
            if tp.peek() == Some(&p) {
                tp.next();
                fk.b(b'0');
            } else {
                c += 1;
                fk.b(if sel.get(c as i64) { b'1' } else { b'0' });
            }
            fk.tick()?;
        }
        fk.b(b'1');
        fk.flush()?;
        let rn = |x: u64| if sel.get(x as i64) { sel.rank(&rk, x) } else { DROPPED };
        for x in new.0.iter_mut() {
            if *x != 0 && *x != ABSENT {
                *x = rn(*x as u64);
            }
        }
        for e in empty_prod.iter_mut() {
            e.1 = rn(e.1) as u64;
        }
        if inline {
            rk_keep = rk;
        }
        clock.lap("keep");
    }
    drop(tin);
    // --inline: off if the IDs do not increase strictly or a literal is too large
    let max_abs = max_abs.max(ci.as_ref().map_or(0, |c| c.max_abs)).max(root.unsigned_abs());
    let inline_off = if !inline {
        ""
    } else if !ids_ok {
        "ids"
    } else if max_abs >= LIT_LIMIT as u64 {
        "literals"
    } else {
        ""
    };
    let inline_on = inline && inline_off.is_empty();
    if let Some(c) = ci.as_mut() {
        c.fifo = Default::default();
        c.spare = Vec::new();
        c.scanned = Bits(Vec::new());
    }
    let init = if inline_on {
        Some(InitLits {
            mk,
            in_off: std::mem::take(&mut in_off),
            in_lits: std::mem::take(&mut in_lits),
            v,
            node_off: std::mem::take(&mut node_off),
            node_p: std::mem::take(&mut node_p),
            arg: std::mem::take(&mut arg),
            tdef: tdef.iter().map(|&x| x - m).collect(),
            neg_root,
            root,
            sel: if mask { Some((&sel, &rk_keep[..])) } else { None },
        })
    } else {
        None
    };
    drop((in_off, in_lits, node_off, node_p, arg));
    drop(tdef);
    let first = nr + 1;
    let fin_max = first + n_add; // bound on the ID of the final step (the empty clause)
    let mut ntrim: u64 = 0; // additions left out by --trim
    let mut cited = Bits::new(if trim && !mask { neg_root } else { 0 }); // (--trim, not --keep)
    let mut cite = |c: u64| {
        if cited.set(c as i64) {
            ncited[if c <= mk { 0 } else if c < neg_root { 1 } else { 2 }] += 1;
        }
    };

    // Pass 2: defining clauses into OUT.cnf, additions renumbered into OUT.lrat.
    let ndrop0 = ndrop; // tautological additions are counted from here
    let mut nxt = first;
    let mut root_unit: Option<u64> = None;
    let mut nadds: u64 = 0;
    let mut nhints: u64 = 0; // hints of the kept additions (--inline statistics)
    let mut inliner =
        if inline_on { Some(Inliner::new(first, n_add, max_abs as i64)) } else { None };
    // with --delete: new clause ID -> last step citing it
    let mut last = IdMap(if delete { vec![0u32; fin_max as usize + 1] } else { Vec::new() });
    let lrat_path = format!("{out}.lrat");
    let tmp_path = format!("{out}.lrat.tmp");
    let mut fl = Out::create(if delete { &tmp_path } else { &lrat_path })?;
    let mut fc = Out::create(&out_cnf)?;
    fc.s(format!("p cnf {maxvar} {nr}\n").as_bytes());
    cur.clear();
    let mut iv: u64 = 0; // new ID of the last non-tautological input clause
    for_each_line(cnf_path, |line| {
        let mut t = Tok::new(line);
        let Some(t0) = t.next() else { return Ok(()) };
        if t0 == b"c" || t0 == b"p" {
            return Ok(());
        }
        for x in std::iter::once(t0).chain(t) {
            let x = int(x)?;
            if x == 0 {
                // " ".join(map(str, cur + [0])), tautologies left out (--keep: unselected too)
                if !taut(&cur) && { iv += 1; !mask || sel.get(iv as i64) } {
                    for &l in &cur {
                        fc.i(l);
                        fc.b(b' ');
                    }
                    fc.s(b"0\n");
                }
                cur.clear();
            } else {
                cur.push(x);
            }
        }
        fc.tick()
    })?;
    let mut nh: Vec<u32> = Vec::new();
    let mut dv: u64 = mk; // new ID of the last non-tautological defining clause
    for_each_line(cpog_path, |line| {
        let mut t = Tok::new(line);
        let Some(t0) = t.next() else { return Ok(()) };
        if t0 == b"c" || t0 == b"d" || t0 == b"r" {
            return Ok(());
        }
        let kind = t.next().ok_or_else(|| missing("step kind", line))?;
        let is_p = kind == b"p";
        let is_s = kind == b"s";
        let old = if is_p || is_s { 0 } else { int(t0)? };
        nums.clear();
        for x in t {
            nums.push(int(x)?);
        }
        if is_p {
            // [[u] + [-a for a in args]] + [[-u, a] for a in args]
            let u = *nums.first().ok_or_else(|| missing("extension variable", line))?;
            let args = mid(&nums, 1);
            cl.clear();
            cl.push(u);
            cl.extend(args.iter().map(|&a| -a));
            // `{ dv += 1; .. }`: next defining clause, written unless --keep leaves it out
            if !taut(&cl) && { dv += 1; !mask || sel.get(dv as i64) } {
                fc.i(u);
                for &a in args {
                    fc.b(b' ');
                    fc.i(-a);
                }
                fc.s(b" 0\n");
            }
            for &a in args {
                if a == u {
                    continue; // [-u, u] is a tautology
                }
                dv += 1;
                if mask && !sel.get(dv as i64) {
                    continue;
                }
                fc.i(-u);
                fc.b(b' ');
                fc.i(a);
                fc.s(b" 0\n");
            }
            return fc.tick();
        }
        if is_s {
            // [[-u, x, y], [u, -x], [u, -y]]
            if nums.len() < 3 {
                return Err(missing("sum argument", line));
            }
            let (u, x, y) = (nums[0], nums[1], nums[2]);
            if !taut(&[-u, x, y]) && { dv += 1; !mask || sel.get(dv as i64) } {
                fc.i(-u);
                fc.b(b' ');
                fc.i(x);
                fc.b(b' ');
                fc.i(y);
                fc.s(b" 0\n");
            }
            if x != u && { dv += 1; !mask || sel.get(dv as i64) } {
                fc.i(u);
                fc.b(b' ');
                fc.i(-x);
                fc.s(b" 0\n");
            }
            if y != u && { dv += 1; !mask || sel.get(dv as i64) } {
                fc.i(u);
                fc.b(b' ');
                fc.i(-y);
                fc.s(b" 0\n");
            }
            return fc.tick();
        }
        let z = nums.iter().position(|&x| x == 0).ok_or("ValueError: 0 is not in list")?;
        let (lits, hints) = (&nums[..z], mid(&nums, z + 1));
        nh.clear();
        nh.extend(hints.iter().map(|&h| new.get(h)));
        if nh.contains(&0) {
            let unknown: Vec<i64> =
                hints.iter().zip(&nh).filter(|(_, &v)| v == 0).map(|(&h, _)| h).collect();
            return Err(format!(
                "step {old}: hint(s) {unknown:?} cite no earlier input, defining or added clause"
            ));
        }
        if taut(lits) {
            // skipped by the checker: no position
            new.put(old, ABSENT as u64)?;
            ndrop += 1;
            return Ok(());
        }
        if trim && !keep.get(old) {
            // outside the cone: no kept step cites it, no position
            new.put(old, ABSENT as u64)?;
            ntrim += 1;
            return Ok(());
        }
        if mask && nh.contains(&DROPPED) {
            return Err(format!(
                "step {old}: --keep: a hint cites an initial clause that pass 1b did not select \
                 (an addition reuses its clause ID)"
            ));
        }
        nh.retain(|&h| h != ABSENT);
        new.put(old, nxt)?;
        if trim && !mask {
            for &c in &nh {
                if (c as u64) < first {
                    cite(c as u64);
                }
            }
        }
        nhints += nh.len() as u64;
        if let (Some(il), Some(c), Some(init)) = (inliner.as_mut(), ci.as_ref(), init.as_ref()) {
            // --inline: the step enters the ring, IDs in OUT.lrat are given when it leaves
            let single = c.c1.get(old) && !c.c2.get(old);
            let root_step = c.root_old == Some(old);
            let far = c.far.get(old);
            il.add(lits, &nh, single, far, root_step, init, &mut fl, binary, &mut last, delete)?;
        } else {
            if delete {
                for &c in &nh {
                    last.put(c as i64, nxt)?;
                }
            }
            write_add(&mut fl, binary, nxt, lits, &nh);
            if lits.len() == 1 && lits[0] == root {
                root_unit = Some(nxt);
            }
        }
        nxt += 1;
        nadds += 1;
        fl.tick()
    })?;
    drop(new);
    fc.s(format!("{} 0\n", -root).as_bytes());
    fc.flush()?;
    drop(fc);
    let mut fin = nxt; // ID of the final step (the empty clause)
    if let Some(il) = inliner.as_mut() {
        il.finish(&mut fl, binary, &mut last, delete)?;
        root_unit = il.root_out;
        fin = il.out_next;
    }
    // constant true (valid formula): cpog-gen uses the defining clause [u] as the root unit
    // and derives no addition for it
    let root_unit = root_unit
        .or_else(|| empty_prod.iter().find(|&&(u, _)| u == root).map(|&(_, id)| id))
        .ok_or("no root unit clause among the additions")?;
    if nadds + ntrim + (ndrop - ndrop0) != n_add {
        return Err(format!("internal: {} additions in pass 2, {n_add} in pass 1", nadds + ntrim));
    }
    drop(keep);
    if trim && !mask {
        if root_unit < first {
            cite(root_unit);
        }
        cite(neg_root);
    }
    if binary {
        write_add(&mut fl, true, fin, &[], &[root_unit as u32, nr as u32]);
    } else {
        // f"{nxt} 0 {root_unit} {neg_root} 0\n" (one space, unlike the join pattern)
        fl.s(format!("{fin} 0 {root_unit} {nr} 0\n").as_bytes());
    }
    fl.flush()?;
    drop(fl);
    clock.lap("pass2");

    let mut ndel: u64 = 0;
    if delete {
        ndel = add_deletions(&tmp_path, &lrat_path, binary, last, first, fin, root_unit, nr)?;
        clock.lap("pass3");
    }
    // additions: all non-tautological ones of the certificate, also with --trim
    let mut stats = format!(
        "vars={maxvar} clauses={neg_root} (input {m}, defs {ndefs}) additions={}",
        nadds + ntrim
    );
    if delete {
        stats += &format!(" deleted={ndel}");
    }
    if ndrop > 0 {
        stats += &format!(" taut_dropped={ndrop}");
    }
    if trim {
        // on stderr (stdout stays as without --trim); totals: the clauses with a position
        eprintln!(
            "trim additions_kept={nadds} additions_total={} cited_input={} input_clauses={mk} \
             cited_defs={} def_clauses={nkept} cited_neg_root={}",
            nadds + ntrim,
            ncited[0],
            ncited[1],
            ncited[2]
        );
        if mask {
            eprintln!("keep keep_ones={nr} keep_len={}", m + ndefs + 1);
        }
        if inline {
            // the reference's statistics line (scripts/lrat_inline.py), then fifo_peak (and off)
            let s = match inliner.as_ref() {
                Some(il) => il.s.clone(),
                None => InlineStats {
                    adds_in: nadds,
                    adds_out: nadds,
                    hints_in: nhints,
                    hints_out: nhints,
                    ..Default::default()
                },
            };
            eprintln!(
                "inline window={INLINE_W} additions_in={} additions_out={} hints_in={} \
                 hints_out={} inlined={} rejected={} not_at_hand={} invalid={} dead_removed={} \
                 dead_written={} far_cited={} far_lits={} fifo_peak={}{}{}",
                s.adds_in,
                s.adds_out,
                s.hints_in,
                s.hints_out,
                s.inlined,
                s.rejected,
                s.not_at_hand,
                s.invalid,
                s.dead_removed,
                s.dead_written,
                s.far_cited,
                s.far_lits,
                s.fifo_peak,
                if inline_off.is_empty() { "" } else { " off=" },
                inline_off
            );
        }
    }
    Ok(stats)
}

/// Pass 3 (--delete): copy TMP to LRAT, deleting every clause after the last step that cites
/// it (a clause never cited: after its own step, or after the first step for input and
/// defining clauses). The root unit and the negated root stay until the final step.
#[allow(clippy::too_many_arguments)]
fn add_deletions(
    tmp: &str,
    dst: &str,
    binary: bool,
    mut last: IdMap,
    first: u64,
    fin: u64,
    root_unit: u64,
    neg_root: u64,
) -> Res<u64> {
    last.put(root_unit as i64, fin)?;
    last.put(neg_root as i64, fin)?;
    let n = (fin - first) as usize; // steps first .. fin-1 can be followed by deletions
    let step = |c: u64| -> u64 {
        let s = last.get(c as i64) as u64;
        if s != 0 {
            s
        } else {
            c.max(first)
        }
    };
    // Counting sort of the clauses 1 .. fin-1 by deletion step, increasing within a step.
    let mut start = vec![0u32; n + 1];
    for c in 1..fin {
        let d = step(c);
        if d < fin {
            start[(d - first) as usize] += 1;
        }
    }
    let mut acc: u64 = 0;
    for s in start.iter_mut() {
        let x = *s as u64;
        *s = acc as u32;
        acc += x;
    }
    let mut order = vec![0u32; acc as usize];
    let mut fill = start.clone();
    for c in 1..fin {
        let d = step(c);
        if d < fin {
            let f = &mut fill[(d - first) as usize];
            order[*f as usize] = c as u32;
            *f += 1;
        }
    }
    drop(fill);
    drop(last);
    let mut fo = Out::create(dst)?;
    let rec_len: fn(&[u8]) -> Option<usize> = if binary { bin_add_len } else { line_len };
    scan(tmp, rec_len, |rec| {
        fo.s(rec);
        // t = int(line.split(maxsplit=1)[0]), the step ID
        let t = if binary {
            let mut u: u64 = 0;
            for (k, &b) in rec[1..].iter().enumerate() {
                u |= ((b & 127) as u64) << (7 * k);
                if b < 128 {
                    break;
                }
            }
            u >> 1
        } else {
            int(Tok::new(rec).next().ok_or("empty line in the LRAT file")?)? as u64
        };
        if t < fin {
            let i = (t - first) as usize;
            let (a, b) = (start[i] as usize, start[i + 1] as usize);
            if b > a {
                // f"{t} d {' '.join(order[a:b])} 0\n"
                if binary {
                    fo.b(b'd');
                    for &c in &order[a..b] {
                        fo.varint(c as i64);
                    }
                    fo.b(0);
                } else {
                    fo.u(t);
                    fo.s(b" d ");
                    for (k, &c) in order[a..b].iter().enumerate() {
                        if k > 0 {
                            fo.b(b' ');
                        }
                        fo.u(c as u64);
                    }
                    fo.s(b" 0\n");
                }
            }
        }
        fo.tick()
    })?;
    fo.flush()?;
    fs::remove_file(tmp).map_err(|e| format!("{tmp}: {e}"))?;
    Ok(acc)
}

fn main() {
    match run() {
        Ok(stats) => println!("{stats}"),
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    }
}

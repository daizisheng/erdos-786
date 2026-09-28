// Erdős #786 step 1, implementation B (independent of fN_cpsat.py).
// f(N) = max |A|, A ⊆ [1,N], with no identity a1..ar = b1..bs of DISTINCT elements of A, r != s.
// Method: f(N) ∈ {f(N-1), f(N-1)+1}; decide existence of a P-set of size f(N-1)+1 by DFS over
// x = 2..N in increasing order (include / exclude), checking each inclusion by an exact DP:
// does some c ∈ {-1,0,1}^(A∪{x}) with c_x = 1 give Σ c v = 0, Σ c ≠ 0?
// DP processes elements grouped by largest prime factor, descending; after the group of prime p
// every element divisible by p has been seen, so e_p must be 0 and the coordinate is dropped.
use std::collections::HashSet;
use std::env;

fn factor(mut n: u32) -> Vec<(u32, i32)> {
    let mut f = vec![]; let mut p = 2;
    while p * p <= n { if n % p == 0 { let mut e = 0; while n % p == 0 { n /= p; e += 1; } f.push((p, e)); } p += 1; }
    if n > 1 { f.push((n, 1)); }
    f
}

struct Ctx { n: u32, pidx: Vec<usize>, vecs: Vec<Vec<(usize, i32)>>, lpf: Vec<u32>, np: usize }

type St = [i8; 24]; // coords 0..np-1 exponents, coord 23 = d

// true iff adding x to set `a` (which already satisfies P) creates a violation
fn violates(ctx: &Ctx, a: &[u32], x: u32) -> bool {
    let mut elems: Vec<u32> = a.to_vec();
    elems.sort_by(|u, v| ctx.lpf[*v as usize].cmp(&ctx.lpf[*u as usize]));
    // remaining capacity per prime, for pruning
    let mut cap = vec![0i32; ctx.np];
    for &e in &elems { for &(i, k) in &ctx.vecs[e as usize] { cap[i] += k; } }
    let mut s0: St = [0; 24];
    for &(i, k) in &ctx.vecs[x as usize] { s0[i] = k as i8; }
    s0[23] = 1;
    // primes of x must be coverable
    for &(i, k) in &ctx.vecs[x as usize] { if k > cap[i] { return false; } }
    let mut cur: HashSet<St> = HashSet::new(); cur.insert(s0);
    let mut idx = 0;
    while idx < elems.len() {
        let p = ctx.lpf[elems[idx] as usize];
        let mut j = idx; while j < elems.len() && ctx.lpf[elems[j] as usize] == p { j += 1; }
        for &e in &elems[idx..j] {
            for &(i, k) in &ctx.vecs[e as usize] { cap[i] -= k; }
            let mut nxt: HashSet<St> = HashSet::with_capacity(cur.len() * 3);
            for s in cur.iter() {
                for c in [-1i32, 0, 1] {
                    let mut t = *s;
                    let mut ok = true;
                    for &(i, k) in &ctx.vecs[e as usize] {
                        let v = t[i] as i32 + c * k;
                        if v.abs() > cap[i] { ok = false; break; }
                        t[i] = v as i8;
                    }
                    if !ok { continue; }
                    t[23] = (t[23] as i32 + c) as i8;
                    nxt.insert(t);
                }
            }
            cur = nxt;
        }
        // close prime p: its exponent must now be zero (cap is 0 so pruning already forced it)
        let pi = ctx.pidx[p as usize];
        cur.retain(|s| s[pi] == 0);
        idx = j;
    }
    // any state with all exponents zero and d != 0
    cur.iter().any(|s| s[..ctx.np].iter().all(|&v| v == 0) && s[23] != 0)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let n1: u32 = args[1].parse().unwrap();
    let mut f_prev = 0usize; // f(1) = 0 (1 is never allowed)
    for n in 2..=n1 {
        // primes that can occur in a relation: p <= n/2 (a prime > n/2 divides only one element)
        let mut pidx = vec![usize::MAX; (n + 1) as usize];
        let mut np = 0;
        for p in 2..=n { if factor(p).len() == 1 && factor(p)[0].1 == 1 && 2 * p <= n { pidx[p as usize] = np; np += 1; } }
        assert!(np <= 23);
        let mut vecs = vec![vec![]; (n + 1) as usize];
        let mut lpf = vec![0u32; (n + 1) as usize];
        for m in 1..=n {
            let f = factor(m);
            lpf[m as usize] = f.iter().map(|q| q.0).max().unwrap_or(1);
            vecs[m as usize] = f.iter().filter(|q| pidx[q.0 as usize] != usize::MAX).map(|q| (pidx[q.0 as usize], q.1)).collect();
        }
        // an element with a prime factor p > n/2 can never be in a relation: treat as free (always included).
        // implemented implicitly: its vector drops p, but then m = p*k with k<2 => m = p, vector empty,
        // and an empty-vector element would falsely look like "1". So handle explicitly:
        let ctx = Ctx { n, pidx, vecs, lpf, np };
        let free: Vec<u32> = (2..=n).filter(|&m| factor(m).iter().any(|q| 2 * q.0 > n)).collect();
        let target_total = f_prev + 1;
        let target = target_total.saturating_sub(free.len());
        // search over non-free elements only
        let rest: Vec<u32> = (2..=n).filter(|m| !free.contains(m)).collect();
        let mut s = Search2 { ctx: &ctx, rest: &rest, target, found: None, nodes: 0 };
        let mut a = vec![];
        s.dfs(0, &mut a);
        let f = if let Some(ref a) = s.found { let _ = a; target_total } else { f_prev };
        let witness: Vec<u32> = match &s.found { Some(a) => { let mut w = a.clone(); w.extend(&free); w.sort(); w } None => vec![] };
        println!("{{\"N\":{},\"f\":{},\"D\":{},\"nodes\":{},\"witness_if_increase\":{:?}}}", n, f, n as usize - f, s.nodes, witness);
        f_prev = f;
    }
}

struct Search2<'a> { ctx: &'a Ctx, rest: &'a [u32], target: usize, found: Option<Vec<u32>>, nodes: u64 }
impl<'a> Search2<'a> {
    fn dfs(&mut self, i: usize, a: &mut Vec<u32>) {
        if self.found.is_some() { return; }
        self.nodes += 1;
        if a.len() >= self.target { self.found = Some(a.clone()); return; }
        if i >= self.rest.len() || a.len() + (self.rest.len() - i) < self.target { return; }
        let x = self.rest[i];
        if !violates(self.ctx, a, x) {
            a.push(x); self.dfs(i + 1, a); a.pop();
            if self.found.is_some() { return; }
        }
        self.dfs(i + 1, a);
    }
}

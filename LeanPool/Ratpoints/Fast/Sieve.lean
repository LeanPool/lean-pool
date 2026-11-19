/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Model.BruteForce
public import LeanPool.Ratpoints.Model.Candidate
public import LeanPool.Ratpoints.Model.Setup
public import LeanPool.Ratpoints.Model.Sturm

/-!
# A fast search for the points

`Ratpoints.Fast.fastPoints c H bLow bHigh` lists the normalized points of height at most `H` on
`y ^ 2 = F(x, z)` whose denominator `z` lies in the range of `bLow` and `bHigh` (the points at
infinity always), each once, in an order of its own: only such points in any case, and all of them
assuming Sturm's theorem, on which the region of the numerators rests. It is not a model of the C
code: it sieves in the way that suits Lean, with bit masks held in natural numbers, which Lean
represents by GMP integers, so that one `&&&` ANDs thousands of candidates without an allocation
per word. The program `ratpoints-lean` runs `Ratpoints.FastMask.fastPoints`, the same sieve with
the masks held in byte arrays, which lists the same points in another order.

* Without a range of the denominators (`bLow ≤ 1`, and `bHigh < 1` or `H ≤ bHigh`) the coefficients
  are reversed where the reversal check of `ratpoints` reverses them (`Ratpoints.Fast.reversed`, on
  `Ratpoints.Setup.reversal`: the binary form with `x` and `z` exchanged); the search
  `Ratpoints.Fast.sievePoints` then runs on them over the whole box, and its points are mapped back
  by `Ratpoints.Sieve.swapPoint`.
* The numerators `x = -H, …, H` are split into the classes of `x + H` modulo `G = 2 ^ e`; a class
  is searched for the denominator `b` only when the residues of `x` and `b` modulo `G` allow a
  point (`Ratpoints.Fast.admitTable`).
* Each class is searched in chunks of at most `L` numerators `a₀, a₀ + G, a₀ + 2G, …`. A chunk is a
  bit mask with one bit per numerator, ANDed with the rows of the families of moduli
  (`Ratpoints.Fast.Family`): the row of the family of the moduli `m₁, …, mₖ` for `b` has the bit of
  `x` set when for every `mᵢ` the residues of `x` and `b` allow a point. The rows of a family
  depend on `b` modulo `M = m₁ ⋯ mₖ` only, and on `x` modulo `M`: they are made once, for the
  numerators `0, G, 2G, …`, and shifted to the start of a chunk, by a multiple of `8` when `M` is
  odd (`Ratpoints.Fast.Family.shift`).
* The denominators are the outer loop: for each `b`, every chunk of every class that `b` allows is
  searched in turn, with the same rows, which the search on byte arrays then finds in the cache.
* The bits that survive go to the exact check of the brute force,
  `Ratpoints.BruteForce.pointsOfDen`.
* For odd degree only the denominators `s k ^ 2` with `s` dividing the leading coefficient can
  carry a point, and only they are searched; for even degree no multiple of an odd `p` with
  `(c_d / p) = -1` can (`Ratpoints.Fast.forbiddenDens`).
* The numerators of a denominator `b` are those `a` with `a / b` in the intervals that the Sturm
  step of `ratpoints` keeps (`Ratpoints.Fast.region`), outside of which `F(a, b) < 0` assuming
  Sturm's theorem: each chunk is cut to the 64-bit words that hold the numerators from the first
  to the last of them (`Ratpoints.Fast.bounds`, `Ratpoints.Fast.part`).

The choice of `G`, `L` and the families affects the speed only: the proofs hold for every choice.

## Main definitions

* `Ratpoints.Fast.fastPoints`: the points, by the sieve.
* `Ratpoints.Fast.sievePoints`: the search without the reversal.
-/

@[expose] public section

namespace Ratpoints

namespace Fast

open BruteForce

/-! ### Residues that allow a point -/

/-- The squares modulo `m`: entry `v` is `true` when `v = y * y % m` for some `y < m` (each
`y * y % m` marked in turn). -/
def sqTable (m : Nat) : Array Bool :=
  (List.range m).foldl (fun A y ↦ A.set! (y * y % m) true) (Array.replicate m false)

/-- Horner's rule modulo `m`: the value `w₀ + x (w₁ + x (w₂ + ⋯))` reduced modulo `m` at each
step. -/
def hornerMod : List Int → Int → Nat → Int
  | [], _, _ => 0
  | a :: w, x, m => (a + x * hornerMod w x m) % (m : Int)

/-- `r ^ e % m`, by repeated multiplication modulo `m`. -/
def powMod (r m : Nat) : Nat → Nat
  | 0 => 1 % m
  | e + 1 => powMod r m e * r % m

/-- The products `cₖ r^(d - k)` of `Ratpoints.BruteForce.scaledCoeffs c d r`, reduced modulo
`m`. -/
def scaledCoeffsMod (c : List Int) (d m r : Nat) : List Int :=
  (List.range (d + 1)).map fun k ↦ c.getD k 0 % (m : Int) * (powMod r m (d - k) : Int)

/-- `Nat.gcd a b` by Euclid's algorithm in Lean, which on small numbers is much faster than the
runtime's `Nat.gcd`: that one goes through GMP. -/
def natGcd (a b : Nat) : Nat := if b = 0 then a else natGcd b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- Whether `x` has no prime factor in common with `g`, quickly when `g = 1`. -/
def coprimeWith (g x : Nat) : Bool := g == 1 || natGcd x g == 1

/-- The row `r` of `Ratpoints.Fast.admitTable c d m`, computed directly (`sq` is
`Ratpoints.Fast.sqTable m`): entry `x` is `true` when `x`, `r` and `m` have no prime factor in
common and `F(x, r)` is a square modulo `m`. -/
def admitRow (c : List Int) (d m : Nat) (sq : Array Bool) (r : Nat) : Array Bool :=
  let w := scaledCoeffsMod c d m r
  let f : Int := if d % 2 = 1 then r else 1
  let g := natGcd r m
  (List.range m).toArray.map fun x ↦
    coprimeWith g x && sq[(hornerMod w x m * f % (m : Int)).toNat]!

/-- Candidates for the inverses modulo `m`, entry `i` by `inv i = -(m / i) inv (m % i)`: the
inverses when `m` is prime, and checked where they are used. -/
def invTable (m : Nat) : Array Nat :=
  (List.range m).foldl (fun inv i ↦
    inv.push (if i ≤ 1 then i else (m - m / i * inv[m % i]! % m) % m)) #[]

/-- The row `one` permuted: entry `x < m` is `one[x * u % m]`, the index stepped by `u` (for
`u < m`), without a division. -/
def permRow (one : Array Bool) (m u : Nat) : Array Bool := go 0 0 (Array.emptyWithCapacity m)
where
  /-- `acc` with the entries `one[i]` pushed for `x` up to `m - 1`, the index `i` stepped by `u`
  modulo `m`. -/
  go (x i : Nat) (acc : Array Bool) : Array Bool :=
    if x < m then go (x + 1) (if i + u < m then i + u else i + u - m) (acc.push one[i]!) else acc
  termination_by m - x

/-- The residues modulo `m` that allow a point `(a, y, b)` with `gcd(a, b) = 1` of the binary form
of degree `d` of `c`: entry `x` of row `r` (for `r, x < m`) is `true` when `x`, `r` and `m` have no
prime factor in common and `F(x, r)` is a square modulo `m`. A row `r` with an inverse `u < m`
modulo `m` (from `Ratpoints.Fast.invTable`) is row `1` permuted (`Ratpoints.Fast.permRow`):
`F(x, r) = r ^ D F(x u, 1)` with `D` even; the others come from `Ratpoints.Fast.admitRow`. -/
def admitTable (c : List Int) (d m : Nat) : Array (Array Bool) :=
  let sq := sqTable m
  let one := admitRow c d m sq 1
  let inv := invTable m
  go sq one inv 0 (Array.emptyWithCapacity m)
where
  /-- `acc` with the rows `r` to `m - 1` of `Ratpoints.Fast.admitTable` pushed. -/
  go (sq one : Array Bool) (inv : Array Nat) (r : Nat) (acc : Array (Array Bool)) :
      Array (Array Bool) :=
    if r < m then
      let u := inv[r]!
      go sq one inv (r + 1)
        (acc.push (if r * u % m == 1 % m && u < m then permRow one m u
          else admitRow c d m sq r))
    else acc
  termination_by m - r

/-! ### Bit masks -/

/-- The number with bit `j` set for every `j < m` with `f j`. -/
def pattern (m : Nat) (f : Nat → Bool) : Nat :=
  (List.range m).foldl (fun P j ↦ if f j then P ||| 1 <<< j else P) 0

/-- The pattern `P` of `m` bits repeated `2 ^ k` times. -/
def repeatPattern (P m : Nat) : Nat → Nat
  | 0 => P
  | k + 1 => repeatPattern P m k ||| repeatPattern P m k <<< (m * 2 ^ k)

/-- A number `k` of doublings with `N ≤ m * 2 ^ k` for `0 < m`. -/
def doublings (m N : Nat) : Nat := Nat.log2 (N / m) + 1

/-- The positions of the bits set in `n`, from the highest down, one `Nat.log2` at a time. -/
def setBitsSmall (n : Nat) : List Nat :=
  if h : n = 0 then [] else n.log2 :: setBitsSmall (n - 2 ^ n.log2)
termination_by n
decreasing_by exact Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.two_pow_pos _)

/-- The positions, offset by `o`, of the bits set in `n`: those of `n >>> h` and of `n % 2 ^ h`
for `h = 64 * 2 ^ (k - 1)` in turn, down to `k = 0`, where `Ratpoints.Fast.setBitsSmall` takes all
the bits that are left. -/
def setBitsAux (o n : Nat) : Nat → List Nat
  | 0 => (setBitsSmall n).map (o + ·)
  | k + 1 =>
    if n = 0 then [] else
      let h := 64 * 2 ^ k
      setBitsAux (o + h) (n >>> h) k ++ setBitsAux o (n % 2 ^ h) k

/-- The positions of the bits set in `n`, in descending order. -/
def setBits (n : Nat) : List Nat := setBitsAux 0 n (Nat.log2 (n.log2 / 64 + 1) + 1)

/-! ### Families of moduli -/

/-- The row of the modulus `m` for the residue `r` of the denominator, for the numerators
`0, G, 2G, …` and at least `N` of them, from the table `T = Ratpoints.Fast.admitTable c d m`: bit
`j` is set when the residues `G j` and `r` modulo `m` allow a point. -/
def baseRow (T : Array (Array Bool)) (m G N r : Nat) : Nat :=
  repeatPattern (pattern m fun j ↦ T[r]![G * j % m]!) m (doublings m N)

/-- A family of moduli with product `M`, for the step `G` of the numerators: an inverse `ginv` of
`G` modulo `M` and the rows for the residues `r < M` of the denominator, for the numerators
`0, G, 2G, …`: the AND of the rows of its moduli (`Ratpoints.Fast.baseRow`). -/
structure Family where
  /-- The product of the moduli. -/
  M : Nat
  /-- An inverse of the step `G` modulo `M`. -/
  ginv : Nat
  /-- The rows, for the residues `0, …, M - 1` of the denominator. -/
  rows : Array Nat

/-- The family of the moduli `m` of the list `ts` of pairs `(m, T)`, `T` the table
`Ratpoints.Fast.admitTable c d m`, for the step `G` and chunks of at most `L` numerators, if every
modulus is positive and `G` is invertible modulo their product `M`: its rows have `L + 8 M` bits,
enough for a chunk at every shift below `8 M` (`Ratpoints.Fast.Family.shift`). -/
def mkFamily (G L : Nat) (ts : List (Nat × Array (Array Bool))) : Option Family :=
  if ts.all (0 < ·.1) then
    let M := ts.foldl (· * ·.1) 1
    match (List.range M).find? fun u ↦ G * u % M == 1 % M with
    | none => none
    | some ginv =>
      let N := L + 8 * M
      let base := ts.map fun (m, T) ↦ (m, (List.range m).toArray.map (baseRow T m G N))
      let full := 2 ^ N - 1
      some { M, ginv, rows := (List.range M).toArray.map fun r ↦
        base.foldl (fun acc (m, B) ↦ acc &&& B[r % m]!) full }
  else none

/-- The shift that aligns the rows of the family `F` with a chunk starting at the numerator `a₀`:
`s < 8 F.M` with `G s ≡ a₀` modulo `F.M`, the least one plus the multiple of `F.M` that makes it a
multiple of `8` when `F.M` is odd (`F.M ^ 2 ≡ 1` modulo `8`), so that the search on byte arrays
reads whole bytes of the rows. -/
def Family.shift (F : Family) (a₀ : Int) : Nat :=
  let s := (a₀ * F.ginv % (F.M : Int)).toNat
  s + F.M * ((8 - s % 8) * F.M % 8)

/-! ### The sieve -/

/-- The candidates of a chunk: the mask ANDed with the rows `rs[i]` shifted by `sh[i] + o`, in
turn; once nothing is left, the rest is skipped. -/
def sieve (rs sh : Array Nat) (o mask : Nat) : Nat :=
  (List.range rs.size).foldl (fun acc i ↦ if acc == 0 then 0 else acc &&& rs[i]! >>> (sh[i]! + o))
    mask

/-- The number of the indices `i < n` with `i % G = ρ`. -/
def classCount (n G ρ : Nat) : Nat := (n + G - 1 - ρ) / G

/-- The chunks of `[0, cnt)`: their starts `k L` and lengths `min L (cnt - k L)`. -/
def chunks (cnt L : Nat) : List (Nat × Nat) :=
  (List.range ((cnt + L - 1) / L)).map fun k ↦ (k * L, min L (cnt - k * L))

/-- The chunks of the search, class by class: for the numerators `x` with `x + H ≡ ρ` modulo `G`,
each chunk as the residue of its numerators modulo `G`, its first numerator `a₀` and its length
`len`, for the numerators `a₀, a₀ + G, …, a₀ + (len - 1) G`. -/
def slots (H G L : Nat) : List (Nat × Int × Nat) :=
  (List.range G).flatMap fun ρ ↦
    (chunks (classCount (2 * H + 1) G ρ) L).map fun (t₀, len) ↦
      ((((ρ : Int) - H) % (G : Int)).toNat, ((ρ + G * t₀ : Nat) : Int) - H, len)

/-- The points with the denominator `b` in the chunk of `len` numerators `a₀, a₀ + G, …`, by the
sieve with the rows `rs` of `b` and the shifts `sh` moved by `o`. -/
def chunkPoints (c : List Int) (d G : Nat) (rs sh : Array Nat) (o : Nat) (a₀ : Int) (len b : Nat) :
    List (Int × Int × Int) :=
  let acc := sieve rs sh o (2 ^ len - 1)
  if acc == 0 then [] else pointsOfDen c d b ((setBits acc).map fun t ↦ a₀ + (G * t : Nat))

/-! ### The region -/

/-- The intervals of `x` that the Sturm step of `ratpoints` (`Ratpoints.Sturm.computeSturm`) keeps
at the depth `depth` of the whole line, outside of which `F(x, 1) < 0` assuming Sturm's theorem;
`none`, no restriction, when the step does not apply (the degree `0` or at least `2 ^ 57`, a height
of at least `2 ^ 63`, a depth beyond `55`, or a polynomial that is not squarefree). -/
def sturmIntervals (c : List Int) (d H depth : Nat) : Option (Array (Double × Double)) :=
  if 1 ≤ d ∧ d < 2 ^ 57 ∧ H < 2 ^ 63 ∧ depth ≤ 55 then
    Id.run (Sturm.computeSturm c d depth #[(Double.huge.neg, Double.huge)])
  else none

/-- An end of an interval of the region, for the numerators of absolute value at most `H`: the
exact value `n / q` of the double in lowest terms (`q` a power of `2`) when it is finite and of
absolute value at most `H`, else `H + 1` or `-(H + 1)` by its sign (an infinity too), which bound
the values `a / b` with `|a| ≤ H` and `b ≥ 1` as the end does, so that an interval beyond `H`
keeps no numerator; `none`, read by `Ratpoints.Fast.numRange` as no bound, only for a NaN. -/
def endFrac (H : Nat) (x : Double) : Option (Int × Nat) :=
  if x.isFinite then
    let (m, e) := x.toDyadic
    let q := 2 ^ (-e).toNat
    let n := m * 2 ^ e.toNat
    let g := Nat.gcd n.natAbs q
    if n.natAbs ≤ H * q then some (n / g, q / g)
    else some (if n < 0 then -((H : Int) + 1) else (H : Int) + 1, 1)
  else if x.isNaN then none
  else some (if x.signBit then -((H : Int) + 1) else (H : Int) + 1, 1)

/-- The region of the search, for the numerators of absolute value at most `H`: the intervals of
`Ratpoints.Fast.sturmIntervals` with their ends as in `Ratpoints.Fast.endFrac`. -/
def region (c : List Int) (d H depth : Nat) :
    Option (Array (Option (Int × Nat) × Option (Int × Nat))) :=
  (sturmIntervals c d H depth).map (·.map fun iv ↦ (endFrac H iv.1, endFrac H iv.2))

/-- The numerators `a` with `|a| ≤ H` and `a / b` in the interval with the ends `iv` (as in
`Ratpoints.Fast.endFrac`, an end `none` bounding nothing), from the first to the last; an end
beyond `H` gives its bound without the product with `b`, which would leave the small integers. -/
def numRange (H b : Nat) (iv : Option (Int × Nat) × Option (Int × Nat)) : Int × Int :=
  (match iv.1 with
    | some (n, q) =>
      if n.natAbs ≤ H * q then max (-(H : Int)) (-(-(b * n) / (q : Int)))
      else if 0 < n then (H : Int) + 1 else -(H : Int)
    | none => -(H : Int),
    match iv.2 with
    | some (n, q) =>
      if n.natAbs ≤ H * q then min (H : Int) (b * n / (q : Int))
      else if 0 < n then (H : Int) else -((H : Int) + 1)
    | none => H)

/-- The numerators of the denominator `b` to search: from the first to the last `a` with
`|a| ≤ H` and `a / b` in one of the intervals of `reg` (`none` when there is none), or all of
`-H, …, H` without a region. -/
def bounds (H b : Nat) (reg : Option (Array (Option (Int × Nat) × Option (Int × Nat)))) :
    Option (Int × Int) :=
  match reg with
  | none => some (-(H : Int), H)
  | some iv => iv.foldl (fun acc i ↦
      let r := numRange H b i
      if r.1 ≤ r.2 then
        match acc with
        | none => some r
        | some (lo, hi) => some (min lo r.1, max hi r.2)
      else acc) none

/-- The part of the chunk of the `len` numerators `a₀, a₀ + G, …` that holds those from `lo` to
`hi`, from the 64-bit word of the first to the end of the word of the last, or the whole chunk when
that part leaves out fewer than `len / 4` of its numerators (`none` when there is none): the bits
`t₁, …, t₁ + len₁ - 1` of the chunk as the pair `(t₁, len₁)`, `t₁` a multiple of `64`. -/
@[inline] def part (G : Nat) (lo hi a₀ : Int) (len : Nat) : Option (Nat × Nat) :=
  let t₁ : Int := max 0 ((lo - a₀ + G - 1) / G)
  let t₂ : Int := min (len - 1 : Int) ((hi - a₀) / G)
  if t₁ ≤ t₂ then
    let s := 64 * (t₁.toNat / 64)
    let e := min len (64 * (t₂.toNat / 64 + 1))
    if e - s + len / 4 ≤ len then some (s, e - s) else some (0, len)
  else none

/-- The points with the denominator `b` in the part of the chunk of the `len` numerators
`a₀, a₀ + G, …` that holds those from `lo` to `hi` (`Ratpoints.Fast.part`), by the sieve with the
rows `rs` of `b` and the shifts `sh` of the chunk moved by the offset of the part. -/
def partPoints (c : List Int) (d G : Nat) (rs sh : Array Nat) (lo hi a₀ : Int) (len b : Nat) :
    List (Int × Int × Int) :=
  match part G lo hi a₀ len with
  | none => []
  | some (t₁, len₁) => chunkPoints c d G rs sh t₁ (a₀ + (G * t₁ : Nat)) len₁ b

/-- The points with the denominator `b` in the chunks `sl`, each given by its residue modulo `G`,
its first numerator `a₀`, its length and the shifts of the families `fams` to `a₀`, by the sieve
with the rows of `b` and the region `reg`: none when the row of `b` of some family is `0`, which
clears every chunk; else the chunks whole when the numerators of `b` in the region
(`Ratpoints.Fast.bounds`) are all of `-H, …, H`, else their parts that hold these numerators
(`Ratpoints.Fast.partPoints`). -/
def denPoints (c : List Int) (d H G : Nat) (fams : Array Family)
    (reg : Option (Array (Option (Int × Nat) × Option (Int × Nat))))
    (sl : List (Nat × Int × Nat × Array Nat)) (b : Nat) : List (Int × Int × Int) :=
  let rs := fams.map fun F ↦ F.rows[b % F.M]!
  if rs.any (· == 0) then [] else
  match bounds H b reg with
  | none => []
  | some (lo, hi) =>
    if lo == -(H : Int) && hi == (H : Int) then
      sl.flatMap fun (_, a₀, len, sh) ↦ chunkPoints c d G rs sh 0 a₀ len b
    else sl.flatMap fun (_, a₀, len, sh) ↦ partPoints c d G rs sh lo hi a₀ len b

/-- The points with the denominators `dens` (all positive), by the sieve with the step `G`, chunks
of at most `L` numerators, the families `fams` and the region `reg`: for each denominator `b`, the
chunks of the classes that the residue of `b` modulo `G` allows (`Ratpoints.Fast.admitTable`
modulo `G`; these chunks are listed once for each residue), cut to the numerators of `b` in the
region (`Ratpoints.Fast.denPoints`). -/
def search (c : List Int) (d H G L : Nat) (fams : Array Family)
    (reg : Option (Array (Option (Int × Nat) × Option (Int × Nat)))) (dens : List Nat) :
    List (Int × Int × Int) :=
  let fams := fams.filter fun F ↦ F.rows.size == F.M && 0 < F.M
  let TG := admitTable c d G
  let sl := (slots H G L).map fun (r, a₀, len) ↦ (r, a₀, len, fams.map (Family.shift · a₀))
  let byRes := (List.range G).toArray.map fun g ↦ sl.filter fun (r, _) ↦ TG[g]![r]!
  let dens := dens.filter fun b ↦ !byRes[b % G]!.isEmpty
  dens.flatMap fun b ↦ denPoints c d H G fams reg byRes[b % G]! b

/-! ### The denominators -/

/-- Whether `k` is a square. -/
def isSquare (k : Nat) : Bool := k.sqrt * k.sqrt == k

/-- The Jacobi symbol `(a / n)` times `s` for odd `n`, by Euclid's algorithm in at most `fuel`
steps: the factors `2` of `a` are taken out with the sign of `(2 / n)`, and for odd `a` the
symbol becomes `(n % a / a)` with the sign of the reciprocity. The value is `0` when `a` and `n`
have a common factor, and also when the steps run out, which they do not for `n < 2 ^ 64` and
`fuel = 256`; only the value `-1` is used (`Ratpoints.Fast.forbiddenDens`). -/
def jacobiNatAux : Nat → Nat → Nat → Int → Int
  | 0, _, _, _ => 0
  | fuel + 1, a, n, s =>
    if a == 0 then (if n == 1 then s else 0)
    else if a % 2 == 0 then
      jacobiNatAux fuel (a / 2) n (if n % 8 == 3 || n % 8 == 5 then -s else s)
    else jacobiNatAux fuel (n % a) a (if a % 4 == 3 && n % 4 == 3 then -s else s)

/-- The Jacobi symbol `(a / n)` for odd `n` (`Ratpoints.Fast.jacobiNatAux`), or `0`. -/
def jacobiNat (a n : Nat) : Int := jacobiNatAux 256 (a % n) n 1

/-- `a` with the bytes `j, j + n, j + 2 n, …` up to `hi` set to `1`. -/
def markMultiples (a : ByteArray) (n j hi : Nat) : ByteArray :=
  if j ≤ hi ∧ 0 < n then markMultiples (a.set! j 1) n (j + n) hi else a
termination_by hi + 1 - j

/-- The loop of `Ratpoints.Fast.forbiddenDens` over the odd numbers from `p` to `hi`, with the odd
composites marked in `comp` and the forbidden denominators in `forb` so far: an unmarked `p` is a
prime, whose odd multiples from `p ^ 2` on are marked composite, and whose multiples are marked
forbidden when `(lc / p) = -1`. -/
def forbiddenDensFrom (lc : Int) (hi : Nat) (comp forb : ByteArray) (p : Nat) : ByteArray :=
  if p ≤ hi then
    if comp[p]! != 0 then forbiddenDensFrom lc hi comp forb (p + 2)
    else
      let comp := markMultiples comp (2 * p) (p * p) hi
      let r := (lc % (p : Int)).toNat
      let forb := if r != 0 && jacobiNat r p == -1 then markMultiples forb p p hi else forb
      forbiddenDensFrom lc hi comp forb (p + 2)
  else forb
termination_by hi + 1 - p

/-- The denominators up to `hi` that no point of a curve of even degree with the leading
coefficient `lc` can have, marked `1`: the multiples of an odd `p` with `(lc / p) = -1`
(`Ratpoints.Fast.jacobiNat`), `p` running over the odd primes up to `hi`, found by the sieve of
Eratosthenes along the way (which `p` are tried affects the speed only). -/
def forbiddenDens (lc : Int) (hi : Nat) : ByteArray :=
  let z : ByteArray := ⟨Array.replicate (hi + 1) 0⟩
  forbiddenDensFrom lc hi z z 3

/-- The numbers `b` from `max lo 1` to `n` with `m[b] = v`, in ascending order, before `acc`. -/
def collectMarked (m : ByteArray) (v : UInt8) (lo : Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | b + 1, acc =>
    if b + 1 < lo then acc
    else collectMarked m v lo b (if m[b + 1]! == v then (b + 1) :: acc else acc)

/-- `a` with the bytes `s j ^ 2 ≤ hi` for `j` from `k` on (and `j ≤ hi`) set to `1`. -/
def markSquares (a : ByteArray) (s k hi : Nat) : ByteArray :=
  if k ≤ hi ∧ s * k * k ≤ hi then markSquares (a.set! (s * k * k) 1) s (k + 1) hi else a
termination_by hi + 1 - k

/-- The numbers `s k ^ 2 ≤ hi` with `s` dividing `n` and `k ≥ 1`, marked `1` (for `n ≥ 1`). -/
def squareDens (n hi : Nat) : ByteArray :=
  (List.range' 1 (min n hi)).foldl (fun a s ↦ if n % s == 0 then markSquares a s 1 hi else a)
    ⟨Array.replicate (hi + 1) 0⟩

/-- The upper finite denominator bound: a positive requested bound capped by the height,
or the height when the requested bound is nonpositive. -/
def denominatorBound (bHigh : Int) (H : Nat) : Nat :=
  if bHigh < 1 then H else min H bHigh.toNat

/-- The denominators of the search, for the degree `d`, the height bound `H` and the range of
`bLow` and `bHigh`: those `b` with `max 1 bLow ≤ b ≤ H`, and `b ≤ bHigh` unless `bHigh < 1`; for
odd `d` only those of the form `s k ^ 2` with `s` dividing the leading coefficient
(`Ratpoints.Fast.squareDens`), for even `d` those that `Ratpoints.Fast.forbiddenDens` does not mark
(all of them when the leading coefficient is a positive square, which
`Ratpoints.Fast.forbiddenDens` would not mark); in ascending order. -/
def denominators (c : List Int) (d H : Nat) (bLow bHigh : Int) : List Nat :=
  let lo := max 1 bLow.toNat
  let hi := denominatorBound bHigh H
  if d % 2 = 1 then collectMarked (squareDens (c.getD d 0).natAbs hi) 1 lo hi []
  else if 0 < c.getD d 0 && isSquare (c.getD d 0).toNat then List.range' lo (hi + 1 - lo)
  else collectMarked (forbiddenDens (c.getD d 0) hi) 0 lo hi []

/-! ### The choice of the parameters -/

/-- The fraction, in thousandths, of the pairs of residues modulo `m` that allow a point, from
the table `T = Ratpoints.Fast.admitTable c d m`. -/
def density (m : Nat) (T : Array (Array Bool)) : Nat :=
  let count (row : Array Bool) : Nat := row.foldl (fun n b ↦ if b then n + 1 else n) 0
  let c₁ := count T[1 % m]!
  -- a row prime to `m` is row `1` permuted
  let n := (List.range m).foldl (fun n r ↦ n + if natGcd r m == 1 then c₁ else count T[r]!) 0
  1000 * n / (m * m)

/-- The pairs `(m, T)` grouped into families: in ascending order of `m`, each family taking moduli
while their product stays at most `Mmax`. -/
def groupModuli (Mmax : Nat) :
    List (Nat × Array (Array Bool)) → List (List (Nat × Array (Array Bool)))
  | [] => []
  | t :: ts =>
    match groupModuli Mmax ts with
    | (g :: gs) => if t.1 * g.foldl (· * ·.1) 1 ≤ Mmax then (t :: g) :: gs else [t] :: g :: gs
    | [] => [[t]]

/-- The parameters of the search: the step `G`, the chunk length `L` and the families, the most
selective first. -/
structure Config where
  /-- The step of the numerators in a chunk, a power of `2`. -/
  G : Nat
  /-- The largest number of numerators in a chunk. -/
  L : Nat
  /-- The families. -/
  fams : Array Family

/-- The moduli that the sieve may use. -/
def candidateModuli : List Nat :=
  [9, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127]

/-- The further moduli, for the searches in which many candidates are expected to survive the
moduli of `Ratpoints.Fast.candidateModuli` (`Ratpoints.Fast.takeModuli`). -/
def furtherModuli : List Nat :=
  [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347,
    349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457,
    461, 463, 467, 479, 487, 491, 499, 503, 509]

/-- The moduli `m` of `ms` with their tables `Ratpoints.Fast.admitTable c d m`, taken in turn while
`64 m ^ 2 ≤ κ E`, `E` the expected number of candidates that survive the moduli taken so far (each
taken modulus keeps the share of them given by the density of its table): a modulus pays for its
table, of cost about `m ^ 2`, only while many candidates are left. -/
def takeModuli (c : List Int) (d κ : Nat) : List Nat → Nat → List (Nat × Array (Array Bool))
  | [], _ => []
  | m :: ms, E =>
    if 64 * m * m ≤ κ * E then
      let T := admitTable c d m
      (m, T) :: takeModuli c d κ ms (E * density m T / 1000)
    else []

/-- Settings of the choice of the parameters (for tuning): the step `G`, the largest chunk length,
the largest product of a family, the weight of the choice of the moduli and the depth of the Sturm
step; `0` for the default. -/
structure Tuning where
  /-- The step. -/
  G : Nat := 0
  /-- The largest chunk length. -/
  L : Nat := 0
  /-- The largest product of the moduli of a family. -/
  Mmax : Nat := 0
  /-- The weight `κ` of `Ratpoints.Fast.takeModuli`. -/
  further : Nat := 0
  /-- The depth of the Sturm step (`Ratpoints.Fast.region`). -/
  sturm : Nat := 0

/-- `x`, or `dflt` when `x = 0`. -/
def orDefault (x dflt : Nat) : Nat := if x = 0 then dflt else x

/-- The moduli of the sieve with their tables, for the coefficients `c` of degree `d`, the height
bound `H` and `B` denominators: those of `Ratpoints.Fast.candidateModuli` and then of
`Ratpoints.Fast.furtherModuli` that the expected number of survivors pays for
(`Ratpoints.Fast.takeModuli`, from the `(2 H + 1) B` candidates). -/
def moduliTables (tu : Tuning) (c : List Int) (d H B : Nat) : List (Nat × Array (Array Bool)) :=
  takeModuli c d (orDefault tu.further 512) (candidateModuli ++ furtherModuli) ((2 * H + 1) * B)

/-- The moduli of `Ratpoints.Fast.moduliTables` grouped into families
(`Ratpoints.Fast.groupModuli`), the most selective first. -/
def sortedGroups (tu : Tuning) (c : List Int) (d H B : Nat) :
    List (List (Nat × Array (Array Bool))) :=
  let Mmax := orDefault tu.Mmax (max 15 (min 1500 (B / 16)))
  let scored := (groupModuli Mmax (moduliTables tu c d H B)).map fun g ↦
    (g, g.foldl (fun s (m, T) ↦ s * density m T / 1000) 1000)
  (scored.mergeSort fun x y ↦ x.2 ≤ y.2).map (·.1)

/-- The parameters for the coefficients `c` of degree `d`, the height bound `H` and `B`
denominators. The chunk length is `tu.L` (by default `8192`), but at most the number of numerators
of a class rounded up to a multiple of `64`: by default a multiple of `64`, so that the rows of the
families are long enough at every shift for the fast path of `Ratpoints.Mask.andRows` in
`Ratpoints.FastMask.choose`, which makes the same choice. -/
def choose (tu : Tuning) (c : List Int) (d H B : Nat) : Config :=
  let G := orDefault tu.G 16
  let cnt := (2 * H + 1 + G - 1) / G
  let L := max 1 (min (orDefault tu.L 8192) (64 * ((cnt + 63) / 64)))
  { G, L, fams := ((sortedGroups tu c d H B).filterMap (mkFamily G L)).toArray }

/-! ### The search -/

/-- The normalized points of height at most `H` on `y ^ 2 = F(x, z)` whose denominator `z` is `0`
or lies in the range of `bLow` and `bHigh` (`bLow ≤ z`, and `z ≤ bHigh` unless `bHigh < 1`), each
once: the points at infinity, then those that the sieve finds (only such points in any case, and
all of them assuming Sturm's theorem, on which the region of the numerators rests). -/
def sievePoints (c : List Int) (H : Nat) (bLow bHigh : Int) (tu : Tuning := {}) :
    List (Int × Int × Int) :=
  let d := BruteForce.degree c
  let dens := denominators c d H bLow bHigh
  let cfg := choose tu c d H dens.length
  (if 1 ≤ H then pointsOfDen c d 0 [1] else []) ++
    search c d H cfg.G cfg.L cfg.fams (region c d H (orDefault tu.sturm 10)) dens

/-- The coefficients to search with and whether they are reversed: the reversed coefficients when
the reversal check of `ratpoints` (`Ratpoints.Setup.reversal`) reverses them and no range of the
denominators restricts the search (`bLow ≤ 1`, and `bHigh < 1` or `H ≤ bHigh`); otherwise, the
refusal of the check included, `c` itself. -/
def reversed (c : List Int) (H : Nat) (bLow bHigh : Int) : List Int × Bool :=
  if bLow ≤ 1 ∧ (bHigh < 1 ∨ (H : Int) ≤ bHigh) then
    match Setup.reversal true c (BruteForce.degree c) with
    | .ok (c', _, true) => (c', true)
    | _ => (c, false)
  else (c, false)

/-- The normalized points of height at most `H` on `y ^ 2 = F(x, z)` whose denominator `z` is `0`
or lies in the range of `bLow` and `bHigh` (`bLow ≤ z`, and `z ≤ bHigh` unless `bHigh < 1`), each
once: those of `Ratpoints.Fast.sievePoints`, on the coefficients reversed as `ratpoints` reverses
them when no range of the denominators is given (`Ratpoints.Fast.reversed`; the binary form with
`x` and `z` exchanged), with the points mapped back by `Ratpoints.Sieve.swapPoint` (only such
points in any case, and all of them assuming Sturm's theorem, on which the region of the
numerators rests). -/
def fastPoints (c : List Int) (H : Nat) (bLow bHigh : Int) (tu : Tuning := {}) :
    List (Int × Int × Int) :=
  match reversed c H bLow bHigh with
  | (c', true) => (sievePoints c' H 1 0 tu).map Sieve.swapPoint
  | _ => sievePoints c H bLow bHigh tu

end Fast

end Ratpoints

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4Geometry
public import LeanPool.DistinctDistances.RationalFarkasRows

/-!
# Computable geometric row families

Each tag selects a rational row and checks its side conditions. The row-soundness
modules prove that every accepted row holds for the normalized configuration.
-/

@[expose] public section

namespace Esgk.S4

open Finset EuclideanGeometry Esgk.FarkasPackedCheck

/-! ### Row tags -/

/-- A row tag: the row family and its grid indices, band indices and rational witnesses
(`(num, den)` pairs). -/
inductive Tag where
  /-- `𝒜(gᵢ) ≤ 𝒜(gⱼ)` -/
  | amono (i j : Nat)
  /-- `3ℛ - 𝒜` is nondecreasing from `gᵢ` to `gⱼ` -/
  | xmono (i j : Nat)
  /-- `𝒜(gᵢ) ≤ 3ℛ(gᵢ)` -/
  | xpos (i : Nat)
  /-- `3ℛ(gᵢ) - 𝔮 ≤ 𝒜(gᵢ)` -/
  | xleq (i : Nat)
  /-- `1 - 1/n ≤ 𝒜(gᵢ)` for `gᵢ ≥ 2` -/
  | a2lo (i : Nat)
  /-- Lemma M (lower Riemann sum over the whole grid) -/
  | mlo
  /-- Lemma K over the grid points `gᵢ, …, gⱼ` -/
  | layer (i j : Nat)
  /-- Lemma P''(a) at `ρ = g_iρ`, `r′ = g_ir`, with `g_ih = ρ/2` and chord evidence `e` -/
  | pa (iρ ir ih e : Nat)
  /-- Lemma P''(b) -/
  | pb (iρ ir ih e : Nat)
  /-- Lemma P''(c) -/
  | pc (iρ ir ih e : Nat)
  /-- Lemma A'' at `λ = g_il`, `w = g_iw`, `h = g_ih`, with the witness `r₄ ≥ √(4 - λ²)` -/
  | aa (il iw ih r4n r4d : Nat)
  /-- Lemma J at `λ = g_il`, `g₂ = g_ig2`, `g_σ = g_igs`, with the witness
  `u ≤ √(sBar² - h₀²)` -/
  | jj (il ig2 igs un ud : Nat)
  /-- Lemma AB, row AB1, over the bands `b₀, …, b₀ + m - 1` of one threshold -/
  | ab1 (b0 m : Nat)
  /-- Lemma AB, row AB2, on band `b` -/
  | ab2 (b : Nat)
  /-- Lemma AB, row AB3, on band `b` at `t = tn/td` -/
  | ab3 (b tn td : Nat)
  /-- Lemma AB, row AB4, on band `b` at `t = tn/td` -/
  | ab4 (b tn td : Nat)
  /-- Lemma AB, row AB6u, over the bands `b₀, …, b₀ + m - 1` -/
  | ab6u (b0 m : Nat)
  /-- Lemma AB, row AB6v, over the bands `b₀, …, b₀ + m - 1`, with `h = g_ih` -/
  | ab6v (b0 m ih : Nat)
  /-- the upper case row (`Y_lo ≤ yMean` with the upper Riemann sum) -/
  | caselo
  /-- the lower case row (`yMean ≤ Y_hi` with the lower Riemann sum) -/
  | casehi

/-! ### The row builder -/

namespace Params

variable (P : Params)

/-- `gᵢ² ≤ gᵢ₊₁²` for the `c` cells starting at `k`. -/
def gridMono : Nat → Nat → Bool
  | 0, _ => true
  | c + 1, k => decide (P.sq k ≤ P.sq (k + 1)) && gridMono c (k + 1)

/-- The entries `f k, f (k + 1), …, f (k + c - 1)`, concatenated. -/
def cells (f : Nat → List (Nat × ℚ)) : Nat → Nat → List (Nat × ℚ)
  | 0, _ => []
  | c + 1, k => f k ++ cells f c (k + 1)

/-- The bands `b₀, …, b₀ + m - 1` share the threshold of `b₀`, have nondecreasing edges, and
the upper edge of each band is the lower edge of the next. -/
def chain (b0 : Nat) : Nat → Bool
  | 0 => true
  | m + 1 => chain b0 m && Nat.beq (P.bLam (b0 + m)) (P.bLam b0) &&
      decide (P.sq (P.bLo (b0 + m)) ≤ P.sq (P.bHi (b0 + m))) &&
      (Nat.beq m 0 || Nat.beq (P.bHi (b0 + m - 1)) (P.bLo (b0 + m)))

/-- The chord evidence `e` for the condition `(lo, hi, T)`: `0` is Step L0, `1` is the radius
bound, `k + 2` is the proved chord condition `k`. -/
def chordOK (lo hi T : ℚ) : Nat → Bool
  | 0 => decide ((1 - sig * sig) * (1 + sig) ≤ sig * T)
  | 1 => decide ((1 - sig * sig) * (1 - sig * sig) * (hi * hi) ≤ sig * sig * (T * T)) &&
      decide (0 ≤ T)
  | k + 2 => Nat.blt k P.nch && decide (0 ≤ (P.ch k).1) && decide ((P.ch k).1 ≤ lo) &&
      decide (0 ≤ hi) && decide (hi ≤ (P.ch k).2.1) && decide ((P.ch k).2.2 ≤ T)

/-- Step L0 at the squared threshold `l`. -/
def stepL0 (l : ℚ) : Bool := decide ((1 - sig * sig) * (sig + 1) ≤ sig * l)

/-- The rows `𝒜(gᵢ) ≤ 𝒜(gⱼ)`. -/
def rowAmono (i j : Nat) : Option QRow :=
  if P.ok i && P.ok j && decide (P.sq i ≤ P.sq j) then
    some ⟨[(aVar i, 1), (aVar j, -1)], 0⟩
  else none

/-- The rows `3ℛ(gᵢ) - 𝒜(gᵢ) ≤ 3ℛ(gⱼ) - 𝒜(gⱼ)`. -/
def rowXmono (i j : Nat) : Option QRow :=
  if P.ok i && P.ok j && decide (P.sq i ≤ P.sq j) then
    some ⟨[(rVar i, 3), (aVar i, -1), (rVar j, -3), (aVar j, 1)], 0⟩
  else none

/-- The rows `𝒜(gᵢ) ≤ 3ℛ(gᵢ)`. -/
def rowXpos (i : Nat) : Option QRow :=
  if P.ok i then some ⟨[(aVar i, 1), (rVar i, -3)], 0⟩ else none

/-- The rows `3ℛ(gᵢ) - 𝒜(gᵢ) - 3 D/n - 1/n ≤ -1`. -/
def rowXleq (i : Nat) : Option QRow :=
  if P.ok i then some ⟨[(rVar i, 3), (aVar i, -1), (P.dV, -3), (P.eV, -1)], -1⟩ else none

/-- The row `-𝒜(gᵢ) - 1/n ≤ -1` for `gᵢ² ≥ 4`. -/
def rowA2lo (i : Nat) : Option QRow :=
  if P.ok i && decide (4 ≤ P.sq i) then some ⟨[(aVar i, -1), (P.eV, -1)], -1⟩ else none

/-- The entries of one cell of Lemma M. -/
def mloCell (k : Nat) : List (Nat × ℚ) :=
  [(aVar k, -((P.sq (k + 1) - P.sq k) / 2)), (rVar k, 6 * ((P.sq (k + 1) - P.sq k) / 2))]

/-- The row of Lemma M: `∑ w (6ℛ(a) - 𝒜(a)) - 12 D/n - 2/n ≤ -3`. -/
def rowMlo : Option QRow :=
  if Nat.blt 0 P.ng && decide (0 ≤ P.sq 0) && P.gridMono (P.ng - 1) 0 &&
      decide (P.sq (P.ng - 1) ≤ 4) then
    some ⟨cells P.mloCell (P.ng - 1) 0 ++ [(P.dV, -12), (P.eV, -2)], -3⟩
  else none

/-- The entries of one cell of Lemma K. -/
def layerCell (k : Nat) : List (Nat × ℚ) := [(aVar k, P.sq (k + 1) - P.sq k)]

/-- The row of Lemma K over `gᵢ, …, gⱼ`: `∑ (b² - a²) 𝒜(a) ≤ 2sBar`. -/
def rowLayer (i j : Nat) : Option QRow :=
  if P.ok j && Nat.ble i j && P.gridMono (j - i) i &&
      decide (P.sq j ≤ 2 * sig * sig + 2 * sig) then
    some ⟨cells P.layerCell (j - i) i, 2 * sig⟩
  else none

/-- The side conditions of Lemma P'' at `ρ = g_iρ`, `r′ = g_ir`, `ρ/2 = g_ih`. -/
def palOK (iρ ir ih e : Nat) : Bool :=
  P.ok iρ && P.ok ir && P.ok ih && decide (0 ≤ P.g ih) && decide (4 * P.sq ih ≤ P.sq iρ) &&
    decide (P.sq ih ≤ P.sq ir) && P.chordOK (P.g ih) (P.g ir) (P.sq iρ) e

/-- The common part of the rows of Lemma P'': `𝒜(r′) - 2ℛ(r′) - 𝒜(ρ) ≤ 0`, or for `r′ ≥ 2`,
`-1/n - 2 D/n - 𝒜(ρ) ≤ -1`. -/
def palBase (iρ ir : Nat) : List (Nat × ℚ) × ℚ :=
  bif decide (4 ≤ P.sq ir) then ([(P.eV, -1), (P.dV, -2), (aVar iρ, -1)], -1)
  else ([(aVar ir, 1), (rVar ir, -2), (aVar iρ, -1)], 0)

/-- The row of Lemma P''(a). -/
def rowPa (iρ ir ih e : Nat) : Option QRow :=
  if P.palOK iρ ir ih e then some ⟨(P.palBase iρ ir).1, (P.palBase iρ ir).2⟩ else none

/-- The row of Lemma P''(b): Lemma P''(a) plus `𝒜(ρ/2) - ℛ(ρ/2)`. -/
def rowPb (iρ ir ih e : Nat) : Option QRow :=
  if P.palOK iρ ir ih e then
    some ⟨(P.palBase iρ ir).1 ++ [(aVar ih, 1), (rVar ih, -1)], (P.palBase iρ ir).2⟩
  else none

/-- The row of Lemma P''(c): Lemma P''(a) minus `𝒜(ρ/2) - 2ℛ(ρ/2)`. -/
def rowPc (iρ ir ih e : Nat) : Option QRow :=
  if P.palOK iρ ir ih e then
    some ⟨(P.palBase iρ ir).1 ++ [(aVar ih, -1), (rVar ih, 2)], (P.palBase iρ ir).2⟩
  else none

/-- The row of Lemma A'': `-2𝒜(λ) - (4/3)𝒜(h) + (4/3)𝒜(w) - 6 D/n - 4/n ≤ -4`, with
`r₄ = r4n/r4d`. -/
def rowAA (il iw ih r4n r4d : Nat) : Option QRow :=
  let r4 := mkRat r4n r4d
  if P.ok il && P.ok iw && P.ok ih && decide (0 ≤ r4) && decide (4 - P.sq il ≤ r4 * r4) &&
      decide (4 - P.sq il ≤ 4 * (sig * sig)) && stepL0 (P.sq il) &&
      decide (0 ≤ P.sq iw) && decide (P.sq iw ≤ sig * sig + 1 - sig * r4) &&
      decide (2 + r4 ≤ P.sq ih) then
    some ⟨[(aVar il, -2), (aVar ih, -4 / 3), (aVar iw, 4 / 3), (P.dV, -6), (P.eV, -4)], -4⟩
  else none

/-- The row of Lemma J: `𝒜(g₂) - 𝒜(λ) - 𝒜(g_σ) - 6 D/n - 2/n ≤ -2`, with `h₀ = W/(2λ)`
(`H = h₀²`) and `u = un/ud`. -/
def rowJ (il ig2 igs un ud : Nat) : Option QRow :=
  let u := mkRat un ud
  let H := wid * wid / (4 * P.sq il)
  if P.ok il && P.ok ig2 && P.ok igs && decide (0 < P.sq il) &&
      decide (wid * wid ≤ 4 * P.sq il * H) && decide (P.sq ig2 < 4 * (sig * sig - H)) &&
      decide (0 ≤ u) && decide (u * u ≤ sig * sig - H) && decide (0 ≤ P.g igs) &&
      decide (1 - sig * sig ≤ P.g igs * P.g igs + 2 * P.g igs * u) then
    some ⟨[(aVar ig2, 1), (aVar il, -1), (aVar igs, -1), (P.dV, -6), (P.eV, -2)], -2⟩
  else none

/-- The entries `(sel (b₀ + j), q)` for `j < m`. -/
def bandEnt (sel : Nat → Nat) (q : ℚ) (b0 : Nat) : Nat → List (Nat × ℚ)
  | 0 => []
  | m + 1 => bandEnt sel q b0 m ++ [(sel (b0 + m), q)]

/-- The row AB1: `-2𝒜(λ) - 6 D/n - 4/n - ∑ⱼ W_j ≤ -4`. -/
def rowAB1 (b0 m : Nat) : Option QRow :=
  if Nat.blt 0 m && P.okB (b0 + m - 1) && P.chain b0 m && P.ok (P.bLam b0) &&
      decide (4 * P.sq (P.bLo b0) ≤ P.sq (P.bLam b0)) &&
      decide (4 ≤ P.sq (P.bHi (b0 + m - 1))) then
    some ⟨[(aVar (P.bLam b0), -2), (P.dV, -6), (P.eV, -4)] ++ bandEnt P.wV (-1) b0 m, -4⟩
  else none

/-- The row AB2: `W_b ≤ (4/3)(𝒜(e_hi) - 𝒜(e_lo))`. -/
def rowAB2 (b : Nat) : Option QRow :=
  if P.okB b && P.ok (P.bLo b) && P.ok (P.bHi b) && stepL0 (P.sq (P.bLam b)) &&
      decide (P.sq (P.bLo b) ≤ P.sq (P.bHi b)) then
    some ⟨[(P.wV b, 1), (aVar (P.bHi b), -4 / 3), (aVar (P.bLo b), 4 / 3)], 0⟩
  else none

/-- The row AB3 at `t`: `(2e_lo² - ((4 + t)sBar² + (4sBar² - λ²)/t)) W_b - (1 + 2/t) U_b
- (2 + t) V_b ≤ 0`. -/
def rowAB3 (b tn td : Nat) : Option QRow :=
  let t := mkRat tn td
  if P.okB b && decide (0 < t) then
    some ⟨[(P.wV b, 2 * P.sq (P.bLo b) -
        ((4 + t) * (sig * sig) + (4 * (sig * sig) - P.sq (P.bLam b)) / t)),
      (P.uV b, -(1 + 2 / t)), (P.vV b, -(2 + t))], 0⟩
  else none

/-- `max x 0`. -/
def posPartQ (x : ℚ) : ℚ := bif decide (x ≤ 0) then 0 else x

/-- The row AB4 at `t`: `((4 - t)sBar² - (4sBar² - λ²)/t - 2e_hi²) W_b - max(2/t - 1, 0) U_b
- max(t - 2, 0) V_b ≤ 0`. -/
def rowAB4 (b tn td : Nat) : Option QRow :=
  let t := mkRat tn td
  if P.okB b && decide (0 < t) then
    some ⟨[(P.wV b, ((4 - t) * (sig * sig) - (4 * (sig * sig) - P.sq (P.bLam b)) / t) -
        2 * P.sq (P.bHi b)),
      (P.uV b, -posPartQ (2 / t - 1)), (P.vV b, -posPartQ (t - 2))], 0⟩
  else none

/-- The row AB6u for the case `yMean ≤ Y_hi`: `∑ⱼ U_j - 12 Y_hi D/n + 12 Y_hi ℛ(λ) ≤ 0`. -/
def rowAB6u (Yhi : ℚ) (b0 m : Nat) : Option QRow :=
  if Nat.blt 0 m && P.okB (b0 + m - 1) && P.chain b0 m && P.ok (P.bLam b0) then
    some ⟨bandEnt P.uV 1 b0 m ++ [(P.dV, -12 * Yhi), (rVar (P.bLam b0), 12 * Yhi)], 0⟩
  else none

/-- The row AB6v for the case `yMean ≤ Y_hi`: `∑ⱼ V_j - 4 Y_hi D/n + 4 Y_hi ℛ(h) ≤ 0`. -/
def rowAB6v (Yhi : ℚ) (b0 m ih : Nat) : Option QRow :=
  if Nat.blt 0 m && P.okB (b0 + m - 1) && P.chain b0 m && P.ok ih &&
      stepL0 (P.sq (P.bLam b0)) && decide (4 * P.sq ih ≤ P.sq (P.bLam b0)) then
    some ⟨bandEnt P.vV 1 b0 m ++ [(P.dV, -4 * Yhi), (rVar ih, 4 * Yhi)], 0⟩
  else none

/-- The entries of one cell of the upper case row. -/
def upCell (k : Nat) : List (Nat × ℚ) :=
  [(rVar (k + 1), -6 * ((P.sq (k + 1) - P.sq k) / 2)),
    (aVar (k + 1), 2 * ((P.sq (k + 1) - P.sq k) / 2))]

/-- The upper case row for `Y_lo ≤ yMean`: `12 D/n + 4/n - 2 Up ≤ W - Y_lo + 4`. -/
def rowCaseLo (Ylo : ℚ) : Option QRow :=
  if Nat.blt 0 P.ng && decide (0 ≤ P.sq 0) && P.gridMono (P.ng - 1) 0 &&
      decide (4 ≤ P.sq (P.ng - 1)) then
    some ⟨[(P.dV, 12), (P.eV, 4)] ++ cells P.upCell (P.ng - 1) 0 ++
        [(rVar 0, -6 * (P.sq 0 / 2)), (aVar 0, 2 * (P.sq 0 / 2))], wid - Ylo + 4⟩
  else none

/-- The entries of one cell of the lower case row. -/
def loCell (k : Nat) : List (Nat × ℚ) :=
  [(rVar k, 6 * ((P.sq (k + 1) - P.sq k) / 2)), (aVar k, -2 * ((P.sq (k + 1) - P.sq k) / 2))]

/-- The lower case row for `yMean ≤ Y_hi`: `-12 D/n - 4/n + 2 Lo ≤ Y_hi - W - 4`. -/
def rowCaseHi (Yhi : ℚ) : Option QRow :=
  if Nat.blt 0 P.ng && decide (0 ≤ P.sq 0) && P.gridMono (P.ng - 1) 0 &&
      decide (P.sq (P.ng - 1) ≤ 4) then
    some ⟨[(P.dV, -12), (P.eV, -4)] ++ cells P.loCell (P.ng - 1) 0, Yhi - wid - 4⟩
  else none

/-- The row of a tag in the case `Y_lo ≤ yMean ≤ Y_hi`, or `none` if a side condition fails. -/
def build (Ylo Yhi : ℚ) : Tag → Option QRow
  | .amono i j => P.rowAmono i j
  | .xmono i j => P.rowXmono i j
  | .xpos i => P.rowXpos i
  | .xleq i => P.rowXleq i
  | .a2lo i => P.rowA2lo i
  | .mlo => P.rowMlo
  | .layer i j => P.rowLayer i j
  | .pa iρ ir ih e => P.rowPa iρ ir ih e
  | .pb iρ ir ih e => P.rowPb iρ ir ih e
  | .pc iρ ir ih e => P.rowPc iρ ir ih e
  | .aa il iw ih r4n r4d => P.rowAA il iw ih r4n r4d
  | .jj il ig2 igs un ud => P.rowJ il ig2 igs un ud
  | .ab1 b0 m => P.rowAB1 b0 m
  | .ab2 b => P.rowAB2 b
  | .ab3 b tn td => P.rowAB3 b tn td
  | .ab4 b tn td => P.rowAB4 b tn td
  | .ab6u b0 m => P.rowAB6u Yhi b0 m
  | .ab6v b0 m ih => P.rowAB6v Yhi b0 m ih
  | .caselo => P.rowCaseLo Ylo
  | .casehi => P.rowCaseHi Yhi

/-- The integer row of a tag. -/
noncomputable def buildInt (Ylo Yhi : ℚ) (t : Tag) : Option Row :=
  (P.build Ylo Yhi t).bind QRow.toRow

/-- The box of the normalized variables: `𝒜 ∈ [0, 1]`, `ℛ ∈ [0, dMean]`,
`D/n ∈ [1/3 - ε/3, dMean]`, `1/n ∈ [0, ε]`, `W ∈ [0, 2]`, `U, V ∈ [0, 4]`. -/
def box : Box where
  nv := P.nv
  lo k := bif Nat.beq k (2 * P.ng) then 1 / 3 - eps / 3 else 0
  hi k := bif Nat.blt k (2 * P.ng) then (bif Nat.beq (k % 2) 0 then 1 else dbar)
    else bif Nat.beq k (2 * P.ng) then dbar
    else bif Nat.beq k (2 * P.ng + 1) then eps
    else bif Nat.beq ((k - (2 * P.ng + 2)) % 3) 0 then 2 else 4

/-- The proved chord conditions hold for `S`. -/
def ChordsHold {n : ℕ} (S : Setting n) : Prop :=
  ∀ k < P.nch, S.ChordHolds (P.ch k).1 (P.ch k).2.1 (P.ch k).2.2

end Params

end Esgk.S4

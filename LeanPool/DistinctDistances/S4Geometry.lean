/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.BandTriples
public import LeanPool.DistinctDistances.PalettePairCountCut
public import LeanPool.DistinctDistances.S4RowFacts
public import LeanPool.DistinctDistances.ThinAnnulus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Geometric parameters and normalized certificate variables

Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md` is proved by an
exact-rational certificate: in each of `60` cases for the mean radial excess `yMean`, a
nonnegative combination of valid linear rows contradicts the box of the normalized
variables. This file fixes the interface between the certificate data and the geometry:

* `Params`: the certificate parameters (the grid, the bands of Lemma AB and the proved chord
  conditions), as computable functions of an index;
* `Setting`: a configuration with the hypotheses of the contradiction argument
  (`n ≥ 10000` and `D ≤ (1/3 + 1/40) n`), with the derived annulus facts;
* `val`: the normalized variables `𝒜(g) = P(g²ρ²)/n²`, `ℛ(g) = R(g²ρ²)/n`, `D/n`, `1/n` and
  the band variables `W, U, V` of Lemma AB, as a function of a variable index;
* `box`: the box of the normalized variables.

`RationalFarkasRows` supplies the generic rational-to-integer row conversion.
`S4RowBuilder` selects the geometric rows, and the `S4Sound*` modules prove their soundness.

Variables: `𝒜(gᵢ) ↦ 2i`, `ℛ(gᵢ) ↦ 2i + 1` (`i < ng`), `D/n ↦ 2 ng`, `1/n ↦ 2 ng + 1`, and
for band `b < nb`: `W_b ↦ 2 ng + 2 + 3b`, `U_b ↦ 2 ng + 3 + 3b`, `V_b ↦ 2 ng + 4 + 3b`.
-/

@[expose] public section

namespace Esgk.S4

open Finset EuclideanGeometry

/-! ### Constants of the certificate -/

/-- The annulus parameter `sBar = 41821/50000` (`sBar² ≤ 1 - 12/40 - 4/10⁴`). -/
def sig : ℚ := 41821 / 50000

/-- The annulus width `W = 1 - sBar²`. -/
def wid : ℚ := 1 - sig * sig

/-- The upper bound `1/3 + 1/40` of `D/n` under the contradiction hypothesis. -/
def dbar : ℚ := 1 / 3 + 1 / 40

/-- The upper bound `1/10000` of `1/n`. -/
def eps : ℚ := 1 / 10000

/-! ### Certificate parameters and variables -/

/-- The certificate parameters. -/
structure Params where
  /-- the number of grid points -/
  ng : Nat
  /-- the grid point of an index -/
  g : Nat → ℚ
  /-- the number of bands of Lemma AB -/
  nb : Nat
  /-- the grid index of the threshold `λ` of a band -/
  bLam : Nat → Nat
  /-- the grid index of the lower edge of a band -/
  bLo : Nat → Nat
  /-- the grid index of the upper edge of a band -/
  bHi : Nat → Nat
  /-- the number of proved chord conditions -/
  nch : Nat
  /-- the proved chord conditions `(lo, hi, T)` -/
  ch : Nat → ℚ × ℚ × ℚ

/-- The variable `𝒜(gᵢ)`. -/
def aVar (i : Nat) : Nat := 2 * i

/-- The variable `ℛ(gᵢ)`. -/
def rVar (i : Nat) : Nat := 2 * i + 1

namespace Params

variable (P : Params)

/-- The variable `D/n`. -/
def dV : Nat := 2 * P.ng

/-- The variable `1/n`. -/
def eV : Nat := 2 * P.ng + 1

/-- The variable `W_b` (the number of triples of band `b`, over `n²`). -/
def wV (b : Nat) : Nat := 2 * P.ng + 2 + 3 * b

/-- The variable `U_b` (the base excess of band `b`, over `n²`). -/
def uV (b : Nat) : Nat := 2 * P.ng + 3 + 3 * b

/-- The variable `V_b` (the apex excess of band `b`, over `n²`). -/
def vV (b : Nat) : Nat := 2 * P.ng + 4 + 3 * b

/-- The number of variables. -/
def nv : Nat := 2 * P.ng + 2 + 3 * P.nb

/-- The squared grid point `gᵢ²`. -/
def sq (i : Nat) : ℚ := P.g i * P.g i

/-- The index is a grid index. -/
def ok (i : Nat) : Bool := Nat.blt i P.ng

/-- The index is a band index. -/
def okB (b : Nat) : Bool := Nat.blt b P.nb

end Params

/-! ### The configuration -/

/-- A configuration with the hypotheses of the contradiction argument for Theorem S4. -/
structure Setting (n : ℕ) where
  /-- the points -/
  p : Config n
  hp : Function.Injective p
  hgp : InGeneralPosition (Config.toFinset p)
  hn : 10000 ≤ n
  hD : (NumDistances p : ℝ) ≤ (1 / 3 + 1 / 40) * (n : ℝ)

namespace Setting

variable {n : ℕ} (S : Setting n)

/-- The annulus radius `ρ`. -/
noncomputable def ρ : ℝ := distanceAnnulusRadius S.p

/-- The centroid. -/
noncomputable def c : Point := configCentroid S.p

/-- `P(t)`: the number of ordered pairs of distinct points at squared distance at most `t`. -/
noncomputable def pairs (t : ℝ) : ℝ :=
  ∑ j, ((((univ : Finset (Fin n)).filter (fun q ↦ dist (S.p j) (S.p q) ^ 2 ≤ t)).card : ℝ) - 1)

/-- `R(t)`: the number of palette values `r` with `r² ≤ t`. -/
noncomputable def pal (t : ℝ) : ℝ :=
  (((OrderedDistanceValues S.p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ)

/-- The number `D` of distances. -/
noncomputable def D : ℝ := (NumDistancesOrdered S.p : ℝ)

/-- The radial excess `yᵢ = |pᵢ - c|²/ρ² - sBar²`. -/
noncomputable def y (i : Fin n) : ℝ := radialExcess S.p S.c S.ρ (sig : ℝ) i

/-- The mean radial excess `yMean`. -/
noncomputable def ybar : ℝ := (∑ i, S.y i) / n

/-- The triples of band `b` of Lemma AB. -/
noncomputable def bandTri (P : Params) (b : Nat) : Finset (Fin n × Fin n × Fin n) :=
  apexBandTriples S.p S.ρ ((P.g (P.bLam b) : ℝ) ^ 2) ((P.g (P.bLo b) : ℝ) ^ 2)
    ((P.g (P.bHi b) : ℝ) ^ 2)

/-- The band variables `W_b` (`r = 0`), `U_b` (`r = 1`) and `V_b` (`r = 2`), times `n²`. -/
noncomputable def bandCount (P : Params) (b r : Nat) : ℝ :=
  if r = 0 then ((S.bandTri P b).card : ℝ)
  else if r = 1 then ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2)
  else ∑ x ∈ S.bandTri P b, S.y x.1

/-- The chord condition `(lo, hi, T)`: every saturated incidence of radius `r` with
`lo²ρ² < r² ≤ hi²ρ²` has two of its points at squared distance at most `Tρ²`. -/
def ChordHolds (lo hi T : ℚ) : Prop :=
  ∀ ir ∈ SaturatedDistanceIncidences S.p, (lo : ℝ) ^ 2 * S.ρ ^ 2 < ir.2 ^ 2 →
    ir.2 ^ 2 ≤ (hi : ℝ) ^ 2 * S.ρ ^ 2 → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue S.p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue S.p ir.1 ir.2 ∧ a < b ∧
      dist (S.p a) (S.p b) ^ 2 ≤ (T : ℝ) * S.ρ ^ 2

theorem n_pos (S : Setting n) : 0 < n := by have := S.hn; omega

theorem hnR (S : Setting n) : (10000 : ℝ) ≤ n := by exact_mod_cast S.hn

theorem hcap : ∀ i r, (DistanceOutNeighborsAtValue S.p i r).card ≤ 3 :=
  distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular S.hp S.hgp.2

theorem hρ : 0 < S.ρ := distanceAnnulusRadius_pos S.hp (by have := S.hn; omega) S.hcap

theorem hρsq : S.ρ ^ 2 = distanceAnnulusRadiusSq S.p :=
  (distanceAnnulusRadius_bounds S.n_pos S.hcap).2.1

theorem hD_ordered : S.D ≤ (1 / 3 + 1 / 40) * (n : ℝ) := by
  have h := S.hD
  rw [numDistances_eq_numDistancesOrdered_of_injective S.hp] at h
  exact h

theorem n_le_three_D : (n : ℝ) ≤ 3 * S.D :=
  numPoints_le_three_mul_numDistancesOrdered_real S.hp S.hgp (by have := S.hn; omega)

theorem hhi (i : Fin n) : dist (S.p i) S.c ^ 2 ≤ S.ρ ^ 2 := by
  rw [S.hρsq]
  exact (thin_annulus_sq_of_noFourCocircular S.hp S.hgp.2 S.n_pos S.hD i).2

theorem sig_cast : ((sig : ℚ) : ℝ) = 41821 / 50000 := by
  norm_num [sig]

theorem hlo (i : Fin n) : (sig : ℝ) ^ 2 * S.ρ ^ 2 ≤ dist (S.p i) S.c ^ 2 := by
  have h := (thin_annulus_sq_of_noFourCocircular S.hp S.hgp.2 S.n_pos S.hD i).1
  rw [← S.hρsq] at h
  have h4n : 4 / (n : ℝ) ≤ 4 / 10000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) S.hnR
  have hσ : (sig : ℝ) ^ 2 ≤ 1 - 12 * (1 / 40 : ℝ) - 4 / (n : ℝ) := by
    rw [sig_cast]
    linarith
  have hρ2 : 0 ≤ S.ρ ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_right hσ hρ2
  change (sig : ℝ) ^ 2 * S.ρ ^ 2 ≤ dist (S.p i) (configCentroid S.p) ^ 2
  linarith

theorem hsum : ∑ i, (S.p i - S.c) = 0 := sum_sub_configCentroid S.p S.n_pos

end Setting

/-! ### The valuation -/

/-- The normalized variables of the certificate, by variable index. -/
noncomputable def val {n : ℕ} (P : Params) (S : Setting n) (k : Nat) : ℝ :=
  if k < 2 * P.ng then
    if k % 2 = 0 then S.pairs ((P.g (k / 2) : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n)
    else S.pal ((P.g (k / 2) : ℝ) ^ 2 * S.ρ ^ 2) / n
  else if k = 2 * P.ng then S.D / n
  else if k = 2 * P.ng + 1 then 1 / n
  else S.bandCount P ((k - (2 * P.ng + 2)) / 3) ((k - (2 * P.ng + 2)) % 3) / ((n : ℝ) * n)

section Valuation

variable {n : ℕ} (P : Params) (S : Setting n)

theorem val_aVar {i : Nat} (hi : i < P.ng) :
    val P S (aVar i) = S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n) := by
  unfold val aVar
  rw [ite_eq_left (by omega), ite_eq_left (by omega), show 2 * i / 2 = i by omega]

theorem val_rVar {i : Nat} (hi : i < P.ng) :
    val P S (rVar i) = S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) / n := by
  unfold val rVar
  rw [ite_eq_left (by omega), ite_eq_right (by omega), show (2 * i + 1) / 2 = i by omega]

theorem val_dV : val P S P.dV = S.D / n := by
  unfold val Params.dV
  rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem val_eV : val P S P.eV = 1 / n := by
  unfold val Params.eV
  rw [ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl]

theorem val_wV (b : Nat) :
    val P S (P.wV b) = ((S.bandTri P b).card : ℝ) / ((n : ℝ) * n) := by
  unfold val Params.wV
  rw [ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega),
    show (2 * P.ng + 2 + 3 * b - (2 * P.ng + 2)) / 3 = b by omega,
    show (2 * P.ng + 2 + 3 * b - (2 * P.ng + 2)) % 3 = 0 by omega]
  simp [Setting.bandCount]

theorem val_uV (b : Nat) :
    val P S (P.uV b) = (∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2)) / ((n : ℝ) * n) := by
  unfold val Params.uV
  rw [ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega),
    show (2 * P.ng + 3 + 3 * b - (2 * P.ng + 2)) / 3 = b by omega,
    show (2 * P.ng + 3 + 3 * b - (2 * P.ng + 2)) % 3 = 1 by omega]
  simp [Setting.bandCount]

theorem val_vV (b : Nat) :
    val P S (P.vV b) = (∑ x ∈ S.bandTri P b, S.y x.1) / ((n : ℝ) * n) := by
  unfold val Params.vV
  rw [ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega),
    show (2 * P.ng + 4 + 3 * b - (2 * P.ng + 2)) / 3 = b by omega,
    show (2 * P.ng + 4 + 3 * b - (2 * P.ng + 2)) % 3 = 2 by omega]
  simp [Setting.bandCount]

end Valuation

end Esgk.S4

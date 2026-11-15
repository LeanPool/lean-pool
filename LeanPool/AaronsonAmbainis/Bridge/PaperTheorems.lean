/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.RowDefs
public import LeanPool.AaronsonAmbainis.Level.Increments
public import LeanPool.AaronsonAmbainis.Average.Influence
public import LeanPool.AaronsonAmbainis.Bridge.PrintedAA

/-!
# The row bound, the statements on functions with rows, and the main theorem

The propositions of `Statements.lean` and `RowDefs.lean` write the condition of a row of a real
function "for all `x, y`" with the difference set `Δ(x,y)`, they state the bounds without square
roots, and the proposition `MainTheorem` carries the hypothesis `0 < variance f`. The paper
writes the condition "for every `S ⊆ [n]`" with `x^S` (Definition 2.3), it states the bounds with
the powers `3/2` and `5/2` of the variance as well, and its main theorem assumes `n ≥ 1` and
`d ≥ 1` in place of positive variance. The following comparisons are made here:

* `rows_iff_printed` — a family of rows of cost at most `K` in the form of the propositions is
  the same as a row of cost at most `K`, in the sense of Definition 2.3, at every point;
* `rowBoundPM_iff_printed : RowBoundPM ↔ RowBoundPMPrinted` (the row bound, Theorem 6.8 of the
  paper);
* `meanIncrement_iff_printed : MeanIncrementBound ↔ MeanIncrementPrinted` (the bound for the mean
  absolute increments of a function with a row of cost at most `K` at every point, Theorem 7.10,
  with all its assertions: `K > 0`, the inequality `Var(f)^3 ≤ 36 K^4 L_j(f)^2` and the bound
  `L_j(f) ≥ Var(f)^{3/2} / (6 K²)`);
* `influence_iff_printed : InfluenceBound ↔ InfluencePrinted` (the bound for the influences of
  such a function, Theorem 8.3, with all its assertions: `0 < L(f) ≤ K`, the inequality
  `3 Var(f)^5 ≤ 3125 L(f)² K^4 Inf_j(f)^2` and the bounds
  `Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / (L(f) K²) ≥ (√15 / 125) Var(f)^{5/2} / K³`);
* `meanIncrementDegree_iff_printed : MeanIncrementDegreeBound ↔ MeanIncrementDegreePrinted` (the
  bound for the mean absolute increments of a bounded function of degree at most `d`,
  Corollary 7.11: `d ≥ 1` and `L_j(f) ≥ Var(f)^{3/2} / (6 π^4 d^4)`);
* `mainTheorem_iff_printed : MainTheorem ↔ MainTheoremPrinted` (the main theorem as stated in
  the paper, Theorem 1.1: `n ≥ 1`, `d ≥ 1`, no hypothesis on the variance, and the bound
  `(√15 / (500 π^4)) Var(f)^{5/2} / d^6`).

Nothing here says that any of these statements holds. The propositions are proved in
`Chain.lean`.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Rows -/

/-- Rows of cost at most `K` in the two forms: a family `a` with
`|f(x) − f(y)| ≤ ∑_{j ∈ Δ(x,y)} a x j` for all `x, y`, as in the propositions of
`Statements.lean`; and, for every `x`, a vector `a ∈ [0,∞)^n` with `‖a‖ ≤ K` and
`|f(x) − f(x^S)| ≤ a(S)` for every `S ⊆ [n]`, as in Definition 2.3 of the paper. -/
theorem rows_iff_printed (f : Cube ι → ℝ) (K : ℝ) :
    (∃ a : Cube ι → ι → ℝ, (∀ x j, 0 ≤ a x j) ∧ (∀ x, ∑ j, a x j ≤ K) ∧
        ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) ↔
      ∀ x : Cube ι, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ K ∧
        ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ j ∈ S, a j := by
  constructor
  · rintro ⟨a, ha0, ha1, ha2⟩ x
    refine ⟨a x, ha0 x, ha1 x, fun S => ?_⟩
    have h2 := ha2 x (flipSet x S)
    rw [diffSet_flipSet] at h2
    exact h2
  · intro h
    choose a ha0 ha1 ha2 using h
    refine ⟨a, ha0, ha1, fun x y => ?_⟩
    have h2 := ha2 x (diffSet x y)
    rw [flipSet_diffSet] at h2
    exact h2

/-! ### The row bound (Theorem 6.8) -/

/-- The row bound as stated in the paper (Theorem 6.8), with Definition 2.3 of a row written out:
for every `x` there is `a ∈ [0,∞)^n` with `‖a‖ ≤ π² d²` and `|f(x) − f(x^S)| ≤ a(S)` for every
`S ⊆ [n]` (`f` with values in `[-1,1]` and of degree at most `d`). -/
def RowBoundPMPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
    ∀ x : Cube ι, ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ i ∈ S, a i

theorem rowBoundPM_iff_printed : RowBoundPM ↔ RowBoundPMPrinted :=
  ⟨fun h ι _ _ d f hbd hdeg => (rows_iff_printed f _).mp (h ι d f hbd hdeg),
    fun h ι _ _ d f hbd hdeg => (rows_iff_printed f _).mpr (h ι d f hbd hdeg)⟩

/-! ### Functions with a row of cost at most `K` at every point (Theorem 7.10, Theorem 8.3) -/

/-- The bound for the mean absolute increments as stated in the paper (Theorem 7.10), with
Definition 2.3 of a row written out: if `Var(f) > 0` and for every `x` there is `a_x ∈ [0,∞)^n`
with `‖a_x‖ ≤ K` and `|f(x) − f(x^S)| ≤ a_x(S)` for all `S`, then `K > 0`, and some coordinate
`j` has `Var(f)^3 ≤ 36 K^4 L_j(f)^2` and `L_j(f) ≥ Var(f)^{3/2} / (6 K²)`. The power
`Var(f)^{3/2}` is written `Var(f) √Var(f)`. (The assertion `n ≥ 1` of Theorem 7.10 is contained
in the existence of a coordinate.) -/
def MeanIncrementPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ),
    (∀ x : Cube ι, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ K ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ j ∈ S, a j) →
    0 < variance f →
    0 < K ∧ ∃ j, variance f ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr f j ^ 2 ∧
      variance f * Real.sqrt (variance f) / (6 * K ^ 2) ≤ meanAbsIncr f j

theorem meanIncrement_iff_printed : MeanIncrementBound ↔ MeanIncrementPrinted := by
  constructor
  · intro h ι _ _ f K hrow hvar
    obtain ⟨a, ha0, ha1, ha2⟩ := (rows_iff_printed f K).mpr hrow
    have hK : 0 < K := Level.cost_pos ha0 ha1 ha2 hvar
    obtain ⟨j, hj⟩ := h ι f K a ha0 ha1 ha2 hvar
    refine ⟨hK, j, hj, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    exact ((Level.cube_le_iff_mul_sqrt_le hvar.le (Level.meanAbsIncr_nonneg f j)).mp hj).trans
      (le_of_eq (by ring))
  · intro h ι _ _ f K a ha0 ha1 ha2 hvar
    obtain ⟨-, j, hj, -⟩ := h ι f K ((rows_iff_printed f K).mp ⟨a, ha0, ha1, ha2⟩) hvar
    exact ⟨j, hj⟩

/-- The arithmetic of the printed form of the bound for the influences: for `V, K > 0`,
`0 ≤ L ≤ K` and `I ≥ 0`, the inequality `3 V^5 ≤ 3125 L² K^4 I²` gives `L > 0`,
`I ≥ (√15 / 125) V^{5/2} / (L K²)` and `I ≥ (√15 / 125) V^{5/2} / K³`. -/
theorem influence_printed_arith {V K L I : ℝ} (hV : 0 < V) (hK : 0 < K) (hL0 : 0 ≤ L)
    (hLK : L ≤ K) (hI : 0 ≤ I) (h : 3 * V ^ 5 ≤ 3125 * L ^ 2 * K ^ 4 * I ^ 2) :
    0 < L ∧ Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / (L * K ^ 2) ≤ I ∧
      Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / K ^ 3 ≤ I := by
  have hL : 0 < L := by
    rcases hL0.eq_or_lt with h0 | hpos
    · exfalso
      rw [← h0] at h
      have h5 : 0 < V ^ 5 := pow_pos hV 5
      have e : 3125 * (0 : ℝ) ^ 2 * K ^ 4 * I ^ 2 = 0 := by ring
      rw [e] at h
      linarith
    · exact hpos
  have h1 := (Average.pow_le_iff_sqrt_mul_le hV.le hL.le hI).mp h
  have hq : Real.sqrt 15 / 125 * (V ^ 2 * Real.sqrt V) / (L * K ^ 2) ≤ I := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  refine ⟨hL, hq, le_trans ?_ hq⟩
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc L * K ^ 2 ≤ K * K ^ 2 := mul_le_mul_of_nonneg_right hLK (sq_nonneg K)
    _ = K ^ 3 := by ring

/-- The bound for the influences as stated in the paper (Theorem 8.3), with Definition 2.3 of a
row written out: if `Var(f) > 0` and for every `x` there is `a_x ∈ [0,∞)^n` with `‖a_x‖ ≤ K` and
`|f(x) − f(x^S)| ≤ a_x(S)` for all `S`, then `0 < L(f) ≤ K`, where `L(f) = ∑_k L_k(f)`, and some
coordinate `j` has `3 Var(f)^5 ≤ 3125 L(f)² K^4 Inf_j(f)^2`,
`Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / (L(f) K²)` and `Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / K³`.
The power `Var(f)^{5/2}` is written `Var(f)² √Var(f)`. (The assertion `n ≥ 1` of Theorem 8.3 is
contained in the existence of a coordinate.) -/
def InfluencePrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ),
    (∀ x : Cube ι, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ K ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ j ∈ S, a j) →
    0 < variance f →
    0 < ∑ k, meanAbsIncr f k ∧ ∑ k, meanAbsIncr f k ≤ K ∧
      ∃ j, 3 * variance f ^ 5 ≤ 3125 * (∑ k, meanAbsIncr f k) ^ 2 * K ^ 4 * inflR f j ^ 2 ∧
        Real.sqrt 15 / 125 * (variance f ^ 2 * Real.sqrt (variance f))
            / ((∑ k, meanAbsIncr f k) * K ^ 2) ≤ inflR f j ∧
        Real.sqrt 15 / 125 * (variance f ^ 2 * Real.sqrt (variance f)) / K ^ 3 ≤ inflR f j

theorem influence_iff_printed : InfluenceBound ↔ InfluencePrinted := by
  constructor
  · intro h ι _ _ f K hrow hvar
    obtain ⟨a, ha0, ha1, ha2⟩ := (rows_iff_printed f K).mpr hrow
    obtain ⟨j, hj⟩ := h ι f K a ha0 ha1 ha2 hvar
    have hLK : ∑ k, meanAbsIncr f k ≤ K := Level.sum_meanAbsIncr_le_cost ha1 ha2
    obtain ⟨hL, h1, h2⟩ := influence_printed_arith hvar (Level.cost_pos ha0 ha1 ha2 hvar)
      (Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k) hLK (Level.inflR_nonneg f j) hj
    exact ⟨hL, hLK, j, hj, h1, h2⟩
  · intro h ι _ _ f K a ha0 ha1 ha2 hvar
    obtain ⟨-, -, j, hj, -, -⟩ := h ι f K ((rows_iff_printed f K).mp ⟨a, ha0, ha1, ha2⟩) hvar
    exact ⟨j, hj⟩

/-! ### Bounded functions of degree at most `d` (Corollary 7.11) -/

/-- The bound for the mean absolute increments of a bounded function of degree at most `d` as
stated in the paper (Corollary 7.11): if `f` has values in `[-1,1]`, degree at most `d` and
`Var(f) > 0`, then `d ≥ 1`, and some coordinate `j` has `L_j(f) ≥ Var(f)^{3/2} / (6 π^4 d^4)`.
The power `Var(f)^{3/2}` is written `Var(f) √Var(f)`. (The assertion `n ≥ 1` of Corollary 7.11
is contained in the existence of a coordinate.) -/
def MeanIncrementDegreePrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    1 ≤ d ∧ ∃ j, variance f * Real.sqrt (variance f) / (6 * Real.pi ^ 4 * (d : ℝ) ^ 4)
      ≤ meanAbsIncr f j

theorem meanIncrementDegree_iff_printed :
    MeanIncrementDegreeBound ↔ MeanIncrementDegreePrinted := by
  constructor
  · intro h ι _ _ d f hbd hdeg hvar
    obtain ⟨hd, -⟩ := aa_hyps_force hdeg hvar
    have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hpi : 0 < Real.pi := Real.pi_pos
    obtain ⟨j, hj⟩ := h ι d f hbd hdeg hvar
    refine ⟨hd, j, ?_⟩
    have h' : variance f ^ 3 ≤ 36 * (Real.pi ^ 2 * (d : ℝ) ^ 2) ^ 4 * meanAbsIncr f j ^ 2 :=
      hj.trans (le_of_eq (by ring))
    rw [div_le_iff₀ (by positivity)]
    exact ((Level.cube_le_iff_mul_sqrt_le hvar.le (Level.meanAbsIncr_nonneg f j)).mp h').trans
      (le_of_eq (by ring))
  · intro h ι _ _ d f hbd hdeg hvar
    obtain ⟨hd, j, hj⟩ := h ι d f hbd hdeg hvar
    have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hpi : 0 < Real.pi := Real.pi_pos
    refine ⟨j, ?_⟩
    rw [div_le_iff₀ (by positivity)] at hj
    have h' : variance f * Real.sqrt (variance f)
        ≤ 6 * (Real.pi ^ 2 * (d : ℝ) ^ 2) ^ 2 * meanAbsIncr f j := hj.trans (le_of_eq (by ring))
    exact ((Level.cube_le_iff_mul_sqrt_le hvar.le (Level.meanAbsIncr_nonneg f j)).mpr h').trans
      (le_of_eq (by ring))

/-! ### The main theorem (Theorem 1.1) -/

/-- The main theorem as stated in the paper (Theorem 1.1): for `n ≥ 1` (a nonempty index type)
and `d ≥ 1`, every `f : {-1,1}^n → [-1,1]` of degree at most `d` has a coordinate `j` with
`Inf_j(f) ≥ (√15 / (500 π^4)) Var(f)^{5/2} / d^6`. The power `Var(f)^{5/2}` is written
`Var(f)² √Var(f)`. -/
def MainTheoremPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (d : ℕ), 1 ≤ d →
    ∀ f : Cube ι → ℝ, (∀ x, |f x| ≤ 1) → HasDegreeLE f d →
    ∃ j, Real.sqrt 15 / (500 * Real.pi ^ 4) * (variance f ^ 2 * Real.sqrt (variance f))
      / (d : ℝ) ^ 6 ≤ inflR f j

theorem mainTheoremPrinted_of_mainTheorem (h : MainTheorem) : MainTheoremPrinted := by
  intro ι _ _ hne d hd f hbd hdeg
  have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rcases (Level.variance_nonneg f).lt_or_eq with hpos | hzero
  · obtain ⟨j, hj⟩ := h ι d f hbd hdeg hpos
    have h1 := (sqrt_form_iff (c₁ := 1) (c₂ := 500) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hpos.le hD (Level.inflR_nonneg f j)).mpr hj
    rw [one_mul] at h1
    exact ⟨j, h1⟩
  · obtain ⟨j⟩ := hne
    refine ⟨j, ?_⟩
    rw [← hzero, zero_pow two_ne_zero, zero_mul, mul_zero, zero_div]
    exact Level.inflR_nonneg f j

theorem mainTheorem_of_mainTheoremPrinted (h : MainTheoremPrinted) : MainTheorem := by
  intro ι _ _ d f hbd hdeg hpos
  obtain ⟨hd, hne⟩ := aa_hyps_force hdeg hpos
  have : Nonempty ι := hne
  have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨j, hj⟩ := h ι d hd f hbd hdeg
  refine ⟨j, ?_⟩
  rw [← one_mul (Real.sqrt 15)] at hj
  exact (sqrt_form_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hpos.le hD
    (Level.inflR_nonneg f j)).mp hj

theorem mainTheorem_iff_printed : MainTheorem ↔ MainTheoremPrinted :=
  ⟨mainTheoremPrinted_of_mainTheorem, mainTheorem_of_mainTheoremPrinted⟩

end AaronsonAmbainis.Bridge

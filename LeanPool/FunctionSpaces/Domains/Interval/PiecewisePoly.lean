/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.LintegralForm
public import LeanPool.FunctionSpaces.Domains.Interval.Polynomials
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Synthesis
public import Mathlib.Algebra.Order.Floor.Semifield

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Dyadic piecewise polynomials on `[0, 1]`

A **piecewise polynomial of level `k` and degree `< r`** agrees on each dyadic interval
`I_{k,n} = [n 2^(-k), (n + 1) 2^(-k))` with a polynomial of degree `< r`
(`Interval.ppFun`).  Their classes in `L_p[0, 1]` form subspaces `V_k` increasing in `k`
(`Interval.ppSpace`), and the scheme with approximants `V_{⌊log₂ n⌋}` of complexity `n`
(`Interval.ppScheme`, an `ApproximationScheme.ofMonotoneSubmodules`) has `V_k` as approximants
of complexity `2^k`.

This file sets up the spaces, the bookkeeping for the pieces (on `I_{k,m}` a piecewise
polynomial is the polynomial `Q_m`, and `0` beyond `[0, 1)`, `Interval.ppFun_eq_polyFun`) and
for integrals over unions of dyadic intervals (`Interval.lintegral_Icc_le_sum`,
`Interval.lintegral_Icc_le_sum_dyadicIco`, `Interval.lintegral_unit_eq_sum_dyadicIco`); a dyadic
interval is the disjoint union of its two halves (`Interval.dyadicIco_eq_union`,
`Interval.disjoint_dyadicIco_halves`). A piecewise polynomial is bounded
(`Interval.exists_norm_ppFun_le`) and integrable on `[0, 1]` (`Interval.integrableOn_ppFun`).
Jackson's inequality is in `FunctionSpaces.Domains.Interval.PiecewiseJackson`, the inverse
inequality and the identification of the approximation spaces in
`FunctionSpaces.Domains.Interval.PiecewiseInverse`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction ComplexConjugate
open ENNReal (dyadicWeight)

namespace Interval

/-- Lebesgue measure on `[0, 1]`. -/
noncomputable abbrev unitVol : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- Lebesgue measure on `[0, 1]` is a probability measure. -/
instance isProbabilityMeasure_unitVol : IsProbabilityMeasure unitVol :=
  ⟨by simp [unitVol, Real.volume_Icc]⟩

/-- Almost every point of `[0, 1]` lies in `[0, 1)`. -/
theorem ae_mem_Ico_unitVol : ∀ᵐ x ∂unitVol, x ∈ Ico (0 : ℝ) 1 := by
  rw [unitVol, ← Measure.restrict_congr_set Ico_ae_eq_Icc]
  exact ae_restrict_mem measurableSet_Ico

/-- The dyadic interval `I_{k,n} = [n 2^(-k), (n + 1) 2^(-k))`. -/
noncomputable def dyadicIco (k n : ℕ) : Set ℝ := Ico ((n : ℝ) / 2 ^ k) ((n + 1) / 2 ^ k)

/-- Dyadic intervals are measurable. -/
theorem measurableSet_dyadicIco (k n : ℕ) : MeasurableSet (dyadicIco k n) := measurableSet_Ico

/-- `x ∈ I_{k,n}` iff `n ≤ 2^k x < n + 1`. -/
theorem mem_dyadicIco {k n : ℕ} {x : ℝ} :
    x ∈ dyadicIco k n ↔ (n : ℝ) ≤ 2 ^ k * x ∧ 2 ^ k * x < n + 1 := by
  have h : (0 : ℝ) < 2 ^ k := by positivity
  rw [dyadicIco, mem_Ico, div_le_iff₀ h, lt_div_iff₀ h, mul_comm x]

/-- Dyadic intervals of one level are disjoint. -/
theorem eq_of_mem_dyadicIco {k n m : ℕ} {x : ℝ} (hn : x ∈ dyadicIco k n)
    (hm : x ∈ dyadicIco k m) : n = m := by
  rw [mem_dyadicIco] at hn hm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith [hn.2, hm.1]
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith [hm.2, hn.1]

/-- A point of `[0, 1)` lies in the dyadic interval `I_{k, ⌊2^k x⌋}`, of index `< 2^k`. -/
theorem mem_dyadicIco_floor {k : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    x ∈ dyadicIco k ⌊2 ^ k * x⌋₊ ∧ ⌊2 ^ k * x⌋₊ < 2 ^ k := by
  have h0 : 0 ≤ 2 ^ k * x := mul_nonneg (by positivity) hx.1
  refine ⟨mem_dyadicIco.2 ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩, ?_⟩
  have : 2 ^ k * x < (2 ^ k : ℕ) := by
    push_cast
    exact mul_lt_of_lt_one_right (by positivity) hx.2
  exact (Nat.floor_lt h0).2 this

/-- The parent dyadic interval: `⌊2^k x⌋ = ⌊2^(k+1) x⌋ / 2`. -/
theorem floor_two_pow_succ_div (k : ℕ) (x : ℝ) :
    ⌊2 ^ (k + 1) * x⌋₊ / 2 = ⌊2 ^ k * x⌋₊ := by
  rw [← Nat.floor_div_natCast]
  congr 1
  push_cast
  ring

/-- The **piecewise polynomial** `∑_n 1_{I_{k,n}} Q_n` of level `k`. -/
noncomputable def ppFun (k : ℕ) (Q : ℕ → ℂ[X]) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (2 ^ k), (dyadicIco k n).indicator (polyFun (Q n)) x

/-- On `I_{k,n}` the piecewise polynomial is `Q_n`. -/
theorem ppFun_eq_of_mem {k n : ℕ} (Q : ℕ → ℂ[X]) {x : ℝ} (hn : n < 2 ^ k)
    (hx : x ∈ dyadicIco k n) : ppFun k Q x = polyFun (Q n) x := by
  rw [ppFun, Finset.sum_eq_single n (fun m _ hmn => indicator_of_notMem
    (fun hm => hmn (eq_of_mem_dyadicIco hm hx)) _)
    (fun h => absurd (Finset.mem_range.2 hn) h), indicator_of_mem hx]

/-- Piecewise polynomials are measurable. -/
theorem measurable_ppFun (k : ℕ) (Q : ℕ → ℂ[X]) : Measurable (ppFun k Q) :=
  Finset.measurable_sum _ fun n _ =>
    (measurable_polyFun (Q n)).indicator (measurableSet_dyadicIco k n)

/-- Piecewise polynomials lie in `L_p[0, 1]`. -/
theorem memLp_ppFun (k : ℕ) (Q : ℕ → ℂ[X]) (p : ℝ≥0∞) : MemLp (ppFun k Q) p unitVol := by
  have : ppFun k Q = ∑ n ∈ Finset.range (2 ^ k), (dyadicIco k n).indicator (polyFun (Q n)) := by
    funext x; rw [ppFun, Finset.sum_apply]
  rw [this]
  exact memLp_finsetSum' _ fun n _ =>
    (memLp_polyFun (Q n) p 0 1).indicator (measurableSet_dyadicIco k n).nullMeasurableSet

/-- Piecewise polynomials are additive in the pieces. -/
theorem ppFun_add (k : ℕ) (Q Q' : ℕ → ℂ[X]) :
    ppFun k (Q + Q') = ppFun k Q + ppFun k Q' := by
  funext x
  simp only [ppFun, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : x ∈ dyadicIco k n
  · simp [indicator_of_mem hx, polyFun]
  · simp [indicator_of_notMem hx]

/-- Piecewise polynomials are homogeneous in the pieces. -/
theorem ppFun_const_mul (k : ℕ) (c : ℂ) (Q : ℕ → ℂ[X]) :
    ppFun k (fun n => C c * Q n) = fun x => c * ppFun k Q x := by
  funext x
  simp only [ppFun, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : x ∈ dyadicIco k n
  · simp [indicator_of_mem hx, polyFun]
  · simp [indicator_of_notMem hx]

/-- The zero polynomial. -/
theorem polyFun_zero : polyFun 0 = 0 := funext fun x => by simp [polyFun]

/-- The piecewise polynomials of level `k` with zero pieces vanish. -/
theorem ppFun_zero (k : ℕ) : ppFun k 0 = 0 := by
  funext x
  simp [ppFun, polyFun_zero]

/-- Piecewise polynomials are additive in the pieces, for finite sums. -/
theorem ppFun_sum {ι : Type*} (k : ℕ) (s : Finset ι) (Q : ι → ℕ → ℂ[X]) :
    ppFun k (∑ i ∈ s, Q i) = ∑ i ∈ s, ppFun k (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ppFun_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ppFun_add, ih]

/-- The dyadic intervals `I_{k,n}`, `n < 2^k`, lie in `[0, 1)`. -/
theorem dyadicIco_subset {k n : ℕ} (hn : n < 2 ^ k) : dyadicIco k n ⊆ Ico 0 1 := by
  intro x hx
  rw [mem_dyadicIco] at hx
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hn' : (n : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.succ_le_of_lt hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · nlinarith
  · nlinarith

/-- A piecewise polynomial vanishes outside `[0, 1)`. -/
theorem ppFun_eq_zero {k : ℕ} (Q : ℕ → ℂ[X]) {x : ℝ} (hx : x ∉ Ico (0 : ℝ) 1) :
    ppFun k Q x = 0 :=
  Finset.sum_eq_zero fun _ hn =>
    indicator_of_notMem (fun h => hx (dyadicIco_subset (Finset.mem_range.1 hn) h)) _

/-- **Piecewise polynomials are bounded**: for every level `k` and pieces `Q` there is `M` with
`‖ppFun k Q x‖ ≤ M` for all `x ∈ ℝ`, since each piece is a polynomial on a subinterval of the
compact interval `[0, 1]`. -/
theorem exists_norm_ppFun_le (k : ℕ) (Q : ℕ → ℂ[X]) : ∃ M : ℝ, ∀ x, ‖ppFun k Q x‖ ≤ M := by
  choose M hM using fun n : ℕ =>
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (continuous_polyFun (Q n)).continuousOn
  refine ⟨∑ n ∈ Finset.range (2 ^ k), M n, fun x => ?_⟩
  rw [ppFun]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  by_cases hx : x ∈ dyadicIco k n
  · rw [indicator_of_mem hx]
    exact hM n x (Ico_subset_Icc_self (dyadicIco_subset (Finset.mem_range.1 hn) hx))
  · rw [indicator_of_notMem hx, norm_zero]
    exact (norm_nonneg _).trans (hM n 0 ⟨le_rfl, zero_le_one⟩)

/-- Piecewise polynomials are integrable on `[0, 1]`. -/
theorem integrableOn_ppFun (k : ℕ) (Q : ℕ → ℂ[X]) : IntegrableOn (ppFun k Q) (Icc (0 : ℝ) 1) :=
  memLp_one_iff_integrable.1 (memLp_ppFun k Q 1)

/-- **Refinement of piecewise polynomials, everywhere**: the pieces `Q_{⌊n/2⌋}` of level `k + 1`
give the same function as the pieces `Q_n` of level `k`, on all of `ℝ`. -/
theorem ppFun_refine_eq (k : ℕ) (Q : ℕ → ℂ[X]) :
    ppFun (k + 1) (fun n => Q (n / 2)) = ppFun k Q := by
  funext x
  by_cases hx : x ∈ Ico (0 : ℝ) 1
  · obtain ⟨h1, h1'⟩ := mem_dyadicIco_floor (k := k + 1) hx
    obtain ⟨h2, h2'⟩ := mem_dyadicIco_floor (k := k) hx
    rw [ppFun_eq_of_mem _ h1' h1, ppFun_eq_of_mem _ h2' h2, floor_two_pow_succ_div]
  · rw [ppFun_eq_zero _ hx, ppFun_eq_zero _ hx]

/-- **Refinement**: a piecewise polynomial of level `k` is one of level `k + 1` with the pieces
`Q_{⌊n/2⌋}`, almost everywhere on `[0, 1]` (`Interval.ppFun_refine_eq` holds everywhere). -/
theorem ppFun_refine (k : ℕ) (Q : ℕ → ℂ[X]) :
    ppFun (k + 1) (fun n => Q (n / 2)) =ᵐ[unitVol] ppFun k Q :=
  Filter.EventuallyEq.of_eq (ppFun_refine_eq k Q)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The space `V_k` of **piecewise polynomials of level `k` and degree `< r`** in `L_p[0, 1]`. -/
noncomputable def ppSpace (r k : ℕ) : Submodule ℝ (Lp ℂ p unitVol) where
  carrier := {g | ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧
    (g : ℝ → ℂ) =ᵐ[unitVol] ppFun k Q}
  add_mem' := by
    rintro g g' ⟨Q, hQ, hg⟩ ⟨Q', hQ', hg'⟩
    refine ⟨Q + Q', fun n => Submodule.add_mem _ (hQ n) (hQ' n), ?_⟩
    filter_upwards [Lp.coeFn_add g g', hg, hg'] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ppFun_add, Pi.add_apply]
  zero_mem' := ⟨0, fun n => Submodule.zero_mem _, by
    filter_upwards [Lp.coeFn_zero ℂ p unitVol] with x hx
    rw [hx, ppFun_zero]⟩
  smul_mem' := by
    rintro c g ⟨Q, hQ, hg⟩
    refine ⟨fun n => C (c : ℂ) * Q n, fun n => ?_, ?_⟩
    · change C (c : ℂ) * Q n ∈ degreeLT ℂ r
      rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (hQ n)
    · filter_upwards [Lp.coeFn_smul c g, hg] with x h1 h2
      rw [h1, Pi.smul_apply, h2, ppFun_const_mul, Complex.real_smul]

omit [Fact (1 ≤ p)] in
/-- The spaces of piecewise polynomials increase with the level. -/
theorem ppSpace_mono (r : ℕ) : Monotone (ppSpace p r) := by
  refine monotone_nat_of_le_succ fun k g hg => ?_
  obtain ⟨Q, hQ, hgQ⟩ := hg
  exact ⟨fun n => Q (n / 2), fun n => hQ _, hgQ.trans (ppFun_refine k Q).symm⟩

variable (p) in
/-- The **scheme of dyadic piecewise polynomials** of degree `< r` in `L_p[0, 1]`: `{0}` at
complexity `0` and `V_{⌊log₂ n⌋}` at complexity `n ≥ 1`. -/
noncomputable def ppScheme (r : ℕ) : ApproximationScheme (Lp ℂ p unitVol) :=
  ApproximationScheme.ofMonotoneSubmodules (ppSpace p r) (ppSpace_mono r)

/-- The approximants of complexity `0` are `{0}`. -/
theorem mem_ppScheme_zero {r : ℕ} {g : Lp ℂ p unitVol} : g ∈ ppScheme p r 0 ↔ g = 0 :=
  ApproximationScheme.mem_ofMonotoneSubmodules_zero

/-- The approximants of complexity `n ≥ 1` are the piecewise polynomials of level `⌊log₂ n⌋`. -/
theorem mem_ppScheme {r n : ℕ} (hn : n ≠ 0) {g : Lp ℂ p unitVol} :
    g ∈ ppScheme p r n ↔ g ∈ ppSpace p r (Nat.log 2 n) :=
  ApproximationScheme.mem_ofMonotoneSubmodules hn

/-- The approximants of complexity `2^k` are the piecewise polynomials of level `k`. -/
theorem mem_ppScheme_two_pow {r k : ℕ} {g : Lp ℂ p unitVol} :
    g ∈ ppScheme p r (2 ^ k) ↔ g ∈ ppSpace p r k :=
  ApproximationScheme.mem_ofMonotoneSubmodules_two_pow

/-- The piecewise polynomial scheme is linear. -/
theorem ppScheme_isLinear (r : ℕ) : (ppScheme p r).IsLinear :=
  ApproximationScheme.isLinear_ofMonotoneSubmodules _ _

/-- **Integrals over a union of intervals**: `∫_{[u, u + mL]} G ≤ ∑_{n < m} ∫_{[u + nL, u +
(n+1)L]} G`
for `L ≥ 0`. -/
theorem lintegral_Icc_le_sum (G : ℝ → ℝ≥0∞) (u : ℝ) {L : ℝ} (hL : 0 ≤ L) (m : ℕ) :
    ∫⁻ x in Icc u (u + m * L), G x ≤
      ∑ n ∈ Finset.range m, ∫⁻ x in Icc (u + n * L) (u + (n + 1) * L), G x := by
  induction m with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, Finset.range_zero, Finset.sum_empty]
    rw [Icc_self, setLIntegral_measure_zero _ _ (Real.volume_singleton)]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hsplit : Icc u (u + ((m + 1 : ℕ) : ℝ) * L) =
        Icc u (u + m * L) ∪ Icc (u + m * L) (u + (m + 1) * L) := by
      push_cast
      exact (Icc_union_Icc_eq_Icc (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
        (by nlinarith)).symm
    rw [hsplit]
    exact (lintegral_union_le _ _ _).trans (add_le_add ih le_rfl)

/-- **Integrals over a union of intervals, reverse inequality**: for measurable `G` and `L ≥ 0`,
`∑_{n < m} ∫_{[u + nL, u + (n+1)L]} G ≤ ∫_{[u, u + mL]} G`, the intervals meeting in single
points. -/
theorem sum_le_lintegral_Icc {G : ℝ → ℝ≥0∞} (u : ℝ) {L : ℝ} (hL : 0 ≤ L) (m : ℕ) :
    ∑ n ∈ Finset.range m, ∫⁻ x in Icc (u + n * L) (u + (n + 1) * L), G x ≤
      ∫⁻ x in Icc u (u + m * L), G x := by
  have hIco : ∀ a b : ℝ, ∫⁻ x in Icc a b, G x = ∫⁻ x in Ico a b, G x := fun a b =>
    (setLIntegral_congr Ico_ae_eq_Icc).symm
  simp_rw [hIco]
  refine le_of_eq ?_
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hsplit : Ico u (u + ((m + 1 : ℕ) : ℝ) * L) =
        Ico u (u + m * L) ∪ Ico (u + m * L) (u + (m + 1) * L) := by
      push_cast
      exact (Ico_union_Ico_eq_Ico (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
        (by nlinarith)).symm
    rw [hsplit, lintegral_union measurableSet_Ico (Ico_disjoint_Ico_same.mono_left
      (fun _ h => h) |>.mono_right (fun _ h => h))]

/-- The closed intervals `[0 + n 2^(-k), 0 + (n + 1) 2^(-k)]` of `Interval.lintegral_Icc_le_sum`
agree with the dyadic intervals up to a null set. -/
theorem lintegral_Icc_eq_dyadicIco (G : ℝ → ℝ≥0∞) (k n : ℕ) :
    ∫⁻ x in Icc ((0 : ℝ) + n * (1 / 2 ^ k)) ((0 : ℝ) + (n + 1) * (1 / 2 ^ k)), G x =
      ∫⁻ x in dyadicIco k n, G x := by
  have hIco :
      Ico ((0 : ℝ) + n * (1 / 2 ^ k)) ((0 : ℝ) + (n + 1) * (1 / 2 ^ k)) = dyadicIco k n := by
    rw [dyadicIco]
    congr 1 <;> ring
  rw [← setLIntegral_congr Ico_ae_eq_Icc, hIco]

/-- `[0, 1]` is the union of the `2^k` intervals of length `2^(-k)` starting at `0`. -/
theorem zero_add_two_pow_mul_eq_one (k : ℕ) : (0 : ℝ) + ((2 ^ k : ℕ) : ℝ) * (1 / 2 ^ k) = 1 := by
  rw [zero_add]; push_cast; field_simp

/-- **`[0, 1]` against the dyadic intervals**: `∫_{[0,1]} G ≤ ∑_{n < 2^k} ∫_{I_{k,n}} G`. -/
theorem lintegral_Icc_le_sum_dyadicIco (G : ℝ → ℝ≥0∞) (k : ℕ) :
    ∫⁻ x in Icc (0 : ℝ) 1, G x ≤ ∑ n ∈ Finset.range (2 ^ k), ∫⁻ x in dyadicIco k n, G x := by
  have hsplit := lintegral_Icc_le_sum G 0 (by positivity : (0 : ℝ) ≤ 1 / 2 ^ k) (2 ^ k)
  rw [zero_add_two_pow_mul_eq_one] at hsplit
  exact hsplit.trans_eq (Finset.sum_congr rfl fun n _ => lintegral_Icc_eq_dyadicIco G k n)

/-- **The dyadic intervals against `[0, 1]`**: `∑_{n < 2^k} ∫_{I_{k,n}} G ≤ ∫_{[0,1]} G`. -/
theorem sum_lintegral_dyadicIco_le (G : ℝ → ℝ≥0∞) (k : ℕ) :
    ∑ n ∈ Finset.range (2 ^ k), ∫⁻ x in dyadicIco k n, G x ≤ ∫⁻ x in Icc (0 : ℝ) 1, G x := by
  have hsum := sum_le_lintegral_Icc (G := G) 0 (by positivity : (0 : ℝ) ≤ 1 / 2 ^ k) (2 ^ k)
  rw [zero_add_two_pow_mul_eq_one] at hsum
  exact (Finset.sum_congr rfl fun n _ => (lintegral_Icc_eq_dyadicIco G k n).symm).trans_le hsum

/-- Continuous functions are integrable on the dyadic intervals. -/
theorem integrableOn_dyadicIco_of_continuous {F : ℝ → ℂ} (hF : Continuous F) (k m : ℕ) :
    IntegrableOn F (dyadicIco k m) :=
  hF.integrableOn_Icc.mono_set Ico_subset_Icc_self

/-- Floor of `2^k x` on a dyadic interval: `x ∈ I_{k,n}` gives `⌊2^k x⌋ = n`. -/
theorem floor_eq_of_mem_dyadicIco {k n : ℕ} {x : ℝ} (hx : x ∈ dyadicIco k n) :
    ⌊2 ^ k * x⌋₊ = n := by
  rw [mem_dyadicIco] at hx
  exact (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hx.1)).2 hx

/-- The dyadic intervals of one level are pairwise disjoint. -/
theorem pairwise_disjoint_dyadicIco (k : ℕ) : Pairwise (Function.onFun Disjoint (dyadicIco k)) :=
  fun _ _ hnm => Set.disjoint_left.2 fun _ hn hm => hnm (eq_of_mem_dyadicIco hn hm)

/-- On `I_{k,m}` a piecewise polynomial of level `k` is a polynomial: `Q_m` for `m < 2^k`, and
`0` for the intervals beyond `[0, 1)`. -/
theorem ppFun_eq_polyFun {k m : ℕ} (Q : ℕ → ℂ[X]) {x : ℝ} (hx : x ∈ dyadicIco k m) :
    ppFun k Q x = polyFun (if m < 2 ^ k then Q m else 0) x := by
  split_ifs with hm
  · exact ppFun_eq_of_mem Q hm hx
  · rw [polyFun_zero, Pi.zero_apply]
    exact Finset.sum_eq_zero fun n hn => indicator_of_notMem
      (fun h => hm (eq_of_mem_dyadicIco h hx ▸ Finset.mem_range.1 hn)) _

/-- The piece `Q_m` (or `0` beyond `[0, 1)`) has degree `< r`. -/
theorem ite_mem_degreeLT {r : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r) (k m : ℕ) :
    (if m < 2 ^ k then Q m else 0) ∈ degreeLT ℂ r := by
  split_ifs
  · exact hQ m
  · exact zero_mem _

/-! ### Halves, lengths and integrals of the dyadic intervals -/

/-- The integral over `[0, 1]` is the sum over the dyadic intervals of level `k`. -/
theorem lintegral_unit_eq_sum_dyadicIco (G : ℝ → ℝ≥0∞) (k : ℕ) :
    ∫⁻ x in Icc (0 : ℝ) 1, G x = ∑ n ∈ Finset.range (2 ^ k), ∫⁻ x in dyadicIco k n, G x :=
  le_antisymm (lintegral_Icc_le_sum_dyadicIco G k) (sum_lintegral_dyadicIco_le G k)

/-- A function integrable on a measurable bounded set, times a polynomial, is integrable there. -/
theorem integrableOn_mul_polyFun {g : ℝ → ℂ} {s : Set ℝ} (hg : IntegrableOn g s)
    (hsm : MeasurableSet s) {a b : ℝ} (hs : s ⊆ Icc a b) (Q : ℂ[X]) :
    IntegrableOn (fun x => g x * polyFun Q x) s := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuous_polyFun Q).continuousOn
  exact hg.mul_bdd (c := M) (continuous_polyFun Q).aestronglyMeasurable
    ((ae_restrict_iff' hsm).2 (Filter.Eventually.of_forall fun x hx => hM x (hs hx)))

/-- The dyadic interval `I_{k,m}` is the union of its halves `I_{k+1,2m}` and `I_{k+1,2m+1}`. -/
theorem dyadicIco_eq_union (k m : ℕ) :
    dyadicIco k m = dyadicIco (k + 1) (2 * m) ∪ dyadicIco (k + 1) (2 * m + 1) := by
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  have e1 : ((2 * m : ℕ) : ℝ) / 2 ^ (k + 1) = (m : ℝ) / 2 ^ k := by
    push_cast; rw [pow_succ]; field_simp
  have e2 : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((m : ℝ) + 1) / 2 ^ k := by
    push_cast; rw [pow_succ]; field_simp; ring
  have e3 : ((2 * m : ℕ) : ℝ) + 1 = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [dyadicIco, dyadicIco, dyadicIco, e1, e2, e3, Ico_union_Ico_eq_Ico]
  · rw [← e1]
    gcongr
    exact_mod_cast Nat.le_succ _
  · rw [← e2]
    gcongr
    linarith

/-- The halves of a dyadic interval are disjoint. -/
theorem disjoint_dyadicIco_halves (k m : ℕ) :
    Disjoint (dyadicIco (k + 1) (2 * m)) (dyadicIco (k + 1) (2 * m + 1)) :=
  pairwise_disjoint_dyadicIco (k + 1) (by omega)

/-- `I_{j,m}` has length `2^(-j)`. -/
theorem volume_dyadicIco (j m : ℕ) : volume (dyadicIco j m) = ENNReal.ofReal (1 / 2 ^ j) := by
  rw [dyadicIco, Real.volume_Ico]
  congr 1
  ring

/-- `|I_{j,n}| = 2^(-j)`, written as an inverse in `[0, ∞]`. -/
theorem volume_dyadicIco_eq_inv (j n : ℕ) : volume (dyadicIco j n) = ((2 : ℝ≥0∞) ^ j)⁻¹ := by
  rw [volume_dyadicIco, one_div, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- **Change of variables** on a dyadic interval:
`2^j ∫_{I_{j,m}} φ = ∫_0^1 φ(t 2^(-j) + m 2^(-j))`. -/
theorem integral_dyadicIco_eq (j m : ℕ) (φ : ℝ → ℂ) :
    (((2 : ℝ) ^ j : ℝ) : ℂ) * ∫ y in dyadicIco j m, φ y =
      ∫ t in Icc (0 : ℝ) 1, φ (t / 2 ^ j + m / 2 ^ j) := by
  have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
  have hle : (m : ℝ) / 2 ^ j ≤ (m + 1) / 2 ^ j := by
    have : (0 : ℝ) < 2 ^ j := by positivity
    rw [div_le_div_iff_of_pos_right this]
    linarith
  have hL : ∫ y in dyadicIco j m, φ y = ∫ y in ((m : ℝ) / 2 ^ j)..((m + 1) / 2 ^ j), φ y := by
    rw [intervalIntegral.integral_of_le hle, dyadicIco, integral_Ico_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
  have hR : ∫ t in Icc (0 : ℝ) 1, φ (t / 2 ^ j + m / 2 ^ j) =
      ∫ t in (0 : ℝ)..1, φ (t / 2 ^ j + m / 2 ^ j) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  have hb1 : (0 : ℝ) / 2 ^ j + m / 2 ^ j = m / 2 ^ j := by rw [zero_div, zero_add]
  have hb2 : (1 : ℝ) / 2 ^ j + m / 2 ^ j = (m + 1) / 2 ^ j := by ring
  rw [hL, hR, intervalIntegral.integral_comp_div_add φ h2, hb1, hb2, Complex.real_smul]

/-- Piecewise polynomials only depend on the pieces in `[0, 1)`. -/
theorem ppFun_congr {k : ℕ} {Q Q' : ℕ → ℂ[X]} (h : ∀ n < 2 ^ k, polyFun (Q n) = polyFun (Q' n)) :
    ppFun k Q = ppFun k Q' := by
  funext x
  exact Finset.sum_congr rfl fun n hn => by rw [h n (Finset.mem_range.1 hn)]

/-- The conjugate of a piecewise polynomial is the piecewise polynomial with the conjugate
pieces. -/
theorem conj_ppFun (k : ℕ) (Q : ℕ → ℂ[X]) (x : ℝ) :
    conj (ppFun k Q x) = ppFun k (fun n => (Q n).map (starRingEnd ℂ)) x := by
  simp only [ppFun, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : x ∈ dyadicIco k n
  · rw [indicator_of_mem hx, indicator_of_mem hx, polyFun_map_conj]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, map_zero]

omit [Fact (1 ≤ p)] in
/-- Almost everywhere on `[0, 1]` gives almost everywhere on the dyadic intervals in `[0, 1)`. -/
theorem ae_dyadicIco_of_unitVol {F G : ℝ → ℂ} (h : F =ᵐ[unitVol] G) {j m : ℕ} (hm : m < 2 ^ j) :
    F =ᵐ[volume.restrict (dyadicIco j m)] G :=
  ae_restrict_of_ae_restrict_of_subset ((dyadicIco_subset hm).trans Ico_subset_Icc_self) h

/-- Elements of `L_p[0, 1]` are integrable on the dyadic intervals in `[0, 1)`. -/
theorem integrableOn_dyadicIco (f : Lp ℂ p unitVol) {j m : ℕ} (hm : m < 2 ^ j) :
    IntegrableOn f (dyadicIco j m) :=
  IntegrableOn.mono_set ((Lp.memLp f).integrable Fact.out)
    ((dyadicIco_subset hm).trans Ico_subset_Icc_self)

end Interval

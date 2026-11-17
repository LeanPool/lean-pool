/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.MultidimFiltered
public import LeanPool.KLS.LevyStochCalc.Brownian.AugmentedFiltration
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFourthMoment

/-!
# The direct cross identity for distinct Brownian coordinates

For a `d`-dimensional Brownian motion `W` whose coordinates are all Brownian motions for one
filtration `ℱ`, and distinct coordinates `i ≠ j`, the identity
`E[Z (Wⁱ_b - Wⁱ_a)(Wʲ_b - Wʲ_a)] = 0` holds for a bounded `ℱ_a`-measurable weight `Z`: along a
uniform grid of `[a, b]`, the product of the two increments telescopes into cell-wise terms, the
terms with a past factor are killed by conditioning, and the sum of the cell-wise cross products
has second moment `(b - a)² / m` by the independence of the two coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

/-- Every coordinate is a Brownian motion for the augmented joint natural filtration. -/
theorem isBrownianFiltration_augNatural (W : MultidimBrownianMotion P d) (j : Fin d) :
    IsBrownianFiltration (W.W j) (augFiltration W.naturalFiltration P) :=
  isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural j)

section DirectCross

/-- Borel functionals of the paths of two distinct coordinates are independent. -/
lemma indepFun_comp_coord (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {φ ψ : (ℝ → ℝ) → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (fun ω => φ fun t => (W.W i).W t ω) (fun ω => ψ fun t => (W.W j).W t ω) P :=
  (W.components_independent.indepFun hij).comp hφ hψ

/-- An increment of a Brownian motion over a possibly degenerate interval is square-integrable. -/
lemma memLp_two_increment_of_le (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    MemLp (fun ω => V.W q ω - V.W p ω) 2 P := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    simp only [sub_self]
    exact memLp_const 0
  · exact Ito.memLp_increment V hp h 2 (by simp)

/-- Increments of a Brownian motion over two intervals, the second starting after the first
ends, are uncorrelated. -/
lemma integral_increment_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {p q r v : ℝ}
    (hpr : p ≤ r) (hqr : q ≤ r) (hr : 0 ≤ r) (hrv : r < v) :
    ∫ ω, (V.W q ω - V.W p ω) * (V.W v ω - V.W r ω) ∂P = 0 := by
  have hY : StronglyMeasurable[ℱ r] fun ω => V.W q ω - V.W p ω :=
    (((hV.measurable q).mono (ℱ.mono hqr) le_rfl).sub
      ((hV.measurable p).mono (ℱ.mono hpr) le_rfl)).stronglyMeasurable
  have hYm : Measurable fun ω => V.W q ω - V.W p ω :=
    (V.measurable_eval q).sub (V.measurable_eval p)
  have h := Ito.integral_mul_increment_pow V ℱ hV hr hrv hY hYm 1
  rw [Ito.integral_increment_pow_odd V hr hrv odd_one, mul_zero] at h
  simpa only [pow_one] using h

/-- The uniform grid `a, a + h, a + 2h, …`. -/
noncomputable def affineGrid (a h : ℝ) (k : ℕ) : ℝ := a + k * h

lemma affineGrid_zero (a h : ℝ) : affineGrid a h 0 = a := by simp [affineGrid]

lemma affineGrid_succ_sub (a h : ℝ) (k : ℕ) : affineGrid a h (k + 1) - affineGrid a h k = h := by
  simp only [affineGrid, Nat.cast_succ]; ring

lemma affineGrid_mono {a h : ℝ} (hh : 0 ≤ h) {k l : ℕ} (hkl : k ≤ l) :
    affineGrid a h k ≤ affineGrid a h l := by
  simp only [affineGrid]
  have hkl' : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
  nlinarith

lemma affineGrid_lt_succ {a h : ℝ} (hh : 0 < h) (k : ℕ) :
    affineGrid a h k < affineGrid a h (k + 1) := by
  have := affineGrid_succ_sub a h k
  linarith

lemma le_affineGrid {a h : ℝ} (hh : 0 ≤ h) (k : ℕ) : a ≤ affineGrid a h k := by
  simpa [affineGrid_zero] using affineGrid_mono (a := a) hh (Nat.zero_le k)

lemma affineGrid_nonneg {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (k : ℕ) : 0 ≤ affineGrid a h k :=
  ha.trans (le_affineGrid hh k)

/-- The second moment of the sum of cross products of the increments of two distinct
coordinates over the cells of a uniform grid. -/
lemma integral_crossSum_sq (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2) P
    ∧ ∫ ω, (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2 ∂P
      = m * h ^ 2 := by
  have hg0 : ∀ k : ℕ, 0 ≤ affineGrid a h k := affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, affineGrid a h k < affineGrid a h (k + 1) := affineGrid_lt_succ hh
  -- the functional on path space picking out the product of two increments
  have hφ : ∀ k l : ℕ, Measurable fun path : ℝ → ℝ =>
      (path (affineGrid a h (k + 1)) - path (affineGrid a h k))
        * (path (affineGrid a h (l + 1)) - path (affineGrid a h l)) := fun k l => by
    fun_prop
  have hind : ∀ k l : ℕ, IndepFun
      (fun ω => ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
        * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
      (fun ω => ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
        * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) P :=
    fun k l => indepFun_comp_coord W hij (hφ k l) (hφ k l)
  have hint2 : ∀ (V : BrownianMotion P) (k l : ℕ), Integrable
      (fun ω => (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
        * (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω)) P := fun V k l =>
    MemLp.integrable_mul (memLp_two_increment_of_le V (hg0 k) (hglt k).le)
      (memLp_two_increment_of_le V (hg0 l) (hglt l).le)
  have hcov : ∀ (V : BrownianMotion P), IsBrownianFiltration V ℱ → ∀ k l : ℕ,
      ∫ ω, (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
        * (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω) ∂P
        = if k = l then h else 0 := by
    intro V hV k l
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · rw [ite_eq_right hkl.ne]
      exact integral_increment_mul_increment_eq_zero V hV
        (affineGrid_mono hh.le hkl.le) (affineGrid_mono hh.le hkl) (hg0 l) (hglt l)
    · have hsq := Ito.integral_increment_sq V (hg0 k) (hglt k)
      rw [affineGrid_succ_sub] at hsq
      have hsq' : ∫ ω, (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
          * (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω) ∂P
          = ∫ ω, (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω) ^ 2 ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq _).symm)
      rw [ite_eq_left rfl, hsq', hsq]
    · rw [ite_eq_right hlk.ne']
      rw [show (fun ω => (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
          * (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω))
          = fun ω => (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω)
            * (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω) from
        funext fun ω => mul_comm _ _]
      exact integral_increment_mul_increment_eq_zero V hV
        (affineGrid_mono hh.le hlk.le) (affineGrid_mono hh.le hlk) (hg0 k) (hglt k)
  have hterm : ∀ k l : ℕ,
      ∫ ω, (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) ∂P
        = if k = l then h ^ 2 else 0 := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
        * (((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    have hmul := (hind k l).integral_mul_eq_mul_integral
      (hint2 (W.W i) k l).1 (hint2 (W.W j) k l).1
    rw [show ∫ ω, (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
        * (((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) ∂P
        = (∫ ω, ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω) ∂P)
        * ∫ ω, ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω) ∂P from hmul,
      hcov (W.W i) (hcoord i) k l, hcov (W.W j) (hcoord j) k l]
    by_cases hkl : k = l
    · simp [hkl, sq]
    · simp [hkl]
  have hint : ∀ k l : ℕ, Integrable
      (fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω))) P := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
        * (((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    exact (hind k l).integrable_mul (hint2 (W.W i) k l) (hint2 (W.W j) k l)
  have hexp : (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2)
      = fun ω => ∑ k ∈ Finset.range m, ∑ l ∈ Finset.range m,
        (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ l, hterm, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun x hx => ite_eq_left hx, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- A coefficient measurable at the start of an interval is orthogonal to the Brownian increment
over it. -/
lemma integral_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s < u) {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ s] Y) (hYm : Measurable Y) :
    ∫ ω, Y ω * (V.W u ω - V.W s ω) ∂P = 0 := by
  have h := Ito.integral_mul_increment_pow V ℱ hV hs hsu hY hYm 1
  rw [Ito.integral_increment_pow_odd V hs hsu odd_one, mul_zero] at h
  simpa only [pow_one] using h

/-- Against a bounded coefficient measurable at the start of a uniform grid, the product of the
increments of two coordinates over the whole grid pairs like the sum of the cell-wise cross
products. -/
lemma integral_mul_increment_mul_increment_eq_crossSum (W : MultidimBrownianMotion P d)
    (i j : Fin d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z)
    (hZm : Measurable Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W (affineGrid a h m) ω - (W.W i).W a ω)
      * ((W.W j).W (affineGrid a h m) ω - (W.W j).W a ω)) ∂P
      = ∫ ω, Z ω * ∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω) ∂P := by
  have hg0 : ∀ k : ℕ, 0 ≤ affineGrid a h k := affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, affineGrid a h k < affineGrid a h (k + 1) := affineGrid_lt_succ hh
  have hag : ∀ k : ℕ, a ≤ affineGrid a h k := le_affineGrid hh.le
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact (hZb ω).trans (le_abs_self C)
  have hAm : ∀ (V : BrownianMotion P) (k : ℕ),
      Measurable fun ω => V.W (affineGrid a h k) ω - V.W a ω :=
    fun V k => (V.measurable_eval _).sub (V.measurable_eval _)
  -- a bounded coefficient times a past increment is killed by a fresh increment
  have hzero : ∀ (V V' : BrownianMotion P), IsBrownianFiltration V ℱ →
      IsBrownianFiltration V' ℱ → ∀ k : ℕ,
      ∫ ω, Z ω * ((V.W (affineGrid a h k) ω - V.W a ω)
        * (V'.W (affineGrid a h (k + 1)) ω - V'.W (affineGrid a h k) ω)) ∂P = 0 := by
    intro V V' hV hV' k
    have hY : StronglyMeasurable[ℱ (affineGrid a h k)] fun ω =>
        Z ω * (V.W (affineGrid a h k) ω - V.W a ω) :=
      (hZ.mono (ℱ.mono (hag k))).mul
        ((hV.measurable _).sub ((hV.measurable a).mono (ℱ.mono (hag k)) le_rfl)).stronglyMeasurable
    have h := integral_mul_increment_eq_zero V' hV' (hg0 k) (hglt k) hY (hZm.mul (hAm V k))
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (mul_assoc _ _ _).symm)
  have hintA : ∀ (V V' : BrownianMotion P) (k : ℕ), Integrable (fun ω =>
      Z ω * ((V.W (affineGrid a h k) ω - V.W a ω)
        * (V'.W (affineGrid a h (k + 1)) ω - V'.W (affineGrid a h k) ω))) P := fun V V' k =>
    Integrable.bdd_mul (MemLp.integrable_mul (memLp_two_increment_of_le V ha (hag k))
      (memLp_two_increment_of_le V' (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have hintΔ : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
        * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))) P := fun k =>
    Integrable.bdd_mul (MemLp.integrable_mul (memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
      (memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have htel : ∀ ω, Z ω * (((W.W i).W (affineGrid a h m) ω - (W.W i).W a ω)
        * ((W.W j).W (affineGrid a h m) ω - (W.W j).W a ω))
      = ∑ k ∈ Finset.range m,
        (Z ω * (((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
            * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
          + Z ω * (((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)
            * ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω))
          + Z ω * (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
            * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))) := by
    intro ω
    have h0 := Finset.sum_range_sub (fun k => ((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
      * ((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)) m
    simp only [affineGrid_zero, sub_self, mul_zero, sub_zero] at h0
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint3 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        + Z ω * (((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω))
        + Z ω * (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))) P :=
    fun k => ((hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)).add (hintΔ k)
  have hint12 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        + Z ω * (((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω))) P :=
    fun k => (hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)
  rw [integral_congr_ae (Filter.Eventually.of_forall htel), integral_finsetSum _ fun k _ => hint3 k]
  simp_rw [integral_add (hint12 _) (hintΔ _),
    integral_add (hintA (W.W i) (W.W j) _) (hintA (W.W j) (W.W i) _),
    hzero (W.W i) (W.W j) (hcoord i) (hcoord j), hzero (W.W j) (W.W i) (hcoord j) (hcoord i),
    add_zero, zero_add]
  rw [← integral_finsetSum _ fun k _ => hintΔ k]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (Finset.mul_sum _ _ _).symm)

/-- **The cross term over a common interval vanishes.** For distinct coordinates, the product of
the two increments over one interval is orthogonal to every bounded coefficient measurable at its
start. -/
theorem integral_mul_increment_mul_increment_eq_zero (W : MultidimBrownianMotion P d) {i j : Fin d}
    (hij : i ≠ j) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z) (hZm : Measurable Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P = 0 := by
  set I := ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P
    with hI
  have hC : ∀ ω, |Z ω| ≤ |C| := fun ω => (hZb ω).trans (le_abs_self C)
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      |I| ≤ |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
    intro ε hε m
    have hnpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hh : 0 < (b - a) / (m + 1 : ℕ) := div_pos (by linarith) hnpos
    have hgm : affineGrid a ((b - a) / (m + 1 : ℕ)) (m + 1) = b := by
      simp only [affineGrid]
      field_simp
      ring
    obtain ⟨hQ2int, hQ2⟩ := integral_crossSum_sq W hij hcoord ha hh (m + 1)
    have hI' := integral_mul_increment_mul_increment_eq_crossSum W i j hcoord ha hh (m + 1) hZ
      hZm hZb
    rw [hgm] at hI'
    rw [hI, hI']
    have hg0 : ∀ k : ℕ, 0 ≤ affineGrid a ((b - a) / (m + 1 : ℕ)) k := affineGrid_nonneg ha hh.le
    have hglt : ∀ k : ℕ, affineGrid a ((b - a) / (m + 1 : ℕ)) k
        < affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1) := affineGrid_lt_succ hh
    have hQint : Integrable (fun ω => ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) P :=
      integrable_finsetSum _ fun k _ => MemLp.integrable_mul
        (memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
        (memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)
    have hZQ := Integrable.bdd_mul hQint hZm.aestronglyMeasurable hCabs
    -- the arithmetic-geometric bound
    have hpt : ∀ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)|
        ≤ |C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2 := by
      intro ω
      generalize (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) = Q
      have hQ : |Q| ≤ ε / 2 + Q ^ 2 / (2 * ε) := by
        rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (ε - |Q|), sq_abs Q]
      calc |Z ω * Q| = |Z ω| * |Q| := abs_mul _ _
        _ ≤ |C| * (ε / 2 + Q ^ 2 / (2 * ε)) :=
          mul_le_mul (hC ω) hQ (abs_nonneg _) (abs_nonneg _)
        _ = |C| * ε / 2 + |C| / (2 * ε) * Q ^ 2 := by ring
    calc |∫ ω, Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω) ∂P|
        ≤ ∫ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)| ∂P :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2) ∂P :=
          integral_mono hZQ.abs ((integrable_const _).add (hQ2int.const_mul _)) hpt
      _ = |C| * ε / 2 + |C| / (2 * ε) * ((m + 1 : ℕ) * ((b - a) / (m + 1 : ℕ)) ^ 2) := by
          rw [integral_add (integrable_const _) (hQ2int.const_mul _), integral_const,
            integral_const_mul, hQ2]
          simp
      _ = |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
          have hn : ((m : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          rw [div_pow, mul_div_assoc', sq ((m : ℝ) + 1), mul_div_mul_left _ _ hn]
          ring
  have hlim : ∀ ε : ℝ, 0 < ε → |I| ≤ |C| * ε / 2 := by
    intro ε hε
    have ht : Filter.Tendsto (fun m : ℕ =>
        |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1))) Filter.atTop
        (nhds (|C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _)
    rw [mul_zero, add_zero] at ht
    exact ge_of_tendsto' ht (hbound ε hε)
  have hI0 : |I| ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h1 := hlim (|I| / (|C| + 1)) (by positivity)
    have h2 : |C| * (|I| / (|C| + 1)) ≤ |I| := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg C, abs_nonneg I]
    linarith
  exact abs_nonpos_iff.mp hI0

end DirectCross

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian

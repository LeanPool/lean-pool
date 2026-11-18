/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.VectorItoVersionSup
public import LeanPool.KLS.LevyStochCalc.Ito.ItoFormulaUnbounded

/-!
# Continuous versions for unbounded coefficients

Clamping the coefficients at level `j` gives a vector Itô process with bounded coefficients, hence
a continuous version. The window supremum of the difference of two such versions is controlled by
the clamping mesh, so along levels whose meshes are summable the versions converge uniformly on
each window.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le` — the window supremum
  of the difference of two clamped versions, in terms of the clamping mesh.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

section ClampSup

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in
/-- **The window supremum of the difference of two clamped versions**, in terms of the clamping
mesh at the two levels. -/
theorem lintegral_iSup_sq_norm_clamp_version_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
    {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {j j' : ℕ} {Xj Xj' : ℝ → Ω → Fin n → ℝ}
    (hXj : IsVectorItoVersion W ℱ hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) Xj)
    (hXj' : IsVectorItoVersion W ℱ hcoord (clampCoeff H j')
      (fun p k => measurable_clampCoeff hm j' p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j' p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j' p k T' hT')
      X₀ (clampDrift b j') Xj')
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Xj' (t : ℝ) ω - Xj (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 32 * (n : ℝ≥0∞) ^ 2 * (clampMesh P H b T j + clampMesh P H b T j') := by
  classical
  set A : Fin n → ℝ≥0∞ := fun p => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖clampDrift b j' p ω s - clampDrift b j p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hAdef
  set a : Fin n → ℝ≥0∞ := fun p => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hadef
  set a' : Fin n → ℝ≥0∞ := fun p => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖clampDrift b j' p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with ha'def
  set B : Fin n → Fin d → ℝ≥0∞ := fun p k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖clampCoeff H j' p k ω s - clampCoeff H j p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hBdef
  set bb : Fin n → Fin d → ℝ≥0∞ := fun p k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hbbdef
  set bb' : Fin n → Fin d → ℝ≥0∞ := fun p k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖clampCoeff H j' p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hbb'def
  have hA : ∀ p : Fin n, A p ≤ 2 * (a' p + a p) := fun p =>
    lintegral_energy_sub_le (measurable_clampDrift hbm j' p) (measurable_clampDrift hbm j p)
      (hbm p) T
  have hB : ∀ (p : Fin n) (k : Fin d), B p k ≤ 2 * (bb' p k + bb p k) := fun p k =>
    lintegral_energy_sub_le (measurable_clampCoeff hm j' p k) (measurable_clampCoeff hm j p k)
      (hm p k) T
  have hper : ∀ p : Fin n,
      4 * (ENNReal.ofReal T * A p) + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, B p k))
        ≤ 32 * ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
    intro p
    have h2 : ∑ k : Fin d, B p k ≤ 2 * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k) := by
      refine (Finset.sum_le_sum fun k _ => hB p k).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    calc 4 * (ENNReal.ofReal T * A p) + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, B p k))
        ≤ 4 * (ENNReal.ofReal T * (2 * (a' p + a p)))
          + 4 * (4 * ((d : ℝ≥0∞) * (2 * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k)))) :=
          add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl (hA p)))
            (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl h2)))
      _ = 8 * (ENNReal.ofReal T * (a' p + a p))
          + 32 * ((d : ℝ≥0∞) * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k)) := by ring
      _ ≤ 64 * (ENNReal.ofReal T * (a' p + a p))
          + 64 * ((d : ℝ≥0∞) * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k)) :=
          add_le_add (mul_le_mul' (by norm_num) le_rfl) (mul_le_mul' (by norm_num) le_rfl)
      _ = 32 * ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
          ring
  have hgen := lintegral_iSup_sq_norm_version_sub_le W ℱ hcoord
    (hbm₁ := fun p => measurable_clampDrift hbm j p)
    (hbm₂ := fun p => measurable_clampDrift hbm j' p)
    (hbq₁ := fun p T' hT' => energy_clampDrift_lt_top j p T' hT')
    (hbq₂ := fun p T' hT' => energy_clampDrift_lt_top j' p T' hT')
    hXj hXj' hT
  refine hgen.trans ?_
  have hmesh : clampMesh P H b T j + clampMesh P H b T j'
      = ∑ p : Fin n, ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
        + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
    unfold clampMesh
    rw [← Finset.sum_add_distrib]
  rw [hmesh]
  calc (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
        (4 * (ENNReal.ofReal T * A p) + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, B p k)))
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
        32 * ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun p _ => hper p)
    _ = 32 * (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
        ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
        rw [← Finset.mul_sum]
        ring

end ClampSup

end LevyStochCalc.Brownian.Ito

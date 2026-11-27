/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationRegular
public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationDiscs

/-!
# Weighted evaluation of the original wave on the full physical shell

The actual normalized-target estimate is transported back to physical
mass and extended by the genuine null discs. The same constant and
the exact manuscript exponential rate are preserved.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem smul_scaleBy {E : ℝ} (hE : E ≠ 0) (z : ComplexSpacetime) :
    (E : ℂ) • scaleBy E z = z := by
  have hEc : (E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE
  apply Prod.ext
  · change (E : ℂ) * (z.1 / (E : ℂ)) = z.1
    field_simp [hEc]
  · funext j
    change (E : ℂ) * (z.2 j / (E : ℂ)) = z.2 j
    field_simp [hEc]

theorem weightedSource_fullShell_evaluation
    {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ Metric.ball 0 T →
        ∀ u v : SourceTestSpace hm U, ∀ E : ℝ, m ≤ E →
          ∀ z : ComplexSpacetime, z ∈ complexShell m → euclidSq z ≤ (2 * E) ^ 2 →
            ‖complexSourceWave u.1 z + Complex.I * complexSourceWave v.1 z‖ ^ 2 ≤
              C / E ^ 2 * Real.exp (2 * (2048 / Real.sin (2 * Real.pi * c)) * T * E) *
                ‖sourceModularWeight hm U c
                  (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
                    Complex.I • Gaussian.HilbertComplexification.ofReal
                      (v : SourceHilbert hm U))‖ ^ 2 := by
  obtain ⟨C, hC, hregular⟩ := normalizedTarget_weightedSource_evaluation hc hc2
  refine ⟨C, hC, ?_⟩
  intro m hm T hT U hU u v E hmE z hz hsize
  have hE : 0 < E := hm.trans_le hmE
  have heq : m / E * E = m := div_mul_cancel₀ m hE.ne'
  -- Rewrite while the mass-positivity proof is still quantified, so the
  -- source carriers and their proof parameter change together.
  have hreg := hregular (m / E) E hE
  rw [heq] at hreg
  specialize hreg hm T hT U hU
  apply complexSourceWave_bound_of_normalizedTarget hm hmE (by positivity) u.1 v.1 ?_ hz hsize
  intro w hw
  have hb := hreg u v (scaleBy E w) hw
  simp only [scaledComplexTestWave, smul_scaleBy hE.ne'] at hb
  have hdiv : ‖complexSourceWave u.1 w + Complex.I * complexSourceWave v.1 w‖ ^ 2 ≤
      (C * Real.exp (2 * (2048 / Real.sin (2 * Real.pi * c)) * T * E) *
        ‖sourceModularWeight hm U c
          (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
            Complex.I • Gaussian.HilbertComplexification.ofReal
              (v : SourceHilbert hm U))‖ ^ 2) / E ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hE)).mpr (by simpa only [mul_comm] using hb)
  convert hdiv using 1
  ring

end VacuumBellSeparation

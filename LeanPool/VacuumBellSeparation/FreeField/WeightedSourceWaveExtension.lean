/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceWaveFunctional

/-!
# Genuine completed weighted source-wave evaluation

The norm bound first applies to the actual complexified test space.
Its dense isometric inclusion then constructs the continuous extension
and preserves the same weighted bound. The extension is independent of
the auxiliary energy and modular exponent used to prove its bound.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification

theorem weightedSource_testWave_bound {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ Metric.ball 0 T →
        ∀ E : ℝ, m ≤ E → ∀ z : ComplexSpacetime,
          z ∈ complexShell m → euclidSq z ≤ (2 * E) ^ 2 →
          ∀ x : ComplexSourceTestSpace hm U,
            ‖complexSourceTestWave hm U z x‖ ≤
              (C / E * Real.exp ((2048 / Real.sin (2 * Real.pi * c)) * T * E)) *
                ‖sourceModularWeight hm U c (complexSourceTestInclusion hm U x)‖ := by
  obtain ⟨C, hC, hb⟩ := weightedSource_fullShell_evaluation hc hc2
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro m hm T hT U hU E hmE z hz hsize x
  have hE : 0 < E := hm.trans_le hmE
  have h := hb m hm T hT U hU x.re x.im E hmE z hz hsize
  rw [← complexSourceTestInclusion_decompose hm U x,
    ← complexSourceTestWave_apply hm U z x] at h
  let a : ℝ := (2048 / Real.sin (2 * Real.pi * c)) * T * E
  have hexp : Real.exp (2 * a) = (Real.exp a) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have heq : ((Real.sqrt C / E * Real.exp a) *
      ‖sourceModularWeight hm U c (complexSourceTestInclusion hm U x)‖) ^ 2 =
        C / E ^ 2 * Real.exp (2 * a) *
          ‖sourceModularWeight hm U c (complexSourceTestInclusion hm U x)‖ ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hC.le, hexp]
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  rw [← pow_two, ← pow_two]
  rw [heq]
  simpa only [a, mul_assoc] using h

/-- Continuous linear map for the completed source wave, of type `ComplexSourceHilbert hm U →L[ℂ]
ℂ`. -/
noncomputable def completedSourceWave {m : ℝ} (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (z : ComplexSpacetime) :
    ComplexSourceHilbert hm U →L[ℂ] ℂ :=
  extendComplexSourceTestFunctional hm U (complexSourceTestWave hm U z)

theorem weightedSource_completedShell_evaluation
    {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ Metric.ball 0 T →
        ∀ E : ℝ, m ≤ E → ∀ z : ComplexSpacetime,
          z ∈ complexShell m → euclidSq z ≤ (2 * E) ^ 2 →
          (∀ x : ComplexSourceTestSpace hm U,
            completedSourceWave hm U z (complexSourceTestInclusion hm U x) =
              complexSourceTestWave hm U z x) ∧
          ∀ x : ComplexSourceHilbert hm U, ‖completedSourceWave hm U z x‖ ≤
            (C / E * Real.exp ((2048 / Real.sin (2 * Real.pi * c)) * T * E)) *
              ‖sourceModularWeight hm U c x‖ := by
  obtain ⟨C, hC, hb⟩ := weightedSource_testWave_bound hc hc2
  refine ⟨C, hC, ?_⟩
  intro m hm T hT U hU E hmE z hz hsize
  have hE : 0 < E := hm.trans_le hmE
  have hbound := hb m hm T hT U hU E hmE z hz hsize
  constructor
  · exact fun x => extendComplexSourceTestFunctional_eq hm U
      (complexSourceTestWave hm U z) (sourceModularWeight hm U c) (by positivity) hbound x
  · exact extendComplexSourceTestFunctional_weight_bound hm U
      (complexSourceTestWave hm U z) (sourceModularWeight hm U c) (by positivity) hbound

end VacuumBellSeparation

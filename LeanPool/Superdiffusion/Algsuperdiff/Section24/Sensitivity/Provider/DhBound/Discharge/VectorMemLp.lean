/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.UnitCubeValue

/-!
# VectorMemLp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Componentwise `L^p` bookkeeping for `Vec d`-valued fields

`Vec d = Fin d → ℝ` carries the supremum norm, and every vector is the finite
sum of its coordinate multiples of the standard basis.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24 MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- Componentwise criterion for `MemLp` of a `Vec d`-valued field. -/
theorem memLp_vec_of_components {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {q : ℝ≥0∞} {f : α → Vec d}
    (h : ∀ i : Fin d, MemLp (fun x => f x i) q μ) : MemLp f q μ :=
  MeasureTheory.memLp_pi_iff.mpr h

/-- An a.e. bound gives an `L^∞` cube-norm bound. -/
theorem cubeLpNorm_infty_le_of_ae_bound {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (f : Vec d → E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖f x‖ ≤ M) :
    cubeLpNorm Q ∞ f ≤ M := by
  by_cases hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)
  swap
  · rw [cubeLpNorm, eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.toReal_top]
    exact hM
  have hle : eLpNorm f ∞ (normalizedCubeMeasure Q) ≤ ENNReal.ofReal M := by
    rw [MeasureTheory.eLpNorm_exponent_top hf]
    exact MeasureTheory.eLpNormEssSup_le_of_ae_bound h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simpa [cubeLpNorm, ENNReal.toReal_ofReal hM] using this

/-- The mean term of the positive Besov norm is controlled by any componentwise
a.e. bound. -/
theorem sqrt_vecNormSq_cubeAverageVec_le_of_ae_bound (Q : TriadicCube d)
    {F : Vec d → Vec d} {M : ℝ} (hM : 0 ≤ M)
    (hmem : ∀ i : Fin d, MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (h : ∀ i : Fin d, ∀ᵐ x ∂normalizedCubeMeasure Q, |F x i| ≤ M) :
    Real.sqrt (vecNormSq (cubeAverageVec Q F)) ≤ Real.sqrt (d : ℝ) * M := by
  classical
  have hcoord : ∀ i : Fin d, |cubeAverage Q (fun x => F x i)| ≤ M := by
    intro i
    have h2 : ‖cubeAverage Q (fun x => F x i)‖ ≤ cubeLpNorm Q (2 : ℝ≥0∞) (fun x => F x i) :=
      norm_cubeAverage_le_cubeLpNorm_two Q _ (hmem i)
    have hinf : cubeLpNorm Q (2 : ℝ≥0∞) (fun x => F x i) ≤ M := by
      refine le_trans ?_ (cubeLpNorm_infty_le_of_ae_bound Q (fun x => F x i) hM ?_)
      · exact cubeLpNorm_two_le_cubeLpNorm_infty_of_memLp_infty Q _
          (by
            refine MeasureTheory.MemLp.of_bound (hmem i).aestronglyMeasurable M ?_
            filter_upwards [h i] with x hx using by simpa [Real.norm_eq_abs] using hx)
      · filter_upwards [h i] with x hx using by simpa [Real.norm_eq_abs] using hx
    simpa [Real.norm_eq_abs] using h2.trans hinf
  have hsum : vecNormSq (cubeAverageVec Q F) ≤ (d : ℝ) * M ^ 2 := by
    have : vecNormSq (cubeAverageVec Q F) =
        ∑ i : Fin d, (cubeAverage Q (fun x => F x i)) ^ 2 := by
      simp [vecNormSq, vecDot, cubeAverageVec, sq]
    rw [this]
    calc (∑ i : Fin d, (cubeAverage Q (fun x => F x i)) ^ 2)
        ≤ ∑ _i : Fin d, M ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hcoord i
          nlinarith [abs_nonneg (cubeAverage Q (fun x => F x i)),
            sq_abs (cubeAverage Q (fun x => F x i))]
      _ = (d : ℝ) * M ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc Real.sqrt (vecNormSq (cubeAverageVec Q F))
      ≤ Real.sqrt ((d : ℝ) * M ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * M := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM]

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

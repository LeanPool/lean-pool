/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Vector-valued ten-thirds bounds in the Leray limit

The space-time `L^(10/3)` estimate for the regularized velocities in
`prop:leray-limit` is proved coordinate by coordinate. This file assembles
uniform coordinate bounds into a uniform bound for the vector field.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Uniform coordinate `L^(10/3)` bounds for a sequence of velocity fields give
a uniform `L^(10/3)` bound for the vector fields, with the constant multiplied
by the number of coordinates. -/
theorem lerayLimit_vector_tenThirds_of_component_bounds
    (μ : Measure ParabolicPoint)
    (F : ℕ → ParabolicPoint → Vec3) (M : ℝ≥0∞)
    (hcomponents : ∀ (n : ℕ) (i : Fin 3),
      MemLp (fun z : ParabolicPoint => F n z i)
        (ENNReal.ofReal (10 / 3 : ℝ)) μ)
    (hcomponentBound : ∀ (n : ℕ) (i : Fin 3),
      eLpNorm (fun z : ParabolicPoint => F n z i)
        (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ M) :
    ∀ n, MemLp (F n) (ENNReal.ofReal (10 / 3 : ℝ)) μ ∧
      eLpNorm (F n) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ 3 * M := by
  intro n
  let p : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  have hp : 1 ≤ p := by
    change 1 ≤ ENNReal.ofReal (10 / 3 : ℝ)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hmem : MemLp (F n) p μ := memLp_pi_iff.mpr (hcomponents n)
  refine ⟨hmem, ?_⟩
  have hpointwise (z : ParabolicPoint) :
      ‖F n z‖ ≤ ‖∑ i : Fin 3, ‖F n z i‖‖ := by
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    refine (pi_norm_le_iff_of_nonneg
      (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr fun i => ?_
    exact Finset.single_le_sum (f := fun j : Fin 3 => ‖F n z j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  calc
    eLpNorm (F n) p μ ≤
        eLpNorm (fun z => ∑ i : Fin 3, ‖F n z i‖) p μ :=
      eLpNorm_mono hmem.aestronglyMeasurable hpointwise
    _ ≤ ∑ i : Fin 3, eLpNorm (fun z => ‖F n z i‖) p μ :=
      eLpNorm_sum_le (p := p) (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i => fun z => ‖F n z i‖) hp
    _ = ∑ i : Fin 3, eLpNorm (fun z => F n z i) p μ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact eLpNorm_norm (fun z => F n z i) (hcomponents n i).aestronglyMeasurable
    _ ≤ ∑ _i : Fin 3, M :=
      Finset.sum_le_sum fun i _ => hcomponentBound n i
    _ = 3 * M := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num

end CKN.Leray

end

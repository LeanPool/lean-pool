/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCellPartition
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortLatticeProfile3D
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortDyadicDecay
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Summing the short-time cells

The normal Gaussian decay dominates any fixed dyadic polynomial, while
a reciprocal-square profile sums the spatial grid.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A fixed dyadic polynomial times normal Gaussian decay remains
summable after shifting the index to the short-time layers. -/
theorem bu_short_shifted_dyadic_gaussian_summable
    (N : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℕ => (2 : ℝ) ^ (N * (k + 1)) *
      Real.exp (-(c * (2 : ℝ) ^ (k + 1)))) := by
  have h := bu_short_dyadic_gaussian_summable N c hc
  have hshift := h.comp_injective Nat.succ_injective
  apply hshift.congr
  intro k
  rfl

/-- A Gaussian cell estimate with any fixed dyadic polynomial implies
integrability on the union of shifted cells (`lem:bu-small-time`). -/
theorem bu_short_integrable_on_shifted_dyadic_cells
    (N : ℕ) (c K : ℝ) (hc : 0 < c)
    (F : ParabolicPoint → ℝ)
    (hCellInt : ∀ (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048),
      IntegrableOn F
        (buShortShiftedDyadicCell (k + 1 : ℤ) m ell) volume)
    (hCellBound : ∀ (k : ℕ) (m : Fin 3 → ℤ) (ell : Fin 2048),
      (∫ z in buShortShiftedDyadicCell (k + 1 : ℤ) m ell,
        ‖F z‖ ∂(volume : Measure ParabolicPoint)) ≤
          K * ((2 : ℝ) ^ (N * (k + 1)) *
            Real.exp (-(c * (2 : ℝ) ^ (k + 1)))) *
              buShortSpatialProfile m) :
    IntegrableOn F
      (⋃ ij : (ℕ × (Fin 3 → ℤ)) × Fin 2048,
        buShortShiftedDyadicCell (ij.1.1 + 1 : ℤ) ij.1.2 ij.2)
      volume := by
  let f : ℕ → ℝ := fun k => (2 : ℝ) ^ (N * (k + 1)) *
    Real.exp (-(c * (2 : ℝ) ^ (k + 1)))
  have hf : Summable f := bu_short_shifted_dyadic_gaussian_summable N c hc
  have hf0 (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hg := bu_short_spatial_profile_summable
  have hg0 := bu_short_int_profile_nonneg
  have hprofile0 (m : Fin 3 → ℤ) : 0 ≤ buShortSpatialProfile m := by
    dsimp [buShortSpatialProfile]
    exact mul_nonneg (hg0 _) (mul_nonneg (hg0 _) (hg0 _))
  have hfg : Summable (fun ij : ℕ × (Fin 3 → ℤ) =>
      f ij.1 * buShortSpatialProfile ij.2) :=
    hf.mul_of_nonneg hg hf0 hprofile0
  have hone : Summable (fun _ : Fin 2048 => (1 : ℝ)) :=
    Summable.of_finite
  have hbase : Summable (fun ij : (ℕ × (Fin 3 → ℤ)) × Fin 2048 =>
      (f ij.1.1 * buShortSpatialProfile ij.1.2) * 1) :=
    hfg.mul_of_nonneg hone
      (fun ij => mul_nonneg (hf0 _) (hprofile0 _))
      (fun _ => by norm_num)
  have hbound : Summable (fun ij : (ℕ × (Fin 3 → ℤ)) × Fin 2048 =>
      K * f ij.1.1 * buShortSpatialProfile ij.1.2) := by
    convert hbase.mul_left K using 1
    funext ij
    ring
  have hsum : Summable (fun ij : (ℕ × (Fin 3 → ℤ)) × Fin 2048 =>
      ∫ z in buShortShiftedDyadicCell (ij.1.1 + 1 : ℤ) ij.1.2 ij.2,
        ‖F z‖ ∂(volume : Measure ParabolicPoint)) := by
    apply hbound.of_nonneg_of_le
    · intro ij
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro ij
      exact hCellBound ij.1.1 ij.1.2 ij.2
  exact integrableOn_iUnion_of_summable_integral_norm
    (fun ij => hCellInt ij.1.1 ij.1.2 ij.2) hsum

end ESS

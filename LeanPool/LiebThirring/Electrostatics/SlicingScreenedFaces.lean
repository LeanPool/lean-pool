/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingScreenedCells
import all LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry
import all LeanPool.LiebThirring.Electrostatics.FaceMeasureBasic

/-!
# Cancellation of the directed screened face terms

Pairing the two cell orientations cancels the common potential trace and
leaves the normal derivative jump, with coefficient exactly minus 4 pi
times the landed face density.
-/

public section

open Set MeasureTheory
open scoped NNReal RealInnerProductSpace

namespace LiebThirring

theorem bisectorNormal_reverse {M : ℕ} (R : Fin M → Position) (k l : Fin M) :
    bisectorNormal R l k = -bisectorNormal R k l := by
  unfold bisectorNormal
  rw [norm_sub_rev (R k) (R l), ← neg_sub (R l) (R k), smul_neg]

theorem sum_directedNuclearPairs_oriented {M : ℕ} {A : Type*} [AddCommMonoid A]
    (f : ∀ k l : Fin M, k ≠ l → A) :
    (∑ k : Fin M, ∑ l : {l : Fin M // l ≠ k}, f k l.val l.property.symm) =
      ∑ p : NuclearPair M, (f p.val.1 p.val.2 (ne_of_lt p.property) +
        f p.val.2 p.val.1 (ne_of_lt p.property).symm) := by
  classical
  let g : NuclearPair M ⊕ NuclearPair M → A := Sum.elim
    (fun p => f p.val.1 p.val.2 (ne_of_lt p.property))
    (fun p => f p.val.2 p.val.1 (ne_of_lt p.property).symm)
  calc
    _ = ∑ p : (Σ k : Fin M, {l : Fin M // l ≠ k}), f p.1 p.2.val p.2.property.symm :=
      (Fintype.sum_sigma _).symm
    _ = ∑ p : NuclearPair M ⊕ NuclearPair M, g p := by
      apply Fintype.sum_equiv (directedNuclearPairEquiv M)
      rintro ⟨k, l, hl⟩
      dsimp only [directedNuclearPairEquiv, Equiv.coe_fn_mk]
      by_cases h : k < l
      · simp only [dite_eq_left h, g, Sum.elim_inl]
      · simp only [dite_eq_right h, g, Sum.elim_inr]
    _ = _ := by
      rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
      rfl

theorem screenedCellBoundaryTerm_pair {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k l : Fin M)
    (f : Position → ℝ) {x : Position} (hx : x ∈ voronoiFace R k l) :
    screenedCellBoundaryTerm Z R k l f x + screenedCellBoundaryTerm Z R l k f x =
      -4 * Real.pi * nuclearFaceDensity R (Z : ℝ) k l x * f x := by
  have hx' : x ∈ voronoiFace R l k := (voronoiFace_comm R k l) ▸ hx
  have hk := screenedPotentialReal_eq_screenedCellPotential Z R hR k
    (voronoiFace_subset_closed R k l hx)
  have hl := screenedPotentialReal_eq_screenedCellPotential Z R hR l
    (voronoiFace_subset_closed R l k hx')
  have hj := fderiv_screenedCellPotential_jump Z R hR k l hx (bisectorNormal R k l)
  have hi : inner ℝ (bisectorNormal R k l) (bisectorNormal R k l) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_bisectorNormal R hR hx.1, one_pow]
  rw [hi, mul_one] at hj
  unfold screenedCellBoundaryTerm
  rw [bisectorNormal_reverse R k l, map_neg, map_neg, ← hk, ← hl]
  calc
    _ = f x * (fderiv ℝ (screenedCellPotential Z R l) x (bisectorNormal R k l) -
        fderiv ℝ (screenedCellPotential Z R k) x (bisectorNormal R k l)) := by ring
    _ = _ := by
      rw [hj, nuclearFaceDensity, nuclearHalfDistance]
      field_simp
      ring

theorem integral_screenedCellBoundaryTerm_pair {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l)
    (f : Position → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x in voronoiFace R k l, screenedCellBoundaryTerm Z R k l f x
      ∂bisectorSurfaceMeasure R hR k l hkl) +
    (∫ x in voronoiFace R l k, screenedCellBoundaryTerm Z R l k f x
      ∂bisectorSurfaceMeasure R hR l k hkl.symm) =
      -4 * Real.pi * ∫ x in voronoiFace R k l,
        nuclearFaceDensity R (Z : ℝ) k l x * f x ∂bisectorSurfaceMeasure R hR k l hkl := by
  have hleft := integrableOn_screenedCellBoundaryTerm Z R hR k l hkl f hf hfc
  have hright := integrableOn_screenedCellBoundaryTerm Z R hR l k hkl.symm f hf hfc
  rw [← voronoiFace_comm R k l, ← bisectorSurfaceMeasure_comm R hR k l hkl] at hright ⊢
  rw [← integral_add hleft hright, ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_voronoiFace R k l)
  intro x hx
  simpa only [mul_assoc] using screenedCellBoundaryTerm_pair Z R hR k l f hx

end LiebThirring

end

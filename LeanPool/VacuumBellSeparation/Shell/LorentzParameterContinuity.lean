/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ComplexLorentzFamilySmooth
public import LeanPool.VacuumBellSeparation.Shell.SpacetimeFrameCoordinates

/-!
# Pointwise and inverse operator-norm continuity of actual Lorentz maps

The inverse coordinates follow from the Minkowski bilinear form. This
avoids assuming continuity of an abstract inverse operation on the
space of parameterized equivalences.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

theorem lorentz_inverse_time_coordinate {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (x : Spacetime) :
    (Λ.symm x).1 = minkowskiForm (Λ (1, 0)) x := by
  have h := hΛ (1, 0) (Λ.symm x)
  simpa only [ContinuousLinearEquiv.apply_symm_apply, minkowskiForm,
    one_mul, inner_zero_left, sub_zero] using h.symm

theorem lorentz_inverse_spatial_coordinate {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (x : Spacetime) (j : Fin 3) :
    (Λ.symm x).2 j = -minkowskiForm (Λ (spacetimeAxis j)) x := by
  have h := hΛ (spacetimeAxis j) (Λ.symm x)
  have hi : ⟪WithLp.toLp 2 (Pi.single j (1 : ℝ)), (Λ.symm x).2⟫_ℝ =
      (Λ.symm x).2 j := by
    simpa only [EuclideanSpace.single, PiLp.single, map_one, one_mul] using
      (EuclideanSpace.inner_single_left j (1 : ℝ) (Λ.symm x).2)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  change minkowskiForm (Λ (spacetimeAxis j)) x =
    0 * (Λ.symm x).1 - ⟪WithLp.toLp 2 (Pi.single j (1 : ℝ)), (Λ.symm x).2⟫_ℝ at h
  rw [zero_mul, zero_sub, hi] at h
  exact (neg_eq_iff_eq_neg.mp h.symm)

theorem continuous_lorentzInverse_family {A : Type*} [TopologicalSpace A]
    (Λ : A → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ a, IsLorentzMap (Λ a))
    (hc : ∀ x : Spacetime, Continuous fun a => Λ a x) (x : Spacetime) :
    Continuous (fun a => (Λ a).symm x) := by
  have ht : Continuous (fun a => ((Λ a).symm x).1) := by
    simp only [lorentz_inverse_time_coordinate (hΛ _)]
    exact ((hc (1, 0)).fst.mul continuous_const).sub
      ((hc (1, 0)).snd.inner continuous_const)
  have hs : Continuous (fun a => ((Λ a).symm x).2) := by
    change Continuous (fun a => WithLp.toLp 2 (fun j => ((Λ a).symm x).2 j))
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro j
    simp only [lorentz_inverse_spatial_coordinate (hΛ _)]
    exact (((hc (spacetimeAxis j)).fst.mul continuous_const).sub
      ((hc (spacetimeAxis j)).snd.inner continuous_const)).neg
  exact ht.prodMk hs

theorem continuous_lorentzInverse_operatorNorm_family {A : Type*} [TopologicalSpace A]
    (Λ : A → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ a, IsLorentzMap (Λ a))
    (hc : ∀ x : Spacetime, Continuous fun a => Λ a x) :
    Continuous (fun a => spacetimeEuclideanOperatorNorm (Λ a).symm) :=
  continuous_spacetimeEuclideanOperatorNorm_family (fun a => (Λ a).symm)
    (continuous_lorentzInverse_family Λ hΛ hc)

theorem continuous_complexSpacetimeRe : Continuous complexSpacetimeRe := by
  apply Continuous.prodMk
  · fun_prop
  · apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    fun_prop

theorem complexSpacetimeRe_ofReal (x : Spacetime) :
    complexSpacetimeRe (complexSpacetimeOfReal x) = x := by
  apply Prod.ext
  · rfl
  · ext i
    rfl

theorem continuous_lorentzParameterFamily_apply (x : Spacetime) :
    Continuous (fun s : Fin 6 → ℝ => lorentzParameterFamily s x) := by
  have h : Continuous (fun s : Fin 6 → ℝ =>
      complexLorentzFamilyAction s (complexSpacetimeOfReal x)) := by
    have step (j : Fin 6) (z : (Fin 6 → ℝ) → ComplexSpacetime)
        (hz : Continuous z) :
        Continuous (fun s => complexLorentzParameterAction j (s j) (z s)) := by
      have hj : Continuous (fun q : ℝ × ComplexSpacetime =>
          complexLorentzParameterAction j q.1 q.2) :=
        (contDiff_complexLorentzParameterAction j).continuous
      exact hj.comp ((continuous_apply j).prodMk hz)
    simp only [complexLorentzFamilyAction_factors]
    apply step 5
    apply step 4
    apply step 3
    apply step 2
    apply step 1
    apply step 0
    exact continuous_const
  have he (s : Fin 6 → ℝ) : complexSpacetimeRe
      (complexLorentzFamilyAction s (complexSpacetimeOfReal x)) = lorentzParameterFamily s x := by
    exact (congrArg complexSpacetimeRe
      (complexifiedSpacetimeMap_ofReal (lorentzParameterFamily s) x)).trans
        (complexSpacetimeRe_ofReal (lorentzParameterFamily s x))
  simpa only [Function.comp_def, he] using continuous_complexSpacetimeRe.comp h

end VacuumBellSeparation

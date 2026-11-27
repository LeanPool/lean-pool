/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSpacetime
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Joint continuity of the literal complex Fourier wave

Compact spatial support makes the original Fourier integral continuous
in all three complex coordinates simultaneously. Real map parameters
enter through their actual four coordinate images.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

theorem continuous_complexSpatialFourier (f : SpatialTestFunction) :
    Continuous (complexSpatialFourier f) := by
  let K : (Fin 3 → ℂ) → EuclideanSpace ℝ (Fin 3) → ℂ := fun z x =>
    Complex.exp (-(Complex.I * spatialDot z (fun i => (x i : ℂ)))) * (f.1 x : ℂ)
  have hf := f.2.1.continuous
  have hK : Continuous K.uncurry := by
    dsimp [K, Function.uncurry, spatialDot]
    fun_prop
  have he (z : Fin 3 → ℂ) : (∫ x in tsupport f.1, K z x) = complexSpatialFourier f z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [K, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, mul_zero]
  simpa only [he] using continuous_parametric_integral_of_continuous (μ := volume) hK f.2.2

theorem continuous_complexSourceWave (u : TimeZeroSource) : Continuous (complexSourceWave u) :=
  ((continuous_complexSpatialFourier u.1).comp continuous_snd).add
    ((continuous_const.mul continuous_fst).mul
      ((continuous_complexSpatialFourier u.2).comp continuous_snd))

theorem continuous_complexSpacetimeOfReal : Continuous complexSpacetimeOfReal := by
  change Continuous (fun x : Spacetime => ((x.1 : ℂ), fun i => (x.2 i : ℂ)))
  fun_prop

theorem continuous_complexShellBoost (m : ℝ) (ζ : ℂ) : Continuous (complexShellBoost m ζ) := by
  unfold complexShellBoost
  have hw := continuous_dispersion m
  fun_prop

theorem continuous_complexifiedSpacetimeMap_family
    {A : Type*} [TopologicalSpace A] (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ x : Spacetime, Continuous fun a => Λ a x) :
    Continuous (fun q : A × ComplexSpacetime => complexifiedSpacetimeMap (Λ q.1) q.2) := by
  simp_rw [complexifiedSpacetimeMap_apply]
  apply Continuous.add
  · exact continuous_snd.fst.smul
      (continuous_complexSpacetimeOfReal.comp ((hΛ (coordDir 0)).comp continuous_fst))
  · apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_snd.snd).smul
      (continuous_complexSpacetimeOfReal.comp ((hΛ (coordDir i.succ)).comp continuous_fst))

theorem continuous_lorentzContourWave
    {A : Type*} [TopologicalSpace A] (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ x : Spacetime, Continuous fun a => Λ a x)
    (m θ : ℝ) (u : TimeZeroSource) :
    Continuous (fun q : A × EuclideanSpace ℝ (Fin 3) =>
      complexSourceWave u (complexifiedSpacetimeMap (Λ q.1)
        (complexShellBoost m ((θ : ℂ) * Complex.I) q.2))) := by
  have hpair : Continuous (fun q : A × EuclideanSpace ℝ (Fin 3) =>
      (q.1, complexShellBoost m ((θ : ℂ) * Complex.I) q.2)) :=
    (continuous_fst : Continuous (Prod.fst : A × EuclideanSpace ℝ (Fin 3) → A)).prodMk
      ((continuous_complexShellBoost m ((θ : ℂ) * Complex.I)).comp continuous_snd)
  have hmap : Continuous (fun q : A × EuclideanSpace ℝ (Fin 3) =>
      complexifiedSpacetimeMap (Λ q.1) (complexShellBoost m ((θ : ℂ) * Complex.I) q.2)) :=
    Continuous.comp'
      (f := fun q : A × EuclideanSpace ℝ (Fin 3) =>
        (q.1, complexShellBoost m ((θ : ℂ) * Complex.I) q.2))
      (g := fun q : A × ComplexSpacetime => complexifiedSpacetimeMap (Λ q.1) q.2)
      (continuous_complexifiedSpacetimeMap_family Λ hΛ) hpair
  exact Continuous.comp'
    (f := fun q : A × EuclideanSpace ℝ (Fin 3) =>
      complexifiedSpacetimeMap (Λ q.1) (complexShellBoost m ((θ : ℂ) * Complex.I) q.2))
    (g := complexSourceWave u) (continuous_complexSourceWave u) hmap

end VacuumBellSeparation

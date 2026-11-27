/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionBounds
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# A genuine Banach factorization of each tempered distribution

Weighted derivatives of a Schwartz function are actual bounded continuous
functions. Finitely many such coordinates form a Banach space. Continuity of
a tempered distribution bounds it by finitely many coordinates; descent to
the actual range and complex Hahn–Banach then factor the distribution through
this Banach space. This does not assume a norm or Bochner integral on Schwartz
space, and does not assert the cutoff Fourier integral identity, which is proved from this
factorization as `distribution_cutoffFourier_integral` in `FreeField/CutoffFourierIntegral.lean`.
-/

@[expose] public section

open scoped SchwartzMap BoundedContinuousFunction

namespace VacuumBellSeparation

/-- A bounded scalar functional on the range of a linear map extends to its
actual normed codomain. Injectivity of the map is unnecessary. -/
theorem exists_functional_factor_of_bound
    {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (J : A →ₗ[ℂ] B) (T : A →ₗ[ℂ] ℂ) (C : ℝ)
    (hb : ∀ x, ‖T x‖ ≤ C * ‖J x‖) :
    ∃ L : B →L[ℂ] ℂ, ∀ x, L (J x) = T x := by
  have hk : LinearMap.ker J.rangeRestrict ≤ LinearMap.ker T := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    have hz : J x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    exact norm_eq_zero.mp (le_antisymm (by simpa [hz] using hb x) (norm_nonneg _))
  let l : J.range →ₗ[ℂ] ℂ :=
    J.rangeRestrict.liftOfSurjective J.surjective_rangeRestrict ⟨T, hk⟩
  have hl : ∀ x, l (J.rangeRestrict x) = T x := fun x =>
    LinearMap.equivOfSurjective_apply J.surjective_rangeRestrict hk
  have hbl : ∀ y : J.range, ‖l y‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨x, rfl⟩ := J.surjective_rangeRestrict y
    change ‖l (J.rangeRestrict x)‖ ≤ C * ‖J x‖
    rw [hl]
    exact hb x
  let lc : J.range →L[ℂ] ℂ := l.mkContinuous C hbl
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq J.range lc
  refine ⟨L, fun x => ?_⟩
  exact (hL (J.rangeRestrict x)).trans (hl x)

/-- One actual weighted derivative, with the supremum norm of bounded continuous functions. -/
noncomputable def schwartzWeightedDerivative (k j : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    EuclideanSpace ℝ (Fin 3) →ᵇ
      ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin 3)) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ‖x‖ ^ k • iteratedFDeriv ℝ j φ x)
    ((continuous_norm.pow k).smul
      ((φ.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k j φ) (fun x => by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ k)]
        using φ.le_seminorm ℂ k j x)

@[simp] theorem schwartzWeightedDerivative_apply (k j : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (x : EuclideanSpace ℝ (Fin 3)) :
    schwartzWeightedDerivative k j φ x = ‖x‖ ^ k • iteratedFDeriv ℝ j φ x := rfl

/-- These are exactly the genuine Schwartz seminorms, not replacement norms. -/
theorem norm_schwartzWeightedDerivative (k j : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    ‖schwartzWeightedDerivative k j φ‖ = SchwartzMap.seminorm ℂ k j φ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
    intro x
    simpa only [schwartzWeightedDerivative_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ k)] using φ.le_seminorm ℂ k j x
  · apply SchwartzMap.seminorm_le_bound ℂ k j φ
      (norm_nonneg (schwartzWeightedDerivative k j φ))
    intro x
    simpa only [schwartzWeightedDerivative_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ k)] using
      (schwartzWeightedDerivative k j φ).norm_coe_le_norm x

/-- The finite product is complete by the actual bounded-continuous-function instances. -/
abbrev SchwartzDerivativeBanach (s : Finset (ℕ × ℕ)) :=
  ∀ i : s, EuclideanSpace ℝ (Fin 3) →ᵇ
    ContinuousMultilinearMap ℝ (fun _ : Fin i.val.2 => EuclideanSpace ℝ (Fin 3)) ℂ

/-- The actual finite weighted-derivative map. -/
noncomputable def schwartzDerivativeMap (s : Finset (ℕ × ℕ)) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ →ₗ[ℂ] SchwartzDerivativeBanach s where
  toFun φ i := schwartzWeightedDerivative i.val.1 i.val.2 φ
  map_add' φ ψ := by
    funext i
    apply BoundedContinuousFunction.ext
    intro x
    change ‖x‖ ^ i.val.1 • iteratedFDeriv ℝ i.val.2 (φ + ψ) x = _
    rw [show (⇑(φ + ψ)) = (⇑φ + ⇑ψ) by rfl,
      iteratedFDeriv_add_apply (φ.smooth _).contDiffAt (ψ.smooth _).contDiffAt,
      smul_add]
    rfl
  map_smul' c φ := by
    funext i
    apply BoundedContinuousFunction.ext
    intro x
    change ‖x‖ ^ i.val.1 • iteratedFDeriv ℝ i.val.2 (c • φ) x = _
    rw [show (⇑(c • φ)) = c • ⇑φ by rfl,
      iteratedFDeriv_const_smul_apply (φ.smooth _).contDiffAt, smul_comm]
    rfl

theorem seminorm_le_norm_schwartzDerivativeMap (s : Finset (ℕ × ℕ))
    (i : ℕ × ℕ) (hi : i ∈ s) (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    SchwartzMap.seminorm ℂ i.1 i.2 φ ≤ ‖schwartzDerivativeMap s φ‖ := by
  rw [← norm_schwartzWeightedDerivative]
  exact norm_le_pi_norm (schwartzDerivativeMap s φ) ⟨i, hi⟩

/-- Every actual tempered distribution factors through a genuine finite Banach
product of weighted derivatives. Fourier integration through this factor still
requires actual integrability and equality of the derivative coordinates. -/
theorem temperedDistribution_banach_factorization
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ L : SchwartzDerivativeBanach s →L[ℂ] ℂ,
      ∀ φ, L (schwartzDerivativeMap s φ) = T φ := by
  obtain ⟨s, C, _, hb⟩ := temperedDistribution_finite_seminorm_bound T
  refine ⟨s, ?_⟩
  apply exists_functional_factor_of_bound
    (A := SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (B := SchwartzDerivativeBanach s) (schwartzDerivativeMap s) T.toLinearMap
    ((C : ℝ) * s.card)
  intro φ
  have hs := Seminorm.finset_sup_le_sum
    (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 3)) ℂ) s φ
  have hsum : (∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 φ) ≤
      (s.card : ℝ) * ‖schwartzDerivativeMap s φ‖ := by
    calc
      _ ≤ ∑ _i ∈ s, ‖schwartzDerivativeMap s φ‖ :=
        Finset.sum_le_sum (fun i hi => seminorm_le_norm_schwartzDerivativeMap s i hi φ)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    ‖T φ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 3)) ℂ)) φ := hb φ
    _ ≤ C * (∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 φ) := by
      apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
      simpa only [sum_apply, schwartzSeminormFamily] using hs
    _ ≤ C * ((s.card : ℝ) * ‖schwartzDerivativeMap s φ‖) :=
      mul_le_mul_of_nonneg_left hsum C.coe_nonneg
    _ = _ := by ring

end VacuumBellSeparation

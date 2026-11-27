/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SandwichRangeForm
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers

/-!
# Positive powers of an actual faithful operator

Positive real powers of an injective positive bounded operator remain
injective and have dense range. The inverse exists only on that actual
range. The proof uses genuine continuous functional calculus and the
zero-eigenvector implication, without a bounded-inverse assumption.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positive_rpow_injective {A : E →L[ℂ] E} (hA : 0 ≤ A)
    (hinj : Function.Injective A) {s : ℝ} (hs : 0 < s) :
    Function.Injective (A ^ s) := by
  have hz : ∀ x : E, (A ^ s) x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have heig : (A ^ s) x = (0 : ℝ) • x := by simpa only [zero_smul] using hx
    have hh := rpow_apply_eigenvector (CFC.rpow_nonneg (a := A) (y := s))
      (eigenvalue_mem_real_spectrum hne heig) heig (inv_pos.mpr hs)
    rw [CFC.rpow_rpow_of_exponent_nonneg A s s⁻¹ hs.le (inv_nonneg.mpr hs.le) hA,
      mul_inv_cancel₀ hs.ne', CFC.rpow_one A hA,
      Real.zero_rpow (inv_ne_zero hs.ne'), zero_smul] at hh
    exact hne (hinj (hh.trans (map_zero A).symm))
  intro x y hxy
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hxy, sub_self]

theorem selfAdjoint_injective_denseRange {A : E →L[ℂ] E}
    (hs : IsSelfAdjoint A) (hinj : Function.Injective A) : DenseRange A := by
  have hk : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hc := A.orthogonal_ker
  rw [hk, Submodule.bot_orthogonal_eq_top, hs.adjoint_eq] at hc
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hc.symm

theorem positive_rpow_denseRange {A : E →L[ℂ] E} (hA : 0 ≤ A)
    (hinj : Function.Injective A) {s : ℝ} (hs : 0 < s) :
    DenseRange (A ^ s) :=
  selfAdjoint_injective_denseRange (CFC.rpow_nonneg (a := A) (y := s)).isSelfAdjoint
    (positive_rpow_injective hA hinj hs)

theorem faithful_power_sandwich_unique {σ : E →L[ℂ] E}
    (hσ : IsFaithfulDensity σ) {s : ℝ} (hs : 0 < s)
    {Θ Ξ : E →L[ℂ] E} (h : σ ^ s * Θ * σ ^ s = σ ^ s * Ξ * σ ^ s) : Θ = Ξ :=
  sandwich_factorization_unique (σ ^ s)
    (positive_rpow_injective hσ.1 hσ.2.2 hs)
    (positive_rpow_denseRange hσ.1 hσ.2.2 hs) h

end VacuumBellSeparation.Gaussian

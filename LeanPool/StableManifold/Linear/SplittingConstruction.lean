/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Linear.HyperbolicSplitting
public import LeanPool.StableManifold.Linear.FiniteDimensionalSubspaces
import Mathlib.LinearAlgebra.Projection

/-! # Constructing an exponential splitting in finite dimension -/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A hyperbolic splitting exists** in finite dimension when the stable and unstable subspaces
are complementary.

Proof: `P` projects onto the stable subspace. Invert the restriction of `A` to the
unstable subspace and precompose with the complementary projection to obtain `B`.
The orbits of `A P` and of `B` tend to zero, so their powers decay geometrically. -/
theorem nonempty_hyperbolicSplitting [FiniteDimensional ℝ E] {A : E →L[ℝ] E}
    (h : IsCompl A.stableSubspace A.unstableSubspace) : Nonempty A.HyperbolicSplitting := by
  -- The projection `P` onto `Eₛ` along `Eᵤ`, continuous in finite dimension.
  let P : E →L[ℝ] E :=
    LinearMap.toContinuousLinearMap (A.stableSubspace.projection A.unstableSubspace h)
  have hPs (x : E) : P x ∈ A.stableSubspace := Submodule.projection_apply_mem h x
  have hPu (x : E) : x - P x ∈ A.unstableSubspace := Submodule.sub_projection_mem h x
  have hPself {x : E} (hx : x ∈ A.stableSubspace) : P x = x :=
    Submodule.projection_apply_of_mem_left h hx
  have hPzero {x : E} : P x = 0 ↔ x ∈ A.unstableSubspace :=
    Submodule.projection_apply_eq_zero_iff h
  have hPP : P * P = P := by
    ext x
    exact hPself (hPs x)
  -- `A` commutes with `P`, since it preserves `Eₛ` and `Eᵤ`.
  have hAP : A * P = P * A := by
    ext x
    have e : A x = A (P x) + A (x - P x) := by rw [← map_add, add_sub_cancel]
    change A (P x) = P (A x)
    rw [e, map_add, hPself (map_mem_stableSubspace (hPs x)),
      hPzero.2 (map_mem_unstableSubspace (hPu x)), add_zero]
  let T : A.unstableSubspace →L[ℝ] A.unstableSubspace :=
    A.restrict fun _ hx ↦ map_mem_unstableSubspace hx
  have hT : Function.Bijective T := by
    refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
    · exact Subtype.ext (injOn_unstableSubspace A x.2 y.2 (congrArg Subtype.val hxy))
    · obtain ⟨y, hy, heq⟩ := exists_mem_unstableSubspace_apply_eq x.2
      exact ⟨⟨y, hy⟩, Subtype.ext heq⟩
  let e : A.unstableSubspace ≃L[ℝ] A.unstableSubspace :=
    (LinearEquiv.ofBijective (T : A.unstableSubspace →ₗ[ℝ] A.unstableSubspace) hT)
      |>.toContinuousLinearEquiv
  let Q := (1 - P).codRestrict A.unstableSubspace fun x ↦ by
    simpa only [sub_apply, one_apply_eq_self] using hPu x
  let B : E →L[ℝ] E := A.unstableSubspace.subtypeL ∘L e.symm.toContinuousLinearMap ∘L Q
  have hAB : A * B = 1 - P := by
    ext x
    change A (e.symm (Q x) : E) = (Q x : E)
    exact congrArg Subtype.val (e.apply_symm_apply (Q x))
  have hBA : B * A = 1 - P := by
    ext x
    change (e.symm (Q (A x)) : E) = (Q x : E)
    have hQ : Q (A x) = e (Q x) := by
      apply Subtype.ext
      change (1 - P) (A x) = A ((1 - P) x)
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, sub_mul, mul_sub, one_mul, mul_one, hAP]
    rw [hQ, e.symm_apply_apply]
  have hBP : B * P = 0 := by
    ext x
    change (e.symm (Q (P x)) : E) = 0
    have hQ : Q (P x) = 0 := by
      apply Subtype.ext
      change (1 - P) (P x) = 0
      rw [sub_apply, one_apply_eq_self, hPself (hPs x), sub_self]
    rw [hQ, map_zero, Submodule.coe_zero]
  -- Geometric decay on `Eₛ`: the orbits of `A P` tend to `0`.
  have hc : Commute A P := hAP
  have hQ (n : ℕ) : (A * P) ^ n * P = A ^ n * P := by
    rw [hc.mul_pow, mul_assoc, ← pow_succ, IsIdempotentElem.pow_succ_eq n hPP]
  have hQt (v : E) : Tendsto (fun n : ℕ ↦ ((A * P) ^ n) v) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have hv (n : ℕ) : ((A * P) ^ (n + 1)) v = (A ^ (n + 1)) (P v) := by
      rw [hc.mul_pow, mul_apply_eq_comp, IsIdempotentElem.pow_succ_eq n hPP]
    simp_rw [hv]
    exact (tendsto_add_atTop_iff_nat 1).2 (mem_stableSubspace.1 (hPs v))
  obtain ⟨C₁, r₁, hC₁, hr₁, hr₁', hCr₁⟩ := exists_norm_pow_le_mul_pow_of_tendsto (A * P) hQt
  -- Geometric decay on `Eᵤ`: the orbits of `B` tend to `0`, being backward orbits of `A`.
  have hBu {u : E} (hu : u ∈ A.unstableSubspace) :
      Tendsto (fun n : ℕ ↦ (B ^ n) u) atTop (𝓝 0) := by
    obtain ⟨w, hw0, hwA, hwt⟩ := hu
    have hwmem (n : ℕ) : w n ∈ A.unstableSubspace :=
      ⟨fun k ↦ w (k + n), by simp, fun k ↦ by
        change A (w (k + 1 + n)) = w (k + n); rw [Nat.add_right_comm]; exact hwA _,
        (tendsto_add_atTop_iff_nat n).2 hwt⟩
    have hBw (n : ℕ) : B (w n) = w (n + 1) := by
      rw [← hwA n, ← mul_apply_eq_comp B A, hBA, sub_apply, one_apply_eq_self,
        hPzero.2 (hwmem (n + 1)), sub_zero]
    have hBpow (n : ℕ) : (B ^ n) u = w n := by
      induction n with
      | zero => rw [pow_zero, one_apply_eq_self, hw0]
      | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, hBw]
    exact hwt.congr fun n ↦ (hBpow n).symm
  have hBt (v : E) : Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have hBv : B v ∈ A.unstableSubspace := (e.symm (Q v)).2
    simp_rw [pow_succ, mul_apply_eq_comp]
    exact hBu hBv
  obtain ⟨C₂, r₂, hC₂, hr₂, hr₂', hCr₂⟩ := exists_norm_pow_le_mul_pow_of_tendsto B hBt
  -- The constants.
  have hK : 1 ≤ max 1 (max ‖P‖ ‖1 - P‖) := le_max_left _ _
  have hCr (n : ℕ) {C r a : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (ha : 0 ≤ a) (hCm : C ≤ max C₁ C₂)
      (hrm : r ≤ max r₁ r₂) (ham : a ≤ max 1 (max ‖P‖ ‖1 - P‖)) :
      C * r ^ n * a ≤ max C₁ C₂ * max 1 (max ‖P‖ ‖1 - P‖) * max r₁ r₂ ^ n := by
    have hpow : r ^ n ≤ max r₁ r₂ ^ n := pow_le_pow_left₀ hr hrm n
    have hproduct : C * r ^ n ≤ max C₁ C₂ * max r₁ r₂ ^ n :=
      mul_le_mul hCm hpow (pow_nonneg hr n) (hC.trans hCm)
    calc
      C * r ^ n * a ≤ max C₁ C₂ * max r₁ r₂ ^ n * max 1 (max ‖P‖ ‖1 - P‖) :=
        mul_le_mul hproduct ham ha (mul_nonneg (hC.trans hCm) ((pow_nonneg hr n).trans hpow))
      _ = _ := mul_right_comm _ _ _
  refine ⟨{
    proj := P
    unstableInv := B
    const := max C₁ C₂ * max 1 (max ‖P‖ ‖1 - P‖)
    rate := max r₁ r₂
    unstableInv_mul_proj := hBP
    mul_unstableInv := hAB
    unstableInv_mul := hBA
    one_le_const := one_le_mul_of_one_le_of_one_le (hC₁.trans (le_max_left _ _)) hK
    rate_pos := hr₁.trans_le (le_max_left _ _)
    rate_lt_one := max_lt hr₁' hr₂'
    norm_pow_mul_proj_le := fun n ↦ ?_
    norm_unstableInv_pow_mul_le := fun n ↦ ?_ }⟩
  · calc ‖A ^ n * P‖ = ‖(A * P) ^ n * P‖ := by rw [hQ]
      _ ≤ ‖(A * P) ^ n‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ C₁ * r₁ ^ n * ‖P‖ := mul_le_mul_of_nonneg_right (hCr₁ n) (norm_nonneg _)
      _ ≤ _ := hCr n (zero_le_one.trans hC₁) hr₁.le (norm_nonneg _)
          (le_max_left _ _) (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
  · calc ‖B ^ n * (1 - P)‖ ≤ ‖B ^ n‖ * ‖1 - P‖ := norm_mul_le _ _
      _ ≤ C₂ * r₂ ^ n * ‖1 - P‖ := mul_le_mul_of_nonneg_right (hCr₂ n) (norm_nonneg _)
      _ ≤ _ := hCr n (zero_le_one.trans hC₂) hr₂.le (norm_nonneg _)
          (le_max_right _ _) (le_max_right _ _) ((le_max_right _ _).trans (le_max_right _ _))

end ContinuousLinearMap

/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Linear.HyperbolicSplitting
public import LeanPool.StableManifold.Linear.Splitting

/-! # Constructing an exponential splitting in finite dimension -/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A hyperbolic splitting exists** in finite dimension when the stable and unstable subspaces
are complementary.

Proof: `P` is the projection onto `Eₛ` along `Eᵤ`; `T = A (1 - P) + P` is invertible, and
`B = T⁻¹ (1 - P)`. The orbits of `A P` and of `B` tend to `0`, so their powers decay
geometrically (`exists_norm_pow_le_mul_pow_of_tendsto`), and `Aⁿ P = (A P)ⁿ P`. -/
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
  have hP1 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hP2 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  -- `T = A (1 - P) + P` (`A` on `Eᵤ`, the identity on `Eₛ`) is injective, hence invertible.
  set T : E →L[ℝ] E := A * (1 - P) + P with hT
  have hTP : T * P = P := by rw [hT, add_mul, mul_assoc, hP1, mul_zero, zero_add, hPP]
  have hPT : P * T = P := by
    rw [hT, mul_add, ← mul_assoc, ← hAP, mul_assoc, hP2, mul_zero, zero_add, hPP]
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hPx : P x = 0 := by rw [← hPT, mul_apply_eq_comp, hx, map_zero]
    have hAx : A x = A 0 := by
      rw [map_zero, ← hx, hT, add_apply, hPx, add_zero, mul_apply_eq_comp, sub_apply,
        one_apply_eq_self, hPx, sub_zero]
    exact injOn_unstableSubspace A (hPzero.1 hPx) A.unstableSubspace.zero_mem hAx
  let e : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (T : E →ₗ[ℝ] E) hTinj).toContinuousLinearEquiv
  have he (x : E) : e x = T x := rfl
  set R : E →L[ℝ] E := (e.symm : E →L[ℝ] E)
  have hTR : T * R = 1 := by
    ext x
    rw [mul_apply_eq_comp, ← he]
    exact e.apply_symm_apply x
  have hRT : R * T = 1 := by
    ext x
    rw [mul_apply_eq_comp, ← he]
    exact e.symm_apply_apply x
  have hRP : R * P = P := calc
    R * P = R * (T * P) := by rw [hTP]
    _ = P := by rw [← mul_assoc, hRT, one_mul]
  have hPR : P * R = P := calc
    P * R = P * T * R := by rw [hPT]
    _ = P := by rw [mul_assoc, hTR, mul_one]
  -- `B = T⁻¹ (1 - P) = (1 - P) T⁻¹` inverts `A` on `Eᵤ`.
  set B : E →L[ℝ] E := R * (1 - P) with hB
  have hB' : B = (1 - P) * R := by rw [hB, mul_sub, sub_mul, mul_one, one_mul, hRP, hPR]
  have hA1 : (1 - P) * A = A * (1 - P) := by rw [sub_mul, mul_sub, one_mul, mul_one, hAP]
  have hA2 : A * (1 - P) = T * (1 - P) := by
    rw [mul_sub T, mul_one, hTP, hT, add_sub_cancel_right]
  have hA3 : A * (1 - P) = (1 - P) * T := by
    rw [sub_mul, one_mul, hPT, hT, add_sub_cancel_right]
  have hBA : B * A = 1 - P := by
    rw [hB, mul_assoc, hA1, hA2, ← mul_assoc, hRT, one_mul]
  have hAB : A * B = 1 - P := by
    rw [hB', ← mul_assoc, hA3, mul_assoc, hTR, mul_one]
  have hBP : B * P = 0 := by rw [hB, mul_assoc, hP1, mul_zero]
  have hPB : P * B = 0 := by rw [hB, ← mul_assoc, hPR, hP2]
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
    have hBv : B v ∈ A.unstableSubspace := by
      rw [← hPzero, ← mul_apply_eq_comp P B, hPB, zero_apply]
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

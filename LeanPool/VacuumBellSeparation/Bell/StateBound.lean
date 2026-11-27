/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Reflections

/-!
# Norm bound for states and boundedness of the CHSH values

* `State.norm_apply_le` : `‖ω T‖ ≤ 2 * ‖T‖` for a state `ω` on `B(H)`.
* `bddAbove_chshValues` : the set of CHSH values is bounded above.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a self-adjoint contraction a state takes a real value in `[-1, 1]`. -/
theorem State.im_eq_zero_and_abs_re_le_one (ω : State H) {S : H →L[ℂ] H}
    (hsa : IsSelfAdjoint S) (hn : ‖S‖ ≤ 1) : (ω S).im = 0 ∧ |(ω S).re| ≤ 1 := by
  have hp := ω.map_nonneg' _ (isPositive_one_add_of_saContraction hsa hn)
  have hm := ω.map_nonneg' _ (isPositive_one_sub_of_saContraction hsa hn)
  have e1 : ω.toLinearMap (1 + S) = 1 + ω.toLinearMap S := by rw [map_add, ω.map_one']
  have e2 : ω.toLinearMap (1 - S) = 1 - ω.toLinearMap S := by rw [map_sub, ω.map_one']
  rw [e1] at hp
  rw [e2] at hm
  have hp1 : (ω.toLinearMap S).im = 0 := by
    have h := hp.1
    first
      | (rw [Complex.add_im, Complex.one_im, zero_add] at h; exact h)
  have hp2 : 0 ≤ 1 + (ω.toLinearMap S).re := by
    have h := hp.2
    first
      | (rw [Complex.add_re, Complex.one_re] at h; exact h)
  have hm2 : 0 ≤ 1 - (ω.toLinearMap S).re := by
    have h := hm.2
    first
      | (rw [Complex.sub_re, Complex.one_re] at h; exact h)
  exact ⟨hp1, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- A state is bounded by `r` on self-adjoint operators of norm at most `r`. -/
theorem State.norm_apply_le_of_isSelfAdjoint (ω : State H) {S : H →L[ℂ] H}
    (hsa : IsSelfAdjoint S) {r : ℝ} (hr : 0 < r) (hn : ‖S‖ ≤ r) : ‖ω S‖ ≤ r := by
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hstar : star ((r⁻¹ : ℝ) : ℂ) = ((r⁻¹ : ℝ) : ℂ) := by
    first
      | exact Complex.conj_ofReal _
  have hsa' : IsSelfAdjoint (((r⁻¹ : ℝ) : ℂ) • S) := by
    first
      | (rw [isSelfAdjoint_iff, star_smul, hsa.star_eq, hstar])
  have hnc : ‖((r⁻¹ : ℝ) : ℂ)‖ = r⁻¹ := by
    first
      | exact Complex.norm_of_nonneg hri.le
  have hn' : ‖((r⁻¹ : ℝ) : ℂ) • S‖ ≤ 1 := by
    rw [norm_smul, hnc]
    calc r⁻¹ * ‖S‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hn hri.le
      _ = 1 := inv_mul_cancel₀ hr.ne'
  obtain ⟨him, hre⟩ := ω.im_eq_zero_and_abs_re_le_one hsa' hn'
  have hS : ((r : ℝ) : ℂ) • (((r⁻¹ : ℝ) : ℂ) • S) = S := by
    first
      | (rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one,
          one_smul])
  have hval : ω.toLinearMap S
      = ((r : ℝ) : ℂ) * ω.toLinearMap (((r⁻¹ : ℝ) : ℂ) • S) := by
    have h1 : ω.toLinearMap (((r : ℝ) : ℂ) • (((r⁻¹ : ℝ) : ℂ) • S))
        = ((r : ℝ) : ℂ) * ω.toLinearMap (((r⁻¹ : ℝ) : ℂ) • S) :=
      map_smul ω.toLinearMap _ _
    rw [hS] at h1
    exact h1
  have hle : ‖ω.toLinearMap (((r⁻¹ : ℝ) : ℂ) • S)‖ ≤ 1 := by
    have hz : ω.toLinearMap (((r⁻¹ : ℝ) : ℂ) • S)
        = (((ω.toLinearMap (((r⁻¹ : ℝ) : ℂ) • S)).re : ℝ) : ℂ) :=
      (ofReal_re_eq_of_im_eq_zero him).symm
    rw [hz]
    first
      | (rw [Complex.norm_real, Real.norm_eq_abs]; exact hre)
  have hrn : ‖((r : ℝ) : ℂ)‖ = r := by
    first
      | exact Complex.norm_of_nonneg hr.le
  rw [hval, norm_mul, hrn]
  calc r * ‖ω.toLinearMap (((r⁻¹ : ℝ) : ℂ) • S)‖ ≤ r * 1 :=
        mul_le_mul_of_nonneg_left hle hr.le
    _ = r := mul_one r

/-- **Norm bound for states**: `‖ω T‖ ≤ 2 * ‖T‖`. -/
theorem State.norm_apply_le (ω : State H) (T : H →L[ℂ] H) : ‖ω T‖ ≤ 2 * ‖T‖ := by
  by_cases hT : T = 0
  · subst hT
    have h0 : ω.toLinearMap (0 : H →L[ℂ] H) = 0 := map_zero _
    have h1 : ‖ω.toLinearMap (0 : H →L[ℂ] H)‖ = 0 := by rw [h0, norm_zero]
    have h2 : (2 : ℝ) * ‖(0 : H →L[ℂ] H)‖ = 0 := by rw [norm_zero, mul_zero]
    exact le_of_eq (h1.trans h2.symm)
  · have hr : 0 < 2 * ‖T‖ := mul_pos two_pos (norm_pos_iff.mpr hT)
    have hs : ‖star T‖ = ‖T‖ := norm_star T
    have hPsa : IsSelfAdjoint (T + star T) := by
      rw [isSelfAdjoint_iff, star_add, star_star, add_comm]
    have hI : star Complex.I = -Complex.I := by
      first
        | exact Complex.conj_I
    have hQsa : IsSelfAdjoint (Complex.I • (star T - T)) := by
      first
        | (rw [isSelfAdjoint_iff, star_smul, star_sub, star_star, hI, neg_smul, ← smul_neg,
            neg_sub])
    have hPn : ‖T + star T‖ ≤ 2 * ‖T‖ := by
      have h := norm_add_le T (star T)
      linarith
    have hQn : ‖Complex.I • (star T - T)‖ ≤ 2 * ‖T‖ := by
      have h := norm_sub_le (star T) T
      rw [norm_smul, Complex.norm_I, one_mul]
      linarith
    have hP := ω.norm_apply_le_of_isSelfAdjoint hPsa hr hPn
    have hQ := ω.norm_apply_le_of_isSelfAdjoint hQsa hr hQn
    have hII : Complex.I • (Complex.I • (star T - T)) = T - star T := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_sub]
    have hdecomp : (T + star T) + Complex.I • (Complex.I • (star T - T)) = T + T := by
      rw [hII]; abel
    have h2 : ω.toLinearMap ((T + star T) + Complex.I • (Complex.I • (star T - T)))
        = ω.toLinearMap (T + star T)
          + Complex.I * ω.toLinearMap (Complex.I • (star T - T)) := by
      rw [map_add, map_smul, smul_eq_mul]
    have h3 : ω.toLinearMap (T + T) = ω.toLinearMap T + ω.toLinearMap T := map_add _ _ _
    rw [hdecomp, h3] at h2
    have h4 : ‖ω.toLinearMap T + ω.toLinearMap T‖ = 2 * ‖ω.toLinearMap T‖ := by
      have e : ω.toLinearMap T + ω.toLinearMap T = (2 : ℝ) • ω.toLinearMap T :=
        (two_smul ℝ _).symm
      first
        | (rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (two_pos : (0 : ℝ) < 2)])
    have hmul : ‖Complex.I * ω.toLinearMap (Complex.I • (star T - T))‖
        = ‖ω.toLinearMap (Complex.I • (star T - T))‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have h5 := norm_add_le (ω.toLinearMap (T + star T))
      (Complex.I * ω.toLinearMap (Complex.I • (star T - T)))
    rw [hmul, ← h2, h4] at h5
    linarith

/-- The CHSH operator of four contractions has norm at most `4`. -/
theorem norm_chshOp_le {A₀ A₁ B₀ B₁ : H →L[ℂ] H} (hA₀ : ‖A₀‖ ≤ 1) (hA₁ : ‖A₁‖ ≤ 1)
    (hB₀ : ‖B₀‖ ≤ 1) (hB₁ : ‖B₁‖ ≤ 1) : ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 4 := by
  have hs : ‖B₀ + B₁‖ ≤ 2 := by
    have h := norm_add_le B₀ B₁
    linarith
  have hd : ‖B₀ - B₁‖ ≤ 2 := by
    have h := norm_sub_le B₀ B₁
    linarith
  have h1 : ‖A₀ * (B₀ + B₁)‖ ≤ 2 := by
    have h := norm_mul_le A₀ (B₀ + B₁)
    have h' : ‖A₀‖ * ‖B₀ + B₁‖ ≤ 1 * 2 := mul_le_mul hA₀ hs (norm_nonneg _) zero_le_one
    linarith
  have h2 : ‖A₁ * (B₀ - B₁)‖ ≤ 2 := by
    have h := norm_mul_le A₁ (B₀ - B₁)
    have h' : ‖A₁‖ * ‖B₀ - B₁‖ ≤ 1 * 2 := mul_le_mul hA₁ hd (norm_nonneg _) zero_le_one
    linarith
  change ‖A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)‖ ≤ 4
  have h3 := norm_add_le (A₀ * (B₀ + B₁)) (A₁ * (B₀ - B₁))
  linarith

/-- The set of CHSH values of a state is bounded above (by `4`). -/
theorem bddAbove_chshValues (ω : State H) (𝔄 𝔅 : VonNeumannAlgebra H) :
    BddAbove (chshValues ω 𝔄 𝔅) := by
  refine ⟨4, ?_⟩
  intro x hx
  obtain ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩ := hx
  have hA₀' : A₀ ∈ 𝔄 ∧ IsSelfAdjoint A₀ ∧ ‖A₀‖ ≤ 1 := hA₀
  have hA₁' : A₁ ∈ 𝔄 ∧ IsSelfAdjoint A₁ ∧ ‖A₁‖ ≤ 1 := hA₁
  have hB₀' : B₀ ∈ 𝔅 ∧ IsSelfAdjoint B₀ ∧ ‖B₀‖ ≤ 1 := hB₀
  have hB₁' : B₁ ∈ 𝔅 ∧ IsSelfAdjoint B₁ ∧ ‖B₁‖ ≤ 1 := hB₁
  have h := ω.norm_apply_le (chshOp A₀ A₁ B₀ B₁)
  have h' := norm_chshOp_le hA₀'.2.2 hA₁'.2.2 hB₀'.2.2 hB₁'.2.2
  linarith

end VacuumBellSeparation

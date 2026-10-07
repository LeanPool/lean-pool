/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseDecay
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Balls reaching the positive normal phase

At each time before one, the positive normal-phase region reaches
arbitrarily high above the boundary. A ball centered there can contain
any prescribed interior point while remaining in the half-space.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The normal phase eventually exceeds its fixed threshold at every
time strictly between one half and one. -/
theorem bu_short_phase_positive_at_high_center
    {scale s y₃ : ℝ}
    (hs : 1 / 2 < s) (hs1 : s < 1) :
    ∃ H : ℝ, y₃ < H ∧ 1 < H ∧
      buShortB scale < buShortF H s := by
  let c := (1 - s) * s ^ (-(3 / 4 : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    have hs0 : 0 < s := lt_trans (by norm_num) hs
    positivity
  let T := max 1 (max y₃ (buShortB scale / c))
  let H := T + 1
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTy : y₃ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTB : buShortB scale / c ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hTH : T < H := by
    dsimp [H]
    exact lt_add_of_pos_right T (by norm_num : (0 : ℝ) < 1)
  have hH1 : 1 < H := lt_of_le_of_lt hT1 hTH
  have hHy : y₃ < H := lt_of_le_of_lt hTy hTH
  have hBc : buShortB scale < c * H := by
    have h := (div_le_iff₀ hc).1 hTB
    calc
      buShortB scale ≤ T * c := h
      _ = c * T := by ring
      _ < c * H := mul_lt_mul_of_pos_left hTH hc
  have hpow : H ≤ H ^ (3 / 2 : ℝ) :=
    Real.self_le_rpow_of_one_le hH1.le (by norm_num)
  have hF : buShortF H s = c * H ^ (3 / 2 : ℝ) := by
    dsimp [buShortF, c]
    ring
  refine ⟨H, hHy, hH1, ?_⟩
  rw [hF]
  exact hBc.trans_le (mul_le_mul_of_nonneg_left hpow hc.le)

/-- A high center with positive normal phase admits a half-space ball
containing an arbitrary target point. -/
theorem bu_short_positive_phase_ball
    {scale s : ℝ}
    (hs : 1 / 2 < s) (hs1 : s < 1)
    (y : Vec3) (hy : 0 < y 2) :
    ∃ c : Vec3, ∃ R : ℝ,
      0 < R ∧ y ∈ vec3Ball c R ∧
      vec3Ball c R ⊆ {x : Vec3 | 0 < x 2} ∧
      buShortB scale < buShortF (c 2) s := by
  obtain ⟨H, hHy, _, hphase⟩ :=
    bu_short_phase_positive_at_high_center hs hs1 (y₃ := y 2) (scale := scale)
  let c : Vec3 := fun i => if i = (2 : Fin 3) then H else y i
  let R := H - y 2 / 2
  have hR : 0 < R := by dsimp [R]; linarith only [hHy, hy]
  have hc2 : c 2 = H := by simp [c]
  have hdist : vec3EuclideanNorm (y - c) ≤ H - y 2 := by
    calc
      vec3EuclideanNorm (y - c) ≤
          ∑ i : Fin 3, |(y - c) i| := vec3EuclideanNorm_le_sum_abs _
      _ = H - y 2 := by
        simp only [Fin.sum_univ_three, Pi.sub_apply]
        have h0 : c 0 = y 0 := by simp [c]
        have h1 : c 1 = y 1 := by simp [c]
        rw [h0, h1, hc2]
        simp only [sub_self, abs_zero, zero_add]
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hHy.le)]
  have hyball : y ∈ vec3Ball c R := by
    apply (mem_vec3Ball).2
    dsimp [R]
    nlinarith only [hdist, hy]
  have hballHalf : vec3Ball c R ⊆ {x : Vec3 | 0 < x 2} := by
    intro x hx
    have hnorm := (mem_vec3Ball).1 hx
    have hcoord := abs_apply_le_vec3EuclideanNorm (x - c) 2
    have hdiff : |x 2 - H| < R := by
      simpa only [Pi.sub_apply, hc2] using hcoord.trans_lt hnorm
    have hleft := (abs_lt.mp hdiff).1
    dsimp [R] at hleft
    change 0 < x 2
    linarith only [hleft, hy]
  exact ⟨c, R, hR, hyball, hballHalf, by simpa [hc2] using hphase⟩

end ESS

/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Inv


/-!
# M5: the top structure's parameter conditions for `a = 8`, `s = 11`, `β = 64`

Heights `1, 2, 3` are checked by computation. Above, every quantity is linear in `x = 8^k`
(with floors by constants), once the two quotients `(τ_h - 1)/λ_{h-1}` and `Π_h/γ_{h-1}` are
bounded by constants (17 and 30).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model

theorem pows (k : Nat) : (8 : Nat) ^ (k + 4) = 4096 * 8 ^ k ∧ (8 : Nat) ^ (k + 3) = 512 * 8 ^ k ∧
    (8 : Nat) ^ (k + 2) = 64 * 8 ^ k := ⟨by ring, by ring, by ring⟩

section
variable {P : Params} (ha : P.a = 8) (hs : P.s = 11)
include ha hs

theorem Wd_eq (h : Nat) : Wd P h = 2 * 8 ^ h := by unfold Wd; rw [ha]
theorem Kd_eq (h : Nat) : Kd P h = (2 * 8 ^ h + 2) / 9 + 1 := by unfold Kd; rw [Wd_eq ha hs, hs]
theorem Pid_eq (h : Nat) : Pid P h = 2 * 8 ^ h + 2 + 2 * ((2 * 8 ^ h + 2) / 9 + 1) := by
  unfold Pid; rw [Wd_eq ha hs, Kd_eq ha hs]
theorem taud_eq (k : Nat) : taud P (k + 2) = 8 ^ (k + 2) + 1 + Pid P (k + 1) := by
  show P.a ^ (k + 2) + 1 + Pid P (k + 1) = _; rw [ha]
theorem lamd_eq (k : Nat) : lamd P (k + 2) = 8 ^ (k + 2) + 1 - Pid P (k + 1) := by
  show P.a ^ (k + 2) + 1 - Pid P (k + 1) = _; rw [ha]

theorem s3_8 : 3 ≤ P.s := by rw [hs]; omega

theorem lamK_8 (h : Nat) (h1 : 1 ≤ h) : 2 + 2 * Kd P h ≤ lamd P h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rcases k with _ | k
  · rw [Kd_eq ha hs]; show _ ≤ P.a; rw [ha]; norm_num
  · rw [show k + 1 + 1 = k + 2 from rfl, lamd_eq ha hs, Kd_eq ha hs, Pid_eq ha hs]
    have hx : 1 ≤ 8 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [show (8 : Nat) ^ (k + 2) = 64 * 8 ^ k by ring, show (8 : Nat) ^ (k + 1) = 8 * 8 ^ k by ring]
    generalize 8 ^ k = x at hx ⊢
    omega

theorem piW_8 (h : Nat) (h2 : 2 ≤ h) : Pid P (h - 1) ≤ Wd P h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rw [Nat.add_sub_cancel, Pid_eq ha hs, Wd_eq ha hs, show (8 : Nat) ^ (k + 1) = 8 * 8 ^ k by ring]
  have hx : 1 ≤ 8 ^ k := Nat.one_le_pow _ _ (by norm_num)
  generalize 8 ^ k = x at hx ⊢
  omega

theorem gam1_8 (h : Nat) (h1 : 1 ≤ h) : 1 ≤ gamd P h := by
  unfold gamd
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rcases k with _ | k
  · rw [Wd_eq ha hs]; show 1 ≤ 2 * 8 ^ 1 + 1 - (P.a + 1); rw [ha]; norm_num
  · rw [show k + 1 + 1 = k + 2 from rfl, taud_eq ha hs, Wd_eq ha hs, Pid_eq ha hs,
      show (8 : Nat) ^ (k + 2) = 8 * 8 ^ (k + 1) by ring]
    have hx : 1 ≤ 8 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    generalize 8 ^ (k + 1) = x at hx ⊢
    omega

theorem n0max_le (k : Nat) : n0max P (k + 4) ≤ 27 := by
  unfold n0max
  rw [ite_eq_right (by omega), show k + 4 - 1 = k + 1 + 2 from rfl]
  have hq : (taud P (k + 4) - 1) / lamd P (k + 1 + 2) ≤ 17 := by
    apply Nat.div_le_of_le_mul
    rw [show k + 4 = (k + 2) + 2 from rfl, taud_eq ha hs, lamd_eq ha hs, Pid_eq ha hs, Pid_eq ha hs]
    obtain ⟨p4, p3, p2⟩ := pows k
    rw [show k + 2 + 2 = k + 4 from rfl, show k + 2 + 1 = k + 3 from rfl,
      show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl, p4, p3, p2]
    have hx : 1 ≤ 8 ^ k := Nat.one_le_pow _ _ (by norm_num)
    generalize 8 ^ k = x at hx ⊢
    omega
  generalize (taud P (k + 4) - 1) / lamd P (k + 1 + 2) = q at hq
  omega

theorem Dmax_le (k : Nat) : Dmax P (k + 4) ≤ 58 := by
  have hn := n0max_le ha hs k
  unfold Dmax
  rw [ite_eq_right (by omega), show k + 4 - 1 = k + 3 from rfl]
  have hr : Pid P (k + 4) / gamd P (k + 3) ≤ 30 := by
    apply Nat.div_le_of_le_mul
    unfold gamd
    rw [show k + 3 = (k + 1) + 2 from rfl, taud_eq ha hs, Wd_eq ha hs, Pid_eq ha hs, Pid_eq ha hs]
    obtain ⟨p4, p3, p2⟩ := pows k
    rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl, p4, p3, p2]
    have hx : 1 ≤ 8 ^ k := Nat.one_le_pow _ _ (by norm_num)
    generalize 8 ^ k = x at hx ⊢
    omega
  generalize Pid P (k + 4) / gamd P (k + 3) = r at hr
  omega

theorem room_8 (hb : P.beta = 64) (h : Nat) (h1 : 1 ≤ h) : 2 ^ Dmax P h * (n0max P h + 1) ≤ 2 ^ P.beta := by
  rw [hb]
  have hP1 : Pid P 1 = 24 := by rw [Pid_eq ha hs]; norm_num
  have hP2 : Pid P 2 = 160 := by rw [Pid_eq ha hs]; norm_num
  have hP3 : Pid P 3 = 1256 := by rw [Pid_eq ha hs]; norm_num
  have ht1 : taud P 1 = 9 := by show P.a + 1 = 9; rw [ha]
  have hl1 : lamd P 1 = 8 := by show P.a = 8; rw [ha]
  have ht2 : taud P 2 = 89 := by rw [show 2 = 0 + 2 from rfl, taud_eq ha hs, hP1]; norm_num
  have hl2 : lamd P 2 = 41 := by rw [show 2 = 0 + 2 from rfl, lamd_eq ha hs, hP1]; norm_num
  have ht3 : taud P 3 = 673 := by rw [show 3 = 1 + 2 from rfl, taud_eq ha hs, hP2]; norm_num
  have hg1 : gamd P 1 = 8 := by unfold gamd; rw [Wd_eq ha hs, ht1]; norm_num
  have hg2 : gamd P 2 = 40 := by unfold gamd; rw [Wd_eq ha hs, ht2]; norm_num
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rcases k with _ | _ | _ | k
  · have hn : n0max P 1 = 9 := by unfold n0max; rw [ite_eq_left le_rfl, ha]
    have hd : Dmax P 1 = 12 := by unfold Dmax; rw [ite_eq_left le_rfl, hP1]
    rw [hn, hd]; norm_num
  · have hn : n0max P 2 = 18 := by unfold n0max; rw [ite_eq_right (by omega), ht2,
    show 2 - 1 = 1 from rfl, hl1]
    have hd : Dmax P 2 = 39 := by
      unfold Dmax; rw [ite_eq_right (by omega), hn, hP2, show 2 - 1 = 1 from rfl, hg1]
    rw [show 0 + 1 + 1 = 2 from rfl, hn, hd]; norm_num
  · have hn : n0max P 3 = 25 := by unfold n0max; rw [ite_eq_right (by omega), ht3,
    show 3 - 1 = 2 from rfl, hl2]
    have hd : Dmax P 3 = 57 := by
      unfold Dmax; rw [ite_eq_right (by omega), hn, hP3, show 3 - 1 = 2 from rfl, hg2]
    rw [show 0 + 1 + 1 + 1 = 3 from rfl, hn, hd]; norm_num
  · rw [show k + 1 + 1 + 1 + 1 = k + 4 from rfl]
    have hn := n0max_le ha hs k
    have hd := Dmax_le ha hs k
    calc 2 ^ Dmax P (k + 4) * (n0max P (k + 4) + 1) ≤ 2 ^ 58 * 28 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hd) (by omega)
      _ ≤ 2 ^ 64 := by norm_num

theorem tab_8 (h : Nat) (h1 : 1 ≤ h) : n0max P h + 2 * Dmax P h ≤ 160 := by
  have hP1 : Pid P 1 = 24 := by rw [Pid_eq ha hs]; norm_num
  have hP2 : Pid P 2 = 160 := by rw [Pid_eq ha hs]; norm_num
  have hP3 : Pid P 3 = 1256 := by rw [Pid_eq ha hs]; norm_num
  have ht1 : taud P 1 = 9 := by show P.a + 1 = 9; rw [ha]
  have hl1 : lamd P 1 = 8 := by show P.a = 8; rw [ha]
  have ht2 : taud P 2 = 89 := by rw [show 2 = 0 + 2 from rfl, taud_eq ha hs, hP1]; norm_num
  have hl2 : lamd P 2 = 41 := by rw [show 2 = 0 + 2 from rfl, lamd_eq ha hs, hP1]; norm_num
  have ht3 : taud P 3 = 673 := by rw [show 3 = 1 + 2 from rfl, taud_eq ha hs, hP2]; norm_num
  have hg1 : gamd P 1 = 8 := by unfold gamd; rw [Wd_eq ha hs, ht1]; norm_num
  have hg2 : gamd P 2 = 40 := by unfold gamd; rw [Wd_eq ha hs, ht2]; norm_num
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rcases k with _ | _ | _ | k
  · have hn : n0max P 1 = 9 := by unfold n0max; rw [ite_eq_left le_rfl, ha]
    have hd : Dmax P 1 = 12 := by unfold Dmax; rw [ite_eq_left le_rfl, hP1]
    rw [hn, hd]; norm_num
  · have hn : n0max P 2 = 18 := by unfold n0max; rw [ite_eq_right (by omega), ht2,
    show 2 - 1 = 1 from rfl, hl1]
    have hd : Dmax P 2 = 39 := by
      unfold Dmax; rw [ite_eq_right (by omega), hn, hP2, show 2 - 1 = 1 from rfl, hg1]
    rw [show 0 + 1 + 1 = 2 from rfl, hn, hd]; norm_num
  · have hn : n0max P 3 = 25 := by unfold n0max; rw [ite_eq_right (by omega), ht3,
    show 3 - 1 = 2 from rfl, hl2]
    have hd : Dmax P 3 = 57 := by
      unfold Dmax; rw [ite_eq_right (by omega), hn, hP3, show 3 - 1 = 2 from rfl, hg2]
    rw [show 0 + 1 + 1 + 1 = 3 from rfl, hn, hd]; norm_num
  · rw [show k + 1 + 1 + 1 + 1 = k + 4 from rfl]
    have hn := n0max_le ha hs k
    have hd := Dmax_le ha hs k
    omega

/-- **The top structure's parameter conditions** for `a = 8`, `s = 11`, `β = 64`. -/
theorem topParams_8 (hb : P.beta = 64) : TopParams P :=
  ⟨s3_8 ha hs, lamK_8 ha hs, room_8 ha hs hb, piW_8 ha hs, gam1_8 ha hs, tab_8 ha hs⟩

end

end OrderMaintenance.Proof.Top

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Probability.Exponents
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Lattice

/-!
# The cell chain of the probability criterion

Pure real-analysis core of Theorem 3.1 of the manuscript: a two-setting, two-outcome box
whose cells obey the forward and reverse power bounds, and whose correlators are `q`-close
to the product correlators with `q` below the cut, satisfies the CHSH bound.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Correlator of a two-setting, two-outcome box. -/
def boxCorr (p : Bool → Bool → Bool → Bool → ℝ) (i j : Bool) : ℝ :=
  p i j true true + p i j false false - p i j true false - p i j false true

/-- A power bound `x ^ r ≤ K * m ^ (r - 1)` with `x > 0` forces `m > 0`. -/
private lemma pos_of_bound {x m K r : ℝ} (hr : 1 < r) (hx : 0 < x) (hm : 0 ≤ m)
    (h : x ^ r ≤ K * m ^ (r - 1)) : 0 < m := by
  rcases hm.eq_or_lt with h0 | h0
  · exfalso
    subst h0
    rw [Real.zero_rpow (sub_pos.mpr hr).ne', mul_zero] at h
    exact absurd h (not_le.mpr (Real.rpow_pos_of_pos hx r))
  · exact h0

/-- Logarithmic form of a power bound. -/
private lemma log_bound {x m K r : ℝ} (hr : 1 < r) (hx : 0 < x) (hm : 0 < m) (hK : 0 < K)
    (h : x ^ r ≤ K * m ^ (r - 1)) :
    Real.log x ≤ (1 / r) * Real.log K + (1 - 1 / r) * Real.log m := by
  have hr0 : (0 : ℝ) < r := by linarith
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hx r) h
  rw [Real.log_rpow hx, Real.log_mul hK.ne' (Real.rpow_pos_of_pos hm _).ne',
    Real.log_rpow hm] at h1
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / r := ⟨_, rfl⟩
  rw [← ht]
  have htr : t * r = 1 := by rw [ht]; exact one_div_mul_cancel hr0.ne'
  have ht0 : 0 ≤ t := by rw [ht]; exact (one_div_pos.mpr hr0).le
  have h2 := mul_le_mul_of_nonneg_left h1 ht0
  have hX : t * r * Real.log x = Real.log x := by rw [htr, one_mul]
  have hM : t * r * Real.log m = Real.log m := by rw [htr, one_mul]
  nlinarith [h2, hX, hM]

/-- The scalar chain in logarithmic variables. -/
private lemma chain_core {t s W EA EB XA XB L10 L01 L00 LKp LKm L2 : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hs1 : s < 1)
    (h1 : W ≤ t * LKp + (1 - t) * (EA + EB))
    (h2 : L10 ≤ t * LKp + (1 - t) * (EA + XB))
    (h3 : L01 ≤ t * LKp + (1 - t) * (XA + EB))
    (h4 : XA + XB ≤ s * LKm + (1 - s) * L00)
    (h10 : EA - L2 ≤ L10) (h01 : EB - L2 ≤ L01) (h00 : L00 < W) :
    0 < ((1 - s) * (1 - t) ^ 2 - t) * W + (2 - t) * t * LKp + s * (1 - t) ^ 2 * LKm
        + 2 * (1 - t) * L2 := by
  have hb : 0 < 1 - t := sub_pos.mpr ht1
  have ha : 0 < 1 - s := sub_pos.mpr hs1
  have hsum : 0 ≤ 2 * t * LKp + (1 - t) * (EA + EB) + (1 - t) * (XA + XB)
      - (EA + EB - 2 * L2) := by linarith
  have p1 := mul_nonneg ht0.le (sub_nonneg.mpr h1)
  have p2 := mul_nonneg hb.le hsum
  have p3 := mul_nonneg (sq_nonneg (1 - t)) (sub_nonneg.mpr h4)
  have p4 := mul_pos (mul_pos ha (pow_pos hb 2)) (sub_pos.mpr h00)
  nlinarith [p1, p2, p3, p4]

private lemma expEta_mul {rp rm : ℝ} (ha : expA rm ≠ 0) (hb : expB rp ≠ 0) :
    expEta rp rm * (expA rm * expB rp ^ 2) = expA rm * expB rp ^ 2 - (1 - expB rp) := by
  unfold expEta
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (mul_ne_zero ha (pow_ne_zero 2 hb))]

private lemma nuPlus_mul {rp rm : ℝ} (ha : expA rm ≠ 0) (hb : expB rp ≠ 0) :
    nuPlus rp rm * (expA rm * expB rp ^ 2) = (1 + expB rp) * (1 / rp) := by
  unfold nuPlus
  have hD : expA rm * expB rp ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hb)
  rw [show expA rm * rp * expB rp ^ 2 = rp * (expA rm * expB rp ^ 2) by ring,
    div_mul_eq_div_div, div_mul_cancel₀ _ hD, mul_one_div]

private lemma nuMinus_mul {rp rm : ℝ} (ha : expA rm ≠ 0) :
    nuMinus rm * (expA rm * expB rp ^ 2) = (1 - expA rm) * expB rp ^ 2 := by
  unfold nuMinus
  rw [← mul_assoc, div_mul_cancel₀ _ ha]

private lemma cut_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    2 / (a * b) * (a * b ^ 2) = 2 * b := by
  rw [show a * b ^ 2 = a * b * b by ring, ← mul_assoc, div_mul_cancel₀ _ (mul_ne_zero ha hb)]

/-- The final linear-arithmetic contradiction between the chain and the cut. -/
private lemma final_arith {η νp νm c a b tp tm W Q LKp LKm L2 : ℝ}
    (hb : b = 1 - tp) (ha : a = 1 - tm) (ha0 : 0 < a) (hb0 : 0 < b)
    (h1 : η * (a * b ^ 2) = a * b ^ 2 - (1 - b))
    (h2 : νp * (a * b ^ 2) = (1 + b) * tp)
    (h3 : νm * (a * b ^ 2) = (1 - a) * b ^ 2)
    (h4 : c * (a * b ^ 2) = 2 * b)
    (hη : 0 < η) (hWQ : W < Q)
    (hC : η * Q + νp * LKp + νm * LKm ≤ -c * L2)
    (hP : 0 < ((1 - tm) * (1 - tp) ^ 2 - tp) * W + (2 - tp) * tp * LKp
        + tm * (1 - tp) ^ 2 * LKm + 2 * (1 - tp) * L2) : False := by
  have hD : 0 < a * b ^ 2 := mul_pos ha0 (pow_pos hb0 2)
  have e1 := mul_nonneg (sub_nonneg.mpr hC) hD.le
  have e2 := mul_pos (mul_pos hη hD) (sub_pos.mpr hWQ)
  have g1 : η * (a * b ^ 2) * W = (a * b ^ 2 - (1 - b)) * W := by rw [h1]
  have g2 : νp * (a * b ^ 2) * LKp = (1 + b) * tp * LKp := by rw [h2]
  have g3 : νm * (a * b ^ 2) * LKm = (1 - a) * b ^ 2 * LKm := by rw [h3]
  have g4 : c * (a * b ^ 2) * L2 = 2 * b * L2 := by rw [h4]
  subst hb ha
  nlinarith [e1, e2, g1, g2, g3, g4, hP]

/-- The scalar chain: a least winning cell below `q` contradicts the cut. -/
private lemma chain_false {rp rm Kp Km q : ℝ} (hrp : 1 < rp) (hrm : 1 < rm)
    (hη : 0 < expEta rp rm) (hKp : 0 < Kp) (hKm : 0 < Km)
    (hcut : q ^ expEta rp rm * Kp ^ nuPlus rp rm * Km ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp))))
    {w w10 w01 w00 eA eB xA xB : ℝ}
    (hup : w ^ rp ≤ Kp * (eA * eB) ^ (rp - 1))
    (hup10 : w10 ^ rp ≤ Kp * (eA * xB) ^ (rp - 1))
    (hup01 : w01 ^ rp ≤ Kp * (xA * eB) ^ (rp - 1))
    (hlow : (xA * xB) ^ rm ≤ Km * w00 ^ (rm - 1))
    (hxA : 0 ≤ xA) (hxB : 0 ≤ xB) (hw00 : 0 ≤ w00)
    (hA10 : 0 ≤ eA - w10) (hB01 : 0 ≤ eB - w01) (hw10 : w ≤ w10) (hw01 : w ≤ w01)
    (hlin : (eA - w10) + (eB - w01) + w00 < w)
    (hwq : w < q) : False := by
  have hw : 0 < w := by linarith
  have hw10p : 0 < w10 := by linarith
  have hw01p : 0 < w01 := by linarith
  have heA : 0 < eA := by linarith
  have heB : 0 < eB := by linarith
  have hq : 0 < q := by linarith
  have hrp0 : 0 < rp := by linarith
  have hrm0 : 0 < rm := by linarith
  have hxBp : 0 < xB := by
    have hm := pos_of_bound hrp hw10p (mul_nonneg heA.le hxB) hup10
    by_contra hcon
    have h0 : xB = 0 := le_antisymm (not_lt.mp hcon) hxB
    rw [h0, mul_zero] at hm
    exact lt_irrefl _ hm
  have hxAp : 0 < xA := by
    have hm := pos_of_bound hrp hw01p (mul_nonneg hxA heB.le) hup01
    by_contra hcon
    have h0 : xA = 0 := le_antisymm (not_lt.mp hcon) hxA
    rw [h0, zero_mul] at hm
    exact lt_irrefl _ hm
  have hw00p : 0 < w00 := pos_of_bound hrm (mul_pos hxAp hxBp) hw00 hlow
  have l1 := log_bound hrp hw (mul_pos heA heB) hKp hup
  have l2 := log_bound hrp hw10p (mul_pos heA hxBp) hKp hup10
  have l3 := log_bound hrp hw01p (mul_pos hxAp heB) hKp hup01
  have l4 := log_bound hrm (mul_pos hxAp hxBp) hw00p hKm hlow
  rw [Real.log_mul heA.ne' heB.ne'] at l1
  rw [Real.log_mul heA.ne' hxBp.ne'] at l2
  rw [Real.log_mul hxAp.ne' heB.ne'] at l3
  rw [Real.log_mul hxAp.ne' hxBp.ne'] at l4
  have h10 : Real.log eA - Real.log 2 ≤ Real.log w10 := by
    have hle : eA / 2 ≤ w10 := by linarith
    have h := Real.log_le_log (half_pos heA) hle
    rwa [Real.log_div heA.ne' (two_ne_zero)] at h
  have h01 : Real.log eB - Real.log 2 ≤ Real.log w01 := by
    have hle : eB / 2 ≤ w01 := by linarith
    have h := Real.log_le_log (half_pos heB) hle
    rwa [Real.log_div heB.ne' (two_ne_zero)] at h
  have h00 : Real.log w00 < Real.log w := Real.log_lt_log hw00p (by linarith)
  have hWQ : Real.log w < Real.log q := Real.log_lt_log hw hwq
  have ht0 : (0 : ℝ) < 1 / rp := one_div_pos.mpr hrp0
  have ht1 : 1 / rp < 1 := by rw [div_lt_one hrp0]; exact hrp
  have hs1 : 1 / rm < 1 := by rw [div_lt_one hrm0]; exact hrm
  have core := chain_core ht0 ht1 hs1 l1 l2 l3 l4 h10 h01 h00
  have ha0 : 0 < expA rm := show (0 : ℝ) < 1 - 1 / rm from sub_pos.mpr hs1
  have hb0 : 0 < expB rp := show (0 : ℝ) < 1 - 1 / rp from sub_pos.mpr ht1
  have hpos1 : 0 < q ^ expEta rp rm := Real.rpow_pos_of_pos hq _
  have hpos2 : 0 < Kp ^ nuPlus rp rm := Real.rpow_pos_of_pos hKp _
  have hpos3 : 0 < Km ^ nuMinus rm := Real.rpow_pos_of_pos hKm _
  have hC := Real.log_le_log (mul_pos (mul_pos hpos1 hpos2) hpos3) hcut
  rw [Real.log_mul (mul_pos hpos1 hpos2).ne' hpos3.ne', Real.log_mul hpos1.ne' hpos2.ne',
    Real.log_rpow hq, Real.log_rpow hKp, Real.log_rpow hKm,
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hC
  exact final_arith (a := expA rm) (b := expB rp) (tp := 1 / rp) (tm := 1 / rm) rfl rfl ha0 hb0
    (expEta_mul ha0.ne' hb0.ne') (nuPlus_mul ha0.ne' hb0.ne')
    (nuMinus_mul ha0.ne') (cut_mul ha0.ne' hb0.ne') hη hWQ hC core

/-- The product CHSH expression is bounded by the larger Bob correlator bound. -/
private lemma chsh_prod_bound {m0 m1 n0 n1 N : ℝ}
    (hm0l : -1 ≤ m0) (hm0u : m0 ≤ 1) (hm1l : -1 ≤ m1) (hm1u : m1 ≤ 1)
    (hn0l : -N ≤ n0) (hn0u : n0 ≤ N) (hn1l : -N ≤ n1) (hn1u : n1 ≤ N) :
    m0 * (n0 + n1) + m1 * (n0 - n1) ≤ 2 * N := by
  have a0 : 0 ≤ 1 - m0 := by linarith
  have b0 : 0 ≤ m0 + 1 := by linarith
  have a1 : 0 ≤ 1 - m1 := by linarith
  have b1 : 0 ≤ m1 + 1 := by linarith
  rcases le_total 0 (n0 + n1) with h1 | h1 <;> rcases le_total 0 (n0 - n1) with h2 | h2
  · nlinarith [mul_nonneg a0 h1, mul_nonneg a1 h2]
  · nlinarith [mul_nonneg a0 h1, mul_nonneg b1 (neg_nonneg.mpr h2)]
  · nlinarith [mul_nonneg b0 (neg_nonneg.mpr h1), mul_nonneg a1 h2]
  · nlinarith [mul_nonneg b0 (neg_nonneg.mpr h1), mul_nonneg b1 (neg_nonneg.mpr h2)]

/-- Bob's outcome in the winning cell with settings `i j` and Alice outcome `α`. -/
private def winOut : Bool → Bool → Bool → Bool
  | true, true, α => !α
  | _, _, α => α

private lemma exists_min_bool3 (g : Bool → Bool → Bool → ℝ) :
    ∃ i j α, ∀ i' j' α', g i j α ≤ g i' j' α' := by
  obtain ⟨x, -, hx⟩ := Finset.exists_min_image (Finset.univ : Finset (Bool × Bool × Bool))
    (fun x => g x.1 x.2.1 x.2.2) Finset.univ_nonempty
  exact ⟨x.1, x.2.1, x.2.2, fun i' j' α' => hx (i', j', α') (Finset.mem_univ _)⟩

/-- A CHSH value `q`-close to a product value whose Bob correlators are bounded by `1 - 2 q`
is at most one. -/
private lemma chsh_close_le_one {c00 c01 c10 c11 m0 m1 n0 n1 q : ℝ}
    (hm0l : -1 ≤ m0) (hm0u : m0 ≤ 1) (hm1l : -1 ≤ m1) (hm1u : m1 ≤ 1)
    (hn0l : -(1 - 2 * q) ≤ n0) (hn0u : n0 ≤ 1 - 2 * q)
    (hn1l : -(1 - 2 * q) ≤ n1) (hn1u : n1 ≤ 1 - 2 * q)
    (h00 : |c00 - m0 * n0| ≤ q) (h01 : |c01 - m0 * n1| ≤ q)
    (h10 : |c10 - m1 * n0| ≤ q) (h11 : |c11 - m1 * n1| ≤ q) :
    (1 / 2 : ℝ) * (c00 + c01 + c10 - c11) ≤ 1 := by
  have hprod : m0 * n0 + m0 * n1 + m1 * n0 - m1 * n1 ≤ 2 * (1 - 2 * q) :=
    calc m0 * n0 + m0 * n1 + m1 * n0 - m1 * n1
        = m0 * (n0 + n1) + m1 * (n0 - n1) := by ring
      _ ≤ 2 * (1 - 2 * q) := chsh_prod_bound hm0l hm0u hm1l hm1u hn0l hn0u hn1l hn1u
  have e00 := (abs_le.mp h00).2
  have e01 := (abs_le.mp h01).2
  have e10 := (abs_le.mp h10).2
  have e11 := (abs_le.mp h11).1
  linarith

theorem chsh_box_le_one
    {rp rm Kp Km q : ℝ} (hrp : 1 < rp) (hrm : 1 < rm)
    (hη : 0 < expEta rp rm) (hKp : 0 < Kp) (hKm : 0 < Km)
    (p : Bool → Bool → Bool → Bool → ℝ) (pA pB : Bool → Bool → ℝ)
    (hp : ∀ i j α β, 0 ≤ p i j α β)
    (hA : ∀ i j α, p i j α true + p i j α false = pA i α)
    (hB : ∀ i j β, p i j true β + p i j false β = pB j β)
    (hnorm : ∀ i, pA i true + pA i false = 1)
    (hup : ∀ i j α β, p i j α β ^ rp ≤ Kp * (pA i α * pB j β) ^ (rp - 1))
    (hlow : ∀ i j α β, (pA i α * pB j β) ^ rm ≤ Km * p i j α β ^ (rm - 1))
    (hcl : ∀ i j, |boxCorr p i j - (pA i true - pA i false) * (pB j true - pB j false)| ≤ q)
    (hcut : q ^ expEta rp rm * Kp ^ nuPlus rp rm * Km ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp)))) :
    (1 / 2 : ℝ) * (boxCorr p false false + boxCorr p false true + boxCorr p true false
        - boxCorr p true true) ≤ 1 := by
  by_contra hS
  have hS2 := not_le.mp hS
  simp only [boxCorr] at hS2
  have hcellA : ∀ i j α β, p i j α β ≤ pA i α := fun i j α β => by
    cases β <;> linarith [hA i j α, hp i j α true, hp i j α false]
  have hcellB : ∀ i j α β, p i j α β ≤ pB j β := fun i j α β => by
    cases α <;> linarith [hB i j β, hp i j true β, hp i j false β]
  have hpA : ∀ i α, 0 ≤ pA i α := fun i α =>
    le_trans (hp i false α true) (hcellA i false α true)
  have hpB : ∀ j β, 0 ≤ pB j β := fun j β =>
    le_trans (hp false j true β) (hcellB false j true β)
  have hBs : ∀ j, pB j true + pB j false = 1 := fun j => by
    linarith [hB false j true, hB false j false, hA false j true, hA false j false, hnorm false]
  obtain ⟨i, j, α, hmin0⟩ := exists_min_bool3 (fun i j α => p i j α (winOut i j α))
  have hmin : ∀ i' j' α', p i j α (winOut i j α) ≤ p i' j' α' (winOut i' j' α') := hmin0
  clear hmin0
  have hwq : p i j α (winOut i j α) < q := by
    by_contra hge
    have hge' := not_lt.mp hge
    have c1 : q ≤ p false false false false := le_trans hge' (hmin false false false)
    have c2 : q ≤ p false false true true := le_trans hge' (hmin false false true)
    have c3 : q ≤ p false true false false := le_trans hge' (hmin false true false)
    have c4 : q ≤ p false true true true := le_trans hge' (hmin false true true)
    have q1 : q ≤ pB false false := le_trans c1 (hcellB false false false false)
    have q2 : q ≤ pB false true := le_trans c2 (hcellB false false true true)
    have q3 : q ≤ pB true false := le_trans c3 (hcellB false true false false)
    have q4 : q ≤ pB true true := le_trans c4 (hcellB false true true true)
    have s0 := hBs false
    have s1 := hBs true
    have nf := hnorm false
    have nt := hnorm true
    have u1 := hpA false true
    have u2 := hpA false false
    have u3 := hpA true true
    have u4 := hpA true false
    exact hS (chsh_close_le_one (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (hcl false false) (hcl false true) (hcl true false) (hcl true true))
  have a1 := hA false false false
  have a2 := hA false false true
  have a3 := hA false true false
  have a4 := hA false true true
  have a5 := hA true false false
  have a6 := hA true false true
  have a7 := hA true true false
  have a8 := hA true true true
  have b1 := hB false false false
  have b2 := hB false false true
  have b3 := hB false true false
  have b4 := hB false true true
  have b5 := hB true false false
  have b6 := hB true false true
  have b7 := hB true true false
  have b8 := hB true true true
  have nf := hnorm false
  have nt := hnorm true
  cases i <;> cases j <;> cases α
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup false false false false) (hup false true false false) (hup true false false false)
      (hlow true true false false)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin false true false) (hmin true false false) (by linarith) hwq
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup false false true true) (hup false true true true) (hup true false true true)
      (hlow true true true true)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin false true true) (hmin true false true) (by linarith) hwq
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup false true false false) (hup false false false false) (hup true true true false)
      (hlow true false true false)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin false false false) (hmin true true true) (by linarith) hwq
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup false true true true) (hup false false true true) (hup true true false true)
      (hlow true false false true)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin false false true) (hmin true true false) (by linarith) hwq
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup true false false false) (hup true true false true) (hup false false false false)
      (hlow false true false true)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin true true false) (hmin false false false) (by linarith) hwq
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup true false true true) (hup true true true false) (hup false false true true)
      (hlow false true true false)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin true true true) (hmin false false true) (by linarith) hwq
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup true true false true) (hup true false false false) (hup false true true true)
      (hlow false false true false)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin true false false) (hmin false true true) (by linarith) hwq
  · exact chain_false hrp hrm hη hKp hKm hcut
      (hup true true true false) (hup true false true true) (hup false true false false)
      (hlow false false false true)
      (hpA _ _) (hpB _ _) (hp _ _ _ _) (sub_nonneg.mpr (hcellA _ _ _ _))
      (sub_nonneg.mpr (hcellB _ _ _ _))
      (hmin true false true) (hmin false true false) (by linarith) hwq

end VacuumBellSeparation

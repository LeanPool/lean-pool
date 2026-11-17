/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 9, part (c): the arithmetic

With `C₃ = C(k-3, d-3)`, `C₂ = C(k-2, d-2)`, `C₁ = C(k-1, d-1)`, `C₀ = C(k, d)`, the hypothesis (6)
`2y + x ≤ (d-4)/(d-3) · min(2 C₃, C₀) - 2` and the bounds from Lemma 8 on the 1-piles
(`k G₁ ≤ d x + k - 1`, `(k-1) G₂ ≤ (d-1) G₁ + k - 2`, `(k-2) G₃ ≤ (d-2) G₂ + k - 3`) give the room
required by Lemma 7 at each stage (`roomA`, `roomB`, `roomC`; the paper's (11)–(13)). Two cases
in each: the factor `C_i / C₀` is at most `1/2`, or it is larger.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L9

section
variable {K D C3 C2 C1 C0 x y G1 G2 G3 : ℚ}

theorem chain1 (_ : 0 < K) (hG1 : K * G1 ≤ D * x + K - 1) : K * G1 ≤ D * x + K := by linarith

theorem chain2 (hD : 1 ≤ D) (hDK : D ≤ K) (_ : 0 ≤ x) (hK : 2 ≤ K)
    (hG1 : K * G1 ≤ D * x + K - 1) (hG2 : (K - 1) * G2 ≤ (D - 1) * G1 + K - 2) :
    K * (K - 1) * G2 ≤ D * (D - 1) * x + 2 * (K * (K - 1)) := by
  have h1 : K * ((K - 1) * G2) ≤ K * ((D - 1) * G1 + K - 2) :=
    mul_le_mul_of_nonneg_left hG2 (by linarith)
  have h2 : (D - 1) * (K * G1) ≤ (D - 1) * (D * x + K - 1) :=
    mul_le_mul_of_nonneg_left hG1 (by linarith)
  nlinarith

theorem chain3 (hD : 2 ≤ D) (hDK : D ≤ K) (_ : 0 ≤ x) (hK : 3 ≤ K)
    (hG2' : K * (K - 1) * G2 ≤ D * (D - 1) * x + 2 * (K * (K - 1)))
    (hG3 : (K - 2) * G3 ≤ (D - 2) * G2 + K - 3) :
    K * (K - 1) * (K - 2) * G3 ≤ D * (D - 1) * (D - 2) * x + 3 * (K * (K - 1) * (K - 2)) := by
  have h1 : (K * (K - 1)) * ((K - 2) * G3) ≤ (K * (K - 1)) * ((D - 2) * G2 + K - 3) :=
    mul_le_mul_of_nonneg_left hG3 (by nlinarith)
  have h2 : (D - 2) * (K * (K - 1) * G2) ≤ (D - 2) * (D * (D - 1) * x + 2 * (K * (K - 1))) :=
    mul_le_mul_of_nonneg_left hG2' (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hDK (show 0 ≤ K * (K - 1) by nlinarith)]

/-- **Room at the third stage** (13). -/
theorem roomC (hD : 5 ≤ D) (hDK : D + 2 ≤ K) (_ : 0 ≤ C3) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (e0 : D * (D - 1) * (D - 2) * C0 = K * (K - 1) * (K - 2) * C3)
    (hnA : 2 * y + x ≤ (D - 4) / (D - 3) * (2 * C3) - 2)
    (hnB : 2 * y + x ≤ (D - 4) / (D - 3) * C0 - 2)
    (hG3 : K * (K - 1) * (K - 2) * G3 ≤ D * (D - 1) * (D - 2) * x + 3 * (K * (K - 1) * (K - 2))) :
    G3 + y ≤ (D - 4) / (D - 3) * C3 + 2 := by
  set P := K * (K - 1) * (K - 2) with hP
  set Q := D * (D - 1) * (D - 2) with hQ
  set r := (D - 4) / (D - 3) with hr
  have hP0 : 0 < P := by rw [hP]; apply mul_pos (mul_pos _ _) _ <;> linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
  have hr0 : 0 ≤ r := by rw [hr]; apply div_nonneg <;> linarith
  suffices h : P * (G3 + y) ≤ P * (r * C3 + 2) from le_of_mul_le_mul_left h hP0
  by_cases hc : 2 * Q ≤ P
  · nlinarith [mul_nonneg (sub_nonneg.2 hc) hx, mul_le_mul_of_nonneg_left hnA hP0.le]
  · push Not at hc
    have h1 : Q * (2 * y + x) ≤ Q * (r * C0 - 2) := mul_le_mul_of_nonneg_left hnB hQ0
    have h2 : r * (Q * C0) = r * (P * C3) := by rw [e0]
    nlinarith [mul_nonneg (sub_nonneg.2 hc.le) hy]

/-- **Room at the second stage** (12). -/
theorem roomB (hD : 5 ≤ D) (hDK : D + 2 ≤ K) (hC3 : 0 ≤ C3) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (e2 : (D - 2) * C2 = (K - 2) * C3) (e0 : D * (D - 1) * C0 = K * (K - 1) * C2)
    (hnA : 2 * y + x ≤ (D - 4) / (D - 3) * (2 * C3) - 2)
    (hnB : 2 * y + x ≤ (D - 4) / (D - 3) * C0 - 2)
    (hG2 : K * (K - 1) * G2 ≤ D * (D - 1) * x + 2 * (K * (K - 1))) :
    G2 + y ≤ (D - 3) / (D - 2) * C2 + 2 := by
  set P := K * (K - 1) with hP
  set Q := D * (D - 1) with hQ
  have hP0 : 0 < P := by rw [hP]; apply mul_pos <;> linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; apply mul_nonneg <;> linarith
  have hr : (D - 4) / (D - 3) ≤ (D - 3) / (D - 2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hr0 : 0 ≤ (D - 4) / (D - 3) := by apply div_nonneg <;> linarith
  have hC23 : C3 ≤ C2 := by
    by_contra h; push Not at h
    have : (D - 2) * C2 < (K - 2) * C3 := by nlinarith
    linarith
  have hC2 : 0 ≤ C2 := le_trans hC3 hC23
  have hk : (D - 4) / (D - 3) * C3 ≤ (D - 3) / (D - 2) * C2 :=
    mul_le_mul hr hC23 hC3 (le_trans hr0 hr)
  suffices h : P * (G2 + y) ≤ P * ((D - 3) / (D - 2) * C2 + 2) from le_of_mul_le_mul_left h hP0
  by_cases hc : 2 * Q ≤ P
  · nlinarith [mul_nonneg (sub_nonneg.2 hc) hx, mul_le_mul_of_nonneg_left hnA hP0.le,
      mul_le_mul_of_nonneg_left hk hP0.le]
  · push Not at hc
    have h1 : Q * (2 * y + x) ≤ Q * ((D - 4) / (D - 3) * C0 - 2) :=
      mul_le_mul_of_nonneg_left hnB hQ0
    have h2 : (D - 4) / (D - 3) * (Q * C0) = (D - 4) / (D - 3) * (P * C2) := by rw [e0]
    have h3 : (D - 4) / (D - 3) * (P * C2) ≤ (D - 3) / (D - 2) * (P * C2) :=
      mul_le_mul_of_nonneg_right hr (mul_nonneg hP0.le hC2)
    nlinarith [mul_nonneg (sub_nonneg.2 hc.le) hy]

/-- **Room at the first stage** (11). -/
theorem roomA (hD : 5 ≤ D) (hDK : D + 2 ≤ K) (hC3 : 0 ≤ C3) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (e2 : (D - 2) * C2 = (K - 2) * C3) (e1 : (D - 1) * C1 = (K - 1) * C2) (e0 : D * C0 = K * C1)
    (hnA : 2 * y + x ≤ (D - 4) / (D - 3) * (2 * C3) - 2)
    (hnB : 2 * y + x ≤ (D - 4) / (D - 3) * C0 - 2)
    (hG1 : K * G1 ≤ D * x + K) :
    G1 + y ≤ (D - 2) / (D - 1) * C1 + 2 := by
  have hK0 : 0 < K := by linarith
  have hr : (D - 4) / (D - 3) ≤ (D - 2) / (D - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hr0 : 0 ≤ (D - 4) / (D - 3) := by apply div_nonneg <;> linarith
  have hC23 : C3 ≤ C2 := by
    by_contra h; push Not at h
    have : (D - 2) * C2 < (K - 2) * C3 := by nlinarith
    linarith
  have hC2 : 0 ≤ C2 := le_trans hC3 hC23
  have hC12 : C2 ≤ C1 := by
    by_contra h; push Not at h
    have : (D - 1) * C1 < (K - 1) * C2 := by nlinarith
    linarith
  have hC1 : 0 ≤ C1 := le_trans hC2 hC12
  have hk : (D - 4) / (D - 3) * C3 ≤ (D - 2) / (D - 1) * C1 :=
    mul_le_mul hr (le_trans hC23 hC12) hC3 (le_trans hr0 hr)
  suffices h : K * (G1 + y) ≤ K * ((D - 2) / (D - 1) * C1 + 2) from le_of_mul_le_mul_left h hK0
  by_cases hc : 2 * D ≤ K
  · nlinarith [mul_nonneg (sub_nonneg.2 hc) hx, mul_le_mul_of_nonneg_left hnA hK0.le,
      mul_le_mul_of_nonneg_left hk hK0.le]
  · push Not at hc
    have h1 : D * (2 * y + x) ≤ D * ((D - 4) / (D - 3) * C0 - 2) :=
      mul_le_mul_of_nonneg_left hnB (by linarith)
    have h2 : (D - 4) / (D - 3) * (D * C0) = (D - 4) / (D - 3) * (K * C1) := by rw [e0]
    have h3 : (D - 4) / (D - 3) * (K * C1) ≤ (D - 2) / (D - 1) * (K * C1) :=
      mul_le_mul_of_nonneg_right hr (mul_nonneg hK0.le hC1)
    nlinarith [mul_nonneg (sub_nonneg.2 hc.le) hy]

end

/-- The binomial identities. -/
theorem choose_rel {k d : ℕ} (hd : 3 ≤ d) (hdk : d ≤ k) :
    ((d : ℚ) - 2) * ((k - 2).choose (d - 2) : ℕ) = ((k : ℚ) - 2) * ((k - 3).choose (d - 3) : ℕ) ∧
    ((d : ℚ) - 1) * ((k - 1).choose (d - 1) : ℕ) = ((k : ℚ) - 1) * ((k - 2).choose (d - 2) : ℕ) ∧
    (d : ℚ) * (k.choose d : ℕ) = (k : ℚ) * ((k - 1).choose (d - 1) : ℕ) := by
  have e3 := Nat.add_one_mul_choose_eq (k - 3) (d - 3)
  have e2 := Nat.add_one_mul_choose_eq (k - 2) (d - 2)
  have e1 := Nat.add_one_mul_choose_eq (k - 1) (d - 1)
  rw [show k - 3 + 1 = k - 2 by omega, show d - 3 + 1 = d - 2 by omega] at e3
  rw [show k - 2 + 1 = k - 1 by omega, show d - 2 + 1 = d - 1 by omega] at e2
  rw [show k - 1 + 1 = k by omega, show d - 1 + 1 = d by omega] at e1
  have c3 : ((k - 2 : ℕ) : ℚ) = (k : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have c2 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have d2 : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have d1 : ((d - 1 : ℕ) : ℚ) = (d : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun n : ℕ => (n : ℚ)) e3
    push_cast at this
    rw [c3, d2] at this; linarith
  · have := congrArg (fun n : ℕ => (n : ℚ)) e2
    push_cast at this
    rw [c2, d1] at this; linarith
  · have := congrArg (fun n : ℕ => (n : ℚ)) e1
    push_cast at this
    linarith

end Bkls.L9

end LeanPool.BalancedEdgeColourings

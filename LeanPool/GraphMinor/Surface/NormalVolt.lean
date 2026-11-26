/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.NormalWord
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Sums along the normal word

Give each label a value `V`. Reading the word `ew a b c`, add the value of a letter, or subtract it
for an inverse
letter. `Sm V j` is the sum of the first `j` letters. Handles add nothing, a cross-cap adds twice
its value, and a hole
adds the value of its free side (`Sm_total`).
-/

@[expose] public section

namespace GraphMinor.Surface

variable {A : Type} [AddCommGroup A] {a b c : ℕ}

/-- The corner where the side `p` starts, read along its label. -/
def st (a b c p : ℕ) : ℕ := if sgn a b c p then p else p + 1

/-- The corner where the side `p` ends, read along its label. -/
def en (a b c p : ℕ) : ℕ := if sgn a b c p then p + 1 else p

/-- The signed value of the side `j`. -/
def lv (a b c : ℕ) (V : ℕ → A) (j : ℕ) : A := if sgn a b c j then V (lab a b c j) else - V
  (lab a b c j)

/-- The sum of the first `j` sides. -/
def Sm (a b c : ℕ) (V : ℕ → A) (j : ℕ) : A := ∑ i ∈ Finset.range j, lv a b c V i

theorem Sm_succ (V : ℕ → A) (j : ℕ) : Sm a b c V (j + 1) = Sm a b c V j + lv a b c V j :=
  Finset.sum_range_succ _ _

theorem Sm_en (V : ℕ → A) (j : ℕ) : Sm a b c V (en a b c j) = Sm a b c V (st a b c j) + V
  (lab a b c j) := by
  unfold en st
  by_cases h : sgn a b c j
  · rw [ite_eq_left h, ite_eq_left h, Sm_succ, lv, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, Sm_succ, lv, ite_eq_right h]
    abel

theorem lab_h {i δ : ℕ} (hi : i < a) (hδ : δ < 4) : lab a b c (4 * i + δ) = 2 * i + δ % 2 := by
  unfold lab
  rw [ite_eq_left (by omega)]
  omega

theorem sgn_h {i δ : ℕ} (hi : i < a) (hδ : δ < 4) : sgn a b c (4 * i + δ) = decide (δ < 2) := by
  unfold sgn
  rw [ite_eq_left (by omega)]
  congr 1
  apply propext
  omega

theorem lab_c {i δ : ℕ} (hi : i < b) (hδ : δ < 2) : lab a b c (4 * a + 2 * i + δ) = 2 * a + i := by
  unfold lab
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  omega

theorem sgn_c {i δ : ℕ} (hi : i < b) (hδ : δ < 2) : sgn a b c (4 * a + 2 * i + δ) = true := by
  unfold sgn
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

theorem lab_t {i δ : ℕ} (hi : i < c) (hδ : δ < 3) :
    lab a b c (4 * a + 2 * b + 3 * i + δ) = 2 * a + b + 2 * i + δ % 2 := by
  unfold lab
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  omega

theorem sgn_t {i δ : ℕ} (hi : i < c) (hδ : δ < 3) : sgn a b c (4 * a + 2 * b + 3 * i + δ) = decide
  (δ < 2) := by
  unfold sgn
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  congr 1
  apply propext
  omega

theorem lab_l {δ : ℕ} : lab a b c (4 * a + 2 * b + 3 * c + δ) = 2 * a + b + 2 * c := by
  unfold lab
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem sgn_l {δ : ℕ} : sgn a b c (4 * a + 2 * b + 3 * c + δ) = decide (δ = 0) := by
  unfold sgn
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  congr 1
  apply propext
  omega

theorem lv_h (V : ℕ → A) {i δ : ℕ} (hi : i < a) (hδ : δ < 4) : lv a b c V (4 * i + δ) =
    if δ < 2 then V (2 * i + δ % 2) else - V (2 * i + δ % 2) := by
  simp only [lv, lab_h hi hδ, sgn_h hi hδ, decide_eq_true_eq]

theorem lv_c (V : ℕ → A) {i δ : ℕ} (hi : i < b) (hδ : δ < 2) : lv a b c V (4 * a + 2 * i + δ) = V
  (2 * a + i) := by
  simp only [lv, lab_c hi hδ, sgn_c hi hδ, ite_true]

theorem lv_t (V : ℕ → A) {i δ : ℕ} (hi : i < c) (hδ : δ < 3) : lv a b c V
  (4 * a + 2 * b + 3 * i + δ) =
    if δ < 2 then V (2 * a + b + 2 * i + δ % 2) else - V (2 * a + b + 2 * i + δ % 2) := by
  simp only [lv, lab_t hi hδ, sgn_t hi hδ, decide_eq_true_eq]

theorem Sm_handle (V : ℕ → A) {i : ℕ} (hi : i < a) : Sm a b c V (4 * (i + 1)) = Sm a b c V (4 * i)
  := by
  have e : 4 * (i + 1) = 4 * i + 3 + 1 := by ring
  rw [e, Sm_succ, Sm_succ, Sm_succ, Sm_succ]
  rw [show 4 * i = 4 * i + 0 from rfl, lv_h V hi (δ := 0) (by norm_num),
    lv_h V hi (δ := 1) (by norm_num),
    lv_h V hi (δ := 2) (by norm_num), lv_h V hi (δ := 3) (by norm_num)]
  simp only [Nat.add_zero, Nat.zero_mod, Nat.reduceMod, Nat.reduceLT, ite_true, ite_false,
    Nat.ofNat_pos]
  abel

theorem Sm_cap (V : ℕ → A) {i : ℕ} (hi : i < b) :
    Sm a b c V (4 * a + 2 * (i + 1)) = Sm a b c V (4 * a + 2 * i) + 2 • V (2 * a + i) := by
  have e : 4 * a + 2 * (i + 1) = 4 * a + 2 * i + 1 + 1 := by ring
  rw [e, Sm_succ, Sm_succ]
  rw [show 4 * a + 2 * i = 4 * a + 2 * i + 0 from rfl, lv_c V hi (δ := 0) (by norm_num),
    lv_c V hi (δ := 1) (by norm_num)]
  simp only [Nat.add_zero, two_nsmul, add_assoc]

theorem Sm_hole (V : ℕ → A) {i : ℕ} (hi : i < c) : Sm a b c V (4 * a + 2 * b + 3 * (i + 1)) =
    Sm a b c V (4 * a + 2 * b + 3 * i) + V (2 * a + b + 2 * i + 1) := by
  have e : 4 * a + 2 * b + 3 * (i + 1) = 4 * a + 2 * b + 3 * i + 2 + 1 := by ring
  rw [e, Sm_succ, Sm_succ, Sm_succ]
  rw [show 4 * a + 2 * b + 3 * i = 4 * a + 2 * b + 3 * i + 0 from rfl,
    lv_t V hi (δ := 0) (by norm_num),
    lv_t V hi (δ := 1) (by norm_num), lv_t V hi (δ := 2) (by norm_num)]
  simp only [Nat.add_zero, Nat.zero_mod, Nat.reduceMod, Nat.reduceLT, ite_true, ite_false,
    Nat.ofNat_pos]
  abel

theorem Sm_last (V : ℕ → A) : Sm a b c V (4 * a + 2 * b + 3 * c + 2) = Sm a b c V
  (4 * a + 2 * b + 3 * c) := by
  have e1 : ∀ δ, lv a b c V (4 * a + 2 * b + 3 * c + δ) =
      if δ = 0 then V (2 * a + b + 2 * c) else - V (2 * a + b + 2 * c) := fun δ => by
    simp only [lv, lab_l, sgn_l, decide_eq_true_eq]
  have e2 : 4 * a + 2 * b + 3 * c + 2 = 4 * a + 2 * b + 3 * c + 1 + 1 := rfl
  rw [e2, Sm_succ, Sm_succ, e1 1, show 4 * a + 2 * b + 3 * c = 4 * a + 2 * b + 3 * c + 0 from rfl,
    e1 0]
  simp

theorem Sm_handles (V : ℕ → A) {i : ℕ} (hi : i ≤ a) : Sm a b c V (4 * i) = 0 := by
  induction i with
  | zero => simp [Sm]
  | succ i ih => rw [Sm_handle V (by omega), ih (by omega)]

theorem Sm_caps (V : ℕ → A) {i : ℕ} (hi : i ≤ b) :
    Sm a b c V (4 * a + 2 * i) = 2 • ∑ l ∈ Finset.range i, V (2 * a + l) := by
  induction i with
  | zero =>
    have := Sm_handles (a := a) (b := b) (c := c) V le_rfl
    simpa using this
  | succ i ih => rw [Sm_cap V (by omega), ih (by omega), Finset.sum_range_succ, smul_add]

theorem Sm_holes (V : ℕ → A) {i : ℕ} (hi : i ≤ c) : Sm a b c V (4 * a + 2 * b + 3 * i) =
    2 • (∑ l ∈ Finset.range b, V (2 * a + l)) + ∑ l ∈ Finset.range i, V (2 * a + b + 2 * l + 1)
      := by
  induction i with
  | zero =>
    have := Sm_caps (a := a) (b := b) (c := c) V le_rfl
    simpa using this
  | succ i ih => rw [Sm_hole V (by omega), ih (by omega), Finset.sum_range_succ, add_assoc]

theorem Sm_total (V : ℕ → A) : Sm a b c V (4 * a + 2 * b + 3 * c + 2) =
    2 • (∑ l ∈ Finset.range b, V (2 * a + l)) + ∑ l ∈ Finset.range c, V (2 * a + b + 2 * l + 1)
      := by
  rw [Sm_last, Sm_holes V le_rfl]

theorem twin_eq_iff {p : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) :
    twin a b c p = p ↔ ∃ i < c, p = 4 * a + 2 * b + 3 * i + 1 := by
  unfold twin
  constructor
  · intro h
    refine ⟨(p - (4 * a + 2 * b)) / 3, ?_, ?_⟩ <;> split_ifs at h <;> omega
  · rintro ⟨i, hi, rfl⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right
      (by omega), ite_eq_right (by omega)]

theorem st_lt {p : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) : st a b c p ≤ 4 * a + 2 * b + 3 * c + 2
  := by
  unfold st
  split_ifs <;> omega

theorem en_lt {p : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) : en a b c p ≤ 4 * a + 2 * b + 3 * c + 2
  := by
  unfold en
  split_ifs <;> omega

/-- If the values of the loops and of the free sides are zero, then the sum vanishes at the start of
each side that is
not free. -/
theorem Sm_st_zero (V : ℕ → A) (h1 : ∀ k < 2 * a + b, V k = 0) (h2 : ∀ i < c, V
  (2 * a + b + 2 * i + 1) = 0) {p : ℕ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) (ht : twin a b c p ≠ p) : Sm a b c V (st a b c p) = 0 := by
  have hb : ∑ l ∈ Finset.range b, V (2 * a + l) = 0 := Finset.sum_eq_zero fun l hl => h1 _ (by
    have := Finset.mem_range.mp hl
    omega)
  have hc : ∀ i ≤ c, Sm a b c V (4 * a + 2 * b + 3 * i) = 0 := fun i hi => by
    rw [Sm_holes V hi, hb, smul_zero, zero_add]
    exact Finset.sum_eq_zero fun l hl => h2 _ (by
      have := Finset.mem_range.mp hl
      omega)
  have hlow : ∀ j ≤ 4 * a + 2 * b, Sm a b c V j = 0 := by
    intro j
    induction j with
    | zero => intro _; simp [Sm]
    | succ j ih =>
      intro hj
      rw [Sm_succ, ih (by omega), zero_add, lv]
      have h3 : lab a b c j < 2 * a + b := by
        unfold lab
        split_ifs <;> omega
      rw [h1 _ h3]
      simp
  by_cases hp1 : p < 4 * a + 2 * b
  · refine hlow _ ?_
    unfold st
    split_ifs <;> omega
  by_cases hp2 : p < 4 * a + 2 * b + 3 * c
  · obtain ⟨x, rfl⟩ : ∃ x, p = 4 * a + 2 * b + x := ⟨p - (4 * a + 2 * b), by omega⟩
    have hd : x % 3 = 0 ∨ x % 3 = 2 := by
      by_contra hcon
      apply ht
      refine (twin_eq_iff hp).mpr ⟨x / 3, by omega, by omega⟩
    rcases hd with hd | hd
    · have e : 4 * a + 2 * b + x = 4 * a + 2 * b + 3 * (x / 3) + 0 := by omega
      have h4 : st a b c (4 * a + 2 * b + x) = 4 * a + 2 * b + 3 * (x / 3) := by
        unfold st
        rw [e, sgn_t (by omega) (by norm_num)]
        simp
      rw [h4]
      exact hc _ (by omega)
    · have e : 4 * a + 2 * b + x = 4 * a + 2 * b + 3 * (x / 3) + 2 := by omega
      have h4 : st a b c (4 * a + 2 * b + x) = 4 * a + 2 * b + 3 * (x / 3 + 1) := by
        unfold st
        rw [e, sgn_t (by omega) (by norm_num)]
        simp
        omega
      rw [h4]
      exact hc _ (by omega)
  · obtain ⟨x, hx, rfl⟩ : ∃ x, x < 2 ∧ p = 4 * a + 2 * b + 3 * c + x := ⟨p -
    (4 * a + 2 * b + 3 * c), by omega, by omega⟩
    interval_cases x
    · have h4 : st a b c (4 * a + 2 * b + 3 * c + 0) = 4 * a + 2 * b + 3 * c := by
        unfold st
        rw [sgn_l]
        simp
      rw [h4]
      exact hc _ le_rfl
    · have h4 : st a b c (4 * a + 2 * b + 3 * c + 1) = 4 * a + 2 * b + 3 * c + 2 := by
        unfold st
        rw [sgn_l]
        simp
      rw [h4, Sm_last]
      exact hc _ le_rfl

end GraphMinor.Surface

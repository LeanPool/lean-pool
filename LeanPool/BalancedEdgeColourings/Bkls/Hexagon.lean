/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.HexTable
public import Mathlib.Tactic.FinCases

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 5

`hexagon`: pendant colours `p i ∈ Fin 4` on a hexagon (with diagonals on the opposite pairs in
`D`), `p i ≠ p (i + 3)` off `D`, extend to a proper colouring of the hexagon and the diagonals in
which opposite vertices see different colour sets. The witnesses come from `Hex.table`, checked by
`Hex.check`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.Hex

theorem dig_lt (n i : Nat) : dig n i < 4 := Nat.mod_lt _ (by decide)

theorem qv_lt (mask n w i : Nat) : qv mask n w i < 4 := by
  unfold qv; split_ifs <;> exact dig_lt _ _

/-- The encoding of `p`. -/
def enc (p : ZMod 6 → Fin 4) : Nat :=
  (p 0).val + 4 * (p 1).val + 16 * (p 2).val + 64 * (p 3).val + 256 * (p 4).val +
    1024 * (p 5).val

theorem enc_lt (p : ZMod 6 → Fin 4) : enc p < 4096 := by
  unfold enc
  have := (p 0).isLt; have := (p 1).isLt; have := (p 2).isLt; have := (p 3).isLt
  have := (p 4).isLt; have := (p 5).isLt
  omega

theorem dig_enc (p : ZMod 6 → Fin 4) (i : ZMod 6) : dig (enc p) i.val = (p i).val := by
  unfold dig enc
  have := (p 0).isLt; have := (p 1).isLt; have := (p 2).isLt; have := (p 3).isLt
  have := (p 4).isLt; have := (p 5).isLt
  fin_cases i <;> simp <;> omega

/-- The encoding of `D` (one bit per opposite pair). -/
noncomputable def maskOf (D : Finset (ZMod 6)) : Nat := by
  classical
  exact (if (0 : ZMod 6) ∈ D then 1 else 0) + (if (1 : ZMod 6) ∈ D then 2 else 0) +
    (if (2 : ZMod 6) ∈ D then 4 else 0)

theorem maskOf_lt (D : Finset (ZMod 6)) : maskOf D < 8 := by
  unfold maskOf; split_ifs <;> omega

theorem inD_iff (m j : Nat) : inD m j = true ↔ m / 2 ^ j % 2 = 1 := by
  simp [inD, Nat.shiftRight_eq_div_pow]

theorem maskOf_bits (D : Finset (ZMod 6)) :
    (maskOf D / 2 ^ 0 % 2 = 1 ↔ (0 : ZMod 6) ∈ D) ∧ (maskOf D / 2 ^ 1 % 2 = 1 ↔ (1 : ZMod 6) ∈ D) ∧
      (maskOf D / 2 ^ 2 % 2 = 1 ↔ (2 : ZMod 6) ∈ D) := by
  classical
  unfold maskOf
  by_cases a : (0 : ZMod 6) ∈ D <;> by_cases b : (1 : ZMod 6) ∈ D <;>
    by_cases c : (2 : ZMod 6) ∈ D <;> simp [a, b, c]

theorem zmod6_cases (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide

theorem inD_maskOf (D : Finset (ZMod 6)) (hD : ∀ i, i ∈ D ↔ i + 3 ∈ D) (i : ZMod 6) :
    inD (maskOf D) (i.val % 3) = true ↔ i ∈ D := by
  rw [inD_iff]
  obtain ⟨b0, b1, b2⟩ := maskOf_bits D
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  · exact b0
  · exact b1
  · exact b2
  · rw [show (3 : ZMod 6) = 0 + 3 from rfl, ← hD 0]; exact b0
  · rw [show (4 : ZMod 6) = 1 + 3 from rfl, ← hD 1]; exact b1
  · rw [show (5 : ZMod 6) = 2 + 3 from rfl, ← hD 2]; exact b2

theorem sum_three {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ x ∈ ({a, b, c} : Finset (Fin 4)), x.val = a.val + b.val + c.val := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]; omega

theorem val_sub_one (i : ZMod 6) : (i - 1).val = (i.val + 5) % 6 := by
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem val_add_three (i : ZMod 6) : (i + 3).val = (i.val + 3) % 6 := by
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem val_lt_six (i : ZMod 6) : i.val < 6 := by
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Lemma 5.** -/
theorem hexagon (D : Finset (ZMod 6)) (hD : ∀ i, i ∈ D ↔ i + 3 ∈ D) (p : ZMod 6 → Fin 4)
    (hp : ∀ i, i ∉ D → p i ≠ p (i + 3)) :
    ∃ h q : ZMod 6 → Fin 4, (∀ i, i ∉ D → q i = p i) ∧ (∀ i, i ∈ D → q i = q (i + 3)) ∧
      Proper h q ∧ ∀ i, S h q i ≠ S h q (i + 3) := by
  set n := enc p
  set m := maskOf D
  have hok : okEntry m n = true := by
    have := check
    simp only [List.all_eq_true, List.mem_range] at this
    exact this m (maskOf_lt D) n (enc_lt p)
  have hpre : ((List.range 3).all fun i => inD m i || dig n i != dig n (i + 3)) = true := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]
    intro j hj
    have hjv : ((j : ZMod 6)).val = j := by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> rfl
    by_cases hin : (j : ZMod 6) ∈ D
    · left
      have := (inD_maskOf D hD (j : ZMod 6)).2 hin
      rwa [hjv, Nat.mod_eq_of_lt hj] at this
    · right
      have h1 := dig_enc p (j : ZMod 6)
      have h2 := dig_enc p ((j : ZMod 6) + 3)
      rw [hjv] at h1
      rw [val_add_three, hjv, Nat.mod_eq_of_lt (by omega)] at h2
      rw [h1, h2]
      exact fun e => hp _ hin (Fin.ext e)
  unfold okEntry at hok
  rw [hpre] at hok
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    at hok
  obtain ⟨hv, hs⟩ := hok
  set w := wit (m * 4096 + n)
  let h : ZMod 6 → Fin 4 := fun i => ⟨dig w i.val, dig_lt _ _⟩
  let q : ZMod 6 → Fin 4 := fun i => ⟨qv m n w i.val, qv_lt _ _ _ _⟩
  have hprop : Proper h q := by
    intro i
    have := hv i.val (val_lt_six i)
    simp only [okVertex, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨fun e => h1 ?_, fun e => h2 ?_, fun e => h3 ?_⟩
    · have := congrArg Fin.val e; simp only [h, val_sub_one] at this; exact this
    · have := congrArg Fin.val e; simp only [h, q, val_sub_one] at this; exact this
    · have := congrArg Fin.val e; simp only [h, q] at this; exact this
  refine ⟨h, q, fun i hi => ?_, fun i hi => ?_, hprop, fun i e => ?_⟩
  · have hf : inD m (i.val % 3) = false := by
      have := (inD_maskOf D hD i).not.2 hi; simpa using this
    apply Fin.ext
    simp only [q, qv, hf, Bool.false_eq_true, ite_false]
    exact dig_enc p i
  · have ht : inD m (i.val % 3) = true := (inD_maskOf D hD i).2 hi
    have ht' : inD m ((i + 3).val % 3) = true := (inD_maskOf D hD (i + 3)).2 ((hD i).1 hi)
    apply Fin.ext
    simp only [q, qv, ht, ht', ite_true]
    rw [val_add_three]
    congr 1
    have := val_lt_six i
    omega
  · -- compare the sums of the colour sets
    obtain ⟨a1, a2, a3⟩ := hprop i
    obtain ⟨b1, b2, b3⟩ := hprop (i + 3)
    have e2 := congrArg (fun T : Finset (Fin 4) => ∑ x ∈ T, x.val) e
    simp only [S] at e2
    rw [sum_three a1 a2 a3, sum_three b1 b2 b3] at e2
    simp only [h, q, val_sub_one, val_add_three] at e2
    have hi6 := val_lt_six i
    rcases Nat.lt_or_ge i.val 3 with hlt | hge
    · have := hs i.val hlt
      simp only [sumAt, bne_iff_ne, ne_eq] at this
      apply this
      rw [show (i.val + 3) % 6 = i.val + 3 by omega] at e2
      rw [show (i.val + 3 + 5) % 6 = (i.val + 3 + 5) % 6 from rfl]
      exact e2
    · have := hs (i.val - 3) (by omega)
      simp only [sumAt, bne_iff_ne, ne_eq] at this
      apply this
      rw [show i.val - 3 + 3 = i.val by omega, show (i.val + 3) % 6 = i.val - 3 by omega,
        show (i.val - 3 + 5) % 6 = (i.val - 3 + 5) % 6 from rfl] at *
      exact e2.symm

end Bkls.Hex

end LeanPool.BalancedEdgeColourings

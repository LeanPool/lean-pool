/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Theory.CycleSets
public import Mathlib.Data.List.GetD

/-!
# Numeric codes for integral atoms

For kernel computations the atoms of `IntegralAtom (Fin s) (Fin n)` are numbered `0, …, s + 2 * n`:
`one ↦ 0`, `symm i ↦ 1 + i`, `nsymm i b ↦ 1 + s + 2 * i + b`.
-/

@[expose] public section

namespace RACert

open FiniteIntegralRelationAlgebras.RelationAlgebra IntegralAtom

variable {s n : ℕ}

/-- The number of atoms. -/
def numAtoms (s n : ℕ) : ℕ := 1 + s + 2 * n

/-- The numeric code of an atom. -/
def enc : IntegralAtom (Fin s) (Fin n) → ℕ
  | .one => 0
  | .symm i => 1 + i
  | .nsymm i b => 1 + s + 2 * i + b.toNat

/-- The atom with a given code (`one` for codes out of range). -/
def dec (s n : ℕ) (c : ℕ) : IntegralAtom (Fin s) (Fin n) :=
  if c = 0 then .one
  else if hs : c - 1 < s then .symm ⟨c - 1, hs⟩
  else if hn : (c - 1 - s) / 2 < n then
    .nsymm ⟨(c - 1 - s) / 2, hn⟩ ((c - 1 - s) % 2 == 1)
  else .one

/-- Converse on codes. -/
def cvN (s c : ℕ) : ℕ :=
  bif Nat.ble c s then c
  else bif Nat.beq (Nat.mod (Nat.sub c s) 2) 1 then Nat.add c 1 else Nat.sub c 1

theorem enc_lt (a : IntegralAtom (Fin s) (Fin n)) : enc a < numAtoms s n := by
  cases a with
  | one => simp [enc, numAtoms]
  | symm i => simp only [enc, numAtoms]; omega
  | nsymm i b => cases b <;> simp only [enc, numAtoms, Bool.toNat_false, Bool.toNat_true] <;> omega

@[simp]
theorem dec_enc (a : IntegralAtom (Fin s) (Fin n)) : dec s n (enc a) = a := by
  cases a with
  | one => simp [enc, dec]
  | symm i =>
    have : 1 + (i : ℕ) - 1 = i := by omega
    simp [enc, dec, this]
  | nsymm i b =>
    have h1 : ¬ (1 + s + 2 * (i : ℕ) + b.toNat = 0) := by omega
    have h2 : ¬ (1 + s + 2 * (i : ℕ) + b.toNat - 1 < s) := by omega
    have h3 : (1 + s + 2 * (i : ℕ) + b.toNat - 1 - s) / 2 = i := by
      cases b <;> simp <;> omega
    have h4 : (1 + s + 2 * (i : ℕ) + b.toNat - 1 - s) % 2 = b.toNat := by
      cases b <;> simp <;> omega
    simp only [enc, dec, h1, h2, h3, h4, dite_false, Fin.is_lt, dite_true, Fin.eta, ite_false]
    cases b <;> simp

theorem enc_injective : Function.Injective (enc : IntegralAtom (Fin s) (Fin n) → ℕ) :=
  Function.LeftInverse.injective dec_enc

@[simp]
theorem enc_inj {a b : IntegralAtom (Fin s) (Fin n)} : enc a = enc b ↔ a = b := enc_injective.eq_iff

theorem enc_dec {c : ℕ} (hc : c < numAtoms s n) : enc (dec s n c) = c := by
  unfold dec
  split_ifs with h0 hs hn
  · simp [enc, h0]
  · simp only [enc]; omega
  · simp only [enc]
    rcases Nat.mod_two_eq_zero_or_one (c - 1 - s) with h | h <;> simp [h] <;> omega
  · simp only [numAtoms] at hc; omega

@[simp]
theorem enc_one : enc (.one : IntegralAtom (Fin s) (Fin n)) = 0 := rfl

@[simp]
theorem enc_eq_zero_iff {a : IntegralAtom (Fin s) (Fin n)} : enc a = 0 ↔ a = .one := by
  rw [← enc_one, enc_inj]

@[simp]
theorem dec_zero : dec s n 0 = .one := by simp [dec]

theorem cvN_of_le {s c : ℕ} (h : c ≤ s) : cvN s c = c := by
  have hb : Nat.ble c s = true := Nat.ble_eq_true_of_le h
  simp only [cvN, hb, Bool.cond_true]

theorem cvN_of_odd {s c : ℕ} (h : s < c) (h2 : (c - s) % 2 = 1) : cvN s c = c + 1 := by
  have hb : Nat.ble c s = false := by
    rw [Bool.eq_false_iff, Ne, Nat.ble_eq]; omega
  have hm : Nat.beq (Nat.mod (Nat.sub c s) 2) 1 = true := by
    rw [Nat.beq_eq]; exact h2
  unfold cvN
  rw [hb, hm]
  rfl

theorem cvN_of_even {s c : ℕ} (h : s < c) (h2 : (c - s) % 2 = 0) : cvN s c = c - 1 := by
  have hb : Nat.ble c s = false := by
    rw [Bool.eq_false_iff, Ne, Nat.ble_eq]; omega
  have hm : Nat.beq (Nat.mod (Nat.sub c s) 2) 1 = false := by
    rw [Bool.eq_false_iff, Ne, Nat.beq_eq]
    change ¬ ((c - s) % 2 = 1)
    omega
  unfold cvN
  rw [hb, hm]
  rfl

@[simp]
theorem enc_conv (a : IntegralAtom (Fin s) (Fin n)) : enc (conv a) = cvN s (enc a) := by
  cases a with
  | one => rw [cvN_of_le (by simp [enc])]; rfl
  | symm i => rw [cvN_of_le (by simp only [enc]; omega)]; rfl
  | nsymm i b =>
    cases b
    · rw [cvN_of_odd (by simp only [enc]; omega) (by simp only [enc, Bool.toNat_false]; omega)]
      simp [enc]
    · rw [cvN_of_even (by simp only [enc]; omega) (by simp only [enc, Bool.toNat_true]; omega)]
      simp [enc]

theorem cvN_lt {c : ℕ} (hc : c < numAtoms s n) : cvN s c < numAtoms s n := by
  rw [← enc_dec hc, ← enc_conv]
  exact enc_lt _

theorem cvN_cvN {c : ℕ} (hc : c < numAtoms s n) : cvN s (cvN s c) = c := by
  rw [← enc_dec hc, ← enc_conv, ← enc_conv, conv_conv]

theorem dec_cvN {c : ℕ} (hc : c < numAtoms s n) : dec s n (cvN s c) = conv (dec s n c) := by
  apply enc_injective
  rw [enc_conv, enc_dec hc, enc_dec (cvN_lt hc)]

/-- Quantification over atoms is quantification over codes. -/
theorem forall_atom_iff {p : IntegralAtom (Fin s) (Fin n) → Prop} :
    (∀ a, p a) ↔ ∀ c < numAtoms s n, p (dec s n c) :=
  ⟨fun h c _ => h _, fun h a => by simpa using h (enc a) (enc_lt a)⟩

theorem exists_atom_iff {p : IntegralAtom (Fin s) (Fin n) → Prop} :
    (∃ a, p a) ↔ ∃ c < numAtoms s n, p (dec s n c) :=
  ⟨fun ⟨a, h⟩ => ⟨enc a, enc_lt a, by simpa using h⟩, fun ⟨c, _, h⟩ => ⟨_, h⟩⟩

/-- The map on atoms described by a list of codes: the atom with code `c` is sent to the atom with
code `l[c]`. -/
def permFun (s n : ℕ) (l : List ℕ) (a : IntegralAtom (Fin s) (Fin n)) :
    IntegralAtom (Fin s) (Fin n) :=
  dec s n (l.getD (enc a) 0)

/-- The number of lawful cycle sets invariant under the atom map coded by `l`. -/
noncomputable def fixCountL (s n : ℕ) (l : List ℕ) : ℕ :=
  Nat.card {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T ∧
    ∀ a b c, (permFun s n l a, permFun s n l b, permFun s n l c) ∈ T ↔ (a, b, c) ∈ T}

end RACert

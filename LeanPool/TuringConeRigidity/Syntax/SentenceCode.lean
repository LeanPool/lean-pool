/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SentenceCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryLanguage

/-!
# Sentence Code
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel

/-- The natural-number code of an atomic syntax label. -/
def atom (n : ℕ) : ℕ := Nat.pair 0 n
/-- The natural-number code of a binary tree cell. -/
def cell (a b : ℕ) : ℕ := Nat.pair (a+1) b
/-- Encode a tagged binary syntax constructor with its two child codes. -/
def binary (tag a b : ℕ) : ℕ := cell (atom tag) (cell a (cell b (atom 0)))
/-- Encode a tagged unary syntax constructor with its child code. -/
def unary (tag a : ℕ) : ℕ := cell (atom tag) (cell a (atom 0))

theorem encode_equal (i j : ℕ) :
    Encodable.encode (SentenceForm.equal i j) = binary 0 (atom i) (atom j) := rfl
theorem encode_member (i j : ℕ) :
    Encodable.encode (SentenceForm.member i j) = binary 1 (atom i) (atom j) := rfl
theorem encode_conj (p q : SentenceForm) :
    Encodable.encode (SentenceForm.conj p q) = binary 2 (Encodable.encode p) (Encodable.encode q)
      := rfl
theorem encode_neg (p : SentenceForm) :
    Encodable.encode (SentenceForm.neg p) = unary 3 (Encodable.encode p) := rfl
theorem encode_ex (p : SentenceForm) :
    Encodable.encode (SentenceForm.ex p) = unary 4 (Encodable.encode p) := rfl

theorem cell_left_lt (a b : ℕ) : a < cell a b := by
  have h := Nat.left_le_pair (a+1) b
  unfold cell; omega

theorem cell_right_le (a b : ℕ) : b ≤ cell a b := Nat.right_le_pair _ _

theorem binary_left_lt (t a b : ℕ) : a < binary t a b :=
  lt_of_lt_of_le (cell_left_lt a _) (cell_right_le _ _)
theorem binary_right_lt (t a b : ℕ) : b < binary t a b :=
  lt_of_lt_of_le (cell_left_lt b _) (le_trans (cell_right_le _ _) (cell_right_le _ _))
theorem unary_child_lt (t a : ℕ) : a < unary t a :=
  lt_of_lt_of_le (cell_left_lt a _) (cell_right_le _ _)

/-- A code is a valid formula constructor whose immediate child codes satisfy `C`. -/
def Step (C : ℕ → Prop) (c : ℕ) : Prop :=
  (∃ i j, c = binary 0 (atom i) (atom j)) ∨
  (∃ i j, c = binary 1 (atom i) (atom j)) ∨
  (∃ a b, c = binary 2 a b ∧ C a ∧ C b) ∨
  (∃ a, c = unary 3 a ∧ C a) ∨
  (∃ a, c = unary 4 a ∧ C a)

/-- Every immediate subformula code satisfies the predicate `C`. -/
def Children (C : ℕ → Prop) : SentenceForm → Prop
  | .equal _ _ | .member _ _ => True
  | .conj p q => C (Encodable.encode p) ∧ C (Encodable.encode q)
  | .neg p | .ex p => C (Encodable.encode p)

theorem step_encode (C : ℕ → Prop) (p : SentenceForm) :
    Step C (Encodable.encode p) ↔ Children C p := by
  cases p <;>
    simp [Step,Children,encode_equal,encode_member,encode_conj,encode_neg,encode_ex,
      binary,unary,cell,atom,Nat.pair_eq_pair]

/-- Every member of `C` is a valid constructor with its children again in `C`. -/
def Closed (C : ℕ → Prop) : Prop := ∀ c, C c → Step C c

theorem Closed.valid {C : ℕ → Prop} (h : Closed C) (c : ℕ) (hc : C c) :
    ∃ p : SentenceForm, c = Encodable.encode p := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    rcases h c hc with he|hm|ha|hn|hx
    · obtain ⟨i,j,rfl⟩ := he; exact ⟨.equal i j,(encode_equal i j).symm⟩
    · obtain ⟨i,j,rfl⟩ := hm; exact ⟨.member i j,(encode_member i j).symm⟩
    · obtain ⟨a,b,rfl,ha,hb⟩ := ha
      obtain ⟨p,rfl⟩ := ih a (binary_left_lt _ _ _) ha
      obtain ⟨q,rfl⟩ := ih b (binary_right_lt _ _ _) hb
      exact ⟨.conj p q,(encode_conj p q).symm⟩
    · obtain ⟨a,rfl,ha⟩ := hn
      obtain ⟨p,rfl⟩ := ih a (unary_child_lt _ _) ha
      exact ⟨.neg p,(encode_neg p).symm⟩
    · obtain ⟨a,rfl,ha⟩ := hx
      obtain ⟨p,rfl⟩ := ih a (unary_child_lt _ _) ha
      exact ⟨.ex p,(encode_ex p).symm⟩

end TuringRigidity.SentenceCoding

end OAI

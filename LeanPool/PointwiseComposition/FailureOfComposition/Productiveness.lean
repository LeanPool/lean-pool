/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Computability.RE

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The productiveness step in v36, for Mathlib's program numbering.
The productivity function is the identity on program numbers.
-/

@[expose] public section

namespace FailureOfComposition

open Encodable Denumerable _root_.Nat.Partrec

/-- The W construction in `FailureOfComposition`. -/
def W (e n : ℕ) : Prop :=
  (Code.eval (ofNat Code e) n).Dom

/-- The diagonal Halts construction in `FailureOfComposition`. -/
def diagonalHalts (n : ℕ) : Prop :=
  W n n

/-- The usual productive-set condition, including computability of the witness. -/
def Productive (A : ℕ → Prop) : Prop :=
  ∃ p : ℕ → ℕ, Computable p ∧ ∀ d, (∀ n, W d n → A n) → A (p d) ∧ ¬W d (p d)

theorem diagonal_escape (d : ℕ) (h : ∀ n, W d n → ¬diagonalHalts n) :
    ¬diagonalHalts d ∧ ¬W d d :=
  by
  have hd : ¬W d d := fun hd => h d hd hd
  exact ⟨hd, hd⟩

theorem complement_diagonal_productive : Productive (fun n => ¬diagonalHalts n) := by
  exact ⟨id, Computable.id, diagonal_escape⟩

/-- A domain presentation of an r.e. predicate, with the numbering made explicit. -/
theorem exists_domain_index {D : ℕ → Prop} (hD : REPred D) : ∃ d, ∀ n, W d n ↔ D n :=
  by
  have hf := hD.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨encode c, ?_⟩
  intro n
  simp [W, hc, Part.assert]

/-- The diagonal index itself escapes any r.e. subset of the divergent diagonal. -/
theorem productive_escape_re {D : ℕ → Prop} (hD : REPred D)
    (hSound : ∀ n, D n → ¬diagonalHalts n) : ∃ d, ¬diagonalHalts d ∧ ¬D d :=
  by
  obtain ⟨d, hd⟩ := exists_domain_index hD
  obtain ⟨hdiv, hnot⟩ := diagonal_escape d (fun n hn => hSound n ((hd n).mp hn))
  exact ⟨d, hdiv, fun hn => hnot ((hd d).mpr hn)⟩

end FailureOfComposition

end

end PointwiseComposition

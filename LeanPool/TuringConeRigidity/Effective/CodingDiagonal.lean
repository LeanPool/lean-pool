/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingDiagonal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingColumns
public import LeanPool.TuringConeRigidity.Computability.OracleCode
public import LeanPool.TuringConeRigidity.Effective.CodingForcing

/-!
# Coding Diagonal
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingDiagonal
open CodingForcing CodingColumns

/-- At some assigned coding position, the designated program does not return the left-word
bit, including when it diverges. -/
def Diagonal (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (k cutoff : ℕ) (e : OracleCode) (p : Condition) : Prop :=
  ∃ n, location (A k) (hA k) k cutoff n < p.left.length ∧
    OracleCode.eval (oracleFunction (A k)) e n ≠
      Part.some (if p.left.getD (location (A k) (hA k) k cutoff n) false then 1 else 0)

theorem diagonal_mono {A : ℕ → Oracle} {hA : ∀ k, {a | A k a = true}.Infinite}
    {k cutoff : ℕ} {e : OracleCode} {p q : Condition}
    (hpq : Extends A p q) (hp : Diagonal A hA k cutoff e p) :
    Diagonal A hA k cutoff e q := by
  obtain ⟨n, hn, he⟩ := hp
  exact ⟨n, hn.trans_le hpq.1.length_le, by rwa [getD_of_prefix hpq.1 hn]⟩

theorem exists_different_bit (v : Part ℕ) :
    ∃ b : Bool, v ≠ Part.some (if b then 1 else 0) := by
  by_cases h : v = Part.some 0
  · exact ⟨true, by simp [h]⟩
  · exact ⟨false, h⟩

theorem prescribe (A : ℕ → Oracle) (p : Condition) (m : ℕ)
    (hm : p.left.length ≤ m) (b : Bool) :
    ∃ q, Extends A p q ∧ m < q.left.length ∧ q.left.getD m false = b := by
  refine ⟨append p (List.replicate (m - p.left.length + 1) b), append_extends A p _, ?_, ?_⟩
  · simp only [append, List.length_append, List.length_replicate]
    omega
  · simp only [append, List.getD_eq_getElem?_getD, List.getElem?_append,
      ite_eq_right (Nat.not_lt.mpr hm)]
    simp

theorem diagonal_dense (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (k cutoff : ℕ) (e : OracleCode) (p : Condition) :
    ∃ q, Extends A p q ∧ Diagonal A hA k cutoff e q := by
  let n := p.left.length
  let m := location (A k) (hA k) k cutoff n
  obtain ⟨b, hb⟩ := exists_different_bit (OracleCode.eval (oracleFunction (A k)) e n)
  obtain ⟨q, hpq, hmq, hqb⟩ := prescribe A p m (le_location _ _ _ _ _) b
  refine ⟨q, hpq, n, hmq, ?_⟩
  simpa only [← hqb] using hb

end TuringRigidity.CodingDiagonal

end OAI

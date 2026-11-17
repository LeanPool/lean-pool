/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelJoin.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelPairing
public import LeanPool.TuringConeRigidity.Computability.Joins

/-!
# Set Model Join
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem natSet_successor_eq (n m : ℕ) :
    natSet.{u} n = insert (natSet m) (natSet m) ↔ n = m+1 := by
  change natSet n = natSet (m+1) ↔ n = m+1
  exact natSet_injective.eq_iff

theorem join_true_iff (A B : Oracle) (v : ℕ) : join A B v = true ↔
    ∃ n, (v = 2*n ∧ A n = true) ∨ (v = 2*n+1 ∧ B n = true) := by
  constructor
  · intro h
    have hv : v = 2*(v/2) ∨ v = 2*(v/2)+1 := by omega
    refine ⟨v/2,?_⟩
    rcases hv with he|he
    · exact Or.inl ⟨he,(join_even A B (v/2)).symm.trans ((congrArg (join A B) he).symm.trans h)⟩
    · exact Or.inr ⟨he,(join_odd A B (v/2)).symm.trans ((congrArg (join A B) he).symm.trans h)⟩
  · rintro ⟨n,⟨rfl,hA⟩|⟨rfl,hB⟩⟩
    · exact (join_even A B n).trans hA
    · exact (join_odd A B n).trans hB

def joinFormula : Formula :=
  .existsMem 1 (.disj (.conj (tripleFormula 0 0 1 5 6) (.member 0 3))
    (.existsMem 2 (.conj (tripleFormula 1 1 0 6 7)
      (.conj (.successor 2 0) (.member 1 5)))))

theorem eval_joinFormula (A B : Oracle) (v : ℕ) :
    joinFormula.Eval (cons (natSet.{u} v) (cons ZFSet.omega (cons (realSet A)
      (cons (realSet B) (cons additionSet (fun _ => pairNumbers)))))) ↔ join A B v = true := by
  simp only [joinFormula,Formula.Eval,Formula.eval_disj,eval_tripleFormula,
    Formula.eval_successor,cons_zero,cons_succ]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,addition_code,natSet_successor_eq,nat_mem_realSet]
  rw [join_true_iff]
  simp [two_mul]

theorem join_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {A B : Oracle} (hA : A ∈ reals M) (hB : B ∈ reals M) : join A B ∈ reals M := by
  have hω := omega_mem M hM hS hI
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  let e := cons ZFSet.omega (cons (realSet A) (cons (realSet B)
    (cons additionSet (fun _ => pairNumbers))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hA
    · exact hB
    · exact ha
    · exact hd
  exact real_comprehension M hM hS hI (join A B) joinFormula e he (eval_joinFormula A B)

end
end TuringRigidity.SetModelArithmetic

end OAI

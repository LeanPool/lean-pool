/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Models.Signed.Transfer
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Examples of satisfiability checks

Finite satisfiability of a variable inequality, of incompatible bounds, and of the recursive
constructor bounds `f(x, …, x) ≤ x ≤ f(x, …, x)` at arities zero and one: the recursive bounds
have a finite solution exactly at arity zero. The checks are proved in the kernel and then
evaluated with the compiled procedures, also for a contravariant constructor, for constraints
without variables, and for satisfiability over arbitrary trees.

## Main declarations

- `inequality`, `inconsistent`: a satisfiable inequality and incompatible bounds, at every arity.
-/

@[expose] public section


namespace DeciSigma1.Examples.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Satisfiability DeciSigma1.Semantics

/-- A variable inequality has a finite solution at every arity and variance. -/
theorem inequality (n : ℕ) (c : Fin n → Bool) :
    satFinB c ([.le false true] : List (LitT n Bool)) = true := by
  apply (satFinB_iff _ _).mpr
  refine ⟨fun _ => .bot, ?_⟩
  simp [SatT, HoldsT, treeLe_refl]

example : satFinB (n := 0) (fun _ => false) ([.le false true] : List (LitT 0 Bool)) = true :=
  inequality 0 _

example : satFinB (n := 1) (fun _ => false) ([.le false true] : List (LitT 1 Bool)) = true :=
  inequality 1 _

/-- The constraint `x = ⊤ ∧ x ≤ y ∧ y = ⊥` has no finite solution, at every arity. -/
theorem inconsistent (n : ℕ) : satFinB (fun _ => false)
    ([.eqTop false, .le false true, .eqBot true] : List (LitT n Bool)) = false := by
  simp only [Bool.eq_false_iff, ne_eq, satFinB_iff]
  rintro ⟨σ, hσ⟩
  have ht : (σ false).toTree = Tree.top := hσ (.eqTop false) (by simp)
  have hb : (σ true).toTree = Tree.bot := hσ (.eqBot true) (by simp)
  have hle : (σ false).toTree ≤ (σ true).toTree :=
    (treeLe_false_iff_le _ _).mp (hσ (.le false true) (by simp))
  rw [ht, hb] at hle
  exact Tree.top_ne_bot ((Tree.le_bot_iff _).mp hle)

example : satFinB (n := 0) (fun _ => false)
    ([.eqTop false, .le false true, .eqBot true] : List (LitT 0 Bool)) = false :=
  inconsistent 0

example : satFinB (n := 1) (fun _ => false)
    ([.eqTop false, .le false true, .eqBot true] : List (LitT 1 Bool)) = false :=
  inconsistent 1

example : satFinB (n := 0) (fun _ => false)
    ([.fLe (fun _ => ()) (), .leF () (fun _ => ())] : List (LitT 0 Unit)) = true := by
  apply (satFinB_iff _ _).mpr
  refine ⟨fun _ => .node (fun i => i.elim0), ?_⟩
  simp [SatT, HoldsT, treeLe_false_iff_le, FTree.toTree]

example : satFinB (n := 1) (fun _ => false)
    ([.fLe (fun _ => ()) (), .leF () (fun _ => ())] : List (LitT 1 Unit)) = false := by
  simp only [Bool.eq_false_iff, ne_eq, satFinB_iff, satFinite_iff_signed, satFin_iff]
  intro h
  apply h.2
  refine ⟨[0], ((), false), ((), false), by simp, ?_, .refl _, ?_⟩
  · exact LowerAt.cons (a := fun _ => ((), false)) (by simp [signed,
    signedLit]) (.refl _) (.nil (.refl _))
  · exact UpperAt.cons (b := fun _ => ((), false)) (.refl _) (by simp [signed,
    signedLit]) (.nil (.refl _))

end DeciSigma1.Examples.Satisfiability

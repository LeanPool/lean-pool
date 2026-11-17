/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/OracleCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.Degrees
public import LeanPool.TuringConeRigidity.Effective.EncodableTree
public import Mathlib.Data.Set.Countable

/-!
# Oracle Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

inductive OracleCode where
  | zero | succ | left | right | query
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | find : OracleCode → OracleCode

namespace OracleCode

/-- The constructor-tag encoding used by the former Encodable derivation. -/
def toTree : OracleCode → EncodableTree
  | .zero => .cons (.nat 0) (.nat 0)
  | .succ => .cons (.nat 1) (.nat 0)
  | .left => .cons (.nat 2) (.nat 0)
  | .right => .cons (.nat 3) (.nat 0)
  | .query => .cons (.nat 4) (.nat 0)
  | .pair a b => .cons (.nat 5) (.cons (toTree a) (.cons (toTree b) (.nat 0)))
  | .comp a b => .cons (.nat 6) (.cons (toTree a) (.cons (toTree b) (.nat 0)))
  | .prec a b => .cons (.nat 7) (.cons (toTree a) (.cons (toTree b) (.nat 0)))
  | .find a => .cons (.nat 8) (.cons (toTree a) (.nat 0))

/-- Decode the constructor-tag encoding, rejecting malformed trees. -/
def fromTree : EncodableTree → Option OracleCode
  | .cons (.nat 0) (.nat 0) => some .zero
  | .cons (.nat 1) (.nat 0) => some .succ
  | .cons (.nat 2) (.nat 0) => some .left
  | .cons (.nat 3) (.nat 0) => some .right
  | .cons (.nat 4) (.nat 0) => some .query
  | .cons (.nat 5) (.cons a (.cons b (.nat 0))) => do
    return .pair (← fromTree a) (← fromTree b)
  | .cons (.nat 6) (.cons a (.cons b (.nat 0))) => do
    return .comp (← fromTree a) (← fromTree b)
  | .cons (.nat 7) (.cons a (.cons b (.nat 0))) => do
    return .prec (← fromTree a) (← fromTree b)
  | .cons (.nat 8) (.cons a (.nat 0)) => do
    return .find (← fromTree a)
  | _ => none

theorem fromTree_toTree (p : OracleCode) : fromTree (toTree p) = some p := by
  induction p <;> simp_all [toTree, fromTree]

end OracleCode

-- Module-port repair: explicit instance, with the same tree tags as deriving.
instance : Encodable OracleCode :=
  Encodable.ofLeftInjection OracleCode.toTree OracleCode.fromTree OracleCode.fromTree_toTree

namespace OracleCode

def eval (g : ℕ →. ℕ) : OracleCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .query => g
  | .pair c d => fun n => Nat.pair <$> eval g c n <*> eval g d n
  | .comp c d => fun n => eval g d n >>= eval g c
  | .prec c d => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (eval g c a) fun y ih => do
        let i ← ih
        eval g d (Nat.pair a (Nat.pair y i))
  | .find c => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> eval g c (Nat.pair a n)

theorem eval_recursiveIn (g : ℕ →. ℕ) (c : OracleCode) :
    Nat.RecursiveIn {g} (eval g c) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | query => exact .oracle g (Set.mem_singleton g)
  | pair c d hc hd => exact .pair hc hd
  | comp c d hc hd => exact .comp hc hd
  | prec c d hc hd => exact .prec hc hd
  | find c hc => exact .rfind hc

theorem exists_code {g f : ℕ →. ℕ} (hf : Nat.RecursiveIn {g} f) :
    ∃ c : OracleCode, eval g c = f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle f hf =>
      have hfg : f = g := Set.mem_singleton_iff.mp hf
      subst f
      exact ⟨.query, rfl⟩
  | pair _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.pair c d, rfl⟩
  | comp _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.comp c d, rfl⟩
  | prec _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.prec c d, rfl⟩
  | rfind _ hc =>
      obtain ⟨c, rfl⟩ := hc
      exact ⟨.find c, rfl⟩

theorem turingReducible_iff_exists_code (f g : ℕ →. ℕ) :
    TuringReducible f g ↔ ∃ c : OracleCode, eval g c = f := by
  change RecursiveIn {g} f ↔ _
  rw [RecursiveIn.iff_nat]
  exact ⟨exists_code, fun ⟨c, hc⟩ => hc ▸ eval_recursiveIn g c⟩

theorem countable_reducible (g : ℕ →. ℕ) :
    {f : ℕ →. ℕ | TuringReducible f g}.Countable := by
  have heq : {f : ℕ →. ℕ | TuringReducible f g} = Set.range (eval g) := by
    ext f
    exact turingReducible_iff_exists_code f g
  rw [heq]
  exact Set.countable_range _

end OracleCode

theorem oracleFunction_injective : Function.Injective oracleFunction := by
  intro A B hab
  funext n
  have h := congrFun hab n
  cases ha : A n <;> cases hb : B n <;> simp [oracleFunction, ha, hb] at h ⊢

theorem countable_reduces (B : Oracle) : {A : Oracle | Reduces A B}.Countable := by
  exact (OracleCode.countable_reducible (oracleFunction B)).preimage oracleFunction_injective

theorem countable_degree_fiber (a : Degree) : {A : Oracle | degree A = a}.Countable := by
  obtain ⟨B, rfl⟩ := degree_surjective a
  apply (countable_reduces B).mono
  intro A hA
  exact ((degree_eq_iff A B).mp hA).1

theorem countable_lift_fiber {X : Type*} (C : X → Oracle) (hC : Function.Injective C)
    (π : Degree → Degree) (hπ : Function.Injective π)
    (F : X → Oracle) (hF : ∀ x, degree (F x) = π (degree (C x))) (B : Oracle) :
    {x : X | F x = B}.Countable := by
  by_cases hne : ∃ x, F x = B
  · obtain ⟨x₀, hx₀⟩ := hne
    apply ((countable_degree_fiber (degree (C x₀))).preimage hC).mono
    intro x hx
    apply hπ
    rw [← hF x, ← hF x₀, hx, hx₀]
  · have hempty : {x : X | F x = B} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨x,h⟩
    rw [hempty]
    exact Set.countable_empty

end TuringRigidity

end OAI

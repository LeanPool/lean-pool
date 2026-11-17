/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticSkolem.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticFiniteTest

/-!
# Arithmetic Skolem
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section

/-- The predicate has a presentation by a finite arithmetic test. -/
def HasTest (P : Predicate) : Prop := ∃ t : Test, t.Presents P

namespace HasTest

private def col (k : ℕ) (t : Test) : Test :=
  t.subst .input (fun s => .witness (.pair (.const k) s))

private theorem col_eval (k : ℕ) (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    (col k t).eval O f v ↔ t.eval O (fun n => f (Nat.pair k n)) v :=
  t.eval_subst _ _ O f _ v (fun _ => rfl)

theorem pure (P : ℕ → Prop) (hP : PrimrecPred P) : HasTest (fun _ v => P v) := by
  refine ⟨.pure P hP (.left .input),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem query (i : ℕ) : HasTest (fun O v => O i v = true) := by
  refine ⟨.query i (.left .input),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem not_pure (P : ℕ → Prop) (hP : PrimrecPred P) : HasTest (fun _ v => ¬ P v) := by
  refine ⟨.neg (.pure P hP (.left .input)),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem not_query (i : ℕ) : HasTest (fun O v => ¬ O i v = true) := by
  refine ⟨.neg (.query i (.left .input)),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem and {P Q} (hP : HasTest P) (hQ : HasTest Q) :
    HasTest (fun O v => P O v ∧ Q O v) := by
  classical
  obtain ⟨t,ht⟩ := hP
  obtain ⟨s,hs⟩ := hQ
  refine ⟨.and (col 0 t) (col 1 s),fun O v => ?_⟩
  simp only [Test.eval,col_eval]
  constructor
  · rintro ⟨hp,hq⟩
    obtain ⟨f,hf⟩ := (ht O v).mp hp
    obtain ⟨g,hg⟩ := (hs O v).mp hq
    refine ⟨fun k => if (Nat.unpair k).1 = 0 then f (Nat.unpair k).2 else g (Nat.unpair k).2,?_⟩
    intro n
    constructor
    · simpa only [Nat.unpair_pair,ite_eq_left rfl,ite_true] using hf n
    · simpa only [Nat.unpair_pair,ite_eq_right (Nat.one_ne_zero)] using hg n
  · rintro ⟨f,hf⟩
    exact ⟨(ht O v).mpr ⟨_,fun n => (hf n).1⟩,
      (hs O v).mpr ⟨_,fun n => (hf n).2⟩⟩

private def tailTest (t : Test) : Test :=
  t.subst .input (fun s => .witness (.prim Nat.succ Primrec.succ s))

private theorem tail_eval (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    (tailTest t).eval O f v ↔ t.eval O (fun n => f (n+1)) v :=
  t.eval_subst _ _ O f _ v (fun _ => rfl)

private def zeroTag : Test :=
  .pure (fun n => n = 0) (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (.witness (.const 0))

theorem or {P Q} (hP : HasTest P) (hQ : HasTest Q) :
    HasTest (fun O v => P O v ∨ Q O v) := by
  classical
  obtain ⟨t,ht⟩ := hP
  obtain ⟨s,hs⟩ := hQ
  refine ⟨(Test.and zeroTag (tailTest t)).or (.and (.neg zeroTag) (tailTest s)),fun O v => ?_⟩
  simp only [Test.eval_or,Test.eval,tail_eval,zeroTag,Term.eval]
  constructor
  · intro h
    rcases h with hp | hq
    · obtain ⟨f,hf⟩ := (ht O v).mp hp
      exact ⟨(fun n => Nat.casesOn n 0 f),fun n => Or.inl ⟨rfl,hf n⟩⟩
    · obtain ⟨g,hg⟩ := (hs O v).mp hq
      exact ⟨(fun n => Nat.casesOn n 1 g),fun n => Or.inr ⟨by simp,hg n⟩⟩
  · rintro ⟨f,hf⟩
    by_cases hz : f 0 = 0
    · exact Or.inl ((ht O v).mpr ⟨_,fun n => ((hf n).resolve_right (fun h => h.1 hz)).2⟩)
    · exact Or.inr ((hs O v).mpr ⟨_,fun n => ((hf n).resolve_left (fun h => hz h.1)).2⟩)

theorem comp {P} (hP : HasTest P) (g : ℕ → ℕ) (hg : Primrec g) :
    HasTest (fun O v => P O (g v)) := by
  obtain ⟨t,ht⟩ := hP
  let inputTerm : Term := .pair (.prim g hg (.left .input)) (.right .input)
  refine ⟨t.subst inputTerm Term.witness,fun O v => ?_⟩
  dsimp only
  rw [ht]
  apply exists_congr
  intro f
  apply forall_congr'
  intro n
  simpa only [inputTerm,Term.eval,Term.left,Term.right,UniformArithmetic.left,
    UniformArithmetic.right,Nat.unpair_pair] using
    (t.eval_subst inputTerm Term.witness O f f (Nat.pair v n) (fun _ => rfl)).symm

theorem ex {P} (hP : HasTest P) : HasTest (fun O v => ∃ k, P O (Nat.pair v k)) := by
  obtain ⟨t,ht⟩ := hP
  let inputTerm : Term := .pair (.pair (.left .input) (.witness (.const 0))) (.right .input)
  let q : Term → Term := fun s => .witness (.prim Nat.succ Primrec.succ s)
  have he O f v n : (t.subst inputTerm q).eval O f (Nat.pair v n) ↔
      t.eval O (fun k => f (k+1)) (Nat.pair (Nat.pair v (f 0)) n) := by
    simpa only [inputTerm,Term.eval,Term.left,Term.right,UniformArithmetic.left,
      UniformArithmetic.right,Nat.unpair_pair] using
      t.eval_subst inputTerm q O f (fun k => f (k+1)) (Nat.pair v n) (fun _ => rfl)
  refine ⟨t.subst inputTerm q,fun O v => ?_⟩
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨f,hf⟩ := (ht O (Nat.pair v k)).mp hk
    exact ⟨(fun n => Nat.casesOn n k f),fun n => (he _ _ _ _).mpr (hf n)⟩
  · rintro ⟨f,hf⟩
    exact ⟨f 0,(ht O _).mpr ⟨_,fun n => (he _ _ _ _).mp (hf n)⟩⟩

theorem all {P} (hP : HasTest P) : HasTest (fun O v => ∀ k, P O (Nat.pair v k)) := by
  classical
  obtain ⟨t,ht⟩ := hP
  let inputTerm : Term := .pair (.pair (.left .input) (.left (.right .input))) (.right (.right
    .input))
  let q : Term → Term := fun s => .witness (.pair (.left (.right .input)) s)
  have he O f v n : (t.subst inputTerm q).eval O f (Nat.pair v n) ↔
      t.eval O (fun k => f (Nat.pair (Nat.unpair n).1 k))
        (Nat.pair (Nat.pair v (Nat.unpair n).1) (Nat.unpair n).2) := by
    simpa only [inputTerm,Term.eval,Term.left,Term.right,UniformArithmetic.left,
      UniformArithmetic.right,Nat.unpair_pair] using
      t.eval_subst inputTerm q O f (fun k => f (Nat.pair (Nat.unpair n).1 k))
        (Nat.pair v n) (fun _ => by simp [q,Term.eval,Term.left,Term.right,
          UniformArithmetic.left,UniformArithmetic.right])
  refine ⟨t.subst inputTerm q,fun O v => ?_⟩
  constructor
  · intro h
    have hh : ∀ k, ∃ f, ∀ n, t.eval O f (Nat.pair (Nat.pair v k) n) :=
      fun k => (ht O _).mp (h k)
    choose f hf using hh
    refine ⟨fun n => f (Nat.unpair n).1 (Nat.unpair n).2,fun n => (he _ _ _ _).mpr ?_⟩
    simpa only [Nat.unpair_pair] using hf (Nat.unpair n).1 (Nat.unpair n).2
  · rintro ⟨f,hf⟩ k
    refine (ht O _).mpr ⟨fun n => f (Nat.pair k n),fun n => ?_⟩
    simpa only [Nat.unpair_pair] using (he _ _ _ _).mp (hf (Nat.pair k n))

theorem congr {P Q} (hP : HasTest P) (he : ∀ O v, P O v ↔ Q O v) : HasTest Q := by
  obtain ⟨t,ht⟩ := hP
  exact ⟨t,fun O v => (he O v).symm.trans (ht O v)⟩
end HasTest

theorem arithmetic_tests {P} (h : Arith P) : HasTest P ∧ HasTest (fun O v => ¬ P O v) := by
  induction h with
  | pure P hP => exact ⟨HasTest.pure P hP,HasTest.not_pure P hP⟩
  | query i => exact ⟨HasTest.query i,HasTest.not_query i⟩
  | neg h ih => exact ⟨ih.2,ih.1.congr (fun _ _ => not_not.symm)⟩
  | and h k ih ik =>
    exact ⟨ih.1.and ik.1,(ih.2.or ik.2).congr (fun _ _ => not_and_or.symm)⟩
  | ex h ih => exact ⟨ih.1.ex,ih.2.all.congr (fun _ _ => not_exists.symm)⟩
  | comp f h hf ih => exact ⟨ih.1.comp f hf,ih.2.comp f hf⟩

end
end TuringRigidity.ArithmeticTree

end OAI

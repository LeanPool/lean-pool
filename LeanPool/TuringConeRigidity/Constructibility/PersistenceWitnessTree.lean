/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistenceWitnessTree.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticSkolem
public import LeanPool.TuringConeRigidity.Computability.ArithmeticWitnessTree
public import LeanPool.TuringConeRigidity.Constructibility.PersistentNonidentity

/-!
# Persistence Witness Tree
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Test

/-- Replace oracle-query leaves of a test by the supplied tests. -/
def bindOracle (q : ℕ → Term → Test) : Test → Test
  | .pure P hP t => .pure P hP t
  | .query i t => q i t
  | .neg t => .neg (t.bindOracle q)
  | .and t s => .and (t.bindOracle q) (s.bindOracle q)

theorem eval_bindOracle (t : Test) (q : ℕ → Term → Test)
    (O U : Oracles) (f : ℕ → ℕ) (v : ℕ)
    (hq : ∀ i s, (q i s).eval O f v ↔ U i (s.eval f v) = true) :
    (t.bindOracle q).eval O f v ↔ t.eval U f v := by
  induction t with
  | pure P hP t => rfl
  | query i t => exact hq i t
  | neg t ih => exact not_congr ih
  | and t s ih ik => exact and_congr ih ik

/-- Keep the first two oracle channels and read remaining queries from the numerical witness's
real channel. -/
def realQuery : ℕ → Term → Test
  | 0, t => .query 0 t
  | 1, t => .query 1 t
  | _+2, t => .pure (fun n => n = 1)
      (Primrec.eq.comp Primrec.id (Primrec.const 1)) (.witness (.pair (.const 0) t))

/-- Combine real queries and witness queries into separate channels of one numerical witness. -/
def mergeReal (t : Test) : Test :=
  (t.subst .input (fun s => .witness (.pair (.const 1) s))).bindOracle realQuery

/-- The Boolean real encoded in channel zero of a numerical witness. -/
def realPart (f : ℕ → ℕ) : Oracle := fun n => decide (f (Nat.pair 0 n) = 1)
/-- The numerical witness function encoded in channel one. -/
def witnessPart (f : ℕ → ℕ) : ℕ → ℕ := fun n => f (Nat.pair 1 n)

theorem mergeReal_eval (t : Test) (A R : Oracle) (f : ℕ → ℕ) (v : ℕ) :
    t.mergeReal.eval (parameters A R (fun _ => false)) f v ↔
      t.eval (parameters A R (realPart f)) (witnessPart f) v := by
  unfold mergeReal
  apply Iff.trans (t.subst _ _ |>.eval_bindOracle realQuery _
    (parameters A R (realPart f)) f v ?_)
  · exact t.eval_subst _ _ _ f _ v (fun _ => rfl)
  · intro i s
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => simp [realQuery,eval,Term.eval,parameters,realPart]

private def joinWitness (H : Oracle) (f : ℕ → ℕ) : ℕ → ℕ := fun n =>
  if (Nat.unpair n).1 = 0 then (if H (Nat.unpair n).2 then 1 else 0) else f (Nat.unpair n).2

private theorem realPart_join (H : Oracle) (f : ℕ → ℕ) :
    realPart (joinWitness H f) = H := by
  funext n
  cases hn : H n <;> simp [realPart,joinWitness,hn]

private theorem witnessPart_join (H : Oracle) (f : ℕ → ℕ) :
    witnessPart (joinWitness H f) = f := by
  funext n
  simp [witnessPart,joinWitness]

theorem exists_mergeReal (t : Test) (A R : Oracle) (v : ℕ) :
    (∃ H : Oracle, ∃ f : ℕ → ℕ, ∀ n, t.eval (parameters A R H) f (Nat.pair v n)) ↔
      ∃ f : ℕ → ℕ, ∀ n, t.mergeReal.eval (parameters A R (fun _ => false)) f (Nat.pair v n) := by
  constructor
  · rintro ⟨H,f,hf⟩
    refine ⟨joinWitness H f,fun n => (t.mergeReal_eval _ _ _ _).mpr ?_⟩
    simpa only [realPart_join,witnessPart_join] using hf n
  · rintro ⟨f,hf⟩
    exact ⟨realPart f,witnessPart f,fun n => (t.mergeReal_eval _ _ _ _).mp (hf n)⟩
end Test

theorem piOneOne_tree {P : Oracle → Oracle → Prop} (hP : PiOneOne P) :
    ∃ t : Test, ∀ A R, P A R ↔
      WellFounded (t.Child (parameters A R (fun _ => false)) 0) := by
  obtain ⟨Q,hQ,hiff⟩ := hP
  obtain ⟨t,ht⟩ := (arithmetic_tests hQ).2
  refine ⟨t.mergeReal,fun A R => ?_⟩
  rw [t.mergeReal.wellFounded_iff,← t.exists_mergeReal]
  rw [hiff]
  simp only [not_exists]
  apply forall_congr'
  intro H
  have he := ht (parameters A R H) 0
  simpa only [not_not,not_exists] using not_congr he

theorem persistence_trees :
    (∃ t : Test, ∀ A R, Property A R ↔
      WellFounded (t.Child (parameters A R (fun _ => false)) 0)) ∧
    (∃ t : Test, ∀ A R, (Property A R ∧ Moved A R) ↔
      WellFounded (t.Child (parameters A R (fun _ => false)) 0)) :=
  ⟨piOneOne_tree source_4_2_1,piOneOne_tree nonidentity_piOneOne⟩

end
end TuringRigidity.ArithmeticTree

end OAI

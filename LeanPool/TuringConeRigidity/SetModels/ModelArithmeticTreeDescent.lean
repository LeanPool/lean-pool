/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelArithmeticTreeDescent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTreeSequence
public import LeanPool.TuringConeRigidity.Constructibility.PersistenceWitnessTree
public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalRealRelation
public import LeanPool.TuringConeRigidity.SetModels.ModelArithmeticComprehension

/-!
# Model Arithmetic Tree Descent
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticTree
open UniformArithmetic BoundedSetTheory TransitiveNameModel ArithmeticPersistence
universe u
noncomputable section

theorem Test.sourceT_chain (t : Test) (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (O : Oracles) (hO : ∀ i, O i ∈ modelReals M) (v : ℕ)
    (hw : ∃ f : ℕ → ℕ, ∀ n, t.eval O f (Nat.pair v n)) :
    ∃ s : ℕ → ℕ, ∃ G ∈ modelReals M,
      (∀ n k, G (Nat.pair n k) = true ↔ k = s n) ∧
      ∀ n, t.eval O (chainValue s) (Nat.pair v n) := by
  let P : Predicate := fun O k => t.codeChild O v (left k) (right k)
  let B := arithmeticReal P O
  have hB : B ∈ modelReals M := sourceT_arithmetic_comprehension M hM hT (t.codeChild_arith v) O hO
  have hb (x y : ℕ) : B (Nat.pair x y) = true ↔ t.codeChild O v x y := by
    simpa only [P,left,right,Nat.unpair_pair] using arithmeticReal_true P O (Nat.pair x y)
  obtain ⟨s,hs⟩ := t.code_chain_exists O v hw
  obtain ⟨s,G,hGM,hG,hs⟩ := sourceT_realRelation_descent M hM hT hB
    ⟨s,fun n => (hb _ _).mpr (hs n)⟩
  exact ⟨s,G,hGM,hG,t.code_chain_eval O v s (fun n => (hb _ _).mp (hs n))⟩

/-- Read one value from a decoded finite witness-tree node, using zero when the entry is
absent. -/
def nodeValue (k i : ℕ) : ℕ := ((decodeNode k)[i]?).getD 0

theorem nodeValue_primrec : Primrec (fun p : ℕ × ℕ => nodeValue p.1 p.2) :=
  Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (decodeNode_primrec.comp Primrec.fst) Primrec.snd)
    (Primrec.const 0)

/-- The coded chain has a node at stage `i + 1` whose `i`th entry is the proposed value. -/
def chainGraphPredicate (O : Oracles) (v : ℕ) : Prop :=
  ∃ k, O 0 (Nat.pair (left v + 1) k) = true ∧ nodeValue k (left v) = right v

theorem chainGraph_arith : Arith chainGraphPredicate := by
  have hq := (Arith.query 0).comp (fun v => Nat.pair (left (left v)+1) (right v))
    (Primrec₂.natPair.comp (Primrec.succ.comp (left_primrec.comp left_primrec)) right_primrec)
  have he := equal
    (nodeValue_primrec.comp (right_primrec.pair (left_primrec.comp left_primrec)))
    (right_primrec.comp left_primrec)
  exact (hq.and he).ex.congr (fun _ _ => by
    simp only [chainGraphPredicate,left,right,Nat.unpair_pair])

theorem sourceT_chainGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (s : ℕ → ℕ) {G : Oracle} (hGM : G ∈ modelReals M)
    (hG : ∀ n k, G (Nat.pair n k) = true ↔ k = s n) :
    ∃ F ∈ modelReals M, ∀ i j, F (Nat.pair i j) = true ↔ j = chainValue s i := by
  let O : Oracles := fun _ => G
  refine ⟨arithmeticReal chainGraphPredicate O,
    sourceT_arithmetic_comprehension M hM hT chainGraph_arith O (fun _ => hGM),?_⟩
  intro i j
  rw [arithmeticReal_true]
  simp only [chainGraphPredicate,O,left,right,Nat.unpair_pair,hG,exists_eq_left]
  exact eq_comm

theorem sourceT_realPart (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (f : ℕ → ℕ) {F : Oracle} (hFM : F ∈ modelReals M)
    (hF : ∀ i j, F (Nat.pair i j) = true ↔ j = f i) : Test.realPart f ∈ modelReals M := by
  have hq := (Arith.query 0).comp (fun n => Nat.pair (Nat.pair 0 n) 1)
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id) (Primrec.const 1))
  apply sourceT_arithmetic_real M hM hT hq (fun _ => F) (fun _ => hFM) (Test.realPart f)
  intro n
  simp only [Test.realPart,decide_eq_true_eq,hF]
  exact eq_comm

end
end TuringRigidity.ArithmeticTree

end OAI

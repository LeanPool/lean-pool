/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalAtomicTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.AtomicDecisionFormula
public import LeanPool.TuringConeRigidity.Syntax.AtomicTruth
public import LeanPool.TuringConeRigidity.SetModels.InternalContainer

/-!
# Internal Atomic Truth
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

/-- The condition filter meets every dense family whose set code belongs to the ground model. -/
def GroundGeneric (M : ZFSet.{u}) (G : GenericFilter (Conditions c)) : Prop :=
  ∀ D ∈ M, Dense {q | label c q ∈ D} → ∃ q ∈ G.carrier, label c q ∈ D

theorem internal_atomic_requirements (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) :
    ∃ D ∈ M, ∃ E ∈ M,
      (∀ q, label c q ∈ D ↔ q ∈ MemTest a b) ∧ (∀ q, label c q ∈ E ↔ q ∈ EqTest a b) := by
  obtain ⟨d,hd,hdT,hdab⟩ := internal_transitive_container M hM hP hU hS hR hI
    (pair_mem M hM hP ha hb)
  have had : a.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hbd : b.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let e := cons d (cons c (cons k (cons o (cons f
    (cons (a.encode (label c)) (cons (b.encode (label c)) (fun _ => c)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hk
    rcases i with _ | i
    · exact hoM
    rcases i with _ | i
    · exact hf
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hb
    exact hc
  let φ := AtomicFormula.memTest 1 2 3 4 5 6 7 0
  let ψ := AtomicFormula.eqTest 1 2 3 4 5 6 7 0
  have hφ (q : Conditions c) : φ.Eval (cons (label c q) e) ↔ q ∈ MemTest a b := by
    simp only [φ,AtomicFormula.memTest,Formula.eval_disj,AtomicFormula.eval_witness,
      AtomicFormula.eval_negMem,cons_zero,cons_succ,e]
    exact or_congr (codeWitness_iff hdT ho hfG a b had hbd q)
      (codeNeg_iff hdT ho hfG a b had hbd q)
  have hψ (q : Conditions c) : ψ.Eval (cons (label c q) e) ↔ q ∈ EqTest a b := by
    simp only [ψ,AtomicFormula.eqTest,Formula.eval_disj,AtomicFormula.eval_triple,
      AtomicFormula.eval_refute,cons_zero,cons_succ,e]
    have hEq := (triple_pair had hbd).trans (hfG.correct hdT ho a b had hbd q)
    have hA := codeRefute_iff hdT ho hfG a b had hbd q
    have hB := codeRefute_iff hdT ho hfG b a hbd had q
    cases a
    cases b
    exact or_congr hEq (or_congr hA hB)
  refine ⟨ZFSet.sep (fun z => φ.Eval (cons z e)) c,sep_mem M hM hS φ e he hc,
    ZFSet.sep (fun z => ψ.Eval (cons z e)) c,sep_mem M hM hS ψ e he hc,?_,?_⟩
  · intro q
    simp only [ZFSet.mem_sep,label_mem c q,true_and,hφ]
  · intro q
    simp only [ZFSet.mem_sep,label_mem c q,true_and,hψ]

theorem groundGeneric_atomic (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) : Generic (names M c) G := by
  have requirements (a : Name (Conditions c)) (ha : a ∈ names M c)
      (b : Name (Conditions c)) (hb : b ∈ names M c) :=
    internal_atomic_requirements M hM hP hU hPow hS hR hI hc hoM ho a b ha hb
  constructor
  · intro a ha b hb
    obtain ⟨D,hD,E,hE,hDm,hEe⟩ := requirements a ha b hb
    have hd : Dense {q | label c q ∈ D} := by
      intro p
      obtain ⟨q,hq,hm⟩ := memTest_dense a b p
      exact ⟨q,hq,(hDm q).mpr hm⟩
    obtain ⟨q,hq,hqd⟩ := hG D hD hd
    exact ⟨q,hq,(hDm q).mp hqd⟩
  · intro a ha b hb
    obtain ⟨D,hD,E,hE,hDm,hEe⟩ := requirements a ha b hb
    have hd : Dense {q | label c q ∈ E} := by
      intro p
      obtain ⟨q,hq,hm⟩ := eqTest_dense a b p
      exact ⟨q,hq,(hEe q).mpr hm⟩
    obtain ⟨q,hq,hqe⟩ := hG E hE hd
    exact ⟨q,hq,(hEe q).mp hqe⟩

theorem internal_atomic_truth (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) :
    (Name.val G.carrier a = Name.val G.carrier b ↔ ∃ p ∈ G.carrier, EqForces a b p) ∧
    (Name.val G.carrier a ∈ Name.val G.carrier b ↔ ∃ p ∈ G.carrier, MemForces a b p) := by
  have hg := groundGeneric_atomic M hM hP hU hPow hS hR hI hc hoM ho G hG
  exact ⟨eq_truth (names_childClosed M c hM) G hg a b ha hb,
    mem_truth (names_childClosed M c hM) G hg a b ha hb⟩

end TuringRigidity.AtomicForcing

end OAI

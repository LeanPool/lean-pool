/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalProductReplacement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductClosure

/-!
# Ordinal Product Replacement
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

def productSigma : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.bounded (productMatrix 3 4 5 2 1 0))))

theorem productSigma_sentence : fromSigma productSigma = productSentence := rfl

theorem productSigma_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSigma.Realize M e ↔ e 0 = (a*b).toZFSet := by
  rw [← sigma_sat,productSigma_sentence]
  exact productSentence_sourceT M hM hT e he a b ha hb

def multiplePairSigma : SigmaFormula :=
  .existsSet (.conj (.bounded (.orderedPair 1 2 0))
    (productSigma.rename (fun i => if i = 0 then 0 else if i = 1 then 3 else 2)))

theorem multiplePairSigma_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a c : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hc : c.toZFSet ∈ M)
    (y : ZFSet.{u}) (hy : y ∈ M) :
    multiplePairSigma.Realize M (cons y (cons c.toZFSet (fun _ => a.toZFSet))) ↔
      y = ZFSet.pair c.toZFSet (a*c).toZFSet := by
  change (∃ v ∈ M, (SigmaFormula.conj _ _).Realize M
    (cons v (cons y (cons c.toZFSet (fun _ => a.toZFSet))))) ↔ _
  have sem (v : ZFSet.{u}) (hv : v ∈ M) :
      (SigmaFormula.conj (.bounded (.orderedPair 1 2 0))
        (productSigma.rename (fun i => if i = 0 then 0 else if i = 1 then 3 else 2))).Realize M
        (cons v (cons y (cons c.toZFSet (fun _ => a.toZFSet)))) ↔
      y = ZFSet.pair c.toZFSet v ∧ v = (a*c).toZFSet := by
    rw [SigmaFormula.realize_conj]
    apply and_congr
    · change (Formula.orderedPair 1 2 0).Realize M _ ↔ _
      rw [Formula.absolute _ M hM _ (by
        intro i; rcases i with _|_|_|i <;> assumption),Formula.eval_orderedPair]
      rfl
    · rw [SigmaFormula.realize_rename]
      exact productSigma_sourceT M hM hT _ (by
        intro i
        change cons v (cons y (cons c.toZFSet (fun _ => a.toZFSet)))
          (if i = 0 then 0 else if i = 1 then 3 else 2) ∈ M
        split
        · exact hv
        split
        · exact ha
        exact hc) a c rfl rfl
  constructor
  · rintro ⟨v,hv,h⟩
    obtain ⟨he,rfl⟩ := (sem v hv).mp h
    exact he
  · intro h
    have hv := (ordinal_mul_internal M hM hT a c ha hc).1
    exact ⟨_,hv,(sem _ hv).mpr ⟨h,rfl⟩⟩

theorem ordinal_multiple_graph_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    ∃ f ∈ M, ∀ z : ZFSet.{u}, z ∈ f ↔
      ∃ c < b, z = ZFSet.pair c.toZFSet (a*c).toZFSet := by
  let pairAt := fun c : Ordinal.{u} => ZFSet.pair c.toZFSet (a*c).toZFSet
  have hcM (c : Ordinal.{u}) (hc : c < b) : c.toZFSet ∈ M :=
    hM _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc)
  have hpM (c : Ordinal.{u}) (hc : c < b) : pairAt c ∈ M :=
    orderedPair_mem M hM hT.pairing (hcM c hc)
      (ordinal_mul_internal M hM hT a c ha (hcM c hc)).1
  obtain ⟨f,hf,hdef⟩ := hT.replacement.finitePrefix multiplePairSigma (fun _ => a.toZFSet)
    (fun _ => ha) b.toZFSet hb (by
      intro x hx
      obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      refine ⟨pairAt c,hpM c hc,
        (multiplePairSigma_sourceT M hM hT a c ha (hcM c hc) _ (hpM c hc)).mpr rfl,?_⟩
      intro y hy h
      exact (multiplePairSigma_sourceT M hM hT a c ha (hcM c hc) y hy).mp h)
  refine ⟨f,hf,?_⟩
  intro z
  constructor
  · intro hz
    have hzM := hM _ hf _ hz
    obtain ⟨x,hx,hp⟩ := (hdef z hzM).mp hz
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    exact ⟨c,hc,(multiplePairSigma_sourceT M hM hT a c ha (hcM c hc) z hzM).mp hp⟩
  · rintro ⟨c,hc,rfl⟩
    exact (hdef _ (hpM c hc)).mpr ⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hc,
      (multiplePairSigma_sourceT M hM hT a c ha (hcM c hc) _ (hpM c hc)).mpr rfl⟩

end TuringRigidity.OrdinalArithmetic

end OAI

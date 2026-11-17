/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicDefinability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.AtomicCertificate

/-!
# Atomic Definability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

def Atomic (isMem : Bool) (a b : Name (Conditions c)) (p : Conditions c) : Prop :=
  if isMem then MemForces a b p else EqForces a b p

private theorem eval_matrix (isMem : Bool) (d k o f : ZFSet.{u})
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a b : Name (Conditions c)) (p : Conditions c) (tail : ℕ → ZFSet.{u}) :
    (AtomicFormula.matrix isMem).Eval (cons f (cons k (cons d (cons (label c p)
      (cons (a.encode (label c)) (cons (b.encode (label c)) (cons c (cons o tail)))))))) ↔
    Transitive d ∧ a.encode (label c) ∈ d ∧ b.encode (label c) ∈ d ∧
      k = ZFSet.prod d d ∧ Graph d c o f ∧ Atomic isMem a b p := by
  let e := cons f (cons k (cons d (cons (label c p)
    (cons (a.encode (label c)) (cons (b.encode (label c)) (cons c (cons o tail)))))))
  have query (hd : Transitive d) (ha : a.encode (label c) ∈ d)
      (hb : b.encode (label c) ∈ d) (hk : k = ZFSet.prod d d) (hf : Graph d c o f) :
      (AtomicFormula.query isMem 2 6 1 7 0 4 5 3).Eval e ↔ Atomic isMem a b p := by
    cases isMem
    · simp only [AtomicFormula.query,Atomic,Bool.false_eq_true,ite_false,AtomicFormula.eval_triple]
      change Triple k f (a.encode (label c)) (b.encode (label c)) (label c p) ↔ _
      rw [hk]
      exact (triple_pair ha hb).trans (hf.correct hd ho a b ha hb p)
    · exact eval_membership hd ho hf a b ha hb p e 2 6 1 7 0 4 5 3
        ⟨rfl,rfl,hk,rfl,rfl,rfl,rfl,rfl⟩
  change (AtomicFormula.matrix isMem).Eval e ↔ _
  simp only [AtomicFormula.matrix,Formula.Eval,Formula.eval_transitive,
    AtomicFormula.eval_product,cons_zero,cons_succ,e]
  constructor
  · rintro ⟨hd,ha,hb,hk,hgraph,hquery⟩
    have hf := (AtomicFormula.eval_graph 2 6 1 7 0 e hk).mp hgraph
    exact ⟨hd,ha,hb,hk,hf,(query hd ha hb hk hf).mp hquery⟩
  · rintro ⟨hd,ha,hb,hk,hf,hq⟩
    exact ⟨hd,ha,hb,hk,(AtomicFormula.eval_graph 2 6 1 7 0 e hk).mpr hf,
      (query hd ha hb hk hf).mpr hq⟩

theorem realize_atomicCertificate (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (isMem : Bool) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) (p : Conditions c) :
    (AtomicFormula.certificate isMem).Realize M (cons (label c p)
      (cons (a.encode (label c)) (cons (b.encode (label c)) (cons c (cons o (fun _ => c)))))) ↔
      Atomic isMem a b p := by
  have hp : label c p ∈ M := hM c hc _ (label_mem c p)
  let e := cons (label c p) (cons (a.encode (label c))
    (cons (b.encode (label c)) (cons c (cons o (fun _ => c)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hp
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hb
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hoM
    exact hc
  have matrix (d k f : ZFSet.{u}) (hd : d ∈ M) (hk : k ∈ M) (hf : f ∈ M) :
      (AtomicFormula.matrix isMem).Realize M (cons f (cons k (cons d e))) ↔
        Transitive d ∧ a.encode (label c) ∈ d ∧ b.encode (label c) ∈ d ∧
          k = ZFSet.prod d d ∧ Graph d c o f ∧ Atomic isMem a b p := by
    have he' : ∀ i, cons f (cons k (cons d e)) i ∈ M := by
      intro i
      rcases i with _ | i
      · exact hf
      rcases i with _ | i
      · exact hk
      rcases i with _ | i
      · exact hd
      exact he i
    exact (Formula.absolute _ M hM _ he').trans (eval_matrix isMem d k o f ho a b p _)
  change (∃ d ∈ M, ∃ k ∈ M, ∃ f ∈ M,
    (AtomicFormula.matrix isMem).Realize M (cons f (cons k (cons d e)))) ↔ _
  constructor
  · rintro ⟨d,hd,k,hk,f,hf,hm⟩
    exact ((matrix d k f hd hk hf).mp hm).2.2.2.2.2
  · intro h
    obtain ⟨d,hd,hdT,hdab⟩ := internal_transitive_container M hM hP hU hS hR hI
      (pair_mem M hM hP ha hb)
    have had : a.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inl rfl))
    have hbd : b.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inr rfl))
    have hk := product_mem M hM hP hU hPow hS hd hd
    obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
    exact ⟨d,hd,_,hk,f,hf,(matrix d _ f hd hk hf).mpr ⟨hdT,had,hbd,rfl,hfG,h⟩⟩

end TuringRigidity.AtomicForcing

end OAI

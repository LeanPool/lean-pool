/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenFactor.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenPartition

/-!
# Internal Cohen Factor
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenFactor
open TransitiveNameModel BoundedSetTheory CohenGroundPoset InternalCohenRestriction
  InternalCohenPartition
open InternalCohen (alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Project a set-coded condition onto a subset of its coordinates. -/
noncomputable def project (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A)) : Conditions (conditions B) :=
  equivShrink _ ⟨restrict B (label _ p),restrict_condition A B _ hBA (label_mem _ p)⟩

theorem label_project (A B : ZFSet.{0}) (hBA : B ⊆ A) (p : Conditions (conditions A)) :
    label _ (project A B hBA p) = restrict B (label _ p) := by simp [project,label]

/-- Combine conditions on a coordinate subset and its complement by taking their union. -/
noncomputable def combine (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions B)) (q : Conditions (conditions (A \ B))) :
    Conditions (conditions A) :=
  equivShrink _ ⟨label _ p ∪ label _ q,union_condition A B _ _ hBA (label_mem _ p) (label_mem _ q)⟩

theorem label_combine (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions B)) (q : Conditions (conditions (A \ B))) :
    label _ (combine A B hBA p q) = label _ p ∪ label _ q := by simp [combine,label]

/-- Factor the set-coded condition poset into the posets on a subset and its complement. -/
noncomputable def factorIso (A B : ZFSet.{0}) (hBA : B ⊆ A) :
    Conditions (conditions A) ≃o (Conditions (conditions B) × Conditions (conditions (A \ B))) where
  toFun p := (project A B hBA p,project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p)
  invFun p := combine A B hBA p.1 p.2
  left_inv p := by
    apply label_injective
    rw [label_combine,label_project,label_project,union_restrict A B _ (label_mem _ p)]
  right_inv p := by
    apply Prod.ext <;> apply label_injective
    · rw [label_project,label_combine,restrict_union_left A B _ _ (label_mem _ p.1) (label_mem _
      p.2)]
    · rw [label_project,label_combine,restrict_union_right A B _ _ (label_mem _ p.1) (label_mem _
      p.2)]
  map_rel_iff' := by
    intro p q
    change (label _ (project A B hBA q) ⊆ label _ (project A B hBA p) ∧
      label _ (project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) q) ⊆ label _ (project A (A
        \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p)) ↔ label _ q ⊆ label _ p
    rw [label_project,label_project,label_project,label_project]
    exact (subset_iff_restrict A B _ _ (label_mem _ q) (label_mem _ p)).symm

/-- The set-coded product of the two factors in the coordinate decomposition. -/
noncomputable def productCode (A B : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.prod (conditions B) (conditions (A \ B))

/-- Set-coded graph pairing each condition with its two coordinate restrictions. -/
noncomputable def factorGraph (A B : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (productCode A B)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions B, ∃ r ∈ conditions (A \ B),
      z = ZFSet.pair p (ZFSet.pair q r) ∧ q = restrict B p ∧ r = restrict (A \ B) p)

theorem factorGraph_pair (A B p q r : ZFSet.{0}) :
    ZFSet.pair p (ZFSet.pair q r) ∈ factorGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions B ∧ r ∈ conditions (A \ B) ∧
        q = restrict B p ∧ r = restrict (A \ B) p := by
  simp only [factorGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,r',hr,he,hs⟩
    obtain ⟨hpEq,hqrEq⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hqEq,hrEq⟩ := ZFSet.pair_inj.mp hqrEq
    subst p'; subst q'; subst r'
    exact ⟨hp,hq,hr,hs⟩
  · rintro ⟨hp,hq,hr,hs⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,ZFSet.pair_mem_prod.mpr ⟨hq,hr⟩⟩,
      p,hp,q,hq,r,hr,rfl,hs⟩

theorem factorGraph_is_iso_graph (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A))
    (q : Conditions (conditions B)) (r : Conditions (conditions (A \ B))) :
    ZFSet.pair (label _ p) (ZFSet.pair (label _ q) (label _ r)) ∈ factorGraph A B ↔
      factorIso A B hBA p = (q,r) := by
  rw [factorGraph_pair]
  simp only [label_mem,true_and]
  constructor
  · intro h
    apply Prod.ext <;> apply label_injective
    · exact (label_project A B hBA p).trans h.1.symm
    · exact (label_project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p).trans h.2.symm
  · intro h
    have hq := congrArg (fun t => label (conditions B) t.1) h
    have hr := congrArg (fun t => label (conditions (A \ B)) t.2) h
    exact ⟨hq.symm.trans (label_project A B hBA p),hr.symm.trans (label_project A (A \ B) (fun _ h
      => (ZFSet.mem_sdiff.mp h).1) p)⟩

theorem factor_internal (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) :
    conditions B ∈ M ∧ conditions (A \ B) ∈ M ∧
      InternalCollapse.orderSet (conditions B) ∈ M ∧
      InternalCollapse.orderSet (conditions (A \ B)) ∈ M ∧ factorGraph A B ∈ M := by
  have hD := complement_mem M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  have hcD := conditions_mem M (A \ B) hM hT hD
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hcB hcD
  refine ⟨hcB,hcD,InternalCollapse.orderSet_mem M hM hT hcB,
    InternalCollapse.orderSet_mem M hM hT hcD,?_⟩
  let e := cons (conditions A) (cons (conditions B) (cons (conditions (A \ B))
    (cons (productCode A B) (cons B (cons (A \ B) (fun _ => alphabet))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|i
    · exact hcA
    · exact hcB
    · exact hcD
    · exact hprod
    · exact hB
    · exact hD
    · exact InternalCohen.alphabet_mem M hM hT
  let φ : Formula := .existsMem 1 (.existsMem 3 (.existsMem 5
    (.existsMem 7 (.conj (.orderedPair 0 2 1) (.conj (.orderedPair 4 3 0)
      (.conj (restrictionFormula 9 11 3 2) (restrictionFormula 10 11 3 1)))))))
  have hs₁ (z p q r t : ZFSet.{0}) := restrictionFormula_spec 9 11 3 2
    (cons t (cons r (cons q (cons p (cons z e))))) rfl
  have hs₂ (z p q r t : ZFSet.{0}) := restrictionFormula_spec 10 11 3 1
    (cons t (cons r (cons q (cons p (cons z e))))) rfl
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      ∃ p ∈ conditions A, ∃ q ∈ conditions B, ∃ r ∈ conditions (A \ B),
        z = ZFSet.pair p (ZFSet.pair q r) ∧ q = restrict B p ∧ r = restrict (A \ B) p := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,hs₁,hs₂,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨p,hp,q,hq,r,hr,t,_,ht,hz,hs⟩
      exact ⟨p,hp,q,hq,r,hr,ht ▸ hz,hs⟩
    · rintro ⟨p,hp,q,hq,r,hr,hz,hs⟩
      exact ⟨p,hp,q,hq,r,hr,ZFSet.pair q r,ZFSet.pair_mem_prod.mpr ⟨hq,hr⟩,rfl,hz,hs⟩
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hprod)
  simpa only [factorGraph,hφ,productCode] using hh

end TuringRigidity.InternalCohenFactor

end OAI

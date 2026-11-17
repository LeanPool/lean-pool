/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenPartitionBridge.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFactor
public import LeanPool.TuringConeRigidity.CohenForcing.TaggedProductGeneric

/-!
# Cohen Partition Bridge
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenPartitionBridge
open TransitiveNameModel BoundedSetTheory CohenGroundPoset InternalCohenFactor
open TaggedProductConditions CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def bridge (a b T f g : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod a b).sep (fun z => ∃ x ∈ a, ∃ y ∈ b,
    z = ZFSet.pair x y ∧ ∃ t ∈ T, ZFSet.pair t x ∈ f ∧ ZFSet.pair y t ∈ g)

theorem pair_bridge (a b T f g x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ bridge a b T f g ↔
      x ∈ a ∧ y ∈ b ∧ ∃ t ∈ T, ZFSet.pair t x ∈ f ∧ ZFSet.pair y t ∈ g := by
  constructor
  · intro h
    obtain ⟨_,x',hx,y',hy,he,ht⟩ := ZFSet.mem_sep.mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,ht⟩
  · rintro ⟨hx,hy,ht⟩
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,ht⟩

theorem bridge_mem (M a b T f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hTm : T ∈ M) (hf : f ∈ M) (hg : g ∈ M) :
    bridge a b T f g ∈ M := by
  let e := cons a (cons b (cons T (cons f (fun _ => g))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | _ | _ | _ | i
    · exact ha
    · exact hb
    · exact hTm
    · exact hf
    · exact hg
  simpa only
    [bridge,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.conj (.pairMem 0 2 7) (.pairMem 1 0 8)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb)

theorem internal_union_iso (M A B c f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A) (hc : c ∈ M) (hf : f ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions B, ∃ s ∈ conditions (A \ B), z = code p s)
    (hfs : ∀ p ∈ conditions B, ∀ s ∈ conditions (A \ B), ∀ z,
      ZFSet.pair (ZFSet.pair p s) z ∈ f ↔ z = code p s) :
    let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B
      hBA).symm
    ∃ g ∈ M, ∀ p q, ZFSet.pair (label c p) (label (conditions A) q) ∈ g ↔ q = e p := by
  have hfac := factor_internal M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hfac.1 hfac.2.1
  let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B
    hBA).symm
  refine ⟨bridge c (conditions A) (productCode A B) f (factorGraph A B),
    bridge_mem M _ _ _ _ _ hM hT hc hcA hprod hf hfac.2.2.2.2,?_⟩
  intro p q
  obtain ⟨⟨r,s⟩,rfl⟩ := (productIso (conditions B) (conditions (A \ B)) c hcs).surjective p
  have heval : e (productIso (conditions B) (conditions (A \ B)) c hcs (r,s)) =
      (factorIso A B hBA).symm (r,s) := by
    change (factorIso A B hBA).symm
      ((productIso (conditions B) (conditions (A \ B)) c hcs).symm
        ((productIso (conditions B) (conditions (A \ B)) c hcs) (r,s))) = _
    rw [OrderIso.symm_apply_apply]
  rw [pair_bridge]
  simp only [label_mem,true_and]
  change (∃ t ∈ productCode A B,
    ZFSet.pair t (label c (productMap _ _ c hcs (r,s))) ∈ f ∧
      ZFSet.pair (label _ q) t ∈ factorGraph A B) ↔ q = e ((productIso _ _ c hcs) (r,s))
  rw [label_productMap,heval]
  constructor
  · rintro ⟨t,ht,htf,htg⟩
    obtain ⟨u,hu,v,hv,rfl⟩ := ZFSet.mem_prod.mp ht
    obtain ⟨u,rfl⟩ := label_surjective (conditions B) hu
    obtain ⟨v,rfl⟩ := label_surjective (conditions (A \ B)) hv
    obtain ⟨hu,hv⟩ := (code_injective _ _ _ _).mp ((hfs _ (label_mem _ u) _ (label_mem _ v) _).mp
      htf)
    have hur : u = r := label_injective _ hu.symm
    have hvs : v = s := label_injective _ hv.symm
    subst u; subst v
    have hq := (factorGraph_is_iso_graph A B hBA q r s).mp htg
    simpa only [OrderIso.symm_apply_apply] using congrArg (factorIso A B hBA).symm hq
  · intro hq
    refine ⟨ZFSet.pair (label _ r) (label _ s),ZFSet.pair_mem_prod.mpr ⟨label_mem _ r,label_mem _
      s⟩,
      (hfs _ (label_mem _ r) _ (label_mem _ s) _).mpr rfl,?_⟩
    apply (factorGraph_is_iso_graph A B hBA q r s).mpr
    rw [hq,OrderIso.apply_symm_apply]

end TuringRigidity.CohenPartitionBridge

end OAI

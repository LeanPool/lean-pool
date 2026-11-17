/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenTailTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenTailHomogeneity
public import LeanPool.TuringConeRigidity.SetModels.InternalHomogeneousTruth

/-!
# Internal Cohen Tail Truth
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenTailHomogeneity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem weak_of_internal_tail_symmetry (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions (conditions A)))
    (he : ∀ i, (e i).encode (label (conditions A)) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (p q : Conditions (conditions A)) (hp : Forces e φ p)
    (hpq : restrict B (label _ p) ⊆ restrict B (label _ q)) :
    Forces e (.neg (.neg φ)) q := by
  have hc := conditions_mem M A hM hT hA
  have truthAt (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
      (ψ : BoundedSetTheory.Formula) := internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair _)
    G hG ψ e he
  intro u hu hn
  have hpu : restrict B (label _ p) ⊆ restrict B (label _ u) :=
    fun z hz => restrict_mono B _ _ hu (hpq hz)
  obtain ⟨w,hw,a,ha,hfix,r,hrp,hru⟩ :=
    internally_tail_homogeneous M A B hM hT hA hB hBA p u hpu
  obtain ⟨G,hr,hG⟩ := ArithmeticTree.countable_ground_generic M hct ⟨conditions A,hc⟩ (a.symm r)
  have hpG : p ∈ G.carrier := G.upper (by simpa using a.symm.monotone hrp) hr
  have hval := (truthAt G hG φ).mpr ⟨p,hpG,hp⟩
  let H := AutomorphismName.mapFilter a G
  have hH : GroundGeneric M H :=
    InternalOrderIsoTransport.map_ground_generic M _ _ w hM hT hc hc hw a ha G hG
  have hrH : r ∈ H.carrier := hr
  have huH : u ∈ H.carrier := H.upper hru hrH
  have hnot := (truthAt H hH (.neg φ)).mpr ⟨u,huH,hn⟩
  exact hnot ((hinv w hw a ha hfix G hG).mpr hval)

theorem cone_truth_of_internal_tail_symmetry (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions (conditions A)))
    (he : ∀ i, (e i).encode (label (conditions A)) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (p : Conditions (conditions A)) (hp : Forces e φ p)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
    (hcone : ∃ q ∈ G.carrier, restrict B (label _ p) ⊆ restrict B (label _ q)) :
    φ.Eval (fun i => (e i).val G.carrier) := by
  classical
  obtain ⟨q,hq,hpq⟩ := hcone
  have hw := weak_of_internal_tail_symmetry M A B hM hT hct hA hB hBA φ e he hinv p q hp hpq
  have hc := conditions_mem M A hM hT hA
  have hv := (internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair _)
    G hG (.neg (.neg φ)) e he).mpr ⟨q,hq,hw⟩
  exact not_not.mp hv

end TuringRigidity.BoundedForcing

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalHomogeneousTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenHomogeneity
public import LeanPool.TuringConeRigidity.SetModels.InternalOrderIsoTransport
public import LeanPool.TuringConeRigidity.SetModels.InternalBoundedTruth
public import LeanPool.TuringConeRigidity.Representation.SourceTGenericExistence

/-!
# Internal Homogeneous Truth
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem top_weak_of_internal_symmetry (M c : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M)
    (hct : (M : Set ZFSet.{0}).Countable) (hc : c ∈ M)
    (hom : ∀ p q : Conditions c, ∃ w ∈ M, ∃ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) ∧
      ∃ r, r ≤ a p ∧ r ≤ q)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (p : Conditions c) (hp : Forces e φ p) : Forces e (.neg (.neg φ)) ⊤ := by
  have truthAt (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
      (ψ : BoundedSetTheory.Formula) := internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair c)
    G hG ψ e he
  intro q _ hn
  obtain ⟨w,hw,a,ha,r,hrp,hrq⟩ := hom p q
  obtain ⟨G,hr,hG⟩ := ArithmeticTree.countable_ground_generic M hct ⟨c,hc⟩ (a.symm r)
  have hpG : p ∈ G.carrier :=
    G.upper (by simpa using a.symm.monotone hrp) hr
  have hval := (truthAt G hG φ).mpr ⟨p,hpG,hp⟩
  let H := AutomorphismName.mapFilter a G
  have hH : GroundGeneric M H :=
    InternalOrderIsoTransport.map_ground_generic M c c w hM hT hc hc hw a ha G hG
  have hrH : r ∈ H.carrier := hr
  have hqH : q ∈ H.carrier := H.upper hrq hrH
  have hnot := (truthAt H hH (.neg φ)).mpr ⟨q,hqH,hn⟩
  exact hnot ((hinv w hw a ha G hG).mpr hval)

theorem all_generics_of_internal_symmetry (M c : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M)
    (hct : (M : Set ZFSet.{0}).Countable) (hc : c ∈ M)
    (hom : ∀ p q : Conditions c, ∃ w ∈ M, ∃ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) ∧
      ∃ r, r ≤ a p ∧ r ≤ q)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (G₀ : GenericFilter (Conditions c)) (hG₀ : GroundGeneric M G₀)
    (hφ : φ.Eval (fun i => (e i).val G₀.carrier)) :
    Forces e (.neg (.neg φ)) ⊤ ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        φ.Eval (fun i => (e i).val G.carrier) := by
  classical
  have truthAt (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
      (ψ : BoundedSetTheory.Formula) := internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair c)
    G hG ψ e he
  obtain ⟨p,_,hp⟩ := (truthAt G₀ hG₀ φ).mp hφ
  have ht := top_weak_of_internal_symmetry M c hM hT hct hc hom φ e he hinv p hp
  refine ⟨ht,?_⟩
  intro G hG
  obtain ⟨q,hq⟩ := G.nonempty
  have hv := (truthAt G hG (.neg (.neg φ))).mpr ⟨⊤,G.upper le_top hq,ht⟩
  exact not_not.mp hv

end TuringRigidity.BoundedForcing

end OAI

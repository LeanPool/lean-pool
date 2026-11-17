/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenGroundGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset
public import LeanPool.TuringConeRigidity.Representation.CountableGroundGeneric
public import LeanPool.TuringConeRigidity.Representation.AutomorphismName

/-!
# Cohen Ground Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenGroundGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AutomorphismName
open CohenSymmetry CohenConditionCode CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def codeSet (A : ZFSet.{0}) (E : Set (Condition (Conditions A))) : ZFSet.{0} :=
  ZFSet.range (fun p : E => graph A p.val)

theorem graph_mem_codeSet (A : ZFSet.{0}) (E : Set (Condition (Conditions A)))
    (p : Condition (Conditions A)) : graph A p ∈ codeSet A E ↔ p ∈ E := by
  rw [codeSet,ZFSet.mem_range]
  exact ⟨fun ⟨q,hq⟩ => graph_injective A hq ▸ q.property,fun hp => ⟨⟨p,hp⟩,rfl⟩⟩

theorem groundGeneric_iff (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (G : GenericFilter (Condition (Conditions A))) :
    AtomicForcing.GroundGeneric M (mapFilter (conditionEquiv A) G) ↔
      ∀ E : Set (Condition (Conditions A)), codeSet A E ∈ M → Dense E →
        ∃ p ∈ G.carrier, p ∈ E := by
  constructor
  · intro h E hE hd
    have hd' : Dense {q : Conditions (conditions A) | label _ q ∈ codeSet A E} := by
      intro q
      obtain ⟨p,hp,hpE⟩ := hd ((conditionEquiv A).symm q)
      refine ⟨conditionEquiv A p,?_,?_⟩
      · simpa using (conditionEquiv A).monotone hp
      · change label _ (encode A p) ∈ codeSet A E
        rw [label_encode,graph_mem_codeSet]
        exact hpE
    obtain ⟨q,hq,hqE⟩ := h (codeSet A E) hE hd'
    refine ⟨(conditionEquiv A).symm q,hq,?_⟩
    apply (graph_mem_codeSet A E _).mp
    have he : graph A ((conditionEquiv A).symm q) = label _ q := by
      rw [←label_encode]
      exact congrArg (label _) ((conditionEquiv A).apply_symm_apply q)
    rwa [he]
  · intro h D hD hd
    let E : Set (Condition (Conditions A)) := {p | graph A p ∈ D}
    have hEq : codeSet A E = (conditions A).sep (fun z => z ∈ D) := by
      apply ZFSet.ext; intro z
      rw [ZFSet.mem_sep,codeSet,ZFSet.mem_range]
      constructor
      · rintro ⟨p,rfl⟩
        exact ⟨(mem_conditions A _).mpr (graph_isCondition A p.val),p.property⟩
      · rintro ⟨hc,hz⟩
        obtain ⟨p,rfl⟩ := (isCondition_iff_graph A z).mp ((mem_conditions A z).mp hc)
        exact ⟨⟨p,hz⟩,rfl⟩
    have hEM : codeSet A E ∈ M := by
      rw [hEq]
      exact sep_mem M hM hT.separation.finitePrefix.bounded (.member 0 1)
        (fun _ => D) (fun _ => hD) (conditions_mem M A hM hT hA)
    have hED : Dense E := by
      intro p
      obtain ⟨q,hq,hqD⟩ := hd (conditionEquiv A p)
      refine ⟨(conditionEquiv A).symm q,?_,?_⟩
      · simpa using (conditionEquiv A).symm.monotone hq
      · change graph A ((conditionEquiv A).symm q) ∈ D
        rw [←label_encode]
        have he := congrArg (label _) ((conditionEquiv A).apply_symm_apply q)
        exact he.symm ▸ hqD
    obtain ⟨p,hp,hpE⟩ := h E hEM hED
    change graph A p ∈ D at hpE
    exact ⟨conditionEquiv A p,by simpa [mapFilter] using hp,
      by simpa only [show conditionEquiv A p = encode A p from rfl,label_encode] using hpE⟩

theorem encode_name (A : ZFSet.{0}) (τ : Name (Condition (Conditions A))) :
    Name.encode (label (conditions A)) (τ.rename (conditionEquiv A)) =
      Name.encode (graph A) τ := by
  induction τ with
  | mk ι child tag ih =>
    simp only [Name.rename,Name.encode,Function.comp_apply,ih]
    congr 1; funext i
    rw [show conditionEquiv A (tag i) = encode A (tag i) from rfl,label_encode]

theorem val_name (A : ZFSet.{0}) (τ : Name (Condition (Conditions A)))
    (G : GenericFilter (Condition (Conditions A))) :
    (τ.rename (conditionEquiv A)).val (mapFilter (conditionEquiv A) G).carrier =
      τ.val G.carrier :=
  Name.val_rename _ _ _ (fun _ => by simp [mapFilter]) τ

theorem empty_mem_conditions (A : ZFSet.{0}) : (∅ : ZFSet.{0}) ∈ conditions A := by
  have he : graph A (⊤ : Condition (Conditions A)) = ∅ := by
    apply ZFSet.ext; intro z
    rw [mem_graph]
    constructor
    · rintro ⟨i,b,hi,_⟩; cases hi
    · intro hz; exact False.elim (ZFSet.notMem_empty _ hz)
  rw [←he]
  exact (mem_conditions A _).mpr (graph_isCondition A _)

theorem exists_extension (M A : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M)
    (p : Condition (Conditions A)) :
    ∃ G : GenericFilter (Conditions (conditions A)), encode A p ∈ G.carrier ∧
      AtomicForcing.GroundGeneric M G ∧
      M ⊆ genericExtensionSet M (conditions A) G.carrier ∧
      Transitive (genericExtensionSet M (conditions A) G.carrier) ∧
      SourceT (genericExtensionSet M (conditions A) G.carrier) ∧
      AtomicForcing.Generic (names M (conditions A)) G := by
  let _ := InternalCollapse.top (conditions A) (empty_mem_conditions A)
  have hc := conditions_mem M A hM hT hA
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  obtain ⟨G,hp,hG⟩ := AtomicForcing.countable_ground_generic M ⟨A,hA⟩ (encode A p)
  have ht : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  refine ⟨G,hp,hG,?_,genericExtensionSet_transitive M _ hM G.carrier,?_,?_⟩
  · exact ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  · exact extension_sourceT M hM hT hc ho (InternalCollapse.orderSet_pair _) G hG ht
  · exact AtomicForcing.groundGeneric_atomic M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
      (InternalCollapse.orderSet_pair _) G hG

end TuringRigidity.CohenGroundGeneric

end OAI

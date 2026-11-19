/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenSupportedValue.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenProjectedGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.CohenNiceNameConstruction

/-!
# Internal Cohen Supported Value
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenSupportedValue
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset CohenInternalSupport InternalCohenRestriction InternalCohenPartition
open InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem supported_condition (A B p : ZFSet.{0}) (hBA : B ⊆ A)
    (hp : p ∈ conditions A) (hs : supportSet A p ⊆ B) :
    p ∈ conditions B ∧ restrict B p = p := by
  have he : restrict B p = p := by
    apply ZFSet.ext; intro z
    rw [mem_restrict]
    refine ⟨And.left,fun hz => ⟨hz,?_⟩⟩
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (condition_subset A p hp hz)
    exact ZFSet.pair_mem_prod.mpr ⟨hs (ZFSet.mem_sep.mpr ⟨hx,b,hb,hz⟩),hb⟩
  exact ⟨he ▸ restrict_condition A B p hBA hp,he⟩

theorem supported_hit_iff (A B E : ZFSet.{0}) (hBA : B ⊆ A) (hE : E ⊆ conditions B)
    (G : GenericFilter (Conditions (conditions A))) :
    (∃ p ∈ G.carrier, label _ p ∈ E) ↔
      ∃ q ∈ (projected A B hBA G).carrier, label _ q ∈ E := by
  constructor
  · rintro ⟨p,hp,hpE⟩
    refine ⟨project A B hBA p,projected_contains A B hBA G hp,?_⟩
    rw [label_project,restrict_eq_self B _ (hE hpE)]; exact hpE
  · rintro ⟨q,hq,hqE⟩
    obtain ⟨p,hp,hpq⟩ := (mem_projected A B hBA G q).mp hq
    have hqA := condition_mono A B (label _ q) hBA (label_mem _ q)
    obtain ⟨r,hr⟩ := label_surjective (conditions A) hqA
    refine ⟨r,G.upper (p := p) ?_ hp,?_⟩
    · change label _ r ⊆ label _ p
      rw [hr,←hpq,label_project]
      exact fun _ h => (ZFSet.mem_sep.mp h).1
    · rwa [hr]

theorem nice_value_projected (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ⊆ conditions B)
    (G : GenericFilter (Conditions (conditions A))) :
    (InternalNiceName.nice E : Name (Conditions (conditions B))).val (projected A B hBA G).carrier =
      (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier := by
  obtain ⟨p,hp⟩ := G.nonempty
  have htA : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  let H := projected A B hBA G
  obtain ⟨q,hq⟩ := H.nonempty
  have htB : (⊤ : Conditions (conditions B)) ∈ H.carrier := H.upper le_top hq
  apply ZFSet.ext; intro x
  rw [InternalNiceName.mem_val_nice E _ htB,InternalNiceName.mem_val_nice E _ htA]
  constructor
  · rintro ⟨n,q,hq,hqE,hx⟩
    obtain ⟨p,hp,hpE⟩ := (supported_hit_iff A B (E n) hBA (hE n) G).mpr ⟨q,hq,hqE⟩
    exact ⟨n,p,hp,hpE,hx⟩
  · rintro ⟨n,p,hp,hpE,hx⟩
    obtain ⟨q,hq,hqE⟩ := (supported_hit_iff A B (E n) hBA (hE n) G).mp ⟨p,hp,hpE⟩
    exact ⟨n,q,hq,hqE,hx⟩

theorem nice_value_mem_projected (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hB : B ∈ M) (hBA : B ⊆ A) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ conditions B) (hgraph : orbitGraph E ∈ M)
    (G : GenericFilter (Conditions (conditions A))) :
    (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier ∈
      genericExtensionSet M (conditions B) (projected A B hBA G).carrier := by
  rw [←nice_value_projected A B hBA E (fun n => (hE n).2) G]
  have hn := InternalNiceName.nice_internal M hM hT (conditions_mem M B hM hT hB) E hE hgraph
  change _ ∈ (genericExtensionSet M (conditions B) (projected A B hBA G).carrier : Set ZFSet.{0})
  rw [genericExtensionSet_coe]
  exact ⟨InternalNiceName.nice E,hn,rfl⟩

end TuringRigidity.InternalCohenSupportedValue

end OAI

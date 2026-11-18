/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenColumnReading.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenSupportedValue
public import LeanPool.TuringConeRigidity.SetModels.InternalColumnProjection

/-!
# Internal Cohen Column Reading
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenColumnReading
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset CohenInternalSupport InternalCohenRestriction InternalCohenPartition
open InternalCohenFactor InternalCohenProjectedGeneric InternalCohenSupportedValue
open InternalColumnProjection
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem internal_column_reading (M K : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K,
      (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
        (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
        (InternalNiceName.nice E : Name (Conditions (conditions (ZFSet.prod C ZFSet.omega)))).encode
          (label (conditions (ZFSet.prod C ZFSet.omega))) ∈ M ∧
        ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
        ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
          AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
          AtomicForcing.GroundGeneric M (projected _ _ hBA G) ∧
          (InternalNiceName.nice E : Name (Conditions (conditions (ZFSet.prod C ZFSet.omega)))).val
            (projected _ _ hBA G).carrier = τ.val G.carrier ∧
          τ.val G.carrier ∈ genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega))
            (projected _ _ hBA G).carrier ∧
          ∀ p ∈ G.carrier, project _ _ hBA p ∈ (projected _ _ hBA G).carrier := by
  let A := ZFSet.prod K ZFSet.omega
  have hω := sourceT_omega_mem M hM hT
  have hA : A ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  obtain ⟨E,hgraph,hE,_,⟨S,hSM,hSA,hS,hct⟩,hval⟩ :=
    CohenNiceNameConstruction.internal_nice_name M A hM hT hA τ hτ
  let C := columns K S
  obtain ⟨hCM,hCK,hSC,hCct⟩ := columns_counted M K S hM hT hK hSM hSA hct
  let B := ZFSet.prod C ZFSet.omega
  have hBM : B ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hCM hω
  have hBA : B ⊆ A := by
    intro z hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨hCK hx,hn⟩
  have hEcB (n : ℕ) : E n ∈ M ∧ E n ⊆ conditions B := by
    refine ⟨(hE n).1,?_⟩
    intro p hp
    have hpA : p ∈ conditions A := (ZFSet.mem_sep.mp ((hE n).2.1 hp)).1
    apply (supported_condition A B p hBA hpA ?_).1
    intro x hx
    exact hSC ((hS x).mpr ⟨n,p,hp,hx⟩)
  refine ⟨C,hCM,hCK,hCct,E,hgraph,hEcB,
    InternalNiceName.nice_internal M hM hT (conditions_mem M B hM hT hBM) E hEcB hgraph,
    hBA,?_⟩
  intro G hG hreal
  have he := hval G hG hreal
  refine ⟨projected_groundGeneric M A B hM hT hA hBM hBA G hG,
    (nice_value_projected A B hBA E (fun n => (hEcB n).2) G).trans he,?_,
    fun p hp => projected_contains A B hBA G hp⟩
  rw [←he]
  exact nice_value_mem_projected M A B hM hT hBM hBA E hEcB hgraph G

end TuringRigidity.InternalCohenColumnReading

end OAI

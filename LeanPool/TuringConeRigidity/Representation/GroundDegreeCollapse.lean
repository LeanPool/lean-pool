/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GroundDegreeCollapse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GroundDegreePresentation
public import LeanPool.TuringConeRigidity.Representation.GlobalJumpRestriction
public import LeanPool.TuringConeRigidity.Computability.ArithmeticPersistenceDegreeModel

/-!
# Ground Degree Collapse
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel PersistentRestrictions PersistentPresentation PersistentCountability
  OracleJump
open CountableForcing
universe u
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem ground_degree_persistent_collapse (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (π : Degree ≃o Degree)
    (X Y : Oracle) (hX : X ∈ modelReals M) (hY : Y ∈ modelReals M)
    (hx : degree X = π (degree (jump FixedArithmetic.zero)))
    (hy : degree Y = π.symm (degree (jump FixedArithmetic.zero))) :
    ∃ c ∈ M, ∃ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G ∧
      let N := genericExtensionSet M c G.carrier
      M ⊆ N ∧ Transitive N ∧ SourceT N ∧
      ∃ I : CountableIdeal, ∃ H ∈ modelReals N, ∃ hH : Presented I H,
        (∀ a : Degree, a ∈ I.carrier ↔ ∃ A ∈ modelReals M, degree A = a) ∧
        ∃ ρ : I ≃o I, RestrictsTo π I ρ ∧ Persistent I ρ ∧
          graphOracle hH ρ ∈ modelReals N ∧
          ∃ S ∈ N, degreeUniverse S ∈ N ∧ degreeOrder S ∈ N ∧
            presentationGraph S H (graphOracle hH ρ) ∈ N ∧
            (LevySigma.persistent 0 1 2 3 4).Realize N
              (modelDegreeEnv S (presentationSet S H) (presentationGraph S H (graphOracle hH ρ)))
                := by
  classical
  obtain ⟨S,hSM,hS,hSd⟩ := internal_real_power M hM hT
  have hd : ∀ x ∈ S, ∃ A : Oracle, realCode A = x := by
    intro x hx; obtain ⟨A,_,hA⟩ := hSd x hx; exact ⟨A,hA⟩
  have hU := internal_degreeUniverse M hM hT S hSM hd
  have hne : ∃ D, D ∈ degreeUniverse S :=
    ⟨degreeCode S FixedArithmetic.zero,(mem_degreeUniverse S _).mpr
      ⟨FixedArithmetic.zero,(hS _).mpr (sourceT_zero_real M hM hT),rfl⟩⟩
  obtain ⟨c,hcM,_,_,G,hG,hMN,hN,hTN,hcount⟩ :=
    InternalCollapse.exists_internal_counting_extension M hM hT hU hne
  let N := genericExtensionSet M c G.carrier
  obtain ⟨I,H,hHN,hH,_,_,hI,hz,hjump⟩ :=
    ground_degree_presentation M N hM hN hT hTN S hS hd (hMN hU) hcount
  have himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ I.carrier :=
    I.join_mem ((hI _).mpr ⟨X,hX,hx⟩) ((hI _).mpr ⟨Y,hY,hy⟩)
  obtain ⟨ρ,hρ,hp⟩ := PersistentLocality.global_jump_restriction π I hjump himages
  have hRN := sourceT_persistent_graph_real N hN hTN hH hHN ρ hp hz
  obtain ⟨T,hTNmem,hTr,hTd⟩ := internal_real_power N hN hTN
  have htd : ∀ x ∈ T, ∃ A : Oracle, realCode A = x := by
    intro x hx; obtain ⟨A,_,hA⟩ := hTd x hx; exact ⟨A,hA⟩
  have hcol : ∀ n, realCode (EncodedForcing.columns H n) ∈ T :=
    fun n => (hTr _).mpr (sourceT_real_column N hN hTN hHN n)
  have hr : ∀ v, graphOracle hH ρ v = true ↔ Graph ρ hH v := by intro v; simp [graphOracle]
  have hg := sourceT_arbitrary_persistent_graph N hN hTN T hTNmem hTr htd hH hHN ρ hp hz
    (presentationGraph T H (graphOracle hH ρ)) (fun _ h => (ZFSet.mem_sep.mp h).1)
    (presentationGraph_actual T hH hcol ρ hr)
  exact ⟨c,hcM,G,hG,hMN,hN,hTN,I,H,hHN,hH,hI,ρ,hρ,hp,hRN,T,hTNmem,
    internal_degreeUniverse N hN hTN T hTNmem htd,internal_degreeOrder N hN hTN T hTNmem htd,hg⟩

end TuringRigidity.BoundedSetTheory

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanFilterReconstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanEvaluationWitness
public import LeanPool.TuringConeRigidity.Representation.SameRealBooleanFilter

/-!
# Boolean Filter Reconstruction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanFilterReconstruction
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalBooleanBits InternalBooleanGeneric InternalGeneratedAlgebra InternalProjectedGeneric
open BooleanExpressionCertificate BooleanExpressionTruth
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

theorem witness_bound (M c B Q S A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hSB : S ⊆ B)
    (hA : A ⊆ generated c B Q S) :
    ∃ W ∈ M, ∀ U ∈ A, ∃ K ∈ W, Witness c B Q S K U := by
  have he := parameters_mem M c B Q S hM hT hc hBM hQM hSM
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  obtain ⟨W,hWM,hW⟩ := hColl (.bounded witnessBody) (BooleanExpressionCertificate.parameters c B Q
    S) he A hAM (by
    intro U hU
    obtain ⟨K,hKM,hK⟩ := generated_certificate M c B Q S U hM hT hc hBM hQM hSM hB hQ hSB (hA hU)
    exact ⟨K,hKM,(witnessBody_realize M c B Q S K U hM he hKM (hM A hAM U hU)).mpr hK⟩)
  refine ⟨W,hWM,?_⟩
  intro U hU
  obtain ⟨K,hKW,hK⟩ := hW U hU
  exact ⟨K,hKW,(witnessBody_realize M c B Q S K U hM he (hM W hWM K hKW) (hM A hAM U hU)).mp hK⟩

theorem hit_values_mem (M N c B Q S A W R : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N)
    (hc : c ∈ M) (hcN : c ∈ N) (hBN : B ∈ N) (hQN : Q ∈ N) (hSN : S ∈ N)
    (hAN : A ∈ N) (hWN : W ∈ N) (hRN : R ∈ N)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B)
    (hbound : ∀ U ∈ A, ∃ K ∈ W, Witness c B Q S K U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hseed : ∀ U ∈ S, U ∈ R ↔ Hit G U) : A.sep (Hit G) ∈ N := by
  let e := evaluationParameters W c B Q S R
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|_|_|_|_|_|i
    · exact hWN
    · exact hcN
    · exact hBN
    · exact hQN
    · exact hSN
    · exact hRN
    all_goals exact hN _ (sourceT_omega_mem N hN hTN) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have spec (U : ZFSet.{0}) (hUA : U ∈ A) :
      (∃ Y ∈ N, evaluationBody.Realize N (cons Y (cons U e))) ↔ Hit G U := by
    constructor
    · rintro ⟨Y,hYN,hbody⟩
      obtain ⟨K,_,hK,hy,g,_,hg,t,htK,hp,htY⟩ :=
        (evaluationBody_realize N W c B Q S R Y U hN he hYN (hN A hAN U hUA)).mp hbody
      have hv := (hy.agrees hK t htK).mp htY
      exact (certificate_value M c B Q S K g R hM hT hc hB hQ hg G hG hseed t U hp).mp hv
    · intro hhit
      obtain ⟨K,hKW,hK,g,hgK,hg,t,htK,hp⟩ := hbound U hUA
      have hKN := hN W hWN K hKW
      have hYN := valueSet_mem N K B R hN hTN hKN hK hBN hRN
      have hv := (certificate_value M c B Q S K g R hM hT hc hB hQ hg G hG hseed t U hp).mpr hhit
      refine ⟨valueSet K B R,hYN,
        (evaluationBody_realize N W c B Q S R _ U hN he hYN (hN A hAN U hUA)).mpr ?_⟩
      exact ⟨K,hKW,hK,valueSet_good K B R hK,g,hgK,hg,t,htK,hp,ZFSet.mem_sep.mpr ⟨htK,hv⟩⟩
  obtain ⟨a,ha,hspec⟩ := hTN.separation.finitePrefix (.existsSet (.bounded evaluationBody)) e he A
    hAN
  have eq : a = A.sep (Hit G) := by
    apply ZFSet.ext; intro U
    constructor
    · intro hU
      obtain ⟨hUA,hbody⟩ := (hspec U (hN a ha U hU)).mp hU
      exact ZFSet.mem_sep.mpr ⟨hUA,(spec U hUA).mp hbody⟩
    · intro hU
      obtain ⟨hUA,hhit⟩ := ZFSet.mem_sep.mp hU
      exact (hspec U (hN A hAN U hUA)).mpr ⟨hUA,(spec U hUA).mpr hhit⟩
  exact eq ▸ ha

theorem projected_filter_eq_hits (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      A.sep (Hit G) := by
  apply ZFSet.ext; intro U
  rw [mem_genericFilterSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨(ZFSet.mem_sep.mp (label_mem (positive A) q)).1,hq⟩
  · rintro ⟨hUA,p,hp,hpU⟩
    have hU0 : U ≠ ∅ := fun he => ZFSet.notMem_empty _ (he ▸ hpU)
    obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hUA,hU0⟩)
    refine ⟨q,?_,hq⟩
    change Hit G (label (positive A) q)
    rw [hq]
    exact ⟨p,hp,hpU⟩

theorem projected_filter_mem_from_real (M N c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier)
    (hX : (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier ∈ N) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ∈ N :=
      by
  have hSM := seeds_mem M c B hM hT hc hBM E hE hgraph
  obtain ⟨W,hWM,hbound⟩ := witness_bound M c B Q (seeds c B E) A hM hT hc hBM hQM hSM hAM hB hQ
    (fun _ h => (ZFSet.mem_sep.mp h).1) (fun _ h => hAe ▸ h)
  have hRN := seedTruth_mem N c B hN hTN (hMN hc) (hMN hBM) E
    (fun n => ⟨hMN (hE n).1,(hE n).2⟩) (hMN hgraph) _ hX
  rw [projected_filter_eq_hits M c B Q A hM hT hc hBM hAM hB hQ hA G]
  exact hit_values_mem M N c B Q (seeds c B E) A W _ hM hT hN hTN hc (hMN hc) (hMN hBM)
    (hMN hQM) (hMN hSM) (hMN hAM) (hMN hWM) hRN hB hQ hbound G hG
    (fun U hU => seedTruth_hit M c B hM hT hc E hE G hG hGt U hU)

theorem projected_extension_least_for_real (M N c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier)
    (hX : (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier ∈ N) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆ N := by
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  exact projected_filter_mem_from_real M N c B Q A hM hT hN hTN hMN hc hBM hQM hAM hB hQ hA
    E hE hgraph hAe G hG hGt hX

end TuringRigidity.BooleanFilterReconstruction

end OAI

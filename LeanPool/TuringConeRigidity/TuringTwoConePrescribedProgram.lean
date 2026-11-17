/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePrescribedProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePullbackDefinition
public import LeanPool.TuringConeRigidity.TuringTwoConeGenericTransfer
public import LeanPool.TuringConeRigidity.SetModels.NoNewOrdinals

/-!
# A prescribed joined-inverse program in a Cohen extension

Restrict the ORIGINAL global isomorphism to the extension's degree ideal.
Its constructible inverse relation therefore agrees with the original joined
inverse on all extension inputs. The relation-only compiler handles the new
real definition parameter without changing the old computational parameter.
The relative source equation then transfers column correctness.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePrescribedProgram

open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions TwoConePullbackProgram TwoConeProgramGlobalization
open RelativeConstructible RecursiveNames CountableForcing AtomicForcing CohenGroundPoset
open CohenColumnRealName InternalCountableOrdinals OracleJump GenericIdentity
open ConePersistence (Cone)
open ConePullbackProgram (Output)
open TwoConeLocality (forwardAnchor inverseAnchor jumpPoint)

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

/-- One fixed program, with an old parameter representing e(a'), works on
every sufficiently arithmetic-generic real of this Cohen extension. -/
theorem prescribed_program {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (M K : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (hpost : forwardAnchor e ∈ (modelIdeal M hM hT).carrier)
    (hpre : inverseAnchor e ∈ (modelIdeal M hM hT).carrier)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    ∃ (R : Oracle) (p : OracleCode), degree R = forwardAnchor e ∧
      ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
        ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) Y →
          RepresentsInverseAt e p (iterate R 5) Y := by
  let c := poset K
  let E := genericExtensionSet M c G.carrier
  have hc := (manyColumn_internal M K hM hT hK.2.1).1
  have ho := (manyColumn_internal M K hM hT hK.2.1).2
  have ht : (⊤ : Conditions c) ∈ G.carrier := G.upper le_top G.nonempty.choose_spec
  have hE := genericExtensionSet_transitive M c hM G.carrier
  have hTE := extension_sourceT M hM hT hc ho (InternalCollapse.orderSet_pair c) G hG ht
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  let I := modelIdeal M hM hT
  let J := modelIdeal E hE hTE
  have hIJ : I.carrier ⊆ J.carrier := by
    rintro d ⟨D, hD, rfl⟩
    refine ⟨D, ?_, rfl⟩
    change realCode D ∈ E
    exact hME hD
  obtain ⟨σ, hσ, hpσ, _⟩ := TwoConePrescribedModels.model_restriction_of_anchors
    e E hE hTE (hIJ hpost) (hIJ hpre)
  have haE : a ∈ J.carrier :=
    J.lower (Set.mem_Ici.mp (e.symm (jumpPoint b)).property) (hIJ hpre)
  have hbE : b ∈ J.carrier :=
    J.lower (Set.mem_Ici.mp (e (jumpPoint a)).property) (hIJ hpost)
  obtain ⟨R, hRM, hR⟩ := hpost
  change realCode R ∈ M at hRM
  have houtputs := model_outputs_of_restriction e E hE hTE σ hbE hσ R hR
  have hgraphE : pullbackGraph σ hbE ∈ E := relativeModel_subset E _
    (TwoConePullbackDefinition.graph_mem_relativeModel E hE hTE σ hpσ haE hbE)
  obtain ⟨δ, P, φ, hδ, hPE, _, hPL, hdef⟩ :=
    TwoConePullbackDefinition.graph_one_real_definition E hE hTE σ hpσ haE hbE
  have hδM := extension_ordinal_ground M c hM hT G.carrier δ hδ
  obtain ⟨f, hf, hfg⟩ := (mem_extensionSet M c G.carrier _).mp hgraphE
  obtain ⟨τ, hτ, hτv⟩ := (mem_extensionSet M c G.carrier (realCode P)).mp hPE
  have hreal : τ.val G.carrier ⊆ ZFSet.omega := by rw [hτv]; exact realCode_subset P
  have hXL : τ.val G.carrier ∈ level (groundReals E) δ := hτv.symm ▸ hPL
  have hdef' : f.val G.carrier = definedSubset (level (groundReals E) δ) φ
      (fun _ : Fin φ.bound => τ.val G.carrier) := by
    rw [hfg, hτv]
    exact hdef
  have houtputs' : ∀ A ∈ modelReals E, ∃ X : Oracle,
      Reduces X (iterate (join A R) 5) ∧ Output E (f.val G.carrier) A X := by
    rw [hfg]
    exact houtputs
  obtain ⟨i, hi⟩ := InternalCountableOrdinals.nonempty M K hK
  obtain ⟨hN, _, fX, _, _, GX, _, _, _, p, _, hsem, _⟩ :=
    ConeRealParameterProgram.program_from_one_real_definition M K i hM hT hK hi R hRM
      τ f hτ hf G hG hreal δ hδM φ hXL hdef' houtputs'
  rw [hτv] at hN hsem
  let N := RealGeneratedModel.hull M (realCode P)
  have hRN : R ∈ modelReals N := by
    change realCode R ∈ N
    exact hN.2.2.1 hRM
  have hRP : realCode (iterate R 5) ∈ N :=
    sourceT_real_iterate N hN.1 hN.2.1 hRN 5
  obtain ⟨B, hB⟩ := degree_surjective b
  have hBR : Reduces B R := by
    change degree B ≤ degree R
    rw [hB, hR]
    exact Set.mem_Ici.mp (e (jumpPoint a)).property
  have hBM : realCode B ∈ M := sourceT_real_lower M hM hT hRM hBR
  have hBN : realCode B ∈ N := hN.2.2.1 hBM
  have hsem' : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric N H →
      genericExtensionSet N (poset K) H.carrier = E →
      ∀ Y : Oracle, (realName K i).val H.carrier = realCode Y →
        RepresentsInverseAt e p (iterate R 5) Y := by
    intro H hH hEq Y hv
    have hy := hsem H hH hEq Y hv
    rw [hfg] at hy
    exact own_program_prescribed e σ hbE hσ E p (iterate R 5) Y hy
  have hrep := (TwoConeGenericTransfer.real_hull_prescribed_transfer e M K i hM hT hK hi
    G hG P B hPE hB hBN p (iterate R 5) hRP hsem').2
  exact ⟨R, p, hR, hrep⟩

end OAI.TuringRigidity.TwoConePrescribedProgram

/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeRealParameterProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeOracleProgram
public import LeanPool.TuringConeRigidity.Representation.OriginalRealUniformDefinition

/-!
# Absorb an extension-real parameter before selecting the program

A definition in one Cohen extension need not have a ground-real parameter.
The existing real-generated-model construction absorbs that real, produces a
uniform definition name over the enlarged model, and preserves the original
extension. Combining this with the relational program compiler needs no
native automorphism or cone-extension formula across the other filters.

The graph being defined must still be the intended inverse-join graph.
The final transfer from model-relative column inputs to all sufficiently
generic ambient inputs is not asserted in this file.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeRealParameterProgram

open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open CohenGroundPoset CohenColumnRealName InternalCountableOrdinals RelativeConstructible
open ElementaryModel ConePullbackProgram OracleJump GenericIdentity
open PersistentRestrictions SetDegreeDecoding ConePersistence

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

/-- Every input in a model has the bounded witness needed by the program
selection theorem when the relation is the inverse graph of an extension. -/
theorem model_extension_outputs (E : ZFSet.{0}) [Countable (Conditions E)]
    (hE : Transitive E) (hTE : SourceT E)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hIJ : I.carrier ⊆ (modelIdeal E hE hTE).carrier)
    (σ : modelIdeal E hE hTE ≃o Cone (modelIdeal E hE hTE) a)
    (he : ConePersistence.Extends hIJ ρ σ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hR : degree R = (ρ ⟨degree (jump FixedArithmetic.zero), hz⟩).val) :
    ∀ A ∈ modelReals E, ∃ X : Oracle,
      Reduces X (iterate (join A R) 5) ∧ Output E (pullbackGraph σ) A X := by
  intro A hA
  exact output_of_extension ρ σ hIJ he hz R hR E
    (ground_degreeUniverse_eq_idealSet E hE hTE) A ⟨A, hA, rfl⟩

/-- From an actual one-real definition and pointwise arithmetic bounds to
one fixed program. The real definition parameter may be new; the program's
oracle parameter R remains in the old model. -/
theorem program_from_one_real_definition (M K i : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (hi : i ∈ K)
    (R : Oracle) (hRM : realCode R ∈ M)
    (τ f : Name (Conditions (poset K)))
    (hτ : τ.encode (label (poset K)) ∈ M) (hf : f.encode (label (poset K)) ∈ M)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (hreal : τ.val G.carrier ⊆ ZFSet.omega)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (φ : SentenceForm)
    (hX : τ.val G.carrier ∈ level (groundReals (genericExtensionSet M (poset K) G.carrier)) δ)
    (hdef : f.val G.carrier = definedSubset
      (level (groundReals (genericExtensionSet M (poset K) G.carrier)) δ)
        φ (fun _ : Fin φ.bound => τ.val G.carrier))
    (houtputs : ∀ A ∈ modelReals (genericExtensionSet M (poset K) G.carrier),
      ∃ X : Oracle, Reduces X (iterate (join A R) 5) ∧
        Output (genericExtensionSet M (poset K) G.carrier) (f.val G.carrier) A X) :
    let c := poset K
    let E := genericExtensionSet M c G.carrier
    let N := RealGeneratedModel.hull M (τ.val G.carrier)
    RealGeneratedModel.Contains M (τ.val G.carrier) N ∧ (N : Set ZFSet.{0}).Countable ∧
      ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
        (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
          fX.val H.carrier = definedSubset
            (level (groundReals (genericExtensionSet N c H.carrier)) δ)
              φ (fun _ : Fin φ.bound => τ.val G.carrier)) ∧
        ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
          genericExtensionSet N c GX.carrier = E ∧ fX.val GX.carrier = f.val G.carrier ∧
          ∃ p : OracleCode,
            (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
              ∀ A : Oracle, (realName K i).val H.carrier = realCode A →
                OwnProgramAt (genericExtensionSet N c H.carrier) (fX.val H.carrier)
                  p (iterate R 5) A) ∧
            (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
              genericExtensionSet N c H.carrier = E →
              ∀ A : Oracle, (realName K i).val H.carrier = realCode A →
                OwnProgramAt E (f.val G.carrier) p (iterate R 5) A) ∧
            ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
              (∀ A, ShuffleRequirements.GenericFor D A → Total p (iterate R 5) A) ∧
              ContinuousOn (value p (iterate R 5)) {A | ShuffleRequirements.GenericFor D A} := by
  intro c E N
  obtain ⟨hN, fX, hfX, hall, GX, hGX, hExt, hval, _⟩ :=
    OriginalRealDefinitionTransport.original_uniform_definition M K hM hT hK
      τ f hτ hf G hG hreal δ hδ φ hX hdef
  change genericExtensionSet N c GX.carrier = E at hExt
  have hct : (M : Set ZFSet.{0}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro z hz; exact label_surjective M hz
  have hc : c ∈ N := hN.2.2.1 (manyColumn_internal M K hM hT hK.2.1).1
  have hNE : N ⊆ E := by
    rw [←hExt]
    exact ground_inclusion_set N c hN.1 hN.2.1.pairing hN.2.1.union hN.2.1.powerSet
      hN.2.1.separation.finitePrefix.bounded hN.2.1.replacement.finitePrefix hN.2.1.infinity
      hc GX.carrier (GX.upper le_top GX.nonempty.choose_spec)
  have hNct : (N : Set ZFSet.{0}).Countable := by
    have hEct : (E : Set ZFSet.{0}).Countable := by
      rw [genericExtensionSet_coe]
      exact genericExtension_countable M c hct G.carrier
    exact hEct.mono hNE
  let : Countable (N : Set ZFSet.{0}) := hNct.to_subtype
  let : Countable (Conditions N) := Function.Injective.countable
    (f := fun p : Conditions N => (⟨label N p, label_mem N p⟩ : (N : Set ZFSet.{0})))
    (fun x y he => label_injective N (congrArg (fun z : (N : Set ZFSet.{0}) => z.val) he))
  have hKN : K ∈ N := hN.2.2.1 hK.2.1
  obtain ⟨A, _, hA, _, _⟩ := projected_real_value N K i hN.1 hN.2.1 hKN hi GX hGX
  have hAE : A ∈ modelReals E := by
    rw [←hExt]
    exact (mem_extensionSet N c GX.carrier _).mpr
      ⟨realName K i, realName_internal N K i hN.1 hN.2.1 hKN hi, hA⟩
  obtain ⟨X, hred, hout⟩ := houtputs A hAE
  have hw : ∃ A X : Oracle, (realName K i).val GX.carrier = realCode A ∧
      Reduces X (iterate (join A R) 5) ∧
      Output (genericExtensionSet N c GX.carrier) (fX.val GX.carrier) A X := by
    refine ⟨A, X, hA, hred, ?_⟩
    rw [hExt, hval]
    exact hout
  obtain ⟨p, hown, hcont⟩ := ConeOracleProgram.column_oracle_program N K i hN.1 hN.2.1 hKN hi
    δ (τ.val G.carrier) φ R (hN.2.2.1 hRM) fX hfX hall GX hGX hw
  refine ⟨hN, hNct, fX, hfX, hall, GX, hGX, hExt, hval, p, hown, ?_, hcont⟩
  intro H hH he A hv
  have hfEq := defined_value_extension_eq N c δ (τ.val G.carrier) φ fX hall H GX hH hGX
    (he.trans hExt.symm)
  have h := hown H hH A hv
  rw [he, hfEq, hval] at h
  exact h

end OAI.TuringRigidity.ConeRealParameterProgram

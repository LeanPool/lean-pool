/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeOracleProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeProjectedProgram
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundProgram
public import LeanPool.TuringConeRigidity.Syntax.DefinedPrefixRemoval
public import LeanPool.TuringConeRigidity.CohenForcing.CohenProgramTotality
public import LeanPool.TuringConeRigidity.Constructibility.RelativeDegreeIdeal
public import LeanPool.TuringConeRigidity.Representation.CommonGenericModels

/-!
# An actual oracle program from a uniform inverse-graph name

Starting from one bounded output and a graph name with a fixed level definition,
we select one table index, simulate the five input jumps from a generic input
and the fifth jump of an old parameter, remove the finite prefix restriction,
and compile the resulting table computation to OracleCode.

The uniform graph-definition/name hypothesis is explicit. This file does not
yet derive that hypothesis for every arbitrary global cone isomorphism.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeOracleProgram

open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenColumnRealName CohenGroundPoset OracleJump TableIndices IndexMatrix
open ConePullbackProgram GenericIdentity ElementaryModel SetDegreeDecoding
open PersistentRestrictions ConePersistence

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

/-- A single program, with oracle A join R^(5), works at every generic
selected-column input. Neither its index nor R depends on the varying filter H. -/
theorem column_oracle_program (M K i : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (hi : i ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm)
    (R : Oracle) (hRM : realCode R ∈ M)
    (f : Name (Conditions (poset K))) (hf : f.encode (label (poset K)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (hw : ∃ A X : Oracle, (realName K i).val G.carrier = realCode A ∧
      Reduces X (iterate (join A R) 5) ∧
      Output (genericExtensionSet M (poset K) G.carrier) (f.val G.carrier) A X) :
    ∃ p : OracleCode,
      (∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
        ∀ A : Oracle, (realName K i).val H.carrier = realCode A →
          OwnProgramAt (genericExtensionSet M (poset K) H.carrier) (f.val H.carrier)
            p (iterate R 5) A) ∧
      ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
        (∀ A, ShuffleRequirements.GenericFor D A → Total p (iterate R 5) A) ∧
        ContinuousOn (value p (iterate R 5)) {A | ShuffleRequirements.GenericFor D A} := by
  obtain ⟨A₀, d, ℓ, _, hprefix⟩ := ConeProjectedProgram.column_prefix_program
    M K i hM hT hK hi δ Z φ R hRM f hf hfv G hG hw
  obtain ⟨d', hsim⟩ := InternalCohen.selected_column_table_simulation
    M K i hM hT hK hi R hRM 5 d
  have hground : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K i).val H.carrier = realCode A →
        (∀ n < ℓ, A n = A₀ n) → ∃ X : Oracle,
          Represents (join A (iterate R 5)) (machine d') X ∧
          Output (genericExtensionSet M (poset K) H.carrier) (f.val H.carrier) A X := by
    intro H hH A hv hpre
    obtain ⟨X, hrep, hout⟩ := hprefix H hH A hv hpre
    exact ⟨X, hsim H hH A hv X hrep, hout⟩
  obtain ⟨d'', htable⟩ := remove_defined_program_prefix M K i hM hT hK hi
    δ Z φ f hfv (iterate R 5) A₀ d' ℓ hground
  obtain ⟨p, hp⟩ := own_program_of_table d''
  have hown : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K i).val H.carrier = realCode A →
        OwnProgramAt (genericExtensionSet M (poset K) H.carrier) (f.val H.carrier)
          p (iterate R 5) A := by
    intro H hH A hv
    exact hp _ _ _ _ (htable H hH A hv)
  exact ⟨p, hown, column_program_generic_totality M K i hM hT hK hi G hG
    p (iterate R 5) (fun H hH A hv => (hown H hH A hv).1)⟩

/-- Supply the single-output witness from an actual extended cone map.
Only the graph/name definition across filters remains as a representation
hypothesis; a program is not among the assumptions. -/
theorem column_program_of_extension (M K i : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (hi : i ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hRM : realCode R ∈ M)
    (hR : degree R = (ρ ⟨degree (jump FixedArithmetic.zero), hz⟩).val)
    (f : Name (Conditions (poset K))) (hf : f.encode (label (poset K)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    let E := genericExtensionSet M (poset K) G.carrier
    let hE := genericExtensionSet_transitive M (poset K) hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK).1
      (manyColumn_internal M K hM hT hK).2 (InternalCollapse.orderSet_pair (poset K))
      G hG (G.upper le_top G.nonempty.choose_spec)
    let J := modelIdeal E hE hTE
    ∀ hIJ : I.carrier ⊆ J.carrier, ∀ σ : J ≃o Cone J a,
      ConePersistence.Extends hIJ ρ σ → f.val G.carrier = pullbackGraph σ →
      ∃ p : OracleCode,
        (∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
          ∀ A : Oracle, (realName K i).val H.carrier = realCode A →
            OwnProgramAt (genericExtensionSet M (poset K) H.carrier) (f.val H.carrier)
              p (iterate R 5) A) ∧
        ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
          (∀ A, ShuffleRequirements.GenericFor D A → Total p (iterate R 5) A) ∧
          ContinuousOn (value p (iterate R 5)) {A | ShuffleRequirements.GenericFor D A} := by
  intro E hE hTE J hIJ σ he hfg
  obtain ⟨A, _, hA, _, _⟩ := projected_real_value M K i hM hT hK hi G hG
  have hAE : A ∈ modelReals E := (mem_extensionSet M (poset K) G.carrier _).mpr
    ⟨realName K i, realName_internal M K i hM hT hK hi, hA⟩
  have hAJ : degree A ∈ J.carrier := ⟨A, hAE, rfl⟩
  have hD : degreeUniverse (groundReals E) = idealSet J :=
    ground_degreeUniverse_eq_idealSet E hE hTE
  obtain ⟨X, hred, hout⟩ := output_of_extension ρ σ hIJ he hz R hR E hD A hAJ
  have hw : ∃ A X : Oracle, (realName K i).val G.carrier = realCode A ∧
      Reduces X (iterate (join A R) 5) ∧
      Output E (f.val G.carrier) A X := ⟨A, X, hA, hred, hfg.symm ▸ hout⟩
  exact column_oracle_program M K i hM hT hK hi δ Z φ R hRM f hf hfv G hG hw

end OAI.TuringRigidity.ConeOracleProgram

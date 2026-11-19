/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputCone.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ProjectedArithmeticOutputName
public import LeanPool.TuringConeRigidity.SetModels.FixedArithmeticTailCone
public import LeanPool.TuringConeRigidity.Representation.OwnDegreeExtensionMeaning
public import LeanPool.TuringConeRigidity.SetModels.InternalColumnExtension
public import LeanPool.TuringConeRigidity.Representation.CommonGenericModels
public import LeanPool.TuringConeRigidity.Syntax.DefinedOutputTailCone

/-!
# Projected Arithmetic Output Cone
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenFactor OracleJump TableIndices IndexMatrix
open PersistentRestrictions SetDegreeDecoding ElementaryModel FullSetForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem projected_arithmetic_output_cone (M C B : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
    (I : CountableIdeal) (ρ : I ≃o I)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hRM : realCode R ∈ M)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero), hz⟩).val)
    (f : Name (Conditions (conditions C))) (hf : f.encode (label (conditions C)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (conditions C) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (hOwn : OwnDegreeExtension (genericExtensionSet M (conditions C) G.carrier)
      (idealSet I) (automorphismSet ρ) (f.val G.carrier))
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M)
    (A : Oracle) (hτv : τ.val (projected C B hBC G).carrier = realCode A)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ x y : Name (Conditions (conditions C)),
      x.encode (label (conditions C)) ∈ M ∧ y.encode (label (conditions C)) ∈ M ∧
      x.val G.carrier = realCode A ∧
      (∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        τ.val (projected C B hBC H).carrier ⊆ ZFSet.omega →
          x.val H.carrier = τ.val (projected C B hBC H).carrier) ∧
      ∃ d : ℕ, ∃ p ∈ G.carrier, p ≤ p₀ ∧
        ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
          project C B hBC p ∈ (projected C B hBC H).carrier →
            ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
              Represents (iterate (join A' R) 5) (machine d) X' ∧
              ∃ a ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
              ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
                realCode A' ∈ a ∧ realCode X' ∈ b ∧ ZFSet.pair a b ∈ f.val H.carrier := by
  have hct : (M : Set ZFSet.{0}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro z hz; exact label_surjective M hz
  have hc := conditions_mem M C hM hT hC
  have ht := G.upper le_top G.nonempty.choose_spec
  let E := genericExtensionSet M (conditions C) G.carrier
  have hE := genericExtensionSet_transitive M (conditions C) hM G.carrier
  have hTE := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) G hG ht
  let J := modelIdeal E hE hTE
  obtain ⟨hIJ,σ,hσ,hext⟩ := (own_degree_extension_iff E hE hTE I ρ _).mp hOwn
  have hAN : A ∈ modelReals
      (genericExtensionSet M (conditions B) (projected C B hBC G).carrier) :=
    (mem_extensionSet _ _ _ _).mpr ⟨τ,hτ,hτv⟩
  have hAE : A ∈ modelReals E := by
    change realCode A ∈ E
    exact InternalColumnExtension.column_extension_subset M C B hM hT hC hB hBC G hG hAN
  have hAJ : degree A ∈ J.carrier := ⟨A,hAE,rfl⟩
  have hRN : R ∈ modelReals
      (genericExtensionSet M (conditions B) (projected C B hBC G).carrier) := by
    have hcB := conditions_mem M B hM hT hB
    let H := projected C B hBC G
    exact ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB H.carrier
      (H.upper le_top H.nonempty.choose_spec) hRM
  obtain ⟨x,hx,hxv,hxfix⟩ := CohenProjectedNameLift.lift_projected_real_name M C B hM hT hC hB hBC
    τ hτ
  have hxG : x.val G.carrier = realCode A :=
    (hxv G hG (by rw [hτv]; exact realCode_subset A)).trans hτv
  obtain ⟨X,hX,hred,_,y,hy,hyG,hyfix⟩ :=
    ProjectedArithmeticOutputName.projected_output_name M C B hM hT hC hB hBC G hG
      I J hIJ ρ σ hext hz A R hAJ hR hAN hRN
  obtain ⟨c,hprog⟩ := reduces_represents hred
  let d := Encodable.encode c
  have hd : Represents (iterate (join A R) 5) (machine d) X := by
    simpa only [d, machine_encode] using hprog
  have houtput : ∃ a ∈ degreeUniverse (groundReals E), ∃ b ∈ degreeUniverse (groundReals E),
      x.val G.carrier ∈ a ∧ y.val G.carrier ∈ b ∧ ZFSet.pair a b ∈ f.val G.carrier := by
    rw [ownDegreeUniverse_eq_idealSet E hE hTE (groundReals E) (mem_groundReals E),
      ←hσ,hxG,hyG]
    exact boundedOutputFormula_raw _ _ _ _ |>.mp
      ((boundedOutputFormula_spec J σ A hAJ (realCode X)).mpr ⟨X,rfl,hX⟩)
  obtain ⟨q,hq,hqp₀,hqout⟩ := defined_output_tail_cone M C B hM hT hct hC hB hBC
    δ Z φ f x y hf hx hy hfv hxfix hyfix G hG houtput p₀ hp₀
  obtain ⟨p,hp,hpq,hpcode⟩ := fixed_arithmetic_tail_cone M C B hM hT hct hC hB hBC
    x y hx hy hxfix hyfix R hRM d 5 G hG A X hxG hyG hd q hq
  refine ⟨x,y,hx,hy,hxG,hxv,d,p,hp,hpq.trans hqp₀,?_⟩
  intro H hH hpH
  have hqH : project C B hBC q ∈ (projected C B hBC H).carrier := by
    apply (projected C B hBC H).upper (p := project C B hBC p) _ hpH
    change label _ (project C B hBC q) ⊆ label _ (project C B hBC p)
    simpa only [label_project] using restrict_mono B _ _ hpq
  obtain ⟨A',X',hxa,hya,hrep⟩ := hpcode H hH hpH
  refine ⟨A',X',hxa,hya,hrep,?_⟩
  simpa only [hxa,hya] using hqout H hH hqH

end TuringRigidity.BoundedForcing

end OAI

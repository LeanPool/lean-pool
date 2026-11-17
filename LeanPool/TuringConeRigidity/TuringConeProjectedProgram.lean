/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeProjectedProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePullbackProgram
public import LeanPool.TuringConeRigidity.SetModels.ProjectedArithmeticOutputCone
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnRealValue
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnPrefixCone

/-!
# Selecting a single program for a uniformly defined degree relation

This is the relational part of the original selected-column argument. It
requires neither a permutation of degrees nor an automorphism: a single
arithmetically bounded output in one extension is enough, provided the graph
name has the same level definition throughout the generic extensions.
The latter hypothesis remains explicit; producing that name for the original
global cone map is a separate obligation.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeProjectedProgram

open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenFactor OracleJump TableIndices IndexMatrix
open BoundedForcing CohenColumnRealName ConePullbackProgram

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

/-- A real arithmetic in the selected coordinates and an old parameter has
an output name invariant under permutations of the other coordinates. -/
theorem projected_bounded_output_name (M C B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (A R X : Oracle)
    (hAN : A ∈ modelReals (genericExtensionSet M (conditions B) (projected C B hBC G).carrier))
    (hRN : R ∈ modelReals (genericExtensionSet M (conditions B) (projected C B hBC G).carrier))
    (hred : Reduces X (iterate (join A R) 5)) :
    ∃ y : Name (Conditions (conditions C)), y.encode (label (conditions C)) ∈ M ∧
      y.val G.carrier = realCode X ∧
      ∀ s : Conditions (conditions C) ≃o Conditions (conditions C),
        (∀ p, restrict B (label _ (s p)) = restrict B (label _ p)) →
        ∀ H : GenericFilter (Conditions (conditions C)),
          y.val (AutomorphismName.mapFilter s H).carrier = y.val H.carrier := by
  let H := projected C B hBC G
  let N := genericExtensionSet M (conditions B) H.carrier
  have hH : GroundGeneric M H := projected_groundGeneric M C B hM hT hC hB hBC G hG
  have hc := conditions_mem M B hM hT hB
  have hN := genericExtensionSet_transitive M (conditions B) hM H.carrier
  have hTN := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) H hH (H.upper le_top H.nonempty.choose_spec)
  have hj : join A R ∈ modelReals N := sourceT_real_join N hN hTN hAN hRN
  have hXN : X ∈ modelReals N := sourceT_real_lower N hN hTN
    (sourceT_real_iterate N hN hTN hj 5) hred
  obtain ⟨τ, hτ, hτv⟩ := (mem_extensionSet M (conditions B) H.carrier (realCode X)).mp hXN
  obtain ⟨y, hy, hyv, hinv⟩ := CohenProjectedNameLift.lift_projected_real_name
    M C B hM hT hC hB hBC τ hτ
  exact ⟨y, hy, (hyv G hG (by rw [hτv]; exact realCode_subset X)).trans hτv, hinv⟩

/-- Force a fixed table index and output relation using only the selected
coordinates. The witness assumption is at G only; the conclusion is uniform
in every suitable H meeting the resulting projected condition. -/
theorem projected_program (M C B : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
    (R : Oracle) (hRM : realCode R ∈ M)
    (f : Name (Conditions (conditions C))) (hf : f.encode (label (conditions C)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (conditions C) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M)
    (A X : Oracle) (hτv : τ.val (projected C B hBC G).carrier = realCode A)
    (hred : Reduces X (iterate (join A R) 5))
    (hout : Output (genericExtensionSet M (conditions C) G.carrier) (f.val G.carrier) A X)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ x : Name (Conditions (conditions C)),
      (∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        τ.val (projected C B hBC H).carrier ⊆ ZFSet.omega →
          x.val H.carrier = τ.val (projected C B hBC H).carrier) ∧
      ∃ d : ℕ, ∃ p ∈ G.carrier, p ≤ p₀ ∧
        ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
          project C B hBC p ∈ (projected C B hBC H).carrier →
            ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧
              Represents (iterate (join A' R) 5) (machine d) X' ∧
              Output (genericExtensionSet M (conditions C) H.carrier) (f.val H.carrier) A' X' := by
  have hct : (M : Set ZFSet.{0}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro z hz; exact label_surjective M hz
  have hAN : A ∈ modelReals
      (genericExtensionSet M (conditions B) (projected C B hBC G).carrier) :=
    (mem_extensionSet _ _ _ _).mpr ⟨τ, hτ, hτv⟩
  have hRN : R ∈ modelReals
      (genericExtensionSet M (conditions B) (projected C B hBC G).carrier) := by
    have hcB := conditions_mem M B hM hT hB
    let H := projected C B hBC G
    exact ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB H.carrier
      (H.upper le_top H.nonempty.choose_spec) hRM
  obtain ⟨x, hx, hxv, hxfix⟩ :=
    CohenProjectedNameLift.lift_projected_real_name M C B hM hT hC hB hBC τ hτ
  have hxG : x.val G.carrier = realCode A :=
    (hxv G hG (by rw [hτv]; exact realCode_subset A)).trans hτv
  obtain ⟨y, hy, hyG, hyfix⟩ := projected_bounded_output_name
    M C B hM hT hC hB hBC G hG A R X hAN hRN hred
  obtain ⟨code, hprog⟩ := reduces_represents hred
  let d := Encodable.encode code
  have hd : Represents (iterate (join A R) 5) (machine d) X := by
    simpa only [d, machine_encode] using hprog
  have houtput : ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C)
    G.carrier)),
      ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) G.carrier)),
        x.val G.carrier ∈ u ∧ y.val G.carrier ∈ v ∧ ZFSet.pair u v ∈ f.val G.carrier := by
    simpa only [Output, hxG, hyG] using hout
  obtain ⟨q, hq, hqp₀, hqout⟩ := defined_output_tail_cone M C B hM hT hct hC hB hBC
    δ Z φ f x y hf hx hy hfv hxfix hyfix G hG houtput p₀ hp₀
  obtain ⟨p, hp, hpq, hpcode⟩ := fixed_arithmetic_tail_cone M C B hM hT hct hC hB hBC
    x y hx hy hxfix hyfix R hRM d 5 G hG A X hxG hyG hd q hq
  refine ⟨x, hxv, d, p, hp, hpq.trans hqp₀, ?_⟩
  intro H hH hpH
  have hqH : project C B hBC q ∈ (projected C B hBC H).carrier := by
    apply (projected C B hBC H).upper (p := project C B hBC p) _ hpH
    change label _ (project C B hBC q) ⊆ label _ (project C B hBC p)
    simpa only [label_project] using restrict_mono B _ _ hpq
  obtain ⟨A', X', hxa, hya, hrep⟩ := hpcode H hH hpH
  refine ⟨A', X', hxa, hrep, ?_⟩
  simpa only [Output, hxa, hya] using hqout H hH hqH

/-- Specialize to one Cohen column and express the condition as agreement
with a finite input prefix. -/
theorem column_prefix_program (M K i : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (hi : i ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
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
    ∃ A₀ : Oracle, ∃ d ℓ : ℕ,
      (realName K i).val G.carrier = realCode A₀ ∧
      ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
        ∀ A : Oracle, (realName K i).val H.carrier = realCode A →
          (∀ n < ℓ, A n = A₀ n) → ∃ X : Oracle,
            Represents (iterate (join A R) 5) (machine d) X ∧
            Output (genericExtensionSet M (poset K) H.carrier) (f.val H.carrier) A X := by
  let C := ZFSet.prod K ZFSet.omega
  let B := ZFSet.prod {i} ZFSet.omega
  have hBC := singleton_coordinates_subset K i hi
  have hsingle := singleton_mem M hM hT.pairing (hM K hK i hi)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  obtain ⟨A, X, hA, hred, hout⟩ := hw
  obtain ⟨AG, hτv, hfull, _, _⟩ := projected_real_value M K i hM hT hK hi G hG
  have he : AG = A := realCode_injective (hfull.symm.trans hA)
  subst AG
  obtain ⟨x, hxv, d, p, hp, _, hcone⟩ := projected_program M C B hM hT hC hB hBC
    δ Z φ R hRM f hf hfv G hG (realName {i} i)
    (realName_internal M {i} i hM hT hsingle (ZFSet.mem_singleton.mpr rfl))
    A X hτv hred hout ⊤ (G.upper le_top G.nonempty.choose_spec)
  obtain ⟨A₀, hA₀, ℓ, hprefix⟩ := selected_prefix_cone M K i hM hT hK hi G hG p hp
  refine ⟨A₀, d, ℓ, hA₀, ?_⟩
  intro H hH AH hv hpre
  obtain ⟨A', X', hx, hrep, hout⟩ := hcone H hH (hprefix H hH AH hv hpre)
  obtain ⟨A'', hτH, hfullH, _, _⟩ := projected_real_value M K i hM hT hK hi H hH
  have h1 : A' = A'' := realCode_injective
    (hx.symm.trans ((hxv H hH (hτH.symm ▸ realCode_subset A'')).trans hτH))
  have h2 : A'' = AH := realCode_injective (hfullH.symm.trans hv)
  subst A'
  subst A''
  exact ⟨X', hrep, hout⟩

end OAI.TuringRigidity.ConeProjectedProgram

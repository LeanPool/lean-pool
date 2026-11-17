/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/DefinedOutputTailCone.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenTailTruth
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenProjectionSymmetry
public import LeanPool.TuringConeRigidity.Effective.UniformDegreeUniverseName
public import LeanPool.TuringConeRigidity.Syntax.BoundedAutomorphismOutput
public import LeanPool.TuringConeRigidity.CohenForcing.CohenNiceNameConstruction

/-!
# Defined Output Tail Cone
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem defined_output_tail_cone (M C B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
    (f x y : Name (Conditions (conditions C)))
    (hf : f.encode (label (conditions C)) ∈ M)
    (hx : x.encode (label (conditions C)) ∈ M)
    (hy : y.encode (label (conditions C)) ∈ M)
    (hfv : ∀ G : GenericFilter (Conditions (conditions C)), GroundGeneric M G →
      f.val G.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (conditions C) G.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (hxfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions C)),
        x.val (AutomorphismName.mapFilter a G).carrier = x.val G.carrier)
    (hyfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions C)),
        y.val (AutomorphismName.mapFilter a G).carrier = y.val G.carrier)
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (houtput : ∃ d ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) G.carrier)),
      ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) G.carrier)),
        x.val G.carrier ∈ d ∧ y.val G.carrier ∈ b ∧ ZFSet.pair d b ∈ f.val G.carrier)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ p ∈ G.carrier, p ≤ p₀ ∧
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        project C B hBC p ∈ (projected C B hBC H).carrier →
          ∃ d ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
          ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
            x.val H.carrier ∈ d ∧ y.val H.carrier ∈ b ∧ ZFSet.pair d b ∈ f.val H.carrier := by
  have hc := conditions_mem M C hM hT hC
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have ht (H : GenericFilter (Conditions (conditions C))) : ⊤ ∈ H.carrier := by
    obtain ⟨q,hq⟩ := H.nonempty; exact H.upper le_top hq
  obtain ⟨D,hD,hDv⟩ := uniform_degreeUniverse_name M hM hT hc ho (InternalCollapse.orderSet_pair _)
  let e := push f (push x (push y (fun _ => D)))
  have he (i : ℕ) : (e i).encode (label (conditions C)) ∈ M := by
    rcases i with _|_|_|i
    · exact hf
    · exact hx
    · exact hy
    · exact hD
  have hev (H : GenericFilter (Conditions (conditions C))) : (fun i => (e i).val H.carrier) =
      cons (f.val H.carrier) (cons (x.val H.carrier) (cons (y.val H.carrier) (fun _ => D.val
        H.carrier))) := by
    funext i; rcases i with _|_|_|i <;> rfl
  have hinv : ∀ w ∈ M, ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        (boundedOutputFormula.Eval (fun i => (e i).val (AutomorphismName.mapFilter a H).carrier) ↔
          boundedOutputFormula.Eval (fun i => (e i).val H.carrier)) := by
    intro w hw a ha hfix H hH
    have hHa := InternalOrderIsoTransport.map_ground_generic M _ _ w hM hT hc hc hw a ha H hH
    have hExt := InternalOrderIsoTransport.extension_eq M _ _ w hM hT hc hc hw a ha H hH
    rw [hev _,hev H,hxfix a hfix H,hyfix a hfix H,hfv _ hHa,hfv H hH,
      hDv _ hHa (ht _),hDv H hH (ht H),hExt]
  have hφ : boundedOutputFormula.Eval (fun i => (e i).val G.carrier) := by
    rw [hev G,boundedOutputFormula_raw,hDv G hG (ht G)]
    exact houtput
  obtain ⟨r,hr,hrφ⟩ := (internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
    (InternalCollapse.orderSet_pair _) G hG boundedOutputFormula e he).mp hφ
  obtain ⟨p,hp,hp₀',hpr⟩ := G.directed hp₀ hr
  refine ⟨p,hp,hp₀',?_⟩
  intro H hH hpH
  have hv := cone_truth_of_internal_tail_symmetry M C B hM hT hct hC hB hBC
    boundedOutputFormula e he hinv p (forces_mono _ e hpr hrφ) H hH
    ((projected_cone_iff C B hBC H p).mp hpH)
  rw [hev H,boundedOutputFormula_raw,hDv H hH (ht H)] at hv
  exact hv

end TuringRigidity.BoundedForcing

end OAI

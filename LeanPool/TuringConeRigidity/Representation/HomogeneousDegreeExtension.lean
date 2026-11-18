/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/HomogeneousDegreeExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformDegreeOrderName
public import LeanPool.TuringConeRigidity.SetModels.InternalHomogeneousTruth
public import LeanPool.TuringConeRigidity.SetModels.SetModelActionSatisfaction

/-!
# Homogeneous Degree Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible SetModelSatisfaction
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- A set-coded action on the extension's own degree universe extends the designated partial
action. -/
def OwnDegreeExtension (E I ρ f : ZFSet.{0}) : Prop :=
  IsAction f (degreeUniverse (groundReals E)) (degreeOrder (groundReals E)) ∧
    I ⊆ degreeUniverse (groundReals E) ∧ ρ ⊆ f

/-- Bounded formula expressing an action with the required source subset and extending graph. -/
def degreeExtensionFormula : BoundedSetTheory.Formula :=
  .conj (actionFormula 0 1 2) (.conj (.subset 3 1) (.subset 4 0))

theorem degreeExtensionFormula_spec (f D L I ρ : ZFSet.{0}) :
    degreeExtensionFormula.Eval (cons f (cons D (cons L (cons I (fun _ => ρ))))) ↔
      IsAction f D L ∧ I ⊆ D ∧ ρ ⊆ f := by
  simp only [degreeExtensionFormula,Formula.Eval,eval_actionFormula,Formula.eval_subset,
    cons_zero,cons_succ]

theorem degree_extension_all_generics (M c I ρ : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M)
    (hct : (M : Set ZFSet.{0}).Countable) (hc : c ∈ M) (hI : I ∈ M) (hρ : ρ ∈ M)
    (hom : ∀ p q : Conditions c, ∃ w ∈ M, ∃ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) ∧
      ∃ r, r ≤ a p ∧ r ≤ q)
    (f : Name (Conditions c)) (hf : f.encode (label c) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        f.val (AutomorphismName.mapFilter a G).carrier = f.val G.carrier)
    (G₀ : GenericFilter (Conditions c)) (hG₀ : GroundGeneric M G₀)
    (h₀ : OwnDegreeExtension (genericExtensionSet M c G₀.carrier) I ρ (f.val G₀.carrier)) :
    ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
      OwnDegreeExtension (genericExtensionSet M c G.carrier) I ρ (f.val G.carrier) := by
  have hoM := InternalCollapse.orderSet_mem M hM hT hc
  have ho := InternalCollapse.orderSet_pair c
  obtain ⟨D,hD,hDv⟩ := uniform_degreeUniverse_name M hM hT hc hoM ho
  obtain ⟨L,hL,hLv⟩ := uniform_degreeOrder_name M hM hT hc hoM ho
  have hcheck {x : ZFSet.{0}} (hx : x ∈ M) :
      (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hx
  let e := push f (push D (push L (push (Name.check I) (fun _ => Name.check ρ))))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _|_|_|_|i
    · exact hf
    · exact hD
    · exact hL
    · exact hcheck hI
    · exact hcheck hρ
  have hs (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
      degreeExtensionFormula.Eval (fun i => (e i).val G.carrier) ↔
        OwnDegreeExtension (genericExtensionSet M c G.carrier) I ρ (f.val G.carrier) := by
    obtain ⟨q,hq⟩ := G.nonempty
    have ht := G.upper le_top hq
    have hv : (fun i => (e i).val G.carrier) =
        cons (f.val G.carrier) (cons (D.val G.carrier) (cons (L.val G.carrier)
          (cons I (fun _ => ρ)))) := by
      funext i; rcases i with _|_|_|_|i
      · rfl
      · rfl
      · rfl
      · exact Name.val_check G.carrier ht _
      exact Name.val_check G.carrier ht _
    rw [hv,degreeExtensionFormula_spec,hDv G hG ht,hLv G hG ht]
    rfl
  have hsym : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        (degreeExtensionFormula.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          degreeExtensionFormula.Eval (fun i => (e i).val G.carrier)) := by
    intro w hw a ha G hG
    have hH := InternalOrderIsoTransport.map_ground_generic M c c w hM hT hc hc hw a ha G hG
    rw [hs _ hH,hs G hG,InternalOrderIsoTransport.extension_eq M c c w hM hT hc hc hw a ha G hG,
      hinv w hw a ha G hG]
  have hall := (all_generics_of_internal_symmetry M c hM hT hct hc hom
    degreeExtensionFormula e he hsym G₀ hG₀ ((hs G₀ hG₀).mpr h₀)).2
  exact fun G hG => (hs G hG).mp (hall G hG)

end TuringRigidity.BoundedForcing

end OAI

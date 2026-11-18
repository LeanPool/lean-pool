/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealGeneratedModel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanFilterReconstruction
public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanExtension

/-!
# Real Generated Model
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RealGeneratedModel
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric InternalBooleanTop

/-- A transitive SourceT model contains the ground model and the distinguished set `X`. -/
def Contains (M X N : ZFSet.{0}) : Prop :=
  Transitive N ∧ SourceT N ∧ M ⊆ N ∧ X ∈ N

/-- Intersect all suitable transitive extensions inside one chosen witness, using empty set if
none exists. -/
noncomputable def hull (M X : ZFSet.{0}) : ZFSet.{0} := by
  classical
  exact if h : ∃ N, Contains M X N then
    h.choose.sep (fun z => ∀ N, Contains M X N → z ∈ N)
  else ∅

theorem mem_hull (M X z : ZFSet.{0}) (h : ∃ N, Contains M X N) :
    z ∈ hull M X ↔ ∀ N, Contains M X N → z ∈ N := by
  rw [hull,dite_eq_left h,ZFSet.mem_sep]
  exact ⟨fun hz => hz.2,fun hz => ⟨hz h.choose h.choose_spec,hz⟩⟩

theorem hull_eq_of_least (M X H : ZFSet.{0}) (hH : Contains M X H)
    (hleast : ∀ N, Contains M X N → H ⊆ N) : hull M X = H := by
  apply ZFSet.ext; intro z
  rw [mem_hull M X z ⟨H,hH⟩]
  exact ⟨fun hz => hz H hH,fun hz N hN => hleast N hN hz⟩

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

theorem projected_extension_eq_hull (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈
      G.carrier) :
    genericExtensionSet M (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      hull M ((InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier) := by
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := fun he => ZFSet.notMem_empty _
    (Eq.mp (congrArg (fun d => label c ⊤ ∈ d) he) (label_mem c ⊤))
  let _ := booleanTop c A hcA hc0
  have ht : label (positive A) ⊤ = c := label_booleanTop c A hcA hc0
  have hbits (n : ℕ) : bitCode c (E n) ∈ A := by
    rw [hAe]
    exact seeds_subset c B Q _ (fun _ h => (ZFSet.mem_sep.mp h).1)
      (bit_mem_seeds M c B hM hT hc hB E (fun n => (hE n).1) n)
  obtain ⟨hN,hTN,hMN,hXN,_,_⟩ := InternalBooleanExtension.projected_extension_sandwich
    M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hgraph hbits G hG hGt
  symm
  apply hull_eq_of_least M _ _ ⟨hN,hTN,hMN,hXN⟩
  intro N hN
  exact BooleanFilterReconstruction.projected_extension_least_for_real M N c B Q A hM hT
    hN.1 hN.2.1 hN.2.2.1 hc hBM hQM hAM hB hQ hA E hE hgraph hAe G hG hGt hN.2.2.2

theorem hull_properties (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈
      G.carrier) :
    let X := (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier
    Contains M X (hull M X) ∧
      genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ∈
        hull M X ∧
      hull M X ⊆ genericExtensionSet M c G.carrier := by
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := fun he => ZFSet.notMem_empty _
    (Eq.mp (congrArg (fun d => label c ⊤ ∈ d) he) (label_mem c ⊤))
  let _ := booleanTop c A hcA hc0
  have ht : label (positive A) ⊤ = c := label_booleanTop c A hcA hc0
  have hbits (n : ℕ) : bitCode c (E n) ∈ A := by
    rw [hAe]
    exact seeds_subset c B Q _ (fun _ h => (ZFSet.mem_sep.mp h).1)
      (bit_mem_seeds M c B hM hT hc hB E (fun n => (hE n).1) n)
  obtain ⟨hN,hTN,hMN,hXN,hHN,hNG⟩ := InternalBooleanExtension.projected_extension_sandwich
    M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hgraph hbits G hG hGt
  have he := projected_extension_eq_hull M c B Q A hM hT hc hBM hQM hAM hB hQ hA E hE hgraph hAe G
    hG hGt
  dsimp only
  rw [←he]
  exact ⟨⟨hN,hTN,hMN,hXN⟩,hHN,hNG⟩

end TuringRigidity.RealGeneratedModel

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanTop
public import LeanPool.TuringConeRigidity.SetModels.InternalSubsetSequence
public import LeanPool.TuringConeRigidity.SetModels.InternalSameNameGeneric

/-!
# Internal Boolean Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanName
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalBooleanBits InternalProjectedGeneric InternalBooleanTop
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

/-- The positive Boolean codes equal to the value of the `n`th name-bit family. -/
noncomputable def tags (c A : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (n : ℕ) : ZFSet.{0} :=
  (positive A).sep (fun U => U = bitCode c (E n))

theorem tags_info (M c A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hA : A ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M) :
    ∀ n, tags c A E n ∈ M ∧ tags c A E n ⊆ positive A := by
  intro n
  refine ⟨?_,fun _ h => (ZFSet.mem_sep.mp h).1⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (bitFormula 1 2 0) (cons c (fun _ => E n))
    (by
      intro i
      cases i
      · exact hc
      · exact hE n) (positive_mem M A hM hT hA)
  simpa only [bitFormula_spec,cons_zero,cons_succ,tags] using hs

theorem tags_graph_mem (M c A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hA : A ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) :
    orbitGraph (tags c A E) ∈ M := by
  obtain ⟨R,hRM,hR⟩ := internal_power M hM hT.powerSet hc
  let e := cons c (cons R (fun _ => orbitGraph E))
  let φ : BoundedSetTheory.Formula := .existsMem 3 (.conj (.pairMem 2 0 5) (bitFormula 3 0 1))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | _ | i
    · exact hc
    · exact hRM
    · exact hgraph
  apply InternalSubsetSequence.subset_sequence M (positive A) hM hT
    (positive_mem M A hM hT hA) φ e he (tags c A E)
    (fun n _ h => (ZFSet.mem_sep.mp h).1)
  intro n U hU
  simp only [φ,Formula.Eval,Formula.eval_pairMem,bitFormula_spec,cons_zero,cons_succ,e,
    tags,ZFSet.mem_sep,and_iff_right hU]
  constructor
  · rintro ⟨W,_,hnW,hUW⟩
    have hw := (orbitGraph_pair E n W).mp hnW
    exact hw ▸ hUW
  · intro h
    exact ⟨E n,(hR _).mpr (hE n),(orbitGraph_pair E n _).mpr rfl,h⟩

/-- The Boolean-poset name built from the bit-value tag families. -/
noncomputable def booleanName (c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (E : ℕ → ZFSet.{0}) : Name (Conditions (positive A)) :=
  InternalNiceName.nice (tags c A E)

theorem booleanName_internal (M c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hA : A ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hgraph : orbitGraph E ∈ M) : (booleanName c A E).encode (label (positive A)) ∈ M :=
  InternalNiceName.nice_internal M hM hT (positive_mem M A hM hT hA)
    (tags c A E) (tags_info M c A hM hT hc hA E (fun n => (hE n).1))
    (tags_graph_mem M c A hM hT hc hA E hE hgraph)

theorem mem_val_booleanName (c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (E : ℕ → ZFSet.{0}) (H : Set (Conditions (positive A))) (hH : ⊤ ∈ H)
    (x : ZFSet.{0}) : x ∈ (booleanName c A E).val H ↔
      ∃ n, (∃ q ∈ H, label (positive A) q = bitCode c (E n)) ∧ natSet n = x := by
  rw [booleanName,InternalNiceName.mem_val_nice _ H hH]
  constructor
  · rintro ⟨n,q,hq,ht,hx⟩
    exact ⟨n,⟨q,hq,(ZFSet.mem_sep.mp ht).2⟩,hx⟩
  · rintro ⟨n,⟨q,hq,he⟩,hx⟩
    exact ⟨n,q,hq,ZFSet.mem_sep.mpr ⟨label_mem _ q,he⟩,hx⟩

theorem val_booleanName (M c B Q A : ZFSet.{0})
    [Top (Conditions c)] [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hTop : ⊤ ∈ G.carrier) :
    (booleanName c A E).val (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      (InternalNiceName.nice E : Name (Conditions c)).val G.carrier := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hHt := top_in_filter c A (fun U hU => ((hB U).mp (hA.1 hU)).2.1) ht H
  apply ZFSet.ext
  intro x
  rw [mem_val_booleanName c A E H.carrier hHt]
  dsimp only [H]
  simp only [InternalSameNameGeneric.projected_bit_iff M c B Q A hM hT hc hBM hAM
    hB hQ hA E hE hbits G hG hTop]
  constructor
  · rintro ⟨n,hn,rfl⟩; exact hn
  · intro hx
    obtain ⟨n,p,hp,hpE,hnx⟩ := (InternalNiceName.mem_val_nice E G.carrier hTop x).mp hx
    exact ⟨n,hnx.symm ▸ hx,hnx⟩

theorem same_value_mem_projected_extension (M c B Q A : ZFSet.{0})
    [Top (Conditions c)] [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hTop : ⊤ ∈
      G.carrier) :
    (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∈
      genericExtensionSet M (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier
        :=
  (mem_extensionSet _ _ _ _).mpr ⟨booleanName c A E,
    booleanName_internal M c A hM hT hc hAM E hE hgraph,
    val_booleanName M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hbits G hG hTop⟩

end TuringRigidity.InternalBooleanName

end OAI

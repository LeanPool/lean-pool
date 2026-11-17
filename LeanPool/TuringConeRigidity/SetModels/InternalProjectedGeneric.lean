/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalProjectedGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanDense
public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanGraph

/-!
# Internal Projected Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalProjectedGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The nonempty members of `A`. -/
noncomputable def positive (A : ZFSet.{0}) : ZFSet.{0} := A.sep (fun U => U ≠ ∅)

theorem positive_mem (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) : positive A ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 0 (.equal 0 0)) (fun _ => A) (fun _ => hA) hA
  have he : A.sep (fun U => (Formula.existsMem 0 (.equal 0 0)).Eval (cons U (fun _ => A))) =
    positive A := by
    apply ZFSet.ext
    intro U
    simp only [positive,ZFSet.mem_sep,Formula.Eval,cons_zero]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨p,hp,_⟩ h0
      exact ZFSet.notMem_empty p (h0 ▸ hp)
    · intro hn
      obtain h0 | ⟨p,hp⟩ := ZFSet.eq_empty_or_nonempty U
      · exact False.elim (hn h0)
      · exact ⟨p,hp,True.intro⟩
  exact he ▸ hs

/-- The partial order on positive Boolean codes induced by subset inclusion of their labels. -/
@[instance_reducible]
noncomputable def codeOrder (A : ZFSet.{0}) : PartialOrder (Conditions (positive A)) where
  le p q := label (positive A) p ⊆ label (positive A) q
  lt p q := label (positive A) p ⊆ label (positive A) q ∧ ¬ label (positive A) q ⊆ label (positive
    A) p
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl _ := fun _ h => h
  le_trans _ _ _ hpq hqr := fun _ h => hqr (hpq h)
  le_antisymm _ _ hpq hqp := label_injective _ (ZFSet.ext (fun _ => ⟨fun h => hpq h,fun h => hqp
    h⟩))

/-- The preorder induced by the partial order on positive Boolean-code labels. -/
@[instance_reducible]
noncomputable def codePreorder (algebraSet : ZFSet.{0}) :
    Preorder (Conditions (positive algebraSet)) :=
  (codeOrder algebraSet).toPreorder

attribute [local instance] codeOrder codePreorder

theorem label_info (A : ZFSet.{0}) (p : Conditions (positive A)) :
    label (positive A) p ∈ A ∧ label (positive A) p ≠ ∅ :=
  ZFSet.mem_sep.mp (label_mem (positive A) p)

/-- Project a condition filter to the positive Boolean codes hit by its members. -/
noncomputable def projected (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) : GenericFilter (Conditions (positive A)) where
  carrier := {p | Hit G (label (positive A) p)}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    let b := basicCode c (label c p)
    have hbM : b ∈ M := basicCode_mem M c _ hM hT hc (label_mem c p)
    have hbc : IsCode c b := regular_isCode c _
    have hb : label c p ∈ b := mem_basicCode c _ (label_mem c p)
    have hpb := subset_project c A b hbc.1 hb
    have hPA := project_mem_part M c B Q A b hM hT hc hBM hAM hbM hB hQ hA
    have hn : project c A b ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ hpb)
    obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hPA,hn⟩)
    exact ⟨q,p,hp,hq.symm ▸ hpb⟩
  upper := by
    intro p q hpq hp
    obtain ⟨r,hr,hrp⟩ := hp
    exact ⟨r,hr,hpq hrp⟩
  directed := by
    intro p q hp hq
    let U := label (positive A) p
    let V := label (positive A) q
    have hU := (label_info A p).1
    have hV := (label_info A q).1
    have hUc := ((hB U).mp (hA.1 hU)).2
    have hVc := ((hB V).mp (hA.1 hV)).2
    let F : ZFSet.{0} := {U,V}
    have hFM : F ∈ M := pair_mem M hM hT.pairing (hM A hAM U hU) (hM A hAM V hV)
    have hFA : F ⊆ A := by
      intro W hW
      exact (ZFSet.mem_pair.mp hW).elim (fun h => h ▸ hU) (fun h => h ▸ hV)
    have hWA := closed_inf M c B Q A F hM hT hc hBM hB hQ hA hFM hFA
    obtain ⟨r,hr,hrU⟩ := hp
    obtain ⟨s,hs,hsV⟩ := hq
    obtain ⟨t,ht,htr,hts⟩ := G.directed hr hs
    have htU := code_lower c U hUc _ hrU _ (label_mem c t) htr
    have htV := code_lower c V hVc _ hsV _ (label_mem c t) hts
    have htW : label c t ∈ infCode c F := by
      refine ZFSet.mem_sep.mpr ⟨label_mem c t,fun W hW => ?_⟩
      exact (ZFSet.mem_pair.mp hW).elim (fun h => h ▸ htU) (fun h => h ▸ htV)
    have hn : infCode c F ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ htW)
    obtain ⟨w,hw⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hWA,hn⟩)
    refine ⟨w,⟨t,ht,hw.symm ▸ htW⟩,?_,?_⟩
    · change label (positive A) w ⊆ U
      rw [hw]
      exact inf_subset c F (ZFSet.mem_pair.mpr (Or.inl rfl))
    · change label (positive A) w ⊆ V
      rw [hw]
      exact inf_subset c F (ZFSet.mem_pair.mpr (Or.inr rfl))

theorem projected_ground_generic (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (projected M c B Q A hM hT hc hBM hAM hB hQ hA G) := by
  intro D hDM hD
  let D' := (positive A).sep (fun U => U ∈ D)
  have hD'M : D' ∈ M := by
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded
      (.member 0 1) (fun _ => D) (fun _ => hDM) (positive_mem M A hM hT hAM)
    simpa only [D',Formula.Eval,cons_zero,cons_succ] using hs
  have hd : DenseCodes A D' := by
    intro U hUA hU0
    obtain ⟨p,hp⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hUA,hU0⟩)
    obtain ⟨q,hqp,hqD⟩ := hD p
    refine ⟨label (positive A) q,ZFSet.mem_sep.mpr ⟨label_mem _ q,hqD⟩,
      (label_info A q).1,(label_info A q).2,?_⟩
    change label (positive A) q ⊆ label (positive A) p at hqp
    rwa [hp] at hqp
  obtain ⟨U,hUD,hUG⟩ := ground_meets_dense_codes M c B Q A D' hM hT hc hBM hAM hD'M hB hQ hA hd G hG
  obtain ⟨hUp,hUD⟩ := ZFSet.mem_sep.mp hUD
  obtain ⟨p,hp⟩ := label_surjective (positive A) hUp
  exact ⟨p,(show Hit G (label (positive A) p) from hp.symm ▸ hUG),hp.symm ▸ hUD⟩

theorem projected_order_code (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) :
    InternalBooleanGraph.inclusionOrder (positive A) ∈ M ∧
      ∀ p q : Conditions (positive A),
        ZFSet.pair (label (positive A) p) (label (positive A) q) ∈
          InternalBooleanGraph.inclusionOrder (positive A) ↔ p ≤ q := by
  refine ⟨InternalBooleanGraph.inclusionOrder_mem M _ hM hT (positive_mem M A hM hT hA),?_⟩
  intro p q
  rw [InternalBooleanGraph.pair_inclusionOrder]
  exact ⟨fun h => h.2.2,fun h => ⟨label_mem _ p,label_mem _ q,h⟩⟩

end TuringRigidity.InternalProjectedGeneric

end OAI

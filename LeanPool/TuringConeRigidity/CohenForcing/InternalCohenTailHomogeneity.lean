/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenTailHomogeneity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenHomogeneity
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenPartition

/-!
# Internal Cohen Tail Homogeneity
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenTailHomogeneity
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohenBitFlip InternalCohenRestriction
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  Classical.propDecidable

noncomputable def tailMatchingSet (A B p q : ZFSet.{0}) : ZFSet.{0} :=
  (matchingSet A p q).sep (fun x => x ∉ B)

theorem tailMatchingSet_mem (M A B p q : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hp : p ∈ M) (hq : q ∈ M) :
    tailMatchingSet A B p q ∈ M := by
  simpa only [tailMatchingSet,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.neg (.member 0 1))
      (fun _ => B) (fun _ => hB) (matchingSet_mem M A p q hM hT hA hp hq)

theorem restrict_flip (A B C : ZFSet.{0}) (hBA : B ⊆ A)
    (hBC : ∀ x ∈ B, x ∉ C) (s : Conditions (conditions A)) :
    restrict B (label _ (InternalCohenBitFlip.flipIso A C s)) = restrict B (label _ s) := by
  classical
  have hf := ((pair_flipGraph A C _ _).mp
    ((flipGraph_spec A C s (InternalCohenBitFlip.flipIso A C s)).mpr rfl)).2.2
  apply ZFSet.ext; intro z
  by_cases hz : z ∈ ZFSet.prod B alphabet
  · obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    have h := hf x (hBA hx)
    have hb' : bitSet b ∈ alphabet := (mem_alphabet _).mpr ⟨b,rfl⟩
    cases b
    · simpa only [pair_restrict,hx,hb',and_true,hBC x hx,false_and,true_and,
        false_or,not_false_eq_true] using h.1
    · simpa only [pair_restrict,hx,hb',and_true,hBC x hx,false_and,true_and,
        false_or,not_false_eq_true] using h.2
  · simp only [mem_restrict,hz,and_false]

theorem mask_tailMatchingSet (A B : ZFSet.{0})
    (p q : Condition (Conditions A)) (i : Conditions A) :
    mask A (tailMatchingSet A B (graph A p) (graph A q)) i =
      if label A i ∈ B then false else matchingMask p q i := by
  classical
  by_cases hi : label A i ∈ B
  · simp [mask,tailMatchingSet,hi]
  · rw [ite_eq_right hi,← congrFun (mask_matchingSet A p q) i]
    simp only [mask,tailMatchingSet,ZFSet.mem_sep,hi,not_false_eq_true,and_true]

theorem tail_matching_compatible (A B : ZFSet.{0})
    (p q : Condition (Conditions A))
    (hpq : restrict B (graph A p) ⊆ restrict B (graph A q)) :
    Compatible (flip (mask A (tailMatchingSet A B (graph A p) (graph A q))) p) q := by
  classical
  intro i a b ha hb
  by_cases hi : label A i ∈ B
  · have hm : mask A (tailMatchingSet A B (graph A p) (graph A q)) i = false := by
      rw [mask_tailMatchingSet,ite_eq_left hi]
    have hp : p.val i = some a := by simpa [CohenSymmetry.flip,hm] using ha
    have hpair := hpq ((pair_restrict B (graph A p) (label A i) (bitSet a)).mpr
      ⟨(pair_mem_graph A p i a).mpr hp,hi,(mem_alphabet _).mpr ⟨a,rfl⟩⟩)
    have hq := (pair_mem_graph A q i a).mp ((pair_restrict _ _ _ _).mp hpair).1
    exact Option.some.inj (hq.symm.trans hb)
  · have hm : mask A (tailMatchingSet A B (graph A p) (graph A q)) i =
        matchingMask p q i := by rw [mask_tailMatchingSet,ite_eq_right hi]
    exact matching_compatible p q i a b (by simpa only [CohenSymmetry.flip,hm] using ha) hb

theorem tail_matching_common_extension (A B : ZFSet.{0})
    (p q : Conditions (conditions A))
    (hpq : restrict B (label _ p) ⊆ restrict B (label _ q)) :
    ∃ r, r ≤ InternalCohenBitFlip.flipIso A
      (tailMatchingSet A B (label _ p) (label _ q)) p ∧ r ≤ q := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv A).surjective q
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv A q) = graph A q := label_encode A q
  rw [hp,hq] at hpq ⊢
  let m := mask A (tailMatchingSet A B (graph A p) (graph A q))
  refine ⟨conditionEquiv A (merge (flip m p) q),?_,
    (conditionEquiv A).monotone (merge_le_right (tail_matching_compatible A B p q hpq))⟩
  change conditionEquiv A (merge (flip m p) q) ≤
    conditionEquiv A (flip m ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv A).monotone (merge_le_left _ _)

theorem internally_tail_homogeneous (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M)
    (hBA : B ⊆ A) (p q : Conditions (conditions A))
    (hpq : restrict B (label _ p) ⊆ restrict B (label _ q)) :
    ∃ w ∈ M, ∃ e : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = e s) ∧
      (∀ s, restrict B (label _ (e s)) = restrict B (label _ s)) ∧
      ∃ r, r ≤ e p ∧ r ≤ q := by
  let C := tailMatchingSet A B (label _ p) (label _ q)
  have hc := conditions_mem M A hM hT hA
  have hC : C ∈ M := tailMatchingSet_mem M A B _ _ hM hT hA hB
    (hM _ hc _ (label_mem _ p)) (hM _ hc _ (label_mem _ q))
  refine ⟨flipGraph A C,flipGraph_mem M A C hM hT hA hC,
    InternalCohenBitFlip.flipIso A C,flipGraph_spec A C,?_,
    tail_matching_common_extension A B p q hpq⟩
  exact restrict_flip A B C hBA (fun x hx h => (ZFSet.mem_sep.mp h).2 hx)

end TuringRigidity.InternalCohenTailHomogeneity

end OAI

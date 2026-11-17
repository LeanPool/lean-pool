/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenHomogeneity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenBitFlip

/-!
# Internal Cohen Homogeneity
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenBitFlip
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def matchingSet (A p q : ZFSet.{0}) : ZFSet.{0} :=
  A.sep (fun x =>
    (ZFSet.pair x (bitSet true) ∈ p ∧ ZFSet.pair x (bitSet true) ∉ q) ∨
    (ZFSet.pair x (bitSet true) ∉ p ∧ ZFSet.pair x (bitSet true) ∈ q))

def matchingFormula (x p q z1 : ℕ) : Formula :=
  .disj (.conj (.pairMem x z1 p) (.neg (.pairMem x z1 q)))
    (.conj (.neg (.pairMem x z1 p)) (.pairMem x z1 q))

theorem matchingFormula_spec (x p q z1 : ℕ) (e : ℕ → ZFSet.{0})
    (h1 : e z1 = bitSet true) :
    (matchingFormula x p q z1).Eval e ↔
      (ZFSet.pair (e x) (bitSet true) ∈ e p ∧ ZFSet.pair (e x) (bitSet true) ∉ e q) ∨
      (ZFSet.pair (e x) (bitSet true) ∉ e p ∧ ZFSet.pair (e x) (bitSet true) ∈ e q) := by
  simp only [matchingFormula,Formula.eval_disj,Formula.Eval,Formula.eval_pairMem,h1]

theorem matchingSet_mem (M A p q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hp : p ∈ M) (hq : q ∈ M) : matchingSet A p q ∈ M := by
  have hb : bitSet true ∈ M :=
    hM _ (InternalCohen.alphabet_mem M hM hT) _ ((mem_alphabet _).mpr ⟨true,rfl⟩)
  let e := cons p (cons q (fun _ => bitSet true))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hp
    · exact hq
    · exact hb
  simpa only [matchingSet,matchingFormula,Formula.eval_disj,Formula.Eval,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (matchingFormula 0 1 2 3) e he hA

theorem mask_matchingSet (A : ZFSet.{0}) (p q : Condition (Conditions A)) :
    mask A (matchingSet A (graph A p) (graph A q)) = matchingMask p q := by
  classical
  funext i
  have hm : label A i ∈ matchingSet A (graph A p) (graph A q) ↔
      (p.val i = some true ∧ q.val i ≠ some true) ∨
      (p.val i ≠ some true ∧ q.val i = some true) := by
    simp only [matchingSet,ZFSet.mem_sep,label_mem,true_and,pair_mem_graph]
  simp only [mask,hm,matchingMask]
  cases hp : p.val i with
  | none => cases hq : q.val i with
    | none => rfl
    | some b => cases b <;> decide
  | some a => cases hq : q.val i with
    | none => cases a <;> decide
    | some b => cases a <;> cases b <;> decide

theorem matching_common_extension (A : ZFSet.{0}) (p q : Conditions (conditions A)) :
    ∃ r, r ≤ flipIso A (matchingSet A (label _ p) (label _ q)) p ∧ r ≤ q := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv A).surjective q
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv A q) = graph A q := label_encode A q
  rw [hp,hq]
  refine ⟨conditionEquiv A (merge (flip (matchingMask p q) p) q),?_,
    (conditionEquiv A).monotone (merge_le_right (matching_compatible p q))⟩
  change conditionEquiv A (merge (flip (matchingMask p q) p) q) ≤
    conditionEquiv A (flip (mask A (matchingSet A (graph A p) (graph A q)))
      ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply,mask_matchingSet]
  exact (conditionEquiv A).monotone (merge_le_left _ _)

theorem internally_homogeneous (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (p q : Conditions (conditions A)) :
    ∃ w ∈ M, ∃ e : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = e s) ∧
      ∃ r, r ≤ e p ∧ r ≤ q := by
  let B := matchingSet A (label _ p) (label _ q)
  have hc := conditions_mem M A hM hT hA
  have hB : B ∈ M := matchingSet_mem M A _ _ hM hT hA
    (hM _ hc _ (label_mem _ p)) (hM _ hc _ (label_mem _ q))
  exact ⟨flipGraph A B,flipGraph_mem M A B hM hT hA hB,flipIso A B,
    flipGraph_spec A B,matching_common_extension A p q⟩

end TuringRigidity.InternalCohenBitFlip

end OAI

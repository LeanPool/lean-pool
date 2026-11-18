/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenBitFlip.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset

/-!
# Internal Cohen Bit Flip
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenBitFlip
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The Boolean mask indicating which set-coded coordinates belong to `B`. -/
noncomputable def mask (A B : ZFSet.{0}) (i : Conditions A) : Bool :=
  @decide (label A i ∈ B) (Classical.propDecidable _)

/-- On coordinates in `A`, the Boolean assignments in `q` match those in `p` with bits flipped
on `B`. -/
def FlipMatches (A B p q : ZFSet.{0}) : Prop :=
  ∀ x ∈ A,
    (ZFSet.pair x (bitSet false) ∈ q ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet true) ∈ p) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet false) ∈ p)) ∧
    (ZFSet.pair x (bitSet true) ∈ q ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet false) ∈ p) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet true) ∈ p))

/-- Bounded formula expressing the set-coded bit-flip relation `FlipMatches`. -/
def flipMatchesFormula (A B p q z0 z1 : ℕ) : Formula :=
  .allMem A (.conj
    (.iff (.pairMem 0 (z0+1) (q+1))
      (.disj (.conj (.member 0 (B+1)) (.pairMem 0 (z1+1) (p+1)))
        (.conj (.neg (.member 0 (B+1))) (.pairMem 0 (z0+1) (p+1)))))
    (.iff (.pairMem 0 (z1+1) (q+1))
      (.disj (.conj (.member 0 (B+1)) (.pairMem 0 (z0+1) (p+1)))
        (.conj (.neg (.member 0 (B+1))) (.pairMem 0 (z1+1) (p+1))))))

theorem flipMatchesFormula_spec (A B p q z0 z1 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = bitSet false) (h1 : e z1 = bitSet true) :
    (flipMatchesFormula A B p q z0 z1).Eval e ↔
      FlipMatches (e A) (e B) (e p) (e q) := by
  simp only [flipMatchesFormula,FlipMatches,Formula.eval_allMem,Formula.eval_iff,
    Formula.eval_pairMem,Formula.eval_disj,Formula.Eval,cons_zero,cons_succ,h0,h1]

theorem flipMatches_graph_iff (A B : ZFSet.{0})
    (p q : Condition (Conditions A)) :
    FlipMatches A B (graph A p) (graph A q) ↔ q = flip (mask A B) p := by
  classical
  constructor
  · intro h
    apply Condition.ext; funext i
    apply Option.ext; intro b
    have hh := h (label A i) (label_mem A i)
    simp only [pair_mem_graph] at hh
    cases b <;> cases hp : p.val i <;>
      by_cases hi : label A i ∈ B <;>
      simp_all [CohenSymmetry.flip,mask]
  · rintro rfl x hx
    obtain ⟨i,rfl⟩ := label_surjective A hx
    simp only [pair_mem_graph]
    cases hp : p.val i <;> by_cases hi : label A i ∈ B <;>
      simp_all [CohenSymmetry.flip,mask]

/-- The order automorphism of set-coded conditions induced by flipping coordinates in `B`. -/
noncomputable def flipIso (A B : ZFSet.{0}) :
    Conditions (conditions A) ≃o Conditions (conditions A) :=
  (conditionEquiv A).symm.trans
    ((CohenSymmetry.flipIso (mask A B)).trans (conditionEquiv A))

/-- Set-coded graph of the Boolean flip on condition graphs. -/
noncomputable def flipGraph (A B : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (conditions A)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions A,
      z = ZFSet.pair p q ∧ FlipMatches A B p q)

theorem pair_flipGraph (A B p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ flipGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions A ∧ FlipMatches A B p q := by
  simp only [flipGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,h⟩
  · rintro ⟨hp,hq,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,h⟩

theorem flipGraph_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : flipGraph A B ∈ M := by
  have hc := conditions_mem M A hM hT hA
  have hb (b : Bool) : bitSet b ∈ M :=
    hM _ (InternalCohen.alphabet_mem M hM hT) _ ((mem_alphabet _).mpr ⟨b,rfl⟩)
  let e := cons (conditions A) (cons A (cons B (cons (bitSet false) (fun _ => bitSet true))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hc
    · exact hA
    · exact hB
    · exact hb false
    · exact hb true
  simpa only [flipGraph,flipMatchesFormula,FlipMatches,Formula.eval_allMem,Formula.eval_iff,
    Formula.eval_pairMem,Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
        (flipMatchesFormula 4 5 1 0 6 7)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hc hc)

theorem flipGraph_spec (A B : ZFSet.{0})
    (p q : Conditions (conditions A)) :
    ZFSet.pair (label _ p) (label _ q) ∈ flipGraph A B ↔ q = flipIso A B p := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv A).surjective q
  rw [pair_flipGraph,and_iff_right (label_mem _ _),and_iff_right (label_mem _ _)]
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv A q) = graph A q := label_encode A q
  rw [hp,hq,flipMatches_graph_iff]
  change q = flip (mask A B) p ↔ conditionEquiv A q =
    conditionEquiv A (flip (mask A B) ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv A).injective.eq_iff.symm

end TuringRigidity.InternalCohenBitFlip

end OAI

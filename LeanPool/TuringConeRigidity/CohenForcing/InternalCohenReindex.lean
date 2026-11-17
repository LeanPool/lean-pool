/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenReindex.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalGraphEquiv
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset

/-!
# Internal Cohen Reindex
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenReindex
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Two condition graphs assign the same bits at coordinates corresponding through `f`. -/
def Matches (A B f p q : ZFSet.{0}) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ∀ b ∈ alphabet,
    (ZFSet.pair x b ∈ p ↔ ZFSet.pair y b ∈ q)

/-- Bounded formula expressing agreement of condition graphs under coordinate reindexing. -/
def matchesFormula (A B f p q bit : ℕ) : Formula :=
  .allMem A (.allMem (B+1) (.imp (.pairMem 1 0 (f+2))
    (.allMem (bit+2) (.iff (.pairMem 2 0 (p+3)) (.pairMem 1 0 (q+3))))))

theorem matchesFormula_spec (A B f p q bit : ℕ) (e : ℕ → ZFSet.{0}) (hb : e bit = alphabet) :
    (matchesFormula A B f p q bit).Eval e ↔ Matches (e A) (e B) (e f) (e p) (e q) := by
  simp only [Matches,matchesFormula,Formula.eval_allMem,Formula.eval_imp,Formula.eval_iff,
    Formula.eval_pairMem,cons_zero,cons_succ,hb]

theorem matches_graph_iff (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Condition (Conditions A)) (q : Condition (Conditions B)) :
    Matches A B f (graph A p) (graph B q) ↔ q = CohenCoordinates.reindex e p := by
  constructor
  · intro h
    apply Condition.ext; funext j
    apply Option.ext; intro b
    have hh := h (label A (e.symm j)) (label_mem _ _) (label B j) (label_mem _ _)
      ((he _ _).mpr (e.apply_symm_apply j).symm) (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)
    rw [pair_mem_graph,pair_mem_graph] at hh
    exact hh.symm
  · rintro rfl x hx y hy hxy b hb
    obtain ⟨i,rfl⟩ := label_surjective A hx
    obtain ⟨j,rfl⟩ := label_surjective B hy
    obtain rfl := (he i j).mp hxy
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    rw [pair_mem_graph,pair_mem_graph]
    change p.val i = some b ↔ p.val (e.symm (e i)) = some b
    rw [e.symm_apply_apply]

/-- Order isomorphism reindexing set-coded conditions along the coordinate equivalence. -/
noncomputable def reindexIso (A B : ZFSet.{0}) (e : Conditions A ≃ Conditions B) :
    Conditions (conditions A) ≃o Conditions (conditions B) :=
  (conditionEquiv A).symm.trans ((CohenCoordinates.reindex e).trans (conditionEquiv B))

/-- Set-coded graph of the condition reindexing relation. -/
noncomputable def reindexGraph (A B f : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (conditions B)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions B, z = ZFSet.pair p q ∧ Matches A B f p q)

theorem pair_reindexGraph (A B f p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ reindexGraph A B f ↔ p ∈ conditions A ∧ q ∈ conditions B ∧ Matches A B f p q
      := by
  simp only [reindexGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,h⟩
  · rintro ⟨hp,hq,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,h⟩

theorem reindexGraph_mem (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hf : f ∈ M) : reindexGraph A B f ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons A (cons B (cons f (fun _ => alphabet)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    · exact hcA
    · exact hcB
    · exact hA
    · exact hB
    · exact hf
    · exact InternalCohen.alphabet_mem M hM hT
  have hmatches (pairValue leftCondition rightCondition : ZFSet.{0}) :
      (matchesFormula 5 6 7 1 0 8).Eval
        (cons rightCondition (cons leftCondition (cons pairValue e))) ↔
        Matches A B f leftCondition rightCondition :=
    matchesFormula_spec 5 6 7 1 0 8 _ rfl
  simpa only [reindexGraph,Formula.Eval,Formula.eval_orderedPair,hmatches,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (matchesFormula 5 6 7 1 0 8)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)

theorem reindexGraph_spec (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Conditions (conditions A)) (q : Conditions (conditions B)) :
    ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = reindexIso A B e p := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv B).surjective q
  rw [pair_reindexGraph]
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv B q) = graph B q := label_encode B q
  rw [and_iff_right (label_mem _ _),and_iff_right (label_mem _ _),hp,hq,matches_graph_iff A B f e
    he]
  change q = CohenCoordinates.reindex e p ↔
    conditionEquiv B q = conditionEquiv B (CohenCoordinates.reindex e ((conditionEquiv A).symm
      (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv B).injective.eq_iff.symm

theorem internal_reindex (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hfM : f ∈ M) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    ∃ e : Conditions (conditions A) ≃o Conditions (conditions B),
      reindexGraph A B f ∈ M ∧
      (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = e p) ∧
      conditions A ∈ M ∧ InternalCollapse.orderSet (conditions A) ∈ M ∧
      conditions B ∈ M ∧ InternalCollapse.orderSet (conditions B) ∈ M := by
  let e := InternalGraphEquiv.graphEquiv A B f hf hi hs
  exact ⟨reindexIso A B e,reindexGraph_mem M A B f hM hT hA hB hfM,
    reindexGraph_spec A B f e (InternalGraphEquiv.graphEquiv_spec A B f hf hi hs),
    (poset_internal M A hM hT hA).1,(poset_internal M A hM hT hA).2,
    poset_internal M B hM hT hB⟩

end TuringRigidity.InternalCohenReindex

end OAI

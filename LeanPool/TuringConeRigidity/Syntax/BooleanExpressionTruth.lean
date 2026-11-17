/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanExpressionTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanExpressionCoverage
public import LeanPool.TuringConeRigidity.Syntax.BoundedTruthRecursion

/-!
# Boolean Expression Truth
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory

theorem rankWF : WellFounded (fun a b : ZFSet.{0} => ZFSet.rank a < ZFSet.rank b) :=
  InvImage.wf ZFSet.rank Ordinal.lt_wf

def body (B R t : ZFSet.{0}) (rec : ∀ s : ZFSet.{0}, ZFSet.rank s < ZFSet.rank t → Prop) : Prop :=
  (∃ U ∈ B, t = FiniteTerm.tag 0 U ∧ U ∈ R) ∨
  (∃ s, ∃ h : t = FiniteTerm.tag 1 s,
    ¬ rec s (by rw [h]; exact FiniteTerm.pair_rank_right _ _)) ∨
  (∃ T, ∃ h : t = FiniteTerm.tag 2 T, ∃ s, ∃ hs : s ∈ T,
    rec s (by rw [h]; exact (ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)))

noncomputable def value (B R : ZFSet.{0}) : ZFSet.{0} → Prop := rankWF.fix (body B R)

theorem value_unfold (B R t : ZFSet.{0}) : value B R t ↔
    (∃ U ∈ B, t = FiniteTerm.tag 0 U ∧ U ∈ R) ∨
    (∃ s, t = FiniteTerm.tag 1 s ∧ ¬ value B R s) ∨
    (∃ T, t = FiniteTerm.tag 2 T ∧ ∃ s ∈ T, value B R s) := by
  change rankWF.fix (body B R) t ↔ _
  rw [WellFounded.fix_eq]
  simp only [body,value,exists_prop]

theorem payload_mem (D : ZFSet.{0}) (hD : Transitive D) (n : ℕ) (s : ZFSet.{0})
    (ht : FiniteTerm.tag n s ∈ D) : s ∈ D := by
  have hp := hD _ ht _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  exact hD _ hp _ (ZFSet.mem_pair.mpr (Or.inr rfl))

def step (K B R Y t : ZFSet.{0}) : Prop :=
  (∃ U ∈ B, t = FiniteTerm.tag 0 U ∧ U ∈ R) ∨
  (∃ s ∈ K, t = FiniteTerm.tag 1 s ∧ s ∉ Y) ∨
  (∃ T ∈ K, t = FiniteTerm.tag 2 T ∧ ∃ s ∈ T, s ∈ Y)

def formula : Formula :=
  .disj (.existsMem 3 (.conj (.orderedPair 1 6 0) (.member 0 5)))
    (.disj (.existsMem 2 (.conj (.orderedPair 1 7 0) (.neg (.member 0 2))))
      (.existsMem 2 (.conj (.orderedPair 1 8 0) (.existsMem 0 (.member 0 3)))))

def parameters (K B R : ZFSet.{0}) : ℕ → ZFSet.{0} :=
  cons K (cons B (cons R (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2)))))

theorem formula_spec (K B R Y t : ZFSet.{0}) :
    formula.Eval (cons t (cons Y (parameters K B R))) ↔ step K B R Y t := by
  simp only [formula,Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,
    parameters,cons_zero,cons_succ,step,FiniteTerm.tag]

theorem formula_local (K B R : ZFSet.{0}) : BoundedTruthRecursion.Local formula (parameters K B R)
  := by
  intro D hD t ht Y Z ha
  rw [formula_spec,formula_spec]
  apply or_congr Iff.rfl
  apply or_congr
  · apply exists_congr; intro s
    apply and_congr_right; intro _
    apply and_congr_right; intro he
    have hsD := payload_mem D hD 1 s (he ▸ ht)
    have hlt : ZFSet.rank s < ZFSet.rank t := by rw [he]; exact FiniteTerm.pair_rank_right _ _
    exact not_congr (ha s hsD hlt)
  · apply exists_congr; intro T
    apply and_congr_right; intro _
    apply and_congr_right; intro he
    have hTD := payload_mem D hD 2 T (he ▸ ht)
    apply exists_congr; intro s
    apply and_congr_right; intro hs
    have hlt : ZFSet.rank s < ZFSet.rank t := by
      rw [he]; exact (ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)
    exact ha s (hD T hTD s hs) hlt

noncomputable def valueSet (K B R : ZFSet.{0}) : ZFSet.{0} := K.sep (value B R)

theorem valueSet_fixed (K B R : ZFSet.{0}) (hK : Transitive K) :
    ∀ t ∈ K, t ∈ valueSet K B R ↔ formula.Eval (cons t (cons (valueSet K B R) (parameters K B R)))
      := by
  intro t ht
  rw [valueSet,ZFSet.mem_sep,and_iff_right ht,value_unfold,formula_spec]
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨s,he,hs⟩
      have hsK := payload_mem K hK 1 s (he ▸ ht)
      exact ⟨s,hsK,he,fun h => hs (ZFSet.mem_sep.mp h).2⟩
    · rintro ⟨s,hsK,he,hs⟩
      exact ⟨s,he,fun hv => hs (ZFSet.mem_sep.mpr ⟨hsK,hv⟩)⟩
  · constructor
    · rintro ⟨T,he,s,hs,hv⟩
      have hTK := payload_mem K hK 2 T (he ▸ ht)
      exact ⟨T,hTK,he,s,hs,ZFSet.mem_sep.mpr ⟨hK T hTK s hs,hv⟩⟩
    · rintro ⟨T,_,he,s,hs,hv⟩
      exact ⟨T,he,s,hs,(ZFSet.mem_sep.mp hv).2⟩

theorem valueSet_mem (N K B R : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hKN : K ∈ N) (hK : Transitive K) (hB : B ∈ N) (hR : R ∈ N) : valueSet K B R ∈ N := by
  have he : ∀ i, parameters K B R i ∈ N := by
    intro i; rcases i with _|_|_|_|_|i
    · exact hKN
    · exact hB
    · exact hR
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hi := BoundedTruthRecursion.truth_internal N K (valueSet K B R) hN hT hKN hK
    formula (parameters K B R) he (formula_local K B R) (valueSet_fixed K B R hK)
  have eq : K.sep (fun t => t ∈ valueSet K B R) = valueSet K B R := by
    apply ZFSet.ext; intro t
    simp only [valueSet,ZFSet.mem_sep,and_self_left]
  exact eq ▸ hi

end TuringRigidity.BooleanExpressionTruth

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalPairSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalCodeBranch
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalPairCode

/-!
# Ordinal Pair Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

/-- A full formula expressing the two branches of the ordered ordinal-pair encoding. -/
noncomputable def pairCodeSentence : SentenceForm :=
  .conj (fromBounded (.conj (ordinalFormula 1) (ordinalFormula 2)))
    (.disj (.conj (fromBounded (.subset 2 1)) (codeBranchSentence false))
      (.conj (.neg (fromBounded (.subset 2 1)))
        ((codeBranchSentence true).rename (fun i => if i = 0 then 0 else if i = 1 then 2 else 1))))

theorem pairCodeSentence_bound : pairCodeSentence.bound = 3 := by
  have hord : (fromBounded (.conj (ordinalFormula 1) (ordinalFormula 2))).bound = 3 := by rfl
  have hsub : (fromBounded (.subset 2 1)).bound = 3 := by rfl
  have hrename : ((codeBranchSentence true).rename
      (fun i => if i = 0 then 0 else if i = 1 then 2 else 1)).bound ≤ 3 :=
    code_rename_bound (codeBranchSentence true) _ 3 (by intro i _; split <;> (try split) <;> omega)
  have finish (p q r s : SentenceForm)
      (hp : p.bound = 3) (hq : q.bound = 3) (hr : r.bound = 3) (hs : s.bound ≤ 3) :
      (SentenceForm.conj p (.disj (.conj q r) (.conj (.neg q) s))).bound = 3 := by
    change max p.bound (max (max q.bound r.bound) (max q.bound s.bound)) = 3
    rw [hp, hq, hr]
    omega
  exact finish _ _ _ _ hord hsub (codeBranchSentence_bound false) hrename

theorem pairCodeSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    pairCodeSentence.Sat (M : Set ZFSet) e ↔
      ((e 1).IsOrdinal ∧ (e 2).IsOrdinal) ∧
      ((e 2 ⊆ e 1 ∧ (codeBranchSentence false).Sat (M : Set ZFSet) e) ∨
        (¬ e 2 ⊆ e 1) ∧ (codeBranchSentence true).Sat (M : Set ZFSet)
          (fun i => e (if i = 0 then 0 else if i = 1 then 2 else 1))) := by
  change ((fromBounded _).Sat _ e ∧ (SentenceForm.disj _ _).Sat _ e) ↔ _
  rw [bounded_sat,Formula.absolute _ M hM e he,Formula.Eval,eval_ordinalFormula,eval_ordinalFormula,
    SentenceForm.sat_disj]
  simp only [SentenceForm.Sat,SentenceForm.sat_rename,bounded_sat,
    Formula.absolute _ M hM e he,Formula.eval_subset]

theorem pairCodeSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    pairCodeSentence.Sat (M : Set ZFSet) e →
      (e 1).IsOrdinal ∧ (e 2).IsOrdinal ∧ e 0 = (pairCode (e 1).rank (e 2).rank).toZFSet := by
  rw [pairCodeSentence_semantics M hM e he]
  rintro ⟨⟨ha,hb⟩,h⟩
  refine ⟨ha,hb,?_⟩
  have hsub : e 2 ⊆ e 1 ↔ (e 2).rank ≤ (e 1).rank := by
    rw [← ha.toZFSet_rank_eq,← hb.toZFSet_rank_eq,Ordinal.toZFSet_subset_toZFSet_iff]
    simp only [Ordinal.rank_toZFSet]
  rcases h with ⟨hle,hc⟩|⟨hnle,hc⟩
  · have hv := codeBranchSentence_sound M hM hω false e he _ _
      ha.toZFSet_rank_eq.symm hb.toZFSet_rank_eq.symm hc
    simpa only [pairCode,ite_eq_left (hsub.mp
      hle),codeBranchValue,codeScale,Bool.false_eq_true,↓reduceIte] using hv
  · have hv := codeBranchSentence_sound M hM hω true
      (fun i => e (if i = 0 then 0 else if i = 1 then 2 else 1)) (fun i => he _) _ _
      hb.toZFSet_rank_eq.symm ha.toZFSet_rank_eq.symm hc
    simpa only [pairCode,ite_eq_right (fun h => hnle (hsub.mpr
      h)),codeBranchValue,codeScale,↓reduceIte] using hv

theorem pairCodeSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    pairCodeSentence.Sat (M : Set ZFSet) e ↔
      (e 1).IsOrdinal ∧ (e 2).IsOrdinal ∧ e 0 = (pairCode (e 1).rank (e 2).rank).toZFSet := by
  have hω := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  refine ⟨pairCodeSentence_sound M hM hω e he,?_⟩
  rintro ⟨ha,hb,hc⟩
  apply (pairCodeSentence_semantics M hM e he).mpr
  refine ⟨⟨ha,hb⟩,?_⟩
  have hsub : e 2 ⊆ e 1 ↔ (e 2).rank ≤ (e 1).rank := by
    rw [← ha.toZFSet_rank_eq,← hb.toZFSet_rank_eq,Ordinal.toZFSet_subset_toZFSet_iff]
    simp only [Ordinal.rank_toZFSet]
  by_cases hle : (e 2).rank ≤ (e 1).rank
  · left
    refine ⟨hsub.mpr hle,(codeBranchSentence_sourceT M hM hT false e he _ _
      ha.toZFSet_rank_eq.symm hb.toZFSet_rank_eq.symm).mpr ?_⟩
    simpa only [pairCode,ite_eq_left hle,codeBranchValue,codeScale,Bool.false_eq_true,↓reduceIte]
      using hc
  · right
    refine ⟨fun h => hle (hsub.mp h),(codeBranchSentence_sourceT M hM hT true
      (fun i => e (if i = 0 then 0 else if i = 1 then 2 else 1)) (fun i => he _) _ _
        hb.toZFSet_rank_eq.symm ha.toZFSet_rank_eq.symm).mpr ?_⟩
    simpa only [pairCode,ite_eq_right hle,codeBranchValue,codeScale,↓reduceIte] using hc

theorem pairCodeSentence_recovers (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (hc : e 0 = (pairCode a b).toZFSet)
    (hp : pairCodeSentence.Sat (M : Set ZFSet) e) : e 1 = a.toZFSet ∧ e 2 = b.toZFSet := by
  obtain ⟨ha,hb,h⟩ := pairCodeSentence_sound M hM hω e he hp
  rw [hc] at h
  have h := congrArg ZFSet.rank h
  simp only [Ordinal.rank_toZFSet] at h
  obtain ⟨h1,h2⟩ := (pairCode_inj a b (e 1).rank (e 2).rank).mp h
  exact ⟨by rw [h1,ha.toZFSet_rank_eq],by rw [h2,hb.toZFSet_rank_eq]⟩

end TuringRigidity.OrdinalCoding

end OAI

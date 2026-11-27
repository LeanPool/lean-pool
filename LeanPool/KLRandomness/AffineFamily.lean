/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineBlock
import Mathlib.Tactic.NormNum

/-!
# Positive finite-stage laws for disjoint affine blocks

Pairwise disjoint full-row-rank blocks have the product of their syndrome
probabilities. Hence conditioning on any finite family is well defined as a
probability measure, without a separate nonnull-background assumption.
-/

@[expose] public section

namespace Klr.AffineBlock

open MeasureTheory ProbabilityTheory
open FiniteStage
open scoped ENNReal

theorem fairCoin_finset_familyEvent {κ : Type*} (B : κ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (J : Finset κ) :
    fairCoin {X | ∀ k ∈ J, X ∈ (B k).event} =
      ∏ k ∈ J, (1 / 2 : ℝ≥0∞) ^ (B k).rank := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert k J hk ih =>
    let A : Set Cantor := {X | ∀ i ∈ J, X ∈ (B i).event}
    let H := J.biUnion (fun i => (B i).support)
    have hA : DependsOn (fun X : Cantor => X ∈ A) (H : Set ℕ) := by
      intro X Y hxy
      have he (i : κ) (hi : i ∈ J) : (X ∈ (B i).event) = (Y ∈ (B i).event) := by
        apply (B i).dependsOn_event
        intro n hn
        exact hxy n (Finset.mem_biUnion.mpr ⟨i, hi, hn⟩)
      apply propext
      constructor
      · intro hX i hi
        exact (iff_of_eq (he i hi)).mp (hX i hi)
      · intro hY i hi
        exact (iff_of_eq (he i hi)).mpr (hY i hi)
    have hd : Disjoint (B k).support H := by
      rw [Finset.disjoint_left]
      intro n hn hm
      obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hm
      have hki : k ≠ i := by rintro rfl; exact hk hi
      exact Finset.disjoint_left.mp (hdis hki) hn hni
    have he : {X | ∀ i ∈ insert k J, X ∈ (B i).event} = (B k).event ∩ A := by
      ext X
      simp [A]
    rw [he, fairCoin_inter_of_disjoint_support (B k).event A (B k).support H
      (B k).dependsOn_event hA hd, (B k).fairCoin_event, Finset.prod_insert hk]
    exact congrArg ((1 / 2 : ℝ≥0∞) ^ (B k).rank * ·) ih

/-- Exact measure of a finite family of pairwise disjoint block constraints. -/
theorem fairCoin_familyEvent {κ : Type*} [Fintype κ] (B : κ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    fairCoin (familyEvent B) = ∏ k, (1 / 2 : ℝ≥0∞) ^ (B k).rank := by
  simpa [familyEvent] using fairCoin_finset_familyEvent B hdis Finset.univ

/-- Finite, disjoint, full-rank constraints always have a nonnull conjunction. -/
theorem fairCoin_familyEvent_ne_zero {κ : Type*} [Finite κ] (B : κ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    fairCoin (familyEvent B) ≠ 0 := by
  let _ := Fintype.ofFinite κ
  rw [fairCoin_familyEvent B hdis]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (by norm_num))

theorem finiteStageLaw_isProbabilityMeasure_of_disjoint {κ : Type*} [Finite κ]
    (B : κ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) :
    IsProbabilityMeasure (finiteStageLaw B) :=
  finiteStageLaw_isProbabilityMeasure B (fairCoin_familyEvent_ne_zero B hdis)

/-- The new syndrome has its uniform probability under every valid previous finite stage. -/
theorem finiteStageLaw_event_of_disjoint {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support) :
    (finiteStageLaw old) B.event = (1 / 2 : ℝ≥0∞) ^ B.rank :=
  finiteStageLaw_event old B hnew (fairCoin_familyEvent_ne_zero old hold)

/-- Adding a disjoint block does not change a transcript probability while that block's
unread columns still have full row rank. Both sides are actual conditioned measures. -/
theorem nextStageLaw_transcript {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (π : ScanRule) (v : List Bool) (hfull : B.UnreadFullRank π v) :
    (cond fairCoin (familyEvent old ∩ B.event)) {X | π.transcript X v.length = v} =
      (finiteStageLaw old) {X | π.transcript X v.length = v} := by
  rw [← cond_cond_eq_cond_inter (measurableSet_familyEvent old) B.measurableSet_event fairCoin]
  change (cond (finiteStageLaw old) B.event) {X | π.transcript X v.length = v} = _
  rw [cond_apply B.measurableSet_event, Set.inter_comm,
    finiteStage_identity old B hnew π v hfull,
    finiteStageLaw_event_of_disjoint old B hold hnew, ← mul_assoc,
    ENNReal.inv_mul_cancel (pow_ne_zero _ (by norm_num)) (by finiteness), one_mul]

end Klr.AffineBlock

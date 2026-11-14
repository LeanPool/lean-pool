/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Round
public import Mathlib.FieldTheory.Finiteness
public import LeanPool.SingleCopyStabilizer.AdaptiveProcess


/-!
# Stochastic compression of unsigned binary stabilizer labels

This module instantiates the finite adaptive-process theorem with the actual
binary label-space update. At every round, it samples an X label uniformly
from the current X projection and an independent uniform binary correction.
The progress lower bound is proved from the one-round symplectic results.

This is a theorem about unsigned label spaces. It does not assert that a
quantum measurement supplies the stated distribution or reconstruct phases.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace LeanPool.SingleCopyStabilizer.ExactLearning

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An unsigned binary Lagrangian label space. -/
abbrev State (ι : Type*) [Fintype ι] :=
  {L : BinarySpace ι // IsIsotropic L ∧ Module.finrank (ZMod 2) L = Fintype.card ι}

/-- An observed X label together with its independent correction bit. -/
abbrev Outcome (ι : Type*) := BinaryVec ι × ZMod 2

/-- The number of diagonal generators still missing. -/
def rank (s : State ι) : ℕ :=
  Fintype.card ι - Module.finrank (ZMod 2) (diagonalSpace s.val)

/-- Totalized round update, with the Lagrangian invariants preserved. -/
def next (s : State ι) (o : Outcome ι) : State ι :=
  ⟨safeBinaryRound s.val o.1 o.2,
    safeBinaryRound_isotropic s.val s.property.1 o.1 o.2,
    (safeBinaryRound_finrank s.val o.1 o.2).trans s.property.2⟩

open Classical in
/-- Uniform sampling on the current X projection, independently of a
uniform correction bit. Impossible X labels have weight zero. -/
def weight (s : State ι) (o : Outcome ι) : ℝ :=
  if o.1 ∈ xProjection s.val then
    1 / ((Nat.card (xProjection s.val) : ℝ) * 2) else 0

omit [DecidableEq ι] in
theorem projection_card_pos (s : State ι) :
    0 < Nat.card (xProjection s.val) := Nat.card_pos

omit [DecidableEq ι] in
theorem weight_nonneg (s : State ι) (o : Outcome ι) : 0 ≤ weight s o := by
  classical
  unfold weight
  split_ifs <;> positivity

theorem weight_sum (s : State ι) : ∑ o, weight s o = 1 := by
  classical
  have hc : (Nat.card (xProjection s.val) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (projection_card_pos s)
  have hinner (u : BinaryVec ι) :
      (∑ b : ZMod 2, weight s (u, b)) =
        if u ∈ xProjection s.val then 1 / (Nat.card (xProjection s.val) : ℝ) else 0 := by
    by_cases hu : u ∈ xProjection s.val
    · simp [weight, hu]
    · simp [weight, hu]
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun u : BinaryVec ι => u ∈ xProjection s.val).card =
      Nat.card (xProjection s.val) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  field_simp

omit [DecidableEq ι] in
theorem diagonal_finrank_le (s : State ι) :
    Module.finrank (ZMod 2) (diagonalSpace s.val) ≤ Fintype.card ι := by
  classical
  have h := finrank_xProjection_add_diagonal s.val
  rw [s.property.2] at h
  omega

omit [DecidableEq ι] in
theorem rank_eq_projection_finrank (s : State ι) :
    rank s = Module.finrank (ZMod 2) (xProjection s.val) := by
  classical
  have h := finrank_xProjection_add_diagonal s.val
  rw [s.property.2] at h
  unfold rank
  omega

omit [DecidableEq ι] in
/-- The current X projection contains exactly `2^rank` labels. -/
theorem projection_card_eq_pow_rank (s : State ι) :
    Nat.card (xProjection s.val) = 2 ^ rank s := by
  classical
  rw [Nat.card_eq_fintype_card, rank_eq_projection_finrank,
    Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem rank_mono (s : State ι) (o : Outcome ι) : rank (next s o) ≤ rank s := by
  classical
  exact Nat.sub_le_sub_left (safeBinaryRound_diagonal_mono s.val s.property.1 o.1 o.2) _

/-- The finite probability process whose random outcomes are projection
labels and correction bits, and whose state is the evolving label space. -/
def process : AdaptiveProcess.RankedProcess (State ι) (Outcome ι) where
  weight := weight
  next := next
  rank := rank
  weight_nonneg := weight_nonneg
  weight_sum := weight_sum
  rank_mono := rank_mono

/-- Any nonzero allowed X label admits at least one correction that strictly
reduces the number of missing diagonal generators. -/
theorem exists_rank_progress (s : State ι) (u : BinaryVec ι)
    (hu : u ∈ xProjection s.val) (hzero : u ≠ 0) :
    ∃ b : ZMod 2, rank (next s (u, b)) < rank s := by
  classical
  obtain ⟨b, hb⟩ := binaryRound_exists_progress s.val s.property.1 u hu hzero
  refine ⟨b, ?_⟩
  have hdiag := diagonal_finrank_le (next s (u, b))
  change Module.finrank (ZMod 2) (diagonalSpace (safeBinaryRound s.val u b)) ≤ _ at hdiag
  have hnext : safeBinaryRound s.val u b = binaryRound s.val u b := by
    simp [safeBinaryRound, hu]
  rw [hnext] at hdiag
  change Fintype.card ι - Module.finrank (ZMod 2) (diagonalSpace (safeBinaryRound s.val u b)) <
    Fintype.card ι - Module.finrank (ZMod 2) (diagonalSpace s.val)
  rw [hnext]
  omega

omit [DecidableEq ι] in
/-- Positive rank guarantees at least two possible X labels. -/
theorem two_le_projection_card (s : State ι) (hrank : 0 < rank s) :
    2 ≤ Nat.card (xProjection s.val) := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [rank_eq_projection_finrank] at hrank
  have : Nontrivial (xProjection s.val) := Module.finrank_pos_iff.mp hrank
  have h := Fintype.one_lt_card (α := xProjection s.val)
  omega

open Classical in
/-- Cardinality of the nonzero part of the X projection. -/
theorem nonzero_projection_card (s : State ι) :
    (Finset.univ.filter fun u : BinaryVec ι => u ∈ xProjection s.val ∧ u ≠ 0).card =
      Nat.card (xProjection s.val) - 1 := by
  classical
  have hset : (Finset.univ.filter fun u : BinaryVec ι => u ∈ xProjection s.val ∧ u ≠ 0) =
      (Finset.univ.filter fun u : BinaryVec ι => u ∈ xProjection s.val).erase 0 := by
    ext u
    simp [and_comm]
  rw [hset, Finset.card_erase_of_mem (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (xProjection s.val).zero_mem⟩)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Counting one successful correction for every nonzero X label gives
an unconditional progress mass of at least `(#X-1)/(2#X)`. -/
theorem progress_mass_lower_bound (s : State ι) :
    ((Nat.card (xProjection s.val) : ℝ) - 1) /
      ((Nat.card (xProjection s.val) : ℝ) * 2) ≤ process.progressMass s := by
  classical
  let c : ℝ := 1 / ((Nat.card (xProjection s.val) : ℝ) * 2)
  have hnonneg (u : BinaryVec ι) (b : ZMod 2) :
      0 ≤ if rank (next s (u, b)) < rank s then weight s (u, b) else 0 := by
    split_ifs
    · exact weight_nonneg _ _
    · exact le_rfl
  have hinner (u : BinaryVec ι) :
      (if u ∈ xProjection s.val ∧ u ≠ 0 then c else 0) ≤
        ∑ b : ZMod 2, if rank (next s (u, b)) < rank s then weight s (u, b) else 0 := by
    by_cases hu : u ∈ xProjection s.val ∧ u ≠ 0
    · obtain ⟨b, hb⟩ := exists_rank_progress s u hu.1 hu.2
      have hsingle := Finset.single_le_sum (fun b _ => hnonneg u b) (Finset.mem_univ b)
      simpa [hu, hb, weight, hu.1, c] using hsingle
    · simp only [ite_eq_right hu]
      exact Finset.sum_nonneg fun b _ => hnonneg u b
  calc
    _ = ∑ u : BinaryVec ι, if u ∈ xProjection s.val ∧ u ≠ 0 then c else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, nonzero_projection_card]
      rw [Nat.cast_sub (by
        have := projection_card_pos s
        omega : 1 ≤ Nat.card (xProjection s.val))]
      simp only [Nat.cast_one]
      dsimp [c]
      ring
    _ ≤ ∑ u : BinaryVec ι, ∑ b : ZMod 2,
        if rank (next s (u, b)) < rank s then weight s (u, b) else 0 :=
      Finset.sum_le_sum fun u _ => hinner u
    _ = process.progressMass s := by
      simp only [AdaptiveProcess.RankedProcess.progressMass, Fintype.sum_prod_type, process]
      rfl

/-- The exact rank-dependent progress parameter used in the paper is also
proved for this label process. -/
theorem progress_mass_ge_rank_parameter (s : State ι) :
    (1 - (1 / 2 : ℝ) ^ rank s) / 2 ≤ process.progressMass s := by
  classical
  have h := progress_mass_lower_bound s
  rw [projection_card_eq_pow_rank] at h
  push_cast at h
  have heq : (((2 : ℝ) ^ rank s) - 1) / ((2 : ℝ) ^ rank s * 2) =
      (1 - (1 / 2 : ℝ) ^ rank s) / 2 := by
    rw [div_pow, one_pow]
    field_simp
  rwa [heq] at h

/-- The quarter-progress assumption is derived from the label-space update,
not left as a hypothesis of the compression theorem. -/
theorem progress_mass_ge_quarter (s : State ι) (hrank : 0 < rank s) :
    (1 / 4 : ℝ) ≤ process.progressMass s := by
  classical
  have hcard : (2 : ℝ) ≤ Nat.card (xProjection s.val) := by
    exact_mod_cast two_le_projection_card s hrank
  apply le_trans _ (progress_mass_lower_bound s)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (Nat.card (xProjection s.val) : ℝ) * 2)).2
  nlinarith

/-- After `8(n+k)` uniform-X-label rounds, the probability that the label
space is not fully diagonal is at most `2^(-k)`. Here `n = #ι`, and all the
per-round progress hypotheses have been discharged. -/
theorem compression_failure_probability (s : State ι) (k : ℕ) :
    process.failureProbability (8 * (Fintype.card ι + k)) s ≤ (1 / 2 : ℝ) ^ k := by
  classical
  apply process.failure_probability_eight_rounds_per_bit
    (fun s hs => progress_mass_ge_quarter s hs) (Fintype.card ι) k s
  exact Nat.sub_le _ _

omit [DecidableEq ι] in
/-- The terminal event has exactly the expected algebraic meaning. -/
theorem rank_zero_iff_full_diagonal (s : State ι) :
    rank s = 0 ↔ Module.finrank (ZMod 2) (diagonalSpace s.val) = Fintype.card ι := by
  classical
  have h := diagonal_finrank_le s
  unfold rank
  omega

omit [DecidableEq ι] in
/-- Equivalently, at termination every binary vector is a diagonal label. -/
theorem rank_zero_iff_diagonal_eq_top (s : State ι) :
    rank s = 0 ↔ diagonalSpace s.val = ⊤ := by
  classical
  constructor
  · intro hs
    apply Submodule.eq_top_of_finrank_eq
    simpa using (rank_zero_iff_full_diagonal s).mp hs
  · intro hs
    apply (rank_zero_iff_full_diagonal s).mpr
    rw [hs]
    simp

end LeanPool.SingleCopyStabilizer.ExactLearning

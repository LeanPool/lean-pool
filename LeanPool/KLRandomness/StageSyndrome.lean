/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineFamily
public import LeanPool.KLRandomness.StageSyndromeComputable
public import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Averaging the actual conditional laws over all syndromes

For a new full-rank block disjoint from all old blocks, every syndrome has
probability `2⁻ʳ` under the old finite-stage law. The equally weighted average
of the new conditional expectations is therefore exactly the old expectation.
This is the measure identity behind the computable syndrome minimization.
-/

@[expose] public section

namespace Klr.StageSyndrome

open MeasureTheory ProbabilityTheory AffineBlock FiniteMeasure
open scoped BigOperators

/-- Vary only the syndrome of the candidate block. -/
def withSyndrome (B : AffineBlock) (y : Fin B.rank → ZMod 2) : AffineBlock :=
  { B with syndrome := y }

@[simp] theorem withSyndrome_support (B : AffineBlock) (y : Fin B.rank → ZMod 2) :
    (withSyndrome B y).support = B.support := rfl

@[simp] theorem withSyndrome_rank (B : AffineBlock) (y : Fin B.rank → ZMod 2) :
    (withSyndrome B y).rank = B.rank := rfl

theorem mem_withSyndrome_event (B : AffineBlock) (y : Fin B.rank → ZMod 2) (X : Cantor) :
    X ∈ (withSyndrome B y).event ↔
      B.matrix (coordinateValues (fun i : B.support => i.val) X) = y := Iff.rfl

/-- The syndrome events form an exact finite partition on every input. -/
theorem sum_syndrome_indicators (B : AffineBlock) (f : Cantor → ℝ) (X : Cantor) :
    (∑ y : Fin B.rank → ZMod 2, (withSyndrome B y).event.indicator f X) = f X := by
  classical
  let y₀ := B.matrix (coordinateValues (fun i : B.support => i.val) X)
  rw [Finset.sum_eq_single y₀]
  · exact Set.indicator_of_mem rfl f
  · intro y _ hne
    apply Set.indicator_of_notMem
    intro h
    exact hne ((mem_withSyndrome_event B y X).mp h).symm
  · simp

theorem sum_setIntegral_syndromes (B : AffineBlock) {μ : Measure Cantor}
    {f : Cantor → ℝ} (hf : Integrable f μ) :
    (∑ y : Fin B.rank → ZMod 2, ∫ X in (withSyndrome B y).event, f X ∂μ) =
      ∫ X, f X ∂μ := by
  simp_rw [← integral_indicator (withSyndrome B _).measurableSet_event]
  rw [← integral_finsetSum _ (fun y _ => hf.indicator (withSyndrome B y).measurableSet_event)]
  exact integral_congr_ae (Filter.Eventually.of_forall (sum_syndrome_indicators B f))

/-- Each actual new conditional law has the expected normalization factor. -/
theorem integral_cond_syndrome {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    (y : Fin B.rank → ZMod 2) (f : Cantor → ℝ) :
    (∫ X, f X ∂cond (finiteStageLaw old) (withSyndrome B y).event) =
      (2 : ℝ) ^ B.rank * ∫ X in (withSyndrome B y).event, f X ∂finiteStageLaw old := by
  rw [ProbabilityTheory.cond, integral_smul_measure,
    finiteStageLaw_event_of_disjoint old (withSyndrome B y) hold hnew]
  simp [ENNReal.toReal_inv, ENNReal.toReal_pow, smul_eq_mul]

/-- Exact averaging over all syndromes recovers the old-stage expectation. -/
theorem average_integral_cond_syndrome {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    {f : Cantor → ℝ} (hf : Integrable f (finiteStageLaw old)) :
    (∑ y : Fin B.rank → ZMod 2,
      ∫ X, f X ∂cond (finiteStageLaw old) (withSyndrome B y).event) / (2 : ℝ) ^ B.rank =
      ∫ X, f X ∂finiteStageLaw old := by
  simp_rw [integral_cond_syndrome old B hold hnew]
  rw [← Finset.mul_sum, sum_setIntegral_syndromes B hf]
  exact mul_div_cancel_left₀ _ (by positivity)

/-- Some syndrome has objective no larger than the old expectation. The
computable minimizer attains at least this good a value. -/
theorem exists_integral_cond_syndrome_le {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support)
    {f : Cantor → ℝ} (hf : Integrable f (finiteStageLaw old)) :
    ∃ y : Fin B.rank → ZMod 2,
      (∫ X, f X ∂cond (finiteStageLaw old) (withSyndrome B y).event) ≤
        ∫ X, f X ∂finiteStageLaw old := by
  classical
  by_contra h
  push Not at h
  have hs := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin B.rank → ZMod 2)))
    (fun y _ => (h y).le) ⟨0, Finset.mem_univ _, h 0⟩
  have ha := average_integral_cond_syndrome old B hold hnew hf
  have hp : (0 : ℝ) < 2 ^ B.rank := by positivity
  have hc : Fintype.card (Fin B.rank → ZMod 2) = 2 ^ B.rank := by simp
  rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul] at hs
  have he := (div_eq_iff (ne_of_gt hp)).mp ha
  push_cast at hs
  nlinarith

end Klr.StageSyndrome

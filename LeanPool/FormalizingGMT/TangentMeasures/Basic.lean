/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Covering.Differentiation
public import LeanPool.FormalizingGMT.WeakConvergence.CompactnessCriterion
public import LeanPool.FormalizingGMT.Densities.Basic

/-!
# Basic definitions for tangent measures

This file defines blow-up maps, rescaled measures, tangent measures, and the basic facts used by
the Chapter 14 results.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Topology
open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}


/--
The blow-up map `T_{a,r}(x) = (x - a) / r` on Euclidean space `ℝⁿ`.
-/
def blowUpMap {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n))
    (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  r⁻¹ • (x - a)

lemma continuous_blowUpMap (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Continuous (blowUpMap a r) :=
  (continuous_id.sub continuous_const).const_smul r⁻¹

lemma measurable_blowUpMap (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Measurable (blowUpMap a r) :=
  (continuous_blowUpMap a r).measurable

/-- `IsTangentMeasure μ ν a` asserts that `ν` is a tangent measure of `μ` at the point `a`:
`ν` is a nonzero Radon measure which is the weak limit of a sequence of rescaled blow-ups of `μ`
at `a` along radii tending to `0`. -/
def IsTangentMeasure
    (μ ν : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : Prop :=
  ν.Regular ∧ ν ≠ 0 ∧
  ∃ (r : ℕ → ℝ) (c : ℕ → ℝ≥0∞),
    (∀ i, 0 < r i) ∧
    (∀ i, 0 < c i) ∧
    (∀ i, c i ≠ ∞) ∧
    Tendsto r atTop (𝓝 0) ∧
    Measure.WeaklyConverges
      (fun i ↦ c i • (μ.map (blowUpMap a (r i))))
      ν

/-! ## Elementary facts about weak convergence -/

namespace MeasureTheory

section WeakConvergenceFacts

variable {n : ℕ}

/-- Weak convergence is inherited by subsequences (more generally, by any reindexing along a
map tending to infinity). -/
lemma Measure.WeaklyConverges.comp
    {μ : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (h : Measure.WeaklyConverges μ ν) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    Measure.WeaklyConverges (fun j ↦ μ (φ j)) ν :=
  fun f ↦ (h f).comp hφ

/-- Rescaling a weakly convergent sequence by constants tending to `1` does not change the
weak limit. -/
lemma Measure.WeaklyConverges.smul_of_tendsto_one
    {μ : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (h : Measure.WeaklyConverges μ ν) {e : ℕ → ℝ≥0∞}
    (he1 : Tendsto (fun i ↦ (e i).toReal) atTop (𝓝 1)) :
    Measure.WeaklyConverges (fun i ↦ e i • μ i) ν := by
  intro f
  have hint : ∀ i, ∫ x, f x ∂(e i • μ i) = (e i).toReal * ∫ x, f x ∂(μ i) := by
    intro i
    rw [integral_smul_measure, smul_eq_mul]
  simp only [hint]
  simpa using he1.mul (h f)

/-- Weak convergence only depends on the underlying sequence of measures. -/
lemma Measure.WeaklyConverges.congr_seq
    {F G : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hFG : ∀ i, F i = G i)
    (h : Measure.WeaklyConverges G ν) :
    Measure.WeaklyConverges F ν := by
  rw [funext hFG]
  exact h

end WeakConvergenceFacts

end MeasureTheory

/-! ## Extracting a strictly decreasing sequence of radii -/

/-- A positive sequence tending to `0` has a strictly decreasing subsequence. -/
lemma exists_strictMono_strictAnti_subseq {r : ℕ → ℝ} (hpos : ∀ i, 0 < r i)
    (hr : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (fun j ↦ r (φ j)) := by
  have hstep : ∀ m : ℕ, ∃ k, m < k ∧ r k < r m := by
    intro m
    have h1 : ∀ᶠ k in atTop, r k < r m := hr.eventually_lt_const (hpos m)
    have h2 : ∀ᶠ k in atTop, m < k := eventually_gt_atTop m
    exact (h2.and h1).exists
  choose next hnext1 hnext2 using hstep
  refine ⟨fun j ↦ Nat.rec 0 (fun _ m ↦ next m) j, strictMono_nat_of_lt_succ (fun j ↦ ?_),
    strictAnti_nat_of_succ_lt (fun j ↦ ?_)⟩
  · exact hnext1 _
  · exact hnext2 _

/-! ## Basic properties of the blow-up maps -/

section BlowUp

variable {n : ℕ}

lemma blowUpMap_preimage_ball (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    blowUpMap a r ⁻¹' (ball 0 ρ) = ball a (r * ρ) := by
  ext x
  simp only [blowUpMap, mem_preimage, mem_ball, dist_eq_norm]
  rw [sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_lt_iff₀ hr]

lemma blowUpMap_preimage_closedBall (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (ρ : ℝ) :
    blowUpMap a r ⁻¹' (closedBall 0 ρ) = closedBall a (r * ρ) := by
  ext x
  simp only [blowUpMap, mem_preimage, mem_closedBall, dist_eq_norm]
  rw [sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_le_iff₀ hr]

/-- The blow-up map as a homeomorphism of Euclidean space. -/
def blowUpHomeomorph (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.subRight a).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))

/-- The push-forward of a Radon measure under a blow-up map is a Radon measure. -/
lemma regular_map_blowUp {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    (μ.map (blowUpMap a r)).Regular := by
  let _ : μ.Regular := hμ
  have hmap : μ.map (blowUpMap a r) = μ.map ⇑(blowUpHomeomorph a hr) := rfl
  rw [hmap]
  exact Measure.Regular.map (blowUpHomeomorph a hr)

/-- A finite rescaling of the push-forward of a Radon measure under a blow-up map is again a
Radon measure. -/
lemma regular_smul_map_blowUp {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) {c : ℝ≥0∞}
    (hc : c ≠ ∞) :
    (c • μ.map (blowUpMap a r)).Regular := by
  let _ : (μ.map (blowUpMap a r)).Regular := regular_map_blowUp hμ a hr
  exact Measure.Regular.smul hc

lemma map_blowUp_apply_ball (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    (μ.map (blowUpMap a r)) (ball 0 ρ) = μ (ball a (r * ρ)) := by
  rw [Measure.map_apply (measurable_blowUpMap a r) measurableSet_ball,
    blowUpMap_preimage_ball a hr]

lemma map_blowUp_apply_closedBall (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    (μ.map (blowUpMap a r)) (closedBall 0 ρ) = μ (closedBall a (r * ρ)) := by
  rw [Measure.map_apply (measurable_blowUpMap a r) measurableSet_closedBall,
    blowUpMap_preimage_closedBall a hr]

end BlowUp

/-! ## Balls of positive and finite measure -/

section Balls

variable {n : ℕ}

lemma measure_ball_pos_of_mem_support {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ μ.support) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < μ (ball a ρ) :=
  (Measure.mem_support_iff_forall a).mp ha _ (ball_mem_nhds a hρ)

lemma regular_measure_closedBall_lt_top {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    μ (closedBall a ρ) < ∞ := by
  let _ : μ.Regular := hμ
  exact (isCompact_closedBall a ρ).measure_lt_top

lemma regular_measure_ball_lt_top {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    μ (ball a ρ) < ∞ :=
  lt_of_le_of_lt (measure_mono ball_subset_closedBall)
    (regular_measure_closedBall_lt_top hμ a ρ)

end Balls

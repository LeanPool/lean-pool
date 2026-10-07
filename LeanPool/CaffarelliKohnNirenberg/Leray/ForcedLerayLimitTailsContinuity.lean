/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHilbertEnergyBridge

/-!
# Continuity of weighted kinetic energies

In the proof of `lem:forced-tails` the localized energy inequality is passed
to the endpoints of a time interval using the continuity of
t ↦ ∫ |u(x,t)|² q(x) dx for a bounded weight q. For a velocity whose
slices form a continuous curve in L² (as in `lem:regularised-forced`) this
follows from |∫ (|a|² - |b|²) q| ≤ ‖a - b‖₂ ‖q (a + b)‖₂.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The difference of two weighted kinetic energies is bounded by the L²
distance of the fields times the L² norm of the weighted sum. -/
private theorem forcedTailsCont_difference_le {a b : Vec3 → Vec3}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) {q : Vec3 → ℝ} (hq : Measurable q)
    {C : ℝ} (hqC : ∀ x, |q x| ≤ C) :
    |(∫ x : Vec3, vec3EuclideanNorm (a x) ^ (2 : ℕ) * q x) -
        ∫ x : Vec3, vec3EuclideanNorm (b x) ^ (2 : ℕ) * q x| ≤
      ‖realVectorL2OfCoordinateFunction a ha - realVectorL2OfCoordinateFunction b hb‖ *
        Real.sqrt (2 * C ^ 2 *
          (‖realVectorL2OfCoordinateFunction a ha‖ ^ 2 +
            ‖realVectorL2OfCoordinateFunction b hb‖ ^ 2)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hqC 0)
  have forcedTailsCont_norm_sq : ∀ v : Vec3,
      vec3EuclideanNorm v ^ (2 : ℕ) = ∑ i : Fin 3, v i ^ 2 := fun v => by
    rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  let g : Vec3 → Vec3 := fun x i => q x * (a x i + b x i)
  have hgi : ∀ i, MemLp (fun x => g x i) 2 volume := by
    intro i
    have hs : MemLp (fun x => C * (a x i + b x i)) 2 volume :=
      ((ha.eval i).add (hb.eval i)).const_mul C
    refine hs.of_le ((hq.aestronglyMeasurable).mul
      ((ha.eval i).add (hb.eval i)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    simp only [g, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right (hqC x) (abs_nonneg _)
  have hg : MemLp g 2 volume := memLp_pi_iff.2 hgi
  have hWa := inner_realVectorL2OfCoordinateFunction
    (realVectorL2OfCoordinateFunction_rep a ha).symm g hg
  have hWb := inner_realVectorL2OfCoordinateFunction
    (realVectorL2OfCoordinateFunction_rep b hb).symm g hg
  have hga : ∀ i, Integrable (fun x => g x i * a x i) := fun i =>
    (hgi i).integrable_mul (ha.eval i)
  have hgb : ∀ i, Integrable (fun x => g x i * b x i) := fun i =>
    (hgi i).integrable_mul (hb.eval i)
  have hqa : Integrable (fun x => vec3EuclideanNorm (a x) ^ (2 : ℕ) * q x) := by
    have h : Integrable (fun x => ∑ i : Fin 3, (g x i * a x i - q x * (b x i * a x i))) :=
      integrable_finsetSum _ fun i _ => (hga i).sub
        (((hb.eval i).integrable_mul (ha.eval i)).bdd_mul hq.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hqC x))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [g, forcedTailsCont_norm_sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hqb : Integrable (fun x => vec3EuclideanNorm (b x) ^ (2 : ℕ) * q x) := by
    have h : Integrable (fun x => ∑ i : Fin 3, (g x i * b x i - q x * (a x i * b x i))) :=
      integrable_finsetSum _ fun i _ => (hgb i).sub
        (((ha.eval i).integrable_mul (hb.eval i)).bdd_mul hq.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hqC x))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [g, forcedTailsCont_norm_sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hid : (∫ x : Vec3, vec3EuclideanNorm (a x) ^ (2 : ℕ) * q x) -
      ∫ x : Vec3, vec3EuclideanNorm (b x) ^ (2 : ℕ) * q x =
      inner ℝ (realVectorL2OfCoordinateFunction a ha - realVectorL2OfCoordinateFunction b hb)
        (realVectorL2OfCoordinateFunction g hg) := by
    rw [inner_sub_left, hWa, hWb, ← integral_sub hqa hqb,
      ← integral_sub (integrable_finsetSum _ fun i _ => hga i)
        (integrable_finsetSum _ fun i _ => hgb i)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [g, forcedTailsCont_norm_sq, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hgnorm : ‖realVectorL2OfCoordinateFunction g hg‖ ^ 2 ≤
      2 * C ^ 2 * (‖realVectorL2OfCoordinateFunction a ha‖ ^ 2 +
        ‖realVectorL2OfCoordinateFunction b hb‖ ^ 2) := by
    rw [realVectorL2OfCoordinateFunction_norm_sq, realVectorL2OfCoordinateFunction_norm_sq,
      realVectorL2OfCoordinateFunction_norm_sq, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (((ha.eval i).integrable_sq).const_mul _)
        (((hb.eval i).integrable_sq).const_mul _)]
    refine integral_mono (hgi i).integrable_sq
      ((((ha.eval i).integrable_sq).const_mul _).add (((hb.eval i).integrable_sq).const_mul _))
      fun x => ?_
    have hq2 : q x ^ 2 ≤ C ^ 2 := by
      have h := hqC x
      nlinarith only [h, abs_nonneg (q x), sq_abs (q x)]
    simp only [g]
    nlinarith only [hq2, sq_nonneg (a x i + b x i), sq_nonneg (a x i - b x i), sq_nonneg (q x)]
  rw [hid]
  refine (abs_real_inner_le_norm _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Real.le_sqrt_of_sq_le hgnorm

/-- The weighted kinetic energy t ↦ ∫ |u(x,t)|² q(x) dx of a velocity whose
slices form a continuous curve in L² is continuous on [0,∞) for every
bounded measurable weight q (`lem:forced-tails`). -/
theorem forcedTails_weightedEnergy_continuousOn (u : ParabolicPoint → Vec3)
    (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : Continuous (fun t : Set.Ici (0 : ℝ) =>
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)))
    {q : Vec3 → ℝ} (hq : Measurable q) {C : ℝ} (hqC : ∀ x, |q x| ≤ C) :
    ContinuousOn (fun τ => ∫ x : Vec3, vec3EuclideanNorm (u (x, τ)) ^ (2 : ℕ) * q x)
      (Ici 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let W : Set.Ici (0 : ℝ) → RealVectorL2 := fun t =>
    realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)
  let Y : Set.Ici (0 : ℝ) → ℝ := fun t =>
    ∫ x : Vec3, vec3EuclideanNorm (u (x, t.1)) ^ (2 : ℕ) * q x
  change Continuous Y
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hbound : ∀ t, |Y t - Y t₀| ≤ ‖W t - W t₀‖ *
      Real.sqrt (2 * C ^ 2 * (‖W t‖ ^ 2 + ‖W t₀‖ ^ 2)) := fun t =>
    forcedTailsCont_difference_le (hSlice t.1 t.2) (hSlice t₀.1 t₀.2) hq hqC
  have hlim : Tendsto (fun t => ‖W t - W t₀‖ *
      Real.sqrt (2 * C ^ 2 * (‖W t‖ ^ 2 + ‖W t₀‖ ^ 2))) (𝓝 t₀) (𝓝 0) := by
    have h1 : Tendsto (fun t => ‖W t - W t₀‖) (𝓝 t₀) (𝓝 0) := by
      have := ((hcont.tendsto t₀).sub_const (W t₀)).norm
      rw [sub_self, norm_zero] at this
      exact this
    have h2 : Tendsto (fun t => Real.sqrt (2 * C ^ 2 * (‖W t‖ ^ 2 + ‖W t₀‖ ^ 2))) (𝓝 t₀)
        (𝓝 (Real.sqrt (2 * C ^ 2 * (‖W t₀‖ ^ 2 + ‖W t₀‖ ^ 2)))) :=
      ((((hcont.tendsto t₀).norm.pow 2).add_const _).const_mul _).sqrt
    simpa using h1.mul h2
  have habs : Tendsto (fun t => |Y t - Y t₀|) (𝓝 t₀) (𝓝 0) :=
    squeeze_zero (fun t => abs_nonneg _) hbound hlim
  have : Tendsto (fun t => Y t - Y t₀) (𝓝 t₀) (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have h := this.add_const (Y t₀)
  simp only [sub_add_cancel, zero_add] at h
  exact h

end CKN.Leray

end

/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import LeanPool.FormalizingGMT.TangentMeasures.Basic

/-!
# Density and ball bounds for Mattila's Lemma 14.7

This file develops the quantitative density and ball-measure estimates used in Lemma 14.7.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Topology
open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-! ## Densities -/
/-- For a measure on Euclidean space, the upper `s`-density `dimensionalUpperDensity`
(from `DensitiesBasic`) is the `limsup` as `r ↓ 0` of `μ (closedBall a r) / (2 r) ^ s`. -/
lemma dimensional_upper_density_toOuterMeasure_eq {n : ℕ} (s : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) :
    dimensionalUpperDensity μ.toOuterMeasure s a =
      limsup (fun r : ℝ ↦ μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s)) (𝓝[>] (0 : ℝ)) := by
  refine limsup_congr ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [dimensional_density_ratio_closedBall _ _ _ (le_of_lt (Set.mem_Ioi.mp hr))]
  rfl
/-- For a measure on Euclidean space, the lower `s`-density `dimensionalLowerDensity`
(from `DensitiesBasic`) is the `liminf` as `r ↓ 0` of `μ (closedBall a r) / (2 r) ^ s`. -/
lemma dimensional_lower_density_toOuterMeasure_eq {n : ℕ} (s : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) :
    dimensionalLowerDensity μ.toOuterMeasure s a =
      liminf (fun r : ℝ ↦ μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s)) (𝓝[>] (0 : ℝ)) := by
  refine liminf_congr ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [dimensional_density_ratio_closedBall _ _ _ (le_of_lt (Set.mem_Ioi.mp hr))]
  rfl
/-- The set `A` of Mattila, Lemma 14.7: the points `a` at which
`0 < Θ^s_*(μ, a) ≤ Θ^{*s}(μ, a) < ∞`. -/
def positiveFiniteDensitySet {n : ℕ} (s : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {a | 0 < dimensionalLowerDensity μ.toOuterMeasure s a ∧
    dimensionalLowerDensity μ.toOuterMeasure s a ≤
      dimensionalUpperDensity μ.toOuterMeasure s a ∧
    dimensionalUpperDensity μ.toOuterMeasure s a < ∞}
/-- The density ratio `t (a) = Θ^s_*(μ, a) / Θ^{*s}(μ, a)` of Mattila, Lemma 14.7: the lower
`s`-dimensional density of `μ` at `a` divided by the upper one. -/
noncomputable def RatioOfDensities {n : ℕ} (s : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  dimensionalLowerDensity μ.toOuterMeasure s a / dimensionalUpperDensity μ.toOuterMeasure s a
/-- The quantity `limsup_{δ ↓ 0} sup {d (B) ^ (-s) μ (B) : B a closed ball with z ∈ B and
d (B) < δ}` appearing in the hypothesis of Mattila, Lemma 14.7 (2). Here `d (B) = 2 ρ` is the
diameter of the ball `B = B (y, ρ)`. -/
def upperBallSDensity {n : ℕ} (s : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  limsup (fun δ : ℝ ↦ ⨆ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (_ : 0 < ρ) (_ : 2 * ρ < δ)
      (_ : z ∈ closedBall y ρ), μ (closedBall y ρ) / ENNReal.ofReal ((2 * ρ) ^ s))
    (𝓝[>] (0 : ℝ))
/-! ## Supports -/
/-- A set all of whose points lie outside the support of `μ` is `μ`-null.
(Second countability of the space is what makes the usual Lindelöf argument work.) -/
lemma measure_eq_zero_of_disjoint_support {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] {μ : Measure X} {V : Set X}
    (h : ∀ y ∈ V, y ∉ Measure.support μ) : μ V = 0 :=
  measure_mono_null (fun y hy ↦ h y hy) μ.measure_compl_support
/-- An open set of positive measure contains a point of the support. -/
lemma exists_mem_support_of_measure_pos {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] {μ : Measure X} {V : Set X}
    (h : 0 < μ V) : ∃ y ∈ V, y ∈ Measure.support μ := by
  by_contra hcon
  push Not at hcon
  exact h.ne' (measure_eq_zero_of_disjoint_support hcon)
/-! ## Blow-ups of balls with arbitrary centres -/
variable {n : ℕ}
lemma blowUpMap_preimage_ball' (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    blowUpMap a r ⁻¹' (ball x ρ) = ball (a + r • x) (r * ρ) := by
  ext y
  have hx : r⁻¹ • (r • x) = x := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hkey : r⁻¹ • (y - a) - x = r⁻¹ • (y - (a + r • x)) := by
    simp only [smul_sub, smul_add, hx]
    abel
  simp only [blowUpMap, mem_preimage, mem_ball, dist_eq_norm, hkey, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos hr]
  rw [inv_mul_lt_iff₀ hr]
lemma blowUpMap_preimage_closedBall' (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (ρ : ℝ) :
    blowUpMap a r ⁻¹' (closedBall x ρ) = closedBall (a + r • x) (r * ρ) := by
  ext y
  have hx : r⁻¹ • (r • x) = x := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hkey : r⁻¹ • (y - a) - x = r⁻¹ • (y - (a + r • x)) := by
    simp only [smul_sub, smul_add, hx]
    abel
  simp only [blowUpMap, mem_preimage, mem_closedBall, dist_eq_norm, hkey, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos hr]
  rw [inv_mul_le_iff₀ hr]
lemma blowUp_smul_apply_ball (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) (ρ : ℝ) :
    (c • Measure.map (blowUpMap a r) μ) (ball x ρ) = c * μ (ball (a + r • x) (r * ρ)) := by
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_blowUpMap a r) measurableSet_ball,
    blowUpMap_preimage_ball' a x hr ρ]
lemma blowUp_smul_apply_closedBall (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) (ρ : ℝ) :
    (c • Measure.map (blowUpMap a r) μ) (closedBall x ρ)
      = c * μ (closedBall (a + r • x) (r * ρ)) := by
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_blowUpMap a r) measurableSet_closedBall,
    blowUpMap_preimage_closedBall' a x hr ρ]



variable {n : ℕ}
namespace MattilaSupportGrowth
/-- Fubini bound: the integral over `x ∈ B (x₀, R)` of `ν (B (x, r))` is at most `r ^ n` times
the volume of the unit ball times `ν (B (x₀, R + r))`. -/
lemma lintegral_measure_closedBall_le (ν : Measure (EuclideanSpace ℝ (Fin n))) [SFinite ν]
    (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) {r : ℝ} (hr0 : 0 < r) :
    ∫⁻ x in closedBall x₀ R, ν (closedBall x r) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      ≤ ENNReal.ofReal (r ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ν (closedBall x₀ (R + r)) := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {q | dist q.1 q.2 ≤ r} with hSdef
  have hS : MeasurableSet S := (isClosed_le (by fun_prop) continuous_const).measurableSet
  set f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x y ↦ S.indicator 1 (x, y) with hfdef
  have hfmeas : Measurable (Function.uncurry f) := by
    have : Function.uncurry f =
        S.indicator (1 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞) := by
      funext p; simp [hfdef, Function.uncurry]
    rw [this]
    exact (measurable_one).indicator hS
  -- the inner integral in `y` recovers the measure of a ball
  have hinner : ∀ x : EuclideanSpace ℝ (Fin n), ∫⁻ y, f x y ∂ν = ν (closedBall x r) := by
    intro x
    have hfun : (fun y ↦ f x y) =
        (closedBall x r).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) := by
      funext y
      by_cases hy : y ∈ closedBall x r
      · have hxy : (x, y) ∈ S := by
          simpa [hSdef, dist_comm] using (mem_closedBall.mp hy)
        simp [hfdef, hy, hxy]
      · have hxy : (x, y) ∉ S := by
          simpa [hSdef, dist_comm, mem_closedBall] using hy
        simp [hfdef, hy, hxy]
    rw [hfun, lintegral_indicator measurableSet_closedBall]
    simp
  -- the inner integral in `x`
  have houter : ∀ y : EuclideanSpace ℝ (Fin n), ∫⁻ x in closedBall x₀ R, f x y ∂volume
      ≤ (closedBall x₀ (R + r)).indicator
        (fun _ ↦ ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) y := by
    intro y
    have hfun : (fun x ↦ f x y) =
        (closedBall y r).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ closedBall y r
      · have hxy : (x, y) ∈ S := by
          simpa [hSdef] using (mem_closedBall.mp hx)
        simp [hfdef, hx, hxy]
      · have hxy : (x, y) ∉ S := by
          simpa [hSdef, mem_closedBall] using hx
        simp [hfdef, hx, hxy]
    by_cases hy : y ∈ closedBall x₀ (R + r)
    · have hle : ∫⁻ x in closedBall x₀ R, f x y ∂volume
          ≤ ∫⁻ x, f x y ∂volume := setLIntegral_le_lintegral _ _
      have hval : ∫⁻ x, f x y ∂volume = volume (closedBall y r) := by
        rw [hfun, lintegral_indicator measurableSet_closedBall]
        simp
      have hball : volume (closedBall y r)
          = ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
        have h := Measure.addHaar_closedBall (volume : Measure (EuclideanSpace ℝ (Fin n))) y hr0.le
        rw [hfr] at h
        simpa using h
      simp only [hy, indicator_of_mem]
      rw [hval, hball] at hle
      exact hle
    · have hzero : ∫⁻ x in closedBall x₀ R, f x y ∂volume = 0 := by
        refine setLIntegral_eq_zero measurableSet_closedBall ?_
        intro x hx
        have hxy : (x, y) ∉ S := by
          simp only [hSdef, mem_ofPred_eq, not_le]
          have h1 : dist x x₀ ≤ R := mem_closedBall.mp hx
          have h2 : R + r < dist y x₀ := by
            simpa [mem_closedBall, not_le] using hy
          have h3 := dist_triangle y x x₀
          rw [dist_comm x y]
          linarith
        simp [hfdef, hxy]
      simp [hzero]
  -- combine via Fubini
  have hswap : ∫⁻ x, ∫⁻ y, f x y ∂ν ∂(volume.restrict (closedBall x₀ R))
      = ∫⁻ y, ∫⁻ x in closedBall x₀ R, f x y ∂volume ∂ν :=
    lintegral_lintegral_swap hfmeas.aemeasurable
  calc ∫⁻ x in closedBall x₀ R, ν (closedBall x r) ∂volume
      = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂(volume.restrict (closedBall x₀ R)) := by
        simp only [hinner]
    _ = ∫⁻ y, ∫⁻ x in closedBall x₀ R, f x y ∂volume ∂ν := hswap
    _ ≤ ∫⁻ y, (closedBall x₀ (R + r)).indicator
          (fun _ ↦ ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) y ∂ν :=
        lintegral_mono houter
    _ = ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        ν (closedBall x₀ (R + r)) := by
        rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
/-- A locally finite Borel measure on `ℝⁿ` cannot satisfy a uniform lower bound
`c ρ ^ s ≤ ν (B (x, ρ))` at every point when `s < n` and `c > 0`. -/
theorem no_uniform_lower_bound_of_lt_dim {s : ℝ} (hsn : s < n)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts ν]
    {c : ℝ≥0∞} (hc : 0 < c)
    (hlow : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r < 1 →
      c * ENNReal.ofReal (r ^ s) ≤ ν (closedBall x r)) :
    False := by
  set E := EuclideanSpace ℝ (Fin n)
  set V : ℝ≥0∞ := volume (ball (0 : E) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ∞ := measure_ball_lt_top.ne
  have hVclosed : volume (closedBall (0 : E) 1) = V := by
    have := Measure.addHaar_closedBall (volume : Measure E) (0 : E) (zero_le_one)
    simpa [hV] using this
  set K : ℝ≥0∞ := ν (closedBall (0 : E) 2) with hK
  have hKtop : K ≠ ∞ := (isCompact_closedBall _ _).measure_lt_top.ne
  -- the key inequality at every scale
  have hkey : ∀ r : ℝ, 0 < r → r < 1 → c ≤ ENNReal.ofReal (r ^ (n - s)) * K := by
    intro r hr0 hr1
    have hlower : c * ENNReal.ofReal (r ^ s) * V
        ≤ ∫⁻ x in closedBall (0 : E) 1, ν (closedBall x r) ∂volume := by
      calc c * ENNReal.ofReal (r ^ s) * V
          = ∫⁻ _ in closedBall (0 : E) 1, c * ENNReal.ofReal (r ^ s) ∂volume := by
            rw [setLIntegral_const, hVclosed]
        _ ≤ _ := lintegral_mono fun x ↦ hlow x r hr0 hr1
    have hupper : ∫⁻ x in closedBall (0 : E) 1, ν (closedBall x r) ∂volume
        ≤ ENNReal.ofReal (r ^ n) * volume (ball (0 : E) 1) * K := by
      refine (lintegral_measure_closedBall_le ν 0 1 hr0).trans ?_
      gcongr
      exact measure_mono (closedBall_subset_closedBall (by linarith))
    have hcomb : c * ENNReal.ofReal (r ^ s) * V ≤ ENNReal.ofReal (r ^ n) * V * K :=
      hlower.trans hupper
    -- rearrange so that the volume factor can be cancelled
    have hcomb' : (c * ENNReal.ofReal (r ^ s)) * V ≤ (ENNReal.ofReal (r ^ n) * K) * V := by
      calc (c * ENNReal.ofReal (r ^ s)) * V ≤ ENNReal.ofReal (r ^ n) * V * K := hcomb
        _ = (ENNReal.ofReal (r ^ n) * K) * V := by ring
    have hcancel : c * ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (r ^ n) * K :=
      (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp hcomb'
    -- split `r ^ n = r ^ s * r ^ (n - s)`
    have hsplit : ENNReal.ofReal (r ^ n) =
        ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ (n - s)) := by
      have hreal : (r : ℝ) ^ n = r ^ s * r ^ (n - s) := by
        rw [← Real.rpow_add hr0]
        rw [show s + ((n : ℝ) - s) = (n : ℝ) by ring, Real.rpow_natCast]
      rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le s)]
    have hpow0 : ENNReal.ofReal (r ^ s) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, Real.rpow_pos_of_pos hr0 s]
    have hpowtop : ENNReal.ofReal (r ^ s) ≠ ∞ := ENNReal.ofReal_ne_top
    have : c * ENNReal.ofReal (r ^ s)
        ≤ (ENNReal.ofReal (r ^ (n - s)) * K) * ENNReal.ofReal (r ^ s) := by
      calc c * ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (r ^ n) * K := hcancel
        _ = (ENNReal.ofReal (r ^ (n - s)) * K) * ENNReal.ofReal (r ^ s) := by
            rw [hsplit]; ring
    exact (ENNReal.mul_le_mul_iff_left hpow0 hpowtop).mp this
  -- let the radius tend to `0`
  have hexp : (0 : ℝ) < (n : ℝ) - s := by linarith
  set ρ : ℕ → ℝ := fun k ↦ 1 / (k + 2) with hρ
  have hρ0 : ∀ k, 0 < ρ k := by
    intro k
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    simpa [hρ] using this
  have hρ1 : ∀ k, ρ k < 1 := by
    intro k
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [hρ, div_lt_one (by linarith)]
    exact hk
  have hρtend : Tendsto ρ atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    rw [hρ]
    convert h2.inv_tendsto_atTop using 1
    funext k
    simp only [one_div, Pi.inv_apply]
  have hpowtend : Tendsto (fun k ↦ ENNReal.ofReal (ρ k ^ ((n : ℝ) - s)) * K) atTop (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ x ^ ((n : ℝ) - s)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)
    have h1 : Tendsto (fun k ↦ ρ k ^ ((n : ℝ) - s)) atTop (𝓝 ((0 : ℝ) ^ ((n : ℝ) - s))) :=
      hcont.tendsto.comp hρtend
    rw [Real.zero_rpow hexp.ne'] at h1
    have h2 : Tendsto (fun k ↦ ENNReal.ofReal (ρ k ^ ((n : ℝ) - s))) atTop (𝓝 0) := by
      convert (ENNReal.continuous_ofReal.tendsto 0).comp h1 using 1
      · funext k
        rfl
      · simp
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hKtop)
  have hle : c ≤ 0 :=
    ge_of_tendsto' hpowtend fun k ↦ hkey (ρ k) (hρ0 k) (hρ1 k)
  exact absurd (le_antisymm hle (by exact bot_le)) hc.ne'
end MattilaSupportGrowth
/-- **The support of a measure with `s`-dimensional lower growth, `s < n`, is not everything.**
If `ν` is a Radon measure (a regular Borel measure) on `ℝⁿ` and there is `c > 0` with
`c ρ ^ s ≤ ν (B (x, ρ))` for every `x ∈ spt ν` and every `ρ > 0`, and if `s < n`, then
`spt ν ≠ ℝⁿ`.  This is the step of Mattila's proof of Lemma 14.7 (3) which produces a point
outside the support of the tangent measure supplied by part (1). -/
theorem support_ne_univ_of_lower_growth {s : ℝ} (hsn : s < n)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (hν : Measure.Regular ν)
    {c : ℝ≥0∞} (hc : 0 < c)
    (hlow : ∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
      c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) :
    Measure.support ν ≠ (univ : Set (EuclideanSpace ℝ (Fin n))) := by
  intro hfull
  let _ : ν.Regular := hν
  refine MattilaSupportGrowth.no_uniform_lower_bound_of_lt_dim hsn ν hc ?_
  intro x r hr0 _
  exact hlow x (by rw [hfull]; trivial) r hr0


variable {n : ℕ}
/-- **Holes at every scale.**
If `s < n` and the measures of the balls centred on `F` of radius `ρ < r₀` are between
`p ρ ^ s` and `q ρ ^ s`, then there is `κ > 0` such that every ball `B (x, δ)` with `x ∈ F` and
`δ < r₀ / 2` contains a point at distance more than `κ δ` from `F`. -/
theorem exists_hole_of_ball_bounds {s p q r₀ : ℝ} (hsn : s < n) (hp : 0 < p) (hq : 0 < q)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    {F : Set (EuclideanSpace ℝ (Fin n))}
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ)) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ x ∈ F, ∀ δ : ℝ, 0 < δ → δ < r₀ / 2 →
      ∃ z, dist z x ≤ δ ∧ κ * δ < infDist z F := by
  have hexp : (0 : ℝ) < (n : ℝ) - s := by linarith
  set C : ℝ := (3 : ℝ) ^ (n : ℕ) * q * (2 : ℝ) ^ s with hC
  have hCpos : 0 < C := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (n : ℕ) := by positivity
    rw [hC]; positivity
  set κ₀ : ℝ := (p / (2 * C)) ^ (1 / ((n : ℝ) - s)) with hκ₀
  have hpC : 0 < p / (2 * C) := by positivity
  have hκ₀pos : 0 < κ₀ := Real.rpow_pos_of_pos hpC _
  set κ : ℝ := min (1 / 3) κ₀ with hκdef
  have hκpos : 0 < κ := lt_min (by norm_num) hκ₀pos
  have hκ3 : κ ≤ 1 / 3 := min_le_left _ _
  have hκ1 : κ < 1 := lt_of_le_of_lt hκ3 (by norm_num)
  have hkey : C * κ ^ ((n : ℝ) - s) < p := by
    have h0 : κ₀ ^ ((n : ℝ) - s) = p / (2 * C) := by
      rw [hκ₀, ← Real.rpow_mul hpC.le, one_div, inv_mul_cancel₀ hexp.ne', Real.rpow_one]
    have h1 : κ ^ ((n : ℝ) - s) ≤ κ₀ ^ ((n : ℝ) - s) :=
      Real.rpow_le_rpow hκpos.le (min_le_right _ _) hexp.le
    calc C * κ ^ ((n : ℝ) - s) ≤ C * (p / (2 * C)) := by rw [← h0]; gcongr
      _ = p / 2 := by field_simp
      _ < p := by linarith
  refine ⟨κ, hκpos, hκ1, ?_⟩
  intro x hxF δ hδ hδr
  by_contra hcon
  push Not at hcon
  -- the associated Borel measure
  let _ : μ.Regular := hμ
  have hr₀ : 0 < r₀ := by linarith
  have hκδ : 0 < κ * δ := by positivity
  have hκδr : κ * δ < r₀ := by nlinarith
  -- a uniform lower bound for the measures of the balls `B (z, 3 κ δ)`, `z ∈ B (x, δ)`
  have hz : ∀ z ∈ closedBall x δ,
      ENNReal.ofReal (p * (κ * δ) ^ s) ≤ μ (closedBall z (3 * (κ * δ))) := by
    intro z hzmem
    have h1 : infDist z F ≤ κ * δ := hcon z (mem_closedBall.mp hzmem)
    have h2 : infDist z F < 2 * (κ * δ) := lt_of_le_of_lt h1 (by linarith)
    obtain ⟨y, hyF, hdy⟩ := (Metric.infDist_lt_iff ⟨x, hxF⟩).mp h2
    have hsub : closedBall y (κ * δ) ⊆ closedBall z (3 * (κ * δ)) := by
      intro w hw
      have h3 : dist w y ≤ κ * δ := mem_closedBall.mp hw
      have h4 : dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      rw [mem_closedBall]
      rw [dist_comm y z] at h4
      linarith
    calc ENNReal.ofReal (p * (κ * δ) ^ s) ≤ μ (closedBall y (κ * δ)) :=
          hlower y hyF _ hκδ hκδr
      _ = μ (closedBall y (κ * δ)) := rfl
      _ ≤ μ (closedBall z (3 * (κ * δ))) := measure_mono hsub
  -- Fubini
  set V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ∞ := measure_ball_lt_top.ne
  have hvol : volume (closedBall x δ) = ENNReal.ofReal (δ ^ (n : ℕ)) * V := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    have h := Measure.addHaar_closedBall
      (volume : Measure (EuclideanSpace ℝ (Fin n))) x hδ.le
    rw [hfr] at h
    simpa [hV] using h
  have hint1 : ENNReal.ofReal (p * (κ * δ) ^ s) * volume (closedBall x δ)
      ≤ ∫⁻ z in closedBall x δ, μ (closedBall z (3 * (κ * δ))) ∂volume := by
    calc ENNReal.ofReal (p * (κ * δ) ^ s) * volume (closedBall x δ)
        = ∫⁻ _ in closedBall x δ, ENNReal.ofReal (p * (κ * δ) ^ s) ∂volume := by
          rw [setLIntegral_const]
      _ ≤ _ := setLIntegral_mono' measurableSet_closedBall hz
  have hint2 := MattilaSupportGrowth.lintegral_measure_closedBall_le μ x δ
    (show (0 : ℝ) < 3 * (κ * δ) by positivity)
  have hball2 : μ (closedBall x (δ + 3 * (κ * δ))) ≤ ENNReal.ofReal (q * (2 * δ) ^ s) := by
    calc μ (closedBall x (δ + 3 * (κ * δ))) ≤ μ (closedBall x (2 * δ)) := by
          refine measure_mono (closedBall_subset_closedBall ?_)
          nlinarith
      _ = μ (closedBall x (2 * δ)) := rfl
      _ ≤ ENNReal.ofReal (q * (2 * δ) ^ s) := hupper x hxF _ (by linarith) (by linarith)
  -- put the pieces together
  have hchain : ENNReal.ofReal (p * (κ * δ) ^ s) * (ENNReal.ofReal (δ ^ (n : ℕ)) * V)
      ≤ ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ)) * V * ENNReal.ofReal (q * (2 * δ) ^ s) := by
    rw [← hvol]
    exact hint1.trans (hint2.trans (by gcongr))
  have hreal : p * (κ * δ) ^ s * δ ^ (n : ℕ)
      ≤ (3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s) := by
    have hA : (0 : ℝ) ≤ p * (κ * δ) ^ s * δ ^ (n : ℕ) := by positivity
    have hB : (0 : ℝ) ≤ (3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s) := by positivity
    have h1 : ENNReal.ofReal (p * (κ * δ) ^ s * δ ^ (n : ℕ)) * V
        ≤ ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s)) * V := by
      calc ENNReal.ofReal (p * (κ * δ) ^ s * δ ^ (n : ℕ)) * V
          = ENNReal.ofReal (p * (κ * δ) ^ s) * (ENNReal.ofReal (δ ^ (n : ℕ)) * V) := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ p * (κ * δ) ^ s)]; ring
        _ ≤ ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ)) * V * ENNReal.ofReal (q * (2 * δ) ^ s) :=
            hchain
        _ = ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s)) * V := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 * (κ * δ)) ^ (n : ℕ))]; ring
    have h2 := (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp h1
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp h2
  -- and derive the contradiction with the choice of `κ`
  have hpow : (κ * δ) ^ s = κ ^ s * δ ^ s := Real.mul_rpow hκpos.le hδ.le
  have hpow2 : (2 * δ) ^ s = (2 : ℝ) ^ s * δ ^ s :=
    Real.mul_rpow (by norm_num) hδ.le
  have hpow3 : (3 * (κ * δ)) ^ (n : ℕ) = (3 : ℝ) ^ (n : ℕ) * κ ^ (n : ℕ) * δ ^ (n : ℕ) := by
    ring
  rw [hpow, hpow2, hpow3] at hreal
  have hδs : (0 : ℝ) < δ ^ s := Real.rpow_pos_of_pos hδ s
  have hδn : (0 : ℝ) < δ ^ (n : ℕ) := by positivity
  have hcancel : p * κ ^ s ≤ C * κ ^ (n : ℕ) := by
    have hpos : (0 : ℝ) < δ ^ s * δ ^ (n : ℕ) := by positivity
    rw [hC]
    refine le_of_mul_le_mul_right ?_ hpos
    calc (p * κ ^ s) * (δ ^ s * δ ^ (n : ℕ)) = p * (κ ^ s * δ ^ s) * δ ^ (n : ℕ) := by ring
      _ ≤ (3 : ℝ) ^ (n : ℕ) * κ ^ (n : ℕ) * δ ^ (n : ℕ) * (q * ((2 : ℝ) ^ s * δ ^ s)) := hreal
      _ = ((3 : ℝ) ^ (n : ℕ) * q * (2 : ℝ) ^ s * κ ^ (n : ℕ)) * (δ ^ s * δ ^ (n : ℕ)) := by ring
  have hsplit : κ ^ (n : ℕ) = κ ^ ((n : ℝ) - s) * κ ^ s := by
    rw [← Real.rpow_natCast κ n, ← Real.rpow_add hκpos]
    ring_nf
  have hκs : (0 : ℝ) < κ ^ s := Real.rpow_pos_of_pos hκpos s
  rw [hsplit, ← mul_assoc] at hcancel
  have hlt : C * κ ^ ((n : ℝ) - s) * κ ^ s < p * κ ^ s := mul_lt_mul_of_pos_right hkey hκs
  linarith



/-! ## A few elementary facts -/
/-- A nonzero measure charges some ball centred at the origin. -/
lemma exists_ball_pos_of_ne_zero {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν0 : ν ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ 0 < ν (ball 0 R) := by
  by_contra hcon
  push Not at hcon
  apply hν0
  have hz : ∀ k : ℕ, ν (ball 0 ((k : ℝ) + 1)) = 0 := by
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    exact le_antisymm (hcon _ hk) (show 0 ≤ ν (ball 0 ((k : ℝ) + 1)) from zero_le)
  have hsub : (univ : Set (EuclideanSpace ℝ (Fin n))) ⊆ ⋃ k : ℕ, ball 0 ((k : ℝ) + 1) := by
    intro x _
    obtain ⟨k, hk⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨k, by simp only [mem_ball]; linarith⟩
  have huniv : ν univ = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq (measure_iUnion_null hz)) zero_le
  ext s
  exact le_antisymm ((measure_mono (subset_univ s)).trans_eq huniv) zero_le
/-- Splitting off the scaling factor `r ^ s` from `d * (r * v) ^ s`. -/
lemma ofReal_mul_rpow_mul {d v ri s : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (hri : 0 ≤ ri) :
    ENNReal.ofReal (d * (ri * v) ^ s)
      = ENNReal.ofReal (d * v ^ s) * ENNReal.ofReal (ri ^ s) := by
  rw [Real.mul_rpow hri hv, show d * (ri ^ s * v ^ s) = d * v ^ s * ri ^ s by ring]
  exact ENNReal.ofReal_mul (mul_nonneg hd (Real.rpow_nonneg hv s))
/-! ## The engine behind Lemma 14.7 (4) -/
section Engine
variable {s d t r₀ : ℝ} {μ ν : Measure (EuclideanSpace ℝ (Fin n))}
  {a : EuclideanSpace ℝ (Fin n)} {rs : ℕ → ℝ} {cs : ℕ → ℝ≥0∞} {lam : ℝ≥0∞}
/-- If `x` belongs to the support of a blow-up limit `ν`, then, for large `i`, the point
`a + r i • x` is within distance `ε * r i` of the support of `μ`. -/
lemma tangent_exists_nearby_support_point
    (hrpos : ∀ i, 0 < rs i)
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Measure.support ν) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ y ∈ Measure.support μ, dist y (a + rs i • x) < rs i * ε := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have hpos : 0 < ν (ball x ε) := measure_ball_pos_of_mem_support hx hε
  have hli := hb.2 (ball x ε) isOpen_ball
  have hev : ∀ᶠ i in atTop,
      0 < (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x ε) :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hpos hli)
  filter_upwards [hev] with i hi
  rw [blowUp_smul_apply_ball μ a x (hrpos i) (cs i) ε] at hi
  have hμpos : 0 < μ (ball (a + rs i • x) (rs i * ε)) := by
    rcases eq_or_lt_of_le (bot_le : 0 ≤ μ (ball (a + rs i • x) (rs i * ε))) with h | h
    · exfalso
      simp [h.symm] at hi
    · exact h
  obtain ⟨y, hy, hyspt⟩ := exists_mem_support_of_measure_pos hμpos
  exact ⟨y, hyspt, mem_ball.mp hy⟩
/-- Upper bound in Lemma 14.7 (1), from the uniform upper bound on `spt μ`. -/
lemma tangent_closedBall_le
    (hd : 0 ≤ d) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (hupper : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hlamfin : lam ≠ ∞)
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν)
    {x : EuclideanSpace ℝ (Fin n)}
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∃ y ∈ P, dist y (a + rs i • x) < rs i * ε)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ν (closedBall x ρ) ≤ ENNReal.ofReal (d * ρ ^ s) * lam := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have key : ∀ v : ℝ, ρ < v → ν (closedBall x ρ) ≤ ENNReal.ofReal (d * v ^ s) * lam := by
    intro v hv
    have hvpos : 0 < v := hρ.trans hv
    set u : ℝ := (ρ + v) / 2 with hu
    have hρu : ρ < u := by rw [hu]; linarith
    have huv : u < v := by rw [hu]; linarith
    have hupos : 0 < u := hρ.trans hρu
    have hεpos : 0 < v - u := by linarith
    have h1 : ν (closedBall x ρ) ≤ ν (ball x u) :=
      measure_mono (closedBall_subset_ball hρu)
    have h2 := hb.2 (ball x u) isOpen_ball
    have hsmall : ∀ᶠ i in atTop, rs i * v < r₀ := by
      have h0 : Tendsto (fun i ↦ rs i * v) atTop (𝓝 0) := by simpa using hr0.mul_const v
      exact h0.eventually_lt_const hr₀
    have h3 : ∀ᶠ i in atTop,
        (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x u)
          ≤ ENNReal.ofReal (d * v ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
      filter_upwards [hnear (v - u) hεpos, hsmall] with i hi hsm
      obtain ⟨y, hyspt, hy⟩ := hi
      have hsub : ball (a + rs i • x) (rs i * u) ⊆ closedBall y (rs i * v) := by
        intro z hz
        rw [mem_ball] at hz
        rw [mem_closedBall]
        have : dist z y ≤ dist z (a + rs i • x) + dist (a + rs i • x) y :=
          dist_triangle _ _ _
        have hy' : dist (a + rs i • x) y < rs i * (v - u) := by
          rwa [dist_comm]
        refine le_of_lt ?_
        calc dist z y ≤ dist z (a + rs i • x) + dist (a + rs i • x) y := this
          _ < rs i * u + rs i * (v - u) := by gcongr
          _ = rs i * v := by ring
      rw [blowUp_smul_apply_ball μ a x (hrpos i) (cs i) u]
      calc cs i * μ (ball (a + rs i • x) (rs i * u))
          ≤ cs i * μ (closedBall y (rs i * v)) := by gcongr
        _ ≤ cs i * ENNReal.ofReal (d * (rs i * v) ^ s) := by
            gcongr
            exact hupper y hyspt _ (mul_pos (hrpos i) hvpos) hsm
        _ = ENNReal.ofReal (d * v ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
            rw [ofReal_mul_rpow_mul hd hvpos.le (hrpos i).le]
            ring
    have hlim : Tendsto
        (fun i ↦ ENNReal.ofReal (d * v ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
        (𝓝 (ENNReal.ofReal (d * v ^ s) * lam)) :=
      ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
    have h4 : liminf (fun i ↦ (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x u)) atTop
        ≤ ENNReal.ofReal (d * v ^ s) * lam := by
      calc liminf (fun i ↦ (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x u)) atTop
          ≤ liminf (fun i ↦ ENNReal.ofReal (d * v ^ s) *
              (cs i * ENNReal.ofReal (rs i ^ s))) atTop :=
            liminf_le_liminf h3
        _ = ENNReal.ofReal (d * v ^ s) * lam := hlim.liminf_eq
    exact h1.trans (h2.trans h4)
  have hcont : Tendsto (fun v : ℝ ↦ ENNReal.ofReal (d * v ^ s) * lam) (𝓝[>] ρ)
      (𝓝 (ENNReal.ofReal (d * ρ ^ s) * lam)) := by
    have h1 : ContinuousAt (fun v : ℝ ↦ d * v ^ s) ρ := by
      exact continuousAt_const.mul (Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne'))
    have h2 : ContinuousAt (fun v : ℝ ↦ ENNReal.ofReal (d * v ^ s)) ρ :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    exact (ENNReal.Tendsto.mul_const (h2.tendsto.mono_left nhdsWithin_le_nhds)
      (Or.inr hlamfin))
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)
/-- Lower bound in Lemma 14.7 (1), from the uniform lower bound on `spt μ`. -/
lemma le_tangent_closedBall
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (hlower : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hlamfin : lam ≠ ∞)
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν)
    {x : EuclideanSpace ℝ (Fin n)}
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∃ y ∈ P, dist y (a + rs i • x) < rs i * ε)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (t * d * ρ ^ s) * lam ≤ ν (closedBall x ρ) := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have hcompact := hb.1 (closedBall x ρ) (isCompact_closedBall _ _)
  have key : ∀ w : ℝ, 0 < w → w < ρ →
      ENNReal.ofReal (t * d * w ^ s) * lam ≤ ν (closedBall x ρ) := by
    intro w hw hwρ
    have hεpos : 0 < ρ - w := by linarith
    have hsmall : ∀ᶠ i in atTop, rs i * w < r₀ := by
      have h0 : Tendsto (fun i ↦ rs i * w) atTop (𝓝 0) := by simpa using hr0.mul_const w
      exact h0.eventually_lt_const hr₀
    have h3 : ∀ᶠ i in atTop,
        ENNReal.ofReal (t * d * w ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
          ≤ (cs i • Measure.map (blowUpMap a (rs i)) μ) (closedBall x ρ) := by
      filter_upwards [hnear (ρ - w) hεpos, hsmall] with i hi hsm
      obtain ⟨y, hyspt, hy⟩ := hi
      have hsub : closedBall y (rs i * w) ⊆ closedBall (a + rs i • x) (rs i * ρ) := by
        intro z hz
        rw [mem_closedBall] at hz ⊢
        calc dist z (a + rs i • x) ≤ dist z y + dist y (a + rs i • x) := dist_triangle _ _ _
          _ ≤ rs i * w + rs i * (ρ - w) := by gcongr
          _ = rs i * ρ := by ring
      rw [blowUp_smul_apply_closedBall μ a x (hrpos i) (cs i) ρ]
      calc ENNReal.ofReal (t * d * w ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
          = cs i * ENNReal.ofReal (t * d * (rs i * w) ^ s) := by
            rw [ofReal_mul_rpow_mul (mul_nonneg ht hd) hw.le (hrpos i).le]
            ring
        _ ≤ cs i * μ (closedBall y (rs i * w)) := by
            gcongr
            exact hlower y hyspt _ (mul_pos (hrpos i) hw) hsm
        _ ≤ cs i * μ (closedBall (a + rs i • x) (rs i * ρ)) := by
            gcongr
    have hlim : Tendsto
        (fun i ↦ ENNReal.ofReal (t * d * w ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
        (𝓝 (ENNReal.ofReal (t * d * w ^ s) * lam)) :=
      ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
    calc ENNReal.ofReal (t * d * w ^ s) * lam
        = liminf (fun i ↦ ENNReal.ofReal (t * d * w ^ s) *
            (cs i * ENNReal.ofReal (rs i ^ s))) atTop := hlim.liminf_eq.symm
      _ ≤ liminf (fun i ↦
            (cs i • Measure.map (blowUpMap a (rs i)) μ) (closedBall x ρ)) atTop :=
          liminf_le_liminf h3
      _ ≤ limsup (fun i ↦
            (cs i • Measure.map (blowUpMap a (rs i)) μ) (closedBall x ρ)) atTop :=
          liminf_le_limsup
      _ ≤ ν (closedBall x ρ) := hcompact
  have hcont : Tendsto (fun w : ℝ ↦ ENNReal.ofReal (t * d * w ^ s) * lam) (𝓝[<] ρ)
      (𝓝 (ENNReal.ofReal (t * d * ρ ^ s) * lam)) := by
    have h1 : ContinuousAt (fun w : ℝ ↦ t * d * w ^ s) ρ :=
      continuousAt_const.mul (Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne'))
    have h2 : ContinuousAt (fun w : ℝ ↦ ENNReal.ofReal (t * d * w ^ s)) ρ :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    exact ENNReal.Tendsto.mul_const (h2.tendsto.mono_left nhdsWithin_le_nhds) (Or.inr hlamfin)
  refine le_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds hρ)] with w hw1 hw2
  exact key w hw2 hw1
/-- The scaling constants of a blow-up sequence are bounded, under the uniform lower bound. -/
lemma tangent_scaling_lt_top
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (ha : a ∈ P)
    (hlower : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν) :
    lam ≠ ∞ := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have hcompact := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
  have hsmall : ∀ᶠ i in atTop, rs i < r₀ := hr0.eventually_lt_const hr₀
  have h3 : ∀ᶠ i in atTop,
      ENNReal.ofReal (t * d) * (cs i * ENNReal.ofReal (rs i ^ s))
        ≤ (cs i • Measure.map (blowUpMap a (rs i)) μ) (closedBall 0 1) := by
    filter_upwards [hsmall] with i hsm
    rw [blowUp_smul_apply_closedBall μ a 0 (hrpos i) (cs i) 1, smul_zero, add_zero, mul_one]
    calc ENNReal.ofReal (t * d) * (cs i * ENNReal.ofReal (rs i ^ s))
        = cs i * ENNReal.ofReal (t * d * rs i ^ s) := by
          rw [show t * d * rs i ^ s = (t * d) * rs i ^ s from rfl,
            ENNReal.ofReal_mul (mul_nonneg ht.le hd.le)]
          ring
      _ ≤ cs i * μ (closedBall a (rs i)) := by
          gcongr
          exact hlower a ha _ (hrpos i) hsm
  have hlim : Tendsto
      (fun i ↦ ENNReal.ofReal (t * d) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
      (𝓝 (ENNReal.ofReal (t * d) * lam)) :=
    ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
  have hle : ENNReal.ofReal (t * d) * lam ≤ ν (closedBall 0 1) := by
    calc ENNReal.ofReal (t * d) * lam
        = liminf (fun i ↦ ENNReal.ofReal (t * d) *
            (cs i * ENNReal.ofReal (rs i ^ s))) atTop := hlim.liminf_eq.symm
      _ ≤ liminf (fun i ↦
            (cs i • Measure.map (blowUpMap a (rs i)) μ) (closedBall 0 1)) atTop :=
          liminf_le_liminf h3
      _ ≤ limsup (fun i ↦
            (cs i • Measure.map (blowUpMap a (rs i)) μ) (closedBall 0 1)) atTop :=
          liminf_le_limsup
      _ ≤ ν (closedBall 0 1) := hcompact
  intro hlamtop
  rw [hlamtop] at hle
  rw [ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)] at hle
  exact (regular_measure_closedBall_lt_top hν 0 1).ne (top_le_iff.mp hle)
/-- The scaling constants of a blow-up sequence do not degenerate, under the uniform upper
bound. -/
lemma tangent_scaling_pos
    (hd : 0 < d) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (ha : a ∈ P)
    (hupper : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hν0 : ν ≠ 0)
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν) :
    0 < lam := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  obtain ⟨R, hR1, hRpos⟩ := exists_ball_pos_of_ne_zero hν0
  have hRpos' : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hopen := hb.2 (ball 0 R) isOpen_ball
  have hsmall : ∀ᶠ i in atTop, rs i * R < r₀ := by
    have h0 : Tendsto (fun i ↦ rs i * R) atTop (𝓝 0) := by simpa using hr0.mul_const R
    exact h0.eventually_lt_const hr₀
  have h3 : ∀ᶠ i in atTop,
      (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball 0 R)
        ≤ ENNReal.ofReal (d * R ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
    filter_upwards [hsmall] with i hsm
    rw [blowUp_smul_apply_ball μ a 0 (hrpos i) (cs i) R, smul_zero, add_zero]
    calc cs i * μ (ball a (rs i * R))
        ≤ cs i * μ (closedBall a (rs i * R)) := by
          gcongr
          exact ball_subset_closedBall
      _ ≤ cs i * ENNReal.ofReal (d * (rs i * R) ^ s) := by
          gcongr
          exact hupper a ha _ (mul_pos (hrpos i) hRpos') hsm
      _ = ENNReal.ofReal (d * R ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
          rw [ofReal_mul_rpow_mul hd.le hRpos'.le (hrpos i).le]
          ring
  have hlim : Tendsto
      (fun i ↦ ENNReal.ofReal (d * R ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
      (𝓝 (ENNReal.ofReal (d * R ^ s) * lam)) :=
    ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
  have hle : ν (ball 0 R) ≤ ENNReal.ofReal (d * R ^ s) * lam := by
    calc ν (ball 0 R)
        ≤ liminf (fun i ↦
            (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball 0 R)) atTop := hopen
      _ ≤ liminf (fun i ↦ ENNReal.ofReal (d * R ^ s) *
            (cs i * ENNReal.ofReal (rs i ^ s))) atTop := liminf_le_liminf h3
      _ = ENNReal.ofReal (d * R ^ s) * lam := hlim.liminf_eq
  have hnonneg : (0 : ℝ≥0∞) ≤ lam := by exact zero_le
  rcases eq_or_lt_of_le hnonneg with h | h
  · have hle_zero : ν (ball 0 R) ≤ 0 := by
      have hfactor : ENNReal.ofReal (d * R ^ s) * lam = 0 := by
        rw [← h, mul_zero]
      simpa [hfactor] using hle
    exact absurd (le_antisymm hle_zero (by exact zero_le)) hRpos.ne'
  · exact h
end Engine
/-! ## The doubling condition from uniform ball bounds -/
section Doubling
variable {s d t r₀ : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
  {a : EuclideanSpace ℝ (Fin n)}
/-- Uniform two-sided ball bounds on `spt μ` imply Mattila's assumption 14.3 (1) at every point
of `spt μ`. -/
lemma limsup_ball_ratio_lt_top_of_uniform
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀) (ha : a ∈ Measure.support μ)
    (hupper : ∀ y ∈ Measure.support μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hlower : ∀ y ∈ Measure.support μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ)) :
    limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞ := by
  set K : ℝ := (4 : ℝ) ^ s / t with hK
  have hKpos : 0 < K := by
    apply div_pos _ ht
    exact Real.rpow_pos_of_pos (by norm_num) s
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      μ (ball a (2 * ρ)) / μ (ball a ρ) ≤ ENNReal.ofReal K := by
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (0 : ℝ) < ρ := self_mem_nhdsWithin
    have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r₀ / 2 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by positivity))
    filter_upwards [h1, h2] with ρ hρ hρ'
    have hρ2 : (0 : ℝ) < 2 * ρ := by linarith
    have hρhalf : (0 : ℝ) < ρ / 2 := by linarith
    have hkey : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal K * μ (ball a ρ) := by
      have hup : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (d * (2 * ρ) ^ s) :=
        le_trans (measure_mono ball_subset_closedBall)
          (hupper a ha _ hρ2 (by linarith))
      have hlo : ENNReal.ofReal (t * d * (ρ / 2) ^ s) ≤ μ (ball a ρ) :=
        le_trans (hlower a ha _ hρhalf (by linarith))
          (measure_mono (closedBall_subset_ball (by linarith)))
      have hid : d * (2 * ρ) ^ s = K * (t * d * (ρ / 2) ^ s) := by
        have h4 : (2 : ℝ) * ρ = 4 * (ρ / 2) := by ring
        rw [h4, Real.mul_rpow (by norm_num) hρhalf.le, hK]
        field_simp
      calc μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (d * (2 * ρ) ^ s) := hup
        _ = ENNReal.ofReal K * ENNReal.ofReal (t * d * (ρ / 2) ^ s) := by
            rw [hid, ENNReal.ofReal_mul hKpos.le]
        _ ≤ ENNReal.ofReal K * μ (ball a ρ) := by gcongr
    exact ENNReal.div_le_of_le_mul hkey
  exact lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) hev) ENNReal.ofReal_lt_top
end Doubling
/-! ## Nearby points of a set with a density point
This is the ingredient which replaces, in the proof of Lemma 14.7 (1), the elementary fact used
for Lemma 14.7 (4) that an open set of positive measure meets `spt μ`. -/
section DensityPoint
variable {s p q r₀ : ℝ} {μ ν : Measure (EuclideanSpace ℝ (Fin n))}
  {a : EuclideanSpace ℝ (Fin n)} {rs : ℕ → ℝ} {cs : ℕ → ℝ≥0∞}
  {B : Set (EuclideanSpace ℝ (Fin n))}
/-- If `a` is a `μ`-density point of a set `B` on which the measures of small balls are
comparable to `ρ ^ s`, and `x` lies in the support of a blow-up limit `ν` of `μ` at `a`, then for
large `i` the point `a + r i • x` is within distance `ε * r i` of `B`. -/
lemma tangent_exists_nearby_point_of_density
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀) (haB : a ∈ B)
    (hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ))
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Measure.support ν) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ y ∈ B, dist y (a + rs i • x) < rs i * ε := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  set R : ℝ := ‖x‖ + ε with hR
  have hRpos : 0 < R := by positivity
  -- a positive finite amount of mass in the limit ball `ball x ε`
  have hνpos : 0 < ν (ball x ε) := measure_ball_pos_of_mem_support hx hε
  have hmin_pos : 0 < min (ν (ball x ε)) 1 := lt_min hνpos one_pos
  have hmin_ne_top : min (ν (ball x ε)) 1 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set β : ℝ≥0∞ := min (ν (ball x ε)) 1 / 2 with hβ
  have hβpos : 0 < β := ENNReal.half_pos hmin_pos.ne'
  have hβlt : β < ν (ball x ε) :=
    lt_of_lt_of_le (ENNReal.half_lt_self hmin_pos.ne' hmin_ne_top) (min_le_left _ _)
  have hev1 : ∀ᶠ i in atTop,
      β < (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x ε) :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hβlt (hb.2 (ball x ε) isOpen_ball))
  -- the normalizing constants are eventually bounded above
  set M : ℝ≥0∞ := ν (closedBall 0 1) + 1 with hM
  have hνcb : ν (closedBall 0 1) ≠ ∞ := (regular_measure_closedBall_lt_top hν 0 1).ne
  have hMtop : M ≠ ∞ := by simp [hM, ENNReal.add_eq_top, hνcb]
  have hev2 : ∀ᶠ i in atTop, cs i * μ (closedBall a (rs i)) < M := by
    have hlimsup := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
    have h := eventually_lt_of_limsup_lt
      (lt_of_le_of_lt hlimsup (ENNReal.lt_add_right hνcb one_ne_zero))
    filter_upwards [h] with i hi
    rwa [blowUp_smul_apply_closedBall μ a 0 (hrpos i) (cs i) 1, smul_zero, add_zero,
      mul_one] at hi
  -- comparison of the measures of the balls `B (a, R r i)` and `B (a, r i)`
  set K : ℝ≥0∞ := ENNReal.ofReal (q * R ^ s) / ENNReal.ofReal p with hK
  have hpne : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  have hKtop : K ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hpne
  have hKMtop : K * M ≠ ∞ := ENNReal.mul_ne_top hKtop hMtop
  set γ : ℝ≥0∞ := β / (K * M) with hγ
  have hγpos : 0 < γ := ENNReal.div_pos_iff.2 ⟨hβpos.ne', hKMtop⟩
  -- the density hypothesis, transported to the sequence of radii `R * r i`
  have htendR : Tendsto (fun i ↦ rs i * R) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using hr0.mul_const R
    · exact Eventually.of_forall fun i ↦ mul_pos (hrpos i) hRpos
  have hev3 : ∀ᶠ i in atTop,
      μ (closedBall a (rs i * R) \ B) ≤ γ * μ (closedBall a (rs i * R)) :=
    htendR.eventually (hdens γ hγpos)
  have hev4 : ∀ᶠ i in atTop, rs i * R < r₀ := by
    have h0 : Tendsto (fun i ↦ rs i * R) atTop (𝓝 0) := by simpa using hr0.mul_const R
    exact h0.eventually_lt_const hr₀
  have hev5 : ∀ᶠ i in atTop, rs i < r₀ := hr0.eventually_lt_const hr₀
  filter_upwards [hev1, hev2, hev3, hev4, hev5] with i h1 h2 h3 h4 h5
  by_contra hcon
  push Not at hcon
  -- if no point of `B` is near `a + r i • x`, the ball `U i` is contained in `B (a, R r i) \ B`
  have hsub : ball (a + rs i • x) (rs i * ε) ⊆ closedBall a (rs i * R) \ B := by
    intro z hz
    rw [mem_ball] at hz
    have hdist : dist (a + rs i • x) a = rs i * ‖x‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hrpos i)]
    constructor
    · rw [mem_closedBall]
      calc dist z a ≤ dist z (a + rs i • x) + dist (a + rs i • x) a := dist_triangle _ _ _
        _ ≤ rs i * ε + rs i * ‖x‖ := by rw [hdist]; gcongr
        _ = rs i * R := by rw [hR]; ring
    · intro hzB
      exact absurd hz (not_lt.2 (hcon z hzB))
  have hKineq : μ (closedBall a (rs i * R)) ≤ K * μ (closedBall a (rs i)) := by
    have hup : μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := by
      rw [← ofReal_mul_rpow_mul hq.le hRpos.le (hrpos i).le]
      exact hupper a haB _ (mul_pos (hrpos i) hRpos) h4
    have hlo : ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s) ≤ μ (closedBall a (rs i)) := by
      rw [← ENNReal.ofReal_mul hp.le]
      exact hlower a haB _ (hrpos i) h5
    calc μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := hup
      _ = K * (ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s)) := by
          rw [hK, ← mul_assoc, ENNReal.div_mul_cancel hpne ENNReal.ofReal_ne_top]
      _ ≤ K * μ (closedBall a (rs i)) := by gcongr
  have hchain : β < β := by
    calc β < (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x ε) := h1
      _ = cs i * μ (ball (a + rs i • x) (rs i * ε)) :=
          blowUp_smul_apply_ball μ a x (hrpos i) (cs i) ε
      _ ≤ cs i * (γ * (K * μ (closedBall a (rs i)))) := by
          gcongr
          calc μ (ball (a + rs i • x) (rs i * ε))
              ≤ μ (closedBall a (rs i * R) \ B) := measure_mono hsub
            _ ≤ γ * μ (closedBall a (rs i * R)) := h3
            _ ≤ γ * (K * μ (closedBall a (rs i))) := by gcongr
      _ = γ * K * (cs i * μ (closedBall a (rs i))) := by ring
      _ ≤ γ * K * M := by gcongr
      _ = γ * (K * M) := by ring
      _ ≤ β := ENNReal.mul_le_of_le_div le_rfl
  exact absurd hchain (lt_irrefl _)
/-- Under the hypotheses of the density-point lemma, the blow-ups give arbitrarily small mass to
sets which live at a fixed multiple of the scale `r i` around `a` and avoid `B`. -/
lemma tangent_smul_measure_le_of_disjoint
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀) (haB : a ∈ B)
    (hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ))
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν)
    {R : ℝ} (hR : 0 < R) {β : ℝ≥0∞} (hβ : 0 < β) :
    ∀ᶠ i in atTop, ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      S ⊆ closedBall a (rs i * R) → Disjoint S B → cs i * μ S ≤ β := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  set M : ℝ≥0∞ := ν (closedBall 0 1) + 1 with hM
  have hνcb : ν (closedBall 0 1) ≠ ∞ := (regular_measure_closedBall_lt_top hν 0 1).ne
  have hMtop : M ≠ ∞ := by simp [hM, ENNReal.add_eq_top, hνcb]
  have hev2 : ∀ᶠ i in atTop, cs i * μ (closedBall a (rs i)) < M := by
    have hlimsup := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
    have h := eventually_lt_of_limsup_lt
      (lt_of_le_of_lt hlimsup (ENNReal.lt_add_right hνcb one_ne_zero))
    filter_upwards [h] with i hi
    rwa [blowUp_smul_apply_closedBall μ a 0 (hrpos i) (cs i) 1, smul_zero, add_zero,
      mul_one] at hi
  set K : ℝ≥0∞ := ENNReal.ofReal (q * R ^ s) / ENNReal.ofReal p with hK
  have hpne : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  have hKtop : K ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hpne
  have hKMtop : K * M ≠ ∞ := ENNReal.mul_ne_top hKtop hMtop
  set γ : ℝ≥0∞ := β / (K * M) with hγ
  have hγpos : 0 < γ := ENNReal.div_pos_iff.2 ⟨hβ.ne', hKMtop⟩
  have htendR : Tendsto (fun i ↦ rs i * R) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using hr0.mul_const R,
      Eventually.of_forall fun i ↦ mul_pos (hrpos i) hR⟩
  have hev3 : ∀ᶠ i in atTop,
      μ (closedBall a (rs i * R) \ B) ≤ γ * μ (closedBall a (rs i * R)) :=
    htendR.eventually (hdens γ hγpos)
  have hev4 : ∀ᶠ i in atTop, rs i * R < r₀ := by
    have h0 : Tendsto (fun i ↦ rs i * R) atTop (𝓝 0) := by simpa using hr0.mul_const R
    exact h0.eventually_lt_const hr₀
  have hev5 : ∀ᶠ i in atTop, rs i < r₀ := hr0.eventually_lt_const hr₀
  filter_upwards [hev2, hev3, hev4, hev5] with i h2 h3 h4 h5 S hSsub hSdisj
  have hKineq : μ (closedBall a (rs i * R)) ≤ K * μ (closedBall a (rs i)) := by
    have hup : μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := by
      rw [← ofReal_mul_rpow_mul hq.le hR.le (hrpos i).le]
      exact hupper a haB _ (mul_pos (hrpos i) hR) h4
    have hlo : ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s) ≤ μ (closedBall a (rs i)) := by
      rw [← ENNReal.ofReal_mul hp.le]
      exact hlower a haB _ (hrpos i) h5
    calc μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := hup
      _ = K * (ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s)) := by
          rw [hK, ← mul_assoc, ENNReal.div_mul_cancel hpne ENNReal.ofReal_ne_top]
      _ ≤ K * μ (closedBall a (rs i)) := by gcongr
  calc cs i * μ S ≤ cs i * (γ * (K * μ (closedBall a (rs i)))) := by
        gcongr
        calc μ S ≤ μ (closedBall a (rs i * R) \ B) :=
              measure_mono (subset_sdiff.2 ⟨hSsub, hSdisj⟩)
          _ ≤ γ * μ (closedBall a (rs i * R)) := h3
          _ ≤ γ * (K * μ (closedBall a (rs i))) := by gcongr
    _ = γ * K * (cs i * μ (closedBall a (rs i))) := by ring
    _ ≤ γ * K * M := by gcongr
    _ = γ * (K * M) := by ring
    _ ≤ β := ENNReal.mul_le_of_le_div le_rfl
/-- Upper bound for tangent measures of balls with **arbitrary** centres, from a bound on the
measures of all small balls meeting the set `P`. -/
lemma tangent_closedBall_le_of_ball_bounds {d : ℝ} {lam : ℝ≥0∞}
    (hd : 0 ≤ d) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (hballbd : ∀ z ∈ P, ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < r₀ →
      z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal (d * w ^ s))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hlamfin : lam ≠ ∞)
    (hseq : ∀ i, Measure.Regular (cs i • Measure.map (blowUpMap a (rs i)) μ))
    (hν : Measure.Regular ν)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ cs i • Measure.map (blowUpMap a (rs i)) μ) ν)
    (hsmall : ∀ β : ℝ≥0∞, 0 < β → ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop,
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ closedBall a (rs i * R) → Disjoint S P →
        cs i * μ S ≤ β)
    (x : EuclideanSpace ℝ (Fin n)) {ρ : ℝ} (hρ : 0 < ρ) :
    ν (closedBall x ρ) ≤ ENNReal.ofReal (d * ρ ^ s) * lam := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have key : ∀ u : ℝ, ρ < u → ν (closedBall x ρ) ≤ ENNReal.ofReal (d * u ^ s) * lam := by
    intro u hu
    have hupos : 0 < u := hρ.trans hu
    have hRpos : 0 < ‖x‖ + u := by positivity
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hβ : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hε
    have hsm : ∀ᶠ i in atTop, rs i * u < r₀ := by
      have h0 : Tendsto (fun i ↦ rs i * u) atTop (𝓝 0) := by simpa using hr0.mul_const u
      exact h0.eventually_lt_const hr₀
    have h3 : ∀ᶠ i in atTop,
        (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x u)
          ≤ ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
            + (ε : ℝ≥0∞) := by
      filter_upwards [hsmall (ε : ℝ≥0∞) hβ (‖x‖ + u) hRpos, hsm] with i hi hsmi
      rw [blowUp_smul_apply_ball μ a x (hrpos i) (cs i) u]
      by_cases hmeet : ∃ z ∈ P, z ∈ closedBall (a + rs i • x) (rs i * u)
      · obtain ⟨z, hzP, hz⟩ := hmeet
        have hball : μ (ball (a + rs i • x) (rs i * u))
            ≤ ENNReal.ofReal (d * (rs i * u) ^ s) :=
          le_trans (measure_mono ball_subset_closedBall)
            (hballbd z hzP _ _ (mul_pos (hrpos i) hupos) hsmi hz)
        calc cs i * μ (ball (a + rs i • x) (rs i * u))
            ≤ cs i * ENNReal.ofReal (d * (rs i * u) ^ s) := by gcongr
          _ = ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
              rw [ofReal_mul_rpow_mul hd hupos.le (hrpos i).le]
              ring
          _ ≤ _ := le_self_add
      · push Not at hmeet
        have hdisj : Disjoint (closedBall (a + rs i • x) (rs i * u)) P := by
          rw [Set.disjoint_right]
          intro z hzP hz
          exact hmeet z hzP hz
        have hsub : closedBall (a + rs i • x) (rs i * u)
            ⊆ closedBall a (rs i * (‖x‖ + u)) := by
          intro z hz
          rw [mem_closedBall] at hz ⊢
          have hdist : dist (a + rs i • x) a = rs i * ‖x‖ := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_pos (hrpos i)]
          calc dist z a ≤ dist z (a + rs i • x) + dist (a + rs i • x) a := dist_triangle _ _ _
            _ ≤ rs i * u + rs i * ‖x‖ := by rw [hdist]; gcongr
            _ = rs i * (‖x‖ + u) := by ring
        calc cs i * μ (ball (a + rs i • x) (rs i * u))
            ≤ cs i * μ (closedBall (a + rs i • x) (rs i * u)) := by
              gcongr
              exact ball_subset_closedBall
          _ ≤ (ε : ℝ≥0∞) := hi _ hsub hdisj
          _ ≤ _ := le_add_self
    have hlim : Tendsto
        (fun i ↦ ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
          + (ε : ℝ≥0∞)) atTop
        (𝓝 (ENNReal.ofReal (d * u ^ s) * lam + (ε : ℝ≥0∞))) :=
      (ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)).add tendsto_const_nhds
    calc ν (closedBall x ρ) ≤ ν (ball x u) := measure_mono (closedBall_subset_ball hu)
      _ ≤ liminf (fun i ↦ (cs i • Measure.map (blowUpMap a (rs i)) μ) (ball x u))
            atTop := hb.2 (ball x u) isOpen_ball
      _ ≤ liminf (fun i ↦ ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
            + (ε : ℝ≥0∞)) atTop := liminf_le_liminf h3
      _ = ENNReal.ofReal (d * u ^ s) * lam + (ε : ℝ≥0∞) := hlim.liminf_eq
  have hcont : Tendsto (fun u : ℝ ↦ ENNReal.ofReal (d * u ^ s) * lam) (𝓝[>] ρ)
      (𝓝 (ENNReal.ofReal (d * ρ ^ s) * lam)) := by
    have h1 : ContinuousAt (fun u : ℝ ↦ d * u ^ s) ρ :=
      continuousAt_const.mul (Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne'))
    have h2 : ContinuousAt (fun u : ℝ ↦ ENNReal.ofReal (d * u ^ s)) ρ :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    exact ENNReal.Tendsto.mul_const (h2.tendsto.mono_left nhdsWithin_le_nhds) (Or.inr hlamfin)
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)
end DensityPoint
/-! ## Mattila's reduction step for Lemma 14.7 (1) -/
/-- **Mattila, Lemma 14.7, reduction step.**
Let `τ`, `d`, `r₀` be positive numbers and let `B` be a set with
`τ d ρ ^ s ≤ μ (B (y, ρ)) ≤ d ρ ^ s` for `y ∈ B` and `0 < ρ < r₀`.
If `a ∈ B` is a `μ`-density point of `B`, then every tangent measure `ν ∈ Tan (μ, a)` satisfies
`τ c ρ ^ s ≤ ν (B (x, ρ)) ≤ c ρ ^ s` for `x ∈ spt ν` and `0 < ρ < ∞`, for some positive finite
constant `c`. -/
theorem tangent_ball_bounds_of_density_point {s d t r₀ : ℝ}
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hbounds : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) ∧
        μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    {a : EuclideanSpace ℝ (Fin n)} (haB : a ∈ B)
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (htan : IsTangentMeasure μ ν a) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  have hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).2
  have hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).1
  obtain ⟨hν, hν0, rs, cs, hrpos, hcpos, hcfin, hr0, hconv⟩ := htan
  obtain ⟨lam, -, φ, hφ, hlam⟩ := (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq
    (x := fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) (fun i ↦ mem_univ _)
  have hrpos' : ∀ j, 0 < rs (φ j) := fun j ↦ hrpos _
  have hr0' : Tendsto (fun j ↦ rs (φ j)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  have hconv' : Measure.WeaklyConverges
      (fun j ↦ cs (φ j) • Measure.map (blowUpMap a (rs (φ j))) μ) ν :=
      hconv.comp hφ.tendsto_atTop
  have hseq' : ∀ j, Measure.Regular (cs (φ j) • Measure.map (blowUpMap a (rs (φ j))) μ) :=
    fun j ↦ regular_smul_map_blowUp hμ a (hrpos _).ne' (hcfin _)
  have hlamfin : lam ≠ ∞ :=
    tangent_scaling_lt_top hd ht hr₀ haB hlower hrpos' hr0' hlam hseq' hν hconv'
  have hlampos : 0 < lam :=
    tangent_scaling_pos hd hr₀ haB hupper hrpos' hr0' hlam hν0 hseq' hν hconv'
  refine ⟨ENNReal.ofReal d * lam, ENNReal.mul_pos (ENNReal.ofReal_pos.2 hd).ne' hlampos.ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlamfin, ?_⟩
  intro x hx ρ hρ
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∃ y ∈ B, dist y (a + rs (φ j) • x) < rs (φ j) * ε :=
    fun ε hε ↦ tangent_exists_nearby_point_of_density (mul_pos ht hd) hd hr₀ haB hupper
      hlower hdens hrpos' hr0' hseq' hν hconv' hx hε
  have hup :=
    tangent_closedBall_le hd.le hr₀ hupper hrpos' hr0' hlam hlamfin hseq' hν hconv' hnear hρ
  have hlo := le_tangent_closedBall hd.le ht.le hr₀ hlower hrpos' hr0' hlam hlamfin hseq' hν hconv'
    hnear hρ
  constructor
  · refine le_trans (le_of_eq ?_) hlo
    rw [ENNReal.ofReal_mul (mul_nonneg ht.le hd.le), ENNReal.ofReal_mul ht.le]
    ring
  · refine le_trans hup (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hd.le]
    ring
/-! ## Mattila's reduction step for Lemma 14.7 (2) -/
/-- **Mattila, Lemma 14.7, reduction step for part (2).**
If, in addition to the hypotheses of the reduction step for part (1), the measures of *all* small
balls meeting `B` are bounded by `d ρ ^ s`, then the upper bound for the tangent measure holds for
balls with arbitrary centres, with the same constant `c`. -/
theorem tangent_ball_bounds_of_density_point_of_ball_bounds {s d t r₀ : ℝ}
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hbounds : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) ∧
        μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hballbd : ∀ z ∈ B, ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < r₀ →
      z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal (d * w ^ s))
    {a : EuclideanSpace ℝ (Fin n)} (haB : a ∈ B)
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (htan : IsTangentMeasure μ ν a) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  have hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).2
  have hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).1
  obtain ⟨hν, hν0, rs, cs, hrpos, hcpos, hcfin, hr0, hconv⟩ := htan
  obtain ⟨lam, -, φ, hφ, hlam⟩ := (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq
    (x := fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) (fun i ↦ mem_univ _)
  have hrpos' : ∀ j, 0 < rs (φ j) := fun j ↦ hrpos _
  have hr0' : Tendsto (fun j ↦ rs (φ j)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  have hconv' : Measure.WeaklyConverges
      (fun j ↦ cs (φ j) • Measure.map (blowUpMap a (rs (φ j))) μ) ν :=
      hconv.comp hφ.tendsto_atTop
  have hseq' : ∀ j, Measure.Regular (cs (φ j) • Measure.map (blowUpMap a (rs (φ j))) μ) :=
    fun j ↦ regular_smul_map_blowUp hμ a (hrpos _).ne' (hcfin _)
  have hlamfin : lam ≠ ∞ :=
    tangent_scaling_lt_top hd ht hr₀ haB hlower hrpos' hr0' hlam hseq' hν hconv'
  have hlampos : 0 < lam :=
    tangent_scaling_pos hd hr₀ haB hupper hrpos' hr0' hlam hν0 hseq' hν hconv'
  have hsmall : ∀ β : ℝ≥0∞, 0 < β → ∀ R : ℝ, 0 < R → ∀ᶠ j in atTop,
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ closedBall a (rs (φ j) * R) →
        Disjoint S B → cs (φ j) * μ S ≤ β :=
    fun β hβ R hR ↦ tangent_smul_measure_le_of_disjoint (mul_pos ht hd) hd hr₀ haB hupper
      hlower hdens hrpos' hr0' hseq' hν hconv' hR hβ
  refine ⟨ENNReal.ofReal d * lam, ENNReal.mul_pos (ENNReal.ofReal_pos.2 hd).ne' hlampos.ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlamfin, ?_, ?_⟩
  · intro x hx ρ hρ
    have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        ∃ y ∈ B, dist y (a + rs (φ j) • x) < rs (φ j) * ε :=
      fun ε hε ↦ tangent_exists_nearby_point_of_density (mul_pos ht hd) hd hr₀ haB hupper
        hlower hdens hrpos' hr0' hseq' hν hconv' hx hε
    have hlo :=
      le_tangent_closedBall hd.le ht.le hr₀ hlower hrpos' hr0' hlam hlamfin hseq' hν hconv'
      hnear hρ
    refine le_trans (le_of_eq ?_) hlo
    rw [ENNReal.ofReal_mul (mul_nonneg ht.le hd.le), ENNReal.ofReal_mul ht.le]
    ring
  · intro x ρ hρ
    have hup := tangent_closedBall_le_of_ball_bounds hd.le hr₀ hballbd hrpos' hr0' hlam
      hlamfin hseq' hν hconv' hsmall x hρ
    refine le_trans hup (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hd.le]
    ring

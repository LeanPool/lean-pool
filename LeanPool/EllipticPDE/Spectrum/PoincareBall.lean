/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Spectrum.PoincareWirtinger
public import LeanPool.EllipticPDE.Extension.GraphOperator
public import LeanPool.EllipticPDE.Extension.Translate
public import LeanPool.EllipticPDE.Analysis.Dilation


/-!
# Poincaré's inequality on a ball

Evans §5.8.1 Theorem 2: one constant, depending on the dimension alone at `p = 2`, bounds the
`L²` distance of a class on any ball from its mean over that ball by the radius times the `L²`
norm of its gradient. The case of the unit ball is `poincare_wirtinger_ball`; the general ball
is taken onto it by the affine map `y ↦ r y + x`, under which Lebesgue measure scales by
`r^d`, the mean is unchanged, a weak gradient picks up the factor `r`, and the `L²` seminorm
on the unit ball is the seminorm on the ball scaled by `r^{-d/2}`, which cancels between the
two sides.

The affine map is a measure-preserving map from the unit ball with Lebesgue measure to the
ball with Lebesgue measure scaled by `r^{-d}`, which is what makes every transport a one-line
application of Mathlib's `MeasurePreserving` API.

## Main declarations

* `EllipticPdes.Sobolev.affineBall`: the map `y ↦ r y + x`.
* `EllipticPdes.Sobolev.measurePreserving_affineBall`: its measure transport.
* `EllipticPdes.Sobolev.hasWeakGradOn_comp_affineBall`: a weak gradient transported through
  it.
* `EllipticPdes.Sobolev.poincare_ball`: the inequality.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.8.1 Theorem 2 (p. 291).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Analysis (partialD_comp_smul)
open EllipticPdes.Extension (hasC1Boundary_ball mem_W12_of_hasWeakGradOn
  measurableEmbedding_translate partialD_comp_translate exists_lt_radius_of_isCompact_subset_ball)

variable {d : ℕ}

/-! ### The affine map of the unit ball onto a ball -/

/-- The map `y ↦ r y + x` of the unit ball onto the ball of centre `x` and radius `r`. -/
def affineBall (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := r • y + x

theorem affineBall_preimage_ball (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    affineBall x r ⁻¹' ball x r = ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  ext y
  simp only [affineBall, mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, sub_zero]
  constructor <;> intro h <;> nlinarith [norm_nonneg y]

theorem measurableEmbedding_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : r ≠ 0) :
    MeasurableEmbedding (affineBall x r) :=
  (measurableEmbedding_translate x).comp (MeasurableEquiv.smul₀ r hr).measurableEmbedding

/-- The factor by which Lebesgue measure scales under the map, as a measure multiplier. -/
def ballScale (d : ℕ) (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal |(r ^ d)⁻¹|

theorem ballScale_ne_zero {r : ℝ} (hr : 0 < r) : ballScale d r ≠ 0 := by
  rw [ballScale, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem ballScale_ne_top (r : ℝ) : ballScale d r ≠ ⊤ := ENNReal.ofReal_ne_top

theorem ballScale_toReal {r : ℝ} (hr : 0 < r) : (ballScale d r).toReal = (r ^ d)⁻¹ := by
  rw [ballScale, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity)]

/-- **Measure transport of the affine map.** From the unit ball with Lebesgue measure to the
ball with Lebesgue measure scaled by `r^{-d}`. -/
theorem measurePreserving_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    MeasurePreserving (affineBall x r) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      (ballScale d r • volume.restrict (ball x r)) := by
  have h1 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin d) => r • y) volume
      (ballScale d r • volume) :=
    ⟨measurable_const_smul r, by
      rw [Measure.map_addHaar_smul volume hr.ne', finrank_euclideanSpace_fin]; rfl⟩
  have h2 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin d) => y + x)
      (ballScale d r • volume) (ballScale d r • volume) :=
    (measurePreserving_add_right volume x).smul_measure _
  have h3 : MeasurePreserving (affineBall x r) volume (ballScale d r • volume) := h2.comp h1
  have h4 := h3.restrict_preimage (s := ball x r) measurableSet_ball
  rwa [affineBall_preimage_ball x hr, Measure.restrict_smul] at h4

/-- Transport of an integral over the ball. -/
theorem integral_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, f (affineBall x r y)
      = (ballScale d r).toReal * ∫ z in ball x r, f z := by
  rw [(measurePreserving_affineBall x hr).integral_comp (measurableEmbedding_affineBall x hr.ne')
    f, integral_smul_measure, smul_eq_mul]

/-- Transport of an `L²` seminorm over the ball. -/
theorem eLpNorm_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (ball x r))) :
    eLpNorm (f ∘ affineBall x r) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = ballScale d r ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 (volume.restrict (ball x r)) := by
  rw [eLpNorm_comp_measurePreserving (hf.smul_measure _) (measurePreserving_affineBall x hr),
    eLpNorm_smul_measure_of_ne_top (by norm_num) f _ hf, smul_eq_mul]

/-- The mean over the ball is the mean over the unit ball of the transported function. -/
theorem average_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ⨍ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, f (affineBall x r y) = ⨍ z in ball x r, f z := by
  rw [setAverage_eq, setAverage_eq, integral_comp_affineBall x hr, smul_eq_mul, smul_eq_mul,
    measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ballScale_toReal hr]
  have hV : (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (isOpen_ball.measure_pos volume (nonempty_ball.mpr one_pos)).ne'
      measure_ball_lt_top.ne).ne'
  have hr' : r ^ d ≠ 0 := by positivity
  field_simp

/-! ### The weak gradient through the affine map -/

/-- **Weak gradient transported through the affine map**, which picks up the factor `r`. A test
function on the unit ball is pushed forward to one on the ball, whose partial derivative is
`r⁻¹` times the original's, and the integrals transport by the measure-preserving map. -/
theorem hasWeakGradOn_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : HasWeakGradOn (ball x r) u g) :
    HasWeakGradOn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (u ∘ affineBall x r)
      fun k y => r * g k (affineBall x r y) := by
  intro φ hφc hφcs hφB k
  have hr0 : r ≠ 0 := hr.ne'
  -- the test function pushed forward to the ball
  set ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun z => φ (r⁻¹ • (z + -x)) with hψ
  have hF : Differentiable ℝ fun w : EuclideanSpace ℝ (Fin d) => φ (r⁻¹ • w) := by
    intro w
    exact ((hφc.differentiable (by simp)) _).comp w (differentiableAt_id.const_smul r⁻¹)
  have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφc.comp ((contDiff_id.add contDiff_const).const_smul r⁻¹)
  have hψcs : HasCompactSupport ψ := by
    have := hφcs.comp_homeomorph
      ((Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr0)))
    exact this
  have hψB : tsupport ψ ⊆ ball x r := by
    obtain ⟨ρ, hρ1, hρ0, hK⟩ := exists_lt_radius_of_isCompact_subset_ball one_pos
      hφcs.isCompact hφB
    refine (closure_minimal ?_ isClosed_closedBall).trans
      (closedBall_subset_ball (by nlinarith : r * ρ < r))
    intro z hz
    have h1 : r⁻¹ • (z + -x) ∈ tsupport φ := subset_tsupport _ hz
    have h2 := hK h1
    rw [mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr] at h2
    rw [mem_closedBall, dist_eq_norm, ← sub_eq_add_neg] at *
    exact ((inv_mul_lt_iff₀ hr).mp h2).le
  have hkey := hw ψ hψc hψcs hψB k
  -- the partial derivative of the pushed-forward test function
  have hψd : ∀ z, partialD k ψ z = r⁻¹ * partialD k φ (r⁻¹ • (z + -x)) := by
    intro z
    have h1 : partialD k ψ z
        = partialD k (fun w : EuclideanSpace ℝ (Fin d) => φ (r⁻¹ • w)) (z + -x) :=
      partialD_comp_translate hF (-x) k z
    rw [h1, partialD_comp_smul (hφc.differentiable (by simp)) r⁻¹ k]
  have hA : ∀ y : EuclideanSpace ℝ (Fin d), r⁻¹ • (affineBall x r y + -x) = y := by
    intro y
    simp only [affineBall, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hψA : ∀ y, ψ (affineBall x r y) = φ y := fun y => by simp only [hψ, hA]
  have hψdA : ∀ y, partialD k ψ (affineBall x r y) = r⁻¹ * partialD k φ y := fun y => by
    rw [hψd, hA]
  -- transport of the two integrals
  have hc0 : 0 < (ballScale d r).toReal :=
    ENNReal.toReal_pos (ballScale_ne_zero hr) (ballScale_ne_top r)
  have e1 : ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, (u ∘ affineBall x r) y * partialD k φ y
      = r * ((ballScale d r).toReal * ∫ z in ball x r, u z * partialD k ψ z) := by
    rw [← integral_comp_affineBall x hr, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply, hψdA]
    field_simp
  have e2 : ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, r * g k (affineBall x r y) * φ y
      = r * ((ballScale d r).toReal * ∫ z in ball x r, g k z * ψ z) := by
    rw [← integral_comp_affineBall x hr, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hψA]
    ring
  rw [e1, e2, hkey]
  ring

/-! ### The inequality -/

/-- The unit ball, as a local abbreviation for the proof below. -/
local notation "B₁" => Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1

/-- **Poincaré's inequality on a ball** (Evans §5.8.1 Theorem 2 at `p = 2`). One constant,
depending on the dimension alone, bounds the `L²` distance of a class on any ball from its
mean over the ball by the radius times the `L²` norm of its gradient. -/
theorem poincare_ball (hd : 0 < d) :
    ∃ C : ℝ, ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        MemLp u 2 (volume.restrict (ball x r)) →
        (∀ k, MemLp (g k) 2 (volume.restrict (ball x r))) →
        HasWeakGradOn (ball x r) u g →
        (eLpNorm (fun y => u y - ⨍ z in ball x r, u z) 2 (volume.restrict (ball x r))).toReal
          ≤ C * r * Real.sqrt (∑ k, (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal ^ 2) := by
  classical
  obtain ⟨C, hC⟩ := poincare_wirtinger_ball hd
  refine ⟨C, fun x r hr u g hu hg hw => ?_⟩
  set s : ℝ≥0∞ := ballScale d r ^ (1 / (2 : ℝ≥0∞)).toReal with hs
  have hs0 : s ≠ 0 := by
    rw [hs, ne_eq, ENNReal.rpow_eq_zero_iff]
    simp only [not_or, not_and]
    exact ⟨fun h => absurd h (ballScale_ne_zero hr), fun h => absurd h (ballScale_ne_top r)⟩
  have hstop : s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (ballScale_ne_top r)
  have hspos : 0 < s.toReal := ENNReal.toReal_pos hs0 hstop
  have hMP := measurePreserving_affineBall x hr
  -- the transported class and its gradient
  have hv : MemLp (u ∘ affineBall x r) 2 (volume.restrict B₁) :=
    (hu.smul_measure (ballScale_ne_top r)).comp_measurePreserving hMP
  have hh : ∀ k, MemLp (fun y => r * g k (affineBall x r y)) 2 (volume.restrict B₁) := fun k =>
    (((hg k).smul_measure (ballScale_ne_top r)).comp_measurePreserving hMP).const_mul r
  have hwg : HasWeakGradOn B₁ (u ∘ affineBall x r) fun k y => r * g k (affineBall x r y) :=
    hasWeakGradOn_comp_affineBall x hr hw
  set V : H1amb B₁ := WithLp.toLp 2 (Fin.cons (hv.toLp _) fun k => (hh k).toLp _) with hV
  have hVW : V ∈ W12 B₁ := mem_W12_of_hasWeakGradOn hv hh hwg
  have hV0 : V 0 = hv.toLp _ := by rw [hV, PiLp.toLp_apply, Fin.cons_zero]
  have hVk : ∀ k : Fin d, V k.succ = (hh k).toLp _ := fun k => by
    rw [hV, PiLp.toLp_apply, Fin.cons_succ]
  have hineq := hC ⟨V, hVW⟩
  -- the mean of the transported class is the mean over the ball
  set m : ℝ := ⨍ z in ball x r, u z with hm
  have hmean : meanL2 isBounded_ball (embW12 B₁ ⟨V, hVW⟩) = m := by
    rw [embW12_apply]
    change meanL2 isBounded_ball (V 0) = m
    rw [hV0, meanL2_apply, integral_congr_ae hv.coeFn_toLp, hm, ← average_comp_affineBall x hr,
      setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  -- the left side
  have hL : ‖embW12 B₁ ⟨V, hVW⟩
        - constL2 isBounded_ball (meanL2 isBounded_ball (embW12 B₁ ⟨V, hVW⟩))‖
      = s.toReal * (eLpNorm (fun y => u y - m) 2 (volume.restrict (ball x r))).toReal := by
    rw [hmean, embW12_apply]
    change ‖V 0 - constL2 isBounded_ball m‖ = _
    rw [hV0, Lp.norm_def]
    have hae : ((hv.toLp (u ∘ affineBall x r) - constL2 isBounded_ball m : L2D B₁) :
        EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict B₁] (fun y => u y - m) ∘ affineBall x r := by
      filter_upwards [Lp.coeFn_sub (hv.toLp (u ∘ affineBall x r)) (constL2 isBounded_ball m),
        hv.coeFn_toLp,
        coeFn_constL2 isBounded_ball m] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      rfl
    have hasm : AEStronglyMeasurable (fun y => u y - m) (volume.restrict (ball x r)) :=
      hu.aestronglyMeasurable.sub aestronglyMeasurable_const
    rw [eLpNorm_congr_ae hae, eLpNorm_comp_affineBall x hr hasm, ENNReal.toReal_mul]
  -- the right side
  have hR : ∀ k : Fin d, ‖((⟨V, hVW⟩ : W12 B₁) : H1amb B₁) k.succ‖
      = r * s.toReal * (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal := by
    intro k
    change ‖V k.succ‖ = _
    rw [hVk, Lp.norm_toLp]
    have : (fun y => r * g k (affineBall x r y)) = r • (g k ∘ affineBall x r) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [this, eLpNorm_const_smul, eLpNorm_comp_affineBall x hr (hg k).aestronglyMeasurable,
        ENNReal.toReal_mul,
      ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos hr]
    ring
  rw [hL] at hineq
  simp only [hR] at hineq
  -- divide by the common factor
  have hsum : Real.sqrt (∑ k : Fin d,
      (r * s.toReal * (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal) ^ 2)
      = r * s.toReal
        * Real.sqrt (∑ k, (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal ^ 2) := by
    have h : ∀ k : Fin d,
        (r * s.toReal * (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal) ^ 2
        = (r * s.toReal) ^ 2 * (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal ^ 2 :=
      fun k => by ring
    simp_rw [h]
    rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsum] at hineq
  have hfinal : s.toReal * (eLpNorm (fun y => u y - m) 2 (volume.restrict (ball x r))).toReal
      ≤ s.toReal * (C * r * Real.sqrt (∑ k, (eLpNorm (g k) 2
        (volume.restrict (ball x r))).toReal ^ 2)) := by
    linarith [hineq]
  exact le_of_mul_le_mul_left hfinal hspos

end EllipticPdes.Sobolev

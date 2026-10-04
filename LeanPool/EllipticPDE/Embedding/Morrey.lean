/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.RayIntegral
public import LeanPool.EllipticPDE.Embedding.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique


/-!
# Riesz-kernel `Lᵖ` bound for the Morrey embedding

For `p > d` the `(d-1)`-Riesz potential of an `Lᵖ` function over a ball of radius `R`
centred at the base point is controlled by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ}`. The exponent
`1 - d/p` is the Morrey Hölder exponent, produced here from Hölder's inequality with the
conjugate exponent `q = p/(p-1)` together with the radial `L^q` norm of the singular kernel.

The kernel-norm computation is isolated in the private lemma `setIntegral_ball_dist_rpow`,
a closed-form value for the radial integral `∫_{B(x,R)} dist x y^s` over a ball centred at the
singularity, valid for `s > -d`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Radial power integral over a ball centred at the singularity.** For `s > -d`, the integral
of `dist x ·^s` over the ball `B(x, R)` has the closed form `d · ω_d · R^{s+d}/(s+d)`, where
`ω_d` is the volume of the unit ball. Proof: translate to the origin, then apply the polar
change of variables `integral_fun_norm_addHaar` and evaluate the resulting `1`-D radial integral
with `integral_rpow`. This is the isolated kernel-norm computation feeding the Hölder step. -/
private theorem setIntegral_ball_dist_rpow (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : -(d : ℝ) < s) :
    ∫ y in ball x R, dist x y ^ s ∂volume
      = (d : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          * (R ^ (s + (d : ℝ)) / (s + (d : ℝ))) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  -- Translate the integral to the origin.
  have hmp : MeasurePreserving (fun w : EuclideanSpace ℝ (Fin d) => x + w) volume volume :=
    measurePreserving_add_left volume x
  have hpre : (fun w : EuclideanSpace ℝ (Fin d) => x + w) ⁻¹' ball x R
      = ball (0 : EuclideanSpace ℝ (Fin d)) R := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  rw [show (∫ y in ball x R, dist x y ^ s ∂volume)
        = ∫ w in ball (0 : EuclideanSpace ℝ (Fin d)) R, ‖w‖ ^ s ∂volume from by
    rw [← hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft x)
          (fun y => dist x y ^ s) (ball x R), hpre]
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    rw [dist_eq_norm, show x - (x + w) = -w from by abel, norm_neg]]
  -- Rewrite as an integral over the whole space of a radial function.
  rw [← integral_indicator
      (measurableSet_ball : MeasurableSet (ball (0 : EuclideanSpace ℝ (Fin d)) R))]
  rw [show (fun w : EuclideanSpace ℝ (Fin d) => (ball (0 : EuclideanSpace ℝ (Fin d)) R).indicator
        (fun w => ‖w‖ ^ s) w) = (fun w => (Set.Iio R).indicator (fun t : ℝ => t ^ s) ‖w‖) from by
    funext w
    by_cases hw : ‖w‖ < R
    · rw [Set.indicator_of_mem (by rw [mem_ball, dist_zero_right]; exact hw),
        Set.indicator_of_mem (show ‖w‖ ∈ Set.Iio R from hw)]
    · rw [Set.indicator_of_notMem (by rw [mem_ball, dist_zero_right]; exact hw),
        Set.indicator_of_notMem (show ‖w‖ ∉ Set.Iio R from hw)]]
  rw [integral_fun_norm_addHaar volume (fun t : ℝ => (Set.Iio R).indicator (fun u => u ^ s) t)]
  -- Evaluate the resulting radial integral.
  have hinner : ∫ y in Set.Ioi (0 : ℝ),
        y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1)
          • (Set.Iio R).indicator (fun u => u ^ s) y
      = R ^ (s + (d : ℝ)) / (s + (d : ℝ)) := by
    rw [finrank_euclideanSpace_fin]
    rw [show (fun y : ℝ => y ^ (d - 1) • (Set.Iio R).indicator (fun u => u ^ s) y)
          = (Set.Iio R).indicator (fun y : ℝ => y ^ (d - 1) * y ^ s) from by
      funext y
      by_cases hy : y ∈ Set.Iio R
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, smul_eq_mul]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]]
    rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
    rw [setIntegral_congr_fun measurableSet_Ioo
        (g := fun y : ℝ => y ^ (((d - 1 : ℕ) : ℝ) + s)) (fun y hy => ?_)]
    · rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR.le,
        integral_rpow (Or.inl (by rw [Nat.cast_sub hd]; push_cast; linarith [hs]))]
      rw [show (((d - 1 : ℕ) : ℝ) + s) + 1 = s + (d : ℝ) from by
          rw [Nat.cast_sub hd]; push_cast; ring]
      rw [Real.zero_rpow (ne_of_gt (show (0 : ℝ) < s + (d : ℝ) by linarith [hs])), sub_zero]
    · obtain ⟨hy0, _⟩ := hy
      rw [← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy0]
  rw [hinner, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Riesz-kernel `Lᵖ` bound.** For `p > d` there is a constant `Cdp` (depending only on
`d, p`) such that the `(d-1)`-Riesz potential of any `Lᵖ` function over a ball of radius
`R` centred at the base point is bounded by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ}`. The exponent
`1 - d/p` is precisely the Morrey Hölder exponent. -/
theorem exists_kernel_bound (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ Cdp : ℝ≥0, ∀ (x : EuclideanSpace ℝ (Fin d)) {R : ℝ}, 0 < R →
      ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ),
        MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x R)) →
        ∫ y in Metric.ball x R, ‖g y‖ / dist x y ^ (d - 1)
          ≤ (Cdp : ℝ) * R ^ (1 - (d : ℝ) / p)
              * (eLpNorm g (ENNReal.ofReal p) (volume.restrict (Metric.ball x R))).toReal := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp1 : (1 : ℝ) < p := lt_of_le_of_lt h1d hp
  obtain ⟨q, hpq⟩ : ∃ q, p.HolderConjugate q := ⟨_, Real.HolderConjugate.conjExponent hp1⟩
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hqconj : q = p / (p - 1) := hpq.conjugate_eq
  have hpm1 : 0 < p - 1 := hpq.sub_one_pos
  have hp0' : p ≠ 0 := hp0.ne'
  have hpm1' : p - 1 ≠ 0 := hpm1.ne'
  have hq0' : q ≠ 0 := hq0.ne'
  set n : ℕ := d - 1 with hn_def
  have hn : ((n : ℝ)) = (d : ℝ) - 1 := by rw [hn_def, Nat.cast_sub hd, Nat.cast_one]
  set s : ℝ := (-(n : ℝ)) * q with hs_def
  set ω : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω_def
  have hω_pos : 0 < ω := by
    rw [hω_def, measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos volume 0 one_pos, measure_ball_lt_top⟩
  have ha_eq : s + (d : ℝ) = (p - (d : ℝ)) / (p - 1) := by
    rw [hs_def, hn, hqconj]; field_simp; ring
  have ha_pos : 0 < s + (d : ℝ) := by
    rw [ha_eq]; exact div_pos (by linarith) hpm1
  have hs_lb : -(d : ℝ) < s := by linarith [ha_pos]
  have haq : (s + (d : ℝ)) / q = 1 - (d : ℝ) / p := by
    rw [ha_eq, hqconj]; field_simp
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hp_netop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCnn : 0 ≤ ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hω_pos.le) ha_pos.le) _
  refine ⟨⟨((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q), hCnn⟩, ?_⟩
  intro x R hR g hmem
  -- Almost-everywhere the running point differs from the centre.
  have hxne : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), y ≠ x := by
    rw [ae_iff, show {y : EuclideanSpace ℝ (Fin d) | ¬ y ≠ x} = {x} from by ext z; simp]
    exact measure_singleton x
  -- Pointwise: the `q`-power of the kernel is a `dist`-power with exponent `s`.
  have hpt : ∀ y : EuclideanSpace ℝ (Fin d), y ≠ x →
      ((dist x y ^ n)⁻¹) ^ q = dist x y ^ s := by
    intro y hy
    have hD : 0 < dist x y := dist_pos.mpr (fun h => hy h.symm)
    rw [← Real.rpow_natCast (dist x y) n, ← Real.rpow_neg hD.le, ← Real.rpow_mul hD.le, hs_def]
  -- Integrability of the `dist`-power on the ball (Task 4b pattern).
  have hdist_int : IntegrableOn (fun y => dist x y ^ s) (ball x R) volume := by
    have hfrk : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]; exact hd
    have hmp : MeasurePreserving (fun w : EuclideanSpace ℝ (Fin d) => x + w) volume volume :=
      measurePreserving_add_left volume x
    rw [← hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft x)]
    rw [show (fun w : EuclideanSpace ℝ (Fin d) => x + w) ⁻¹' ball x R
        = ball (0 : EuclideanSpace ℝ (Fin d)) R from by
      ext w; simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left,
        sub_zero]]
    rw [show (fun y => dist x y ^ s) ∘ (fun w : EuclideanSpace ℝ (Fin d) => x + w)
        = fun w => ‖w‖ ^ s from by
      funext w
      simp only [Function.comp_apply, dist_eq_norm, show x - (x + w) = -w from by abel, norm_neg]]
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := 1) (α := -s) hfrk
    · rw [finrank_euclideanSpace_fin]; linarith [hs_lb]
    · filter_upwards with w
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_neg, one_mul]
    · exact (measurable_norm.pow measurable_const).aestronglyMeasurable
  -- Transfer integrability to the kernel's `q`-power.
  have hae : (fun y => dist x y ^ s)
      =ᵐ[volume.restrict (ball x R)] (fun y => ((dist x y ^ n)⁻¹) ^ q) := by
    filter_upwards [ae_restrict_of_ae hxne] with y hy
    exact (hpt y hy).symm
  have hKint : IntegrableOn (fun y => ((dist x y ^ n)⁻¹) ^ q) (ball x R) volume :=
    hdist_int.congr hae
  -- Membership of the kernel in `L^q`.
  have hpe : ∀ y : EuclideanSpace ℝ (Fin d),
      ‖(dist x y ^ n)⁻¹‖ₑ ^ q = ‖((dist x y ^ n)⁻¹) ^ q‖ₑ := by
    intro y
    have ha : (0 : ℝ) ≤ (dist x y ^ n)⁻¹ := by positivity
    rw [← ofReal_norm ((dist x y ^ n)⁻¹ ^ q), ← ofReal_norm ((dist x y ^ n)⁻¹),
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg (Real.rpow_nonneg ha q), ENNReal.ofReal_rpow_of_nonneg ha hq0.le]
  have hKmeas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin d) =>
      (dist x y ^ n)⁻¹) (volume.restrict (ball x R)) := by
    fun_prop
  have hKmem : MemLp (fun y => (dist x y ^ n)⁻¹) (ENNReal.ofReal q)
      (volume.restrict (ball x R)) := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq0) ENNReal.ofReal_ne_top
        hKmeas,
      ENNReal.toReal_ofReal hq0.le, lintegral_congr hpe]
    exact hasFiniteIntegral_iff_enorm.mp hKint.2
  -- Hölder's inequality at the Bochner level.
  have hf_nn : 0 ≤ᵐ[volume.restrict (ball x R)] (fun y => ‖g y‖) :=
    ae_of_all _ (fun y => norm_nonneg _)
  have hK_nn : 0 ≤ᵐ[volume.restrict (ball x R)] (fun y => (dist x y ^ n)⁻¹) :=
    ae_of_all _ (fun y => by positivity)
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf_nn hK_nn hmem.norm hKmem
  -- The `Lᵖ` factor equals the `toReal` of the `eLpNorm`.
  have hpint_nn : 0 ≤ ∫ y in ball x R, ‖g y‖ ^ p ∂volume :=
    integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) _)
  have heLp : (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball x R))).toReal
      = (∫ y in ball x R, ‖g y‖ ^ p ∂volume) ^ (1 / p) := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm hp_ne0 hp_netop, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hpint_nn _), one_div]
  -- The kernel factor equals the constant times `R^{1-d/p}`.
  have hker_val : ∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂volume
      = (d : ℝ) * ω * (R ^ (s + (d : ℝ)) / (s + (d : ℝ))) := by
    rw [setIntegral_congr_ae measurableSet_ball (g := fun y => dist x y ^ s)
        (by filter_upwards [hxne] with y hy; exact fun _ => hpt y hy),
      setIntegral_ball_dist_rpow hd x hR hs_lb, ← hω_def]
  have hKfac : (∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂volume) ^ (1 / q)
      = ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p) := by
    rw [hker_val]
    rw [show (d : ℝ) * ω * (R ^ (s + (d : ℝ)) / (s + (d : ℝ)))
        = ((d : ℝ) * ω / (s + (d : ℝ))) * R ^ (s + (d : ℝ)) from by field_simp]
    rw [Real.mul_rpow (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hω_pos.le) ha_pos.le)
        (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le, mul_one_div, haq]
  -- Assemble.
  calc ∫ y in ball x R, ‖g y‖ / dist x y ^ n ∂volume
      = ∫ y in ball x R, ‖g y‖ * (dist x y ^ n)⁻¹ ∂volume := by simp_rw [div_eq_mul_inv]
    _ ≤ (∫ y in ball x R, ‖g y‖ ^ p ∂volume) ^ (1 / p)
          * (∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂volume) ^ (1 / q) := holder
    _ = (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball x R))).toReal
          * (((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p)) := by
        rw [← heLp, hKfac]
    _ = ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p)
          * (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball x R))).toReal := by ring

/-- **Gradient norm is `Lᵖ` on a ball.** For a smooth `φ` the map `y ↦ ‖fderiv ℝ φ y‖` is
continuous, hence bounded on the compact closed ball, hence `Lᵖ` on the finite-measure
restricted ball. This is the `MemLp` witness fed to `exists_kernel_bound`. -/
private theorem memLp_norm_fderiv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {p : ℝ} (z : EuclideanSpace ℝ (Fin d)) {r : ℝ} (_hr : 0 < r) :
    MemLp (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p) (volume.restrict (Metric.ball z r)) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball z r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => ‖fderiv ℝ φ y‖) :=
    (hφ.continuous_fderiv (by simp)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound hcont.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  exact hC y (ball_subset_closedBall hy)

/-- **Subset Riesz-kernel bound.** The indicator corollary of `exists_kernel_bound`: for a
measurable subset `S` of the ball `ball x R` (singularity at the centre `x`), the `(d-1)`-Riesz
potential of an `Lᵖ` function `g` over `S` is bounded by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ(S)}`, the
`Lᵖ` norm being taken over `S`. This lets the averaging domain of the Morrey estimate shrink to a
convex lens while retaining the correct radial scaling. -/
private theorem exists_kernel_bound_subset (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ Cdp : ℝ≥0, ∀ (x : EuclideanSpace ℝ (Fin d)) {R : ℝ}, 0 < R →
      ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ),
        MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x R)) →
        ∀ {S : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet S → S ⊆ Metric.ball x R →
          ∫ y in S, ‖g y‖ / dist x y ^ (d - 1)
            ≤ (Cdp : ℝ) * R ^ (1 - (d : ℝ) / p)
                * (eLpNorm g (ENNReal.ofReal p) (volume.restrict S)).toReal := by
  obtain ⟨Cdp, hCdp⟩ := exists_kernel_bound hd hp
  refine ⟨Cdp, ?_⟩
  intro x R hR g hg S hSmeas hSsub
  have key := hCdp x hR (S.indicator g) (hg.indicator hSmeas)
  have hfun : (fun y => ‖(S.indicator g) y‖ / dist x y ^ (d - 1))
      = S.indicator (fun y => ‖g y‖ / dist x y ^ (d - 1)) := by
    funext y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, norm_zero, zero_div]
  rw [hfun, setIntegral_indicator hSmeas, Set.inter_eq_right.mpr hSsub,
    eLpNorm_indicator_eq_eLpNorm_restrict hSmeas,
    Measure.restrict_restrict_of_subset hSsub] at key
  exact key

/-- **Lens measure lower bound.** For `x, x'` in `ball c r` with `ρ = dist x x' > 0`, the convex
lens `ball x (2ρ) ∩ ball x' (2ρ) ∩ ball c r`, which contains both points and lies inside the
domain, has volume at least `(ρ/4)^d · ω_d`, where `ω_d` is the unit-ball volume. Proof: exhibit
an inscribed ball `ball q (ρ/4)`, with `q` the midpoint pushed towards the centre `c` when the
midpoint sits near the boundary, contained in all three balls, and compare volumes. -/
private theorem lens_volume_lower_bound (_hd : 0 < d) (c x x' : EuclideanSpace ℝ (Fin d))
    {r : ℝ} (_hr : 0 < r) (hx : x ∈ ball c r) (hx' : x' ∈ ball c r) (hne : x ≠ x') :
    (dist x x' / 4) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      ≤ volume.real (ball x (2 * dist x x') ∩ ball x' (2 * dist x x') ∩ ball c r) := by
  set ρ := dist x x' with hρ_def
  have hρ_pos : 0 < ρ := dist_pos.mpr hne
  have hρ4 : (0 : ℝ) < ρ / 4 := by linarith
  set m := midpoint ℝ x x' with hm_def
  have hmc : dist m c < r := by
    have hmem : m ∈ ball c r := (convex_ball c r).midpoint_mem hx hx'
    rwa [mem_ball] at hmem
  have hdmx : dist m x = ρ / 2 := by
    rw [hm_def, dist_midpoint_left, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      ← hρ_def]
    ring
  have hdmx' : dist m x' = ρ / 2 := by
    rw [hm_def, dist_midpoint_right, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      ← hρ_def]
    ring
  have hρ_lt : ρ < 2 * r := by
    have h1 : dist x c < r := by rwa [mem_ball] at hx
    have h2 : dist x' c < r := by rwa [mem_ball] at hx'
    calc ρ = dist x x' := hρ_def
      _ ≤ dist x c + dist c x' := dist_triangle x c x'
      _ = dist x c + dist x' c := by rw [dist_comm c x']
      _ < 2 * r := by linarith
  have hr2 : (0 : ℝ) < r - ρ / 2 := by linarith
  -- Choose an inscribed centre `q` with `dist q c ≤ r - ρ/2` and `dist q m ≤ ρ/2`.
  obtain ⟨q, hqc, hqm⟩ : ∃ q : EuclideanSpace ℝ (Fin d),
      dist q c ≤ r - ρ / 2 ∧ dist q m ≤ ρ / 2 := by
    by_cases hcase : dist m c ≤ r - ρ / 2
    · exact ⟨m, hcase, by rw [dist_self]; linarith⟩
    · replace hcase : r - ρ / 2 < dist m c := not_le.mp hcase
      have hDpos : 0 < dist m c := lt_trans hr2 hcase
      set lam := (r - ρ / 2) / dist m c with hlam
      have hlam_nn : 0 ≤ lam := by rw [hlam]; exact div_nonneg hr2.le hDpos.le
      have hlam_lt : lam < 1 := by rw [hlam, div_lt_one hDpos]; exact hcase
      refine ⟨c + lam • (m - c), le_of_eq ?_, ?_⟩
      · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hlam_nn, ← dist_eq_norm, hlam, div_eq_mul_inv, mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hDpos), mul_one]
      · have heq : (c + lam • (m - c)) - m = (1 - lam) • (c - m) := by module
        have hval : dist (c + lam • (m - c)) m = dist m c - (r - ρ / 2) := by
          rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam), ← dist_eq_norm, dist_comm c m,
            sub_mul, one_mul, hlam, div_eq_mul_inv, mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hDpos), mul_one]
        rw [hval]; linarith
  -- The inscribed ball lies inside all three balls.
  have hsub : ball q (ρ / 4) ⊆ ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r := by
    refine subset_inter (subset_inter ?_ ?_) ?_
    · refine ball_subset_ball' ?_
      have hqx : dist q x ≤ ρ := by
        calc dist q x ≤ dist q m + dist m x := dist_triangle q m x
          _ ≤ ρ / 2 + ρ / 2 := by rw [hdmx]; linarith
          _ = ρ := by ring
      linarith
    · refine ball_subset_ball' ?_
      have hqx' : dist q x' ≤ ρ := by
        calc dist q x' ≤ dist q m + dist m x' := dist_triangle q m x'
          _ ≤ ρ / 2 + ρ / 2 := by rw [hdmx']; linarith
          _ = ρ := by ring
      linarith
    · refine ball_subset_ball' ?_
      linarith
  -- Compare volumes.
  have hWtop : volume (ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (fun z hz => hz.2))
  have hvolq : volume.real (ball q (ρ / 4))
      = (ρ / 4) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume q hρ4, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ4.le _), finrank_euclideanSpace_fin, measureReal_def]
  calc (ρ / 4) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      = volume.real (ball q (ρ / 4)) := hvolq.symm
    _ ≤ volume.real (ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r) :=
        ENNReal.toReal_mono hWtop (measure_mono hsub)

/-- **Smooth Morrey Hölder estimate on a ball.** For `p > d` there is a constant `C`,
depending only on `d` and `p`, such that every smooth `φ` is Hölder continuous on `ball c r`
with exponent `1 - d/p` and constant `C · ‖∇φ‖_{Lᵖ(ball c r)}`. This is Gilbarg–Trudinger
Theorem 7.19: the interior Hölder seminorm is controlled by the domain-restricted `Lᵖ` norm of
the gradient. The proof averages over the convex lens
`ball x (2ρ) ∩ ball x' (2ρ) ∩ ball c r`, which contains both points and stays inside the domain,
so the averaging never sees the gradient outside `ball c r`. -/
theorem exists_holder_smooth (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ C : ℝ≥0, ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      ∀ (c : EuclideanSpace ℝ (Fin d)) {r : ℝ}, 0 < r →
        HolderOnWith
          (C * (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball c r))).toNNReal)
          (morreyExponent d p) φ (Metric.ball c r) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp0 : (0 : ℝ) < p := lt_trans hdR hp
  set ω : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω_def
  have hω_pos : 0 < ω := by
    rw [hω_def, measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos volume 0 one_pos, measure_ball_lt_top⟩
  obtain ⟨Cdp, hCdp⟩ := exists_kernel_bound_subset hd hp
  set K : ℝ := 8 ^ d / ((d : ℝ) * ω) * (Cdp : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) with hK_def
  refine ⟨(2 * K).toNNReal, ?_⟩
  intro φ hφ c r hr
  set E := eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p) (volume.restrict (ball c r))
    with hE_def
  have hE_ne_top : E ≠ ⊤ := (memLp_norm_fderiv (p := p) hφ c hr).eLpNorm_ne_top
  intro x hx x' hx'
  by_cases hxx : x = x'
  · subst hxx; simp
  · have hρpos : 0 < dist x x' := dist_pos.mpr hxx
    have hρ4 : (0 : ℝ) < dist x x' / 4 := by positivity
    have h2ρ : (0 : ℝ) < 2 * dist x x' := by positivity
    set W : Set (EuclideanSpace ℝ (Fin d)) :=
      ball x (2 * dist x x') ∩ ball x' (2 * dist x x') ∩ ball c r with hW_def
    have hWmeas : MeasurableSet W :=
      (measurableSet_ball.inter measurableSet_ball).inter measurableSet_ball
    have hWconv : Convex ℝ W :=
      ((convex_ball _ _).inter (convex_ball _ _)).inter (convex_ball _ _)
    have hBlb : (dist x x' / 4) ^ d * ω ≤ volume.real W := by
      have h := lens_volume_lower_bound hd c x x' hr hx hx' hxx
      rwa [← hW_def, ← hω_def] at h
    have hWposR : 0 < volume.real W :=
      lt_of_lt_of_le (mul_pos (pow_pos hρ4 d) hω_pos) hBlb
    have hWposR' : 0 < (volume W).toReal := by rw [← measureReal_def]; exact hWposR
    obtain ⟨hWpos, hWtop⟩ := ENNReal.toReal_pos_iff.mp hWposR'
    have hEW_le_N :
        (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p) (volume.restrict W)).toReal
          ≤ E.toReal :=
      ENNReal.toReal_mono hE_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono (fun z hz => hz.2) le_rfl))
    -- Per-point lens bound (applied at `x` and at `x'`).
    have hkey : ∀ a : EuclideanSpace ℝ (Fin d), a ∈ ball c r → a ∈ W →
        W ⊆ ball a (2 * dist x x') →
        |φ a - ⨍ y in W, φ y| ≤ K * dist x x' ^ (1 - (d : ℝ) / p) * E.toReal := by
      intro a ha haW hWsub_a
      have hint_a : IntegrableOn (fun z => ‖fderiv ℝ φ z‖ / dist a z ^ (d - 1)) W volume :=
        (riesz_potential_integrableOn hφ hd c a hr ha).mono_set (fun z hz => hz.2)
      have hosc := oscillation_le_potential_convex hφ hd a hWmeas hWconv haW hWpos.ne' hWtop.ne
        h2ρ hWsub_a hint_a
      have hmemA : MemLp (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
          (volume.restrict (ball a (2 * dist x x'))) := memLp_norm_fderiv (p := p) hφ a h2ρ
      have hker_a := hCdp a h2ρ (fun y => ‖fderiv ℝ φ y‖) hmemA hWmeas hWsub_a
      simp only [norm_norm] at hker_a
      have hP_nonneg : 0 ≤ ∫ z in W, ‖fderiv ℝ φ z‖ / dist a z ^ (d - 1) :=
        integral_nonneg (fun z => by positivity)
      have hP_bound : (∫ z in W, ‖fderiv ℝ φ z‖ / dist a z ^ (d - 1))
          ≤ (Cdp : ℝ) * (2 * dist x x') ^ (1 - (d : ℝ) / p) * E.toReal :=
        le_trans hker_a (mul_le_mul_of_nonneg_left hEW_le_N (by positivity))
      have hA_bound :
          (2 * dist x x') ^ d / ((d : ℝ) * volume.real W) ≤ 8 ^ d / ((d : ℝ) * ω) := by
        rw [div_le_div_iff₀ (mul_pos hdR hWposR) (mul_pos hdR hω_pos)]
        have hkey84 : (2 * dist x x') ^ d = 8 ^ d * (dist x x' / 4) ^ d := by
          rw [← mul_pow]; congr 1; ring
        calc (2 * dist x x') ^ d * ((d : ℝ) * ω)
            = 8 ^ d * (dist x x' / 4) ^ d * ((d : ℝ) * ω) := by rw [hkey84]
          _ = 8 ^ d * (d : ℝ) * ((dist x x' / 4) ^ d * ω) := by ring
          _ ≤ 8 ^ d * (d : ℝ) * volume.real W :=
              mul_le_mul_of_nonneg_left hBlb (by positivity)
          _ = 8 ^ d * ((d : ℝ) * volume.real W) := by ring
      have hC1_nonneg : (0 : ℝ) ≤ 8 ^ d / ((d : ℝ) * ω) :=
        div_nonneg (by positivity) (mul_nonneg hdR.le hω_pos.le)
      calc |φ a - ⨍ y in W, φ y|
          ≤ (2 * dist x x') ^ d / ((d : ℝ) * volume.real W)
              * ∫ z in W, ‖fderiv ℝ φ z‖ / dist a z ^ (d - 1) := hosc
        _ ≤ 8 ^ d / ((d : ℝ) * ω)
              * ((Cdp : ℝ) * (2 * dist x x') ^ (1 - (d : ℝ) / p) * E.toReal) :=
            mul_le_mul hA_bound hP_bound hP_nonneg hC1_nonneg
        _ = K * dist x x' ^ (1 - (d : ℝ) / p) * E.toReal := by
            rw [Real.mul_rpow (by norm_num) hρpos.le, hK_def]; ring
    -- Assemble the two-point bound.
    have hxW : x ∈ W :=
      Set.mem_inter
        (Set.mem_inter (mem_ball_self h2ρ)
          (mem_ball.mpr (by linarith : dist x x' < 2 * dist x x'))) hx
    have hx'W : x' ∈ W :=
      Set.mem_inter
        (Set.mem_inter (mem_ball.mpr (by rw [dist_comm]; linarith : dist x' x < 2 * dist x x'))
          (mem_ball_self h2ρ)) hx'
    have hbx := hkey x hx hxW (fun z hz => hz.1.1)
    have hbx' := hkey x' hx' hx'W (fun z hz => hz.1.2)
    have hreal : |φ x - φ x'| ≤ 2 * K * E.toReal * dist x x' ^ (1 - (d : ℝ) / p) := by
      have htri := abs_sub_le (φ x) (⨍ y in W, φ y) (φ x')
      rw [abs_sub_comm (⨍ y in W, φ y) (φ x')] at htri
      calc |φ x - φ x'|
          ≤ |φ x - ⨍ y in W, φ y| + |φ x' - ⨍ y in W, φ y| := htri
        _ ≤ K * dist x x' ^ (1 - (d : ℝ) / p) * E.toReal
              + K * dist x x' ^ (1 - (d : ℝ) / p) * E.toReal := add_le_add hbx hbx'
        _ = 2 * K * E.toReal * dist x x' ^ (1 - (d : ℝ) / p) := by ring
    rw [edist_dist (φ x) (φ x'), Real.dist_eq, edist_dist x x', coe_morreyExponent hp hd]
    calc ENNReal.ofReal |φ x - φ x'|
        ≤ ENNReal.ofReal (2 * K * E.toReal * dist x x' ^ (1 - (d : ℝ) / p)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2 * K) * ENNReal.ofReal E.toReal
            * ENNReal.ofReal (dist x x' ^ (1 - (d : ℝ) / p)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ = ((2 * K).toNNReal * E.toNNReal : ℝ≥0)
            * ENNReal.ofReal (dist x x') ^ (1 - (d : ℝ) / p) := by
          rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hE_ne_top, ENNReal.ofReal_toReal hE_ne_top,
            ENNReal.ofReal_rpow_of_pos hρpos]
          rfl

/-- **Operator norm of a derivative bounded by its coordinate partials.** On
`EuclideanSpace ℝ (Fin d)` the operator norm of `fderiv ℝ u y` is bounded by the sum of the
absolute values of the coordinate partial derivatives `partialD k u y`. This converts the
`‖∇u‖`-shaped constant of `exists_holder_smooth` into the coordinate-partial sum. -/
theorem norm_fderiv_le_sum_partialD (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ u y‖ ≤ ∑ k, ‖partialD k u y‖ := by
  set L := fderiv ℝ u y with hL_def
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) (fun x => ?_)
  have hx : x = ∑ k, x k • EuclideanSpace.single k (1 : ℝ) := by
    conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr x]
    simp only [PiLp.basisFun_repr, PiLp.basisFun_apply, EuclideanSpace.single]
  calc ‖L x‖ = ‖L (∑ k, x k • EuclideanSpace.single k (1 : ℝ))‖ := by rw [← hx]
    _ = ‖∑ k, x k • L (EuclideanSpace.single k (1 : ℝ))‖ := by
        rw [map_sum]; simp_rw [map_smul]
    _ ≤ ∑ k, ‖x k • L (EuclideanSpace.single k (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ k, ‖x k‖ * ‖partialD k u y‖ := by simp_rw [norm_smul, hL_def, partialD]
    _ ≤ ∑ k, ‖x‖ * ‖partialD k u y‖ :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x k) (norm_nonneg _)
    _ = (∑ k, ‖partialD k u y‖) * ‖x‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Morrey on a ball in the smooth case.** A smooth `u` with gradient components `gₖ = ∂ₖu`
in `Lᵖ(ball c r)` (`p > d`) is Hölder-`(1−d/p)` on the ball, with constant linear in
`∑ₖ ‖gₖ‖_{Lᵖ(ball c r)}`. This lifts `exists_holder_smooth` to the coordinate-partial form
consumed by the weak-gradient statement, by dominating the operator-norm `Lᵖ` seminorm of the
derivative by the sum of the coordinate-partial `Lᵖ` seminorms. -/
theorem morrey_ball_contDiff (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p)
    (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) u →
      (∀ k, MemLp (fun y => partialD k u y) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball c r))) →
        HolderOnWith
          (C * ∑ k, (eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p)
                      (volume.restrict (Metric.ball c r))).toNNReal)
          (morreyExponent d p) u (Metric.ball c r) := by
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd.ne'
  have hp1 : (1 : ℝ) ≤ p := le_of_lt (lt_of_le_of_lt h1d hp)
  have hpge1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]; exact ENNReal.ofReal_le_ofReal hp1
  obtain ⟨C, hC⟩ := exists_holder_smooth hd hp
  refine ⟨C, fun u hu hmem => ?_⟩
  set μ := volume.restrict (Metric.ball c r) with hμ_def
  -- The coordinate-partial `Lᵖ` seminorms are all finite.
  have hfin : ∀ k, eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ ≠ ⊤ :=
    fun k => (hmem k).eLpNorm_ne_top
  -- Bound the operator-norm seminorm by the sum of coordinate-partial seminorms.
  have hstep : eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p) μ
      ≤ ∑ k, eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ := by
    have h1 : eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p) μ
        ≤ eLpNorm (fun y => ∑ k, ‖partialD k u y‖) (ENNReal.ofReal p) μ := by
      refine eLpNorm_mono
        ((hu.continuous_fderiv (by simp)).norm.aestronglyMeasurable.restrict) fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
      exact norm_fderiv_le_sum_partialD u y
    have h2 : eLpNorm (fun y => ∑ k, ‖partialD k u y‖) (ENNReal.ofReal p) μ
        ≤ ∑ k, eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ := by
      rw [show (fun y => ∑ k, ‖partialD k u y‖)
          = ∑ k, (fun y => ‖partialD k u y‖) from by funext y; rw [Finset.sum_apply]]
      refine (eLpNorm_sum_le hpge1).trans_eq ?_
      exact Finset.sum_congr rfl fun k _ =>
        eLpNorm_norm _ (hmem k).aestronglyMeasurable
    exact h1.trans h2
  -- Transfer to `toNNReal` and to the two-argument `HolderOnWith` constant.
  have hsum_fin : (∑ k, eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ => hfin k
  have htoNN : (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p) μ).toNNReal
      ≤ ∑ k, (eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ).toNNReal := by
    calc (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p) μ).toNNReal
        ≤ (∑ k, eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ).toNNReal :=
          ENNReal.toNNReal_mono hsum_fin hstep
      _ = ∑ k, (eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ).toNNReal :=
          ENNReal.toNNReal_sum fun k _ => hfin k
  have hconst : C * (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p) μ).toNNReal
      ≤ C * ∑ k, (eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p) μ).toNNReal :=
    mul_le_mul_right htoNN C
  -- Apply the smooth Hölder estimate and enlarge the constant.
  intro x hx y hy
  exact (hC u hu c hr x hx y hy).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.mpr hconst) _)

/-- **Gradient-convolution bridge.** If `g` is the weak gradient of `u` on a measurable
set `B` and `ρ` is a normalised bump of outer radius `ε` centred at `0`, then at every interior
point `x` with `Metric.closedBall x ε ⊆ B` the `k`-th partial of the mollification equals the
mollified gradient component: `partialD k (uB ⋆ ρ) x = (gBk ⋆ ρ) x`, where `uB`, `gBk` are the
extensions by zero off `B`. At `B = Set.univ` the support hypothesis is vacuous and the
indicators are the identity, which is the form the `Lᵖ` bootstrap consumes. -/
theorem partialD_convolution_eq_of_hasWeakGradOn
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume)
    (hg : HasWeakGradOn B u g)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (k : Fin d)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : Metric.closedBall x φ.rOut ⊆ B) :
    partialD k
        (B.indicator u ⋆[ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ), volume]
          (φ.normed volume)) x
      = (B.indicator (g k)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ), volume] (φ.normed volume)) x := by
  -- Abbreviations for the bilinear form, the normalised kernel and the indicator extension.
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL_def
  set ρ := φ.normed volume with hρ_def
  have hρ_cs : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρ_cd : ContDiff ℝ (⊤ : ℕ∞) ρ := φ.contDiff_normed
  have hρ_cd1 : ContDiff ℝ 1 ρ := hρ_cd.of_le (by exact_mod_cast le_top)
  have hρ_diff : Differentiable ℝ ρ := hρ_cd.differentiable (by simp)
  have hρ_tsup : tsupport ρ = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) φ.rOut :=
    φ.tsupport_normed_eq
  -- The indicator extension of `u` is integrable, hence locally integrable.
  have huB_int : Integrable (B.indicator u) volume :=
    hu.integrable_indicator hB
  have huB_li : LocallyIntegrable (B.indicator u) volume :=
    huB_int.locallyIntegrable
  -- The scalar bilinear form is ordinary multiplication on the reals.
  have hLmul : ∀ a b : ℝ, L a b = a * b := fun a b => by
    rw [hL_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- Rewrite an indicator-kernel convolution at `x` as a set integral over the ball.
  have conv_setInt : ∀ (w f : EuclideanSpace ℝ (Fin d) → ℝ),
      (B.indicator w ⋆[L, volume] f) x
        = ∫ y in B, w y * f (x - y) := by
    intro w f
    rw [convolution_def, ← MeasureTheory.integral_indicator hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change L (B.indicator w y) (f (x - y))
        = B.indicator (fun z => w z * f (x - z)) y
    rw [hLmul]
    exact (Set.indicator_mul_left (B) w (fun z => f (x - z))).symm
  -- Step 2: differentiate the mollification, reducing the `precompR` convolution.
  have hderiv := hρ_cs.hasFDerivAt_convolution_right (L := L) huB_li hρ_cd1 x
  have step2 : partialD k (B.indicator u ⋆[L, volume] ρ) x
      = (B.indicator u ⋆[L, volume] partialD k ρ) x := by
    have hpd : partialD k (B.indicator u ⋆[L, volume] ρ) x
        = (fderiv ℝ (B.indicator u ⋆[L, volume] ρ) x)
            (EuclideanSpace.single k 1) := rfl
    have hprec :
        (B.indicator u ⋆[L.precompR (EuclideanSpace ℝ (Fin d)), volume]
            fderiv ℝ ρ) x (EuclideanSpace.single k 1)
          = (B.indicator u ⋆[L, volume]
              fun a => (fderiv ℝ ρ a) (EuclideanSpace.single k 1)) x :=
      convolution_precompR_apply (𝕜 := ℝ) (L := L) huB_li (hρ_cs.fderiv (𝕜 := ℝ))
        (hρ_cd.continuous_fderiv (by simp)) x (EuclideanSpace.single k 1)
    rw [hpd, hderiv.fderiv, hprec]
    rfl
  -- Step 3: the test function `ψ y = ρ (x - y)` and its analytic properties.
  set ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ρ (x - y) with hψ_def
  have hpsi_eval : ∀ y, ψ y = ρ (x - y) := fun y => by rw [hψ_def]
  have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ := hρ_cd.comp (contDiff_const.sub contDiff_id)
  have hsupp_sub : Function.support ψ ⊆ Metric.closedBall x φ.rOut := by
    intro y hy
    have hne : ρ (x - y) ≠ 0 := by
      have hy' := Function.mem_support.mp hy
      rwa [hpsi_eval] at hy'
    have hxy : x - y ∈ tsupport ρ := subset_tsupport ρ (Function.mem_support.mpr hne)
    rw [hρ_tsup, Metric.mem_closedBall, dist_zero_right] at hxy
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact hxy
  have hsub_tsup : tsupport ψ ⊆ Metric.closedBall x φ.rOut :=
    closure_minimal hsupp_sub isClosed_closedBall
  have hψ_cs : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x φ.rOut)
      (isClosed_tsupport ψ) hsub_tsup
  have htsup : tsupport ψ ⊆ B := hsub_tsup.trans hx
  -- The `k`-th partial of `ψ` is the reflected partial of `ρ`.
  have hpsi_partial : ∀ y, partialD k ψ y = -(partialD k ρ) (x - y) := by
    intro y
    have hfd : HasFDerivAt ψ ((fderiv ℝ ρ (x - y)).comp
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) y := by
      have h1 : HasFDerivAt (fun z => x - z)
          (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) y :=
        (hasFDerivAt_id y).const_sub x
      exact (hρ_diff (x - y)).hasFDerivAt.comp y h1
    have heval : partialD k ψ y = (fderiv ℝ ψ y) (EuclideanSpace.single k 1) := rfl
    rw [heval, hfd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
      ContinuousLinearMap.id_apply, map_neg, partialD]
  -- Step 4: integrate by parts against `ψ` and cancel the signs.
  have hibp := hg ψ hψ_cd hψ_cs htsup k
  simp only [hpsi_partial, hpsi_eval, mul_neg] at hibp
  rw [MeasureTheory.integral_neg] at hibp
  rw [step2, conv_setInt u (partialD k ρ), conv_setInt (g k) ρ]
  exact neg_inj.mp hibp

/-- **Uniform-limit engine.** A sequence `U n` that is eventually (in `n`) `γ`-Hölder with a common
constant `M` on each pair of points of an open set `B`, and converges pointwise almost everywhere
on `B` to `u`, admits a limit `u'` that is `HolderOnWith M γ` on all of `B` and agrees
with `u` almost everywhere. No Arzelà–Ascoli or continuous-extension machinery is needed: the
Hölder bound provides equicontinuity, density of the almost-everywhere convergence set forces
`U · x` to be Cauchy at every point of `B`, and the closed-ness of `≤` passes the Hölder
inequality to the pointwise limit. -/
private theorem exists_holderOnWith_of_ae_tendsto
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : IsOpen B) {M γ : ℝ≥0} (hγ : 0 < γ)
    {U : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hHol : ∀ x ∈ B, ∀ y ∈ B, ∀ᶠ n in Filter.atTop,
        edist (U n x) (U n y) ≤ (M : ℝ≥0∞) * edist x y ^ (γ : ℝ))
    (hae : ∀ᵐ x ∂(volume.restrict B),
        Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 (u x))) :
    ∃ u' : EuclideanSpace ℝ (Fin d) → ℝ,
      HolderOnWith M γ u' B ∧ u' =ᵐ[volume.restrict B] u := by
  have hγR : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast hγ
  -- The pointwise-convergence set `G` and the fact that its complement is null inside `B`.
  set G : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 (u x))} with hG_def
  have hbad : volume (Gᶜ ∩ B) = 0 := by
    have h0 := ae_iff.mp hae
    rwa [Measure.restrict_apply' hB.measurableSet] at h0
  -- `G` is dense in every open subset of `B`, because its complement is null.
  have hdense : ∀ A : Set (EuclideanSpace ℝ (Fin d)), IsOpen A → A ⊆ B →
      ∀ x ∈ A, ∃ p ∈ A, p ∈ G := by
    intro A hA hAB x hxA
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hA x hxA
    have hpos : 0 < volume A :=
      lt_of_lt_of_le (measure_ball_pos volume x hδ) (measure_mono hball)
    have hnull : volume (A \ G) = 0 :=
      measure_mono_null (t := Gᶜ ∩ B)
        (fun z hz => ⟨hz.2, hAB hz.1⟩) hbad
    have hAG : 0 < volume (A ∩ G) := by
      have hle : volume A ≤ volume (A ∩ G) + volume (A \ G) := by
        conv_lhs => rw [← Set.inter_union_sdiff A G]
        exact measure_union_le _ _
      rw [hnull, add_zero] at hle
      exact lt_of_lt_of_le hpos hle
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hAG.ne'
    exact ⟨p, hp.1, hp.2⟩
  -- Every point of `B` yields a Cauchy, hence convergent, sequence.
  have hconv : ∀ x ∈ B, ∃ ℓ : ℝ, Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 ℓ) := by
    intro x hxB
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε hε => ?_)
    set f : EuclideanSpace ℝ (Fin d) → ℝ := fun y => (M : ℝ) * dist x y ^ (γ : ℝ) with hf_def
    have hfval : ∀ y, f y = (M : ℝ) * dist x y ^ (γ : ℝ) := fun _ => rfl
    have hfnonneg : ∀ y, 0 ≤ f y :=
      fun y => mul_nonneg M.coe_nonneg (Real.rpow_nonneg dist_nonneg _)
    have hfcont : Continuous f :=
      continuous_const.mul ((continuous_const.dist continuous_id).rpow_const
        fun y => Or.inr γ.coe_nonneg)
    set W : Set (EuclideanSpace ℝ (Fin d)) := {y | f y < ε / 3} ∩ B with hW_def
    have hWopen : IsOpen W := (isOpen_lt hfcont continuous_const).inter hB
    have hxW : x ∈ W :=
      ⟨by rw [Set.mem_ofPred_eq, hfval, dist_self, Real.zero_rpow hγR.ne', mul_zero]
          exact div_pos hε (by norm_num), hxB⟩
    obtain ⟨p, hpW, hpG⟩ := hdense W hWopen Set.inter_subset_right x hxW
    have hpB : p ∈ B := hpW.2
    have hpf : f p < ε / 3 := hpW.1
    -- Eventually the sequence at `x` stays within `f p` of the sequence at `p`.
    have hev : ∀ᶠ n in Filter.atTop, dist (U n x) (U n p) ≤ f p := by
      filter_upwards [hHol x hxB p hpB] with n hn
      have hrhs : (M : ℝ≥0∞) * edist x p ^ (γ : ℝ) = ENNReal.ofReal (f p) := by
        rw [hfval, edist_dist, ENNReal.ofReal_mul M.coe_nonneg, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg γ.coe_nonneg]
      rw [hrhs, edist_dist] at hn
      exact (ENNReal.ofReal_le_ofReal_iff (hfnonneg p)).mp hn
    obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.mp hpG.cauchySeq (ε / 3) (div_pos hε (by norm_num))
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max N1 N2, fun m hm n hn => ?_⟩
    have e1 : dist (U m x) (U m p) ≤ f p := hN2 m (le_trans (le_max_right N1 N2) hm)
    have e2 : dist (U n p) (U n x) ≤ f p := by
      rw [dist_comm]; exact hN2 n (le_trans (le_max_right N1 N2) hn)
    have e3 : dist (U m p) (U n p) < ε / 3 :=
      hN1 m (le_trans (le_max_left N1 N2) hm) n (le_trans (le_max_left N1 N2) hn)
    calc dist (U m x) (U n x)
        ≤ dist (U m x) (U m p) + dist (U m p) (U n p) + dist (U n p) (U n x) :=
          dist_triangle4 _ _ _ _
      _ < ε := by linarith
  -- The pointwise limit and its defining tendsto.
  set u' : EuclideanSpace ℝ (Fin d) → ℝ := fun x => Filter.limUnder Filter.atTop (fun n => U n x)
    with hu'_def
  have hu'lim : ∀ x ∈ B, Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 (u' x)) :=
    fun x hxB => tendsto_nhds_limUnder (hconv x hxB)
  refine ⟨u', ?_, ?_⟩
  · intro x hxB y hyB
    exact le_of_tendsto ((hu'lim x hxB).edist (hu'lim y hyB)) (hHol x hxB y hyB)
  · filter_upwards [hae, ae_restrict_mem hB.measurableSet] with x hxtend hxB
    exact tendsto_nhds_unique (hu'lim x hxB) hxtend

/-- **Uniform-constant coordinate-partial Morrey estimate.** Identical to
`morrey_ball_contDiff`, but with a single constant valid for every centre and radius, obtained
by keeping the ball inside the quantifier of `exists_holder_smooth`. This uniformity is what
lets the exhaustion of a ball by interior sub-balls have a fixed Hölder constant. -/
private theorem exists_holder_smooth_partialD (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ C : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) v →
      ∀ (c : EuclideanSpace ℝ (Fin d)) {r : ℝ}, 0 < r →
        (∀ k, MemLp (fun y => partialD k v y) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball c r))) →
          HolderOnWith
            (C * ∑ k, (eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p)
                        (volume.restrict (Metric.ball c r))).toNNReal)
            (morreyExponent d p) v (Metric.ball c r) := by
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd.ne'
  have hpge1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_le_of_lt h1d hp))
  obtain ⟨C, hC⟩ := exists_holder_smooth hd hp
  refine ⟨C, fun v hv c r hr hmem => ?_⟩
  set μ := volume.restrict (Metric.ball c r) with hμ_def
  have hfin : ∀ k, eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ ≠ ⊤ :=
    fun k => (hmem k).eLpNorm_ne_top
  have hstep : eLpNorm (fun y => ‖fderiv ℝ v y‖) (ENNReal.ofReal p) μ
      ≤ ∑ k, eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ := by
    have h1 : eLpNorm (fun y => ‖fderiv ℝ v y‖) (ENNReal.ofReal p) μ
        ≤ eLpNorm (fun y => ∑ k, ‖partialD k v y‖) (ENNReal.ofReal p) μ := by
      refine eLpNorm_mono
        ((hv.continuous_fderiv (by simp)).norm.aestronglyMeasurable.restrict) fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
      exact norm_fderiv_le_sum_partialD v y
    have h2 : eLpNorm (fun y => ∑ k, ‖partialD k v y‖) (ENNReal.ofReal p) μ
        ≤ ∑ k, eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ := by
      rw [show (fun y => ∑ k, ‖partialD k v y‖)
          = ∑ k, (fun y => ‖partialD k v y‖) from by funext y; rw [Finset.sum_apply]]
      refine (eLpNorm_sum_le hpge1).trans_eq ?_
      exact Finset.sum_congr rfl fun k _ =>
        eLpNorm_norm _ (hmem k).aestronglyMeasurable
    exact h1.trans h2
  have hsum_fin : (∑ k, eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ => hfin k
  have htoNN : (eLpNorm (fun y => ‖fderiv ℝ v y‖) (ENNReal.ofReal p) μ).toNNReal
      ≤ ∑ k, (eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ).toNNReal := by
    calc (eLpNorm (fun y => ‖fderiv ℝ v y‖) (ENNReal.ofReal p) μ).toNNReal
        ≤ (∑ k, eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ).toNNReal :=
          ENNReal.toNNReal_mono hsum_fin hstep
      _ = ∑ k, (eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ).toNNReal :=
          ENNReal.toNNReal_sum fun k _ => hfin k
  have hconst : C * (eLpNorm (fun y => ‖fderiv ℝ v y‖) (ENNReal.ofReal p) μ).toNNReal
      ≤ C * ∑ k, (eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p) μ).toNNReal :=
    mul_le_mul_right htoNN C
  intro x hx y hy
  exact (hC v hv c hr x hx y hy).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.mpr hconst) _)

/-- **Morrey embedding on a ball (weak-gradient form).** For `p > d`, a function `u` that is
integrable on `Metric.ball c r` with an `Lᵖ` weak gradient `g` there has a continuous
representative `u'` which is Hölder-`(1 - d/p)` on the ball, with constant linear in
`∑ₖ ‖gₖ‖_{Lᵖ(ball c r)}`. The representative is obtained by mollification: each mollification is
smooth and, by the smooth Morrey estimate applied on interior sub-balls, uniformly Hölder with the
target constant; the mollified gradients are bounded in `Lᵖ` by Young's inequality, and the
mollifications converge to `u` almost everywhere. The uniform-limit engine then produces `u'`. -/
theorem morrey_ball (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p)
    (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u (Metric.ball c r) volume →
      (∀ k, MemLp (g k) (ENNReal.ofReal p) (volume.restrict (Metric.ball c r))) →
      HasWeakGradOn (Metric.ball c r) u g →
      ∃ u' : EuclideanSpace ℝ (Fin d) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)] u ∧
        HolderOnWith
          (C * ∑ k, (eLpNorm (g k) (ENNReal.ofReal p)
                      (volume.restrict (Metric.ball c r))).toNNReal)
          (morreyExponent d p) u' (Metric.ball c r) := by
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hp
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd.ne'
  have hp1 : (1 : ℝ) ≤ p := le_of_lt (lt_of_le_of_lt h1d hp)
  have hpge1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]; exact ENNReal.ofReal_le_ofReal hp1
  have hγpos : 0 < morreyExponent d p :=
    Real.toNNReal_pos.mpr (sub_pos.mpr ((div_lt_one hp0).mpr hp))
  obtain ⟨C₀, hC0⟩ := exists_holder_smooth_partialD hd hp
  refine ⟨C₀, fun u g hu hmemg hweak => ?_⟩
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL_def
  set uB := (Metric.ball c r).indicator u with huB_def
  have huB_int : Integrable uB volume := hu.integrable_indicator measurableSet_ball
  have huB_li : LocallyIntegrable uB volume := huB_int.locallyIntegrable
  have hgBk : ∀ k, MemLp ((Metric.ball c r).indicator (g k)) (ENNReal.ofReal p) volume :=
    fun k => (memLp_indicator_iff_restrict measurableSet_ball).mpr (hmemg k)
  -- The shrinking mollifier family.
  have hn2 : ∀ n : ℕ, (0 : ℝ) < (n + 2 : ℝ) := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := r / (n + 2 : ℝ) / 2
      rOut := r / (n + 2 : ℝ)
      rIn_pos := div_pos (div_pos hr (hn2 n)) two_pos
      rIn_lt_rOut := half_lt_self (div_pos hr (hn2 n)) }
  set U : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => uB ⋆[L, volume] (φ n).normed volume with hU_def
  have hUval : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      U n x = (uB ⋆[L, volume] (φ n).normed volume) x := fun _ _ => rfl
  set M : ℝ≥0 := C₀ * ∑ k, (eLpNorm (g k) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball c r))).toNNReal with hM_def
  have hLflip : L.flip = L := by
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [hL_def, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
    exact mul_comm b a
  have hrOut : ∀ n, (φ n).rOut = r / (n + 2 : ℝ) := fun _ => rfl
  have hrIn : ∀ n, (φ n).rIn = r / (n + 2 : ℝ) / 2 := fun _ => rfl
  have hφrOut : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop)
  have hφratio : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 2 * (φ n).rIn :=
    Filter.Eventually.of_forall fun n => le_of_eq (by rw [hrOut, hrIn]; ring)
  -- Uniform Hölder bound of each mollification on interior sub-balls.
  have key : ∀ (r' : ℝ), 0 < r' → ∀ n : ℕ, r' + (φ n).rOut ≤ r →
      HolderOnWith M (morreyExponent d p) (U n) (Metric.ball c r') := by
    intro r' hr'pos n hcond
    have hρ0 : 0 ≤ (φ n).normed volume := fun x => (φ n).nonneg_normed x
    have hρcont : Continuous ((φ n).normed volume) :=
      ((φ n).contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) ((φ n).normed volume)).continuous
    have hρm : AEStronglyMeasurable ((φ n).normed volume) volume := hρcont.aestronglyMeasurable
    have hρ1 : ∫ y, (φ n).normed volume y ∂volume = 1 := (φ n).integral_normed
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (U n) :=
      (φ n).hasCompactSupport_normed.contDiff_convolution_right (L := L) huB_li
        (φ n).contDiff_normed
    have hbridge : ∀ z ∈ Metric.ball c r', ∀ k,
        partialD k (U n) z
          = ((Metric.ball c r).indicator (g k) ⋆[L, volume] (φ n).normed volume) z := by
      intro z hz k
      have hzc : dist z c < r' := by rwa [Metric.mem_ball] at hz
      have hzsub : Metric.closedBall z (φ n).rOut ⊆ Metric.ball c r := by
        intro w hw
        rw [Metric.mem_closedBall] at hw
        rw [Metric.mem_ball]
        calc dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
          _ ≤ (φ n).rOut + dist z c := by gcongr
          _ < (φ n).rOut + r' := by gcongr
          _ ≤ r := by linarith
      exact partialD_convolution_eq_of_hasWeakGradOn measurableSet_ball hu hweak (φ n) k hzsub
    have hcongr : ∀ k, (fun y => partialD k (U n) y) =ᵐ[volume.restrict (Metric.ball c r')]
        (fun y => ((Metric.ball c r).indicator (g k) ⋆[L, volume] (φ n).normed volume) y) :=
      fun k => (ae_restrict_iff' measurableSet_ball).mpr
        (Filter.Eventually.of_forall fun z hz => hbridge z hz k)
    have hpartMemLp : ∀ k, MemLp (fun y => partialD k (U n) y) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball c r')) := by
      intro k
      have hgBk_li : LocallyIntegrable ((Metric.ball c r).indicator (g k)) volume :=
        (hgBk k).locallyIntegrable hpge1
      have hsmoothConv : ContDiff ℝ (⊤ : ℕ∞)
          ((Metric.ball c r).indicator (g k) ⋆[L, volume] (φ n).normed volume) :=
        (φ n).hasCompactSupport_normed.contDiff_convolution_right (L := L) hgBk_li
          (φ n).contDiff_normed
      have hconvMemLp : MemLp ((Metric.ball c r).indicator (g k)
          ⋆[L, volume] (φ n).normed volume) (ENNReal.ofReal p) volume :=
        lt_of_le_of_lt (eLpNorm_convolution_le hp1 hρ0 hρm hρ1 (hgBk k))
          (hgBk k).eLpNorm_lt_top
      exact (memLp_congr_ae (hcongr k)).mpr (hconvMemLp.restrict (Metric.ball c r'))
    have hsum : (∑ k, (eLpNorm (fun y => partialD k (U n) y) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball c r'))).toNNReal)
        ≤ ∑ k, (eLpNorm (g k) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball c r))).toNNReal := by
      refine Finset.sum_le_sum fun k _ => ENNReal.toNNReal_mono (hmemg k).eLpNorm_ne_top ?_
      rw [eLpNorm_congr_ae (hcongr k)]
      calc eLpNorm (fun y => ((Metric.ball c r).indicator (g k)
              ⋆[L, volume] (φ n).normed volume) y) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball c r'))
          ≤ eLpNorm ((Metric.ball c r).indicator (g k)) (ENNReal.ofReal p) volume :=
            eLpNorm_convolution_restrict_le hp1 hρ0 hρm hρ1 (hgBk k) (Metric.ball c r')
        _ = eLpNorm (g k) (ENNReal.ofReal p) (volume.restrict (Metric.ball c r)) :=
            eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball
    exact (hC0 (U n) hsmooth c hr'pos hpartMemLp).mono_const (mul_le_mul' (le_refl C₀) hsum)
  -- Almost-everywhere convergence of the mollifications to `u` on the ball.
  have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball c r)),
      Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 (u x)) := by
    have hae0 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) (g := uB) hφrOut hφratio huB_li
    filter_upwards [ae_restrict_of_ae hae0, ae_restrict_mem measurableSet_ball] with x hx hxmem
    have huBx : uB x = u x := Set.indicator_of_mem hxmem u
    rw [← huBx]
    refine hx.congr fun n => ?_
    rw [hUval n x]
    exact congrFun (by rw [← hLflip]; exact (convolution_flip (L := L)).symm) x
  -- Feed the mollified sequence into the uniform-limit engine.
  have hHol : ∀ x ∈ Metric.ball c r, ∀ y ∈ Metric.ball c r, ∀ᶠ n in Filter.atTop,
      edist (U n x) (U n y) ≤ (M : ℝ≥0∞) * edist x y ^ (morreyExponent d p : ℝ) := by
    intro x hx y hy
    have hxc : dist x c < r := by rwa [Metric.mem_ball] at hx
    have hyc : dist y c < r := by rwa [Metric.mem_ball] at hy
    set a : ℝ := max (dist x c) (dist y c) with ha_def
    have ha_nonneg : 0 ≤ a := le_trans dist_nonneg (le_max_left _ _)
    have ha_lt : a < r := max_lt hxc hyc
    set r' : ℝ := (a + r) / 2 with hr'_def
    have h2r' : 2 * r' = a + r := by rw [hr'_def]; ring
    have hr'pos : 0 < r' := by linarith
    have har' : a < r' := by linarith
    have hxr' : x ∈ Metric.ball c r' :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (le_max_left _ _) har')
    have hyr' : y ∈ Metric.ball c r' :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (le_max_right _ _) har')
    have hev : ∀ᶠ n in Filter.atTop, r' + (φ n).rOut ≤ r := by
      have hpos : (0 : ℝ) < r - r' := by linarith
      filter_upwards [hφrOut.eventually (Iio_mem_nhds hpos)] with n hn
      have hn' : (φ n).rOut < r - r' := hn
      linarith
    filter_upwards [hev] with n hn
    exact (key r' hr'pos n hn).edist_le hxr' hyr'
  obtain ⟨u', hu'H, hu'ae⟩ :=
    exists_holderOnWith_of_ae_tendsto Metric.isOpen_ball hγpos hHol hae
  exact ⟨u', hu'ae, hu'H⟩

end EllipticPdes.Embedding

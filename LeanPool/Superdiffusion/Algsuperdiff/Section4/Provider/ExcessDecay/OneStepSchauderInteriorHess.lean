/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderInteriorGrad

/-!
# OneStepSchauderInteriorHess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior Hessian estimate and the gradient-Lipschitz estimate

The analytic apex of the interior half of the Schauder gradient-Hölder estimate.  For `u`
harmonic on `ball x R` and `0 < r < R`,

```text
  ‖D²u(p)‖ ≤ C(d) · r⁻¹ · r⁻¹ · √(msd_{B(x,r)}(u, c))    for every p ∈ B(x, r/2),
```

for **every** constant `c` (the deviation is measured against an arbitrary
constant, which is what later lets the estimate be taken to the infimum over
affine competitors).  The convex mean-value inequality on `B(x, r/2)` then gives
the **gradient-Lipschitz** form

```text
  ‖∇u(y) − ∇u(z)‖ ≤ C(d) · r⁻¹ · r⁻¹ · √(msd_{B(x,r)}(u, c)) · ‖y − z‖ .
```

The route: differentiate the reproducing convolution twice, bound the *kernel*
Hessian by its sup `(ε^{d+2})⁻¹ · B`, integrate `|u−c|`, upgrade `∫|·|` to
`√(vol · ∫(·)²)` by Cauchy–Schwarz, and convert the Haar ball volume by
`Measure.addHaar_ball`.  The inner-ball version re-centres at `p ∈ B(x, r/2)`
with radii `r/4 < r/2` and pays `2^d` for enlarging the averaging ball.
-/

-- ==== interior second-derivative estimate, `L²` form ====
open scoped Real Convolution Topology
open MeasureTheory Metric Set InnerProductSpace
open HCPolySupport (Vec euclideanBall volumeAverage)
open HCPolySupport.Book.Ch01 (meanSquareDeviationOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

/-! ## Instance caches for the Euclidean and Hessian carriers

The base carrier `EuclideanSpace ℝ (Fin d)`, the gradient carrier
`EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ` and the Hessian carrier
`EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ` are searched
hundreds of times while elaborating this file (measured: 82 `MeasureSpace`,
75 `Module`, 63 `NormedSpace` closed top-level searches on the base carrier
alone).  Caching the recurring classes once at module level — outside the
section, so that every declaration sees them — turns each search into a single
step.  Every cache below is literally the instance Lean would otherwise
rediscover, so no definitional content changes.
-/

noncomputable instance instMeasureSpaceEuclid (d : ℕ) :
    MeasureTheory.MeasureSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

noncomputable instance instModuleEuclid (d : ℕ) :
    Module ℝ (EuclideanSpace ℝ (Fin d)) := inferInstance

noncomputable instance instNormedSpaceEuclid (d : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin d)) := inferInstance

noncomputable instance instModuleGradCarrier (d : ℕ) :
    Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance

noncomputable instance instNormedSpaceGradCarrier (d : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance

noncomputable instance instNormHessCarrier (d : ℕ) :
    Norm (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
  inferInstance

noncomputable instance instSeminormedAddGroupHessCarrier (d : ℕ) :
    SeminormedAddGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
  inferInstance

instance instFiniteDimensionalEuclid (d : ℕ) :
    FiniteDimensional ℝ (EuclideanSpace ℝ (Fin d)) := inferInstance

instance instProperSpaceEuclid (d : ℕ) :
    ProperSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

instance instHasContDiffBumpEuclid (d : ℕ) :
    HasContDiffBump (EuclideanSpace ℝ (Fin d)) := inferInstance

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### A sup bound for the unit-kernel Hessian -/

/-- **Sup bound for the second derivative of a compactly supported `C³` function.**  Stated for an
abstract `f` so that the compact support of the *real-valued* norm function `z ↦ ‖D²f z‖` is routed
through the `tsupport`-subset chain: the tower-valued `HasCompactSupport.fderiv` blows up `whnf` on
the iterated continuous-linear-map type (the same pitfall documented at
`KernelHessL1.integrable_norm_fderivSq_of`). -/
theorem exists_forall_norm_fderiv_fderiv_le_of {f : 𝔼 → ℝ} (hf : ContDiff ℝ 3 f)
    (hcs : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : 𝔼, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B := by
  have hcont : Continuous (fun z : 𝔼 => ‖fderiv ℝ (fderiv ℝ f) z‖) :=
    ((hf.fderiv_right (m := 2) (by norm_num)).continuous_fderiv (by norm_num)).norm
  have hsubR : Function.support (fun z : 𝔼 => ‖fderiv ℝ (fderiv ℝ f) z‖) ⊆ tsupport f := by
    intro z hz
    rw [Function.mem_support] at hz
    have hz' : fderiv ℝ (fderiv ℝ f) z ≠ 0 :=
      fun h => hz (by rw [h]; exact ContinuousLinearMap.opNorm_zero)
    have h1 : Function.support (fderiv ℝ (fderiv ℝ f)) ⊆ tsupport (fderiv ℝ f) :=
      support_fderiv_subset (𝕜 := ℝ)
    have h2 : tsupport (fderiv ℝ f) ⊆ tsupport f := tsupport_fderiv_subset (𝕜 := ℝ)
    exact h2 (h1 hz')
  have hcsR : HasCompactSupport (fun z : 𝔼 => ‖fderiv ℝ (fderiv ℝ f) z‖) :=
    hcs.of_isClosed_subset isClosed_closure (closure_minimal hsubR isClosed_closure)
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcsR
  have hB' : ∀ z : 𝔼, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B := by
    intro z
    have hz := hB z
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ f) z))] at hz
  refine ⟨B, ?_, hB'⟩
  exact le_trans (by positivity) (hB' 0)

/-- The Hessian of the unit radial kernel is bounded: it is continuous with compact support. -/
theorem exists_forall_norm_fderiv_fderiv_radialKernel_le (d : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : EuclideanSpace ℝ (Fin d),
      ‖fderiv ℝ (fderiv ℝ (radialKernel d)) z‖ ≤ B :=
  exists_forall_norm_fderiv_fderiv_le_of (radialKernel_contDiff (d := d) (n := 3))
    (radialKernel_hasCompactSupport d)

/-! ### The core `L¹` Hessian bound -/

/-- **Core `L¹` interior Hessian bound.**  For a globally-`C²` function `w` harmonic on `ball x₀ ρ`
with `2ε ≤ ρ`, the second derivative at the centre is bounded by `(ε^{d+2})⁻¹·B` times the `L¹` norm
of `w` on `ball x₀ (2ε)`, where `B` bounds the unit-kernel Hessian.

Proof: differentiate the native reproducing convolution **twice** (as in
`norm_fderiv_fderiv_le_of_harmonic_bound`), then bound the kernel factor pointwise by its sup
`‖D²K_ε(t)‖ ≤ (ε^d)⁻¹·ε⁻¹·ε⁻¹·B = (ε^{d+2})⁻¹·B` and integrate `|w|` (as in
`norm_fderiv_le_L1_of_harmonic`) — the `L¹`-on-the-data / sup-on-the-kernel split, which is what
makes the subsequent Cauchy–Schwarz upgrade to an `L²` deviation possible. -/
theorem norm_fderiv_fderiv_le_L1_of_harmonic [NeZero d] {w : 𝔼 → ℝ} (hw : ContDiff ℝ 2 w)
    {x₀ : 𝔼} {ε ρ B : ℝ} (hε : 0 < ε) (h2ε : 2 * ε ≤ ρ)
    (hB : ∀ z : 𝔼, ‖fderiv ℝ (fderiv ℝ (radialKernel d)) z‖ ≤ B)
    (hharm : HarmonicOnNhd w (ball x₀ ρ)) :
    ‖fderiv ℝ (fderiv ℝ w) x₀‖ ≤ (ε ^ (d + 2))⁻¹ * B * ∫ y in ball x₀ (2 * ε), |w y| ∂volume := by
  let : NormSMulClass ℝ (𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ) :=
    NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ)
  set K : 𝔼 → ℝ := radialKernelScaled d ε with hKdef
  set g : 𝔼 → ℝ := Set.indicator (ball x₀ (2 * ε)) w with hgdef
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hIO : IntegrableOn w (ball x₀ (2 * ε)) volume :=
    (hw.continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ (2 * ε))).mono_set ball_subset_closedBall
  have hg_int : Integrable g volume := hIO.integrable_indicator measurableSet_ball
  have hg_loc : LocallyIntegrable g volume := hg_int.locallyIntegrable
  -- neighbourhood reproducing identity `w =ᶠ (K ⋆ g)`.
  have heq : w =ᶠ[𝓝 x₀] (K ⋆[L, volume] g) := by
    filter_upwards [Metric.ball_mem_nhds x₀ hε] with x' hx'
    have hdx : dist x' x₀ < ε := Metric.mem_ball.mp hx'
    have hball : ball x' ε ⊆ ball x₀ (2 * ε) :=
      Metric.ball_subset_ball' (by linarith [le_of_lt hdx])
    have hharm' : HarmonicOnNhd w (ball x' ε) :=
      hharm.mono (Metric.ball_subset_ball' (by linarith [le_of_lt hdx]))
    exact (convolution_radialKernelScaled_indicator_apply hw hε (le_refl ε) hball hharm').symm
  -- first derivative of the convolution, as a function.
  have hfd_conv : fderiv ℝ (K ⋆[L, volume] g) = (fderiv ℝ K ⋆[L.precompL 𝔼, volume] g) := by
    funext x
    exact ((radialKernelScaled_hasCompactSupport d hε).hasFDerivAt_convolution_left L
      (radialKernelScaled_contDiff (d := d) (ε := ε) (n := 1)) hg_loc x).fderiv
  -- second derivative of the convolution at `x₀`.
  have hfdK_cs : HasCompactSupport (fderiv ℝ K) :=
    (radialKernelScaled_hasCompactSupport d hε).fderiv ℝ
  have hfdK_cd1 : ContDiff ℝ 1 (fderiv ℝ K) :=
    (radialKernelScaled_contDiff (d := d) (ε := ε) (n := 2)).fderiv_right (m := 1) (by norm_num)
  have hFD2 := hfdK_cs.hasFDerivAt_convolution_left (L.precompL 𝔼) hfdK_cd1 hg_loc x₀
  have hww : fderiv ℝ (fderiv ℝ w) x₀ = fderiv ℝ (fderiv ℝ (K ⋆[L, volume] g)) x₀ :=
    (heq.fderiv).fderiv_eq
  rw [hww, hfd_conv, hFD2.fderiv, convolution_def]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  -- pointwise evaluation of the double `precompL`.
  have hintegrand : ∀ t, ‖((L.precompL 𝔼).precompL 𝔼) (fderiv ℝ (fderiv ℝ K) t) (g (x₀ - t))‖
      = |g (x₀ - t)| * ‖fderiv ℝ (fderiv ℝ K) t‖ := by
    intro t
    have hval : ((L.precompL 𝔼).precompL 𝔼) (fderiv ℝ (fderiv ℝ K) t) (g (x₀ - t))
        = (g (x₀ - t)) • fderiv ℝ (fderiv ℝ K) t := by
      ext x v
      simp only [ContinuousLinearMap.precompL_apply, smul_apply, hLdef,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      ring
    rw [hval, norm_smul, Real.norm_eq_abs]
  -- pointwise sup bound on the kernel Hessian.
  have hKbound : ∀ t, ‖fderiv ℝ (fderiv ℝ K) t‖ ≤ (ε ^ (d + 2))⁻¹ * B := by
    intro t
    rw [hKdef, norm_fderiv_fderiv_radialKernelScaled d hε]
    have hpowid : (ε : ℝ) ^ (d + 2) = ε ^ d * ε * ε := by ring
    have hpow : (ε ^ d)⁻¹ * ε⁻¹ * ε⁻¹ = (ε ^ (d + 2))⁻¹ := by
      rw [hpowid, mul_inv, mul_inv]
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (hB _) (inv_nonneg.mpr (pow_nonneg hε.le _))
  have hmono : ∫ t, ‖((L.precompL 𝔼).precompL 𝔼) (fderiv ℝ (fderiv ℝ K) t) (g (x₀ - t))‖ ∂volume
      ≤ ∫ t, |g (x₀ - t)| * ((ε ^ (d + 2))⁻¹ * B) ∂volume := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      ((hg_int.comp_sub_left x₀).abs.mul_const _) ?_
    filter_upwards with t
    rw [hintegrand t]
    exact mul_le_mul_of_nonneg_left (hKbound t) (abs_nonneg _)
  refine hmono.trans (le_of_eq ?_)
  have hreflect : ∫ t, |g (x₀ - t)| ∂volume = ∫ y in ball x₀ (2 * ε), |w y| ∂volume := by
    have h1 : ∫ t, |g (x₀ - t)| ∂volume = ∫ y, |g y| ∂volume :=
      integral_sub_left_eq_self (fun y => |g y|) volume x₀
    rw [h1, hgdef]
    have habs : (fun y => |(ball x₀ (2 * ε)).indicator w y|)
        = (ball x₀ (2 * ε)).indicator (fun y => |w y|) := by
      funext y
      by_cases hy : y ∈ ball x₀ (2 * ε) <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
    rw [habs, integral_indicator measurableSet_ball]
  calc ∫ t, |g (x₀ - t)| * ((ε ^ (d + 2))⁻¹ * B) ∂volume
      = (∫ t, |g (x₀ - t)| ∂volume) * ((ε ^ (d + 2))⁻¹ * B) := by rw [integral_mul_const]
    _ = (ε ^ (d + 2))⁻¹ * B * ∫ y in ball x₀ (2 * ε), |w y| ∂volume := by rw [hreflect]; ring

/-! ### Ball-volume and coefficient algebra -/

/-- Haar ball-volume scaling in the shape used below: `vol(B(x,r)) = rᵈ · vol(B(0,1))`. -/
private theorem volume_ball_toReal_eq [NeZero d] (x : 𝔼) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.ball x r)).toReal
      = r ^ d * (volume (Metric.ball (0 : 𝔼) 1)).toReal := by
  rw [Measure.addHaar_ball (volume : Measure 𝔼) x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _), finrank_euclideanSpace_fin]

/-- Pure-real coefficient identity behind the centre estimate:
`((r/2)^{d+2})⁻¹ · B · (rᵈ·ω·S) = B·ω·2^{d+2}·r⁻¹·r⁻¹·S`. -/
private theorem hess_centre_coeff_algebra {r B ω S : ℝ} (d : ℕ) (hr : 0 < r) :
    ((r / 2) ^ (d + 2))⁻¹ * B * (r ^ d * ω * S) = B * ω * 2 ^ (d + 2) * r⁻¹ * r⁻¹ * S := by
  have hrne : r ≠ 0 := hr.ne'
  have hrd : (r : ℝ) ^ d ≠ 0 := pow_ne_zero d hrne
  have h2 : ((2 : ℝ)) ^ (d + 2) ≠ 0 := by positivity
  have hnum : (r : ℝ) ^ (d + 2) = r ^ d * r * r := by ring
  have h1 : ((r / 2) ^ (d + 2) : ℝ) = r ^ d * r * r / 2 ^ (d + 2) := by rw [div_pow, hnum]
  rw [h1]
  field_simp

/-- Pure-real coefficient identity behind the inner-ball estimate:
`C·(r/4)⁻¹·(r/4)⁻¹·(2ᵈ·S) = 16·C·2ᵈ·r⁻¹·r⁻¹·S`. -/
private theorem hess_ball_coeff_algebra {C r S : ℝ} (d : ℕ) (hr : 0 < r) :
    C * (r / 4)⁻¹ * (r / 4)⁻¹ * (2 ^ d * S) = 16 * C * 2 ^ d * r⁻¹ * r⁻¹ * S := by
  have hrne : r ≠ 0 := hr.ne'
  field_simp
  ring

/-- Pure-real volume-ratio identity: enlarging the averaging ball from radius `r/4` to `r` costs a
factor `4ᵈ` in the mean-square deviation. -/
private theorem msd_ratio_algebra {r ω I : ℝ} (d : ℕ) (hr : 0 < r) (hω : 0 < ω) :
    ((r / 4) ^ d * ω)⁻¹ * I = 4 ^ d * ((r ^ d * ω)⁻¹ * I) := by
  have hrne : r ≠ 0 := hr.ne'
  have hrd : (r : ℝ) ^ d ≠ 0 := pow_ne_zero d hrne
  have hωne : ω ≠ 0 := hω.ne'
  have h4 : ((4 : ℝ)) ^ d ≠ 0 := by positivity
  rw [div_pow]
  field_simp

/-! ### The centre `L²` Hessian estimate -/

/-- **Interior Hessian estimate, `L²`-deviation shape (native), at the centre.**
For `u` harmonic (mathlib sense) on `B(x, R)` and any inner radius `0 < r < R`,
the Hessian at the centre is bounded by `C·r⁻²` times the square root of the
mean-square deviation of `u` on `B(x, r)` (measured on the corresponding
CoarseGraining Euclidean ball — the §4.3 excess), for any constant `c`.

This is the exact second-order analogue of `interiorGradientEstimateL2`; the explicit constant is
`B·ω·2^{d+2}`, with `B` the sup of the unit-kernel Hessian and `ω = vol(B(0,1))`. -/
theorem interiorSecondDerivEstimateL2 (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (x : EuclideanSpace ℝ (Fin d)) {R r : ℝ} (c : ℝ), 0 < r → r < R →
      HarmonicOnNhd u (Metric.ball x R) →
      ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * r⁻¹ * r⁻¹ *
        Real.sqrt (meanSquareDeviationOn (euclideanBall (toEuc.symm x) r) (u ∘ toEuc) c) := by
  obtain ⟨B, hB0, hB⟩ := exists_forall_norm_fderiv_fderiv_radialKernel_le d
  set ω : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hωdef
  have hω0 : 0 < ω := by
    rw [hωdef]
    have hpos : 0 < volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      measure_ball_pos volume 0 one_pos
    have hne : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
    exact ENNReal.toReal_pos hpos.ne' hne
  refine ⟨B * ω * 2 ^ (d + 2), mul_nonneg (mul_nonneg hB0 hω0.le) (by positivity), ?_⟩
  intro u x R r c hr hR hharm
  set S : ℝ := meanSquareDeviationOn (euclideanBall (toEuc.symm x) r) (u ∘ toEuc) c with hSdef
  set ε : ℝ := r / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have h2εr : 2 * ε = r := by rw [hεdef]; ring
  -- volume of `ball x r` is `r^d · ω`.
  have hVol : (volume (ball x r)).toReal = r ^ d * ω := by
    rw [hωdef]; exact volume_ball_toReal_eq x hr.le
  have hVol0 : 0 < (volume (ball x r)).toReal := by rw [hVol]; positivity
  have hVolball_ne : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  -- cutoff: `v = χ·u`, `χ = 1` on `closedBall x r`,
  -- `tsupport χ ⊆ closedBall x ((r+R)/2) ⊆ ball x R`.
  have hrlt : r < (r + R) / 2 := by linarith
  set χ : ContDiffBump x := ⟨r, (r + R) / 2, hr, hrlt⟩ with hχ
  have hrout : (χ.rOut : ℝ) = (r + R) / 2 := rfl
  have htsχ : tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ ball x R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by rw [hrout]; linarith)
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun y => χ y * u y with hv
  have hv_cd : ContDiff ℝ 2 v := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    · exact (χ.contDiff.contDiffAt).mul ((hharm y (htsχ hy)).1)
    · have hev : v =ᶠ[𝓝 y] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
        simp [hv, hz]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  have hvu_on : ∀ y ∈ closedBall x r, v y = u y := by
    intro y hy
    have : (χ : EuclideanSpace ℝ (Fin d) → ℝ) y = 1 := χ.one_of_mem_closedBall hy
    simp [hv, this]
  have hv_harm : HarmonicOnNhd v (ball x r) := by
    intro p hp
    have hχ1 : (χ : EuclideanSpace ℝ (Fin d) → ℝ) =ᶠ[𝓝 p] 1 := χ.eventuallyEq_one_of_mem_ball hp
    have hvu : v =ᶠ[𝓝 p] u := by filter_upwards [hχ1] with z hz; simp [hv, hz]
    have hpR : p ∈ ball x R := (Metric.ball_subset_ball hR.le) hp
    exact (harmonicAt_congr_nhds hvu).2 (hharm p hpR)
  have hvu_nhds : v =ᶠ[𝓝 x] u := by
    have hχ1 : (χ : EuclideanSpace ℝ (Fin d) → ℝ) =ᶠ[𝓝 x] 1 :=
      χ.eventuallyEq_one_of_mem_ball (mem_ball_self χ.rIn_pos)
    filter_upwards [hχ1] with z hz; simp [hv, hz]
  -- `w = v − c`: globally `C²`, harmonic on `ball x r`, `D²w x = D²u x`, `= u − c` on the ball.
  set w : EuclideanSpace ℝ (Fin d) → ℝ := fun y => v y - c with hw
  have hw_cd : ContDiff ℝ 2 w := hv_cd.sub contDiff_const
  have hw_harm : HarmonicOnNhd w (ball x r) := harmonicOnNhd_sub_const hv_harm c
  have hfderiv_eq : fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ w) x := by
    have h1 : fderiv ℝ w = fderiv ℝ v := by funext z; rw [hw, fderiv_sub_const]
    have h2 : fderiv ℝ (fderiv ℝ w) x = fderiv ℝ (fderiv ℝ v) x := by rw [h1]
    have h3 : fderiv ℝ (fderiv ℝ v) x = fderiv ℝ (fderiv ℝ u) x := (hvu_nhds.fderiv).fderiv_eq
    rw [h2, h3]
  have hwuc : ∀ y ∈ ball x r, w y = u y - c := by
    intro y hy
    show v y - c = u y - c
    rw [hvu_on y (Metric.ball_subset_closedBall hy)]
  -- core `L¹` Hessian bound at `ε = r/2`, `ρ = r`.
  have hcore := norm_fderiv_fderiv_le_L1_of_harmonic (d := d) hw_cd (x₀ := x) (ε := ε) (ρ := r)
    (B := B) hε (by rw [h2εr]) hB hw_harm
  rw [h2εr] at hcore
  -- rewrite the `L²` integral in terms of `u − c` on `ball x r`.
  have hL2 : ∫ y in ball x r, (w y) ^ 2 ∂volume = ∫ y in ball x r, (u y - c) ^ 2 ∂volume :=
    setIntegral_congr_fun measurableSet_ball (fun y hy => by rw [hwuc y hy])
  -- Cauchy–Schwarz on `ball x r` for `f = w`, bounded via continuity on the compact closed ball.
  have hw_cont : Continuous w := hw_cd.continuous
  obtain ⟨Mw, hMw⟩ :=
    (isCompact_closedBall x r).exists_bound_of_continuousOn hw_cont.continuousOn
  have hCS : (∫ y in ball x r, |w y| ∂volume) ^ 2
      ≤ (volume (ball x r)).toReal * ∫ y in ball x r, (w y) ^ 2 ∂volume := by
    refine sq_setIntegral_abs_le (ball x r) measurableSet_ball hVolball_ne
      hw_cont.aestronglyMeasurable (Mf := Mw) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have := hMw y (Metric.ball_subset_closedBall hy)
    rwa [Real.norm_eq_abs] at this
  -- the mean-square deviation, unfolded.
  have hmsd : S = (volume (ball x r)).toReal⁻¹ * ∫ z in ball x r, (u z - c) ^ 2 ∂volume := by
    rw [hSdef]; exact meanSquareDeviationOn_euclideanBall_eq u x hr c
  have hVolne : (volume (ball x r)).toReal ≠ 0 := hVol0.ne'
  have hIX : ∫ z in ball x r, (u z - c) ^ 2 ∂volume = (volume (ball x r)).toReal * S := by
    rw [hmsd]; field_simp
  have hS0 : 0 ≤ S := by
    rw [hmsd]
    exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _)
  -- `∫|w| ≤ vol · √S` (Cauchy–Schwarz in square-root form).
  have hI0 : 0 ≤ ∫ y in ball x r, |w y| ∂volume :=
    setIntegral_nonneg measurableSet_ball fun _ _ => abs_nonneg _
  have hsqle : (∫ y in ball x r, |w y| ∂volume) ^ 2
      ≤ ((volume (ball x r)).toReal) ^ 2 * S := by
    refine hCS.trans (le_of_eq ?_)
    rw [hL2, hIX]; ring
  have hI : (∫ y in ball x r, |w y| ∂volume) ≤ (volume (ball x r)).toReal * Real.sqrt S := by
    calc ∫ y in ball x r, |w y| ∂volume
        = Real.sqrt ((∫ y in ball x r, |w y| ∂volume) ^ 2) := (Real.sqrt_sq hI0).symm
      _ ≤ Real.sqrt (((volume (ball x r)).toReal) ^ 2 * S) := Real.sqrt_le_sqrt hsqle
      _ = (volume (ball x r)).toReal * Real.sqrt S := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hVol0.le]
  -- assembly.
  have hcoefnn : (0 : ℝ) ≤ (ε ^ (d + 2))⁻¹ * B :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) hB0
  rw [hfderiv_eq]
  calc ‖fderiv ℝ (fderiv ℝ w) x‖
      ≤ (ε ^ (d + 2))⁻¹ * B * ∫ y in ball x r, |w y| ∂volume := hcore
    _ ≤ (ε ^ (d + 2))⁻¹ * B * ((volume (ball x r)).toReal * Real.sqrt S) :=
        mul_le_mul_of_nonneg_left hI hcoefnn
    _ = B * ω * 2 ^ (d + 2) * r⁻¹ * r⁻¹ * Real.sqrt S := by
        rw [hVol, hεdef]; exact hess_centre_coeff_algebra d hr

/-! ### The uniform inner-ball `L²` Hessian estimate -/

/-- **Interior Hessian estimate, `L²`-deviation shape (native), uniformly on the half-radius ball.**
For `u` harmonic on `B(x, R)` and `0 < r < R`, the Hessian is bounded by `C·r⁻²·√msd` at **every**
point of `B(x, r/2)`, with the mean-square deviation still measured on the *fixed outer ball*
`B(x, r)`.

Proof: apply the centre estimate `interiorSecondDerivEstimateL2` re-centred at `y` with radii
`r/4 < r/2` (legitimate since `B(y, r/2) ⊆ B(x, R)`), then enlarge the averaging ball from
`B(y, r/4)` to `B(x, r)`: the integral only grows (the integrand is nonnegative) while the
normalizing volume shrinks by `4^{-d}`, so `msd_{B(y,r/4)} ≤ 4^d · msd_{B(x,r)}` and the square root
costs a factor `2^d`.  The explicit constant is `16·C·2^d` with `C` the centre constant. -/
theorem interiorSecondDerivEstimateL2_ball (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (x : EuclideanSpace ℝ (Fin d)) {R r : ℝ} (c : ℝ), 0 < r → r < R →
      HarmonicOnNhd u (Metric.ball x R) →
      ∀ y ∈ Metric.ball x (r / 2),
        ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ C * r⁻¹ * r⁻¹ *
          Real.sqrt (meanSquareDeviationOn (euclideanBall (toEuc.symm x) r) (u ∘ toEuc) c) := by
  obtain ⟨C, hC0, hC⟩ := interiorSecondDerivEstimateL2 d
  refine ⟨16 * C * 2 ^ d, by positivity, ?_⟩
  intro u x R r c hr hR hharm y hy
  have hyx : dist y x < r / 2 := Metric.mem_ball.mp hy
  have hr4 : (0 : ℝ) < r / 4 := by linarith
  have hsub2 : Metric.ball y (r / 2) ⊆ Metric.ball x R :=
    Metric.ball_subset_ball' (by linarith)
  -- the centre estimate at `y`, radii `r/4 < r/2`.
  have hcore := hC u y (R := r / 2) (r := r / 4) c hr4 (by linarith) (hharm.mono hsub2)
  set SX : ℝ := meanSquareDeviationOn (euclideanBall (toEuc.symm x) r) (u ∘ toEuc) c with hSX
  set SY : ℝ := meanSquareDeviationOn (euclideanBall (toEuc.symm y) (r / 4)) (u ∘ toEuc) c with hSY
  -- ball volumes.
  set ω : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hωdef
  have hω0 : 0 < ω := by
    rw [hωdef]
    have hpos : 0 < volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      measure_ball_pos volume 0 one_pos
    have hne : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
    exact ENNReal.toReal_pos hpos.ne' hne
  have hVolX : (volume (ball x r)).toReal = r ^ d * ω := by
    rw [hωdef]; exact volume_ball_toReal_eq x hr.le
  have hVolY : (volume (ball y (r / 4))).toReal = (r / 4) ^ d * ω := by
    rw [hωdef]; exact volume_ball_toReal_eq y hr4.le
  -- integrability of `(u − c)²` on the outer ball (harmonic ⇒ continuous on `closedBall x r`).
  have hclos : Metric.closedBall x r ⊆ Metric.ball x R := Metric.closedBall_subset_ball hR
  have hcontOn : ContinuousOn (fun z : EuclideanSpace ℝ (Fin d) => (u z - c) ^ 2)
      (Metric.closedBall x r) := by
    intro z hz
    exact ((((hharm z (hclos hz)).1.continuousAt).sub continuousAt_const).pow 2).continuousWithinAt
  have hIntOn : IntegrableOn (fun z : EuclideanSpace ℝ (Fin d) => (u z - c) ^ 2)
      (Metric.ball x r) volume :=
    (hcontOn.integrableOn_compact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  -- `msd` comparison.
  have hsubY : Metric.ball y (r / 4) ⊆ Metric.ball x r := Metric.ball_subset_ball' (by linarith)
  have hIle : ∫ z in ball y (r / 4), (u z - c) ^ 2 ∂volume
      ≤ ∫ z in ball x r, (u z - c) ^ 2 ∂volume :=
    setIntegral_mono_set hIntOn (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      hsubY.eventuallyLE
  have hmsdX : SX = (volume (ball x r)).toReal⁻¹ * ∫ z in ball x r, (u z - c) ^ 2 ∂volume := by
    rw [hSX]; exact meanSquareDeviationOn_euclideanBall_eq u x hr c
  have hmsdY : SY = (volume (ball y (r / 4))).toReal⁻¹ *
      ∫ z in ball y (r / 4), (u z - c) ^ 2 ∂volume := by
    rw [hSY]; exact meanSquareDeviationOn_euclideanBall_eq u y hr4 c
  have hcy : (0 : ℝ) ≤ ((r / 4) ^ d * ω)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (pow_nonneg hr4.le d) hω0.le)
  have hmsdle : SY ≤ 4 ^ d * SX := by
    rw [hmsdX, hmsdY, hVolX, hVolY]
    calc ((r / 4) ^ d * ω)⁻¹ * ∫ z in ball y (r / 4), (u z - c) ^ 2 ∂volume
        ≤ ((r / 4) ^ d * ω)⁻¹ * ∫ z in ball x r, (u z - c) ^ 2 ∂volume :=
          mul_le_mul_of_nonneg_left hIle hcy
      _ = 4 ^ d * ((r ^ d * ω)⁻¹ * ∫ z in ball x r, (u z - c) ^ 2 ∂volume) :=
          msd_ratio_algebra d hr hω0
  have h4 : (((2 : ℝ)) ^ d) ^ 2 = (4 : ℝ) ^ d := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsqrtle : Real.sqrt SY ≤ 2 ^ d * Real.sqrt SX := by
    have h1 : Real.sqrt SY ≤ Real.sqrt ((4 : ℝ) ^ d * SX) := Real.sqrt_le_sqrt hmsdle
    have h2 : Real.sqrt ((4 : ℝ) ^ d * SX) = 2 ^ d * Real.sqrt SX := by
      rw [← h4, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rwa [h2] at h1
  have hcnn : (0 : ℝ) ≤ C * (r / 4)⁻¹ * (r / 4)⁻¹ :=
    mul_nonneg (mul_nonneg hC0 (inv_nonneg.mpr (by linarith))) (inv_nonneg.mpr (by linarith))
  calc ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (r / 4)⁻¹ * (r / 4)⁻¹ * Real.sqrt SY := hcore
    _ ≤ C * (r / 4)⁻¹ * (r / 4)⁻¹ * (2 ^ d * Real.sqrt SX) :=
        mul_le_mul_of_nonneg_left hsqrtle hcnn
    _ = 16 * C * 2 ^ d * r⁻¹ * r⁻¹ * Real.sqrt SX := hess_ball_coeff_algebra d hr

/-! ### The gradient-Lipschitz consequence -/

/-- **Interior gradient-Lipschitz estimate from the `L²` deviation (native).**  For `u` harmonic on
`B(x, R)` and `0 < r < R`, the gradient of `u` is Lipschitz on the half-radius ball `B(x, r/2)` with
constant `C·r⁻²·√( msd_{B(x,r)}(u, c) )`:

  `‖∇u(y) − ∇u(z)‖ ≤ C·r⁻¹·r⁻¹·√( msd_{B(x,r)}(u, c) ) · ‖y − z‖`  for `y, z ∈ B(x, r/2)`.

This is the convex mean-value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le` applied to the
`C¹` map `fderiv ℝ u` on the convex set `B(x, r/2)`, with the derivative bound supplied by
`interiorSecondDerivEstimateL2_ball`.  Differentiability of `fderiv ℝ u` on the ball comes from the
`C²` regularity contained in `HarmonicAt`. -/
theorem interiorGradLipschitz_le_l2dev (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (x : EuclideanSpace ℝ (Fin d)) {R r : ℝ} (c : ℝ), 0 < r → r < R →
      HarmonicOnNhd u (Metric.ball x R) →
      ∀ y ∈ Metric.ball x (r / 2), ∀ z ∈ Metric.ball x (r / 2),
        ‖fderiv ℝ u y - fderiv ℝ u z‖ ≤
          (C * r⁻¹ * r⁻¹ *
            Real.sqrt (meanSquareDeviationOn (euclideanBall (toEuc.symm x) r) (u ∘ toEuc) c))
          * ‖y - z‖ := by
  obtain ⟨C, hC0, hC⟩ := interiorSecondDerivEstimateL2_ball d
  refine ⟨C, hC0, ?_⟩
  intro u x R r c hr hR hharm y hy z hz
  have hdiff : ∀ p ∈ Metric.ball x (r / 2), DifferentiableAt ℝ (fderiv ℝ u) p := by
    intro p hp
    have hpR : p ∈ Metric.ball x R := by
      have hd : dist p x < r / 2 := Metric.mem_ball.mp hp
      exact Metric.mem_ball.mpr (by linarith)
    have hc1 : ContDiffAt ℝ 1 (fderiv ℝ u) p := by
      have := (hharm p hpR).1.fderiv_right (m := 1) (by norm_num)
      simpa using this
    exact hc1.differentiableAt (by norm_num)
  have hbound : ∀ p ∈ Metric.ball x (r / 2), ‖fderiv ℝ (fderiv ℝ u) p‖ ≤
      C * r⁻¹ * r⁻¹ *
        Real.sqrt (meanSquareDeviationOn (euclideanBall (toEuc.symm x) r) (u ∘ toEuc) c) :=
    fun p hp => hC u x c hr hR hharm p hp
  exact (convex_ball x (r / 2)).norm_image_sub_le_of_norm_fderiv_le hdiff hbound hz hy

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder


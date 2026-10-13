/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomBridgeDataEmbedding
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGDischargeTestClass

/-!
# HomCGFinalGagliardo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `C^{0,α}(□) ⊂ W^{s′,q}(□)` at `s′ < α`, with the exact cube scaling

## What this file supplies

The measurement named two "absent analytic inputs" for the order-loss route.
MINING CORRECTION: the first one is **not absent** — the
`Provider.Regularity.lintegral_enorm_sub_rpow_neg_le_of_subset_ball`
(`HolderGagliardoRadial.lean`) is already the β-Riesz ball integral at
**general** `β ∈ (0,d)` in the ambient sup metric,

```text
  ∫_{B(x,R)} |x-y|^{-β} dy ≤ C_rad(d,β) · R^{d} · R^{-β},
```

with `C_rad(d,β) = 3^{β} 2^{d} (1-3^{β-d})^{-1}`.  A search of
`CoarseGraining` and Mathlib by name finds only `CoarseGraining`'s `β = 1`
instance; the general statement was proved in this repository's own Theorem C
tree.  Nothing is re-derived here.

What IS new here is the transfer of that estimate to **`CoarseGraining`'s**
fractional carriers, whose kernel differs from the Theorem C tree's:

* `Gagliardo.gagliardoKernel s 2` uses the ambient `dist`, at `p = 2`, and the
  Hölder exponent is pinned to `1/2` in
  `normalizedGagliardoESeminormOn_le_of_holderHalf`;
* `cubeEuclideanWspKernel s′ q` uses `euclideanDist` and `HilbertVec.ofVec`, at
  a general finite exponent `q`.

`cubeEuclideanWspESeminorm_le_of_holder` is the general `(α, s′, q)` statement
at `CoarseGraining`'s carrier, and `cubeEuclideanWspFullENorm_le_of_holder`
assembles it with the `L^q` half into the **full** norm `CoarseGraining`'s
smooth dual pairs against.

## The exponent arithmetic (machine-checked below)

With `t = |x-y|` (sup metric) and `E = euclideanDist x y ≥ t`,

```text
  ‖cubeEuclideanWspKernel s′ q φ (x,y)‖ = E^{-(s′+d/q)} · |φ(x)-φ(y)|_eucl
                                        ≤ t^{-(s′+d/q)} · d · K · t^{α}
                                        = (d K) · t^{α - s′ - d/q},
```

so the `q`-th power is `(dK)^q · t^{-β}` with

```text
  β  =  d - (α - s′) q  ∈ (0, d)      ↔      0 < (α - s′) q < d.
```

The ball estimate then gives `R^{d}R^{-β} = R^{(α-s′)q}`, and the `q`-th root
restores the single factor `R^{α-s′}`.  On `□_m`, `R = 3^{m}`, so the seminorm
half carries exactly `3^{m(α-s′)}`; the `L^q` half carries `3^{-s′m}` from
`cubeEuclideanWspScalePowerWeight`, which is `3^{m(α-s′)} · 3^{-αm}`, i.e. the
same factor times the Hölder gauge's own `3^{-αm}` weight.  Hence the ONE
factor `3^{m(α-s′)}` in front of `wsInftyGauge □_m α Ksup KHol`, as the
measurement predicted.

The Euclidean/sup comparison is taken at `CoarseGraining`'s own constant `d`
(`euclideanNorm_le_dimension_mul_norm`), not `√d`; nothing downstream is
sensitive to which.
-/

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The Gagliardo singularity exponent of a `C^{0,α}` field at `(s′, q)` -/

/-- `β(d, α, s′, q) = d - (α - s′)·q`: the singularity exponent of the
`W^{s′,q}` Gagliardo integrand of a `C^{0,α}` field. -/
def cgGagliardoBeta (d : ℕ) (alpha s' q : ℝ) : ℝ := (d : ℝ) - (alpha - s') * q

theorem cgGagliardoBeta_lt {alpha s' q : ℝ} (h : 0 < (alpha - s') * q) :
    cgGagliardoBeta d alpha s' q < (d : ℝ) := by
  rw [cgGagliardoBeta]
  linarith only [h]

theorem cgGagliardoBeta_pos {alpha s' q : ℝ} (h : (alpha - s') * q < (d : ℝ)) :
    0 < cgGagliardoBeta d alpha s' q := by
  rw [cgGagliardoBeta]
  linarith only [h]

/-! ## 2. The finite exponent as a real -/

/-- `1 < p.exponent.toReal` for a `FiniteLpExponent`. -/
theorem one_lt_finiteLpExponent_toReal (q : FiniteLpExponent) : 1 < q.exponent.toReal := by
  have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top q.lt_top.ne).mpr q.one_lt
  simpa only [ENNReal.toReal_one] using h

/-! ## 3. The pointwise majorant on `CoarseGraining`'s fractional kernel -/

/-- The real-arithmetic core: `(A · t^{c})^{r} = A^{r} · t^{c r}`. -/
private theorem mul_rpow_rpow_eq {A t c r : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    (A * t ^ c) ^ r = A ^ r * t ^ (c * r) := by
  rw [Real.mul_rpow hA (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]

/-- The `q`-th power of `CoarseGraining`'s `W^{s′,q}` kernel of a `C^{0,α}` field is dominated
by the sup-metric Riesz kernel at exponent `β = d - (α-s′)q`. -/
private theorem enorm_cubeEuclideanWspKernel_rpow_le {A : Set (Vec d)}
    {s' : FractionalOrder} {q : FiniteLpExponent} {phi : Vec d → Vec d} {alpha K : ℝ}
    (hK : 0 ≤ K) (hg : HolderSeminormBoundOn A alpha K phi)
    {z : Vec d × Vec d} (h1 : z.1 ∈ A) (h2 : z.2 ∈ A) :
    ‖cubeEuclideanWspKernel s' q phi z‖ₑ ^ q.exponent.toReal ≤
      ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
        ‖z.1 - z.2‖ₑ ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal) := by
  have hrpos : 0 < q.exponent.toReal := finiteLpExponent_toReal_pos q
  have hrne : q.exponent.toReal ≠ 0 := ne_of_gt hrpos
  have hdq : 0 ≤ (d : ℝ) / q.exponent.toReal :=
    div_nonneg (Nat.cast_nonneg d) hrpos.le
  have hs'pos : 0 < s'.1 := s'.2.1
  have hexpnp : -(s'.1 + (d : ℝ) / q.exponent.toReal) ≤ 0 := by
    linarith only [hs'pos, hdq]
  rcases eq_or_ne z.1 z.2 with heq | hne
  · have hzero : cubeEuclideanWspKernel s' q phi z = 0 := by
      simp [cubeEuclideanWspKernel_apply, heq]
    rw [hzero, enorm_zero, ENNReal.zero_rpow_of_pos hrpos]
    exact zero_le
  have ht : 0 < dist z.1 z.2 := dist_pos.mpr hne
  have hE : dist z.1 z.2 ≤ euclideanDist z.1 z.2 := dist_le_euclideanDist z.1 z.2
  have hdK : (0 : ℝ) ≤ (d : ℝ) * K := mul_nonneg (Nat.cast_nonneg d) hK
  have hscal : euclideanDist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) ≤
      dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) :=
    Real.rpow_le_rpow_of_nonpos ht hE hexpnp
  have hvec : euclideanNorm (phi z.1 - phi z.2) ≤
      (d : ℝ) * K * dist z.1 z.2 ^ alpha := by
    have h1' : euclideanNorm (phi z.1 - phi z.2) ≤ (d : ℝ) * ‖phi z.1 - phi z.2‖ :=
      euclideanNorm_le_dimension_mul_norm _
    have h2' : ‖phi z.1 - phi z.2‖ ≤ K * ‖z.1 - z.2‖ ^ alpha := hg z.1 h1 z.2 h2
    rw [(dist_eq_norm z.1 z.2).symm] at h2'
    have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    calc euclideanNorm (phi z.1 - phi z.2) ≤ (d : ℝ) * ‖phi z.1 - phi z.2‖ := h1'
      _ ≤ (d : ℝ) * (K * dist z.1 z.2 ^ alpha) := mul_le_mul_of_nonneg_left h2' hdnn
      _ = (d : ℝ) * K * dist z.1 z.2 ^ alpha := by ring
  have hadd : dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) *
      dist z.1 z.2 ^ alpha =
      dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha) :=
    (Real.rpow_add ht _ _).symm
  have hMeq : dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) *
        ((d : ℝ) * K * dist z.1 z.2 ^ alpha) =
      ((d : ℝ) * K) *
        dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha) := by
    calc dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) *
          ((d : ℝ) * K * dist z.1 z.2 ^ alpha)
        = ((d : ℝ) * K) * (dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) *
            dist z.1 z.2 ^ alpha) := by ring
      _ = ((d : ℝ) * K) *
            dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha) := by
          rw [hadd]
  have hM0 : (0 : ℝ) ≤ ((d : ℝ) * K) *
      dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha) := by
    have hb : (0 : ℝ) ≤
        dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha) :=
      Real.rpow_nonneg ht.le _
    exact mul_nonneg hdK hb
  have hbound : ‖cubeEuclideanWspKernel s' q phi z‖ₑ ≤ ENNReal.ofReal (((d : ℝ) * K) *
      dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha)) := by
    rw [← ofReal_norm, norm_cubeEuclideanWspKernel]
    refine ENNReal.ofReal_le_ofReal ?_
    have hnn : (0 : ℝ) ≤ euclideanNorm (phi z.1 - phi z.2) := euclideanNorm_nonneg _
    rw [← hMeq]
    calc euclideanDist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) *
          euclideanNorm (phi z.1 - phi z.2)
        ≤ dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) *
            euclideanNorm (phi z.1 - phi z.2) := mul_le_mul_of_nonneg_right hscal hnn
      _ ≤ dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)) *
            ((d : ℝ) * K * dist z.1 z.2 ^ alpha) :=
          mul_le_mul_of_nonneg_left hvec (Real.rpow_nonneg ht.le _)
  have hexp : (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha) * q.exponent.toReal =
      -cgGagliardoBeta d alpha s'.1 q.exponent.toReal := by
    have hdiv : (d : ℝ) / q.exponent.toReal * q.exponent.toReal = (d : ℝ) :=
      div_mul_cancel₀ _ hrne
    rw [cgGagliardoBeta]
    linear_combination -hdiv
  have hMr : (((d : ℝ) * K) *
        dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha)) ^
        q.exponent.toReal = ((d : ℝ) * K) ^ q.exponent.toReal *
      dist z.1 z.2 ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal) := by
    rw [mul_rpow_rpow_eq hdK ht, hexp]
  have henorm : ‖z.1 - z.2‖ₑ = ENNReal.ofReal (dist z.1 z.2) := by
    rw [dist_eq_norm, ← ofReal_norm]
  have hsquare : (ENNReal.ofReal (((d : ℝ) * K) *
        dist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal) + alpha))) ^
        q.exponent.toReal =
      ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
        ‖z.1 - z.2‖ₑ ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hM0 hrpos.le, hMr,
      ENNReal.ofReal_mul (Real.rpow_nonneg hdK _), henorm,
      ENNReal.ofReal_rpow_of_pos ht]
  rw [← hsquare]
  exact ENNReal.rpow_le_rpow hbound hrpos.le

/-! ## 4. The seminorm half -/

/-- A Hölder bound with a positive exponent makes the field continuous on the set. -/
private theorem continuousOn_of_holderSeminormBoundOn {U : Set (Vec d)} {alpha K : ℝ}
    {f : Vec d → Vec d} (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hf : HolderSeminormBoundOn U alpha K f) : ContinuousOn f U := by
  rw [Metric.continuousOn_iff]
  intro b hb eps heps
  have hK1 : (0 : ℝ) < K + 1 := by linarith only [hK]
  have hq : (0 : ℝ) < eps / (K + 1) := div_pos heps hK1
  refine ⟨(eps / (K + 1)) ^ alpha⁻¹, Real.rpow_pos_of_pos hq _, fun a ha hab => ?_⟩
  have hstep : ‖a - b‖ ^ alpha < ((eps / (K + 1)) ^ alpha⁻¹) ^ alpha := by
    refine Real.rpow_lt_rpow (norm_nonneg _) ?_ halpha
    rwa [dist_eq_norm] at hab
  have hpow : ((eps / (K + 1)) ^ alpha⁻¹) ^ alpha = eps / (K + 1) := by
    rw [← Real.rpow_mul hq.le, inv_mul_cancel₀ (ne_of_gt halpha), Real.rpow_one]
  have hmul : K * ‖a - b‖ ^ alpha ≤ K * (eps / (K + 1)) := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left hstep.le hK
  have hlt : K * (eps / (K + 1)) < eps := by
    have hid : K * (eps / (K + 1)) = (K / (K + 1)) * eps := by field_simp
    have hfrac : K / (K + 1) < 1 := (div_lt_one hK1).2 (by linarith only [])
    rw [hid]
    calc (K / (K + 1)) * eps < 1 * eps := mul_lt_mul_of_pos_right hfrac heps
      _ = eps := one_mul eps
  have hbd := hf a ha b hb
  rw [dist_eq_norm]
  linarith only [hbd, hmul, hlt]

/-- The `W^{s′,q}` kernel of a `C^{0,α}` field is a.e. strongly measurable for the
Gagliardo cube measure: the scalar factor is globally measurable, and the vector factor
is continuous on `□ × □`. -/
private theorem aestronglyMeasurable_cubeEuclideanWspKernel_of_holder {Q : TriadicCube d}
    {s' : FractionalOrder} {q : FiniteLpExponent} {phi : Vec d → Vec d} {alpha K : ℝ}
    (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hg : HolderSeminormBoundOn (openCubeSet Q) alpha K phi)
    (hmu : Gagliardo.gagliardoCubeMeasure Q =
      (volume (openCubeSet Q))⁻¹ •
        ((volume.prod volume).restrict (openCubeSet Q ×ˢ openCubeSet Q))) :
    AEStronglyMeasurable (cubeEuclideanWspKernel s' q phi)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  have hset : MeasurableSet (openCubeSet Q) := (isOpen_openCubeSet Q).measurableSet
  have hcont := continuousOn_of_holderSeminormBoundOn hK halpha hg
  rw [hmu]
  refine AEStronglyMeasurable.smul_measure ?_ _
  have hdist : Continuous fun z : Vec d × Vec d => euclideanDist z.1 z.2 := by
    simp_rw [euclideanDist_eq_norm_sub_ofVec]
    exact (((HilbertVec.ofVecL d).continuous.comp continuous_fst).sub
      ((HilbertVec.ofVecL d).continuous.comp continuous_snd)).norm
  have hscal : AEStronglyMeasurable
      (fun z : Vec d × Vec d =>
        euclideanDist z.1 z.2 ^ (-(s'.1 + (d : ℝ) / q.exponent.toReal)))
      ((volume.prod volume).restrict (openCubeSet Q ×ˢ openCubeSet Q)) :=
    (hdist.measurable.pow_const _).aestronglyMeasurable
  have hvec : ContinuousOn (fun z : Vec d × Vec d => HilbertVec.ofVec (phi z.1 - phi z.2))
      (openCubeSet Q ×ˢ openCubeSet Q) :=
    (HilbertVec.ofVecL d).continuous.comp_continuousOn
      ((hcont.comp continuous_fst.continuousOn fun _ hz => hz.1).sub
        (hcont.comp continuous_snd.continuousOn fun _ hz => hz.2))
  exact hscal.smul (hvec.aestronglyMeasurable (hset.prod hset))

/-- **`[φ]_{W^{s′,q}(□)} ≤ d · K · C_rad(d,β)^{1/q} · L^{α-s′}`.**

The `C^{0,α} ↪ W^{s′,q}` embedding at `CoarseGraining`'s carrier, on a triadic
cube, with `L = cubeScaleFactor □` the side length.  The order loss `α - s′ >
0` is what makes the Gagliardo integral converge; the range guard is `0 < (α -
s′)·q < d`, i.e. `β ∈ (0,d)`. -/
theorem cubeEuclideanWspESeminorm_le_of_holder {Q : TriadicCube d}
    {s' : FractionalOrder} {q : FiniteLpExponent} {phi : Vec d → Vec d} {alpha K : ℝ}
    (hK : 0 ≤ K)
    (hlo : 0 < (alpha - s'.1) * q.exponent.toReal)
    (hhi : (alpha - s'.1) * q.exponent.toReal < (d : ℝ))
    (hg : HolderSeminormBoundOn (openCubeSet Q) alpha K phi) :
    cubeEuclideanWspESeminorm Q s' q phi ≤
      ENNReal.ofReal ((d : ℝ) * K *
        Regularity.radialKernelConst d
            (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) ^
          (q.exponent.toReal)⁻¹ *
        cubeScaleFactor Q ^ (alpha - s'.1)) := by
  have hrpos : 0 < q.exponent.toReal := finiteLpExponent_toReal_pos q
  have hbpos : 0 < cgGagliardoBeta d alpha s'.1 q.exponent.toReal :=
    cgGagliardoBeta_pos hhi
  have hblt : cgGagliardoBeta d alpha s'.1 q.exponent.toReal < (d : ℝ) :=
    cgGagliardoBeta_lt hlo
  have hR : 0 < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hAmeas : MeasurableSet (openCubeSet Q) := (isOpen_openCubeSet Q).measurableSet
  have hvolopen : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [volume_openCubeSet_eq_volume_cubeSet, ← cubeMeasure_apply_univ Q,
      cubeMeasure_apply_univ_eq]
  have hA0 : volume (openCubeSet Q) ≠ 0 := by
    rw [hvolopen]
    exact (ENNReal.ofReal_pos.mpr (cubeVolume_pos Q)).ne'
  have hAtop : volume (openCubeSet Q) ≠ ⊤ := by
    rw [hvolopen]
    exact ENNReal.ofReal_ne_top
  have hball : ∀ x ∈ openCubeSet Q, openCubeSet Q ⊆ Metric.ball x (cubeScaleFactor Q) :=
    fun x hx => subset_trans (openCubeSet_subset_cubeSet Q)
      (cubeSet_subset_ball_of_mem (openCubeSet_subset_cubeSet Q hx))
  have hmu : Gagliardo.gagliardoCubeMeasure Q =
      (volume (openCubeSet Q))⁻¹ •
        ((volume.prod volume).restrict (openCubeSet Q ×ˢ openCubeSet Q)) := by
    rw [← normalizedGagliardoMeasureOn_cubeSet Q, normalizedGagliardoMeasureOn_def,
      normalizedVolumeMeasureOn_def, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      Measure.prod_smul_left, Measure.prod_restrict, volume_openCubeSet_eq_volume_cubeSet]
  have hkermeas : Measurable fun z : Vec d × Vec d =>
      ‖z.1 - z.2‖ₑ ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_fst.sub measurable_snd).enorm
  have hcnn : (0 : ℝ) ≤ Regularity.radialKernelConst d
      (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
      (cubeScaleFactor Q ^ d *
        cubeScaleFactor Q ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal)) := by
    have h1 := (Regularity.radialKernelConst_pos hblt).le
    have h2 : (0 : ℝ) < cubeScaleFactor Q ^ d := pow_pos hR d
    have h3 : (0 : ℝ) < cubeScaleFactor Q ^
        (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal) := Real.rpow_pos_of_pos hR _
    exact mul_nonneg h1 (mul_nonneg h2.le h3.le)
  have hinner : ∫⁻ z in openCubeSet Q ×ˢ openCubeSet Q,
        ‖cubeEuclideanWspKernel s' q phi z‖ₑ ^ q.exponent.toReal ∂(volume.prod volume) ≤
      ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
        (ENNReal.ofReal (Regularity.radialKernelConst d
            (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
          (cubeScaleFactor Q ^ d *
            cubeScaleFactor Q ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal))) *
          volume (openCubeSet Q)) := by
    calc ∫⁻ z in openCubeSet Q ×ˢ openCubeSet Q,
          ‖cubeEuclideanWspKernel s' q phi z‖ₑ ^ q.exponent.toReal ∂(volume.prod volume)
        ≤ ∫⁻ z in openCubeSet Q ×ˢ openCubeSet Q,
            ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
              ‖z.1 - z.2‖ₑ ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal)
            ∂(volume.prod volume) :=
          setLIntegral_mono' (hAmeas.prod hAmeas)
            fun z hz => enorm_cubeEuclideanWspKernel_rpow_le hK hg hz.1 hz.2
      _ = ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
            ∫⁻ z in openCubeSet Q ×ˢ openCubeSet Q,
              ‖z.1 - z.2‖ₑ ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal)
              ∂(volume.prod volume) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
            ∫⁻ x in openCubeSet Q, ∫⁻ y in openCubeSet Q,
              ‖x - y‖ₑ ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal)
              ∂volume ∂volume := by
          rw [← Measure.prod_restrict, MeasureTheory.lintegral_prod _ hkermeas.aemeasurable]
      _ ≤ ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
            ∫⁻ _ in openCubeSet Q, ENNReal.ofReal (Regularity.radialKernelConst d
              (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
              (cubeScaleFactor Q ^ d *
                cubeScaleFactor Q ^
                  (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal))) ∂volume :=
          mul_le_mul' le_rfl (setLIntegral_mono' hAmeas fun x hx =>
            Regularity.lintegral_enorm_sub_rpow_neg_le_of_subset_ball
              (hball x hx) hR hbpos hblt)
      _ = ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
            (ENNReal.ofReal (Regularity.radialKernelConst d
                (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
              (cubeScaleFactor Q ^ d *
                cubeScaleFactor Q ^
                  (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal))) *
              volume (openCubeSet Q)) := by rw [setLIntegral_const]
  have hkey : ∫⁻ z, ‖cubeEuclideanWspKernel s' q phi z‖ₑ ^ q.exponent.toReal
        ∂(Gagliardo.gagliardoCubeMeasure Q) ≤
      ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
        ENNReal.ofReal (Regularity.radialKernelConst d
            (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
          (cubeScaleFactor Q ^ d *
            cubeScaleFactor Q ^
              (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal))) := by
    rw [hmu, lintegral_smul_measure]
    calc (volume (openCubeSet Q))⁻¹ *
          ∫⁻ z in openCubeSet Q ×ˢ openCubeSet Q,
            ‖cubeEuclideanWspKernel s' q phi z‖ₑ ^ q.exponent.toReal ∂(volume.prod volume)
        ≤ (volume (openCubeSet Q))⁻¹ *
            (ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
              (ENNReal.ofReal (Regularity.radialKernelConst d
                  (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
                (cubeScaleFactor Q ^ d *
                  cubeScaleFactor Q ^
                    (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal))) *
                volume (openCubeSet Q))) := mul_le_mul' le_rfl hinner
      _ = ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
            ENNReal.ofReal (Regularity.radialKernelConst d
                (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
              (cubeScaleFactor Q ^ d *
                cubeScaleFactor Q ^
                  (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal))) *
            ((volume (openCubeSet Q))⁻¹ * volume (openCubeSet Q)) := by ring
      _ = ENNReal.ofReal (((d : ℝ) * K) ^ q.exponent.toReal) *
            ENNReal.ofReal (Regularity.radialKernelConst d
                (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) *
              (cubeScaleFactor Q ^ d *
                cubeScaleFactor Q ^
                  (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal))) := by
          rw [ENNReal.inv_mul_cancel hA0 hAtop, mul_one]
  have hinv : (0 : ℝ) ≤ (q.exponent.toReal)⁻¹ := inv_nonneg.mpr hrpos.le
  have hdK : (0 : ℝ) ≤ (d : ℝ) * K := mul_nonneg (Nat.cast_nonneg d) hK
  have hdKt : (0 : ℝ) ≤ ((d : ℝ) * K) ^ q.exponent.toReal := Real.rpow_nonneg hdK _
  have hdKti : (0 : ℝ) ≤ (((d : ℝ) * K) ^ q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ :=
    Real.rpow_nonneg hdKt _
  have halpha : 0 < alpha := by
    have hdiff : 0 < alpha - s'.1 := pos_of_mul_pos_left hlo hrpos.le
    linarith only [hdiff, s'.2.1]
  rw [cubeEuclideanWspESeminorm_eq_lintegral Q s' q phi
    (aestronglyMeasurable_cubeEuclideanWspKernel_of_holder hK halpha hg hmu), one_div]
  refine (ENNReal.rpow_le_rpow hkey hinv).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hinv,
    ENNReal.ofReal_rpow_of_nonneg hdKt hinv,
    ENNReal.ofReal_rpow_of_nonneg hcnn hinv, ← ENNReal.ofReal_mul hdKti]
  congr 1
  have hfirst : (((d : ℝ) * K) ^ q.exponent.toReal) ^ (q.exponent.toReal)⁻¹ =
      (d : ℝ) * K := by
    rw [← Real.rpow_mul hdK, mul_inv_cancel₀ hrpos.ne', Real.rpow_one]
  have hCnn : (0 : ℝ) ≤ Regularity.radialKernelConst d
      (cgGagliardoBeta d alpha s'.1 q.exponent.toReal) :=
    (Regularity.radialKernelConst_pos hblt).le
  have hpownn : (0 : ℝ) ≤ cubeScaleFactor Q ^ d *
      cubeScaleFactor Q ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal) := by
    have h3 : (0 : ℝ) < cubeScaleFactor Q ^
        (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal) := Real.rpow_pos_of_pos hR _
    exact mul_nonneg (pow_pos hR d).le h3.le
  have hpow : (cubeScaleFactor Q ^ d *
      cubeScaleFactor Q ^ (-cgGagliardoBeta d alpha s'.1 q.exponent.toReal)) ^
        (q.exponent.toReal)⁻¹ = cubeScaleFactor Q ^ (alpha - s'.1) := by
    have hRd : (cubeScaleFactor Q : ℝ) ^ d = cubeScaleFactor Q ^ ((d : ℝ)) :=
      (Real.rpow_natCast _ d).symm
    rw [hRd, ← Real.rpow_add hR, ← Real.rpow_mul hR.le]
    congr 1
    rw [cgGagliardoBeta]
    have hinv : q.exponent.toReal * (q.exponent.toReal)⁻¹ = 1 :=
      mul_inv_cancel₀ hrpos.ne'
    linear_combination (alpha - s'.1) * hinv
  rw [Real.mul_rpow hCnn hpownn, hfirst, hpow, ← mul_assoc]

end

end Algsuperdiff.Section4.Provider.Homogenization

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyBox
public import Mathlib.Analysis.Convolution

/-!
# HomMollifyPairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the mollifier's pairing against the gauge

## The core lemma of this file

The mollifier calculus needs one estimate, and this module proves it:

> **The kernel pairing.**  If the vector field `F` obeys the translate-uniform
> negative gauge `‖(F)_{y+□_n}‖ ≤ A 3^{-ns}` at the scale `n`, then for every
> probability density `ψ` (nonnegative, unit mass) the `ψ`-mixture of the
> scale-`n` box averages of `F` obeys the *same* bound:
> ```text
>   ‖∫ ψ(z) (F)_{x-z+□_n} dz‖ ≤ A · 3^{-ns}   for every x.
> ```
> (`norm_boxMixtureVec_le_of_uniformBoxGauge`, constant exactly `1`.)

The mechanism is the manuscript's own: a mollifier at scale `3^n` is a
*superposition of translated scale-`n` box averages*, and the negative gauge is
by definition a uniform bound on each of them.  No dimensional constant is
lost, because a probability density has unit mass; the dimensional factor
`C(d)` of this file enters only later, when the gradient vector is paired
against a displacement in the supremum norm (`HomMollifyGradient`).

The identification of a mollifier with such a superposition is
`convolution_boxKernel_eq_boxAverage` below: convolving with the normalized
indicator `boxKernel n` of the scale-`n` box *is* the sliding box average, so
convolving with `ψ ⋆ boxKernel n` is the `ψ`-mixture of those averages.
`ψ ⋆ boxKernel n` is smooth whenever `ψ` is, which is what makes the family
admissible as a test function against the weak gradient.

## The reconstruction residue

The gauge used here is the *translate* gauge `UniformBoxGaugeBound`, not the
grid gauge `negBesovInftyNorm`.  The missing implication is exactly:

```text
  RECONSTRUCTION.  Let F ∈ L¹_loc(□_m).  Suppose that for every n ≤ m and
  every triadic cube R ⊆ □_m of scale n one has ‖(F)_R‖ ≤ A 3^{-ns}.  Then
  for every n ≤ m and every x with x + □_n ⊆ □_m,
      ‖(F)_{x+□_n}‖ ≤ C(d) · (1 + (1 - 3^{-(1-s)})⁻¹) · A · 3^{-ns}.
```

Its proof is the triadic martingale decomposition `F = Σ_k (E_k F - E_{k-1}F)`
(`CoarseGraining`'s `cubeProjection`, whose a.e. convergence is
`ae_tendsto_cubeProjection_of_integrableOn`): the term `E_n F` is bounded by
the grid hypothesis directly, and each finer increment `E_k F - E_{k-1} F`
has mean zero on every grid cube of scale `k+1`, so only the `O(3^{(n-k)(d-1)})`
cubes straddling `∂(x + □_n)` contribute, giving the geometric factor
`3^{k-n}` and the sum `Σ_{k<n} 3^{k(1-s)}·3^{-n} = 3^{-ns}·(1-3^{-(1-s)})⁻¹`.

It is *not* formalized in this file.  The ingredients absent from the tree are
the boundary-layer count for the straddling cubes and the `L¹` convergence of
the triadic projections; `CoarseGraining` supplies `cubeProjection` and its
a.e. convergence but neither of the other two.  Consumers must therefore either
harvest the Step-3 estimate at all translates (which the coarse-graining
machinery does supply — the source estimate is not grid-bound) or discharge the
reconstruction separately.

## Main definitions and results

* `boxKernel n` — the normalized indicator of the scale-`n` box at the
  origin, with `integrable_boxKernel` and `locallyIntegrable_boxKernel`.
* `convolution_boxKernel_eq_boxAverage` — **unconditionally**, convolving with
  `boxKernel n` is the sliding scale-`n` box average.
* `boxMixture`, `boxMixtureVec` — the `ψ`-mixture of sliding box averages,
  and `boxMixture_eq_convolution`.
* `abs_boxMixture_le` — a uniform bound on the box averages passes to the
  mixture, with no integrability hypothesis (the Bochner integral of a
  non-integrable function is `0`, which obeys the bound as well).
* `norm_boxMixtureVec_le_of_uniformBoxGauge` — **the kernel pairing**.

## References

* ABK26, the negative Besov seminorm definition.
* ABK26, Theorem B Step 3.
-/

open MeasureTheory HCPolySupport

open scoped Convolution

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The box kernel -/

/-- **The scale-`n` box kernel**: the normalized indicator of the box of side
`3^n` centred at the origin.  Convolution with it is the sliding box average
(`convolution_boxKernel_eq_boxAverage`). -/
def boxKernel (n : ℤ) : Vec d → ℝ :=
  Set.indicator (boxSet n 0) fun _ => (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹

theorem boxKernel_def (n : ℤ) :
    boxKernel (d := d) n = Set.indicator (boxSet n 0) fun _ => (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹ := rfl

theorem boxKernel_apply_of_mem {n : ℤ} {z : Vec d} (hz : z ∈ boxSet n 0) :
    boxKernel n z = (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹ := by
  rw [boxKernel_def, Set.indicator_of_mem hz]

theorem boxKernel_apply_of_not_mem {n : ℤ} {z : Vec d} (hz : z ∉ boxSet n 0) :
    boxKernel n z = 0 := by
  rw [boxKernel_def, Set.indicator_of_notMem hz]

theorem integrable_boxKernel (n : ℤ) : Integrable (boxKernel (d := d) n) volume := by
  refine (integrable_indicator_iff (measurableSet_boxSet n 0)).2 ?_
  exact integrableOn_const (by rw [volume_boxSet]; exact ENNReal.ofReal_ne_top)

theorem locallyIntegrable_boxKernel (n : ℤ) :
    LocallyIntegrable (boxKernel (d := d) n) volume :=
  (integrable_boxKernel n).locallyIntegrable

/-! ## 2. Convolution with the box kernel is the sliding box average -/

/-- **The identification.**  Convolving `f` with the scale-`n` box kernel
produces exactly the sliding scale-`n` box average of `f`.  No hypothesis on
`f` is needed: both sides are the same Bochner integral. -/
theorem convolution_boxKernel_eq_boxAverage (n : ℤ) (f : Vec d → ℝ) (x : Vec d) :
    (boxKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x = boxAverage n x f := by
  have hswap : ∫ t : Vec d, boxKernel n t * f (x - t)
      = ∫ t : Vec d, boxKernel n (x - t) * f t := by
    have h := integral_sub_left_eq_self
      (fun t : Vec d => boxKernel n t * f (x - t)) (volume : Measure (Vec d)) x
    simpa only [sub_sub_cancel] using h.symm
  have hpt : ∀ t : Vec d, boxKernel n (x - t) * f t
      = (boxSet n x).indicator (fun y => (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹ * f y) t := by
    intro t
    by_cases ht : t ∈ boxSet n x
    · have hmem : x - t ∈ boxSet (d := d) n 0 := by
        rw [mem_boxSet_iff, sub_zero]
        rw [mem_boxSet_iff] at ht
        rw [← norm_neg, neg_sub]
        exact ht
      rw [boxKernel_apply_of_mem hmem, Set.indicator_of_mem ht]
    · have hmem : x - t ∉ boxSet (d := d) n 0 := by
        intro hc
        refine ht ?_
        rw [mem_boxSet_iff]
        rw [mem_boxSet_iff, sub_zero] at hc
        rw [← norm_neg, neg_sub]
        exact hc
      rw [boxKernel_apply_of_not_mem hmem, Set.indicator_of_notMem ht, zero_mul]
  rw [convolution_lsmul]
  simp only [smul_eq_mul]
  rw [hswap]
  simp only [hpt]
  rw [integral_indicator (measurableSet_boxSet n x), boxAverage_eq_inv_mul_integral,
    integral_const_mul]

/-! ## 3. The mixture of sliding box averages -/

/-- The **`ψ`-mixture of the sliding scale-`n` box averages** of `f`: the
value at `x` of the convolution of `ψ` with the sliding average. -/
def boxMixture (n : ℤ) (ψ f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ z, ψ z * boxAverage n (x - z) f

/-- The coordinatewise mixture of a vector field. -/
def boxMixtureVec (n : ℤ) (ψ : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d) : Vec d :=
  fun i => boxMixture n ψ (fun y => F y i) x

theorem boxMixture_def (n : ℤ) (ψ f : Vec d → ℝ) (x : Vec d) :
    boxMixture n ψ f x = ∫ z, ψ z * boxAverage n (x - z) f := rfl

theorem boxMixtureVec_apply (n : ℤ) (ψ : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    boxMixtureVec n ψ F x i = boxMixture n ψ (fun y => F y i) x := rfl

/-- The mixture is the convolution of `ψ` with the sliding average. -/
theorem boxMixture_eq_convolution (n : ℤ) (ψ f : Vec d → ℝ) (x : Vec d) :
    boxMixture n ψ f x
      = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => boxAverage n y f) x := by
  rw [convolution_lsmul, boxMixture_def]
  simp only [smul_eq_mul]

/-- A density of unit mass is integrable (otherwise its integral would be
zero by the junk-value convention). -/
theorem integrable_of_integral_eq_one {ψ : Vec d → ℝ} (hψ1 : ∫ z, ψ z = 1) :
    Integrable ψ volume := by
  by_contra hc
  rw [integral_undef hc] at hψ1
  exact zero_ne_one hψ1

/-! ## 4. The kernel pairing -/

/-- **The scalar kernel pairing.**  A uniform bound `B` on the sliding
scale-`n` box averages of `f` passes to every mixture of them against a
probability density, at constant exactly `1`.

No integrability hypothesis on the mixture is required: when the mixing
integral fails to converge the Bochner integral is `0`, which obeys the
bound. -/
theorem abs_boxMixture_le {n : ℤ} {ψ f : Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : ∫ z, ψ z = 1)
    (hbd : ∀ y, |boxAverage n y f| ≤ B) (x : Vec d) :
    |boxMixture n ψ f x| ≤ B := by
  have hψ : Integrable ψ volume := integrable_of_integral_eq_one hψ1
  by_cases hint : Integrable (fun z => ψ z * boxAverage n (x - z) f) volume
  · have hmono : ∀ z : Vec d, |ψ z * boxAverage n (x - z) f| ≤ ψ z * B := by
      intro z
      rw [abs_mul, abs_of_nonneg (hψ0 z)]
      exact mul_le_mul_of_nonneg_left (hbd (x - z)) (hψ0 z)
    calc |boxMixture n ψ f x| ≤ ∫ z, |ψ z * boxAverage n (x - z) f| := by
          rw [boxMixture_def]
          exact abs_integral_le_integral_abs
      _ ≤ ∫ z, ψ z * B := integral_mono hint.abs (hψ.mul_const B) hmono
      _ = B := by rw [integral_mul_const, hψ1, one_mul]
  · rw [boxMixture_def, integral_undef hint, abs_zero]
    exact hB

/-- **THE KERNEL PAIRING**.

If the vector field `F` obeys the translate-uniform negative gauge of order
`-s` on the scales `≤ m`, then at every scale `n ≤ m` and every point `x`,
the mixture of the sliding scale-`n` box averages of `F` against any
probability density `ψ` obeys the same bound `A · 3^{-ns}`.

The constant is exactly `1`: a mollifier at scale `3^n` is a superposition of
translated scale-`n` box averages of total mass one, and the gauge bounds each
of them. -/
theorem norm_boxMixtureVec_le_of_uniformBoxGauge {m : ℤ} {s A : ℝ} {F : Vec d → Vec d}
    (h : UniformBoxGaugeBound m s A F) {n : ℤ} (hn : n ≤ m)
    {ψ : Vec d → ℝ} (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : ∫ z, ψ z = 1) (x : Vec d) :
    ‖boxMixtureVec n ψ F x‖ ≤ A * (3 : ℝ) ^ (-((n : ℝ) * s)) := by
  have hB : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-((n : ℝ) * s)) :=
    mul_nonneg h.nonneg (three_rpow_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hB).2 ?_
  intro i
  rw [Real.norm_eq_abs, boxMixtureVec_apply]
  refine abs_boxMixture_le hB hψ0 hψ1 ?_ x
  intro y
  have hcoord : |boxAverage n y fun z => F z i| ≤ ‖boxAverageVec n y F‖ := by
    have := norm_le_pi_norm (boxAverageVec n y F) i
    rwa [Real.norm_eq_abs, boxAverageVec_apply] at this
  exact hcoord.trans (h n hn y)

end

end Algsuperdiff.Section4.Provider.Homogenization

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyChain

/-!
# HomSpineRepLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the continuous representative, PRODUCED

## What this module is

The §4.5 spine has ONE irreducible frame item: the
existence of a continuous representative of the `H¹₀` zero extension of `u -
v`.  The print obtains it in the paper by citing `u - v ∈ H¹₀(□_m)`, which for
`d ≥ 2` does not supply one; the correction records the gap and the suggested
print correction.  This module carries it out:

```text
  (a)  w ⋆ ψ_k → w   a.e.                      (ae_tendsto_convolution_mollifyBump)
  (b)  each w ⋆ ψ_k is (1-s, 16 d A)-Hölder     (the mollifier chain, ψ-uniform)
  (c)  (a) + (b)  ⟹  w has a continuous representative
```

Step (a) is Mathlib's
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`; its ratio
hypothesis `rOut ≤ K · rIn` holds for the `mollifyBump` at `K = 2` EXACTLY
(`rOut = 1/(k+1)`, `rIn = 1/(2(k+1))`).  Step (b) is the
`holderSeminormBoundOn_convolution_of_uniformBoxGauge`, whose constant does not
depend on the mollifier.  Step (c) is the scalar precise-representative lemma
`exists_continuous_ae_eq_of_uniformHolderBall` proved here.

### Why (c) needs no compactness

The classical route is Arzelà–Ascoli on the closure of the cube.  It is not
needed: a co-null set is DENSE, and equicontinuity transports the Cauchy
property from a dense set to EVERY point,

```text
  |f_k x - f_j x| ≤ 2 K ‖x - z‖^α + |f_k z - f_j z|,
```

so `(f_k x)` is Cauchy at every `x` and the pointwise limit `g` exists
everywhere.  `g` is then Hölder on every ball of radius `r` by the
`holderSeminormBoundOn_of_tendsto`, hence continuous; and `g = w` wherever the
a.e. convergence holds, hence a.e.  No covering, no compactness, no
completeness beyond that of `ℝ`.

## Main results

* `ae_tendsto_convolution_mollifyBump` — step (a), the a.e. mollifier limit;
* `exists_continuous_ae_eq_of_uniformHolderBall` — step (c), the scalar
  precise representative from a uniformly Hölder, a.e.-convergent family;
* `exists_continuous_ae_eq_of_uniformBoxGauge` — **THE PRODUCER**: the
  continuous representative from the negative-order gauge on `∇w` plus local
  integrability and compact support ALONE.  No representative is assumed.

## References

* ABK26, Theorem B Step 3.
-/

open MeasureTheory HCPolySupport

open scoped Convolution

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The a.e. mollifier limit -/

/-- **The a.e. mollification limit.**

For an integrable scalar, the mollifications along the shrinking bump family
converge almost everywhere.  This is Mathlib's Lebesgue-point statement; the
only repository-specific input is the radius ratio, which for `mollifyBump` is
`rOut = 2 · rIn` exactly, so the hypothesis holds at `K = 2` with no slack. -/
theorem ae_tendsto_convolution_mollifyBump {w : Vec d → ℝ} (hwI : Integrable w volume) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Filter.Tendsto (fun k : ℕ => (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((mollifyBump (d := d) k).normed volume)) x) Filter.atTop (nhds (w x)) := by
  have hbase : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Filter.Tendsto (fun k : ℕ => (((mollifyBump (d := d) k).normed volume)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x) Filter.atTop (nhds (w x)) := by
    refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (K := 2) tendsto_mollifyBump_rOut ?_ hwI.locallyIntegrable
    filter_upwards with k
    have heq : (2 : ℝ) * (1 / (2 * ((k : ℝ) + 1))) = 1 / ((k : ℝ) + 1) := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by linarith only [hk0]
      field_simp
    change (mollifyBump (d := d) k).rOut ≤ 2 * (mollifyBump (d := d) k).rIn
    change (1 : ℝ) / ((k : ℝ) + 1) ≤ 2 * (1 / (2 * ((k : ℝ) + 1)))
    rw [heq]
  refine hbase.mono fun x hx => ?_
  have hrw : ∀ k : ℕ, (((mollifyBump (d := d) k).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x
      = (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((mollifyBump (d := d) k).normed volume)) x := by
    intro k
    rw [convolution_comm_real ((mollifyBump (d := d) k).normed volume) w]
  simpa only [hrw] using hx

/-! ## 2. Hölder bounds and distances -/

/-- A Hölder bound on a ball, read as a distance estimate. -/
theorem dist_lt_of_holderSeminormBoundOn {alpha K r eps : ℝ} {h : Vec d → ℝ} {z x y : Vec d}
    (hh : HolderSeminormBoundOn (Metric.closedBall z r) alpha K h)
    (hx : x ∈ Metric.closedBall z r) (hy : y ∈ Metric.closedBall z r)
    (hmod : K * dist x y ^ alpha < eps) : dist (h x) (h y) < eps :=
  calc dist (h x) (h y) = ‖h x - h y‖ := dist_eq_norm _ _
    _ ≤ K * ‖x - y‖ ^ alpha := hh x hx y hy
    _ = K * dist x y ^ alpha := by rw [dist_eq_norm]
    _ < eps := hmod

/-- **The modulus of continuity of a Hölder bound.**  For a positive exponent
the map `t ↦ K t^α` vanishes at `0`, so every tolerance is met on a small
enough scale. -/
theorem exists_delta_holder_lt {alpha K : ℝ} (halpha : 0 < alpha) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 ≤ t → t < delta → K * t ^ alpha < eps := by
  have hca : Filter.Tendsto (fun t : ℝ => t ^ alpha) (nhds 0) (nhds ((0 : ℝ) ^ alpha)) :=
    Real.continuousAt_rpow_const (0 : ℝ) alpha (Or.inr halpha.le)
  rw [Real.zero_rpow (ne_of_gt halpha)] at hca
  have hmul : Filter.Tendsto (fun t : ℝ => K * t ^ alpha) (nhds 0) (nhds 0) := by
    simpa using hca.const_mul K
  have hev : ∀ᶠ t : ℝ in nhds 0, dist (K * t ^ alpha) 0 < eps :=
    Metric.tendsto_nhds.mp hmul eps heps
  obtain ⟨delta, hdelta0, hdelta⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨delta, hdelta0, fun t ht0 htd => ?_⟩
  have hdt : dist t (0 : ℝ) < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    exact htd
  have hlt := hdelta hdt
  rw [Real.dist_eq, sub_zero] at hlt
  exact lt_of_le_of_lt (le_abs_self _) hlt

/-! ## 3. The scalar precise representative -/

/-- **THE SCALAR PRECISE REPRESENTATIVE.**

A family of scalars that is uniformly Hölder — one exponent `α > 0`, one
constant `K`, on every closed ball of one fixed radius `r > 0` — and converges
almost everywhere has a CONTINUOUS limit, defined at every point, which is an
everywhere-defined representative of the a.e. limit.

The proof is the equicontinuity transport described in the module docstring:
the convergence set is co-null, hence dense; the Hölder bound turns density
into the Cauchy property at every point; `ℝ` is complete. -/
theorem exists_continuous_ae_eq_of_uniformHolderBall {alpha K r : ℝ}
    (halpha : 0 < alpha) (hr : 0 < r)
    {f : ℕ → Vec d → ℝ} {w : Vec d → ℝ}
    (hf : ∀ (z : Vec d) (k : ℕ),
      HolderSeminormBoundOn (Metric.closedBall z r) alpha K (f k))
    (hae : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Filter.Tendsto (fun k => f k x) Filter.atTop (nhds (w x))) :
    ∃ g : Vec d → ℝ, Continuous g ∧ w =ᵐ[volume] g := by
  classical
  have hdense : Dense {x : Vec d |
      Filter.Tendsto (fun k => f k x) Filter.atTop (nhds (w x))} :=
    MeasureTheory.Measure.dense_of_ae hae
  /- every point is a Cauchy point: transport from a nearby point of the dense s -/
  have hCauchy : ∀ x : Vec d, CauchySeq (fun k => f k x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro eps heps
    obtain ⟨delta, hdelta0, hdelta⟩ :=
      exists_delta_holder_lt (K := K) halpha (div_pos heps (by norm_num : (0 : ℝ) < 3))
    obtain ⟨z, hzmem, hzdist⟩ := hdense.exists_dist_lt x (lt_min hdelta0 hr)
    have hzr : dist x z ≤ r := le_of_lt (lt_of_lt_of_le hzdist (min_le_right _ _))
    have hzd : dist x z < delta := lt_of_lt_of_le hzdist (min_le_left _ _)
    have hxmem : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
    have hzball : z ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_comm]
      exact hzr
    have hnear : ∀ k : ℕ, dist (f k x) (f k z) < eps / 3 := fun k =>
      dist_lt_of_holderSeminormBoundOn (hf x k) hxmem hzball
        (hdelta (dist x z) dist_nonneg hzd)
    have hzc : CauchySeq (fun k => f k z) := hzmem.cauchySeq
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.mp hzc (eps / 3) (div_pos heps (by norm_num : (0 : ℝ) < 3))
    refine ⟨N, fun n hn j hj => ?_⟩
    have h1 : dist (f n x) (f n z) < eps / 3 := hnear n
    have h2 : dist (f n z) (f j z) < eps / 3 := hN n hn j hj
    have h3 : dist (f j z) (f j x) < eps / 3 := by
      rw [dist_comm]
      exact hnear j
    have t1 : dist (f n x) (f j x) ≤ dist (f n x) (f n z) + dist (f n z) (f j x) :=
      dist_triangle (f n x) (f n z) (f j x)
    have t2 : dist (f n z) (f j x) ≤ dist (f n z) (f j z) + dist (f j z) (f j x) :=
      dist_triangle (f n z) (f j z) (f j x)
    linarith only [t1, t2, h1, h2, h3]
  choose g hg using fun x : Vec d => cauchySeq_tendsto_of_complete (hCauchy x)
  have hgHolder : ∀ z : Vec d, HolderSeminormBoundOn (Metric.closedBall z r) alpha K g :=
    fun z => holderSeminormBoundOn_of_tendsto (hf z) fun x _ => hg x
  refine ⟨g, ?_, ?_⟩
  · rw [Metric.continuous_iff]
    intro b eps heps
    obtain ⟨delta, hdelta0, hdelta⟩ := exists_delta_holder_lt (K := K) halpha heps
    refine ⟨min delta r, lt_min hdelta0 hr, fun a hab => ?_⟩
    have habr : dist a b ≤ r := le_of_lt (lt_of_lt_of_le hab (min_le_right _ _))
    have habd : dist a b < delta := lt_of_lt_of_le hab (min_le_left _ _)
    exact dist_lt_of_holderSeminormBoundOn (hgHolder b)
      (Metric.mem_closedBall.mpr habr) (Metric.mem_closedBall_self hr.le)
      (hdelta (dist a b) dist_nonneg habd)
  · filter_upwards [hae] with x hx
    exact tendsto_nhds_unique hx (hg x)

/-! ## 4. The producer -/

/-- **THE PRODUCER — the continuous representative from the gauge alone.**

From the translate-uniform negative gauge of order `-s` on `∇w`, together with
the frame items the chain already needs (`w` weakly differentiable on `Vec d`,
integrable, compactly supported, gradient coordinates integrable), the scalar
`w` HAS a continuous representative.  Nothing about a representative is
assumed: this is the step the manuscript obtains by citing `H¹₀` membership,
which does not supply it.

The radius is `r = 3^m / 2`, so that a closed `r`-ball has diameter at most
`3^m` and the `ψ`-uniform Hölder bound applies on it with constant `16 d A`. -/
theorem exists_continuous_ae_eq_of_uniformBoxGauge {m : ℤ} {s A : ℝ}
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G) (hs0 : 0 < s) (hs2 : s ≤ 1 / 2) :
    ∃ g : Vec d → ℝ, Continuous g ∧ w =ᵐ[volume] g := by
  have halpha : (0 : ℝ) < 1 - s := by linarith only [hs2]
  have hthree : (0 : ℝ) < (3 : ℝ) ^ ((m : ℤ) : ℝ) := three_rpow_pos _
  have hr : (0 : ℝ) < (3 : ℝ) ^ ((m : ℤ) : ℝ) / 2 := by linarith only [hthree]
  refine exists_continuous_ae_eq_of_uniformHolderBall (K := 16 * (d : ℝ) * A)
    (r := (3 : ℝ) ^ ((m : ℤ) : ℝ) / 2) halpha hr ?_ (ae_tendsto_convolution_mollifyBump hwI)
  intro z k
  refine holderSeminormBoundOn_convolution_of_uniformBoxGauge hw hwI hwc hGI hgauge hs0 hs2
    (isMollifierDensity_mollifyBump k) ?_
  intro x hx y hy
  rw [Metric.mem_closedBall] at hx hy
  have hyz : dist z y ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ) / 2 := by
    rw [dist_comm]
    exact hy
  calc ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
    _ ≤ dist x z + dist z y := dist_triangle _ _ _
    _ ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ) / 2 + (3 : ℝ) ^ ((m : ℤ) : ℝ) / 2 := add_le_add hx hyz
    _ = (3 : ℝ) ^ ((m : ℤ) : ℝ) := by ring

end

end Algsuperdiff.Section4.Provider.Homogenization

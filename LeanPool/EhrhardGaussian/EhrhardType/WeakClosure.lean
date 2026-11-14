/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.Characterization
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weak closure of Ehrhard-type laws

A strict margin in the normal probability parameter permits passage through the
open/closed Portmanteau bounds without requiring the limiting law to be atomless.
This proves weak closure of Ehrhard-type laws, including constant limits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace EhrhardGaussian.EhrhardType

/-- A strict bound for a limit quantile is eventually a bound for the approximating quantiles. -/
theorem eventually_gaussianQuantileTransport_lt
    {ν : ℕ → ProbabilityMeasure ℝ} {ν' : ProbabilityMeasure ℝ}
    (hlim : Tendsto ν atTop (nhds ν')) {z x : ℝ}
    (hx : gaussianQuantileTransport (ν' : Measure ℝ) z < x) :
    ∀ᶠ k in atTop, gaussianQuantileTransport (ν k : Measure ℝ) z < x := by
  have hxCDF := (gaussianQuantileTransport_lt_iff _ z x).mp hx
  have hENN : ENNReal.ofReal (cdf (gaussianReal 0 1) z) < (ν' : Measure ℝ) (Iio x) :=
    (ENNReal.ofReal_lt_iff_lt_toReal (cdf_nonneg _ _) (measure_ne_top _ _)).mpr hxCDF
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (isOpen_Iio (a := x))
  have hev := eventually_lt_of_lt_liminf (hENN.trans_le hport)
  filter_upwards [hev] with k hk
  apply (gaussianQuantileTransport_lt_iff _ z x).mpr
  exact (ENNReal.ofReal_lt_iff_lt_toReal (cdf_nonneg _ _) (measure_ne_top _ _)).mp hk

/-- A strict quantile bound persists at a slightly larger normal argument. -/
theorem exists_gt_gaussianQuantileTransport_lt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z x : ℝ} (hx : gaussianQuantileTransport μ z < x) :
    ∃ w > z, gaussianQuantileTransport μ w < x := by
  have hxCDF := (gaussianQuantileTransport_lt_iff μ z x).mp hx
  have hopen : IsOpen {w | cdf (gaussianReal 0 1) w < μ.real (Iio x)} :=
    isOpen_lt continuous_standardGaussian_cdf continuous_const
  obtain ⟨l, u, hz, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hxCDF)
  obtain ⟨w, hzw, hwu⟩ := exists_between hz.2
  exact ⟨w, hzw, (gaussianQuantileTransport_lt_iff μ w x).mpr
    (hsub ⟨hz.1.trans hzw, hwu⟩)⟩

/-- A quantile bound controls the mass of the corresponding closed half-line. -/
theorem normal_mass_le_of_transport_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z R : ℝ} (hz : gaussianQuantileTransport μ z ≤ R) :
    (gaussianReal 0 1) (Iic z) ≤ μ (Iic R) := by
  rw [← map_gaussianQuantileTransport μ, Measure.map_apply
    (measurable_gaussianQuantileTransport μ) measurableSet_Iic]
  apply measure_mono
  intro y hy
  exact ((monotone_gaussianQuantileTransport μ) hy).trans hz

/-- Closed Portmanteau with a strict normal-argument margin bounds a limit quantile. -/
theorem transport_le_of_eventually_le
    {ν : ℕ → ProbabilityMeasure ℝ} {ν' : ProbabilityMeasure ℝ}
    (hlim : Tendsto ν atTop (nhds ν')) {z w R : ℝ} (hzw : z < w)
    (hev : ∀ᶠ k in atTop, gaussianQuantileTransport (ν k : Measure ℝ) w ≤ R) :
    gaussianQuantileTransport (ν' : Measure ℝ) z ≤ R := by
  have hmass : ∀ᶠ k in atTop, (gaussianReal 0 1) (Iic w) ≤ (ν k : Measure ℝ) (Iic R) :=
    hev.mono fun _ hk => normal_mass_le_of_transport_le _ hk
  have hlow : (gaussianReal 0 1) (Iic w) ≤
      atTop.limsup (fun k => (ν k : Measure ℝ) (Iic R)) :=
    le_limsup_of_frequently_le hmass.frequently
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim
    (isClosed_Iic (a := R))
  have hreal : cdf (gaussianReal 0 1) w ≤ (ν' : Measure ℝ).real (Iic R) := by
    rw [cdf_eq_real]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hlow.trans hport)
  apply le_of_forall_gt_imp_ge_of_dense
  intro a hRa
  have hCDF : cdf (gaussianReal 0 1) z < (ν' : Measure ℝ).real (Iio a) :=
    ((strictMono_standardGaussian_cdf hzw).trans_le hreal).trans_le
      (measureReal_mono (Iic_subset_Iio.mpr hRa))
  exact ((gaussianQuantileTransport_lt_iff _ z a).mpr hCDF).le

/-- Weak limits of monotone-convex Gaussian transports still have convex canonical transport. -/
theorem convexOn_gaussianQuantileTransport_of_tendsto
    {ν : ℕ → ProbabilityMeasure ℝ} {ν' : ProbabilityMeasure ℝ}
    (hlim : Tendsto ν atTop (nhds ν')) (hν : ∀ k, IsEhrhardType (ν k : Measure ℝ)) :
    ConvexOn ℝ univ (gaussianQuantileTransport (ν' : Measure ℝ)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change gaussianQuantileTransport (ν' : Measure ℝ) (a * x + b * y) ≤
    a * gaussianQuantileTransport (ν' : Measure ℝ) x + b * gaussianQuantileTransport (ν' : Measure
      ℝ) y
  apply le_of_forall_pos_le_add
  intro ε hε
  let u := gaussianQuantileTransport (ν' : Measure ℝ) x + ε
  let v := gaussianQuantileTransport (ν' : Measure ℝ) y + ε
  obtain ⟨x', hxx', hxu⟩ := exists_gt_gaussianQuantileTransport_lt (ν' : Measure ℝ)
    (show gaussianQuantileTransport (ν' : Measure ℝ) x < u by dsimp [u]; linarith only [hε])
  obtain ⟨y', hyy', hyv⟩ := exists_gt_gaussianQuantileTransport_lt (ν' : Measure ℝ)
    (show gaussianQuantileTransport (ν' : Measure ℝ) y < v by dsimp [v]; linarith only [hε])
  have hmargin : a * x + b * y < a * x' + b * y' := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith only [hab, ha0]
      simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hyy'
    · exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hxx' (lt_of_le_of_ne ha (Ne.symm ha0)))
        (mul_le_mul_of_nonneg_left hyy'.le hb)
  have hev : ∀ᶠ k in atTop,
      gaussianQuantileTransport (ν k : Measure ℝ) (a * x' + b * y') ≤ a * u + b * v := by
    filter_upwards [eventually_gaussianQuantileTransport_lt hlim hxu,
      eventually_gaussianQuantileTransport_lt hlim hyv] with k hkx hky
    exact ((convexOn_gaussianQuantileTransport (hν k)).2 (mem_univ _) (mem_univ _) ha hb hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left hkx.le ha) (mul_le_mul_of_nonneg_left hky.le hb))
  have hbound := transport_le_of_eventually_le hlim hmargin hev
  have heq : a * u + b * v = a * gaussianQuantileTransport (ν' : Measure ℝ) x +
      b * gaussianQuantileTransport (ν' : Measure ℝ) y + ε := by
    dsimp [u, v]
    calc
      _ = a * gaussianQuantileTransport (ν' : Measure ℝ) x +
          b * gaussianQuantileTransport (ν' : Measure ℝ) y + (a + b) * ε := by ring
      _ = _ := by rw [hab, one_mul]
  exact hbound.trans_eq heq

/-- Weak closure of Ehrhard-type laws: the class of Ehrhard-type laws is closed under weak
probability-measure limits. -/
theorem isEhrhardType_of_tendsto
    (ν : ℕ → ProbabilityMeasure ℝ) (ν' : ProbabilityMeasure ℝ)
    (hlim : Tendsto ν atTop (nhds ν')) (hν : ∀ k, IsEhrhardType (ν k : Measure ℝ)) :
    IsEhrhardType (ν' : Measure ℝ) := by
  rw [← map_gaussianQuantileTransport (ν' : Measure ℝ)]
  exact isEhrhardType_map_of_monotone_convex (monotone_gaussianQuantileTransport _)
    (convexOn_gaussianQuantileTransport_of_tendsto hlim hν)

end EhrhardGaussian.EhrhardType

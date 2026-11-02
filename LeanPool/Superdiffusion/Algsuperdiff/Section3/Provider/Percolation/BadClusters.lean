/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.BadClusterRate
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.TranslatedCrossing

/-!
# BadClusters

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `l.percolation.bad.clusters`: the density and diameter conclusions

This module feeds the site family of `SiteFamilyBridge.lean` and the per-scale
tails of `SiteFamilyTails.lean` into the abstract percolation layer, at the
gates of `BadClusterRate.lean`, and produces the two displayed conclusions of
ABK26's Lemma `l.percolation.bad.clusters`.

## The admissibility interfaces

The original public compatibility theorems carry the **amended** display
`e.percolation.admissibility.bad.clusters`:

```
E >= exp(C sigma^{-1}) ,   E >= C c_star^{-1} ,   E >= C b^{-1} ,   gamma <= E^{-5} ,
```

The standing source hypotheses `E in [1,infinity)`, `S(m-1,E)`, `sigma in
(0,1/2]`, `b in (0,1/8]` and `h in N` (with `h >= 1`, the manuscript's `N`
convention) are carried verbatim.

The corresponding declarations suffixed `_of_gates` expose instead the four
raw consequences actually used by the single-cube probability estimates:
`4 <= E`, `unitGate M`, `gamma <= 1/20`, and `E⁻² <= cstar`.  This separates
the probabilistic proof from the stronger packaged premise and lets the frozen
maximum gate discharge the exact consequences directly.

## The density conclusion

`e.density.bound.bad.clusters`:

```
P[ avsum_{z in 3^{m-h} Z^d cap cu_m} 1_{B^*(z + cu_{m-h})}
     > exp(-c E^{-2} gamma^{-1}) + 3^{-h/2} ]  <=  exp(-3^{h/2}) .
```

Proved locally as `measureReal_badExtendedDensity_gt_le_exp_of_gates`, with the
explicit dimension-only `c(d) = siteRateBase d / 2`.  The threshold's first
term is supplied by the tail sum of the site family; the deviation half is
`measureReal_densityAverage_gt_le_exp`, whose range binder is verified by
`densityThreshold_of_le` at the gate `densityAmplitude_le_sqrt_siteRateSq`.
The manuscript's own `a = 3/2` forces `d >= 2` (the source lemma's own `a <
d`); this is the disclosed constraint.

## The diameter conclusion

`e.diameter.bound.bad.clusters` is the probability that some 2-cluster of
`B^*_{m-h}` has diameter at least `3^{bh} 3^{m-h}`.  What the percolation layer
supplies, and what is proved here, is the probabilistic content of that
display: the union over the base lattice `3^{m-h} Z^d cap cu_m` of the crossing
events of `e.diameter.bound` at the scale `k = ceil(b h)` has probability at
most `exp(-3^{(1-sigma) b h})` (`measureReal_badClusterCrossingEvent_le_exp`).
The entropy-versus-gain step is exactly the arithmetic, discharged by
`entropyGate_of_admissible`.

## Main results

* `measureReal_badExtendedDensity_gt_le_exp_of_gates`:
  `e.density.bound.bad.clusters` from the raw probability gates.
* `measureReal_badUnion_siteBadEvent_le_of_gates`: the union over all reindexed
  levels of the site family has probability at most
  `exp(-c(d) E^{-2} gamma^{-1})`, the first term of the density threshold.
* The names without `_of_gates` are compatibility wrappers for the prior
  amended-preliminary interface.

## References

* ABK26, `l.percolation.bad.clusters`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## Elementary numerics -/


private theorem two_le_exp_one' : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

/-- `3 ^ ((3/2) l) >= 1 + l`: the elementary comparison that turns the
doubly-exponential per-scale tail into a geometric series. -/
private theorem one_add_le_three_rpow_scale (l : ℕ) :
    1 + (l : ℝ) ≤ (3 : ℝ) ^ ((3 / 2 : ℝ) * (l : ℝ)) := by
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have h := one_add_le_three_rpow (x := (3 / 2 : ℝ) * (l : ℝ)) (by positivity)
  linarith

/-! ## The tail sum of the site family -/

/-- **The probability of the extended bad event's superset.**  The union over
all reindexed levels of the site family — the abstract layer's `B(z)` — has
probability at most `exp(-c(d) E^{-2} gamma^{-1})` with
`c(d) = siteRateBase d / 2`.  This is the first term of the threshold in
`e.density.bound.bad.clusters`. -/
theorem measureReal_badUnion_siteBadEvent_le_of_gates (M : ABKModel d) (base : ℤ)
    {m : ℤ} {E : ℝ} (hE : 1 ≤ E) (hE4 : 4 ≤ E) (hunit : unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hbase : base ≤ m - 1) (hgamma : M.gamma ≤ E ^ (-5 : ℤ))
    (hEabs : 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) ≤ badRateConst d * E ^ 3)
    (hrate : 4 ≤ siteRateSq M E) (u : Fin d → ℤ) :
    (cutoffSampleLaw M).toMeasure.real (badUnion (siteBadEvent M base) u) ≤
      Real.exp (-(siteRateSq M E / 2)) := by
  classical
  set κ : ℝ := siteRateSq M E with hκdef
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hq0 : (0 : ℝ) < Real.exp (-κ) := Real.exp_pos _
  have hqhalf : Real.exp (-κ) ≤ 1 / 2 := by
    have h1 : Real.exp 1 ≤ Real.exp κ := Real.exp_le_exp.2 (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp κ := le_trans two_le_exp_one' h1
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos κ)]
    linarith
  have hq1 : Real.exp (-κ) < 1 := by linarith
  -- the per-level geometric bound
  have hterm : ∀ l : ℕ,
      (cutoffSampleLaw M).toMeasure.real (siteBadEvent M base l u) ≤
        Real.exp (-κ) * Real.exp (-κ) ^ l := by
    intro l
    refine le_trans (measureReal_siteBadEvent_le_of_gates M base hE hE4 hunit hgamma20
      hinvSq hS hbase hgamma hEabs l u) ?_
    have hpowid : Real.exp (-κ) * Real.exp (-κ) ^ l = Real.exp (-(κ * (1 + (l : ℝ)))) := by
      induction l with
      | zero => simp
      | succ n ih =>
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
          rw [pow_succ, ← mul_assoc, ih, ← Real.exp_add, hcast]
          congr 1
          ring
    rw [hpowid]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    exact mul_le_mul_of_nonneg_left (one_add_le_three_rpow_scale l) hκ0.le
  have hsummable : Summable fun l : ℕ => Real.exp (-κ) * Real.exp (-κ) ^ l :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  have hcover : badUnion (siteBadEvent M base) u = ⋃ l : ℕ, siteBadEvent M base l u := rfl
  have hbound : (cutoffSampleLaw M).toMeasure (badUnion (siteBadEvent M base) u) ≤
      ENNReal.ofReal (∑' l : ℕ, Real.exp (-κ) * Real.exp (-κ) ^ l) := by
    rw [hcover, ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) hsummable]
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun l => ?_)
    have hfin : (cutoffSampleLaw M).toMeasure (siteBadEvent M base l u) ≠ ⊤ :=
      measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hterm l)
  have hsum : ∑' l : ℕ, Real.exp (-κ) * Real.exp (-κ) ^ l =
      Real.exp (-κ) * (1 - Real.exp (-κ))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
  have hgeom : Real.exp (-κ) * (1 - Real.exp (-κ))⁻¹ ≤ 2 * Real.exp (-κ) := by
    have hden : (0 : ℝ) < 1 - Real.exp (-κ) := by linarith
    rw [mul_inv_le_iff₀ hden]
    nlinarith [hq0, hqhalf]
  have hhalf : 2 * Real.exp (-κ) ≤ Real.exp (-(κ / 2)) := by
    have hexp2 : (2 : ℝ) ≤ Real.exp (κ / 2) := by
      have h1 : Real.exp 1 ≤ Real.exp (κ / 2) := Real.exp_le_exp.2 (by linarith)
      exact le_trans two_le_exp_one' h1
    have hsplit : Real.exp (-κ) = Real.exp (-(κ / 2)) * Real.exp (-(κ / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcancel : Real.exp (κ / 2) * Real.exp (-(κ / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc 2 * Real.exp (-κ) = 2 * Real.exp (-(κ / 2)) * Real.exp (-(κ / 2)) := by
          rw [hsplit]; ring
      _ ≤ Real.exp (κ / 2) * Real.exp (-(κ / 2)) * Real.exp (-(κ / 2)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hexp2 (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = Real.exp (-(κ / 2)) := by rw [hcancel, one_mul]
  calc (cutoffSampleLaw M).toMeasure.real (badUnion (siteBadEvent M base) u)
      = ((cutoffSampleLaw M).toMeasure (badUnion (siteBadEvent M base) u)).toReal := rfl
    _ ≤ (ENNReal.ofReal (∑' l : ℕ, Real.exp (-κ) * Real.exp (-κ) ^ l)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ∑' l : ℕ, Real.exp (-κ) * Real.exp (-κ) ^ l :=
        ENNReal.toReal_ofReal (tsum_nonneg fun l => by positivity)
    _ ≤ Real.exp (-(κ / 2)) := by rw [hsum]; linarith [hgeom, hhalf]


/-! ## The density statistic of `e.bad.cluster.def` -/

/-- ABK26 `e.bad.cluster.def`: the normalized count of those base cubes `z +
cu_{m-h}`, `z in 3^{m-h} Z^d cap cu_m`, for which the extended bad event `B^*(z
+ cu_{m-h})` occurs.  The lattice `3^{m-h} Z^d cap cu_m` is represented by
`cubeFinset h` through `z = 3^{m-h} u`. -/
def badExtendedDensity (M : ABKModel d) (m : ℤ) (h : ℕ) : CutoffSample d → ℝ :=
  fun omega => ((cubeFinset (d := d) h).card : ℝ)⁻¹ *
    ∑ u ∈ cubeFinset h,
      (badExtended M (siteCube (m - (h : ℤ)) u)).indicator (fun _ => (1 : ℝ)) omega

/-- The manuscript's own inclusion `B^* subseteq bigcup_L B_L`, at the level of
the density statistic: the extended-bad density is dominated by the centered
density average of the site family plus the uniform bound on the centering. -/
theorem badExtendedDensity_le_densityAverage_add (M : ABKModel d) (m : ℤ) (h : ℕ)
    {theta : ℝ}
    (hp : ∀ u : Fin d → ℤ, (cutoffSampleLaw M).toMeasure.real
      (badUnion (siteBadEvent M (m - (h : ℤ))) u) ≤ theta)
    (omega : CutoffSample d) :
    badExtendedDensity M m h omega ≤
      densityAverage (siteBadEvent M (m - (h : ℤ))) (cutoffSampleLaw M).toMeasure h
        omega + theta := by
  classical
  have hN : ((cubeFinset (d := d) h).card : ℝ) = (3 : ℝ) ^ (d * h) := by
    rw [card_cubeFinset]
    push_cast
    ring
  have hNpos : (0 : ℝ) < ((cubeFinset (d := d) h).card : ℝ) := by
    rw [hN]; positivity
  have hle : ∀ u ∈ cubeFinset (d := d) h,
      (badExtended M (siteCube (m - (h : ℤ)) u)).indicator (fun _ => (1 : ℝ)) omega ≤
        centeredUnion (siteBadEvent M (m - (h : ℤ))) (cutoffSampleLaw M).toMeasure u
          omega + theta := by
    intro u _
    have hsub : badExtended M (siteCube (m - (h : ℤ)) u) ⊆
        badUnion (siteBadEvent M (m - (h : ℤ))) u :=
      badExtended_subset_iUnion_siteBadEvent M (m - (h : ℤ)) u
    have hcu : centeredUnion (siteBadEvent M (m - (h : ℤ)))
          (cutoffSampleLaw M).toMeasure u omega =
        (badUnion (siteBadEvent M (m - (h : ℤ))) u).indicator (fun _ => (1 : ℝ)) omega -
          (cutoffSampleLaw M).toMeasure.real
            (badUnion (siteBadEvent M (m - (h : ℤ))) u) := rfl
    rw [hcu]
    by_cases hmem : omega ∈ badExtended M (siteCube (m - (h : ℤ)) u)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hsub hmem)]
      linarith [hp u]
    · rw [Set.indicator_of_notMem hmem]
      have hind : (0 : ℝ) ≤
          (badUnion (siteBadEvent M (m - (h : ℤ))) u).indicator (fun _ => (1 : ℝ)) omega :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) omega
      linarith [hp u]
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hstep := mul_le_mul_of_nonneg_left hsum
    (le_of_lt (inv_pos.2 hNpos))
  have hid : ((cubeFinset (d := d) h).card : ℝ)⁻¹ *
      (∑ u ∈ cubeFinset (d := d) h,
          centeredUnion (siteBadEvent M (m - (h : ℤ))) (cutoffSampleLaw M).toMeasure u
            omega + ((cubeFinset (d := d) h).card : ℝ) * theta) =
      densityAverage (siteBadEvent M (m - (h : ℤ))) (cutoffSampleLaw M).toMeasure h
        omega + theta := by
    rw [densityAverage]
    field_simp
  rw [badExtendedDensity]
  rw [hid] at hstep
  exact hstep

/-! ## The density conclusion -/

/-- **ABK26 `e.density.bound.bad.clusters`**, at the explicit dimension-only
constant `c(d) = siteRateBase d / 2` and from the raw single-cube probability
gates.

```
P[ avsum_{z} 1_{B^*(z + cu_{m-h})} > exp(-c E^{-2} gamma^{-1}) + 3^{-h/2} ]
  <= exp(-3^{h/2}) .
```

The range binder of `measureReal_densityAverage_gt_le_exp` is verified inside,
at the manuscript's own `a = 3/2`; the source lemma's own constraint `a < d`
forces the disclosed `d >= 2`. -/
theorem measureReal_badExtendedDensity_gt_le_exp_of_gates (M : ABKModel d) {m : ℤ}
    (h : ℕ)
    {E sigma b : ℝ} (hd : 2 ≤ d) (hh : 1 ≤ h) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    (cutoffSampleLaw M).toMeasure.real
        {omega | Real.exp (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) +
            (3 : ℝ) ^ (-(h : ℝ) / 2) < badExtendedDensity M m h omega} ≤
      Real.exp (-((3 : ℝ) ^ ((h : ℝ) / 2))) := by
  classical
  have hb1' : b ≤ 1 := by linarith
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hEabs := treeCountGate_of_admissible hd hsigma0 hsigma hb0 hb1' hEexp hEb
  have hrate := four_le_siteRateSq M hd hsigma0 hsigma hb0 hb1' hEexp hEb hgamma
  have hbase : m - (h : ℤ) ≤ m - 1 := by
    have : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
    omega
  set T : ℝ := Real.sqrt (siteRateSq M E) with hTdef
  have hSnn : (0 : ℝ) ≤ siteRateSq M E := by linarith
  have hTsq : T ^ 2 = siteRateSq M E := Real.sq_sqrt hSnn
  have hT1 : 1 ≤ T := by
    nlinarith [Real.sqrt_nonneg (siteRateSq M E), hTsq]
  -- the tail hypothesis
  have htail : ∀ (l : ℕ) (y : Fin d → ℤ),
      (cutoffSampleLaw M).toMeasure.real (siteBadEvent M (m - (h : ℤ)) l y) ≤
        Real.exp (-(T ^ 2 * (3 : ℝ) ^ ((3 / 2 : ℝ) * (l : ℝ)))) := by
    intro l y
    rw [hTsq]
    exact measureReal_siteBadEvent_le_of_gates M (m - (h : ℤ)) hE hE4 hunit
      hgamma20 hinvSq hS hbase hgamma hEabs l y
  have hK : densityAmplitude d ≤ T :=
    densityAmplitude_le_sqrt_siteRateSq M hd hsigma0 hsigma hb0 hb1' hEexp hEb hgamma
  have hrange := densityThreshold_of_le (T := T) h hd hK
  have hdens := measureReal_densityAverage_gt_le_exp
    (μ := (cutoffSampleLaw M).toMeasure) (B := siteBadEvent M (m - (h : ℤ)))
    (a := (3 : ℝ) / 2) (T := T) (t := (3 : ℝ) ^ (-(h : ℝ) / 2)) (m := h)
    (measurableSet_siteBadEvent M (m - (h : ℤ)))
    (indep_siteSigma_siteBadEvent M (m - (h : ℤ))) htail (by norm_num)
    (by linarith) hT1 hrange
  -- the exponent dominates `3^{h/2}`
  have hTA : densityExponentAmplitude d ≤ T ^ 2 := by
    rw [hTsq]
    exact densityExponentAmplitude_le_siteRateSq M hd hsigma0 hsigma hb0 hb1' hEexp hEb hgamma
  have hM := one_le_densityExponent hd hTA
  have hts : ((3 : ℝ) ^ (-(h : ℝ) / 2)) ^ 2 = (3 : ℝ) ^ (-(h : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(h : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hprod : (3 : ℝ) ^ (-(h : ℝ)) * (3 : ℝ) ^ ((3 : ℝ) / 2 * (h : ℝ)) =
      (3 : ℝ) ^ ((h : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hYpos : (0 : ℝ) < (3 : ℝ) ^ ((h : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hexp : (3 : ℝ) ^ ((h : ℝ) / 2) ≤
      densityBoundExpConst d * ((3 : ℝ) ^ (-(h : ℝ) / 2)) ^ 2 * ((3 : ℝ) / 2) ^ 2 *
        ((d : ℝ) - (3 : ℝ) / 2) ^ 2 * T ^ 2 * (3 : ℝ) ^ ((3 : ℝ) / 2 * (h : ℝ)) := by
    calc (3 : ℝ) ^ ((h : ℝ) / 2) = 1 * (3 : ℝ) ^ ((h : ℝ) / 2) := (one_mul _).symm
      _ ≤ densityBoundExpConst d * ((3 : ℝ) / 2) ^ 2 * ((d : ℝ) - 3 / 2) ^ 2 * T ^ 2 *
            (3 : ℝ) ^ ((h : ℝ) / 2) := mul_le_mul_of_nonneg_right hM hYpos.le
      _ = densityBoundExpConst d * ((3 : ℝ) ^ (-(h : ℝ) / 2)) ^ 2 * ((3 : ℝ) / 2) ^ 2 *
            ((d : ℝ) - (3 : ℝ) / 2) ^ 2 * T ^ 2 *
            (3 : ℝ) ^ ((3 : ℝ) / 2 * (h : ℝ)) := by
          rw [hts, ← hprod]
          ring
  have hdens' := le_trans hdens (Real.exp_le_exp.2 (neg_le_neg hexp))
  -- the inclusion of events
  have hp : ∀ u : Fin d → ℤ, (cutoffSampleLaw M).toMeasure.real
      (badUnion (siteBadEvent M (m - (h : ℤ))) u) ≤
        Real.exp (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
    intro u
    refine le_trans (measureReal_badUnion_siteBadEvent_le_of_gates M (m - (h : ℤ))
      hE hE4 hunit hgamma20 hinvSq hS hbase hgamma hEabs hrate u) (le_of_eq ?_)
    congr 1
    rw [siteRateSq]
    ring
  have hsubset : {omega : CutoffSample d |
        Real.exp (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) +
          (3 : ℝ) ^ (-(h : ℝ) / 2) < badExtendedDensity M m h omega} ⊆
      {omega : CutoffSample d | (3 : ℝ) ^ (-(h : ℝ) / 2) <
        densityAverage (siteBadEvent M (m - (h : ℤ))) (cutoffSampleLaw M).toMeasure h
          omega} := by
    intro omega homega
    have hdom := badExtendedDensity_le_densityAverage_add M m h hp omega
    simp only [Set.mem_ofPred_eq] at homega ⊢
    linarith
  exact le_trans (measureReal_mono hsubset (measure_ne_top _ _)) hdens'


/-! ## The diameter conclusion -/


end

end Algsuperdiff.Section3.Provider.Percolation

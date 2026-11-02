/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.ClusterTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.BadClusters

/-!
# BadClusterDiameter

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.diameter.bound.bad.clusters`: the diameter conclusion at the ruled adjacency

```
P[ max_{z in 3^{m-h} Z^d cap cu_m} diam( B^*_{m-h}(z;2) ) >= 3^{bh} 3^{m-h} ]
  <= exp( - 3^{(1-sigma) b h} ) .
```

The three ingredients are

* the distance-two abstract percolation layer of `LatticeTwo`,
  `ClusterEventTwo`, `DiameterTwo` (the ruled re-run of the diameter induction,
  at the *same* gate constant `16 d exp(40 (1-b)^{-1}) <= T^2 b` as the proved
  distance-one layer);
* the 2-cluster definitions and the deterministic step of `ClusterTwo`;
* the proved site family, its tails and its finite-range independence
  (`SiteFamily`, `SiteFamilyTails`, `SiteFamilyBridge`) and the gate arithmetic
  of `BadClusterRate`.

## Units

Everything is in *cube-side units*: the base lattice `3^{m-h} Z^d cap cu_m` is
the `Finset` `cubeFinset h` through `z = 3^{m-h} u`, and `badClusterDiam` is the
sup-metric diameter of the union of the closed base cubes of the 2-cluster,
divided by the cube side `3^{m-h}`.  The printed threshold `3^{bh} 3^{m-h}`
becomes `3^{bh}`.

## The scale of the crossing, and the constant that pays for it

The source says the diameter bound "follows from `e.diameter.bound`
(rescaled)".  That step is a gloss: a cluster of diameter `D` produces a
crossing of the annulus `cu_{k+1} \ cu_k` only when `3^{k+1} <= 2 D`, so the
crossing scale `k` must sit strictly *below* `b h`, whereas the gain of
`e.diameter.bound` at scale `k` is `3^{(1-sigma) k}` and the target is
`3^{(1-sigma) b h}`.  Here `k` is taken to be `ceil(b h) - 2`, which loses a
factor at most `9` in the gain; the loss is paid for out of the admissibility
display, not by weakening the conclusion: `entropyGate₂_of_admissible` extracts
`(3 + 18 d) / b <= exp(-40/sigma) T^2 / 2` from the *same* amended display
`e.percolation.admissibility.bad.clusters` (`E >= C b^{-1}`) at the *same*
dimension-only `badClustersConst d`, where the proved
`entropyGate_of_admissible` extracts only `1 + 2 d / b`.  No constant of the
node moves, and no hypothesis is added.

For `b h <= 1` the crossing route is unavailable (a cluster of diameter `< 3`
crosses no annulus) and the bound is obtained instead by the plain union bound
over the `3^{dh}` base sites, which in that regime (`h <= b^{-1}`) is dominated
by the same gate.

## Main definitions

* `badSiteFinset`, `badCluster₂`, `badClusterDiam`: the random site set
  `B^*_{m-h}` of `e.bad.cluster.def`, its 2-clusters `B^*_{m-h}(z;2)` and their
  diameter in cube-side units.
* `badClusterCrossingEvent₂`: the union over the base lattice of the
  distance-two crossing events at a given scale.

## Main results

* `entropyGate₂_of_admissible`: the sharpened entropy gate.
* `measureReal_badClusterCrossingEvent₂_le_exp_of_gates`: the crossing-union
  bound at any scale `k` whose gain is within a factor `9` of the target, from
  the exact raw probability gates.
* `measureReal_maxBadClusterDiam_le_exp_of_gates`:
  `e.diameter.bound.bad.clusters` from those gates.
* The names without `_of_gates` are compatibility wrappers for the packaged
  preliminary admissibility.

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

/-! ## The sharpened entropy gate -/

/-- The proved `entropyGate_of_admissible` extracts `2 (1 + 2 d) e^{40/sigma}
b^{-1}` from the same display; the extra room is what pays for the bounded
scale loss in the cluster-to-crossing step. -/
theorem entropyGate₂_of_admissible (M : ABKModel d) {E sigma b : ℝ} (hd : 2 ≤ d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    (6 + 36 * (d : ℝ)) * Real.exp (40 / sigma) / b ≤ siteRateSq M E := by
  have hS : 0 < siteRateBase d := siteRateBase_pos d
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hnum : (0 : ℝ) < 6 + 36 * (d : ℝ) := by linarith only [hd0]
  have hSinv : (0 : ℝ) < (siteRateBase d)⁻¹ := inv_pos.2 hS
  have hA0 : (0 : ℝ) < (6 + 36 * (d : ℝ)) / siteRateBase d := div_pos hnum hS
  have hAle : (6 + 36 * (d : ℝ)) / siteRateBase d ≤ badClustersAmplitude d := by
    have hbr : (6 + 36 * (d : ℝ)) ≤
        4 + 32 * (d : ℝ) + 2 * (1 + 2 * (d : ℝ)) + densityAmplitude d ^ 2 +
          densityExponentAmplitude d := by
      have h3 : (0 : ℝ) ≤ densityAmplitude d ^ 2 := sq_nonneg _
      have h4 := densityExponentAmplitude_pos hd
      linarith only [h3, h4]
    have hstep : (6 + 36 * (d : ℝ)) * (siteRateBase d)⁻¹ ≤
        (4 + 32 * (d : ℝ) + 2 * (1 + 2 * (d : ℝ)) + densityAmplitude d ^ 2 +
          densityExponentAmplitude d) * (siteRateBase d)⁻¹ :=
      mul_le_mul_of_nonneg_right hbr hSinv.le
    have htree : (0 : ℝ) ≤
        2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) / badRateConst d := by
      have hk := badRateConst_pos d
      have hl20 : (0 : ℝ) ≤ Real.log 20 := Real.log_nonneg (by norm_num)
      have hl3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have hnum2 : (0 : ℝ) ≤ 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) := by
        linarith only [hl20, mul_nonneg hd0 hl3]
      exact div_nonneg hnum2 hk.le
    have hamp : badClustersAmplitude d =
        2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) / badRateConst d +
          (4 + 32 * (d : ℝ) + 2 * (1 + 2 * (d : ℝ)) + densityAmplitude d ^ 2 +
            densityExponentAmplitude d) / siteRateBase d := rfl
    rw [hamp, div_eq_mul_inv, div_eq_mul_inv (4 + 32 * (d : ℝ) + 2 * (1 + 2 * (d : ℝ)) +
      densityAmplitude d ^ 2 + densityExponentAmplitude d)]
    linarith only [hstep, htree]
  have hcube := le_cube_of_admissible hA0 hAle hsigma0 hsigma hb0 hE hEb
  have hbase := siteRateBase_mul_cube_le M (one_le_of_admissible hsigma0 hE) hgamma
  have hmul := mul_le_mul_of_nonneg_left hcube hS.le
  have heq : siteRateBase d *
      ((6 + 36 * (d : ℝ)) / siteRateBase d * Real.exp (40 / sigma) / b) =
      (6 + 36 * (d : ℝ)) * Real.exp (40 / sigma) / b := by
    field_simp
  rw [heq] at hmul
  linarith only [hmul, hbase]

/-- The gate in the form consumed by the union bound: the gain constant
`G = e^{-40/sigma} T^2 / 2` dominates `(3 + 18 d) b^{-1}`. -/
theorem gainGate₂_of_admissible (M : ABKModel d) {E sigma b : ℝ} (hd : 2 ≤ d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hE : Real.exp (badClustersConst d / sigma) ≤ E)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    (3 + 18 * (d : ℝ)) / b ≤ Real.exp (-(40 / sigma)) * siteRateSq M E / 2 := by
  have hgate := entropyGate₂_of_admissible M hd hsigma0 hsigma hb0 hE hEb hgamma
  set u : ℝ := Real.exp (40 / sigma) with hudef
  have hu : (0 : ℝ) < u := Real.exp_pos _
  have hstep : u⁻¹ * ((6 + 36 * (d : ℝ)) * u / b) ≤ u⁻¹ * siteRateSq M E :=
    mul_le_mul_of_nonneg_left hgate (le_of_lt (inv_pos.2 hu))
  have hid : u⁻¹ * ((6 + 36 * (d : ℝ)) * u / b) = (6 + 36 * (d : ℝ)) / b := by
    field_simp
  rw [hid] at hstep
  have hsplit : (6 + 36 * (d : ℝ)) / b = 2 * ((3 + 18 * (d : ℝ)) / b) := by
    simp only [div_eq_mul_inv]
    ring
  rw [Real.exp_neg, ← hudef]
  rw [hsplit] at hstep
  linarith only [hstep]

/-! ## The entropy of the base lattice -/

/-- The site entropy `d h log 3` of the base lattice is dominated by
`2 d b^{-1} 3^{(1-sigma) b h}`, uniformly in `h`. -/
private theorem entropy_le_gain₂ {b sigma : ℝ} (d h : ℕ) (hsigma : sigma ≤ 1 / 2)
    (hb0 : 0 < b) :
    (d : ℝ) * (h : ℝ) * Real.log 3 ≤
      2 * (d : ℝ) / b * (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := lt_of_lt_of_le zero_lt_one one_le_log_three
  have hs : (1 : ℝ) / 2 ≤ 1 - sigma := by linarith only [hsigma]
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hY : (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) =
      Real.exp (Real.log 3 * ((1 - sigma) * b * (h : ℝ))) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hkey : (h : ℝ) * (Real.log 3 * ((1 - sigma) * b)) ≤
      (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) := by
    rw [hY]
    have hexp := Real.add_one_le_exp (Real.log 3 * ((1 - sigma) * b * (h : ℝ)))
    linarith only [hexp]
  have hmul : (d : ℝ) * (h : ℝ) * Real.log 3 * b ≤
      2 * (d : ℝ) * (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) := by
    have hX0 : (0 : ℝ) ≤ (d : ℝ) * (h : ℝ) * Real.log 3 * b :=
      mul_nonneg (mul_nonneg (mul_nonneg hd0 hh0) hlog3.le) hb0.le
    have hXs : (0 : ℝ) ≤ (1 / 2 - sigma) * ((d : ℝ) * (h : ℝ) * Real.log 3 * b) :=
      mul_nonneg (by linarith only [hs]) hX0
    linarith only [mul_le_mul_of_nonneg_left hkey
      (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)), hXs]
  rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
  linarith only [hmul]

/-- The final scalar step of the union bound: the entropy `2 q Y` is beaten by
the gain `G Y / 9` as soon as `G ≥ 9 + 18 q`. -/
private theorem final_exponent_bound {q Y G : ℝ} (hY : 0 < Y)
    (hG : 9 + 18 * q ≤ G) : 2 * q * Y - G * Y / 9 ≤ -Y := by
  linarith only [mul_le_mul_of_nonneg_right hG hY.le]

/-! ## The random site set and its 2-clusters -/

/-- ABK26 `e.bad.cluster.def`: the random set `B^*_{m-h} = { z + cu_{m-h}: z in
3^{m-h} Z^d cap cu_m, B^*(z + cu_{m-h}) occurs }`, in cube-side units `z =
3^{m-h} u`. -/
def badSiteFinset (M : ABKModel d) (m : ℤ) (h : ℕ) (omega : CutoffSample d) :
    Finset (Fin d → ℤ) :=
  @Finset.filter _ (fun u => omega ∈ badExtended M (siteCube (m - (h : ℤ)) u))
    (Classical.decPred _) (cubeFinset h)

theorem mem_badSiteFinset_iff {M : ABKModel d} {m : ℤ} {h : ℕ} {omega : CutoffSample d}
    {u : Fin d → ℤ} :
    u ∈ badSiteFinset M m h omega ↔
      u ∈ cubeFinset (d := d) h ∧ omega ∈ badExtended M (siteCube (m - (h : ℤ)) u) := by
  let : DecidablePred
      (fun u : Fin d → ℤ => omega ∈ badExtended M (siteCube (m - (h : ℤ)) u)) :=
    Classical.decPred _
  unfold badSiteFinset
  rw [Finset.mem_filter]

theorem badSiteFinset_subset (M : ABKModel d) (m : ℤ) (h : ℕ) (omega : CutoffSample d) :
    badSiteFinset M m h omega ⊆ cubeFinset (d := d) h :=
  fun _ hu => (mem_badSiteFinset_iff.mp hu).1

/-- ABK26 `e.bad.cluster.def`: the 2-connected component `B^*_{m-h}(z;2)` of the
bad base cubes containing `z + cu_{m-h}` if `B^*(z + cu_{m-h})` occurs, and the
empty set otherwise (the latter is `cluster₂_eq_empty_of_notMem`). -/
def badCluster₂ (M : ABKModel d) (m : ℤ) (h : ℕ) (omega : CutoffSample d)
    (u : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  cluster₂ (badSiteFinset M m h omega) u

/-- `diam(B^*_{m-h}(z;2))` in units of the cube side `3^{m-h}`: the sup-metric
diameter of the union of the closed base cubes of the 2-cluster. -/
def badClusterDiam (M : ABKModel d) (m : ℤ) (h : ℕ) (omega : CutoffSample d)
    (u : Fin d → ℤ) : ℕ :=
  closedLatDiam (badCluster₂ M m h omega u)

/-! ## The crossing-union bound at a general scale -/

/-- The union over the base lattice `3^{m-h} Z^d cap cu_m` of the *distance-two*
crossing events of `e.diameter.bound` at scale `k`. -/
def badClusterCrossingEvent₂ (M : ABKModel d) (m : ℤ) (h k : ℕ) :
    Set (CutoffSample d) :=
  ⋃ w ∈ cubeFinset (d := d) h, crossingEvent₂At (siteBadEvent M (m - (h : ℤ))) k w

/-- **The crossing-union bound for distance-two crossings.**

At any scale `k` whose gain `3^{(1-sigma) k}` is within a factor `9` of the
target `3^{(1-sigma) b h}`, the probability that some base site starts a
distance-two crossing of its own annulus at scale `k` is at most
`exp(-3^{(1-sigma) b h})`, uniformly in `h`. -/
theorem measureReal_badClusterCrossingEvent₂_le_exp_of_gates (M : ABKModel d) {m : ℤ}
    (h : ℕ)
    {E sigma b : ℝ} (hd : 2 ≤ d) (hh : 1 ≤ h) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) (k : ℕ)
    (hk : (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) ≤ 9 * (3 : ℝ) ^ ((1 - sigma) * (k : ℝ))) :
    (cutoffSampleLaw M).toMeasure.real (badClusterCrossingEvent₂ M m h k) ≤
      Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)))) := by
  classical
  have hb1' : b ≤ 1 := by linarith only [hb1]
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hEabs := treeCountGate_of_admissible hd hsigma0 hsigma hb0 hb1' hEexp hEb
  have hrate := four_le_siteRateSq M hd hsigma0 hsigma hb0 hb1' hEexp hEb hgamma
  have hbase : m - (h : ℤ) ≤ m - 1 := by
    have : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
    omega
  set T : ℝ := Real.sqrt (siteRateSq M E) with hTdef
  have hSnn : (0 : ℝ) ≤ siteRateSq M E := by linarith only [hrate]
  have hTsq : T ^ 2 = siteRateSq M E := Real.sq_sqrt hSnn
  have hgate : 16 * (d : ℝ) * Real.exp (40 / (1 - (1 - sigma))) ≤ T ^ 2 * (1 - sigma) := by
    rw [hTsq]
    exact percolationGate_of_admissible' M hd hsigma0 hsigma hb0 hb1' hEexp hEb hgamma
  have hB : ∀ (L : ℕ) (w : Fin d → ℤ),
      (cutoffSampleLaw M).toMeasure (siteBadEvent M (m - (h : ℤ)) L w) ≤
        ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ ((3 / 2 : ℝ) * (L : ℝ))))) := by
    intro L w
    have hreal : (cutoffSampleLaw M).toMeasure.real (siteBadEvent M (m - (h : ℤ)) L w) ≤
        Real.exp (-(T ^ 2 * (3 : ℝ) ^ ((3 / 2 : ℝ) * (L : ℝ)))) := by
      rw [hTsq]
      exact measureReal_siteBadEvent_le_of_gates M (m - (h : ℤ)) hE hE4 hunit
        hgamma20 hinvSq hS hbase hgamma hEabs L w
    have hfin : (cutoffSampleLaw M).toMeasure (siteBadEvent M (m - (h : ℤ)) L w) ≠ ⊤ :=
      measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hreal
  have hcross : ∀ w : Fin d → ℤ,
      (cutoffSampleLaw M).toMeasure.real
          (crossingEvent₂At (siteBadEvent M (m - (h : ℤ))) k w) ≤
        Real.exp (-(Real.exp (-(40 / sigma)) * T ^ 2 *
          (3 : ℝ) ^ ((1 - sigma) * (k : ℝ)) / 2)) := by
    intro w
    have hbnd := measure_crossingEvent₂At_le_exp (μ := (cutoffSampleLaw M).toMeasure)
      (B := siteBadEvent M (m - (h : ℤ))) (a := (3 : ℝ) / 2) (b := 1 - sigma) (T := T)
      hd1 (by linarith only [hsigma]) (by linarith only [hsigma0])
      (by linarith only [hsigma0]) hgate
      (indep_siteSigma_siteBadEvent M (m - (h : ℤ))) hB k w
    have hone : (1 : ℝ) - (1 - sigma) = sigma := by ring
    rw [hone] at hbnd
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hunion : (cutoffSampleLaw M).toMeasure.real
      (badClusterCrossingEvent₂ M m h k) ≤
      ((cubeFinset (d := d) h).card : ℝ) *
        Real.exp (-(Real.exp (-(40 / sigma)) * T ^ 2 *
          (3 : ℝ) ^ ((1 - sigma) * (k : ℝ)) / 2)) := by
    rw [badClusterCrossingEvent₂]
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun w _ => hcross w) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hunion ?_
  set Y : ℝ := (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) with hYdef
  set Z : ℝ := (3 : ℝ) ^ ((1 - sigma) * (k : ℝ)) with hZdef
  set G : ℝ := Real.exp (-(40 / sigma)) * T ^ 2 / 2 with hGdef
  have hYpos : (0 : ℝ) < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hG : (3 + 18 * (d : ℝ)) / b ≤ G := by
    rw [hGdef, hTsq]
    exact gainGate₂_of_admissible M hd hsigma0 hsigma hb0 hEexp hEb hgamma
  have hbinv : (8 : ℝ) ≤ b⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hb0]
    linarith only [hb1]
  have hid : (3 + 18 * (d : ℝ)) / b = 3 * b⁻¹ + 18 * ((d : ℝ) / b) := by
    simp only [div_eq_mul_inv]
    ring
  have hGbig : 9 + 18 * ((d : ℝ) / b) ≤ G := by
    rw [hid] at hG
    linarith only [hG, hbinv]
  have hentropy0 := entropy_le_gain₂ (b := b) (sigma := sigma) d h hsigma hb0
  have hentropy : (d : ℝ) * (h : ℝ) * Real.log 3 ≤ 2 * ((d : ℝ) / b) * Y := by
    rw [hYdef]
    rw [mul_div_assoc] at hentropy0
    exact hentropy0
  have hN : ((cubeFinset (d := d) h).card : ℝ) = (3 : ℝ) ^ (d * h) := by
    rw [card_cubeFinset]
    push_cast
    ring
  have hcardle : ((cubeFinset (d := d) h).card : ℝ) ≤ Real.exp (2 * ((d : ℝ) / b) * Y) := by
    rw [hN]
    have hlogcard : Real.log ((3 : ℝ) ^ (d * h)) = (d : ℝ) * (h : ℝ) * Real.log 3 := by
      rw [Real.log_pow]
      push_cast
      ring
    calc (3 : ℝ) ^ (d * h) = Real.exp (Real.log ((3 : ℝ) ^ (d * h))) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (2 * ((d : ℝ) / b) * Y) := by
          refine Real.exp_le_exp.2 ?_
          rw [hlogcard]
          exact hentropy
  have hgainle : Real.exp (-(Real.exp (-(40 / sigma)) * T ^ 2 * Z / 2)) ≤
      Real.exp (-(G * Y / 9)) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hGZ : Real.exp (-(40 / sigma)) * T ^ 2 * Z / 2 = G * Z := by rw [hGdef]; ring
    rw [hGZ]
    have hG0 : (0 : ℝ) < G := by
      have hbd : (0 : ℝ) ≤ 18 * ((d : ℝ) / b) := by positivity
      linarith only [hGbig, hbd]
    have hYZ : Y / 9 ≤ Z := by linarith only [hk]
    have hGYZ := mul_le_mul_of_nonneg_left hYZ hG0.le
    linarith only [hGYZ]
  calc ((cubeFinset (d := d) h).card : ℝ) *
        Real.exp (-(Real.exp (-(40 / sigma)) * T ^ 2 * Z / 2))
      ≤ Real.exp (2 * ((d : ℝ) / b) * Y) * Real.exp (-(G * Y / 9)) :=
        mul_le_mul hcardle hgainle (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * ((d : ℝ) / b) * Y - G * Y / 9) := by rw [← Real.exp_add]; congr 1
    _ ≤ Real.exp (-Y) :=
        Real.exp_le_exp.2 (final_exponent_bound hYpos hGbig)


/-! ## The diameter conclusion -/

private theorem largeBadCluster_event_subset_pathCover :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} (h : ℕ) {b : ℝ},
      (1 : ℝ) < b * (↑h : ℝ) →
        ∀ (k : ℕ),
          (↑k : ℝ) + (1 : ℝ) ≤ b * (↑h : ℝ) →
            {omega : CutoffSample d |
                ∃ u ∈ cubeFinset h, (3 : ℝ) ^ (b * (↑h : ℝ)) ≤ (↑(badClusterDiam M m h omega u) :
                  ℝ)} ⊆
              badClusterCrossingEvent₂ M m h k := by
  intro d M m h b hcase k hk1
  rintro omega ⟨u, -, hu⟩
  have hthree : (3 : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)) := by
    have h1 : (3 : ℝ) ^ (1 : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hcase
    rwa [Real.rpow_one] at h1
  have hne : (badCluster₂ M m h omega u).Nonempty := by
    by_contra hcon
    have hz : badClusterDiam M m h omega u = 0 := by
      unfold badClusterDiam closedLatDiam
      rw [ite_eq_right hcon]
    rw [hz, Nat.cast_zero] at hu
    linarith only [hu, hthree]
  have hdiam : badClusterDiam M m h omega u = latDiam (badCluster₂ M m h omega u) + 1 :=
    closedLatDiam_eq_of_nonempty hne
  rw [hdiam] at hu
  push_cast at hu
  have hlat1 : (1 : ℝ) ≤ (latDiam (badCluster₂ M m h omega u) : ℝ) := by
    linarith only [hu, hthree]
  -- `3 ^ (k+1) ≤ 2 * latDiam` in `ℕ`
  have hkey : (3 : ℕ) ^ (k + 1) ≤ 2 * latDiam (badCluster₂ M m h omega u) := by
    have hR : ((3 ^ (k + 1) : ℕ) : ℝ) ≤ ((2 * latDiam (badCluster₂ M m h omega u) : ℕ) : ℝ) :=
      by
      push_cast
      have hpow : (3 : ℝ) ^ (k + 1 : ℕ) = (3 : ℝ) ^ (((k : ℝ) + 1)) := by
        rw [← Real.rpow_natCast (3 : ℝ) (k + 1), Nat.cast_add, Nat.cast_one]
      rw [hpow]
      calc (3 : ℝ) ^ ((k : ℝ) + 1) ≤ (3 : ℝ) ^ (b * (h : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hk1
        _ ≤ (latDiam (badCluster₂ M m h omega u) : ℝ) + 1 := hu
        _ ≤ 2 * (latDiam (badCluster₂ M m h omega u) : ℝ) := by linarith only [hlat1]
    exact_mod_cast hR
  have hbadsites : ∀ y ∈ badSiteFinset M m h omega,
      omega ∈ ⋃ L : ℕ, siteBadEvent M (m - (h : ℤ)) L y := by
    intro y hy
    exact badExtended_subset_iUnion_siteBadEvent M (m - (h : ℤ)) y
      (mem_badSiteFinset_iff.mp hy).2
  obtain ⟨w, hw, hcross⟩ :=
    exists_crossingEvent₂At_of_le_latDiam (B := siteBadEvent M (m - (h : ℤ)))
      (ω := omega) (S := badSiteFinset M m h omega) (u := u) (k := k) hbadsites hkey
  refine Set.mem_iUnion₂.mpr ⟨w, ?_, hcross⟩
  exact badSiteFinset_subset M m h omega (cluster₂_subset _ u hw)

/-- **ABK26 `e.diameter.bound.bad.clusters`**, at the AUTHOR-adjacency and from the
raw single-cube probability gates:

```
P[ max_{z in 3^{m-h} Z^d cap cu_m} diam( B^*_{m-h}(z;2) ) >= 3^{bh} 3^{m-h} ]
  <= exp( - 3^{(1-sigma) b h} ) ,
```

in cube-side units (`badClusterDiam` is `diam(B^*_{m-h}(z;2)) / 3^{m-h}`),
where `diam` is the sup metric and the 2-cluster is the one of
`e.bad.cluster.def` read at lattice sup distance `<= 2`.

The manuscript's own `a = 3/2` in the companion density bound forces `d >= 2`,
and `h >= 1` is ABK's `N` convention; both are carried as disclosed
binders. -/
theorem measureReal_maxBadClusterDiam_le_exp_of_gates (M : ABKModel d) {m : ℤ}
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
        {omega | ∃ u ∈ cubeFinset (d := d) h,
          (3 : ℝ) ^ (b * (h : ℝ)) ≤ (badClusterDiam M m h omega u : ℝ)} ≤
      Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)))) := by
  classical
  have hb1' : b ≤ 1 := by linarith only [hb1]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hhpos : (0 : ℝ) < (h : ℝ) := by
    have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    linarith only [h1]
  have hbh0 : (0 : ℝ) ≤ b * (h : ℝ) := mul_nonneg hb0.le hh0
  have hbhpos : (0 : ℝ) < b * (h : ℝ) := mul_pos hb0 hhpos
  have hEabs := treeCountGate_of_admissible hd hsigma0 hsigma hb0 hb1' hEexp hEb
  have hrate := four_le_siteRateSq M hd hsigma0 hsigma hb0 hb1' hEexp hEb hgamma
  have hbase : m - (h : ℤ) ≤ m - 1 := by
    have : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
    omega
  set Y : ℝ := (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) with hYdef
  have hYpos : (0 : ℝ) < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  by_cases hcase : 1 < b * (h : ℝ)
  · -- the crossing route
    have hceil2 : 2 ≤ ⌈b * (h : ℝ)⌉₊ := by
      have hlt : (1 : ℕ) < ⌈b * (h : ℝ)⌉₊ :=
        Nat.lt_ceil.mpr (by exact_mod_cast hcase)
      omega
    obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌈b * (h : ℝ)⌉₊ - 2 := ⟨_, rfl⟩
    have hk1 : ((k : ℝ) + 1) ≤ b * (h : ℝ) := by
      have hcast : (k : ℝ) = (⌈b * (h : ℝ)⌉₊ : ℝ) - 2 := by
        rw [hkdef, Nat.cast_sub hceil2]
        norm_num
      have hlt : (⌈b * (h : ℝ)⌉₊ : ℝ) < b * (h : ℝ) + 1 := Nat.ceil_lt_add_one hbh0
      rw [hcast]
      linarith only [hlt]
    have hkge : b * (h : ℝ) - 2 ≤ (k : ℝ) := by
      have hcast : (k : ℝ) = (⌈b * (h : ℝ)⌉₊ : ℝ) - 2 := by
        rw [hkdef, Nat.cast_sub hceil2]
        norm_num
      have hge : b * (h : ℝ) ≤ (⌈b * (h : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      rw [hcast]
      linarith only [hge]
    -- the gain at scale `k` is within a factor `9` of the target
    have hkgain : Y ≤ 9 * (3 : ℝ) ^ ((1 - sigma) * (k : ℝ)) := by
      have h9 : (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      have hexp : (1 - sigma) * b * (h : ℝ) ≤ 2 + (1 - sigma) * (k : ℝ) := by
        linarith only [mul_nonneg (show (0 : ℝ) ≤ 1 - sigma by linarith only [hsigma])
          (show (0 : ℝ) ≤ (k : ℝ) - (b * (h : ℝ) - 2) by linarith only [hkge]),
          hsigma0.le]
      calc Y ≤ (3 : ℝ) ^ (2 + (1 - sigma) * (k : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = (3 : ℝ) ^ (2 : ℝ) * (3 : ℝ) ^ ((1 - sigma) * (k : ℝ)) :=
            Real.rpow_add (by norm_num) _ _
        _ = 9 * (3 : ℝ) ^ ((1 - sigma) * (k : ℝ)) := by rw [← h9]
    -- the deterministic inclusion
    have hsubset := @largeBadCluster_event_subset_pathCover (d) (M) (m) (h) (b) (hcase) (k) (hk1)
    refine le_trans (measureReal_mono hsubset (measure_ne_top _ _)) ?_
    exact measureReal_badClusterCrossingEvent₂_le_exp_of_gates M h hd hh hE hS hsigma0
      hsigma hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma k hkgain
  · -- the short-cluster regime `b h ≤ 1`: the plain union bound over base sites
    push Not at hcase
    have hG := gainGate₂_of_admissible M hd hsigma0 hsigma hb0 hEexp hEb hgamma
    have hbinv : (8 : ℝ) ≤ b⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hb0]
      linarith only [hb1]
    have hexpone : (1 : ℝ) ≤ Real.exp (40 / sigma) := by
      have h0 : (0 : ℝ) ≤ 40 / sigma := by positivity
      linarith only [h0, Real.add_one_le_exp (40 / sigma)]
    have hT2nn : (0 : ℝ) ≤ siteRateSq M E := by linarith only [hrate]
    have hle1 : Real.exp (-(40 / sigma)) ≤ 1 := by
      have h0 : (0 : ℝ) ≤ 40 / sigma := by positivity
      have hmono : Real.exp (-(40 / sigma)) ≤ Real.exp 0 :=
        Real.exp_le_exp.2 (by linarith only [h0])
      rwa [Real.exp_zero] at hmono
    have hshrink : Real.exp (-(40 / sigma)) * siteRateSq M E / 2
        ≤ siteRateSq M E / 2 := by
      have h1 : Real.exp (-(40 / sigma)) * siteRateSq M E ≤ 1 * siteRateSq M E :=
        mul_le_mul_of_nonneg_right hle1 hT2nn
      rw [one_mul] at h1
      linarith only [h1]
    have hid : (3 + 18 * (d : ℝ)) / b = 3 * b⁻¹ + 18 * ((d : ℝ) / b) := by
      simp only [div_eq_mul_inv]
      ring
    have hhalf : 2 * ((d : ℝ) / b) + 3 ≤ siteRateSq M E / 2 := by
      rw [hid] at hG
      have hdb : (0 : ℝ) ≤ (d : ℝ) / b := by positivity
      linarith only [hG, hdb, hbinv, hshrink]
    have hYsmall : Y ≤ 3 := by
      have hexp : (1 - sigma) * b * (h : ℝ) ≤ 1 := by
        linarith only [hcase, mul_nonneg hsigma0.le hbh0]
      rw [hYdef]
      calc (3 : ℝ) ^ ((1 - sigma) * b * (h : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = 3 := Real.rpow_one 3
    have hent : (d : ℝ) * (h : ℝ) * Real.log 3 ≤ 2 * ((d : ℝ) / b) := by
      have hlog : Real.log 3 ≤ 2 := log_three_le_two
      have h1 : (d : ℝ) * (h : ℝ) * Real.log 3 ≤ 2 * ((d : ℝ) * (h : ℝ)) := by
        linarith only [mul_nonneg (mul_nonneg hd0 hh0)
          (by linarith only [hlog] : (0 : ℝ) ≤ 2 - Real.log 3)]
      have h2 : 2 * ((d : ℝ) * (h : ℝ)) ≤ 2 * ((d : ℝ) / b) := by
        rw [mul_div_assoc'] at *
        rw [le_div_iff₀ hb0]
        linarith only [mul_le_mul_of_nonneg_left hcase
          (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))]
      linarith only [h1, h2]
    have hsubset : {omega : CutoffSample d | ∃ u ∈ cubeFinset (d := d) h,
        (3 : ℝ) ^ (b * (h : ℝ)) ≤ (badClusterDiam M m h omega u : ℝ)} ⊆
          ⋃ u ∈ cubeFinset (d := d) h, badUnion (siteBadEvent M (m - (h : ℤ))) u := by
      rintro omega ⟨u, hu0, hu⟩
      have hone : (1 : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)) := by
        have h1 : (3 : ℝ) ^ (0 : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hbhpos
        rwa [Real.rpow_zero] at h1
      have hne : (badCluster₂ M m h omega u).Nonempty := by
        by_contra hcon
        have hz : badClusterDiam M m h omega u = 0 := by
          unfold badClusterDiam closedLatDiam
          rw [ite_eq_right hcon]
        rw [hz, Nat.cast_zero] at hu
        linarith only [hu, hone]
      have humem : u ∈ badSiteFinset M m h omega := cluster₂_nonempty_iff.mp hne
      refine Set.mem_iUnion₂.mpr ⟨u, hu0, ?_⟩
      exact badExtended_subset_iUnion_siteBadEvent M (m - (h : ℤ)) u
        (mem_badSiteFinset_iff.mp humem).2
    refine le_trans (measureReal_mono hsubset (measure_ne_top _ _)) ?_
    have hterm : ∀ u ∈ cubeFinset (d := d) h,
        (cutoffSampleLaw M).toMeasure.real (badUnion (siteBadEvent M (m - (h : ℤ))) u) ≤
          Real.exp (-(siteRateSq M E / 2)) :=
      fun u _ => measureReal_badUnion_siteBadEvent_le_of_gates M (m - (h : ℤ)) hE hE4
        hunit hgamma20 hinvSq hS hbase hgamma hEabs hrate u
    have hunion : (cutoffSampleLaw M).toMeasure.real
        (⋃ u ∈ cubeFinset (d := d) h, badUnion (siteBadEvent M (m - (h : ℤ))) u) ≤
        ((cubeFinset (d := d) h).card : ℝ) * Real.exp (-(siteRateSq M E / 2)) := by
      refine le_trans (measureReal_biUnion_finset_le _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans hunion ?_
    have hN : ((cubeFinset (d := d) h).card : ℝ) = (3 : ℝ) ^ (d * h) := by
      rw [card_cubeFinset]
      push_cast
      ring
    have hcardle : ((cubeFinset (d := d) h).card : ℝ)
        ≤ Real.exp ((d : ℝ) * (h : ℝ) * Real.log 3) := by
      rw [hN]
      have hlogcard : Real.log ((3 : ℝ) ^ (d * h)) = (d : ℝ) * (h : ℝ) * Real.log 3 := by
        rw [Real.log_pow]
        push_cast
        ring
      calc (3 : ℝ) ^ (d * h) = Real.exp (Real.log ((3 : ℝ) ^ (d * h))) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((d : ℝ) * (h : ℝ) * Real.log 3) := le_of_eq (by rw [hlogcard])
    calc ((cubeFinset (d := d) h).card : ℝ) * Real.exp (-(siteRateSq M E / 2))
        ≤ Real.exp ((d : ℝ) * (h : ℝ) * Real.log 3) * Real.exp (-(siteRateSq M E / 2)) :=
          mul_le_mul_of_nonneg_right hcardle (Real.exp_pos _).le
      _ = Real.exp ((d : ℝ) * (h : ℝ) * Real.log 3 - siteRateSq M E / 2) := by
          rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ Real.exp (-Y) := by
          refine Real.exp_le_exp.2 ?_
          linarith only [hent, hhalf, hYsmall]


end

end Algsuperdiff.Section3.Provider.Percolation

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveOscillationsCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.MinimalScaleSeparation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport

/-!
# WaveOscillations

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `p.bfA.multiscalebound`, Step 2: wave oscillations across the random separation

This module develops conditional infrastructure for the node
`p.bfA.multiscalebound`, the wave-oscillations step (ABK26, proof of Proposition
`p.bfA.multiscalebound`, Step 2): the wave contribution is decomposed over the
layers lying between the field scale `ell` and the random depth `hsep`, and
each layer is priced separately.  It does **not** realize or close the exact
source node; the divergences recorded below remain part of the current theorem
statements.

## The display, and the corrections that shape it

The manuscript's display `e.wave.influence.bound` reads

```
  c gamma^{1/2} 3^{-gamma(n-k-h_k)} ||k_L - k_{n-k-h_k}||_{L^4bar(cu_{n-k})}
     <= gamma^{1/2} hsep^{1/2} + O_{Gamma_2}(gamma^{1/2}(L-l)^{1/2} 3^{gamma(L-l)})
        + O_{Gamma_{2(1+sigma)^{-1}}}(sigma^{-1} 3^{-(d/8)k_0}) ,
```

with `l = n - k - h_k + hsep = n - k - ceil(b(1-b)^{-1}k) - k_0` deterministic.

* **** (a genuine correction).  The printed left-hand prefactor is
  `3^{-gamma(n-k-h_k)} = 3^{-gamma l} 3^{gamma hsep}`, larger than `3^{-gamma
  l}` by the unbounded random factor `3^{gamma hsep}`.  Every step of the
  display's own proof and its Step-3 consumer carry `3^{-gamma l}`.  The local
  formulation uses the corrected prefactor `gamma^{1/2} 3^{-gamma l}` and the
  increment `k_L - k_{l - hsep}`; the parameters are named `ell = l` and `lout
  = n - k` here.
* **** (a form choice).  The manuscript splits the increment and applies a
  triangle inequality in the cube-averaged norm `||.||_{L^4bar(cu_{n-k})}`.
  This repository has no such norm and needs none: the wave amplitude is
  represented by the *uniform* gauge on the observation cube, and the split is
  performed at the level of the layer decomposition `k_b - k_a = sum_{a < k <=
  b} j_k`, where the proved per-layer `Gamma_2` displays live.  Every `Gamma_2`
  factor below is therefore a **per-layer cube supremum**, not a whole
  increment norm.
* **** (a form choice).  The manuscript writes the random-index sum `sum_h
  1_{{hsep = h}} ||k_l - k_{l-h}||`.  On the layer sum this becomes `sum_i
  1_{{i < hsep}} ||j_{l-i}||`, identical bookkeeping for nonnegative per-layer
  quantities, but with *measurable* summands, which the countable `Gamma_sigma`
  triangle inequality requires.  The abstract assembly is
  `WaveOscillationsCore.isBigOWith_gammaSigma_truncatedSum`.

The Orlicz exponent of the lower leg is kept free: `e.indc.O.sigma` is applied
at a general `sigma_2 > 0`, where the manuscript fixes `t = sigma/2`, i.e.
`sigma_2 = 2/sigma`.  At that value the delivered exponent `2 sigma_2/(2 +
sigma_2)` is exactly the printed `2(1+sigma)^{-1}`, so the Gamma index
specializes to the manuscript's on the nose.  (The truncation scale is a
factor-2 stronger exponent than the printed display — `3^{-(1-sigma)b sigma
h/2}` here vs the printed `…/4` — so the printed bound is implied with slack.)

Two other conventions of the local formulation are both strengthenings.  The
manuscript's left-hand constant `c` is taken to be `1` (the usual `0 < c ≤ 1 ≤
C` convention; the tex does not pin `c`, and `c = 1` is the strongest reading),
and the amplitude is the **uniform** (`L^infty`) size of the increment at every
point of the open cube `cu_lout`.  Passing to the manuscript's cube-averaged
`L-bar^4` amplitude costs constant `1`, NOT a dimensional factor: the tex's own
linear-algebra convention makes `|·|` the matrix O norm (= CoarseGraining
`matrixOperatorNorm`), and an average of a pointwise-dominated quantity is
dominated with constant 1.

Two further entries are consumed rather than corrected: (the shift-free `hsep`
carrier of `Provider.Percolation.MinimalScaleSeparation`, whose `sInf` junk
value and standing nonemptiness binder this module never needs, because it only
uses the *tail* of `3^{b hsep}` and the events `{i < hsep}`) (the `3^{gamma
hsep}` collapse, which belongs to Step 3, not here).

## Divergences from the printed right-hand side, recorded honestly

* The manuscript's **first** (`gamma^{1/2} hsep^{1/2}`) and **third**
  (`O_{Gamma_{2(1+sigma)^{-1}}}(sigma^{-1} 3^{-(d/8)k_0})`) terms are delivered
  **merged** into a single `Gamma_{2 sigma_2/(2+sigma_2)}` lower leg, an
  explicit convergent series carrying **no** `3^{-(d/8)k_0}` decay.  The reason
  is a missing dependency, not a defect of this step: the split needs the
  large-scale gain of `l.km.kn.Lp.estimates` (`e.km.kn.Lp` at `p = 4`), i.e. a
  per-layer bound of the shape "deterministic head `+` geometrically decaying
  `Gamma_2` tail".  The proved per-layer input here (`e.km.kn.Linfty`,
  `Provider.Stream.isBigOWith_gammaSigma_largeCubeSupBound`) has a single
  `Gamma_2` envelope with no gain.  No uniform (`L^infinity`) per-layer gauge
  can carry the `3^{-(d/8)k_0}` gain: the gain is a cube-averaging phenomenon,
  and a bound on the supremum of a stationary nondegenerate field over a
  growing cube cannot decay in the cube size (the proved `e.km.kn.Linfty`
  amplitude in fact grows like `(lout-ell+i)^{1/2}`).  The third-term split
  therefore requires re-basing the lower leg onto the manuscript's own
  `L-bar^4` average — i.e. reversing the form choice for that term only,
  reinstating the `L-bar^4` Minkowski step
  there.  The truncated-sum assembly
  (`WaveOscillationsCore.isBigOWith_gammaSigma_truncatedSum`) is unaffected,
  and the re-basing is performed in `WaveThirdTerm.lean`, whose head-plus-tail
  split `streamIncrementLpNorm_le_waveL4Head_add_waveL4Tail` is the `L-bar^4`
  form of the per-layer input; it consumes `IncrementLpLarge` and, for the
  squared form, `IncrementLpSquared`.  The printed endpoint is still not
  matched there: the exact layer specialization and the final tail-series
  comparison are not proved.
* The `Gamma_2` leg carries a covering penalty built from
  `Provider.Stream.largeCubeLogConst` and the dimensional constant
  `streamLinftyConst d` of `e.km.kn.Linfty` in place of the printed bare
  `gamma^{1/2}(L-l)^{1/2}`, and `min{gamma^{-1/2},(L-l)^{1/2}}` is relaxed to
  `(L-l)^{1/2}`.

## Measurability of `hsep`

ABK26 asserts that `hsep` is a random variable, and the proved
`Provider.Percolation.MinimalScaleSeparation` module leaves the `Measurable`
statement as A hygiene for the first consumer.  This module is that consumer,
and proves what it needs: `measurableSet_lt_hsep`.  The proof is elementary —
the bad-site pattern ranges over the finitely many subsets of `cubeFinset h`,
each with a measurable defining event — so no hypothesis is assumed.

## Main results

* `measurableSet_lt_hsep`: `{i < hsep}` is measurable, so `hsep` is a random
  variable at the level the wave step needs it.

## References

* ABK26, proof of `p.bfA.multiscalebound`, Step 2.
* ABK26, `e.km.kn.Linfty`; `e.indc.O.sigma`; `e.multGammasig`;
  `l.Gamma.sigma.triangle`; `e.hsep.tails`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## Measurability of the minimal scale separation -/

/-- The bad-site pattern is determined by finitely many measurable bad events,
so each of its finitely many possible values is a measurable event. -/
private theorem measurableSet_badSiteFinset_eq (M : ABKModel d) (m : ℤ) (h : ℕ)
    {S : Finset (Fin d → ℤ)} (hS : S ⊆ cubeFinset (d := d) h) :
    MeasurableSet {omega : CutoffSample d | badSiteFinset M m h omega = S} := by
  classical
  have hset : {omega : CutoffSample d | badSiteFinset M m h omega = S} =
      (⋂ u ∈ S, BadEvents.badExtended M (siteCube (m - (h : ℤ)) u)) ∩
        ⋂ u ∈ cubeFinset (d := d) h \ S,
          (BadEvents.badExtended M (siteCube (m - (h : ℤ)) u))ᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨fun u hu => (mem_badSiteFinset_iff.mp hu).2, fun u hu hmem => ?_⟩
      rw [Finset.mem_sdiff] at hu
      exact hu.2 (mem_badSiteFinset_iff.mpr ⟨hu.1, hmem⟩)
    · rintro ⟨hin, hout⟩
      ext u
      rw [mem_badSiteFinset_iff]
      constructor
      · rintro ⟨hu, hbad⟩
        by_contra hnot
        exact hout u (Finset.mem_sdiff.mpr ⟨hu, hnot⟩) hbad
      · intro hu
        exact ⟨hS hu, hin u hu⟩
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.biInter S.countable_toSet fun u _ =>
      BadEvents.measurableSet_badExtended M _
  · exact MeasurableSet.biInter (cubeFinset (d := d) h \ S).countable_toSet fun u _ =>
      (BadEvents.measurableSet_badExtended M _).compl

/-- The bad-cluster diameter is a measurable `N`-valued random variable: it is a
function of the bad-site pattern, which ranges over the finitely many subsets of
`cubeFinset h`. -/
private theorem measurable_badClusterDiam (M : ABKModel d) (m : ℤ) (h : ℕ)
    (u : Fin d → ℤ) :
    Measurable fun omega : CutoffSample d => badClusterDiam M m h omega u := by
  classical
  refine measurable_to_countable' fun n => ?_
  have hset : (fun omega : CutoffSample d => badClusterDiam M m h omega u) ⁻¹' {n} =
      ⋃ S ∈ (cubeFinset (d := d) h).powerset.filter
          (fun S => closedLatDiam (cluster₂ S u) = n),
        {omega : CutoffSample d | badSiteFinset M m h omega = S} := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · intro hn
      exact ⟨badSiteFinset M m h omega,
        ⟨badSiteFinset_subset M m h omega, by rw [← hn]; rfl⟩, rfl⟩
    · rintro ⟨S, ⟨_, hSn⟩, rfl⟩
      exact hSn
  rw [hset]
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun S hS => ?_
  have hS' : S ∈ (cubeFinset (d := d) h).powerset :=
    (Finset.mem_filter.1 (Finset.mem_coe.1 hS)).1
  exact measurableSet_badSiteFinset_eq M m h (Finset.mem_powerset.1 hS')

/-- The extended-bad density is a finite average of indicators of measurable
events, hence measurable. -/
private theorem measurable_badExtendedDensity (M : ABKModel d) (m : ℤ) (h : ℕ) :
    Measurable (badExtendedDensity M m h) := by
  classical
  have hrw : badExtendedDensity M m h = fun omega : CutoffSample d =>
      ((cubeFinset (d := d) h).card : ℝ)⁻¹ *
        ∑ u ∈ cubeFinset (d := d) h,
          (BadEvents.badExtended M (siteCube (m - (h : ℤ)) u)).indicator
            (fun _ => (1 : ℝ)) omega := rfl
  rw [hrw]
  refine measurable_const.mul ?_
  exact Finset.measurable_sum _ fun u _ =>
    measurable_const.indicator (BadEvents.measurableSet_badExtended M _)

/-- The good-scale event of `p.minimal.scale.separation` is measurable. -/
private theorem measurableSet_scaleSeparationGood (M : ABKModel d) (m : ℤ) (E b : ℝ)
    (h : ℕ) :
    MeasurableSet {omega : CutoffSample d | scaleSeparationGood M m E b h omega} := by
  classical
  have hset : {omega : CutoffSample d | scaleSeparationGood M m E b h omega} =
      (⋂ u ∈ cubeFinset (d := d) h,
          {omega : CutoffSample d |
            (badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ))}) ∩
        badExtendedDensity M m h ⁻¹' Set.Iic (scaleSeparationDensityThreshold M E h) := by
    ext omega
    simp only [scaleSeparationGood, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Iic]
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.biInter (cubeFinset (d := d) h).countable_toSet fun u _ => ?_
    have hpre : {omega : CutoffSample d |
          (badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ))} =
        (fun omega : CutoffSample d => badClusterDiam M m h omega u) ⁻¹'
          {n : ℕ | (n : ℝ) < (3 : ℝ) ^ (b * (h : ℝ))} := rfl
    rw [hpre]
    exact (measurable_badClusterDiam M m h u) (Set.to_countable _).measurableSet
  · exact measurable_badExtendedDensity M m h measurableSet_Iic

/-- Membership of a level in the admissible-separation set is a measurable
event. -/
private theorem measurableSet_mem_hsepSet (M : ABKModel d) (m : ℤ) (E b : ℝ) (j : ℕ) :
    MeasurableSet {omega : CutoffSample d | j ∈ hsepSet M m E b omega} := by
  classical
  by_cases hj : 1 ≤ j
  · have hset : {omega : CutoffSample d | j ∈ hsepSet M m E b omega} =
        ⋂ h : ℕ, ⋂ _ : j ≤ h,
          {omega : CutoffSample d | scaleSeparationGood M m E b h omega} := by
      ext omega
      simp only [mem_hsepSet_iff, Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun hmem h hh => hmem.2 h hh, fun hall => ⟨hj, fun h hh => hall h hh⟩⟩
    rw [hset]
    exact MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ =>
      measurableSet_scaleSeparationGood M m E b h
  · have hset : {omega : CutoffSample d | j ∈ hsepSet M m E b omega} = (∅ : Set (CutoffSample d)) := by
      ext omega
      simp only [mem_hsepSet_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hmem => hj hmem.1
    rw [hset]
    exact MeasurableSet.empty

/-- **`hsep` is a random variable, at the level the wave step needs it** (ABK26
asserts this; the proved `Provider.Percolation.MinimalScaleSeparation` module
leaves it as A hygiene for the consumer).

Because `hsepSet` is upward closed, `i < hsep omega` says exactly that `hsep` is
meaningful and that `i` itself is not admissible. -/
theorem measurableSet_lt_hsep (M : ABKModel d) (m : ℤ) (E b : ℝ) (i : ℕ) :
    MeasurableSet {omega : CutoffSample d | i < hsep M m E b omega} := by
  classical
  have hset : {omega : CutoffSample d | i < hsep M m E b omega} =
      (⋃ j : ℕ, {omega : CutoffSample d | j ∈ hsepSet M m E b omega}) ∩
        {omega : CutoffSample d | i ∈ hsepSet M m E b omega}ᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_compl_iff]
    constructor
    · intro hlt
      have hne : (hsepSet M m E b omega).Nonempty := one_le_hsep_iff.1 (by omega)
      obtain ⟨j, hj⟩ := hne
      refine ⟨⟨j, hj⟩, fun hmem => ?_⟩
      exact absurd (hsep_le_of_mem hmem) (not_le.2 hlt)
    · rintro ⟨⟨j, hj⟩, hnot⟩
      have hmem := hsep_mem ⟨j, hj⟩
      by_contra hcon
      exact hnot (hsepSet_upward hmem (not_lt.1 hcon))
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iUnion fun j => measurableSet_mem_hsepSet M m E b j
  · exact (measurableSet_mem_hsepSet M m E b i).compl

/-! ## The per-layer wave gauge -/


/-! ## The deterministic domination -/


/-! ## Numeric preliminaries

Isolated real-analytic steps, kept away from the probabilistic statements so
that no elaboration mixes `Real.rpow` algebra with weak-Orlicz unfolding. -/


/-! ## The per-layer `Gamma_2` scale -/


/-! ## Summability of the truncated-sum scale series -/


/-! ## The two legs of `e.wave.influence.bound` -/


/-! ## The corrected display -/


end

end Algsuperdiff.Section3.Provider.Multiscale

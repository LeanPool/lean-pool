/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RangeNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LowerShellRange

/-!
# IncrementLaw

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The restriction-law carrier of a finite stream increment

The node `e.kl.bounds.large` of `l.km.kn.Lp.estimates` (ABK26) improves the
`l`-uniform estimate `e.kmn.bounds` on scales larger than `3^m` by combining
the finite-range assumption `a.j.frd` with the concentration proposition
`p.concentration`, applied to the average of the cube `L^p` masses over the
scale-`m` subcubes of `cu_l`.

The concentration input available to this repository is CoarseGraining's
partition-average fluctuation theorem
`isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw`,
whose hypotheses are structural assumptions on a restriction-lane law `P:
Ch04.RestrictionCoeffLaw d`, namely `RestrictionStationaryLaw P` and
`RestrictionUnitRangeDependentLaw P`.  This module supplies the law and both
structural assumptions for the stream increment `k_m - k_n = sum_{k in (n,m]}
j_k`.

## What is proved

* `scaledStreamIncrementLaw_stationary_real`,
  `scaledStreamIncrementLaw_stationary` — the joint, multi-shell translation
  covariance, at an arbitrary nonzero spatial rescaling.  This is *not* the
  one-shell statement `map_shellObservable_translate_eq`: it is the
  whole-sequence invariance `Cutoff.sequenceLaw_stationary` (derived in the
  Cutoff layer from the independence of the shells, the marginal scaling law
  and (J1)), pushed through the exact commutation
  `translateReg_finiteShellIncrement`.
* `scaledStreamIncrementLaw_unitRangeDependent` — CoarseGraining's *unit*-range
  dependence for a rescaled increment law.  Any factor leaving strict bridge
  slack for the literal range `sqrt(d) 3^m` turns that range into a strictly
  sub-unit one, exactly as `Cutoff.RangeNormalization` does for the coefficient
  cutoff `a_m`.
* `partitionStreamIncrementLaw`, the rescaling the partition step can actually
  use, at the depth `Cutoff.cutoffNormalizationDepth d m`;
  `partitionStreamIncrementLaw_stationary` and
  `partitionStreamIncrementLaw_unitRangeDependent` are the two structural
  assumptions the concentration theorem asks for, at that law.
* `scaledStreamIncrementLaw_eq_map`, the un-normalization dictionary: every
  statement about a rescaled law is a statement about `x |-> (k_m - k_n)(r x)`
  under `M.P`.

## References

* ABK26, `e.kl.bounds.large`; `l.km.kn.Lp.estimates`; the cutoff range;
  `a.j.frd`.
* `Algsuperdiff/Section3/Cutoff/RangeNormalization.lean`, the same
  normalization for the coefficient cutoff.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory Metric
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-! ## Continuity of the increment in the space variable -/

/-- Every matrix entry of a finite stream increment is continuous in the point:
the increment is a finite sum of shells, each of which is a continuous
matrix-valued path. -/
theorem continuous_finiteShellIncrement_entry (omega : ShellSeq d) (n m : ℤ)
    (i j : Fin d) :
    Continuous (fun x : Vec d => finiteShellIncrement omega n m x i j) := by
  have h : (fun x : Vec d => finiteShellIncrement omega n m x i j) =
      fun x : Vec d => ∑ k ∈ Finset.Ioc n m, (omega k) x i j := by
    funext x
    exact finiteShellIncrement_apply_entry omega n m x i j
  rw [h]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_apply j).comp ((continuous_apply i).comp (omega k).1.1.continuous)

/-! ## Joint multi-shell translation covariance -/

/-- Translating the whole shell sequence translates the finite increment.  This
is the multi-shell covariance the concentration input needs: it is an exact
identity of regular coefficient fields, uniform in the finitely many shells
`(n, m]`. -/
theorem translateReg_finiteShellIncrement (z : Vec d) (n m : ℤ)
    (omega : ShellSeq d) :
    translateReg z (finiteShellIncrement omega n m) =
      finiteShellIncrement (ShellField.translateSequence z omega) n m := by
  refine RegCoeffField.ext fun x => ?_
  have hshell : ∀ k : ℤ,
      shellReg (ShellField.translateSequence z omega) k =
        translateReg z (shellReg omega k) := by
    intro k
    rw [shellReg, shellReg, ShellField.translateSequence_apply,
      ShellField.forgetShell_translate]
  rw [translateReg_apply, finiteShellIncrement_apply, finiteShellIncrement_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hshell k, translateReg_apply]

/-! ## Locality of the increment in the lower-shell stream -/

/-- A finite stream increment reads only shells of index at most `m`, so it is
measurable for the lower-shell integral-local sigma-field at scale `m`.  No
relation between `n` and `m` is needed: for `m < n` the increment is the zero
field. -/
theorem measurable_finiteShellIncrement_local (n m : ℤ) (U : Set (Vec d)) :
    @Measurable (ShellSeq d) (RegCoeffField d)
      (lowerShellLocalSigma m U) (LocalSigmaR U)
      (fun omega : ShellSeq d => finiteShellIncrement omega n m) := by
  by_cases hnm : n ≤ m
  · have hq : m - ((m - n).toNat : ℤ) = n := by omega
    have heq : (fun omega : ShellSeq d => finiteShellIncrement omega n m) =
        finiteLowerCutoff m (m - n).toNat := by
      funext omega
      rw [finiteLowerCutoff, hq]
    rw [heq]
    exact measurable_finiteLowerCutoff_local m (m - n).toNat U
  · have hempty : Finset.Ioc n m = (∅ : Finset ℤ) :=
      Finset.Ioc_eq_empty fun hlt => hnm hlt.le
    have hzero : (fun omega : ShellSeq d => finiteShellIncrement omega n m) =
        fun _ : ShellSeq d => (0 : RegCoeffField d) := by
      funext omega
      rw [finiteShellIncrement, hempty, Finset.sum_empty]
    rw [hzero]
    exact measurable_const

/-! ## Spatially rescaled increment laws

CoarseGraining's restriction-lane partition-average concentration theorem
`isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw`
requires its *subcube* scale to be `>= 0`, because its proof reaches a
descendant cube from the origin cube by an **integer** translation and
`RestrictionStationaryLaw` is integer-translation invariance only.  The
normalization depth of `Cutoff.RangeNormalization` (which sends the range
`sqrt(d) 3^m` below `1`) sends the scale-`m` subcubes to a strictly *negative*
scale, so it cannot be the normalization used for the partition step.: NO
rescaling clears the CoarseGraining `0 ≤ n` restriction for the manuscript's
own scale-`m` subcubes — unit range needs `r > 2·sqrt(d)·3^m > 3^m` while
nonnegative subcube scale needs `r ≤ 3^m`; the two are incompatible.  The
factor may be a negative power of `3`, outside the range of
`restrictionScaleNormalizedLaw : ℕ → _`.

Both normalizations are therefore obtained here from one statement about an
arbitrary nonzero spatial scaling `smulReg r`. -/

/-- The increment law spatially rescaled by a nonzero factor `r`: the law of
`x |-> (k_m - k_n)(r x)`. -/
def scaledStreamIncrementLaw (M : ABKModel d) (n m : ℤ) (r : ℝ) (hr : r ≠ 0) :
    HCPolySupport.Book.Ch04.RestrictionCoeffLaw d :=
  Measure.map
    (fun omega : ShellSeq d => smulReg r hr (finiteShellIncrement omega n m))
    M.P.toMeasure

theorem scaledStreamIncrementLaw_eq_map (M : ABKModel d) (n m : ℤ) {r : ℝ}
    (hr : r ≠ 0) :
    scaledStreamIncrementLaw M n m r hr =
      Measure.map
        (fun omega : ShellSeq d => smulReg r hr (finiteShellIncrement omega n m))
        M.P.toMeasure :=
  rfl

instance scaledStreamIncrementLaw_isProbabilityMeasure (M : ABKModel d) (n m : ℤ)
    (r : ℝ) (hr : r ≠ 0) :
    IsProbabilityMeasure (scaledStreamIncrementLaw M n m r hr) := by
  unfold scaledStreamIncrementLaw; infer_instance

/-- Translation commutes with spatial rescaling on the carrier. -/
theorem translateReg_smulReg {r : ℝ} (hr : r ≠ 0) (z : Vec d)
    (a : RegCoeffField d) :
    translateReg z (smulReg r hr a) = smulReg r hr (translateReg (r • z) a) := by
  refine RegCoeffField.ext fun x => ?_
  rw [translateReg_apply, smulReg_apply, smulReg_apply, translateReg_apply,
    smul_add]

/-- **Real-translation stationarity survives every spatial rescaling**, because
the increment law is invariant under *all* real translations. -/
theorem scaledStreamIncrementLaw_stationary_real (M : ABKModel d) (n m : ℤ)
    {r : ℝ} (hr : r ≠ 0) (z : Vec d) :
    Measure.map (translateReg z) (scaledStreamIncrementLaw M n m r hr) =
      scaledStreamIncrementLaw M n m r hr := by
  have hmeas : Measurable
      (fun omega : ShellSeq d => smulReg r hr (finiteShellIncrement omega n m)) :=
    (measurable_smulReg r hr).comp (measurable_finiteShellIncrement n m)
  have htr : Measurable (ShellField.translateSequence (d := d) (r • z)) :=
    ShellField.measurable_translateSequence (r • z)
  have key : translateReg z ∘
      (fun omega : ShellSeq d => smulReg r hr (finiteShellIncrement omega n m)) =
      (fun omega : ShellSeq d => smulReg r hr (finiteShellIncrement omega n m)) ∘
        ShellField.translateSequence (r • z) := by
    funext omega
    simp only [Function.comp_apply]
    rw [translateReg_smulReg hr z, translateReg_finiteShellIncrement]
  rw [scaledStreamIncrementLaw_eq_map,
    Measure.map_map (measurable_translateReg z) hmeas, key,
    ← Measure.map_map hmeas htr, sequenceLaw_stationary M (r • z)]

/-- **CoarseGraining's restriction-stationarity predicate for every rescaled
increment law.** -/
theorem scaledStreamIncrementLaw_stationary (M : ABKModel d) (n m : ℤ) {r : ℝ}
    (hr : r ≠ 0) :
    HCPolySupport.Book.Ch04.RestrictionStationaryLaw
      (scaledStreamIncrementLaw M n m r hr) :=
  fun z => scaledStreamIncrementLaw_stationary_real M n m hr (intVecToRealVec z)

/-! ## Unit-range dependence of the normalized increment law -/

private theorem vecNorm_smul (c : ℝ) (v : Vec d) :
    HCPolySupport.Book.Ch02.vecNorm (c • v) =
      |c| * HCPolySupport.Book.Ch02.vecNorm v := by
  change ‖(WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d))‖ =
    |c| * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖
  have h : (WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d)) =
      c • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by
    ext i
    rfl
  rw [h, norm_smul, Real.norm_eq_abs]

/-- The literal increment range on the two scaled thickenings.  This is the
same geometry as `Cutoff.RangeNormalization`, at an arbitrary positive
rescaling factor leaving strictly more room than the literal range
`sqrt(d) 3^m`. -/
private theorem increment_range_on_scaled_thickenings (d : ℕ) (m : ℤ) {r : ℝ}
    (hrpos : 0 < r) (U V : Set (Vec d)) (hUV : AreUnitSeparated U V)
    (hslack : cutoffNaturalRange d m < r * (1 - 2 * cutoffBridgeEpsilon)) :
    ∀ ⦃x y : Vec d⦄,
      x ∈ r • thickening cutoffBridgeEpsilon U →
      y ∈ r • thickening cutoffBridgeEpsilon V →
      cutoffNaturalRange d m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
  rintro x y ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
  have hgap :=
    Algsuperdiff.Section3.Annealed.one_sub_two_mul_lt_vecNorm_sub_of_mem_thickenings
      (d := d) hUV (epsilon := cutoffBridgeEpsilon) hx0 hy0
  have hstrict : cutoffNaturalRange d m <
      HCPolySupport.Book.Ch02.vecNorm (r • x0 - r • y0) := by
    rw [← smul_sub, vecNorm_smul, abs_of_pos hrpos]
    exact hslack.trans (mul_lt_mul_of_pos_left hgap hrpos)
  exact hstrict.le

/-- **CoarseGraining's exact unit-range dependence for a rescaled increment law.**

The increment `k_m - k_n` reads only shells of index at most `m`, whose joint
integral-local information has literal Euclidean range `sqrt(d) 3^m`
(`Cutoff.indep_lowerShellLocalSigma_of_cutoff_separation`).  Rescaling by any
factor `r` that leaves strict `epsilon = 1/4` bridge slack for that range turns
it into a strictly sub-unit range, which is CoarseGraining's
`RestrictionUnitRangeDependentLaw` after the thickening bridge.  This is the
`RestrictionUnitRangeDependentLaw` hypothesis of
`isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw`. -/
theorem scaledStreamIncrementLaw_unitRangeDependent (M : ABKModel d) (n m : ℤ)
    {r : ℝ} (hr : r ≠ 0) (hrpos : 0 < r)
    (hslack : cutoffNaturalRange d m < r * (1 - 2 * cutoffBridgeEpsilon)) :
    HCPolySupport.Book.Ch04.RestrictionUnitRangeDependentLaw
      (scaledStreamIncrementLaw M n m r hr) := by
  intro U V hU hV hUV
  let S : Set (Vec d) := thickening cutoffBridgeEpsilon U
  let T : Set (Vec d) := thickening cutoffBridgeEpsilon V
  have hS : MeasurableSet S := isOpen_thickening.measurableSet
  have hT : MeasurableSet T := isOpen_thickening.measurableSet
  have hrS : MeasurableSet (r • S) := hS.const_smul_of_ne_zero hr
  have hrT : MeasurableSet (r • T) := hT.const_smul_of_ne_zero hr
  have hsep : ∀ ⦃x y : Vec d⦄, x ∈ r • S → y ∈ r • T →
      cutoffNaturalRange d m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
    simpa only [S, T] using
      increment_range_on_scaled_thickenings d m hrpos U V hUV hslack
  let A : ShellSeq d → RegCoeffField d :=
    fun omega => smulReg r hr (finiteShellIncrement omega n m)
  have hAmeas : Measurable A :=
    (measurable_smulReg r hr).comp (measurable_finiteShellIncrement n m)
  have hAcont : ∀ omega i j, Continuous (fun x : Vec d => A omega x i j) := by
    intro omega i j
    exact (continuous_finiteShellIncrement_entry omega n m i j).comp
      ((continuous_const : Continuous (fun _ : Vec d => r)).smul
        (continuous_id : Continuous (fun x : Vec d => x)))
  have hlocalSource :=
    indep_lowerShellLocalSigma_of_cutoff_separation M m hrS hrT hsep
  have hA_local_S : @Measurable (ShellSeq d) (RegCoeffField d)
      (lowerShellLocalSigma m (r • S)) (LocalSigmaR S) A :=
    (measurable_smulReg_local r hr S).comp
      (measurable_finiteShellIncrement_local n m (r • S))
  have hA_local_T : @Measurable (ShellSeq d) (RegCoeffField d)
      (lowerShellLocalSigma m (r • T)) (LocalSigmaR T) A :=
    (measurable_smulReg_local r hr T).comp
      (measurable_finiteShellIncrement_local n m (r • T))
  have hlocal : Indep (MeasurableSpace.comap A (LocalSigmaR S))
      (MeasurableSpace.comap A (LocalSigmaR T)) M.P.toMeasure :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hlocalSource hA_local_S.comap_le)
      hA_local_T.comap_le
  have hbridge :=
    Algsuperdiff.Section3.Annealed.indep_restrictionSigmaR_map_of_indep_localSigmaR_thickenings
      A hAmeas hAcont U V hU hV cutoffBridgeEpsilon cutoffBridgeEpsilon_pos hlocal
  have hmap : Measure.map A M.P.toMeasure = scaledStreamIncrementLaw M n m r hr :=
    rfl
  simpa [A, S, T] using hmap ▸ hbridge

/-! ## The partition normalization

CoarseGraining's restriction-lane partition theorem needs its *subcube* scale
to be `≥ 0`.  The scale that achieves this sends the scale-`m` subcubes to
scale `0`, i.e. rescales by `3^{m+c}` where `3^c > 2 sqrt(d)`; this is in
general **not** a rescaling by a natural power of `3`, so it is outside the
range of `restrictionScaleNormalizedLaw`. -/

/-- The dimensional shift `c`: the least triadic depth with `3^c > 2 sqrt(d)`. -/
def incrementPartitionShift (d : ℕ) : ℕ := cutoffNormalizationDepth d 0

/-- The partition normalization factor `3^{m+c}`: it sends the scale-`m`
subcubes of the partition to unit cubes and the literal range `sqrt(d) 3^m`
strictly below the bridge budget. -/
def incrementPartitionScale (d : ℕ) (m : ℤ) : ℝ :=
  (3 : ℝ) ^ (m + (incrementPartitionShift d : ℤ))

theorem incrementPartitionScale_pos (d : ℕ) (m : ℤ) :
    0 < incrementPartitionScale d m := by
  rw [incrementPartitionScale]
  positivity

theorem incrementPartitionScale_ne_zero (d : ℕ) (m : ℤ) :
    incrementPartitionScale d m ≠ 0 :=
  (incrementPartitionScale_pos d m).ne'

theorem incrementPartitionScale_strict_slack (d : ℕ) (m : ℤ) :
    cutoffNaturalRange d m <
      incrementPartitionScale d m * (1 - 2 * cutoffBridgeEpsilon) := by
  have hspec : 2 * Real.sqrt (d : ℝ) <
      (3 : ℝ) ^ (incrementPartitionShift d) := by
    simpa [incrementPartitionShift, cutoffNaturalRange_zero] using
      cutoffNormalizationDepth_spec d 0
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hsplit : incrementPartitionScale d m =
      (3 : ℝ) ^ m * (3 : ℝ) ^ (incrementPartitionShift d) := by
    rw [incrementPartitionScale, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  rw [hsplit, one_sub_two_mul_cutoffBridgeEpsilon, cutoffNaturalRange]
  nlinarith [hspec, h3m]

/-- **The partition-normalized increment law**: the law of `x |-> (k_m -
k_n)(3^{m+c} x)`, under which the scale-`(m+c)` subcubes of `cu_l` become the
scale-`0` descendants of `cu_{l-m-c}` (the scale-`m` subcubes land at scale
`-c`;). -/
def partitionStreamIncrementLaw (M : ABKModel d) (n m : ℤ) :
    HCPolySupport.Book.Ch04.RestrictionCoeffLaw d :=
  scaledStreamIncrementLaw M n m (incrementPartitionScale d m)
    (incrementPartitionScale_ne_zero d m)

instance partitionStreamIncrementLaw_isProbabilityMeasure (M : ABKModel d)
    (n m : ℤ) : IsProbabilityMeasure (partitionStreamIncrementLaw M n m) :=
  scaledStreamIncrementLaw_isProbabilityMeasure M n m _ _

theorem partitionStreamIncrementLaw_stationary (M : ABKModel d) (n m : ℤ) :
    HCPolySupport.Book.Ch04.RestrictionStationaryLaw
      (partitionStreamIncrementLaw M n m) :=
  scaledStreamIncrementLaw_stationary M n m _

theorem partitionStreamIncrementLaw_unitRangeDependent (M : ABKModel d)
    (n m : ℤ) :
    HCPolySupport.Book.Ch04.RestrictionUnitRangeDependentLaw
      (partitionStreamIncrementLaw M n m) :=
  scaledStreamIncrementLaw_unitRangeDependent M n m _
    (incrementPartitionScale_pos d m) (incrementPartitionScale_strict_slack d m)

end

end Algsuperdiff.Section3.Provider.Stream

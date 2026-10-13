/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DeepBandSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LayerPerCubePricing

/-!
# DeepBandGroup

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/- The following definitions are temporary proof-probe names.  They model a
geometric partition of the band `(top-k₀, top]`; they are not proposed public
A. -/

/-- The upper scale index of a truncated geometric band. -/
def probeBandIndex (top : ℤ) (k₀ p : ℕ) : ℤ :=
  top - ((min (3 ^ p - 1) k₀ : ℕ) : ℤ)

/-- The number of scales in a truncated geometric band. -/
def probeBandLength (k₀ p : ℕ) : ℕ :=
  min (3 ^ (p + 1) - 1) k₀ - min (3 ^ p - 1) k₀

/-- The nonempty truncated bands among the first `N` bands. -/
def probeBandGroups (top : ℤ) (k₀ N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun p => probeBandIndex top k₀ (p + 1) < probeBandIndex top k₀ p

private theorem pow_three_succ_probe (p : ℕ) :
    (3 : ℕ) ^ (p + 1) = 3 * 3 ^ p := by ring

private theorem one_le_pow_three_probe (p : ℕ) : 1 ≤ (3 : ℕ) ^ p :=
  Nat.one_le_pow _ _ (by norm_num)


theorem probeBandIndex_le (top : ℤ) (k₀ p : ℕ) :
    probeBandIndex top k₀ p ≤ top := by
  unfold probeBandIndex
  omega

theorem probeBandIndex_succ_le (top : ℤ) (k₀ p : ℕ) :
    probeBandIndex top k₀ (p + 1) ≤ probeBandIndex top k₀ p := by
  have h3 := pow_three_succ_probe p
  have h1 := one_le_pow_three_probe p
  unfold probeBandIndex
  omega

theorem probeBandIndex_of_cover (top : ℤ) {k₀ N : ℕ} (hN : k₀ < 3 ^ N) :
    probeBandIndex top k₀ N = top - (k₀ : ℤ) := by
  unfold probeBandIndex
  omega

theorem probeBandIndex_sub (top : ℤ) (k₀ p : ℕ) :
    probeBandIndex top k₀ p - probeBandIndex top k₀ (p + 1) =
      (probeBandLength k₀ p : ℤ) := by
  have h3 := pow_three_succ_probe p
  have h1 := one_le_pow_three_probe p
  unfold probeBandIndex probeBandLength
  omega

theorem probeBandLength_le (k₀ p : ℕ) :
    probeBandLength k₀ p ≤ 2 * 3 ^ p := by
  have h3 := pow_three_succ_probe p
  have h1 := one_le_pow_three_probe p
  unfold probeBandLength
  omega

theorem streamIncrementLpNorm_self_probe {p : ℝ} (hp : 0 < p)
    (l a : ℤ) (omega : ShellSeq d) :
    streamIncrementLpNorm p l a a omega = 0 := by
  simp [streamIncrementLpNorm, streamIncrementLpMass, streamIncrementLpDensity,
    finiteShellIncrement, Book.Ch02.average, hp.ne']

/- Sharp finite-band Minkowski at the proved volume-normalized carrier. -/
theorem streamIncrementLpNorm_probeBand_ladder {p : ℝ} (hp : 1 ≤ p)
    (l top : ℤ) (k₀ N : ℕ) (omega : ShellSeq d) :
    streamIncrementLpNorm p l (probeBandIndex top k₀ N) top omega ≤
      ∑ r ∈ Finset.range N,
        streamIncrementLpNorm p l (probeBandIndex top k₀ (r + 1))
          (probeBandIndex top k₀ r) omega := by
  induction N with
  | zero =>
      have hzero : probeBandIndex top k₀ 0 = top := by
        simp [probeBandIndex]
      rw [hzero]
      simp [streamIncrementLpNorm_self_probe (lt_of_lt_of_le zero_lt_one hp)]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have htri := streamIncrementLpNorm_add_le (d := d) hp l
        (probeBandIndex_succ_le top k₀ N) (probeBandIndex_le top k₀ N) omega
      linarith

theorem streamIncrementLpNorm_probeBand_ladder_of_cover {p : ℝ} (hp : 1 ≤ p)
    (l ell : ℤ) {k₀ N : ℕ} (hN : k₀ < 3 ^ N) (omega : ShellSeq d) :
    streamIncrementLpNorm p l ell (ell + (k₀ : ℤ)) omega ≤
      ∑ r ∈ Finset.range N,
        streamIncrementLpNorm p l
          (probeBandIndex (ell + (k₀ : ℤ)) k₀ (r + 1))
          (probeBandIndex (ell + (k₀ : ℤ)) k₀ r) omega := by
  have h := streamIncrementLpNorm_probeBand_ladder (d := d) hp l
    (ell + (k₀ : ℤ)) k₀ N omega
  rw [probeBandIndex_of_cover _ hN, add_sub_cancel_right] at h
  exact h

@[simp] theorem mem_probeBandGroups {top : ℤ} {k₀ N r : ℕ} :
    r ∈ probeBandGroups top k₀ N ↔
      r ∈ Finset.range N ∧
        probeBandIndex top k₀ (r + 1) < probeBandIndex top k₀ r := by
  simp [probeBandGroups]

theorem zero_mem_probeBandGroups (top : ℤ) {k₀ N : ℕ}
    (hk₀ : 2 ≤ k₀) (hN : k₀ < 3 ^ N) :
    0 ∈ probeBandGroups top k₀ N := by
  have hN0 : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    subst N
    norm_num at hN
    omega
  rw [mem_probeBandGroups]
  refine ⟨Finset.mem_range.2 hN0, ?_⟩
  simp [probeBandIndex]
  omega

theorem probeBandIndex_eq_of_not_mem_groups {top : ℤ} {k₀ N r : ℕ}
    (hr : r ∈ Finset.range N) (hnot : r ∉ probeBandGroups top k₀ N) :
    probeBandIndex top k₀ (r + 1) = probeBandIndex top k₀ r := by
  have hle := probeBandIndex_succ_le top k₀ r
  have hnlt : ¬ probeBandIndex top k₀ (r + 1) < probeBandIndex top k₀ r := by
    intro hlt
    exact hnot (mem_probeBandGroups.2 ⟨hr, hlt⟩)
  omega

theorem cubeStreamIncrementLpNorm_self_probe {p : ℝ} (hp : 0 < p)
    (Q : TriadicCube d) (a : ℤ) (omega : ShellSeq d) :
    cubeStreamIncrementLpNorm p Q a a omega = 0 := by
  rw [cubeStreamIncrementLpNorm_eq_streamIncrementLpNorm_translate hp]
  exact streamIncrementLpNorm_self_probe hp Q.scale a _

theorem cubeStreamIncrementLpNorm_probeBand_ladder_of_cover {p : ℝ}
    (hp : 1 ≤ p) (Q : TriadicCube d) (ell : ℤ) {k₀ N : ℕ}
    (hN : k₀ < 3 ^ N) (omega : ShellSeq d) :
    cubeStreamIncrementLpNorm p Q ell (ell + (k₀ : ℤ)) omega ≤
      ∑ r ∈ probeBandGroups (ell + (k₀ : ℤ)) k₀ N,
        cubeStreamIncrementLpNorm p Q
          (probeBandIndex (ell + (k₀ : ℤ)) k₀ (r + 1))
          (probeBandIndex (ell + (k₀ : ℤ)) k₀ r) omega := by
  have hfull := streamIncrementLpNorm_probeBand_ladder_of_cover (d := d) hp
    Q.scale ell hN (ShellField.translateSequence (triadicCubeShift Q) omega)
  have hconvert : ∀ a b : ℤ,
      streamIncrementLpNorm p Q.scale a b
          (ShellField.translateSequence (triadicCubeShift Q) omega) =
        cubeStreamIncrementLpNorm p Q a b omega := by
    intro a b
    exact (cubeStreamIncrementLpNorm_eq_streamIncrementLpNorm_translate
      (lt_of_lt_of_le zero_lt_one hp) Q a b omega).symm
  simp_rw [hconvert] at hfull
  refine hfull.trans_eq ?_
  rw [probeBandGroups]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  split
  case isTrue hlt => rfl
  case isFalse hlt =>
    have hnot : r ∉ probeBandGroups (ell + (k₀ : ℤ)) k₀ N := by
      intro hmem
      exact hlt (mem_probeBandGroups.1 hmem).2
    have heq := probeBandIndex_eq_of_not_mem_groups hr hnot
    rw [heq, cubeStreamIncrementLpNorm_self_probe
      (lt_of_lt_of_le zero_lt_one hp) Q]

/-- The sum of fourth-moment stream tails over the selected deep bands. -/
def probeDeepBandTail (M : ABKModel d) (Q : TriadicCube d)
    (top : ℤ) (k₀ N : ℕ) (omega : CutoffSample d) : ℝ :=
  ∑ r ∈ probeBandGroups top k₀ N,
    cubeStreamIncrementLpTail M 4 Q
      (probeBandIndex top k₀ (r + 1)) (probeBandIndex top k₀ r) omega.1 ^
        (4 : ℝ)⁻¹

theorem measurable_cubeStreamIncrementLpTail_rpow_cutoff_probe (M : ABKModel d)
    {p : ℝ} (hp : 0 < p) (Q : TriadicCube d) (n m : ℤ) :
    Measurable fun omega : CutoffSample d =>
      cubeStreamIncrementLpTail M p Q n m omega.1 ^ p⁻¹ := by
  have hmass : Measurable fun omega : ShellSeq d =>
      streamIncrementLpMass p Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) := by
    have heq : (fun omega : ShellSeq d =>
        streamIncrementLpMass p Q.scale n m
          (ShellField.translateSequence (triadicCubeShift Q) omega)) =
        fun omega : ShellSeq d =>
          cubeAverage Q (streamIncrementLpDensity p n m omega) := by
      funext omega
      exact (cubeAverage_streamIncrementLpDensity_eq_streamIncrementLpMass_translate
        hp Q n m omega).symm
    rw [heq]
    exact measurable_cubeAverage_streamIncrementLpDensity hp Q n m
  have htail : Measurable fun omega : ShellSeq d =>
      cubeStreamIncrementLpTail M p Q n m omega := by
    change Measurable fun omega : ShellSeq d =>
      streamIncrementLpTail M p Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega)
    by_cases hc : m + (incrementPartitionShift d : ℤ) ≤ Q.scale
    · have heq : (fun omega : ShellSeq d =>
          streamIncrementLpTail M p Q.scale n m
            (ShellField.translateSequence (triadicCubeShift Q) omega)) =
          fun omega : ShellSeq d =>
            |streamIncrementLpMass p Q.scale n m
                (ShellField.translateSequence (triadicCubeShift Q) omega) -
              ∫ w, streamIncrementLpMass p
                  (m + (incrementPartitionShift d : ℤ)) n m w ∂M.P.toMeasure| := by
        funext omega
        rw [streamIncrementLpTail, ite_eq_left hc]
      rw [heq]
      exact (hmass.sub measurable_const).abs
    · have heq : (fun omega : ShellSeq d =>
          streamIncrementLpTail M p Q.scale n m
            (ShellField.translateSequence (triadicCubeShift Q) omega)) =
          fun omega : ShellSeq d =>
            streamIncrementLpMass p Q.scale n m
              (ShellField.translateSequence (triadicCubeShift Q) omega) := by
        funext omega
        rw [streamIncrementLpTail, ite_eq_right hc]
      rw [heq]
      exact hmass
  exact ((htail.comp measurable_subtype_coe).pow_const _)

theorem probeDeepBandTail_measurable (M : ABKModel d) (Q : TriadicCube d)
    (top : ℤ) (k₀ N : ℕ) :
    Measurable (probeDeepBandTail M Q top k₀ N) := by
  classical
  exact Finset.measurable_sum _ fun r _ =>
    measurable_cubeStreamIncrementLpTail_rpow_cutoff_probe M (by norm_num) Q _ _

theorem probeDeepBandTail_nonneg (M : ABKModel d) (Q : TriadicCube d)
    (top : ℤ) (k₀ N : ℕ) (omega : CutoffSample d) :
    0 ≤ probeDeepBandTail M Q top k₀ N omega := by
  classical
  exact Finset.sum_nonneg fun r _ => Real.rpow_nonneg
    (cubeStreamIncrementLpTail_nonneg M 4 Q _ _ omega.1) _

theorem cubeStreamIncrementLpNorm_deepBand_groupSplit_probe
    (M : ABKModel d) (Q : TriadicCube d) (ell : ℤ) {k₀ N : ℕ}
    (hk₀ : 2 ≤ k₀) (hN : k₀ < 3 ^ N) :
    (∀ omega : CutoffSample d,
        cubeStreamIncrementLpNorm 4 Q ell (ell + (k₀ : ℤ)) omega.1 ≤
          (∑ r ∈ probeBandGroups (ell + (k₀ : ℤ)) k₀ N,
            streamIncrementLpMassHead M 4
                (probeBandIndex (ell + (k₀ : ℤ)) k₀ (r + 1))
                (probeBandIndex (ell + (k₀ : ℤ)) k₀ r) ^ (4 : ℝ)⁻¹) +
            probeDeepBandTail M Q (ell + (k₀ : ℤ)) k₀ N omega) ∧
      IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
        (IndependentSums.gammaSigma 2)
        (probeDeepBandTail M Q (ell + (k₀ : ℤ)) k₀ N)
        (IndependentSums.gammaTriangleConst 2 *
          ∑ r ∈ probeBandGroups (ell + (k₀ : ℤ)) k₀ N,
            streamIncrementLpGainScale M 4 Q.scale
                (probeBandIndex (ell + (k₀ : ℤ)) k₀ (r + 1))
                (probeBandIndex (ell + (k₀ : ℤ)) k₀ r) ^ (4 : ℝ)⁻¹) := by
  classical
  let top : ℤ := ell + (k₀ : ℤ)
  let S : Finset ℕ := probeBandGroups top k₀ N
  have hSne : S.Nonempty := ⟨0, by
    rw [show S = probeBandGroups top k₀ N by rfl]
    exact zero_mem_probeBandGroups top hk₀ hN⟩
  have hrow : ∀ r ∈ S,
      let n := probeBandIndex top k₀ (r + 1)
      let m := probeBandIndex top k₀ r
      (∀ omega : ShellSeq d,
          cubeStreamIncrementLpNorm 4 Q n m omega ≤
            streamIncrementLpMassHead M 4 n m ^ (4 : ℝ)⁻¹ +
              cubeStreamIncrementLpTail M 4 Q n m omega ^ (4 : ℝ)⁻¹) ∧
        IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d =>
            cubeStreamIncrementLpTail M 4 Q n m omega ^ (4 : ℝ)⁻¹)
          (streamIncrementLpGainScale M 4 Q.scale n m ^ (4 : ℝ)⁻¹) := by
    intro r hr
    exact cubeStreamIncrementLpNorm_head_tail_gain M (by norm_num)
      (mem_probeBandGroups.1 hr).2 Q
  constructor
  · intro omega
    have hladder := cubeStreamIncrementLpNorm_probeBand_ladder_of_cover
      (d := d) (by norm_num : (1 : ℝ) ≤ 4) Q ell hN omega.1
    calc
      cubeStreamIncrementLpNorm 4 Q ell top omega.1
          ≤ ∑ r ∈ S,
              cubeStreamIncrementLpNorm 4 Q
                (probeBandIndex top k₀ (r + 1))
                (probeBandIndex top k₀ r) omega.1 := by
            simpa [top, S] using hladder
      _ ≤ ∑ r ∈ S,
            (streamIncrementLpMassHead M 4
                (probeBandIndex top k₀ (r + 1))
                (probeBandIndex top k₀ r) ^ (4 : ℝ)⁻¹ +
              cubeStreamIncrementLpTail M 4 Q
                (probeBandIndex top k₀ (r + 1))
                (probeBandIndex top k₀ r) omega.1 ^ (4 : ℝ)⁻¹) :=
          Finset.sum_le_sum fun r hr => (hrow r hr).1 omega.1
      _ = (∑ r ∈ S,
            streamIncrementLpMassHead M 4
                (probeBandIndex top k₀ (r + 1))
                (probeBandIndex top k₀ r) ^ (4 : ℝ)⁻¹) +
            probeDeepBandTail M Q top k₀ N omega := by
          rw [Finset.sum_add_distrib]
          rfl
  · have hpos : ∀ r ∈ S,
        0 < streamIncrementLpGainScale M 4 Q.scale
              (probeBandIndex top k₀ (r + 1))
              (probeBandIndex top k₀ r) ^ (4 : ℝ)⁻¹ := by
      intro r hr
      exact Real.rpow_pos_of_pos
        (streamIncrementLpGainScale_pos M (by norm_num)
          (mem_probeBandGroups.1 hr).2 Q.scale) _
    have hbigO : ∀ r ∈ S,
        IndependentSums.IsBigO (cutoffSampleLaw M).toMeasure
          (IndependentSums.gammaSigma 2)
          (fun omega : CutoffSample d =>
            cubeStreamIncrementLpTail M 4 Q
                (probeBandIndex top k₀ (r + 1))
                (probeBandIndex top k₀ r) omega.1 ^ (4 : ℝ)⁻¹)
          (streamIncrementLpGainScale M 4 Q.scale
              (probeBandIndex top k₀ (r + 1))
              (probeBandIndex top k₀ r) ^ (4 : ℝ)⁻¹) := by
      intro r hr
      let nr : ℤ := probeBandIndex top k₀ (r + 1)
      let mr : ℤ := probeBandIndex top k₀ r
      have hnonneg : ∀ omega : CutoffSample d,
          0 ≤ cubeStreamIncrementLpTail M 4 Q nr mr omega.1 ^ (4 : ℝ)⁻¹ :=
        fun omega => Real.rpow_nonneg
          (cubeStreamIncrementLpTail_nonneg M 4 Q nr mr omega.1) _
      have hwith : IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
          (IndependentSums.gammaSigma 2)
          (fun omega : CutoffSample d =>
            cubeStreamIncrementLpTail M 4 Q nr mr omega.1 ^ (4 : ℝ)⁻¹)
          (streamIncrementLpGainScale M 4 Q.scale nr mr ^ (4 : ℝ)⁻¹) :=
        isBigOWith_cutoffSampleLaw_comp_val (hrow r hr).2
      exact (Orlicz.isBigOWith_iff_isBigO_of_nonneg hnonneg).1 hwith
    have htri := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := (cutoffSampleLaw M).toMeasure) S (by norm_num : (0 : ℝ) < 2)
      hSne hpos hbigO (fun r _ =>
        measurable_cubeStreamIncrementLpTail_rpow_cutoff_probe M (by norm_num) Q _ _)
    exact (Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (probeDeepBandTail_nonneg M Q top k₀ N)).2 (by simpa [probeDeepBandTail] using! htri)

/- Pure arithmetic needed to compress the exact group sums.  These are probe
lemmas, not proposed public declarations. -/

theorem probeBandLength_eq_zero {k₀ r : ℕ} (h : k₀ < 3 ^ r) :
    probeBandLength k₀ r = 0 := by
  have h3 := pow_three_succ_probe r
  have h1 := one_le_pow_three_probe r
  unfold probeBandLength
  omega

private theorem sqrt_pow_eq_probe {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

private theorem geom_sum_mul_sub_one_probe (r : ℝ) (n : ℕ) :
    (∑ p ∈ Finset.range n, r ^ p) * (r - 1) = r ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

private theorem sqrt_three_le_probe : Real.sqrt 3 ≤ 1.733 := by
  have h : Real.sqrt 3 ≤ Real.sqrt (1.733 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.733)] at h

private theorem le_sqrt_three_probe : (1.73 : ℝ) ≤ Real.sqrt 3 := by
  have h : Real.sqrt (1.73 ^ 2) ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.73)] at h

private theorem sqrt_two_le_probe : Real.sqrt 2 ≤ 1.415 := by
  have h : Real.sqrt 2 ≤ Real.sqrt (1.415 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.415)] at h

theorem sqrt_probeBandLength_le (k₀ r : ℕ) :
    Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ) ≤
      Real.sqrt 2 * Real.sqrt 3 ^ r := by
  have hcast : ((probeBandLength k₀ r : ℕ) : ℝ) ≤ 2 * (3 : ℝ) ^ r := by
    have h := Nat.cast_le (α := ℝ) |>.2 (probeBandLength_le k₀ r)
    push_cast at h
    exact h
  calc
    Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ)
        ≤ Real.sqrt (2 * (3 : ℝ) ^ r) := Real.sqrt_le_sqrt hcast
    _ = Real.sqrt 2 * Real.sqrt ((3 : ℝ) ^ r) := Real.sqrt_mul (by norm_num) _
    _ = Real.sqrt 2 * Real.sqrt 3 ^ r := by
      rw [sqrt_pow_eq_probe (by norm_num : (0 : ℝ) ≤ 3)]

private theorem probeMeanSumAlgebra {s2 s3 T sk : ℝ}
    (hs2 : s2 ≤ 1.415) (hs3 : 1.73 ≤ s3) (hs3' : s3 ≤ 1.733)
    (hT : 0 ≤ T) (hsk : 0 ≤ sk) (hgeom : T * (s3 - 1) ≤ s3 * sk) :
    s2 * T ≤ 3.7 * sk := by
  have h1 : T * 0.73 ≤ T * (s3 - 1) := by
    nlinarith [mul_nonneg hT (by linarith : (0 : ℝ) ≤ s3 - 1.73)]
  have h2 : s3 * sk ≤ 1.733 * sk := by
    nlinarith [mul_nonneg hsk (by linarith : (0 : ℝ) ≤ 1.733 - s3)]
  have h3 : T ≤ 2.375 * sk := by linarith
  have h4 : s2 * T ≤ 1.415 * T := by
    nlinarith [mul_nonneg hT (by linarith : (0 : ℝ) ≤ 1.415 - s2)]
  linarith

theorem probeBandMeanSumRaw (k₀ N : ℕ) :
    ∑ r ∈ Finset.range N, Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ) ≤
      3.7 * Real.sqrt (k₀ : ℝ) := by
  rcases Nat.eq_zero_or_pos k₀ with hk | hk
  · subst hk
    have hz : ∀ r ∈ Finset.range N,
        Real.sqrt ((probeBandLength 0 r : ℕ) : ℝ) = 0 := by
      intro r _
      simp [probeBandLength]
    rw [Finset.sum_congr rfl hz]
    simp
  · have hk0 : k₀ ≠ 0 := by omega
    have hPk : 3 ^ Nat.log 3 k₀ ≤ k₀ := Nat.pow_log_le_self 3 hk0
    have hkP : k₀ < 3 ^ (Nat.log 3 k₀ + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) k₀
    have hstep1 :
        ∑ r ∈ Finset.range N, Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ) ≤
          ∑ r ∈ Finset.range (Nat.log 3 k₀ + 1),
            Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ) := by
      rcases le_total N (Nat.log 3 k₀ + 1) with h | h
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 h) (fun i _ _ => Real.sqrt_nonneg _)
      · refine le_of_eq (Finset.sum_subset (Finset.range_subset_range.2 h) ?_).symm
        intro x _ hnx
        have hxP : Nat.log 3 k₀ + 1 ≤ x := by
          simpa only [Finset.mem_range, not_lt] using hnx
        have hpow : 3 ^ (Nat.log 3 k₀ + 1) ≤ 3 ^ x :=
          Nat.pow_le_pow_right (by norm_num) hxP
        rw [probeBandLength_eq_zero (by omega)]
        simp
    have hstep2 :
        ∑ r ∈ Finset.range (Nat.log 3 k₀ + 1),
            Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ) ≤
          Real.sqrt 2 * ∑ r ∈ Finset.range (Nat.log 3 k₀ + 1), Real.sqrt 3 ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun r _ => sqrt_probeBandLength_le k₀ r
    have hT0 : 0 ≤ ∑ r ∈ Finset.range (Nat.log 3 k₀ + 1), Real.sqrt 3 ^ r :=
      Finset.sum_nonneg fun r _ => pow_nonneg (Real.sqrt_nonneg _) r
    have hlek : Real.sqrt 3 ^ Nat.log 3 k₀ ≤ Real.sqrt (k₀ : ℝ) := by
      rw [← sqrt_pow_eq_probe (by norm_num : (0 : ℝ) ≤ 3)]
      refine Real.sqrt_le_sqrt ?_
      have h := Nat.cast_le (α := ℝ) |>.2 hPk
      push_cast at h
      exact h
    have hgeom :
        (∑ r ∈ Finset.range (Nat.log 3 k₀ + 1), Real.sqrt 3 ^ r) *
            (Real.sqrt 3 - 1) ≤ Real.sqrt 3 * Real.sqrt (k₀ : ℝ) := by
      rw [geom_sum_mul_sub_one_probe]
      have h : Real.sqrt 3 ^ (Nat.log 3 k₀ + 1) ≤
          Real.sqrt 3 * Real.sqrt (k₀ : ℝ) := by
        calc
          Real.sqrt 3 ^ (Nat.log 3 k₀ + 1) =
              Real.sqrt 3 ^ Nat.log 3 k₀ * Real.sqrt 3 := pow_succ _ _
          _ ≤ Real.sqrt (k₀ : ℝ) * Real.sqrt 3 :=
            mul_le_mul_of_nonneg_right hlek (Real.sqrt_nonneg _)
          _ = Real.sqrt 3 * Real.sqrt (k₀ : ℝ) := mul_comm _ _
      linarith
    have hcore := probeMeanSumAlgebra sqrt_two_le_probe le_sqrt_three_probe
      sqrt_three_le_probe hT0 (Real.sqrt_nonneg (k₀ : ℝ)) hgeom
    linarith

theorem probeBandMeanSum (t : ℝ) (k₀ N : ℕ) :
    ∑ r ∈ Finset.range N,
        Real.sqrt (min t ((probeBandLength k₀ r : ℕ) : ℝ)) ≤
      3.7 * Real.sqrt (k₀ : ℝ) := by
  refine le_trans (Finset.sum_le_sum fun r _ => ?_) (probeBandMeanSumRaw k₀ N)
  exact Real.sqrt_le_sqrt (min_le_right _ _)

private theorem eight_mul_add_one_le_pow_three_probe (r : ℕ) :
    3 ≤ r → 8 * r + 1 ≤ 3 ^ r := by
  induction r with
  | zero => omega
  | succ n ih =>
      intro _
      rcases Nat.lt_or_ge n 3 with h | h
      · have hn : n = 2 := by omega
        subst hn
        norm_num
      · have hih := ih h
        have h3 := pow_three_succ_probe n
        omega

private theorem probeLeOfPowEightLe {q : ℝ} (h : q ^ 8 ≤ 1 / 9) :
    q ≤ 0.76 := by
  by_contra hcon
  push Not at hcon
  have hb : (0.76 : ℝ) ^ 8 ≤ q ^ 8 :=
    pow_le_pow_left₀ (by norm_num) hcon.le 8
  norm_num at hb
  linarith

private theorem probeGainSumCore {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.76) (N : ℕ) :
    ∑ r ∈ Finset.range N, Real.sqrt 3 ^ r * q ^ (3 ^ r - 1) ≤ 2.35 := by
  have hq1 : q ≤ 1 := by linarith
  have hq2 : q ^ 2 ≤ 0.578 := by
    have h := pow_le_pow_left₀ hq0 hq 2
    calc q ^ 2 ≤ (0.76 : ℝ) ^ 2 := h
      _ ≤ 0.578 := by norm_num
  have hq8 : q ^ 8 ≤ 0.112 := by
    have h := pow_le_pow_left₀ hq0 hq 8
    calc q ^ 8 ≤ (0.76 : ℝ) ^ 8 := h
      _ ≤ 0.112 := by norm_num
  have hq8nn : 0 ≤ q ^ 8 := pow_nonneg hq0 8
  have hgnn : ∀ r : ℕ, 0 ≤ Real.sqrt 3 ^ r * q ^ (3 ^ r - 1) :=
    fun r => by positivity
  have h3sum :
      ∑ r ∈ Finset.range 3, Real.sqrt 3 ^ r * q ^ (3 ^ r - 1) ≤ 2.34 := by
    have e2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hb1 : Real.sqrt 3 * q ^ 2 ≤ 1.733 * 0.578 := by
      have ha : Real.sqrt 3 * q ^ 2 ≤ 1.733 * q ^ 2 :=
        mul_le_mul_of_nonneg_right sqrt_three_le_probe (pow_nonneg hq0 2)
      have hb : (1.733 : ℝ) * q ^ 2 ≤ 1.733 * 0.578 :=
        mul_le_mul_of_nonneg_left hq2 (by norm_num)
      linarith
    have hb2 : (3 : ℝ) * q ^ 8 ≤ 3 * 0.112 := by linarith
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num [e2]
    linarith
  rcases le_or_gt N 3 with hN | hN
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hN)
      (fun i _ _ => hgnn i)).trans (by linarith)
  · obtain ⟨K, rfl⟩ : ∃ K, N = 3 + K := ⟨N - 3, by omega⟩
    rw [Finset.sum_range_add]
    have hrho0 : 0 ≤ Real.sqrt 3 * q ^ 8 := by positivity
    have hrho : Real.sqrt 3 * q ^ 8 ≤ 0.195 := by
      have ha : Real.sqrt 3 * q ^ 8 ≤ 1.733 * q ^ 8 :=
        mul_le_mul_of_nonneg_right sqrt_three_le_probe hq8nn
      have hb : (1.733 : ℝ) * q ^ 8 ≤ 1.733 * 0.112 :=
        mul_le_mul_of_nonneg_left hq8 (by norm_num)
      linarith
    have hterm : ∀ x ∈ Finset.range K,
        Real.sqrt 3 ^ (3 + x) * q ^ (3 ^ (3 + x) - 1) ≤
          (0.195 : ℝ) ^ 3 * (0.195 : ℝ) ^ x := by
      intro x _
      have hexp : 8 * (3 + x) ≤ 3 ^ (3 + x) - 1 := by
        have h := eight_mul_add_one_le_pow_three_probe (3 + x) (by omega)
        omega
      have h1 : q ^ (3 ^ (3 + x) - 1) ≤ q ^ (8 * (3 + x)) :=
        pow_le_pow_of_le_one hq0 hq1 hexp
      calc
        Real.sqrt 3 ^ (3 + x) * q ^ (3 ^ (3 + x) - 1)
            ≤ Real.sqrt 3 ^ (3 + x) * q ^ (8 * (3 + x)) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (Real.sqrt_nonneg _) _)
        _ = (Real.sqrt 3 * q ^ 8) ^ (3 + x) := by rw [pow_mul, ← mul_pow]
        _ ≤ (0.195 : ℝ) ^ (3 + x) := pow_le_pow_left₀ hrho0 hrho _
        _ = (0.195 : ℝ) ^ 3 * (0.195 : ℝ) ^ x := by rw [pow_add]
    have hS : (∑ x ∈ Finset.range K, (0.195 : ℝ) ^ x) * ((0.195 : ℝ) - 1) =
        (0.195 : ℝ) ^ K - 1 := geom_sum_mul_sub_one_probe _ K
    have hKnn : 0 ≤ (0.195 : ℝ) ^ K := by positivity
    have hSle : (∑ x ∈ Finset.range K, (0.195 : ℝ) ^ x) ≤ 1.243 := by
      linarith
    have htail :
        ∑ x ∈ Finset.range K,
            Real.sqrt 3 ^ (3 + x) * q ^ (3 ^ (3 + x) - 1) ≤ 0.01 := by
      calc
        _ ≤ ∑ x ∈ Finset.range K, (0.195 : ℝ) ^ 3 * (0.195 : ℝ) ^ x :=
          Finset.sum_le_sum hterm
        _ = (0.195 : ℝ) ^ 3 * ∑ x ∈ Finset.range K, (0.195 : ℝ) ^ x := by
          rw [Finset.mul_sum]
        _ ≤ (0.195 : ℝ) ^ 3 * 1.243 :=
          mul_le_mul_of_nonneg_left hSle (by norm_num)
        _ ≤ 0.01 := by norm_num
    linarith

theorem probeBandLength_zero {k₀ : ℕ} (hk₀ : 2 ≤ k₀) :
    probeBandLength k₀ 0 = 2 := by
  unfold probeBandLength
  omega

theorem probeBandGainSum (t : ℝ) (N g₀ : ℕ) {k₀ : ℕ} (hk₀ : 2 ≤ k₀)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.76) :
    ∑ r ∈ Finset.range N,
        Real.sqrt (min t ((probeBandLength k₀ r : ℕ) : ℝ)) *
          q ^ (g₀ + (3 ^ r - 1)) ≤
      3 * (q ^ g₀ * Real.sqrt ((probeBandLength k₀ 0 : ℕ) : ℝ)) := by
  have hg0nn : 0 ≤ q ^ g₀ := pow_nonneg hq0 _
  have hterm : ∀ r ∈ Finset.range N,
      Real.sqrt (min t ((probeBandLength k₀ r : ℕ) : ℝ)) *
          q ^ (g₀ + (3 ^ r - 1)) ≤
        q ^ g₀ * (Real.sqrt 2 * (Real.sqrt 3 ^ r * q ^ (3 ^ r - 1))) := by
    intro r _
    have h1 : Real.sqrt (min t ((probeBandLength k₀ r : ℕ) : ℝ)) ≤
        Real.sqrt 2 * Real.sqrt 3 ^ r :=
      (Real.sqrt_le_sqrt (min_le_right _ _)).trans (sqrt_probeBandLength_le k₀ r)
    have h2 : 0 ≤ q ^ (3 ^ r - 1) := pow_nonneg hq0 _
    calc
      Real.sqrt (min t ((probeBandLength k₀ r : ℕ) : ℝ)) *
            q ^ (g₀ + (3 ^ r - 1)) =
          (Real.sqrt (min t ((probeBandLength k₀ r : ℕ) : ℝ)) *
            q ^ (3 ^ r - 1)) * q ^ g₀ := by rw [pow_add]; ring
      _ ≤ ((Real.sqrt 2 * Real.sqrt 3 ^ r) * q ^ (3 ^ r - 1)) * q ^ g₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) hg0nn
      _ = q ^ g₀ * (Real.sqrt 2 * (Real.sqrt 3 ^ r * q ^ (3 ^ r - 1))) := by ring
  have hL0 : Real.sqrt ((probeBandLength k₀ 0 : ℕ) : ℝ) = Real.sqrt 2 := by
    rw [probeBandLength_zero hk₀]
    norm_num
  have hmain := probeGainSumCore hq0 hq N
  rw [hL0]
  calc
    _ ≤ ∑ r ∈ Finset.range N,
        q ^ g₀ * (Real.sqrt 2 * (Real.sqrt 3 ^ r * q ^ (3 ^ r - 1))) :=
      Finset.sum_le_sum hterm
    _ = (q ^ g₀ * Real.sqrt 2) *
        ∑ r ∈ Finset.range N, Real.sqrt 3 ^ r * q ^ (3 ^ r - 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    _ ≤ (q ^ g₀ * Real.sqrt 2) * 2.35 :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    _ ≤ 3 * (q ^ g₀ * Real.sqrt 2) := by
      have hpos : 0 ≤ q ^ g₀ * Real.sqrt 2 :=
        mul_nonneg hg0nn (Real.sqrt_nonneg 2)
      nlinarith

/-- The gain from one scale in the deep-band estimate. -/
def probeBandUnitGain (d : ℕ) : ℝ := (3 : ℝ) ^ (-(d : ℝ) / 8)

/-- The gain over a block of scales in the deep-band estimate. -/
def probeBandBlockGain (d : ℕ) (g : ℤ) : ℝ :=
  (3 : ℝ) ^ (-(d : ℝ) / 8 * (g : ℝ))

theorem probeBandUnitGain_nonneg (d : ℕ) : 0 ≤ probeBandUnitGain d :=
  Real.rpow_nonneg (by norm_num) _

theorem probeBandBlockGain_natCast (d g : ℕ) :
    probeBandBlockGain d (g : ℤ) = probeBandUnitGain d ^ g := by
  rw [probeBandBlockGain, probeBandUnitGain,
    ← Real.rpow_natCast ((3 : ℝ) ^ (-(d : ℝ) / 8)) g,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1

theorem probeBandUnitGain_le (hd : 2 ≤ d) : probeBandUnitGain d ≤ 0.76 := by
  refine probeLeOfPowEightLe ?_
  have hpow : probeBandUnitGain d ^ 8 = (3 : ℝ) ^ (-(d : ℝ)) := by
    rw [probeBandUnitGain,
      ← Real.rpow_natCast ((3 : ℝ) ^ (-(d : ℝ) / 8)) 8,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hexp : (3 : ℝ) ^ (-(d : ℝ)) ≤ (3 : ℝ) ^ (-(2 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hval : (3 : ℝ) ^ (-(2 : ℝ)) = 1 / 9 := by
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [hpow]
  exact hexp.trans_eq hval

/-- The dimension-dependent mean amplitude for the deep-band estimate. -/
def probeDeepBandMeanAmplitude (d : ℕ) : ℝ :=
  3.7 * deepBandAmplitude d 4

theorem probeDeepBandMeanAmplitude_nonneg (d : ℕ) :
    0 ≤ probeDeepBandMeanAmplitude d := by
  unfold probeDeepBandMeanAmplitude
  exact mul_nonneg (by norm_num) (deepBandAmplitude_nonneg d (by norm_num))

/-- The unnormalized mean budget for a finite deep-band range. -/
def probeDeepBandRawMean (d : ℕ) (gamma : ℝ) (top : ℤ) (k₀ : ℕ) : ℝ :=
  probeDeepBandMeanAmplitude d * Real.sqrt (k₀ : ℝ) *
    (3 : ℝ) ^ (gamma * (top : ℝ))

/-- The fourth-root gain constant used to bound deep-band fluctuations. -/
def probeDeepBandGainRootConst (d : ℕ) : ℝ :=
  streamIncrementLpGainConst d (1 / 2) ^ (4 : ℝ)⁻¹ * deepBandAmplitude d 4

/-- The unnormalized fluctuation budget after the initial depth cutoff. -/
def probeDeepBandRawFluct (d : ℕ) (gamma : ℝ) (top : ℤ) (g₀ : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 *
      (probeBandUnitGain d ^ g₀ * Real.sqrt 2) *
        (3 : ℝ) ^ (gamma * (top : ℝ)))

theorem streamIncrementLpMassHead_fourth_eq_probe (M : ABKModel d)
    {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMassHead M 4 n m ^ (4 : ℝ)⁻¹ =
      deepBandAmplitude d 4 *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
  rw [streamIncrementLpMassHead_rpow_inv M (by norm_num) hnm]
  unfold streamPointScale deepBandAmplitude
  ring

theorem streamIncrementLpGainScale_fourth_eq_probe (M : ABKModel d)
    {n m : ℤ} (hnm : n < m) (l : ℤ) :
    streamIncrementLpGainScale M 4 l n m ^ (4 : ℝ)⁻¹ =
      probeDeepBandGainRootConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)) * probeBandBlockGain d (l - m) := by
  have hC : 0 ≤ streamIncrementLpGainConst d (2 / (4 : ℝ)) :=
    (streamIncrementLpGainConst_pos d _).le
  have hpow : 0 ≤ (3 : ℝ) ^
      (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hH : 0 ≤ streamIncrementLpMassHead M 4 n m :=
    (streamIncrementLpMassHead_pos M (by norm_num) hnm).le
  have hblock :
      ((3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) ^ (4 : ℝ)⁻¹ =
        probeBandBlockGain d (l - m) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    unfold probeBandBlockGain
    congr 1
    push_cast
    ring
  rw [streamIncrementLpGainScale,
    Real.mul_rpow (mul_nonneg hC hpow) hH,
    Real.mul_rpow hC hpow,
    streamIncrementLpMassHead_fourth_eq_probe M hnm, hblock]
  unfold probeDeepBandGainRootConst
  norm_num
  ring

theorem three_rpow_gamma_probeBandIndex_le {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (top : ℤ) (k₀ r : ℕ) :
    (3 : ℝ) ^ (gamma * (probeBandIndex top k₀ r : ℝ)) ≤
      (3 : ℝ) ^ (gamma * (top : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h : (probeBandIndex top k₀ r : ℝ) ≤ (top : ℝ) := by
    exact_mod_cast probeBandIndex_le top k₀ r
  exact mul_le_mul_of_nonneg_left h hgamma

theorem sum_probeBandMassHead_fourth_le (M : ABKModel d)
    (top : ℤ) (k₀ N : ℕ) :
    ∑ r ∈ probeBandGroups top k₀ N,
        streamIncrementLpMassHead M 4
            (probeBandIndex top k₀ (r + 1)) (probeBandIndex top k₀ r) ^
          (4 : ℝ)⁻¹ ≤
      probeDeepBandRawMean d M.gamma top k₀ := by
  classical
  let S : Finset ℕ := probeBandGroups top k₀ N
  have hA : 0 ≤ deepBandAmplitude d 4 := deepBandAmplitude_nonneg d (by norm_num)
  have hthree : 0 ≤ (3 : ℝ) ^ (M.gamma * (top : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ r ∈ S,
      streamIncrementLpMassHead M 4
            (probeBandIndex top k₀ (r + 1)) (probeBandIndex top k₀ r) ^
          (4 : ℝ)⁻¹ ≤
        deepBandAmplitude d 4 * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) := by
    intro r hr
    have hlt := (mem_probeBandGroups.1 hr).2
    have hgap : ((probeBandIndex top k₀ r : ℝ) -
        (probeBandIndex top k₀ (r + 1) : ℝ)) =
          ((probeBandLength k₀ r : ℕ) : ℝ) := by
      exact_mod_cast probeBandIndex_sub top k₀ r
    have hsqrtmin :
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ)) =
          Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) := by
      rcases le_total M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ) with h | h
      · rw [min_eq_left h, min_eq_left (Real.sqrt_le_sqrt h)]
      · rw [min_eq_right h, min_eq_right (Real.sqrt_le_sqrt h)]
    rw [streamIncrementLpMassHead_fourth_eq_probe M hlt, hgap]
    rw [hsqrtmin]
    have hanchor := three_rpow_gamma_probeBandIndex_le M.shellPrefix.gamma_pos.le
      top k₀ r
    have hs : 0 ≤ Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) :=
      Real.sqrt_nonneg _
    calc
      deepBandAmplitude d 4 *
          Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (probeBandIndex top k₀ r : ℝ))
          ≤ deepBandAmplitude d 4 *
              Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
                (3 : ℝ) ^ (M.gamma * (top : ℝ)) :=
        mul_le_mul_of_nonneg_left hanchor (mul_nonneg hA hs)
      _ = deepBandAmplitude d 4 * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) := by ring
  calc
    ∑ r ∈ S,
        streamIncrementLpMassHead M 4
            (probeBandIndex top k₀ (r + 1)) (probeBandIndex top k₀ r) ^
          (4 : ℝ)⁻¹
        ≤ ∑ r ∈ S,
            deepBandAmplitude d 4 * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
              Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ r ∈ Finset.range N,
          deepBandAmplitude d 4 * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
            Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro r _ _
      exact mul_nonneg (mul_nonneg hA hthree) (Real.sqrt_nonneg _)
    _ = deepBandAmplitude d 4 * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          ∑ r ∈ Finset.range N,
            Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ deepBandAmplitude d 4 * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          (3.7 * Real.sqrt (k₀ : ℝ)) :=
      mul_le_mul_of_nonneg_left (probeBandMeanSum M.gamma⁻¹ k₀ N)
        (mul_nonneg hA hthree)
    _ = probeDeepBandRawMean d M.gamma top k₀ := by
      unfold probeDeepBandRawMean probeDeepBandMeanAmplitude
      ring

theorem probeBandIndex_of_mem_groups {top : ℤ} {k₀ N r : ℕ}
    (hr : r ∈ probeBandGroups top k₀ N) :
    probeBandIndex top k₀ r = top - ((3 ^ r - 1 : ℕ) : ℤ) := by
  have hlt := (mem_probeBandGroups.1 hr).2
  have hlen : probeBandLength k₀ r ≠ 0 := by
    intro hzero
    have hsub := probeBandIndex_sub top k₀ r
    rw [hzero] at hsub
    omega
  have hclip : ¬k₀ < 3 ^ r := fun hk => hlen (probeBandLength_eq_zero hk)
  have hmin : min (3 ^ r - 1) k₀ = 3 ^ r - 1 := by omega
  rw [probeBandIndex, hmin]

theorem probeDeepBandGainRootConst_nonneg (d : ℕ) :
    0 ≤ probeDeepBandGainRootConst d := by
  unfold probeDeepBandGainRootConst
  exact mul_nonneg
    (Real.rpow_nonneg (streamIncrementLpGainConst_pos d (1 / 2)).le _)
    (deepBandAmplitude_nonneg d (by norm_num))

theorem gammaTriangle_mul_sum_probeBandGain_fourth_le (M : ABKModel d)
    (Q : TriadicCube d) (top : ℤ) (k₀ N g₀ : ℕ) (hk₀ : 2 ≤ k₀)
    (hQ : Q.scale = top + (g₀ : ℤ)) :
    IndependentSums.gammaTriangleConst 2 *
        ∑ r ∈ probeBandGroups top k₀ N,
          streamIncrementLpGainScale M 4 Q.scale
              (probeBandIndex top k₀ (r + 1)) (probeBandIndex top k₀ r) ^
            (4 : ℝ)⁻¹ ≤
      probeDeepBandRawFluct d M.gamma top g₀ := by
  classical
  let S : Finset ℕ := probeBandGroups top k₀ N
  let C : ℝ := probeDeepBandGainRootConst d
  let q : ℝ := probeBandUnitGain d
  have hC : 0 ≤ C := probeDeepBandGainRootConst_nonneg d
  have hq0 : 0 ≤ q := probeBandUnitGain_nonneg d
  have hq : q ≤ 0.76 := probeBandUnitGain_le M.shellPrefix.dimension
  have hthree : 0 ≤ (3 : ℝ) ^ (M.gamma * (top : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ r ∈ S,
      streamIncrementLpGainScale M 4 Q.scale
            (probeBandIndex top k₀ (r + 1)) (probeBandIndex top k₀ r) ^
          (4 : ℝ)⁻¹ ≤
        C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          (Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
            q ^ (g₀ + (3 ^ r - 1))) := by
    intro r hr
    have hlt := (mem_probeBandGroups.1 hr).2
    have hgap : ((probeBandIndex top k₀ r : ℝ) -
        (probeBandIndex top k₀ (r + 1) : ℝ)) =
          ((probeBandLength k₀ r : ℕ) : ℝ) := by
      exact_mod_cast probeBandIndex_sub top k₀ r
    have hsqrtmin :
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((probeBandLength k₀ r : ℕ) : ℝ)) =
          Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) := by
      rcases le_total M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ) with h | h
      · rw [min_eq_left h, min_eq_left (Real.sqrt_le_sqrt h)]
      · rw [min_eq_right h, min_eq_right (Real.sqrt_le_sqrt h)]
    have hcarrier : Q.scale - probeBandIndex top k₀ r =
        ((g₀ + (3 ^ r - 1) : ℕ) : ℤ) := by
      rw [hQ, probeBandIndex_of_mem_groups hr]
      push_cast
      ring
    rw [streamIncrementLpGainScale_fourth_eq_probe M hlt Q.scale, hgap,
      hsqrtmin, hcarrier, probeBandBlockGain_natCast, ← show q = probeBandUnitGain d by rfl,
      ← show C = probeDeepBandGainRootConst d by rfl]
    have hanchor := three_rpow_gamma_probeBandIndex_le M.shellPrefix.gamma_pos.le
      top k₀ r
    have hs : 0 ≤ Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) :=
      Real.sqrt_nonneg _
    have hqn : 0 ≤ q ^ (g₀ + (3 ^ r - 1)) := pow_nonneg hq0 _
    calc
      C * Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (probeBandIndex top k₀ r : ℝ)) *
              q ^ (g₀ + (3 ^ r - 1))
          ≤ C * Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
              (3 : ℝ) ^ (M.gamma * (top : ℝ)) * q ^ (g₀ + (3 ^ r - 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ hqn
        exact mul_le_mul_of_nonneg_left hanchor (mul_nonneg hC hs)
      _ = C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          (Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
            q ^ (g₀ + (3 ^ r - 1))) := by ring
  have hsum :
      ∑ r ∈ S,
          streamIncrementLpGainScale M 4 Q.scale
              (probeBandIndex top k₀ (r + 1)) (probeBandIndex top k₀ r) ^
            (4 : ℝ)⁻¹ ≤
        C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          (3 * (q ^ g₀ * Real.sqrt 2)) := by
    calc
      _ ≤ ∑ r ∈ S,
          C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
            (Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
              q ^ (g₀ + (3 ^ r - 1))) := Finset.sum_le_sum hterm
      _ ≤ ∑ r ∈ Finset.range N,
          C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
            (Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
              q ^ (g₀ + (3 ^ r - 1))) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro r _ _
        exact mul_nonneg (mul_nonneg hC hthree)
          (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hq0 _))
      _ = C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          ∑ r ∈ Finset.range N,
            Real.sqrt (min M.gamma⁻¹ ((probeBandLength k₀ r : ℕ) : ℝ)) *
              q ^ (g₀ + (3 ^ r - 1)) := by
        rw [Finset.mul_sum]
      _ ≤ C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          (3 * (q ^ g₀ * Real.sqrt ((probeBandLength k₀ 0 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (probeBandGainSum M.gamma⁻¹ N g₀ hk₀ hq0 hq)
          (mul_nonneg hC hthree)
      _ = C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          (3 * (q ^ g₀ * Real.sqrt 2)) := by rw [probeBandLength_zero hk₀]; norm_num
  have htri0 : 0 ≤ IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos.le
  calc
    _ ≤ IndependentSums.gammaTriangleConst 2 *
        (C * (3 : ℝ) ^ (M.gamma * (top : ℝ)) *
          (3 * (q ^ g₀ * Real.sqrt 2))) :=
      mul_le_mul_of_nonneg_left hsum htri0
    _ = probeDeepBandRawFluct d M.gamma top g₀ := by
      unfold probeDeepBandRawFluct
      rw [show C = probeDeepBandGainRootConst d by rfl,
        show q = probeBandUnitGain d by rfl]
      ring

theorem cubeStreamIncrementLpNorm_deepBand_groupMeanSplit_probe
    (M : ABKModel d) (Q : TriadicCube d) (ell : ℤ) {k₀ N g₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hN : k₀ < 3 ^ N)
    (hQ : Q.scale = ell + (k₀ : ℤ) + (g₀ : ℤ)) :
    (∀ omega : CutoffSample d,
        cubeStreamIncrementLpNorm 4 Q ell (ell + (k₀ : ℤ)) omega.1 ≤
          probeDeepBandRawMean d M.gamma (ell + (k₀ : ℤ)) k₀ +
            probeDeepBandTail M Q (ell + (k₀ : ℤ)) k₀ N omega) ∧
      IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
        (IndependentSums.gammaSigma 2)
        (probeDeepBandTail M Q (ell + (k₀ : ℤ)) k₀ N)
        (probeDeepBandRawFluct d M.gamma (ell + (k₀ : ℤ)) g₀) ∧
      Measurable (probeDeepBandTail M Q (ell + (k₀ : ℤ)) k₀ N) := by
  obtain ⟨hdom, htail⟩ := cubeStreamIncrementLpNorm_deepBand_groupSplit_probe
    M Q ell hk₀ hN
  refine ⟨fun omega => ?_, ?_, probeDeepBandTail_measurable M Q _ _ _⟩
  · have hmain := hdom omega
    have hmean := sum_probeBandMassHead_fourth_le M (ell + (k₀ : ℤ)) k₀ N
    linarith
  · exact htail.mono_scale
      (gammaTriangle_mul_sum_probeBandGain_fourth_le M Q
        (ell + (k₀ : ℤ)) k₀ N g₀ hk₀ (by omega))

/-! ## 8. The single wave-gauge application -/

/-- The grouped deep-band tail after applying exactly the wave gauge from the
upper ellipticity argument. -/
def probeDeepBandGaugedTail (M : ABKModel d) (Q : TriadicCube d)
    (ell : ℤ) (k₀ N : ℕ) (omega : CutoffSample d) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    probeDeepBandTail M Q (ell + (k₀ : ℤ)) k₀ N omega

theorem probeDeepBandGaugedTail_nonneg (M : ABKModel d) (Q : TriadicCube d)
    (ell : ℤ) (k₀ N : ℕ) (omega : CutoffSample d) :
    0 ≤ probeDeepBandGaugedTail M Q ell k₀ N omega := by
  unfold probeDeepBandGaugedTail
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
    (probeDeepBandTail_nonneg M Q (ell + (k₀ : ℤ)) k₀ N omega)

/-- The exact `Γ₂` scale of the wave-gauged grouped tail. -/
def probeDeepBandGaugedFluct (M : ABKModel d) (ell : ℤ) (k₀ g₀ : ℕ) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    probeDeepBandRawFluct d M.gamma (ell + (k₀ : ℤ)) g₀

/-- Applying the wave gauge once turns the grouped deterministic head into the
exact `waveBandMean` slot, while preserving the `Γ₂` tail certificate. -/
theorem cubeStreamIncrementLpNorm_deepBand_waveGauge_probe
    (M : ABKModel d) (Q : TriadicCube d) (ell : ℤ) {k₀ N g₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hN : k₀ < 3 ^ N)
    (hQ : Q.scale = ell + (k₀ : ℤ) + (g₀ : ℤ)) :
    (∀ omega : CutoffSample d,
        Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
            cubeStreamIncrementLpNorm 4 Q ell (ell + (k₀ : ℤ)) omega.1 ≤
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ +
            probeDeepBandGaugedTail M Q ell k₀ N omega) ∧
      IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
        (IndependentSums.gammaSigma 2)
        (probeDeepBandGaugedTail M Q ell k₀ N)
        (probeDeepBandGaugedFluct M ell k₀ g₀) ∧
      Measurable (probeDeepBandGaugedTail M Q ell k₀ N) := by
  obtain ⟨hdom, htail, hmeas⟩ :=
    cubeStreamIncrementLpNorm_deepBand_groupMeanSplit_probe
      M Q ell hk₀ hN hQ
  let a : ℝ := Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ)))
  have ha : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (by norm_num) _)
  have hthree : (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (((ell + (k₀ : ℤ) : ℤ) : ℝ)) ) =
        (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hmean :
      a * probeDeepBandRawMean d M.gamma (ell + (k₀ : ℤ)) k₀ =
        waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ := by
    dsimp [a]
    unfold probeDeepBandRawMean waveBandMean
    rw [show
      Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
          (probeDeepBandMeanAmplitude d * Real.sqrt (k₀ : ℝ) *
            (3 : ℝ) ^ (M.gamma * (((ell + (k₀ : ℤ) : ℤ) : ℝ))) ) =
        probeDeepBandMeanAmplitude d * Real.sqrt M.gamma * Real.sqrt (k₀ : ℝ) *
          ((3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (((ell + (k₀ : ℤ) : ℤ) : ℝ))) ) by ring]
    rw [hthree]
  refine ⟨fun omega => ?_, ?_, ?_⟩
  · have hscaled := mul_le_mul_of_nonneg_left (hdom omega) ha
    calc
      Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
            cubeStreamIncrementLpNorm 4 Q ell (ell + (k₀ : ℤ)) omega.1
          = a * cubeStreamIncrementLpNorm 4 Q ell (ell + (k₀ : ℤ)) omega.1 := rfl
      _ ≤ a * (probeDeepBandRawMean d M.gamma (ell + (k₀ : ℤ)) k₀ +
            probeDeepBandTail M Q (ell + (k₀ : ℤ)) k₀ N omega) := hscaled
      _ = waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ +
            probeDeepBandGaugedTail M Q ell k₀ N omega := by
        rw [mul_add, hmean]
        rfl
  · simpa [probeDeepBandGaugedTail, probeDeepBandGaugedFluct, a] using!
      htail.const_mul ha
  · unfold probeDeepBandGaugedTail
    exact (measurable_const.mul measurable_const).mul hmeas

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity

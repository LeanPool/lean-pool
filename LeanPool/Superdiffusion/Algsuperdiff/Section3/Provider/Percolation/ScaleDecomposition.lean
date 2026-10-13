/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.ColoredConcentration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.CenteredIndicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# ScaleDecomposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The scale decomposition of the bad event and its per-scale concentration

Step 1 of ABK26's `l.percolation.bound.general` controls the centered density
average

`⨍_{z ∈ □_m ∩ ℤ^d} (1_{B(z)} - ℙ[B(z)])`, where `B(z) = ⋃_{L ∈ ℕ} B_L(z)`,

by decomposing it over the scales `L`.

## A replacement for the printed decomposition

The printed argument sums the *raw* scale events, invoking
`1_{B(z)} ≤ ∑_L 1_{B_L(z)}` and `ℙ[B(z)] ≤ ∑_L ℙ[B_L(z)]`. Those two
inequalities point in *opposite* directions once the centering is subtracted:
they give

`1_{B(z)} - ℙ[B(z)] ≤ ∑_L (1_{B_L(z)} - ℙ[B_L(z)]) + Δ(z)`,
`Δ(z) := ∑_L ℙ[B_L(z)] - ℙ[B(z)] ≥ 0`,

and the deterministic overshoot `Δ(z)`, of size up to `∑_L exp(-T² 3^{aL})`, is
*not* dominated by the target amplitude `C(a^{-1}+(d-a)^{-1}) T^{-1} 3^{-am/2}`,
which tends to `0` as `m → ∞` while `Δ` does not.

The decomposition used here replaces `B_L(z)` by the *first-occurrence* events

`badFirst B L z := B_L(z) \ ⋃_{L' < L} B_{L'}(z)`.

These are pairwise disjoint with union `B(z)`, so both inequalities become
*equalities* and `Δ ≡ 0`; and since `badFirst B L z ⊆ B_L(z)` the tail bound
`ℙ[B_L(z)] ≤ exp(-T² 3^{aL})` is inherited. Crucially the first-occurrence event
is still measurable with respect to `siteSigma B {z} L`, the σ-algebra of the
scales `≤ L` at the single site `z`, so ABK26's finite-range hypothesis at range
`3 ^ L` applies to it verbatim. No hypothesis of the source lemma is used beyond
those already present.

## Main definitions

* `badUnion`: ABK26's `B(z)` of `e.badevent.decomp`.
* `badFirst`: the first-occurrence refinement of the scale decomposition.
* `centeredScale`, `centeredUnion`: the centered indicators.
* `scaleAverage`, `densityAverage`: the cube averages of ABK26 Step 1.
* `colorScale`: the colouring cost factor produced by
  `isBigO_gammaSigma_average_of_separatedIndep`.

## Main results

* `tsum_scaleAverage`: `∑'_L scaleAverage L = densityAverage`, the exact scale
  decomposition.
* `densityAverage_le_tsum_abs_scaleAverage`: the signed series is dominated by
  the absolutely convergent series of absolute values, which is the form the
  countable triangle inequality consumes.
* `isBigO_gammaSigma_scaleAverage`: the per-scale estimate.

## References

* ABK26, Lemma `l.percolation.bound.general`, Step 1.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ### The scale decomposition -/

/-- ABK26, `e.badevent.decomp`: `B(z) := ⋃_{L ∈ ℕ} B_L(z)`. -/
def badUnion (B : ℕ → (Fin d → ℤ) → Set Ω) (z : Fin d → ℤ) : Set Ω := ⋃ L, B L z

/-- The first-occurrence refinement of the scale decomposition: the event that
`B_L(z)` occurs and no `B_{L'}(z)` with `L' < L` does. -/
def badFirst (B : ℕ → (Fin d → ℤ) → Set Ω) (L : ℕ) (z : Fin d → ℤ) : Set Ω :=
  B L z \ ⋃ L' ∈ Set.Iio L, B L' z

theorem badFirst_subset (B : ℕ → (Fin d → ℤ) → Set Ω) (L : ℕ) (z : Fin d → ℤ) :
    badFirst B L z ⊆ B L z := Set.sdiff_subset

theorem mem_badFirst_iff {B : ℕ → (Fin d → ℤ) → Set Ω} {L : ℕ} {z : Fin d → ℤ} {ω : Ω} :
    ω ∈ badFirst B L z ↔ ω ∈ B L z ∧ ∀ L' < L, ω ∉ B L' z := by
  simp [badFirst]

theorem mem_badUnion_iff {B : ℕ → (Fin d → ℤ) → Set Ω} {z : Fin d → ℤ} {ω : Ω} :
    ω ∈ badUnion B z ↔ ∃ L, ω ∈ B L z := by
  simp [badUnion]

/-- The first-occurrence event at scale `L` is localised at the single site `z`
and involves only the scales `≤ L`. -/
theorem measurableSet_badFirst_siteSigma (B : ℕ → (Fin d → ℤ) → Set Ω) (L : ℕ)
    (z : Fin d → ℤ) :
    MeasurableSet[siteSigma B ({z} : Set (Fin d → ℤ)) L] (badFirst B L z) := by
  have hL : MeasurableSet[siteSigma B ({z} : Set (Fin d → ℤ)) L] (B L z) :=
    MeasurableSpace.measurableSet_generateFrom ⟨L, le_rfl, z, rfl, rfl⟩
  have hlt : MeasurableSet[siteSigma B ({z} : Set (Fin d → ℤ)) L]
      (⋃ L' ∈ Set.Iio L, B L' z) :=
    MeasurableSet.biUnion (Set.to_countable _) fun L' hL' =>
      MeasurableSpace.measurableSet_generateFrom ⟨L', le_of_lt hL', z, rfl, rfl⟩
  exact hL.diff hlt

theorem pairwise_disjoint_badFirst (B : ℕ → (Fin d → ℤ) → Set Ω) (z : Fin d → ℤ) :
    Pairwise (Function.onFun Disjoint fun L => badFirst B L z) := by
  intro L L' hne
  rw [Function.onFun, Set.disjoint_left]
  intro ω hω hω'
  rcases lt_or_gt_of_ne hne with h | h
  · exact (mem_badFirst_iff.mp hω').2 L h (mem_badFirst_iff.mp hω).1
  · exact (mem_badFirst_iff.mp hω).2 L' h (mem_badFirst_iff.mp hω').1

theorem iUnion_badFirst (B : ℕ → (Fin d → ℤ) → Set Ω) (z : Fin d → ℤ) :
    ⋃ L, badFirst B L z = badUnion B z := by
  classical
  ext ω
  simp only [Set.mem_iUnion, mem_badUnion_iff]
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, (mem_badFirst_iff.mp hL).1⟩
  · rintro ⟨L, hL⟩
    have hex : ∃ L, ω ∈ B L z := ⟨L, hL⟩
    exact ⟨Nat.find hex,
      mem_badFirst_iff.mpr ⟨Nat.find_spec hex, fun L' hL' => Nat.find_min hex hL'⟩⟩

theorem exists_mem_badFirst {B : ℕ → (Fin d → ℤ) → Set Ω} {z : Fin d → ℤ} {ω : Ω}
    (h : ω ∈ badUnion B z) : ∃ L, ω ∈ badFirst B L z := by
  rw [← iUnion_badFirst] at h
  exact Set.mem_iUnion.mp h

theorem notMem_badFirst_of_notMem_badUnion {B : ℕ → (Fin d → ℤ) → Set Ω}
    {z : Fin d → ℤ} {ω : Ω} (h : ω ∉ badUnion B z) (L : ℕ) : ω ∉ badFirst B L z :=
  fun hcon => h (mem_badUnion_iff.mpr ⟨L, (mem_badFirst_iff.mp hcon).1⟩)

theorem summable_indicator_badFirst (B : ℕ → (Fin d → ℤ) → Set Ω) (z : Fin d → ℤ)
    (ω : Ω) : Summable fun L => (badFirst B L z).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  by_cases hmem : ω ∈ badUnion B z
  · obtain ⟨L₀, hL₀⟩ := exists_mem_badFirst hmem
    refine summable_of_ne_finset_zero (s := {L₀}) fun L hL => ?_
    refine Set.indicator_of_notMem (fun hcon => ?_) _
    exact Set.disjoint_left.mp
      (pairwise_disjoint_badFirst B z (Finset.notMem_singleton.mp hL)) hcon hL₀
  · refine summable_of_ne_finset_zero (s := ∅) fun L _ => ?_
    exact Set.indicator_of_notMem (notMem_badFirst_of_notMem_badUnion hmem L) _

theorem tsum_indicator_badFirst (B : ℕ → (Fin d → ℤ) → Set Ω) (z : Fin d → ℤ) (ω : Ω) :
    ∑' L, (badFirst B L z).indicator (fun _ => (1 : ℝ)) ω =
      (badUnion B z).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  by_cases hmem : ω ∈ badUnion B z
  · obtain ⟨L₀, hL₀⟩ := exists_mem_badFirst hmem
    have hzero : ∀ L, L ≠ L₀ → (badFirst B L z).indicator (fun _ => (1 : ℝ)) ω = 0 := by
      intro L hL
      refine Set.indicator_of_notMem (fun hcon => ?_) _
      exact Set.disjoint_left.mp (pairwise_disjoint_badFirst B z hL) hcon hL₀
    rw [tsum_eq_single L₀ hzero, Set.indicator_of_mem hL₀, Set.indicator_of_mem hmem]
  · have hzero : ∀ L, (badFirst B L z).indicator (fun _ => (1 : ℝ)) ω = 0 := fun L =>
      Set.indicator_of_notMem (notMem_badFirst_of_notMem_badUnion hmem L) _
    rw [Set.indicator_of_notMem hmem]
    simp [hzero]

section Measure

variable [MeasurableSpace Ω] {μ : Measure Ω}

theorem measurableSet_badFirst {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (L : ℕ) (z : Fin d → ℤ) :
    MeasurableSet (badFirst B L z) :=
  (hB L z).diff (MeasurableSet.biUnion (Set.to_countable _) fun L' _ => hB L' z)


theorem summable_measureReal_badFirst [IsFiniteMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (z : Fin d → ℤ) :
    Summable fun L => μ.real (badFirst B L z) := by
  refine ENNReal.summable_toReal ?_
  rw [← measure_iUnion (μ := μ) (pairwise_disjoint_badFirst B z)
    fun L => measurableSet_badFirst hB L z]
  exact measure_ne_top μ _

theorem tsum_measureReal_badFirst [IsFiniteMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (z : Fin d → ℤ) :
    ∑' L, μ.real (badFirst B L z) = μ.real (badUnion B z) := by
  have hmeas := measure_iUnion (μ := μ) (pairwise_disjoint_badFirst B z)
    fun L => measurableSet_badFirst hB L z
  rw [iUnion_badFirst] at hmeas
  show ∑' L, (μ (badFirst B L z)).toReal = (μ (badUnion B z)).toReal
  rw [hmeas, ENNReal.tsum_toReal_eq fun L => measure_ne_top μ _]

/-! ### Centered indicators -/

/-- The centered indicator of the first-occurrence event at scale `L`. -/
def centeredScale (B : ℕ → (Fin d → ℤ) → Set Ω) (μ : Measure Ω) (L : ℕ)
    (z : Fin d → ℤ) : Ω → ℝ :=
  fun ω => (badFirst B L z).indicator (fun _ => (1 : ℝ)) ω - μ.real (badFirst B L z)

/-- The centered indicator of `B(z)`: the summand of ABK26's density average. -/
def centeredUnion (B : ℕ → (Fin d → ℤ) → Set Ω) (μ : Measure Ω) (z : Fin d → ℤ) :
    Ω → ℝ :=
  fun ω => (badUnion B z).indicator (fun _ => (1 : ℝ)) ω - μ.real (badUnion B z)

theorem summable_abs_centeredScale [IsFiniteMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (z : Fin d → ℤ) (ω : Ω) :
    Summable fun L => |centeredScale B μ L z ω| := by
  refine Summable.of_nonneg_of_le (fun L => abs_nonneg _) (fun L => ?_)
    ((summable_indicator_badFirst B z ω).add
      (summable_measureReal_badFirst (μ := μ) hB z))
  refine le_trans (abs_sub _ _) (le_of_eq ?_)
  rw [abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω),
    abs_of_nonneg (measureReal_nonneg (μ := μ) (s := badFirst B L z))]

theorem summable_centeredScale [IsFiniteMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (z : Fin d → ℤ) (ω : Ω) :
    Summable fun L => centeredScale B μ L z ω :=
  Summable.of_abs (summable_abs_centeredScale (μ := μ) hB z ω)

theorem tsum_centeredScale [IsFiniteMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (z : Fin d → ℤ) (ω : Ω) :
    ∑' L, centeredScale B μ L z ω = centeredUnion B μ z ω := by
  show ∑' L, ((badFirst B L z).indicator (fun _ => (1 : ℝ)) ω -
      μ.real (badFirst B L z)) = _
  rw [Summable.tsum_sub (summable_indicator_badFirst B z ω)
      (summable_measureReal_badFirst (μ := μ) hB z),
    tsum_indicator_badFirst, tsum_measureReal_badFirst (μ := μ) hB]
  rfl

theorem measurable_centeredScale {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (L : ℕ) (z : Fin d → ℤ) :
    Measurable (centeredScale B μ L z) :=
  (measurable_const.indicator (measurableSet_badFirst hB L z)).sub measurable_const

theorem measurable_centeredScale_siteSigma (B : ℕ → (Fin d → ℤ) → Set Ω) (μ : Measure Ω)
    (L : ℕ) (z : Fin d → ℤ) :
    Measurable[siteSigma B ({z} : Set (Fin d → ℤ)) L] (centeredScale B μ L z) :=
  (measurable_const.indicator (measurableSet_badFirst_siteSigma B L z)).sub measurable_const

theorem integral_centeredScale_eq_zero [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (L : ℕ) (z : Fin d → ℤ) :
    ∫ ω, centeredScale B μ L z ω ∂μ = 0 := by
  have hmeas := measurableSet_badFirst hB L z
  have hint : Integrable ((badFirst B L z).indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hmeas
  show ∫ ω, ((badFirst B L z).indicator (fun _ => (1 : ℝ)) ω -
    μ.real (badFirst B L z)) ∂μ = 0
  rw [integral_sub hint (integrable_const _), integral_indicator_const (1 : ℝ) hmeas,
    integral_const]
  simp

/-! ### The cube averages -/

/-- The per-scale cube average of ABK26 Step 1. -/
def scaleAverage (B : ℕ → (Fin d → ℤ) → Set Ω) (μ : Measure Ω) (L m : ℕ) : Ω → ℝ :=
  fun ω => ((cubeFinset (d := d) m).card : ℝ)⁻¹ *
    ∑ z ∈ cubeFinset m, centeredScale B μ L z ω

/-- ABK26's centered density average `⨍_{z ∈ □_m ∩ ℤ^d} (1_{B(z)} - ℙ[B(z)])`. -/
def densityAverage (B : ℕ → (Fin d → ℤ) → Set Ω) (μ : Measure Ω) (m : ℕ) : Ω → ℝ :=
  fun ω => ((cubeFinset (d := d) m).card : ℝ)⁻¹ *
    ∑ z ∈ cubeFinset m, centeredUnion B μ z ω

theorem summable_abs_scaleAverage [IsFiniteMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (m : ℕ) (ω : Ω) :
    Summable fun L => |scaleAverage B μ L m ω| := by
  have hmaj : Summable fun L => ((cubeFinset (d := d) m).card : ℝ)⁻¹ *
      ∑ z ∈ cubeFinset m, |centeredScale B μ L z ω| :=
    Summable.mul_left _ (summable_sum fun z (_ : z ∈ cubeFinset (d := d) m) =>
      summable_abs_centeredScale (μ := μ) hB z ω)
  refine Summable.of_nonneg_of_le (fun L => abs_nonneg _) (fun L => ?_) hmaj
  show |((cubeFinset (d := d) m).card : ℝ)⁻¹ *
      ∑ z ∈ cubeFinset m, centeredScale B μ L z ω| ≤
    ((cubeFinset (d := d) m).card : ℝ)⁻¹ *
      ∑ z ∈ cubeFinset m, |centeredScale B μ L z ω|
  rw [abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((cubeFinset (d := d) m).card : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- **The exact scale decomposition.** With the first-occurrence events the
density average is the *sum* of the per-scale averages, with no deterministic
overshoot. -/
theorem tsum_scaleAverage [IsFiniteMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (m : ℕ) (ω : Ω) :
    ∑' L, scaleAverage B μ L m ω = densityAverage B μ m ω := by
  show ∑' L, ((cubeFinset (d := d) m).card : ℝ)⁻¹ *
      ∑ z ∈ cubeFinset m, centeredScale B μ L z ω = _
  rw [tsum_mul_left,
    Summable.tsum_finsetSum fun z _ => summable_centeredScale (μ := μ) hB z ω]
  show _ = ((cubeFinset (d := d) m).card : ℝ)⁻¹ *
    ∑ z ∈ cubeFinset m, centeredUnion B μ z ω
  exact congrArg _ (Finset.sum_congr rfl fun z _ => tsum_centeredScale (μ := μ) hB z ω)

/-- The signed decomposition is dominated by the absolutely convergent series of
absolute values. This is the step that lets the ABK26 countable triangle
inequality — which requires nonnegative summands — be applied to a *signed*
scale decomposition. -/
theorem densityAverage_le_tsum_abs_scaleAverage [IsFiniteMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y)) (m : ℕ) (ω : Ω) :
    densityAverage B μ m ω ≤ ∑' L, |scaleAverage B μ L m ω| := by
  rw [← tsum_scaleAverage (μ := μ) hB m ω]
  exact Summable.tsum_le_tsum (fun L => le_abs_self _)
    (Summable.of_abs (summable_abs_scaleAverage (μ := μ) hB m ω))
    (summable_abs_scaleAverage (μ := μ) hB m ω)

/-! ### The per-scale estimate -/

/-- The colouring cost factor at scale `L` for the cube `□_m`, as produced by
`isBigO_gammaSigma_average_of_separatedIndep`. -/
def colorScale (d m L : ℕ) : ℝ :=
  gammaTriangleConst 2 * HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst 2 *
    (Real.sqrt (min (((3 ^ L + 1) ^ d : ℕ) : ℝ) (((cubeFinset (d := d) m).card : ℝ))) *
      (Real.sqrt ((cubeFinset (d := d) m).card : ℝ) /
        ((cubeFinset (d := d) m).card : ℝ)))

/-- **The per-scale estimate of ABK26 Step 1**.

If every bad event at scale `L` has probability at most `exp(-A^{-2})` with
`0 < A ≤ 1`, then the scale-`L` cube average is `O_{Γ₂}` at the colouring scale
times `2A`. At the ABK26 call site `A = T^{-1} 3^{-aL/2}`, so that
`A^{-2} = T² 3^{aL}`. -/
theorem isBigO_gammaSigma_scaleAverage [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {m L : ℕ} {A : ℝ}
    (hB : ∀ (l : ℕ) (y : Fin d → ℤ), MeasurableSet (B l y))
    (hindep : ∀ S S' : Set (Fin d → ℤ), (∀ u ∈ S, ∀ v ∈ S', 3 ^ L < latDist u v) →
      Indep (siteSigma B S L) (siteSigma B S' L) μ)
    (hA : 0 < A) (hA1 : A ≤ 1)
    (htail : ∀ z : Fin d → ℤ, μ.real (B L z) ≤ Real.exp (-(A ^ (-(2 : ℝ))))) :
    IsBigO μ (gammaSigma 2) (scaleAverage B μ L m) (colorScale d m L * (2 * A)) := by
  refine isBigO_gammaSigma_average_of_separatedIndep hindep (cubeFinset_nonempty m)
    (by norm_num) (by norm_num) (by positivity)
    (fun z _ => measurable_centeredScale_siteSigma B μ L z)
    (fun z => measurable_centeredScale hB L z) (fun z _ => ?_)
    fun z _ => integral_centeredScale_eq_zero hB L z
  exact Orlicz.isBigO_gammaSigma_two_indicator_sub_measureReal hA hA1
    (le_trans (measureReal_mono (badFirst_subset B L z) (measure_ne_top μ _)) (htail z))

end Measure

end

end Algsuperdiff.Section3.Provider.Percolation

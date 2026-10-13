/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GeometricSums
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations

/-!
# TruncatedScaleTriangle

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The truncated `Γ_σ` scale triangle and the geometric-weight tail closure

ABK26, `l.Gamma.sigma.triangle` at the *scale sum*: the step that turns
per-layer one-sided tails `W j ≤ O_{Γ_σ}(B j)` into a single tail on the
geometrically weighted layer sum `∑'_j 3^{−sj} W j`. It is the one generic input
the `l.minimal.scale.sep` Step-1 head and the Step-3 below-window legs still
need after the window/geometric arithmetic of
`Algsuperdiff.Probability.GeometricSums` and
`Algsuperdiff.Probability.WindowAmplitudes`.

## Why a *truncated* triangle

The countable triangle in its naive form asks for a genuine pointwise sum
`HasSum (fun j => X j ω) (S ω)` at every `ω`. The layer families of the kicking
lemma do not provide one: an individual sample may be large at infinitely many
layers, so no per-`ω` summability is available before the tails are known. The
route taken here — the one the source itself takes — replaces the pointwise
limit by

* the *uniform* finite triangle on the partial sums `W N = ∑_{L<N} X L` (one
  amplitude, valid for every `N`), and
* an *eventual domination* of the target variable by those partial sums, shifted
  by a deterministic gap `g ≥ 0`:  `c < S ω → ∀ᶠ N, c < W N ω + g`.

The conclusion is one-sided (an `IsBigOWith`, i.e. an upper-tail estimate),
which is exactly what the consumers use.

## No measurability in the limit passage

`measureReal_upperTail_of_uniform_partial` needs **no** measurability at all: the
eventual domination puts the target tail event inside the increasing union of the
sets `U N = {ω | ∀ n ≥ N, W n ω > A t}`, each of which sits inside the `N`-th
partial-sum tail event, and mathlib's continuity from below
(`Monotone.measure_iUnion`) holds for arbitrary — not necessarily measurable —
sets. Measurability re-enters only through the finite triangle input of
`isBigOWith_gammaSigma_scaleTriangle`, which is CoarseGraining's
`isBigO_finset_sum_of_isBigO_gammaSigma` and asks for it on the summands.

## Main results

* `Algsuperdiff.Probability.measureReal_upperTail_of_uniform_partial`
* `Algsuperdiff.Probability.isBigOWith_gammaSigma_of_uniform_partial`
* `Algsuperdiff.Probability.isBigOWith_gammaSigma_scaleTriangle`
* `Algsuperdiff.Probability.partialSum_eventually_gt_of_nonneg`
* `Algsuperdiff.Probability.weightedTsum_isBigOWith_perLayer` — the per-layer
  amplitude closure, the form the Step-1 head and the Step-3 below-window legs
  consume (their amplitude hypotheses are
  `Algsuperdiff.Probability.summable_weight_step3HeadAmp` and
  `Algsuperdiff.Probability.tsum_weight_step3HeadAmp_le`).
* `Algsuperdiff.Probability.weightedTsum_isBigOWith` — the constant-amplitude
  corollary at the geometric closure constant `geomTailConst s`.

## References

* ABK26, `l.Gamma.sigma.triangle` and the scale summation of its Appendix;
* ABK26, `l.minimal.scale.sep` Step 1 and Step 3, the two consumers.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport.IndependentSums

section Truncated

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Truncated one-sided triangle — raw tail form.** Suppose

* every partial-sum surrogate `W N` obeys the *same* upper-tail bound
  `μ.real {A t < W N} ≤ exp(−t^σ)` for `t ≥ 1` (the finite triangle, uniformly
  in `N`);
* `S` is eventually dominated at every threshold:
  `c < S ω → ∀ᶠ N, c < W N ω + g`.

Then `μ.real {A t + g < S} ≤ exp(−t^σ)` for every `t ≥ 1`.

No pointwise summability of `∑_N (W (N+1) − W N)` is required — `W` is an
arbitrary family — and no measurability of `W N` or of `S` either: the passage
to the limit is the purely set-theoretic continuity from below on the increasing
family `{ω | ∀ n ≥ N, A t < W n ω}`. -/
theorem measureReal_upperTail_of_uniform_partial [IsFiniteMeasure μ]
    {W : ℕ → Ω → ℝ} {S : Ω → ℝ} {A g σ : ℝ}
    (huniform : ∀ N, ∀ ⦃t : ℝ⦄, 1 ≤ t →
      μ.real (upperTailEvent (W N) (A * t)) ≤ Real.exp (-(t ^ σ)))
    (hdom : ∀ ω, ∀ ⦃c : ℝ⦄, c < S ω → ∀ᶠ N in Filter.atTop, c < W N ω + g) :
    ∀ ⦃t : ℝ⦄, 1 ≤ t →
      μ.real (upperTailEvent S (A * t + g)) ≤ Real.exp (-(t ^ σ)) := by
  intro t ht
  set c : ℝ := A * t
  set E : ℕ → Set Ω := fun N => upperTailEvent (W N) c
  set U : ℕ → Set Ω := fun N => {ω | ∀ n, N ≤ n → ω ∈ E n}
  have hU_mono : Monotone U := by
    intro N M hNM ω hω n hMn
    exact hω n (hNM.trans hMn)
  -- The eventual domination puts the target tail event inside `⋃ N, U N`.
  have htarget : upperTailEvent S (c + g) ⊆ ⋃ N, U N := by
    intro ω hω
    have hlt : c + g < S ω := hω
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hdom ω hlt)
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    intro n hNn
    show c < W n ω
    have hn : c + g < W n ω + g := hN n hNn
    linarith only [hn]
  have hE_bound : ∀ N, μ (E N) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    intro N
    have htail := huniform N ht
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E N))]
    exact ENNReal.ofReal_le_ofReal htail
  have hU_bound : ∀ N, μ (U N) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    intro N
    refine (measure_mono ?_).trans (hE_bound N)
    intro ω hω
    change ∀ n, N ≤ n → ω ∈ E n at hω
    exact hω N le_rfl
  have hunion : μ (⋃ N, U N) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    rw [hU_mono.measure_iUnion]
    exact iSup_le hU_bound
  have hfinite : μ (upperTailEvent S (c + g)) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) :=
    (measure_mono htarget).trans hunion
  have hreal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hfinite
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  exact hreal

/-- **Truncated one-sided triangle — `IsBigOWith` form.** With the uniform bound
packaged as `W N ≤ O_{Γ_σ}(A)` for every `N` and a deterministic gap `g ≥ 0`, the
eventually dominated variable satisfies `S ≤ O_{Γ_σ}(A + g)`.

The scale is `A + g`, not `A`, because the gap enters the threshold additively;
the conversion uses `A t + g ≤ (A + g) t` for `t ≥ 1`. -/
theorem isBigOWith_gammaSigma_of_uniform_partial [IsFiniteMeasure μ]
    {W : ℕ → Ω → ℝ} {S : Ω → ℝ} {A g σ : ℝ}
    (hg : 0 ≤ g)
    (hWbound : ∀ N, IsBigOWith μ (gammaSigma σ) (W N) A)
    (hdom : ∀ ω, ∀ ⦃c : ℝ⦄, c < S ω → ∀ᶠ N in Filter.atTop, c < W N ω + g) :
    IsBigOWith μ (gammaSigma σ) S (A + g) := by
  have huniform : ∀ N, ∀ ⦃t : ℝ⦄, 1 ≤ t →
      μ.real (upperTailEvent (W N) (A * t)) ≤ Real.exp (-(t ^ σ)) :=
    fun N => isBigOWith_gammaSigma_iff.mp (hWbound N)
  have hcore := measureReal_upperTail_of_uniform_partial
    (μ := μ) (W := W) (S := S) (A := A) (g := g) (σ := σ) huniform hdom
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have hthr : A * t + g ≤ (A + g) * t := by
    have hgt : g ≤ g * t := le_mul_of_one_le_right hg ht
    have hexp : (A + g) * t = A * t + g * t := by ring
    linarith only [hgt, hexp]
  refine le_trans (measureReal_mono ?_) (hcore ht)
  exact upperTailEvent_mono_right hthr

/-- **The truncated countable scale triangle** (`l.Gamma.sigma.triangle` at the
scale sum). Per-layer variables `X L = O_{Γ_σ}(K L)` with summable positive
scales `K` have partial sums obeying the finite triangle at the *`N`-independent*
amplitude `gammaTriangleConst σ · ∑'_L K L`; if a variable `S` is eventually
dominated by those partial sums shifted by a deterministic gap `g ≥ 0`, then

`S ≤ O_{Γ_σ}(gammaTriangleConst σ · ∑'_L K L + g)`  (one-sided).

**No pointwise summability of `∑_L X L ω` is assumed**, and `S` is not required
to be measurable.  Measurability of the *summands* is CoarseGraining's
requirement in `isBigO_finset_sum_of_isBigO_gammaSigma`, whose amplitude is the
only one available uniformly in the truncation level. -/
theorem isBigOWith_gammaSigma_scaleTriangle [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℕ → ℝ} {σ g : ℝ} {S : Ω → ℝ}
    (hσ : 0 < σ)
    (hK : ∀ L, 0 < K L)
    (hKsum : Summable K)
    (hX : ∀ L, IsBigO μ (gammaSigma σ) (X L) (K L))
    (hXm : ∀ L, Measurable (X L))
    (hg : 0 ≤ g)
    (hdom : ∀ ω, ∀ ⦃c : ℝ⦄, c < S ω →
      ∀ᶠ N in Filter.atTop, c < (∑ L ∈ Finset.range N, X L ω) + g) :
    IsBigOWith μ (gammaSigma σ) S (gammaTriangleConst σ * ∑' L, K L + g) := by
  set W : ℕ → Ω → ℝ := fun N ω => ∑ L ∈ Finset.range N, X L ω with hWdef
  set A : ℝ := gammaTriangleConst σ * ∑' L, K L with hAdef
  have htri_pos : 0 < gammaTriangleConst σ := gammaTriangleConst_pos
  have hWbound : ∀ N, IsBigOWith μ (gammaSigma σ) (W N) A := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · -- `W 0 = 0`, and the upper-tail event at a nonnegative threshold is empty.
      subst hN0
      intro t ht
      have hAt_nonneg : 0 ≤ A * t := by
        have htsum : 0 < ∑' L, K L := hKsum.tsum_pos (fun L => (hK L).le) 0 (hK 0)
        have hApos : 0 ≤ A := by rw [hAdef]; exact mul_nonneg htri_pos.le htsum.le
        have ht0 : 0 ≤ t := le_trans zero_le_one ht
        exact mul_nonneg hApos ht0
      have hempty : upperTailEvent (W 0) (A * t) = (∅ : Set Ω) := by
        ext ω
        simp only [hWdef, Finset.range_zero, Finset.sum_empty, upperTailEvent,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact hAt_nonneg
      rw [hempty, measureReal_empty, gammaSigma_inv]
      exact (Real.exp_pos _).le
    · have hne : (Finset.range N).Nonempty := by
        rw [Finset.nonempty_range_iff]
        omega
      have htri :
          IsBigO μ (gammaSigma σ) (W N)
            (gammaTriangleConst σ * ∑ L ∈ Finset.range N, K L) :=
        isBigO_finset_sum_of_isBigO_gammaSigma (μ := μ) (s := Finset.range N)
          (X := X) (a := K) (σ := σ) hσ hne (fun i _ => hK i) (fun i _ => hX i)
          (fun i _ => hXm i)
      have hscale_le : gammaTriangleConst σ * ∑ L ∈ Finset.range N, K L ≤ A := by
        rw [hAdef]
        exact mul_le_mul_of_nonneg_left
          (hKsum.sum_le_tsum (Finset.range N) (fun i _ => (hK i).le)) htri_pos.le
      -- one-sided: `W N ≤ |W N|`.
      exact (htri.mono_scale hscale_le).of_le (fun ω => le_abs_self (W N ω))
  exact isBigOWith_gammaSigma_of_uniform_partial hg hWbound hdom

end Truncated

/-! ## The partial-sum domination of a nonnegative series -/

/-- For a nonnegative series every `c` below the `tsum` is eventually beaten by
the partial sums — including the non-summable case, where the `tsum` is the junk
value `0` and the partial sums are nonnegative. This is the domination input of
the one-sided truncated triangle when the target variable *is* the series. -/
theorem partialSum_eventually_gt_of_nonneg {f : ℕ → ℝ} (h0 : ∀ n, 0 ≤ f n)
    {c : ℝ} (hc : c < ∑' n, f n) :
    ∀ᶠ N in Filter.atTop, c < ∑ n ∈ Finset.range N, f n := by
  by_cases hsum : Summable f
  · exact hsum.hasSum.tendsto_sum_nat.eventually (lt_mem_nhds hc)
  · rw [tsum_eq_zero_of_not_summable hsum] at hc
    exact Filter.Eventually.of_forall fun N =>
      lt_of_lt_of_le hc (Finset.sum_nonneg fun n _ => h0 n)

/-! ## The geometric-weight one-sided closure -/

section Weighted

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The geometric-weight one-sided tail closure amplitudes.** Per-layer one-sided
tails `W j ≤ O_{Γ_σ}(B j)` on nonnegative measurable layers close to a `Γ_σ`
tail on the geometrically weighted layer series at the amplitude
`gammaTriangleConst σ · ∑'_j 3^{−sj} B j`.

The amplitude sequence is **not** required to be uniform, which is what the
Step-1 head and the Step-3 below-window legs need (their per-layer amplitude
grows like `√j`; see `Algsuperdiff.Probability.step3HeadAmp`). Only the weighted
amplitudes must be summable — no pointwise summability of the layer *series* is
assumed. -/
theorem weightedTsum_isBigOWith_perLayer [IsFiniteMeasure μ]
    {W : ℕ → Ω → ℝ} {B : ℕ → ℝ} {s σ : ℝ} (hσ : 0 < σ)
    (hB : ∀ j, 0 < B j)
    (hBsum : Summable (fun j : ℕ => (3 : ℝ) ^ (-(s * (j : ℝ))) * B j))
    (hW0 : ∀ j ω, 0 ≤ W j ω) (hWm : ∀ j, Measurable (W j))
    (hW : ∀ j, IsBigOWith μ (gammaSigma σ) (W j) (B j)) :
    IsBigOWith μ (gammaSigma σ)
      (fun ω => ∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) * W j ω)
      (gammaTriangleConst σ * (∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) * B j)) := by
  set X : ℕ → Ω → ℝ := fun j ω => (3 : ℝ) ^ (-(s * (j : ℝ))) * W j ω
  set K : ℕ → ℝ := fun j => (3 : ℝ) ^ (-(s * (j : ℝ))) * B j
  have hg3 : ∀ j : ℕ, (0 : ℝ) < (3 : ℝ) ^ (-(s * (j : ℝ))) :=
    fun _ => Real.rpow_pos_of_pos (by norm_num) _
  have hX0 : ∀ j ω, 0 ≤ X j ω := fun j ω => mul_nonneg (hg3 j).le (hW0 j ω)
  have hKpos : ∀ j, 0 < K j := fun j => mul_pos (hg3 j) (hB j)
  have hXtail : ∀ j, IsBigO μ (gammaSigma σ) (X j) (K j) := fun j =>
    isBigO_of_isBigOWith_of_nonneg (fun ω => hX0 j ω) ((hW j).const_mul (hg3 j).le)
  have hXm : ∀ j, Measurable (X j) := fun j => (hWm j).const_mul _
  have hdom : ∀ ω, ∀ ⦃c : ℝ⦄, c < (fun ω => ∑' j : ℕ, X j ω) ω →
      ∀ᶠ N in Filter.atTop, c < (∑ L ∈ Finset.range N, X L ω) + 0 := by
    intro ω c hc
    simp only [add_zero]
    exact partialSum_eventually_gt_of_nonneg (fun j => hX0 j ω) hc
  have h := isBigOWith_gammaSigma_scaleTriangle hσ hKpos hBsum hXtail hXm le_rfl hdom
  rw [add_zero] at h
  exact h

/-- **The geometric-weight one-sided tail closure, uniform amplitude.** The
constant-amplitude case `B j := B` of `weightedTsum_isBigOWith_perLayer`, with
the geometric series summed: the closure amplitude is
`gammaTriangleConst σ · geomTailConst s · B`, where
`geomTailConst s = (1 − 3^{−s})⁻¹` by definition. No pointwise summability of the
layer series is assumed. -/
theorem weightedTsum_isBigOWith [IsFiniteMeasure μ]
    {W : ℕ → Ω → ℝ} {B s σ : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hB : 0 < B)
    (hW0 : ∀ j ω, 0 ≤ W j ω) (hWm : ∀ j, Measurable (W j))
    (hW : ∀ j, IsBigOWith μ (gammaSigma σ) (W j) B) :
    IsBigOWith μ (gammaSigma σ)
      (fun ω => ∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) * W j ω)
      (gammaTriangleConst σ * (geomTailConst s * B)) := by
  have hsum : HasSum (fun j : ℕ => (3 : ℝ) ^ (-(s * (j : ℝ))) * B)
      (geomTailConst s * B) := (hasSum_threePow_neg hs).mul_right B
  have h := weightedTsum_isBigOWith_perLayer (μ := μ) (W := W) (B := fun _ => B)
    hσ (fun _ => hB) hsum.summable hW0 hWm hW
  rwa [hsum.tsum_eq] at h

end Weighted

end Algsuperdiff.Probability

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.CenteredIndicator
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle

/-!
# WaveOscillationsCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The random-truncation Orlicz core of `p.bfA.multiscalebound`, Step 2

ABK26, proof of Proposition `p.bfA.multiscalebound`, **Step 2**, assembles the
wave amplitude `||k_ell - k_{ell - hsep}||` out of a *random* number of layers.
The manuscript writes that assembly as the random-index sum

```
  ||k_ell - k_{ell - hsep}||  =  sum_{h = 0}^infty  1_{{hsep = h}} ||k_ell - k_{ell-h}|| ,
```

each summand being an `e.indc.O.sigma` indicator times an increment amplitude,
recombined by `e.multGammasig` and the countable `Gamma_sigma` triangle
inequality.

This module supplies that assembly **abstractly**, in the *layer-decomposed*
shape, over an arbitrary finite measure space and an arbitrary `N`-valued
truncation index.

## Two deliberate changes of form against the manuscript

* **`1_{{i < N}}` in place of `1_{{N = h}}`**.  On a sum of *nonnegative
  per-layer* quantities the two decompositions are the same bookkeeping, `sum_h
  1_{{N = h}} sum_{i < h} Y_i = sum_i 1_{{i < N}} Y_i`, but only the `i`-form
  has *measurable* summands without a measurable handle on the random index
  itself.  Since the countable triangle inequality
  `Provider.Orlicz.isBigOWith_gammaSigma_tsum` demands measurable summands, the
  `i`-form is the only one this tree can carry.
* **The `Gamma_2` factor is the per-layer amplitude**, not a whole increment
  norm.  That is a property of the *consumer* (`WaveOscillations.lean`), but it
  is what makes the abstract statement below usable: the family `Y i` it takes
  is a family of per-layer gauges, whose `Gamma_2` tails are the proved
  single-shell displays.

## Main definitions

* `Algsuperdiff.Section3.Provider.Multiscale.truncationIndicatorScale`: the
  scale `(K 3^{-b i})^{(1-sigma)/sigma_2}` at which `e.indc.O.sigma` prices the
  indicator of `{i < N}`.

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.isBigOWith_gammaSigma_indicator_of_one_le`:
  the trivial branch `1_E <= O_{Gamma_sigma}(A)` for `A >= 1`.
* `Algsuperdiff.Section3.Provider.Multiscale.isBigOWith_gammaSigma_indicator_natLt`:
  **ABK26's `e.indc.O.sigma` at the events `{i < N}`**, derived from the
  `Gamma_{1-sigma}` tail of `3^{b N}`.
* `Algsuperdiff.Section3.Provider.Multiscale.isBigOWith_gammaSigma_truncatedSum`:
  the truncated-sum assembly, `e.multGammasig` termwise followed by the
  countable `Gamma_sigma` triangle inequality.

## References

* ABK26, proof of `p.bfA.multiscalebound`, Step 2.
* ABK26, `e.indc.O.sigma`; `e.multGammasig`; `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-! ## The trivial branch: an indicator against a scale `>= 1` -/

/-- An indicator is `O_{Gamma_sigma}(A)` for **any** `A >= 1`: the tail event
`{1_E > A t}` is empty for `t >= 1`.  This covers the finitely many indices at
which the quantitative `e.indc.O.sigma` scale of
`isBigOWith_gammaSigma_indicator_natLt` already exceeds `1`. -/
theorem isBigOWith_gammaSigma_indicator_of_one_le {sigma A : ℝ} {E : Set Omega}
    (hA : 1 ≤ A) :
    IsBigOWith mu (gammaSigma sigma) (E.indicator fun _ => (1 : ℝ)) A := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have hAt : (1 : ℝ) ≤ A * t := one_le_mul_of_one_le_of_one_le hA ht
  have hempty : upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t) = (∅ : Set Omega) := by
    ext omega
    simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
    by_cases homega : omega ∈ E
    · simpa only [Set.indicator_of_mem homega] using hAt
    · simpa only [Set.indicator_of_notMem homega] using le_trans zero_le_one hAt
  rw [hempty, measureReal_empty]
  positivity

/-! ## `e.indc.O.sigma` at the events `{i < N}` -/

/-- The scale at which `e.indc.O.sigma` prices the indicator of `{i < N}`,
given the `Gamma_{1-sigma}` tail `3^{b N} <= O_{Gamma_{1-sigma}}(K)`:

```
  truncationIndicatorScale b sigma sigma_2 K i  =  (K 3^{-b i})^{(1-sigma)/sigma_2} ,
```

i.e. the manuscript's `C 3^{-(1-sigma) b t h}` at `t = 1/sigma_2`. -/
def truncationIndicatorScale (b sigma sigma2 K : ℝ) (i : ℕ) : ℝ :=
  (K * (3 : ℝ) ^ (-(b * (i : ℝ)))) ^ ((1 - sigma) / sigma2)

theorem truncationIndicatorScale_pos {b sigma sigma2 K : ℝ} (hK : 0 < K) (i : ℕ) :
    0 < truncationIndicatorScale b sigma sigma2 K i :=
  Real.rpow_pos_of_pos (mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _)) _

/-- The exact reciprocal identity behind the pricing:
`(truncationIndicatorScale ...)^{-sigma_2} = (K 3^{-b i})^{-(1-sigma)}`. -/
private theorem truncationIndicatorScale_rpow_neg {b sigma sigma2 K : ℝ}
    (hK : 0 < K) (hsigma2 : sigma2 ≠ 0) (i : ℕ) :
    truncationIndicatorScale b sigma sigma2 K i ^ (-sigma2) =
      (K * (3 : ℝ) ^ (-(b * (i : ℝ)))) ^ (-(1 - sigma)) := by
  have hbase : (0 : ℝ) < K * (3 : ℝ) ^ (-(b * (i : ℝ))) :=
    mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _)
  rw [truncationIndicatorScale, ← Real.rpow_mul hbase.le]
  congr 1
  field_simp

/-- **ABK26's `e.indc.O.sigma` at the truncation events `{i < N}`**.

From the `Gamma_{1-sigma}` tail `3^{b N} <= O_{Gamma_{1-sigma}}(K)`
(the manuscript's `e.hsep.tails`),

```
  1_{{i < N}}  <=  O_{Gamma_{sigma_2}}( (K 3^{-b i})^{(1-sigma)/sigma_2} )     for all i in N,
```

which is the manuscript's `O_{Gamma_{1/t}}(^{-(1-sigma) b t h})` at `t =
1/sigma_2`.  The statement is uniform in `i`: for the finitely many `i` with
`3^{b i} < K` the quantitative branch is unavailable, and there the scale
exceeds `1`, so `isBigOWith_gammaSigma_indicator_of_one_le` applies. -/
theorem isBigOWith_gammaSigma_indicator_natLt [IsFiniteMeasure mu] {N : Omega → ℕ}
    {b sigma sigma2 K : ℝ} (hb : 0 < b) (hsigma2 : 0 < sigma2) (hsigma : 0 < 1 - sigma)
    (hK : 0 < K)
    (htail : IsBigOWith mu (gammaSigma (1 - sigma))
      (fun omega => (3 : ℝ) ^ (b * (N omega : ℝ))) K)
    (i : ℕ) :
    IsBigOWith mu (gammaSigma sigma2)
      ({omega | i < N omega}.indicator fun _ => (1 : ℝ))
      (truncationIndicatorScale b sigma sigma2 K i) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(b * (i : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  have hbase : (0 : ℝ) < K * (3 : ℝ) ^ (-(b * (i : ℝ))) := mul_pos hK h3
  rcases le_or_gt (K * (3 : ℝ) ^ (-(b * (i : ℝ)))) 1 with hle | hgt
  · -- Quantitative branch: `3^{b i} >= K`, so the tail bound is available at
    -- the admissible threshold `t = 3^{b i} / K >= 1`.
    refine Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_indicator_of_le
      hsigma2.le (truncationIndicatorScale_pos hK i) ?_
    rw [truncationIndicatorScale_rpow_neg hK (ne_of_gt hsigma2) i]
    -- the admissible threshold
    set t : ℝ := (K * (3 : ℝ) ^ (-(b * (i : ℝ))))⁻¹ with ht_def
    have ht1 : (1 : ℝ) ≤ t := by
      rw [ht_def, le_inv_comm₀ (by norm_num) hbase]
      simpa using hle
    have htail' := (isBigOWith_gammaSigma_iff.1 htail) ht1
    have hKt : K * t = (3 : ℝ) ^ (b * (i : ℝ)) := by
      rw [ht_def, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hK), one_mul,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), inv_inv]
    have hset : {omega | i < N omega} ⊆
        upperTailEvent (fun omega => (3 : ℝ) ^ (b * (N omega : ℝ))) (K * t) := by
      intro omega homega
      have hlt : (i : ℝ) < (N omega : ℝ) := by exact_mod_cast homega
      rw [mem_upperTailEvent, hKt]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        (mul_lt_mul_of_pos_left hlt hb)
    have hexp : t ^ (1 - sigma) =
        (K * (3 : ℝ) ^ (-(b * (i : ℝ)))) ^ (-(1 - sigma)) := by
      rw [ht_def, Real.inv_rpow hbase.le, Real.rpow_neg hbase.le]
    calc mu.real {omega | i < N omega}
        ≤ mu.real (upperTailEvent (fun omega => (3 : ℝ) ^ (b * (N omega : ℝ))) (K * t)) :=
          measureReal_mono hset (measure_ne_top mu _)
      _ ≤ Real.exp (-(t ^ (1 - sigma))) := htail'
      _ = Real.exp (-((K * (3 : ℝ) ^ (-(b * (i : ℝ)))) ^ (-(1 - sigma)))) := by rw [hexp]
  · -- Trivial branch: the scale already exceeds `1`.
    refine isBigOWith_gammaSigma_indicator_of_one_le ?_
    rw [truncationIndicatorScale]
    exact Real.one_le_rpow hgt.le (by positivity)

/-! ## The truncated-sum assembly -/

/-- **The truncated-sum assembly of Step 2**.

Given a family of nonnegative measurable per-layer variables `Y i` with
`Gamma_{sigma_1}` tails at scales `a i`, and a truncation index `N` whose
indicators `1_{{i < N}}` carry `Gamma_{sigma_2}` tails at scales `B i`, the
randomly truncated sum obeys

```
  sum_{i < N}  Y i  <=  O_{Gamma_tau}( Gamma_triangle(tau) * sum'_i C(sigma_1,sigma_2) a_i B_i ) ,
  tau = sigma_1 sigma_2 / (sigma_1 + sigma_2) .
```

This is `e.multGammasig` applied termwise to `Y i * 1_{{i < N}}`, followed by
the countable `Gamma_sigma` triangle inequality
`Provider.Orlicz.isBigOWith_gammaSigma_tsum`. -/
theorem isBigOWith_gammaSigma_truncatedSum [IsFiniteMeasure mu] {N : Omega → ℕ}
    {Y : ℕ → Omega → ℝ} {a B : ℕ → ℝ} {sigma1 sigma2 : ℝ}
    (hsigma1 : 0 < sigma1) (hsigma2 : 0 < sigma2)
    (hNm : ∀ i : ℕ, MeasurableSet {omega | i < N omega})
    (hYm : ∀ i, Measurable (Y i)) (hY0 : ∀ i omega, 0 ≤ Y i omega)
    (ha : ∀ i, 0 < a i) (hB : ∀ i, 0 < B i)
    (hYO : ∀ i, IsBigOWith mu (gammaSigma sigma1) (Y i) (a i))
    (hBO : ∀ i, IsBigOWith mu (gammaSigma sigma2)
      ({omega | i < N omega}.indicator fun _ => (1 : ℝ)) (B i))
    (hsum : Summable fun i => a i * B i) :
    IsBigOWith mu (gammaSigma (sigma1 * sigma2 / (sigma1 + sigma2)))
      (fun omega => ∑ i ∈ Finset.range (N omega), Y i omega)
      (gammaTriangleConst (sigma1 * sigma2 / (sigma1 + sigma2)) *
        ∑' i, HCPolySupport.Book.Ch04.gammaProductConst sigma1 sigma2 * (a i * B i)) := by
  classical
  set tau : ℝ := sigma1 * sigma2 / (sigma1 + sigma2) with htau_def
  have htau : 0 < tau := by
    rw [htau_def]
    exact div_pos (mul_pos hsigma1 hsigma2) (by linarith)
  have hCprod : (0 : ℝ) < HCPolySupport.Book.Ch04.gammaProductConst sigma1 sigma2 := by
    rw [HCPolySupport.Book.Ch04.gammaProductConst]
    positivity
  set X : ℕ → Omega → ℝ := fun i omega =>
    Y i omega * ({omega | i < N omega}.indicator (fun _ => (1 : ℝ)) omega) with hX_def
  have hX0 : ∀ i omega, 0 ≤ X i omega := fun i omega =>
    mul_nonneg (hY0 i omega) (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  have hXm : ∀ i, Measurable (X i) := fun i =>
    (hYm i).mul (measurable_const.indicator (hNm i))
  have hXO : ∀ i, IsBigOWith mu (gammaSigma tau) (X i)
      (HCPolySupport.Book.Ch04.gammaProductConst sigma1 sigma2 * (a i * B i)) := by
    intro i
    have h := Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_mul_of_nonneg
      hsigma1 hsigma2 (ha i).le (hB i).le (fun omega => hY0 i omega)
      (fun omega => Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
      (hYO i) (hBO i)
    rw [← htau_def] at h
    exact h.mono_scale (le_of_eq (by ring))
  have hsum' : Summable fun i =>
      HCPolySupport.Book.Ch04.gammaProductConst sigma1 sigma2 * (a i * B i) :=
    hsum.mul_left _
  have hpos' : ∀ i,
      (0 : ℝ) < HCPolySupport.Book.Ch04.gammaProductConst sigma1 sigma2 * (a i * B i) :=
    fun i => mul_pos hCprod (mul_pos (ha i) (hB i))
  have htsum := Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum
    (μ := mu) htau hX0 hXm hpos' hsum' hXO
  have hfun : (fun omega => ∑' i, X i omega) =
      fun omega => ∑ i ∈ Finset.range (N omega), Y i omega := by
    funext omega
    refine tsum_eq_sum ?_ |>.trans (Finset.sum_congr rfl fun i hi => ?_)
    · intro i hi
      have hnot : ¬ i < N omega := by simpa using hi
      rw [hX_def]
      simp only [Set.indicator_of_notMem (by simpa using hnot : omega ∉ {omega | i < N omega}),
        mul_zero]
    · have hmem : omega ∈ {omega | i < N omega} := by simpa using Finset.mem_range.1 hi
      rw [hX_def]
      simp only [Set.indicator_of_mem hmem, mul_one]
  rwa [hfun] at htsum

end

end Algsuperdiff.Section3.Provider.Multiscale

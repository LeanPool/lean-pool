/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ShellNorms
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.LargeCubeW1Inf

/-!
# TailGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The deterministic upper-tail gauges of the stream matrix

ABK26 builds its stream matrix from the scale decomposition
`k(x) = Σ_{n ∈ ℤ} j_n(x)`, a sum which does not converge; only the differences
`k(x) - k(y)` converge.  The normalized field `k(x) = Σ_n (j_n(x) - j_n(0))`
does converge, and the two halves converge for different reasons:

* the descending half `n ≤ 0` converges because `‖j_n‖_{L^∞(□_ℓ)}` is of order
  `3^{γ n}`, the content of the lower-tail condition already carried by
  `Algsuperdiff.Section3.Cutoff.CutoffSample`;
* the ascending half `n ≥ 0` converges because `‖∇ j_n‖_{L^∞(□_ℓ)}` is of order
  `3^{(γ-1) n}`, so that `|j_n(x) - j_n(0)| ≤ |x| ‖∇ j_n‖_{L^∞(□_ℓ)}` is
  summable.

This module supplies the deterministic layer of the ascending half: the finite
partial sums of the volume-normalized gradient gauge `‖∇ j_k‖_{W^{1,∞}(y+□_n)}`
of `Algsuperdiff.Section4.Support.shellW1InfGradNorm` on the cubes `y + □_n`,
the two bounded-partial-sum conditions built from them, their measurability, and
the summability and tail bounds they produce.  It asserts nothing probabilistic.

The second condition is quantitative.  A bare summability condition at each
scale gives no rate across scales, and hence no growth bound for the field; the
condition used here weighs scale `ℓ` by `3^{-ℓ}` on the descending leg and by
`3^{ℓ}` on the ascending leg, which is exactly the weighting under which the
`ℓ`-th term has expectation of order `3^{(γ-1) ℓ}`.

## Main definitions

* `lowerValuePartialSum ℓ q ω` — `Σ_{r < q} ‖j_{ℓ-r}‖_{L^∞(□_ℓ)}`.
* `upperGradPartialSum n y q ω` — `Σ_{r < q} ‖∇ j_{n+r}‖_{W^{1,∞}(y+□_n)}`.
* `UpperGradBounded n y ω` — the partial sums of the second family are bounded.
* `StreamGrowthBounded C ω` — the weighted two-leg bound at rate `C 3^{ℓ}`.
* `SharpTailBounded γ C ω` — the two shell gauges obey their sharp scaling
  rates at every integer shell/cube crossover pair, with polynomial power one.

## References

* ABK26, the scale decomposition and the stream matrix.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. The two partial-sum families -/

/-- The descending value partial sum on the origin cube of scale `ℓ`:
`Σ_{r < q} ‖j_{ℓ-r}‖_{L^∞(□_ℓ)}`.  The cube scale and the top shell index
agree, which is the pairing under which the summand has expectation of order
`3^{γ(ℓ-r)} (1+r)^{1/2}`. -/
def lowerValuePartialSum (ell q : ℕ) (omega : CutoffSample d) : ℝ :=
  ∑ r ∈ Finset.range q, localCubeControl (ell : ℤ) (omega.1 ((ell : ℤ) - (r : ℤ)))

/-- The ascending gradient partial sum on `y + □_n`:
`Σ_{r < q} ‖∇ j_{n+r}‖_{W^{1,∞}(y+□_n)}`, in the volume-normalized gauge of
`Algsuperdiff.Section4.Support.shellW1InfGradNorm`.  Reindexed by `k = n + r`
this is the head of the tail sum `Σ_{k ≥ n}` of the large-scale event. -/
def upperGradPartialSum (n : ℤ) (y : Vec d) (q : ℕ) (omega : CutoffSample d) : ℝ :=
  ∑ r ∈ Finset.range q,
    Section4.Support.shellW1InfGradNorm n
      (ShellField.translate y (omega.1 (n + (r : ℤ))))

theorem lowerValuePartialSum_nonneg (ell q : ℕ) (omega : CutoffSample d) :
    0 ≤ lowerValuePartialSum ell q omega :=
  Finset.sum_nonneg fun _ _ => localCubeControl_nonneg _ _

theorem upperGradPartialSum_nonneg (n : ℤ) (y : Vec d) (q : ℕ)
    (omega : CutoffSample d) :
    0 ≤ upperGradPartialSum n y q omega :=
  Finset.sum_nonneg fun _ _ => Section4.Support.shellW1InfGradNorm_nonneg _ _

theorem measurable_upperGradPartialSum (n : ℤ) (y : Vec d) (q : ℕ) :
    Measurable (upperGradPartialSum (d := d) n y q) :=
  Finset.measurable_sum _ fun _ _ =>
    (Section4.Support.measurable_shellW1InfGradNorm n).comp
      ((ShellField.measurable_translate y).comp
        ((measurable_pi_apply _).comp measurable_subtype_coe))

/-! ## 2. The two bounded-partial-sum conditions -/

/-- The ascending gradient series on `y + □_n` has bounded partial sums. -/
def UpperGradBounded (n : ℤ) (y : Vec d) (omega : CutoffSample d) : Prop :=
  ∃ C : ℕ, ∀ q : ℕ, upperGradPartialSum n y q omega ≤ (C : ℝ)

/-- The quantitative two-leg condition at rate `C`: on every origin cube of
nonnegative scale `ℓ`, the descending value series and the ascending gradient
series obey

`Σ_{r} ‖j_{ℓ-r}‖_{L^∞(□_ℓ)} + 3^{2ℓ} Σ_{r} ‖∇ j_{ℓ+r}‖_{W^{1,∞}(□_ℓ)} ≤ C 3^{ℓ}` .

Both legs then contribute at most `C 3^{ℓ}` to the size of the normalized field
on `□_ℓ`: the first directly, the second after the mean value inequality on a
cube of diameter `3^{ℓ}` and the volume normalization `3^{ℓ}` of the gauge. -/
def StreamGrowthBounded (C : ℕ) (omega : CutoffSample d) : Prop :=
  ∀ ell q : ℕ,
    lowerValuePartialSum ell q omega +
        (3 : ℝ) ^ (2 * ell) * upperGradPartialSum (ell : ℤ) 0 q omega ≤
      (C : ℝ) * (3 : ℝ) ^ ell

/-! ## 2a. The sharp two-sided shell rates -/

/-- The polynomial weight used by the sharp all-crossover event.  Its exponent
is one; the additive `2` makes it uniformly positive. -/
def sharpTailWeight (n ell : ℤ) : ℝ :=
  (2 + n.natAbs + ell.natAbs : ℕ)

theorem sharpTailWeight_pos (n ell : ℤ) : 0 < sharpTailWeight n ell := by
  unfold sharpTailWeight
  positivity

/-- The derivative gauge at shell scale `n`, observed on the origin cube of
scale `ell`, normalized back from `largeCubeDerivGauge` to the manuscript's
`W^{1,∞}` rate.  It equals the first-derivative norm plus `3^n` times the
second-derivative norm. -/
def sharpGradientGauge (ell n : ℤ) (omega : CutoffSample d) : ℝ :=
  (3 : ℝ) ^ (-n) *
    Algsuperdiff.Section3.Provider.Stream.largeCubeDerivGauge ell n (omega.1 n)

theorem sharpGradientGauge_eq (ell n : ℤ) (omega : CutoffSample d) :
    sharpGradientGauge ell n omega =
      localCubeDerivNorm ell (omega.1 n) +
        (3 : ℝ) ^ n * localCubeSecondDerivNorm ell (omega.1 n) := by
  rw [sharpGradientGauge,
    Algsuperdiff.Section3.Provider.Stream.largeCubeDerivGauge_eq]
  have hpow : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  calc
    (3 : ℝ) ^ (-n) *
        ((3 : ℝ) ^ n * (localCubeDerivNorm ell (omega.1 n) +
          (3 : ℝ) ^ n * localCubeSecondDerivNorm ell (omega.1 n))) =
      ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ n) *
        (localCubeDerivNorm ell (omega.1 n) +
          (3 : ℝ) ^ n * localCubeSecondDerivNorm ell (omega.1 n)) := by ring
    _ = _ := by rw [hpow, one_mul]

theorem sharpGradientGauge_nonneg (ell n : ℤ) (omega : CutoffSample d) :
    0 ≤ sharpGradientGauge ell n omega :=
  mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) (-n)).le
    (Algsuperdiff.Section3.Provider.Stream.largeCubeDerivGauge_nonneg ell n (omega.1 n))

theorem measurable_sharpGradientGauge (ell n : ℤ) :
    Measurable (sharpGradientGauge (d := d) ell n) :=
  measurable_const.mul
    ((Algsuperdiff.Section3.Provider.Stream.measurable_largeCubeDerivGauge ell n).comp
      ((measurable_pi_apply n).comp measurable_subtype_coe))

/-- The sharp two-sided shell estimate with polynomial power one. -/
def SharpTailBounded (gamma : ℝ) (C : ℕ) (omega : CutoffSample d) : Prop :=
  ∀ n ell : ℤ,
    localCubeControl ell (omega.1 n) ≤
        (C : ℝ) * Real.rpow 3 (gamma * (n : ℝ)) * sharpTailWeight n ell ∧
      sharpGradientGauge ell n omega ≤
        (C : ℝ) * Real.rpow 3 ((gamma - 1) * (n : ℝ)) * sharpTailWeight n ell

/-- Some natural-valued sample constant controls both sharp shell rates. -/
def SharpTailGood (gamma : ℝ) (omega : CutoffSample d) : Prop :=
  ∃ C : ℕ, SharpTailBounded gamma C omega

theorem measurableSet_sharpTailBounded (gamma : ℝ) (C : ℕ) :
    MeasurableSet {omega : CutoffSample d | SharpTailBounded gamma C omega} := by
  have hrw : {omega : CutoffSample d | SharpTailBounded gamma C omega} =
      ⋂ n : ℤ, ⋂ ell : ℤ,
        {omega | localCubeControl ell (omega.1 n) ≤
            (C : ℝ) * Real.rpow 3 (gamma * (n : ℝ)) * sharpTailWeight n ell} ∩
          {omega | sharpGradientGauge ell n omega ≤
            (C : ℝ) * Real.rpow 3 ((gamma - 1) * (n : ℝ)) * sharpTailWeight n ell} := by
    ext omega
    simp only [SharpTailBounded, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_inter_iff]
  rw [hrw]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun ell =>
    (measurableSet_le
      ((measurable_localCubeControl ell).comp
        ((measurable_pi_apply n).comp measurable_subtype_coe)) measurable_const).inter
      (measurableSet_le (measurable_sharpGradientGauge ell n) measurable_const)

theorem measurableSet_sharpTailGood (gamma : ℝ) :
    MeasurableSet {omega : CutoffSample d | SharpTailGood gamma omega} := by
  have hrw : {omega : CutoffSample d | SharpTailGood gamma omega} =
      ⋃ C : ℕ, {omega : CutoffSample d | SharpTailBounded gamma C omega} := by
    ext omega
    simp only [SharpTailGood, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hrw]
  exact MeasurableSet.iUnion fun C => measurableSet_sharpTailBounded gamma C

theorem measurableSet_upperGradBounded (n : ℤ) (y : Vec d) :
    MeasurableSet {omega : CutoffSample d | UpperGradBounded n y omega} := by
  have hrw : {omega : CutoffSample d | UpperGradBounded n y omega} =
      ⋃ C : ℕ, ⋂ q : ℕ, {omega | upperGradPartialSum n y q omega ≤ (C : ℝ)} := by
    ext omega
    simp [UpperGradBounded]
  rw [hrw]
  exact MeasurableSet.iUnion fun C =>
    MeasurableSet.iInter fun q =>
      measurableSet_le (measurable_upperGradPartialSum n y q) measurable_const

/-! ## 3. Summability and tail bounds -/

theorem summable_of_upperGradBounded {n : ℤ} {y : Vec d} {omega : CutoffSample d}
    (h : UpperGradBounded n y omega) :
    Summable fun r : ℕ =>
      Section4.Support.shellW1InfGradNorm n
        (ShellField.translate y (omega.1 (n + (r : ℤ)))) := by
  obtain ⟨C, hC⟩ := h
  refine summable_of_sum_range_le (c := (C : ℝ))
    (fun _ => Section4.Support.shellW1InfGradNorm_nonneg _ _) fun q => ?_
  simpa only [upperGradPartialSum] using hC q

theorem tsum_lowerValue_le_of_streamGrowthBounded {C : ℕ} {omega : CutoffSample d}
    (h : StreamGrowthBounded C omega) (ell : ℕ) :
    (∑' r : ℕ, localCubeControl (ell : ℤ) (omega.1 ((ell : ℤ) - (r : ℤ)))) ≤
      (C : ℝ) * (3 : ℝ) ^ ell := by
  refine Real.tsum_le_of_sum_range_le (fun _ => localCubeControl_nonneg _ _) fun q => ?_
  have hq := h ell q
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * ell) * upperGradPartialSum (ell : ℤ) 0 q omega :=
    mul_nonneg (by positivity) (upperGradPartialSum_nonneg _ _ _ _)
  have := le_trans (le_add_of_nonneg_right hpos) hq
  simpa only [lowerValuePartialSum] using this

/-- The ascending leg of the quantitative condition, read at the origin cube:
the volume-normalized gradient series is bounded by `C 3^{-ℓ}`. -/
theorem upperGradBounded_of_streamGrowthBounded {C : ℕ} {omega : CutoffSample d}
    (h : StreamGrowthBounded C omega) (ell : ℕ) :
    ∀ q : ℕ, upperGradPartialSum (ell : ℤ) 0 q omega ≤ (C : ℝ) * (3 : ℝ) ^ ell / (3 : ℝ) ^ (2 * ell) := by
  intro q
  have hq := h ell q
  have hlow : (0 : ℝ) ≤ lowerValuePartialSum ell q omega :=
    lowerValuePartialSum_nonneg _ _ _
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (2 * ell) := by positivity
  rw [le_div_iff₀ hpow, mul_comm]
  linarith only [hq, hlow]

/-! ## 4. The ascending gradient sums in the raw gauge -/

/-- **The ascending gradient sums on `□_ℓ` are bounded by the sample constant.**
The volume normalization of the gauge divides out `3^{ℓ}` on the first-derivative
leg, and the quantitative condition supplies the remaining `3^{ℓ}`. -/
theorem sum_range_localCubeDerivNorm_le {C : ℕ} {omega : CutoffSample d}
    (hC : StreamGrowthBounded C omega) (ell q : ℕ) :
    ∑ r ∈ Finset.range q,
        localCubeDerivNorm (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ))) ≤ (C : ℝ) := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ ell := by positivity
  have hstep : ∀ r ∈ Finset.range q,
      localCubeDerivNorm (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ))) ≤
        (3 : ℝ) ^ ell *
          Section4.Support.shellW1InfGradNorm (ell : ℤ)
            (omega.1 ((ell : ℤ) + (r : ℤ))) := by
    intro r _
    have h := Section4.Support.three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm
      (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ)))
    have hz : ((3 : ℝ) ^ ((ell : ℕ) : ℤ))⁻¹ = ((3 : ℝ) ^ ell)⁻¹ := by simp
    rw [zpow_neg, hz] at h
    calc localCubeDerivNorm (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ))) =
        (3 : ℝ) ^ ell *
          (((3 : ℝ) ^ ell)⁻¹ *
            localCubeDerivNorm (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ)))) := by
          field_simp
      _ ≤ (3 : ℝ) ^ ell *
            Section4.Support.shellW1InfGradNorm (ell : ℤ)
              (omega.1 ((ell : ℤ) + (r : ℤ))) :=
          mul_le_mul_of_nonneg_left h hpow.le
  have hsum : ∑ r ∈ Finset.range q,
      localCubeDerivNorm (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ))) ≤
        (3 : ℝ) ^ ell * upperGradPartialSum (ell : ℤ) 0 q omega := by
    rw [upperGradPartialSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    simpa only [ShellField.translate_zero] using hstep r hr
  have hub := upperGradBounded_of_streamGrowthBounded hC ell q
  have hpow2 : (0 : ℝ) < (3 : ℝ) ^ (2 * ell) := by positivity
  have hid : (3 : ℝ) ^ ell * ((C : ℝ) * (3 : ℝ) ^ ell / (3 : ℝ) ^ (2 * ell)) = (C : ℝ) := by
    rw [two_mul, pow_add]
    field_simp
  refine hsum.trans ?_
  calc (3 : ℝ) ^ ell * upperGradPartialSum (ell : ℤ) 0 q omega ≤
      (3 : ℝ) ^ ell * ((C : ℝ) * (3 : ℝ) ^ ell / (3 : ℝ) ^ (2 * ell)) :=
        mul_le_mul_of_nonneg_left hub hpow.le
    _ = (C : ℝ) := hid

end

end Algsuperdiff.Section5.Field

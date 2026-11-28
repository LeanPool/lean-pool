/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.DriftProcessPredictable
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoProcessPredictable
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.MetricSpace.Contracting

/-! # SDE existence/uniqueness via Picard on `E` (build)

The strong solution of `dX = b(X)dt + σ(X)dB`, `X₀ = η` is the fixed point of the Picard iterate
`Φ(X)_t = η + ∫₀ᵗ b(X_s) ds + ∫₀ᵗ σ(X_s) dB_s`, built as a self-map of the predictable `L²` space
`E := Lp ℝ 2 (trimMeasure T)`. Both analytic terms already land back in `E` — the drift as a
genuine CLM `driftProcessAssembled : E →L[ℝ] E`, the Itô term as the element-valued linear map
`itoProcessAssembled : E → E` (built from a continuous modification, so *not* a CLM — its linearity
is re-established a.e.). This file wires them into the Picard map, proves the contraction estimate
`‖Φ(X) − Φ(Y)‖ ≤ (T·L_b + √T·L_σ)·‖X − Y‖`, and — when that constant is `< 1` — obtains the **unique
fixed point** (`picardSolution`) via Banach's theorem: existence and uniqueness of the strong
solution in `E`.

The `T` vs `√T` asymmetry is structural: both terms integrate a `[0,t]` quantity over `t ∈ [0,T]`,
but Cauchy–Schwarz already spends a factor of time inside each drift slice (leaving the full `T`),
whereas the Itô isometry bounds each `[0,t]` energy flatly by the total energy (so only `√T`
survives the outer time-integral). The `driftProcessAssembled_norm_le` (`≤ T‖·‖`) and
`itoProcessAssembled_norm_le` (`≤ √T‖·‖`) bounds live with their operators in
`DriftProcessPredictable` / `ItoProcessPredictable`.

* `lipComp` — the coefficient composition `f ∘ X ∈ E` (centered via `lipschitz_sub_const`);
  `lipComp_sub_norm_le` — its `L`-Lipschitz bound.
* `picardMap` — the Picard iterate `Φ : E → E`.
* `picardMap_contraction` — the contraction estimate; `picardMap_contractingWith` — as
  `ContractingWith`.
* `picardSolution` — the strong solution (the fixed point); `picardMap_exists_unique_fixedPoint` —
  `∃!`.

**All horizons.** The smallness condition is removed by iterating: the *band energy*
`bandEnergy T s Z = ∫_{(0,s]×Ω} Z²` of the Picard difference satisfies the Volterra inequality
`bandEnergy s (Φ X − Φ Y) ≤ 2(T L_b² + L_σ²) ∫₀ˢ bandEnergy u (X − Y) du` (the Itô term exactly,
by the Itô isometry on bands; the drift term by Cauchy–Schwarz on simple processes, extended by
density), hence `‖Φⁿ X − Φⁿ Y‖² ≤ (2(T L_b² + L_σ²) T)ⁿ/n! · ‖X − Y‖²`. For large `n` the iterate
`Φⁿ` is a contraction and Mathlib's `ContractingWith.isFixedPt_fixedPoint_iterate` gives the unique
fixed point for every `T` (`picardMap_exists_unique_fixedPoint_any_horizon`). The short-horizon
`picardSolution` is kept: downstream modules consume it with its `ContractingWith` hypothesis.

The remaining bridge to the benchmark `sc-thm-8.2.5` (its `ℝ`-time, pointwise-per-`t`,
`intervalIntegral`-drift, opaque-`Iσ` shape) is the next step.

## Main definitions

* `lipComp`: the composition `f ∘ X ∈ E` of a Lipschitz `f : ℝ → ℝ` with a process `X` in the
  predictable `L²` space `E`, centred at `f 0`.
* `picardMap`: the Picard iterate
  `Φ(X) = η + driftProcessAssembled(b∘X) + itoProcessAssembled(σ∘X)`, a self-map of `E`.
* `picardSolution`: the fixed point of `picardMap` given by Banach's theorem when it is a
  contraction.

* `bandEnergy`: the `L²` mass `∫_{(0,s]×Ω} Z²` of a process of `E` on a time band.
* `picardRate`: the Volterra constant `2(T L_b² + L_σ²)`.

## Main results

* `lipComp_sub_norm_le`: `lipComp` is `L`-Lipschitz in `X` for the `E`-norm.
* `picardMap_contraction`: `‖Φ(X) − Φ(Y)‖ ≤ (T·L_b + √T·L_σ)·‖X − Y‖`.
* `picardMap_contractingWith`: `picardMap` is a contraction on `E` once `T·L_b + √T·L_σ < 1`.
* `picardMap_exists_unique_fixedPoint`: in that regime `picardSolution` is a fixed point of the
  Picard map and the only one in `E`.
* `bandEnergy_itoProcessAssembled`, `bandEnergy_driftProcessAssembled_le`,
  `bandEnergy_picardMap_sub_le`: the band-by-band (Volterra) estimates.
* `picardMap_iterate_norm_sq_le`: `‖Φⁿ X − Φⁿ Y‖² ≤ (2(T L_b² + L_σ²) T)ⁿ/n! · ‖X − Y‖²`.
* `picardMap_exists_unique_fixedPoint_any_horizon`: for every horizon `T`, the Picard map has a
  unique fixed point in `E`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Thm 8.2.5

## Tags

stochastic differential equation, strong solution, Picard iteration, Banach fixed point,
Lipschitz coefficients, existence and uniqueness, MSC 60H10, MSC 60H05
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace SDEExistence
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
  ItoIntegralProcessContinuousModification

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- Centering a Lipschitz coefficient at `0`: `x ↦ f x − f 0` is `L`-Lipschitz and
sends `0 ↦ 0`, so it composes with an `L²` process via `LipschitzWith.compLp`. -/
theorem lipschitz_sub_const {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fun x ↦ f x - f 0) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y

/-- **The coefficient composition** `f ∘ X ∈ E` for a Lipschitz `f : ℝ → ℝ` and a
predictable process `X ∈ E`: `f(0)·1 + (f − f 0)∘X`. The centered part lands in `E` by
`compLp` (predictability is inherited from `E`'s trim measure); the constant `f 0` is
added back as a genuine element of `E` (finite measure). -/
noncomputable def lipComp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (f : ℝ → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (X : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  Lp.const 2 _ (f 0) + (lipschitz_sub_const hf).compLp (by simp) X

/-- **The composition is `L`-Lipschitz in `X`** — the constant `f 0` cancels in the
difference, and `LipschitzWith.norm_compLp_sub_le` bounds the centered part. This is the
per-coefficient Lipschitz factor of the Picard contraction. -/
theorem lipComp_sub_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖lipComp T hBmeas f L hf X - lipComp T hBmeas f L hf Y‖ ≤ (L : ℝ) * ‖X - Y‖ := by
  rw [lipComp, lipComp, add_sub_add_left_eq_sub]
  exact (lipschitz_sub_const hf).norm_compLp_sub_le (by simp) X Y

/-- **The Picard iterate** `Φ(X) = η + driftProcessAssembled(b∘X) + itoProcessAssembled(σ∘X)`,
a self-map of `E`. Its fixed point is the strong solution of the SDE. -/
noncomputable def picardMap (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (X : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  η_E + driftProcessAssembled T hBmeas (lipComp T hBmeas b Lb hb X)
      + itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)

/-- **The Picard difference.** The initial condition cancels, so `Φ(X) − Φ(Y)` is the drift of the
difference `b∘X − b∘Y` plus the Itô term of `σ∘X − σ∘Y`. Both the global contraction estimate
and the pointwise-in-time (band energy) estimates below start from this decomposition. -/
theorem picardMap_sub (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    picardMap hB T hBmeas hBcont hb hσ η_E X - picardMap hB T hBmeas hBcont hb hσ η_E Y
      = driftProcessAssembled (μ := μ) T hBmeas
          (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y)
        + itoProcessAssembled hB T hBmeas hBcont
          (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y) := by
  rw [map_sub (driftProcessAssembled (μ := μ) T hBmeas),
    itoProcessAssembled_sub hB T hBmeas hBcont, picardMap, picardMap]
  abel

/-- **The Picard contraction estimate** `‖Φ(X) − Φ(Y)‖ ≤ (T·L_b + √T·L_σ)·‖X − Y‖`. The
initial condition cancels in the difference; the drift term contributes `T·L_b` (operator
bound `T` × Lipschitz `L_b`), the Itô term `√T·L_σ` (operator bound `√T` × Lipschitz `L_σ`).
For `T` small this constant is `< 1`, giving a contraction. -/
theorem picardMap_contraction (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖picardMap hB T hBmeas hBcont hb hσ η_E X - picardMap hB T hBmeas hBcont hb hσ η_E Y‖
      ≤ ((T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ) * ‖X - Y‖ := by
  rw [picardMap_sub hB T hBmeas hBcont hb hσ η_E X Y]
  calc ‖driftProcessAssembled (μ := μ) T hBmeas
            (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y)
          + itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y)‖
      ≤ ‖driftProcessAssembled (μ := μ) T hBmeas
            (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y)‖
        + ‖itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y)‖ := norm_add_le _ _
    _ ≤ (T : ℝ) * ‖lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y‖
        + Real.sqrt (T : ℝ) * ‖lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y‖ :=
        add_le_add (driftProcessAssembled_norm_le T hBmeas _)
          (itoProcessAssembled_norm_le hB T hBmeas hBcont _)
    _ ≤ (T : ℝ) * ((Lb : ℝ) * ‖X - Y‖) + Real.sqrt (T : ℝ) * ((Lσ : ℝ) * ‖X - Y‖) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (lipComp_sub_norm_le T hBmeas hb X Y) T.coe_nonneg)
          (mul_le_mul_of_nonneg_left (lipComp_sub_norm_le T hBmeas hσ X Y) (Real.sqrt_nonneg _))
    _ = ((T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ) * ‖X - Y‖ := by ring

/-- **The Picard map is a contraction** on `E` once `T·L_b + √T·L_σ < 1` (a smallness
condition on the horizon `T` given the Lipschitz constants). Packages
`picardMap_contraction` as Mathlib's `ContractingWith`. -/
theorem picardMap_contractingWith (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    ContractingWith (Real.toNNReal ((T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ))
      (picardMap hB T hBmeas hBcont hb hσ η_E) := by
  have hc0 : (0 : ℝ) ≤ (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ := by positivity
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun X Y ↦ ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0, NNReal.coe_one]; exact hc
  · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc0]
    exact picardMap_contraction hB T hBmeas hBcont hb hσ η_E X Y

/-- **The strong solution** of the SDE (contraction regime): the unique fixed point of the
Picard map in `E`, from Banach's fixed-point theorem (`ContractingWith.fixedPoint`; `E` is a
complete, nonempty metric space). -/
noncomputable def picardSolution (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint _

/-- **Existence + uniqueness** of the strong solution: `picardSolution` is a fixed point of
the Picard map, and it is the *only* one — the SDE `dX = b(X)dt + σ(X)dB` has a unique
strong solution in `E` under the contraction condition. -/
theorem picardMap_exists_unique_fixedPoint (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    ∃! X, picardMap hB T hBmeas hBcont hb hσ η_E X = X := by
  refine ⟨picardSolution hB T hBmeas hBcont hb hσ η_E hc, ?_, fun Y hY ↦ ?_⟩
  · exact (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint_isFixedPt
  · exact (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint_unique hY

/-! ### Pointwise-in-time (band) energy

The contraction `picardMap_contraction` is global in `T`. To remove the smallness condition we need
its time-localised form: the energy of the Picard difference on the band `(0, s] × Ω` is bounded by
a Volterra integral `∫₀ˢ` of the energy of the input on `(0, u] × Ω`. The band energy is the
quantity the Itô isometry already speaks (`itoProcessCLM_norm_sq`). -/

/-- The **band energy** `∫_{(0,s]×Ω} Z² d(trimMeasure T)` of a predictable `L²` process: its `L²`
mass on the time band `(0, s]`. For `s = T` it is `‖Z‖²`. -/
noncomputable def bandEnergy (T s : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) : ℝ :=
  ∫ z in Set.Ioc 0 s ×ˢ (Set.univ : Set Ω), (Z z) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas)

omit [IsProbabilityMeasure μ] in
theorem bandEnergy_nonneg (T s : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) : 0 ≤ bandEnergy T s hBmeas Z :=
  integral_nonneg fun _ ↦ sq_nonneg _

omit [IsProbabilityMeasure μ] in
theorem monotone_bandEnergy (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Monotone fun s ↦ bandEnergy T s hBmeas Z :=
  fun _ _ h ↦ setIntegral_mono_set (Lp.memLp Z).integrable_sq.integrableOn
    (ae_of_all _ fun _ ↦ sq_nonneg _)
    (ae_of_all _ fun _ hx ↦ Set.prod_mono (Set.Ioc_subset_Ioc_right h) subset_rfl hx)

omit [IsProbabilityMeasure μ] in
theorem bandEnergy_le_norm_sq (T s : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) : bandEnergy T s hBmeas Z ≤ ‖Z‖ ^ 2 := by
  rw [bandEnergy, lp_two_norm_sq]
  exact setIntegral_le_integral (Lp.memLp Z).integrable_sq (ae_of_all _ fun _ ↦ sq_nonneg _)

/-- The trim measure lives on `(0, T] × Ω`, so the band energy at the horizon is the full energy. -/
theorem norm_sq_eq_bandEnergy (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) : ‖Z‖ ^ 2 = bandEnergy T T hBmeas Z := by
  have h : (trimMeasure (μ := μ) T hBmeas).restrict (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
      = trimMeasure (μ := μ) T hBmeas :=
    Measure.restrict_eq_self_of_ae_mem
      ((ae_fst_mem_Ioc_trimMeasure (μ := μ) T hBmeas).mono fun _ hz ↦ ⟨hz, Set.mem_univ _⟩)
  rw [bandEnergy, lp_two_norm_sq, h]

omit [IsProbabilityMeasure μ] in
theorem bandEnergy_add_le (T s : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z W : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    bandEnergy T s hBmeas (Z + W) ≤ 2 * bandEnergy T s hBmeas Z + 2 * bandEnergy T s hBmeas W := by
  have hZ := (Lp.memLp Z).integrable_sq.integrableOn
    (s := Set.Ioc 0 s ×ˢ (Set.univ : Set Ω))
  have hW := (Lp.memLp W).integrable_sq.integrableOn
    (s := Set.Ioc 0 s ×ˢ (Set.univ : Set Ω))
  have hsum : ∫ z in Set.Ioc 0 s ×ˢ (Set.univ : Set Ω), (2 * (Z z) ^ 2 + 2 * (W z) ^ 2)
        ∂(trimMeasure (μ := μ) T hBmeas)
      = 2 * bandEnergy T s hBmeas Z + 2 * bandEnergy T s hBmeas W := by
    rw [integral_add (hZ.const_mul 2) (hW.const_mul 2), integral_const_mul, integral_const_mul,
      bandEnergy, bandEnergy]
  refine le_trans (integral_mono_ae (Lp.memLp (Z + W)).integrable_sq.integrableOn
    ((hZ.const_mul 2).add (hW.const_mul 2)) ?_) hsum.le
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_add Z W)] with z hz
  simp only [hz, Pi.add_apply]
  nlinarith [sq_nonneg (Z z - W z)]

/-- `timeMeasure` restricted to a bounded time-interval `(0, s]` is finite. -/
private instance isFiniteMeasure_timeMeasure_restrict_Ioc_zero (s : ℝ≥0) :
    IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) s)) :=
  inferInstanceAs (IsFiniteMeasure (timeMeasureHorizon s))

omit [IsProbabilityMeasure μ] in
/-- The band energy is a bounded monotone, hence integrable, function of the band edge. -/
theorem integrable_bandEnergy (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (s : ℝ≥0) :
    Integrable (fun u ↦ bandEnergy T u hBmeas Z) (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) s)) :=
  Integrable.of_bound (monotone_bandEnergy T hBmeas Z).measurable.aestronglyMeasurable (‖Z‖ ^ 2)
    (ae_of_all _ fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (bandEnergy_nonneg T u hBmeas Z)]
      exact bandEnergy_le_norm_sq T u hBmeas Z)

/-- Restricting the predictable product to a band `(0, t] × Ω` restricts the time factor. -/
theorem prod_restrict_band (T : ℝ≥0) {t : ℝ≥0} (htT : t ≤ T) :
    ((timeMeasureHorizon T).prod μ).restrict (Set.Ioc (0 : ℝ≥0) t ×ˢ (Set.univ : Set Ω))
      = (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)).prod μ := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, timeMeasureHorizon,
    Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc_right htT)]

/-- **Band energy as a time integral of slices.** For a predictable `L²` process given by a
function `g`, the band energy over `(0, s]` is `∫₀ˢ 𝔼[g_t²] dt`. -/
theorem bandEnergy_toLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {g : ℝ≥0 → Ω → ℝ}
    (hg : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Function.uncurry g))
    (hmem : MemLp (Function.uncurry g) 2 (trimMeasure (μ := μ) T hBmeas)) {s : ℝ≥0}
    (hsT : s ≤ T) :
    bandEnergy T s hBmeas (hmem.toLp _)
      = ∫ t in Set.Ioc (0 : ℝ≥0) s, ∫ ω, (g t ω) ^ 2 ∂μ ∂timeMeasure := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas
  have hband : MeasurableSet[𝓕.predictable] (Set.Ioc (0 : ℝ≥0) s ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 s MeasurableSet.univ
  have hbandP : MeasurableSet (Set.Ioc (0 : ℝ≥0) s ×ˢ (Set.univ : Set Ω)) :=
    MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
  have hint : Integrable (fun z ↦ (Function.uncurry g z) ^ 2) ((timeMeasureHorizon T).prod μ) :=
    (memLp_of_memLp_trim 𝓕.predictable_le_prod hmem).integrable_sq
  have h1 : bandEnergy T s hBmeas (hmem.toLp _)
      = ∫ z in Set.Ioc (0 : ℝ≥0) s ×ˢ (Set.univ : Set Ω), (Function.uncurry g z) ^ 2
          ∂(trimMeasure (μ := μ) T hBmeas) := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hmem.coeFn_toLp] with z hz
    rw [hz]
  have hsm : StronglyMeasurable[𝓕.predictable]
      ((Set.Ioc (0 : ℝ≥0) s ×ˢ (Set.univ : Set Ω)).indicator
        (fun z ↦ (Function.uncurry g z) ^ 2)) :=
    (hg.pow 2).indicator hband
  have h2 : ∫ z in Set.Ioc (0 : ℝ≥0) s ×ˢ (Set.univ : Set Ω), (Function.uncurry g z) ^ 2
        ∂(trimMeasure (μ := μ) T hBmeas)
      = ∫ z in Set.Ioc (0 : ℝ≥0) s ×ˢ (Set.univ : Set Ω), (Function.uncurry g z) ^ 2
        ∂((timeMeasureHorizon T).prod μ) := by
    rw [← integral_indicator hband, ← integral_indicator hbandP]
    exact (integral_trim (μ := (timeMeasureHorizon T).prod μ) 𝓕.predictable_le_prod hsm).symm
  have h3 : ∫ z in Set.Ioc (0 : ℝ≥0) s ×ˢ (Set.univ : Set Ω), (Function.uncurry g z) ^ 2
        ∂((timeMeasureHorizon T).prod μ)
      = ∫ t in Set.Ioc (0 : ℝ≥0) s, ∫ ω, (g t ω) ^ 2 ∂μ ∂timeMeasure := by
    rw [setIntegral_prod _ hint.integrableOn]
    simp only [Measure.restrict_univ, Function.uncurry_apply_pair]
    rw [timeMeasureHorizon, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 (Set.Ioc_subset_Ioc_right hsT)]
  rw [h1, h2, h3]

/-- **The Itô term, band by band.** `‖𝟙_{(0,s]}·(φ●B)‖² = ∫₀ˢ ‖𝟙_{(0,u]}·φ‖² du`: the band energy
of the assembled Itô process is the Volterra integral of the band energy of the integrand
(slice by slice the modification identity plus `itoProcessCLM_norm_sq`). -/
theorem bandEnergy_itoProcessAssembled (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {s : ℝ≥0} (hsT : s ≤ T) :
    bandEnergy T s hBmeas (itoProcessAssembled hB T hBmeas hBcont φ)
      = ∫ u in Set.Ioc (0 : ℝ≥0) s, bandEnergy T u hBmeas φ ∂timeMeasure := by
  rw [itoProcessAssembled,
    bandEnergy_toLp T hBmeas (g := itoContinuousMod T hBmeas φ)
      (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ)
      (memLp_itoContinuousMod hB T hBmeas hBcont φ) hsT]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  have htT : t ≤ T := ht.2.trans hsT
  have hb : bandEnergy T t hBmeas φ = ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 :=
    (itoProcessCLM_norm_sq hB htT hBmeas φ).symm
  change ∫ ω, (itoContinuousMod T hBmeas φ t ω) ^ 2 ∂μ = bandEnergy T t hBmeas φ
  rw [hb, lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont φ htT] with ω hω
  rw [hω]

theorem continuous_bandEnergy (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {s : ℝ≥0} (hsT : s ≤ T) :
    Continuous fun Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) ↦ bandEnergy T s hBmeas Z := by
  have h : (fun Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) ↦ bandEnergy T s hBmeas Z)
      = fun Z ↦ ‖itoProcessCLM hB T s hBmeas Z‖ ^ 2 :=
    funext fun Z ↦ (itoProcessCLM_norm_sq hB hsT hBmeas Z).symm
  rw [h]
  exact (itoProcessCLM hB T s hBmeas).continuous.norm.pow 2

/-- The assembled Itô process is `√T`-Lipschitz in the integrand (additivity and the operator
bound `itoProcessAssembled_norm_le`), in particular continuous. -/
theorem lipschitzWith_itoProcessAssembled (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) :
    LipschitzWith (NNReal.sqrt T) (itoProcessAssembled hB T hBmeas hBcont) := by
  refine LipschitzWith.of_dist_le_mul fun X Y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, ← itoProcessAssembled_sub, Real.coe_sqrt]
  exact itoProcessAssembled_norm_le hB T hBmeas hBcont _

/-- **The elementary drift, band by band.** For a `T`-bounded simple process `V`, the band energy
of its drift is at most `s ∫₀ˢ (band energy of V on (0,u]) du`: pointwise Cauchy–Schwarz
(`driftSimpleProcess_sq_le` at horizon `t`) gives `d_t² ≤ t∫₀ᵗ V²`, then Fubini on the band. -/
theorem bandEnergy_driftSimpleProcessLp_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T hBmeas) {s : ℝ≥0} (hsT : s ≤ T) :
    bandEnergy T s hBmeas (driftSimpleProcessLp (μ := μ) T hBmeas V.val)
      ≤ (s : ℝ) * ∫ u in Set.Ioc (0 : ℝ≥0) s,
          bandEnergy T u hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V) ∂timeMeasure := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas
  have hmemD := memLp_uncurry_driftSimpleProcess (μ := μ) T hBmeas V.val
  have hmemV := memLp_uncurry_trimMeasure (μ := μ) T hBmeas V.val
  have hpredD : StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (driftSimpleProcess hBmeas V.val)) :=
    driftSimpleProcess_isStronglyPredictable hBmeas V.val
  have hpredV : StronglyMeasurable[𝓕.predictable] (Function.uncurry ⇑V.val) :=
    V.val.isStronglyPredictable
  have hsAsm : simpleAssemblyHorizon (μ := μ) T hBmeas V
      = hmemV.toLp (Function.uncurry ⇑V.val) := rfl
  have hintD : Integrable (fun z ↦ (Function.uncurry (driftSimpleProcess hBmeas V.val) z) ^ 2)
      ((timeMeasureHorizon T).prod μ) :=
    (memLp_of_memLp_trim 𝓕.predictable_le_prod hmemD).integrable_sq
  have hintV : Integrable (fun z ↦ (Function.uncurry ⇑V.val z) ^ 2)
      ((timeMeasureHorizon T).prod μ) :=
    (memLp_of_memLp_trim 𝓕.predictable_le_prod hmemV).integrable_sq
  -- the slice bound at a fixed time `t ≤ T`
  have hpt : ∀ t : ℝ≥0, t ≤ T →
      Integrable (fun ω ↦ (driftSimpleProcess hBmeas V.val t ω) ^ 2) μ →
      ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ
        ≤ (t : ℝ) * bandEnergy T t hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V) := by
    intro t htT hint_t
    have hintV_t : Integrable (fun z ↦ (Function.uncurry ⇑V.val z) ^ 2)
        ((timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)).prod μ) := by
      rw [← prod_restrict_band T htT]
      exact hintV.integrableOn
    have hswap : ∫ ω, ∫ r in Set.Ioc (0 : ℝ≥0) t, (⇑V.val r ω) ^ 2 ∂timeMeasure ∂μ
        = ∫ r in Set.Ioc (0 : ℝ≥0) t, ∫ ω, (⇑V.val r ω) ^ 2 ∂μ ∂timeMeasure :=
      (integral_integral_swap (f := fun r ω ↦ (⇑V.val r ω) ^ 2) hintV_t).symm
    have hsim : bandEnergy T t hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V)
        = ∫ r in Set.Ioc (0 : ℝ≥0) t, ∫ ω, (⇑V.val r ω) ^ 2 ∂μ ∂timeMeasure := by
      rw [hsAsm]
      exact bandEnergy_toLp T hBmeas (g := ⇑V.val) hpredV hmemV htT
    rw [hsim, ← hswap, ← integral_const_mul]
    exact integral_mono_ae hint_t (hintV_t.integral_prod_right.const_mul _)
      (ae_of_all _ fun ω ↦ driftSimpleProcess_sq_le t hBmeas V.val le_rfl ω)
  have hL : bandEnergy T s hBmeas (driftSimpleProcessLp (μ := μ) T hBmeas V.val)
      = ∫ t in Set.Ioc (0 : ℝ≥0) s, ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ
          ∂timeMeasure :=
    bandEnergy_toLp T hBmeas (g := driftSimpleProcess hBmeas V.val) hpredD hmemD hsT
  have hslice : ∀ᵐ t ∂(timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) s)),
      Integrable (fun ω ↦ (driftSimpleProcess hBmeas V.val t ω) ^ 2) μ := by
    have h : ∀ᵐ t ∂(timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)),
        Integrable (fun ω ↦ (driftSimpleProcess hBmeas V.val t ω) ^ 2) μ :=
      hintD.prod_right_ae
    exact ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc_right hsT) h
  have hintDt : Integrable (fun t ↦ ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ)
      (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) s)) := by
    have h : Integrable (fun t ↦ ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := hintD.integral_prod_left
    exact h.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right hsT) le_rfl)
  rw [hL, ← integral_const_mul]
  refine integral_mono_ae hintDt
    ((integrable_bandEnergy T hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V) s).const_mul _)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hslice] with t ht hint_t
  exact (hpt t (ht.2.trans hsT) hint_t).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast ht.2) (bandEnergy_nonneg T t hBmeas _))

/-- **The assembled drift, band by band.** For every `g ∈ E` and `s ≤ T`,
`‖𝟙_{(0,s]}·∫₀·g‖² ≤ s · ‖𝟙_{(0,s]}·(g●B)‖²` — i.e. `s ∫₀ˢ (energy of g on (0,u]) du`, the Itô
side being its exact Volterra form (`bandEnergy_itoProcessAssembled`). Proved on the dense simple
processes (`bandEnergy_driftSimpleProcessLp_le`) and extended by continuity of both sides. -/
theorem bandEnergy_driftProcessAssembled_le (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {s : ℝ≥0} (hsT : s ≤ T) (g : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    bandEnergy T s hBmeas (driftProcessAssembled T hBmeas g)
      ≤ (s : ℝ) * bandEnergy T s hBmeas (itoProcessAssembled hB T hBmeas hBcont g) := by
  have hc1 : Continuous fun g' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) ↦
      bandEnergy T s hBmeas (driftProcessAssembled T hBmeas g') :=
    (continuous_bandEnergy hB T hBmeas hsT).comp (driftProcessAssembled T hBmeas).continuous
  have hc2 : Continuous fun g' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) ↦
      (s : ℝ) * bandEnergy T s hBmeas (itoProcessAssembled hB T hBmeas hBcont g') :=
    continuous_const.mul ((continuous_bandEnergy hB T hBmeas hsT).comp
      (lipschitzWith_itoProcessAssembled hB T hBmeas hBcont).continuous)
  have key : ∀ V : TBoundedSP T hBmeas,
      bandEnergy T s hBmeas
          (driftProcessAssembled T hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V))
        ≤ (s : ℝ) * bandEnergy T s hBmeas
          (itoProcessAssembled hB T hBmeas hBcont (simpleAssemblyHorizon (μ := μ) T hBmeas V)) :=
    fun V ↦ by
      rw [driftProcessAssembled_simpleAssembly,
        bandEnergy_itoProcessAssembled hB T hBmeas hBcont _ hsT]
      exact bandEnergy_driftSimpleProcessLp_le T hBmeas V hsT
  exact DenseRange.induction_on (simpleAssemblyHorizon_denseRange (μ := μ) T hBmeas) g
    (isClosed_le hc1 hc2) key

/-- **The coefficient composition, band by band.** Pointwise `|f x − f y| ≤ L|x − y|` integrates
over any band: `‖𝟙_{(0,s]}(f∘X − f∘Y)‖² ≤ L²‖𝟙_{(0,s]}(X − Y)‖²`. -/
theorem bandEnergy_lipComp_sub_le (T s : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    bandEnergy T s hBmeas (lipComp T hBmeas f L hf X - lipComp T hBmeas f L hf Y)
      ≤ (L : ℝ) ^ 2 * bandEnergy T s hBmeas (X - Y) := by
  have key : ∀ a b : ℝ, (f a - f 0 - (f b - f 0)) ^ 2 ≤ (L : ℝ) ^ 2 * (a - b) ^ 2 := by
    intro a b
    have h := (lipschitz_sub_const hf).dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at h
    calc (f a - f 0 - (f b - f 0)) ^ 2 = |f a - f 0 - (f b - f 0)| ^ 2 := (sq_abs _).symm
      _ ≤ ((L : ℝ) * |a - b|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (L : ℝ) ^ 2 * (a - b) ^ 2 := by rw [mul_pow, sq_abs]
  rw [lipComp, lipComp, add_sub_add_left_eq_sub]
  have hint := (Lp.memLp (X - Y)).integrable_sq.integrableOn
    (s := Set.Ioc 0 s ×ˢ (Set.univ : Set Ω))
  unfold bandEnergy
  rw [← integral_const_mul]
  refine integral_mono_ae (Lp.memLp _).integrable_sq.integrableOn (hint.const_mul _) ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [Lp.coeFn_sub ((lipschitz_sub_const hf).compLp (by simp) X)
      ((lipschitz_sub_const hf).compLp (by simp) Y),
    (lipschitz_sub_const hf).coeFn_compLp (by simp) X,
    (lipschitz_sub_const hf).coeFn_compLp (by simp) Y, Lp.coeFn_sub X Y] with z h1 h2 h3 h4
  simp only [h1, Pi.sub_apply, h2, h3, h4, Function.comp_apply]
  exact key _ _

/-- The Volterra rate constant `2 (T L_b² + L_σ²)` of the Picard difference. -/
noncomputable def picardRate (T Lb Lσ : ℝ≥0) : ℝ := 2 * ((T : ℝ) * (Lb : ℝ) ^ 2 + (Lσ : ℝ) ^ 2)

theorem picardRate_nonneg (T Lb Lσ : ℝ≥0) : 0 ≤ picardRate T Lb Lσ := by
  unfold picardRate; positivity

/-- **The Picard difference is a Volterra operator on band energies.** For `s ≤ T`,
`‖𝟙_{(0,s]}(Φ X − Φ Y)‖² ≤ 2(T L_b² + L_σ²) ∫₀ˢ ‖𝟙_{(0,u]}(X − Y)‖² du`. The drift term is
bounded by `bandEnergy_driftProcessAssembled_le`, the Itô term is exactly its Volterra integral
(`bandEnergy_itoProcessAssembled`), and `(a + b)² ≤ 2a² + 2b²` splits the sum. -/
theorem bandEnergy_picardMap_sub_le (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {s : ℝ≥0} (hsT : s ≤ T) :
    bandEnergy T s hBmeas
        (picardMap hB T hBmeas hBcont hb hσ η_E X - picardMap hB T hBmeas hBcont hb hσ η_E Y)
      ≤ picardRate T Lb Lσ *
        ∫ u in Set.Ioc (0 : ℝ≥0) s, bandEnergy T u hBmeas (X - Y) ∂timeMeasure := by
  have hI0 : 0 ≤ ∫ u in Set.Ioc (0 : ℝ≥0) s, bandEnergy T u hBmeas (X - Y) ∂timeMeasure :=
    integral_nonneg fun u ↦ bandEnergy_nonneg T u hBmeas _
  -- the Volterra integral of a Lipschitz composition
  have hlip : ∀ {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f),
      ∫ u in Set.Ioc (0 : ℝ≥0) s,
          bandEnergy T u hBmeas (lipComp T hBmeas f L hf X - lipComp T hBmeas f L hf Y) ∂timeMeasure
        ≤ (L : ℝ) ^ 2 * ∫ u in Set.Ioc (0 : ℝ≥0) s, bandEnergy T u hBmeas (X - Y) ∂timeMeasure := by
    intro f L hf
    rw [← integral_const_mul]
    exact integral_mono (integrable_bandEnergy T hBmeas _ s)
      ((integrable_bandEnergy T hBmeas _ s).const_mul _)
      fun u ↦ bandEnergy_lipComp_sub_le T u hBmeas hf X Y
  have hito : bandEnergy T s hBmeas (itoProcessAssembled hB T hBmeas hBcont
        (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y))
      ≤ (Lσ : ℝ) ^ 2 * ∫ u in Set.Ioc (0 : ℝ≥0) s, bandEnergy T u hBmeas (X - Y) ∂timeMeasure := by
    rw [bandEnergy_itoProcessAssembled hB T hBmeas hBcont _ hsT]
    exact hlip hσ
  have hdrift : bandEnergy T s hBmeas (driftProcessAssembled T hBmeas
        (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y))
      ≤ (T : ℝ) * ((Lb : ℝ) ^ 2 *
          ∫ u in Set.Ioc (0 : ℝ≥0) s, bandEnergy T u hBmeas (X - Y) ∂timeMeasure) := by
    refine (bandEnergy_driftProcessAssembled_le hB T hBmeas hBcont hsT _).trans ?_
    rw [bandEnergy_itoProcessAssembled hB T hBmeas hBcont _ hsT]
    exact (mul_le_mul_of_nonneg_left (hlip hb) s.coe_nonneg).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hsT) (mul_nonneg (sq_nonneg _) hI0))
  rw [picardMap_sub hB T hBmeas hBcont hb hσ η_E X Y]
  refine (bandEnergy_add_le T s hBmeas _ _).trans ?_
  unfold picardRate
  nlinarith [hito, hdrift]

/-- `∫₀ˢ uⁿ du = sⁿ⁺¹/(n+1)` against `timeMeasure` (the Lebesgue measure on `ℝ≥0`). -/
theorem setIntegral_pow_Ioc_timeMeasure (n : ℕ) (s : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ≥0) s, (u : ℝ) ^ n ∂timeMeasure = (s : ℝ) ^ (n + 1) / (n + 1) := by
  have hcongr : ∫ x in (0 : ℝ)..(s : ℝ), ((Real.toNNReal x : ℝ≥0) : ℝ) ^ n
      = ∫ x in (0 : ℝ)..(s : ℝ), x ^ n :=
    intervalIntegral.integral_congr fun x hx ↦ by
      have hx0 : 0 ≤ x := by
        rcases Set.mem_uIcc.1 hx with h | h
        · exact h.1
        · linarith [h.1, h.2, s.coe_nonneg]
      simp only [Real.coe_toNNReal _ hx0]
  rw [timeMeasure_Ioc_eq_interval (g := fun u : ℝ≥0 ↦ (u : ℝ) ^ n), hcongr, integral_pow]
  simp

/-- **Picard iterates decay factorially, band by band.** For `s ≤ T`,
`‖𝟙_{(0,s]}(Φⁿ X − Φⁿ Y)‖² ≤ (2(T L_b² + L_σ²) s)ⁿ / n! · ‖X − Y‖²`. By induction on the Volterra
estimate `bandEnergy_picardMap_sub_le`, using `∫₀ˢ uⁿ du = sⁿ⁺¹/(n+1)`. -/
theorem bandEnergy_picardMap_iterate_le (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (n : ℕ) :
    ∀ s : ℝ≥0, s ≤ T →
      bandEnergy T s hBmeas ((picardMap hB T hBmeas hBcont hb hσ η_E)^[n] X
          - (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] Y)
        ≤ (picardRate T Lb Lσ * (s : ℝ)) ^ n / (n.factorial : ℝ) * ‖X - Y‖ ^ 2 := by
  induction n with
  | zero =>
    intro s _
    simpa using bandEnergy_le_norm_sq T s hBmeas (X - Y)
  | succ n ih =>
    intro s hsT
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine (bandEnergy_picardMap_sub_le hB T hBmeas hBcont hb hσ η_E _ _ hsT).trans ?_
    have hK : 0 ≤ picardRate T Lb Lσ := picardRate_nonneg T Lb Lσ
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hmono : ∫ u in Set.Ioc (0 : ℝ≥0) s, bandEnergy T u hBmeas
          ((picardMap hB T hBmeas hBcont hb hσ η_E)^[n] X
            - (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] Y) ∂timeMeasure
        ≤ ∫ u in Set.Ioc (0 : ℝ≥0) s,
            (picardRate T Lb Lσ ^ n / (n.factorial : ℝ) * ‖X - Y‖ ^ 2) * (u : ℝ) ^ n
              ∂timeMeasure := by
      refine setIntegral_mono_on (integrable_bandEnergy T hBmeas _ s) ?_ measurableSet_Ioc
        fun u hu ↦ ?_
      · exact ((continuous_const.mul (NNReal.continuous_coe.pow n)).integrableOn_Icc).mono_set
          Set.Ioc_subset_Icc_self
      · calc _ ≤ (picardRate T Lb Lσ * (u : ℝ)) ^ n / (n.factorial : ℝ) * ‖X - Y‖ ^ 2 :=
              ih u (hu.2.trans hsT)
          _ = _ := by rw [mul_pow]; ring
    rw [integral_const_mul, setIntegral_pow_Ioc_timeMeasure] at hmono
    refine (mul_le_mul_of_nonneg_left hmono hK).trans_eq ?_
    rw [Nat.factorial_succ]
    push_cast
    first | (field_simp; done) | (field_simp; ring)

/-- **Picard iterates contract in `E`, factorially.**
`‖Φⁿ X − Φⁿ Y‖² ≤ (2(T L_b² + L_σ²) T)ⁿ / n! · ‖X − Y‖²` for every horizon `T`. -/
theorem picardMap_iterate_norm_sq_le (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E X Y : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (n : ℕ) :
    ‖(picardMap hB T hBmeas hBcont hb hσ η_E)^[n] X
        - (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] Y‖ ^ 2
      ≤ (picardRate T Lb Lσ * (T : ℝ)) ^ n / (n.factorial : ℝ) * ‖X - Y‖ ^ 2 :=
  (norm_sq_eq_bandEnergy T hBmeas _).le.trans
    (bandEnergy_picardMap_iterate_le hB T hBmeas hBcont hb hσ η_E X Y n T le_rfl)

/-- **A unique Picard fixed point on every horizon.** For Lipschitz `b, σ`
and any `T` (no smallness condition `T L_b + √T L_σ < 1`), the Picard map of
`dX = b(X)dt + σ(X)dB`, `X₀ = η` has exactly one fixed point in the predictable `L²` space `E`.
Some iterate `Φⁿ` is a contraction (`picardMap_iterate_norm_sq_le`: factorial decay), and a map
with a contracting iterate has a unique fixed point
(`ContractingWith.isFixedPt_fixedPoint_iterate`). -/
theorem picardMap_exists_unique_fixedPoint_any_horizon (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∃! X, picardMap hB T hBmeas hBcont hb hσ η_E X = X := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (picardRate T Lb Lσ * (T : ℝ)) ^ n / (n.factorial : ℝ) < 1 / 4 :=
    ((FloorSemiring.tendsto_pow_div_factorial_atTop (picardRate T Lb Lσ * (T : ℝ))).eventually
      (gt_mem_nhds (by norm_num))).exists
  let K : ℝ≥0 := ⟨1 / 2, by norm_num⟩
  have hK : (K : ℝ) = 1 / 2 := rfl
  have hc : ContractingWith K (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] := by
    refine ⟨by rw [← NNReal.coe_lt_coe, hK]; norm_num, LipschitzWith.of_dist_le_mul fun X Y ↦ ?_⟩
    rw [dist_eq_norm, dist_eq_norm, hK]
    have h2 : ‖(picardMap hB T hBmeas hBcont hb hσ η_E)^[n] X
          - (picardMap hB T hBmeas hBcont hb hσ η_E)^[n] Y‖ ^ 2 ≤ (1 / 2 * ‖X - Y‖) ^ 2 :=
      (picardMap_iterate_norm_sq_le hB T hBmeas hBcont hb hσ η_E X Y n).trans
        (calc _ ≤ 1 / 4 * ‖X - Y‖ ^ 2 := mul_le_mul_of_nonneg_right hn.le (sq_nonneg _)
          _ = _ := by ring)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  exact ⟨hc.fixedPoint _, hc.isFixedPt_fixedPoint_iterate,
    fun Y hY ↦ hc.fixedPoint_unique (Function.IsFixedPt.iterate hY n)⟩

end SDEExistence
end MathFin

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use the v4.35.0
-- `eLpNorm`/`MemLp` API.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_two_rpow_eq_lintegral_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrementMoment
public import LeanPool.KLS.LevyStochCalc.Probability.MartingaleDifference

/-!
# Compensated square increments of the Itô integral

The increment `(M_b − M_a)² − ∫_a^b H_s² ds` of the compensated square of the Itô integral is
conditionally centred at its left endpoint, so a weighted sum of such increments over a
partition is a sum of martingale differences.

## Main statements

* `LevyStochCalc.Brownian.Ito.quadVarIncrement` — the compensated square increment.
* `LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement` — it is conditionally centred at the
  left endpoint.
* `LevyStochCalc.Brownian.Ito.compensator_sub_bounds` — the compensator increment across
  `(a, b]` lies between `0` and `C²(b − a)`.
* `LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le` — its second moment is at most
  `(2(6 + c) + 2)·C⁴·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_quadVarSum_le` — the second moment of a
  weighted sum over a grid is at most `D²·(2(6 + c) + 2)·C⁴·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
* `LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian` — the
  Itô integral of a bounded integrand has a modification with continuous paths.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The compensated square increment `(M_b − M_a)² − ∫_a^b H_s² ds` of the Itô integral. -/
noncomputable def quadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
    - ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)

include hℱ in
/-- The compensated square increment is conditionally centred at its left endpoint. -/
theorem condExp_quadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P[quadVarIncrement W ℱ hℱ H hm hp hq a b | ℱ.rightCont a] =ᵐ[P] 0 := by
  have hMmart := martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
  have hQmart := martingale_rightCont_quadVar_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
  have hMmem : ∀ t : ℝ, MemLp (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) 2 P :=
    fun t => stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq t
  have hMint : ∀ t : ℝ, Integrable (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) P :=
    fun t => (hMmem t).integrable (by norm_num)
  have hAint : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
    fun t ht => compensatorH_integrable H hm hq ht
  have hMsq : ∀ t : ℝ,
      Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2) P := by
    intro t
    have hfun : (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2)
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t
          * stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact (hMmem t).integrable_mul (hMmem t)
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  -- the three pieces of the decomposition
  have hi1 : Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
      - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume) P := (hMsq b).sub (hAint b hb)
  have hi2 : Integrable (fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) P :=
    (hMmem a).integrable_mul (hMmem b)
  have hi3 : Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) P := (hMsq a).add (hAint a ha)
  have hdecomp : quadVarIncrement W ℱ hℱ H hm hp hq a b
      = (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        + ((-2 : ℝ) • fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
            * stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        + (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
            + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
    funext ω
    simp only [quadVarIncrement, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- conditional expectations of the three pieces
  have h1 : P[fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := hQmart.2 a b hab
  have h2 : P[fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω | ℱ.rightCont a]
      =ᵐ[P] fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 := by
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ.rightCont a)
      hMa hi2 (hMint b)
    have hfun : (fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq a
          * stochasticIntegralBrownian W ℱ hℱ H hm hp hq b := rfl
    rw [hfun]
    filter_upwards [hkey, hMmart.2 a b hab] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', pow_two]
  have h3 : P[fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := by
    refine Filter.EventuallyEq.of_eq (MeasureTheory.condExp_of_stronglyMeasurable
      (ℱ.rightCont.le a) ?_ hi3)
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hAa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (fun ω => ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) :=
      (compensatorH_adapted ℱ H hp a).mono (ℱ.le_rightCont a)
    exact ((hMa.measurable.pow_const 2).stronglyMeasurable).add hAa
  -- assemble
  rw [hdecomp]
  have hadd1 := MeasureTheory.condExp_add hi1 (hi2.smul (-2 : ℝ)) (ℱ.rightCont a)
  have hadd2 := MeasureTheory.condExp_add (hi1.add (hi2.smul (-2 : ℝ))) hi3 (ℱ.rightCont a)
  have hsmul := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (-2 : ℝ)
    (fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
  filter_upwards [hadd2, hadd1, hsmul, h1, h2, h3] with ω e2 e1 es f1 f2 f3
  rw [e2, Pi.add_apply, e1, Pi.add_apply, es, Pi.smul_apply, f1, f2, f3, Pi.zero_apply]
  simp only [smul_eq_mul]
  ring

end QuadVarIncrement


/-- A square-integrable function lies in `L²`. -/
theorem memLp_two_of_lintegral_sq_lt_top {P' : Measure Ω} {f : Ω → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f P')
    (h : ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P' < ⊤) : MemLp f 2 P' := by
  rw [MeasureTheory.memLp_iff]
  by_contra hcon
  have htop : MeasureTheory.eLpNorm f 2 P' = ⊤ := top_le_iff.mp (not_lt.mp hcon)
  rw [← eLpNorm_two_rpow_eq_lintegral_sq f hf, htop,
    ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  exact lt_irrefl _ h

section Bounds

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hm hC0 hCH in
/-- The square of a bounded integrand is integrable on every set of finite measure. -/
theorem integrableOn_sq (ω : Ω) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) s volume := by
  have hmeas : Measurable fun u => (H ω u) ^ 2 :=
    ((Measurable.of_uncurry_left hm).pow_const 2)
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := C ^ 2) hs
    hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (H ω u) ^ 2)]
  nlinarith [hCH ω u, abs_nonneg (H ω u), sq_abs (H ω u)]

include hm hC0 hCH in
/-- The compensator increment across `(a, b]` is between `0` and `C²(b − a)`. -/
theorem compensator_sub_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω) :
    0 ≤ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume
      ∧ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume ≤ C ^ 2 * (b - a) := by
  have hmeas : Measurable fun u => (H ω u) ^ 2 :=
    ((Measurable.of_uncurry_left hm).pow_const 2)
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_sq H hm hC0 hCH ω (by simp)
  have hint2 : MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) (Set.Ioc a b) volume :=
    integrableOn_sq H hm hC0 hCH ω (by simp)
  have hadd : (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      = (∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
        + ∫ u in Set.Ioc a b, (H ω u) ^ 2 ∂volume := by
    rw [hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2
  rw [hadd, add_sub_cancel_left]
  refine ⟨MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun u _ => by positivity, ?_⟩
  have hle : ∫ u in Set.Ioc a b, (H ω u) ^ 2 ∂volume
      ≤ ∫ _u in Set.Ioc a b, C ^ 2 ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hint2
      (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
      fun u _ => ?_
    nlinarith [hCH ω u, abs_nonneg (H ω u), sq_abs (H ω u)]
  refine hle.trans ?_
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  exact le_of_eq (mul_comm _ _)

end Bounds


section IncrementL2

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- The square of an increment of the Itô integral lies in `L²`. -/
theorem memLp_two_sq_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) 2 P := by
  have hmeas : Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
        (ℱ.le b)).measurable).sub
      (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
        (ℱ.le a)).measurable)
  refine memLp_two_of_lintegral_sq_lt_top (hmeas.pow_const 2).aestronglyMeasurable ?_
  have hpt : ∀ ω : Ω, (‖(stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2‖₊ : ℝ≥0∞) ^ 2
      = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
    intro ω
    rw [nnnorm_pow, ENNReal.coe_pow, ← pow_mul]
  simp_rw [hpt]
  exact lt_of_le_of_lt
    (lintegral_stochasticIntegralBrownian_sub_pow_four_le W ℱ hℱ H hm hp hq hC0 hCH ha hab)
    (by simp)

include hm hq hC0 hCH in
/-- The compensator increment lies in `L²`. -/
theorem memLp_two_compensator_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) 2 P := by
  have hint := ((compensatorH_integrable H hm hq (ha.trans hab)).sub
    (compensatorH_integrable H hm hq ha))
  refine MeasureTheory.MemLp.of_bound hint.aestronglyMeasurable (C ^ 2 * (b - a)) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  obtain ⟨h1, h2⟩ := compensator_sub_bounds H hm hC0 hCH ha hab ω
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

include hℱ hC0 hCH in
/-- The compensated square increment lies in `L²`. -/
theorem memLp_two_quadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (quadVarIncrement W ℱ hℱ H hm hp hq a b) 2 P :=
  (memLp_two_sq_increment W ℱ hℱ H hm hp hq hC0 hCH ha hab).sub
    (memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le)

include hℱ hC0 hCH in
/-- Second moment of the compensated square increment. -/
theorem integral_sq_quadVarIncrement_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ (2 * (6 + gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by
  have hcg : (0 : ℝ) ≤ gaussianFourthMoment := gaussianFourthMoment_nonneg
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hXmem := memLp_two_sq_increment W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hYmem := memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le
  have hXint : Integrable (fun ω => ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) P := by
    have hfun : (fun ω => ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2)
          * (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hXmem.integrable_mul hXmem
  have hYint : Integrable (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) P := by
    have hfun : (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)
        = (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
          * (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hYmem.integrable_mul hYmem
  -- the fourth moment of the increment
  have hX : ∫ ω, ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P
      ≤ (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by
    have hK : (0 : ℝ) ≤ (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by positivity
    have heq : ENNReal.ofReal (∫ ω, ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal (((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) ∂P :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hXint
        (Filter.Eventually.of_forall fun ω => by positivity)
    have hpt : ∀ ω : Ω, ENNReal.ofReal (((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
      have key : ∀ x : ℝ, ENNReal.ofReal ((x ^ 2) ^ 2) = (‖x‖₊ : ℝ≥0∞) ^ 4 := by
        intro x
        have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
          rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
          exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
        rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
        congr 1
        ring
      exact fun ω => key _
    rw [← ENNReal.ofReal_le_ofReal_iff hK, heq]
    simp_rw [hpt]
    exact lintegral_stochasticIntegralBrownian_sub_pow_four_le W ℱ hℱ H hm hp hq hC0 hCH ha hab
  -- the compensator increment
  have hY : ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
      ≤ C ^ 4 * (b - a) ^ 2 := by
    have hbnd : ∀ ω : Ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ≤ C ^ 4 * (b - a) ^ 2 := by
      intro ω
      obtain ⟨h1, h2⟩ := compensator_sub_bounds H hm hC0 hCH ha hab.le ω
      nlinarith [sq_nonneg C, mul_nonneg (mul_nonneg hC0 hC0) hba]
    calc ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
        ≤ ∫ _ω : Ω, C ^ 4 * (b - a) ^ 2 ∂P :=
          MeasureTheory.integral_mono hYint (integrable_const _) hbnd
      _ = C ^ 4 * (b - a) ^ 2 := by simp
  -- combine
  have hptwise : ∀ ω : Ω, (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2
      ≤ 2 * (((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) := by
    intro ω
    simp only [quadVarIncrement]
    nlinarith [sq_nonneg ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume))]
  have hζint : Integrable (fun ω => (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2) P := by
    have hmem := memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH ha hab
    have hfun : (fun ω => (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2)
        = quadVarIncrement W ℱ hℱ H hm hp hq a b * quadVarIncrement W ℱ hℱ H hm hp hq a b := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hmem.integrable_mul hmem
  calc ∫ ω, (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * (((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
          + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)) ∂P :=
        MeasureTheory.integral_mono hζint ((hXint.const_mul 2).add (hYint.const_mul 2)) hptwise
    _ = 2 * (∫ ω, ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
          + 2 * (∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P) := by
        rw [MeasureTheory.integral_add (hXint.const_mul 2) (hYint.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) + 2 * (C ^ 4 * (b - a) ^ 2) := by
        gcongr
    _ = (2 * (6 + gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by ring

end IncrementL2


section WeightedSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ in
/-- The compensated square increment across a grid cell is measurable for the σ-algebra at the
right endpoint. -/
theorem stronglyMeasurable_quadVarIncrement {a b : ℝ} (hab : a ≤ b) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (quadVarIncrement W ℱ hℱ H hm hp hq a b) := by
  have hMmart := martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
  have hMb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b) := hMmart.1 b
  have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) :=
    (hMmart.1 a).mono (ℱ.rightCont.mono hab)
  have hAb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume) :=
    (compensatorH_adapted ℱ H hp b).mono (ℱ.le_rightCont b)
  have hAa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) :=
    ((compensatorH_adapted ℱ H hp a).mono (ℱ.le_rightCont a)).mono (ℱ.rightCont.mono hab)
  exact ((hMb.sub hMa).measurable.pow_const 2).stronglyMeasurable.sub (hAb.sub hAa)

include hℱ hC0 hCH in
/-- **Second moment of a weighted sum of compensated square increments.** The increments are
martingale differences, so the weighted sum's second moment is controlled by the sum of the
squared cell lengths. -/
theorem integral_sq_weighted_quadVarSum_le
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ)
    (hg : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (t k)) (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n,
        g i ω * quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
        * ∑ i ∈ Finset.range n, (t (i + 1) - t i) ^ 2 := by
  have htmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => h0.trans (htmono.monotone (Nat.zero_le k))
  -- the martingale-difference data
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => ℱ.rightCont (t k) with h𝒢
  have h𝒢le : ∀ k, 𝒢 k ≤ ‹MeasurableSpace Ω› := fun k => ℱ.rightCont.le (t k)
  have h𝒢mono : Monotone 𝒢 := fun i j hij => ℱ.rightCont.mono (htmono.monotone hij)
  set Y : ℕ → Ω → ℝ := fun k ω =>
    g k ω * quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1)) ω with hY
  have hζmem : ∀ k, MemLp (quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1))) 2 P :=
    fun k => memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH (ht0 k) (ht k)
  have hgmeas : ∀ k, Measurable (g k) := fun k => ((hg k).mono (h𝒢le k)).measurable
  have hYmem : ∀ k, MemLp (Y k) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul D)
      ((hgmeas k).aestronglyMeasurable.mul (hζmem k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_right (hgD k ω) (abs_nonneg _)
  have hYmeas : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (𝒢 (k + 1)) (Y k) := by
    intro k
    exact ((hg k).mono (h𝒢mono (Nat.le_succ k))).mul
      (stronglyMeasurable_quadVarIncrement W ℱ hℱ H hm hp hq (ht k).le)
  have hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0 := by
    intro k
    have hprod : Integrable (g k * quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1))) P :=
      (hYmem k).integrable (by norm_num)
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (hg k)
      hprod ((hζmem k).integrable (by norm_num))
    have hfun : Y k = g k * quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1)) := rfl
    rw [hfun]
    filter_upwards [hkey,
      condExp_quadVarIncrement W ℱ hℱ H hm hp hq (ht0 k) (ht k).le] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  -- orthogonality
  rw [LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero 𝒢 h𝒢le h𝒢mono Y hYmem
    hYmeas hYcond n]
  -- termwise bound
  have hterm : ∀ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ D ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4) * (t (i + 1) - t i) ^ 2 := by
    intro i _
    have hζint : Integrable
        (fun ω => (quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2) P := by
      have hfun : (fun ω => (quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2)
          = quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1))
            * quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) := by
        funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hζmem i).integrable_mul (hζmem i)
    have hYint : Integrable (fun ω => (Y i ω) ^ 2) P := by
      have hfun : (fun ω => (Y i ω) ^ 2) = Y i * Y i := by funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hYmem i).integrable_mul (hYmem i)
    have hstep : ∫ ω, (Y i ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω, (quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P := by
      have hle : ∫ ω, (Y i ω) ^ 2 ∂P
          ≤ ∫ ω, D ^ 2 * (quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono hYint (hζint.const_mul _) fun ω => ?_
        have hgi : (g i ω) ^ 2 ≤ D ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (g i ω)) (hgD i ω) 2
          rwa [← abs_pow, abs_of_nonneg (sq_nonneg (g i ω))] at h
        have : (Y i ω) ^ 2 = (g i ω) ^ 2
            * (quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 := by
          simp only [hY]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hgi (sq_nonneg _)
      rwa [MeasureTheory.integral_const_mul] at hle
    have hbnd := integral_sq_quadVarIncrement_le W ℱ hℱ H hm hp hq hC0 hCH (ht0 i) (ht i)
    have hD2 : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
    calc ∫ ω, (Y i ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω, (quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P := hstep
      _ ≤ D ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4 * (t (i + 1) - t i) ^ 2) :=
          mul_le_mul_of_nonneg_left hbnd hD2
      _ = D ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4) * (t (i + 1) - t i) ^ 2 := by
          ring
  calc ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ ∑ i ∈ Finset.range n,
          D ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4) * (t (i + 1) - t i) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = D ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
          * ∑ i ∈ Finset.range n, (t (i + 1) - t i) ^ 2 := by
        rw [Finset.mul_sum]

end WeightedSum


section ContinuousModification

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

/-- The extended distance between two reals is the norm of their difference. -/
theorem edist_eq_coe_nnnorm_sub (x y : ℝ) : edist x y = (‖x - y‖₊ : ℝ≥0∞) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
  exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))

include hℱ hC0 hCH in
/-- **A continuous modification of the `L²` Itô integral of a bounded integrand.** The
fourth-moment increment bound is the Kolmogorov–Chentsov condition with exponents `(4, 2)`. -/
theorem exists_continuous_modification_stochasticIntegralBrownian :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous fun t => Y t ω)
        ∧ ∀ t : ℝ, 0 ≤ t →
            Y t =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  set K : ℝ := (6 + gaussianFourthMoment) * C ^ 4 with hK
  have hK0 : 0 ≤ K := by
    have := gaussianFourthMoment_nonneg
    positivity
  set Xc : ℝ → Ω → ℝ :=
    fun t ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (max t 0) ω with hXc
  have hXmeas : ∀ t : ℝ, Measurable (Xc t) := fun t =>
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq (max t 0)).mono
      (ℱ.le _)).measurable
  -- the Kolmogorov condition with exponents `(4, 2)`
  have hpair : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
        ≤ ENNReal.ofReal (K * (b - a) ^ 2) := by
    intro a b ha hab
    have hswap : ∀ ω : Ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞)
        = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) := by
      intro ω
      rw [← nnnorm_neg, neg_sub]
    simp_rw [hswap]
    exact lintegral_stochasticIntegralBrownian_sub_pow_four_le W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hkol : ∀ s t : ℝ, ∫⁻ ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ) ∂P
      ≤ (K.toNNReal : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
    intro s t
    have hnat4 : ∀ ω : Ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ)
        = (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) := by
      intro ω
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
        edist_eq_coe_nnnorm_sub]
    have hnat2 : edist s t ^ (2 : ℝ) = ENNReal.ofReal (|s - t| ^ 2) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, edist_dist,
        Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _)]
    have hdiff : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
    simp_rw [hnat4]
    rw [hnat2, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      Real.coe_toNNReal K hK0]
    rcases lt_trichotomy (max s 0) (max t 0) with hst | hst | hst
    · refine le_trans (hpair (max s 0) (max t 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max t 0 - max s 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max t 0 - max s 0), abs_sub_comm]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max t 0 - max s 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
    · have hzero : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) = 0 := by
        intro ω
        simp [hXc, hst]
      simp_rw [hzero]
      simp
    · have hswap : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞)
          = (‖Xc t ω - Xc s ω‖₊ : ℝ≥0∞) := fun ω => by rw [← nnnorm_neg, neg_sub]
      simp_rw [hswap]
      refine le_trans (hpair (max t 0) (max s 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max s 0 - max t 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max s 0 - max t 0)]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max s 0 - max t 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
  have hKolProc : ProbabilityTheory.IsKolmogorovProcess Xc P 4 2 K.toNNReal :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology hXmeas hkol
      (by norm_num) (by norm_num)
  obtain ⟨Y, hYcont, hYmod⟩ :=
    LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification P Xc hKolProc
      (by norm_num)
  refine ⟨Y, hYcont, fun t ht => ?_⟩
  have h := hYmod t
  simp only [hXc, max_eq_left ht] at h
  exact h

end ContinuousModification

end LevyStochCalc.Brownian.Ito

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with source adaptations
-- (deprecated names, proof-context visibility, the v4.35.0 `eLpNorm`/`MemLp` API, a measurability
-- premise of the private `eLpNorm_mul_le_of_bound`) listed in vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_two_rpow_eq_lintegral_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebraProduct

/-!
# Associativity and locality of the `L²` Brownian Itô integral

Summing the increments of the `L²` Itô integral of a process `H` against the coefficients of a
simple integrand `G` gives the `L²` Itô integral of the product `G · H`; specialising to the step
integrands `1_{(a, b]}` identifies the `L²` Itô integral of an integrand restricted to `(a, b]`
with the increment of the integral of the unrestricted integrand across `(a, b]`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

private lemma eLpNorm_mul_le_of_bound {P : Measure Ω} {c g : Ω → ℝ} {M : ℝ}
    (hM : ∀ ω, |c ω| ≤ M) (hcg : MeasureTheory.AEStronglyMeasurable (fun ω => c ω * g ω) P) :
    MeasureTheory.eLpNorm (fun ω => c ω * g ω) 2 P
      ≤ (‖M‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm g 2 P := by
  have hsm : (fun ω => M * g ω) = (M • g : Ω → ℝ) := by funext ω; simp
  refine le_trans (MeasureTheory.eLpNorm_mono (g := fun ω => M * g ω) hcg fun ω => ?_) ?_
  · have hM0 : 0 ≤ M := (abs_nonneg (c ω)).trans (hM ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hM ω) (abs_nonneg _)
  · rw [hsm]; exact MeasureTheory.eLpNorm_const_smul_le

section Associativity

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **Associativity against a simple integrand.** Summing the increments of the `L²` Itô integral
of `H` against the coefficients of a simple integrand `G` gives the `L²` Itô integral of the
product `G · H`. -/
theorem stochasticIntegralBrownian_integralAgainst {t : ℝ} (ht : 0 < t) :
    G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
        hmm hmp hmq t := by
  classical
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  choose Th Q hQadapt hQeval hQint using fun n : ℕ =>
    SimplePredictable.exists_mul_simple W ℱ G (masterApprox ℱ H hm hp hq n) h_adapt
      (masterApprox_adapt ℱ H hm hp hq n)
  choose Mb hMb using G.ξ_bounded
  -- measurability bookkeeping
  have hMmeas : ∀ u : ℝ, Measurable (stochasticIntegralBrownian W ℱ hℱ H hm hp hq u) :=
    fun u => ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq u).mono
      (ℱ.le u)).measurable
  have hInmeas : ∀ (n : ℕ) (u : ℝ),
      Measurable (simpleIntegral W (masterApprox ℱ H hm hp hq n) u) := by
    intro n u
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((masterApprox ℱ H hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hQmeas : ∀ n : ℕ, Measurable (simpleIntegral W (Q n) t) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIAmeas : Measurable (G.integralAgainst
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t) := by
    unfold SimplePredictable.integralAgainst
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((hMmeas _).sub (hMmeas _))
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.AEStronglyMeasurable g P →
      MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
        = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g hg
    rw [← eLpNorm_two_rpow_eq_lintegral_sq g hg,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  -- (d) the product elementary integrals converge to the `L²` integral of `G.eval · H`
  have hd : Filter.Tendsto (fun n => ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
      intro s ω
      calc (‖G.eval s ω‖₊ : ℝ≥0∞)
          = ENNReal.ofReal ‖G.eval s ω‖ := by
            rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
        _ ≤ ENNReal.ofReal B :=
            ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
    have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
    have hkey : ∀ n, ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H hm hp hq n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n)
        (fun ω s => G.eval s ω * H ω s) hmm hmp hmq ht,
        ← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun ω => ?_
      rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun s => ?_
      have hrw : (Q n).eval s ω - G.eval s ω * H ω s
          = G.eval s ω * -(H ω s - (masterApprox ℱ H hm hp hq n).eval s ω) := by
        rw [hQeval n s ω]; ring
      rw [hrw, nnnorm_mul, nnnorm_neg, ENNReal.coe_mul, mul_pow]
      gcongr
      exact hbd s ω
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Filter.Eventually.of_forall fun n => bot_le) (Filter.Eventually.of_forall hkey)
    have hml := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B ^ 2)
      (masterApprox_eval_tendsto (t := t) ℱ H hm hp hq) (Or.inr hne)
    simpa using hml
  -- (e) the product elementary integrals converge to the integral against the `L²` integral
  have hu_nn : ∀ i : Fin G.N, 0 ≤ min (G.partition i.succ) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hu_nn' : ∀ i : Fin G.N, 0 ≤ min (G.partition i.castSucc) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hstep : ∀ n : ℕ, (fun ω => simpleIntegral W (Q n) t ω
      - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
      = ∑ i : Fin G.N,
        ((fun ω => G.ξ i ω * (simpleIntegral W (masterApprox ℱ H hm hp hq n)
            (min (G.partition i.succ) t) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω))
        - (fun ω => G.ξ i ω * (simpleIntegral W (masterApprox ℱ H hm hp hq n)
            (min (G.partition i.castSucc) t) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (min (G.partition i.castSucc) t) ω))) := by
    intro n
    funext ω
    simp only [Finset.sum_apply, Pi.sub_apply]
    rw [← hQint n t ω]
    unfold SimplePredictable.integralAgainst
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : ∀ n : ℕ, MeasureTheory.eLpNorm (fun ω => simpleIntegral W (Q n) t ω
      - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P
      ≤ ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P) := by
    intro n
    have haesm : ∀ (i : Fin G.N) (u : ℝ), MeasureTheory.AEStronglyMeasurable
        (fun ω => G.ξ i ω * (simpleIntegral W (masterApprox ℱ H hm hp hq n) u ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) P :=
      fun i u => ((G.ξ_measurable i).mul ((hInmeas n u).sub (hMmeas u))).aestronglyMeasurable
    rw [hstep n]
    refine le_trans (MeasureTheory.eLpNorm_sum_le (by norm_num)) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (MeasureTheory.eLpNorm_sub_le (by norm_num)) ?_
    exact add_le_add (eLpNorm_mul_le_of_bound (hMb i) (haesm i _))
      (eLpNorm_mul_le_of_bound (hMb i) (haesm i _))
  have hlim : Filter.Tendsto (fun n : ℕ =>
      ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P)) Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin G.N, (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i _ => ?_
    have h1 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn i)) (Or.inr ENNReal.coe_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn' i)) (Or.inr ENNReal.coe_ne_top)
    simpa using h1.add h2
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω =>
      simpleIntegral W (Q n) t ω
        - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)
  have he : Filter.Tendsto (fun n => ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
      - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    have h2 := ENNReal.Tendsto.mul heL (Or.inr (by simp)) heL (Or.inr (by simp))
    simpa using h2.congr fun n => hconv _ ((hQmeas n).sub hIAmeas).aestronglyMeasurable
  -- squeeze the two limits together
  have hle : ∫⁻ ω,
      (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim2 : Filter.Tendsto (fun n => 2 * ((∫⁻ ω, (‖simpleIntegral W (Q n) t ω
          - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
            : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
          - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) Filter.atTop (nhds 0) := by
      have h3 := ENNReal.Tendsto.const_mul (a := 2) (he.add hd) (Or.inr (by simp))
      simpa using h3
    refine ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun n => ?_)
    have hm2 : AEMeasurable (fun ω => (‖simpleIntegral W (Q n) t ω
        - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
          : ℝ≥0∞) ^ 2) P :=
      ((((hQmeas n).sub hIAmeas).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
    calc ∫⁻ ω, (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
          - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖simpleIntegral W (Q n) t ω
              - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2
            + (‖simpleIntegral W (Q n) t ω
              - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
                - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                    hmm hmp hmq t ω
              = -(simpleIntegral W (Q n) t ω
                    - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
                + (simpleIntegral W (Q n) t ω
                    - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                        hmm hmp hmq t ω) := by ring
          rw [hrw]
          refine le_trans (sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖simpleIntegral W (Q n) t ω
              - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
              - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω,
      (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P = 0 := le_antisymm hle bot_le
  have hSIm : Measurable (stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω * H ω s) hmm hmp hmq t) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
      hmm hmp hmq t).mono (ℱ.le t)).measurable
  have hmeas : Measurable fun ω =>
      (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hIAmeas.sub hSIm).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0

end Associativity

/-- The simple integrand `1_{(a, b]}`, for `0 < a < b`. -/
noncomputable def stepIoc (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    SimplePredictable Ω b where
  N := 2
  partition := ![0, a, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hab
  ξ := ![fun _ => 0, fun _ => 1]
  ξ_bounded := by intro i; fin_cases i <;> exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i <;> exact measurable_const

/-- The simple integrand `1_{(0, b]}`, for `0 < b`. -/
noncomputable def stepIoc₀ (Ω) [MeasurableSpace Ω] {b : ℝ} (hb : 0 < b) :
    SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![fun _ => 1]
  ξ_bounded := by intro i; fin_cases i; exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i; exact measurable_const

theorem stepIoc_eval {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (stepIoc Ω ha hab).eval s ω
      = ∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
          then (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_two]
  by_cases h : a < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    show (if (0 : ℝ) < s ∧ s ≤ a then (0 : ℝ) else 0)
      + (if a < s ∧ s ≤ b then (1 : ℝ) else 0) = 0
    simp only [ite_self, zero_add]
    exact ite_eq_right h

theorem stepIoc₀_eval {b : ℝ} (hb : 0 < b) (s : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).eval s ω = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (stepIoc₀ Ω hb).eval s ω
      = ∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
          then (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_one]
  by_cases h : (0 : ℝ) < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
    exact ite_eq_right h

theorem stepIoc_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∀ i : Fin (stepIoc Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc Ω ha hab).partition i.castSucc)) ((stepIoc Ω ha hab).ξ i) := by
  intro i
  fin_cases i <;> exact MeasureTheory.stronglyMeasurable_const

theorem stepIoc₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b) :
    ∀ i : Fin (stepIoc₀ Ω hb).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc₀ Ω hb).partition i.castSucc)) ((stepIoc₀ Ω hb).ξ i) := by
  intro i
  fin_cases i
  exact MeasureTheory.stronglyMeasurable_const

theorem stepIoc_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) (M : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).integralAgainst M t ω = M (min b t) ω - M (min a t) ω := by
  have hrw : (stepIoc Ω ha hab).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp

theorem stepIoc₀_integralAgainst {b : ℝ} (hb : 0 < b) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).integralAgainst M t ω = M (min b t) ω - M (min 0 t) ω := by
  have hrw : (stepIoc₀ Ω hb).integralAgainst M t ω
      = ∑ i : Fin 1, (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp

/-- The `L²` Itô integral depends on the integrand only through the function itself. -/
theorem stochasticIntegralBrownian_congr_fun
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {F₁ F₂ : Ω → ℝ → ℝ} (hEq : F₁ = F₂)
    (hm₁ : Measurable (Function.uncurry F₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ F₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry F₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ F₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ F₁ hm₁ hp₁ hq₁ t
      = stochasticIntegralBrownian W ℱ hℱ F₂ hm₂ hp₂ hq₂ t := by
  subst hEq; rfl

/-- **Locality of the `L²` Itô integral.** Restricting the integrand to `(a, b]` gives the
increment of the integral across `(a, b]`. -/
theorem stochasticIntegralBrownian_indicator_Ioc
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (him : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) him hip hiq t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min b t) ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => (stepIoc₀ Ω hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [stepIoc₀_eval]
    have hpt : ∀ (ω : Ω) (s : ℝ), (stepIoc₀ Ω hab).eval s ω * H ω s
        = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (stepIoc₀ Ω hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (stepIoc₀ Ω hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc₀ Ω hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := stochasticIntegralBrownian_integralAgainst W ℱ hℱ (stepIoc₀ Ω hab)
      (stepIoc₀_adapt ℱ hab) H hm hp hq him' hip' hiq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => stepIoc₀_integralAgainst hab _ t ω)
  · have hfun : (fun ω s => (stepIoc Ω ha' hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [stepIoc_eval]
    have hpt : ∀ (ω : Ω) (s : ℝ), (stepIoc Ω ha' hab).eval s ω * H ω s
        = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (stepIoc Ω ha' hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (stepIoc Ω ha' hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc Ω ha' hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := stochasticIntegralBrownian_integralAgainst W ℱ hℱ (stepIoc Ω ha' hab)
      (stepIoc_adapt ℱ ha' hab) H hm hp hq him' hip' hiq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => stepIoc_integralAgainst ha' hab _ t ω)

end LevyStochCalc.Brownian.Ito

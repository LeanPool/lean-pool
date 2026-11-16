/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutput
public import LeanPool.KLS.LevyStochCalc.Ito.PicardLimit

/-!
# The Picard contraction estimate

The contraction estimate of `bieleckiNorm_picardStep_diff_le` is stated for the Picard step along
two raw path maps. Along two processes of the space its hypotheses are supplied by the frozen
integrand lemmas, and the Bielecki norm of a difference is unchanged by freezing at the horizon, so
the estimate transfers to `picardStepOnStop`, from there through the modification
`picardSelfMap_ae_eq` to `picardSelfMap` itself, and in the same way to the step taken against a
raw state process. The iterates `picardIter` of the self-map are consequently geometrically
Bielecki-Cauchy, and at a weight making the contraction rate `< 1` they converge to
`bieleckiLimit`.

## Main statements

* `bieleckiNorm_picardStepOnStop_diff_le` — the estimate for the step along frozen processes.
* `bieleckiNorm_picardSelfMap_diff_le` — the estimate for the self-map.
* `bieleckiNorm_picardIter_sub_bieleckiLimit_le` — the iterates converge to `bieleckiLimit`.
* `bieleckiNorm_picardStepOnStop_sub_rawStop_le` — the estimate against a raw state process.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The difference of two frozen processes -/

/-- The squared norm of a difference is at most twice the sum of the squared norms. -/
theorem sq_nnnorm_sub_le {α : Type*} [SeminormedAddCommGroup α] (a b : α) :
    (‖a - b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h := norm_sub_le a b
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]
  calc (‖a - b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖a - b‖ ^ 2) := sq_coe_nnnorm _
    _ ≤ ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), sq_coe_nnnorm, sq_coe_nnnorm,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- The difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Y.stop.X s ω) :=
  (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
    (Y.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst))

/-- The norm of the difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub_norm (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X.stop.X s ω - Y.stop.X s ω‖) :=
  (measurable_uncurry_stop_sub X Y).norm

/-- The `ω`-slice of the squared norms of a path map is measurable in time. -/
theorem measurable_sq_slice_time {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (ω : Ω) :
    Measurable fun s : ℝ => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_id.prodMk measurable_const))).nnnorm)).pow_const 2

/-- The squared norms of a path map are jointly measurable. -/
theorem measurable_uncurry_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_snd.prodMk measurable_fst))).nnnorm)).pow_const 2

/-- The energy of a path map over a window is measurable in the sample point. -/
theorem measurable_lintegral_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (b : ℝ) :
    Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
  (measurable_uncurry_sq hZm).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) b))

omit [IsProbabilityMeasure P] in
/-- The energy of the difference of two path maps of finite energy is finite. -/
theorem lintegral_sq_sub_lt_top_of_energy {Z₁ Z₂ : ℝ → Ω → (Fin n → ℝ)}
    (hm₁ : Measurable (Function.uncurry Z₁)) (hm₂ : Measurable (Function.uncurry Z₂))
    (h₁ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h₂ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω : Ω, ∀ s : ℝ, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    refine (sq_nnnorm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = 2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [lintegral_add_left ((measurable_sq_slice_time hm₁ ω).const_mul 2),
      lintegral_const_mul _ (measurable_sq_slice_time hm₁ ω),
      lintegral_const_mul _ (measurable_sq_slice_time hm₂ ω)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
          (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2
            + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := lintegral_congr fun ω => hinner ω
    _ = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [lintegral_add_left ((measurable_lintegral_sq hm₁ b).const_mul 2),
          lintegral_const_mul _ (measurable_lintegral_sq hm₁ b),
          lintegral_const_mul _ (measurable_lintegral_sq hm₂ b)]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (h₁ b),
        ENNReal.mul_lt_top (by norm_num) (h₂ b)⟩

/-- The energy of the difference of two frozen processes is finite on every window. -/
theorem lintegral_sq_stop_sub_lt_top (X Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖X.stop.X s ω - Y.stop.X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_sub_lt_top_of_energy X.stop.measurable_path Y.stop.measurable_path
    (fun c => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le X hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2)))
    (fun c => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le Y hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) b

/-- Freezing at the horizon does not change the Bielecki norm of a difference. -/
theorem bieleckiNorm_stop_sub (β : ℝ) (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.stop.X t ω i - Y.stop.X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) :=
  bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Y.X t ω i

/-! ### The contraction estimate for the step and the self-map -/

/-- **The Picard step along frozen processes is a Bielecki contraction**, with the rate of
`bieleckiNorm_picardStep_diff_le`. -/
theorem bieleckiNorm_picardStepOnStop_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  rw [← bieleckiNorm_stop_sub β X Y]
  exact bieleckiNorm_picardStep_diff_le W N ℱ hℱW hℱN coeffs hLip X.stop.X Y.stop.X x₀
    (fun i j => measurable_sigma_stop coeffs hReg X i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg X i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    (fun i => measurable_mu_stop coeffs hReg X i)
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (measurable_uncurry_stop_sub_norm X Y)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun b _ => lintegral_sq_stop_sub_lt_top X Y hT.le b)
    (measurable_uncurry_stop_sub X Y) hβ hT

/-- **The Picard self-map is a Bielecki contraction.** The self-map is a modification of the step
along the frozen process, and the Bielecki norm is unchanged under modification. -/
theorem bieleckiNorm_picardSelfMap_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  have hcongr : bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i) := by
    refine bieleckiNorm_congr_ae (P := P) β T fun t => ?_
    filter_upwards [picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X t,
      picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y t] with ω hX hY
    funext i
    rw [hX, hY]
  rw [hcongr]
  exact bieleckiNorm_picardStepOnStop_diff_le W N hℱW hℱN coeffs hReg hLip x₀ hβ hT X Y

/-! ### The Picard iterates and their limit -/

/-- A positive Bielecki weight only shrinks the norm on `[0, T]`. -/
theorem bieleckiNorm_le_bieleckiNorm_zero {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T Z ≤ bieleckiNorm (P := P) 0 T Z := by
  refine iSup₂_le fun t ht => ?_
  have hw : ENNReal.ofReal (Real.exp (-β * t)) ≤ ENNReal.ofReal (Real.exp (-0 * t)) := by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ β * t := mul_nonneg hβ ht.1
    nlinarith
  exact le_trans (mul_le_mul' hw le_rfl)
    (le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-0 * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht)

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-- **The Picard iterates** of a starting process under the self-map. -/
noncomputable def picardIter {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    ℕ → SBoundedProcess (n := n) P ℱ' T
  | 0 => X₀
  | k + 1 => picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
      (picardIter hLip x₀ hT X₀ k)

/-- The Picard iterates are geometrically Bielecki-Cauchy at the contraction rate. -/
theorem bieleckiNorm_picardIter_step_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k).X t ω i)
      ≤ ((ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)) ^ k
        * bieleckiNorm (P := P) β T (fun t ω i =>
            (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
              - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans (bieleckiNorm_picardSelfMap_diff_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
      hLip x₀ hβ hT _ _) ?_
    refine le_trans (mul_le_mul' le_rfl ih) (le_of_eq ?_)
    rw [← mul_assoc, ← pow_succ']

/-! ### The limit of the iterates -/

omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference of two processes of the space is finite. -/
theorem bieleckiNorm_sub_lt_top {β : ℝ} (hβ : 0 ≤ β)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) < ⊤ := by
  have hneg : bieleckiNorm (P := P) 0 T (fun t ω => -(Y.X t ω))
      = bieleckiNorm (P := P) 0 T Y.X := by
    unfold bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X.X t ω i - Y.X t ω i)
      = fun t (ω : Ω) => X.X t ω + (fun i => -(Y.X t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y.X t ω)) :=
    measurable_neg.comp Y.measurable_path
  have hadd := bieleckiNorm_add_le (P := P) 0 T X.X (fun t ω => -(Y.X t ω))
    (fun t => bieleckiNorm_inner_aemeasurable _ X.measurable_path t)
    (fun t => bieleckiNorm_inner_aemeasurable (fun t ω => -(Y.X t ω)) hnegm t)
  refine lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨X.sup_L2, Y.sup_L2⟩

/-- **The Picard iterates converge in Bielecki norm.** At a weight making the contraction rate
`< 1`, the iterates converge to `bieleckiLimit` at that rate. -/
theorem bieleckiNorm_picardIter_sub_bieleckiLimit_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k).X t ω i
          - bieleckiLimit
              (fun m => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).X)
              t ω i)
      ≤ ((ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)) ^ k
        * ((1 - (ENNReal.ofReal
              ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
                / (2 * β))) ^ ((1 : ℝ) / 2))⁻¹
            * bieleckiNorm (P := P) β T (fun t ω i =>
                (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
                  - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X
                      t ω i)) :=
  bieleckiNorm_sub_bieleckiLimit_geometric (P := P) β T
    (fun m => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).measurable_path)
    (bieleckiNorm_picardIter_step_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hβ hT X₀)
    hq (bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne k

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg in
/-- Some Bielecki weight makes the contraction rate strictly less than one. -/
theorem exists_bieleckiWeight_rate_lt_one (L : ℝ) (hT : 0 < T) :
    ∃ β : ℝ, 0 < β ∧
      (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2) < 1 := by
  set A : ℝ := 3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2) with hA
  have hAnn : 0 ≤ A := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * T := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) * L ^ 2) := by positivity
    have h3 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
    rw [hA]; linarith
  refine ⟨A / 2 + 1, by linarith, ?_⟩
  have hden : 0 < 2 * (A / 2 + 1) := by linarith
  have hlt : A / (2 * (A / 2 + 1)) < 1 := by
    rw [div_lt_one hden]; linarith
  refine ENNReal.rpow_lt_one ?_ (by norm_num)
  calc ENNReal.ofReal (A / (2 * (A / 2 + 1))) < ENNReal.ofReal 1 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt
    _ = 1 := ENNReal.ofReal_one

/-! ### Bielecki bookkeeping for the fixed point -/

omit [IsProbabilityMeasure P] [ℱ'.IsRightContinuous] in
/-- Slice measurability suffices for the Bielecki subadditivity hypothesis. -/
theorem bieleckiNorm_inner_aemeasurable_of_slice {Y : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i) (t : ℝ) :
    AEMeasurable (fun ω => (∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P :=
  ((Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp (h t i).nnnorm).pow_const 2).pow_const
      ((1 : ℝ) / 2)).aemeasurable

omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference is symmetric. -/
theorem bieleckiNorm_sub_comm (β T : ℝ) (A B : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T (fun t ω i => A t ω i - B t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => B t ω i - A t ω i) := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  congr 2
  refine lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => ?_
  simp only [show A t ω i - B t ω i = -(B t ω i - A t ω i) from by ring, nnnorm_neg]

omit [ℱ'.IsRightContinuous] in
/-- The unweighted Bielecki norm is bounded by the weighted one, at the cost of `e^{βT}`. -/
theorem bieleckiNorm_zero_le_mul {β : ℝ} (hβ : 0 ≤ β) {T : ℝ} (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) 0 T Z
      ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z := by
  refine iSup₂_le fun t ht => ?_
  have hle : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z :=
    le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  have hexp : ENNReal.ofReal (Real.exp (β * t)) ≤ ENNReal.ofReal (Real.exp (β * T)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [ht.2, ht.1]))
  calc ENNReal.ofReal (Real.exp (-0 * t))
        * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.exp (β * t)) * (ENNReal.ofReal (Real.exp (-β * t))
          * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp
    _ ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z :=
        mul_le_mul' hexp hle

omit [ℱ'.IsRightContinuous] in
/-- A path map at finite Bielecki distance from one of finite Bielecki norm has finite Bielecki
norm. -/
theorem bieleckiNorm_lt_top_of_approx (β T : ℝ) {A Z : ℝ → Ω → (Fin n → ℝ)}
    (hAm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => A t ω i)
    (hZm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Z t ω i)
    (hA : bieleckiNorm (P := P) β T A < ⊤)
    (hd : bieleckiNorm (P := P) β T (fun t ω i => A t ω i - Z t ω i) < ⊤) :
    bieleckiNorm (P := P) β T Z < ⊤ := by
  have hEq : Z = fun t (ω : Ω) => A t ω + fun i => Z t ω i - A t ω i := by
    funext t ω i
    simp [Pi.add_apply]
  have hadd := bieleckiNorm_add_le (P := P) β T A (fun t ω => fun i => Z t ω i - A t ω i)
    (bieleckiNorm_inner_aemeasurable_of_slice hAm)
    (bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hZm t i).sub (hAm t i))
  rw [hEq]
  refine lt_of_le_of_lt hadd (ENNReal.add_lt_top.mpr ⟨hA, ?_⟩)
  rwa [bieleckiNorm_sub_comm (P := P) β T Z A]

/-! ### The step against a raw state process -/

omit [ℱ'.IsRightContinuous] in
/-- **The Picard step contracts between a process of the space and a raw state process.** -/
theorem bieleckiNorm_picardStepOnStop_sub_rawStop_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) := by
  have hZsm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hXe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun c =>
    lt_of_le_of_lt (lintegral_lintegral_sq_stop_le X hT.le c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2))
  have hZe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lintegral_sq_rawStop_lt_top hZm hZb hT.le
  have hdiffm : Measurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Z (min s T) ω) :=
    (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
      (hZsm.comp (measurable_snd.prodMk measurable_fst))
  have hrhs : bieleckiNorm (P := P) β T
      (fun t ω i => X.stop.X t ω i - Z (min t T) ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) :=
    bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Z t ω i
  rw [← hrhs]
  exact bieleckiNorm_picardStep_diff_le W N ℱ' hℱW hℱN coeffs hLip X.stop.X
    (fun s ω => Z (min s T) ω) x₀
    (fun i j => measurable_sigma_stop coeffs hReg X i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg X i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i j hT')
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i hT')
    (fun i => measurable_mu_stop coeffs hReg X i)
    (measurable_mu_rawStop coeffs hReg hZm T)
    hdiffm.norm
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZe i hb)
    (fun b _ => lintegral_sq_sub_lt_top_of_energy X.stop.measurable_path hZsm hXe hZe b)
    hdiffm hβ hT

end LevyStochCalc.Ito.Picard

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Concentration
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# WeightedSubgaussian

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weighted sub-Gaussian concentration from weak Gamma-two tails

Internal probability infrastructure for the corrected off-diagonal part of
ABK26's Section 3.1 L2 estimate. It proves the classical tail-to-MGF bridge
and the weighted independent-family estimate needed after finer-shell
coloring. These ordinary reusable probability lemmas make no source-node
status claim.
-/

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums
open scoped BigOperators NNReal ENNReal

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

/-! ### Pointwise real inequality `exp u ≤ u + exp (u²)`. -/

/-- **The centering pointwise bound.**  For every real `u`,
`exp u ≤ u + exp (u²)`.  Used in the small-`t` MGF regime, where subtracting the
linear term `u` uses the mean-zero hypothesis. -/
private theorem exp_le_add_exp_sq (u : ℝ) : Real.exp u ≤ u + Real.exp (u ^ 2) := by
  rcases le_or_gt 1 u with h1 | h1
  · -- `u ≥ 1`: `exp u ≤ exp (u²)` since `u ≤ u²`.
    have hu2 : u ≤ u ^ 2 :=
      calc u = 1 * u := (one_mul u).symm
        _ ≤ u * u := mul_le_mul_of_nonneg_right h1 (by linarith only [h1])
        _ = u ^ 2 := (pow_two u).symm
    have hle : Real.exp u ≤ Real.exp (u ^ 2) := Real.exp_le_exp.mpr hu2
    linarith only [hle, h1]
  · rcases le_or_gt u (-1) with h2 | h2
    · -- `u ≤ -1`: `exp u ≤ 1 ≤ 1 - u ≤ 1 + u² ≤ exp (u²)`.
      have h_exp_le_one : Real.exp u ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith only [h2])
      have hprod : (0 : ℝ) ≤ u ^ 2 + u :=
        calc (0 : ℝ) ≤ (-u) * (-u - 1) :=
              mul_nonneg (by linarith only [h2]) (by linarith only [h2])
          _ = u ^ 2 + u := by ring
      have hq1 : 1 - u ≤ 1 + u ^ 2 := by linarith only [hprod]
      have hq2 : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by
        have := Real.add_one_le_exp (u ^ 2); linarith only [this]
      linarith only [h_exp_le_one, hq1, hq2]
    · -- `|u| ≤ 1`: `exp u ≤ 1 + u + u² ≤ u + exp (u²)`.
      have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩
      have hb : Real.exp u - 1 - u ≤ u ^ 2 :=
        (abs_le.mp (Real.abs_exp_sub_one_sub_id_le habs)).2
      have hq2 : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by
        have := Real.add_one_le_exp (u ^ 2); linarith only [this]
      linarith only [hb, hq2]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Square-exponential moment via the layer-cake formula. -/

/-- **Square-exponential moment bound.**  For a nonnegative `W` with the clean
exponential tail `P[W > s] ≤ 2 exp(−s)` and `0 ≤ l < 1`, the variable
`exp (l·W)` is integrable with `∫ exp (l·W) ≤ 1 + 2l/(1−l)`.  Proved by the
weighted layer-cake formula: `E[exp l W] = 1 + ∫₀^∞ P[W>s]·l e^{ls} ds`, and the
tail bounds the density integral by `∫₀^∞ 2 l e^{(l−1)s} ds = 2l/(1−l)`. -/
theorem integral_exp_smul_le_of_tail {W : Ω → ℝ} (hW_meas : AEMeasurable W μ)
    (hW_nn : 0 ≤ᵐ[μ] W)
    (hW_tail : ∀ s : ℝ, 0 < s → μ.real {ω | s < W ω} ≤ 2 * Real.exp (-s))
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1) :
    Integrable (fun ω => Real.exp (l * W ω)) μ ∧
      ∫ ω, Real.exp (l * W ω) ∂μ ≤ 1 + 2 * l / (1 - l) := by
  have hposl : (0 : ℝ) < 1 - l := by linarith only [hl1]
  have hlne : l - 1 ≠ 0 := ne_of_lt (by linarith only [hl1])
  set g : ℝ → ℝ := fun s => l * Real.exp (l * s) with hg
  have hg_nn : ∀ t : ℝ, 0 ≤ g t := fun t => mul_nonneg hl0 (Real.exp_pos _).le
  -- Fundamental theorem of calculus: `∫₀^y l e^{ls} = e^{ly} − 1`.
  have hFTC : ∀ y : ℝ, ∫ s in (0:ℝ)..y, g s = Real.exp (l * y) - 1 := by
    intro y
    have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) y,
        HasDerivAt (fun s => Real.exp (l * s)) (g s) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => l * s) l s := by
        simpa using (hasDerivAt_id s).const_mul l
      have h2 := h1.exp
      simpa [hg, mul_comm] using h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous g).intervalIntegrable 0 y)]
    simp
  -- a.e. rewrite `ofReal (exp l W) = ofReal (∫₀^W g) + 1`.
  have hsplit : (fun ω => ENNReal.ofReal (Real.exp (l * W ω)))
      =ᵐ[μ] (fun ω => ENNReal.ofReal (∫ s in (0:ℝ)..(W ω), g s) + 1) := by
    filter_upwards [hW_nn] with ω hω
    have hge : (0 : ℝ) ≤ Real.exp (l * W ω) - 1 := by
      have h1 : (1 : ℝ) ≤ Real.exp (l * W ω) := Real.one_le_exp (mul_nonneg hl0 hω)
      linarith only [h1]
    rw [hFTC (W ω), ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hge zero_le_one]
    congr 1; ring
  -- the layer-cake identity.
  have hg_intble : ∀ t > (0:ℝ), IntervalIntegrable g volume 0 t :=
    fun t _ => (by fun_prop : Continuous g).intervalIntegrable 0 t
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ hW_nn hW_meas hg_intble
    (Filter.Eventually.of_forall hg_nn)
  -- bound the density integral.
  have hRHS : ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < W a} * ENNReal.ofReal (g t)
      ≤ ENNReal.ofReal (2 * l / (1 - l)) := by
    have hbound : ∀ t : ℝ,
        μ {a | t < W a} * ENNReal.ofReal (g t)
          ≤ ENNReal.ofReal (2 * l * Real.exp ((l - 1) * t)) := by
      intro t
      have hmeas_le : μ {a | t < W a} ≤ ENNReal.ofReal (2 * Real.exp (-t)) := by
        rcases le_or_gt t 0 with ht | ht
        · refine le_trans (le_of_le_of_eq (measure_mono (Set.subset_univ _)) measure_univ) ?_
          rw [ENNReal.one_le_ofReal]
          have := Real.one_le_exp (show (0:ℝ) ≤ -t by linarith only [ht])
          linarith only [this]
        · rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
          exact ENNReal.ofReal_le_ofReal (hW_tail t ht)
      calc μ {a | t < W a} * ENNReal.ofReal (g t)
          ≤ ENNReal.ofReal (2 * Real.exp (-t)) * ENNReal.ofReal (g t) :=
            mul_le_mul_left hmeas_le _
        _ = ENNReal.ofReal (2 * Real.exp (-t) * g t) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (2 * l * Real.exp ((l - 1) * t)) := by
            congr 1
            rw [hg, show (l - 1) * t = -t + l * t by ring, Real.exp_add]; ring
    have hint2 : Integrable (fun t => 2 * l * Real.exp ((l - 1) * t))
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      (integrableOn_exp_mul_Ioi (show l - 1 < 0 by linarith only [hl1]) 0).const_mul (2 * l)
    have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
        (fun t => 2 * l * Real.exp ((l - 1) * t)) :=
      Filter.Eventually.of_forall (fun t => by positivity)
    have heval : ∫ t in Set.Ioi (0:ℝ), 2 * l * Real.exp ((l - 1) * t) = 2 * l / (1 - l) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (show l - 1 < 0 by linarith only [hl1]) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp
      ring
    calc ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < W a} * ENNReal.ofReal (g t)
        ≤ ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * l * Real.exp ((l - 1) * t)) :=
          lintegral_mono hbound
      _ = ENNReal.ofReal (∫ t in Set.Ioi (0:ℝ), 2 * l * Real.exp ((l - 1) * t)) :=
          (ofReal_integral_eq_lintegral_ofReal hint2 hnn2).symm
      _ = ENNReal.ofReal (2 * l / (1 - l)) := by rw [heval]
  -- assemble the master `∫⁻` bound.
  have hmain : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * W ω)) ∂μ
      ≤ ENNReal.ofReal (1 + 2 * l / (1 - l)) := by
    rw [lintegral_congr_ae hsplit,
      lintegral_add_right _ measurable_const, lintegral_one, measure_univ, hlayer]
    have hsum : ENNReal.ofReal (1 + 2 * l / (1 - l))
        = ENNReal.ofReal (2 * l / (1 - l)) + 1 := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by positivity) zero_le_one]
      congr 1; ring
    rw [hsum]
    exact add_le_add hRHS le_rfl
  -- integrability and the integral bound.
  have hf_nn : 0 ≤ᵐ[μ] (fun ω => Real.exp (l * W ω)) :=
    Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
  have hf_meas : AEStronglyMeasurable (fun ω => Real.exp (l * W ω)) μ :=
    (Real.measurable_exp.comp_aemeasurable (hW_meas.const_mul l)).aestronglyMeasurable
  have hf_int : Integrable (fun ω => Real.exp (l * W ω)) μ := by
    refine ⟨hf_meas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hf_nn]
    exact lt_of_le_of_lt hmain ENNReal.ofReal_lt_top
  refine ⟨hf_int, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf_nn hf_meas]
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (l * W ω)) ∂μ).toReal
      ≤ (ENNReal.ofReal (1 + 2 * l / (1 - l))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 1 + 2 * l / (1 - l) := ENNReal.toReal_ofReal (by positivity)

/-! ### The tail → MGF converter. -/

/-- A centered real random variable `X` (`∫ X = 0`) with the two-sided sub-Gaussian
tail `P[|X| > t] ≤ 2 exp(−t²/c)` (`c > 0`) has a sub-Gaussian moment generating
function with the universal parameter `8·c`: `HasSubgaussianMG (8·c) μ`.

Centering and measurability are honest hypotheses (mean-zero comes from the
spine downstream). -/
theorem hasSubgaussianMGF_of_tail {X : Ω → ℝ} (hX : AEMeasurable X μ) {c : ℝ≥0}
    (hc : 0 < c) (hcenter : ∫ ω, X ω ∂μ = 0)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < |X ω|} ≤ 2 * Real.exp (- t ^ 2 / c)) :
    HasSubgaussianMGF X (8 * c) μ := by
  set cc : ℝ := (c : ℝ) with hccdef
  have hcc : (0 : ℝ) < cc := by rw [hccdef]; exact_mod_cast hc
  have hccne : cc ≠ 0 := ne_of_gt hcc
  set W : Ω → ℝ := fun ω => (X ω) ^ 2 / cc with hWdef
  have hW_meas : AEMeasurable W μ := (hX.pow_const 2).div_const cc
  have hW_nn : 0 ≤ᵐ[μ] W := Filter.Eventually.of_forall (fun ω => by rw [hWdef]; positivity)
  -- the `W`-tail `P[W > s] ≤ 2 exp(−s)`.
  have hW_tail : ∀ s : ℝ, 0 < s → μ.real {ω | s < W ω} ≤ 2 * Real.exp (-s) := by
    intro s hs
    have hsub : {ω | s < W ω} ⊆ {ω | Real.sqrt (cc * s) < |X ω|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h1 : cc * s < (X ω) ^ 2 := by
        rw [hWdef, lt_div_iff₀ hcc] at hω; linarith only [hω]
      have h2 : Real.sqrt (cc * s) < Real.sqrt ((X ω) ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) h1
      rwa [Real.sqrt_sq_eq_abs] at h2
    calc μ.real {ω | s < W ω}
        ≤ μ.real {ω | Real.sqrt (cc * s) < |X ω|} := measureReal_mono hsub
      _ ≤ 2 * Real.exp (- (Real.sqrt (cc * s)) ^ 2 / c) :=
          htail _ (Real.sqrt_pos.mpr (by positivity))
      _ = 2 * Real.exp (-s) := by
          rw [Real.sq_sqrt (show (0:ℝ) ≤ cc * s by positivity)]
          congr 2
          rw [neg_div, mul_comm cc s, mul_div_assoc, div_self hccne, mul_one]
  -- Young's inequality `t X ≤ cc t²/2 + W/2`, pointwise.
  have hYoung : ∀ (t : ℝ) (ω : Ω), t * X ω ≤ cc * t ^ 2 / 2 + W ω / 2 := by
    intro t ω
    have e : cc * t ^ 2 / 2 + (X ω) ^ 2 / (2 * cc)
        = (cc ^ 2 * t ^ 2 + (X ω) ^ 2) / (2 * cc) := by
      rw [div_add_div _ _ (by norm_num) (by positivity), div_eq_div_iff (by positivity)
        (by positivity)]; ring
    have hW2 : W ω / 2 = (X ω) ^ 2 / (2 * cc) := by rw [hWdef]; ring
    rw [hW2, e, le_div_iff₀ (by positivity)]
    have hsq : (0 : ℝ) ≤ cc ^ 2 * t ^ 2 + (X ω) ^ 2 - t * X ω * (2 * cc) :=
      calc (0 : ℝ) ≤ (cc * t - X ω) ^ 2 := sq_nonneg _
        _ = cc ^ 2 * t ^ 2 + (X ω) ^ 2 - t * X ω * (2 * cc) := by ring
    linarith only [hsq]
  -- integrability of `exp (t X)` for all `t`, via domination.
  have hexpW_half := integral_exp_smul_le_of_tail hW_meas hW_nn hW_tail
    (l := (1:ℝ)/2) (by norm_num) (by norm_num)
  have hintExp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ := by
    intro t
    have hdom : Integrable (fun ω => Real.exp (cc * t ^ 2 / 2) * Real.exp ((1/2) * W ω)) μ :=
      hexpW_half.1.const_mul _
    refine hdom.mono' ((Real.measurable_exp.comp_aemeasurable
      (hX.const_mul t)).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hYoung t ω
    linarith only [this]
  -- `X ∈ L¹` from `0 ∈ interior (integrableExpSet X)`.
  have hExpSet : integrableExpSet X μ = Set.univ :=
    Set.eq_univ_of_forall (fun t => hintExp t)
  have hintX : Integrable X μ :=
    integrable_of_mem_interior_integrableExpSet (by rw [hExpSet]; simp)
  -- the MGF bound `mgf X t ≤ exp (4 cc t²)`.
  have hmgf : ∀ t : ℝ, mgf X μ t ≤ Real.exp (4 * cc * t ^ 2) := by
    intro t
    rw [mgf]
    rcases le_or_gt (cc * t ^ 2) (1/2) with hsmall | hlarge
    · -- small regime.
      set l : ℝ := cc * t ^ 2 with hl
      have hl0 : 0 ≤ l := by rw [hl]; positivity
      have hl1 : l < 1 := by linarith only [hsmall]
      have hW := integral_exp_smul_le_of_tail hW_meas hW_nn hW_tail hl0 hl1
      -- pointwise `exp (t X) ≤ t X + exp (l W)`.
      have hpt : ∀ ω, Real.exp (t * X ω) ≤ t * X ω + Real.exp (l * W ω) := by
        intro ω
        have := exp_le_add_exp_sq (t * X ω)
        have heq : (t * X ω) ^ 2 = l * W ω := by
          have hWω : l * W ω = t ^ 2 * X ω ^ 2 := by
            rw [hl]; change cc * t ^ 2 * (X ω ^ 2 / cc) = t ^ 2 * X ω ^ 2
            field_simp
          rw [hWω]; ring
        rwa [heq] at this
      have hmono : ∫ ω, Real.exp (t * X ω) ∂μ
          ≤ ∫ ω, (t * X ω + Real.exp (l * W ω)) ∂μ :=
        integral_mono (hintExp t) ((hintX.const_mul t).add hW.1) hpt
      rw [integral_add (hintX.const_mul t) hW.1, integral_const_mul, hcenter] at hmono
      have hle : ∫ ω, Real.exp (l * W ω) ∂μ ≤ 1 + 4 * l := by
        refine le_trans hW.2 ?_
        rw [add_le_add_iff_left, div_le_iff₀ (by linarith only [hl1] : (0:ℝ) < 1 - l)]
        have hprod : (0 : ℝ) ≤ 2 * l * (1 - 2 * l) :=
          mul_nonneg (by linarith only [hl0]) (by linarith only [hsmall])
        calc 2 * l = 4 * l * (1 - l) - 2 * l * (1 - 2 * l) := by ring
          _ ≤ 4 * l * (1 - l) := by linarith only [hprod]
      calc ∫ ω, Real.exp (t * X ω) ∂μ
          ≤ t * 0 + ∫ ω, Real.exp (l * W ω) ∂μ := hmono
        _ ≤ 1 + 4 * l := by rw [mul_zero, zero_add]; exact hle
        _ ≤ Real.exp (4 * l) := by
              have := Real.add_one_le_exp (4 * l); linarith only [this]
        _ = Real.exp (4 * cc * t ^ 2) := by rw [hl]; congr 1; ring
    · -- large regime.
      have hW := (integral_exp_smul_le_of_tail hW_meas hW_nn hW_tail
        (l := (1:ℝ)/2) (by norm_num) (by norm_num))
      have hpt : ∀ ω, Real.exp (t * X ω)
          ≤ Real.exp (cc * t ^ 2 / 2) * Real.exp ((1/2) * W ω) := by
        intro ω
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith only [hYoung t ω]
      have hmono : ∫ ω, Real.exp (t * X ω) ∂μ
          ≤ ∫ ω, Real.exp (cc * t ^ 2 / 2) * Real.exp ((1/2) * W ω) ∂μ :=
        integral_mono (hintExp t) (hW.1.const_mul _) hpt
      rw [integral_const_mul] at hmono
      have h3 : ∫ ω, Real.exp ((1/2) * W ω) ∂μ ≤ 3 := by
        refine le_trans hW.2 ?_; norm_num
      have hchain : ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (cc * t ^ 2 / 2) * 3 := by
        refine le_trans hmono ?_
        exact mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      refine le_trans hchain ?_
      -- absorb the factor `3`: `c t² > 1/2 ⟹ 3 ≤ exp (7 c t²/2)`.
      have hexp74 : (3 : ℝ) ≤ Real.exp (7 / 4) := by
        have he1 : (2.7 : ℝ) ≤ Real.exp 1 := le_of_lt (by
          have := Real.exp_one_gt_d9; linarith only [this])
        have he2 : (1 : ℝ) + 3 / 4 ≤ Real.exp (3 / 4) := by
          have := Real.add_one_le_exp (3 / 4); linarith only [this]
        have : Real.exp (7 / 4) = Real.exp 1 * Real.exp (3 / 4) := by
          rw [← Real.exp_add]; norm_num
        rw [this]
        calc (3 : ℝ) ≤ 2.7 * (1 + 3 / 4) := by norm_num
          _ ≤ Real.exp 1 * Real.exp (3 / 4) :=
              mul_le_mul he1 he2 (by norm_num) (Real.exp_pos 1).le
      have hbig : (3 : ℝ) ≤ Real.exp (7 * cc * t ^ 2 / 2) :=
        le_trans hexp74 (Real.exp_le_exp.mpr (by linarith only [hlarge]))
      calc Real.exp (cc * t ^ 2 / 2) * 3
          ≤ Real.exp (cc * t ^ 2 / 2) * Real.exp (7 * cc * t ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hbig (Real.exp_pos _).le
        _ = Real.exp (4 * cc * t ^ 2) := by rw [← Real.exp_add]; congr 1; ring
  -- assemble the structure.
  refine ⟨hintExp, fun t => ?_⟩
  refine le_trans (hmgf t) (le_of_eq ?_)
  rw [show ((8 * c : ℝ≥0) : ℝ) = 8 * cc by rw [hccdef]; push_cast; ring]
  congr 1; ring

/-- `weightedSubgaussianConst ^ 2 / 2 = 1 + log 2`, which lets the union-bound factor
`2` be absorbed into the `t ≥ 1` decay: `2 · exp(−(1+log 2) t²) ≤ exp(−t²)`. -/
noncomputable def weightedSubgaussianConst : ℝ := Real.sqrt (2 * (1 + Real.log 2))

theorem weightedSubgaussianConst_pos : 0 < weightedSubgaussianConst := by
  have : (0 : ℝ) < 2 * (1 + Real.log 2) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  exact Real.sqrt_pos.mpr this

theorem weightedSubgaussianConst_sq :
    weightedSubgaussianConst ^ 2 = 2 * (1 + Real.log 2) := by
  have hnn : (0 : ℝ) ≤ 2 * (1 + Real.log 2) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  unfold weightedSubgaussianConst
  rw [Real.sq_sqrt hnn]

/-- Pure-real absorption of the union-bound factor `2`: for `t ≥ 1`,
`2 · exp(−((1 + log 2) t²)) ≤ exp(−(t ^ (2:ℝ)))`.  Extracted so no numeric
tactic ever enters a `Real.rpow`/`Real.exp` term. -/
theorem two_mul_exp_neg_log_two_le (t : ℝ) (ht : 1 ≤ t) :
    2 * Real.exp (-((1 + Real.log 2) * t ^ 2)) ≤ Real.exp (-(t ^ (2 : ℝ))) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith only [ht]
  have htsq : (1 : ℝ) ≤ t ^ 2 :=
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ t * t := mul_le_mul ht ht zero_le_one ht0
      _ = t ^ 2 := (pow_two t).symm
  have hrpow : t ^ (2 : ℝ) = t ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrpow]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsplit : -((1 + Real.log 2) * t ^ 2)
      = -(t ^ 2) + (-(Real.log 2 * t ^ 2)) := by ring
  rw [hsplit, Real.exp_add]
  have hle : Real.exp (-(Real.log 2 * t ^ 2)) ≤ Real.exp (-Real.log 2) := by
    apply Real.exp_le_exp.2
    have hmul : Real.log 2 * 1 ≤ Real.log 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_left htsq hlog2.le
    linarith only [hmul]
  have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  calc 2 * (Real.exp (-(t ^ 2)) * Real.exp (-(Real.log 2 * t ^ 2)))
      ≤ 2 * (Real.exp (-(t ^ 2)) * Real.exp (-Real.log 2)) := by gcongr
    _ = 2 * (1 / 2) * Real.exp (-(t ^ 2)) := by rw [hhalf]; ring
    _ = Real.exp (-(t ^ 2)) := by ring

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ} {c : ι → ℝ≥0} {s : Finset ι}

/-- **Weighted sub-Gaussian tail (raw two-sided form).**  For whole-family
independent `X` with per-term sub-Gaussian MGF `HasSubgaussianMGF (X i) (c i)`,
real weights `a`, and any `ε ≥ 0`,
`μ.real {ω | ε < |Σ_{i∈s} a i X i ω|} ≤ 2 exp(−ε²/(2 Σ_{i∈s} (a i)² c i))`.
The weighted sum is sub-Gaussian by `const_mul` (scaling by `a i` multiplies the
parameter by `(a i)²`), `iIndepFun.comp` (the scaled family stays independent)
and `sum_of_iIndepFun`; the union of the two Chernoff tails carries the `2`. -/
theorem measureReal_abs_weightedSum_gt_le (a : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε < |∑ i ∈ s, a i * X i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, (a i) ^ 2 * (c i : ℝ))) := by
  -- the scaled family stays independent.
  have hindep' : iIndepFun (fun i ω => a i * X i ω) μ := by
    have h := h_indep.comp (fun i (x : ℝ) => a i * x)
      (fun i => (measurable_id.const_mul (a i)))
    simpa [Function.comp_def] using h
  -- `Σ a i X i` is sub-Gaussian; the ℝ≥0 parameter is inferred (never spelled).
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun (μ := μ) hindep'
    (fun i hi => (h_subG i hi).const_mul (a i))
  -- the two Chernoff tails, at the same parameter.
  have hR := hsum.measure_ge_le hε
  have hL := hsum.neg.measure_ge_le hε
  -- push the coercion of the ℝ≥0 parameter to the real variance `Σ (a i)² c i`.
  simp only [NNReal.coe_sum, Pi.neg_apply] at hR hL
  have hsub : {ω | ε < |∑ i ∈ s, a i * X i ω|}
      ⊆ {ω | ε ≤ ∑ i ∈ s, a i * X i ω} ∪ {ω | ε ≤ -∑ i ∈ s, a i * X i ω} := by
    intro ω hω
    have hω' : ε < |∑ i ∈ s, a i * X i ω| := hω
    rcases le_or_gt (∑ i ∈ s, a i * X i ω) 0 with h | h
    · rw [abs_of_nonpos h] at hω'
      exact Or.inr (le_of_lt hω')
    · rw [abs_of_pos h] at hω'
      exact Or.inl (le_of_lt hω')
  calc μ.real {ω | ε < |∑ i ∈ s, a i * X i ω|}
      ≤ μ.real ({ω | ε ≤ ∑ i ∈ s, a i * X i ω} ∪ {ω | ε ≤ -∑ i ∈ s, a i * X i ω}) :=
        measureReal_mono hsub (by finiteness)
    _ ≤ μ.real {ω | ε ≤ ∑ i ∈ s, a i * X i ω}
          + μ.real {ω | ε ≤ -∑ i ∈ s, a i * X i ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, (a i) ^ 2 * (c i : ℝ)))
          + Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, (a i) ^ 2 * (c i : ℝ))) :=
        add_le_add hR hL
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, (a i) ^ 2 * (c i : ℝ))) := by ring

omit [IsProbabilityMeasure μ] in
/-- If the weighted variance `Σ_{i∈s} (a i)² c i` vanishes then the weighted sum
is a.e. zero: each term is either `0` (weight) or a.e. `0` (a `HasSubgaussianMGF
· 0` variable). -/
theorem weightedSum_ae_zero_of_variance_zero (a : ι → ℝ)
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    (hV0 : ∑ i ∈ s, (a i) ^ 2 * (c i : ℝ) = 0) :
    (fun ω => ∑ i ∈ s, a i * X i ω) =ᵐ[μ] 0 := by
  have hnn : ∀ i ∈ s, (0 : ℝ) ≤ (a i) ^ 2 * (c i : ℝ) :=
    fun i _ => mul_nonneg (sq_nonneg _) (c i).coe_nonneg
  have hterm0 : ∀ i ∈ s, (a i) ^ 2 * (c i : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hV0
  have hzero : ∀ i ∈ s, (fun ω => a i * X i ω) =ᵐ[μ] 0 := by
    intro i hi
    by_cases ha : a i = 0
    · filter_upwards with ω; simp [ha]
    · have hci : c i = 0 := by
        have hsq : (0 : ℝ) < (a i) ^ 2 := by positivity
        have hc0 : (c i : ℝ) = 0 := by
          rcases mul_eq_zero.1 (hterm0 i hi) with h | h
          · exact absurd h (ne_of_gt hsq)
          · exact h
        exact NNReal.coe_eq_zero.1 hc0
      have hXi : X i =ᵐ[μ] 0 :=
        HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zero (by rw [← hci]; exact h_subG i hi)
      filter_upwards [hXi] with ω hω; simp [hω]
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ s, a i * X i ω = 0 := by
    rw [Finset.eventually_all]
    intro i hi
    filter_upwards [hzero i hi] with ω hω
    simpa using hω
  filter_upwards [hall] with ω hω
  simp only [Pi.zero_apply]
  exact Finset.sum_eq_zero (fun i hi => hω i hi)

/-- **Weighted sub-Gaussian concentration (normalized `gammaSigma 2` form).**
For whole-family independent `X` with per-term sub-Gaussian MGF, real weights
`a`, and every `t ≥ 1`,
`μ.real {ω | C · (Σ a² c)^{1/2} · t < |Σ a X ω|} ≤ exp(−(t ^ 2))`, where
`C = weightedSubgaussianConst`.  This is definitionally
`IsBigO μ (gammaSigma 2) (Σ a X) (C (Σ a² c)^{1/2})`. -/
theorem weightedSum_subgaussian_tail (a : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    ∀ ⦃t : ℝ⦄, 1 ≤ t →
      μ.real {ω | weightedSubgaussianConst
          * Real.sqrt (∑ i ∈ s, (a i) ^ 2 * (c i : ℝ)) * t
          < |∑ i ∈ s, a i * X i ω|}
        ≤ Real.exp (-(t ^ (2 : ℝ))) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := by linarith only [ht]
  set V : ℝ := ∑ i ∈ s, (a i) ^ 2 * (c i : ℝ) with hVdef
  have hVnn : 0 ≤ V :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (c i).coe_nonneg)
  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · -- degenerate case `V = 0`: the sum is a.e. zero.
    have hsqrt0 : Real.sqrt V = 0 := by rw [← hV0]; exact Real.sqrt_zero
    have haez := weightedSum_ae_zero_of_variance_zero (μ := μ) (X := X) (c := c) (s := s) a
      h_subG hV0.symm
    have haez' : ∀ᵐ ω ∂μ, (∑ i ∈ s, a i * X i ω) = 0 := by
      filter_upwards [haez] with ω hω; simpa using hω
    simp only [hsqrt0, mul_zero, zero_mul]
    have hnull : μ {ω | (0 : ℝ) < |∑ i ∈ s, a i * X i ω|} = 0 := by
      apply measure_mono_null _ (ae_iff.1 haez')
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      intro hcontra
      rw [hcontra] at hω; simp at hω
    rw [(measureReal_eq_zero_iff (by finiteness)).mpr hnull]; positivity
  · -- non-degenerate case `V > 0`.
    have hVne : V ≠ 0 := ne_of_gt hVpos
    set A : ℝ := weightedSubgaussianConst * Real.sqrt V with hAdef
    have hAnn : 0 ≤ A :=
      mul_nonneg weightedSubgaussianConst_pos.le (Real.sqrt_nonneg _)
    have hε : 0 ≤ A * t := mul_nonneg hAnn ht0
    have hraw := measureReal_abs_weightedSum_gt_le (μ := μ) (X := X) (c := c) (s := s) a
      h_indep h_subG (ε := A * t) hε
    rw [← hVdef] at hraw
    refine hraw.trans ?_
    -- rewrite the Chernoff exponent into the `(1 + log 2) t²` form.
    have h2V : (2 : ℝ) * V ≠ 0 := (mul_pos (by norm_num) hVpos).ne'
    have hAsq : A ^ 2 = 2 * (1 + Real.log 2) * V := by
      rw [hAdef, mul_pow, weightedSubgaussianConst_sq, Real.sq_sqrt hVnn]
    have hexp : -(A * t) ^ 2 / (2 * V) = -((1 + Real.log 2) * t ^ 2) := by
      have hAt : (A * t) ^ 2 = ((1 + Real.log 2) * t ^ 2) * (2 * V) := by
        rw [mul_pow, hAsq]; ring
      rw [hAt, neg_div, mul_div_assoc, div_self h2V, mul_one]
    rw [hexp]
    exact two_mul_exp_neg_log_two_le t ht

/-- The weighted sub-Gaussian tail in CoarseGraining's `Gamma_2` rendering. -/
theorem weightedSum_isBigO_gammaSigma_two
    {X : ι → Ω → ℝ} {c : ι → ℝ≥0} {s : Finset ι} (a : ι → ℝ)
    (h_indep : iIndepFun X μ)
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    IsBigO μ (gammaSigma 2) (fun omega => ∑ i ∈ s, a i * X i omega)
      (weightedSubgaussianConst *
        Real.sqrt (∑ i ∈ s, (a i) ^ 2 * (c i : ℝ))) := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  exact weightedSum_subgaussian_tail a h_indep h_subG ht

/-- The two-sided tail `P[|X| > u] ≤ 2 exp(−u²/(2A²))` (all `u > 0`) is fed to
`hasSubgaussianMGF_of_tail` with `c = 2A²`, `κ = 8`. -/
theorem hasSubgaussianMGF_of_isBigO_gammaSigma_two {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {A : ℝ} (hA : 0 < A)
    (hcenter : ∫ ω, X ω ∂μ = 0) (hbd : IsBigO μ (gammaSigma 2) X A) :
    HasSubgaussianMGF X (8 * (2 * A ^ 2).toNNReal) μ := by
  set c : ℝ≥0 := (2 * A ^ 2).toNNReal with hcdef
  have hccoe : (c : ℝ) = 2 * A ^ 2 := by rw [hcdef, Real.coe_toNNReal _ (by positivity)]
  have hcpos : 0 < c := by rw [hcdef]; exact Real.toNNReal_pos.mpr (by positivity)
  rw [isBigO_gammaSigma_iff] at hbd
  refine hasSubgaussianMGF_of_tail hX hcpos hcenter (fun u hu => ?_)
  rw [hccoe]
  rcases le_or_gt A u with hAu | hAu
  · -- `u ≥ A`: use the weak-Orlicz decay at `t = u/A ≥ 1`.
    have ht1 : (1 : ℝ) ≤ u / A := (one_le_div hA).mpr hAu
    have hb := hbd ht1
    have hAtu : A * (u / A) = u := mul_div_cancel₀ u (ne_of_gt hA)
    rw [hAtu] at hb
    refine le_trans hb ?_
    have hpow : ((u / A) ^ (2 : ℝ)) = u ^ 2 / A ^ 2 := by rw [Real.rpow_two, div_pow]
    rw [hpow]
    have hden : u ^ 2 / (2 * A ^ 2) ≤ u ^ 2 / A ^ 2 := by
      gcongr
      · linarith only [sq_nonneg A]
    have hle_exp : Real.exp (-(u ^ 2 / A ^ 2)) ≤ Real.exp (-u ^ 2 / (2 * A ^ 2)) := by
      apply Real.exp_le_exp.mpr; rw [neg_div]; linarith only [hden]
    linarith only [hle_exp, Real.exp_pos (-u ^ 2 / (2 * A ^ 2))]
  · -- `0 < u < A`: the probability bound `≤ 1` suffices.
    have h1 : μ.real {ω | u < |X ω|} ≤ 1 := by
      rw [← probReal_univ (μ := μ)]; exact measureReal_mono (Set.subset_univ _)
    refine le_trans h1 ?_
    have hexp_half_le : Real.exp (1 / 2) ≤ 2 := by
      have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [pow_two, ← Real.exp_add]; norm_num
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
      rw [hsq]
      linarith only [Real.exp_one_lt_d9]
    have hexphalf : (1 : ℝ) ≤ 2 * Real.exp (-(1 / 2)) := by
      have hinv : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
        rw [← Real.exp_add]; norm_num
      have hmul : Real.exp (-(1 / 2)) * Real.exp (1 / 2) ≤ Real.exp (-(1 / 2)) * 2 :=
        mul_le_mul_of_nonneg_left hexp_half_le (Real.exp_pos _).le
      linarith only [hinv, hmul]
    have hmono : Real.exp (-(1 / 2)) ≤ Real.exp (-u ^ 2 / (2 * A ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      have hlt : u ^ 2 / (2 * A ^ 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have hprod : (0 : ℝ) ≤ A ^ 2 - u ^ 2 :=
          calc (0 : ℝ) ≤ (A - u) * (A + u) :=
                mul_nonneg (by linarith only [hAu]) (by linarith only [hu, hA])
            _ = A ^ 2 - u ^ 2 := by ring
        linarith only [hprod]
      linarith only [hlt]
    linarith only [hexphalf, hmono]

/-- The weighted tail-to-MGF estimate with possibly vanishing scales.  A
zero-scale summand must be almost surely zero; positive-scale summands use the
tail-to-MGF converter above.  This is the form needed when deterministic local
energies supply the scales and some cells can carry no energy. -/
theorem weightedSum_of_gammaSigma_tails_nonneg
    {X : ι → Ω → ℝ} {A : ι → ℝ} {s : Finset ι}
    (a : ι → ℝ) (h_indep : iIndepFun X μ)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hA : ∀ i ∈ s, 0 ≤ A i)
    (hzero : ∀ i ∈ s, A i = 0 → X i =ᵐ[μ] 0)
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (htail : ∀ i ∈ s, IsBigO μ (gammaSigma 2) (X i) (A i)) :
    IsBigO μ (gammaSigma 2) (fun ω => ∑ i ∈ s, a i * X i ω)
      (weightedSubgaussianConst
        * Real.sqrt (∑ i ∈ s, (a i) ^ 2 * (16 * (A i) ^ 2))) := by
  set c : ι → ℝ≥0 := fun i => 8 * (2 * (A i) ^ 2).toNNReal with hcdef
  have hcoe : ∀ i, (c i : ℝ) = 16 * (A i) ^ 2 := by
    intro i
    rw [hcdef, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    push_cast
    ring
  have h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ := by
    intro i hi
    rcases (hA i hi).eq_or_lt with hAi | hAi
    · have hc0 : c i = 0 := by
        apply NNReal.eq
        rw [hcoe i, ← hAi]
        norm_num
      rw [hc0]
      exact HasSubgaussianMGF.fun_zero.congr (hzero i hi hAi.symm).symm
    · exact hasSubgaussianMGF_of_isBigO_gammaSigma_two
        (hX i hi) hAi (hcenter i hi) (htail i hi)
  have hres := weightedSum_isBigO_gammaSigma_two
    (μ := μ) (X := X) (c := c) (s := s) a h_indep h_subG
  have hsum_eq :
      ∑ i ∈ s, (a i) ^ 2 * ((c i : ℝ)) =
        ∑ i ∈ s, (a i) ^ 2 * (16 * (A i) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => by rw [hcoe i])
  rw [hsum_eq] at hres
  exact hres

end Algsuperdiff.Section3.Provider.Orlicz

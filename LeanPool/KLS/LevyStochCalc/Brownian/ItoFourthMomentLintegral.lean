/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with source adaptations
-- (deprecated names, proof-context visibility, the v4.35.0 `eLpNorm`/`MemLp` API) listed in
-- vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_two_rpow_eq_lintegral_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFourthMomentPartialSums

/-!
# Fourth moment of the `L²` Itô integral

Truncation of a simple integrand and the `lintegral` form of the fourth-moment bound. Clamping
the coefficients to `[-C, C]` (`SimplePredictable.truncate`) moves a value no further from a
target already in `[-C, C]`, so a truncated approximant is still an approximant; the bound for
the simple integrands then passes to the `L²` Itô integral of any integrand bounded by `C` by
Fatou along an almost-everywhere convergent subsequence.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A function fixing `0` commutes with a step sum over a strictly monotone partition. -/
theorem comp_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f : Fin M → ℝ) (s : ℝ) (g : ℝ → ℝ) (hg0 : g 0 = 0) :
    g (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g (f j) else 0 := by
  classical
  by_cases h : ∃ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ → j = j₀ := by
      intro j hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (j.succ : Fin (M + 1)) ≤ j₀.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
        exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hj₀.1)
      · have hle : (j₀.succ : Fin (M + 1)) ≤ j.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
        exact absurd (hj₀.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
    have hsum : ∀ h : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h j else 0) = h j₀ := by
      intro h
      rw [Finset.sum_eq_single j₀ (fun j _ hjne => ite_eq_right fun hc => hjne (huniq j hc))
        (fun hnm => absurd (Finset.mem_univ _) hnm)]
      exact ite_eq_left hj₀
    rw [hsum f, hsum fun j => g (f j)]
  · push Not at h
    have hz : ∀ h' : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h' j else 0) = 0 :=
      fun h' => Finset.sum_eq_zero fun j _ => ite_eq_right fun hc => absurd hc.2 (not_le.mpr
        (h j hc.1))
    rw [hz f, hz fun j => g (f j), hg0]

/-- The coefficients of a simple integrand clamped to `[-C, C]`. -/
noncomputable def SimplePredictable.truncate {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ) :
    SimplePredictable Ω T where
  N := G.N
  partition := G.partition
  partition_zero := G.partition_zero
  partition_le_T := G.partition_le_T
  partition_strictMono := G.partition_strictMono
  ξ := fun i ω => max (-C) (min C (G.ξ i ω))
  ξ_bounded := fun i => ⟨|C|, fun ω => abs_le.mpr
    ⟨le_max_of_le_left (neg_le_neg (le_abs_self C)),
      max_le (neg_le_abs C) ((min_le_left C (G.ξ i ω)).trans (le_abs_self C))⟩⟩
  ξ_measurable := fun i =>
    measurable_const.max (measurable_const.min (G.ξ_measurable i))

theorem SimplePredictable.abs_truncate_xi_le {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (i : Fin G.N) (ω : Ω) : |(G.truncate C).ξ i ω| ≤ C := by
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem SimplePredictable.truncate_eval {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (s : ℝ) (ω : Ω) :
    (G.truncate C).eval s ω = max (-C) (min C (G.eval s ω)) := by
  have hg0 : max (-C) (min C (0 : ℝ)) = 0 := by
    rw [min_eq_right hC, max_eq_right (by linarith : -C ≤ (0 : ℝ))]
  exact (comp_sum_ite G.partition_strictMono (fun i => G.ξ i ω) s
    (fun x => max (-C) (min C x)) hg0).symm

theorem SimplePredictable.truncate_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    ∀ i : Fin (G.truncate C).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((G.truncate C).partition i.castSucc)) ((G.truncate C).ξ i) := by
  intro i
  exact (measurable_const.max
    (measurable_const.min (h_adapt i).measurable)).stronglyMeasurable

/-- Clamping to `[-C, C]` moves a value no further from any target already in `[-C, C]`. -/
theorem abs_clamp_sub_le {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  rcases le_or_gt x (-C) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ C), max_eq_left hx,
      abs_of_nonpos (by linarith : -C - y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · rcases le_or_gt x C with hx' | hx'
    · rw [min_eq_right hx', max_eq_right (by linarith : -C ≤ x)]
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -C ≤ C),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ C - y),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
      linarith

section LintegralForm

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

/-- The fourth `lintegral` of an elementary integral as the `ofReal` of its fourth moment. -/
theorem SimplePredictable.lintegral_pow_four_eq {T : ℝ} (G : SimplePredictable Ω T)
    {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ENNReal.ofReal (∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P) := by
  have hmem : MemLp (fun ω => simpleIntegral W G T ω) 4 P := by
    have h := G.memLp_partialSum W hC 4 (by simp) G.N
    have hfun : G.partialSum W G.N = fun ω => simpleIntegral W G T ω := by
      funext ω; exact G.partialSum_card W ω
    rwa [hfun] at h
  have hmem' : MemLp (fun ω => simpleIntegral W G T ω) ((4 : ℕ) : ℝ≥0∞) P := by
    simpa using hmem
  have hint : Integrable (fun ω => (simpleIntegral W G T ω) ^ 4) P := by
    refine (hmem'.integrable_norm_pow (by norm_num)).mono
      ((continuous_pow 4).comp_aestronglyMeasurable hmem.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by simp)
  have hpt : ∀ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4
      = ENNReal.ofReal ((simpleIntegral W G T ω) ^ 4) := by
    intro ω
    have h1 : (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal |simpleIntegral W G T ω| := by
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
      exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
    rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ simpleIntegral W G T ω ^ 4)]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => by positivity)]
  exact lintegral_congr hpt

include hℱ in
/-- The fourth-moment bound for a simple integrand, in `lintegral` form. -/
theorem SimplePredictable.lintegral_simpleIntegral_pow_four_le {T : ℝ}
    (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * T ^ 2) := by
  rw [G.lintegral_pow_four_eq W hC]
  exact ENNReal.ofReal_le_ofReal
    (G.integral_simpleIntegral_pow_four_le_horizon W ℱ hℱ h_adapt hC0 hC)

include hℱ in
/-- The fourth-moment bound against a per-tile coefficient bound, in `lintegral` form. -/
theorem SimplePredictable.lintegral_simpleIntegral_pow_four_le_varClock {T : ℝ}
    (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {c : Fin G.N → ℝ} (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * G.varClock c G.N ^ 2) := by
  rw [G.lintegral_pow_four_eq W hC]
  exact ENNReal.ofReal_le_ofReal
    (G.integral_simpleIntegral_pow_four_le_varClock W ℱ hℱ h_adapt hC0 hC hc)

include hℱ in
/-- **Fourth-moment bound for the `L²` Itô integral of a uniformly bounded integrand.** -/
theorem lintegral_stochasticIntegralBrownian_pow_four_le
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * T ^ 2) := by
  classical
  choose G0 hG0adapt hG0within using fun n : ℕ =>
    exists_adaptedSimple_within ℱ H hm hp hT (hq T hT)
      (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ from ENNReal.inv_pos.mpr
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  have hGadapt : ∀ n, ∀ i : Fin ((G0 n).truncate C).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (((G0 n).truncate C).partition i.castSucc)) (((G0 n).truncate C).ξ i) :=
    fun n => SimplePredictable.truncate_adapt ℱ (G0 n) C (hG0adapt n)
  have hGbdd : ∀ n, ∀ (i : Fin ((G0 n).truncate C).N) (ω : Ω),
      |((G0 n).truncate C).ξ i ω| ≤ C := fun n i ω => (G0 n).abs_truncate_xi_le hC0 i ω
  have hGwithin : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖((G0 n).truncate C).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine le_trans ?_ (hG0within n).le
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    have hle : ‖((G0 n).truncate C).eval s ω - H ω s‖₊ ≤ ‖H ω s - (G0 n).eval s ω‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      rw [(G0 n).truncate_eval hC0 s ω, abs_sub_comm (H ω s)]
      exact abs_clamp_sub_le hC0 (hCH ω s)
    exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr hle) 2
  have htol : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
    refine h.congr fun n => ?_
    simp [Nat.cast_add_one]
  have hsq : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W ((G0 n).truncate C) T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htol
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall fun n => ?_)
    rw [isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ ((G0 n).truncate C)
      (hGadapt n) H hm hp hq hT]
    exact hGwithin n
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => simpleIntegral W ((G0 n).truncate C) T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P) Filter.atTop (nhds 0) := by
    have hrw : ∀ n, MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W ((G0 n).truncate C) T ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P
        = (∫⁻ ω, (‖simpleIntegral W ((G0 n).truncate C) T ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
              ^ ((2 : ℝ))⁻¹ := by
      intro n
      rw [← eLpNorm_two_rpow_eq_lintegral_sq]
      · exact (ENNReal.rpow_rpow_inv (by norm_num) _).symm
      · have hGm : Measurable (simpleIntegral W ((G0 n).truncate C) T) := by
          unfold simpleIntegral
          exact Finset.measurable_sum _ fun i _ =>
            (((G0 n).truncate C).ξ_measurable i).mul
              ((W.measurable_eval _).sub (W.measurable_eval _))
        exact (hGm.sub ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq T).mono
          (ℱ.le T)).measurable).aestronglyMeasurable
    simp_rw [hrw]
    have h := (ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0 |>.comp hsq
    simpa [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < ((2 : ℝ))⁻¹)] using h
  have hmeasG : ∀ n, Measurable (simpleIntegral W ((G0 n).truncate C) T) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      (((G0 n).truncate C).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hTIM : MeasureTheory.TendstoInMeasure P
      (fun n => simpleIntegral W ((G0 n).truncate C) T) Filter.atTop
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq T) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) heL
  obtain ⟨ns, -, hns_ae⟩ := hTIM.exists_seq_tendsto_ae
  have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4 := by
    have hfun : (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4)
        = fun x : ℝ => ((‖x‖₊ ^ 4 : ℝ≥0) : ℝ≥0∞) := by
      funext x; rw [ENNReal.coe_pow]
    rw [hfun]
    exact ENNReal.continuous_coe.comp (continuous_nnnorm.pow 4)
  have hfatou : ∫⁻ ω,
      (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ Filter.liminf (fun k => ∫⁻ ω,
        (‖simpleIntegral W ((G0 (ns k)).truncate C) T ω‖₊ : ℝ≥0∞) ^ 4 ∂P) Filter.atTop := by
    have h1 : ∀ᵐ ω ∂P,
        (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 4
        = Filter.liminf (fun k =>
            (‖simpleIntegral W ((G0 (ns k)).truncate C) T ω‖₊ : ℝ≥0∞) ^ 4) Filter.atTop := by
      filter_upwards [hns_ae] with ω hω
      exact ((hcont.tendsto _).comp hω).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    exact lintegral_liminf_le fun k => (hcont.measurable.comp (hmeasG (ns k)))
  refine hfatou.trans (Filter.liminf_le_of_frequently_le
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => ?_)))
  exact SimplePredictable.lintegral_simpleIntegral_pow_four_le W ℱ hℱ
    ((G0 (ns k)).truncate C) (hGadapt (ns k)) hC0 (hGbdd (ns k))

end LintegralForm

end LevyStochCalc.Brownian.Ito

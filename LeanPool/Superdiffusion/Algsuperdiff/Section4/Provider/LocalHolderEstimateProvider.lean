/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.CubeAmplitude
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Translate
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale

/-!
# LocalHolderEstimateProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The local Hölder estimate on a translated cube

This module assembles the local `C^{0,alpha}` estimate for the zero-datum
Dirichlet problem on the cube `y + □_m`, at every exponent
`alpha ∈ (0, 1 - C sqrt gamma]`, from the clipped-window oscillation family of
the regularity theorem and the Campanato characterisation of Hölder spaces on a
cube.

Three things are supplied here.

* **The centre.**  The oscillation family lives on the origin cube; the
  Dirichlet problem on `y + □_m` at the sample `omega` is the Dirichlet problem
  on `□_m` at the translated sample, and the cutoff-sample law is translation
  invariant, so the minimal scale of the centre `y` is the origin's minimal
  scale read at the translated sample.
* **The exponent range.**  The chaining constant of the Campanato
  characterisation grows without bound as the exponent tends to `0`, while the
  normalized seminorm `3 ^ (alpha m) [·]_{C^{0,alpha}(y + □_m)}` *increases*
  with the exponent, because the cube has diameter `3 ^ m`.  The estimate at a
  small exponent is therefore deduced from the estimate at the exponent
  `max alpha (1/2)`, whose chaining constant is uniform; the minimal scale is
  doubled so that the prefactor `3 ^ ((1 - alpha) X)` still dominates, and the
  tail of the doubled scale is the tail of the original at half the index,
  which the sixteen-fold enlargement of the constant absorbs.
* **The `ℕ`-valued scale.**  The oscillation family carries an `ℕ∞`-valued
  minimal scale; the exponential tail makes it finite almost surely, and the
  estimate is asserted almost surely, so the `ℕ`-valued recast costs nothing.

The small-disorder threshold is chosen so that `1/2` itself lies in the
admissible exponent range, which is what makes the second item available.

## Main results

* `ae_ne_top_of_tail` — an exponential tail forces almost-sure finiteness.
* `tail_exponent_le` — the tail arithmetic of the doubled scale.
* `local_holder_estimate_provider` — the estimate.
-/

namespace Algsuperdiff.Section4.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Tail bookkeeping -/

/-- **The exponential tail forces almost-sure finiteness.** -/
theorem ae_ne_top_of_tail {d : ℕ} {M : ABKModel d} {Cst a : ℝ} (hCst : 0 < Cst) (ha : 0 < a)
    {X : Cutoff.CutoffSample d → ℕ∞}
    (htail : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
        ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / (Cst * M.gamma)))) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤ := by
  have hgpos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hb : (0 : ℝ) < Cst * M.gamma := mul_pos hCst hgpos
  set b : ℝ := Cst * M.gamma with hbdef
  set r : ℝ := Real.exp (-(a / b)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have hab : (0 : ℝ) < a / b := div_pos ha hb
    have hlt := Real.exp_lt_exp.mpr (show -(a / b) < (0 : ℝ) by linarith only [hab])
    rwa [Real.exp_zero] at hlt
  have hpow : ∀ N : ℕ, r ^ N = Real.exp (-(a / b) * (N : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, hrdef, ← Real.exp_add]
        congr 1
        push_cast
        ring
  have hrw : ∀ N : ℕ, Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b) =
      Cst * Real.exp (a * Cst / b) * r ^ N := by
    intro N
    have hstep : Cst * Real.exp (a * Cst / b) * r ^ N =
        Cst * (Real.exp (a * Cst / b) * Real.exp (-(a / b) * (N : ℝ))) := by
      rw [hpow N]; ring
    rw [hstep, ← Real.exp_add]
    have harg : a * Cst / b + -(a / b) * (N : ℝ) = -(a * ((N : ℝ) - Cst)) / b := by
      field_simp
      ring
    rw [harg]
  have hlim : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun N : ℕ => Cst * Real.exp (a * Cst / b) * r ^ N)
        Filter.atTop (nhds (Cst * Real.exp (a * Cst / b) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul _
    rw [mul_zero] at h0
    have hreal : Filter.Tendsto
        (fun N : ℕ => Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)) Filter.atTop
        (nhds 0) := h0.congr fun N => (hrw N).symm
    have hcomp := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa using! hcomp
  rw [MeasureTheory.ae_iff]
  have hsub : ∀ N : ℕ,
      {omega : Cutoff.CutoffSample d | ¬ X omega ≠ ⊤} ⊆
        {omega : Cutoff.CutoffSample d | (N : ℕ∞) ≤ X omega} := by
    intro N omega homega
    have htop : X omega = ⊤ := not_not.mp homega
    simp only [Set.mem_ofPred_eq, htop, le_top]
  have hle : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | ¬ X omega ≠ ⊤} ≤
        ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)) :=
    fun N => le_trans (measure_mono (hsub N)) (htail N)
  exact le_antisymm (ge_of_tendsto' hlim hle) zero_le

/-- **The doubled minimal scale keeps an admissible tail.** -/
theorem tail_exponent_le {A B C0 C N : ℝ} (hC0 : 0 < C0) (hC : 16 * C0 ≤ C)
    (hB : 0 ≤ B) (hBA : B ≤ A) (hA4B : A ≤ 4 * B) (hN : 0 ≤ N) :
    A * (N - C) / C ≤ B * (N / 2 - C0) / C0 := by
  have hCpos : (0 : ℝ) < C := by linarith only [hC0, hC]
  rw [div_le_div_iff₀ hCpos hC0]
  have h1 : B * (16 * C0) ≤ B * C := mul_le_mul_of_nonneg_left hC hB
  have h2 : A * C0 ≤ 4 * B * C0 := mul_le_mul_of_nonneg_right hA4B hC0.le
  have hBC0 : (0 : ℝ) ≤ B * C0 := mul_nonneg hB hC0.le
  have hneg : A * C0 - B * C / 2 ≤ 0 := by linarith only [h1, h2, hBC0]
  have hprod : N * (A * C0 - B * C / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN hneg
  have hdiff : (0 : ℝ) ≤ (A - B) * C * C0 := by
    have hAB : (0 : ℝ) ≤ A - B := by linarith only [hBA]
    have := mul_nonneg (mul_nonneg hAB hCpos.le) hC0.le
    linarith only [this]
  linarith only [hprod, hdiff]

/-! ## The provider -/

theorem local_holder_estimate_provider
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
      ∀ (m : ℤ) (y : Vec d), ∃ X : Cutoff.CutoffSample d → ℕ,
        Measurable X ∧
        (∀ N : ℕ,
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ X omega} ≤
            ENNReal.ofReal
              (C * Real.exp
                (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          ∀ L : ℤ, m ≤ L →
            ∀ (g : Vec d → Vec d) (u : H1Function (cubeSetAt y m)),
              IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField)
                  y m u g →
              (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y m u uRep,
                  ENNReal.ofReal (Real.rpow 3 (alpha * (m : ℝ))) *
                    holderSeminormOn (cubeSetAt y m) alpha uRep) ≤
                ENNReal.ofReal (C * Real.rpow 3 ((1 - alpha) * (X omega : ℝ))) *
                  (eLpNorm
                      (fun x => u.toFun x -
                        HCPolySupport.volumeAverage (cubeSetAt y m) u.toFun) 2
                      (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                        (cubeSetAt y m)) +
                    ENNReal.ofReal ((Annealed.sigmaBar M m : ℝ)⁻¹ *
                        Real.rpow 3 (3 * (m : ℝ) / 2)) *
                      holderSeminormOn (cubeSetAt y m) (1 / 2) g) := by
  classical
  rcases eq_or_ne d 0 with hd0 | hd0
  · subst hd0
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgam alpha halpha0 _halpha m y
    refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
    · intro N
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        refine le_trans prob_le_one (ENNReal.one_le_ofReal.mpr ?_)
        rw [one_mul]
        refine Real.one_le_exp (div_nonneg ?_ ?_)
        · have hsq : (0 : ℝ) ≤ (1 - alpha) ^ (2 : ℕ) := sq_nonneg (1 - alpha)
          push_cast
          linarith only [hsq]
        · have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
          linarith only [hgam]
      · have hset : {omega : Cutoff.CutoffSample 0 | N ≤ (0 : ℕ)} = ∅ := by
          ext omega
          simp [hN.ne']
        rw [hset, measure_empty]
        exact zero_le
    · refine Filter.Eventually.of_forall ?_
      intro omega L _hmL g u _hsol
      have hsub : (cubeSetAt y m).Subsingleton := by
        intro a _ b _
        exact funext fun i => i.elim0
      have hrep : IsCubeRepresentative y m u u.toFun :=
        ⟨Filter.EventuallyEq.rfl, hsub.continuousOn u.toFun⟩
      have hzero : holderSeminormOn (cubeSetAt y m) alpha u.toFun = 0 := by
        refine le_antisymm ?_ zero_le
        simp only [holderSeminormOn, iSup_le_iff]
        intro x _hx z _hz hne
        exact absurd (funext fun i => i.elim0 : x = z) hne
      refine le_trans (iInf_le_of_le u.toFun (iInf_le_of_le hrep le_rfl)) ?_
      rw [hzero, mul_zero]
      exact zero_le
  · have : NeZero d := ⟨hd0⟩
    obtain ⟨g0, C0, Cosc, Cdata, hg0, hC0, hCosc, hCdata, hfeed⟩ :=
      Holder.hasClipGridOscillationDecay_zeroDatum d hd0 cstar hcstar
    have hP2nn : (0 : ℝ) ≤
        StochasticProcess.Common.Regularity.Ported.ballVolumePrice 2 d :=
      StochasticProcess.Common.Regularity.Ported.ballVolumePrice_nonneg 2 d
    have hUdnn : (0 : ℝ) ≤ Holder.uniformCubeHolderConstant d :=
      Holder.uniformCubeHolderConstant_nonneg d
    set Camp : ℝ := 6 * Holder.uniformCubeHolderConstant d * Cosc *
      max (StochasticProcess.Common.Regularity.Ported.ballVolumePrice 2 d) Cdata
      with hCampdef
    have hCampnn : (0 : ℝ) ≤ Camp := by
      rw [hCampdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hUdnn) hCosc)
        (le_trans hP2nn (le_max_left _ _))
    refine ⟨min g0 (1 / (4 * C0 ^ 2)), max (16 * C0) Camp, lt_min hg0 (by positivity),
      lt_of_lt_of_le (by linarith only [hC0]) (le_max_left _ _), ?_⟩
    set C : ℝ := max (16 * C0) Camp with hCdef
    have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by linarith only [hC0]) (le_max_left _ _)
    have h16 : 16 * C0 ≤ C := le_max_left _ _
    have hCampC : Camp ≤ C := le_max_right _ _
    have hC0C : C0 ≤ C := by linarith only [h16, hC0]
    intro M hcs hgam alpha halpha0 halpha m y
    have hgamg0 : M.gamma ≤ g0 := le_trans hgam (min_le_left _ _)
    have hgamB : M.gamma ≤ 1 / (4 * C0 ^ 2) := le_trans hgam (min_le_right _ _)
    have hgpos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have hsqnn : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
    have hsqpos : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 hgpos
    have halpha1 : alpha ≤ 1 := by
      have : (0 : ℝ) < C * Real.sqrt M.gamma := mul_pos hCpos hsqpos
      linarith only [halpha, this]
    have halphaC0 : alpha ≤ 1 - C0 * Real.sqrt M.gamma := by
      have hmono : C0 * Real.sqrt M.gamma ≤ C * Real.sqrt M.gamma :=
        mul_le_mul_of_nonneg_right hC0C hsqnn
      linarith only [halpha, hmono]
    have hhalf : (1 / 2 : ℝ) ≤ 1 - C0 * Real.sqrt M.gamma := by
      have hs : Real.sqrt M.gamma ≤ 1 / (2 * C0) := by
        have h1 : Real.sqrt M.gamma ≤ Real.sqrt (1 / (4 * C0 ^ 2)) :=
          Real.sqrt_le_sqrt hgamB
        have h2 : Real.sqrt (1 / (4 * C0 ^ 2)) = 1 / (2 * C0) := by
          rw [show (1 : ℝ) / (4 * C0 ^ 2) = (1 / (2 * C0)) ^ 2 by field_simp; ring]
          exact Real.sqrt_sq (by positivity)
        rwa [h2] at h1
      have hmul : C0 * Real.sqrt M.gamma ≤ C0 * (1 / (2 * C0)) :=
        mul_le_mul_of_nonneg_left hs hC0.le
      have hval : C0 * (1 / (2 * C0)) = 1 / 2 := by field_simp
      rw [hval] at hmul
      linarith only [hmul]
    set beta : ℝ := max alpha (1 / 2) with hbetadef
    have hbeta_half : (1 / 2 : ℝ) ≤ beta := le_max_right _ _
    have hbeta_ge : alpha ≤ beta := le_max_left _ _
    have hbeta0 : (0 : ℝ) < beta := by linarith only [hbeta_half]
    have hbeta_le : beta ≤ 1 - C0 * Real.sqrt M.gamma := max_le halphaC0 hhalf
    have hbeta1 : beta ≤ 1 := by
      have : (0 : ℝ) < C0 * Real.sqrt M.gamma := mul_pos hC0 hsqpos
      linarith only [hbeta_le, this]
    have hbetalt : beta < 1 := by
      have : (0 : ℝ) < C0 * Real.sqrt M.gamma := mul_pos hC0 hsqpos
      linarith only [hbeta_le, this]
    obtain ⟨Xe, hXmeas, hXtail, hXae⟩ := hfeed M hcs hgamg0 beta hbeta0 hbeta_le m
    have hmeasT : Measurable (Cutoff.translateCutoffSample (d := d) y) :=
      Cutoff.measurable_translateCutoffSample y
    -- the two squared rates
    have hBnn : (0 : ℝ) ≤ (1 - beta) ^ (2 : ℕ) := sq_nonneg _
    have hBpos : (0 : ℝ) < (1 - beta) ^ (2 : ℕ) := by
      have : (0 : ℝ) < 1 - beta := by linarith only [hbetalt]
      positivity
    have h1bnn : (0 : ℝ) ≤ 1 - beta := by linarith only [hbeta1]
    have hBA : (1 - beta) ^ (2 : ℕ) ≤ (1 - alpha) ^ (2 : ℕ) :=
      pow_le_pow_left₀ h1bnn (by linarith only [hbeta_ge]) 2
    have hA4B : (1 - alpha) ^ (2 : ℕ) ≤ 4 * (1 - beta) ^ (2 : ℕ) := by
      have hlin : 1 - alpha ≤ 2 * (1 - beta) := by
        rcases le_total alpha (1 / 2 : ℝ) with h | h
        · have hb : beta = 1 / 2 := max_eq_right h
          rw [hb]; linarith only [halpha0]
        · have hb : beta = alpha := max_eq_left h
          rw [hb]; linarith only [halpha1]
      have := pow_le_pow_left₀ (by linarith only [halpha1] : (0:ℝ) ≤ 1 - alpha) hlin 2
      calc (1 - alpha) ^ (2 : ℕ) ≤ (2 * (1 - beta)) ^ (2 : ℕ) := this
        _ = 4 * (1 - beta) ^ (2 : ℕ) := by ring
    refine ⟨fun omega => 2 * (Xe (Cutoff.translateCutoffSample y omega)).toNat, ?_, ?_, ?_⟩
    · exact Measurable.const_mul (Measurable.of_discrete.comp (hXmeas.comp hmeasT)) 2
    · intro N
      have hsubset : {omega : Cutoff.CutoffSample d |
            N ≤ 2 * (Xe (Cutoff.translateCutoffSample y omega)).toNat} ⊆
          Cutoff.translateCutoffSample y ⁻¹'
            {omega | (((N + 1) / 2 : ℕ) : ℕ∞) ≤ Xe omega} := by
        intro omega hom
        simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hom ⊢
        by_cases htop : Xe (Cutoff.translateCutoffSample y omega) = ⊤
        · rw [htop]; exact le_top
        · rw [← ENat.natCast_toNat htop]
          exact_mod_cast (by omega : (N + 1) / 2 ≤
            (Xe (Cutoff.translateCutoffSample y omega)).toNat)
      have hmeasset : MeasurableSet {omega : Cutoff.CutoffSample d |
          (((N + 1) / 2 : ℕ) : ℕ∞) ≤ Xe omega} :=
        hXmeas (MeasurableSet.of_discrete
          (s := {v : ℕ∞ | (((N + 1) / 2 : ℕ) : ℕ∞) ≤ v}))
      have hNhalf : (N : ℝ) / 2 ≤ (((N + 1) / 2 : ℕ) : ℝ) := by
        have hnat : N ≤ 2 * ((N + 1) / 2) := by omega
        have hcast : (N : ℝ) ≤ 2 * (((N + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
        linarith only [hcast]
      have hkey := tail_exponent_le (A := (1 - alpha) ^ (2 : ℕ))
        (B := (1 - beta) ^ (2 : ℕ)) (C0 := C0) (C := C) (N := (N : ℝ))
        hC0 h16 hBnn hBA hA4B (Nat.cast_nonneg N)
      have hstep2 : (1 - beta) ^ (2 : ℕ) * ((N : ℝ) / 2 - C0) / C0 ≤
          (1 - beta) ^ (2 : ℕ) * ((((N + 1) / 2 : ℕ) : ℝ) - C0) / C0 :=
        (div_le_div_iff_of_pos_right hC0).mpr
          (mul_le_mul_of_nonneg_left (by linarith only [hNhalf]) hBnn)
      have hchain : (1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C) / C ≤
          (1 - beta) ^ (2 : ℕ) * ((((N + 1) / 2 : ℕ) : ℝ) - C0) / C0 :=
        le_trans hkey hstep2
      have hexpineq : -((1 - beta) ^ (2 : ℕ) * ((((N + 1) / 2 : ℕ) : ℝ) - C0)) /
            (C0 * M.gamma) ≤
          -((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma) := by
        rw [neg_div, neg_div, neg_le_neg_iff, div_mul_eq_div_div, div_mul_eq_div_div]
        exact (div_le_div_iff_of_pos_right hgpos).mpr hchain
      calc (Cutoff.cutoffSampleLaw M).toMeasure
            {omega | N ≤ 2 * (Xe (Cutoff.translateCutoffSample y omega)).toNat}
          ≤ (Cutoff.cutoffSampleLaw M).toMeasure
              (Cutoff.translateCutoffSample y ⁻¹'
                {omega | (((N + 1) / 2 : ℕ) : ℕ∞) ≤ Xe omega}) := measure_mono hsubset
        _ = (Cutoff.cutoffSampleLaw M).toMeasure
              {omega | (((N + 1) / 2 : ℕ) : ℕ∞) ≤ Xe omega} :=
            GoodEvents.measure_preimage_translateCutoffSample M y hmeasset
        _ ≤ ENNReal.ofReal (C0 * Real.exp
              (-((1 - beta) ^ (2 : ℕ) * ((((N + 1) / 2 : ℕ) : ℝ) - C0)) /
                (C0 * M.gamma))) := hXtail _
        _ ≤ ENNReal.ofReal (C * Real.exp
              (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact mul_le_mul hC0C (Real.exp_le_exp.2 hexpineq) (Real.exp_pos _).le hCpos.le
    · have hXfin : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, Xe omega ≠ ⊤ :=
        ae_ne_top_of_tail hC0 hBpos hXtail
      have hmp := GoodEvents.measurePreserving_translateCutoffSample M y
      filter_upwards [hmp.quasiMeasurePreserving.ae hXae,
        hmp.quasiMeasurePreserving.ae hXfin] with omega hom hfin
      intro L hmL g u hsol
      set omega' : Cutoff.CutoffSample d := Cutoff.translateCutoffSample y omega with homega'
      set Xn : ℕ := (Xe omega').toNat with hXndef
      have hXnle : Xe omega' ≤ (Xn : ℕ∞) := le_of_eq (ENat.natCast_toNat hfin).symm
      have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
      have hqrpos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow 3 (3 * (m : ℝ) / 2) :=
        mul_pos (inv_pos.2 hsigpos) (Real.rpow_pos_of_pos (by norm_num) _)
      have hCrpos : (0 : ℝ) < C * Real.rpow 3 ((1 - alpha) * (((2 * Xn : ℕ)) : ℝ)) :=
        mul_pos hCpos (Real.rpow_pos_of_pos (by norm_num) _)
      by_cases hHtop : holderSeminormOn (cubeSetAt y m) (1 / 2) g = ⊤
      · rw [hHtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hqrpos).ne', add_top,
          ENNReal.mul_top (ENNReal.ofReal_pos.2 hCrpos).ne']
        exact le_top
      · have hKgnn : (0 : ℝ) ≤ (holderSeminormOn (cubeSetAt y m) (1 / 2) g).toReal :=
          ENNReal.toReal_nonneg
        set Kg : ℝ := (holderSeminormOn (cubeSetAt y m) (1 / 2) g).toReal with hKgdef
        have hKgeq : ENNReal.ofReal Kg = holderSeminormOn (cubeSetAt y m) (1 / 2) g :=
          ENNReal.ofReal_toReal hHtop
        have hgHol : Algsuperdiff.Section4.Support.HolderSeminormBoundOn
            (openCubeSet (originCube d m)) (1 / 2) Kg (fun x => g (y + x)) := by
          refine (holderSeminormOn_le_ofReal_iff hKgnn).1 ?_
          rw [← holderSeminormOn_cubeSetAt_eq, hKgeq]
        have hsol0 : Algsuperdiff.Section4.Support.IsDirichletSolutionOn
            ((Cutoff.coefficientCutoff M.nu L omega').toCoeffField)
            (originCube d m) (originPullback y m u) 0 (fun x => g (y + x)) := by
          have h := (isDirichletSolutionAt_iff_origin _ y m u g).1 hsol
          rw [coefficientCutoff_add_eq_translateCutoffSample M L y omega] at h
          exact h
        have hdec := hom Xn hXnle L hmL (originPullback y m u) (fun x => g (y + x)) Kg
          hKgnn hsol0 hgHol
        set S : ℝ := Algsuperdiff.Section4.Support.normalizedL2On
            (openCubeSet (originCube d m))
            (fun w => (originPullback y m u).toFun w -
              volumeAverage (openCubeSet (originCube d m)) (originPullback y m u).toFun)
          with hSdef
        have hSnn : (0 : ℝ) ≤ S := Algsuperdiff.Section4.Support.normalizedL2On_nonneg _ _
        have hqKgnn : (0 : ℝ) ≤ (Annealed.sigmaBar M m : ℝ)⁻¹ *
            Real.rpow 3 (3 * (m : ℝ) / 2) * Kg := mul_nonneg hqrpos.le hKgnn
        have hDnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-m) *
            (StochasticProcess.Common.Regularity.Ported.ballVolumePrice 2 d * S) +
            Cdata * ((Annealed.sigmaBar M m : ℝ)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg) := by
          have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-m) *
              (StochasticProcess.Common.Regularity.Ported.ballVolumePrice 2 d * S) :=
            mul_nonneg (zpow_nonneg (by norm_num) _) (mul_nonneg hP2nn hSnn)
          have h2 : (0 : ℝ) ≤ Cdata * ((Annealed.sigmaBar M m : ℝ)⁻¹ *
              Real.rpow 3 ((m : ℝ) / 2) * Kg) :=
            mul_nonneg hCdata (mul_nonneg (mul_nonneg (inv_nonneg.2 hsigpos.le)
              (Real.rpow_nonneg (by norm_num) _)) hKgnn)
          linarith only [h1, h2]
        have hKnn : (0 : ℝ) ≤ Holder.campanatoGridConstant beta m Xn Cosc
            ((3 : ℝ) ^ (-m) *
              (StochasticProcess.Common.Regularity.Ported.ballVolumePrice 2 d * S) +
              Cdata * ((Annealed.sigmaBar M m : ℝ)⁻¹ *
                Real.rpow 3 ((m : ℝ) / 2) * Kg)) :=
          Holder.campanatoGridConstant_nonneg m Xn hCosc hDnn
        obtain ⟨uRep, hrep, hsem⟩ :=
          Holder.exists_cubeRepresentative_of_grid hbeta0 hKnn u hdec
        have hpull : (fun x : Vec d => u.toFun (x + y)) = (originPullback y m u).toFun := by
          funext x
          rw [originPullback_toFun]
        have hSeq : Algsuperdiff.Section4.Support.normalizedL2On (cubeSetAt y m)
            (fun x => u.toFun x - volumeAverage (cubeSetAt y m) u.toFun) = S := by
          rw [Holder.normalizedL2On_cubeSetAt, Holder.volumeAverage_cubeSetAt, hpull, hSdef]
          congr 1
          funext x
          rw [originPullback_toFun]
        have hSE : ENNReal.ofReal S ≤ eLpNorm
            (fun x => u.toFun x - volumeAverage (cubeSetAt y m) u.toFun) 2
            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn (cubeSetAt y m)) := by
          rw [← hSeq]
          exact Holder.ofReal_normalizedL2On_le_eLpNorm y m
            (Holder.memLp_sub_volumeAverage_cubeSetAt y m u)
        have hbetannn : (0 : ℝ) ≤ Real.rpow 3 (beta * (m : ℝ)) :=
          Real.rpow_nonneg (by norm_num) _
        have hrnn : (0 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * (((2 * Xn : ℕ)) : ℝ)) :=
          Real.rpow_nonneg (by norm_num) _
        refine le_trans (iInf_le_of_le uRep (iInf_le_of_le hrep le_rfl)) ?_
        refine le_trans (Holder.ofReal_rpow_mul_holderSeminormOn_mono y m hbeta_ge uRep) ?_
        refine le_trans (mul_le_mul' le_rfl hsem) ?_
        rw [← ENNReal.ofReal_mul hbetannn]
        refine le_trans (ENNReal.ofReal_le_ofReal
          (Holder.rpow_mul_campanatoGridConstant_le (alpha := alpha) (beta := beta)
            (Cosc := Cosc) (Cdata := Cdata) (S := S) (Kg := Kg)
            (sigma := (Annealed.sigmaBar M m : ℝ))
            (G := StochasticProcess.Common.Regularity.Campanato.clipOffGridHolderConstant
              d beta 18)
            (Ud := Holder.uniformCubeHolderConstant d)
            (P2 := StochasticProcess.Common.Regularity.Ported.ballVolumePrice 2 d)
            (m := m) (Xn := Xn)
            halpha0 hbeta_ge hbeta1 hCosc hCdata hSnn hKgnn hsigpos hP2nn
            (StochasticProcess.Common.Regularity.Campanato.clipOffGridHolderConstant_nonneg
              d hbeta0 18)
            (Holder.clipOffGridHolderConstant_le_uniform d hbeta_half hbeta1) hUdnn)) ?_
        rw [ENNReal.ofReal_mul (mul_nonneg hCampnn hrnn), ENNReal.ofReal_add hSnn hqKgnn]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hCampC hrnn)) (add_le_add hSE ?_)
        rw [ENNReal.ofReal_mul hqrpos.le, hKgeq]

end

end Algsuperdiff.Section4.Provider

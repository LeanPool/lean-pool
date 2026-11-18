/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# The Laplace law

The Laplace law with rate `β > 0` has density `(β/2) e^{-β|s|}` on `ℝ`. It is the noise `η_β` of
Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1. The function `s ↦ e^{ws}`
is integrable for `η_β` exactly when `|w| < β`; for `|w| ≥ β` it is not integrable (Lean's real
Bochner integral is then `0`, not `∞`). The law has local, not global, exponential moments: its
moment generating function is `β²/(β² - w²)` on `|w| < β`, its mean is `0` and its second moment
`2/β²` (`laplaceMeasure_moments`).
It is a probability measure (`isProbabilityMeasure_laplaceMeasure`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Probability.Line

/-- The Laplace density `(β/2) e^{-β|s|}`. -/
def laplaceDensity (β s : ℝ) : ℝ := β / 2 * Real.exp (-(β * |s|))

/-- The Laplace law with rate `β`: Lebesgue measure with density `(β/2) e^{-β|s|}`. -/
def laplaceMeasure (β : ℝ) : Measure ℝ :=
  volume.withDensity fun s => ENNReal.ofReal (laplaceDensity β s)


/-- The Laplace density has total integral `1`. -/
theorem integral_laplaceDensity {β : ℝ} (hβ : 0 < β) :
    ∫ x : ℝ, laplaceDensity β x = 1 := by
  have habs :
      ∫ x : ℝ, Real.exp (-β * |x|) =
        2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) := by
    simpa using
      (integral_comp_abs (f := fun x : ℝ => Real.exp (-β * x)))
  have hi :
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) = β⁻¹ := by
    simpa using integral_exp_mul_Ioi (a := -β) (by linarith) 0
  have habs' :
      ∫ x : ℝ, Real.exp (-(β * |x|)) =
        2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) := by
    simpa only [neg_mul] using habs
  simp only [laplaceDensity, integral_const_mul]
  rw [habs', hi]
  field_simp

/-- The Laplace density is integrable. -/
theorem integrable_laplaceDensity {β : ℝ} (hβ : 0 < β) :
    Integrable (laplaceDensity β) := by
  have hneg :
      IntegrableOn (fun x : ℝ => Real.exp (-(β * |x|))) (Set.Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := β) hβ 0
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [abs_of_nonpos hx]
    ring_nf
  have hpos :
      IntegrableOn (fun x : ℝ => Real.exp (-(β * |x|))) (Set.Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -β) (by linarith) 0
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [abs_of_pos (show 0 < x from hx), neg_mul]
  have h :
      IntegrableOn (fun x : ℝ => Real.exp (-(β * |x|)))
        (Set.Iic 0 ∪ Set.Ioi 0) :=
    hneg.union hpos
  have h' :
      Integrable (fun x : ℝ => Real.exp (-(β * |x|))) := by
    simpa [Set.Iic_union_Ioi] using h
  have hc := h'.const_mul (β / 2)
  change Integrable (fun x : ℝ => β / 2 * Real.exp (-(β * |x|)))
  exact hc

/-- For `β > 0`, `laplaceMeasure β` has total mass `1`. -/
theorem isProbabilityMeasure_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (laplaceMeasure β) := by
    refine ⟨?_⟩
    simp only [laplaceMeasure, MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_laplaceDensity hβ]
      norm_num
    · exact integrable_laplaceDensity hβ
    · exact Filter.Eventually.of_forall (fun x => by
        simp only [Pi.zero_apply, laplaceDensity]
        positivity)

/-! ### Local moment generating function and moments

The density and law moment generating functions, the moment identification through
`ProbabilityTheory.iteratedDeriv_mgf_zero` and the rational calculus are used only for `|w| < β`. -/

section Moments

open ProbabilityTheory Filter Set
open scoped Topology

/-- **Local moment generating function of the Laplace law**: for `β > 0` and `|w| < β`, the
function `s ↦ e^{ws} (β/2) e^{-β|s|}` is integrable with integral `β² / (β² - w²)`. -/
theorem integral_exp_mul_laplaceDensity {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    MeasureTheory.Integrable (fun s => Real.exp (w * s) * laplaceDensity β s) ∧
      ∫ s, Real.exp (w * s) * laplaceDensity β s = β ^ 2 / (β ^ 2 - w ^ 2) := by
    have hw₁ : -β < w := (abs_lt.mp hw).1
    have hw₂ : w < β := (abs_lt.mp hw).2
    have hnegRate : w - β < 0 := by linarith
    have hposRate : 0 < w + β := by linarith
    have hβw : 0 < β - w := by linarith
    have hwβ : 0 < β + w := by linarith
    have hden : 0 < β ^ 2 - w ^ 2 := by
      nlinarith [mul_pos hβw hwβ]
    let f : ℝ → ℝ :=
      fun s => Real.exp (w * s) * laplaceDensity β s
    have hpos_eq :
        ∀ s ∈ Set.Ioi (0 : ℝ),
          f s = (β / 2) * Real.exp ((w - β) * s) := by
      intro s hs
      dsimp [f, laplaceDensity]
      rw [abs_of_pos hs]
      calc
        Real.exp (w * s) * (β / 2 * Real.exp (-(β * s))) =
            β / 2 * (Real.exp (w * s) * Real.exp (-(β * s))) := by
              ring
        _ = β / 2 * Real.exp (w * s + -(β * s)) := by
              rw [← Real.exp_add]
        _ = β / 2 * Real.exp ((w - β) * s) := by
              congr 2
              ring
    have hneg_eq :
        ∀ s ∈ Set.Iic (0 : ℝ),
          f s = (β / 2) * Real.exp ((w + β) * s) := by
      intro s hs
      dsimp [f, laplaceDensity]
      rw [abs_of_nonpos hs]
      calc
        Real.exp (w * s) * (β / 2 * Real.exp (-(β * -s))) =
            β / 2 * (Real.exp (w * s) * Real.exp (-(β * -s))) := by
              ring
        _ = β / 2 * Real.exp (w * s + -(β * -s)) := by
              rw [← Real.exp_add]
        _ = β / 2 * Real.exp ((w + β) * s) := by
              congr 2
              ring
    have hpos_exp :
        MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp ((w - β) * s)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (a := w - β) hnegRate 0
    have hneg_exp :
        MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp ((w + β) * s)) (Set.Iic 0) :=
      integrableOn_exp_mul_Iic (a := w + β) hposRate 0
    have hpos : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
      have h := hpos_exp.const_mul (β / 2)
      apply h.congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hpos_eq s hs).symm
    have hneg : MeasureTheory.IntegrableOn f (Set.Iic 0) := by
      have h := hneg_exp.const_mul (β / 2)
      apply h.congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with s hs
      exact (hneg_eq s hs).symm
    have hglob : MeasureTheory.Integrable f := by
      have h := hneg.union hpos
      simpa [Set.Iic_union_Ioi] using h
    have hpos_val :
        ∫ s in Set.Ioi (0 : ℝ), f s =
          (β / 2) * (1 / (β - w)) := by
      calc
        ∫ s in Set.Ioi (0 : ℝ), f s =
            ∫ s in Set.Ioi (0 : ℝ),
              (β / 2) * Real.exp ((w - β) * s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
          exact hpos_eq s hs
        _ = (β / 2) *
            ∫ s in Set.Ioi (0 : ℝ), Real.exp ((w - β) * s) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_smul
              (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (β / 2) (fun s : ℝ => Real.exp ((w - β) * s)))
        _ = (β / 2) * (1 / (β - w)) := by
          rw [integral_exp_mul_Ioi (a := w - β) hnegRate (0 : ℝ)]
          simp only [mul_zero, Real.exp_zero]
          field_simp [ne_of_lt hnegRate]
          ring
    have hneg_val :
        ∫ s in Set.Iic (0 : ℝ), f s =
          (β / 2) * (1 / (β + w)) := by
      calc
        ∫ s in Set.Iic (0 : ℝ), f s =
            ∫ s in Set.Iic (0 : ℝ),
              (β / 2) * Real.exp ((w + β) * s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Iic] with s hs
          exact hneg_eq s hs
        _ = (β / 2) *
            ∫ s in Set.Iic (0 : ℝ), Real.exp ((w + β) * s) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_smul
              (μ := MeasureTheory.volume.restrict (Set.Iic (0 : ℝ)))
              (β / 2) (fun s : ℝ => Real.exp ((w + β) * s)))
        _ = (β / 2) * (1 / (β + w)) := by
          rw [integral_exp_mul_Iic (a := w + β) hposRate (0 : ℝ)]
          simp only [mul_zero, Real.exp_zero]
          field_simp [ne_of_gt hposRate]
          ring
    refine ⟨?_, ?_⟩
    · simpa [f] using hglob
    · change ∫ s, f s = β ^ 2 / (β ^ 2 - w ^ 2)
      have hsplit :=
        MeasureTheory.integral_add_compl
          (μ := MeasureTheory.volume) (s := Set.Iic (0 : ℝ))
          measurableSet_Iic hglob
      rw [← hsplit, Set.compl_Iic, hneg_val, hpos_val]
      field_simp [ne_of_gt hβw, ne_of_gt hwβ, ne_of_gt hden]
      ring

/-- The law-level moment generating function on `|w| < β`. -/
theorem laplaceMeasure_mgf {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    Integrable (fun s : ℝ => Real.exp (w * s)) (laplaceMeasure β) ∧
      mgf id (laplaceMeasure β) w = β ^ 2 / (β ^ 2 - w ^ 2) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (laplaceDensity β s)) := by
    unfold laplaceDensity
    fun_prop
  have hfin : ∀ᵐ s : ℝ ∂volume, ENNReal.ofReal (laplaceDensity β s) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hnn (s : ℝ) : 0 ≤ laplaceDensity β s := by
    unfold laplaceDensity
    positivity
  have h := integral_exp_mul_laplaceDensity hβ hw
  constructor
  · unfold laplaceMeasure
    rw [integrable_withDensity_iff hm hfin]
    simpa only [ENNReal.toReal_ofReal (hnn _)] using h.1
  · change (∫ s : ℝ, Real.exp (w * id s) ∂volume.withDensity
      (fun s => ENNReal.ofReal (laplaceDensity β s))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hm hfin]
    simpa only [id_eq, ENNReal.toReal_ofReal (hnn _), smul_eq_mul, mul_comm] using h.2

/-- `0` is an interior point of the exponential-integrability set of the Laplace law. -/
theorem zero_mem_interior_integrableExpSet_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    0 ∈ interior (integrableExpSet id (laplaceMeasure β)) := by
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (Ioo_mem_nhds (by linarith : -β < 0) hβ)
  intro w hw
  exact (laplaceMeasure_mgf hβ (abs_lt.mpr hw)).1

/-- Near `0` the moment generating function is the rational function `β²/(β² - w²)`. -/
theorem laplaceMeasure_mgf_eventuallyEq {β : ℝ} (hβ : 0 < β) :
    mgf id (laplaceMeasure β) =ᶠ[𝓝 (0 : ℝ)] fun w => β ^ 2 / (β ^ 2 - w ^ 2) := by
  filter_upwards [Ioo_mem_nhds (by linarith : -β < 0) hβ] with w hw
  exact (laplaceMeasure_mgf hβ (abs_lt.mpr hw)).2

/-- The `k`-th moment is the `k`-th derivative at `0` of `β²/(β² - w²)`. -/
theorem laplaceMeasure_moment_eq_iteratedDeriv {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    (∫ s : ℝ, s ^ k ∂laplaceMeasure β) =
      iteratedDeriv k (fun w : ℝ => β ^ 2 / (β ^ 2 - w ^ 2)) 0 := by
  have h := ProbabilityTheory.iteratedDeriv_mgf_zero (X := id)
    (zero_mem_interior_integrableExpSet_laplaceMeasure hβ) k
  have hd := Filter.EventuallyEq.iteratedDeriv_eq k (laplaceMeasure_mgf_eventuallyEq hβ)
  simpa only [Pi.pow_apply, id_eq] using h.symm.trans hd

/-- Every polynomial moment of the Laplace law is finite (from the rates `±β/2`). -/
theorem integrable_pow_laplaceMeasure {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k) (laplaceMeasure β) := by
  have hhalf : 0 < β / 2 := by positivity
  have hsmall : |β / 2| < β := by rw [abs_of_pos hhalf]; linarith
  have hp := (laplaceMeasure_mgf hβ hsmall).1
  have hn := (laplaceMeasure_mgf (w := -(β / 2)) hβ (by simpa only [abs_neg] using hsmall)).1
  exact ProbabilityTheory.integrable_pow_of_integrable_exp_mul
    (X := id) hhalf.ne' hp hn k

/-- The Laplace law has the exponential moment `e^{(β/2)|s|}`. -/
theorem integrable_exp_abs_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    Integrable (fun s : ℝ => Real.exp ((β / 2) * |s|)) (laplaceMeasure β) := by
  have hhalf : 0 < β / 2 := by positivity
  have hsmall : |β / 2| < β := by rw [abs_of_pos hhalf]; linarith
  have hp := (laplaceMeasure_mgf hβ hsmall).1
  have hn := (laplaceMeasure_mgf (w := -(β / 2)) hβ (by simpa only [abs_neg] using hsmall)).1
  exact ProbabilityTheory.integrable_exp_mul_abs (X := id) hp hn

private noncomputable def rationalMgf (β w : ℝ) : ℝ := β ^ 2 / (β ^ 2 - w ^ 2)
private noncomputable def rationalMgfDeriv (β w : ℝ) : ℝ :=
  2 * β ^ 2 * w / (β ^ 2 - w ^ 2) ^ 2

/-- `G'(w) = 2β²w/(β² - w²)²` on `|w| < β`. -/
private theorem hasDerivAt_rationalMgf {β w : ℝ} (_hβ : 0 < β) (hw : |w| < β) :
    HasDerivAt (rationalMgf β) (rationalMgfDeriv β w) w := by
  have hbounds := abs_lt.mp hw
  have hprod : 0 < (β - w) * (β + w) := mul_pos (by linarith) (by linarith)
  have hden : 0 < β ^ 2 - w ^ 2 := by nlinarith
  have h := (hasDerivAt_const w (β ^ 2)).div
    ((hasDerivAt_const w (β ^ 2)).sub (hasDerivAt_pow 2 w)) hden.ne'
  have h' : HasDerivAt (rationalMgf β)
      ((0 * (β ^ 2 - w ^ 2) - β ^ 2 * (0 - 2 * w)) / (β ^ 2 - w ^ 2) ^ 2) w := by
    convert! h using 1
    simp [Pi.sub_apply]
  convert h' using 1
  dsimp [rationalMgfDeriv]
  ring

/-- `G'(0) = 0` for `G(w) = β²/(β² - w²)`. -/
private theorem rationalMgf_deriv_zero {β : ℝ} (hβ : 0 < β) :
    deriv (rationalMgf β) 0 = 0 := by
  simpa [rationalMgfDeriv] using
    (hasDerivAt_rationalMgf hβ (by simpa using hβ : |(0 : ℝ)| < β)).deriv

private theorem hasDerivAt_rationalMgfDeriv_zero {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (rationalMgfDeriv β) (2 / β ^ 2) 0 := by
  have hnum : HasDerivAt (fun w : ℝ => 2 * β ^ 2 * w) (2 * β ^ 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * β ^ 2)
  have hbase : HasDerivAt (fun w : ℝ => β ^ 2 - w ^ 2) 0 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (β ^ 2)).sub (hasDerivAt_pow 2 0) using 1
    simp
  have hden : HasDerivAt (fun w : ℝ => (β ^ 2 - w ^ 2) ^ 2) 0 0 := by
    convert! hbase.pow 2 using 1
    simp
  have h := hnum.div hden (by simp [hβ.ne'])
  convert! h using 1
  field_simp [hβ.ne']
  ring

/-- `G''(0) = 2/β²` for `G(w) = β²/(β² - w²)`. -/
private theorem rationalMgf_second_zero {β : ℝ} (hβ : 0 < β) :
    iteratedDeriv 2 (rationalMgf β) 0 = 2 / β ^ 2 := by
  have heq : deriv (rationalMgf β) =ᶠ[𝓝 (0 : ℝ)] rationalMgfDeriv β := by
    filter_upwards [Ioo_mem_nhds (by linarith : -β < 0) hβ] with w hw
    exact (hasDerivAt_rationalMgf hβ (abs_lt.mpr hw)).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  exact heq.deriv_eq.trans (hasDerivAt_rationalMgfDeriv_zero hβ).deriv

/-- The Laplace law is centered. -/
theorem integral_id_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    (∫ s : ℝ, s ∂laplaceMeasure β) = 0 := by
  have h := laplaceMeasure_moment_eq_iteratedDeriv hβ 1
  change (∫ s : ℝ, s ^ 1 ∂laplaceMeasure β) = iteratedDeriv 1 (rationalMgf β) 0 at h
  simpa only [pow_one, iteratedDeriv_one, rationalMgf_deriv_zero hβ] using h

/-- The second moment of the Laplace law is `2/β²` (the source's `σ_β² = 1 + 2/β²` adds the
unit variance of `f`). -/
theorem integral_sq_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    (∫ s : ℝ, s ^ 2 ∂laplaceMeasure β) = 2 / β ^ 2 :=
  (laplaceMeasure_moment_eq_iteratedDeriv hβ 2).trans (rationalMgf_second_zero hβ)

/-- **Mean and variance of the Laplace law**, from the local moment generating function only. -/
theorem laplaceMeasure_moments {β : ℝ} (hβ : 0 < β) :
    Integrable (fun s : ℝ => s) (laplaceMeasure β) ∧
      Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β) ∧
      (∫ s : ℝ, s ∂laplaceMeasure β) = 0 ∧
      (∫ s : ℝ, s ^ 2 ∂laplaceMeasure β) = 2 / β ^ 2 := by
  refine ⟨?_, integrable_pow_laplaceMeasure hβ 2, integral_id_laplaceMeasure hβ,
    integral_sq_laplaceMeasure hβ⟩
  simpa only [pow_one] using integrable_pow_laplaceMeasure hβ 1

/--
**The noise factor of BKL (111) has zero derivative at the origin**: `w ↦ log ∫ e^{(w/σ)s} dη_β(s)`
is differentiable at `0` with derivative `0`, since `η_β` is centered. -/
theorem hasDerivAt_log_integral_exp_laplaceMeasure_zero {β σ : ℝ} (hβ : 0 < β) (hσ : σ ≠ 0) :
    HasDerivAt (fun w : ℝ => Real.log (∫ s : ℝ, Real.exp (w / σ * s) ∂laplaceMeasure β)) 0 0 := by
  have hi (w : ℝ) (hw : |w / σ| < β) :
    (∫ s : ℝ, Real.exp (w / σ * s) ∂laplaceMeasure β) = β ^ 2 / (β ^ 2 - (w / σ) ^ 2) := by
    have h := (laplaceMeasure_mgf hβ hw).2
    simpa only [ProbabilityTheory.mgf, id] using h
  have hev : ∀ᶠ w in nhds (0 : ℝ), |w / σ| < β := by
    have hc : ContinuousAt (fun w : ℝ => |w / σ|) 0 := by fun_prop
    exact hc.eventually (Iio_mem_nhds (by simpa using hβ))
  have hsq : HasDerivAt (fun w : ℝ => (w / σ) ^ 2) 0 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).div_const σ).pow 2
    exact h.congr_deriv (by simp)
  have hden : HasDerivAt (fun w : ℝ => β ^ 2 - (w / σ) ^ 2) 0 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (β ^ 2)).sub hsq
    exact h.congr_deriv (by simp)
  have hG : HasDerivAt (fun w : ℝ => β ^ 2 / (β ^ 2 - (w / σ) ^ 2)) 0 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (β ^ 2)).div hden (by simp [hβ.ne'])
    exact h.congr_deriv (by simp)
  have hlog : HasDerivAt (fun w : ℝ => Real.log (β ^ 2 / (β ^ 2 - (w / σ) ^ 2))) 0 0 := by
    have h := hG.log (by simp [hβ.ne'])
    exact h.congr_deriv (by simp)
  refine hlog.congr_of_eventuallyEq ?_
  filter_upwards [hev] with w hw
  rw [hi w hw]

end Moments

end FunctionalInequalities.Probability.Line

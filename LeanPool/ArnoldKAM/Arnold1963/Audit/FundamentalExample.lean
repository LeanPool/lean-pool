/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Fundamental
public import LeanPool.ArnoldKAM.Arnold1963.Audit.Steps123

/-!
A nondegenerate quadratic integrable Hamiltonian and a nonzero angle perturbation
exercise the analytic single-step construction.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace KamProject.Arnold1963.Audit

/-- A quadratic one-action Hamiltonian used to exercise the local construction. -/
def quadraticAction (p : ComplexSpace 1) : ℂ := p 0 * p 0 / 2

theorem quadraticAction_analytic (p : ComplexSpace 1) : AnalyticAt ℂ quadraticAction p :=
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt p).mul
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt p)).div
    analyticAt_const (by norm_num)

theorem quadraticAction_fderiv (p : ComplexSpace 1) :
    fderiv ℂ quadraticAction p = p 0 • (ContinuousLinearMap.proj 0) := by
  let L : ComplexSpace 1 →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hd := ((L.hasFDerivAt (x := p)).mul L.hasFDerivAt).mul_const (2 : ℂ)⁻¹
  change HasFDerivAt (𝕜 := ℂ) quadraticAction _ p at hd
  rw [hd.fderiv]
  ext v
  simp [L]
  ring

theorem quadraticAction_frequency (p : ComplexSpace 1) : actionFrequency quadraticAction p = p := by
  ext j
  simp [actionFrequency, quadraticAction_fderiv, Fin.eq_zero j]

theorem quadraticAction_nondegenerate (p : ComplexSpace 1) :
    fderiv ℂ (actionFrequency quadraticAction) p = ContinuousLinearMap.id ℂ _ := by
  have he : actionFrequency quadraticAction = id := funext quadraticAction_frequency
  rw [he, fderiv_id]

theorem quadraticAction_second (p v w : ComplexSpace 1) :
    fderiv ℂ (fderiv ℂ quadraticAction) p v w = v 0 * w 0 := by
  have he : fderiv ℂ quadraticAction = fun p => p 0 •
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) :=
    funext quadraticAction_fderiv
  rw [he]
  let L : ComplexSpace 1 →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hd := (L.hasFDerivAt (x := p)).smul_const L
  change ((fderiv ℂ (fun y => L y • L) p) v) w = v 0 * w 0
  rw [hd.fderiv]
  simp [L]

theorem quadraticData : IntegrableData quadraticAction univ 1 where
  analytic := fun p _ => quadraticAction_analytic p
  conj_compatible := by intro p hp; simp [quadraticAction, conjVec]
  frequency_conj := by intro p hp; rw [quadraticAction_frequency, quadraticAction_frequency]
  hessian_bound := by
    intro p hp j k
    simp [quadraticAction_second, Fin.eq_zero j, Fin.eq_zero k]

/-- A compact action ball centered at one for the quadratic example. -/
def exampleActionDomain : Set (ComplexSpace 1) := closedBall (fun _ => 1) (1 / 4)

theorem exampleActionDomain_conj : ConjInvariant exampleActionDomain := by
  intro p hp
  change dist (star p) (fun _ => (1 : ℂ)) ≤ (1 / 4 : ℝ)
  have hd := dist_star_star p (fun _ : Fin 1 => (1 : ℂ))
  simpa only [Pi.star_def, star_one] using hd.le.trans hp

theorem example_frequency_lower {p : ComplexSpace 1} (hp : p ∈ exampleActionDomain) :
    (3 / 4 : ℝ) ≤ ‖p 0‖ := by
  have hh : ‖p 0 - 1‖ ≤ (1 / 4 : ℝ) :=
    (norm_le_pi_norm (p - (fun _ => 1)) 0).trans (by
      simpa only [exampleActionDomain, Metric.mem_closedBall, dist_eq_norm] using hp)
  have ht := norm_sub_norm_le (1 : ℂ) (p 0)
  rw [norm_sub_rev] at ht
  norm_num at ht
  linarith

theorem example_nonresonance {p : ComplexSpace 1} (hp : p ∈ exampleActionDomain) (N : ℝ) :
    FiniteNonresonant (actionFrequency quadraticAction p) (1 / 2) N := by
  rw [quadraticAction_frequency]
  intro k hk
  have hlen : 1 ≤ indexLength k := by
    have hh := (mem_lowModes.mp hk).1
    rw [indexLength_eq_latticeLength] at hh ⊢
    exact_mod_cast (show 1 ≤ latticeLength k by exact_mod_cast hh)
  have he : ‖indexPairing k p‖ = indexLength k * ‖p 0‖ := by
    simp [indexPairing, indexLength, Complex.norm_intCast]
  rw [he]
  have hl2 : 1 ≤ indexLength k ^ (1 + 1) := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlen 2
  have hquot : (1 / 2 : ℝ) / indexLength k ^ (1 + 1) ≤ 1 / 2 :=
    div_le_self (by norm_num) hl2
  have hprod := mul_le_mul hlen (example_frequency_lower hp) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by linarith : (0 : ℝ) ≤ indexLength k)
  exact hquot.trans (by nlinarith)

/-- A real scalar multiple of the analytic cosine perturbation. -/
def scaledCosine (ρ : ℝ≥0) (ε : ℝ) : AnalyticPhaseFunction 1 univ ρ where
  toFun z := (ε : ℂ) * (cosineExample ρ).toFun z
  domain_conj := (cosineExample ρ).domain_conj
  analytic := analyticOnNhd_const.mul (cosineExample ρ).analytic
  periodic := by
    intro p hp q hq k
    dsimp only
    rw [(cosineExample ρ).periodic p hp q hq k]
  conj_compatible := by
    intro z hz
    dsimp only
    rw [(cosineExample ρ).conj_compatible z hz]
    simp
  bounded := ⟨|ε| * (cosineExample ρ).uniformNorm,
    mul_nonneg (abs_nonneg _) ((cosineExample ρ).norm_le_iff.mp le_rfl).nonneg,
    fun z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (((cosineExample ρ).norm_le_iff.mp le_rfl).norm_le hz) (abs_nonneg _)⟩

theorem scaledCosine_bound (ρ : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) :
    (scaledCosine ρ ε).uniformNorm ≤ ε * (cosineExample ρ).uniformNorm := by
  apply ((scaledCosine ρ ε).norm_le_iff).mpr
  refine ⟨mul_nonneg hε ((cosineExample ρ).norm_le_iff.mp le_rfl).nonneg, fun z hz => ?_⟩
  change ‖(ε : ℂ) * (cosineExample ρ).toFun z‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (((cosineExample ρ).norm_le_iff.mp le_rfl).norm_le hz) hε

/-- An amplitude chosen to place the example perturbation safely below a positive threshold. -/
def exampleAmplitude (ρ : ℝ≥0) (M : ℝ) : ℝ :=
  M / (4 * ((cosineExample ρ).uniformNorm + 1))

theorem exampleAmplitude_pos (ρ : ℝ≥0) {M : ℝ} (hM : 0 < M) :
    0 < exampleAmplitude ρ M := by
  have := ((cosineExample ρ).norm_le_iff.mp le_rfl).nonneg
  unfold exampleAmplitude
  positivity

/-- A nonconstant cosine perturbation with its angle average removed. -/
def examplePerturbation (ρ : ℝ≥0) (M : ℝ) :=
  (scaledCosine ρ (exampleAmplitude ρ M)).centered

theorem examplePerturbation_bound (ρ : ℝ≥0) {M : ℝ} (hM : 0 < M) :
    (examplePerturbation ρ M).uniformNorm ≤ M := by
  have hC := ((cosineExample ρ).norm_le_iff.mp le_rfl).nonneg
  have hε := (exampleAmplitude_pos ρ hM).le
  have h1 := (scaledCosine ρ (exampleAmplitude ρ M)).uniformNorm_centered_le
  have h2 := scaledCosine_bound ρ hε
  apply h1.trans
  apply (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)).trans
  dsimp [exampleAmplitude]
  apply (le_of_lt ?_)
  have hc : 0 < 4 * ((cosineExample ρ).uniformNorm + 1) := by positivity
  field_simp
  nlinarith

theorem examplePerturbation_nonconstant (ρ : ℝ≥0) {M : ℝ} (hM : 0 < M)
    (p : ComplexSpace 1) :
    (examplePerturbation ρ M).toFun (p, 0) ≠
      (examplePerturbation ρ M).toFun (p, fun _ => (Real.pi : ℂ)) := by
  have hε := ne_of_gt (exampleAmplitude_pos ρ hM)
  simp only [examplePerturbation, AnalyticPhaseFunction.centered, AnalyticPhaseFunction.sub,
    AnalyticPhaseFunction.angleAverageFunction, scaledCosine, cosineExample,
    Pi.zero_apply, Complex.cos_zero, Complex.cos_pi, mul_one, mul_neg_one, ne_eq,
    sub_left_inj]
  intro he
  have hz : (exampleAmplitude ρ M : ℂ) = 0 := by linear_combination (1 / 2 : ℂ) * he
  exact hε (Complex.ofReal_eq_zero.mp hz)

theorem example_has_nonzero_mode {ρ : ℝ≥0} (hρ : 0 < ρ) {M : ℝ} (hM : 0 < M)
    (p : ComplexSpace 1) :
    ∃ k : FourierIndex 1, k ≠ 0 ∧ (examplePerturbation ρ M).fourierCoeff p k ≠ 0 := by
  by_contra! hall
  have hz : ∀ k, (examplePerturbation ρ M).fourierCoeff p k = 0 := by
    intro k
    by_cases hk : k = 0
    · subst k
      exact (scaledCosine ρ (exampleAmplitude ρ M)).angleAverage_centered_eq_zero (mem_univ p)
    · exact hall k hk
  have h0 := (examplePerturbation ρ M).hasSum_fourier_on_strip (mem_univ p) hρ
    (complexify_mem_angleStrip (0 : RealSpace 1) 0)
  have hπ := (examplePerturbation ρ M).hasSum_fourier_on_strip (mem_univ p) hρ
    (complexify_mem_angleStrip (fun _ => Real.pi) 0)
  have h0' : HasSum (fun _ : FourierIndex 1 => (0 : ℂ))
      ((examplePerturbation ρ M).toFun (p, complexify 0)) := by
    simpa only [hz, zero_mul] using h0
  have hπ' : HasSum (fun _ : FourierIndex 1 => (0 : ℂ))
      ((examplePerturbation ρ M).toFun (p, complexify (fun _ => Real.pi))) := by
    simpa only [hz, zero_mul] using hπ
  exact examplePerturbation_nonconstant ρ hM p (h0'.unique hπ')

theorem exampleInput {ρ β δ γ : ℝ≥0} {M : ℝ}
    (b : FundamentalParameters 1 ρ β δ γ (1 / 2) M 1) :
    FundamentalInput (E := exampleActionDomain) (β := β) (δ := δ) (γ := γ)
      (K := 1 / 2) (M := M) (Θ := 1) quadraticAction (examplePerturbation ρ M) where
  integrable := quadraticData
  domain_subset := subset_univ _
  domain_conj := exampleActionDomain_conj
  perturbation_bound := examplePerturbation_bound ρ b.perturbation_pos
  mean_zero := fun p _ => (scaledCosine ρ (exampleAmplitude ρ M)).angleAverage_centered_eq_zero
    (mem_univ p)
  nonresonant := fun _ hp => example_nonresonance hp _
  budget := b

example {ρ β δ γ : ℝ≥0} {M : ℝ}
    (b : FundamentalParameters 1 ρ β δ γ (1 / 2) M 1) :
    (exampleInput b).result.perturbation.uniformNorm < fundamentalRemainderBound 1 M δ β :=
  (exampleInput b).result.bound

end KamProject.Arnold1963.Audit

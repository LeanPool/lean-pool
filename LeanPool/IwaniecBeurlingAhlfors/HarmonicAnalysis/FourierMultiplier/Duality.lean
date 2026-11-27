/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Basic
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Norming

/-!
# Duality for Fourier multipliers

For `1 < p < ∞` and `q = p / (p − 1)`:

* `HarmonicAnalysis.multiplierNorm_conj_conjExponent` (the adjoint): the `L²`-adjoint of `T_m` is
  `T_{conj m}`, `∫ T_m f · (conj g) = ∫ f · conj (T_{conj m} g)`
  (`HarmonicAnalysis.integral_fourierMultiplier_mul_conj`), so `‖T_m‖_p = ‖T_{conj m}‖_q`, for
  bounded
  measurable `m`.
* `HarmonicAnalysis.fourierMultiplier_conj`, `HarmonicAnalysis.multiplierNorm_conj_comp_neg`
  (conjugation): `conj (T_m (conj f)) = T_{m_reflected} f` with `m_reflected (ξ) = conj (m (−ξ))`,
  so
  `‖T_{m_reflected}‖_p = ‖T_m‖_p`.

* `HarmonicAnalysis.multiplierNorm_comp_neg` (reflection): `‖T_{m (−·)}‖_p = ‖T_m‖_p`.
* `HarmonicAnalysis.multiplierNorm_conjExponent`: `‖T_m‖_p = ‖T_m‖_q` for bounded measurable `m`,
  the case of scalar symbols of Proposition 5.3.7 of Hytönen–van Neerven–Veraar–Weis (HNVW), by
  their proof: `∫ T_m f · g = ∫ T_{m (−·)} g · f`
  (`HarmonicAnalysis.integral_fourierMultiplier_comp_neg_mul`) and reflection.

The adjoint identity holds because both sides equal `∫ m · 𝓕 f · conj (𝓕 g)`
(`HarmonicAnalysis.integral_fourierInv_mul_conj`, Fubini; the bilinear form is
`HarmonicAnalysis.integral_fourierInv_mul`). With Hölder's inequality and the bound
`‖T_{conj m} g‖_q ≤ ‖T_{conj m}‖_q ‖g‖_q`, it gives `|∫ T_m f · (conj g)| ≤ ‖f‖_p ‖T_{conj m}‖_q
‖g‖_q` for every
Schwartz function `g`, hence `‖T_m f‖_p ≤ ‖T_{conj m}‖_q ‖f‖_p`, because Schwartz functions norm
`L^p`
(`HarmonicAnalysis.eLpNorm_le_of_forall_schwartz`). Conjugation rests on
`𝓕 (conj ∘ f) (ξ) = conj (𝓕 f (−ξ))` (`HarmonicAnalysis.fourier_conj`) and on the involution
`f ↦ conj ∘ f` of the Schwartz space (`HarmonicAnalysis.conjSchwartz`).

## References

* A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), [arXiv:2109.08369](https://arxiv.org/abs/2109.08369),
  §1.3.1 (for the powers of the complex Riesz transform).
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), Exercise 1.16.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*, Ergebnisse
  der Mathematik 63, Springer, 2016: Proposition 5.3.7 (p. 403).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace HarmonicAnalysis

/-- Complex conjugation of a Schwartz function, `x ↦ conj (f x)`. -/
def conjSchwartz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝓢(E, ℂ)) :
    𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f

@[simp]
theorem conjSchwartz_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝓢(E, ℂ))
    (x : E) : conjSchwartz f x = conj (f x) := by
  simp [conjSchwartz]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Fourier transform and conjugation -/

/-- `conj (𝐞 t) = 𝐞 (−t)`. -/
theorem conj_fourierChar (t : ℝ) : conj ((𝐞 t : ℂ)) = 𝐞 (-t) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- `𝓕 (conj ∘ f) (ξ) = conj (𝓕 f (−ξ))`, for every function `f`. -/
theorem fourier_conj (f : V → ℂ) (ξ : V) :
    𝓕 (fun v => conj (f v)) ξ = conj (𝓕 f (-ξ)) := by
  simp only [Real.fourier_eq, ← integral_conj, Circle.smul_def, smul_eq_mul, map_mul,
    conj_fourierChar, inner_neg_right, neg_neg]

/-- `𝓕⁻¹ (conj ∘ f) = conj ∘ 𝓕 f`, for every function `f`. -/
theorem fourierInv_conj (f : V → ℂ) (ξ : V) :
    𝓕⁻ (fun v => conj (f v)) ξ = conj (𝓕 f ξ) := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_conj, neg_neg]

/-! ### The adjoint -/

/-- `∫ 𝓕⁻¹ φ · (conj g) = ∫ φ · conj (𝓕 g)` for integrable `φ` and `g`. -/
theorem integral_fourierInv_mul_conj {φ g : V → ℂ} (hφ : Integrable φ) (hg : Integrable g) :
    ∫ x, 𝓕⁻ φ x * conj (g x) = ∫ ξ, φ ξ * conj (𝓕 g ξ) := by
  have hL : Continuous fun p : V × V => (-innerₗ V) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  have hg' : Integrable (fun x => conj (g x)) := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hg
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar hL
    hφ hg'
  have hflip (ξ : V) : VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V).flip
      (fun x => conj (g x)) ξ = conj (𝓕 g ξ) := by
    rw [← fourierInv_conj, Real.fourierInv_eq]
    simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply, LinearMap.neg_apply,
      innerₗ_apply_apply, neg_neg]
    simp_rw [real_inner_comm ξ]
  simp only [smul_eq_mul, hflip] at h
  exact h

/-- Hölder's inequality for the pairing: `|∫ u v| ≤ ‖u‖_P ‖v‖_Q` for conjugate exponents. -/
theorem enorm_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℂ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) (P Q : ℝ≥0∞)
    [ENNReal.HolderConjugate P Q] : ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u P μ * eLpNorm v Q μ := by
  calc ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm (fun x => u x * v x) 1 μ :=
        (eNorm_integral_le_lintegral_eNorm _).trans lintegral_eNorm_le_eLpNorm_one
    _ ≤ 1 * eLpNorm u P μ * eLpNorm v Q μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm (fun a b : ℂ => a * b) 1
          (fun hf hg => hf.mul hg) hu hv (ae_of_all _ fun x => by simp)
    _ = _ := by rw [one_mul]

/-- `∫ 𝓕⁻¹ φ · g = ∫ φ · 𝓕⁻¹ g` for integrable `φ` and `g`. -/
theorem integral_fourierInv_mul {φ g : V → ℂ} (hφ : Integrable φ) (hg : Integrable g) :
    ∫ x, 𝓕⁻ φ x * g x = ∫ ξ, φ ξ * 𝓕⁻ g ξ := by
  have hg' : Integrable (fun x => conj (g x)) := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hg
  have h := integral_fourierInv_mul_conj hφ hg'
  simpa only [← fourierInv_conj, Complex.conj_conj] using h

/-- The `L²`-adjoint of `T_m` is `T_{conj m}`: `∫ T_m f · (conj g) = ∫ f · conj (T_{conj m} g)`
for Schwartz
functions `f`, `g` and a bounded measurable symbol `m`. -/
theorem integral_fourierMultiplier_mul_conj {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) (f g : 𝓢(V, ℂ)) :
    ∫ x, fourierMultiplier m f x * conj (g x) =
      ∫ x, f x * conj (fourierMultiplier (fun ξ => conj (m ξ)) g x) := by
  have hm' : Measurable fun ξ => conj (m ξ) := Complex.continuous_conj.measurable.comp hm
  have hmb' : ∃ C, ∀ ξ, ‖conj (m ξ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hmb
    exact ⟨C, fun ξ => by simpa using hC ξ⟩
  have h1 := integral_fourierInv_mul_conj (integrable_smul_fourier hm hmb f) g.integrable
  have h2 := integral_fourierInv_mul_conj (integrable_smul_fourier hm' hmb' g) f.integrable
  unfold fourierMultiplier
  rw [h1]
  calc ∫ ξ, m ξ • 𝓕 (f : V → ℂ) ξ * conj (𝓕 (g : V → ℂ) ξ)
      = conj (∫ ξ, conj (m ξ) • 𝓕 (g : V → ℂ) ξ * conj (𝓕 (f : V → ℂ) ξ)) := by
        rw [← integral_conj]
        congr 1
        ext ξ
        simp only [smul_eq_mul, map_mul, Complex.conj_conj]
        ring
    _ = conj (∫ x, 𝓕⁻ (fun ξ => conj (m ξ) • 𝓕 (g : V → ℂ) ξ) x * conj (f x)) := by rw [h2]
    _ = _ := by
        rw [← integral_conj]
        congr 1
        ext x
        simp only [map_mul, Complex.conj_conj]
        ring

/-- `‖T_m‖_p ≤ ‖T_{conj m}‖_q`, by duality. -/
private theorem multiplierNorm_le_conj_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ multiplierNorm (fun ξ => conj (m ξ)) (p / (p - 1)) := by
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) :=
    hpq.ennrealOfReal
  refine iSup_le fun f => ENNReal.div_le_of_le_mul ?_
  rw [mul_comm]
  refine eLpNorm_le_of_forall_schwartz (continuous_fourierMultiplier m f) hp fun g => ?_
  rw [integral_fourierMultiplier_mul_conj hm hmb f g]
  set T := fourierMultiplier (fun ξ => conj (m ξ)) g
  have hT : Continuous T := continuous_fourierMultiplier _ g
  calc ‖∫ x, f x * conj (T x)‖ₑ ≤ eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm (fun x => conj (T x)) (ENNReal.ofReal (p / (p - 1))) volume :=
        enorm_integral_mul_le f.continuous.aestronglyMeasurable
          (Complex.continuous_conj.comp hT).aestronglyMeasurable _ _
    _ = eLpNorm f (ENNReal.ofReal p) volume * eLpNorm T (ENNReal.ofReal (p / (p - 1))) volume := by
        congr 1
        exact eLpNorm_conj _ _ _
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume * (multiplierNorm (fun ξ => conj (m ξ)) (p / (p - 1)) *
          eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) := by
        gcongr
        exact eLpNorm_fourierMultiplier_le _ _ g
    _ = _ := (mul_assoc _ _ _).symm

/-- The adjoint of `T_m` is `T_{conj m}`: for a bounded measurable symbol `m` and `1 < p < ∞`,
`‖T_m‖_{L^p} = ‖T_{conj m}‖_{L^q}`, `q = p / (p − 1)`. -/
theorem multiplierNorm_conj_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p = multiplierNorm (fun ξ => conj (m ξ)) (p / (p - 1)) := by
  refine le_antisymm (multiplierNorm_le_conj_conjExponent hm hmb hp) ?_
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hm' : Measurable fun ξ => conj (m ξ) := Complex.continuous_conj.measurable.comp hm
  have hmb' : ∃ C, ∀ ξ, ‖conj (m ξ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hmb
    exact ⟨C, fun ξ => by simpa using hC ξ⟩
  have h := multiplierNorm_le_conj_conjExponent hm' hmb' hpq.symm.lt
  rw [← hpq.symm.conjugate_eq] at h
  simpa using h

/-! ### Conjugation -/

/-- Conjugation: `conj (T_m (conj f)) = T_{m_reflected} f`, `m_reflected (ξ) = conj (m (−ξ))`. -/
theorem fourierMultiplier_conj (m : V → ℂ) (f : V → ℂ) (x : V) :
    fourierMultiplier (fun ξ => conj (m (-ξ))) f x =
      conj (fourierMultiplier m (fun v => conj (f v)) x) := by
  simp only [fourierMultiplier, Real.fourierInv_eq, fourier_conj]
  rw [← integral_conj]
  conv_lhs => rw [← integral_neg_eq_self]
  congr 1
  ext ξ
  simp only [Circle.smul_def, smul_eq_mul, map_mul, conj_fourierChar, Complex.conj_conj, neg_neg,
    inner_neg_left]

/-- Conjugation: `‖T_{m_reflected}‖_{L^p} = ‖T_m‖_{L^p}`, `m_reflected (ξ) = conj (m (−ξ))`. -/
theorem multiplierNorm_conj_comp_neg (m : V → ℂ) (p : ℝ) :
    multiplierNorm (fun ξ => conj (m (-ξ))) p = multiplierNorm m p := by
  have hsurj : Function.Surjective (conjSchwartz : 𝓢(V, ℂ) → 𝓢(V, ℂ)) :=
    fun f => ⟨conjSchwartz f, by ext x; simp⟩
  unfold multiplierNorm
  rw [← hsurj.iSup_comp]
  refine iSup_congr fun f => ?_
  have hf : (conjSchwartz f : V → ℂ) = fun x => conj (f x) := by
    ext x
    simp
  have hT : fourierMultiplier (fun ξ => conj (m (-ξ))) (conjSchwartz f) =
      fun x => conj (fourierMultiplier m f x) := by
    ext x
    have : (fun v => conj (conjSchwartz f v)) = (f : V → ℂ) := by
      ext v
      simp
    rw [fourierMultiplier_conj, this]
  rw [hT, hf]
  exact congr_arg₂ (· / ·) (eLpNorm_conj _ _ _) (eLpNorm_conj _ _ _)

/-! ### Reflection, and `‖T_m‖_p = ‖T_m‖_q` -/

/-- Reflection: `T_{m (−·)} (f (−·)) = (T_m f) (−·)` (HNVW, p. 403), for every function `f`. -/
theorem fourierMultiplier_comp_neg (m : V → ℂ) (f : V → ℂ) (x : V) :
    fourierMultiplier (fun ξ => m (-ξ)) (fun v => f (-v)) x = fourierMultiplier m f (-x) := by
  have h : (fun ξ => m (-ξ) • 𝓕 (fun v => f (-v)) ξ) =
      (fun ξ => m ξ • 𝓕 f ξ) ∘ LinearIsometryEquiv.neg ℝ (E := V) := by
    funext ξ
    exact congrArg (m (-ξ) • ·)
      (Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := V)) f ξ)
  rw [fourierMultiplier, h, Real.fourierInv_comp_linearIsometry]
  rfl

/-- Reflection: `‖T_{m (−·)}‖_{L^p} = ‖T_m‖_{L^p}` (HNVW, p. 403). -/
theorem multiplierNorm_comp_neg (m : V → ℂ) (p : ℝ) :
    multiplierNorm (fun ξ => m (-ξ)) p = multiplierNorm m p := by
  let N : 𝓢(V, ℂ) → 𝓢(V, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : V ≃L[ℝ] V)
  have hN : ∀ f x, N f x = f (-x) := fun f x => rfl
  have hsurj : Function.Surjective N := fun f => ⟨N f, by
    ext x
    simp [hN]⟩
  have hneg : ∀ h : V → ℂ, Continuous h → eLpNorm (fun x => h (-x)) (ENNReal.ofReal p) volume =
      eLpNorm h (ENNReal.ofReal p) volume := fun h hh =>
    eLpNorm_comp_measurePreserving hh.aestronglyMeasurable (Measure.measurePreserving_neg _)
  unfold multiplierNorm
  rw [← hsurj.iSup_comp]
  refine iSup_congr fun f => ?_
  have hT : fourierMultiplier (fun ξ => m (-ξ)) (N f) = fun x => fourierMultiplier m f (-x) :=
    funext fun x => fourierMultiplier_comp_neg m f x
  rw [hT, hneg _ (continuous_fourierMultiplier m f)]
  congr 1
  exact hneg f f.continuous

/-- The bilinear pairing (HNVW, proof of Proposition 5.3.7): `∫ T_m f · g = ∫ T_{m (−·)} g · f` for
Schwartz functions `f`, `g` and a bounded measurable symbol `m`. Both sides are
`∫ m 𝓕 f 𝓕⁻¹ g`. -/
theorem integral_fourierMultiplier_comp_neg_mul {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) (f g : 𝓢(V, ℂ)) :
    ∫ x, fourierMultiplier m f x * g x = ∫ x, fourierMultiplier (fun ξ => m (-ξ)) g x * f x := by
  have hmb' : ∃ C, ∀ ξ, ‖m (-ξ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hmb
    exact ⟨C, fun ξ => hC (-ξ)⟩
  have hm' : Measurable fun ξ => m (-ξ) := hm.comp measurable_neg
  unfold fourierMultiplier
  rw [integral_fourierInv_mul (integrable_smul_fourier hm hmb f) g.integrable,
    integral_fourierInv_mul (integrable_smul_fourier hm' hmb' g) f.integrable]
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1
  funext ξ
  simp only [Real.fourierInv_eq_fourier_neg, neg_neg, smul_eq_mul]
  ring

/-- `‖T_m‖_p ≤ ‖T_{m (−·)}‖_q`, by duality. -/
private theorem multiplierNorm_le_comp_neg_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ multiplierNorm (fun ξ => m (-ξ)) (p / (p - 1)) := by
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) :=
    hpq.ennrealOfReal
  refine iSup_le fun f => ENNReal.div_le_of_le_mul ?_
  rw [mul_comm]
  refine eLpNorm_le_of_forall_schwartz (continuous_fourierMultiplier m f) hp fun g => ?_
  have hg : (conjSchwartz g : V → ℂ) = fun x => conj (g x) := funext fun x => conjSchwartz_apply g x
  have h := integral_fourierMultiplier_comp_neg_mul hm hmb f (conjSchwartz g)
  simp only [conjSchwartz_apply] at h
  rw [h]
  simp_rw [mul_comm _ (f _)]
  refine (enorm_integral_mul_le f.continuous.aestronglyMeasurable
    (continuous_fourierMultiplier _ _).aestronglyMeasurable (ENNReal.ofReal p)
    (ENNReal.ofReal (p / (p - 1)))).trans ?_
  rw [mul_assoc]
  gcongr
  refine (eLpNorm_fourierMultiplier_le _ _ (conjSchwartz g)).trans_eq ?_
  rw [hg]
  exact congrArg _ (eLpNorm_conj _ _ _)

/-- **HNVW, Proposition 5.3.7**, for scalar symbols: `‖T_m‖_{L^p} = ‖T_m‖_{L^q}`,
`q = p / (p − 1)`, for a bounded measurable symbol `m` and `1 < p < ∞`. By the bilinear pairing and
reflection, `‖T_m‖_p ≤ ‖T_{m (−·)}‖_q = ‖T_m‖_q`, and the same with `p` and `q` interchanged. -/
theorem multiplierNorm_conjExponent {m : V → ℂ} (hm : Measurable m) (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C)
    {p : ℝ} (hp : 1 < p) : multiplierNorm m p = multiplierNorm m (p / (p - 1)) := by
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have h := multiplierNorm_le_comp_neg_conjExponent hm hmb hpq.symm.lt
  rw [← hpq.symm.conjugate_eq, multiplierNorm_comp_neg] at h
  refine le_antisymm ?_ h
  rw [← multiplierNorm_comp_neg m (p / (p - 1))]
  exact multiplierNorm_le_comp_neg_conjExponent hm hmb hp

end HarmonicAnalysis

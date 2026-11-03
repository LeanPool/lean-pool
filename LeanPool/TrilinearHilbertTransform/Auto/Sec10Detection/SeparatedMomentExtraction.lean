/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec10Detection.Setup

/-!
# Trilinear Hilbert transform: separated_moment_extraction
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate

open scoped Classical in
private def SeparatedMomentExtractionHArStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (ψ : ℝ → ℝ)
    (_ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (_ : ∀ (x : ℝ), |x| ≤ (1 : ℝ) → ψ x = (1 : ℝ))
    (_ : ∀ (x : ℝ), (2 : ℝ) ≤ |x| → ψ x = (0 : ℝ))
    (d : ℕ)
    (a₀ : ℝ)
    (r : ℝ)
    (C₁ : ℝ)
    (δ₃ : ℝ)
    (A : QuadraticChartData d)
    (_ : IsBoundedQuadraticChart A)
    (_ : (0 : ℝ) < r)
    (w : ℝ × ℝ → ℂ)
    (_ : IsAdmissibleLocalKernel κ a₀ r w)
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (R : ℝ → ℂ)
    (v : ℝ → ℂ)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : (1 : ℝ) ≤ C₁)
    (_ : (0 : ℝ) < δ₃),
  let ν : Measure ℝ :=
    normalizedIntervalMeasure a₀ r
  ∀ (_ : IsProbabilityMeasure ν),
  let K' : ℝ :=
    kernelFourierConst κ
  ∀ (_ : (0 : ℝ) ≤ K')
    (_ : (0 : ℝ) < C₁),
  let ζ : ℝ → ℂ :=
    fun (u : ℝ) => (↑(ψ u) : ℂ)
  ∀ (_ : ζ = fun (u : ℝ) => (↑(ψ u) : ℂ)),
  let Fa : ℝ → ℂ :=
    fun (y : ℝ) => R y * ψa y
  let Fb : ℝ → ℂ :=
    fun (y : ℝ) => v y * ψb y
  ∀ (_ : δ₃ < ‖separatedLocalForm r w (quadraticChartAtom A) a b Fa Fb‖)
    (_ : Measurable Fa)
    (_ : Measurable Fb)
    (_ : eLpNorm Fa (2 : ENNReal) ν ≤ ENNReal.ofReal C₁)
    (_ : eLpNorm Fb (2 : ENNReal) ν ≤ ENNReal.ofReal (1 : ℝ)),
  let δ₂ : ℝ :=
    δ₃ / ((K' + (1 : ℝ)) * C₁)
  ∀ (_ : δ₂ = δ₃ / ((K' + (1 : ℝ)) * C₁)),
  ∀ s < δ₂, ∃ (ξ : ℝ), s < ‖∫ (u : ℝ), (↑((𝐞 : ℝ → Circle) (-(u * ξ))) : ℂ) * (ζ u *
    quadraticChartAtom A (r * u))‖


open scoped Classical in
private def SeparatedMomentExtractionHXStatement : Prop :=
  ∀ (Dk : ℕ)
    (d : ℕ)
    (a₀ : ℝ)
    (r : ℝ)
    (C₁ : ℝ)
    (δ₃ : ℝ)
    (Λ : ℝ)
    (A : QuadraticChartData d)
    (_ : (0 : ℝ) < r)
    (w : ℝ × ℝ → ℂ)
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (R : ℝ → ℂ)
    (v : ℝ → ℂ)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : (1 : ℝ) ≤ C₁)
    (_ : (0 : ℝ) < δ₃),
  let I : Set ℝ :=
    Set.Icc a₀ (a₀ + r)
  let Fa : ℝ → ℂ :=
    fun (y : ℝ) => R y * ψa y
  let Fb : ℝ → ℂ :=
    fun (y : ℝ) => v y * ψb y
  let ε₀ : ℝ :=
    min (1 : ℝ) (δ₃ / ((2 : ℝ) * C₁))
  ∀ (_ : (0 : ℝ) < ε₀)
    (_ : ε₀ * C₁ ≤ δ₃ / (2 : ℝ))
    (ι' : Type)
    (_ : Fintype ι')
    (c : ι' → ℂ)
    (α : ι' → ℝ)
    (β : ι' → ℝ),
  let Eb : ℝ :=
    Real.exp ((↑Dk : ℝ) * ((1 : ℝ) + (3 : ℝ) * Real.log Λ) ^ Dk)
  ∀ (_ : ∑ ν : ι', ‖c ν‖ ≤ Eb)
    (_ : (0 : ℝ) < Eb),
  let Ga : ℝ → ℂ :=
    I.indicator Fa
  let Gb : ℝ → ℂ :=
    I.indicator Fb
  ∀ (_ : |((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ))⁻¹| ≤ (1 : ℝ)),
  let Φ1 : ℝ × ℝ → ℂ :=
    fun (z : ℝ × ℝ) => w z * quadraticChartAtom A z.2 * Ga (realProgressionCoordinate a
      z) * Gb (realProgressionCoordinate b z)
  ∀ (_ : separatedLocalForm r w (quadraticChartAtom A) a b Fa Fb = (↑r : ℂ)⁻¹ ^ (2 : ℕ) * ∫
      (z : ℝ × ℝ), Φ1 z),
  let Ap : ℝ × ℝ → ℂ :=
    fun (z : ℝ × ℝ) => ∑ ν : ι', c ν * (↑((𝐞 : ℝ → Circle) (α ν *
      realProgressionCoordinate a z)) : ℂ) * (↑((𝐞 : ℝ → Circle) (β ν *
      realProgressionCoordinate b z)) : ℂ)
  let Φ2 : ℝ × ℝ → ℂ :=
    fun (z : ℝ × ℝ) => Ap z * Ga (realProgressionCoordinate a z) * Gb
      (realProgressionCoordinate b z)
  let F : ι' → ℝ → ℂ :=
    fun (ν : ι') (y : ℝ) => (↑((𝐞 : ℝ → Circle) (α ν * y)) : ℂ) * Ga y
  let G : ι' → ℝ → ℂ :=
    fun (ν : ι') (y : ℝ) => (↑((𝐞 : ℝ → Circle) (β ν * y)) : ℂ) * Gb y
  ∀ (_ : ∫ (z : ℝ × ℝ), Φ2 z = ∑ ν : ι', c ν * (((↑|((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ))⁻¹| :
      ℂ) * ∫ (y : ℝ), F ν y) * ∫ (y : ℝ), G ν y))
    (_ : ‖(∫ (z : ℝ × ℝ), Φ1 z) - ∫ (z : ℝ × ℝ), Φ2 z‖ ≤ ε₀ * (r * C₁ * (r * (1 : ℝ))))
    (_ : ∀ (ν : ι'), ∫ (y : ℝ), F ν y = ∫ (y : ℝ) in I, R y * ψa y * (↑((𝐞 : ℝ → Circle) (α ν
      * y)) : ℂ))
    (_ : ∀ (ν : ι'), r⁻¹ * ‖∫ (y : ℝ), G ν y‖ ≤ (1 : ℝ))
    (_ : ∀ (α : ℝ), r⁻¹ * ‖∫ (y : ℝ) in I, R y * ψa y * (↑((𝐞 : ℝ → Circle) (α * y)) : ℂ)‖ <
      δ₃ / ((2 : ℝ) * Eb)),
  ‖separatedLocalForm r w (quadraticChartAtom A) a b Fa Fb‖ ≤ δ₃


open scoped Classical in
private def SeparatedMomentExtractionStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (Dk : ℕ)
    (d : ℕ)
    (a₀ : ℝ)
    (r : ℝ)
    (C₁ : ℝ)
    (δ₃ : ℝ)
    (Λ : ℝ)
    (A : QuadraticChartData d)
    (_ : IsBoundedQuadraticChart A)
    (_ : (0 : ℝ) < r)
    (w : ℝ × ℝ → ℂ)
    (_ : IsAdmissibleLocalKernel κ a₀ r w)
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (R : ℝ → ℂ)
    (v : ℝ → ℂ)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : (1 : ℝ) ≤ C₁)
    (_ : (0 : ℝ) < δ₃),
  let ν : Measure ℝ :=
    normalizedIntervalMeasure a₀ r
  ∀ (_ : IsProbabilityMeasure ν),
  let I : Set ℝ :=
    Set.Icc a₀ (a₀ + r)
  let Fa : ℝ → ℂ :=
    fun (y : ℝ) => R y * ψa y
  ∀ (_ : Fa = fun (y : ℝ) => R y * ψa y),
  let Fb : ℝ → ℂ :=
    fun (y : ℝ) => v y * ψb y
  ∀ (_ : δ₃ < ‖separatedLocalForm r w (quadraticChartAtom A) a b Fa Fb‖)
    (_ : Measurable Fb)
    (_ : eLpNorm Fb (2 : ENNReal) ν ≤ ENNReal.ofReal (1 : ℝ)),
  let ε₀ : ℝ :=
    min (1 : ℝ) (δ₃ / ((2 : ℝ) * C₁))
  ∀ (_ : (0 : ℝ) < ε₀)
    (_ : ε₀ * C₁ ≤ δ₃ / (2 : ℝ))
    (ι' : Type)
    (_ : Fintype ι')
    (c : ι' → ℂ)
    (α : ι' → ℝ)
    (β : ι' → ℝ)
    (_ : ∀ (ya yb : ℝ), ya ∈ Set.Icc a₀ (a₀ + r) → yb ∈ Set.Icc a₀ (a₀ + r) → ‖w (ya - (↑(↑a
      : ℕ) : ℝ) * ((yb - ya) / ((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ))), (yb - ya) / ((↑(↑b
      : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ))) * quadraticChartAtom A ((yb - ya) / ((↑(↑b : ℕ) : ℝ)
      - (↑(↑a : ℕ) : ℝ))) - ∑ ν : ι', c ν * (↑((𝐞 : ℝ → Circle) (α ν * ya)) : ℂ) * (↑((𝐞
      : ℝ → Circle) (β ν * yb)) : ℂ)‖ ≤ ε₀),
  let Eb : ℝ :=
    Real.exp ((↑Dk : ℝ) * ((1 : ℝ) + (3 : ℝ) * Real.log Λ) ^ Dk)
  ∀ (_ : ∑ ν : ι', ‖c ν‖ ≤ Eb)
    (_ : (0 : ℝ) < Eb),
  let Ga : ℝ → ℂ :=
    I.indicator Fa
  ∀ (_ : Ga = I.indicator Fa),
  let Gb : ℝ → ℂ :=
    I.indicator Fb
  ∀ (_ : Gb = I.indicator Fb)
    (_ : Measurable Ga)
    (_ : Measurable Gb)
    (_ : Integrable ((Set.Icc a₀ (a₀ + r)).indicator Fa) volume)
    (_ : ∫ (y : ℝ), ‖(Set.Icc a₀ (a₀ + r)).indicator Fa y‖ ≤ r * C₁),
  ∃ (α : ℝ), δ₃ / ((2 : ℝ) * Eb) ≤ r⁻¹ * ‖∫ (y : ℝ) in I, R y * ψa y * (↑((𝐞 : ℝ →
    Circle) (α * y)) : ℂ)‖




private theorem separated_moment_extraction_hAr : SeparatedMomentExtractionHArStatement := by
  classical
  intro κ ψ hψ hψ1 hψ0 d a₀ r C₁ δ₃ A hAb hr w hw a b hab R v ψa ψb hC₁ hδ₃ ν this
  let I : Set ℝ :=
    Set.Icc a₀ (a₀ + r)
  intro K' hK0 hC0 ζ hζ Fa Fb hX hFam hFbm hFa2 hFb2 δ₂ hδ₂ s hs
  by_contra hcon
  push Not at hcon
  have hs0 : 0 ≤ s := (norm_nonneg _).trans (hcon 0)
  have hM : ∀ ξ, ‖∫ u, quadraticChartAtom A (r * u) * ((ψ u : ℝ) : ℂ) *
      (Real.fourierChar (-(ξ * u)) : ℂ)‖ ≤ s := by
    intro ξ
    refine le_of_eq_of_le ?_ (hcon ξ)
    congr 1; congr 1; funext u; rw [hζ, mul_comm ξ u]; ring
  have hsep := separated_form_le hr hw a b hab (quadraticChartAtom_measurable A) hAb
    (plateau_integrable hψ hψ0) hψ1 hM hFam hFbm
    (memLp_Icc_of_normalized hr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFa2))
    (memLp_Icc_of_normalized hr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFb2))
  have hSa := sqrt_normalized_Icc_le_of_eLpNorm hr hC0.le hFa2
  have hSb := sqrt_normalized_Icc_le_of_eLpNorm hr zero_le_one hFb2
  change ‖separatedLocalForm r w (quadraticChartAtom A) a b Fa Fb‖ ≤ _ at hsep
  have h1 : K' * s * Real.sqrt (r⁻¹ * ∫ x in I, ‖Fa x‖ ^ 2) *
      Real.sqrt (r⁻¹ * ∫ x in I, ‖Fb x‖ ^ 2) ≤ K' * δ₂ * C₁ * 1 := by
    gcongr
  have h2 : K' * δ₂ * C₁ * 1 ≤ δ₃ := by
    rw [hδ₂, mul_one]
    have : (K' + 1) * C₁ * (δ₃ / ((K' + 1) * C₁)) = δ₃ := by field_simp
    nlinarith only [div_pos hδ₃ (by positivity : (0 : ℝ) < (K' + 1) * C₁), hC₁, this]
  linarith
-- uniform separation of the kernel



private theorem separated_moment_extraction_hX_ : SeparatedMomentExtractionHXStatement := by
  classical
  intro Dk d a₀ r C₁ δ₃ Λ A hr w a b R v ψa ψb hC₁ hδ₃ I Fa Fb ε₀ hε₀0 hε₀C ι' hι' c α β Eb hcsum'
    hEb0 Ga Gb hjac Φ1 hXr Ap Φ2 F G hΦ2int herr hmomF hmomG hcon
  rw [hXr]
  have hsplit : (r : ℂ)⁻¹ ^ 2 * ∫ z, Φ1 z = (r : ℂ)⁻¹ ^ 2 * (∫ z, Φ2 z) +
      (r : ℂ)⁻¹ ^ 2 * ((∫ z, Φ1 z) - ∫ z, Φ2 z) := by ring
  have hrr : ‖((r : ℂ)⁻¹ ^ 2)‖ = r⁻¹ ^ 2 := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hmain : ‖(r : ℂ)⁻¹ ^ 2 * ∫ z, Φ2 z‖ ≤ δ₃ / 2 := by
    rw [hΦ2int, Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ ν, ‖(r : ℂ)⁻¹ ^ 2 * (c ν * (|((b : ℝ) - (a : ℝ))⁻¹| * (∫ y, F ν y) *
        ∫ y, G ν y))‖ ≤ ‖c ν‖ * (δ₃ / (2 * Eb)) := by
      intro ν
      have hm := hcon (α ν)
      rw [← hmomF ν] at hm
      have hg := hmomG ν
      rw [norm_mul, hrr, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_abs]
      have e : r⁻¹ ^ 2 * (‖c ν‖ * (|((b : ℝ) - (a : ℝ))⁻¹| * ‖∫ y, F ν y‖ * ‖∫ y, G ν y‖)) =
          ‖c ν‖ * (|((b : ℝ) - (a : ℝ))⁻¹| * (r⁻¹ * ‖∫ y, F ν y‖) *
            (r⁻¹ * ‖∫ y, G ν y‖)) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have h0 : 0 ≤ r⁻¹ * ‖∫ y, F ν y‖ := by positivity
      calc |((b : ℝ) - (a : ℝ))⁻¹| * (r⁻¹ * ‖∫ y, F ν y‖) * (r⁻¹ * ‖∫ y, G ν y‖)
          ≤ 1 * (δ₃ / (2 * Eb)) * 1 := by
            gcongr
        _ = _ := by ring
    calc ∑ ν, ‖(r : ℂ)⁻¹ ^ 2 * (c ν * (|((b : ℝ) - (a : ℝ))⁻¹| * (∫ y, F ν y) *
          ∫ y, G ν y))‖ ≤ ∑ ν, ‖c ν‖ * (δ₃ / (2 * Eb)) := Finset.sum_le_sum fun ν _ => hterm ν
      _ = (∑ ν, ‖c ν‖) * (δ₃ / (2 * Eb)) := by rw [Finset.sum_mul]
      _ ≤ Eb * (δ₃ / (2 * Eb)) := by gcongr
      _ = δ₃ / 2 := by field_simp
  have herr' : ‖(r : ℂ)⁻¹ ^ 2 * ((∫ z, Φ1 z) - ∫ z, Φ2 z)‖ ≤ δ₃ / 2 := by
    rw [norm_mul, hrr]
    calc r⁻¹ ^ 2 * ‖(∫ z, Φ1 z) - ∫ z, Φ2 z‖ ≤ r⁻¹ ^ 2 * (ε₀ * (r * C₁ * (r * 1))) :=
          mul_le_mul_of_nonneg_left herr (by positivity)
      _ = ε₀ * C₁ := by field_simp
      _ ≤ δ₃ / 2 := hε₀C
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith



private theorem separated_moment_extraction_stage_1 : SeparatedMomentExtractionStage1Statement := by
  classical
  intro κ Dk d a₀ r C₁ δ₃ Λ A hAb hr w hw a b hab R v ψa ψb hC₁ hδ₃ ν this I Fa hFa Fb hX hFbm
    hFb2 ε₀ hε₀0 hε₀C ι' hι' c α β hpt Eb hcsum' hEb0 Ga hGa Gb hGb hGam hGbm hGai hGan
  obtain ⟨hGbi, hGbn⟩ := integral_indicator_norm_le_of_eLpNorm hr hFbm zero_le_one hFb2
  have hab' : (a : ℝ) ≠ (b : ℝ) := by
    intro h; have := one_le_abs_fin_sub hab; rw [h, sub_self, abs_zero] at this; linarith
  obtain ⟨hPi, hPeq⟩ := real_progression_pair_integral_norm hGam hGbm hGai hGbi hab'
  have hjac : |((b : ℝ) - (a : ℝ))⁻¹| ≤ 1 := by
    rw [abs_inv]; exact inv_le_one_of_one_le₀ (one_le_abs_fin_sub hab)
  set! Φ1 : ℝ × ℝ → ℂ := fun z => w z * quadraticChartAtom A z.2 *
    Ga (realProgressionCoordinate a z) * Gb (realProgressionCoordinate b z) with hΦ1
  have hXr : separatedLocalForm r w (quadraticChartAtom A) a b Fa Fb =
      (r : ℂ)⁻¹ ^ 2 * ∫ z, Φ1 z := by
    unfold separatedLocalForm; congr 2; funext z
    by_cases hz : w z = 0
    · simp [hΦ1, hz]
    have hs := admissibleLocalKernel_support hr.le hw z hz
    simp only [hΦ1, hGa, hGb]
    rw [Set.indicator_of_mem (show realProgressionCoordinate a z ∈ I from hs a),
      Set.indicator_of_mem (show realProgressionCoordinate b z ∈ I from hs b)]
  -- the separated approximation
  set! Ap : ℝ × ℝ → ℂ := fun z => ∑ ν, c ν *
    (Real.fourierChar (α ν * realProgressionCoordinate a z) : ℂ) *
    (Real.fourierChar (β ν * realProgressionCoordinate b z) : ℂ) with hAp
  set! Φ2 : ℝ × ℝ → ℂ := fun z => Ap z * Ga (realProgressionCoordinate a z) *
    Gb (realProgressionCoordinate b z) with hΦ2
  have hpw : ∀ z, ‖Φ1 z - Φ2 z‖ ≤ ε₀ * (‖Ga (realProgressionCoordinate a z)‖ *
      ‖Gb (realProgressionCoordinate b z)‖) := by
    intro z
    by_cases hya : realProgressionCoordinate a z ∈ I
    · by_cases hyb : realProgressionCoordinate b z ∈ I
      · have h := hpt _ _ hya hyb
        have ht : (realProgressionCoordinate b z - realProgressionCoordinate a z) /
            ((b : ℝ) - (a : ℝ)) = z.2 := by
          unfold realProgressionCoordinate
          field_simp [sub_ne_zero.mpr hab'.symm]
          ring
        rw [ht] at h
        have hx : realProgressionCoordinate a z - (a : ℝ) * z.2 = z.1 := by
          unfold realProgressionCoordinate; ring
        rw [hx, Prod.mk.eta] at h
        have e : Φ1 z - Φ2 z = (w z * quadraticChartAtom A z.2 - Ap z) *
            (Ga (realProgressionCoordinate a z) * Gb (realProgressionCoordinate b z)) := by
          simp only [hΦ1, hΦ2]; ring
        rw [e, norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right h (by positivity)
      · simp [hΦ1, hΦ2, Set.indicator_of_notMem hyb, hGb]
    · simp [hΦ1, hΦ2, Set.indicator_of_notMem hya, hGa]
  -- integrability
  set! S := localKernelSupBound κ with hS
  have hΦ1m : Measurable Φ1 := by
    have hca := (continuous_realProgressionCoordinate a).measurable
    have hcb := (continuous_realProgressionCoordinate b).measurable
    exact ((hw.smooth.continuous.measurable.mul
      ((quadraticChartAtom_measurable A).comp measurable_snd)).mul (hGam.comp hca)).mul
      (hGbm.comp hcb)
  have hΦ1i : Integrable Φ1 := by
    refine (hPi.const_mul S).mono' hΦ1m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [hΦ1, norm_mul]
    have h1 := admissibleLocalKernel_norm_le hw z
    have h2 := hAb z.2
    have h3 := norm_nonneg (Ga (realProgressionCoordinate a z))
    have h4 := norm_nonneg (Gb (realProgressionCoordinate b z))
    have h5 := norm_nonneg (w z)
    calc ‖w z‖ * ‖quadraticChartAtom A z.2‖ * ‖Ga (realProgressionCoordinate a z)‖ *
          ‖Gb (realProgressionCoordinate b z)‖
        ≤ S * 1 * ‖Ga (realProgressionCoordinate a z)‖ * ‖Gb (realProgressionCoordinate b z)‖ := by
          gcongr
          exact localKernelSupBound_nonneg κ
      _ = S * (‖Ga (z.1 + (a : ℝ) * z.2)‖ * ‖Gb (z.1 + (b : ℝ) * z.2)‖) := by
          unfold realProgressionCoordinate; ring
  set! F : ι' → ℝ → ℂ := fun ν y => (Real.fourierChar (α ν * y) : ℂ) * Ga y with hF
  set! G : ι' → ℝ → ℂ := fun ν y => (Real.fourierChar (β ν * y) : ℂ) * Gb y with hG
  have hFm : ∀ ν, Measurable (F ν) := fun ν =>
    ((continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp
      (measurable_const.mul measurable_id)).mul hGam
  have hGm : ∀ ν, Measurable (G ν) := fun ν =>
    ((continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp
      (measurable_const.mul measurable_id)).mul hGbm
  have hFn : ∀ ν y, ‖F ν y‖ = ‖Ga y‖ := fun ν y => by simp [hF]
  have hGn : ∀ ν y, ‖G ν y‖ = ‖Gb y‖ := fun ν y => by simp [hG]
  have hFi : ∀ ν, Integrable (F ν) := fun ν =>
    hGai.norm.mono' (hFm ν).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => le_of_eq (hFn ν y))
  have hGi : ∀ ν, Integrable (G ν) := fun ν =>
    hGbi.norm.mono' (hGm ν).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => le_of_eq (hGn ν y))
  have hpair := fun ν => real_progression_pair_integral (hFm ν) (hGm ν) (hFi ν) (hGi ν) hab'
  have hΦ2eq : Φ2 = fun z =>
      ∑ ν, c ν * (F ν (z.1 + (a : ℝ) * z.2) * G ν (z.1 + (b : ℝ) * z.2)) := by
    funext z
    simp only [hΦ2, hAp, hF, hG, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro ν _
    unfold realProgressionCoordinate; ring
  have hΦ2i : Integrable Φ2 := by
    rw [hΦ2eq]; exact integrable_finsetSum _ fun ν _ => (hpair ν).1.const_mul (c ν)
  have hΦ2int : ∫ z, Φ2 z = ∑ ν, c ν * (|((b : ℝ) - (a : ℝ))⁻¹| * (∫ y, F ν y) * ∫ y, G ν y) := by
    rw [hΦ2eq, integral_finsetSum _ fun ν _ => (hpair ν).1.const_mul (c ν)]
    apply Finset.sum_congr rfl; intro ν _
    rw [integral_const_mul, (hpair ν).2]
  -- the error of the separated approximation
  have herr : ‖(∫ z, Φ1 z) - ∫ z, Φ2 z‖ ≤ ε₀ * (r * C₁ * (r * 1)) := by
    rw [← integral_sub hΦ1i hΦ2i]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpw' : ∀ z, ‖(Φ1 - Φ2) z‖ ≤ ε₀ * (‖Ga (z.1 + (a : ℝ) * z.2)‖ *
        ‖Gb (z.1 + (b : ℝ) * z.2)‖) := fun z => hpw z
    refine (integral_mono (hΦ1i.sub hΦ2i).norm (hPi.const_mul ε₀) hpw').trans ?_
    rw [integral_const_mul, hPeq]
    apply mul_le_mul_of_nonneg_left _ hε₀0.le
    have hGa0 : 0 ≤ ∫ u, ‖Ga u‖ := integral_nonneg fun _ => norm_nonneg _
    have hGb0 : 0 ≤ ∫ u, ‖Gb u‖ := integral_nonneg fun _ => norm_nonneg _
    calc |((b : ℝ) - (a : ℝ))⁻¹| * (∫ u, ‖Ga u‖) * ∫ v, ‖Gb v‖
        ≤ 1 * (r * C₁) * (r * 1) := by gcongr
      _ = _ := by ring
  -- the moments
  have hmomF : ∀ ν, ∫ y, F ν y = ∫ y in I, R y * ψa y * (Real.fourierChar (α ν * y) : ℂ) := by
    intro ν
    rw [← integral_indicator measurableSet_Icc]
    congr 1; funext y
    by_cases hy : y ∈ I
    · simp only [hF, hGa, hFa, Set.indicator_of_mem hy]
      rw [Set.indicator_of_mem (show y ∈ Set.Icc a₀ (a₀ + r) from hy)]; ring
    · simp only [hF, hGa, Set.indicator_of_notMem hy, mul_zero]
      rw [Set.indicator_of_notMem (show y ∉ Set.Icc a₀ (a₀ + r) from hy)]
  have hmomG : ∀ ν, r⁻¹ * ‖∫ y, G ν y‖ ≤ 1 := by
    intro ν
    have h : ‖∫ y, G ν y‖ ≤ ∫ y, ‖Gb y‖ :=
      (norm_integral_le_integral_norm (G ν)).trans (le_of_eq (integral_congr_ae
        (Filter.Eventually.of_forall fun y => hGn ν y)))
    rw [inv_mul_le_iff₀ hr]
    linarith
  by_contra hcon
  push Not at hcon
  have hX' : ‖separatedLocalForm r w (quadraticChartAtom A) a b Fa Fb‖ ≤ δ₃ := by
    expose_names
    exact @separated_moment_extraction_hX_ Dk d a₀ r C₁ δ₃ Λ A hr w a b R v ψa ψb hC₁ hδ₃ hε₀0
      hε₀C ι' hι' c α β hcsum' hEb0 hjac hXr hΦ2int herr hmomF hmomG hcon
  exact absurd hX (not_lt.mpr hX')


/-- Blueprint lem:detection, line 1473: a large separated form forces `A_r` to be large,
its kernel is separated by lem:separation, and one normalized moment of `R` against
`ψ_a e(α ·)` is large. -/
theorem separated_moment_extraction (κ : LocalKernelClass) (c₁ : ℕ) (hc₁ : 1 ≤ c₁) :
    ∃ (Dk : ℕ) (Lζ : ℝ), 1 ≤ Dk ∧ 1 ≤ Lζ ∧
    ∀ {d : ℕ} {a₀ r H₁ C₁ δ₃ Λ : ℝ} (A : QuadraticChartData d),
      QuadraticChartComplexity c₁ H₁ A → IsBoundedQuadraticChart A → 0 < r →
      ∀ {w : ℝ × ℝ → ℂ}, IsAdmissibleLocalKernel κ a₀ r w → ∀ {a b : Fin 4}, a ≠ b →
      ∀ {R v ψa ψb : ℝ → ℂ}, Measurable R → Measurable v → Measurable ψa → Measurable ψb →
      (∀ y, ‖ψa y‖ ≤ 1) → (∀ y, ‖ψb y‖ ≤ 1) → 1 ≤ C₁ →
      eLpNorm R 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal C₁ →
      eLpNorm v 2 (normalizedIntervalMeasure a₀ r) ≤ 1 → 0 < δ₃ →
      δ₃ < ‖separatedLocalForm r w (quadraticChartAtom A) a b (fun y => R y * ψa y)
        (fun y => v y * ψb y)‖ →
      1 ≤ Λ → H₁ ≤ Λ → Lζ ≤ Λ → (kernelFourierConst κ + 1) * C₁ / δ₃ ≤ Λ →
      2 * C₁ / δ₃ ≤ Λ →
      ∃ α : ℝ, δ₃ / (2 * Real.exp (Dk * (1 + 3 * Real.log Λ) ^ Dk)) ≤
        r⁻¹ * ‖∫ y in Set.Icc a₀ (a₀ + r), R y * ψa y * (Real.fourierChar (α * y) : ℂ)‖ := by
  obtain ⟨ψ, Kψ, hKψ, hψ, hψ1', hψ1, hψ0, hψd⟩ := exists_plateau_cutoff
  obtain ⟨Dk, hDk, happrox⟩ := separatedKernelApprox c₁ hc₁ 2 (by norm_num) κ
  refine ⟨Dk, max 1 (((Kψ : ℝ) * 2) ^ (Kψ * 2)), hDk, le_max_left _ _, ?_⟩
  intro d a₀ r H₁ C₁ δ₃ Λ A hA hAb hr w hw a b hab R v ψa ψb hRm hvm hψam hψbm hψab hψbb hC₁
    hR hv hδ₃ hX hΛ1 hHΛ hLΛ hΛ2 hΛ3
  set ν := normalizedIntervalMeasure a₀ r with hν
  have : IsProbabilityMeasure ν := normalizedIntervalMeasure_probability a₀ hr
  set I := Set.Icc a₀ (a₀ + r) with hI
  set K' := kernelFourierConst κ with hK'
  have hK0 : 0 ≤ K' := by
    rw [hK']; unfold kernelFourierConst
    have := kernelDerivBound_nonneg κ 0
    have := kernelDerivBound_nonneg κ 3
    positivity
  have hC0 : 0 < C₁ := by linarith
  -- the cutoff
  set! ζ : ℝ → ℂ := fun u => ((ψ u : ℝ) : ℂ) with hζ
  have hζm : Measurable ζ := Complex.measurable_ofReal.comp hψ.continuous.measurable
  have hζb : ∀ u, ‖ζ u‖ ≤ Λ := fun u => by
    rw [hζ, Complex.norm_real, Real.norm_eq_abs]; exact (hψ1' u).trans hΛ1
  have hζL : ∀ u v, ‖ζ v - ζ u‖ ≤ Λ * |v - u| := by
    intro u v
    rw [hζ, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (plateau_lipschitz hψ hψd u v).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hLΛ) (abs_nonneg _)
  have hζs : ∀ u, ζ u ≠ 0 → |u| ≤ 2 := by
    intro u hu
    by_contra h
    exact hu (by simp only [hζ, hψ0 u (not_le.mp h).le, Complex.ofReal_zero])
  -- the two separated inputs
  set Fa : ℝ → ℂ := fun y => R y * ψa y with hFa
  set Fb : ℝ → ℂ := fun y => v y * ψb y with hFb
  have hFam : Measurable Fa := hRm.mul hψam
  have hFbm : Measurable Fb := hvm.mul hψbm
  have hFale : ∀ y, ‖Fa y‖ ≤ ‖R y‖ := fun y => by
    rw [hFa, norm_mul]; simpa using mul_le_mul_of_nonneg_left (hψab y) (norm_nonneg (R y))
  have hFble : ∀ y, ‖Fb y‖ ≤ ‖v y‖ := fun y => by
    rw [hFb, norm_mul]; simpa using mul_le_mul_of_nonneg_left (hψbb y) (norm_nonneg (v y))
  have hFa2 : eLpNorm Fa 2 ν ≤ ENNReal.ofReal C₁ :=
    (eLpNorm_mono hFam.aestronglyMeasurable hFale).trans hR
  have hFb2 : eLpNorm Fb 2 ν ≤ ENNReal.ofReal 1 :=
    ((eLpNorm_mono hFbm.aestronglyMeasurable hFble).trans hv).trans_eq ENNReal.ofReal_one.symm
  -- `A_r` is large
  set! δ₂ := δ₃ / ((K' + 1) * C₁) with hδ₂
  have hδ₂0 : 0 < δ₂ := by positivity
  have hAr : ∀ s < δ₂, ∃ ξ : ℝ, s < ‖∫ u, (Real.fourierChar (-(u * ξ)) : ℂ) *
      (ζ u * quadraticChartAtom A (r * u))‖ := by
    expose_names
    exact @separated_moment_extraction_hAr κ ψ hψ hψ1 hψ0 d a₀ r C₁ δ₃ A hAb hr w hw a b hab R v
      ψa ψb hC₁ hδ₃ this hK0 hC0 hζ hX hFam hFbm hFa2 hFb2 hδ₂
  set! ε₀ := min 1 (δ₃ / (2 * C₁)) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₀1 : ε₀ ≤ 1 := min_le_left _ _
  have hε₀C : ε₀ * C₁ ≤ δ₃ / 2 := by
    have := min_le_right 1 (δ₃ / (2 * C₁))
    calc ε₀ * C₁ ≤ δ₃ / (2 * C₁) * C₁ := mul_le_mul_of_nonneg_right this hC0.le
      _ = δ₃ / 2 := by field_simp
  have happ := happrox Λ δ₂ ε₀ r a₀ A (quadraticChartComplexity_mono hA hHΛ) hr w hw ζ hζm
    hζb hζL hζs hδ₂0 hε₀0 hε₀1 hAr (a : ℝ) (b : ℝ) (one_le_abs_fin_sub hab)
    (abs_fin_four_le a)
  obtain ⟨ι', hι', c, α, β, -, hcsum, hpt⟩ := happ
  set Eb := Real.exp (Dk * (1 + 3 * Real.log Λ) ^ Dk) with hEb
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  have hE₂ : Real.exp (Dk * (1 + Real.log Λ + Real.log (max 1 δ₂⁻¹) + Real.log ε₀⁻¹) ^ Dk)
      ≤ Eb := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 : Real.log (max 1 δ₂⁻¹) ≤ Real.log Λ := by
      apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _))
      apply max_le hΛ1
      rw [hδ₂, inv_div]; exact hΛ2
    have h2 : Real.log ε₀⁻¹ ≤ Real.log Λ := by
      apply Real.log_le_log (inv_pos.mpr hε₀0)
      rw [inv_le_comm₀ hε₀0 (by linarith)]
      apply le_min (inv_le_one_of_one_le₀ hΛ1)
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]; exact hΛ3
    have h3 : 0 ≤ Real.log (max 1 δ₂⁻¹) := Real.log_nonneg (le_max_left _ _)
    have h4 : 0 ≤ Real.log ε₀⁻¹ := Real.log_nonneg (one_le_inv₀ hε₀0 |>.mpr hε₀1)
    exact pow_le_pow_left₀ (by positivity) (by linarith) Dk
  have hcsum' : (∑ ν, ‖c ν‖) ≤ Eb := hcsum.trans hE₂
  have hEb0 : 0 < Eb := Real.exp_pos _
  -- restricted inputs
  set! Ga := I.indicator Fa with hGa
  set! Gb := I.indicator Fb with hGb
  have hGam : Measurable Ga := hFam.indicator measurableSet_Icc
  have hGbm : Measurable Gb := hFbm.indicator measurableSet_Icc
  obtain ⟨hGai, hGan⟩ := integral_indicator_norm_le_of_eLpNorm hr hFam hC0.le hFa2
  expose_names
  exact @separated_moment_extraction_stage_1 κ Dk d a₀ r C₁ δ₃ Λ A hAb hr w hw a b hab R v ψa ψb
    hC₁ hδ₃ this hFa hX hFbm hFb2 hε₀0 hε₀C ι' hι' c α β hpt hcsum' hEb0 hGa hGb hGam hGbm hGai
    hGan

/-- The witness chart `conj(ψ_a e(α ·))` of a moment `∫ R ψ_a e(α ·)`. -/
theorem moment_witness_chart {d c₁ : ℕ} {H₁ : ℝ} (A : QuadraticChartData d)
    (hA : QuadraticChartComplexity c₁ H₁ A) (hAb : IsBoundedQuadraticChart A) (hc₁ : 1 ≤ c₁)
    (α : ℝ) :
    ∃ Φ : QuadraticChartData (d + 0), QuadraticChartComplexity c₁ (H₁ ^ 6) Φ ∧
      IsBoundedQuadraticChart Φ ∧ ∀ y, conj (quadraticChartAtom Φ y) =
        quadraticChartAtom A y * (Real.fourierChar (α * y) : ℂ) := by
  refine ⟨conjugateQuadraticChart (productQuadraticChart A (ordinaryQuadraticChart 0 α)),
    conjugateQuadraticChart_complexity (productQuadraticChart_complexity hA
      (ordinaryQuadraticChart_complexity c₁ hA.lower 0 α) hc₁),
    conjugateQuadraticChart_bounded (productQuadraticChart_bounded hAb
      (ordinaryQuadraticChart_bounded 0 α)), fun y => ?_⟩
  rw [conjugateQuadraticChart_atom, productQuadraticChart_atom, ordinaryQuadraticChart_atom]
  simp

theorem intervalIntegral_eq_Icc {a₀ r : ℝ} (hr : 0 < r) (F : ℝ → ℂ) :
    ∫ x in a₀..a₀ + r, F x = ∫ x in Set.Icc a₀ (a₀ + r), F x := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

theorem qple_max {Y a b : ℝ} {K : ℕ} (ha : QPLe Y K a) (hb : QPLe Y K b) :
    QPLe Y K (max a b) := max_le ha hb

theorem qple_of_exp_Y {Y a : ℝ} (ha : 0 < a) (h : Real.log a ≤ Y) : QPLe Y 1 a := by
  unfold QPLe
  rw [← Real.exp_log ha]; simpa using h

theorem fin_cast_int_real (a : Fin 4) : (((a : ℕ) : ℤ) : ℝ) = (a : ℝ) := by push_cast; rfl

theorem abs_fin_int_le (a : Fin 4) : |((a : ℕ) : ℤ)| ≤ 3 := by
  rw [abs_of_nonneg (by positivity)]
  have := a.isLt
  omega

theorem exp_three_log_le {Λ : ℝ} (hΛ : 1 ≤ Λ) (Dk : ℕ) :
    Real.exp (Dk * (1 + 3 * Real.log Λ) ^ Dk) ≤
      Real.exp ((Dk * 3 ^ Dk : ℕ) * (1 + Real.log Λ) ^ (Dk * 3 ^ Dk)) := by
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have h1 : (1 + 3 * Real.log Λ) ^ Dk ≤ (3 * (1 + Real.log Λ)) ^ Dk :=
    pow_le_pow_left₀ (by positivity) (by linarith) Dk
  have h2 : (1 + Real.log Λ) ^ Dk ≤ (1 + Real.log Λ) ^ (Dk * 3 ^ Dk) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_mul_of_pos_right _ (by positivity))
  rw [mul_pow] at h1
  push_cast
  have h3 : (0 : ℝ) ≤ Dk := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ 3 ^ Dk := by positivity
  calc (Dk : ℝ) * (1 + 3 * Real.log Λ) ^ Dk ≤ Dk * (3 ^ Dk * (1 + Real.log Λ) ^ Dk) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ ≤ Dk * (3 ^ Dk * (1 + Real.log Λ) ^ (Dk * 3 ^ Dk)) := by gcongr
    _ = _ := by ring

/-- Blueprint lem:detection, line 1473: an atom pair with a large local form against
`R, v` yields a large normalized moment of `R` against a bounded atom, with complexity
and moment quasipolynomial in `H, C₁, δ₀⁻¹`. -/
theorem detection_atom_pair (κ : LocalKernelClass) (c₀ : ℕ) (hc₀ : 1 ≤ c₀) :
    ∃ (c₂ K : ℕ), 1 ≤ c₂ ∧ 1 ≤ K ∧
    ∀ {a₀ r H C₁ δ₀ : ℝ} {d e : ℕ} (A : QuadraticChartData d) (A' : QuadraticChartData e),
      QuadraticChartComplexity c₀ H A → QuadraticChartComplexity c₀ H A' →
      IsBoundedQuadraticChart A → IsBoundedQuadraticChart A' → 0 < r →
      ∀ {w : ℝ × ℝ → ℂ}, IsAdmissibleLocalKernel κ a₀ r w →
      ∀ (f : Fin 4 → ℝ → ℂ), (∀ j, Measurable (f j)) →
      ∀ {jR i k lv : Fin 4}, jR ≠ i → jR ≠ k → jR ≠ lv → i ≠ k → i ≠ lv → k ≠ lv →
      f i = quadraticChartAtom A → f k = quadraticChartAtom A' → 1 ≤ C₁ →
      eLpNorm (f jR) 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal C₁ →
      eLpNorm (f lv) 2 (normalizedIntervalMeasure a₀ r) ≤ 1 → 0 < δ₀ → δ₀ ≤ 1 →
      δ₀ < ‖localProgressionForm r w f‖ →
      ∃ (d'' : ℕ) (Φ : QuadraticChartData d''),
        QuadraticChartComplexity c₂
          (Real.exp (K * (1 + Real.log H + Real.log C₁ + Real.log (1 / δ₀)) ^ K)) Φ ∧
        IsBoundedQuadraticChart Φ ∧
        (Real.exp (K * (1 + Real.log H + Real.log C₁ + Real.log (1 / δ₀)) ^ K))⁻¹ ≤
          r⁻¹ * ‖∫ x in a₀..a₀ + r, f jR x * conj (quadraticChartAtom Φ x)‖ := by
  obtain ⟨cp, W₀, hcp, hW₀, hpad⟩ := exists_pad_chart
  set c₀' := max c₀ cp with hc₀'
  have hc₀'1 : 1 ≤ c₀' := le_trans hc₀ (le_max_left _ _)
  obtain ⟨c₁, D, hc₁, hD, hsep⟩ := progressionSeparation c₀' hc₀'1
  obtain ⟨Dk, Lζ, hDk, hLζ, hext⟩ := separated_moment_extraction κ c₁ hc₁
  set W' := localFormUniformConstant κ with hW'
  set K' := kernelFourierConst κ with hK'
  -- the budget exponents
  set k1 : ℕ := 1 + ⌈W₀⌉₊ with hk1
  set! k2 : ℕ := 6 * k1 + k1 with hk2
  set! k3 : ℕ := D * (1 + k2) ^ D + k2 * D with hk3
  set! kW : ℕ := ⌈W'⌉₊ + 1 with hkW
  set! k4 : ℕ := ⌈(2 : ℝ)⌉₊ + k3 + kW + 1 with hk4
  set! k5 : ℕ := 6 * (k3 + k4) + (k3 + k4) with hk5
  set! kδ : ℕ := ⌈(2 : ℝ)⌉₊ + k3 + 1 with hkδ
  set! kΛ1 : ℕ := ⌈K' + 1⌉₊ + 1 + kδ with hkΛ1
  set! kΛ2 : ℕ := ⌈(2 : ℝ)⌉₊ + 1 + kδ with hkΛ2
  set! kΛ : ℕ := k5 + ⌈Lζ⌉₊ + kΛ1 + kΛ2 with hkΛ
  set! D3 : ℕ := Dk * 3 ^ Dk with hD3
  set! k6 : ℕ := D3 * (1 + kΛ) ^ D3 + kΛ * D3 with hk6
  set! k7 : ℕ := ⌈(2 : ℝ)⌉₊ + k6 + kδ with hk7
  set! k8 : ℕ := 6 * k5 + k5 with hk8
  set! Kf : ℕ := k7 + k8 + 1 with hKf
  refine ⟨c₁, Kf, hc₁, by omega, ?_⟩
  intro a₀ r H C₁ δ₀ d e A A' hA hA' hAb hA'b hr w hw f hf jR i k lv h1 h2 h3 h4 h5 h6 hfi hfk
    hC₁ hR hv hδ₀ hδ₀1 hHf
  set Y := 1 + Real.log H + Real.log C₁ + Real.log (1 / δ₀) with hYdef
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlC : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁
  have hlδ : 0 ≤ Real.log (1 / δ₀) := Real.log_nonneg (by rw [le_div_iff₀ hδ₀]; linarith)
  have hY : 1 ≤ Y := by rw [hYdef]; linarith
  have qH : QPLe Y 1 H := qple_of_exp_Y (by linarith) (by rw [hYdef]; linarith)
  have qC : QPLe Y 1 C₁ := qple_of_exp_Y (by linarith) (by rw [hYdef]; linarith)
  have qinv : QPLe Y 1 (1 / δ₀) := qple_of_exp_Y (by positivity) (by rw [hYdef]; linarith)
  have q2 : QPLe Y ⌈(2 : ℝ)⌉₊ 2 := QPLe.const hY 2
  -- padding and separation
  obtain ⟨P, hPa, hPc, hPb⟩ := hpad A hA hc₀
  obtain ⟨P', hP'a, hP'c, hP'b⟩ := hpad A' hA' hc₀
  set H' := max H W₀ ^ 6 with hH'
  have hjl : ((jR : ℕ) : ℤ) ≠ ((lv : ℕ) : ℤ) := by
    intro h; apply h3; exact Fin.ext (by exact_mod_cast h)
  obtain ⟨τ, hτc, cf, φa, φb, φt, size, hexp, hbdd, hsize1, hcs, hcsum, htail, hcomp, -, -⟩ :=
    hsep H' P P' (by omega) (by omega) hPc hP'c ((i : ℕ) : ℤ) ((k : ℕ) : ℤ) ((jR : ℕ) : ℤ)
      ((lv : ℕ) : ℤ) hjl (abs_fin_int_le i) (abs_fin_int_le k) (abs_fin_int_le jR)
      (abs_fin_int_le lv)
  set E₁ := Real.exp (D * (1 + Real.log H') ^ D) with hE₁
  have hE₁0 : 0 < E₁ := Real.exp_pos _
  -- the expansion of the form
  have hexp' : ∀ x t : ℝ, HasSum (fun q => cf q * quadraticChartAtom (φa q) (x + (jR : ℝ) * t) *
      quadraticChartAtom (φb q) (x + (lv : ℝ) * t) * quadraticChartAtom (φt q) t)
      (quadraticChartAtom P (x + (i : ℝ) * t) * quadraticChartAtom P' (x + (k : ℝ) * t)) := by
    intro x t
    have h := hexp x t
    simp only [fin_cast_int_real] at h
    exact h
  have hfi' : f i = quadraticChartAtom P := by rw [hfi]; funext y; rw [hPa]
  have hfk' : f k = quadraticChartAtom P' := by rw [hfk]; funext y; rw [hP'a]
  obtain ⟨hHS, hXb⟩ := localProgressionForm_pair_expansion hr hw h1 h2 h3 h4 h5 h6 (hf jR)
    (hf lv) (by linarith) hR hv cf (fun q => quadraticChartAtom (φa q))
    (fun q => quadraticChartAtom (φb q)) (fun q => quadraticChartAtom (φt q))
    (fun q => quadraticChartAtom_measurable _) (fun q => quadraticChartAtom_measurable _)
    (fun q => quadraticChartAtom_measurable _) (fun q => (hbdd q).1) (fun q => (hbdd q).2.1)
    (fun q => (hbdd q).2.2) hcs hexp' f rfl hfi' hfk' rfl
  -- budgets
  have hW'0 : 0 ≤ W' := localFormUniformConstant_nonneg κ
  have hK'0 : 0 ≤ K' := by
    rw [hK']; unfold kernelFourierConst
    have := kernelDerivBound_nonneg κ 0
    have := kernelDerivBound_nonneg κ 3
    positivity
  have hHm1 : 1 ≤ max H W₀ := le_trans hH1 (le_max_left _ _)
  have qHm : QPLe Y k1 (max H W₀) :=
    qple_max (qH.mono hY (by omega)) ((QPLe.const hY W₀).mono hY (by omega))
  have qH' : QPLe Y k2 H' := qHm.pow hY (by linarith) 6
  have hH'1 : 1 ≤ H' := one_le_pow₀ hHm1
  have qE₁ : QPLe Y k3 E₁ := QPLe.compose hY hH'1 qH'
  have qM : QPLe Y kW (W' * C₁) := (QPLe.const hY W').mul hY (by linarith) qC
  set! T₀ := max 1 (2 * E₁ * (W' * C₁) * (1 / δ₀)) with hT₀
  have qT : QPLe Y k4 T₀ := qple_max (QPLe.one_le hY)
    (((q2.mul hY hE₁0.le qE₁).mul hY (by positivity) qM).mul hY (by positivity) qinv)
  have hT₀1 : 1 ≤ T₀ := le_max_left _ _
  set! H₁ := (E₁ * T₀) ^ 6 with hH₁
  have qH₁ : QPLe Y k5 H₁ := (qE₁.mul hY (by linarith) qT).pow hY (by positivity) 6
  set! δ₃ := δ₀ / (2 * E₁) with hδ₃
  have hδ₃0 : 0 < δ₃ := by positivity
  have hδ₃inv : δ₃⁻¹ = 2 * E₁ * (1 / δ₀) := by rw [hδ₃]; field_simp
  have qδ : QPLe Y kδ δ₃⁻¹ := by
    rw [hδ₃inv]; exact (q2.mul hY hE₁0.le qE₁).mul hY (by positivity) qinv
  -- the shell selection
  have htail' : (∑' q, if T₀ ≤ size q then ‖cf q‖ else 0) * (W' * C₁) ≤ δ₀ / 2 := by
    have ht := htail T₀ hT₀1
    have hT100 : T₀ ≤ T₀ ^ 100 := le_self_pow₀ hT₀1 (by norm_num)
    have hT0 : 0 < T₀ := by linarith
    have hsT : (∑' q, if T₀ ≤ size q then ‖cf q‖ else 0) ≤ E₁ / T₀ :=
      ht.trans (div_le_div_of_nonneg_left hE₁0.le hT0 hT100)
    have hM0 : 0 ≤ W' * C₁ := by positivity
    calc (∑' q, if T₀ ≤ size q then ‖cf q‖ else 0) * (W' * C₁) ≤ E₁ / T₀ * (W' * C₁) :=
          mul_le_mul_of_nonneg_right hsT hM0
      _ ≤ δ₀ / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hT0]
          have : 2 * E₁ * (W' * C₁) * (1 / δ₀) ≤ T₀ := le_max_right _ _
          have e : 2 * E₁ * (W' * C₁) * (1 / δ₀) * δ₀ = 2 * (E₁ * (W' * C₁)) := by
            field_simp
          nlinarith only [hδ₀, this, e]
  obtain ⟨q, hq, hXq⟩ := exists_large_retained_term cf _ size hcs hcsum hE₁0 hXb
    (by positivity) hδ₀.le htail' (by rw [hHS.tsum_eq]; exact hHf)
  -- the retained term
  have hHq : (E₁ * size q) ^ 6 ≤ H₁ :=
    pow_le_pow_left₀ (by have := hsize1 q; positivity)
      (mul_le_mul_of_nonneg_left hq.le hE₁0.le) 6
  have hφt := quadraticChartComplexity_mono (hcomp q).2.2 hHq
  have hφa := quadraticChartComplexity_mono (hcomp q).1 hHq
  set! Λ := max (max H₁ Lζ) (max ((K' + 1) * C₁ * δ₃⁻¹) (2 * C₁ * δ₃⁻¹)) with hΛ
  have hΛ1 : 1 ≤ Λ := le_trans hLζ (le_trans (le_max_right _ _) (le_max_left _ _))
  have qΛ : QPLe Y kΛ Λ := by
    refine qple_max (qple_max (qH₁.mono hY (by omega))
      ((QPLe.const hY Lζ).mono hY (by omega))) (qple_max ?_ ?_)
    · exact (((QPLe.const hY (K' + 1)).mul hY (by linarith) qC).mul hY (by positivity)
        qδ).mono hY (by omega)
    · exact ((q2.mul hY (by linarith) qC).mul hY (by positivity) qδ).mono hY (by omega)
  obtain ⟨α, hmom⟩ := hext (φt q) hφt (hbdd q).2.2 hr hw h3 (hf jR) (hf lv)
    (quadraticChartAtom_measurable _) (quadraticChartAtom_measurable _) (hbdd q).1
    (hbdd q).2.1 hC₁ hR hv hδ₃0 hXq hΛ1
    (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _))
    (by rw [div_eq_mul_inv]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    (by rw [div_eq_mul_inv]; exact le_trans (le_max_right _ _) (le_max_right _ _))
  -- the witness atom
  obtain ⟨Φ, hΦc, hΦb, hΦa⟩ := moment_witness_chart (φa q) hφa (hbdd q).1 hc₁ α
  set Eb := Real.exp (Dk * (1 + 3 * Real.log Λ) ^ Dk) with hEb
  have qEb : QPLe Y k6 Eb :=
    QPLe.of_le (exp_three_log_le hΛ1 Dk) (QPLe.compose (D := D3) hY hΛ1 qΛ)
  have hEb0 : 0 < Eb := Real.exp_pos _
  have qF : QPLe Y k7 (2 * Eb * δ₃⁻¹) := (q2.mul hY hEb0.le qEb).mul hY (by positivity) qδ
  have qH6 : QPLe Y k8 (H₁ ^ 6) := qH₁.pow hY (by positivity) 6
  refine ⟨_, Φ, quadraticChartComplexity_mono hΦc (qH6.mono hY (by omega)), hΦb, ?_⟩
  have hint : ∫ x in a₀..a₀ + r, f jR x * conj (quadraticChartAtom Φ x) =
      ∫ y in Set.Icc a₀ (a₀ + r), f jR y * quadraticChartAtom (φa q) y *
        (Real.fourierChar (α * y) : ℂ) := by
    rw [intervalIntegral_eq_Icc hr]
    congr 1; funext y; rw [hΦa, mul_assoc]
  rw [hint]
  refine le_trans ?_ hmom
  have hF : 2 * Eb * δ₃⁻¹ ≤ Real.exp (Kf * Y ^ Kf) := qF.mono hY (by omega)
  have hFpos : 0 < 2 * Eb * δ₃⁻¹ := by positivity
  calc (Real.exp (Kf * Y ^ Kf))⁻¹ ≤ (2 * Eb * δ₃⁻¹)⁻¹ := inv_anti₀ hFpos hF
    _ = δ₃ / (2 * Eb) := by field_simp

theorem qple_of_quasipolynomial {D : ℝ → ℝ} (hD : QuasipolynomialBound D) :
    ∃ kD : ℕ, ∀ {Y t : ℝ} {K : ℕ}, 1 ≤ Y → 2 ≤ t → QPLe Y K t →
      QPLe Y (kD * (1 + K) ^ kD + K * kD) (D t) ∧ 0 ≤ D t := by
  obtain ⟨C, hC, d, hd, hb⟩ := hD
  refine ⟨max ⌈C⌉₊ d, fun {Y t K} hY ht hq => ⟨?_, (hb t ht).1⟩⟩
  have h1 : 1 ≤ t := by linarith
  refine QPLe.of_le ?_ (QPLe.compose (D := max ⌈C⌉₊ d) hY h1 hq)
  refine (hb t ht).2.trans (Real.exp_le_exp.mpr ?_)
  have hl : 1 ≤ logarithmicSize t := one_le_logarithmicSize ht
  unfold logarithmicSize at hl ⊢
  exact mul_le_mul ((Nat.le_ceil C).trans (by exact_mod_cast le_max_left _ _))
    (pow_le_pow_right₀ hl (le_max_right _ _)) (by positivity) (by positivity)

theorem truncateNorm_eLpNorm_le {μ : Measure ℝ} {p : ENNReal} {g : ℝ → ℂ}
    (hg : Measurable g) (B : ℝ) : eLpNorm (truncateNorm B g) p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono (truncateNorm_measurable hg B).aestronglyMeasurable
    (fun y => norm_truncateNorm_le B g y)

theorem clipExcept_apply_self (B : ℝ) (k : Fin 4) (f : Fin 4 → ℝ → ℂ) :
    clipExcept B k f k = f k := by simp [clipExcept]

theorem clipExcept_apply_ne (B : ℝ) {k j : Fin 4} (h : j ≠ k) (f : Fin 4 → ℝ → ℂ) :
    clipExcept B k f j = truncateNorm B (f j) := by simp [clipExcept, h]

theorem qple_of_le_nat {Y c : ℝ} {k : ℕ} (hY : 1 ≤ Y) (hc : c ≤ k) : QPLe Y k c := by
  unfold QPLe
  have h1 : (k : ℝ) ≤ k * Y ^ k := le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hY)
  linarith [Real.add_one_le_exp ((k : ℝ) * Y ^ k)]

/-- The quasipolynomial budget of blueprint lem:detection, line 1473: the final
complexity is quasipolynomial in `B, C₁, δ⁻¹`, and the clipping height contributes only
a `q`-dependent factor to the logarithm. -/
theorem detection_budget {D : ℝ → ℝ} {kD K₃ : ℕ}
    (hkD : ∀ {Y t : ℝ} {K : ℕ}, 1 ≤ Y → 2 ≤ t → QPLe Y K t →
      QPLe Y (kD * (1 + K) ^ kD + K * kD) (D t) ∧ 0 ≤ D t)
    {Cv W' q C₁ δ X B dinv1 t₁ M₁ dinv2 t₂ M₂ dinv3 Hc δ₀ cB : ℝ}
    {kδ1 kc kτ1 kD1 kδ2 kτ2 kD2 kδ3 kδ0 kH kP kE : ℕ}
    (hkδ1 : kδ1 = 2 + 1) (hkc : kc = ⌈4 * (Cv + 1)⌉₊)
    (hkτ1 : kτ1 = 4 + (kc + 1 + (3 * 1 + 1) + kδ1))
    (hkD1 : kD1 = kD * (1 + kτ1) ^ kD + kτ1 * kD) (hkδ2 : kδ2 = 2 + 1 + kD1 + kδ1)
    (hkτ2 : kτ2 = 4 + (kc + 1 + (3 * 1 + 1) + kδ2))
    (hkD2 : kD2 = kD * (1 + kτ2) ^ kD + kτ2 * kD) (hkδ3 : kδ3 = 2 + 1 + kD2 + kδ2)
    (hkδ0 : kδ0 = 2 + kδ3) (hkH : kH = kD1 + kD2) (hkP : kP = kH + 1 + kδ0)
    (hkE : kE = K₃ * (1 + kP) ^ K₃ + kP * K₃)
    (hW'0 : 0 ≤ W') (hq : 2 < q) (hC₁ : 1 ≤ C₁) (hδ : 0 < δ)
    (hδ2 : δ < 1 / 2)
    (hX : X = 12 * (W' + 1) * C₁ * (1 / δ)) (hX1 : 1 ≤ X)
    (hB : B = max 2 (X ^ (q / (q - 2))))
    (hdinv1 : dinv1 = 4 / 3 * (1 / δ))
    (ht₁ : t₁ = max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dinv1)) (hM₁ : M₁ = max 1 (D t₁))
    (hdinv2 : dinv2 = 2 * B * M₁ * dinv1)
    (ht₂ : t₂ = max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dinv2)) (hM₂ : M₂ = max 1 (D t₂))
    (hdinv3 : dinv3 = 2 * B * M₂ * dinv2) (hHc : Hc = max (D t₁) (D t₂)) (hHc1 : 1 ≤ Hc)
    (hδ₀ : δ₀ = (max 2 dinv3)⁻¹)
    (hcB : cB = Real.log 2 + q / (q - 2) * (1 + Real.log (12 * (W' + 1)))) :
    Real.exp (K₃ * (1 + Real.log Hc + Real.log C₁ + Real.log (1 / δ₀)) ^ K₃) ≤
      Real.exp (kE * (1 + cB) ^ kE * (1 + Real.log C₁ + Real.log (1 / δ)) ^ kE) := by
  have hC0 : 0 ≤ C₁ := by linarith
  have hB1 : 1 ≤ B := by rw [hB]; exact le_trans (by norm_num) (le_max_left _ _)
  have hB0 : 0 < B := by linarith
  have hdinv10 : 0 < dinv1 := by rw [hdinv1]; positivity
  have hM₁1 : 1 ≤ M₁ := by rw [hM₁]; exact le_max_left _ _
  have hM₂1 : 1 ≤ M₂ := by rw [hM₂]; exact le_max_left _ _
  have hdinv20 : 0 < dinv2 := by rw [hdinv2]; positivity
  have hdinv30 : 0 < dinv3 := by rw [hdinv3]; positivity
  have hmax0 : 0 < max 2 dinv3 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; exact inv_pos.mpr hmax0
  have hδ₀1 : δ₀ ≤ 1 := by
    rw [hδ₀]; exact inv_le_one_of_one_le₀ (le_trans (by norm_num) (le_max_left _ _))
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = 1 + Real.log B + Real.log C₁ + Real.log (1 / δ) :=
    ⟨_, rfl⟩
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hlC : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁
  have hlδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hZ : 1 ≤ Z := by rw [hZdef]; linarith
  have qB : QPLe Z 1 B := qple_of_exp_Y hB0 (by rw [hZdef]; linarith)
  have qC : QPLe Z 1 C₁ := qple_of_exp_Y (by linarith) (by rw [hZdef]; linarith)
  have qδ : QPLe Z 1 (1 / δ) := qple_of_exp_Y (by positivity) (by rw [hZdef]; linarith)
  have qd1 : QPLe Z kδ1 dinv1 := by
   rw [hdinv1, hkδ1]
   exact (qple_of_le_nat (k := 2) hZ (by norm_num)).mul hZ (by positivity) qδ
  have qB3 : QPLe Z (3 * 1 + 1) (B ^ 3) := qB.pow hZ hB0.le 3
  have qc : QPLe Z kc (4 * (Cv + 1)) := by rw [hkc]; exact QPLe.const hZ _
  have q4 : ∀ {k : ℕ}, 4 ≤ k → QPLe Z k 4 := fun hk =>
    qple_of_le_nat hZ (by exact_mod_cast hk)
  have q2' : ∀ {k : ℕ}, 2 ≤ k → QPLe Z k 2 := fun hk =>
    qple_of_le_nat hZ (by exact_mod_cast hk)
  have qt1 : QPLe Z kτ1 t₁ := by
   rw [ht₁]
   exact qple_max (q4 (by omega))
    ((((qc.mul hZ hC0 qC).mul hZ (by positivity) qB3).mul hZ hdinv10.le qd1).mono hZ
      (by omega))
  have ht₁2 : 2 ≤ t₁ := by rw [ht₁]; exact le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨qD1, hD10⟩ := hkD hZ ht₁2 qt1
  have qM1 : QPLe Z kD1 M₁ := by rw [hM₁, hkD1]; exact qple_max (QPLe.one_le hZ) qD1
  have qd2 : QPLe Z kδ2 dinv2 := by
   rw [hdinv2, hkδ2]
   exact ((((q2' (le_refl 2)).mul hZ hB0.le qB).mul hZ (by positivity) qM1).mul hZ hdinv10.le qd1)
  have qt2 : QPLe Z kτ2 t₂ := by
   rw [ht₂]
   exact qple_max (q4 (by omega))
    ((((qc.mul hZ hC0 qC).mul hZ (by positivity) qB3).mul hZ hdinv20.le qd2).mono hZ
      (by omega))
  have ht₂2 : 2 ≤ t₂ := by rw [ht₂]; exact le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨qD2, hD20⟩ := hkD hZ ht₂2 qt2
  have qM2 : QPLe Z kD2 M₂ := by rw [hM₂, hkD2]; exact qple_max (QPLe.one_le hZ) qD2
  have qd3 : QPLe Z kδ3 dinv3 := by
   rw [hdinv3, hkδ3]
   exact ((((q2' (le_refl 2)).mul hZ hB0.le qB).mul hZ (by positivity) qM2).mul hZ hdinv20.le qd2)
  have qinv0 : QPLe Z kδ0 (1 / δ₀) := by
    rw [hδ₀, one_div, inv_inv]
    exact qple_max (q2' (by omega)) (qd3.mono hZ (by omega))
  have qHc : QPLe Z kH Hc := by
    rw [hHc]; exact qple_max (qD1.mono hZ (by omega)) (qD2.mono hZ (by omega))
  have qP : QPLe Z kP (Hc * C₁ * (1 / δ₀)) := by
   rw [hkP]
   exact (qHc.mul hZ hC0 qC).mul hZ (by positivity) qinv0
  have hP1 : 1 ≤ Hc * C₁ * (1 / δ₀) := by
    have : 1 ≤ 1 / δ₀ := by rw [le_div_iff₀ hδ₀0]; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hHc1 hC₁) this
  have qE := QPLe.compose (D := K₃) hZ hP1 qP
  rw [← hkE] at qE
  have hY3 : 1 + Real.log Hc + Real.log C₁ + Real.log (1 / δ₀) =
      1 + Real.log (Hc * C₁ * (1 / δ₀)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity)]
    ring
  -- conversion to `1 + log C₁ + log δ⁻¹`
  obtain ⟨Y', hY'⟩ : ∃ Y' : ℝ, Y' = 1 + Real.log C₁ + Real.log (1 / δ) := ⟨_, rfl⟩
  have hY'1 : 1 ≤ Y' := by rw [hY']; linarith
  have hq2 : 0 < q - 2 := by linarith
  have he0 : 0 < q / (q - 2) := div_pos (by linarith) hq2
  have hl0 : 0 ≤ Real.log (12 * (W' + 1)) := Real.log_nonneg (by linarith)
  have hlogX : Real.log X = Real.log (12 * (W' + 1)) + Real.log C₁ + Real.log (1 / δ) := by
    rw [hX, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogB : Real.log B ≤ cB * Y' := by
    have h1' : Real.log B ≤ Real.log 2 + q / (q - 2) * Real.log X := by
      rcases le_total 2 (X ^ (q / (q - 2))) with h | h
      · rw [hB, max_eq_right h, Real.log_rpow (by linarith)]
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      · rw [hB, max_eq_left h]
        have : 0 ≤ q / (q - 2) * Real.log X := mul_nonneg he0.le hlX0
        linarith
    have h2' : Real.log X ≤ (1 + Real.log (12 * (W' + 1))) * Y' := by
      have hm : Real.log (12 * (W' + 1)) * 1 ≤ Real.log (12 * (W' + 1)) * Y' :=
        mul_le_mul_of_nonneg_left hY'1 hl0
      rw [hlogX, add_mul, one_mul]; linarith [hY']
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc Real.log B ≤ Real.log 2 + q / (q - 2) * Real.log X := h1'
      _ ≤ Real.log 2 * Y' + q / (q - 2) * ((1 + Real.log (12 * (W' + 1))) * Y') := by
          exact add_le_add (le_mul_of_one_le_right hl2 hY'1)
            (mul_le_mul_of_nonneg_left h2' he0.le)
      _ = cB * Y' := by rw [hcB]; ring
  have hZY : Z ≤ (1 + cB) * Y' := by rw [add_mul, one_mul]; linarith [hZdef, hY', hlogB]
  have hfin : Real.exp (kE * Z ^ kE) ≤ Real.exp (kE * (1 + cB) ^ kE * Y' ^ kE) := by
    apply Real.exp_le_exp.mpr
    have := pow_le_pow_left₀ (by linarith) hZY kE
    rw [mul_pow] at this
    have hk0 : (0 : ℝ) ≤ kE := Nat.cast_nonneg _
    calc (kE : ℝ) * Z ^ kE ≤ kE * ((1 + cB) ^ kE * Y' ^ kE) := mul_le_mul_of_nonneg_left this hk0
      _ = kE * (1 + cB) ^ kE * Y' ^ kE := by ring
  have hE : Real.exp (K₃ * (1 + Real.log Hc + Real.log C₁ + Real.log (1 / δ₀)) ^ K₃) ≤
      Real.exp (kE * (1 + cB) ^ kE * Y' ^ kE) := by
    rw [hY3]; exact qE.trans hfin
  rw [hY'] at hE
  exact hE

/-- Blueprint lem:detection (Declaration detection, line 1475,
`THT.LocalForm.detectResidual`): if `‖R‖_{2,I} ≤ C₁`, `‖h‖_{q,I} ≤ 1`, `‖u‖_{2,I}, ‖v‖_{2,I} ≤ 1`
and `|H_I(R,h,u,v)| > δ` (any four distinct slots), then `R` has a normalized moment of
magnitude at least `D⁻¹` against a bounded atom of complexity `D`, where
`D = exp(C_q (1 + log C₁ + log δ⁻¹)^C)` with an absolute degree `C`. -/
theorem detectResidual (κ : LocalKernelClass) :
    ∃ (c₂ C : ℕ), 1 ≤ c₂ ∧ 1 ≤ C ∧ ∀ q : ℝ, 2 < q → ∃ Cq : ℝ, 0 < Cq ∧
    ∀ {a₀ r C₁ δ : ℝ}, 0 < r → ∀ {w : ℝ × ℝ → ℂ}, IsAdmissibleLocalKernel κ a₀ r w →
    ∀ (f : Fin 4 → ℝ → ℂ), (∀ j, Measurable (f j)) →
    ∀ {jR ih ku lv : Fin 4}, jR ≠ ih → jR ≠ ku → jR ≠ lv → ih ≠ ku → ih ≠ lv → ku ≠ lv →
    1 ≤ C₁ → 0 < δ → δ < 1 / 2 →
    eLpNorm (f jR) 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal C₁ →
    eLpNorm (f ih) (ENNReal.ofReal q) (normalizedIntervalMeasure a₀ r) ≤ 1 →
    eLpNorm (f ku) 2 (normalizedIntervalMeasure a₀ r) ≤ 1 →
    eLpNorm (f lv) 2 (normalizedIntervalMeasure a₀ r) ≤ 1 →
    δ < ‖localProgressionForm r w f‖ →
    ∃ (d : ℕ) (Φ : QuadraticChartData d),
      QuadraticChartComplexity c₂
        (Real.exp (Cq * (1 + Real.log C₁ + Real.log (1 / δ)) ^ C)) Φ ∧
      IsBoundedQuadraticChart Φ ∧
      (Real.exp (Cq * (1 + Real.log C₁ + Real.log (1 / δ)) ^ C))⁻¹ ≤
        r⁻¹ * ‖∫ x in a₀..a₀ + r, f jR x * conj (quadraticChartAtom Φ x)‖ := by
  obtain ⟨c₀, D, hc₀, hD, hslot⟩ := detection_structured_slot κ
  obtain ⟨kD, hkD⟩ := qple_of_quasipolynomial hD
  obtain ⟨c₂, K₃, hc₂, hK₃, hpair⟩ := detection_atom_pair κ c₀ hc₀
  set Cv := vonNeumannConst κ with hCv
  set W' := localFormUniformConstant κ with hW'
  -- budget exponents in `Z = 1 + log B + log C₁ + log δ⁻¹`
  set kδ1 : ℕ := 2 + 1 with hkδ1
  set kc : ℕ := ⌈4 * (Cv + 1)⌉₊ with hkc
  set kτ1 : ℕ := 4 + (kc + 1 + (3 * 1 + 1) + kδ1) with hkτ1
  set kD1 : ℕ := kD * (1 + kτ1) ^ kD + kτ1 * kD with hkD1
  set! kδ2 : ℕ := 2 + 1 + kD1 + kδ1 with hkδ2
  set! kτ2 : ℕ := 4 + (kc + 1 + (3 * 1 + 1) + kδ2) with hkτ2
  set! kD2 : ℕ := kD * (1 + kτ2) ^ kD + kτ2 * kD with hkD2
  set! kδ3 : ℕ := 2 + 1 + kD2 + kδ2 with hkδ3
  set! kδ0 : ℕ := 2 + kδ3 with hkδ0
  set! kH : ℕ := kD1 + kD2 with hkH
  set! kP : ℕ := kH + 1 + kδ0 with hkP
  set! kE : ℕ := K₃ * (1 + kP) ^ K₃ + kP * K₃ with hkE
  have hkE1 : 1 ≤ kE := le_trans (le_trans hK₃ (Nat.le_mul_of_pos_right _ (by positivity)))
    (Nat.le_add_right _ _)
  refine ⟨c₂, kE, hc₂, hkE1, ?_⟩
  intro q hq
  set! cB := Real.log 2 + q / (q - 2) * (1 + Real.log (12 * (W' + 1))) with hcB
  have hW'0 : 0 ≤ W' := localFormUniformConstant_nonneg κ
  have hcB0 : 0 ≤ cB := by
    have : 0 ≤ Real.log (12 * (W' + 1)) := Real.log_nonneg (by linarith)
    have : 0 < q - 2 := by linarith
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨kE * (1 + cB) ^ kE, by positivity, ?_⟩
  intro a₀ r C₁ δ hr w hw f hf jR ih ku lv h1 h2 h3 h4 h5 h6 hC₁ hδ hδ2 hR hh hu hv hHf
  set ν := normalizedIntervalMeasure a₀ r with hν
  have : IsProbabilityMeasure ν := normalizedIntervalMeasure_probability a₀ hr
  have hC0 : 0 ≤ C₁ := by linarith
  have hCv0 : 0 ≤ Cv := vonNeumannConst_nonneg κ
  -- clipping
  set! X := 12 * (W' + 1) * C₁ * (1 / δ) with hX
  have hX1 : 1 ≤ X := by
    rw [hX]
    have h2 : 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have hA : 1 ≤ 12 * (W' + 1) := by linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hC₁) (by linarith)
  set! B := max 2 (X ^ (q / (q - 2))) with hB
  have hB1 : 1 ≤ B := le_trans (by norm_num) (le_max_left _ _)
  have hB0 : 0 < B := by linarith
  have hclipδ : 3 * (W' * (C₁ * B ^ (-(q - 2) / q) * 1 * 1)) ≤ δ / 4 := by
    have hq2 : 0 < q - 2 := by linarith
    have hXe : (X ^ (q / (q - 2))) ^ (-(q - 2) / q) = X⁻¹ := by
      rw [← Real.rpow_mul (by linarith), show q / (q - 2) * (-(q - 2) / q) = -1 by
        field_simp, Real.rpow_neg_one]
    have hBe : B ^ (-(q - 2) / q) ≤ X⁻¹ := by
      rw [← hXe]
      apply Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right _ _)
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have h0 : 0 ≤ B ^ (-(q - 2) / q) := by positivity
    calc 3 * (W' * (C₁ * B ^ (-(q - 2) / q) * 1 * 1)) ≤ 3 * (W' * (C₁ * X⁻¹)) := by
          simp only [mul_one]; gcongr
      _ = δ / 4 * (W' / (W' + 1)) := by
          rw [hX]; field_simp; ring
      _ ≤ δ / 4 * 1 := by
          gcongr; rw [div_le_one (by linarith)]; linarith
      _ = δ / 4 := mul_one _
  have hcl := detection_clipping hr hw f hf h1 h2 h3 h4 h5 h6 hq hC0 hB1 hR hh hu hv
  set f' := clipExcept B jR f with hf'
  set! δ' := 3 * δ / 4 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hHf' : δ' < ‖localProgressionForm r w f'‖ := by
    rw [hδ']; linarith
  have hf'm : ∀ j, Measurable (f' j) := by
    intro j; by_cases hj : j = jR
    · subst hj; rw [hf', clipExcept_apply_self]; exact hf _
    · rw [hf', clipExcept_apply_ne B hj]; exact truncateNorm_measurable (hf j) B
  have hf'b : ∀ j, j ≠ jR → ∀ x, ‖f' j x‖ ≤ B := by
    intro j hj x; rw [hf', clipExcept_apply_ne B hj]
    exact norm_truncateNorm_le_level hB0.le _ _
  have hf'R : f' jR = f jR := by rw [hf', clipExcept_apply_self]
  have hf'v : eLpNorm (f' lv) 2 ν ≤ 1 := by
    rw [hf', clipExcept_apply_ne B h3.symm]; exact (truncateNorm_eLpNorm_le (hf lv) B).trans hv
  -- the accuracy of a decomposition step
  have hτfact : ∀ {δx dx : ℝ}, 0 < dx → δx * dx = 1 →
      0 < 1 / max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dx) ∧
      1 / max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dx) < 1 / 2 ∧
      4 * (Cv * C₁ * B ^ 3 * (1 / max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dx))) ≤ δx := by
    intro δx dx hdx hδx
    set t := max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dx) with ht
    have ht4 : 4 ≤ t := le_max_left _ _
    have ht0 : 0 < t := by linarith
    refine ⟨by positivity, by rw [div_lt_div_iff₀ ht0 (by norm_num)]; linarith, ?_⟩
    have hδe : δx = 1 / dx := by field_simp; linarith only [hδx]
    have hle : 4 * (Cv + 1) * C₁ * B ^ 3 * dx ≤ t := le_max_right _ _
    rw [hδe]
    have hB3 : 0 ≤ B ^ 3 := by positivity
    calc 4 * (Cv * C₁ * B ^ 3 * (1 / t)) ≤ 4 * ((Cv + 1) * C₁ * B ^ 3 * (1 / t)) := by
          gcongr; linarith
      _ = (4 * (Cv + 1) * C₁ * B ^ 3 * dx) / t / dx := by field_simp
      _ ≤ 1 / dx := by
          gcongr; rw [div_le_one ht0]; exact hle
  -- the first decomposition (slot `ih`)
  set! dinv1 := 4 / 3 * (1 / δ) with hdinv1
  have hdinv10 : 0 < dinv1 := by positivity
  have hd1 : δ' * dinv1 = 1 := by rw [hδ', hdinv1]; field_simp
  set! t₁ := max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dinv1) with ht₁
  obtain ⟨hτ₁0, hτ₁2, hτ₁δ⟩ := hτfact hdinv10 hd1
  obtain ⟨d₁, A₁, hA₁c, hA₁b, hA₁⟩ := hslot hr hw f' hf'm (k := ih) (jR := jR) (b := ku)
    (c := lv) h1.symm h4 h5 h2 h3 h6 hC0 hB1 hτ₁0 hτ₁2 (by rw [hf'R]; exact hR)
    (hf'b ih h1.symm) (hf'b ku h2.symm) (hf'b lv h3.symm) hτ₁δ hHf'
  rw [one_div_one_div] at hA₁c hA₁
  set M₁ := max 1 (D t₁) with hM₁
  set δ2 := δ' / (2 * B * M₁) with hδ2def
  set f2 := Function.update f' ih (quadraticChartAtom A₁) with hf2
  have hf2m : ∀ j, Measurable (f2 j) :=
    measurable_update_slot hf'm ih (quadraticChartAtom_measurable A₁)
  -- the second decomposition (slot `ku`)
  set! dinv2 := 2 * B * M₁ * dinv1 with hdinv2
  have hM₁1 : 1 ≤ M₁ := le_max_left _ _
  have hdinv20 : 0 < dinv2 := by positivity
  have hd2 : δ2 * dinv2 = 1 := by
    rw [hδ2def, hdinv2]; field_simp; linarith only [hd1]
  set! t₂ := max 4 (4 * (Cv + 1) * C₁ * B ^ 3 * dinv2) with ht₂
  obtain ⟨hτ₂0, hτ₂2, hτ₂δ⟩ := hτfact hdinv20 hd2
  obtain ⟨d₂, A₂, hA₂c, hA₂b, hA₂⟩ := hslot hr hw f2 hf2m (k := ku) (jR := jR) (b := ih)
    (c := lv) h2.symm h4.symm h6 h1 h3 h5 hC0 hB1 hτ₂0 hτ₂2
    (by rw [hf2, Function.update_of_ne h1, hf'R]; exact hR)
    (by rw [hf2, Function.update_of_ne h4.symm]; exact hf'b ku h2.symm)
    (by rw [hf2, Function.update_self]; exact fun x => (hA₁b x).trans hB1)
    (by rw [hf2, Function.update_of_ne h5.symm]; exact hf'b lv h3.symm) hτ₂δ hA₁
  rw [one_div_one_div] at hA₂c hA₂
  set M₂ := max 1 (D t₂) with hM₂
  set δ3 := δ2 / (2 * B * M₂) with hδ3
  set f3 := Function.update f2 ku (quadraticChartAtom A₂) with hf3
  have hf3m : ∀ j, Measurable (f3 j) :=
    measurable_update_slot hf2m ku (quadraticChartAtom_measurable A₂)
  set! dinv3 := 2 * B * M₂ * dinv2 with hdinv3
  have hM₂1 : 1 ≤ M₂ := le_max_left _ _
  have hdinv30 : 0 < dinv3 := by positivity
  have hd3 : δ3 * dinv3 = 1 := by
    rw [hδ3, hdinv3]; field_simp; linarith only [hd2]
  -- the atom pair
  set! Hc := max (D t₁) (D t₂) with hHc
  set! δ₀ := (max 2 dinv3)⁻¹ with hδ₀
  have hmax0 : 0 < max 2 dinv3 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hδ₀0 : 0 < δ₀ := inv_pos.mpr hmax0
  have hδ₀1 : δ₀ ≤ 1 := by
    rw [hδ₀]; exact inv_le_one_of_one_le₀ (le_trans (by norm_num) (le_max_left _ _))
  have hδ₀δ : δ₀ ≤ δ3 := by
    rw [hδ₀]
    have : δ3 = dinv3⁻¹ := by field_simp; linarith only [hd3]
    rw [this]; exact inv_anti₀ hdinv30 (le_max_right _ _)
  have hf3i : f3 ih = quadraticChartAtom A₁ := by
    rw [hf3, Function.update_of_ne h4, hf2, Function.update_self]
  have hf3k : f3 ku = quadraticChartAtom A₂ := by rw [hf3, Function.update_self]
  have hf3R : f3 jR = f jR := by
    rw [hf3, Function.update_of_ne h2, hf2, Function.update_of_ne h1, hf'R]
  have hf3v : f3 lv = f' lv := by
    rw [hf3, Function.update_of_ne h6.symm, hf2, Function.update_of_ne h5.symm]
  obtain ⟨d'', Φ, hΦc, hΦb, hΦm⟩ := hpair A₁ A₂
    (quadraticChartComplexity_mono hA₁c (le_max_left _ _))
    (quadraticChartComplexity_mono hA₂c (le_max_right _ _)) hA₁b hA₂b hr hw f3 hf3m
    h1 h2 h3 h4 h5 h6 hf3i hf3k hC₁ (by rw [hf3R]; exact hR)
    (by rw [hf3v]; exact hf'v) hδ₀0 hδ₀1 (lt_of_le_of_lt hδ₀δ hA₂)
  rw [hf3R] at hΦm
  -- the budget in `Z`
  have hHc1 : 1 ≤ Hc := by
    have := hA₁c.lower
    linarith only [Real.add_one_le_exp (2 : ℝ), le_max_left (D t₁) (D t₂), this]
  have hE := detection_budget hkD hkδ1 hkc hkτ1 hkD1 hkδ2 hkτ2 hkD2 hkδ3 hkδ0 hkH hkP hkE
    hW'0 hq hC₁ hδ hδ2 hX hX1 hB hdinv1 ht₁ hM₁ hdinv2 ht₂ hM₂ hdinv3 hHc hHc1 hδ₀ hcB
  refine ⟨d'', Φ, quadraticChartComplexity_mono hΦc hE, hΦb, ?_⟩
  exact (inv_anti₀ (Real.exp_pos _) hE).trans hΦm

end TrilinearHT.Auto

end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoQuadVarSum
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoLinear
public import LeanPool.KLS.LevyStochCalc.Brownian.DriftIncrement

/-!
# The polarised quadratic variation

For two integrands against the *same* Brownian motion, the product of the increments of their
Itô integrals, compensated by the window integral of the product of the integrands, is
conditionally centred at the left endpoint. The identity `2xy = (x+y)² − x² − y²` reduces this
to the compensated square increments of `H₁ + H₂`, of `H₁` and of `H₂`, using additivity of the
Itô integral in the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.polarQuadVarIncrement` — the compensated product of increments.
* `LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae` — the polarisation identity.
* `LevyStochCalc.Brownian.Ito.condExp_polarQuadVarIncrement` — it is conditionally centred at
  the left endpoint.
* `LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le` — its second moment.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Polarised

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The product of the increments of the Itô integrals of `H₁` and `H₂` against the same Brownian
motion, compensated by the window integral of `H₁·H₂`. -/
noncomputable def polarQuadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ a ω)
    * (stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ a ω)
    - ((∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume)

include hℱ in
/-- Additivity of the Itô integral in the integrand, at every nonnegative time. -/
theorem stochasticIntegralBrownian_add_ae_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ
        (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₁ hm₁ hp₁ hq₁ (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₂ hm₂ hp₂ hq₂ (le_refl (0 : ℝ))]
      with ω e0 e1 e2
    rw [e0, e1, e2, Pi.zero_apply, add_zero]
  · exact stochasticIntegralBrownian_add W ℱ hℱ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hma hpa hqa ht'

section Bounds

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)

include hC0 hCH₁ hCH₂ hm₁ hm₂ in
/-- The compensator of the sum expands by the binomial identity. -/
theorem compensator_add_sq_eq {t : ℝ} (ω : Ω) :
    ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = (∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u) ^ 2 ∂volume)
        + 2 * (∫ u in Set.Icc (0 : ℝ) t, H₁ ω u * H₂ ω u ∂volume)
        + ∫ u in Set.Icc (0 : ℝ) t, (H₂ ω u) ^ 2 ∂volume := by
  have hfin : volume (Set.Icc (0 : ℝ) t) ≠ ⊤ := (measure_Icc_lt_top).ne
  have hm₁' : Measurable (H₁ ω) := Measurable.of_uncurry_left hm₁
  have hm₂' : Measurable (H₂ ω) := Measurable.of_uncurry_left hm₂
  have hsq : ∀ x : ℝ, |x| ≤ C → x ^ 2 ≤ C ^ 2 := by
    intro x hx
    nlinarith [abs_nonneg x, sq_abs x]
  have hi₁ : IntegrableOn (fun u => (H₁ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_of_bounded_of_measurable (hm₁'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₁ ω u)) hfin
  have hi₂ : IntegrableOn (fun u => (H₂ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_of_bounded_of_measurable (hm₂'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₂ ω u)) hfin
  have hi₁₂ : IntegrableOn (fun u => 2 * (H₁ ω u * H₂ ω u)) (Set.Icc (0 : ℝ) t) volume := by
    refine integrableOn_of_bounded_of_measurable (B := 2 * C ^ 2)
      ((measurable_const).mul (hm₁'.mul hm₂')) (fun u => ?_) hfin
    change |2 * (H₁ ω u * H₂ ω u)| ≤ 2 * C ^ 2
    have habs : |2 * (H₁ ω u * H₂ ω u)| = 2 * (|H₁ ω u| * |H₂ ω u|) := by
      rw [abs_mul, abs_mul, abs_two]
    rw [habs]
    nlinarith [hCH₁ ω u, hCH₂ ω u, abs_nonneg (H₁ ω u), abs_nonneg (H₂ ω u)]
  have hexp : ∀ u : ℝ, (H₁ ω u + H₂ ω u) ^ 2
      = (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2 := fun u => by ring
  have hcongr : ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = ∫ u in Set.Icc (0 : ℝ) t,
          ((H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2) ∂volume :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => hexp u
  have hiSum : IntegrableOn (fun u => (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u))
      (Set.Icc (0 : ℝ) t) volume := hi₁.add hi₁₂
  rw [hcongr, MeasureTheory.integral_add hiSum hi₂,
    MeasureTheory.integral_add hi₁ hi₁₂, MeasureTheory.integral_const_mul]

include hℱ hC0 hCH₁ hCH₂ in
/-- **Polarisation.** Twice the compensated product is the compensated square increment of
`H₁ + H₂` less those of `H₁` and of `H₂`. -/
theorem smul_two_polarQuadVarIncrement_ae {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (2 : ℝ) • polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b
      =ᵐ[P] fun ω =>
        quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
          - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
          - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω := by
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  filter_upwards [stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂
      hq₁ hq₂ hma hpa hqa hb,
    stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa ha] with ω eb ea
  simp only [Pi.smul_apply, smul_eq_mul, polarQuadVarIncrement, quadVarIncrement]
  rw [eb, ea, compensator_add_sq_eq H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω,
    compensator_add_sq_eq H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω]
  ring

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- The compensated product lies in `L²`. -/
theorem memLp_two_polarQuadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) 2 P := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have mAdd := memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have m₁ := memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have m₂ := memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have hZ : MemLp (fun ω =>
      quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) 2 P := (mAdd.sub m₁).sub m₂
  have hpol := smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hae : (fun ω => (1 / 2 : ℝ) *
      (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω))
      =ᵐ[P] polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b := by
    filter_upwards [hpol] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω
    linarith
  exact (hZ.const_mul (1 / 2 : ℝ)).ae_eq hae

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- **The compensated product is conditionally centred at the left endpoint.** -/
theorem condExp_polarQuadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b | ℱ.rightCont a]
      =ᵐ[P] 0 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have iAdd := (memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab).integrable (by norm_num)
  have i₁ := (memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab).integrable
    (by norm_num)
  have i₂ := (memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab).integrable
    (by norm_num)
  have cAdd := condExp_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa ha hab.le
  have c₁ := condExp_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ ha hab.le
  have c₂ := condExp_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ ha hab.le
  have e1 := MeasureTheory.condExp_sub (iAdd.sub i₁) i₂ (ℱ.rightCont a)
  have e2 := MeasureTheory.condExp_sub iAdd i₁ (ℱ.rightCont a)
  have hcond0 : P[quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b
        - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b | ℱ.rightCont a] =ᵐ[P] 0 := by
    filter_upwards [e1, e2, cAdd, c₁, c₂] with ω h1 h2 hA hh1 hh2
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hA, hh1, hh2, Pi.zero_apply]
    ring
  have hpol := smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hkey := (MeasureTheory.condExp_congr_ae hpol).trans hcond0
  have hsm := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (2 : ℝ)
    (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b)
  filter_upwards [hkey, hsm] with ω h1 h2
  rw [h2, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Pi.zero_apply]
  linarith

include hℱ in
/-- The compensated product across a cell is measurable for the σ-algebra at the right
endpoint. -/
theorem stronglyMeasurable_polarQuadVarIncrement {a b : ℝ} (hab : a ≤ b) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) := by
  have hM₁ := martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁
  have hM₂ := martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂
  have h1b := hM₁.1 b
  have h1a := (hM₁.1 a).mono (ℱ.rightCont.mono hab)
  have h2b := hM₂.1 b
  have h2a := (hM₂.1 a).mono (ℱ.rightCont.mono hab)
  have hcb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume) :=
    (((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont b))
  have hca : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume) :=
    ((((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont a)).mono (ℱ.rightCont.mono hab))
  exact ((h1b.sub h1a).mul (h2b.sub h2a)).sub (hcb.sub hca)

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- **Second moment of the compensated product.** -/
theorem integral_sq_polarQuadVarIncrement_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2) P
      ∧ ∫ ω, (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
        ≤ 3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4) * (b - a) ^ 2 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have mAdd := memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have m₁ := memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have m₂ := memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have lAdd := integral_sq_quadVarIncrement_le W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have l₁ := integral_sq_quadVarIncrement_le W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have l₂ := integral_sq_quadVarIncrement_le W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have hmp := memLp_two_polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab
  have iA : Integrable (fun ω =>
      (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2) P :=
    mAdd.integrable_sq
  have i₁ : Integrable (fun ω => (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2) P :=
    m₁.integrable_sq
  have i₂ : Integrable (fun ω => (quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) P :=
    m₂.integrable_sq
  have iS₁ : Integrable (fun ω =>
      (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2) P := iA.add i₁
  have iS : Integrable (fun ω =>
      (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) P := iS₁.add i₂
  have hdom : Integrable (fun ω => 3 / 4 *
      ((quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2)) P := iS.const_mul _
  have hpol := smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hpt : (fun ω =>
      (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2)
      ≤ᵐ[P] fun ω => 3 / 4 *
        ((quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
          + (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
          + (quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) := by
    filter_upwards [hpol] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω
    have hpe : polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω
        = (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
            - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
            - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) / 2 := by linarith
    rw [hpe]
    nlinarith [sq_nonneg (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        + quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω),
      sq_nonneg (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        + quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω),
      sq_nonneg (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω)]
  have hsplit : ∫ ω,
      ((quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) ∂P
      = (∫ ω, (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2 ∂P)
        + (∫ ω, (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2 ∂P)
        + ∫ ω, (quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2 ∂P := by
    rw [MeasureTheory.integral_add iS₁ i₂, MeasureTheory.integral_add iA i₁]
  refine ⟨hmp.integrable_sq, ?_⟩
  have hstep : ∫ ω,
      (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
      ≤ 3 / 4 * ((∫ ω,
          (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2 ∂P)
        + (∫ ω, (quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2 ∂P)
        + ∫ ω, (quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2 ∂P) := by
    have := MeasureTheory.integral_mono_ae hmp.integrable_sq hdom hpt
    rwa [MeasureTheory.integral_const_mul, hsplit] at this
  refine hstep.trans ?_
  have hC4 : (0 : ℝ) ≤ (2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4 := by
    have hcg : (0 : ℝ) ≤ gaussianFourthMoment := gaussianFourthMoment_nonneg
    positivity
  have hba2 : (0 : ℝ) ≤ (b - a) ^ 2 := sq_nonneg _
  nlinarith [lAdd, l₁, l₂, mul_nonneg hC4 hba2]

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- **Second moment of a weighted sum of compensated products.** The compensated products are
martingale differences, so the weighted sum's second moment is controlled by the sum of the
squared cell lengths. -/
theorem integral_sq_weighted_polarQuadVarSum_le
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ)
    (hg : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (t k)) (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (N : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range N, g i ω
        * polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
        * ∑ i ∈ Finset.range N, (t (i + 1) - t i) ^ 2 := by
  have htmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => h0.trans (htmono.monotone (Nat.zero_le k))
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => ℱ.rightCont (t k) with h𝒢
  have h𝒢le : ∀ k, 𝒢 k ≤ ‹MeasurableSpace Ω› := fun k => ℱ.rightCont.le (t k)
  have h𝒢mono : Monotone 𝒢 := fun p q hpq => ℱ.rightCont.mono (htmono.monotone hpq)
  set Y : ℕ → Ω → ℝ := fun k ω =>
    g k ω * polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1)) ω
    with hY
  have hζmem : ∀ k, MemLp
      (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1))) 2 P :=
    fun k => memLp_two_polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa hC0 hCH₁ hCH₂ (ht0 k) (ht k)
  have hgmeas : ∀ k, Measurable (g k) := fun k => ((hg k).mono (h𝒢le k)).measurable
  have hYmem : ∀ k, MemLp (Y k) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul D)
      ((hgmeas k).aestronglyMeasurable.mul (hζmem k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_right (hgD k ω) (abs_nonneg _)
  have hYmeas : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (𝒢 (k + 1)) (Y k) := fun k =>
    ((hg k).mono (h𝒢mono (Nat.le_succ k))).mul
      (stronglyMeasurable_polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (ht k).le)
  have hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0 := by
    intro k
    have hprod : Integrable (g k
        * polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1))) P :=
      (hYmem k).integrable (by norm_num)
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (hg k)
      hprod ((hζmem k).integrable (by norm_num))
    have hfun : Y k = g k
        * polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1)) := rfl
    rw [hfun]
    filter_upwards [hkey, condExp_polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa hC0 hCH₁ hCH₂ (ht0 k) (ht k)] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  rw [LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero 𝒢 h𝒢le h𝒢mono Y hYmem
    hYmeas hYcond N]
  have hterm : ∀ i ∈ Finset.range N, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ D ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
        * (t (i + 1) - t i) ^ 2 := by
    intro i _
    obtain ⟨hζint, hζle⟩ := integral_sq_polarQuadVarIncrement_le W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂
      hq₁ hq₂ hma hpa hqa hC0 hCH₁ hCH₂ (ht0 i) (ht i)
    have hYint : Integrable (fun ω => (Y i ω) ^ 2) P := by
      have hfun : (fun ω => (Y i ω) ^ 2) = Y i * Y i := by funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hYmem i).integrable_mul (hYmem i)
    have hstep : ∫ ω, (Y i ω) ^ 2 ∂P ≤ D ^ 2 * ∫ ω,
        (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2
          ∂P := by
      have hle : ∫ ω, (Y i ω) ^ 2 ∂P ≤ ∫ ω, D ^ 2 *
          (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2
            ∂P := by
        refine MeasureTheory.integral_mono hYint (hζint.const_mul _) fun ω => ?_
        have hgi : (g i ω) ^ 2 ≤ D ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (g i ω)) (hgD i ω) 2
          rwa [← abs_pow, abs_of_nonneg (sq_nonneg (g i ω))] at h
        have hsq : (Y i ω) ^ 2 = (g i ω) ^ 2 *
            (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
              (t i) (t (i + 1)) ω) ^ 2 := by
          simp only [hY]; ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right hgi (sq_nonneg _)
      rwa [MeasureTheory.integral_const_mul] at hle
    have hD2 : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
    calc ∫ ω, (Y i ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω, (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
            (t i) (t (i + 1)) ω) ^ 2 ∂P := hstep
      _ ≤ D ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)
            * (t (i + 1) - t i) ^ 2) := mul_le_mul_of_nonneg_left hζle hD2
      _ = D ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (t (i + 1) - t i) ^ 2 := by ring
  calc ∑ i ∈ Finset.range N, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ ∑ i ∈ Finset.range N, D ^ 2
          * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (t (i + 1) - t i) ^ 2 := Finset.sum_le_sum hterm
    _ = D ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * ∑ i ∈ Finset.range N, (t (i + 1) - t i) ^ 2 := by rw [Finset.mul_sum]

end Bounds

end Polarised

end LevyStochCalc.Brownian.Ito

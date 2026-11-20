/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2Completion

/-!
# Additivity of the L² Itô integral in the integrand

The Itô isometry and the isometry of differences determine every squared `L²`-distance among
`∫ H₁ dW`, `∫ H₂ dW` and `∫ (H₁ + H₂) dW` in terms of the energies of `H₁`, `H₂`, `H₁ + H₂` and
`H₁ − H₂`. The parallelogram law for those energies then forces
`∫ (H₁ + H₂) dW = ∫ H₁ dW + ∫ H₂ dW` almost everywhere.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The squared extended norm of a real number is the extended real of its square. -/
theorem sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

omit [IsProbabilityMeasure P] in
/-- The Bochner integral of a square as the extended integral of the squared norm. -/
theorem integral_sq_eq_toReal {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) :
    ∫ ω, X ω ^ 2 ∂P = (∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω))
    ((hX.mul hX).congr (Filter.Eventually.of_forall fun ω => (pow_two (X ω)).symm))]
  congr 1
  exact lintegral_congr fun ω => (sq_nnnorm_eq_ofReal_sq (X ω)).symm

omit [IsProbabilityMeasure P] in
/-- The square of a square-integrable function is integrable. -/
theorem integrable_sq_of_memLp {X : Ω → ℝ} (hX : MemLp X 2 P) :
    Integrable (fun ω => X ω ^ 2) P := by
  have h := hX.integrable_mul hX
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact (pow_two (X ω)).symm

section Energy

variable {H₁ H₂ : Ω → ℝ → ℝ}

/-- The energy density of an integrand is measurable in the sample point. -/
theorem measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnNorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'

omit [IsProbabilityMeasure P] in
/-- **The parallelogram law for the energies.** -/
theorem lintegral_energy_parallelogram (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂)) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s) := hm₁.add hm₂
  have hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s) := hm₁.sub hm₂
  have hpt : ∀ a b : ℝ, (‖a + b‖₊ : ℝ≥0∞) ^ 2 + (‖a - b‖₊ : ℝ≥0∞) ^ 2
      = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
    intro a b
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
      sq_nnnorm_eq_ofReal_sq, h2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hinner : ∀ ω : Ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = 2 * (∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    have h1 : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnNorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have h2 : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnNorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have ha : Measurable fun s => (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnNorm.comp (hma.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_add_left ha, ← lintegral_const_mul 2 h1, ← lintegral_const_mul 2 h2,
      ← lintegral_add_left (h1.const_mul 2)]
    exact lintegral_congr fun s => hpt _ _
  have e1 := measurable_energyDensity hm₁ T
  have e2 := measurable_energyDensity hm₂ T
  have ea := measurable_energyDensity hma T
  rw [← lintegral_add_left ea, ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  exact lintegral_congr fun ω => hinner ω

omit [IsProbabilityMeasure P] in
/-- An integrand dominated by twice the sum of two square-integrable energies is itself
square integrable. -/
theorem lintegral_energy_lt_top_of_bound {K : Ω → ℝ → ℝ}
    (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  have e1 := measurable_energyDensity hm₁ T
  have e2 := measurable_energyDensity hm₂ T
  have hstep : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    rw [← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
      ← lintegral_add_left (e1.const_mul 2)]
    refine lintegral_mono fun ω => ?_
    have h1 : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnNorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have h2 : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnNorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_const_mul 2 h1, ← lintegral_const_mul 2 h2,
      ← lintegral_add_left (h1.const_mul 2)]
    refine lintegral_mono fun s => ?_
    calc (‖K ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) := hbound ω s
      _ = 2 * (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := by ring
  refine lt_of_le_of_lt hstep ?_
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by simp) (hq₁ T hT), ENNReal.mul_lt_top (by simp) (hq₂ T hT)⟩

/-- The squared extended norm of a difference is dominated by twice the sum of the squares. -/
theorem sq_nnnorm_sub_le_two_mul (x y : ℝ) :
    (‖x - y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x + y)])

/-- The squared extended norm of a sum is dominated by twice the sum of the squares. -/
theorem sq_nnnorm_add_le_two_mul (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])

omit [IsProbabilityMeasure P] in
/-- Scaling an integrand scales its energy by the square of the scalar. -/
theorem lintegral_energy_const_mul {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (c T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hpt : ∀ a : ℝ, (‖c * a‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (c ^ 2) * (‖a‖₊ : ℝ≥0∞) ^ 2 := by
    intro a
    rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
      ← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    ring
  have hinner : ∀ ω : Ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        = ENNReal.ofReal (c ^ 2)
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    have h1 : Measurable fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnNorm.comp (hm.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_const_mul _ h1]
    exact lintegral_congr fun s => hpt _
  rw [← lintegral_const_mul _ (measurable_energyDensity hm T)]
  exact lintegral_congr fun ω => hinner ω

end Energy

section Parallelogram

omit [IsProbabilityMeasure P] in
/-- **A parallelogram of squared distances forces additivity.** If the squared `L²`-distances
among `u`, `v` and `w` are those of the sides and diagonals of a parallelogram, then `w` is the
sum of `u` and `v`. -/
theorem ae_eq_add_of_sq_distances {u v w : Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P) (hw : MemLp w 2 P) {A B C D : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hSu : ∫⁻ ω, (‖u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSv : ∫⁻ ω, (‖v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSw : ∫⁻ ω, (‖w ω‖₊ : ℝ≥0∞) ^ 2 ∂P = C)
    (hSwu : ∫⁻ ω, (‖w ω - u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSwv : ∫⁻ ω, (‖w ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSuv : ∫⁻ ω, (‖u ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = D)
    (hpar : C + D = 2 * A + 2 * B) :
    w =ᵐ[P] fun ω => u ω + v ω := by
  have eu : ∫ ω, u ω ^ 2 ∂P = A.toReal := by
    rw [integral_sq_eq_toReal hu.aestronglyMeasurable, hSu]
  have ev : ∫ ω, v ω ^ 2 ∂P = B.toReal := by
    rw [integral_sq_eq_toReal hv.aestronglyMeasurable, hSv]
  have ew : ∫ ω, w ω ^ 2 ∂P = C.toReal := by
    rw [integral_sq_eq_toReal hw.aestronglyMeasurable, hSw]
  have ewu : ∫ ω, (w ω - u ω) ^ 2 ∂P = B.toReal := by
    rw [integral_sq_eq_toReal (X := fun ω => w ω - u ω)
      (hw.aestronglyMeasurable.sub hu.aestronglyMeasurable), hSwu]
  have ewv : ∫ ω, (w ω - v ω) ^ 2 ∂P = A.toReal := by
    rw [integral_sq_eq_toReal (X := fun ω => w ω - v ω)
      (hw.aestronglyMeasurable.sub hv.aestronglyMeasurable), hSwv]
  have euv : ∫ ω, (u ω - v ω) ^ 2 ∂P = D.toReal := by
    rw [integral_sq_eq_toReal (X := fun ω => u ω - v ω)
      (hu.aestronglyMeasurable.sub hv.aestronglyMeasurable), hSuv]
  have hreal : C.toReal + D.toReal = 2 * A.toReal + 2 * B.toReal := by
    have h := congrArg ENNReal.toReal hpar
    rwa [ENNReal.toReal_add hC hD,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hA) (ENNReal.mul_ne_top (by simp) hB),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by simp] at h
  have hF : Integrable (fun ω => (w ω - u ω - v ω) ^ 2) P :=
    integrable_sq_of_memLp ((hw.sub hu).sub hv)
  have hW : Integrable (fun ω => w ω ^ 2) P := integrable_sq_of_memLp hw
  have hUV : Integrable (fun ω => (u ω - v ω) ^ 2) P := integrable_sq_of_memLp (hu.sub hv)
  have hU : Integrable (fun ω => u ω ^ 2) P := integrable_sq_of_memLp hu
  have hV : Integrable (fun ω => v ω ^ 2) P := integrable_sq_of_memLp hv
  have hWU : Integrable (fun ω => (w ω - u ω) ^ 2) P := integrable_sq_of_memLp (hw.sub hu)
  have hWV : Integrable (fun ω => (w ω - v ω) ^ 2) P := integrable_sq_of_memLp (hw.sub hv)
  have hkey : ∫ ω, (w ω - u ω - v ω) ^ 2 ∂P = 0 := by
    have hid : ∀ ω : Ω, (w ω - u ω - v ω) ^ 2 + w ω ^ 2 + (u ω - v ω) ^ 2
        = u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2 + (w ω - v ω) ^ 2 := fun ω => by ring
    have heq : ∫ ω, ((w ω - u ω - v ω) ^ 2 + w ω ^ 2 + (u ω - v ω) ^ 2) ∂P
        = ∫ ω, (u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2 + (w ω - v ω) ^ 2) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have hFW : Integrable (fun ω => (w ω - u ω - v ω) ^ 2 + w ω ^ 2) P := hF.add hW
    have hUV2 : Integrable (fun ω => u ω ^ 2 + v ω ^ 2) P := hU.add hV
    have hUV3 : Integrable (fun ω => u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2) P := hUV2.add hWU
    rw [integral_add hFW hUV, integral_add hF hW,
      integral_add hUV3 hWV, integral_add hUV2 hWU,
      integral_add hU hV, eu, ev, ew, ewu, ewv, euv] at heq
    linarith
  have hzero : (fun ω => (w ω - u ω - v ω) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hF).mp hkey
  filter_upwards [hzero] with ω hω
  have h2 : (w ω - u ω - v ω) ^ 2 = 0 := by simpa using hω
  have h0 : w ω - u ω - v ω = 0 := by nlinarith [h2, sq_nonneg (w ω - u ω - v ω)]
  linarith

end Parallelogram

section Additivity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **Additivity of the L² Itô integral in the integrand.** -/
theorem stochasticIntegralBrownian_add {H₁ H₂ : Ω → ℝ → ℝ}
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
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by
  have hqd : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lintegral_energy_lt_top_of_bound (fun ω s => sq_nnnorm_sub_le_two_mul _ _) hm₁ hm₂ hq₁ hq₂
  refine ae_eq_add_of_sq_distances
    (stochasticIntegralBrownian_memLp W ℱ hℱ H₁ hm₁ hp₁ hq₁ T)
    (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ hm₂ hp₂ hq₂ T)
    (stochasticIntegralBrownian_memLp W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa T)
    (hq₁ T hT).ne (hq₂ T hT).ne (hqa T hT).ne (hqd T hT).ne
    (isometry_stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ hT)
    (isometry_stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ hT)
    (isometry_stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa hT)
    ?_ ?_
    (isometry_diff_stochasticIntegralBrownian W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hT)
    (lintegral_energy_parallelogram (P := P) hm₁ hm₂ T)
  · refine Eq.trans (isometry_diff_stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => H₁ ω s + H₂ ω s) H₁ hma hm₁ hpa hp₁ hqa hq₁ hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
  · refine Eq.trans (isometry_diff_stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => H₁ ω s + H₂ ω s) H₂ hma hm₂ hpa hp₂ hqa hq₂ hT) ?_
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf

end Additivity

section Scaling

omit [IsProbabilityMeasure P] in
/-- **Squared distances of a scalar multiple force the scalar relation.** -/
theorem ae_eq_const_mul_of_sq_distances {x y : Ω → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P)
    {c : ℝ} {X Y Z : ℝ≥0∞}
    (hSx : ∫⁻ ω, (‖x ω‖₊ : ℝ≥0∞) ^ 2 ∂P = X)
    (hSy : ∫⁻ ω, (‖y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Y)
    (hSxy : ∫⁻ ω, (‖x ω - y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Z)
    (hXY : X.toReal = c ^ 2 * Y.toReal) (hZY : Z.toReal = (c - 1) ^ 2 * Y.toReal) :
    x =ᵐ[P] fun ω => c * y ω := by
  have ex : ∫ ω, x ω ^ 2 ∂P = X.toReal := by
    rw [integral_sq_eq_toReal hx.aestronglyMeasurable, hSx]
  have ey : ∫ ω, y ω ^ 2 ∂P = Y.toReal := by
    rw [integral_sq_eq_toReal hy.aestronglyMeasurable, hSy]
  have exy : ∫ ω, (x ω - y ω) ^ 2 ∂P = Z.toReal := by
    rw [integral_sq_eq_toReal (X := fun ω => x ω - y ω)
      (hx.aestronglyMeasurable.sub hy.aestronglyMeasurable), hSxy]
  have hsub : Integrable (fun ω => (x ω - y ω) ^ 2) P := integrable_sq_of_memLp (hx.sub hy)
  have hX2 : Integrable (fun ω => (1 - c) * x ω ^ 2) P :=
    (integrable_sq_of_memLp hx).const_mul _
  have hY2 : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2) P :=
    (integrable_sq_of_memLp hy).const_mul _
  have hZ2 : Integrable (fun ω => c * (x ω - y ω) ^ 2) P := hsub.const_mul _
  have hF : Integrable (fun ω => (x ω - c * y ω) ^ 2) P := by
    have : MemLp (fun ω => x ω - c * y ω) 2 P := hx.sub (hy.const_mul c)
    exact integrable_sq_of_memLp this
  have hkey : ∫ ω, (x ω - c * y ω) ^ 2 ∂P = 0 := by
    have hid : ∀ ω : Ω, (x ω - c * y ω) ^ 2
        = (1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) := fun ω => by ring
    have h1 : ∫ ω, (x ω - c * y ω) ^ 2 ∂P
        = ∫ ω, ((1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2)) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have hYZ : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) P :=
      hY2.add hZ2
    rw [h1, integral_add hX2 hYZ, integral_add hY2 hZ2,
      integral_const_mul, integral_const_mul, integral_const_mul, ex, ey, exy, hXY, hZY]
    ring
  have hzero : (fun ω => (x ω - c * y ω) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hF).mp hkey
  filter_upwards [hzero] with ω hω
  have h2 : (x ω - c * y ω) ^ 2 = 0 := by simpa using hω
  nlinarith [h2, sq_nonneg (x ω - c * y ω)]

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The L² Itô integral commutes with scaling of the integrand.** -/
theorem stochasticIntegralBrownian_const_mul {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (c : ℝ)
    (hmc : Measurable (Function.uncurry fun ω s => c * H ω s))
    (hpc : Probability.ProgressivelyMeasurable ℱ fun ω s => c * H ω s)
    (hqc : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T
      =ᵐ[P] fun ω => c * stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω := by
  have hscale := lintegral_energy_const_mul (P := P) hm c T
  have hdiff : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖c * H ω s - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal ((c - 1) ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    refine Eq.trans ?_ (lintegral_energy_const_mul (P := P) hm (c - 1) T)
    exact lintegral_congr fun ω => lintegral_congr fun s => by ring_nf
  refine ae_eq_const_mul_of_sq_distances
    (stochasticIntegralBrownian_memLp W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc T)
    (stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq T)
    (isometry_stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) hmc hpc hqc hT)
    (isometry_stochasticIntegralBrownian W ℱ hℱ H hm hp hq hT)
    (isometry_diff_stochasticIntegralBrownian W ℱ hℱ (fun ω s => c * H ω s) H hmc hm hpc hp
      hqc hq hT) ?_ ?_
  · rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c)]
  · rw [hdiff, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (c - 1))]

end Scaling

end LevyStochCalc.Brownian.Ito

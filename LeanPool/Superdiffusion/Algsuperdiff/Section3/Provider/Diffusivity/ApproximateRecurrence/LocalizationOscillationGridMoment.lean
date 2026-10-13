/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationTail

/-!
# LocalizationOscillationGridMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the grid fourth-moment functional of `e.lower.bound.oscillations`

Source displays in ABK26:

* `e.lower.bound.oscillations` (label; display) opens with the quantity
  `(avsum_{z in 3^n Zd cap cu_K} E[ ‖grad w - (grad
  w)_{z+cu_n}‖^4_{L2bar(z+cu_n)} ])^{1/4}`;
* `e.nablaw.oscillations` (label; display) is the per-base-point estimate that
  gets inserted into it.

This module isolates the purely functional-analytic bookkeeping of that
passage: the mixed "average over the grid, expectation over the sample"
fourth-moment functional and its behaviour under a pointwise two-term
majorant.

## What is proved

* `gridFourthMoment`, `gridFourthMomentRoot` -- the functional `avsum_{R in I}
  integral^4` of the display and its fourth root.
* `cubeFamilyAverage_mono`, `cubeFamilyAverage_add`, `cubeFamilyAverage_const_mul`
  -- the three elementary facts about the grid average of `LocalizationGrid`
  that the assembly uses.
* `gridFourthMoment_le_eight_mul_add` -- if `F <= G + H` pointwise on the grid
  and on the sample space, then `M_4(F) <= 8 M_4(G) + 8 M_4(H)`.  The elementary
  inequality behind it is `(a+b)^4 <= 8(a^4+b^4)`, valid for all reals.
* `gridFourthMomentRoot_le_add_of_le` -- the shape the display consumes:
  from `M_4(G) <= WG^4` and `M_4(H) <= WH^4` one gets
  `M_4(F)^{1/4} <= 8^{1/4} (WG + WH)`.
* `gridFourthMoment_le_of_forall_le` -- a per-cube uniform bound transfers to the
  grid average.

## Divergences from the printed statement

* **The triangle step costs the absolute factor `8^{1/4}`, not `1`.**  The
  manuscript's implicit step is Minkowski's inequality in
  `L^4(counting x P)`, whose constant is `1`.  What is proved here is the
  elementary `(a+b)^4 <= 8(a^4+b^4)` route, whose constant is `8^{1/4} < 1.682`.
  The loss is an absolute number, it is written out in the statement, and it is
  absorbed by the manuscript's dimension-only `C`; no sharper claim is made and
  nothing is hidden inside a constant.
* **Nothing here relates the full grid to its interior part.**  The passage
  from an interior mesh to the full one, and the boundary strip it leaves
  behind, are
  `LocalizationFluctuationMeshTransfer.cubeFamilyAverage_le_add_sqrt_boundaryFraction`
  and its consumers; this module works at a fixed family `I` throughout.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Two elementary real facts -/

/-- The real power `x ^ (4 : ℝ)` is the monoid power `x ^ (4 : ℕ)`. -/
theorem rpow_four_eq_pow_four (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem rpow_four_nonneg (x : ℝ) : 0 ≤ x ^ (4 : ℝ) := by
  rw [rpow_four_eq_pow_four, show x ^ (4 : ℕ) = (x ^ (2 : ℕ)) ^ (2 : ℕ) by ring]
  exact sq_nonneg _

/-- `(a + b)^4 ≤ 8 (a^4 + b^4)`, valid for all reals.  This is the elementary
substitute for Minkowski's inequality used in the grid assembly; the constant
`8` is sharp for this form. -/
theorem add_pow_four_le_eight_mul (a b : ℝ) :
    (a + b) ^ (4 : ℕ) ≤ 8 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
  have h1 : (a + b) ^ (2 : ℕ) ≤ 2 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (a - b)]
  have h2 : (0 : ℝ) ≤ (a + b) ^ (2 : ℕ) := sq_nonneg _
  have h3 : ((a + b) ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (2 * (a ^ (2 : ℕ) + b ^ (2 : ℕ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ h2 h1 2
  have h4 : (a ^ (2 : ℕ) + b ^ (2 : ℕ)) ^ (2 : ℕ) ≤ 2 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
    nlinarith [sq_nonneg (a ^ (2 : ℕ) - b ^ (2 : ℕ))]
  calc (a + b) ^ (4 : ℕ) = ((a + b) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ ≤ (2 * (a ^ (2 : ℕ) + b ^ (2 : ℕ))) ^ (2 : ℕ) := h3
    _ = 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ ≤ 4 * (2 * (a ^ (4 : ℕ) + b ^ (4 : ℕ))) := by linarith
    _ = 8 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by ring

/-- `x^4 + y^4 ≤ (x + y)^4` for nonnegative `x`, `y`. -/
theorem pow_four_add_pow_four_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (4 : ℕ) + y ^ (4 : ℕ) ≤ (x + y) ^ (4 : ℕ) := by
  nlinarith [mul_nonneg hx hy, sq_nonneg x, sq_nonneg y, mul_nonneg (mul_nonneg hx hy) hx,
    mul_nonneg (mul_nonneg hx hy) hy, sq_nonneg (x - y), sq_nonneg (x + y)]

/-! ## Three elementary facts about the grid average -/

theorem cubeFamilyAverage_mono {I : Finset (TriadicCube d)} {F G : TriadicCube d → ℝ}
    (h : ∀ R ∈ I, F R ≤ G R) : cubeFamilyAverage I F ≤ cubeFamilyAverage I G := by
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) ?_
  positivity

theorem cubeFamilyAverage_add (I : Finset (TriadicCube d)) (F G : TriadicCube d → ℝ) :
    cubeFamilyAverage I (fun R => F R + G R) =
      cubeFamilyAverage I F + cubeFamilyAverage I G := by
  unfold cubeFamilyAverage
  rw [Finset.sum_add_distrib]
  ring

theorem cubeFamilyAverage_const_mul (I : Finset (TriadicCube d)) (c : ℝ)
    (F : TriadicCube d → ℝ) :
    cubeFamilyAverage I (fun R => c * F R) = c * cubeFamilyAverage I F := by
  unfold cubeFamilyAverage
  rw [← Finset.mul_sum]
  ring

/-! ## The grid fourth-moment functional -/

/-- **The fourth-moment functional of `e.lower.bound.oscillations`.**  For a family
`F` of nonnegative random variables indexed by the grid `I`, this is `avsum_{R
in I} E[^4]`, the quantity under the outer fourth root of the display. -/
def gridFourthMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Ω → ℝ) : ℝ :=
  cubeFamilyAverage I fun R => ∫ ω, F R ω ^ (4 : ℝ) ∂μ

/-- The outer fourth root of the display. -/
def gridFourthMomentRoot {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Ω → ℝ) : ℝ :=
  gridFourthMoment μ I F ^ ((4 : ℝ)⁻¹)

theorem gridFourthMoment_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Ω → ℝ) :
    0 ≤ gridFourthMoment μ I F :=
  cubeFamilyAverage_nonneg fun _ _ => integral_nonneg fun ω => rpow_four_nonneg (F _ ω)

/-- Scalars come out of the functional at the fourth power. -/
theorem gridFourthMoment_const_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset (TriadicCube d)) (c : ℝ) (F : TriadicCube d → Ω → ℝ) :
    gridFourthMoment μ I (fun R ω => c * F R ω) =
      c ^ (4 : ℕ) * gridFourthMoment μ I F := by
  unfold gridFourthMoment
  rw [← cubeFamilyAverage_const_mul]
  refine congrArg (cubeFamilyAverage I) (funext fun R => ?_)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show (c * F R ω) ^ (4 : ℝ) = c ^ (4 : ℕ) * F R ω ^ (4 : ℝ)
  rw [rpow_four_eq_pow_four, rpow_four_eq_pow_four]
  ring

/-- A uniform per-cube bound transfers to the grid average. -/
theorem gridFourthMoment_le_of_forall_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Ω → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ R ∈ I, (∫ ω, F R ω ^ (4 : ℝ) ∂μ) ≤ B) :
    gridFourthMoment μ I F ≤ B := by
  unfold gridFourthMoment cubeFamilyAverage
  rcases Nat.eq_zero_or_pos I.card with hcard | hcard
  · rw [hcard]
    simpa using hB
  · have hcardR : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcard
    have hsum : ∑ R ∈ I, (∫ ω, F R ω ^ (4 : ℝ) ∂μ) ≤ (I.card : ℝ) * B := by
      calc ∑ R ∈ I, (∫ ω, F R ω ^ (4 : ℝ) ∂μ) ≤ ∑ _R ∈ I, B := Finset.sum_le_sum h
        _ = (I.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    calc ((I.card : ℝ))⁻¹ * ∑ R ∈ I, (∫ ω, F R ω ^ (4 : ℝ) ∂μ)
        ≤ ((I.card : ℝ))⁻¹ * ((I.card : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = B := by field_simp

/-! ## The two-term majorant -/

/-- **The grid fourth moment under a pointwise two-term majorant.**  This is the
step of `e.lower.bound.oscillations` that inserts `e.nablaw.oscillations` into the
grid average, with the elementary constant `8` in place of Minkowski's `1`. -/
theorem gridFourthMoment_le_eight_mul_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Finset (TriadicCube d)) (F G H : TriadicCube d → Ω → ℝ)
    (hF : ∀ R ∈ I, ∀ ω, 0 ≤ F R ω)
    (hle : ∀ R ∈ I, ∀ ω, F R ω ≤ G R ω + H R ω)
    (hGi : ∀ R ∈ I, Integrable (fun ω => G R ω ^ (4 : ℝ)) μ)
    (hHi : ∀ R ∈ I, Integrable (fun ω => H R ω ^ (4 : ℝ)) μ) :
    gridFourthMoment μ I F ≤ 8 * gridFourthMoment μ I G + 8 * gridFourthMoment μ I H := by
  have hcell : ∀ R ∈ I, (∫ ω, F R ω ^ (4 : ℝ) ∂μ) ≤
      8 * (∫ ω, G R ω ^ (4 : ℝ) ∂μ) + 8 * (∫ ω, H R ω ^ (4 : ℝ) ∂μ) := by
    intro R hR
    have hint : Integrable
        (fun ω => 8 * G R ω ^ (4 : ℝ) + 8 * H R ω ^ (4 : ℝ)) μ :=
      ((hGi R hR).const_mul 8).add ((hHi R hR).const_mul 8)
    have hpt : ∀ ω, F R ω ^ (4 : ℝ) ≤ 8 * G R ω ^ (4 : ℝ) + 8 * H R ω ^ (4 : ℝ) := by
      intro ω
      rw [rpow_four_eq_pow_four, rpow_four_eq_pow_four, rpow_four_eq_pow_four]
      calc F R ω ^ (4 : ℕ) ≤ (G R ω + H R ω) ^ (4 : ℕ) :=
            pow_le_pow_left₀ (hF R hR ω) (hle R hR ω) 4
        _ ≤ 8 * (G R ω ^ (4 : ℕ) + H R ω ^ (4 : ℕ)) := add_pow_four_le_eight_mul _ _
        _ = 8 * G R ω ^ (4 : ℕ) + 8 * H R ω ^ (4 : ℕ) := by ring
    have hmono := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω => rpow_four_nonneg (F R ω)) hint
      (Filter.Eventually.of_forall hpt)
    refine hmono.trans_eq ?_
    rw [integral_add ((hGi R hR).const_mul 8) ((hHi R hR).const_mul 8),
      integral_const_mul, integral_const_mul]
  refine (cubeFamilyAverage_mono hcell).trans_eq ?_
  rw [cubeFamilyAverage_add, cubeFamilyAverage_const_mul, cubeFamilyAverage_const_mul]
  rfl

/-- From a fourth-power bound on the functional to a bound on its fourth root. -/
theorem gridFourthMomentRoot_le_of_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Ω → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : gridFourthMoment μ I F ≤ B ^ (4 : ℕ)) :
    gridFourthMomentRoot μ I F ≤ B := by
  have hmono := Real.rpow_le_rpow (gridFourthMoment_nonneg μ I F) h
    (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
  refine hmono.trans_eq ?_
  rw [← rpow_four_eq_pow_four, ← Real.rpow_mul hB]
  norm_num

/-- **The shape `e.lower.bound.oscillations` consumes.**  A pointwise two-term
majorant on the grid, together with fourth-moment bounds for the two majorants,
gives the fourth root of the display's left-hand side at the absolute cost
`8^{1/4}`. -/
theorem gridFourthMomentRoot_le_add_of_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Finset (TriadicCube d)) (F G H : TriadicCube d → Ω → ℝ)
    {WG WH : ℝ} (hWG : 0 ≤ WG) (hWH : 0 ≤ WH)
    (hF : ∀ R ∈ I, ∀ ω, 0 ≤ F R ω)
    (hle : ∀ R ∈ I, ∀ ω, F R ω ≤ G R ω + H R ω)
    (hGi : ∀ R ∈ I, Integrable (fun ω => G R ω ^ (4 : ℝ)) μ)
    (hHi : ∀ R ∈ I, Integrable (fun ω => H R ω ^ (4 : ℝ)) μ)
    (hG : gridFourthMoment μ I G ≤ WG ^ (4 : ℕ))
    (hH : gridFourthMoment μ I H ≤ WH ^ (4 : ℕ)) :
    gridFourthMomentRoot μ I F ≤ (8 : ℝ) ^ ((4 : ℝ)⁻¹) * (WG + WH) := by
  have h8 : (0 : ℝ) ≤ (8 : ℝ) ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg (by norm_num) _
  refine gridFourthMomentRoot_le_of_le μ I F (by positivity) ?_
  have hpow : ((8 : ℝ) ^ ((4 : ℝ)⁻¹) * (WG + WH)) ^ (4 : ℕ) = 8 * (WG + WH) ^ (4 : ℕ) := by
    rw [mul_pow]
    congr 1
    rw [← rpow_four_eq_pow_four, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  rw [hpow]
  calc gridFourthMoment μ I F
      ≤ 8 * gridFourthMoment μ I G + 8 * gridFourthMoment μ I H :=
        gridFourthMoment_le_eight_mul_add μ I F G H hF hle hGi hHi
    _ ≤ 8 * WG ^ (4 : ℕ) + 8 * WH ^ (4 : ℕ) := by linarith
    _ = 8 * (WG ^ (4 : ℕ) + WH ^ (4 : ℕ)) := by ring
    _ ≤ 8 * (WG + WH) ^ (4 : ℕ) := by
        have := pow_four_add_pow_four_le WG WH hWG hWH
        linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

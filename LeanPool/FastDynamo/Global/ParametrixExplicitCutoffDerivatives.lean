/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.BumpAffineScaling
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Explicitly scaled parametrix cutoffs

Two of the three cut-offs of §7.1 of the paper, the input cut-off `φ_n` and the selected
output cut-off `ψ_n`, are nested cutoffs around a point `p`:

* `φ = 1` on `D(p, R / 5)` and `support φ = D(p, R / 4)`;
* `ψ = 1` on `D(p, R / 3)` and `support ψ = D(p, R / 2)`.

Both cutoffs are affine dilates of fixed, unit-scale `ContDiffBump`s.  This
file proves the exact support geometry and derives radius-independent first
and second derivative constants.  In particular, the second Fréchet
derivative is bounded by `K₂ / R²`; this follows from Mathlib's exact
`iteratedFDeriv` scaling theorem, rather than being included as an
assumption on the radius-dependent cutoffs.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped ENNReal NNReal

namespace ParametrixExplicitCutoff

open ConstantCoefficientBackground

/-! ## Canonical radius-dependent and fixed reference bumps -/

/-- The paper's smaller parametrix cutoff: one on radius `R / 5` and
supported on the open ball of radius `R / 4`. -/
def inputBump (p : WholePlane) (R : ℝ) (hR : 0 < R) : ContDiffBump p where
  rIn := R / 5
  rOut := R / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The paper's larger parametrix cutoff: one on radius `R / 3` and
supported on the open ball of radius `R / 2`. -/
def outputBump (p : WholePlane) (R : ℝ) (hR : 0 < R) : ContDiffBump p where
  rIn := R / 3
  rOut := R / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The smaller parametrix cutoff as an ordinary real-valued function. -/
def inputCutoff (p : WholePlane) (R : ℝ) (hR : 0 < R) : WholePlane → ℝ :=
  inputBump p R hR

/-- The larger parametrix cutoff as an ordinary real-valued function. -/
def outputCutoff (p : WholePlane) (R : ℝ) (hR : 0 < R) : WholePlane → ℝ :=
  outputBump p R hR

/-- Fixed reference for the input cutoff.  Its outer-to-inner radius ratio
is `5 / 4`. -/
def unitInputBump : ContDiffBump (0 : WholePlane) where
  rIn := 1
  rOut := 5 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Fixed reference for the output cutoff.  Its outer-to-inner radius ratio
is `3 / 2`. -/
def unitOutputBump : ContDiffBump (0 : WholePlane) where
  rIn := 1
  rOut := 3 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The input cutoff at centre `p` and radius `R` is the fixed unit bump precomposed with the
dilation `x ↦ (5 / R) • (x - p)`. -/
theorem inputCutoff_eq_unit_rescale
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    inputCutoff p R hR x = unitInputBump ((5 / R) • (x - p)) := by
  change (someContDiffBumpBase WholePlane).toFun
      ((R / 4) / (R / 5)) ((R / 5)⁻¹ • (x - p)) =
    (someContDiffBumpBase WholePlane).toFun
      ((5 / 4) / 1) (1⁻¹ • ((5 / R) • (x - p) - 0))
  have hratio : (R / 4) / (R / 5) = (5 / 4 : ℝ) / 1 := by
    field_simp
  have hscale : (R / 5)⁻¹ = 5 / R := by
    field_simp
  rw [hratio, hscale]
  simp

/-- The output cutoff at centre `p` and radius `R` is the fixed unit bump precomposed with the
dilation `x ↦ (3 / R) • (x - p)`. -/
theorem outputCutoff_eq_unit_rescale
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    outputCutoff p R hR x = unitOutputBump ((3 / R) • (x - p)) := by
  change (someContDiffBumpBase WholePlane).toFun
      ((R / 2) / (R / 3)) ((R / 3)⁻¹ • (x - p)) =
    (someContDiffBumpBase WholePlane).toFun
      ((3 / 2) / 1) (1⁻¹ • ((3 / R) • (x - p) - 0))
  have hratio : (R / 2) / (R / 3) = (3 / 2 : ℝ) / 1 := by
    field_simp
  have hscale : (R / 3)⁻¹ = 3 / R := by
    field_simp
  rw [hratio, hscale]
  simp

/-! ## Smoothness and the exact geometry of the paper -/

/-- The input cutoff is smooth. -/
theorem inputCutoff_contDiff (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (inputCutoff p R hR) := by
  exact (inputBump p R hR).contDiff

/-- The output cutoff is smooth. -/
theorem outputCutoff_contDiff (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (outputCutoff p R hR) := by
  exact (outputBump p R hR).contDiff

/-- The input cutoff has compact support. -/
theorem inputCutoff_hasCompactSupport
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (inputCutoff p R hR) := by
  exact (inputBump p R hR).hasCompactSupport

/-- The output cutoff has compact support. -/
theorem outputCutoff_hasCompactSupport
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (outputCutoff p R hR) := by
  exact (outputBump p R hR).hasCompactSupport

/-- The support of the input cutoff is exactly the open disk `D(p, R/4)`; this exact equality is
what makes cutoffs at distinct cell centres have disjoint supports. -/
theorem inputCutoff_support_eq
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    Function.support (inputCutoff p R hR) = Metric.ball p (R / 4) := by
  exact (inputBump p R hR).support_eq

/-- The support of the output cutoff is exactly the open disk `D(p, R/2)`. -/
theorem outputCutoff_support_eq
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    Function.support (outputCutoff p R hR) = Metric.ball p (R / 2) := by
  exact (outputBump p R hR).support_eq

/-- The input cutoff is identically one on the closed disk of radius `R/5`. -/
theorem inputCutoff_eq_one_of_dist_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) {x : WholePlane}
    (hx : dist x p ≤ R / 5) : inputCutoff p R hR x = 1 := by
  apply (inputBump p R hR).one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_comm, inputBump] using hx

/-- The output cutoff is identically one on the closed disk of radius `R/3`. -/
theorem outputCutoff_eq_one_of_dist_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) {x : WholePlane}
    (hx : dist x p ≤ R / 3) : outputCutoff p R hR x = 1 := by
  apply (outputBump p R hR).one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_comm, outputBump] using hx

/-- The output cutoff vanishes at distance at least `R/2` from the centre. -/
theorem outputCutoff_eq_zero_of_radius_le_dist
    (p : WholePlane) (R : ℝ) (hR : 0 < R) {x : WholePlane}
    (hx : R / 2 ≤ dist x p) : outputCutoff p R hR x = 0 := by
  exact (outputBump p R hR).zero_of_le_dist hx

/-- The input cutoff takes values in `[0, 1]`. -/
theorem inputCutoff_mem_Icc
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    inputCutoff p R hR x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(inputBump p R hR).nonneg, (inputBump p R hR).le_one⟩

/-- The output cutoff takes values in `[0, 1]`. -/
theorem outputCutoff_mem_Icc
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    outputCutoff p R hR x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(outputBump p R hR).nonneg, (outputBump p R hR).le_one⟩

/-- The larger cutoff is identically one on the support of the smaller
cutoff.  This is the nesting used to insert the auxiliary cutoff without
changing an already localized function. -/
theorem outputCutoff_eq_one_on_inputSupport
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    ∀ x ∈ Function.support (inputCutoff p R hR),
      outputCutoff p R hR x = 1 := by
  intro x hx
  rw [inputCutoff_support_eq p R hR] at hx
  apply outputCutoff_eq_one_of_dist_le p R hR
  have hx' : dist x p < R / 4 := by
    simpa [Metric.mem_ball, dist_comm] using hx
  linarith

/-- The nesting identity `phi * psi = phi`: inserting the larger cutoff does not change an already
localized function. -/
theorem inputCutoff_mul_outputCutoff
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    inputCutoff p R hR x * outputCutoff p R hR x =
      inputCutoff p R hR x := by
  by_cases hx : inputCutoff p R hR x = 0
  · simp [hx]
  · have hmem : x ∈ Function.support (inputCutoff p R hR) := hx
    rw [outputCutoff_eq_one_on_inputSupport p R hR x hmem, mul_one]

/-! ## First derivative scaling -/

/-- Lipschitz constant of the fixed unit-scale input bump. -/
def unitInputLipschitzConstant : NNReal :=
  contDiffBumpLipschitzConstant unitInputBump

/-- Lipschitz constant of the fixed unit-scale output bump. -/
def unitOutputLipschitzConstant : NNReal :=
  contDiffBumpLipschitzConstant unitOutputBump

/-- The fixed unit input bump is Lipschitz with the constant `unitInputLipschitzConstant`. -/
theorem unitInput_lipschitzWith :
    LipschitzWith unitInputLipschitzConstant
      (unitInputBump : WholePlane → ℝ) := by
  exact contDiffBump_lipschitzWith unitInputBump

/-- The fixed unit output bump is Lipschitz with the constant `unitOutputLipschitzConstant`. -/
theorem unitOutput_lipschitzWith :
    LipschitzWith unitOutputLipschitzConstant
      (unitOutputBump : WholePlane → ℝ) := by
  exact contDiffBump_lipschitzWith unitOutputBump

/-- Lipschitz constant of the radius-`R` input affine dilation. -/
def inputDilationConstant (R : ℝ) (hR : 0 < R) : NNReal :=
  ⟨5 / R, by positivity⟩

/-- Lipschitz constant of the radius-`R` output affine dilation. -/
def outputDilationConstant (R : ℝ) (hR : 0 < R) : NNReal :=
  ⟨3 / R, by positivity⟩

/-- The dilation `x ↦ (5 / R) • (x - p)` is Lipschitz with constant `5 / R`. -/
theorem inputAffine_lipschitzWith
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    LipschitzWith (inputDilationConstant R hR)
      (fun x : WholePlane ↦ (5 / R) • (x - p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((5 / R) • (x - p)) ((5 / R) • (y - p)) ≤
    (5 / R) * dist x y
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) hR), dist_eq_norm]
  rw [show x - p - (y - p) = x - y by abel]

/-- The dilation `x ↦ (3 / R) • (x - p)` is Lipschitz with constant `3 / R`. -/
theorem outputAffine_lipschitzWith
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    LipschitzWith (outputDilationConstant R hR)
      (fun x : WholePlane ↦ (3 / R) • (x - p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((3 / R) • (x - p)) ((3 / R) • (y - p)) ≤
    (3 / R) * dist x y
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) hR), dist_eq_norm]
  rw [show x - p - (y - p) = x - y by abel]

/-- The input cutoff is Lipschitz with the product constant
`unitInputLipschitzConstant * (5 / R)`, exhibiting the `1 / R` scaling. -/
theorem inputCutoff_lipschitzWith_explicit
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    LipschitzWith
      (unitInputLipschitzConstant * inputDilationConstant R hR)
      (inputCutoff p R hR) := by
  have hcomp := unitInput_lipschitzWith.comp
    (inputAffine_lipschitzWith p R hR)
  intro x y
  rw [inputCutoff_eq_unit_rescale p R hR x,
    inputCutoff_eq_unit_rescale p R hR y]
  simpa only [Function.comp_apply] using hcomp x y

/-- The output cutoff is Lipschitz with the product constant
`unitOutputLipschitzConstant * (3 / R)`. -/
theorem outputCutoff_lipschitzWith_explicit
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    LipschitzWith
      (unitOutputLipschitzConstant * outputDilationConstant R hR)
      (outputCutoff p R hR) := by
  have hcomp := unitOutput_lipschitzWith.comp
    (outputAffine_lipschitzWith p R hR)
  intro x y
  rw [outputCutoff_eq_unit_rescale p R hR x,
    outputCutoff_eq_unit_rescale p R hR y]
  simpa only [Function.comp_apply] using hcomp x y

/-- A common, radius-independent first derivative constant for both
parametrix cutoffs. -/
def firstDerivativeConstant : ℝ :=
  1 + 5 * (unitInputLipschitzConstant : ℝ) +
    3 * (unitOutputLipschitzConstant : ℝ)

/-- The common radius-independent first-derivative constant is strictly positive. -/
theorem firstDerivativeConstant_pos : 0 < firstDerivativeConstant := by
  unfold firstDerivativeConstant
  positivity

/-- Every coordinate derivative of the input cutoff is bounded by `firstDerivativeConstant / R`. -/
theorem norm_inputCutoff_coordinateDerivative_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (j : Fin 2) (x : WholePlane) :
    ‖realProfileCoordinateDerivative (inputCutoff p R hR) j x‖ ≤
      firstDerivativeConstant / R := by
  have h := norm_realProfileCoordinateDerivative_le_of_lipschitz
    (inputCutoff_lipschitzWith_explicit p R hR) j x
  calc
    ‖realProfileCoordinateDerivative (inputCutoff p R hR) j x‖ ≤
        ((unitInputLipschitzConstant *
          inputDilationConstant R hR : NNReal) : ℝ) := h
    _ = (5 * (unitInputLipschitzConstant : ℝ)) / R := by
      change (unitInputLipschitzConstant : ℝ) * (5 / R) = _
      ring
    _ ≤ firstDerivativeConstant / R := by
      apply (div_le_div_iff_of_pos_right hR).2
      unfold firstDerivativeConstant
      nlinarith [NNReal.coe_nonneg unitInputLipschitzConstant,
        NNReal.coe_nonneg unitOutputLipschitzConstant]

/-- Every coordinate derivative of the output cutoff is bounded by
`firstDerivativeConstant / R`. -/
theorem norm_outputCutoff_coordinateDerivative_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (j : Fin 2) (x : WholePlane) :
    ‖realProfileCoordinateDerivative (outputCutoff p R hR) j x‖ ≤
      firstDerivativeConstant / R := by
  have h := norm_realProfileCoordinateDerivative_le_of_lipschitz
    (outputCutoff_lipschitzWith_explicit p R hR) j x
  calc
    ‖realProfileCoordinateDerivative (outputCutoff p R hR) j x‖ ≤
        ((unitOutputLipschitzConstant *
          outputDilationConstant R hR : NNReal) : ℝ) := h
    _ = (3 * (unitOutputLipschitzConstant : ℝ)) / R := by
      change (unitOutputLipschitzConstant : ℝ) * (3 / R) = _
      ring
    _ ≤ firstDerivativeConstant / R := by
      apply (div_le_div_iff_of_pos_right hR).2
      unfold firstDerivativeConstant
      nlinarith [NNReal.coe_nonneg unitInputLipschitzConstant,
        NNReal.coe_nonneg unitOutputLipschitzConstant]

/-! ## Fixed second derivative constants -/

/-- The second iterated Fréchet derivative of the fixed unit input bump is globally bounded, being
continuous with compact support. -/
theorem exists_unitInput_secondDerivative_bound :
    ∃ C : ℝ, ∀ x : WholePlane,
      ‖iteratedFDeriv ℝ 2 (unitInputBump : WholePlane → ℝ) x‖ ≤ C := by
  have hcont : Continuous (fun x : WholePlane ↦
      iteratedFDeriv ℝ 2 (unitInputBump : WholePlane → ℝ) x) :=
    (unitInputBump.contDiff : ContDiff ℝ 2
      (unitInputBump : WholePlane → ℝ)).continuous_iteratedFDeriv le_rfl
  have hsupp : HasCompactSupport (iteratedFDeriv ℝ 2
      (unitInputBump : WholePlane → ℝ)) :=
    unitInputBump.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) 2
  exact hcont.bounded_above_of_compact_support hsupp

/-- The second iterated Fréchet derivative of the fixed unit output bump is globally bounded. -/
theorem exists_unitOutput_secondDerivative_bound :
    ∃ C : ℝ, ∀ x : WholePlane,
      ‖iteratedFDeriv ℝ 2 (unitOutputBump : WholePlane → ℝ) x‖ ≤ C := by
  have hcont : Continuous (fun x : WholePlane ↦
      iteratedFDeriv ℝ 2 (unitOutputBump : WholePlane → ℝ) x) :=
    (unitOutputBump.contDiff : ContDiff ℝ 2
      (unitOutputBump : WholePlane → ℝ)).continuous_iteratedFDeriv le_rfl
  have hsupp : HasCompactSupport (iteratedFDeriv ℝ 2
      (unitOutputBump : WholePlane → ℝ)) :=
    unitOutputBump.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) 2
  exact hcont.bounded_above_of_compact_support hsupp

/-- A nonnegative global Hessian bound for the fixed input reference bump. -/
def unitInputSecondDerivativeConstant : ℝ :=
  max 0 (Classical.choose exists_unitInput_secondDerivative_bound)

/-- A nonnegative global Hessian bound for the fixed output reference bump. -/
def unitOutputSecondDerivativeConstant : ℝ :=
  max 0 (Classical.choose exists_unitOutput_secondDerivative_bound)

/-- The chosen unit-scale input Hessian constant is nonnegative, by construction as a `max` with
zero. -/
theorem unitInputSecondDerivativeConstant_nonneg :
    0 ≤ unitInputSecondDerivativeConstant := by
  exact le_max_left _ _

/-- The chosen unit-scale output Hessian constant is nonnegative. -/
theorem unitOutputSecondDerivativeConstant_nonneg :
    0 ≤ unitOutputSecondDerivativeConstant := by
  exact le_max_left _ _

/-- The second iterated derivative of the unit input bump is bounded everywhere by
`unitInputSecondDerivativeConstant`. -/
theorem unitInput_secondDerivative_le (x : WholePlane) :
    ‖iteratedFDeriv ℝ 2 (unitInputBump : WholePlane → ℝ) x‖ ≤
      unitInputSecondDerivativeConstant := by
  exact (Classical.choose_spec exists_unitInput_secondDerivative_bound x).trans
    (le_max_right _ _)

/-- The second iterated derivative of the unit output bump is bounded everywhere by
`unitOutputSecondDerivativeConstant`. -/
theorem unitOutput_secondDerivative_le (x : WholePlane) :
    ‖iteratedFDeriv ℝ 2 (unitOutputBump : WholePlane → ℝ) x‖ ≤
      unitOutputSecondDerivativeConstant := by
  exact (Classical.choose_spec exists_unitOutput_secondDerivative_bound x).trans
    (le_max_right _ _)

/-! ## Exact second derivative scaling -/

/-- Translation contributes no factor and scalar dilation contributes
exactly `a^2` to the second iterated Fréchet derivative. -/
theorem iteratedFDeriv_two_affine_dilation
    (f : WholePlane → ℝ) (hf : ContDiff ℝ 2 f)
    (a : ℝ) (p x : WholePlane) :
    iteratedFDeriv ℝ 2 (fun z ↦ f (a • (z - p))) x =
      a ^ 2 • iteratedFDeriv ℝ 2 f (a • (x - p)) := by
  calc
    iteratedFDeriv ℝ 2 (fun z ↦ f (a • (z - p))) x =
        iteratedFDeriv ℝ 2 (fun y ↦ f (a • y)) (x - p) := by
      exact iteratedFDeriv_comp_sub (𝕜 := ℝ)
        (f := fun y : WholePlane ↦ f (a • y)) 2 p x
    _ = a ^ 2 • iteratedFDeriv ℝ 2 f (a • (x - p)) := by
      exact congrFun (iteratedFDeriv_comp_const_smul
        (𝕜 := ℝ) (f := f) a hf) (x - p)

/-- Exact scaling of the input cutoff's second derivative: it is `(5 / R) ^ 2` times the unit
bump's second derivative at the dilated point. -/
theorem inputCutoff_iteratedFDeriv_two_eq
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    iteratedFDeriv ℝ 2 (inputCutoff p R hR) x =
      (5 / R) ^ 2 • iteratedFDeriv ℝ 2
        (unitInputBump : WholePlane → ℝ) ((5 / R) • (x - p)) := by
  rw [show inputCutoff p R hR =
      (fun z ↦ unitInputBump ((5 / R) • (z - p))) by
    funext z
    exact inputCutoff_eq_unit_rescale p R hR z]
  exact iteratedFDeriv_two_affine_dilation
    (unitInputBump : WholePlane → ℝ)
      (unitInputBump.contDiff : ContDiff ℝ 2
        (unitInputBump : WholePlane → ℝ)) (5 / R) p x

/-- Exact scaling of the output cutoff's second derivative: it is `(3 / R) ^ 2` times the unit
bump's second derivative at the dilated point. -/
theorem outputCutoff_iteratedFDeriv_two_eq
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    iteratedFDeriv ℝ 2 (outputCutoff p R hR) x =
      (3 / R) ^ 2 • iteratedFDeriv ℝ 2
        (unitOutputBump : WholePlane → ℝ) ((3 / R) • (x - p)) := by
  rw [show outputCutoff p R hR =
      (fun z ↦ unitOutputBump ((3 / R) • (z - p))) by
    funext z
    exact outputCutoff_eq_unit_rescale p R hR z]
  exact iteratedFDeriv_two_affine_dilation
    (unitOutputBump : WholePlane → ℝ)
      (unitOutputBump.contDiff : ContDiff ℝ 2
        (unitOutputBump : WholePlane → ℝ)) (3 / R) p x

/-- A common, radius-independent second derivative constant for both
parametrix cutoffs. -/
def secondDerivativeConstant : ℝ :=
  1 + 25 * unitInputSecondDerivativeConstant +
    9 * unitOutputSecondDerivativeConstant

/-- The common radius-independent second-derivative constant is strictly positive. -/
theorem secondDerivativeConstant_pos : 0 < secondDerivativeConstant := by
  unfold secondDerivativeConstant
  nlinarith [unitInputSecondDerivativeConstant_nonneg,
    unitOutputSecondDerivativeConstant_nonneg]

/-- The input cutoff's second derivative is bounded by `secondDerivativeConstant / R ^ 2`, the
`K₂ / R²` law used by the parametrix commutator estimates. -/
theorem norm_inputCutoff_iteratedFDeriv_two_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    ‖iteratedFDeriv ℝ 2 (inputCutoff p R hR) x‖ ≤
      secondDerivativeConstant / R ^ 2 := by
  rw [inputCutoff_iteratedFDeriv_two_eq p R hR x, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (5 / R))]
  calc
    (5 / R) ^ 2 *
        ‖iteratedFDeriv ℝ 2 (unitInputBump : WholePlane → ℝ)
          ((5 / R) • (x - p))‖ ≤
        (5 / R) ^ 2 * unitInputSecondDerivativeConstant := by
      exact mul_le_mul_of_nonneg_left
        (unitInput_secondDerivative_le ((5 / R) • (x - p)))
        (sq_nonneg _)
    _ = (25 * unitInputSecondDerivativeConstant) / R ^ 2 := by ring
    _ ≤ secondDerivativeConstant / R ^ 2 := by
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2
      unfold secondDerivativeConstant
      nlinarith [unitInputSecondDerivativeConstant_nonneg,
        unitOutputSecondDerivativeConstant_nonneg]

/-- The output cutoff's second derivative is bounded by `secondDerivativeConstant / R ^ 2`. -/
theorem norm_outputCutoff_iteratedFDeriv_two_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    ‖iteratedFDeriv ℝ 2 (outputCutoff p R hR) x‖ ≤
      secondDerivativeConstant / R ^ 2 := by
  rw [outputCutoff_iteratedFDeriv_two_eq p R hR x, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (3 / R))]
  calc
    (3 / R) ^ 2 *
        ‖iteratedFDeriv ℝ 2 (unitOutputBump : WholePlane → ℝ)
          ((3 / R) • (x - p))‖ ≤
        (3 / R) ^ 2 * unitOutputSecondDerivativeConstant := by
      exact mul_le_mul_of_nonneg_left
        (unitOutput_secondDerivative_le ((3 / R) • (x - p)))
        (sq_nonneg _)
    _ = (9 * unitOutputSecondDerivativeConstant) / R ^ 2 := by ring
    _ ≤ secondDerivativeConstant / R ^ 2 := by
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2
      unfold secondDerivativeConstant
      nlinarith [unitInputSecondDerivativeConstant_nonneg,
        unitOutputSecondDerivativeConstant_nonneg]

/-! ## Coordinate Hessian bounds -/

/-- The `(j,k)` entry of the second iterated Fréchet derivative in the
orthonormal coordinate directions used throughout the whole-plane API. -/
def secondCoordinateDerivative (f : WholePlane → ℝ)
    (j k : Fin 2) (x : WholePlane) : ℝ :=
  iteratedFDeriv ℝ 2 f x ![wholePlaneBasis j, wholePlaneBasis k]

/-- A coordinate Hessian entry is bounded by the operator norm of the full second derivative, the
coordinate directions being unit vectors. -/
theorem norm_secondCoordinateDerivative_le_opNorm
    (f : WholePlane → ℝ) (j k : Fin 2) (x : WholePlane) :
    ‖secondCoordinateDerivative f j k x‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
  calc
    ‖secondCoordinateDerivative f j k x‖ ≤
        ‖iteratedFDeriv ℝ 2 f x‖ *
          ∏ i : Fin 2, ‖![wholePlaneBasis j, wholePlaneBasis k] i‖ :=
      (iteratedFDeriv ℝ 2 f x).le_opNorm _
    _ = ‖iteratedFDeriv ℝ 2 f x‖ := by
      simp [wholePlaneBasis]

/-- Each coordinate Hessian entry of the output cutoff is bounded by
`secondDerivativeConstant / R ^ 2`. -/
theorem norm_outputCutoff_secondCoordinateDerivative_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (j k : Fin 2) (x : WholePlane) :
    ‖secondCoordinateDerivative (outputCutoff p R hR) j k x‖ ≤
      secondDerivativeConstant / R ^ 2 := by
  exact (norm_secondCoordinateDerivative_le_opNorm
    (outputCutoff p R hR) j k x).trans
      (norm_outputCutoff_iteratedFDeriv_two_le p R hR x)

end ParametrixExplicitCutoff

end

end FastDynamo

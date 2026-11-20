/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusTwoSummandParametrix
public import LeanPool.FastDynamo.Operator.HorizontalSectorBasic

/-!
# The parametrix error and the resolvent on the shifted contour

This module formalises §7.1 of the paper ("The two-resolvent construction").

* **`eq:explicit-error`** (`lem:parametrix-error` and its proof):
  `‖E_n(z)‖_{2→2} ≤ C(√ε/R_n + ε/R_n²) ≤ C(√ℓ_n + ℓ_n)`.
  The first inequality comes from the diffusion-only commutator formula together with the two
  gradient bounds `eq:bg-resolvent` and `eq:local-gradient`; the second from `ε = δ_nℓ_n²`,
  `R_n = √ℓ_n` and `δ_n ∈ I`.  The constant is explicit in the two resolvent constants and in
  the two cut-off constants of `eq:parametrix-cutoff-bounds`, and is independent of `n`, of
  `δ_n ∈ I`, of `z` and of the final enlargement of `K_0`.
* **`eq:parametrix-uniform-bound`**: `‖R_app(z)‖_{2→2} ≤ C_app`, with
  `C_app = C_bg + C_n`.  The input side of the background summand carries the sharp bound
  `‖1 - φ_n‖ ≤ 1`, which the placed cut-off supplies from `0 ≤ φ_n ≤ 1`; the triangle
  inequality would only give `2`.  The corresponding `L²`-to-`H²` norm need not be uniform,
  and none is claimed.
* **`lem:global-contour-resolvent`** and its proof: if `‖E_n(z)‖ < 1` on the parameter set then
  the Neumann series inverts `id + E_n(z)`, `R_app(z)(id + E_n(z))⁻¹` is a right inverse of
  `z - A_{ε,K_n}`, and Fredholm index zero — `lem:torus-sector-basic`, available for the
  horizontal operator as
  `Operator/HorizontalSectorBasic.pencilFredholmIndexZeroOn_horizontalInductionOperator` —
  upgrades it to the resolvent.  `eq:global-resolvent` is recorded as the identity
  `(z - A)⁻¹ = R_app(z)(id + E_n(z))⁻¹`.
* **`eq:error-small`** as a threshold statement: the scalar majorant
  `C(√ℓ + ℓ)` tends to zero as `ℓ ↓ 0`, so for every `η_* > 0` there is a scale threshold below
  which the error is smaller than `η_*`, uniformly in `δ ∈ I`.  Since `ℓ_n ≤ ℓ_0 = 1/K_0`, this
  is exactly "we enlarge `K_0` until …".

The sign convention is the paper's: `(z - A)R_app = id + E_n`, which is also the convention
of `ParametrixNeumannCorrection.rightError`, so no sign flip is needed anywhere.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace TorusParametrixError

open HorizontalCutoffCommutator ParametrixCutoffs LocalizedSummandAlgebra
open TransverseVecMultiplierAlgebra
open TorusTwoSummandParametrix

/-! ## The scalar error majorant -/

/-- The right-hand side of the first inequality of `eq:explicit-error`:
`C(√ε/R + ε/R²)`. -/
def scaleErrorMajorant (C ε R : ℝ) : ℝ :=
  C * (Real.sqrt ε / R + ε / R ^ 2)

/-- At the paper's scaling `ε = δℓ²`, `R = √ℓ` the majorant is exactly
`C(√δ√ℓ + δℓ)`: this is the computation behind the second inequality of `eq:explicit-error`. -/
theorem scaleErrorMajorant_scaled (C δ ℓ : ℝ) (hδ : 0 ≤ δ) (hℓ : 0 < ℓ) :
    scaleErrorMajorant C (δ * ℓ ^ 2) (Real.sqrt ℓ) =
      C * (Real.sqrt δ * Real.sqrt ℓ + δ * ℓ) := by
  have hsqrtℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hsq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  have heps : Real.sqrt (δ * ℓ ^ 2) = Real.sqrt δ * ℓ := by
    rw [Real.sqrt_mul hδ, Real.sqrt_sq hℓ.le]
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hdiv : Real.sqrt δ * ℓ / Real.sqrt ℓ = Real.sqrt δ * Real.sqrt ℓ := by
    rw [mul_div_assoc, Real.div_sqrt]
  have hdiv2 : δ * ℓ ^ 2 / ℓ = δ * ℓ := by
    field_simp
  unfold scaleErrorMajorant
  rw [heps, hsq, hdiv, hdiv2]

/-- `√x ≤ 1 + x` for `x ≥ 0`, the crude bound used to fold `√δ` and `δ` into one constant. -/
theorem sqrt_le_one_add (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]

/-- **The second inequality of `eq:explicit-error`**:
with `ε = δℓ²`, `R = √ℓ` and `δ ≤ δ₊`, the majorant is at most `C(1 + δ₊)(√ℓ + ℓ)`, a constant
multiple of `√ℓ + ℓ`. -/
theorem scaleErrorMajorant_scaled_le (C δ δplus ℓ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hδle : δ ≤ δplus) (hℓ : 0 < ℓ) :
    scaleErrorMajorant C (δ * ℓ ^ 2) (Real.sqrt ℓ) ≤
      C * (1 + δplus) * (Real.sqrt ℓ + ℓ) := by
  rw [scaleErrorMajorant_scaled C δ ℓ hδ hℓ]
  have hδplus : 0 ≤ δplus := le_trans hδ hδle
  have h1 : Real.sqrt δ ≤ 1 + δplus :=
    le_trans (Real.sqrt_le_sqrt hδle) (sqrt_le_one_add δplus hδplus)
  have h2 : δ ≤ 1 + δplus := by linarith
  have hsq : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg ℓ
  have hstep : Real.sqrt δ * Real.sqrt ℓ + δ * ℓ ≤ (1 + δplus) * (Real.sqrt ℓ + ℓ) := by
    nlinarith [hsq, hℓ.le]
  calc
    C * (Real.sqrt δ * Real.sqrt ℓ + δ * ℓ) ≤ C * ((1 + δplus) * (Real.sqrt ℓ + ℓ)) :=
      mul_le_mul_of_nonneg_left hstep hC
    _ = C * (1 + δplus) * (Real.sqrt ℓ + ℓ) := by ring

/-- **`eq:error-small` as a threshold statement** (proof of `lem:global-contour-resolvent`):
the scalar majorant of `eq:explicit-error` tends to zero with the cell scale, uniformly in
`δ ∈ I`.  Since `ℓ_n ≤ ℓ_0 = 1/K_0` for every `n`, enlarging `K_0` beyond `1/L` makes the
parametrix error smaller than any prescribed `η_* > 0`, for every cell at once. -/
theorem exists_scale_threshold (C δplus η : ℝ) (hC : 0 ≤ C) (hδplus : 0 ≤ δplus)
    (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ ℓ : ℝ, 0 ≤ δ → δ ≤ δplus → 0 < ℓ → ℓ ≤ L →
      scaleErrorMajorant C (δ * ℓ ^ 2) (Real.sqrt ℓ) < η := by
  set M : ℝ := C * (1 + δplus) with hM
  have hMnonneg : 0 ≤ M := by positivity
  refine ⟨min 1 ((η / (2 * (M + 1))) ^ 2), ?_, ?_⟩
  · have : 0 < η / (2 * (M + 1)) := by positivity
    exact lt_min one_pos (by positivity)
  · intro δ ℓ hδ hδle hℓ hℓle
    have hℓ1 : ℓ ≤ 1 := le_trans hℓle (min_le_left _ _)
    have hℓL : ℓ ≤ (η / (2 * (M + 1))) ^ 2 := le_trans hℓle (min_le_right _ _)
    have hq : 0 < η / (2 * (M + 1)) := by positivity
    have hsqrt : Real.sqrt ℓ ≤ η / (2 * (M + 1)) := by
      rw [show ((η / (2 * (M + 1))) : ℝ) = Real.sqrt ((η / (2 * (M + 1))) ^ 2) from
        (Real.sqrt_sq hq.le).symm]
      exact Real.sqrt_le_sqrt hℓL
    have hℓsqrt : ℓ ≤ Real.sqrt ℓ := by
      have hsq2 : ℓ ^ 2 ≤ ℓ := by nlinarith
      calc
        ℓ = Real.sqrt (ℓ ^ 2) := (Real.sqrt_sq hℓ.le).symm
        _ ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hsq2
    have hmain := scaleErrorMajorant_scaled_le C δ δplus ℓ hC hδ hδle hℓ
    have hbound : M * (Real.sqrt ℓ + ℓ) ≤ M * (2 * (η / (2 * (M + 1)))) := by
      apply mul_le_mul_of_nonneg_left _ hMnonneg
      have : Real.sqrt ℓ + ℓ ≤ 2 * Real.sqrt ℓ := by linarith
      linarith [hsqrt]
    have hfinal : M * (2 * (η / (2 * (M + 1)))) < η := by
      rw [show M * (2 * (η / (2 * (M + 1)))) = M * η / (M + 1) by
        field_simp]
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    calc
      scaleErrorMajorant C (δ * ℓ ^ 2) (Real.sqrt ℓ) ≤ M * (Real.sqrt ℓ + ℓ) := hmain
      _ ≤ M * (2 * (η / (2 * (M + 1)))) := hbound
      _ < η := hfinal

/-! ## The commutator estimate against the two gradient bounds -/

/-- The constant produced by one diffusion-only commutator: `2√2C₁ + 2C₂`, where `C₁` and `C₂`
are the two constants of `eq:parametrix-cutoff-bounds`.  The `√2` is the Cauchy-Schwarz factor
of `Σ_j‖∂_jh‖ ≤ √2‖∇_⊥h‖`. -/
def commutatorErrorConstant (C₁ C₂ : ℝ) : ℝ :=
  2 * Real.sqrt 2 * C₁ + 2 * C₂

/-- The commutator error constant is nonnegative. -/
theorem commutatorErrorConstant_nonneg {C₁ C₂ : ℝ} (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) :
    0 ≤ commutatorErrorConstant C₁ C₂ := by
  unfold commutatorErrorConstant
  have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- **The commutator half of `eq:explicit-error`** (proof of `lem:parametrix-error`):
if the transverse velocity vanishes on the cut-off gradient, the cut-off obeys the scale bounds
`‖∂_jχ‖_∞ ≤ C₁/R`, `‖Δχ‖_∞ ≤ 2C₂/R²`, and the field `g` obeys the two resolvent bounds
`‖g‖₂ ≤ b` and `√ε‖∇_⊥g‖₂ ≤ b`, then

`‖[A_{ε,K}, χ]g‖₂ ≤ (2√2C₁ + 2C₂) b (√ε/R + ε/R²)`. -/
theorem norm_commutator_le_of_bounds
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf)
    (ε R C₁ C₂ b : ℝ) (K : ℤ) (hε : 0 ≤ ε) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hb : 0 ≤ b)
    (hvanish : VelocityVanishesOnGradient chi u)
    (hgradient : ∀ j, ‖chi.gradient j‖ ≤ C₁ / R)
    (hlaplacian : ‖chi.laplacian‖ ≤ 2 * C₂ / R ^ 2)
    (g : TransverseC2H2)
    (hnorm : ‖transverseH2Embedding g‖ ≤ b)
    (hgrad : Real.sqrt (ε * transverseGradientEnergy g) ≤ b) :
    ‖commutator chi u ε K g‖ ≤
      commutatorErrorConstant C₁ C₂ * b * (Real.sqrt ε / R + ε / R ^ 2) := by
  have hbase := norm_commutator_apply_le_explicitScale chi u ε R C₁ C₂ K hvanish
    hgradient hlaplacian g
  have hcs := sum_norm_deriv_le_sqrt_gradientEnergy (ι := Fin 2) g
  have hE : 0 ≤ transverseGradientEnergy g := transverseGradientEnergy_nonneg g
  have hsqrtE : 0 ≤ Real.sqrt (transverseGradientEnergy g) := Real.sqrt_nonneg _
  have hsqrtEps : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hsplit : Real.sqrt (ε * transverseGradientEnergy g) =
      Real.sqrt ε * Real.sqrt (transverseGradientEnergy g) := Real.sqrt_mul hε _
  have hkey : ε * Real.sqrt (transverseGradientEnergy g) ≤ Real.sqrt ε * b := by
    have h1 : ε * Real.sqrt (transverseGradientEnergy g) =
        Real.sqrt ε * Real.sqrt (ε * transverseGradientEnergy g) := by
      rw [hsplit, ← mul_assoc, Real.mul_self_sqrt hε]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hgrad hsqrtEps
  have hC1R : 0 ≤ C₁ / R := div_nonneg hC₁ hR.le
  have hC2R : 0 ≤ 2 * C₂ / R ^ 2 := div_nonneg (by linarith) (by positivity)
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hstep :
      ε * (2 * ((C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j g‖) +
          (2 * C₂ / R ^ 2) * ‖transverseH2Embedding g‖) ≤
        2 * Real.sqrt 2 * (C₁ / R) * (Real.sqrt ε * b) + (2 * C₂ / R ^ 2) * b * ε := by
    have ha :
        ε * (2 * ((C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j g‖)) ≤
          2 * Real.sqrt 2 * (C₁ / R) * (Real.sqrt ε * b) := by
      have h2 : ε * (2 * ((C₁ / R) *
            ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j g‖)) ≤
          ε * (2 * ((C₁ / R) *
            (Real.sqrt 2 * Real.sqrt (transverseGradientEnergy g)))) := by
        gcongr
      refine h2.trans ?_
      have h3 : ε * (2 * ((C₁ / R) *
            (Real.sqrt 2 * Real.sqrt (transverseGradientEnergy g)))) =
          2 * Real.sqrt 2 * (C₁ / R) *
            (ε * Real.sqrt (transverseGradientEnergy g)) := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
    have hb2 : ε * ((2 * C₂ / R ^ 2) * ‖transverseH2Embedding g‖) ≤
        (2 * C₂ / R ^ 2) * b * ε := by
      have hmid : ε * ((2 * C₂ / R ^ 2) * ‖transverseH2Embedding g‖) ≤
          ε * ((2 * C₂ / R ^ 2) * b) := by gcongr
      refine hmid.trans ?_
      exact le_of_eq (by ring)
    calc
      ε * (2 * ((C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j g‖) +
          (2 * C₂ / R ^ 2) * ‖transverseH2Embedding g‖) =
          ε * (2 * ((C₁ / R) *
              ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j g‖)) +
            ε * ((2 * C₂ / R ^ 2) * ‖transverseH2Embedding g‖) := by ring
      _ ≤ _ := add_le_add ha hb2
  have hfinal :
      2 * Real.sqrt 2 * (C₁ / R) * (Real.sqrt ε * b) + (2 * C₂ / R ^ 2) * b * ε ≤
        commutatorErrorConstant C₁ C₂ * b * (Real.sqrt ε / R + ε / R ^ 2) := by
    unfold commutatorErrorConstant
    have hA : 0 ≤ 2 * Real.sqrt 2 * C₁ * b * (ε / R ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC₁) hb)
        (div_nonneg hε (by positivity))
    have hB : 0 ≤ 2 * C₂ * b * (Real.sqrt ε / R) :=
      mul_nonneg (mul_nonneg (by linarith) hb) (div_nonneg hsqrtEps hR.le)
    have hexpand :
        (2 * Real.sqrt 2 * C₁ + 2 * C₂) * b * (Real.sqrt ε / R + ε / R ^ 2) -
            (2 * Real.sqrt 2 * (C₁ / R) * (Real.sqrt ε * b) +
              (2 * C₂ / R ^ 2) * b * ε) =
          2 * Real.sqrt 2 * C₁ * b * (ε / R ^ 2) + 2 * C₂ * b * (Real.sqrt ε / R) := by
      ring
    linarith
  calc
    ‖commutator chi u ε K g‖ ≤
        |ε| * (2 * ((C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j g‖) +
          (2 * C₂ / R ^ 2) * ‖transverseH2Embedding g‖) := hbase
    _ = ε * (2 * ((C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j g‖) +
          (2 * C₂ / R ^ 2) * ‖transverseH2Embedding g‖) := by rw [abs_of_nonneg hε]
    _ ≤ 2 * Real.sqrt 2 * (C₁ / R) * (Real.sqrt ε * b) + (2 * C₂ / R ^ 2) * b * ε := hstep
    _ ≤ _ := hfinal

/-! ## `eq:explicit-error` and `eq:parametrix-uniform-bound` -/

section Concrete

universe w t

variable {Y : Type w} {F : Type t}
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {u ubg : TransverseRealW1Inf} {ε : ℝ} {K : ℤ} {R : ℝ} {S : Set ℂ}

/-- The constant of `eq:explicit-error`: the commutator constant of the two output cut-offs
times the total resolvent constant `C_bg + C_n`.  The input of the background summand carries
`‖1 - φ_n‖ ≤ 1` (`HorizontalParametrixCutoffs.norm_inputComplement_le`, sharp because
`0 ≤ φ_n ≤ 1` pointwise), not the triangle-inequality factor `2`. -/
def parametrixErrorConstant (Cbg Cloc : ℝ) : ℝ :=
  commutatorErrorConstant cutoffFirstDerivativeConstant cutoffSecondDerivativeConstant *
    (Cbg + Cloc)

/-- The error constant of `eq:explicit-error` is nonnegative. -/
theorem parametrixErrorConstant_nonneg {Cbg Cloc : ℝ} (hbg : 0 ≤ Cbg) (hloc : 0 ≤ Cloc) :
    0 ≤ parametrixErrorConstant Cbg Cloc := by
  unfold parametrixErrorConstant
  exact mul_nonneg
    (commutatorErrorConstant_nonneg cutoffFirstDerivativeConstant_pos.le
      cutoffSecondDerivativeConstant_pos.le) (by linarith)

/-- **`eq:explicit-error`, pointwise** (first inequality):
`‖E_n(z)f‖₂ ≤ C(√ε/R_n + ε/R_n²)‖f‖₂`. -/
theorem norm_error_apply_le (P : TwoSummandParametrixData Y F u ubg ε K R S)
    (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ S) (f : TransverseC2L2) :
    ‖P.error z f‖ ≤
      scaleErrorMajorant
          (parametrixErrorConstant P.background.bound P.selected.bound) ε R * ‖f‖ := by
  have hR := P.cutoffs.radius_pos
  have hf : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hbgb := P.background.bound_nonneg
  have hlocb := P.selected.bound_nonneg
  -- the background summand
  have hinput : ‖P.cutoffs.inputComplement f‖ ≤ ‖f‖ := by
    calc
      ‖P.cutoffs.inputComplement f‖ ≤ ‖P.cutoffs.inputComplement‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f‖ :=
        mul_le_mul_of_nonneg_right P.cutoffs.norm_inputComplement_le hf
      _ = ‖f‖ := one_mul _
  have hbgnorm : ‖transverseH2Embedding
      (P.background.resolvent z (P.cutoffs.inputComplement f))‖ ≤
      P.background.bound * ‖f‖ := by
    refine (P.background.norm_le z hz _).trans ?_
    gcongr
  have hbggrad : Real.sqrt (ε * transverseGradientEnergy
      (P.background.resolvent z (P.cutoffs.inputComplement f))) ≤
      P.background.bound * ‖f‖ := by
    refine (P.background.sqrt_gradient_le z hz _).trans ?_
    gcongr
  have hbg := norm_commutator_le_of_bounds P.cutoffs.background u ε R
    cutoffFirstDerivativeConstant cutoffSecondDerivativeConstant
    (P.background.bound * ‖f‖) K hε hR cutoffFirstDerivativeConstant_pos.le
    cutoffSecondDerivativeConstant_pos.le (by positivity) P.backgroundVanishes
    P.cutoffs.norm_background_gradient_le P.cutoffs.norm_background_laplacian_le
    (P.background.resolvent z (P.cutoffs.inputComplement f)) hbgnorm hbggrad
  -- the selected summand
  have hloc := norm_commutator_le_of_bounds P.cutoffs.output u ε R
    cutoffFirstDerivativeConstant cutoffSecondDerivativeConstant
    (P.selected.bound * ‖f‖) K hε hR cutoffFirstDerivativeConstant_pos.le
    cutoffSecondDerivativeConstant_pos.le (by positivity) P.outputVanishes
    P.cutoffs.norm_output_gradient_le P.cutoffs.norm_output_laplacian_le
    (P.selected.transported z f) (P.selected.norm_le z hz f)
    (P.selected.sqrt_gradient_le z hz f)
  rw [P.error_apply hz, norm_neg]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hbg hloc).trans ?_
  unfold scaleErrorMajorant parametrixErrorConstant
  ring_nf
  rfl

/-- **`eq:explicit-error`** (first inequality) as an operator-norm
bound: `‖E_n(z)‖_{2→2} ≤ C(√ε/R_n + ε/R_n²)`, with `C` explicit in the two resolvent constants
and the two cut-off constants, hence independent of `n`, of `δ_n ∈ I`, of `z` and of the final
enlargement of `K_0`. -/
theorem norm_error_le (P : TwoSummandParametrixData Y F u ubg ε K R S)
    (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ S) :
    ‖P.error z‖ ≤
      scaleErrorMajorant (parametrixErrorConstant P.background.bound P.selected.bound) ε R := by
  have hR := P.cutoffs.radius_pos
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ fun f ↦ norm_error_apply_le P hε hz f
  unfold scaleErrorMajorant
  have h1 : 0 ≤ Real.sqrt ε / R := div_nonneg (Real.sqrt_nonneg ε) hR.le
  have h2 : 0 ≤ ε / R ^ 2 := div_nonneg hε (by positivity)
  exact mul_nonneg
    (parametrixErrorConstant_nonneg P.background.bound_nonneg P.selected.bound_nonneg)
    (by linarith)

/-- **`eq:parametrix-uniform-bound`**:
`‖R_app(z)‖_{2→2} ≤ C_app = C_bg + C_n`, uniformly in the spectral parameter.  Only the
`L²`-to-`L²` norm is bounded; the paper explicitly does not claim uniformity of the
`L²`-to-`H²` norm, and none is asserted here. -/
theorem norm_stateParametrix_apply_le (P : TwoSummandParametrixData Y F u ubg ε K R S)
    {z : ℂ} (hz : z ∈ S) (f : TransverseC2L2) :
    ‖transverseH2Embedding (P.approximateInverse z f)‖ ≤
      (P.background.bound + P.selected.bound) * ‖f‖ := by
  have hf : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hinput : ‖P.cutoffs.inputComplement f‖ ≤ ‖f‖ := by
    calc
      ‖P.cutoffs.inputComplement f‖ ≤ ‖P.cutoffs.inputComplement‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f‖ :=
        mul_le_mul_of_nonneg_right P.cutoffs.norm_inputComplement_le hf
      _ = ‖f‖ := one_mul _
  have hsplit : P.approximateInverse z f =
      P.cutoffs.background.domainMul
          (P.background.resolvent z (P.cutoffs.inputComplement f)) +
        P.selected.extendDomain (P.selected.resolvent z (P.selected.restrictInput f)) := by
    simp only [TwoSummandParametrixData.approximateInverse, twoSummandParametrix,
      localSummand, add_apply, ContinuousLinearMap.comp_apply]
  have hbg : ‖transverseH2Embedding (P.cutoffs.background.domainMul
      (P.background.resolvent z (P.cutoffs.inputComplement f)))‖ ≤
      P.background.bound * ‖f‖ := by
    rw [P.cutoffs.background.embedding_domainMul]
    refine (norm_scalarVectorMulTransverseVec_apply_le _ _).trans ?_
    have h1 : ‖transverseH2Embedding
        (P.background.resolvent z (P.cutoffs.inputComplement f))‖ ≤
        P.background.bound * ‖f‖ :=
      (P.background.norm_le z hz _).trans
        (mul_le_mul_of_nonneg_left hinput P.background.bound_nonneg)
    calc
      ‖P.cutoffs.background.value‖ *
          ‖transverseH2Embedding
            (P.background.resolvent z (P.cutoffs.inputComplement f))‖ ≤
          1 * (P.background.bound * ‖f‖) := by
        apply mul_le_mul P.cutoffs.norm_background_value_le_one h1 (norm_nonneg _)
        norm_num
      _ = P.background.bound * ‖f‖ := by ring
  have hloc := P.selected.norm_summand_le z hz f
  rw [hsplit, map_add]
  refine (norm_add_le _ _).trans ?_
  calc
    ‖transverseH2Embedding (P.cutoffs.background.domainMul
        (P.background.resolvent z (P.cutoffs.inputComplement f)))‖ +
        ‖transverseH2Embedding
          (P.selected.extendDomain (P.selected.resolvent z (P.selected.restrictInput f)))‖ ≤
        P.background.bound * ‖f‖ + P.selected.bound * ‖f‖ := add_le_add hbg hloc
    _ = (P.background.bound + P.selected.bound) * ‖f‖ := by ring

/-! ## `lem:global-contour-resolvent` -/

/-- **`lem:global-contour-resolvent`**.

If the parametrix error is a strict contraction at every point of the parameter set, then the
Neumann series inverts `id + E_n(z)`, the corrected parametrix `R_app(z)(id + E_n(z))⁻¹` is a
right inverse of `z - A_{ε,K_n}` hence a surjection, and Fredholm index zero — which
`lem:torus-sector-basic` supplies for the horizontal operator at every `z` — turns it into the
resolvent.  In particular `Γ_τ ⊂ ρ(A_{ε,K_n})`. -/
def globalContourResolvent (P : TwoSummandParametrixData Y F u ubg ε K R S) (hε : 0 < ε)
    (hsmall : ∀ z ∈ S, ‖P.error z‖ < 1) :
    HasResolventOn (horizontalInductionOperator u ε K) S := by
  refine ParametrixNeumannCorrection.hasResolventOnOfRightParametrixIndexZero
    (horizontalInductionOperator u ε K) P.approximateInverse
    P.continuousOn_approximateInverse ?_ ?_ ?_
  · intro z hz
    rw [P.transfer_rightError_eq hz]
    exact hsmall z hz
  · intro z _
    exact isFredholm_horizontalInductionPencil u ε K hε z
  · intro z _
    exact index_horizontalInductionPencil_eq_zero u ε K hε z

/-- **`eq:global-resolvent`**:
`(z - A_{ε,K_n})⁻¹ = R_app(z)(id + E_n(z))⁻¹`. -/
theorem globalContourResolvent_inv (P : TwoSummandParametrixData Y F u ubg ε K R S)
    (hε : 0 < ε) (hsmall : ∀ z ∈ S, ‖P.error z‖ < 1) {z : ℂ} (hz : z ∈ S) :
    (globalContourResolvent P hε hsmall).inv z =
      (P.approximateInverse z).comp
        (Ring.inverse (ContinuousLinearMap.id ℂ TransverseC2L2 + P.error z)) := by
  change ParametrixNeumannCorrection.correctedInverse
      (horizontalInductionOperator u ε K) P.approximateInverse z = _
  unfold ParametrixNeumannCorrection.correctedInverse ParametrixNeumannCorrection.rightCorrection
  rw [P.transfer_rightError_eq hz]

/-- The contraction hypothesis of `lem:global-contour-resolvent` follows from the explicit error
bound of `eq:explicit-error` together with `eq:error-small`: it suffices that the scalar
majorant be smaller than one. -/
theorem error_norm_lt_one_of_majorant (P : TwoSummandParametrixData Y F u ubg ε K R S)
    (hε : 0 ≤ ε)
    (hmaj : scaleErrorMajorant
      (parametrixErrorConstant P.background.bound P.selected.bound) ε R < 1) :
    ∀ z ∈ S, ‖P.error z‖ < 1 :=
  fun _ hz ↦ lt_of_le_of_lt (norm_error_le P hε hz) hmaj

end Concrete

end TorusParametrixError

end

end FastDynamo

/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.DilationFamilies
public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Derivative kernels

On a finite-dimensional real inner product space `V` of dimension `n` with Lebesgue measure, let
`e_0, …, e_{n-1}` be the orthonormal basis of `Rd.gridBasis`, and for directions
`w = (w_0, …, w_{k-1}) ∈ V^k` let `∂^w = ∂_{w_0} ⋯ ∂_{w_{k-1}}`. For every `m ∈ ℕ` the
Littlewood–Paley block `ψ_1` is a sum of derivatives of order `m` of Schwartz functions:
`ψ_1 = ∑_{i : Fin m → Fin n} ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}} η_i`
(`Rd.sum_iteratedLineDerivOp_derivKernel`). On the Fourier side this is
`‖ξ‖^{2m} = ∑_i ∏_k ⟪ξ, e_{i_k}⟫²` (`Rd.norm_pow_eq_sum_prod_inner`): the kernel `η_i` has the
Fourier transform `𝓕η_i(ξ) = ∏_k ⟪ξ, e_{i_k}⟫ / ((2πi)^m ‖ξ‖^{2m}) · 𝓕ψ_1(ξ)`
(`Rd.derivSymbol`, `Rd.derivKernel`), a smooth function since `𝓕ψ_1` vanishes near `0`.

* **Fourier transforms of derivatives**: `𝓕(∂^w G)(ξ) = (∏_l 2πi ⟪ξ, w_l⟫) 𝓕G(ξ)` for Schwartz
  functions with values in a complex normed space (`SchwartzMap.fourier_iteratedLineDerivOp_apply`).
* **The dilated identity**: with the chain rule `∂^w (G_c) = c^k (∂^w G)_c`
  (`Rd.iteratedLineDerivOp_schwartzDilate`),
  `2^{jm} ψ_{j+1} = ∑_i ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}} ((η_i)_{2^j})`
  (`Rd.two_pow_smul_psi_succ_eq_sum`), with the factor `‖2^n‖ = 2^n` (`Rd.enorm_two_pow_complex`).
* **The derivative families** `((η_i)_{2^j})_j` are Calderón–Zygmund families with overlap `2`
  (`Rd.isCZFamily_derivFamily`).
* **The dual derivative families**: for every `w ∈ V^k` the synthesis kernels satisfy
  `∂^w psiDual_j = 2^{jk} (∂^w psiDualBase_j)_{2^j}` (`Rd.iteratedLineDerivOp_psiDualS`), and the
  dilates on the right form a Calderón–Zygmund family with overlap `4 ((8π)^k ∏_l ‖w_l‖)²`
  (`Rd.isCZFamily_derivDualFamily`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter
open scoped ENNReal SchwartzMap FourierTransform LineDeriv Real

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Coordinates and the symbols -/

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Powers of the norm in coordinates**: with the orthonormal basis `e_0, …, e_{n-1}` of
`Rd.gridBasis`, `‖ξ‖^{2m} = ∑_{i : Fin m → Fin n} ∏_k ⟪ξ, e_{i_k}⟫²`, from
`‖ξ‖² = ∑_i ⟪ξ, e_i⟫²` (Mathlib's `OrthonormalBasis.sum_sq_inner_left`) and the expansion of an
`m`-th power of a sum (Mathlib's `Fintype.sum_pow`). -/
theorem norm_pow_eq_sum_prod_inner (ξ : V) (m : ℕ) :
    ‖ξ‖ ^ (2 * m) = ∑ i : Fin m → Fin (finrank ℝ V), ∏ k, inner ℝ ξ (gridBasis V (i k)) ^ 2 := by
  rw [pow_mul, ← (gridBasis V).sum_sq_inner_left ξ, Fintype.sum_pow]

/-- The **derivative symbol** of the multi-index `i : Fin m → Fin n`:
`σ_i(ξ) = ∏_k ⟪ξ, e_{i_k}⟫ / ((2πi)^m ‖ξ‖^{2m})`, with the orthonormal basis `e` of
`Rd.gridBasis`; at `ξ = 0` its value is `0` for `m ≥ 1` (Lean's convention `x / 0 = 0`). -/
noncomputable def derivSymbol {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) (ξ : V) : ℂ :=
  ((2 * π * Complex.I) ^ m)⁻¹ *
    (((∏ k, inner ℝ ξ (gridBasis V (i k))) / ‖ξ‖ ^ (2 * m) : ℝ) : ℂ)

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The symbols invert the derivatives**: for every `ξ ≠ 0`,
`∑_i (∏_k 2πi ⟪ξ, e_{i_k}⟫) σ_i(ξ) = 1`, since each term is
`(∏_k ⟪ξ, e_{i_k}⟫)² / ‖ξ‖^{2m}` and these add up to `1` (`Rd.norm_pow_eq_sum_prod_inner`). -/
theorem sum_prod_mul_derivSymbol {m : ℕ} {ξ : V} (hξ : ξ ≠ 0) :
    ∑ i : Fin m → Fin (finrank ℝ V),
      (∏ k, 2 * π * Complex.I * (inner ℝ ξ (gridBasis V (i k)) : ℂ)) * derivSymbol i ξ = 1 := by
  have hc : (2 * π * Complex.I : ℂ) ^ m ≠ 0 :=
    pow_ne_zero _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  have hN : ‖ξ‖ ^ (2 * m) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hξ)
  have hreal : ∑ i : Fin m → Fin (finrank ℝ V), (∏ k, inner ℝ ξ (gridBasis V (i k))) *
      ((∏ k, inner ℝ ξ (gridBasis V (i k))) / ‖ξ‖ ^ (2 * m)) = 1 := by
    simp_rw [← mul_div_assoc, ← sq, ← Finset.prod_pow]
    rw [← Finset.sum_div, ← norm_pow_eq_sum_prod_inner, div_self hN]
  calc ∑ i : Fin m → Fin (finrank ℝ V),
        (∏ k, 2 * π * Complex.I * (inner ℝ ξ (gridBasis V (i k)) : ℂ)) * derivSymbol i ξ
      = ∑ i : Fin m → Fin (finrank ℝ V), (((∏ k, inner ℝ ξ (gridBasis V (i k))) *
          ((∏ k, inner ℝ ξ (gridBasis V (i k))) / ‖ξ‖ ^ (2 * m)) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [derivSymbol, Finset.prod_mul_distrib, Fin.prod_const, Complex.ofReal_mul,
          Complex.ofReal_prod]
        field_simp
    _ = 1 := by rw [← Complex.ofReal_sum, hreal, Complex.ofReal_one]

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The symbols are bounded away from the origin**: `|σ_i(ξ)| ≤ 1` for `‖ξ‖ ≥ 1`, since
`|⟪ξ, e⟫| ≤ ‖ξ‖`, `‖ξ‖^m ≤ ‖ξ‖^{2m}` and `(2π)^m ≥ 1`. -/
theorem norm_derivSymbol_le {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) {ξ : V} (hξ : 1 ≤ ‖ξ‖) :
    ‖derivSymbol i ξ‖ ≤ 1 := by
  have hP : |∏ k, inner ℝ ξ (gridBasis V (i k))| ≤ ‖ξ‖ ^ (2 * m) := by
    rw [Finset.abs_prod]
    calc ∏ k, |inner ℝ ξ (gridBasis V (i k))| ≤ ∏ _k : Fin m, ‖ξ‖ :=
          Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ =>
            (abs_real_inner_le_norm _ _).trans_eq (by rw [(gridBasis V).orthonormal.1, mul_one])
      _ = ‖ξ‖ ^ m := Fin.prod_const m ‖ξ‖
      _ ≤ ‖ξ‖ ^ (2 * m) := pow_le_pow_right₀ hξ (by omega)
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  rw [derivSymbol, norm_mul, norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le,
    mul_one, Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ (2 * m))]
  calc ((2 * π) ^ m)⁻¹ * (|∏ k, inner ℝ ξ (gridBasis V (i k))| / ‖ξ‖ ^ (2 * m)) ≤ 1 * 1 :=
        mul_le_mul (inv_le_one_of_one_le₀ (one_le_pow₀ h2π)) (div_le_one_of_le₀ hP (by positivity))
          (by positivity) zero_le_one
    _ = 1 := one_mul 1

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivative symbols are smooth away from the origin: `ξ ↦ ∏_k ⟪ξ, e_{i_k}⟫` and
`ξ ↦ ‖ξ‖^{2m} = (‖ξ‖²)^m` are smooth, and the second vanishes only at `0`. -/
theorem contDiffOn_derivSymbol {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (derivSymbol i) {ξ : V | ξ ≠ 0} := by
  have hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : V => ∏ k, inner ℝ ξ (gridBasis V (i k))) :=
    contDiff_prod fun k _ => contDiff_id.inner ℝ contDiff_const
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : V => ‖ξ‖ ^ (2 * m)) := by
    simp_rw [pow_mul]
    exact (contDiff_norm_sq ℝ).pow m
  have hq := hP.contDiffOn.div hN.contDiffOn fun ξ (hξ : ξ ∈ {ξ : V | ξ ≠ 0}) =>
    pow_ne_zero _ (norm_ne_zero_iff.2 hξ)
  exact contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hq)

/-! ### The block `ψ_1` -/

/-- The block `ψ_1 = Φ_1 - Φ` as a Schwartz function, `ψ_1 = δ_2 (psiBase 1)`. -/
noncomputable def psiOneS : 𝓢(V, ℂ) := schwartzDilate 2 two_ne_zero (psiBase 1)

/-- The Schwartz function `Rd.psiOneS` is the block `ψ_1`. -/
theorem coe_psiOneS : (psiOneS : V → ℂ) = psi (V := V) 1 := by
  have h := dilate_psiBase (V := V) 1
  rw [pow_one] at h
  rw [psiOneS, coe_schwartzDilate, h]

/-- **The blocks are dilates of `ψ_1`**: `ψ_{j+1} = (ψ_1)_{2^j}`. -/
theorem dilate_psi_one (j : ℕ) : dilate (2 ^ j) (psi (V := V) 1) = psi (j + 1) := by
  rw [← coe_psiOneS, psiOneS, coe_schwartzDilate, dilate_dilate, ← pow_succ,
    ← dilate_psiBase (j + 1)]
  rfl

/-- The Fourier transform of the Schwartz function `Rd.psiOneS` is `𝓕ψ_1`. -/
theorem fourier_psiOneS_apply (ξ : V) : 𝓕 (psiOneS (V := V)) ξ = 𝓕 (psi (V := V) 1) ξ := by
  rw [SchwartzMap.fourier_coe, coe_psiOneS]

/-- `𝓕ψ_{j+1}(ξ) = 𝓕ψ_1(2^{-j} ξ)`. -/
theorem fourier_psi_succ_eq_fourier_psi_one (j : ℕ) (ξ : V) :
    𝓕 (psi (V := V) (j + 1)) ξ = 𝓕 (psi (V := V) 1) (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  rw [← dilate_psi_one, fourier_dilate _ (by positivity)]

/-- Where `𝓕ψ_1(ξ) ≠ 0`, `‖ξ‖ > 1`: the case `i = 0` of
`Rd.lt_norm_of_fourier_psi_succ_ne_zero`. -/
theorem one_lt_norm_of_fourier_psi_one_ne_zero {ξ : V} (h : 𝓕 (psi (V := V) 1) ξ ≠ 0) :
    1 < ‖ξ‖ := by
  simpa using lt_norm_of_fourier_psi_succ_ne_zero (i := 0) h

/-! ### The derivative kernels -/

/-- The function `ξ ↦ σ_i(ξ) 𝓕ψ_1(ξ)` is smooth: `𝓕ψ_1` is smooth and vanishes on the unit ball,
and `σ_i` is smooth away from `0` (`Rd.contDiffOn_derivSymbol`). -/
theorem contDiff_derivSymbol_mul_fourier_psi_one {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : V => derivSymbol i ξ * 𝓕 (psi (V := V) 1) ξ) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕 (psi (V := V) 1)) := by
    rw [← coe_psiOneS, ← SchwartzMap.fourier_coe]
    exact SchwartzMap.smooth (𝓕 (psiOneS (V := V))) ⊤
  refine contDiff_iff_contDiffAt.2 fun ξ => ?_
  by_cases hξ : ξ = 0
  · subst hξ
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : V) one_pos] with ζ hζ
    rw [mem_ball_zero_iff] at hζ
    rw [fourier_psi_succ_eq_zero (i := 0) (by rw [pow_zero]; exact hζ.le), mul_zero]
  · exact ((contDiffOn_derivSymbol i).contDiffAt (isOpen_ne.mem_nhds hξ)).mul hF.contDiffAt

/-- The function `ξ ↦ σ_i(ξ) 𝓕ψ_1(ξ)` has compact support: it vanishes outside the closed ball
of radius `4`. -/
theorem hasCompactSupport_derivSymbol_mul_fourier_psi_one {m : ℕ}
    (i : Fin m → Fin (finrank ℝ V)) :
    HasCompactSupport (fun ξ : V => derivSymbol i ξ * 𝓕 (psi (V := V) 1) ξ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : V) 4) fun ξ hξ => ?_
  rw [mem_closedBall_zero_iff, not_le] at hξ
  have h : 𝓕 (psi (V := V) 1) ξ = 0 := by
    by_contra h
    have h4 := norm_lt_of_fourier_psi_ne_zero h
    norm_num at h4
    linarith
  rw [h, mul_zero]

/-- The Fourier transform `ξ ↦ σ_i(ξ) 𝓕ψ_1(ξ)` of the derivative kernel `η_i`, a Schwartz
function. -/
noncomputable def derivKernelHat {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) : 𝓢(V, ℂ) :=
  (hasCompactSupport_derivSymbol_mul_fourier_psi_one i).toSchwartzMap
    (contDiff_derivSymbol_mul_fourier_psi_one i)

/-- The **derivative kernel** `η_i = 𝓕⁻¹(σ_i 𝓕ψ_1)` of the multi-index `i : Fin m → Fin n`. -/
noncomputable def derivKernel {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) : 𝓢(V, ℂ) :=
  𝓕⁻ (derivKernelHat i)

/-- `𝓕η_i(ξ) = σ_i(ξ) 𝓕ψ_1(ξ)`. -/
theorem fourier_derivKernel {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) (ξ : V) :
    𝓕 (derivKernel i : V → ℂ) ξ = derivSymbol i ξ * 𝓕 (psi (V := V) 1) ξ := by
  rw [← SchwartzMap.fourier_coe, derivKernel, FourierInvPair.fourier_fourierInv_eq]
  rfl

/-- **`ψ_1` as a sum of derivatives**: for every `m ∈ ℕ`,
`∑_{i : Fin m → Fin n} ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}} η_i = ψ_1` as Schwartz functions. Both sides
have the same Fourier transform: `(∑_i ∏_k 2πi ⟪ξ, e_{i_k}⟫ σ_i(ξ)) 𝓕ψ_1(ξ) = 𝓕ψ_1(ξ)` for
`ξ ≠ 0` (`Rd.sum_prod_mul_derivSymbol`), and `𝓕ψ_1(0) = 0`. -/
theorem sum_iteratedLineDerivOp_derivKernel (m : ℕ) :
    ∑ i : Fin m → Fin (finrank ℝ V), ∂^{fun k => gridBasis V (i k)} (derivKernel i) =
      psiOneS (V := V) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).injective
  simp only [FourierTransform.fourierCLE_apply, FourierTransform.fourier_sum]
  ext ξ
  rw [sum_apply, SchwartzMap.fourier_coe psiOneS, coe_psiOneS]
  simp_rw [SchwartzMap.fourier_iteratedLineDerivOp_apply, smul_eq_mul,
    SchwartzMap.fourier_coe (derivKernel _), fourier_derivKernel, ← mul_assoc]
  rw [← Finset.sum_mul]
  by_cases hξ : ξ = 0
  · subst hξ
    rw [fourier_psi_succ_eq_zero (i := 0) (by simp), mul_zero]
  · rw [sum_prod_mul_derivSymbol hξ, one_mul]

/-- **The dilated identity**: for all `m, j ∈ ℕ`,
`2^{jm} ψ_{j+1} = ∑_{i : Fin m → Fin n} ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}} ((η_i)_{2^j})`, from
`Rd.sum_iteratedLineDerivOp_derivKernel`, the chain rule for dilations
(`Rd.iteratedLineDerivOp_schwartzDilate`) and `(ψ_1)_{2^j} = ψ_{j+1}`. -/
theorem two_pow_smul_psi_succ_eq_sum (m j : ℕ) :
    ((2 : ℂ) ^ (j * m)) • psi (V := V) (j + 1) =
      ∑ i : Fin m → Fin (finrank ℝ V), ⇑(∂^{fun k => gridBasis V (i k)}
        (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (derivKernel i))) := by
  have h : ∑ i : Fin m → Fin (finrank ℝ V), ∂^{fun k => gridBasis V (i k)}
      (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (derivKernel i)) =
      ((2 : ℂ) ^ (j * m)) • schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) psiOneS := by
    simp_rw [iteratedLineDerivOp_schwartzDilate]
    rw [← Finset.smul_sum, ← schwartzDilate_sum, sum_iteratedLineDerivOp_derivKernel]
    push_cast
    rw [pow_mul]
  funext x
  have hx := congrArg (fun S : 𝓢(V, ℂ) => S x) h
  simp only [sum_apply, smul_apply] at hx
  rw [Finset.sum_apply, hx, Pi.smul_apply, coe_schwartzDilate, coe_psiOneS, dilate_psi_one]

/-- The complex number `2^n` has absolute value `2^n`, by Mathlib's `eNorm_pow` and
`Complex.norm_two`; this is the size of the factor `2^{jm}` of the dilated identity. -/
theorem enorm_two_pow_complex (n : ℕ) : ‖(2 : ℂ) ^ n‖ₑ = 2 ^ n := by
  rw [eNorm_pow, ← ofReal_norm, Complex.norm_two, ENNReal.ofReal_ofNat]

/-! ### The derivative families -/

/-- The **derivative family** of the multi-index `i`: `j ↦ (η_i)_{2^j}`. -/
noncomputable def derivFamily {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) (j : ℕ) : V → ℂ :=
  dilate (2 ^ j) (derivKernel i : V → ℂ)

/-- `𝓕(η_i)_{2^j}(ξ) = σ_i(2^{-j} ξ) 𝓕ψ_{j+1}(ξ)`. -/
theorem fourier_derivFamily {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) (j : ℕ) (ξ : V) :
    𝓕 (derivFamily i j) ξ = derivSymbol i (((2 : ℝ) ^ j)⁻¹ • ξ) * 𝓕 (psi (V := V) (j + 1)) ξ := by
  rw [derivFamily, fourier_dilate _ (by positivity), fourier_derivKernel,
    fourier_psi_succ_eq_fourier_psi_one j ξ]

/-- `|𝓕(η_i)_{2^j}(ξ)| ≤ |𝓕ψ_{j+1}(ξ)|`: where `𝓕ψ_{j+1}(ξ) ≠ 0`, `‖2^{-j} ξ‖ > 1` and
`|σ_i| ≤ 1` there (`Rd.norm_derivSymbol_le`). -/
theorem enorm_fourier_derivFamily_le {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) (j : ℕ) (ξ : V) :
    ‖𝓕 (derivFamily i j) ξ‖ₑ ≤ ‖𝓕 (psi (V := V) (j + 1)) ξ‖ₑ := by
  rw [fourier_derivFamily, eNorm_mul]
  by_cases h : 𝓕 (psi (V := V) (j + 1)) ξ = 0
  · rw [h, eNorm_zero, mul_zero]
  · rw [fourier_psi_succ_eq_fourier_psi_one j ξ] at h
    have h1 := (one_lt_norm_of_fourier_psi_one_ne_zero h).le
    calc ‖derivSymbol i (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ * ‖𝓕 (psi (V := V) (j + 1)) ξ‖ₑ
        ≤ 1 * ‖𝓕 (psi (V := V) (j + 1)) ξ‖ₑ := by
          gcongr
          rw [← ofReal_norm, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (norm_derivSymbol_le i h1)
      _ = ‖𝓕 (psi (V := V) (j + 1)) ξ‖ₑ := one_mul _

/-- **Overlap of a derivative family**: `∑_j |𝓕(η_i)_{2^j}(ξ)|² ≤ 2` for every `ξ`, by comparison
with the blocks (`Rd.enorm_fourier_derivFamily_le`, `Rd.tsum_fourier_psi_sq_le`). -/
theorem tsum_fourier_derivFamily_sq_le {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) (ξ : V) :
    ∑' j, ‖𝓕 (derivFamily i j) ξ‖ₑ ^ 2 ≤ 2 :=
  calc ∑' j, ‖𝓕 (derivFamily i j) ξ‖ₑ ^ 2
      ≤ ∑' j, ‖𝓕 (psi (V := V) (j + 1)) ξ‖ₑ ^ 2 :=
        tsum_le_tsum fun j => by gcongr; exact enorm_fourier_derivFamily_le i j ξ
    _ ≤ ∑' j, ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 :=
        tsum_comp_le_tsum_of_injective (add_left_injective 1)
          fun j => ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2
    _ ≤ 2 := tsum_fourier_psi_sq_le ξ

/-- The seminorm bounds `A^{η_i}_{k,l} = sup_x ‖x‖^k ‖D^l η_i(x)‖` of the derivative kernel
`η_i`. -/
noncomputable def derivKernelBound {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) (k l : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ k l (derivKernel i)

/-- The constant family `j ↦ η_i` is uniformly Schwartz with bounds `Rd.derivKernelBound i`. -/
theorem isUniformSchwartz_derivKernel {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) :
    IsUniformSchwartz (fun _ => derivKernel i) (derivKernelBound i) :=
  IsUniformSchwartz.const _

/-- **The derivative families are Calderón–Zygmund families** with overlap `2` and Hörmander
constant `4 H_{A^{η_i}}`, `H_{A^{η_i}} = Rd.familyHormanderConst V (Rd.derivKernelBound i)`. -/
theorem isCZFamily_derivFamily {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) :
    IsCZFamily (derivFamily i) 2 (4 * familyHormanderConst V (derivKernelBound i)) :=
  IsCZFamily.of_dilation (isUniformSchwartz_derivKernel i) (tsum_fourier_derivFamily_sq_le i)

/-! ### The dual derivative families -/

/-- The synthesis kernel `psiDual_j = (psiDualBase j)_{2^j}` as a Schwartz function. -/
noncomputable def psiDualS (j : ℕ) : 𝓢(V, ℂ) :=
  schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (psiDualBase j)

/-- The Schwartz function `Rd.psiDualS j` is the synthesis kernel `psiDual_j`. -/
theorem coe_psiDualS (j : ℕ) : (psiDualS j : V → ℂ) = psiDual j := by
  rw [psiDualS, coe_schwartzDilate, dilate_psiDualBase]

/-- The **dual derivative bases** `∂^w psiDualBase_j = ∂_{w_0} ⋯ ∂_{w_{k-1}} psiDualBase_j` of
the directions `w ∈ V^k`. -/
noncomputable def derivDualBase {k : ℕ} (w : Fin k → V) (j : ℕ) : 𝓢(V, ℂ) :=
  ∂^{w} (psiDualBase j)

/-- The **dual derivative family** `j ↦ (∂^w psiDualBase_j)_{2^j}`. -/
noncomputable def derivDualFamily {k : ℕ} (w : Fin k → V) (j : ℕ) : V → ℂ :=
  dilate (2 ^ j) (derivDualBase w j : V → ℂ)

/-- **Derivatives of the synthesis kernels**:
`∂^w psiDual_j = 2^{jk} (∂^w psiDualBase_j)_{2^j}` as functions
(`Rd.iteratedLineDerivOp_schwartzDilate` with `c = 2^j`). -/
theorem iteratedLineDerivOp_psiDualS {k : ℕ} (w : Fin k → V) (j : ℕ) :
    ⇑(∂^{w} (psiDualS (V := V) j)) = ((2 : ℂ) ^ (j * k)) • derivDualFamily w j := by
  rw [psiDualS, iteratedLineDerivOp_schwartzDilate]
  funext x
  rw [smul_apply, coe_schwartzDilate, Pi.smul_apply, derivDualFamily, derivDualBase]
  push_cast
  rw [pow_mul]

/-- The seminorm bounds of the dual derivative bases `j ↦ ∂^w psiDualBase_j`: the larger of the
seminorms of `∂^w δ_2 Φ` (`j = 0, 1`) and `∂^w (δ_2 Φ - δ_{1/4} Φ)` (`j ≥ 2`). -/
noncomputable def derivDualBound {k : ℕ} (w : Fin k → V) (a l : ℕ) : ℝ :=
  max (SchwartzMap.seminorm ℝ a l (derivDualBase w 0))
    (SchwartzMap.seminorm ℝ a l (derivDualBase w 2))

/-- The dual derivative bases are uniformly Schwartz with bounds `Rd.derivDualBound w`: they take
the two values of `j = 0` and `j = 2`. -/
theorem isUniformSchwartz_derivDualBase {k : ℕ} (w : Fin k → V) :
    IsUniformSchwartz (derivDualBase w) (derivDualBound w) :=
  IsUniformSchwartz.of_forall_eq_or_eq fun j => by
    match j with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inl rfl
    | _ + 2 => exact Or.inr rfl

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The **overlap of a dual derivative family**, `4 ((8π)^k ∏_l ‖w_l‖)²`. -/
noncomputable def derivDualOverlap {k : ℕ} (w : Fin k → V) : ℝ≥0∞ :=
  4 * (ENNReal.ofReal (8 * π) ^ k * ∏ l, ‖w l‖ₑ) ^ 2

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The overlap of a dual derivative family is finite. -/
theorem derivDualOverlap_ne_top {k : ℕ} (w : Fin k → V) : derivDualOverlap w ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.prod_ne_top fun _ _ => eNorm_ne_top)))

/-- `𝓕(∂^w psiDualBase_j)_{2^j}(ξ) = (∏_l 2πi ⟪2^{-j} ξ, w_l⟫) 𝓕 psiDual_j(ξ)`. -/
theorem fourier_derivDualFamily {k : ℕ} (w : Fin k → V) (j : ℕ) (ξ : V) :
    𝓕 (derivDualFamily w j) ξ = (∏ l, 2 * π * Complex.I *
      (inner ℝ (((2 : ℝ) ^ j)⁻¹ • ξ) (w l) : ℂ)) * 𝓕 (psiDual (V := V) j) ξ := by
  rw [derivDualFamily, fourier_dilate _ (by positivity), ← SchwartzMap.fourier_coe, derivDualBase,
    SchwartzMap.fourier_iteratedLineDerivOp_apply, smul_eq_mul, SchwartzMap.fourier_coe,
    ← fourier_dilate _ (by positivity), dilate_psiDualBase]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|∏_l 2πi ⟪ζ, w_l⟫| ≤ (2πR)^k ∏_l ‖w_l‖` for `‖ζ‖ ≤ R`, by Cauchy–Schwarz. -/
theorem enorm_prod_inner_le {k : ℕ} (w : Fin k → V) {ζ : V} {R : ℝ} (hζ : ‖ζ‖ ≤ R) :
    ‖∏ l, 2 * π * Complex.I * (inner ℝ ζ (w l) : ℂ)‖ₑ ≤
      ENNReal.ofReal (2 * π * R) ^ k * ∏ l, ‖w l‖ₑ := by
  have hR : 0 ≤ R := (norm_nonneg ζ).trans hζ
  have h2πR : 0 ≤ 2 * π * R := mul_nonneg (by positivity) hR
  have h : ‖∏ l, 2 * π * Complex.I * (inner ℝ ζ (w l) : ℂ)‖ ≤ (2 * π * R) ^ k * ∏ l, ‖w l‖ := by
    rw [norm_prod]
    calc ∏ l, ‖2 * π * Complex.I * (inner ℝ ζ (w l) : ℂ)‖ ≤ ∏ l, 2 * π * R * ‖w l‖ :=
          Finset.prod_le_prod₀ (fun l _ => norm_nonneg _) fun l _ => ?_
      _ = (2 * π * R) ^ k * ∏ l, ‖w l‖ := by rw [Finset.prod_mul_distrib, Fin.prod_const]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le, mul_one, Real.norm_eq_abs]
    have h1 := abs_real_inner_le_norm ζ (w l)
    have h2 : ‖ζ‖ * ‖w l‖ ≤ R * ‖w l‖ := by gcongr
    nlinarith [Real.pi_pos]
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [ENNReal.ofReal_mul (pow_nonneg h2πR k), ENNReal.ofReal_pow h2πR,
    ENNReal.ofReal_prod_of_nonneg fun l _ => norm_nonneg _]
  simp_rw [ofReal_norm]

/-- `|𝓕(∂^w psiDualBase_j)_{2^j}(ξ)| ≤ (8π)^k (∏_l ‖w_l‖) |𝓕 psiDual_j(ξ)|`: where
`𝓕 psiDual_j(ξ) ≠ 0`, `‖ξ‖ < 2^{j+2}` (`Rd.norm_lt_of_fourier_psiDual_ne_zero`), so
`‖2^{-j} ξ‖ < 4`. -/
theorem enorm_fourier_derivDualFamily_le {k : ℕ} (w : Fin k → V) (j : ℕ) (ξ : V) :
    ‖𝓕 (derivDualFamily w j) ξ‖ₑ ≤
      ENNReal.ofReal (8 * π) ^ k * (∏ l, ‖w l‖ₑ) * ‖𝓕 (psiDual (V := V) j) ξ‖ₑ := by
  rw [fourier_derivDualFamily, eNorm_mul]
  by_cases h : 𝓕 (psiDual (V := V) j) ξ = 0
  · rw [h, eNorm_zero, mul_zero, mul_zero]
  · rw [show (8 : ℝ) * π = 2 * π * 4 by ring]
    gcongr
    refine enorm_prod_inner_le w ?_
    have h1 := norm_lt_of_fourier_psiDual_ne_zero h
    rw [norm_two_pow_inv_smul, div_le_iff₀ (by positivity)]
    rw [pow_add] at h1
    norm_num at h1
    linarith

/-- **Overlap of a dual derivative family**:
`∑_j |𝓕(∂^w psiDualBase_j)_{2^j}(ξ)|² ≤ 4 ((8π)^k ∏_l ‖w_l‖)²` for every `ξ`, by
comparison with the synthesis kernels (`Rd.enorm_fourier_derivDualFamily_le`,
`Rd.tsum_fourier_psiDual_sq_le`). -/
theorem tsum_fourier_derivDualFamily_sq_le {k : ℕ} (w : Fin k → V) (ξ : V) :
    ∑' j, ‖𝓕 (derivDualFamily w j) ξ‖ₑ ^ 2 ≤ derivDualOverlap w :=
  calc ∑' j, ‖𝓕 (derivDualFamily w j) ξ‖ₑ ^ 2
      ≤ ∑' j, (ENNReal.ofReal (8 * π) ^ k * ∏ l, ‖w l‖ₑ) ^ 2 *
          ‖𝓕 (psiDual (V := V) j) ξ‖ₑ ^ 2 :=
        tsum_le_tsum fun j => by
          rw [← mul_pow]
          gcongr
          exact enorm_fourier_derivDualFamily_le w j ξ
    _ = (ENNReal.ofReal (8 * π) ^ k * ∏ l, ‖w l‖ₑ) ^ 2 *
          ∑' j, ‖𝓕 (psiDual (V := V) j) ξ‖ₑ ^ 2 := ENNReal.tsum_mul_left
    _ ≤ (ENNReal.ofReal (8 * π) ^ k * ∏ l, ‖w l‖ₑ) ^ 2 * 4 := by
        gcongr
        exact tsum_fourier_psiDual_sq_le ξ
    _ = derivDualOverlap w := by rw [derivDualOverlap, mul_comm]

/-- **The dual derivative families are Calderón–Zygmund families** with overlap
`4 ((8π)^k ∏_l ‖w_l‖)²` (`Rd.derivDualOverlap`) and Hörmander constant `4 H_{A^w}`,
`H_{A^w} = Rd.familyHormanderConst V (Rd.derivDualBound w)`. -/
theorem isCZFamily_derivDualFamily {k : ℕ} (w : Fin k → V) :
    IsCZFamily (derivDualFamily w) (derivDualOverlap w)
      (4 * familyHormanderConst V (derivDualBound w)) :=
  IsCZFamily.of_dilation (isUniformSchwartz_derivDualBase w)
    (tsum_fourier_derivDualFamily_sq_le w)

end Rd

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.Solenoidal
public import LeanPool.FastDynamo.Palomar.Velocity

/-!
# The Fourier symbol of the ideal induction operator on `L²_σ`

The library writes the ideal induction equation in the advective form
`∂ₜB = (B·∇)u − (u·∇)B`, with the stretching `(B·∇)u = ∇u · B` taken pointwise
(`literalStretchL2`) and the transport term tested against smooth fields; the Challenge statement
writes it in the divergence form `∂ₜB = curl (u × B)`, with
`curl (u × B)ᵢ = ∑ⱼ ∂ⱼ(uᵢBⱼ − uⱼBᵢ)` read on Fourier coefficients (`inductionRHS u 0`).  For the
divergence-free, Lipschitz velocity `u = mainLiteralVelocity` and a field `W ∈ L²_σ` the two agree
at every frequency `m` and component `i`:

  `((W·∇)u)^ᵢ(m) − 2πi ∑ⱼ mⱼ (uⱼWᵢ)^(m) = 2πi ∑ⱼ mⱼ ((uᵢWⱼ)^(m) − (uⱼWᵢ)^(m))`,

that is, `((W·∇)u)^ᵢ(m) = 2πi ∑ⱼ mⱼ (uᵢWⱼ)^(m)` (`mFourierCoeff_literalStretchL2_main`).

## The proof

Both sides are continuous linear functionals of `W ∈ L²` (`idealStretchDefect`).  On the
character field `W = e_n eⱼ`, integration by parts against the character (the velocity is
Lipschitz with everywhere differentiable lift) gives
`((e_n eⱼ·∇)u)^ᵢ(m) = (∂ⱼuᵢ)^(m − n) = 2πi (m − n)ⱼ ûᵢ(m − n)`, while
`2πi ∑ₖ mₖ (uᵢ (e_n eⱼ)ₖ)^(m) = 2πi mⱼ ûᵢ(m − n)`; the defect is `−2πi nⱼ ûᵢ(m − n)`
(`idealStretchDefect_literalSingleL2`).  On a Fourier partial sum of `W` the defect is therefore
`−2πi ∑ₙ ûᵢ(m − n) ∑ⱼ nⱼ Ŵⱼ(n)`, which vanishes when `div W = 0`; the partial sums tend to `W`
in `L²` (`tendsto_toLp_literalTrigField`), so the defect of `W` vanishes.  The condition
`div W = 0` is needed: for a general `W ∈ L²` the two sides differ by `uᵢ div W`.

## Contents

* `mFourierCoeff_mFourier_mul` — multiplication by a character shifts the coefficients.
* `mFourierCoeff_literalComponentMul` — the coefficients of `uₐ W`.
* `idealStretchDefect`, `idealStretchDefect_apply`, `idealStretchDefect_literalSingleL2`,
  `idealStretchDefect_eq_zero` — the defect functional.
* `mFourierCoeff_literalStretchL2_main` — `((W·∇)u)^ᵢ(m) = 2πi ∑ⱼ mⱼ (uᵢWⱼ)^(m)` on `L²_σ`.
* `idealInductionRHSCLM`, `idealInductionRHSCLM_apply` — `inductionRHS u 0 · m i` is a continuous
  linear functional on `L2`.
* `mFourierCoeff_literalStretchL2_sub_eq_inductionRHS` — **I1, the symbol identity**: the
  advective right-hand side of the library equals `inductionRHS u 0` on `L²_σ`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus Filter Topology HorizontalMode
open ScaleFamily.TorusCellPlacement

/-! ## Characters -/

/-- Multiplication by the character `e_n` shifts the Fourier coefficients by `n`. -/
theorem mFourierCoeff_mFourier_mul (n m : Fin 3 → ℤ) (g : T3 → ℂ) :
    mFourierCoeff (fun x ↦ mFourier n x * g x) m = mFourierCoeff g (m - n) := by
  simp only [mFourierCoeff, smul_eq_mul]
  congr 1
  funext x
  rw [show -(m - n) = -m + n by abel, mFourier_add]
  ring

/-! ## The velocity of the theorem -/

/-- The stretching operator at the theorem's velocity is the pointwise stretching. -/
theorem literalStretchL2_main_coe_ae (B : L2) :
    (literalStretchL2 mainLiteralVelocity B : T3 → C3) =ᵐ[volume]
      literalStretch mainLiteralVelocity (B : T3 → C3) :=
  literalStretchL2_coe_ae globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed mainParameterChoice.tau
    mainParameterChoice.tau_nonneg B

/-- The partial derivatives of the components of the theorem's velocity are the entries of
`literalFDeriv`. -/
theorem torusGradient_mainLiteralVelocity (i j : Fin 3) (x : T3) :
    torusGradient (fun y ↦ ((mainLiteralVelocity y i : ℝ) : ℂ)) x j =
      ((literalFDeriv mainLiteralVelocity x (EuclideanSpace.single j 1) i : ℝ) : ℂ) :=
  torusGradient_literalVelocityCoord globalSeedInterface.smoothingWidth
    mainParameterChoice.placement globalSeedInterface.angularSpeed
    globalSeedInterface.axialSpeed mainParameterChoice.tau mainParameterChoice.tau_nonneg i j x

/-- **Integration by parts for the theorem's velocity**: `(∂ⱼuᵢ)^(m) = 2πi mⱼ ûᵢ(m)`. -/
theorem mFourierCoeff_torusGradient_mainLiteralVelocity (m : Fin 3 → ℤ) (i j : Fin 3) :
    mFourierCoeff (fun x ↦ torusGradient (fun y ↦ ((mainLiteralVelocity y i : ℝ) : ℂ)) x j) m =
      2 * Real.pi * Complex.I * (m j : ℂ) *
        mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ)) m := by
  rw [mFourierCoeff_eq_integral_conj_mFourier_mul, mFourierCoeff_eq_integral_conj_mFourier_mul]
  exact integral_conj_mFourier_mul_torusGradient_literalVelocityCoord
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed mainParameterChoice.tau
    mainParameterChoice.tau_nonneg
    (lipschitzWith_mainLiteralVelocity.comp lipschitzWith_literalTorusPoint) m i j

/-- The coefficients of `uₐ W`, for any proof of continuity of the velocity. -/
theorem mFourierCoeff_literalComponentMul (hu : Continuous mainLiteralVelocity) (a : Fin 3)
    (W : L2) (m : Fin 3 → ℤ) (k : Fin 3) :
    mFourierCoeff (fun x ↦ (literalComponentMul mainLiteralVelocity hu a W : L2) x k) m =
      mFourierCoeff (fun x ↦ ((mainLiteralVelocity x a : ℝ) : ℂ) * W x k) m := by
  refine mFourierCoeff_congr_ae ?_ m
  filter_upwards [literalComponentMul_coe_ae mainLiteralVelocity hu a W] with x hx
  rw [hx, PiLp.smul_apply, smul_eq_mul]

/-! ## The defect functional -/

/-- The defect `W ↦ ((W·∇)u)^ᵢ(m) − 2πi ∑ₖ mₖ (uᵢWₖ)^(m)` of the symbol identity, as a
continuous linear functional on `L2`. -/
def idealStretchDefect (m : Fin 3 → ℤ) (i : Fin 3) : L2 →L[ℂ] ℂ :=
  (l2Coeff m i).comp (literalStretchL2 mainLiteralVelocity) -
    (2 * Real.pi * Complex.I : ℂ) • ∑ k : Fin 3, (m k : ℂ) •
      (l2Coeff m k).comp
        (literalComponentMul mainLiteralVelocity lipschitzWith_mainLiteralVelocity.continuous i)

/-- Evaluation of the defect functional. -/
theorem idealStretchDefect_apply (m : Fin 3 → ℤ) (i : Fin 3) (W : L2) :
    idealStretchDefect m i W =
      mFourierCoeff (fun x ↦ (literalStretchL2 mainLiteralVelocity W : L2) x i) m -
        2 * Real.pi * Complex.I * ∑ k : Fin 3, (m k : ℂ) *
          mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ) * W x k) m := by
  simp only [idealStretchDefect, sub_apply, smul_apply,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply, l2Coeff_apply,
    smul_eq_mul, mFourierCoeff_literalComponentMul]

/-- **The defect on a character field**: for `W = e_n eⱼ` the defect is `−2πi nⱼ ûᵢ(m − n)`. -/
theorem idealStretchDefect_literalSingleL2 (m n : Fin 3 → ℤ) (i j : Fin 3) :
    idealStretchDefect m i (literalSingleL2 j (flatTorus3FourierBasis n)) =
      -(2 * Real.pi * Complex.I * (n j : ℂ) *
        mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ)) (m - n)) := by
  set W : L2 := literalSingleL2 j (flatTorus3FourierBasis n)
  have hW : ∀ᵐ x ∂(volume : Measure T3), W x = mFourier n x • EuclideanSpace.single j (1 : ℂ) := by
    filter_upwards [literalSingleL2_coe_ae j (flatTorus3FourierBasis n),
      flatTorus3FourierBasis_coe_ae n] with x h1 h2
    rw [h1, h2]
  -- the stretching term
  have hS : mFourierCoeff (fun x ↦ (literalStretchL2 mainLiteralVelocity W : L2) x i) m =
      2 * Real.pi * Complex.I * ((m - n) j : ℂ) *
        mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ)) (m - n) := by
    rw [← mFourierCoeff_torusGradient_mainLiteralVelocity, ← mFourierCoeff_mFourier_mul n]
    refine mFourierCoeff_congr_ae ?_ m
    filter_upwards [literalStretchL2_main_coe_ae W, hW] with x h1 h2
    rw [h1, literalStretch, h2, r3Complexify_apply, torusGradient_mainLiteralVelocity]
    simp [PiLp.single_apply, mul_comm]
  -- the transport-type term
  have hT : ∀ k : Fin 3,
      mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ) * W x k) m =
        if k = j then mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ)) (m - n)
        else 0 := by
    intro k
    split_ifs with hk
    · rw [← mFourierCoeff_mFourier_mul n]
      refine mFourierCoeff_congr_ae ?_ m
      filter_upwards [hW] with x hx
      simp [hx, hk, mul_comm]
    · rw [← mFourierCoeff_fun_zero (E := ℂ) m]
      refine mFourierCoeff_congr_ae ?_ m
      filter_upwards [hW] with x hx
      simp [hx, hk]
  rw [idealStretchDefect_apply, hS]
  simp only [hT, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.sub_apply]
  push_cast
  ring

/-- **The defect vanishes on `L²_σ`.** -/
theorem idealStretchDefect_eq_zero (m : Fin 3 → ℤ) (i : Fin 3) {W : L2} (hW : W ∈ L2σ) :
    idealStretchDefect m i W = 0 := by
  have hdiv := (mem_L2σ_iff W).1 hW
  have h0 : ∀ F : Finset (Fin 3 → ℤ), idealStretchDefect m i
      (ContinuousMap.toLp 2 (volume : Measure T3) ℂ
        (literalTrigField F (literalFourierCoeff W))) = 0 := by
    intro F
    rw [toLp_literalTrigField]
    simp only [map_sum, map_smul, smul_eq_mul, idealStretchDefect_literalSingleL2,
      literalFourierCoeff_eq_mFourierCoeff]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    have h := hdiv n
    calc (∑ k : Fin 3, mFourierCoeff (fun x ↦ W x k) n *
          -(2 * Real.pi * Complex.I * (n k : ℂ) *
            mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ)) (m - n)))
        = -(2 * Real.pi * Complex.I *
            mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ)) (m - n)) *
          ∑ k : Fin 3, (n k : ℂ) * mFourierCoeff (fun x ↦ W x k) n := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          ring
      _ = 0 := by rw [h, mul_zero]
  have hlim := ((idealStretchDefect m i).continuous.tendsto W).comp
    (tendsto_toLp_literalTrigField W)
  refine tendsto_nhds_unique hlim ?_
  simp only [Function.comp_def, h0]
  exact tendsto_const_nhds

/-- **The stretching term on `L²_σ`**: `((W·∇)u)^ᵢ(m) = 2πi ∑ₖ mₖ (uᵢWₖ)^(m)` for every
`W ∈ L²_σ`, at the theorem's velocity. -/
theorem mFourierCoeff_literalStretchL2_main (m : Fin 3 → ℤ) (i : Fin 3) {W : L2}
    (hW : W ∈ L2σ) :
    mFourierCoeff (fun x ↦ (literalStretchL2 mainLiteralVelocity W : L2) x i) m =
      2 * Real.pi * Complex.I * ∑ k : Fin 3, (m k : ℂ) *
        mFourierCoeff (fun x ↦ ((mainLiteralVelocity x i : ℝ) : ℂ) * W x k) m := by
  have h := idealStretchDefect_eq_zero m i hW
  rw [idealStretchDefect_apply] at h
  exact sub_eq_zero.1 h

/-! ## The curl form as a continuous functional -/

/-- `B ↦ inductionRHS u 0 B m i` at the theorem's velocity, as a continuous linear functional on
`L2`. -/
def idealInductionRHSCLM (m : Fin 3 → ℤ) (i : Fin 3) : L2 →L[ℂ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ) • ∑ j : Fin 3, (m j : ℂ) •
    ((l2Coeff m j).comp
        (literalComponentMul mainLiteralVelocity lipschitzWith_mainLiteralVelocity.continuous i) -
      (l2Coeff m i).comp
        (literalComponentMul mainLiteralVelocity lipschitzWith_mainLiteralVelocity.continuous j))

/-- Evaluation of `idealInductionRHSCLM`: it is the Challenge's `inductionRHS u 0`. -/
theorem idealInductionRHSCLM_apply (m : Fin 3 → ℤ) (i : Fin 3) (B : L2) :
    idealInductionRHSCLM m i B = inductionRHS mainLiteralVelocity 0 (B : T3 → C3) m i := by
  simp only [idealInductionRHSCLM, inductionRHS, smul_apply,
    FunLike.coe_sum, Finset.sum_apply, sub_apply,
    ContinuousLinearMap.comp_apply, l2Coeff_apply, smul_eq_mul, mFourierCoeff_literalComponentMul,
    Complex.ofReal_zero, mul_zero, zero_mul, sub_zero]

/-- **I1, the symbol identity.**  For `W ∈ L²_σ`, the right-hand side of the library's advective
form of the ideal induction equation, tested with the character `e_m eᵢ`,
`((W·∇)u)^ᵢ(m) − 2πi ∑ⱼ mⱼ (uⱼWᵢ)^(m)`, is the Challenge's divergence form
`inductionRHS u 0 W m i`, at the theorem's velocity. -/
theorem mFourierCoeff_literalStretchL2_sub_eq_inductionRHS (m : Fin 3 → ℤ) (i : Fin 3) {W : L2}
    (hW : W ∈ L2σ) :
    mFourierCoeff (fun x ↦ (literalStretchL2 mainLiteralVelocity W : L2) x i) m -
        ∑ j : Fin 3, 2 * Real.pi * Complex.I * (m j : ℂ) *
          mFourierCoeff (fun x ↦ ((mainLiteralVelocity x j : ℝ) : ℂ) * W x i) m =
      inductionRHS mainLiteralVelocity 0 (W : T3 → C3) m i := by
  rw [mFourierCoeff_literalStretchL2_main m i hW, inductionRHS]
  simp only [Fin.sum_univ_three, Complex.ofReal_zero]
  ring

end

end FastDynamo

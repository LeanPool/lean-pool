/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFactors.Besov

/-!
# Coarse-graining support:
Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube
.CenteredFactors.LocalAlpha

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

/-!
# Exact small-cube centered factors: local alpha comparison
-/

noncomputable section

open scoped ENNReal

private theorem centeredGeometricProductHeightBound
    {hessian gradient firstProduct secondProduct front theta sigma height depth scale : ℝ}
    (hhessian : 0 ≤ hessian) (hgradient : 0 ≤ gradient)
    (hfront : 0 ≤ front) (htheta : 0 ≤ theta) (hsigma : 0 ≤ sigma)
    (hheight : height ≤ depth)
    (hfirst : Real.rpow (3 : ℝ) (-depth) * firstProduct ≤
      Real.rpow (3 : ℝ) (-sigma * depth) * theta)
    (hsecond : Real.rpow (3 : ℝ) (-depth) * secondProduct ≤
      Real.rpow (3 : ℝ) (-sigma * depth) * theta)
    (hscale : (hessian + gradient) * Real.rpow (3 : ℝ) scale ≤ front) :
    hessian * Real.rpow (3 : ℝ) (scale - depth) * firstProduct +
        gradient * Real.rpow (3 : ℝ) (scale - depth) * secondProduct ≤
      front * (Real.rpow (3 : ℝ) (-sigma * height) * theta) := by
  have hpower : 0 ≤ Real.rpow (3 : ℝ) scale := Real.rpow_nonneg (by norm_num) _
  have hdepth : 0 ≤ Real.rpow (3 : ℝ) (-sigma * depth) * theta :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) htheta
  have hexponent : -sigma * depth ≤ -sigma * height :=
    mul_le_mul_of_nonpos_left hheight (neg_nonpos.mpr hsigma)
  have hheightPower := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 3) hexponent
  have hpowerSplit : Real.rpow (3 : ℝ) (scale - depth) =
      Real.rpow (3 : ℝ) scale * Real.rpow (3 : ℝ) (-depth) := by
    rw [sub_eq_add_neg]
    exact Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
  calc
    hessian * Real.rpow (3 : ℝ) (scale - depth) * firstProduct +
        gradient * Real.rpow (3 : ℝ) (scale - depth) * secondProduct =
      (hessian * Real.rpow (3 : ℝ) scale) *
          (Real.rpow (3 : ℝ) (-depth) * firstProduct) +
        (gradient * Real.rpow (3 : ℝ) scale) *
          (Real.rpow (3 : ℝ) (-depth) * secondProduct) := by
            rw [hpowerSplit]
            ring
    _ ≤ (hessian * Real.rpow (3 : ℝ) scale) *
          (Real.rpow (3 : ℝ) (-sigma * depth) * theta) +
        (gradient * Real.rpow (3 : ℝ) scale) *
          (Real.rpow (3 : ℝ) (-sigma * depth) * theta) :=
            add_le_add (mul_le_mul_of_nonneg_left hfirst (mul_nonneg hhessian hpower))
              (mul_le_mul_of_nonneg_left hsecond (mul_nonneg hgradient hpower))
    _ = ((hessian + gradient) * Real.rpow (3 : ℝ) scale) *
        (Real.rpow (3 : ℝ) (-sigma * depth) * theta) := by ring
    _ ≤ front * (Real.rpow (3 : ℝ) (-sigma * depth) * theta) :=
      mul_le_mul_of_nonneg_right hscale hdepth
    _ ≤ front * (Real.rpow (3 : ℝ) (-sigma * height) * theta) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hheightPower htheta) hfront

/-- The Besov/cutoff-product part of the centered exact coefficient localizes
to the parent `Alpha` coefficient once the two Besov scalar fronts are absorbed
into the working constant.  This is the second substitution line in the LaTeX
centered single-cube estimate: the Hessian and gradient cutoff gains are
estimated separately, but both descendant ellipticity products are compared to
the same parent theta term. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_localAcirc_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s t CeffLocal CeffWork : ℝ} {k j : ℕ} {ρ₁ ρ₂ lam Lam : ℝ}
    {hheight : ℝ → ℝ → ℝ}
    (hCeffLocal : 0 ≤ CeffLocal) (hCeffWork : 0 ≤ CeffWork)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j)
    (hscale :
      (coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
          Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ)) :
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂)
          CeffLocal) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
  let H : ℝ := coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal
  let G : ℝ := coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  let Pone : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
  let Psub : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
  let Theta : ℝ := Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let depthTheta : ℝ :=
    Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) * Theta
  let front : ℝ := CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hsub :=
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_localAcirc_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hs1 hR hchoice hlt hjk
  have hprod_one :
      Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone ≤ depthTheta := by
    simpa [Pone, Theta, depthTheta] using
      (faithful_centered_descendant_product_one_le_parent_theta
        (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)
  have hprod_sub :
      Real.rpow (3 : ℝ) (-(j : ℝ)) * Psub ≤ depthTheta := by
    simpa [Psub, Theta, depthTheta] using
      (faithful_centered_descendant_product_le_parent_theta
        (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)
  have hTheta_nonneg : 0 ≤ Theta := by
    dsimp [Theta]
    exact Real.rpow_nonneg (thetaRatio_nonneg Q s t a hs.le ht.le) _
  have hH_nonneg : 0 ≤ H := by
    simpa [H] using
      (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal hs)
  have hG_nonneg : 0 ≤ G := by
    simpa [G] using
      (coarseCaccioppoliCenteredBesovGradientFront_nonneg d hCeffLocal hs hs1)
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
  have hfront_nonneg : 0 ≤ front := by
    dsimp [front]
    exact mul_nonneg (div_nonneg hCeffWork hden_nonneg)
      (coarseCaccioppoliGapInv_nonneg hlt)
  calc
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂)
          CeffLocal)
        ≤ H * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
          G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
            simpa [H, G, Pone, Psub] using hsub
    _ ≤ front *
        (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
          Theta) := by
          exact centeredGeometricProductHeightBound
            hH_nonneg hG_nonneg hfront_nonneg hTheta_nonneg
            (coarseCaccioppoli_sigma_pos hst).le hheight_le_j hprod_one hprod_sub
            (by simpa [H, G, front] using hscale)
    _ = CeffWork / (s * (1 - s)) *
        coarseCaccioppoliGapInv ρ₁ ρ₂ *
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
          dsimp [front, Theta]
          ring
    _ = coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
          rfl

/-- The average and Besov factor-bound pieces of the centered exact coefficient
localize together to one parent `Alpha` coefficient.  This is the combined
budget line in the LaTeX proof: the average front, Hessian front, and gradient
front are absorbed by a single work-constant inequality before applying the
height monotonicity of `Alpha`. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredFactorBounds_localAcirc_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s t CeffLocal CeffWork : ℝ} {k j : ℕ} {ρ₁ ρ₂ lam Lam : ℝ}
    {hheight : ℝ → ℝ → ℝ}
    (hCeffLocal : 0 ≤ CeffLocal) (hCeffWork : 0 ≤ CeffWork)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j)
    (hscale :
      (coarseCaccioppoliCenteredAverageFront d s CeffLocal +
          coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
          Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ)) :
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) CeffLocal +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂)
          CeffLocal) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
  let A : ℝ := coarseCaccioppoliCenteredAverageFront d s CeffLocal
  let H : ℝ := coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal
  let G : ℝ := coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  let Pone : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
  let Psub : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
  let Theta : ℝ := Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let depthTheta : ℝ :=
    Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) * Theta
  let front : ℝ := CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have havg_sub :=
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hR hchoice hlt
  have hbesov_sub :=
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_localAcirc_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hs1 hR hchoice hlt hjk
  have hprod_one :
      Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone ≤ depthTheta := by
    simpa [Pone, Theta, depthTheta] using
      (faithful_centered_descendant_product_one_le_parent_theta
        (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)
  have hprod_sub :
      Real.rpow (3 : ℝ) (-(j : ℝ)) * Psub ≤ depthTheta := by
    simpa [Psub, Theta, depthTheta] using
      (faithful_centered_descendant_product_le_parent_theta
        (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using
      (coarseCaccioppoliCenteredAverageFront_nonneg d hCeffLocal hs)
  have hH_nonneg : 0 ≤ H := by
    simpa [H] using
      (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal hs)
  have hG_nonneg : 0 ≤ G := by
    simpa [G] using
      (coarseCaccioppoliCenteredBesovGradientFront_nonneg d hCeffLocal hs hs1)
  have hTheta_nonneg : 0 ≤ Theta := by
    dsimp [Theta]
    exact Real.rpow_nonneg (thetaRatio_nonneg Q s t a hs.le ht.le) _
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
  have hfront_nonneg : 0 ≤ front := by
    dsimp [front]
    exact mul_nonneg (div_nonneg hCeffWork hden_nonneg)
      (coarseCaccioppoliGapInv_nonneg hlt)
  have havg_rhs_eq :
      ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        Pone =
        A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone := by
    dsimp [A, coarseCaccioppoliCenteredAverageFront]
    ring
  have hfactor_sub :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) CeffLocal +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂)
            CeffLocal) ≤
        A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub) := by
    exact add_le_add (by simpa [Pone] using le_trans havg_sub havg_rhs_eq.le)
      (by simpa [H, G, Pone, Psub] using hbesov_sub)
  calc
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) CeffLocal +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂)
          CeffLocal)
        ≤ A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub) := hfactor_sub
    _ ≤ front *
        (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
          Theta) := by
          calc
            A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
                (H * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
                  G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub) =
              (A + H) * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
                G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by ring
            _ ≤ _ := by
              exact centeredGeometricProductHeightBound
                (add_nonneg hA_nonneg hH_nonneg) hG_nonneg hfront_nonneg hTheta_nonneg
                (coarseCaccioppoli_sigma_pos hst).le hheight_le_j hprod_one hprod_sub
                (by simpa [A, H, G, front] using hscale)
    _ = CeffWork / (s * (1 - s)) *
        coarseCaccioppoliGapInv ρ₁ ρ₂ *
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
          dsimp [front, Theta]
          ring
    _ = coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
          rfl

end

end HCPolySupport

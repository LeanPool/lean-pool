/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessAmplitudeLawFree
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitFrozenFrameDirichletBound
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.RootCertificateAndFoldAbsorption

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessHeadBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (ii), part one: the scheduled head, dominated at an explicit constant

the `hhead` premise binder asks, for every `J` in the outer bracket, for

```
scheduledRateHead d
    √(hsAffineFactor S⁻¹ s ‖S‖) Cdual
    ((3 ^ b · foldedAnchoredFrameConstant …) ^ 2 · Kenergy) hardyConstant
  ≤ ENNReal.ofReal (C₀ s ρ Rad) .
```

This module discharges it at the **explicit** constant
`frozenWitnessHeadConstant`, through real-valued bridge
`scheduledRateHead_le_ofReal` and three factor bounds:

* the `outputFactor_le_gaugeOutputLawFree_mul_fold` premise — the ρ-paid output
  factor, with its eccentricity fold;
* the `three_rpow_mul_foldedAnchoredFrameConstant_le` premise — the flux split, whose
  square root needs the frame constant to be **nonnegative**; no lemma
  said so, and `foldedAnchoredFrameConstant_nonneg` supplies it here;
* any dominating `KenergyBound` — supplied from the modules named above at the call site.

The constant produced still carries `abar`, through the output factor's fold.
That is deliberate and is what that module permits: `C₀` is an *internal*
parameter, chosen after `abar` is in scope; the hole's `C₀`, which must precede
`∀ g`, is reached in the next module by the `constant_and_eccentricity_absorbed` premise, which
moves the eccentricity power into
`pEcc` and the `Lg`-class residual into `Lg`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The frame constant is nonnegative -/

/-- **The folded anchored frame constant is nonnegative.**  Needed to split
`√(X² · Kenergy)` as `X · √Kenergy`; no declaration stated it. -/
theorem foldedAnchoredFrameConstant_nonneg (d : ℕ) [NeZero d]
    {g kappaRate s Rad cnorm delta Jr : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hs₀ : s ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ))
    (hRad : 0 ≤ Rad) :
    0 ≤ foldedAnchoredFrameConstant d g kappaRate s
      (coarseFluxResponseConstant d) Rad cnorm delta Jr := by
  have hb0 : 0 < responseWindowOrder g := responseWindowOrder_pos hg
  have hbs : responseWindowOrder g < s := responseWindowOrder_lt_printOrder hg hs₀
  have hs : 0 < s := hb0.trans hbs
  have hA : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-responseWindowOrder g) :=
    Real.rpow_nonneg (by norm_num) _
  have hB : (0 : ℝ) ≤ Real.rpow (2 * Rad) (s - responseWindowOrder g) :=
    Real.rpow_nonneg (by linarith only [hRad]) _
  have hflux0 : (0 : ℝ) ≤ coarseFluxResponseConstant d := by
    rw [coarseFluxResponseConstant]
    exact mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))
  have hD : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hnorm0 : (0 : ℝ) ≤
      Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) := by
    rw [Book.Ch03.constantCoeffMatrixNormHalf]
    exact Real.rpow_nonneg (Book.Ch02.matrixNorm_nonneg _) _
  have hgap0 := responseOneFromTwoGapFactor_nonneg hb0 hbs
  have hresp0 := foldedAnchoredResponseConstant_nonneg d g kappaRate delta Jr
  have hmax0 : (0 : ℝ) ≤ max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)) :=
    le_trans zero_le_one (le_max_left _ _)
  rw [foldedAnchoredFrameConstant]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg hA hB) hflux0) hD) hnorm0) hgap0) (mul_nonneg hresp0 hmax0)

/-- The whole flux head of the frame constant is nonnegative. -/
theorem three_rpow_mul_foldedAnchoredFrameConstant_nonneg (d : ℕ) [NeZero d]
    {g kappaRate s Rad cnorm delta Jr : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hs₀ : s ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ))
    (hRad : 0 ≤ Rad) :
    0 ≤ Real.rpow (3 : ℝ) (responseWindowOrder g) *
      foldedAnchoredFrameConstant d g kappaRate s
        (coarseFluxResponseConstant d) Rad cnorm delta Jr :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (foldedAnchoredFrameConstant_nonneg d hg hs₀ hRad)

/-! ## The head constant -/

/-- The constant at which the `hhead` premise is discharged.  Its only `abar`
dependence is the output factor's eccentricity fold. -/
@[expose]
noncomputable def frozenWitnessHeadConstant (d : ℕ) [NeZero d]
    (g kappaRate s rho Rad cnorm Cdual hardyReal KenergyBound : ℝ)
    (abar : Mat d) : ℝ :=
  gaugeOutputLawFree d s rho *
        eccentricityFoldFactor abar (((d : ℝ) + 1) / 2) * Cdual *
    (2 * ((fractionalDualToBesovConstant d).toReal *
      (fluxC0Factor d s Rad cnorm * fluxLgFactor d g kappaRate *
          Real.sqrt KenergyBound *
        Real.sqrt hardyReal)))

/-- Monotonicity of the scheduled head's real form in its two variable
factors. -/
theorem headProduct_mono {out out' Cdual Cb sq sq' hr : ℝ}
    (hout : out ≤ out') (hsq : sq ≤ sq')
    (hout0 : 0 ≤ out) (hCdual0 : 0 ≤ Cdual) (hCb0 : 0 ≤ Cb)
    (hsq0 : 0 ≤ sq) (hhr0 : 0 ≤ hr) :
    out * Cdual * (2 * (Cb * (sq * hr))) ≤
      out' * Cdual * (2 * (Cb * (sq' * hr))) := by
  have hout'0 : 0 ≤ out' := hout0.trans hout
  have h1 : out * Cdual ≤ out' * Cdual :=
    mul_le_mul_of_nonneg_right hout hCdual0
  have h2 : sq * hr ≤ sq' * hr := mul_le_mul_of_nonneg_right hsq hhr0
  have h3 : Cb * (sq * hr) ≤ Cb * (sq' * hr) :=
    mul_le_mul_of_nonneg_left h2 hCb0
  have h4 : 2 * (Cb * (sq * hr)) ≤ 2 * (Cb * (sq' * hr)) := by
    linarith only [h3]
  exact mul_le_mul h1 h4
    (mul_nonneg (by norm_num) (mul_nonneg hCb0 (mul_nonneg hsq0 hhr0)))
    (mul_nonneg hout'0 hCdual0)

/-! ## The head domination -/

/-- **(ii), part one.**  the `hhead` premise at the explicit
`frozenWitnessHeadConstant`. -/
theorem frozenWitnessScheduledHead_le [NeZero d]
    {abar : Mat d} {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    {g kappaRate s rho Rad cnorm delta Jr Cdual hardyReal
      Kenergy KenergyBound : ℝ}
    {hardyConstant : ℝ≥0∞}
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hs₀ : s ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ))
    (hU : U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
      openCubeSet (originCube d j))
    (hUsub : U ⊆ ellipsoid abar 1)
    (hinner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad)
    (hRadpos : 0 < Rad)
    (hJr : 0 ≤ Jr) (hJB : (3 : ℝ) ^ Jr ≤ 1 + 3 * (2 * Rad))
    (hdelta1 : Real.sqrt delta ≤ 1)
    (hCdual : 0 ≤ Cdual) (hhardyReal : 0 ≤ hardyReal)
    (hhardy : hardyConstant ≤ ENNReal.ofReal hardyReal)
    (hK0 : 0 ≤ Kenergy) (hKle : Kenergy ≤ KenergyBound) :
    scheduledRateHead d
        (Real.sqrt (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
          ‖matSqrt (symmPart abar)‖)) Cdual
        ((Real.rpow (3 : ℝ) (responseWindowOrder g) *
            foldedAnchoredFrameConstant d g kappaRate s
              (coarseFluxResponseConstant d) Rad cnorm delta Jr) ^ 2 *
          Kenergy)
        hardyConstant ≤
      ENNReal.ofReal (frozenWitnessHeadConstant d g kappaRate s rho Rad cnorm
        Cdual hardyReal KenergyBound abar) := by
  have hb0 : 0 < responseWindowOrder g := responseWindowOrder_pos hg
  have hbs : responseWindowOrder g < s := responseWindowOrder_lt_printOrder hg hs₀
  have hs : 0 < s := hb0.trans hbs
  have hsHalf : s < 1 / 2 := hs₀.2
  have hX0 := three_rpow_mul_foldedAnchoredFrameConstant_nonneg (d := d)
    (kappaRate := kappaRate) (cnorm := cnorm) (delta := delta) (Jr := Jr)
    hg hs₀ hRadpos.le
  have hXle := three_rpow_mul_foldedAnchoredFrameConstant_le (d := d)
    (cnorm := cnorm) hg hkappa hs₀ hRadpos hJr hJB hdelta1
  have hKflux0 : (0 : ℝ) ≤
      (Real.rpow (3 : ℝ) (responseWindowOrder g) *
        foldedAnchoredFrameConstant d g kappaRate s
          (coarseFluxResponseConstant d) Rad cnorm delta Jr) ^ 2 * Kenergy :=
    mul_nonneg (sq_nonneg _) hK0
  refine le_trans (scheduledRateHead_le_ofReal d (Real.sqrt_nonneg _) hCdual
    hKflux0 hhardyReal hhardy) (ENNReal.ofReal_le_ofReal ?_)
  have hout := outputFactor_le_gaugeOutputLawFree_mul_fold hS hs hsHalf hU
    hUsub hinner hsandwich
  have hsq : Real.sqrt
        ((Real.rpow (3 : ℝ) (responseWindowOrder g) *
          foldedAnchoredFrameConstant d g kappaRate s
            (coarseFluxResponseConstant d) Rad cnorm delta Jr) ^ 2 *
          Kenergy) ≤
      fluxC0Factor d s Rad cnorm * fluxLgFactor d g kappaRate *
        Real.sqrt KenergyBound := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hX0]
    exact mul_le_mul hXle (Real.sqrt_le_sqrt hKle) (Real.sqrt_nonneg _)
      (hX0.trans hXle)
  exact headProduct_mono hout hsq (Real.sqrt_nonneg _) hCdual
    ENNReal.toReal_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

end RowSupply
end HighContrast
end HCPolySupport

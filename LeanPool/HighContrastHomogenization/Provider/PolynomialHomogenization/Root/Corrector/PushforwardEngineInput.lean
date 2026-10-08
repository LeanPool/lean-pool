/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardGaugeTranslation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardEngineInput

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The engine's Liouville input at a real translation

Clause (1) of the stationary corrector family clause — integer stationarity of the pushforward
family —
is one application of the translated-gradient identification engine at the real
translation `matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z)`.  The
engine's free translation binder accepts it; what has to be produced is its
Liouville input at the *translated* sample.

This module reduces that input to a single named statement: that the Liouville
class transports along a translation by an arbitrary real vector.  Everything
gauge-theoretic is discharged here by the real-vector conjugation.

**The `0 < theta` binder is necessary.**  Quantifying `theta` over all of `ℝ`
makes the statement **false**:
take `b` any elliptic field, `v = 0`, `Dv = 0`, `theta = -1` and `c = 1`.  The
hypothesis holds — the growth row reads `r ^ 0 * ‖0‖ → 0` — while the conclusion
requires `r ^ 0 * ‖-1‖ = 1 → 0`.  The same failure occurs for every
`theta ≤ -1`.  The defect is exactly the additive recentring: the growth row is
scale-invariant at `theta = -1`, so a nonzero constant is not absorbed.  The
`0 < theta` binder below repairs it, is what the printed Liouville class
carries (`ϑ ∈ (0,1)`), and is supplied by the consumer at
`rootCorrectorGrowth = 1/2`;
`engine_liouville_input_of_realTranslate` carries the same binder.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- **P4, as a named residue.**  The Liouville class transports along a
translation by an arbitrary real vector, the coefficient field translating with
it and an additive constant absorbing the affine part.  The available statements —
`memLiouvilleClass_affineAdd_of_cubeGrowth` and
`memLiouvilleClass_realTranslate_subConst` — give the integer case bundled
with a growth row; this is the bare translation.

The `0 < theta` binder is necessary: without it the statement is false
for the additive recentring at every `theta ≤ -1`. -/
@[expose]
def RealTranslateLiouville (d : ℕ) : Prop :=
  ∀ (b : CoeffField d) (theta : ℝ), 0 < theta →
    ∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d) (t : Vec d) (c : ℝ),
      MemLiouvilleClass b theta v Dv →
        MemLiouvilleClass (fun y ↦ b (y + t)) theta
          (fun y ↦ v (y + t) - c) (fun y ↦ Dv (y + t))

/-- The translated normalized-gauge coefficient is locally uniformly
elliptic. -/
theorem isAELocallyUniformlyElliptic_gaugeCoeff_translate [NeZero d]
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (z : Fin d → ℤ) :
    IsAELocallyUniformlyElliptic
      (fun y ↦ gaugeCoeff a abar hS
        (y + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z))) :=
  (isAELocallyUniformlyElliptic_gaugeCoeff (translateCoeff z a) abar hS).congr
    (gaugeCoeff_translateCoeff_ae a abar hS z)

/-- **Clause (1)'s engine input, from the single residue.**  On the translated
sample the normalized-gauge Liouville membership needed by the
translated-gradient identification engine follows from the untranslated one,
with no hypothesis beyond `RealTranslateLiouville`. -/
theorem engine_liouville_input_of_realTranslate [NeZero d]
    (hT : RealTranslateLiouville d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (G : NormalizedLocalH1Carrier d) (e : Vec d) {theta : ℝ} (htheta : 0 < theta)
    (hLiou : MemLiouvilleClass (gaugeCoeff a abar hS) theta
      (fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
        G.globalValueRepresentative y)
      (fun y ↦ matVecMul (gaugeRoot abar) e +
        G.globalGradientRepresentative y))
    (z : Fin d → ℤ) :
    MemLiouvilleClass (gaugeCoeff (translateCoeff z a) abar hS) theta
      (fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
        G.globalValueRepresentative
          (y + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z)))
      (fun y ↦ matVecMul (gaugeRoot abar) e +
        G.globalGradientRepresentative
          (y + matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z))) := by
  set t : Vec d :=
    matVecMul (gaugeRoot abar)⁻¹ (Source.AKL.intTranslation z) with ht
  set w : Vec d := matVecMul (gaugeRoot abar) e with hw
  have hdot : ∀ y : Vec d, vecDot w (y + t) = vecDot w y + vecDot w t := by
    intro y
    simp only [vecDot, Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  have htrans := hT (gaugeCoeff a abar hS) theta htheta
    (fun y ↦ vecDot w y + G.globalValueRepresentative y)
    (fun y ↦ w + G.globalGradientRepresentative y) t (vecDot w t) hLiou
  have hvalue :
      (fun y ↦ (vecDot w (y + t) + G.globalValueRepresentative (y + t)) -
        vecDot w t) =
        fun y ↦ vecDot w y + G.globalValueRepresentative (y + t) := by
    funext y
    rw [hdot y]
    ring
  rw [hvalue] at htrans
  exact (memLiouvilleClass_congr_coefficient
    (gaugeCoeff_translateCoeff_ae a abar hS z).symm
    (isAELocallyUniformlyElliptic_gaugeCoeff_translate a abar hS z)
    (isAELocallyUniformlyElliptic_gaugeCoeff (translateCoeff z a) abar hS)).mp
    htrans

end

end Root
end HighContrast
end HCPolySupport

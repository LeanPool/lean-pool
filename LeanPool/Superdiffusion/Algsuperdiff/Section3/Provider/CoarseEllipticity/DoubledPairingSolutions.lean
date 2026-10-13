/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledCoarsePoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledPairingGauge

/-!
# DoubledPairingSolutions

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Poincare carriers are the gauged doubled field and its gauged flux

Source displays in ABK26:

* `e.findSfull` and `e.bfS`, the characterization of the double-variable
  solution space `S(cu_m)` used in Remark `r.cg.poincare.doubled.variables`;
* `e.bfA.magic.swapping`,

  ```
  bfA ( p + p^* , a p - a^t p^* ) = ( a p + a^t p^* , p - p^* );
  ```

* `e.CG.Poincare.doubled.vars`, whose two left-hand seminorms are taken of
  `bfA_0^{1/2} X` and `bfA_0^{-1/2} bfA X`.

## What the module supplies

`DoubledCoarsePoincare.lean` proves the doubled Poincare inequality with its two
left-hand sides written as the *explicit* fields `doubledStateField` and
`doubledFluxField` of a primal/adjoint cube-solution pair.  The Step-2 consumer,
by contrast, holds a doubled field `X` and needs the seminorms of `bfA_0^{1/2}X`
and `bfA_0^{-1/2} bfA_m X` in the gauge vocabulary of `DoubledPairingGauge.lean`.

The two are literally the same objects:

* the state carrier needs no lemma at all: `doubledStateField` is, by
  definition, `blockGaugeUp` -- that is `bfA_0^{1/2}` -- applied to
  `Ch02.doubledFieldOfSolutions`;
* `doubledFluxField_apply_eq_blockGaugeDown` -- `doubledFluxField` is
  `bfA_0^{-1/2}` applied to `bfA` applied to the same field, by
  `e.bfA.magic.swapping`.

Together they identify the manuscript's `[bfAhom^{-1/2} bfA_m tilde
S_z]_{H^{-1}}` with the quantity the proved Poincare inequality actually
bounds, which is the `hpoin` leg of
`PerCubeFluctuationArithmetic.perCube_fluct_le`.

`sqrt_mul_add_inv_sqrt_mul_sq_le_two_mul` records the remaining arithmetic
link: the Poincare ellipticity factor squares to at most twice the
`gaugedEllipticitySum` of `LocalizationFluctuationEllipticity.lean`, which is
the form in which carry it.

## Binders

`0 < sig0` is the positivity of the scalar `sigma_0` of `e.form.of.A.naught`;
`hdet` (or the ambient ellipticity that supplies it) is the invertibility of the
symmetric part at the point, which is what makes `bfA` the matrix of
`e.block.matrix.basic.definitions` there.  No smallness, moment or measurability
proposition occurs.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open HCPolySupport.Book
open HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The state carrier is the gauged doubled field

`doubledStateField sig0 Q a v vStar x` unfolds to `blockGaugeUp sig0` of
`(Ch02.doubledFieldOfSolutions (a.coeffOn Q) v vStar).eval x`, so the first of
the two identifications holds by definition and carries no statement here. -/


/-! ## The flux carrier is the gauged image under `bfA` -/

/-- **`e.bfA.magic.swapping` at a point.**  Applying the doubled matrix of
`a` to the doubled field of a solution pair swaps the two legs. -/
theorem blockMatVecMul_blockMatrixField_doubledFieldOfSolutions (Q : TriadicCube d)
    (a : CoeffFamily d) (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a))
    {x : Vec d}
    (hdet : IsUnit (symmPart ((a.coeffOn Q).toCoeffField x)).det) :
    blockMatVecMul (Ch02.blockMatrixField (a.coeffOn Q) x)
        ((Ch02.doubledFieldOfSolutions (a.coeffOn Q) v vStar).eval x) =
      (solutionFluxField Q a v x + solutionFluxField Q (adjointFamily a) vStar x,
        solutionGradientField v x - solutionGradientField vStar x) := by
  have heval : (Ch02.doubledFieldOfSolutions (a.coeffOn Q) v vStar).eval x =
      (v.toH1.grad x + vStar.toH1.grad x,
        matVecMul ((a.coeffOn Q).toCoeffField x) (v.toH1.grad x) -
          matVecMul (matTranspose ((a.coeffOn Q).toCoeffField x)) (vStar.toH1.grad x)) := rfl
  rw [heval, HCPolySupport.Internal.Ch02.BookCh02.book_blockMatrixField_eq_blockCoeffField]
  exact HCPolySupport.blockMatVecMul_blockCoeffField_pair_of_isUnit_det_symmPart
    (a.coeffOn Q).toCoeffField x hdet _ _

/-- **`bfA_0^{-1/2} bfA X` for `X` the doubled field of a solution pair.**  The
second left-hand carrier of `e.CG.Poincare.doubled.vars` is the down-gauge of the
`bfA`-image of `e.findSfull`'s field.

This is the identification the Step-2 consumer needs: the manuscript's
`[bfAhom^{-1/2} bfA_m tilde S_z]_{H^{-1}}` is a seminorm of exactly the field
that `DoubledCoarsePoincare.doubledCoarsePoincare_le_doubledEnergy` bounds. -/
theorem doubledFluxField_apply_eq_blockGaugeDown (sig0 : ℝ) (Q : TriadicCube d)
    (a : CoeffFamily d) (v : CubeSolution Q a) (vStar : CubeSolution Q (adjointFamily a))
    {x : Vec d}
    (hdet : IsUnit (symmPart ((a.coeffOn Q).toCoeffField x)).det) :
    doubledFluxField sig0 Q a v vStar x =
      blockGaugeDown sig0
        (blockMatVecMul (Ch02.blockMatrixField (a.coeffOn Q) x)
          ((Ch02.doubledFieldOfSolutions (a.coeffOn Q) v vStar).eval x)) := by
  rw [blockMatVecMul_blockMatrixField_doubledFieldOfSolutions Q a v vStar hdet]
  rfl


/-! ## The Poincare ellipticity factor against the gauged ellipticity sum -/

/-- **The arithmetic link.**  The ellipticity factor carried by
`e.CG.Poincare.doubled.vars`,

```
Theta_0 = sigma_0^{1/2} lambda_{s,2}^{-1/2} + sigma_0^{-1/2} Lambda_{s,2}^{1/2} ,
```

satisfies `Theta_0^2 <= 2 (sigma_0^{-1} Lambda_{s,2} + sigma_0
lambda_{s,2}^{-1})`, i.e. `Theta_0 <= sqrt 2 * sqrt (gaugedEllipticitySum
sigma_0.)`.  This is what turns the *square root* of the ellipticity sum
appearing in the Poincare factor into the first power appearing: the factor is
spent twice in the quadratic term and twice in the cross term. -/
theorem sqrt_mul_add_inv_sqrt_mul_sq_le_two_mul {sig0 lamInv Lam : ℝ}
    (hsig0 : 0 < sig0) (hlamInv : 0 ≤ lamInv) (hLam : 0 ≤ Lam) :
    (Real.sqrt sig0 * Real.sqrt lamInv + (Real.sqrt sig0)⁻¹ * Real.sqrt Lam) *
        (Real.sqrt sig0 * Real.sqrt lamInv + (Real.sqrt sig0)⁻¹ * Real.sqrt Lam) ≤
      2 * (sig0⁻¹ * Lam + sig0 * lamInv) := by
  have hsq : Real.sqrt sig0 * Real.sqrt sig0 = sig0 := Real.mul_self_sqrt hsig0.le
  have hsqi : (Real.sqrt sig0)⁻¹ * (Real.sqrt sig0)⁻¹ = sig0⁻¹ := by
    rw [← mul_inv, hsq]
  have hl : Real.sqrt lamInv * Real.sqrt lamInv = lamInv := Real.mul_self_sqrt hlamInv
  have hL : Real.sqrt Lam * Real.sqrt Lam = Lam := Real.mul_self_sqrt hLam
  set A : ℝ := Real.sqrt sig0 * Real.sqrt lamInv with hA
  set B : ℝ := (Real.sqrt sig0)⁻¹ * Real.sqrt Lam with hB
  have hAsq : A * A = sig0 * lamInv := by
    rw [hA]; calc
      Real.sqrt sig0 * Real.sqrt lamInv * (Real.sqrt sig0 * Real.sqrt lamInv)
          = (Real.sqrt sig0 * Real.sqrt sig0) * (Real.sqrt lamInv * Real.sqrt lamInv) := by
            ring
      _ = sig0 * lamInv := by rw [hsq, hl]
  have hBsq : B * B = sig0⁻¹ * Lam := by
    rw [hB]; calc
      (Real.sqrt sig0)⁻¹ * Real.sqrt Lam * ((Real.sqrt sig0)⁻¹ * Real.sqrt Lam)
          = ((Real.sqrt sig0)⁻¹ * (Real.sqrt sig0)⁻¹) * (Real.sqrt Lam * Real.sqrt Lam) := by
            ring
      _ = sig0⁻¹ * Lam := by rw [hsqi, hL]
  have hkey : (A + B) * (A + B) ≤ 2 * (A * A + B * B) := by nlinarith [sq_nonneg (A - B)]
  calc
    (A + B) * (A + B) ≤ 2 * (A * A + B * B) := hkey
    _ = 2 * (sig0⁻¹ * Lam + sig0 * lamInv) := by rw [hAsq, hBsq]; ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity

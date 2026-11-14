/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.EllipticityOrdered

/-!
# TransposeGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Transpose invariance of the coarse gauge

Source: ABK26.  The proof of `l.Dh.bound` applies the coarse Poincaré
inequality `e.w.wstar.to.energy` to the *adjoint* half `w^* = ½ v(·, □₀, p, -q;
aᵗ)`, whose maximizer solves the transposed problem.  The right-hand side of
that inequality carries the coarse gauge of the transposed coefficient, and the
frozen statement carries the gauge of `a`.  The two agree:

```
λ_{s,q}(□₀; aᵗ) = λ_{s,q}(□₀; a) .
```

The reason is that the whole multiscale gauge is built from the one-cube norms
`|σ_*^{-1}(R; ·)|`, and `σ_*^{-1}` is *defined* entrywise from the pure-flux
response `J(U, 0, ·)` (`Book.Ch02.sigmaStarInvEntry`).  The adjoint response
identity `responseJ_transpose_neg_right` at `p = 0` says
`J(U, aᵗ, 0, -w) = J(U, a, 0, w)`, and the pure-flux response is even in `w`
because it is the quadratic form of `σ_*^{-1}`.  Hence

```
σ_*^{-1}(U; aᵗ) = σ_*^{-1}(U; a)
```

at every Chapter 2 domain, and the gauge invariance follows by transporting
this through `coarseSigmaStarInvMatrixNorm`,
`maxDescendantSigmaStarInvMatrixNormAtScale`, `lambdaSqFinite` /
`lambdaSqInfinity`, and finally through the frozen characterization theorem.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.UnitCubeMultiscale

noncomputable section

variable {d : ℕ}

/-! ## The pure-flux response is even and transpose invariant -/

/-- The pure-flux response is an even function of the flux loading. -/
theorem responseJ_zero_neg_right (U : Domain d) (a : CoeffOn U) (w : Vec d) :
    responseJ U a 0 (-w) = responseJ U a 0 w := by
  rw [Ch02.responseJ_zero_q_eq_sigmaStarInvCoarse U a (-w),
    Ch02.responseJ_zero_q_eq_sigmaStarInvCoarse U a w, matVecMul_neg,
    vecDot_neg_neg]

/-- The pure-flux response does not see the transpose. -/
theorem responseJ_transpose_zero_left (U : Domain d) (a : CoeffOn U) (w : Vec d) :
    responseJ U a.transpose 0 w = responseJ U a 0 w := by
  have h := responseJ_transpose_neg_right U a 0 (-w)
  rw [neg_neg] at h
  have hzero : vecDot (0 : Vec d) (-w) = 0 := by simp [vecDot]
  rw [hzero] at h
  rw [h, responseJ_zero_neg_right]
  ring

/-! ## Transpose invariance of `σ_*^{-1}` -/

/-- **The canonical coarse matrix `σ_*^{-1}` is transpose invariant.** -/
theorem sigmaStarInvCoarse_transpose (U : Domain d) (a : CoeffOn U) :
    Ch02.sigmaStarInvCoarse U a.transpose = Ch02.sigmaStarInvCoarse U a := by
  ext i j
  change Ch02.sigmaStarInvEntry U a.transpose i j = Ch02.sigmaStarInvEntry U a i j
  unfold Ch02.sigmaStarInvEntry
  by_cases hij : i = j
  · simp only [hij, dite_eq_left, responseJ_transpose_zero_left]
  · simp only [hij, responseJ_transpose_zero_left]

/-! ## The transposed coefficient family -/

/-- The entrywise transpose of a CoarseGraining triadic coefficient family. -/
def transposeCoeffFamily (F : Ch02.TriadicCoeffFamily d) :
    Ch02.TriadicCoeffFamily d where
  coeffOn := fun Q => (F.coeffOn Q).transpose
  restrictsTo_of_subset := by
    intro Q R hQR
    exact (F.restrictsTo_of_subset hQR).mono fun x hx => by simp [hx]

@[simp] theorem transposeCoeffFamily_coeffOn (F : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) :
    (transposeCoeffFamily F).coeffOn Q = (F.coeffOn Q).transpose :=
  rfl

/-! ## Transpose invariance of the multiscale gauge -/

theorem coarseSigmaStarInvMatrixNorm_transposeCoeffFamily
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) :
    Ch02.coarseSigmaStarInvMatrixNorm Q (transposeCoeffFamily F) =
      Ch02.coarseSigmaStarInvMatrixNorm Q F := by
  unfold Ch02.coarseSigmaStarInvMatrixNorm
  rw [transposeCoeffFamily_coeffOn, sigmaStarInvCoarse_transpose]

theorem maxDescendantSigmaStarInvMatrixNormAtScale_transposeCoeffFamily
    (Q : TriadicCube d) (k : ℤ) (F : Ch02.TriadicCoeffFamily d) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k (transposeCoeffFamily F) =
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F := by
  unfold Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  exact Ch02.finsetSupReal_congr _ fun R _ =>
    coarseSigmaStarInvMatrixNorm_transposeCoeffFamily R F

theorem lambdaSq_transposeCoeffFamily (Q : TriadicCube d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (F : Ch02.TriadicCoeffFamily d) :
    Ch02.lambdaSq Q s q (transposeCoeffFamily F) = Ch02.lambdaSq Q s q F := by
  cases q with
  | finite qv =>
      change Ch02.lambdaSqFinite Q s qv (transposeCoeffFamily F) =
        Ch02.lambdaSqFinite Q s qv F
      unfold Ch02.lambdaSqFinite
      simp only [maxDescendantSigmaStarInvMatrixNormAtScale_transposeCoeffFamily]
  | infinity =>
      change Ch02.lambdaSqInfinity Q s (transposeCoeffFamily F) =
        Ch02.lambdaSqInfinity Q s F
      unfold Ch02.lambdaSqInfinity
      simp only [maxDescendantSigmaStarInvMatrixNormAtScale_transposeCoeffFamily]

/-! ## Transpose invariance of the frozen unit-cube gauge -/

/-- **The frozen coarse gauge is transpose invariant.** -/
theorem unitCubeLambda_transpose (s : ℝ) (q : Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    unitCubeLambda s q a.transpose = unitCubeLambda s q a := by
  classical
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  have hFt : CoeffOn.AEEq
      ((transposeCoeffFamily F).coeffOn (originCube d 0)) a.transpose := by
    rw [transposeCoeffFamily_coeffOn]
    exact hF.transpose
  rw [unitCubeLambda_characterization s q a.transpose (transposeCoeffFamily F) hFt,
    unitCubeLambda_characterization s q a F hF, lambdaSq_transposeCoeffFamily]

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

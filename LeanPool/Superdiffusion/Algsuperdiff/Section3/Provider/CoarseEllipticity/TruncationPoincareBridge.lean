/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincare
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincareRHS.TerminalBounds

/-!
# TruncationPoincareBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-truncation form of the coarse-grained Poincare inequality

ABK26 Proposition `p.coarse.grained.Poincare` is available in CoarseGraining as
`coarsePoincareGradient_negativeBesov_le` and
`coarsePoincareFlux_negativeBesov_le`, but stated with the *public* Chapter-3
seminorm `scaleNormalizedNegativeBesovVectorNorm`, whose `q = 2` instance is a
supremum over truncations `N`.  The doubled-variables reformulation
`e.CG.Poincare.doubled.vars` needs the inequality in a form that can be combined
with the triangle inequality, and CoarseGraining's `q = 2` triangle inequality
is a *per-truncation* statement whose supremum form additionally requires the
truncated seminorms to be bounded above.  This module supplies that -- item
(gamma) of the infrastructure list recorded in `DoubledEnergyIdentity.lean`:

* the identification of the public `q = 2` seminorm with CoarseGraining's
  concrete truncated `q = 2` seminorm, truncation by truncation;
* the boundedness of the truncated seminorms of a solution gradient and of a
  solution flux, from their `L^2` membership;
* the two coarse Poincare bounds restated on the concrete seminorm.

## The exponent window

The `q = 2` bounds below are stated for `s in (0,1)`.  Recorded here so the
deviation is visible at the point of use.

## Main results

* `negativeBesovVectorPartialNormFinite_two_eq`,
  `scaleNormalizedNegativeBesovVectorNorm_finite_two_eq` -- the identification.
* `cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memVectorL2` -- the
  truncation bound.
* `solutionGradientField_memVectorL2`, `solutionFluxField_memVectorL2` and the
  two `bddAbove` corollaries.
* `cubeBesovNegativeVectorSeminormTwo_solutionGradientField_le` and
  `cubeBesovNegativeVectorSeminormTwo_solutionFluxField_le` -- the two halves of
  `p.coarse.grained.Poincare` on the concrete seminorm.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.

## References

* ABK26, `p.coarse.grained.Poincare`; `r.cg.poincare.doubled.variables`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open HCPolySupport.Book
open HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## Identification of the public `q = 2` seminorm -/

/-- **Per-truncation identification.**  At `q = 2` the public truncated Besov norm
is CoarseGraining's concrete truncated `q = 2` seminorm. -/
theorem negativeBesovVectorPartialNormFinite_two_eq (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    (F : Vec d → Vec d) :
    negativeBesovVectorPartialNormFinite Q s 2 N F =
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F := by
  unfold negativeBesovVectorPartialNormFinite cubeBesovNegativeVectorPartialSeminormTwo
  have hterm : ∀ j : ℕ,
      Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) 2 =
        (cubeBesovNegativeVectorDepthSeminorm Q s F j) ^ 2 := by
    intro j
    rw [negativeBesovVectorDepthSeminorm_eq_old]
    have h := Real.rpow_natCast (cubeBesovNegativeVectorDepthSeminorm Q s F j) 2
    rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num] at h
    exact h
  simp only [hterm]
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- The supremum form of the identification. -/
theorem scaleNormalizedNegativeBesovVectorNorm_finite_two_eq (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → Vec d) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) F =
      cubeBesovNegativeVectorSeminormTwo Q s F := by
  unfold scaleNormalizedNegativeBesovVectorNorm cubeBesovNegativeVectorSeminormTwo
  simp only [negativeBesovVectorPartialNormFinite_two_eq]

/-! ## The truncation bound -/

/-- **The truncated seminorms of an `L^2` field are bounded above.**  This is
what makes the supremum form of the `q = 2` triangle inequality available. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memVectorL2
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N u) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs u
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hu)

/-! ## `L^2` membership of the two solution fields -/

/-- The gradient of a cube solution is in `L^2` of the closed cube. -/
theorem solutionGradientField_memVectorL2 (Q : TriadicCube d) (a : CoeffFamily d)
    (u : CubeSolution Q a) : MemVectorL2 (cubeSet Q) (solutionGradientField u) := by
  have h := u.toH1.grad_memVectorL2
  simpa [MemVectorL2, solutionGradientField, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using h

/-- The flux of a cube solution is in `L^2` of the closed cube: the pointwise
representative of the coefficient field is uniformly elliptic on the cube, and
the flux agrees with the representative's flux almost everywhere. -/
theorem solutionFluxField_memVectorL2 [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (u : CubeSolution Q a) : MemVectorL2 (cubeSet Q) (solutionFluxField Q a u) := by
  classical
  set U : Ch02.Domain d := Ch02.cubeDomain Q with hU
  set aQ : Ch02.CoeffOn U := a.coeffOn Q with haQ
  have hEll : IsEllipticFieldOn aQ.lam aQ.Lam (cubeSet Q)
      (Internal.Ch02.BookCh02.pointwiseCoeffField U aQ) :=
    pointwiseCoeffField_isEllipticFieldOn_cubeSet Q aQ
  have hgrad : MemVectorL2 (cubeSet Q) (solutionGradientField u) :=
    solutionGradientField_memVectorL2 Q a u
  have hpw : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul (Internal.Ch02.BookCh02.pointwiseCoeffField U aQ x)
        (solutionGradientField u x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hgrad
  have hae : (fun x => matVecMul (Internal.Ch02.BookCh02.pointwiseCoeffField U aQ x)
        (solutionGradientField u x))
      =ᵐ[volumeMeasureOn (cubeSet Q)] solutionFluxField Q a u := by
    have h0 : Ch02.CoeffOn.AEEq (Internal.Ch02.BookCh02.pointwiseCoeffOn U aQ) aQ :=
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U aQ
    have h1 : (Internal.Ch02.BookCh02.pointwiseCoeffOn U aQ).toCoeffField
        =ᵐ[volumeMeasureOn (cubeSet Q)] aQ.toCoeffField := by
      simpa [volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using! h0
    filter_upwards [h1] with x hx
    have hpwf : Internal.Ch02.BookCh02.pointwiseCoeffField U aQ x =
        (Internal.Ch02.BookCh02.pointwiseCoeffOn U aQ).toCoeffField x := rfl
    show matVecMul (Internal.Ch02.BookCh02.pointwiseCoeffField U aQ x)
        (solutionGradientField u x) = solutionFluxField Q a u x
    rw [hpwf, hx, solutionFluxField, haQ, solutionGradientField]
  exact hpw.ae_eq hae

/-- Truncation bound for the gradient field. -/
theorem solutionGradientField_bddAbove (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) (u : CubeSolution Q a) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (solutionGradientField u)) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memVectorL2 Q hs _
    (solutionGradientField_memVectorL2 Q a u)

/-- Truncation bound for the flux field. -/
theorem solutionFluxField_bddAbove [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (hs : 0 < s) (u : CubeSolution Q a) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (solutionFluxField Q a u)) :=
  cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memVectorL2 Q hs _
    (solutionFluxField_memVectorL2 Q a u)

/-! ## `p.coarse.grained.Poincare` on the concrete seminorm -/

/-- **`e.besov.grad.poincare` at `q = 2`, on the concrete seminorm.**  For `s in
(0,1)`,

`[grad u]_{B^{-s}_{2,2}(Q)} <= c_{s,2}^{-1/2} lambda_{s,2}^{-1/2}(Q;a)
   || sigma^{1/2} grad u ||_{L^2(Q)}`. -/
theorem cubeBesovNegativeVectorSeminormTwo_solutionGradientField_le [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) {s : ℝ} (u : CubeSolution Q a)
    (hs : 0 < s) (_hs1 : s < 1) :
    cubeBesovNegativeVectorSeminormTwo Q s (solutionGradientField u) ≤
      poincareDiscountFactor s (.finite 2) *
        poincareLowerEllipticityFactor Q a s (.finite 2) *
          solutionEnergyNorm Q a u := by
  have h := coarsePoincareGradient_negativeBesov_le (d := d) Q a (s := s)
    (q := .finite 2) u hs (by norm_num [Ch02.MultiscaleExponent.IsAdmissible])
  rwa [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq] at h

/-- **`e.besov.flux.poincare` at `q = 2`, on the concrete seminorm.**  For `s in
(0,1)`,

`[a grad u]_{B^{-s}_{2,2}(Q)} <= c_{s,2}^{-1/2} Lambda_{s,2}^{1/2}(Q;a)
   || sigma^{1/2} grad u ||_{L^2(Q)}`. -/
theorem cubeBesovNegativeVectorSeminormTwo_solutionFluxField_le [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) {s : ℝ} (u : CubeSolution Q a)
    (hs : 0 < s) (_hs1 : s < 1) :
    cubeBesovNegativeVectorSeminormTwo Q s (solutionFluxField Q a u) ≤
      poincareDiscountFactor s (.finite 2) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
          solutionEnergyNorm Q a u := by
  have h := coarsePoincareFlux_negativeBesov_le (d := d) Q a (s := s)
    (q := .finite 2) u hs (by norm_num [Ch02.MultiscaleExponent.IsAdmissible])
  rwa [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq] at h

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity

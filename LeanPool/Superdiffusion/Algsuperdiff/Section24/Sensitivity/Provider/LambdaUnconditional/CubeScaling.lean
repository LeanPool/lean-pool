/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CrudeBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeBound
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeColoring

/-!
# CubeScaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# General-cube scaling of the coarse gauge

Source: ABK26, the deep-cube verification step of
`l.J.sensitivity.no.conditions`.  The unconditional sensitivity estimate
applies the *conditional* per-cube machinery at a mesoscopic triadic cube `R`
rather than at the unit cube.  Two purely structural facts about a general
triadic cube are needed for that.

* **Descendant scaling of the gauge.**  On every triadic descendant `S` of a
  cube `Q`, the scale-normalized coarse gauge is monotone:

  ```
  |S| lambda_{s,q}^{-1}(S; A)  <=  |Q| lambda_{s,q}^{-1}(Q; A)   (2 s <= 1) ,
  ```

  where `|Q| = cubeScaleFactor Q = 3^{Q.scale}`.  This is
  `Book.Ch02.maxDescendant_lambdaSq_inv_le` (CoarseGraining's form of
  `e.bound.one.cube.by.lambdas`) combined with the elementary exponent
  arithmetic `l + 2 s (Q.scale - l) <= Q.scale`.

* **Well-definedness of `lambda_{s,q}^{-1}(S; .)`.**  Two CoarseGraining
  triadic families whose representatives agree a.e. on a cube `Q` give the same
  value of `lambda_{s,q}(S; .)` at every `S` contained in `Q`.  This is what
  lets the mesoscopic-cube gauge along the perturbation path be *defined* by a
  single concrete family (`Provider.Lambda.CrudeBound.rootCoeffFamily`) and
  still be computed by any compatible family.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes multiscale weights with explicit `Real.rpow`. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## Elementary facts about triadic cubes -/

/-- A member of a finite family is bounded by its real supremum. -/
theorem le_finsetSupReal_of_mem {α : Type*} (s : Finset α) (f : α → ℝ) {R : α}
    (hR : R ∈ s) : f R ≤ Ch02.finsetSupReal s f := by
  classical
  unfold Ch02.finsetSupReal
  have hbdd : BddAbove (f '' (↑s : Set α)) := ((Set.toFinite _).image f).bddAbove
  exact le_csSup hbdd ⟨R, hR, rfl⟩

/-- The cube scale factor as an `rpow`. -/
theorem cubeScaleFactor_eq_rpow (R : TriadicCube d) :
    cubeScaleFactor R = Real.rpow (3 : ℝ) ((R.scale : ℝ)) := by
  rw [cubeScaleFactor]
  simp only [rpow_eq_pow]
  rw [Real.rpow_intCast]

/-- A cube of nonpositive scale has diameter at most one. -/
theorem cubeScaleFactor_le_one_of_scale_nonpos {R : TriadicCube d}
    (hR : R.scale ≤ 0) : cubeScaleFactor R ≤ 1 := by
  rw [cubeScaleFactor_eq_rpow]
  simp only [rpow_eq_pow]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  exact_mod_cast hR

/-- Every cube is its own descendant at its own scale. -/
theorem mem_descendantsAtScale_self (R : TriadicCube d) :
    R ∈ descendantsAtScale R R.scale := by
  simp [descendantsAtScale]

/-! ## Descendant scaling of the coarse gauge -/

/-- The scale-weight bookkeeping of the descendant gauge scaling:
`3^{l} 3^{2 s (Q.scale - l)} <= 3^{Q.scale}` when `2 s <= 1` and `l <= Q.scale`. -/
theorem cubeScaleFactor_mul_multiscaleDescendantWeight_le
    (Q : TriadicCube d) {s : ℝ} (hs1 : 2 * s ≤ 1) {l : ℤ} (hl : l ≤ Q.scale)
    {S : TriadicCube d} (hS : S ∈ descendantsAtScale Q l) :
    cubeScaleFactor S * Ch02.multiscaleDescendantWeight Q l s ≤ cubeScaleFactor Q := by
  have hSscale : S.scale = l := scale_eq_of_mem_descendantsAtScale hS
  have hfac : cubeScaleFactor S = Real.rpow (3 : ℝ) ((l : ℝ)) := by
    rw [cubeScaleFactor_eq_rpow, hSscale]
  have hweight : Ch02.multiscaleDescendantWeight Q l s =
      Real.rpow (3 : ℝ) (2 * s * (((Q.scale : ℝ)) - (l : ℝ))) := by
    rw [Ch02.multiscaleDescendantWeight]
    congr 1
    push_cast
    ring
  have hQ : cubeScaleFactor Q = Real.rpow (3 : ℝ) ((Q.scale : ℝ)) :=
    cubeScaleFactor_eq_rpow Q
  rw [hfac, hweight, hQ]
  simp only [rpow_eq_pow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hlQ : (l : ℝ) ≤ ((Q.scale : ℝ)) := by exact_mod_cast hl
  nlinarith [hlQ, hs1]

/-- **Descendant scaling of the coarse gauge at a general cube.**  For every
exponent pair with `2 s <= 1`, the scale-normalized coarse gauge of a triadic
descendant is bounded by that of its ancestor. -/
theorem cubeScaleFactor_mul_lambdaSq_inv_le_of_mem_descendantsAtScale [NeZero d]
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ}
    {q : Ch02.MultiscaleExponent} (hs0 : 0 < s) (hs1 : 2 * s ≤ 1)
    (hq : q.IsAdmissible) {l : ℤ} (hl : l ≤ Q.scale) {S : TriadicCube d}
    (hS : S ∈ descendantsAtScale Q l) :
    cubeScaleFactor S * (Ch02.lambdaSq S s q A)⁻¹ ≤
      cubeScaleFactor Q * (Ch02.lambdaSq Q s q A)⁻¹ := by
  have hloc := Ch02.maxDescendant_lambdaSq_inv_le Q A hl hs0 hq
  have hmem : (Ch02.lambdaSq S s q A)⁻¹ ≤
      Ch02.maxDescendantLowerEllipticityInvAtScale Q l s q A :=
    le_finsetSupReal_of_mem _ (fun T => (Ch02.lambdaSq T s q A)⁻¹) hS
  have hchain : (Ch02.lambdaSq S s q A)⁻¹ ≤
      Ch02.multiscaleDescendantWeight Q l s * (Ch02.lambdaSq Q s q A)⁻¹ :=
    hmem.trans hloc
  have hLnn : (0 : ℝ) ≤ cubeScaleFactor S := (cubeScaleFactor_pos_cube S).le
  have hQnn : (0 : ℝ) ≤ (Ch02.lambdaSq Q s q A)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_nonneg Q A hs0 hq)
  have hw := cubeScaleFactor_mul_multiscaleDescendantWeight_le Q hs1 hl hS
  calc cubeScaleFactor S * (Ch02.lambdaSq S s q A)⁻¹
      ≤ cubeScaleFactor S *
          (Ch02.multiscaleDescendantWeight Q l s * (Ch02.lambdaSq Q s q A)⁻¹) :=
        mul_le_mul_of_nonneg_left hchain hLnn
    _ = (cubeScaleFactor S * Ch02.multiscaleDescendantWeight Q l s) *
          (Ch02.lambdaSq Q s q A)⁻¹ := by ring
    _ ≤ cubeScaleFactor Q * (Ch02.lambdaSq Q s q A)⁻¹ :=
        mul_le_mul_of_nonneg_right hw hQnn

/-! ## Well-definedness of the cube gauge -/

/-- Two families that agree a.e. on a cube agree a.e. on every sub-cube. -/
theorem coeffOn_aeeq_of_openCubeSet_subset {Q S : TriadicCube d}
    (hsub : openCubeSet S ⊆ openCubeSet Q) (A B : TriadicCoeffFamily d)
    (hAB : CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q)) :
    CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S) := by
  have hA : (A.coeffOn S).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet S)] (A.coeffOn Q).toCoeffField :=
    A.restrictsTo_of_subset hsub
  have hB : (B.coeffOn S).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet S)] (B.coeffOn Q).toCoeffField :=
    B.restrictsTo_of_subset hsub
  have hQ : (A.coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet S)] (B.coeffOn Q).toCoeffField :=
    ae_restrict_of_ae_restrict_of_subset hsub hAB
  exact (hA.trans hQ).trans hB.symm

/-- The one-cube observable `|sigma_*^{-1}|` only sees the a.e. class. -/
theorem coarseSigmaStarInvMatrixNorm_eq_of_aeeq_of_openCubeSet_subset
    {Q S : TriadicCube d} (hsub : openCubeSet S ⊆ openCubeSet Q)
    (A B : TriadicCoeffFamily d)
    (hAB : CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q)) :
    coarseSigmaStarInvMatrixNorm S A = coarseSigmaStarInvMatrixNorm S B := by
  rw [coarseSigmaStarInvMatrixNorm, coarseSigmaStarInvMatrixNorm,
    Ch02.sigmaStarInvCoarse_eq_ofAEEq
      (coeffOn_aeeq_of_openCubeSet_subset hsub A B hAB)]

/-- **Well-definedness of the cube gauge.**  If two CoarseGraining triadic families
have a.e. equal representatives on a cube `Q`, then they give the same coarse
gauge at every triadic cube contained in `Q`. -/
theorem lambdaSq_inv_eq_of_aeeq_of_openCubeSet_subset [NeZero d]
    {Q S : TriadicCube d} (hsub : openCubeSet S ⊆ openCubeSet Q)
    (A B : TriadicCoeffFamily d)
    (hAB : CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q))
    {s : ℝ} {q : Ch02.MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    (Ch02.lambdaSq S s q A)⁻¹ = (Ch02.lambdaSq S s q B)⁻¹ := by
  have key : ∀ A' B' : TriadicCoeffFamily d,
      CoeffOn.AEEq (A'.coeffOn Q) (B'.coeffOn Q) →
      (Ch02.lambdaSq S s q A')⁻¹ ≤ (Ch02.lambdaSq S s q B')⁻¹ := by
    intro A' B' hAB'
    have hmain : (Ch02.lambdaSq S s q A')⁻¹ ≤ 1 * (Ch02.lambdaSq S s q B')⁻¹ := by
      refine lambdaSq_inv_le_of_descendant_ratio S B' A' zero_le_one hs hq ?_
      intro l hl T hT
      have hsubT : openCubeSet T ⊆ openCubeSet Q :=
        (openCubeSet_subset_of_mem_descendantsAtScale hl hT).trans hsub
      rw [coarseSigmaStarInvMatrixNorm_eq_of_aeeq_of_openCubeSet_subset hsubT A' B' hAB',
        one_mul]
    rwa [one_mul] at hmain
  exact le_antisymm (key A B hAB) (key B A hAB.symm)

end

end Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional

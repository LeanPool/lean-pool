/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.StationaryExpectations

/-!
# RealStationaryTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Real-translation stationary transfer of coarse block expectations

CoarseGraining's stationary-expectation layer
(`Homogenization.Book.Ch04.Theorems.StationaryExpectations`) transfers coarse
block expectations from a triadic cube to the origin cube at the same scale by
writing the cube as a translate of the origin cube.  Its transfer step is
`Ch04.integral_comp_toFun_translation_transfer`, which consumes
`RestrictionStationaryLaw = IsStationaryR`: invariance under *integer*
translations only.  The translation vector `Q.index * 3 ^ Q.scale` is an
integer vector exactly when `0 ≤ Q.scale`, which is why every CoarseGraining
consequence of that route carries a nonnegative-scale hypothesis.

The genuine coefficient-cutoff law is invariant under *every real* translation
(`Algsuperdiff.Section3.Cutoff.coefficientCutoffLaw_stationary_real`), so the
scale restriction is an artifact of the interface, not of the mathematics.
This module reroutes the transfer step through real translations: the
scale-free geometric identity
`Homogenization.cubeSet_eq_translateSet_originCube_of_triadicCube` writes an
arbitrary triadic cube as the `triadicCubeShift` translate of the origin cube at
the same scale, and
`Homogenization.coarseBlockMatrix_translateSet_eq_translateCoeffField` is already
stated for a real translation vector.  The resulting expectation identities hold
at *every* integer scale, positive or negative.

## Main results

* `integral_comp_toFun_translation_transfer_real`
* `integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_stationary_real`
* `integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_mem_descendantsAtScale`
-/

namespace Algsuperdiff.Section3.Provider.Annealed

open MeasureTheory
open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-- Real-translation invariance of a carrier law, the hypothesis actually available
for the coefficient-cutoff law.  CoarseGraining's `IsStationaryR` is its
restriction to integer translation vectors. -/
def IsStationaryRealR (P : RegCoeffLaw d) : Prop :=
  ∀ z : Vec d, Measure.map (translateReg z) P = P

/-- Carrier bridge for real translation: precomposition on the carrier projects to
the raw real translation (`rfl`).  The integer-vector specialization is
CoarseGraining's `Ch04.translateReg_toFun`. -/
theorem translateReg_toFun_real (z : Vec d) (a : RegCoeffField d) :
    (translateReg z a).toFun = translateCoeffField z a.toFun := rfl

/-- **Real-translation carrier transfer.**  A real-translation-covariant raw
observable composed with `toFun` integrates equally on real translates of a set
under a real-translation-invariant carrier law.  This is the exact analogue of
`Ch04.integral_comp_toFun_translation_transfer` with the integer restriction
removed. -/
theorem integral_comp_toFun_translation_transfer_real
    {P : RegCoeffLaw d} {X : Set (Vec d) → CoeffField d → ℝ}
    (hstat : IsStationaryRealR P) {U : Set (Vec d)}
    (hmeas : AEStronglyMeasurable (fun a : RegCoeffField d => X U a.toFun) P)
    (hcov : ∀ (V : Set (Vec d)) (z : Vec d) (a : CoeffField d),
      X (translateSet z V) a = X V (translateCoeffField z a))
    (z : Vec d) :
    ∫ a, X (translateSet z U) a.toFun ∂P = ∫ a, X U a.toFun ∂P := by
  have hbridge :
      (fun a : RegCoeffField d => X (translateSet z U) a.toFun) =
        fun a : RegCoeffField d =>
          (fun b : RegCoeffField d => X U b.toFun) (translateReg z a) := by
    funext a
    show X (translateSet z U) a.toFun = X U (translateReg z a).toFun
    rw [hcov U z a.toFun, translateReg_toFun_real]
  calc
    ∫ a, X (translateSet z U) a.toFun ∂P
        = ∫ a, (fun b : RegCoeffField d => X U b.toFun) (translateReg z a) ∂P := by
          rw [hbridge]
    _ = ∫ a, X U a.toFun ∂P :=
          integral_comp_eq_of_map_eq (measurable_translateReg z) (hstat z)
            (fun b : RegCoeffField d => X U b.toFun) hmeas

/-- A.e. strong measurability of a coarse block matrix entry on a triadic cube,
assembled from the four `RestrictionLawCarrier` a.e.-measurability lemmas. -/
theorem aestronglyMeasurable_blockMatEntry_coarseBlockMatrix_cubeSet
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (R : TriadicCube d)
    (alpha beta : BlockCoord d) :
    AEStronglyMeasurable
      (fun a : RegCoeffField d =>
        blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta) P := by
  cases alpha with
  | inl i =>
      cases beta with
      | inl j =>
          simpa [blockMatEntry] using
            (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet R i j).aestronglyMeasurable
      | inr j =>
          simpa [blockMatEntry] using
            (hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet R i j).aestronglyMeasurable
  | inr i =>
      cases beta with
      | inl j =>
          simpa [blockMatEntry] using
            (hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet R i j).aestronglyMeasurable
      | inr j =>
          simpa [blockMatEntry] using
            (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet R i j).aestronglyMeasurable

/-- **Scale-free stationary transfer of coarse block expectations.**  Under
real-translation invariance, every coarse block matrix entry on an *arbitrary*
triadic cube has the same expectation as the corresponding origin-cube entry at
the same scale.  CoarseGraining's
`integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_stationary` is the
`0 ≤ R.scale` case of this statement. -/
theorem integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_stationary_real
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hstat : IsStationaryRealR P)
    (R : TriadicCube d) (alpha beta : BlockCoord d) :
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta ∂P =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun)
          alpha beta ∂P := by
  have hcov :
      ∀ (V : Set (Vec d)) (z : Vec d) (a : CoeffField d),
        blockMatEntry (coarseBlockMatrix (translateSet z V) a) alpha beta =
          blockMatEntry (coarseBlockMatrix V (translateCoeffField z a)) alpha beta := by
    intro V z a
    exact congrArg (fun A : BlockMat d => blockMatEntry A alpha beta)
      (coarseBlockMatrix_translateSet_eq_translateCoeffField z V a)
  calc
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta ∂P
        =
      ∫ a,
        blockMatEntry
          (coarseBlockMatrix
            (translateSet (triadicCubeShift R) (cubeSet (originCube d R.scale))) a.toFun)
          alpha beta ∂P := by
          rw [cubeSet_eq_translateSet_originCube_of_triadicCube R]
    _ =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun)
          alpha beta ∂P :=
        integral_comp_toFun_translation_transfer_real (P := P)
          (X := fun U a => blockMatEntry (coarseBlockMatrix U a) alpha beta) hstat
          (aestronglyMeasurable_blockMatEntry_coarseBlockMatrix_cubeSet hP
            (originCube d R.scale) alpha beta)
          hcov (triadicCubeShift R)

/-- **Scale-free descendant transfer.**  Under real-translation invariance, every
coarse block matrix entry on a descendant of an origin cube has the same
expectation as the corresponding origin-cube entry at the descendant scale.  No
sign restriction on the scales is needed; CoarseGraining's
`integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_mem_descendantsAtScale_originCube`
is the `0 ≤ n` case. -/
theorem integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_mem_descendantsAtScale
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hstat : IsStationaryRealR P)
    {n k : ℤ} (hnk : n ≤ k) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d k) n) (alpha beta : BlockCoord d) :
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta ∂P =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) alpha beta ∂P := by
  have hscale : R.scale = n := Ch04.scale_eq_of_mem_descendantsAtScale_originCube hnk hR
  calc
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta ∂P
        =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun)
          alpha beta ∂P :=
        integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_stationary_real
          hP hstat R alpha beta
    _ =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) alpha beta ∂P := by
        rw [hscale]

end

end Algsuperdiff.Section3.Provider.Annealed

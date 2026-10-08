/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.Successor
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.CellMuMeasurability
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize

/-!
# High-contrast homogenization: Provider.Window.ScaleMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of the strict successor scale

The response on every standard cell is measurable entry by entry.  Reading its
relative size as the spectral norm of the normalized response makes each bad
scale measurable, and the strict successor is then a countable supremum of
measurable extended-real functions.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open MeasureTheory

open scoped ENNReal

open scoped Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- The relative size of the response on a bounded open cell is measurable. -/
theorem measurable_blockSize_coarseBlock {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUbdd : IsBoundedDomain U) (hUvol : 0 < (volume U).toReal)
    {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    Measurable fun a : CoeffSpace d => blockSize (coarseBlock U a) F := by
  have hentry : ∀ α β : BlockCoord d,
      Measurable fun a : CoeffSpace d => toFullBlockMat (coarseBlock U a) α β := by
    intro α β
    simpa only [← blockMatEntry_eq_toFullBlockMat] using
      Recurrence.measurable_blockMatEntry_coarseBlock_of_measurable_Mu
        (fun Q => Recurrence.measurable_Mu_coeffSpace hUopen hUbdd hUvol Q) α β
  have hnormalized : ∀ α β : BlockCoord d,
      Measurable fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock (coarseBlock U a) F) α β := by
    intro α β
    simp_rw [Recurrence.toFullBlockMat_normalizedBlock_apply]
    exact Finset.measurable_fun_sum _ fun γ _ =>
      Finset.measurable_fun_sum _ fun δ _ =>
        ((hentry δ γ).const_mul _).mul_const _
  have hmatrix : Measurable fun a : CoeffSpace d =>
      fun α β => toFullBlockMat (normalizedBlock (coarseBlock U a) F) α β :=
    measurable_pi_iff.mpr fun α => measurable_pi_iff.mpr fun β => hnormalized α β
  have hnorm : Measurable fun e : BlockCoord d → BlockCoord d → ℝ =>
      ‖(Matrix.of e : FullBlockMat d)‖ :=
    Continuous.measurable (continuous_norm.comp (continuous_matrix fun α β =>
      (continuous_apply β).comp (continuous_apply α)))
  have hrw : (fun a : CoeffSpace d => blockSize (coarseBlock U a) F) =
      fun a => ‖(Matrix.of (fun α β =>
        toFullBlockMat (normalizedBlock (coarseBlock U a) F) α β) : FullBlockMat d)‖ := by
    funext a
    exact PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_coarseBlock _ _) hF hFpd
  rw [hrw]
  exact hnorm.comp hmatrix

/-- The discounted maximal response at a fixed scale is measurable. -/
theorem measurable_badScaleSize (g : ℝ) (E : BlockMat d)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E) (h m : ℤ) :
    Measurable fun a : CoeffSpace d =>
      ⨆ (k : ℤ) (_ : k ≤ m) (w : Fin d → ℤ)
          (_ : standardCellCenter k w ∈ centeredCube d m),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-g * max ((m : ℝ) - (h : ℝ) - (k : ℝ)) 0) *
            blockSize (coarseBlock (standardCell d k w) a) E) := by
  refine Measurable.iSup fun k => Measurable.iSup fun _ =>
    Measurable.iSup fun w => Measurable.iSup fun _ => ?_
  have hU : IsOpenBoundedConvexDomain (standardCell d k w) :=
    isOpenBoundedConvexDomain_openCubeSet (translateCube w (originCube d k))
  have hUvol : 0 < (volume (standardCell d k w)).toReal := by
    change 0 < (volume (openCubeSet (translateCube w (originCube d k)))).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos _
  exact ENNReal.measurable_ofReal.comp
    ((measurable_blockSize_coarseBlock hU.isOpen hU.isBoundedDomain
      hUvol hE hEpd).const_mul _)

/-- Every fixed bad-scale event is measurable. -/
theorem measurableSet_badScaleEvent (g : ℝ) (E : BlockMat d)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E) (h m : ℤ) :
    MeasurableSet {a : CoeffSpace d | badScaleEvent g E h m a} := by
  simpa only [badScaleEvent] using measurableSet_lt measurable_const
    (measurable_badScaleSize g E hE hEpd h m)

/-- The strict successor of the bad scales is measurable. -/
theorem measurable_successorScale (g : ℝ) (E : BlockMat d)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E) (h : ℤ) :
    Measurable fun a : CoeffSpace d => successorScale g E h a := by
  have hterm : ∀ m : ℤ, Measurable fun a : CoeffSpace d =>
      if badScaleEvent g E h m a then ENNReal.ofReal ((3 : ℝ) ^ m) else 0 := by
    intro m
    exact Measurable.ite (measurableSet_badScaleEvent g E hE hEpd h m)
      measurable_const measurable_const
  have hsup : Measurable fun a : CoeffSpace d =>
      ⨆ m : ℤ, if badScaleEvent g E h m a then
        ENNReal.ofReal ((3 : ℝ) ^ m) else 0 :=
    Measurable.iSup hterm
  have hrw : (fun a : CoeffSpace d => successorScale g E h a) =
      fun a => 3 * ⨆ m : ℤ, if badScaleEvent g E h m a then
        ENNReal.ofReal ((3 : ℝ) ^ m) else 0 := by
    funext a
    simp only [successorScale]
    congr 1
    apply iSup_congr
    intro m
    by_cases hm : badScaleEvent g E h m a
    · simp [hm]
    · simp [hm]
  rw [hrw]
  exact hsup.const_mul 3

end

end Window
end HighContrast
end HCPolySupport

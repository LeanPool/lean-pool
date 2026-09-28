/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Numerics.Batch005
/-!
# Gerver sofa dependency batch

* `KernelOnly.LeanCertGerverNumerics`.
* `KernelOnly.ConcreteUniqueZeros`.
-/

@[expose] public section

noncomputable section


section

/-!
# Final LeanCert numerical certificate for Gerver

All expensive 22D checks are already cached in a serial dependency chain
ending at `FullImage21`.  This module only assembles them into the global
norm/self-map facts and the unique-root theorem.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

theorem full_bound_lt : intervalMatrixBound fullPJ < qTarget := by
  apply matrixBound_lt_of_rows fullPJ qTarget qTarget_pos
  intro i
  fin_cases i
  · exact full_row_0_lt
  · exact full_row_1_lt
  · exact full_row_2_lt
  · exact full_row_3_lt
  · exact full_row_4_lt
  · exact full_row_5_lt
  · exact full_row_6_lt
  · exact full_row_7_lt
  · exact full_row_8_lt
  · exact full_row_9_lt
  · exact full_row_10_lt
  · exact full_row_11_lt
  · exact full_row_12_lt
  · exact full_row_13_lt
  · exact full_row_14_lt
  · exact full_row_15_lt
  · exact full_row_16_lt
  · exact full_row_17_lt
  · exact full_row_18_lt
  · exact full_row_19_lt
  · exact full_row_20_lt
  · exact full_row_21_lt

theorem full_bound_le : intervalMatrixBound fullPJ ≤ qTarget :=
  full_bound_lt.le

theorem full_point_values_mem :
    ∀ j : Fin 22,
      systemEval fullExpr
          (fun k => ((zeroCenter (n := 22) k : ℚ) : ℝ)) j ∈
        fullPointCache j := by
  intro j
  fin_cases j
  · exact full_point_0_mem
  · exact full_point_1_mem
  · exact full_point_2_mem
  · exact full_point_3_mem
  · exact full_point_4_mem
  · exact full_point_5_mem
  · exact full_point_6_mem
  · exact full_point_7_mem
  · exact full_point_8_mem
  · exact full_point_9_mem
  · exact full_point_10_mem
  · exact full_point_11_mem
  · exact full_point_12_mem
  · exact full_point_13_mem
  · exact full_point_14_mem
  · exact full_point_15_mem
  · exact full_point_16_mem
  · exact full_point_17_mem
  · exact full_point_18_mem
  · exact full_point_19_mem
  · exact full_point_20_mem
  · exact full_point_21_mem

theorem full_images_inside :
    ∀ i : Fin 22,
      intervalStrictInside (fullImageCachedQ i) (unitBox (n := 22) i) = true := by
  intro i
  fin_cases i
  · exact full_image_0_inside
  · exact full_image_1_inside
  · exact full_image_2_inside
  · exact full_image_3_inside
  · exact full_image_4_inside
  · exact full_image_5_inside
  · exact full_image_6_inside
  · exact full_image_7_inside
  · exact full_image_8_inside
  · exact full_image_9_inside
  · exact full_image_10_inside
  · exact full_image_11_inside
  · exact full_image_12_inside
  · exact full_image_13_inside
  · exact full_image_14_inside
  · exact full_image_15_inside
  · exact full_image_16_inside
  · exact full_image_17_inside
  · exact full_image_18_inside
  · exact full_image_19_inside
  · exact full_image_20_inside
  · exact full_image_21_inside

theorem full_unique_scaled :
    ∃! u, FinBoxMem u (unitBox (n := 22)) ∧ SystemZero fullExpr u := by
  exact uniqueSystemZero_of_certified_contraction_values
    fullExpr fullExpr_supported (unitBox (n := 22)) (zeroCenter (n := 22))
    full_center_mem fullY cfg qTarget qTarget_nonneg qTarget_lt_one
    (by simpa [fullPJ] using full_bound_le)
    fullPointCache full_point_values_mem full_images_inside

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Concrete Unique Zeros
-/

@[expose] public section

noncomputable section

namespace GerverSofa

open LeanCert.Engine

namespace PartALeanCert

/-- The unique normalized reduced-system zero selected from its existence certificate. -/
def reducedRootU : Fin 4 → ℝ := Classical.choose reduced_unique_scaled
/-- The unique normalized full-system zero selected from its existence certificate. -/
def fullRootU : Fin 22 → ℝ := Classical.choose full_unique_scaled

theorem reducedRootU_spec :
    FinBoxMem reducedRootU (unitBox (n := 4)) ∧
      SystemZero reducedExpr reducedRootU :=
  (Classical.choose_spec reduced_unique_scaled).1

theorem fullRootU_spec :
    FinBoxMem fullRootU (unitBox (n := 22)) ∧
      SystemZero fullExpr fullRootU :=
  (Classical.choose_spec full_unique_scaled).1

/-- The certified reduced-system root in the original box coordinates. -/
def reducedRoot : Vec 4 := reducedAffine reducedRootU
/-- The certified full-system root in the original Romik parameter coordinates. -/
def fullRoot : Vec 22 := fullAffine fullRootU

theorem reducedRoot_mem : reducedRoot ∈ Reduced.vectorBox :=
  reducedAffine_mem reducedRootU_spec.1

theorem fullRoot_mem : fullRoot ∈ Romik.vectorBox :=
  fullAffine_mem fullRootU_spec.1

theorem reducedRoot_zero : Reduced.vectorSystem reducedRoot = 0 := by
  have hz : systemEval reducedExpr reducedRootU = 0 := by
    funext i
    exact reducedRootU_spec.2 i
  rw [reduced_systemEval_eq] at hz
  exact hz

theorem fullRoot_zero : Romik.vectorSystem fullRoot = 0 := by
  have hz : systemEval fullExpr fullRootU = 0 := by
    funext i
    exact fullRootU_spec.2 i
  rw [full_systemEval_eq] at hz
  exact hz

/-- Concrete reduced 4D unique zero — no assumptions. -/
def reducedCertifiedUniqueZero :
    CertifiedUniqueZero Reduced.vectorSystem Reduced.vectorBox where
  solution := reducedRoot
  solution_mem := reducedRoot_mem
  satisfies := reducedRoot_zero
  unique_iff := by
    intro y hy
    constructor
    · intro hzero
      let uy := reducedNormalize y
      have huy : FinBoxMem uy (unitBox (n := 4)) := reducedNormalize_mem hy
      have hsys : SystemZero reducedExpr uy := by
        intro i
        change systemEval reducedExpr uy i = 0
        calc
          systemEval reducedExpr uy i =
              Reduced.vectorSystem (reducedAffine uy) i :=
            congrFun (reduced_systemEval_eq uy) i
          _ = Reduced.vectorSystem y i := by
            rw [show reducedAffine uy = y by
              simpa [uy] using reducedAffine_normalize y]
          _ = 0 := congrFun hzero i
      have huEq : uy = reducedRootU := by
        exact reduced_unique_scaled.unique ⟨huy, hsys⟩ reducedRootU_spec
      calc
        y = reducedAffine uy := by symm; exact reducedAffine_normalize y
        _ = reducedAffine reducedRootU := by rw [huEq]
        _ = reducedRoot := rfl
    · rintro rfl
      exact reducedRoot_zero

/-- Existing manuscript-level unique-solution interfaces are now discharged
by concrete numerical certificates rather than assumptions. -/
def reducedCertifiedUniqueSolution :
    CertifiedUniqueSolution Reduced.Equations Reduced.box :=
  Reduced.uniqueSolutionOfVector reducedCertifiedUniqueZero

end PartALeanCert

end GerverSofa

end

end

end

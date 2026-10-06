/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedLaplacianCommutation
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureOperator

/-!
# Coordinate and Hilbert L² energies

The squared real Hilbert-space norm is the finite sum of the coordinate
L² energies of its spatial representative.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The real vector L² norm squared equals the sum of squared L² norms of
its three coordinate representatives. -/
theorem realVectorL2_norm_sq_eq_coordinate_integrals
    (u : RealVectorL2) :
    ‖u‖ ^ 2 = ∑ i : Fin 3,
      ∫ x : Vec3, realVectorL2Representative u x i ^ 2 := by
  have hmem := realVectorL2Representative_memLp_two u
  have hcomp (i : Fin 3) : MemLp
      (fun x : Vec3 => realVectorL2Representative u x i)
      (2 : ℝ≥0∞) volume :=
    hmem.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) i)
  have hInt (i : Fin 3) : Integrable
      (fun x : Vec3 => realVectorL2Representative u x i *
        realVectorL2Representative u x i) volume :=
    (hcomp i).integrable_mul (hcomp i)
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral_realVectorL2Representative]
  rw [integral_finsetSum Finset.univ (fun i _ => hInt i)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext x
  ring

/-- A coordinate L² representative has the expected Hilbert norm squared,
equal to the sum of its three component energy integrals. -/
theorem realVectorL2OfCoordinateFunction_norm_sq
    (a : Vec3 → Vec3) (ha : MemLp a (2 : ℝ≥0∞) volume) :
    ‖realVectorL2OfCoordinateFunction a ha‖ ^ 2 =
      ∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2 := by
  rw [realVectorL2_norm_sq_eq_coordinate_integrals]
  apply Finset.sum_congr rfl
  intro i _
  have hrep := realVectorL2OfCoordinateFunction_rep a ha
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  rw [hx]

end CKN.Leray

end

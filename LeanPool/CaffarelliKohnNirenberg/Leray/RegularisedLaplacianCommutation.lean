/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatHkEnergy

/-!
# Spatial differentiation of the Laplacian

Ordered coordinate derivatives commute with each classical second
coordinate derivative on all-order smooth scalar fields.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Every ordered derivative commutes with a classical second coordinate
derivative of an all-order smooth scalar field. -/
theorem regularisedOrderedSpatialDerivative_comm_secondDerivative
    (v : Vec3 → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (α : List (Fin 3)) (i : Fin 3) (x : Vec3) :
    regularisedOrderedSpatialDerivative α
      (fun y : Vec3 => fderiv ℝ
        (fun z => fderiv ℝ v z (CKN.basisVec i)) y (CKN.basisVec i)) x =
      fderiv ℝ
        (fun y : Vec3 => fderiv ℝ
          (regularisedOrderedSpatialDerivative α v) y (CKN.basisVec i))
        x (CKN.basisVec i) := by
  let Dv : Vec3 → ℝ := fun y => fderiv ℝ v y (CKN.basisVec i)
  have hDv : ContDiff ℝ (⊤ : ℕ∞) Dv :=
    (hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℝ (CKN.basisVec i))
  rw [regularisedOrderedSpatialDerivative_comm_spatialDerivative Dv hDv α i x]
  have hcomm : regularisedOrderedSpatialDerivative α Dv =
      fun y : Vec3 => fderiv ℝ
        (regularisedOrderedSpatialDerivative α v) y (CKN.basisVec i) := by
    funext y
    exact regularisedOrderedSpatialDerivative_comm_spatialDerivative v hv α i y
  rw [hcomm]

/-- Ordered coordinate derivatives distribute over a finite sum of
all-order smooth scalar fields. -/
theorem regularisedOrderedSpatialDerivative_finset_sum
    {ι : Type*} (s : Finset ι) (F : ι → Vec3 → ℝ)
    (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (α : List (Fin 3)) (x : Vec3) :
    regularisedOrderedSpatialDerivative α
      (fun y : Vec3 => ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, regularisedOrderedSpatialDerivative α (F i) x := by
  induction α generalizing x with
  | nil => rfl
  | cons j α ih =>
      have hfun : regularisedOrderedSpatialDerivative α
          (fun y : Vec3 => ∑ i ∈ s, F i y) =
          fun y : Vec3 => ∑ i ∈ s,
            regularisedOrderedSpatialDerivative α (F i) y := by
        funext y
        exact ih y
      have hdiff (i : ι) (hi : i ∈ s) : DifferentiableAt ℝ
          (regularisedOrderedSpatialDerivative α (F i)) x :=
        (regularisedOrderedSpatialDerivative_contDiff (F i) (hF i hi) α).contDiffAt.differentiableAt
          (by norm_num)
      change fderiv ℝ
        (regularisedOrderedSpatialDerivative α
          (fun y : Vec3 => ∑ i ∈ s, F i y)) x (CKN.basisVec j) = _
      rw [hfun]
      have hfun2 : (fun y : Vec3 => ∑ i ∈ s,
          regularisedOrderedSpatialDerivative α (F i) y) =
          ∑ i ∈ s, regularisedOrderedSpatialDerivative α (F i) := by
        funext y
        simp only [Finset.sum_apply]
      rw [hfun2]
      rw [fderiv_sum (u := s) (fun i hi => hdiff i hi)]
      simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rfl

/-- Every ordered coordinate derivative commutes with the classical
Laplacian of an all-order smooth scalar field. -/
theorem regularisedOrderedSpatialDerivative_comm_laplacian
    (v : Vec3 → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (α : List (Fin 3)) (x : Vec3) :
    regularisedOrderedSpatialDerivative α (regularisedScalarLaplacian v) x =
      regularisedScalarLaplacian
        (regularisedOrderedSpatialDerivative α v) x := by
  have hsecond (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => fderiv ℝ
        (fun z => fderiv ℝ v z (CKN.basisVec i)) y (CKN.basisVec i)) := by
    have hfirst : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 => fderiv ℝ v z (CKN.basisVec i)) :=
      (hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ ℝ (CKN.basisVec i))
    exact (hfirst.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℝ (CKN.basisVec i))
  change regularisedOrderedSpatialDerivative α
      (fun y : Vec3 => ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ v z (CKN.basisVec i)) y
          (CKN.basisVec i)) x =
    ∑ i : Fin 3,
      fderiv ℝ
        (fun y : Vec3 => fderiv ℝ
          (regularisedOrderedSpatialDerivative α v) y (CKN.basisVec i))
        x (CKN.basisVec i)
  rw [regularisedOrderedSpatialDerivative_finset_sum
    Finset.univ
    (fun i y => fderiv ℝ
      (fun z => fderiv ℝ v z (CKN.basisVec i)) y (CKN.basisVec i))
    (fun i _ => hsecond i) α x]
  exact Finset.sum_congr rfl (fun i _ =>
    regularisedOrderedSpatialDerivative_comm_secondDerivative v hv α i x)

/-- The ordered derivative of the classical Laplacian is L² when the
scalar has square-integrable ordered derivatives two orders higher. -/
theorem regularisedOrderedSpatialDerivative_laplacian_memLp
    (v : Vec3 → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (α : List (Fin 3))
    (hDeriv : ∀ β : List (Fin 3), β.length ≤ α.length + 2 →
      MemLp (regularisedOrderedSpatialDerivative β v)
        (2 : ℝ≥0∞) volume) :
    MemLp (regularisedOrderedSpatialDerivative α (regularisedScalarLaplacian v))
      (2 : ℝ≥0∞) volume := by
  have hterm (i : Fin 3) : MemLp
      (fun x : Vec3 => fderiv ℝ
        (fun y : Vec3 => fderiv ℝ
          (regularisedOrderedSpatialDerivative α v) y (CKN.basisVec i))
        x (CKN.basisVec i)) (2 : ℝ≥0∞) volume :=
    hDeriv (i :: i :: α) (by simp)
  have hsum : MemLp
      (regularisedScalarLaplacian (regularisedOrderedSpatialDerivative α v))
      (2 : ℝ≥0∞) volume := by
    change MemLp (fun x : Vec3 => ∑ i : Fin 3,
      fderiv ℝ
        (fun y : Vec3 => fderiv ℝ
          (regularisedOrderedSpatialDerivative α v) y (CKN.basisVec i))
        x (CKN.basisVec i)) (2 : ℝ≥0∞) volume
    exact memLp_finsetSum Finset.univ (fun i _ => hterm i)
  convert hsum using 1
  funext x
  exact regularisedOrderedSpatialDerivative_comm_laplacian v hv α x

end CKN.Leray

end

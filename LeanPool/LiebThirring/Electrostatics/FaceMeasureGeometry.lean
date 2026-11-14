/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.VoronoiStrata
public import LeanPool.LiebThirring.Electrostatics.PlaneDistance

/-!
# Geometry for the positive Voronoi face measure

Half the separation of two nuclei, the height appearing in.

A frame chosen only to construct surface measure; its measure is independent of this choice, as
established by `bisectorSurfaceMeasure_eq`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LiebThirring

variable {M : ℕ}

/-- Half the separation of two nuclei, the height appearing in (6.1). -/
noncomputable def nuclearHalfDistance (R : Fin M → Position) (k l : Fin M) : ℝ :=
  ‖R l - R k‖ / 2

theorem nuclearHalfDistance_pos (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} (hkl : k ≠ l) : 0 < nuclearHalfDistance R k l :=
  half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hkl.symm)))

theorem nuclearHalfDistance_comm (R : Fin M → Position) (k l : Fin M) :
    nuclearHalfDistance R k l = nuclearHalfDistance R l k := by
  simp only [nuclearHalfDistance, norm_sub_rev]

theorem measurableSet_voronoiFace (R : Fin M → Position) (k l : Fin M) :
    MeasurableSet (voronoiFace R k l) := by
  classical
  by_cases hkl : k = l
  · subst l
    have he : voronoiFace R k k = ∅ := by
      ext x
      simp [voronoiFace]
    rw [he]
    exact MeasurableSet.empty
  · have he : voronoiFace R k l =
        (bisectorPlane R k l : Set Position) ∩
          ⋂ p : {p : Fin M // p ≠ k ∧ p ≠ l}, {x | dist x (R k) < dist x (R p)} := by
      ext x
      simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq, Subtype.forall]
      constructor
      · rintro ⟨_, hx, hf⟩
        exact ⟨hx, fun p hp => hf p hp.1 hp.2⟩
      · rintro ⟨hx, hf⟩
        exact ⟨hkl, hx, fun p hpk hpl => hf p ⟨hpk, hpl⟩⟩
    rw [he]
    exact (bisectorPlane R k l).closed_of_finiteDimensional.measurableSet.inter
      (MeasurableSet.iInter fun p =>
        (isOpen_lt (continuous_id.dist continuous_const)
          (continuous_id.dist continuous_const)).measurableSet)

theorem bisectorPlane_eq_affinePlane (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} (hkl : k ≠ l) :
    bisectorPlane R k l = affinePlane (bisectorNormal R k l) (midpoint ℝ (R k) (R l)) := by
  have hm := (mem_bisectorPlane_iff_normal R hR hkl _).mp
    (AffineSubspace.midpoint_mem_perpBisector (R k) (R l))
  ext x
  rw [mem_bisectorPlane_iff_normal R hR hkl, mem_affinePlane]
  have hv : x - midpoint ℝ (R k) (R l) =
      (x - R k) - (midpoint ℝ (R k) (R l) - R k) := by abel
  rw [hv, inner_sub_right (bisectorNormal R k l) (x - R k), hm, sub_eq_zero]

theorem planeHeight_bisector (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} (hkl : k ≠ l) :
    planeHeight (bisectorNormal R k l) (midpoint ℝ (R k) (R l)) (R k) =
      nuclearHalfDistance R k l := by
  have hm := (mem_bisectorPlane_iff_normal R hR hkl _).mp
    (AffineSubspace.midpoint_mem_perpBisector (R k) (R l))
  simp only [planeHeight, ← neg_sub (midpoint ℝ (R k) (R l)) (R k), inner_neg_right,
    abs_neg, hm, abs_of_nonneg (show 0 ≤ ‖R l - R k‖ / 2 from by positivity), nuclearHalfDistance]

theorem nuclearHalfDistance_le_norm_on_bisector (R : Fin M → Position)
    (hR : Function.Injective R) {k l : Fin M} (hkl : k ≠ l) {y : Position}
    (hy : y ∈ bisectorPlane R k l) : nuclearHalfDistance R k l ≤ ‖y - R k‖ := by
  have he := (mem_bisectorPlane_iff_normal R hR hkl y).mp hy
  have hb := real_inner_le_norm (bisectorNormal R k l) (y - R k)
  rw [norm_bisectorNormal R hR hkl, one_mul, he] at hb
  exact hb

/-- A frame chosen only to construct surface measure; its measure is independent
of this choice, as established by `bisectorSurfaceMeasure_eq`. -/
noncomputable def bisectorSurfaceFrame (R : Fin M → Position) (hR : Function.Injective R)
    (k l : Fin M) (hkl : k ≠ l) :
    PlaneFrame (affinePlane (bisectorNormal R k l) (midpoint ℝ (R k) (R l))) :=
  Classical.choice (nonempty_planeFrame _ _ (by
    intro hz
    have h := norm_bisectorNormal R hR hkl
    rw [hz, norm_zero] at h
    exact zero_ne_one h))

/-- The usual Euclidean surface measure on a bisector plane. -/
noncomputable def bisectorSurfaceMeasure (R : Fin M → Position) (hR : Function.Injective R)
    (k l : Fin M) (hkl : k ≠ l) : Measure Position :=
  planeMeasure (bisectorSurfaceFrame R hR k l hkl)

theorem planeMeasure_eq_of_plane_eq {H K : AffineSubspace ℝ Position}
    [Nonempty H] [Nonempty K] (h : H = K) (F : PlaneFrame H) (G : PlaneFrame K) :
    planeMeasure F = planeMeasure G := by
  subst K
  exact planeMeasure_eq F G

end LiebThirring

end

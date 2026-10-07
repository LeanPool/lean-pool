/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Spatial Sobolev slices of regularized velocities

Positive-time differentiability and finite global dissipation put almost every
spatial slice in representative-level `H¹`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Almost every positive-time slice of a regularized velocity has the stated
spatial weak gradient in `L²`. -/
theorem regUniform_velocity_h1_slices
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hU : ∀ t, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hDuMeasurable : Measurable Du)
    (hGradientEnergyFinite :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t))
          ∂(volume.restrict Set.univ) ∂volume) < ⊤)
    (hSpatialC1 : ∀ t, 0 < t → ∀ i : Fin 3,
      ContDiff ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (hDerivative : ∀ t, 0 < t → ∀ x i j,
      (fderiv ℝ (fun y : Vec3 => u (y, t) i) x) (CKN.basisVec j) =
        Du (x, t) i j) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = u (x, t) i) ∧
        (∀ i x j, (h i).grad x j = Du (x, t) i j) := by
  have hDuSlices :=
    CKN.Foundation.ae_memLp_two_spatial_gradient_slice_of_lintegral_lt_top
      u Du hDuMeasurable hGradientEnergyFinite
  filter_upwards [hDuSlices, ae_restrict_mem measurableSet_Ioi]
    with t hDuSlice htmem
  have ht : 0 < t := htmem
  have hU_t := hU t (le_of_lt ht)
  refine ⟨fun i => ?_, ?_, ?_⟩
  · let f : Vec3 → ℝ := fun x => u (x, t) i
    let g : Vec3 → Vec3 := fun x j => Du (x, t) i j
    have hf : MemLp f 2 volume := (memLp_pi_iff.mp hU_t) i
    have hg : MemLp g 2 volume := by
      apply memLp_pi_iff.mpr
      intro j
      simpa [g, Measure.restrict_univ] using
        (memLp_pi_iff.mp (memLp_pi_iff.mp hDuSlice i)) j
    have hweak : CKN.HasWeakGradientOn (Set.univ : Set Vec3) f g := by
      intro j
      have hbase := CKN.HasWeakGradientOn.of_contDiff
        (U := (Set.univ : Set Vec3)) (f := f) (hSpatialC1 t ht i)
      have hsame : (fun x : Vec3 => (fderiv ℝ f x) (CKN.basisVec j)) =
          fun x => g x j := by
        funext x
        exact hDerivative t ht x i j
      simpa [hsame] using hbase j
    exact {
      toFun := f
      grad := g
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hf
      gradMemL2 := by
        intro j
        simpa [CKN.GradMemLpOn, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using (memLp_pi_iff.mp hg) j
      hasWeakGradient := hweak
    }
  · intro i x
    rfl
  · intro i x j
    rfl

end CKN.Leray

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRough
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughSliceGrad
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughGradient
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionBundleParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevApprox

/-!
# The distributional heat system for the forced heat response

For a tensor `G ∈ L^{5/2} ∩ L²` supported in `Q_τ`, the forced heat response
`Z = forcedHeat G` has a spatial gradient `DZ ∈ L²(Q_τ)` that is the weak gradient
of almost every time slice, and it solves `∂ₜZ_i - ΔZ_i = ∑_j ∂_j G_ij` both in the
gradient form and in the sense of distributions on `Q_τ`,
`∫ Z_i (-∂ₜφ - Δφ) = -∫ ∑_j G_ij ∂_j φ`. This is the form in which `lem:pv-stokes`
states its equation.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A spatial derivative of a smooth test compactly supported in `Q_τ` is again
such a test. -/
theorem pvStokes_spatialPartial_mem {τ : ℝ} {φ : ParabolicPoint → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ)) (j : Fin 3) :
    (fun p => spatialPartial φ j p) ∈
      spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ) := by
  obtain ⟨hs, hc, hsub⟩ := hφ
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p) := hs
  have heq : (fun p : Vec3 × ℝ => spatialPartial φ j p) =
      fun p => (fderiv ℝ (fun p : Vec3 × ℝ => φ p) p) ((basisVec j, (0 : ℝ)) : Vec3 × ℝ) := by
    funext p
    exact spatialPartial_eq_joint_fderiv hs' p j
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => spatialPartial φ j p)
    rw [heq]
    exact (hs'.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  · change HasCompactSupport (fun p : Vec3 × ℝ => spatialPartial φ j p)
    rw [heq]
    exact hc.fderiv_apply (𝕜 := ℝ) _
  · exact (spatialPartial_tsupport_subset_product (f := fun p : Vec3 × ℝ => φ p) j).trans hsub

/-- The weak heat system for the rough forced heat response, in gradient and in
distributional form, with the gradient bound. -/
theorem pvStokes_response_weak :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      ∃ DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
        (∀ i j, MemLp (DZ i j) 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm (fun z => fun i j => DZ i j z) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        (∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), ∀ i : Fin 3,
          HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcedHeat G (x, s) i)
            (fun x => fun j => DZ i j (x, s))) ∧
        (∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ), ∀ i : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
            (-(forcedHeat G z i * timePartial φ z) +
              ∑ j : Fin 3, DZ i j z * spatialPartial φ j z +
              ∑ j : Fin 3, G i j z * spatialPartial φ j z) = 0) ∧
        (∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ), ∀ i : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
            forcedHeat G z i * (-timePartial φ z - ∑ j : Fin 3, spatialSecondPartial φ j j z) =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
            ∑ j : Fin 3, G i j z * spatialPartial φ j z) := by
  obtain ⟨C, hC, hgrad⟩ := forcedHeat_rough_gradient
  refine ⟨C, hC, fun τ hτ G hG52 hG2 hGsupp => ?_⟩
  obtain ⟨Gs, DZ, hGs, hGsc, hGspos, hGsconv, hDZsmem, hDZmem, hDZlim, henergy⟩ :=
    hgrad τ hτ G hG52 hG2 hGsupp
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  have hweak (φ : ParabolicPoint → ℝ)
      (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ)) :=
    forcedHeat_rough_weak_of_gradient hτ hG2 hGsupp hGs hGsc hGspos hGsconv hDZsmem hDZmem
      hDZlim φ hφ.1 hφ.2.1 hφ.2.2
  have hZ2 : MemLp (forcedHeat G) 2 (volume.restrict Q) :=
    forcedHeat_rough_memLp_two hτ hG52 hG2 hGsupp
  refine ⟨DZ, hDZmem, henergy,
    forcedHeat_slice_weakGradient_of_approx hτ hG2 hGsupp hGs hGsc hGspos hGsconv hDZmem hDZlim,
    fun φ hφ i => (hweak φ hφ).2 i, fun φ hφ i => ?_⟩
  have hT := spaceTimeTest_derivs_memLp_two hφ.1 hφ.2.1 τ
  have hZi : MemLp (fun z => forcedHeat G z i) 2 (volume.restrict Q) := memLp_pi_iff.1 hZ2 i
  have hT2 (j : Fin 3) := spaceTimeTest_derivs_memLp_two (pvStokes_spatialPartial_mem hφ j).1
    (pvStokes_spatialPartial_mem hφ j).2.1 τ
  -- the gradient term, by the weak gradient against `∂ⱼφ`
  have hgradj (j : Fin 3) : ∫ z in Q, DZ i j z * spatialPartial φ j z =
      -∫ z in Q, forcedHeat G z i * spatialSecondPartial φ j j z := by
    have h : ∫ z in Q, forcedHeat G z i * spatialSecondPartial φ j j z =
        -∫ z in Q, DZ i j z * spatialPartial φ j z :=
      (hweak _ (pvStokes_spatialPartial_mem hφ j)).1 i j
    rw [h, neg_neg]
  have hA : Integrable (fun z => forcedHeat G z i * timePartial φ z) (volume.restrict Q) :=
    hZi.integrable_mul hT.1
  have hB (j : Fin 3) : Integrable (fun z => DZ i j z * spatialPartial φ j z)
      (volume.restrict Q) := (hDZmem i j).integrable_mul (hT.2 j)
  have hGi (j : Fin 3) : Integrable (fun z => G i j z * spatialPartial φ j z)
      (volume.restrict Q) := ((hG2 i j).restrict _).integrable_mul (hT.2 j)
  have hS (j : Fin 3) : Integrable (fun z => forcedHeat G z i * spatialSecondPartial φ j j z)
      (volume.restrict Q) := hZi.integrable_mul ((hT2 j).2 j)
  have h0 := (hweak φ hφ).2 i
  have hA' : Integrable (fun z => -(forcedHeat G z i * timePartial φ z)) (volume.restrict Q) :=
    hA.neg
  have hBs : Integrable (fun z => ∑ j : Fin 3, DZ i j z * spatialPartial φ j z)
      (volume.restrict Q) := integrable_finsetSum _ fun j _ => hB j
  have hGs' : Integrable (fun z => ∑ j : Fin 3, G i j z * spatialPartial φ j z)
      (volume.restrict Q) := integrable_finsetSum _ fun j _ => hGi j
  have hAB : Integrable (fun z => -(forcedHeat G z i * timePartial φ z) +
      ∑ j : Fin 3, DZ i j z * spatialPartial φ j z) (volume.restrict Q) := hA'.add hBs
  rw [integral_add hAB hGs', integral_add hA' hBs, integral_neg,
    integral_finsetSum _ fun j _ => hB j, Finset.sum_congr rfl fun j _ => hgradj j] at h0
  have hL : ∫ z in Q, forcedHeat G z i * (-timePartial φ z - ∑ j : Fin 3,
      spatialSecondPartial φ j j z) = -(∫ z in Q, forcedHeat G z i * timePartial φ z) -
        ∑ j : Fin 3, ∫ z in Q, forcedHeat G z i * spatialSecondPartial φ j j z := by
    have hSs : Integrable (fun z => ∑ j : Fin 3, forcedHeat G z i * spatialSecondPartial φ j j z)
        (volume.restrict Q) := integrable_finsetSum _ fun j _ => hS j
    rw [← integral_finsetSum _ fun j _ => hS j, ← integral_neg, ← integral_sub hA' hSs]
    congr 1
    funext z
    rw [mul_sub, Finset.mul_sum]
    ring
  rw [hL]
  simp only [Finset.sum_neg_distrib] at h0
  linarith only [h0]

end ESS

end

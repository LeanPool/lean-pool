/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionMapBound
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionDivFree
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageDistribution

/-!
# The Navier–Stokes forcing of the local solution

For the forcing tensor `G = -(U ⊗ U + p I)` of `prop:pv-local-solution`, cut
off to the slab `ℝ³ × (0, σ)` with the canonical Riesz pressure `p`, we show
that almost every time slice is double-divergence free,
`∑_{ij} ∫ G_ij ∂_i∂_j φ = 0`, which is the equation `-Δp = ∂_i∂_j(U_i U_j)`,
and that the pressure lies in `L^{5/3}` of the slab when `U ∈ L² ∩ L⁴` there.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Second derivatives of a smooth compactly supported function are continuous
with compact support. -/
theorem mixedSecond_continuous_hasCompactSupport {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (i j : Fin 3) :
    Continuous (CKN.mixedSecond φ i j) ∧ HasCompactSupport (CKN.mixedSecond φ i j) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv φ j) := CKN.contDiff_spatialDeriv_smooth hφ j
  have h1c : HasCompactSupport (CKN.spatialDeriv φ j) :=
    hφc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv (CKN.spatialDeriv φ j) i) :=
    CKN.contDiff_spatialDeriv_smooth h1 i
  exact ⟨h2.continuous, h1c.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)⟩

/-- A square integrable function times a continuous compactly supported
function is integrable. -/
theorem integrable_mul_of_memLp_two_of_hasCompactSupport {f g : Vec3 → ℝ}
    (hf : MemLp f 2 volume) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) volume := by
  have h := (hf.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hg hgc
  simpa only [smul_eq_mul] using h

/-- The Navier–Stokes forcing tensor with the canonical pressure is double
divergence free on almost every time slice: `-Δp = ∂_i∂_j(U_i U_j)`. -/
theorem pvSlabForce_doubleDiv {σ : ℝ} {U : ParabolicPoint → Vec3}
    (hT2 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, pvSlabForce σ U i j (y, s) *
        CKN.mixedSecond φ i j y = 0 := by
  set Q := CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)
  set T := pvSlabTensor σ U U
  set P := pvSlabPressure σ U
  set R := CKN.Leray.rieszPressureSpaceTime 2 (by norm_num) T hT2
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have hT2' (i j : Fin 3) : MemLp (T i j) 2 volume := by
    rw [← e2]
    exact hT2 i j
  have hP2 : MemLp P 2 volume := by
    rw [← e2]
    exact pvSlabPressure_memLp (by norm_num : (1 : ℝ) < 2) hT2 hT2
  have hPR : P = Q.indicator R := pvSlabPressure_eq hT2
  have hTs := tensor_slice_memLp_two_ae (τ := σ) hT2' fun i j z hz => pvSlabTensor_eq_zero hz i j
  have hPs := tensor_slice_memLp_two_ae (τ := σ) (G := fun _ _ => P) (fun _ _ => hP2)
    fun _ _ z hz => pvSlabPressure_eq_zero hz
  have hR := CKN.Leray.rieszPressureSpaceTime_slice_laplacian_identity 2 (by norm_num) T hT2
  filter_upwards [hTs, hPs, hR] with s hTs hPs hR
  intro φ hφ hφc
  have hm := mixedSecond_continuous_hasCompactSupport hφ hφc
  by_cases hs : s ∈ Ioo 0 σ
  · have hmem (y : Vec3) : (y, s) ∈ Q := ⟨mem_univ y, hs⟩
    have hPRs (y : Vec3) : P (y, s) = R (y, s) := by
      rw [hPR]
      exact indicator_of_mem (hmem y) _
    have hTi (i j : Fin 3) : Integrable (fun y => T i j (y, s) * CKN.mixedSecond φ i j y) :=
      integrable_mul_of_memLp_two_of_hasCompactSupport (hTs i j) (hm i j).1 (hm i j).2
    have hPi (i j : Fin 3) : Integrable (fun y => P (y, s) * CKN.mixedSecond φ i j y) :=
      integrable_mul_of_memLp_two_of_hasCompactSupport (hPs i j) (hm i j).1 (hm i j).2
    have hGij (i j : Fin 3) : ∫ y : Vec3, pvSlabForce σ U i j (y, s) * CKN.mixedSecond φ i j y =
        -(∫ y, T i j (y, s) * CKN.mixedSecond φ i j y) -
          if i = j then ∫ y, P (y, s) * CKN.mixedSecond φ i j y else 0 := by
      have hpt : (fun y : Vec3 => pvSlabForce σ U i j (y, s) * CKN.mixedSecond φ i j y) =
          fun y => -(T i j (y, s) * CKN.mixedSecond φ i j y) -
            (if i = j then P (y, s) * CKN.mixedSecond φ i j y else 0) := by
        funext y
        simp only [pvSlabForce]
        split_ifs
        · change -(T i j (y, s) + P (y, s)) * _ = _
          ring
        · change -(T i j (y, s) + 0) * _ = _
          ring
      rw [hpt]
      split_ifs
      · rw [integral_sub (f := fun y => -(T i j (y, s) * CKN.mixedSecond φ i j y))
          (g := fun y => P (y, s) * CKN.mixedSecond φ i j y) (hTi i j).neg (hPi i j), integral_neg]
      · rw [integral_sub (f := fun y => -(T i j (y, s) * CKN.mixedSecond φ i j y))
          (g := fun _ => (0 : ℝ)) (hTi i j).neg (integrable_zero _ _ _), integral_neg,
          integral_zero]
    have hrow (i : Fin 3) : ∑ j : Fin 3, ∫ y : Vec3, pvSlabForce σ U i j (y, s) *
        CKN.mixedSecond φ i j y = -(∑ j : Fin 3, ∫ y, T i j (y, s) * CKN.mixedSecond φ i j y) -
          ∫ y, P (y, s) * CKN.mixedSecond φ i i y := by
      simp only [hGij, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    have hL : ∫ x, R (x, s) * (-CKN.spatialLaplacian φ x) =
        -∑ i : Fin 3, ∫ x, P (x, s) * CKN.mixedSecond φ i i x := by
      rw [← integral_finsetSum _ fun i _ => hPi i i, ← integral_neg]
      congr 1
      funext x
      change R (x, s) * -(∑ i : Fin 3, CKN.mixedSecond φ i i x) = _
      rw [← hPRs x, mul_neg, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← hR φ hφ hφc, hL]
    ring
  · have hzero (i j : Fin 3) (y : Vec3) : pvSlabForce σ U i j (y, s) = 0 :=
      pvSlabForce_eq_zero (fun hmem => hs hmem.2) i j
    simp [hzero]

/-- A Hölder triple for the quadratic tensor at exponent `5/3`. -/
theorem pvSlab_holderTriple_tenThirds : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3))
    (ENNReal.ofReal (10 / 3)) (ENNReal.ofReal (5 / 3)) := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 10 / 3),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 5 / 3),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

/-- The canonical pressure of a velocity in `L² ∩ L⁴` of the slab lies in
`L^{5/3}` of the slab. -/
theorem pvSlabPressure_memLp_fiveThirds {σ : ℝ} {U : ParabolicPoint → Vec3}
    (hU2 : MemLp U 2 (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (hU4 : MemLp U (ENNReal.ofReal 4)
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)))) :
    MemLp (pvSlabPressure σ U) (ENNReal.ofReal (5 / 3))
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) := by
  have h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (10 / 3) := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hU103 : MemLp U (ENNReal.ofReal (10 / 3))
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) :=
    serrin_memLp_interpolate two_ne_zero ENNReal.ofReal_ne_top h2
      (ENNReal.ofReal_le_ofReal (by norm_num)) hU2 hU4
  have h103 := pvSlab_holderTriple_tenThirds
  have h4 := pvSlab_holderTriple_four
  have hT2 (i j : Fin 3) : MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume :=
    pvSlabTensor_memLp hU4 hU4 i j
  have hT53 (i j : Fin 3) : MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal (5 / 3)) volume :=
    pvSlabTensor_memLp hU103 hU103 i j
  exact (pvSlabPressure_memLp (by norm_num : (1 : ℝ) < 5 / 3) hT2 hT53).restrict _

end ESS

end

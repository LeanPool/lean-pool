/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesWeak
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyTransfer
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport

/-!
# The explicit pairing modulus

The estimate behind clause (b) of `prop:blowup-limit`, for one field: if the
pairing of the slices of `f` with a smooth test `w` changes by the space-time
integral of the momentum flux, then, after integrating the viscous term by
parts on each slice, the change is at most

  `K (|t - s| (‖Δw‖₂ + ‖∇w‖_∞) + |t - s|^{1/3} ‖div w‖_∞)`,

where `K` depends only on a uniform bound for the slice `L²` norms of `f` on
the support set, an `L^{3/2}` bound for the pressure there, and the volume of
the support set.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Spatial derivatives of smooth functions are smooth. -/
theorem blowupLimitClauses_spatialDeriv_contDiff {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => spatialDeriv φ j x) := by
  rw [contDiff_iff_forall_nat_le]
  intro n _hn
  have hφ' : ContDiff ℝ (n + 1 : ℕ) φ := hφ.of_le (by simp)
  have hfd := hφ'.contDiff_fderiv_apply (m := n) (by simp)
  have hline : ContDiff ℝ n (fun x : Vec3 => (x, CKN.basisVec j)) :=
    contDiff_id.prodMk contDiff_const
  simpa only [Function.comp_def, CKN.spatialDeriv] using hfd.comp hline

/-- Spatial derivatives of compactly supported smooth functions have compact
support inside the support of the function. -/
theorem blowupLimitClauses_spatialDeriv_hasCompactSupport {φ : Vec3 → ℝ}
    (hφc : HasCompactSupport φ) (j : Fin 3) :
    HasCompactSupport (fun x : Vec3 => spatialDeriv φ j x) :=
  hφc.mono' ((subset_tsupport _).trans (CKN.tsupport_spatialDeriv_subset j))

/-- A continuous compactly supported function is square integrable on every
set. -/
theorem blowupLimitClauses_memLp_of_continuous_compact {φ : Vec3 → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (C : Set Vec3) (p : ℝ≥0∞) :
    MemLp φ p (volume.restrict C) :=
  (hφ.memLp_of_hasCompactSupport hφc).restrict C

/-- The viscous flux of a slice with a weak gradient, integrated by parts
against a smooth test carried by the set:
`∫_C ∑ Dg_ij ∂_j w_i = - ∫_C ∑ g_i Δw_i`. -/
theorem blowupLimitClauses_slice_ibp
    {C : Set Vec3} {R : ℝ} (hCR : C ⊆ vec3Ball 0 R)
    {g : Vec3 → Vec3} {Dg : Vec3 → Fin 3 → Vec3}
    (hg : MemLp g 2 (volume.restrict C)) (hDg : MemLp Dg 2 (volume.restrict C))
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (vec3Ball (0 : Vec3) R)
      (fun x => g x i) (fun x => Dg x i))
    {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwC : tsupport w ⊆ C) :
    ∫ x in C, ∑ i : Fin 3, ∑ j : Fin 3, Dg x i j * spatialDeriv (fun y => w y i) j x =
      -∫ x in C, ∑ i : Fin 3, g x i *
        ∑ j : Fin 3, spatialDeriv (fun y => spatialDeriv (fun z => w z i) j y) j x := by
  have hwi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => w y i) := fun i =>
    (contDiff_apply ℝ ℝ i).comp hw
  have hwic : ∀ i, HasCompactSupport (fun y => w y i) := fun i =>
    hwc.comp_left (g := fun v : Vec3 => v i) rfl
  have hwiC : ∀ i, tsupport (fun y => w y i) ⊆ C := fun i =>
    (tsupport_comp_subset (g := fun v : Vec3 => v i) rfl w).trans hwC
  set φ : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j x => spatialDeriv (fun y => w y i) j x
  have hφ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (φ i j) := fun i j =>
    blowupLimitClauses_spatialDeriv_contDiff (hwi i) j
  have hφc : ∀ i j, HasCompactSupport (φ i j) := fun i j =>
    blowupLimitClauses_spatialDeriv_hasCompactSupport (hwic i) j
  have hφC : ∀ i j, tsupport (φ i j) ⊆ C := fun i j =>
    (CKN.tsupport_spatialDeriv_subset j).trans (hwiC i)
  have hψC : ∀ i j, tsupport (fun x => spatialDeriv (φ i j) j x) ⊆ C := fun i j =>
    (CKN.tsupport_spatialDeriv_subset j).trans (hφC i j)
  have hψ : ∀ i j, Continuous (fun x => spatialDeriv (φ i j) j x) := fun i j =>
    (blowupLimitClauses_spatialDeriv_contDiff (hφ i j) j).continuous
  have hψc : ∀ i j, HasCompactSupport (fun x => spatialDeriv (φ i j) j x) := fun i j =>
    blowupLimitClauses_spatialDeriv_hasCompactSupport (hφc i j) j
  have hball : MeasurableSet (vec3Ball (0 : Vec3) R) := (isOpen_vec3Ball 0 R).measurableSet
  -- each pair of indices
  have hpair : ∀ i j, ∫ x in C, Dg x i j * φ i j x =
      -∫ x in C, g x i * spatialDeriv (φ i j) j x := by
    intro i j
    have h := hgrad i j (φ i j) (hφ i j) (hφc i j) ((hφC i j).trans hCR)
    have hL : ∫ x in vec3Ball (0 : Vec3) R, g x i * (fderiv ℝ (φ i j) x) (basisVec j) =
        ∫ x in C, g x i * spatialDeriv (φ i j) j x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hball hCR
      intro x hx
      have hx' : x ∉ tsupport (fun x => spatialDeriv (φ i j) j x) := fun h => hx.2 (hψC i j h)
      have h0 : spatialDeriv (φ i j) j x = 0 := image_eq_zero_of_notMem_tsupport hx'
      change g x i * spatialDeriv (φ i j) j x = 0
      rw [h0, mul_zero]
    have hR : ∫ x in vec3Ball (0 : Vec3) R, Dg x i j * φ i j x =
        ∫ x in C, Dg x i j * φ i j x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hball hCR
      intro x hx
      have hx' : x ∉ tsupport (φ i j) := fun h => hx.2 (hφC i j h)
      rw [image_eq_zero_of_notMem_tsupport hx', mul_zero]
    rw [← hL, ← hR, h, neg_neg]
  -- integrability of the summands
  have hint1 : ∀ i j, Integrable (fun x => Dg x i j * φ i j x) (volume.restrict C) := by
    intro i j
    exact ((hDg.eval i).eval j).integrable_mul
      (blowupLimitClauses_memLp_of_continuous_compact (hφ i j).continuous (hφc i j) C 2)
  have hint2 : ∀ i j, Integrable (fun x => g x i * spatialDeriv (φ i j) j x)
      (volume.restrict C) := by
    intro i j
    exact (hg.eval i).integrable_mul
      (blowupLimitClauses_memLp_of_continuous_compact (hψ i j) (hψc i j) C 2)
  calc
    ∫ x in C, ∑ i : Fin 3, ∑ j : Fin 3, Dg x i j * spatialDeriv (fun y => w y i) j x =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in C, Dg x i j * φ i j x := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ fun j _ => hint1 i j]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, -∫ x in C, g x i * spatialDeriv (φ i j) j x := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpair i j
    _ = -∫ x in C, ∑ i : Fin 3, g x i *
        ∑ j : Fin 3, spatialDeriv (fun y => spatialDeriv (fun z => w z i) j y) j x := by
      have hsum : ∀ x, ∑ i : Fin 3, g x i *
          ∑ j : Fin 3, spatialDeriv (fun y => spatialDeriv (fun z => w z i) j y) j x =
          ∑ i : Fin 3, ∑ j : Fin 3, g x i * spatialDeriv (φ i j) j x := by
        intro x
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      simp_rw [hsum]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint2 i j]
      simp_rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ fun j _ => hint2 i j, ← Finset.sum_neg_distrib]

end ESS

end

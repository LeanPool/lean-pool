/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceSup
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingStrongFamily
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainWord

/-!
# The `H²` energy of the slices of a strong solution

`prop:lps-smoothing`: the sum of the squared `H²` norms of the velocity slices is integrable in
time, and bounds the pointwise square of each velocity component almost everywhere.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The squared `H²` norm of the velocity slice at time `t`. -/
@[expose] def lpsSliceH2 (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ α ∈ sobolevWords 2, ∫ y : Vec3, (lpsStrongFamily u Du D2u i α (y, t)) ^ 2

theorem lpsSliceH2_nonneg (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (t : ℝ) : 0 ≤ lpsSliceH2 u Du D2u t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

/-- The slice `H²` energy is integrable on the time interval (`prop:lps-smoothing`). -/
theorem lps_sliceH2_integrable {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    Integrable (fun t => lpsSliceH2 u Du D2u t) (volume.restrict (Ioo t₀ T)) := by
  unfold lpsSliceH2
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun α hα => ?_
  have hfam := lps_strong_isL2SobolevFamily hderiv hu hDu hD2u i
  exact integrable_slab_sq_slices (a := t₀) (b := T)
    (F := lpsStrongFamily u Du D2u i α)
    (hfam.memL2 α (mem_sobolevWords.mp hα))

/-- Almost every slice of the velocity is bounded pointwise by a universal multiple of its
`H²` energy (`prop:lps-smoothing`). -/
theorem lps_ae_slice_sup_bound_strong :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
      {Dtu : ParabolicPoint → Vec3},
      HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu →
      MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) →
      MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) →
      MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) →
      ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3,
        (u (x, t) i) ^ 2 ≤ K * lpsSliceH2 u Du D2u t := by
  obtain ⟨K, hK, hsup⟩ := lps_ae_slice_sup_bound
  refine ⟨K, hK, fun {t₀ T u Du D2u Dtu} hderiv hu hDu hD2u => ?_⟩
  have h := fun i : Fin 3 => hsup (lps_strong_isL2SobolevFamily hderiv hu hDu hD2u i)
  have hall : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Vec3),
      (u (x, t) i) ^ 2 ≤ K * ∑ α ∈ sobolevWords 2, ∫ y : Vec3, (lpsStrongFamily u Du D2u i α (y, t)) ^ 2 :=
    ae_all_iff.mpr h
  filter_upwards [hall] with t ht
  rw [ae_all_iff]
  intro i
  filter_upwards [ht i] with x hx
  refine hx.trans (mul_le_mul_of_nonneg_left ?_ hK)
  unfold lpsSliceH2
  exact Finset.single_le_sum (f := fun j : Fin 3 => ∑ α ∈ sobolevWords 2,
    ∫ y : Vec3, (lpsStrongFamily u Du D2u j α (y, t)) ^ 2)
    (fun j _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
    (Finset.mem_univ i)

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSobolevBridge
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopf
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices

/-!
# Almost every time slice of a strong solution

For a strong solution with space-time weak derivatives, almost every time slice
has square-integrable velocity, first and second derivatives and time
derivative, the weak-gradient relations between them, and vanishing gradient
trace (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Almost every time slice of a square-integrable space-time field on a slab is
square integrable. -/
theorem lps_slice_memLp_two_ae_slab {a b : ℝ} {E : Type} [NormedAddCommGroup E]
    {F : ParabolicPoint → E}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), MemLp (fun x : Vec3 => F (x, t)) 2 volume := by
  have hν := lps_memLp_slab_to_prod hF
  have hint : Integrable (fun q : Vec3 × ℝ => ‖F (parabolicHomeomorph.symm q)‖ ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).mp hν
  filter_upwards [hint.prod_left_ae, hν.aestronglyMeasurable.prodMk_right] with t h1 h2
  exact (memLp_two_iff_integrable_sq_norm h2).mpr h1

/-- The good slices of a strong solution with space-time weak derivatives: the
time derivative and the second derivatives are square integrable, the second
derivatives are the weak gradients of the first derivatives, and the gradient
trace vanishes (`lem:lps-H1-estimate`). -/
theorem lps_strong_good_slices
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hU : IsLpsStrongSolution t₀ t₁ u Du p)
    (hD : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu)
    (hMu : MemLp u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDu : MemLp Du 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMD2 : MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))))
    (hMDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      MemLp (fun x : Vec3 => Dtu (x, t)) 2 volume ∧
      MemLp (fun x : Vec3 => D2u (x, t)) 2 volume ∧
      (∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x : Vec3 => Du (x, t) i j) (fun x k => D2u (x, t) i j k)) ∧
      (∀ᵐ x ∂(volume : Measure Vec3), ∑ i : Fin 3, Du (x, t) i i = 0) := by
  filter_upwards [ESS.LPS.lps_spatial_sobolev_slices_ae_of_weak_derivs hD hMu hMDu hMD2,
    lps_slice_memLp_two_ae_slab hMDt, lps_slice_memLp_two_ae_slab hMD2,
    ae_restrict_mem measurableSet_Ioo] with t hfam hDt hD2 htI
  have htIcc : t ∈ Icc t₀ t₁ := ⟨htI.1.le, htI.2.le⟩
  have hgrad : ∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x : Vec3 => Du (x, t) i j) (fun x k => D2u (x, t) i j k) := fun i j k =>
    (hfam i).weak [j] k (by simp)
  refine ⟨hDt, hD2, hgrad, ?_⟩
  have hDu2 := (lps_strong_solution_slice_memLp_two hU htIcc).2
  exact serrin_trace_zero_of_divFree (lps_strong_solution_slice_memLp_two hU htIcc).1 hDu2
    (lps_strong_solution_slice_weak_gradient hU htIcc)
    (lps_strong_solution_slice_weak_div_free hU htIcc).2

end ESS

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitSlices
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopf

/-!
# Time calculus for the slices of a strong solution

For a strong solution, the fixed-time kinetic energy and the fixed-time
squared gradient obey the time-integrated chain rule with the specified weak
derivatives (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A component of a matrix-valued function is bounded in `L²` by the
function. -/
theorem lps_component2_eLpNorm_le {v : Vec3 → Fin 3 → Vec3}
    (hv : AEStronglyMeasurable v volume) (i j : Fin 3) :
    eLpNorm (fun x => v x i j) 2 volume ≤ eLpNorm v 2 volume := by
  have h1 : AEStronglyMeasurable (fun x => v x i) volume :=
    (continuous_apply i).comp_aestronglyMeasurable hv
  have h2 : AEStronglyMeasurable (fun x => v x i j) volume :=
    (continuous_apply j).comp_aestronglyMeasurable h1
  exact eLpNorm_mono h2 fun x => (norm_le_pi_norm (v x i) j).trans (norm_le_pi_norm (v x) i)

/-- The energy of the specified gradient of a strong solution changes in time
by the pairing of the time derivative with the Laplacian
(`prop:lps-local-strong`). -/
theorem lps_strong_h1_energy_identity
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hMemU : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∀ s t : ℝ, s ∈ Icc t₀ T → t ∈ Icc t₀ T → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
            ∑ i : Fin 3, Dtu z i * ∑ j : Fin 3, D2u z i j j := by
  obtain ⟨Lu, LD, _, hLDc, _, hLDq, _, hLDid⟩ :=
    lps_strong_time_regularity hU.1 hDerivs hMemU hMemDu hMemD2u hMemDtu
  have hmemD : ∀ t ∈ Icc t₀ T, ∀ i j : Fin 3,
      MemLp (fun x : Vec3 => Du (x, t) i j) 2 volume := by
    intro t ht i j
    have h := (lps_strong_solution_slice_memLp_two hU ht).2
    exact memLp_pi_iff.1 (memLp_pi_iff.1 h i) j
  have hcontD : ∀ t ∈ Icc t₀ T, ∀ i j : Fin 3,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => Du (x, s) i j - Du (x, t) i j) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0) := by
    intro t ht i j
    have hwhole := (hU.2.2.1 t ht).2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwhole
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hdiff : MemLp (fun x : Vec3 => Du (x, s) - Du (x, t)) 2 volume :=
      (lps_strong_solution_slice_memLp_two hU hs).2.sub
        (lps_strong_solution_slice_memLp_two hU ht).2
    have h := lps_component2_eLpNorm_le hdiff.aestronglyMeasurable i j
    simpa only [Pi.sub_apply] using h
  have hslice : ∀ i j : Fin 3, ∀ (t : ℝ) (ht : t ∈ Icc t₀ T),
      ((LD i j ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => Du (x, t) i j := fun i j =>
    lps_curve_eq_of_continuous (F := fun z : Vec3 × ℝ => Du z i j) hU.1 (hLDc i j) (hLDq i j)
      (fun t ht => hmemD t ht i j) (fun t ht => hcontD t ht i j)
  intro s t hs ht hst
  have hnorm : ∀ (r : ℝ) (hr : r ∈ Icc t₀ T),
      ∑ i : Fin 3, ∑ j : Fin 3, ‖LD i j ⟨r, hr⟩‖ ^ 2 =
        ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, r) i j) ^ 2 := by
    intro r hr
    have hint : ∀ i j : Fin 3, Integrable (fun x : Vec3 => (Du (x, r) i j) ^ 2) volume :=
      fun i j => (hmemD r hr i j).integrable_sq
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    exact Finset.sum_congr rfl fun j _ => lps_lp_norm_sq_eq (hslice i j r hr) (hmemD r hr i j)
  have h := hLDid s t hs ht hst
  simp only [Finset.sum_sub_distrib] at h
  rw [← hnorm t ht, ← hnorm s hs]
  linarith only [h]

end ESS.LPS

end

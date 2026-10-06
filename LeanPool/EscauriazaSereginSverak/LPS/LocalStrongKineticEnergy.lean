/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticAssembly

/-!
# The kinetic energy identity of a strong solution

For a strong solution, the fixed-time kinetic energy changes by minus twice
the space-time integral of the squared specified gradient
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A finite sum of slab integrals is the time integral of the sum of the
slice integrals. -/
theorem lps_slab_sum_slice_integral {ι : Type*} (S : Finset ι) {s t : ℝ}
    {F : ι → Vec3 × ℝ → ℝ}
    (hF : ∀ k ∈ S, Integrable (F k) (volume.restrict (vlSlab s t))) :
    ∑ k ∈ S, ∫ z in vlSlab s t, F k z =
      ∫ r in Ioo s t, ∑ k ∈ S, ∫ y : Vec3, F k (y, r) := by
  have hfin : ∀ k ∈ S, Integrable (fun r => ∫ y : Vec3, F k (y, r))
      (volume.restrict (Ioo s t)) := by
    intro k hk
    have h := hF k hk
    rw [vlSlab_measure] at h
    exact h.integral_prod_right
  rw [integral_finsetSum S hfin]
  exact Finset.sum_congr rfl fun k hk => vlSlab_integral_eq (hF k hk)

/-- A component of a vector-valued function is bounded in `L²` by the
function. -/
theorem lps_component1_eLpNorm_le {v : Vec3 → Vec3}
    (hv : AEStronglyMeasurable v volume) (i : Fin 3) :
    eLpNorm (fun x => v x i) 2 volume ≤ eLpNorm v 2 volume :=
  eLpNorm_mono ((continuous_apply i).comp_aestronglyMeasurable hv)
    fun x => norm_le_pi_norm (v x) i

/-- The kinetic energy of a strong solution changes by minus twice the
space-time integral of the squared specified gradient (`prop:lps-local-strong`). -/
theorem lps_strong_kinetic_energy_identity
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hMemU : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemP : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∀ s t : ℝ, s ∈ Icc t₀ T → t ∈ Icc t₀ T → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, (u (x, t) i) ^ 2) +
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
            ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 =
        ∫ x : Vec3, ∑ i : Fin 3, (u (x, s) i) ^ 2 := by
  have hslab : spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T) = vlSlab t₀ T := rfl
  rw [hslab] at hMemU hMemDu hMemD2u hMemDtu hMemP
  have hu : ∀ i, MemLp (fun z : Vec3 × ℝ => u z i) 2 (volume.restrict (vlSlab t₀ T)) :=
    fun i => memLp_pi_iff.1 hMemU i
  have hDt : ∀ i, MemLp (fun z : Vec3 × ℝ => Dtu z i) 2 (volume.restrict (vlSlab t₀ T)) :=
    fun i => memLp_pi_iff.1 hMemDtu i
  have hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vlSlab t₀ T)) :=
    fun i j => memLp_pi_iff.1 (memLp_pi_iff.1 hMemDu i) j
  have hD2 : ∀ i j, MemLp (fun z : Vec3 × ℝ => D2u z i j j) 2
      (volume.restrict (vlSlab t₀ T)) :=
    fun i j => memLp_pi_iff.1 (memLp_pi_iff.1 (memLp_pi_iff.1 hMemD2u i) j) j
  have hkin := lps_strong_kinetic_slice hU hDerivs hu hDu hD2 hDt hMemP
  obtain ⟨Lu, LD, hLuc, _, hLuq, _, hLuid, _⟩ :=
    lps_strong_time_regularity hU.1 hDerivs
      (by rw [hslab]; exact hMemU) (by rw [hslab]; exact hMemDu)
      (by rw [hslab]; exact hMemD2u) (by rw [hslab]; exact hMemDtu)
  have hmemU : ∀ t ∈ Icc t₀ T, ∀ i : Fin 3, MemLp (fun x : Vec3 => u (x, t) i) 2 volume := by
    intro t ht i
    exact memLp_pi_iff.1 (lps_strong_solution_slice_memLp_two hU ht).1 i
  have hcontU : ∀ t ∈ Icc t₀ T, ∀ i : Fin 3,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => u (x, s) i - u (x, t) i) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0) := by
    intro t ht i
    have hwhole := (hU.2.2.1 t ht).1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwhole
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hdiff : MemLp (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume :=
      (lps_strong_solution_slice_memLp_two hU hs).1.sub
        (lps_strong_solution_slice_memLp_two hU ht).1
    have h := lps_component1_eLpNorm_le hdiff.aestronglyMeasurable i
    simpa only [Pi.sub_apply] using h
  have hsliceU : ∀ i : Fin 3, ∀ (t : ℝ) (ht : t ∈ Icc t₀ T),
      ((Lu i ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => u (x, t) i := fun i =>
    lps_curve_eq_of_continuous (F := fun z : Vec3 × ℝ => u z i) hU.1 (hLuc i) (hLuq i)
      (fun t ht => hmemU t ht i) (fun t ht => hcontU t ht i)
  intro s t hs ht hst
  have hnorm : ∀ (r : ℝ) (hr : r ∈ Icc t₀ T),
      ∑ i : Fin 3, ‖Lu i ⟨r, hr⟩‖ ^ 2 = ∫ x : Vec3, ∑ i : Fin 3, (u (x, r) i) ^ 2 := by
    intro r hr
    have hint : ∀ i : Fin 3, Integrable (fun x : Vec3 => (u (x, r) i) ^ 2) volume :=
      fun i => (hmemU r hr i).integrable_sq
    rw [integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl fun i _ => lps_lp_norm_sq_eq (hsliceU i r hr) (hmemU r hr i)
  have hI := hLuid s t hs ht hst
  rw [Finset.sum_sub_distrib, hnorm t ht, hnorm s hs] at hI
  have hsub : vlSlab s t ⊆ vlSlab t₀ T := prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)
  have hmono : ∀ {g : Vec3 × ℝ → ℝ}, MemLp g 2 (volume.restrict (vlSlab t₀ T)) →
      MemLp g 2 (volume.restrict (vlSlab s t)) := fun hg =>
    hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hint1 : ∀ i : Fin 3, Integrable (fun z : Vec3 × ℝ => u z i * Dtu z i)
      (volume.restrict (vlSlab s t)) := fun i => (hmono (hu i)).integrable_mul (hmono (hDt i))
  have hint2 : ∀ k : Fin 3 × Fin 3, Integrable (fun z : Vec3 × ℝ => (Du z k.1 k.2) ^ 2)
      (volume.restrict (vlSlab s t)) := fun k => (hmono (hDu k.1 k.2)).integrable_sq
  have hA : ∫ z in vlSlab s t, ∑ i : Fin 3, u z i * Dtu z i =
      ∫ r in Ioo s t, ∑ i : Fin 3, ∫ y : Vec3, u (y, r) i * Dtu (y, r) i := by
    rw [integral_finsetSum _ (fun i _ => hint1 i)]
    exact lps_slab_sum_slice_integral (Finset.univ : Finset (Fin 3))
      (F := fun i z => u z i * Dtu z i) (fun i _ => hint1 i)
  have hB : ∫ z in vlSlab s t, ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 =
      ∫ r in Ioo s t, ∑ k : Fin 3 × Fin 3, ∫ y : Vec3, (Du (y, r) k.1 k.2) ^ 2 := by
    have h1 : ∫ z in vlSlab s t, ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 =
        ∑ k : Fin 3 × Fin 3, ∫ z in vlSlab s t, (Du z k.1 k.2) ^ 2 := by
      rw [Fintype.sum_prod_type]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint2 (i, j))]
      exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint2 (i, j)
    rw [h1]
    exact lps_slab_sum_slice_integral (Finset.univ : Finset (Fin 3 × Fin 3))
      (F := fun k z => (Du z k.1 k.2) ^ 2) (fun k _ => hint2 k)
  have hae : ∀ᵐ r ∂(volume.restrict (Ioo s t)),
      ∑ i : Fin 3, ∫ y : Vec3, u (y, r) i * Dtu (y, r) i =
        -∑ k : Fin 3 × Fin 3, ∫ y : Vec3, (Du (y, r) k.1 k.2) ^ 2 := by
    have hk := (ae_restrict_iff' measurableSet_Ioo).1 hkin
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hk] with r hr hrI
    have := hr ⟨lt_of_le_of_lt hs.1 hrI.1, lt_of_lt_of_le hrI.2 ht.2⟩
    rw [Fintype.sum_prod_type]
    simp only [mul_comm (u (_, r) _)]
    exact this
  have hAB : ∫ z in vlSlab s t, ∑ i : Fin 3, u z i * Dtu z i =
      -∫ z in vlSlab s t, ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 := by
    rw [hA, hB, ← integral_neg]
    exact setIntegral_congr_ae measurableSet_Ioo
      ((ae_restrict_iff' measurableSet_Ioo).1 hae)
  have hIS : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t), ∑ i : Fin 3, u z i * Dtu z i =
      ∫ z in vlSlab s t, ∑ i : Fin 3, u z i * Dtu z i := rfl
  rw [hIS, hAB] at hI
  change (∫ x : Vec3, ∑ i : Fin 3, (u (x, t) i) ^ 2) +
    2 * ∫ z in vlSlab s t, ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 =
    ∫ x : Vec3, ∑ i : Fin 3, (u (x, s) i) ^ 2
  linarith only [hI]

end ESS.LPS

end

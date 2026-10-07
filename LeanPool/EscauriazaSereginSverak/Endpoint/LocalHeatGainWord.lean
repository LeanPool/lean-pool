/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainCore

/-!
# The energy estimate for each spatial derivative of the cutoff solution

Each spatial derivative `∂^β w`, `|β| ≤ m`, of the cutoff solution solves the
heat equation on `ℝ³ × (a, b)` with a square-integrable source: `H` itself for
`β = []`, and the divergence-form source `∂_k (∂^{β'} H)` for
`β = β' ++ [k]`. It vanishes near `t = a`, so the energy estimate of
`lem:localized-vorticity-energy` (`vlHeat_energy`) gives a curve continuous in
`L²` and a square-integrable weak gradient, bounded by the data.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Slab integrals of squares as iterated integrals. -/
theorem integral_slab_sq_eq {a b : ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (vlSlab a b))) :
    ∫ p in vlSlab a b, F p ^ 2 = ∫ s in Ioo a b, ∫ x, F (x, s) ^ 2 := by
  have h := hF.integrable_sq
  rw [vlSlab_measure] at h ⊢
  exact integral_prod_symm (fun p => F p ^ 2) h

theorem integrable_slab_sq_slices {a b : ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (vlSlab a b))) :
    Integrable (fun s => ∫ x, F (x, s) ^ 2) (volume.restrict (Ioo a b)) := by
  have h := hF.integrable_sq
  rw [vlSlab_measure] at h
  exact h.integral_prod_right

/-- The output of the energy estimate, with the data energy bounded by `M`. -/
theorem vlHeat_result {a b : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ}
    (sol : VlHeatSolution a b w H f (fun _ => 0)) (M : ℝ)
    (hM : (∑ j : Fin 3, ∫ p in vlSlab a b, H j p ^ 2) + (∫ p in vlSlab a b, w p ^ 2) +
      (∫ p in vlSlab a b, f p ^ 2) ≤ M) :
    ∃ (Zc : Icc a b → Lp ℝ 2 (volume : Measure Vec3)) (Dg : Fin 3 → Vec3 × ℝ → ℝ),
      Continuous Zc ∧
      (∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ht : t ∈ Icc a b,
        (Zc ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => w (x, t)) ∧
      (∀ j, MemLp (Dg j) 2 (volume.restrict (vlSlab a b))) ∧
      (∀ j, IsSpaceTimeWeakPartial (vlSlab a b) j w (Dg j)) ∧
      ∀ t, ‖Zc t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg j p ^ 2 ≤ 2 * M := by
  obtain ⟨Zc, Dg, hZc, -, hslice, hDgL, hDgw, hbound⟩ := vlHeat_energy sol
  -- the data energy
  let g : ℝ → ℝ := fun s => (∑ j : Fin 3, ∫ x, H j (x, s) ^ 2) + (∫ x, w (x, s) ^ 2) +
    ∫ x, f (x, s) ^ 2
  have hg : Integrable g (volume.restrict (Ioo a b)) :=
    ((integrable_finsetSum _ fun j _ => integrable_slab_sq_slices (sol.H_L2 j)).add
      (integrable_slab_sq_slices sol.w_L2)).add (integrable_slab_sq_slices sol.f_L2)
  have hg0 : ∀ s, 0 ≤ g s := fun s => add_nonneg (add_nonneg
    (Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)
    (integral_nonneg fun x => sq_nonneg _)) (integral_nonneg fun x => sq_nonneg _)
  have hE (t : Icc a b) : vlDataEnergy (fun _ => 0) w H f a t.1 ≤ M := by
    have h1 : vlDataEnergy (fun _ => 0) w H f a t.1 = ∫ s in Ioo a t.1, g s := by
      simp [vlDataEnergy, g]
    have h2 : ∫ s in Ioo a t.1, g s ≤ ∫ s in Ioo a b, g s :=
      setIntegral_mono_set hg (ae_of_all _ fun s => hg0 s)
        (ae_of_all _ (Ioo_subset_Ioo_right t.2.2))
    have h3 : ∫ s in Ioo a b, g s = (∑ j : Fin 3, ∫ p in vlSlab a b, H j p ^ 2) +
        (∫ p in vlSlab a b, w p ^ 2) + ∫ p in vlSlab a b, f p ^ 2 := by
      have i1 : Integrable (fun s => ∑ j : Fin 3, ∫ x, H j (x, s) ^ 2)
          (volume.restrict (Ioo a b)) :=
        integrable_finsetSum _ fun j _ => integrable_slab_sq_slices (sol.H_L2 j)
      have i2 := integrable_slab_sq_slices sol.w_L2
      have i3 := integrable_slab_sq_slices sol.f_L2
      have i12 : Integrable (fun s => (∑ j : Fin 3, ∫ x, H j (x, s) ^ 2) + ∫ x, w (x, s) ^ 2)
          (volume.restrict (Ioo a b)) := i1.add i2
      change ∫ s in Ioo a b, ((∑ j : Fin 3, ∫ x, H j (x, s) ^ 2) + (∫ x, w (x, s) ^ 2) +
        ∫ x, f (x, s) ^ 2) = _
      rw [integral_add i12 i3, integral_add i1 i2,
        integral_finsetSum _ fun j _ => integrable_slab_sq_slices (sol.H_L2 j),
        integral_slab_sq_eq sol.w_L2, integral_slab_sq_eq sol.f_L2]
      congr 2
      exact Finset.sum_congr rfl fun j _ => (integral_slab_sq_eq (sol.H_L2 j)).symm
    rw [h1]
    exact h2.trans (h3.le.trans hM)
  refine ⟨Zc, Dg, hZc, hslice, hDgL, fun j φ hφ hφc hφV => hDgw j φ ⟨hφ, hφc, hφV⟩,
    fun t => ?_⟩
  have hb : b ∈ Icc a b := right_mem_Icc.2 sol.lt.le
  have hbt := hbound ⟨b, hb⟩
  have hbE := hE ⟨b, hb⟩
  have htt := hbound t
  have htE := hE t
  have hsum_nonneg : 0 ≤ ∑ j : Fin 3, ∫ p in vlSlab a t.1, Dg j p ^ 2 :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun p => sq_nonneg _
  have hnorm_nonneg : 0 ≤ ‖Zc ⟨b, hb⟩‖ ^ 2 := sq_nonneg _
  linarith only [hbt, hbE, htt, htE, hsum_nonneg, hnorm_nonneg]

/-- The energy estimate for each spatial derivative of order at most `m`. -/
theorem localHeatGain_wordEnergy {m : ℕ} (hm1 : 1 ≤ m) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    {Dw DH : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hDw : IsSpaceTimeFamily m (vlSlab a b) Dw) (hDH : IsSpaceTimeFamily (m - 1) (vlSlab a b) DH)
    (hheat : IsHeatSolutionOn univ (Ioo a b) (Dw []) (DH []))
    (hsm : ∀ α, StronglyMeasurable (Dw α)) (hsmH : ∀ α, StronglyMeasurable (DH α))
    (hz0 : ∀ α (p : Vec3 × ℝ), p.2 < a + δ → Dw α p = 0)
    (β : List (Fin 3)) (hβ : β ∈ sobolevWords m) :
    ∃ (Zc : Icc a b → Lp ℝ 2 (volume : Measure Vec3)) (Dg : Fin 3 → Vec3 × ℝ → ℝ),
      Continuous Zc ∧
      (∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ht : t ∈ Icc a b,
        (Zc ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => Dw β (x, t)) ∧
      (∀ j, MemLp (Dg j) 2 (volume.restrict (vlSlab a b))) ∧
      (∀ j, IsSpaceTimeWeakPartial (vlSlab a b) j (Dw β) (Dg j)) ∧
      ∀ t, ‖Zc t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg j p ^ 2 ≤
        2 * ((∑ α ∈ sobolevWords (m - 1), ∫ p in vlSlab a b, DH α p ^ 2) +
          ∫ p in vlSlab a b, Dw β p ^ 2) := by
  have hβm : β.length ≤ m := mem_sobolevWords.1 hβ
  have hNDH0 : ∀ α ∈ sobolevWords (m - 1), 0 ≤ ∫ p in vlSlab a b, DH α p ^ 2 :=
    fun α _ => integral_nonneg fun p => sq_nonneg _
  have hzeroL2 : MemLp (fun _ : Vec3 × ℝ => (0 : ℝ)) 2 (volume.restrict (vlSlab a b)) :=
    MemLp.zero
  rcases List.eq_nil_or_concat β with rfl | ⟨β'', k, hk⟩
  · -- the source form
    have hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
        ∫ p in vlSlab a b, Dw [] p * (-CKN.timePartial φ p -
            ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) =
          ∫ p in vlSlab a b, (-(∑ j : Fin 3, (fun _ : Fin 3 => fun _ : Vec3 × ℝ => (0 : ℝ)) j p *
            CKN.spatialPartial φ j p) + DH [] p * φ p) := by
      intro φ hφ
      refine Eq.trans (hheat φ hφ.1 hφ.2.1 hφ.2.2) ?_
      exact integral_congr_ae (ae_of_all _ fun p => by simp)
    have sol : VlHeatSolution a b (Dw []) (fun _ => fun _ => 0) (DH []) (fun _ => 0) :=
      { lt := hab
        w_meas := hsm []
        H_meas := fun _ => stronglyMeasurable_const
        f_meas := hsmH []
        w_L2 := hDw.memL2 [] (Nat.zero_le _)
        H_L2 := fun _ => hzeroL2
        f_L2 := hDH.memL2 [] (Nat.zero_le _)
        w₀_L2 := MemLp.zero
        weak := hweak
        trace := heatSolution_trace_zero hab hδ (hDw.memL2 [] (Nat.zero_le _))
          (fun _ => hzeroL2) (hDH.memL2 [] (Nat.zero_le _)) hweak (hz0 []) }
    refine vlHeat_result sol _ ?_
    have hmem : ([] : List (Fin 3)) ∈ sobolevWords (m - 1) := mem_sobolevWords.2 (Nat.zero_le _)
    have hle := Finset.single_le_sum hNDH0 hmem
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero,
      Finset.sum_const_zero, zero_add]
    linarith only [hle]
  · -- the divergence form
    rw [List.concat_eq_append] at hk
    subst hk
    have hβ'' : β''.length ≤ m - 1 := by
      simp only [List.length_append, List.length_singleton] at hβm
      omega
    let H : Fin 3 → Vec3 × ℝ → ℝ := fun j => if j = k then DH β'' else fun _ => 0
    have hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
        ∫ p in vlSlab a b, Dw (β'' ++ [k]) p * (-CKN.timePartial φ p -
            ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) =
          ∫ p in vlSlab a b, (-(∑ j : Fin 3, H j p * CKN.spatialPartial φ j p) +
            (fun _ : Vec3 × ℝ => (0 : ℝ)) p * φ p) := by
      intro φ hφ
      refine Eq.trans (heatSolution_family_flux hDw hDH hheat hm1 β'' hβ'' k φ hφ.1 hφ.2.1
        hφ.2.2) ?_
      rw [← integral_neg]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      simp only [H, zero_mul, add_zero]
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
      simp
    have hHm : ∀ j, StronglyMeasurable (H j) := fun j => by
      by_cases hj : j = k
      · simp only [H, hj, ite_true]; exact hsmH β''
      · simp only [H, hj, ite_false]; exact stronglyMeasurable_const
    have hHL : ∀ j, MemLp (H j) 2 (volume.restrict (vlSlab a b)) := fun j => by
      by_cases hj : j = k
      · simp only [H, hj, ite_true]; exact hDH.memL2 β'' hβ''
      · simp only [H, hj, ite_false]; exact hzeroL2
    have sol : VlHeatSolution a b (Dw (β'' ++ [k])) H (fun _ => 0) (fun _ => 0) :=
      { lt := hab
        w_meas := hsm _
        H_meas := hHm
        f_meas := stronglyMeasurable_const
        w_L2 := hDw.memL2 _ hβm
        H_L2 := hHL
        f_L2 := hzeroL2
        w₀_L2 := MemLp.zero
        weak := hweak
        trace := heatSolution_trace_zero hab hδ (hDw.memL2 _ hβm) hHL hzeroL2 hweak (hz0 _) }
    refine vlHeat_result sol _ ?_
    have hmem : β'' ∈ sobolevWords (m - 1) := mem_sobolevWords.2 hβ''
    have hle := Finset.single_le_sum hNDH0 hmem
    have hH : ∑ j : Fin 3, ∫ p in vlSlab a b, H j p ^ 2 = ∫ p in vlSlab a b, DH β'' p ^ 2 := by
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [H, hj]) (by simp)]
      simp [H]
    rw [hH]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, add_zero]
    linarith only [hle]

end ESS

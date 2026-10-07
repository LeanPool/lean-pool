/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopfMomentum
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongEnergyIdentity
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopf
public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionLerayHopfCore
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinLerayHopf

/-!
# A strong solution is a Leray–Hopf solution

The translate of a strong solution on `[t₀, T]` to `[0, T - t₀]`, with an
initial datum that is its almost-everywhere initial slice, satisfies every
clause of the Leray–Hopf definition (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

open ESS.LPS

/-- A strong solution on `[t₀, T]`, translated in time to `[0, T - t₀]`, with
datum its almost-everywhere initial slice, is a Leray–Hopf solution
(`prop:lps-local-strong`). -/
theorem lps_strong_solution_is_leray_hopf
    {t₀ T : ℝ} {b : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    (hb : IsInJ b)
    (hTrace : (fun x : Vec3 => u (x, t₀)) =ᵐ[volume] b) :
    IsLerayHopfSolution (T - t₀) b
      (fun z : ParabolicPoint => u (z.1, t₀ + z.2))
      (fun z i => Du (z.1, t₀ + z.2) i) := by
  have hT : 0 < T - t₀ := sub_pos.2 hU.1
  have hIcc : ∀ s ∈ Icc (0 : ℝ) (T - t₀), t₀ + s ∈ Icc t₀ T := fun s hs =>
    ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  obtain ⟨D2u, Dtu, hDerivs, hMemU, hMemDu, hMemD2u, hMemDtu⟩ :=
    lps_strong_solution_derivative_data hU
  have hmp : MeasurePreserving (lpsShift t₀)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (T - t₀))))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) := by
    have h := lps_shift_measurePreserving t₀ 0 (T - t₀)
    rwa [add_zero, add_sub_cancel] at h
  have hmem : ∀ s ∈ Icc (0 : ℝ) (T - t₀), MemLp
      (fun x : Vec3 => (fun z : ParabolicPoint => u (z.1, t₀ + z.2)) (x, s)) 2 volume :=
    fun s hs => (lps_strong_solution_slice_memLp_two hU (hIcc s hs)).1
  have hcont : ∀ s ∈ Icc (0 : ℝ) (T - t₀), Tendsto (fun r => eLpNorm
      (fun x : Vec3 => (fun z : ParabolicPoint => u (z.1, t₀ + z.2)) (x, r) -
        (fun z : ParabolicPoint => u (z.1, t₀ + z.2)) (x, s)) 2 volume)
      (𝓝[Icc 0 (T - t₀)] s) (𝓝 0) := by
    intro s hs
    have h := (hU.2.2.1 (t₀ + s) (hIcc s hs)).1
    have hmap : Tendsto (fun r : ℝ => t₀ + r) (𝓝[Icc 0 (T - t₀)] s)
        (𝓝[Icc t₀ T] (t₀ + s)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_const.add continuous_id).tendsto s).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using hIcc r hr
    exact h.comp hmap
  have hU2 : MemLp (fun z : ParabolicPoint => u (z.1, t₀ + z.2)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (T - t₀)))) :=
    hMemU.comp_measurePreserving hmp
  have hDU2 : MemLp (fun z : ParabolicPoint => (fun i => Du (z.1, t₀ + z.2) i : Fin 3 → Vec3)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (T - t₀)))) :=
    hMemDu.comp_measurePreserving hmp
  obtain ⟨_, _, _, _, _, _, hkin⟩ := lps_unregularised_h1_energy_identity hU
  have hsqcont := pvLH_sq_continuousOn (T := T - t₀)
    (U := fun z : ParabolicPoint => u (z.1, t₀ + z.2)) hmem hcont
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hsqcont
  refine ⟨hT, hb, hU2.aestronglyMeasurable, hDU2.aestronglyMeasurable, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the slice bound
    have hae : ∀ᵐ s ∂(volume.restrict (Ioo 0 (T - t₀))),
        ∫⁻ x : Vec3, ‖u (x, t₀ + s)‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal M := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Eventually.of_forall fun s hs => ?_
      have hs' : s ∈ Icc (0 : ℝ) (T - t₀) := Ioo_subset_Icc_self hs
      calc ∫⁻ x : Vec3, ‖u (x, t₀ + s)‖ₑ ^ (2 : ℝ) ≤
            ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀ + s))) ^ (2 : ℝ) :=
          lintegral_mono fun x => enorm_sq_le_vec3Euclidean_sq _
        _ = ENNReal.ofReal (∫ x : Vec3, ∑ k : Fin 3, u (x, t₀ + s) k * u (x, t₀ + s) k) :=
          serrin_lintegral_eucl_sq (hmem s hs')
        _ ≤ ENNReal.ofReal M :=
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa using hM s hs'))
    exact lt_of_le_of_lt (essSup_le_of_ae_le _ hae) ENNReal.ofReal_lt_top
  · -- joint square integrability
    have h1 : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (T - t₀)),
        ‖u (z.1, t₀ + z.2)‖ₑ ^ (2 : ℝ)) < ⊤ := by
      have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hU2
      simpa using this
    have h2 : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (T - t₀)),
        ‖(fun i => Du (z.1, t₀ + z.2) i : Fin 3 → Vec3)‖ₑ ^ (2 : ℝ)) < ⊤ := by
      have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hDU2
      simpa using this
    rw [lintegral_add_left' (hU2.aestronglyMeasurable.enorm.pow_const _)]
    exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  · -- weak gradients
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun s hs i => ?_
    exact lps_strong_solution_slice_weak_gradient hU (hIcc s (Ioo_subset_Icc_self hs)) i
  · -- solenoidal slices
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun s hs ψ => ?_
    exact (lps_strong_solution_slice_weak_div_free hU (hIcc s (Ioo_subset_Icc_self hs))).2 ψ
  · -- weak continuity
    exact fun w hw => pvLH_pairing_continuousOn (T := T - t₀)
      (U := fun z : ParabolicPoint => u (z.1, t₀ + z.2)) hmem hcont hw
  · -- the momentum equation
    exact lps_shift_momentum hU
  · -- the energy inequality
    intro t₁ ht₁
    have hDt : MemLp (fun z : ParabolicPoint => (fun i => Du (z.1, t₀ + z.2) i : Fin 3 → Vec3)) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁))) :=
      hDU2.mono_measure (serrin_slab_restrict_le ht₁.2)
    have hDint : Integrable (fun q : ParabolicPoint => ∑ k : Fin 3, ∑ j : Fin 3,
        Du (q.1, t₀ + q.2) k j * Du (q.1, t₀ + q.2) k j)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁))) :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
        (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j).integrable_mul
          (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j)
    have hgrad : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁),
        ENNReal.ofReal (spatialGradientSq (fun z : ParabolicPoint => u (z.1, t₀ + z.2))
          (fun z i => Du (z.1, t₀ + z.2) i) z)) =
        ENNReal.ofReal (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁),
          ∑ k : Fin 3, ∑ j : Fin 3, Du (q.1, t₀ + q.2) k j * Du (q.1, t₀ + q.2) k j) := by
      rw [ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall fun q =>
        Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _)]
      refine lintegral_congr fun q => ?_
      simp only [spatialGradientSq, pow_two]
    have hD0 : 0 ≤ ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁),
        ∑ k : Fin 3, ∑ j : Fin 3, Du (q.1, t₀ + q.2) k j * Du (q.1, t₀ + q.2) k j :=
      integral_nonneg fun q => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
        mul_self_nonneg _
    have hU0 : 0 ≤ ∫ x : Vec3, ∑ k : Fin 3, u (x, t₀ + t₁) k * u (x, t₀ + t₁) k :=
      integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
    -- the kinetic identity, translated
    have hk := hkin t₀ (t₀ + t₁) (left_mem_Icc.2 hU.1.le) (hIcc t₁ ht₁)
      (by linarith only [ht₁.1])
    have hmp1 : MeasurePreserving (lpsShift t₀)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁)))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (t₀ + t₁)))) := by
      have h := lps_shift_measurePreserving t₀ 0 t₁
      rwa [add_zero] at h
    have hcv := hmp1.integral_comp (lps_shift_measurableEmbedding t₀)
      (fun w : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3, (Du w i j) ^ 2)
    have e2 : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (t₀ + t₁)),
        ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 =
        ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁),
          ∑ k : Fin 3, ∑ j : Fin 3, Du (q.1, t₀ + q.2) k j * Du (q.1, t₀ + q.2) k j := by
      rw [← hcv]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp only [lpsShift, pow_two]
    have e1 : ∫ x : Vec3, ∑ i : Fin 3, (u (x, t₀ + t₁) i) ^ 2 =
        ∫ x : Vec3, ∑ k : Fin 3, u (x, t₀ + t₁) k * u (x, t₀ + t₁) k := by
      simp only [pow_two]
    have e0 : ∫ x : Vec3, ∑ i : Fin 3, (u (x, t₀) i) ^ 2 =
        ∫ x : Vec3, ∑ k : Fin 3, b x k * b x k := by
      refine integral_congr_ae ?_
      filter_upwards [hTrace] with x hx
      simp only [hx, pow_two]
    rw [e2, e1, e0] at hk
    change ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3, ENNReal.ofReal
        (vec3EuclideanNorm (u (x, t₀ + t₁))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₁),
        ENNReal.ofReal (spatialGradientSq (fun z : ParabolicPoint => u (z.1, t₀ + z.2))
          (fun z i => Du (z.1, t₀ + z.2) i) z)) ≤
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (b x)) ^ (2 : ℝ)
    rw [serrin_lintegral_eucl_sq (hmem t₁ ht₁), serrin_lintegral_eucl_sq hb.1, hgrad,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) hD0,
      ← ENNReal.ofReal_mul (by norm_num)]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    linarith only [hk]
  · -- the strong initial trace
    have hnear : Icc 0 (T - t₀) ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self
    have h00 : (0 : ℝ) ∈ Icc 0 (T - t₀) := left_mem_Icc.2 hT.le
    have hN : Tendsto (fun s => (eLpNorm (fun x : Vec3 => u (x, t₀ + s) - u (x, t₀ + 0)) 2
        volume).toReal) (𝓝[>] 0) (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        ((hcont 0 h00).mono_left (nhdsWithin_le_of_mem hnear))
      rw [ENNReal.toReal_zero] at h
      exact h
    have hreal : Tendsto (fun s => ∫ x : Vec3, ∑ k : Fin 3,
        (u (x, t₀ + s) - u (x, t₀ + 0)) k * (u (x, t₀ + s) - u (x, t₀ + 0)) k) (𝓝[>] 0)
        (𝓝 0) := by
      have hlim : Tendsto (fun s => 3 * ((eLpNorm (fun x : Vec3 =>
          u (x, t₀ + s) - u (x, t₀ + 0)) 2 volume).toReal * (eLpNorm (fun x : Vec3 =>
          u (x, t₀ + s) - u (x, t₀ + 0)) 2 volume).toReal)) (𝓝[>] 0) (𝓝 0) := by
        simpa using (hN.mul hN).const_mul 3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun s => integral_nonneg fun x =>
          Finset.sum_nonneg fun k _ => mul_self_nonneg _) ?_
      filter_upwards [hnear] with s hs
      exact (le_abs_self _).trans
        (pvLH_pair_le ((hmem s hs).sub (hmem 0 h00)) ((hmem s hs).sub (hmem 0 h00)))
    have h := ENNReal.tendsto_ofReal hreal
    rw [ENNReal.ofReal_zero] at h
    refine h.congr' ?_
    filter_upwards [hnear] with s hs
    have hd : MemLp (fun x : Vec3 => u (x, t₀ + s) - b x) 2 volume := (hmem s hs).sub hb.1
    change ENNReal.ofReal (∫ x : Vec3, ∑ k : Fin 3,
        (u (x, t₀ + s) - u (x, t₀ + 0)) k * (u (x, t₀ + s) - u (x, t₀ + 0)) k) =
      ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀ + s) - b x)) ^ (2 : ℝ)
    rw [serrin_lintegral_eucl_sq hd]
    refine congrArg ENNReal.ofReal (integral_congr_ae ?_)
    filter_upwards [hTrace] with x hx
    simp only [add_zero, hx]

end ESS

end

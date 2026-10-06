/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderGain
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderBound
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLBound
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLSup
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceH2
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSourceSlice
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSpaceTimeProductMixed

/-!
# The base of the regularity ladder

`prop:lps-smoothing`: a strong solution has an `L²(I; H³)` family with `L²`-continuous `H²`
slices on `[t₀ + δ, T]` for every `δ > 0`. Almost every slice has a uniformly bounded `H²`
energy (the `H²` bound of the slice equation together with the uniform bound of the time
derivative), so the convection field is an `L²(I; H¹)` family and the heat gain applies.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A curve of real functions that is `L²`-continuous on a compact interval has bounded
energy there. -/
private theorem lps_ladder_energy_bound {a b : ℝ} {f : ℝ → Vec3 → ℝ}
    (hf : ∀ t ∈ Icc a b, MemLp (f t) 2 volume)
    (hcont : ∀ t ∈ Icc a b, Tendsto (fun s => eLpNorm (fun x : Vec3 => f s x - f t x) 2 volume)
      (𝓝[Icc a b] t) (𝓝 0)) :
    ∃ R : ℝ, ∀ t ∈ Icc a b, ∫ x : Vec3, (f t x) ^ 2 ≤ R := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (lps_l2Norm_continuousOn hf hcont)
  refine ⟨R ^ 2, fun t ht => ?_⟩
  rw [lps_integral_sq_eq_toReal_sq (hf t ht)]
  have h1 : (eLpNorm (f t) 2 volume).toReal ≤ R := by
    have := hR t ht
    rwa [Real.norm_of_nonneg ENNReal.toReal_nonneg] at this
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg h1 2

/-- A componentwise comparison of curves transfers `L²` continuity. -/
private theorem lps_ladder_tendsto_of_le {S : Set ℝ} {t : ℝ} {E : Type*} [NormedAddCommGroup E]
    {F : ℝ → Vec3 → E} {G : ℝ → Vec3 → ℝ}
    (h : Tendsto (fun s => eLpNorm (fun x : Vec3 => F s x) 2 volume) (𝓝[S] t) (𝓝 0))
    (hmeas : ∀ s ∈ S, AEStronglyMeasurable (G s) volume)
    (hle : ∀ s x, ‖G s x‖ ≤ ‖F s x‖) :
    Tendsto (fun s => eLpNorm (fun x : Vec3 => G s x) 2 volume) (𝓝[S] t) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact eLpNorm_mono (hmeas s hs) fun x => hle s x

/-- The `H²` energy of the slices of a strong solution is uniformly bounded for almost every
time in `(t₀ + δ/2, T)` (`prop:lps-smoothing`). -/
theorem lps_sliceH2_ae_bound {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {δ : ℝ} (hδ : 0 < δ) (hδT : t₀ + δ < T) :
    ∃ K : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ / 2) T)), lpsSliceH2 u Du D2u t ≤ K := by
  obtain ⟨C2, hC2, hH2⟩ := lps_slice_H2_bound
  have hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
    fun t ht => (lps_strong_solution_slice_memLp_two hsol ht).1
  have hcont := hsol.2.2.1
  obtain ⟨B, hB0, hB⟩ := lps_dtu_slice_bound hsol.1 hderiv hu hDu hD2u hDtu hsol.2.2.2.2.1
    (LPS.lps_strong_solution_equation_Dtu hsol hderiv hDtu) (LPS.lps_strong_solution_div_free hsol)
    hslice (fun t ht => (hcont t ht).1) (δ := δ / 2) (by linarith only [hδ])
    (by linarith only [hδT, hδ])
  -- uniform bounds for the energies of `u` and `∇u`
  have hR0 : ∀ i : Fin 3, ∃ R : ℝ, ∀ t ∈ Icc t₀ T, ∫ x : Vec3, (u (x, t) i) ^ 2 ≤ R := by
    intro i
    refine lps_ladder_energy_bound (f := fun t x => u (x, t) i)
      (fun t ht => (hslice t ht).eval i) fun t ht => ?_
    refine lps_ladder_tendsto_of_le (F := fun s x => u (x, s) - u (x, t)) (hcont t ht).1
      (fun s hs => (((hslice s hs).eval i).sub ((hslice t ht).eval i)).aestronglyMeasurable) ?_
    intro s x
    exact norm_le_pi_norm (u (x, s) - u (x, t)) i
  have hR1 : ∀ i j : Fin 3, ∃ R : ℝ, ∀ t ∈ Icc t₀ T, ∫ x : Vec3, (Du (x, t) i j) ^ 2 ≤ R := by
    intro i j
    refine lps_ladder_energy_bound (f := fun t x => Du (x, t) i j)
      (fun t ht => ((lps_strong_solution_slice_memLp_two hsol ht).2.eval i).eval j)
      fun t ht => ?_
    refine lps_ladder_tendsto_of_le (F := fun s x => Du (x, s) - Du (x, t)) (hcont t ht).2
      (fun s hs => ((((lps_strong_solution_slice_memLp_two hsol hs).2.eval i).eval j).sub
        (((lps_strong_solution_slice_memLp_two hsol ht).2.eval i).eval j)).aestronglyMeasurable) ?_
    intro s x
    exact (norm_le_pi_norm ((Du (x, s) - Du (x, t)) i) j).trans
      (norm_le_pi_norm (Du (x, s) - Du (x, t)) i)
  choose R0 hR0 using hR0
  choose R1 hR1 using hR1
  set K0 : ℝ := ∑ i, R0 i with hK0
  set K1 : ℝ := ∑ i, ∑ j, R1 i j with hK1
  set Rm : ℝ := 2 * Real.sqrt (3 * B) + C2 * K1 ^ (3 / 2 : ℝ) with hRm
  refine ⟨K0 + K1 + Rm ^ 2, ?_⟩
  have hsub : Ioo (t₀ + δ / 2) T ⊆ Ioo t₀ T := Ioo_subset_Ioo (by linarith only [hδ]) le_rfl
  have hgood := ae_restrict_of_ae_restrict_of_subset hsub
    (lps_strong_good_slices hsol hderiv hu hDu hD2u hDtu)
  have hpress := ae_restrict_of_ae_restrict_of_subset hsub
    (lps_strong_slice_pressure_equation hsol hderiv hu hDu hD2u hDtu)
  have hfam := ae_restrict_of_ae_restrict_of_subset hsub
    (ae_all_iff.mpr fun i : Fin 3 => LPS.lps_sobolevFamily_spatialSlices_ae
      (lps_strong_isL2SobolevFamily hderiv hu hDu hD2u i))
  filter_upwards [hB, hgood, hpress, hfam, ae_restrict_mem measurableSet_Ioo]
    with t hBt hg hp hf htI
  have htIcc : t ∈ Icc t₀ T := ⟨by linarith only [htI.1, hδ], htI.2.le⟩
  obtain ⟨hDt, -, -, hdiv⟩ := hg
  obtain ⟨Gq, hGq, hq, hwq, heqs⟩ := hp
  have hfam' : ∀ i, IsSobolevFamilyOn 2 (Set.univ : Set Vec3) (fun x => u (x, t) i)
      (fun α => match α with
        | [] => fun x => u (x, t) i | [j] => fun x => Du (x, t) i j
        | [j, k] => fun x => D2u (x, t) i j k | _ => fun _ => 0) := by
    intro i
    have e : (fun α : List (Fin 3) => match α with
        | [] => fun x : Vec3 => u (x, t) i | [j] => fun x : Vec3 => Du (x, t) i j
        | [j, k] => fun x : Vec3 => D2u (x, t) i j k | _ => fun _ => 0) =
        fun α x => lpsStrongFamily u Du D2u i α (x, t) := by
      funext α
      match α with
      | [] => rfl
      | [j] => rfl
      | [j, k] => rfl
      | _ :: _ :: _ :: _ => rfl
    rw [e]
    exact hf i
  have hH := hH2 (fun i x => u (x, t) i) (fun i x => Dtu (x, t) i) Gq
    (fun i j x => Du (x, t) i j) (fun i j k x => D2u (x, t) i j k) (fun x => p (x, t))
    hfam' (fun i => hDt.eval i) hq hGq hwq hdiv heqs
  -- the bound for the second derivatives
  have hE1 : ∑ i, ∑ j, ∫ x : Vec3, (Du (x, t) i j) ^ 2 ≤ K1 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hR1 i j t htIcc
  have hE1nn : 0 ≤ ∑ i, ∑ j, ∫ x : Vec3, (Du (x, t) i j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hG : Real.sqrt (∑ i, ∫ x : Vec3, (Dtu (x, t) i) ^ 2) ≤ Real.sqrt (3 * B) := by
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ∫ x : Vec3, (Dtu (x, t) i) ^ 2 ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum fun i _ => hBt i
      _ = 3 * B := by simp
  have hpow : (∑ i, ∑ j, ∫ x : Vec3, (Du (x, t) i j) ^ 2) ^ (3 / 2 : ℝ) ≤ K1 ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hE1nn hE1 (by norm_num)
  have hE2 : Real.sqrt (∑ i, ∑ j, ∑ k, ∫ x : Vec3, (D2u (x, t) i j k) ^ 2) ≤ Rm := by
    refine hH.trans ?_
    rw [hRm]
    gcongr
  have hE2' : ∑ i, ∑ j, ∑ k, ∫ x : Vec3, (D2u (x, t) i j k) ^ 2 ≤ Rm ^ 2 :=
    (Real.sqrt_le_iff.mp hE2).2
  have hexp : lpsSliceH2 u Du D2u t =
      ∑ i, ((∫ y : Vec3, (u (y, t) i) ^ 2) + ∑ j, (∫ y : Vec3, (Du (y, t) i j) ^ 2) +
        ∑ j, ∑ k, (∫ y : Vec3, (D2u (y, t) i j k) ^ 2)) := by
    unfold lpsSliceH2
    exact Finset.sum_congr rfl fun i _ =>
      lps_sum_sobolevWords_two (fun α => ∫ y : Vec3, (lpsStrongFamily u Du D2u i α (y, t)) ^ 2)
  rw [hexp, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hE0 : ∑ i, ∫ y : Vec3, (u (y, t) i) ^ 2 ≤ K0 :=
    Finset.sum_le_sum fun i _ => hR0 i t htIcc
  linarith only [hE0, hE1, hE2']

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLCheb
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLLimit
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainWord
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The initial layer of the time-difference quotients

`prop:lps-smoothing`: the mean over `[t₀, t₀ + δ]` of the squared `L²` norms of the time-difference
quotients of a strong solution is at most the `L²` norm squared of its weak time derivative.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The squared `L²` norm of the weak time derivative is integrable in time. -/
theorem lps_dtu_normSq_integrable {t₀ T : ℝ} {Dtu : ParabolicPoint → Vec3}
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    Integrable (fun σ => ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, σ) i) ^ 2)
      (volume.restrict (Ioo t₀ T)) := by
  have hi : ∀ i : Fin 3, Integrable (fun σ => ∫ x : Vec3, (Dtu (x, σ) i) ^ 2)
      (volume.restrict (Ioo t₀ T)) := fun i =>
    integrable_slab_sq_slices (a := t₀) (b := T) (F := fun z => Dtu z i) (memLp_pi_iff.mp hDt i)
  have hslices : ∀ i : Fin 3, ∀ᵐ σ ∂(volume.restrict (Ioo t₀ T)),
      MemLp (fun x : Vec3 => Dtu (x, σ) i) 2 volume := fun i =>
    lps_ae_slice_memLp_of_slab (F := fun z => Dtu z i) (memLp_pi_iff.mp hDt i)
  have hall := ae_all_iff.mpr hslices
  have hsum : Integrable (fun σ => ∑ i : Fin 3, ∫ x : Vec3, (Dtu (x, σ) i) ^ 2)
      (volume.restrict (Ioo t₀ T)) := integrable_finsetSum _ fun i _ => hi i
  refine hsum.congr ?_
  filter_upwards [hall] with σ hσ
  rw [integral_finsetSum _ fun i _ => (hσ i).integrable_sq]

/-- The mean over the initial layer `[t₀, t₀ + δ]` of the squared `L²` norms of the time-difference
quotients is at most the total `L²` energy of the weak time derivative (`prop:lps-smoothing`). -/
theorem lps_initial_layer_bound {t₀ T δ h : ℝ} (hT : t₀ < T) (hδ : 0 < δ) (hh : 0 < h)
    (hδhT : t₀ + δ + h ≤ T) {u Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    (hEint : IntervalIntegrable
      (fun τ => ∫ x : Vec3, ∑ i : Fin 3, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2)
      volume t₀ (t₀ + δ)) :
    ∫ τ in t₀..(t₀ + δ), (∫ x : Vec3, ∑ i : Fin 3,
        ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2) ≤
      ∫ σ in t₀..T, ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, σ) i) ^ 2 := by
  set f : ℝ → ℝ := fun σ => ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, σ) i) ^ 2 with hf
  have hf0 : ∀ σ, 0 ≤ f σ := fun σ =>
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfI : IntervalIntegrable f volume t₀ T := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le]
    exact lps_dtu_normSq_integrable hDt
  have hfI' : IntervalIntegrable f volume t₀ (t₀ + δ + h) :=
    hfI.mono_set (by
      rw [uIcc_of_le (by linarith only [hδ, hh]), uIcc_of_le hT.le]
      exact Icc_subset_Icc le_rfl hδhT)
  -- the window averages dominate the difference quotients
  have hpoint : ∀ τ ∈ Icc t₀ (t₀ + δ),
      (∫ x : Vec3, ∑ i : Fin 3, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2) ≤
        (1 / h) * ∫ σ in τ..(τ + h), f σ := by
    intro τ hτ
    have h1 := lps_slice_increment_sq_le hT hu hDt htime hslice hcont (s := τ) (t := τ + h)
      hτ.1 (by linarith only [hh]) (by linarith only [hτ.2, hδhT])
    have hexp : (∫ x : Vec3, ∑ i : Fin 3, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2) =
        (1 / h) ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (u (x, τ + h) i - u (x, τ) i) ^ 2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_pow, Finset.mul_sum]
    rw [hexp]
    have h2 : (1 / h) ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (u (x, τ + h) i - u (x, τ) i) ^ 2 ≤
        (1 / h) ^ 2 * (h * ∫ σ in τ..(τ + h), f σ) :=
      mul_le_mul_of_nonneg_left (by simpa using h1) (by positivity)
    calc _ ≤ (1 / h) ^ 2 * (h * ∫ σ in τ..(τ + h), f σ) := h2
      _ = (1 / h) * ∫ σ in τ..(τ + h), f σ := by field_simp
  have hwinI : IntervalIntegrable (fun τ => (1 / h) * ∫ σ in τ..(τ + h), f σ) volume t₀ (t₀ + δ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith only [hδ])]
    refine continuousOn_const.mul ?_
    have hF := intervalIntegral.continuousOn_primitive_interval' hfI' (left_mem_uIcc (a := t₀))
    rw [uIcc_of_le (by linarith only [hδ, hh])] at hF
    have hwin : ∀ τ ∈ Icc t₀ (t₀ + δ), (∫ σ in τ..(τ + h), f σ) =
        (∫ σ in t₀..(τ + h), f σ) - ∫ σ in t₀..τ, f σ := by
      intro τ hτ
      have h1 : IntervalIntegrable f volume t₀ τ := hfI'.mono_set (by
        rw [uIcc_of_le hτ.1, uIcc_of_le (by linarith only [hδ, hh])]
        exact Icc_subset_Icc le_rfl (by linarith only [hτ.2, hh]))
      have h2 : IntervalIntegrable f volume τ (τ + h) := hfI'.mono_set (by
        rw [uIcc_of_le (by linarith only [hh]), uIcc_of_le (by linarith only [hδ, hh])]
        exact Icc_subset_Icc hτ.1 (by linarith only [hτ.2]))
      have := intervalIntegral.integral_add_adjacent_intervals h1 h2
      linarith only [this]
    refine ContinuousOn.congr ?_ hwin
    refine ContinuousOn.sub ?_ ?_
    · exact hF.comp (continuousOn_id.add continuousOn_const) fun τ hτ =>
        ⟨by linarith only [hτ.1, hh], by linarith only [hτ.2]⟩
    · exact hF.mono (Icc_subset_Icc le_rfl (by linarith only [hh]))
  calc (∫ τ in t₀..(t₀ + δ), ∫ x : Vec3, ∑ i : Fin 3,
        ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2)
      ≤ ∫ τ in t₀..(t₀ + δ), (1 / h) * ∫ σ in τ..(τ + h), f σ :=
        intervalIntegral.integral_mono_on (by linarith only [hδ]) hEint hwinI hpoint
    _ ≤ ∫ σ in t₀..(t₀ + δ + h), f σ :=
        ESS.LPS.lps_window_average_integral_le hδ hh hfI' (fun x _ => hf0 x)
    _ ≤ ∫ σ in t₀..T, f σ := by
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (hfI.mono_set (by
            rw [uIcc_of_le (by linarith only [hδ, hh]), uIcc_of_le hT.le]
            exact Icc_subset_Icc le_rfl hδhT) : IntervalIntegrable f volume t₀ (t₀ + δ + h))
          (hfI.mono_set (by
            rw [uIcc_of_le hδhT, uIcc_of_le hT.le]
            exact Icc_subset_Icc (by linarith only [hδ, hh]) le_rfl) :
            IntervalIntegrable f volume (t₀ + δ + h) T)
        have hn : 0 ≤ ∫ σ in (t₀ + δ + h)..T, f σ :=
          intervalIntegral.integral_nonneg hδhT fun u _ => hf0 u
        linarith only [hsplit, hn]

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointPatch

/-!
# Consistency of the slice families of different orders

`prop:lps-smoothing`: two families of slices, each `L²`-continuous in time and each representing the
same field for almost every time, coincide at every time, and hence have the same weak derivatives.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Two `L²`-continuous curves of functions that agree for almost every time agree at every time
of the closed interval (`prop:lps-smoothing`). -/
theorem lps_curves_eq_of_ae_eq {a b : ℝ} (hab : a < b) {f g : ℝ → Vec3 → ℝ}
    (hf : ∀ t ∈ Icc a b, MemLp (f t) 2 volume) (hg : ∀ t ∈ Icc a b, MemLp (g t) 2 volume)
    (hcf : ∀ t ∈ Icc a b, Tendsto (fun s => eLpNorm (f s - f t) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (hcg : ∀ t ∈ Icc a b, Tendsto (fun s => eLpNorm (g s - g t) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (hae : ∀ᵐ t ∂(volume.restrict (Ioo a b)), f t =ᵐ[volume] g t) :
    ∀ t ∈ Icc a b, f t =ᵐ[volume] g t := by
  intro t ht
  set S : Set ℝ := {s | s ∈ Ioo a b ∧ f s =ᵐ[volume] g s} with hS
  have hSae : ∀ᵐ s ∂(volume.restrict (Ioo a b)), s ∈ S := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with s h1 h2 using ⟨h2, h1⟩
  have hcl : t ∈ closure S := by
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    have hlt : max a (t - ε) < min b (t + ε) := by
      refine max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨hab, by linarith only [ht.1, hε]⟩,
        lt_min_iff.mpr ⟨by linarith only [ht.2, hε], by linarith only [hε]⟩⟩
    by_contra hemp
    have hV : Ioo (max a (t - ε)) (min b (t + ε)) ⊆ Sᶜ ∩ Ioo a b := by
      intro s hs
      have hsI : s ∈ Ioo a b := ⟨(le_max_left _ _).trans_lt hs.1, hs.2.trans_le (min_le_left _ _)⟩
      refine ⟨fun hsS => hemp ⟨s, ?_, hsS⟩, hsI⟩
      apply hεU
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith only [(le_max_right a (t - ε)).trans_lt hs.1]
      · linarith only [hs.2.trans_le (min_le_right b (t + ε))]
    have h0 : volume (Sᶜ ∩ Ioo a b) = 0 := by
      have := (ae_restrict_iff' measurableSet_Ioo).mp hSae
      rw [ae_iff] at this
      convert this using 2
      ext x; simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_imp]; tauto
    have := measure_mono_null hV h0
    rw [Real.volume_Ioo] at this
    have hp : (0 : ENNReal) < ENNReal.ofReal (min b (t + ε) - max a (t - ε)) :=
      ENNReal.ofReal_pos.mpr (sub_pos.mpr hlt)
    exact hp.ne' this
  have hne : (𝓝[S] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hSt : 𝓝[S] t ≤ 𝓝[Icc a b] t := by
    refine nhdsWithin_mono t (fun s hs => ?_)
    exact Ioo_subset_Icc_self hs.1
  have h1 := (hcf t ht).mono_left hSt
  have h2 := (hcg t ht).mono_left hSt
  have hsum : Tendsto (fun s => eLpNorm (f s - f t) 2 volume + eLpNorm (g s - g t) 2 volume)
      (𝓝[S] t) (𝓝 (0 + 0)) := h1.add h2
  rw [add_zero] at hsum
  have hle : ∀ᶠ s in 𝓝[S] t, eLpNorm (f t - g t) 2 volume ≤
      eLpNorm (f s - f t) 2 volume + eLpNorm (g s - g t) 2 volume := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have e : f t - g t = (f t - f s) + ((f s - g s) + (g s - g t)) := by
      funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hz : eLpNorm (f s - g s) 2 volume = 0 := by
      rw [eLpNorm_eq_zero_iff (by norm_num)]
      filter_upwards [hs.2] with x hx
      simp [hx]
    have hfs := hf s (Ioo_subset_Icc_self hs.1)
    have hft := hf t ht
    have hgs := hg s (Ioo_subset_Icc_self hs.1)
    have hgt := hg t ht
    calc eLpNorm (f t - g t) 2 volume
        = eLpNorm ((f t - f s) + ((f s - g s) + (g s - g t))) 2 volume := by rw [← e]
      _ ≤ eLpNorm (f t - f s) 2 volume + eLpNorm ((f s - g s) + (g s - g t)) 2 volume :=
          eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (f t - f s) 2 volume + (eLpNorm (f s - g s) 2 volume +
            eLpNorm (g s - g t) 2 volume) := by
          gcongr
          exact eLpNorm_add_le (by norm_num)
      _ = eLpNorm (f s - f t) 2 volume + eLpNorm (g s - g t) 2 volume := by
          rw [hz, zero_add, eLpNorm_sub_comm (f := f t) (g := f s)]
  have h0 : eLpNorm (f t - g t) 2 volume ≤ 0 := ge_of_tendsto hsum hle
  have h00 : eLpNorm (f t - g t) 2 volume = 0 := le_antisymm h0 bot_le
  rw [eLpNorm_eq_zero_iff (by norm_num)] at h00
  filter_upwards [h00] with x hx
  simpa [sub_eq_zero] using hx

end ESS

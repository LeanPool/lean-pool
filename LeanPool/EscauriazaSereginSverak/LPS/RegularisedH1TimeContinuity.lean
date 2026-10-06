/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1GradientEnergy

/-!
# `L²` continuity in time of the regularized momentum right-hand side

The pressure-free part `R = Δ U_ε - (J_ε U_ε · ∇) U_ε` of the regularized momentum right-hand side
is continuous in time with values in `L²`, by the continuity of the ordered derivative paths and
sup-norm bounds for the mollified transport velocity (`lem:lps-regularized-Hk-start`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped Interval
open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS.LPS

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/--
Every ordered spatial derivative of the regularized velocity is `L²`-continuous in time at
positive times.
-/
theorem lps_regR12_word_path_continuousAt {a : ℝ} (ha : 0 < a) (i : Fin 3) (α : List (Fin 3)) :
    ContinuousAt (lpsPath (fun s x => wordDeriv α (fun y => lpsRegU ρ ε hε b hb (y, s) i) x)
      (fun s hs => lps_regR12_slice_memLp ρ ε hε b hb s hs i α)) a := by
  obtain ⟨F, hFc, hF⟩ := lps_regR12Velocity_wordDeriv_continuous_L2 ρ ε hε b hb (a + 1)
    (by linarith only [ha]) i α
  refine lps_continuousAt_lpsPath_of_path ha hFc.continuousAt ?_
  filter_upwards [lt_mem_nhds ha, Iio_mem_nhds (lt_add_one a)] with r hr0 hr1
  exact hF r ⟨hr0.le, hr1.le⟩

/-- The mollifier kernel is square integrable. -/
theorem lps_regR12_kernel_memLp :
    MemLp (CKN.Leray.regUniformMollifierKernel ρ ε hε) 2 volume := by
  obtain ⟨hsm, hcpt, -, -⟩ := lps_regUniformMollifierKernel_properties ρ ε hε
  exact hsm.continuous.memLp_of_hasCompactSupport hcpt

/--
The mollified transport velocity is the convolution of the velocity slice with the mollifier
kernel.
-/
theorem lps_regR12_V_eq_conv {t : ℝ} (ht : 0 ≤ t) (x : Vec3) (k : Fin 3) :
    lpsRegV ρ ε hε b hb (x, t) k =
      convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
        (fun y : Vec3 => lpsRegU ρ ε hε b hb (y, t) k)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x :=
  lps_regUniformMollifiedVelocity_component_convolution ρ ε hε _ t
    (lps_regR12Velocity_slice_isInJ ρ ε hε b hb t ht).1 x k

/--
The sup-norm distance of the mollified transport velocity at two times is bounded by the
kernel's `L²` norm times the `L²` distance of the velocity slices.
-/
theorem lps_regR12_V_diff_abs_le {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (x : Vec3) (k : Fin 3) :
    |lpsRegV ρ ε hε b hb (x, r) k - lpsRegV ρ ε hε b hb (x, a) k| ≤
      Real.sqrt (∫ y, CKN.Leray.regUniformMollifierKernel ρ ε hε y ^ 2) *
        Real.sqrt (∫ y, (lpsRegU ρ ε hε b hb (y, r) k - lpsRegU ρ ε hε b hb (y, a) k) ^ 2) := by
  rw [lps_regR12_V_eq_conv ρ ε hε b hb hr, lps_regR12_V_eq_conv ρ ε hε b hb ha]
  exact lps_convolution_diff_abs_le (lps_regR12_kernel_memLp ρ ε hε)
    (lps_regR12_slice_memLp ρ ε hε b hb r hr k [])
    (lps_regR12_slice_memLp ρ ε hε b hb a ha k []) x

/--
The mollified transport velocity is bounded by the kernel's `L²` norm times the `L²` norm of the
velocity slice.
-/
theorem lps_regR12_V_abs_le {t : ℝ} (ht : 0 ≤ t) (x : Vec3) (k : Fin 3) :
    |lpsRegV ρ ε hε b hb (x, t) k| ≤
      Real.sqrt (∫ y, CKN.Leray.regUniformMollifierKernel ρ ε hε y ^ 2) *
        Real.sqrt (∫ y, lpsRegU ρ ε hε b hb (y, t) k ^ 2) := by
  rw [lps_regR12_V_eq_conv ρ ε hε b hb ht]
  have hmem : MemLp (fun y : Vec3 => lpsRegU ρ ε hε b hb (y, t) k) 2 volume :=
    lps_regR12_slice_memLp ρ ε hε b hb t ht k []
  have h := lps_convolution_diff_abs_le (lps_regR12_kernel_memLp ρ ε hε) hmem
    (g := fun _ => 0) MemLp.zero x
  have hz : convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε) (fun _ : Vec3 => (0 : ℝ))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by simp [convolution_lsmul]
  simpa [hz] using h

/-- One summand `V_k ∂_k U_i` of the transport term. -/
@[expose] def lpsRegTransportTerm (k i : Fin 3) (t : ℝ) : Vec3 → ℝ :=
  fun x => lpsRegV ρ ε hε b hb (x, t) k *
    spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x

/-- Every summand of the transport term is square integrable. -/
theorem lps_regR12_transportTerm_memLp {t : ℝ} (ht : 0 ≤ t) (k i : Fin 3) :
    MemLp (lpsRegTransportTerm ρ ε hε b hb k i t) 2 volume := by
  have hU := lps_regR12Velocity_slice_isInJ ρ ε hε b hb t ht
  obtain ⟨hVs, -⟩ := lps_regUniformMollifiedVelocity_smooth_memLp ρ ε hε
    (lpsRegU ρ ε hε b hb) t hU.1 (lps_regR12_slice_smooth ρ ε hε b hb t ht)
    (fun i α => lps_regR12_slice_memLp ρ ε hε b hb t ht i α)
  have hd : MemLp (spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k) 2 volume :=
    lps_regR12_slice_memLp ρ ε hε b hb t ht i [k]
  refine hd.of_le_mul (c := Real.sqrt (∫ y, CKN.Leray.regUniformMollifierKernel ρ ε hε y ^ 2) *
    Real.sqrt (∫ y, lpsRegU ρ ε hε b hb (y, t) k ^ 2)) ?_ ?_
  · exact ((hVs k).continuous.aestronglyMeasurable).mul hd.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [lpsRegTransportTerm, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (lps_regR12_V_abs_le ρ ε hε b hb ht x k) (abs_nonneg _)

/-- Every summand of the transport term is `L²`-continuous in time at positive times. -/
theorem lps_regR12_transportTerm_continuousAt {a : ℝ} (ha : 0 < a) (k i : Fin 3) :
    ContinuousAt (lpsPath (lpsRegTransportTerm ρ ε hε b hb k i)
      (fun _ hs => lps_regR12_transportTerm_memLp ρ ε hε b hb hs k i)) a := by
  refine lps_continuousAt_lpsPath_of_sq_tendsto ha ?_
  have hu := lps_sq_tendsto_of_continuousAt_lpsPath ha
    (lps_regR12_word_path_continuousAt ρ ε hε b hb ha k [])
  have hB := lps_sq_tendsto_of_continuousAt_lpsPath ha
    (lps_regR12_word_path_continuousAt ρ ε hε b hb ha i [k])
  set κ2 := Real.sqrt (∫ y, CKN.Leray.regUniformMollifierKernel ρ ε hε y ^ 2) with hκ2
  set ν : ℝ → ℝ := fun r => κ2 * Real.sqrt (∫ y, (lpsRegU ρ ε hε b hb (y, r) k -
    lpsRegU ρ ε hε b hb (y, a) k) ^ 2) with hν
  have hνt : Tendsto ν (𝓝 a) (𝓝 0) := by
    have h1 : Tendsto (fun r => ∫ y, (lpsRegU ρ ε hε b hb (y, r) k -
        lpsRegU ρ ε hε b hb (y, a) k) ^ 2) (𝓝 a) (𝓝 0) := by
      simpa [wordDeriv] using hu
    simpa [hν] using (h1.sqrt).const_mul κ2
  have hpos : ∀ᶠ r in 𝓝 a, 0 < r := lt_mem_nhds ha
  have hM : ∀ᶠ r in 𝓝 a, ∀ x, |lpsRegV ρ ε hε b hb (x, r) k| ≤
      κ2 * Real.sqrt (∫ y, lpsRegU ρ ε hε b hb (y, a) k ^ 2) + 1 := by
    filter_upwards [hpos, hνt.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r hr
      hνr x
    have h1 := lps_regR12_V_diff_abs_le ρ ε hε b hb hr.le ha.le x k
    have h2 := lps_regR12_V_abs_le ρ ε hε b hb ha.le x k
    have h3 : |lpsRegV ρ ε hε b hb (x, r) k| ≤
        |lpsRegV ρ ε hε b hb (x, a) k| + |lpsRegV ρ ε hε b hb (x, r) k -
          lpsRegV ρ ε hε b hb (x, a) k| := by
      calc |lpsRegV ρ ε hε b hb (x, r) k| =
          |lpsRegV ρ ε hε b hb (x, a) k + (lpsRegV ρ ε hε b hb (x, r) k -
            lpsRegV ρ ε hε b hb (x, a) k)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h4 : |lpsRegV ρ ε hε b hb (x, r) k - lpsRegV ρ ε hε b hb (x, a) k| ≤ ν r := h1
    linarith only [h2, h3, h4, hνr]
  have hAν : ∀ᶠ r in 𝓝 a, ∀ x, |lpsRegV ρ ε hε b hb (x, r) k - lpsRegV ρ ε hε b hb (x, a) k| ≤ ν
    r := by
    filter_upwards [hpos] with r hr x
    exact lps_regR12_V_diff_abs_le ρ ε hε b hb hr.le ha.le x k
  have hBmem : ∀ᶠ r in 𝓝 a, MemLp (spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, r) i) k) 2
    volume := by
    filter_upwards [hpos] with r hr
    exact lps_regR12_slice_memLp ρ ε hε b hb r hr.le i [k]
  exact lps_sq_tendsto_mul (A := fun r x => lpsRegV ρ ε hε b hb (x, r) k)
    (B := fun r x => spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, r) i) k x)
    (lps_regR12_slice_memLp ρ ε hε b hb a ha.le i [k]) hBmem hB hM hνt hAν

/-- The Laplacian of the `i`-th component of the regularized velocity. -/
@[expose] def lpsRegLap (i : Fin 3) (t : ℝ) : Vec3 → ℝ :=
  spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, t) i)

/-- The regularized momentum right-hand side without its pressure gradient. -/
@[expose] def lpsRegR (i : Fin 3) (t : ℝ) : Vec3 → ℝ :=
  fun x => lpsRegLap ρ ε hε b hb i t x - lpsRegTransport ρ ε hε b hb i t x

/-- The transport term is square integrable. -/
theorem lps_regR12_transport_memLp {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    MemLp (lpsRegTransport ρ ε hε b hb i t) 2 volume := by
  have h : lpsRegTransport ρ ε hε b hb i t =
      fun x => ∑ k : Fin 3, lpsRegTransportTerm ρ ε hε b hb k i t x := rfl
  rw [h]
  exact memLp_finsetSum _ fun k _ => lps_regR12_transportTerm_memLp ρ ε hε b hb ht k i

/-- The pressure-free momentum right-hand side is square integrable. -/
theorem lps_regR12_R_memLp {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    MemLp (lpsRegR ρ ε hε b hb i t) 2 volume :=
  (lps_regR12_lap_memLp ρ ε hε b hb t ht i).sub (lps_regR12_transport_memLp ρ ε hε b hb ht i)

/-- The Laplacian of the regularized velocity is `L²`-continuous in time at positive times. -/
theorem lps_regR12_lap_path_continuousAt {a : ℝ} (ha : 0 < a) (i : Fin 3) :
    ContinuousAt (lpsPath (lpsRegLap ρ ε hε b hb i)
      (fun _ hs => lps_regR12_lap_memLp ρ ε hε b hb _ hs i)) a := by
  have h : lpsPath (lpsRegLap ρ ε hε b hb i)
      (fun _ hs => lps_regR12_lap_memLp ρ ε hε b hb _ hs i) = fun r =>
      ∑ j : Fin 3, lpsPath (fun s x => wordDeriv [j, j] (fun y => lpsRegU ρ ε hε b hb (y, s) i) x)
        (fun s hs => lps_regR12_slice_memLp ρ ε hε b hb s hs i [j, j]) r :=
    funext fun r => lps_lpsPath_finsetSum Finset.univ
      (f := fun j s x => wordDeriv [j, j] (fun y => lpsRegU ρ ε hε b hb (y, s) i) x)
      (hf := fun j s hs => lps_regR12_slice_memLp ρ ε hε b hb s hs i [j, j])
      (g := lpsRegLap ρ ε hε b hb i)
      (hg := fun _ hs => lps_regR12_lap_memLp ρ ε hε b hb _ hs i) (fun t x => rfl) r
  rw [h]
  exact tendsto_finsetSum _ fun j _ => lps_regR12_word_path_continuousAt ρ ε hε b hb ha i [j, j]

/-- The transport term is `L²`-continuous in time at positive times. -/
theorem lps_regR12_transport_path_continuousAt {a : ℝ} (ha : 0 < a) (i : Fin 3) :
    ContinuousAt (lpsPath (lpsRegTransport ρ ε hε b hb i)
      (fun _ hs => lps_regR12_transport_memLp ρ ε hε b hb hs i)) a := by
  have h : lpsPath (lpsRegTransport ρ ε hε b hb i)
      (fun _ hs => lps_regR12_transport_memLp ρ ε hε b hb hs i) = fun r =>
      ∑ k : Fin 3, lpsPath (lpsRegTransportTerm ρ ε hε b hb k i)
        (fun _ hs => lps_regR12_transportTerm_memLp ρ ε hε b hb hs k i) r :=
    funext fun r => lps_lpsPath_finsetSum Finset.univ
      (f := fun k s x => lpsRegTransportTerm ρ ε hε b hb k i s x)
      (hf := fun k _ hs => lps_regR12_transportTerm_memLp ρ ε hε b hb hs k i)
      (g := lpsRegTransport ρ ε hε b hb i)
      (hg := fun _ hs => lps_regR12_transport_memLp ρ ε hε b hb hs i) (fun t x => rfl) r
  rw [h]
  exact tendsto_finsetSum _ fun k _ => lps_regR12_transportTerm_continuousAt ρ ε hε b hb ha k i

/--
The pressure-free momentum right-hand side is `L²`-continuous in time at positive times
(`lem:lps-regularized-Hk-start`).
-/
theorem lps_regR12_R_path_continuousAt {a : ℝ} (ha : 0 < a) (i : Fin 3) :
    ContinuousAt (lpsPath (lpsRegR ρ ε hε b hb i)
      (fun _ hs => lps_regR12_R_memLp ρ ε hε b hb hs i)) a := by
  have h : lpsPath (lpsRegR ρ ε hε b hb i)
      (fun _ hs => lps_regR12_R_memLp ρ ε hε b hb hs i) = fun r =>
      lpsPath (lpsRegLap ρ ε hε b hb i)
        (fun _ hs => lps_regR12_lap_memLp ρ ε hε b hb _ hs i) r -
      lpsPath (lpsRegTransport ρ ε hε b hb i)
        (fun _ hs => lps_regR12_transport_memLp ρ ε hε b hb hs i) r :=
    funext fun r => lps_lpsPath_sub (fun t x => rfl) r
  rw [h]
  exact (lps_regR12_lap_path_continuousAt ρ ε hε b hb ha i).sub
    (lps_regR12_transport_path_continuousAt ρ ε hε b hb ha i)

end

end ESS.LPS

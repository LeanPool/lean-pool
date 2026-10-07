/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyMollifier

/-!
# The Cauchy estimate for mollified weak heat solutions

The time primitive is linear in the kernel. Applied to the difference `ρₙ - ρₘ`
of two mollifiers, the kernel energy inequality bounds, uniformly in
`t ∈ [a, τ]`, both `‖Wₙ(t) - Wₘ(t)‖²` and the slab norm of the difference of
the mollified gradients by twice the sum of the two mollifier errors, and these
errors tend to zero (`lem:localized-vorticity-energy`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Topology Interval


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

theorem vlConvT_sub_kernel_ae {k l : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l)
    {g : Vec3 × ℝ → ℝ} (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) :
    ∀ᵐ s ∂(volume.restrict (Ioo a τ)), ∀ x,
      vlConvT (k - l) g x s = vlConvT k g x s - vlConvT l g x s := by
  filter_upwards [vlSlab_slice_memLp hgm hg] with s hs x
  simp only [vlConvT]
  rw [vlConv_sub_kernel hk hl (hs.locallyIntegrable (by norm_num))]
  rfl

theorem vlSource_sub_kernel_ae (sol : VlHeatSolution a τ w H f w₀) {k l : Vec3 → ℝ}
    (hk : IsVlKernel k) (hl : IsVlKernel l) :
    ∀ᵐ s ∂(volume.restrict (Ioo a τ)), ∀ x,
      vlSource (k - l) w H f x s = vlSource k w H f x s - vlSource l w H f x s := by
  have hw := fun j : Fin 3 => vlConvT_sub_kernel_ae ((hk.deriv j).deriv j)
    ((hl.deriv j).deriv j) sol.w_meas sol.w_L2
  have hH := fun j : Fin 3 => vlConvT_sub_kernel_ae (hk.deriv j) (hl.deriv j)
    (sol.H_meas j) (sol.H_L2 j)
  have hf := vlConvT_sub_kernel_ae hk hl sol.f_meas sol.f_L2
  filter_upwards [ae_all_iff.2 hw, ae_all_iff.2 hH, hf] with s hws hHs hfs x
  have hd : ∀ j : Fin 3, vlDeriv (k - l) j = vlDeriv k j - vlDeriv l j :=
    fun j => vlDeriv_sub hk hl j
  have hdd : ∀ j : Fin 3, vlDeriv (vlDeriv k j - vlDeriv l j) j =
      vlDeriv (vlDeriv k j) j - vlDeriv (vlDeriv l j) j := fun j =>
    vlDeriv_sub (hk.deriv j) (hl.deriv j) j
  simp only [vlSource, hd, hdd, hws, hHs, hfs, Finset.sum_sub_distrib]
  ring

/-- The time primitive is linear in the kernel. -/
theorem vlPrim_sub_kernel (sol : VlHeatSolution a τ w H f w₀) {k l : Vec3 → ℝ}
    (hk : IsVlKernel k) (hl : IsVlKernel l) (x : Vec3) {t : ℝ} (ht : t ∈ Icc a τ) :
    vlPrim a (k - l) w₀ w H f x t = vlPrim a k w₀ w H f x t - vlPrim a l w₀ w H f x t := by
  have hae := vlSource_sub_kernel_ae sol hk hl
  rw [ae_restrict_iff' measurableSet_Ioo] at hae
  have hcongr : ∫ s in a..t, vlSource (k - l) w H f x s =
      ∫ s in a..t, (vlSource k w H f x s - vlSource l w H f x s) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae, Measure.ae_ne volume τ] with s hs hsτ hsI
    rw [uIoc_of_le ht.1] at hsI
    exact hs ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans ht.2) hsτ⟩ x
  simp only [vlPrim]
  rw [hcongr, intervalIntegral.integral_sub (vlSource_intervalIntegrable sol hk x ht)
    (vlSource_intervalIntegrable sol hl x ht),
    vlConv_sub_kernel hk hl (sol.w₀_L2.locallyIntegrable (by norm_num))]
  simp only [Pi.sub_apply]
  ring

/-- The total mollifier error of the data. -/
@[expose] def vlErr (w₀ : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ) (H : Fin 3 → Vec3 × ℝ → ℝ)
    (f : Vec3 × ℝ → ℝ) (a τ : ℝ) (n : ℕ) : ℝ :=
  (∫ x, (vlConv (vlMoll n) w₀ x - w₀ x) ^ 2) +
    ∫ s in Ioo a τ, ((∑ j : Fin 3, vlMollErr n (H j) s) + vlMollErr n w s + vlMollErr n f s)

theorem vlErr_tendsto (sol : VlHeatSolution a τ w H f w₀) :
    Tendsto (fun n => vlErr w₀ w H f a τ n) atTop (𝓝 0) := by
  have hA := vlMoll_tendsto sol.w₀_L2
  have hHj := fun j : Fin 3 => vlMoll_slab_tendsto (sol.H_meas j) (sol.H_L2 j)
  have hW := vlMoll_slab_tendsto sol.w_meas sol.w_L2
  have hF := vlMoll_slab_tendsto sol.f_meas sol.f_L2
  have hsplit : ∀ n, vlErr w₀ w H f a τ n =
      (∫ x, (vlConv (vlMoll n) w₀ x - w₀ x) ^ 2) +
        ((∑ j : Fin 3, ∫ s in Ioo a τ, vlMollErr n (H j) s) +
          (∫ s in Ioo a τ, vlMollErr n w s) + ∫ s in Ioo a τ, vlMollErr n f s) := by
    intro n
    have hIH : ∀ j : Fin 3, IntegrableOn (fun s => vlMollErr n (H j) s) (Ioo a τ) volume :=
      fun j => vlMollErr_integrableOn n (sol.H_meas j) (sol.H_L2 j)
    have hIW := vlMollErr_integrableOn n sol.w_meas sol.w_L2
    have hIF := vlMollErr_integrableOn n sol.f_meas sol.f_L2
    have hsum : IntegrableOn (fun s => ∑ j : Fin 3, vlMollErr n (H j) s) (Ioo a τ) volume :=
      integrable_finsetSum _ fun j _ => hIH j
    have hsw : IntegrableOn (fun s => (∑ j : Fin 3, vlMollErr n (H j) s) + vlMollErr n w s)
        (Ioo a τ) volume := hsum.add hIW
    simp only [vlErr]
    rw [integral_add hsw hIF, integral_add hsum hIW, integral_finsetSum _ fun j _ => hIH j]
  simp_rw [hsplit]
  have h0 : (0 : ℝ) = 0 + ((∑ _j : Fin 3, (0 : ℝ)) + 0 + 0) := by simp
  rw [h0]
  refine hA.add (((tendsto_finsetSum _ fun j _ => ?_).add ?_).add ?_)
  · exact hHj j
  · exact hW
  · exact hF

/-- The kernel energy bound for a mollifier difference, in terms of the
mollifier errors. -/
theorem vlMoll_diff_rhs_le (sol : VlHeatSolution a τ w H f w₀) (n m : ℕ) {t : ℝ}
    (ht : t ∈ Icc a τ) :
    (∫ x, (vlConv (vlMoll n - vlMoll m) w₀ x) ^ 2) +
        ∫ s in Ioo a t, ((∑ j : Fin 3, ∫ x, (vlConvT (vlMoll n - vlMoll m) (H j) x s) ^ 2) +
          (∫ x, (vlConvT (vlMoll n - vlMoll m) w x s) ^ 2) +
          ∫ x, (vlConvT (vlMoll n - vlMoll m) f x s) ^ 2) ≤
      2 * vlErr w₀ w H f a τ n + 2 * vlErr w₀ w H f a τ m := by
  set k := vlMoll n - vlMoll m with hk_def
  have hk : IsVlKernel k := (vlMoll_kernel n).sub (vlMoll_kernel m)
  let R : ℝ → ℝ := fun s => (∑ j : Fin 3, ∫ x, (vlConvT k (H j) x s) ^ 2) +
    (∫ x, (vlConvT k w x s) ^ 2) + ∫ x, (vlConvT k f x s) ^ 2
  let E : ℕ → ℝ → ℝ := fun n s =>
    (∑ j : Fin 3, vlMollErr n (H j) s) + vlMollErr n w s + vlMollErr n f s
  have hR : IntegrableOn R (Ioo a τ) volume := by
    refine (Integrable.add ?_ ?_).add ?_
    · exact integrable_finsetSum _ fun j _ =>
        vlSlab_sliceSq_integrableOn (vlConvT_memLp hk (sol.H_meas j) (sol.H_L2 j))
    · exact vlSlab_sliceSq_integrableOn (vlConvT_memLp hk sol.w_meas sol.w_L2)
    · exact vlSlab_sliceSq_integrableOn (vlConvT_memLp hk sol.f_meas sol.f_L2)
  have hR0 : ∀ s, 0 ≤ R s := fun s => by
    have h1 : 0 ≤ ∑ j : Fin 3, ∫ x, (vlConvT k (H j) x s) ^ 2 :=
      Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _
    have h2 : 0 ≤ ∫ x, (vlConvT k w x s) ^ 2 := integral_nonneg fun x => sq_nonneg _
    have h3 : 0 ≤ ∫ x, (vlConvT k f x s) ^ 2 := integral_nonneg fun x => sq_nonneg _
    exact add_nonneg (add_nonneg h1 h2) h3
  have hE : ∀ n, IntegrableOn (E n) (Ioo a τ) volume := fun n =>
    ((integrable_finsetSum _ fun j _ =>
      vlMollErr_integrableOn n (sol.H_meas j) (sol.H_L2 j)).add
      (vlMollErr_integrableOn n sol.w_meas sol.w_L2)).add
      (vlMollErr_integrableOn n sol.f_meas sol.f_L2)
  have hmono : ∫ s in Ioo a t, R s ≤ ∫ s in Ioo a τ, R s :=
    setIntegral_mono_set hR (Eventually.of_forall fun s => hR0 s)
      (Eventually.of_forall (Ioo_subset_Ioo_right ht.2))
  have hpoint : ∀ᵐ s ∂(volume.restrict (Ioo a τ)), R s ≤ 2 * E n s + 2 * E m s := by
    have hHae : ∀ᵐ s ∂(volume.restrict (Ioo a τ)),
        ∀ j, MemLp (fun y => H j (y, s)) 2 volume :=
      ae_all_iff.2 fun j => vlSlab_slice_memLp (sol.H_meas j) (sol.H_L2 j)
    filter_upwards [vlSlab_slice_memLp sol.w_meas sol.w_L2, hHae,
      vlSlab_slice_memLp sol.f_meas sol.f_L2] with s hws hHs hfs
    have hHj := fun j => vlMoll_sub_sq_le n m (hHs j)
    have hw := vlMoll_sub_sq_le n m hws
    have hf := vlMoll_sub_sq_le n m hfs
    have hsumH := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hHj j
    simp only [R, E, vlMollErr, vlConvT]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsumH
    linarith only [hsumH, hw, hf]
  have hEn2 : IntegrableOn (fun s => 2 * E n s) (Ioo a τ) volume := (hE n).const_mul 2
  have hEm2 : IntegrableOn (fun s => 2 * E m s) (Ioo a τ) volume := (hE m).const_mul 2
  have hEnm : IntegrableOn (fun s => 2 * E n s + 2 * E m s) (Ioo a τ) volume := hEn2.add hEm2
  have hint := integral_mono_ae hR hEnm hpoint
  rw [integral_add hEn2 hEm2, integral_const_mul, integral_const_mul] at hint
  have hw0 := vlMoll_sub_sq_le n m sol.w₀_L2
  simp only [vlErr]
  change (∫ x, (vlConv k w₀ x) ^ 2) + ∫ s in Ioo a t, R s ≤ _
  change _ ≤ 2 * ((∫ x, (vlConv (vlMoll n) w₀ x - w₀ x) ^ 2) + ∫ s in Ioo a τ, E n s) +
    2 * ((∫ x, (vlConv (vlMoll m) w₀ x - w₀ x) ^ 2) + ∫ s in Ioo a τ, E m s)
  linarith only [hint, hmono, hw0]

end ESS

end

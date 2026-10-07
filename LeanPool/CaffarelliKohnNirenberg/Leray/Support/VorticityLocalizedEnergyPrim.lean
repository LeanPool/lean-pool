/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyKernelEnergy

/-!
# The energy inequality for the time primitive of a kernel convolution

For a weak heat solution and a smooth compact kernel `k`, the time primitive
`W(t) = k ⋆ w₀ + ∫ₐᵗ G` of the convolved source is square integrable in space
for every `t ∈ [a, τ]`, and
`‖W(t)‖² + ∫ₐᵗ ‖∇(k ⋆ w)‖² ≤ ‖k ⋆ w₀‖² + ∫ₐᵗ (‖k ⋆ H‖² + ‖k ⋆ w‖² + ‖k ⋆ f‖²)`
(`lem:localized-vorticity-energy` of the Escauriaza–Seregin–Šverák manuscript).
-/

public section

open MeasureTheory Set Filter

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

theorem vlSource_intervalIntegrable (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ}
    (hk : IsVlKernel k) (x : Vec3) {t : ℝ} (ht : t ∈ Icc a τ) :
    IntervalIntegrable (fun s => vlSource k w H f x s) volume a t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  exact (vlSource_integrableOn sol hk x).mono_set (Ioo_subset_Ioo_right ht.2)

/-- The squared primitive at a point, with the primitive replaced inside the
time integral by the convolution itself. -/
theorem vlPrim_sq_eq (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ}
    (hk : IsVlKernel k) (x : Vec3) {t : ℝ} (ht : t ∈ Icc a τ) :
    (vlPrim a k w₀ w H f x t) ^ 2 = (vlConv k w₀ x) ^ 2 +
      ∫ s in Ioo a t, 2 * vlConvT k w x s * vlSource k w H f x s := by
  have hsq := vlTime_sq_primitive (c := vlConv k w₀ x)
    (vlSource_intervalIntegrable sol hk x ht)
  rw [vlPrim, hsq, intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  have hae := vlConvT_ae_eq_prim sol hk x
  have hae' : ∀ᵐ s ∂(volume.restrict (Ioo a t)), vlConvT k w x s = vlPrim a k w₀ w H f x s :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right ht.2) hae
  rw [ae_restrict_iff' measurableSet_Ioo] at hae'
  filter_upwards [hae'] with s hs hsI
  rw [hs hsI, vlPrim]

theorem vlPrim_stronglyMeasurable (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ}
    (hk : IsVlKernel k) {t : ℝ} (ht : a ≤ t) :
    StronglyMeasurable (fun x => vlPrim a k w₀ w H f x t) := by
  have hc : StronglyMeasurable (fun x => vlConv k w₀ x) :=
    (vlConv_continuous hk (sol.w₀_L2.locallyIntegrable (by norm_num))).stronglyMeasurable
  have hG := (vlSource_stronglyMeasurable sol hk).integral_prod_right'
    (ν := volume.restrict (Ioc a t))
  have heq : (fun x => vlPrim a k w₀ w H f x t) =
      fun x => vlConv k w₀ x + ∫ s, vlSource k w H f (x, s).1 (x, s).2
        ∂(volume.restrict (Ioc a t)) := by
    funext x
    rw [vlPrim, intervalIntegral.integral_of_le ht]
  rw [heq]
  exact hc.add hG

/-- The kernel energy inequality. -/
theorem vlPrim_energy_le (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ}
    (hk : IsVlKernel k) {t : ℝ} (ht : t ∈ Icc a τ) :
    MemLp (fun x => vlPrim a k w₀ w H f x t) 2 volume ∧
    (∫ x, (vlPrim a k w₀ w H f x t) ^ 2) +
        (∫ s in Ioo a t, ∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2) ≤
      (∫ x, (vlConv k w₀ x) ^ 2) +
        ∫ s in Ioo a t, ((∑ j : Fin 3, ∫ x, (vlConvT k (H j) x s) ^ 2) +
          (∫ x, (vlConvT k w x s) ^ 2) + ∫ x, (vlConvT k f x s) ^ 2) := by
  have hwt := vlSlab_memLp_mono ht.2 sol.w_L2
  have hHt := fun j => vlSlab_memLp_mono ht.2 (sol.H_L2 j)
  have hft := vlSlab_memLp_mono ht.2 sol.f_L2
  have hC : MemLp (fun p : Vec3 × ℝ => vlConvT k w p.1 p.2) 2
      (volume.restrict (vlSlab a t)) := vlConvT_memLp hk sol.w_meas hwt
  have hG : MemLp (fun p : Vec3 × ℝ => vlSource k w H f p.1 p.2) 2
      (volume.restrict (vlSlab a t)) := vlSlab_memLp_mono ht.2 (vlSource_memLp sol hk)
  -- the product integrand
  let F : Vec3 → ℝ → ℝ := fun x s => 2 * vlConvT k w x s * vlSource k w H f x s
  have hFint : Integrable (Function.uncurry F)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a t))) := by
    have h := (hC.integrable_mul hG).const_mul 2
    rw [vlSlab_measure] at h
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [F, Function.uncurry, Pi.mul_apply]
    ring
  have hc2 : Integrable (fun x => (vlConv k w₀ x) ^ 2) volume :=
    (vlConv_memLp hk sol.w₀_L2).integrable_sq
  have hFx : Integrable (fun x => ∫ s in Ioo a t, F x s) volume :=
    hFint.integral_prod_left
  have hsqfun : (fun x => (vlPrim a k w₀ w H f x t) ^ 2) =
      fun x => (vlConv k w₀ x) ^ 2 + ∫ s in Ioo a t, F x s := by
    funext x
    exact vlPrim_sq_eq sol hk x ht
  have hsqint : Integrable (fun x => (vlPrim a k w₀ w H f x t) ^ 2) volume := by
    rw [hsqfun]
    exact hc2.add hFx
  have hmem : MemLp (fun x => vlPrim a k w₀ w H f x t) 2 volume :=
    (memLp_two_iff_integrable_sq
      (vlPrim_stronglyMeasurable sol hk ht.1).aestronglyMeasurable).2 hsqint
  refine ⟨hmem, ?_⟩
  -- integrate the squared primitive in space and swap
  have hswap : ∫ x, ∫ s in Ioo a t, F x s = ∫ s in Ioo a t, ∫ x, F x s :=
    integral_integral_swap hFint
  have hspace : ∫ x, (vlPrim a k w₀ w H f x t) ^ 2 =
      (∫ x, (vlConv k w₀ x) ^ 2) + ∫ s in Ioo a t, ∫ x, F x s := by
    rw [hsqfun, integral_add hc2 hFx, hswap]
  -- time integrability of the slice terms
  have hD : IntegrableOn (fun s => ∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2)
      (Ioo a t) volume :=
    integrable_finsetSum _ fun j _ =>
      vlSlab_sliceSq_integrableOn (vlConvT_memLp (hk.deriv j) sol.w_meas hwt)
  have hR : IntegrableOn (fun s => (∑ j : Fin 3, ∫ x, (vlConvT k (H j) x s) ^ 2) +
      (∫ x, (vlConvT k w x s) ^ 2) + ∫ x, (vlConvT k f x s) ^ 2) (Ioo a t) volume := by
    refine (Integrable.add ?_ ?_).add ?_
    · exact integrable_finsetSum _ fun j _ =>
        vlSlab_sliceSq_integrableOn (vlConvT_memLp hk (sol.H_meas j) (hHt j))
    · exact vlSlab_sliceSq_integrableOn hC
    · exact vlSlab_sliceSq_integrableOn (vlConvT_memLp hk sol.f_meas hft)
  have hFs : IntegrableOn (fun s => ∫ x, F x s) (Ioo a t) volume :=
    hFint.integral_prod_right
  -- the slice inequality almost everywhere
  have hslice : ∀ᵐ s ∂(volume.restrict (Ioo a t)), ∫ x, F x s ≤
      -(∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2) +
        ((∑ j : Fin 3, ∫ x, (vlConvT k (H j) x s) ^ 2) + (∫ x, (vlConvT k w x s) ^ 2) +
          (∫ x, (vlConvT k f x s) ^ 2)) := by
    have hHae : ∀ᵐ s ∂(volume.restrict (Ioo a t)),
        ∀ j, MemLp (fun y => H j (y, s)) 2 volume :=
      ae_all_iff.2 fun j => vlSlab_slice_memLp (sol.H_meas j) (hHt j)
    filter_upwards [vlSlab_slice_memLp sol.w_meas hwt, hHae,
      vlSlab_slice_memLp sol.f_meas hft] with s hws hHs hfs
    have h := vlSource_slice_pairing_le hk hws hHs hfs
    have hFeq : ∫ x, F x s = 2 * ∫ x, vlConvT k w x s * vlSource k w H f x s := by
      rw [← integral_const_mul]
      congr 1
      funext x
      simp only [F]
      ring
    rw [hFeq]
    exact h
  have hDneg : IntegrableOn (fun s => -(∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2))
      (Ioo a t) volume := hD.neg
  have hsum : IntegrableOn (fun s => -(∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2) +
      ((∑ j : Fin 3, ∫ x, (vlConvT k (H j) x s) ^ 2) + (∫ x, (vlConvT k w x s) ^ 2) +
        (∫ x, (vlConvT k f x s) ^ 2))) (Ioo a t) volume := hDneg.add hR
  have hmono := integral_mono_ae hFs hsum hslice
  rw [integral_add hDneg hR, integral_neg] at hmono
  rw [hspace]
  linarith only [hmono]

end CKN

end

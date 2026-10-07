/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitDerivative

/-!
# Continuous `L²` curves for a field and its first gradient

A scalar slab field with square-integrable time derivative has a continuous
`L²`-valued representative, and its weak spatial derivative, if it has
a square-integrable weak spatial derivative, has one too, with the energy
identities of `prop:lps-local-strong`.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

variable {a b : ℝ} {w r : Vec3 × ℝ → ℝ}

/-- Mollifier convergence on a slab, in slab-integral form. -/
theorem lps_vlMoll_slab_tendsto {g : Vec3 × ℝ → ℝ} (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (volume.restrict (vlSlab a b))) :
    Tendsto (fun n => ∫ z in vlSlab a b,
      (vlConvT (vlMoll n) g z.1 z.2 - g z) ^ 2) atTop (𝓝 0) := by
  have h := vlMoll_slab_tendsto hgm hg
  refine h.congr fun n => ?_
  have hd : MemLp (fun z : Vec3 × ℝ => vlConvT (vlMoll n) g z.1 z.2 - g z) 2
      (volume.restrict (vlSlab a b)) := (vlConvT_memLp (vlMoll_kernel n) hgm hg).sub hg
  rw [vlSlab_integral_sq hd]

/-- The field itself: a continuous `L²` curve and its energy identity. -/
theorem lps_l2_time_curve (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p) :
    ∃ L : Icc a b → Lp ℝ 2 (volume : Measure Vec3), Continuous L ∧
      (∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ hs : s ∈ Icc a b,
        ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => w (x, s)) ∧
      ∀ (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b), s ≤ t →
        ‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2 = 2 * ∫ z in vlSlab s t, w z * r z := by
  have hSw := lps_vlMoll_slab_tendsto hwm hw
  have hSr := lps_vlMoll_slab_tendsto hrm hr
  have hpairDiff : ∀ n m, ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT (vlMoll n - vlMoll m) w x s * vlConvT (vlMoll n - vlMoll m) r x s =
        1 * ∫ x, (vlConvT (vlMoll n) w x s - vlConvT (vlMoll m) w x s) *
          (vlConvT (vlMoll n) r x s - vlConvT (vlMoll m) r x s) := by
    intro n m
    filter_upwards [vlConvT_sub_kernel_ae (vlMoll_kernel n) (vlMoll_kernel m) hwm hw,
      vlConvT_sub_kernel_ae (vlMoll_kernel n) (vlMoll_kernel m) hrm hr] with s h1 h2
    rw [one_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [h1 x, h2 x]
  obtain ⟨L, hLc, hLq, hLid⟩ := lps_kernel_limit_curve hab hwm hrm hw hr hweak
    (k := fun n => vlMoll n) vlMoll_kernel
    (P := fun n z => vlConvT (vlMoll n) w z.1 z.2)
    (Q := fun n z => vlConvT (vlMoll n) r z.1 z.2)
    (fun n => vlConvT_stronglyMeasurable (vlMoll_kernel n).continuous hwm)
    (fun n => vlConvT_stronglyMeasurable (vlMoll_kernel n).continuous hrm)
    (fun n => vlConvT_memLp (vlMoll_kernel n) hwm hw)
    (fun n => vlConvT_memLp (vlMoll_kernel n) hrm hr) 1 hpairDiff
    (fun n => Eventually.of_forall fun s => by rw [one_mul])
    (q := w) (p := w) (q' := r) hwm hw hw hr hSw
    (by
      filter_upwards [vlSlab_slice_memLp hwm hw] with s hs
      exact vlMoll_tendsto hs)
    hSw hSr
  refine ⟨L, hLc, hLq, fun s t hs ht hst => ?_⟩
  rw [hLid s t hs ht hst]
  ring

/-- Second spatial derivative of a slab field as an identity between kernel
convolutions, for almost every time and almost every point. -/
theorem lps_conv_second_deriv_ae {g h : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hwm : StronglyMeasurable w)
    (hhm : StronglyMeasurable h)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hh : MemLp h 2 (volume.restrict (vlSlab a b)))
    (hgrad : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, g p * φ p)
    (hhess : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, g p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, h p * φ p)
    {κ : Vec3 → ℝ} (hκ : IsVlKernel κ) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      vlConvT (vlDeriv (vlDeriv κ j) j) w x s = vlConvT κ h x s := by
  refine lps_ae_slice_of_ae_time
    (F := fun p : Vec3 × ℝ => vlConvT (vlDeriv (vlDeriv κ j) j) w p.1 p.2)
    (G := fun p : Vec3 × ℝ => vlConvT κ h p.1 p.2)
    (vlConvT_stronglyMeasurable ((hκ.deriv j).deriv j).continuous hwm)
    (vlConvT_stronglyMeasurable hκ.continuous hhm) fun x => ?_
  filter_upwards [lps_conv_deriv_ae hw hg j hgrad (hκ.deriv j) x,
    lps_conv_deriv_ae hg hh j hhess hκ x] with s h1 h2
  exact h1.trans h2

/-- First spatial derivative of a slab field as an identity between kernel
convolutions, for almost every time and almost every point. -/
theorem lps_conv_first_deriv_ae {g : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hwm : StronglyMeasurable w) (hgm : StronglyMeasurable g)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hgrad : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, g p * φ p)
    {κ : Vec3 → ℝ} (hκ : IsVlKernel κ) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      vlConvT (vlDeriv κ j) w x s = vlConvT κ g x s :=
  lps_ae_slice_of_ae_time
    (F := fun p : Vec3 × ℝ => vlConvT (vlDeriv κ j) w p.1 p.2)
    (G := fun p : Vec3 × ℝ => vlConvT κ g p.1 p.2)
    (vlConvT_stronglyMeasurable (hκ.deriv j).continuous hwm)
    (vlConvT_stronglyMeasurable hκ.continuous hgm)
    fun x => lps_conv_deriv_ae hw hg j hgrad hκ x

/-- The slice pairing of the differentiated convolutions is minus the pairing
of the convolved second derivative with the convolved time derivative. -/
theorem lps_grad_pairing {g h : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hhm : StronglyMeasurable h)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hh : MemLp h 2 (volume.restrict (vlSlab a b)))
    (hgrad : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, g p * φ p)
    (hhess : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, g p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, h p * φ p)
    {κ : Vec3 → ℝ} (hκ : IsVlKernel κ) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT (vlDeriv κ j) w x s * vlConvT (vlDeriv κ j) r x s =
        -∫ x, vlConvT κ h x s * vlConvT κ r x s := by
  filter_upwards [vlSlab_slice_memLp hwm hw, vlSlab_slice_memLp hrm hr,
    lps_conv_second_deriv_ae j hwm hhm hw hg hh hgrad hhess hκ] with s hws hrs hs2
  have hI := vlConv_integral_mul_deriv (k := vlDeriv κ j) (l := κ) (hκ.deriv j) hκ hws hrs j
  have h1 : ∫ x, vlConvT (vlDeriv κ j) w x s * vlConvT (vlDeriv κ j) r x s =
      ∫ x, vlConv (vlDeriv κ j) (fun y => w (y, s)) x *
        vlConv (vlDeriv κ j) (fun y => r (y, s)) x := rfl
  rw [h1, hI]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hs2] with x hx
  change vlConvT (vlDeriv (vlDeriv κ j) j) w x s * vlConvT κ r x s = _
  rw [hx]

/-- Almost everywhere agreement on almost every slice gives equal slab
distances to a common field. -/
theorem lps_slab_sq_congr {F G g : Vec3 × ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (vlSlab a b)))
    (hG : MemLp G 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hFG : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      F (x, s) = G (x, s)) :
    ∫ z in vlSlab a b, (F z - g z) ^ 2 = ∫ z in vlSlab a b, (G z - g z) ^ 2 := by
  have h1 : MemLp (fun z => F z - g z) 2 (volume.restrict (vlSlab a b)) := hF.sub hg
  have h2 : MemLp (fun z => G z - g z) 2 (volume.restrict (vlSlab a b)) := hG.sub hg
  rw [vlSlab_integral_sq h1, vlSlab_integral_sq h2]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hFG] with s hs hsI
  refine integral_congr_ae ?_
  filter_upwards [hs hsI] with x hx
  simp only [hx]

/-- The first spatial gradient: a continuous `L²` curve and its energy
identity, in direction `j`. -/
theorem lps_gradient_time_curve {g h : Vec3 × ℝ → ℝ} (hab : a < b) (j : Fin 3)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hgm : StronglyMeasurable g) (hhm : StronglyMeasurable h)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hh : MemLp h 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    (hgrad : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, g p * φ p)
    (hhess : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, g p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, h p * φ p) :
    ∃ L : Icc a b → Lp ℝ 2 (volume : Measure Vec3), Continuous L ∧
      (∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ hs : s ∈ Icc a b,
        ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => g (x, s)) ∧
      ∀ (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b), s ≤ t →
        ‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2 = -(2 * ∫ z in vlSlab s t, h z * r z) := by
  have hkn : ∀ n, IsVlKernel (vlDeriv (vlMoll n) j) := fun n => (vlMoll_kernel n).deriv j
  have hSg : Tendsto (fun n => ∫ z in vlSlab a b,
      (vlConvT (vlDeriv (vlMoll n) j) w z.1 z.2 - g z) ^ 2) atTop (𝓝 0) := by
    refine (lps_vlMoll_slab_tendsto hgm hg).congr fun n => ?_
    have hae := lps_conv_first_deriv_ae j hwm hgm hw hg hgrad (vlMoll_kernel n)
    have hcongr := lps_slab_sq_congr
      (F := fun z : Vec3 × ℝ => vlConvT (vlDeriv (vlMoll n) j) w z.1 z.2)
      (G := fun z : Vec3 × ℝ => vlConvT (vlMoll n) g z.1 z.2) (g := g)
      (vlConvT_memLp (hkn n) hwm hw) (vlConvT_memLp (vlMoll_kernel n) hgm hg) hg hae
    exact hcongr.symm
  have hSh := lps_vlMoll_slab_tendsto hhm hh
  have hSr := lps_vlMoll_slab_tendsto hrm hr
  have hpairDiff : ∀ n m, ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT (vlDeriv (vlMoll n) j - vlDeriv (vlMoll m) j) w x s *
          vlConvT (vlDeriv (vlMoll n) j - vlDeriv (vlMoll m) j) r x s =
        (-1) * ∫ x, (vlConvT (vlMoll n) h x s - vlConvT (vlMoll m) h x s) *
          (vlConvT (vlMoll n) r x s - vlConvT (vlMoll m) r x s) := by
    intro n m
    have hκ : IsVlKernel (vlMoll n - vlMoll m) := (vlMoll_kernel n).sub (vlMoll_kernel m)
    have hd := (vlDeriv_sub (vlMoll_kernel n) (vlMoll_kernel m) j).symm
    rw [hd]
    filter_upwards [lps_grad_pairing j hwm hrm hhm hw hr hg hh hgrad hhess hκ,
      vlConvT_sub_kernel_ae (vlMoll_kernel n) (vlMoll_kernel m) hhm hh,
      vlConvT_sub_kernel_ae (vlMoll_kernel n) (vlMoll_kernel m) hrm hr] with s h1 h2 h3
    rw [h1, neg_one_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [h2 x, h3 x]
  have hpairDiag : ∀ n, ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT (vlDeriv (vlMoll n) j) w x s * vlConvT (vlDeriv (vlMoll n) j) r x s =
        (-1) * ∫ x, vlConvT (vlMoll n) h x s * vlConvT (vlMoll n) r x s := by
    intro n
    filter_upwards [lps_grad_pairing j hwm hrm hhm hw hr hg hh hgrad hhess
      (vlMoll_kernel n)] with s h1
    rw [h1, neg_one_mul]
  obtain ⟨L, hLc, hLq, hLid⟩ := lps_kernel_limit_curve hab hwm hrm hw hr hweak
    (k := fun n => vlDeriv (vlMoll n) j) hkn
    (P := fun n z => vlConvT (vlMoll n) h z.1 z.2)
    (Q := fun n z => vlConvT (vlMoll n) r z.1 z.2)
    (fun n => vlConvT_stronglyMeasurable (vlMoll_kernel n).continuous hhm)
    (fun n => vlConvT_stronglyMeasurable (vlMoll_kernel n).continuous hrm)
    (fun n => vlConvT_memLp (vlMoll_kernel n) hhm hh)
    (fun n => vlConvT_memLp (vlMoll_kernel n) hrm hr) (-1) hpairDiff hpairDiag
    (q := g) (p := h) (q' := r) hgm hg hh hr hSg
    (by
      filter_upwards [ae_all_iff.2 (fun n => lps_conv_first_deriv_ae j hwm hgm hw hg hgrad
        (vlMoll_kernel n)), vlSlab_slice_memLp hgm hg] with s hfs hgs
      refine (vlMoll_tendsto hgs).congr fun n => ?_
      refine integral_congr_ae ?_
      filter_upwards [hfs n] with x hx
      change (vlConvT (vlMoll n) g x s - g (x, s)) ^ 2 =
        (vlConvT (vlDeriv (vlMoll n) j) w x s - g (x, s)) ^ 2
      rw [hx])
    hSh hSr
  refine ⟨L, hLc, hLq, fun s t hs ht hst => ?_⟩
  rw [hLid s t hs ht hst]
  ring

end ESS.LPS

end

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyWeakTime

/-!
# Square-integrable fields on a space-time slab

Fubini on the slab `ℝ³ × (a, τ)`: square-integrable slab fields have
square-integrable time slices for almost every time, their slice energies are
integrable in time, and kernel convolutions of slab fields are again
square-integrable on the slab, with the `L¹` norm of the kernel as the Young
constant. These are the measure-theoretic steps of
`lem:localized-vorticity-energy` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set Filter

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

/-- Young's inequality for the squared `L²` integral. -/
theorem vlConv_integral_sq_le {k h : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : MemLp h 2 volume) :
    ∫ x, (vlConv k h x) ^ 2 ≤ (∫ y, |k y|) ^ 2 * ∫ x, (h x) ^ 2 := by
  have hc0 : 0 ≤ ∫ y, |k y| := integral_nonneg fun y => abs_nonneg (k y)
  have hconv := vlConv_memLp hk hh
  have hyoung := vlConv_eLpNorm_le hk hh
  have hsq : ∀ {g : Vec3 → ℝ}, MemLp g 2 volume →
      eLpNorm g 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, (g x) ^ 2)) := by
    intro g hg
    rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 1
    rw [Real.sqrt_eq_rpow]
    congr 1
    · congr 1
      funext x
      rw [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two, sq_abs]
    · norm_num
  rw [hsq hconv, hsq hh, ← ENNReal.ofReal_mul hc0,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc0 (Real.sqrt_nonneg _))] at hyoung
  have hI0 : 0 ≤ ∫ x, (vlConv k h x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hJ0 : 0 ≤ ∫ x, (h x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hyoung 2
  rw [Real.sq_sqrt hI0, mul_pow, Real.sq_sqrt hJ0] at h2
  exact h2

/-- Slab integrals as iterated integrals, time outside. -/
theorem vlSlab_integral_eq {a τ : ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : Integrable F (volume.restrict (vlSlab a τ))) :
    ∫ p in vlSlab a τ, F p = ∫ s in Ioo a τ, ∫ y, F (y, s) := by
  rw [vlSlab_measure] at hF ⊢
  exact integral_prod_symm _ hF

/-- Almost every time slice of a square-integrable slab field is square
integrable. -/
theorem vlSlab_slice_memLp {a τ : ℝ} {g : Vec3 × ℝ → ℝ} (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) :
    ∀ᵐ s ∂(volume.restrict (Ioo a τ)), MemLp (fun y => g (y, s)) 2 volume := by
  have hsq := hg.integrable_sq
  rw [vlSlab_measure] at hsq
  filter_upwards [hsq.prod_left_ae] with s hs
  have hm : AEStronglyMeasurable (fun y => g (y, s)) volume :=
    (hgm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).2 hs

/-- The slice energy of a square-integrable slab field is integrable in time. -/
theorem vlSlab_sliceSq_integrableOn {a τ : ℝ} {g : Vec3 × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) :
    IntegrableOn (fun s => ∫ y, (g (y, s)) ^ 2) (Ioo a τ) volume := by
  have hsq := hg.integrable_sq
  rw [vlSlab_measure] at hsq
  exact hsq.integral_prod_right

/-- The slab energy is the time integral of the slice energies. -/
theorem vlSlab_integral_sq {a τ : ℝ} {g : Vec3 × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) :
    ∫ p in vlSlab a τ, (g p) ^ 2 = ∫ s in Ioo a τ, ∫ y, (g (y, s)) ^ 2 :=
  vlSlab_integral_eq hg.integrable_sq

/-- Kernel convolutions of a measurable field are jointly measurable. -/
theorem vlConvT_stronglyMeasurable {k : Vec3 → ℝ} (hk : Continuous k)
    {w : Vec3 × ℝ → ℝ} (hw : StronglyMeasurable w) :
    StronglyMeasurable (fun p : Vec3 × ℝ => vlConvT k w p.1 p.2) := by
  have hF : StronglyMeasurable (fun q : (Vec3 × ℝ) × Vec3 => k q.2 * w (q.1.1 - q.2, q.1.2)) :=
    (hk.measurable.comp measurable_snd).stronglyMeasurable.mul
      (hw.comp_measurable ((measurable_fst.fst.sub measurable_snd).prodMk
        measurable_fst.snd))
  have h := hF.integral_prod_right' (ν := (volume : Measure Vec3))
  have heq : (fun p : Vec3 × ℝ => vlConvT k w p.1 p.2) =
      fun p => ∫ y, k y * w (p.1 - y, p.2) := by
    funext p
    simp only [vlConvT, vlConv_apply]
  rw [heq]
  exact h

/-- Kernel convolutions of square-integrable slab fields are square integrable
on the slab. -/
theorem vlConvT_memLp {a τ : ℝ} {k : Vec3 → ℝ} (hk : IsVlKernel k)
    {w : Vec3 × ℝ → ℝ} (hwm : StronglyMeasurable w)
    (hw : MemLp w 2 (volume.restrict (vlSlab a τ))) :
    MemLp (fun p : Vec3 × ℝ => vlConvT k w p.1 p.2) 2 (volume.restrict (vlSlab a τ)) := by
  have hm := vlConvT_stronglyMeasurable hk.continuous hwm
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  rw [vlSlab_measure]
  have hsqm : AEStronglyMeasurable (fun p : Vec3 × ℝ => (vlConvT k w p.1 p.2) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a τ))) :=
    (hm.pow 2).aestronglyMeasurable
  refine (integrable_prod_iff' hsqm).2 ⟨?_, ?_⟩
  · filter_upwards [vlSlab_slice_memLp hwm hw] with s hs
    exact (vlConv_memLp hk hs).integrable_sq
  · have hbound : IntegrableOn (fun s => (∫ y, |k y|) ^ 2 * ∫ y, (w (y, s)) ^ 2)
        (Ioo a τ) volume := (vlSlab_sliceSq_integrableOn hw).const_mul _
    refine hbound.mono' ?_ ?_
    · exact hsqm.norm.prod_swap.integral_prod_right'
    · filter_upwards [vlSlab_slice_memLp hwm hw] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      exact vlConv_integral_sq_le hk hs

/-- Restriction of a slab field to a shorter slab. -/
theorem vlSlab_memLp_mono {a τ t : ℝ} (ht : t ≤ τ) {g : Vec3 × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) :
    MemLp g 2 (volume.restrict (vlSlab a t)) :=
  hg.mono_measure (Measure.restrict_mono (prod_mono subset_rfl
    (Ioo_subset_Ioo_right ht)) le_rfl)

end CKN

end

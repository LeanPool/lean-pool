/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitSlices
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongCompactness

/-!
# Identification of a continuous curve with weakly continuous slices

A continuous `L²` curve which represents a family of `L²` slices for almost every time represents
it at every time when the family is weakly continuous (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- Two continuous functions on a closed interval that agree almost everywhere on its interior
agree everywhere. -/
theorem lps_eqOn_Icc_of_ae_eq {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (h : ∀ᵐ s ∂(volume.restrict (Ioo a b)), f s = g s) : EqOn f g (Icc a b) := by
  have hEqIoo := Measure.eqOn_open_of_ae_eq h isOpen_Ioo (hf.mono Ioo_subset_Icc_self)
    (hg.mono Ioo_subset_Icc_self)
  exact hEqIoo.of_subset_closure hf hg Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])

/-- A continuous `L²` curve representing a weakly continuous family of `L²` slices almost
everywhere represents it everywhere. -/
theorem lps_curve_eq_of_weak_continuous {a b : ℝ} (hab : a < b) {F : Vec3 × ℝ → ℝ}
    {L : Icc a b → Lp ℝ 2 (volume : Measure Vec3)} (hL : Continuous L)
    (hLF : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ hs : s ∈ Icc a b,
      ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => F (x, s))
    (hFmem : ∀ t ∈ Icc a b, MemLp (fun x => F (x, t)) 2 volume)
    (hFweak : ∀ w : Vec3 → ℝ, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x, F (x, t) * w x) (Icc a b)) :
    ∀ (t : ℝ) (ht : t ∈ Icc a b),
      ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => F (x, t) := by
  classical
  let proj : ℝ → Icc a b := Set.projIcc a b hab.le
  have hLr : Continuous (fun t : ℝ => L (proj t)) := hL.comp continuous_projIcc
  -- weak identification
  have hweak : ∀ w : Vec3 → ℝ, MemLp w 2 volume → ∀ t (ht : t ∈ Icc a b),
      (∫ x, ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x * w x) =
        ∫ x, F (x, t) * w x := by
    intro w hw t ht
    have hc1 : Continuous (fun s : ℝ => ∫ x, ((L (proj s) : Lp ℝ 2 (volume : Measure Vec3)) :
        Vec3 → ℝ) x * w x) := by
      have : (fun s : ℝ => ∫ x, ((L (proj s) : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x *
          w x) = fun s => inner ℝ (L (proj s)) (hw.toLp w) := by
        funext s
        exact (lps_scalar_lp_inner_left_eq_integral hw).symm
      rw [this]
      exact hLr.inner continuous_const
    have hEq := lps_eqOn_Icc_of_ae_eq hab hc1.continuousOn (hFweak w hw) (by
      filter_upwards [hLF, ae_restrict_mem measurableSet_Ioo] with s hs hsI
      have hsI' : s ∈ Icc a b := Ioo_subset_Icc_self hsI
      have hp : proj s = ⟨s, hsI'⟩ := Set.projIcc_of_mem hab.le hsI'
      simp only [hp]
      exact integral_congr_ae ((hs hsI').mono fun x hx => by
        show ((L ⟨s, hsI'⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x * w x = F (x, s) * w x
        rw [hx]))
    have := hEq ht
    have hp : proj t = ⟨t, ht⟩ := Set.projIcc_of_mem hab.le ht
    simpa only [hp] using this
  intro t ht
  set e : Vec3 → ℝ := fun x => ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x -
    F (x, t) with he
  have hem : MemLp e 2 volume := (Lp.memLp (L ⟨t, ht⟩)).sub (hFmem t ht)
  have hzero : (∫ x, e x * e x) = 0 := by
    have h1 := hweak e hem t ht
    have hint1 : Integrable (fun x => ((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x *
        e x) volume := (Lp.memLp (L ⟨t, ht⟩)).integrable_mul hem
    have hint2 : Integrable (fun x => F (x, t) * e x) volume := (hFmem t ht).integrable_mul hem
    calc (∫ x, e x * e x) = ∫ x, (((L ⟨t, ht⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x *
          e x - F (x, t) * e x) := by
          congr 1; funext x; simp only [he]; ring
      _ = 0 := by rw [integral_sub hint1 hint2, h1, sub_self]
  have hsq : (fun x => e x * e x) = fun x => e x ^ 2 := by funext x; ring
  rw [hsq] at hzero
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (e x)) hem.integrable_sq).1 hzero
  filter_upwards [hz] with x hx
  have : e x = 0 := by simpa using hx
  simp only [he] at this
  linarith only [this]

end ESS.LPS

end

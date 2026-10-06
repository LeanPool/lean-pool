/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyBound

/-!
# The energy of the mollified velocity at a point

At every spatial point the mollified forced regularized velocity is an
absolutely continuous function of time on bounded intervals, with derivative
minus the source. Against a smooth time profile vanishing near the ends of an
interval, the square of the mollified velocity therefore satisfies
`∫ w² ∂ₜψ = 2 ∫ w S ψ`. This is the time part of the local energy inequality
`eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

theorem deriv_eq_zero_of_eventually_eq_zero {g : ℝ → ℝ} {t : ℝ} (h : g =ᶠ[nhds t] fun _ => 0) :
    deriv g t = 0 := by
  rw [h.deriv_eq]
  simp

section AC

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The time energy identity of the mollified velocity at a point. -/
theorem integral_leW_sq_time {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (x : Vec3) (k : Fin 3) {T : ℝ} (hT : 0 < T)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    (hdT : d < T) (hψs : ∀ t, t ∉ Ioo c d → ψ t = 0)
    (hSi : IntegrableOn (fun t => leSF ρ ε hε ha hf η x t k) (Ioo 0 T)) :
    ∫ t in Ioo 0 T, leW ρ ε hε ha hf η x t k ^ 2 * deriv ψ t =
      2 * ∫ t in Ioo 0 T, leW ρ ε hε ha hf η x t k * leSF ρ ε hε ha hf η x t k * ψ t := by
  set W := fun t => leW ρ ε hε ha hf η x t k with hWdef
  set g := fun t => -leSF ρ ε hε ha hf η x t k with hgdef
  have hweak := hasWeakDerivOn_leW_F ρ ε hε ha hf hη hηc x k hT
  have hWc : Continuous W := continuous_leW ρ ε hε ha hf hη.continuous hηc x k
  have hWloc : LocallyIntegrableOn W (Ioo 0 T) volume :=
    hWc.continuousOn.locallyIntegrableOn measurableSet_Ioo
  have hgi : IntegrableOn g (Ioo 0 T) := hSi.neg
  obtain ⟨C, hC⟩ := CKN.eq_const_add_intervalIntegral_of_continuous_weakDeriv hT
    ⟨hc, hcd.trans hdT⟩ hWloc hgi.locallyIntegrableOn hweak hWc.continuousOn
  have hsub : Icc c d ⊆ Ioo 0 T := fun t ht => ⟨hc.trans_le ht.1, ht.2.trans_lt hdT⟩
  have hgint : IntervalIntegrable g volume c d :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd.le).2
      (hgi.mono_set (Ioc_subset_Icc_self.trans hsub))
  set A : ℝ → ℝ := fun t => C + ∫ s in c..t, g s with hAdef
  have hWA : ∀ t ∈ Icc c d, W t = A t := fun t ht => hC t (hsub ht)
  have hAac : AbsolutelyContinuousOnInterval A c d := by
    have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) c d :=
      (contDiffOn_const (c := C)).absolutelyContinuousOnInterval
    exact h1.add (hgint.absolutelyContinuousOnInterval_intervalIntegral (c := c)
      Set.left_mem_uIcc)
  have hA2 : AbsolutelyContinuousOnInterval (fun t => A t * A t) c d := hAac.fun_mul hAac
  have hψac : AbsolutelyContinuousOnInterval ψ c d :=
    (hψ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hibp := hA2.integral_mul_deriv_eq_deriv_mul hψac
  rw [hψs c (fun h => lt_irrefl _ h.1), hψs d (fun h => lt_irrefl _ h.2), mul_zero, mul_zero,
    sub_zero, zero_sub] at hibp
  have hderiv : ∀ᵐ t, t ∈ uIoc c d → deriv (fun t => A t * A t) t * ψ t =
      -(2 * (A t * leSF ρ ε hε ha hf η x t k * ψ t)) := by
    filter_upwards [hgint.ae_hasDerivAt_integral] with t ht htmem
    have htI : t ∈ uIcc c d := uIoc_subset_uIcc htmem
    have hAd : HasDerivAt A (g t) t := by
      have := ht htI c Set.left_mem_uIcc
      simpa [A] using this.const_add C
    have hd : HasDerivAt (fun t => A t * A t) (g t * A t + A t * g t) t := hAd.mul hAd
    rw [hd.deriv]
    simp only [g]
    ring
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_neg] at hibp
  -- replace `A` by `W` on `[c, d]`
  have e1 : ∫ t in c..d, A t * A t * deriv ψ t = ∫ t in c..d, W t ^ 2 * deriv ψ t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hcd.le] at ht
    rw [hWA t ht, sq]
  have e2 : ∫ t in c..d, 2 * (A t * leSF ρ ε hε ha hf η x t k * ψ t) =
      ∫ t in c..d, 2 * (W t * leSF ρ ε hε ha hf η x t k * ψ t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hcd.le] at ht
    rw [hWA t ht]
  rw [e1, e2, neg_neg, intervalIntegral.integral_const_mul] at hibp
  -- pass to set integrals over `(0, T)`
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
    rw [ae_iff]
    simp
  have f1 : ∫ t in Ioo 0 T, W t ^ 2 * deriv ψ t = ∫ t in Ioc c d, W t ^ 2 * deriv ψ t := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
      (Ioc_subset_Icc_self.trans hsub) ?_
    filter_upwards [hnull] with t htc ht
    have hout : t ∉ Icc c d := fun h => ht.2 ⟨lt_of_le_of_ne h.1 (Ne.symm htc), h.2⟩
    have hev : ψ =ᶠ[nhds t] fun _ => 0 := by
      have hopen : IsOpen (Icc c d)ᶜ := isClosed_Icc.isOpen_compl
      filter_upwards [hopen.mem_nhds hout] with s hs
      exact hψs s fun h => hs (Ioo_subset_Icc_self h)
    rw [deriv_eq_zero_of_eventually_eq_zero hev, mul_zero]
  have f2 : ∫ t in Ioo 0 T, W t * leSF ρ ε hε ha hf η x t k * ψ t =
      ∫ t in Ioc c d, W t * leSF ρ ε hε ha hf η x t k * ψ t := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
      (Ioc_subset_Icc_self.trans hsub) (Eventually.of_forall fun t ht => ?_)
    have hout : t ∉ Ioo c d := fun h => ht.2 (Ioo_subset_Ioc_self h)
    rw [hψs t hout, mul_zero]
  rw [f1, f2, ← intervalIntegral.integral_of_le hcd.le, ← intervalIntegral.integral_of_le hcd.le,
    hibp]

end AC

end CKN.Leray

end

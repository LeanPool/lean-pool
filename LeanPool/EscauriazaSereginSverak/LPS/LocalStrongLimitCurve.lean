/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitKernel

/-!
# Continuous `L²` representatives from kernel limits

If mollifications of a field with a square-integrable time derivative
converge in the slab, and the slice pairings of the mollified fields and their
time derivatives are represented by convergent dual fields, then the field has
a continuous `L²`-valued representative with an energy identity in time
(`prop:lps-local-strong`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

variable {a b : ℝ} {w r : Vec3 × ℝ → ℝ}

/-- The kernel-limit theorem: a continuous `L²` curve representing the limit
of the mollified fields, with the energy identity in time. -/
theorem lps_kernel_limit_curve (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : ℕ → Vec3 → ℝ} (hk : ∀ n, IsVlKernel (k n))
    {P Q : ℕ → Vec3 × ℝ → ℝ}
    (hPm : ∀ n, StronglyMeasurable (P n)) (hQm : ∀ n, StronglyMeasurable (Q n))
    (hP : ∀ n, MemLp (P n) 2 (volume.restrict (vlSlab a b)))
    (hQ : ∀ n, MemLp (Q n) 2 (volume.restrict (vlSlab a b))) (c : ℝ)
    (hpairDiff : ∀ n m, ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT (k n - k m) w x s * vlConvT (k n - k m) r x s =
        c * ∫ x, (P n (x, s) - P m (x, s)) * (Q n (x, s) - Q m (x, s)))
    (hpairDiag : ∀ n, ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT (k n) w x s * vlConvT (k n) r x s =
        c * ∫ x, P n (x, s) * Q n (x, s))
    {q p q' : Vec3 × ℝ → ℝ} (hqm : StronglyMeasurable q)
    (hq : MemLp q 2 (volume.restrict (vlSlab a b)))
    (hp : MemLp p 2 (volume.restrict (vlSlab a b)))
    (hq' : MemLp q' 2 (volume.restrict (vlSlab a b)))
    (hSslab : Tendsto (fun n => ∫ z in vlSlab a b,
      (vlConvT (k n) w z.1 z.2 - q z) ^ 2) atTop (𝓝 0))
    (hSslice : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      Tendsto (fun n => ∫ x, (vlConvT (k n) w x s - q (x, s)) ^ 2) atTop (𝓝 0))
    (hPlim : Tendsto (fun n => ∫ z in vlSlab a b, (P n z - p z) ^ 2) atTop (𝓝 0))
    (hQlim : Tendsto (fun n => ∫ z in vlSlab a b, (Q n z - q' z) ^ 2) atTop (𝓝 0)) :
    ∃ L : Icc a b → Lp ℝ 2 (volume : Measure Vec3), Continuous L ∧
      (∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ hs : s ∈ Icc a b,
        ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => q (x, s)) ∧
      ∀ (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b), s ≤ t →
        ‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2 = 2 * c * ∫ z in vlSlab s t, p z * q' z := by
  classical
  have hS2 : ∀ n, MemLp (fun z : Vec3 × ℝ => vlConvT (k n) w z.1 z.2) 2
      (volume.restrict (vlSlab a b)) := fun n => vlConvT_memLp (hk n) hwm hw
  let C : ℕ → Icc a b → Lp ℝ 2 (volume : Measure Vec3) :=
    fun n t => lpsCurve a b (k n) w r t.1
      (lps_prim_memLp hab hwm hrm hw hr hweak (hk n) t.2)
  let eS : ℕ → ℝ := fun n => ∫ z in vlSlab a b, (vlConvT (k n) w z.1 z.2 - q z) ^ 2
  let eP : ℕ → ℝ := fun n => ∫ z in vlSlab a b, (P n z - p z) ^ 2
  let eQ : ℕ → ℝ := fun n => ∫ z in vlSlab a b, (Q n z - q' z) ^ 2
  let f : ℕ → ℝ := fun n =>
    (b - a)⁻¹ * (2 * eS n) + |c| * (2 * eP n + 2 * eQ n)
  have hf : Tendsto f atTop (𝓝 0) := by
    have h := ((hSslab.const_mul (2 : ℝ)).const_mul ((b - a)⁻¹)).add
      ((((hPlim.const_mul (2 : ℝ)).add (hQlim.const_mul (2 : ℝ)))).const_mul |c|)
    simpa using h
  have hdist : ∀ n m (t : Icc a b), ‖C n t - C m t‖ ^ 2 ≤ f n + f m := by
    intro n m t
    have h := lps_curve_dist_sq_le hab hwm hrm hw hr hweak (hk n) (hk m)
      (U := fun z => P n z - P m z) (V := fun z => Q n z - Q m z)
      ((hPm n).sub (hPm m)) ((hQm n).sub (hQm m))
      ((hP n).sub (hP m)) ((hQ n).sub (hQ m)) c (hpairDiff n m) t.2
    have h1 : ∫ z in vlSlab a b, (vlConvT (k n - k m) w z.1 z.2) ^ 2 ≤
        2 * eS n + 2 * eS m := by
      rw [lps_slab_conv_sub_eq hwm hw (hk n) (hk m)]
      exact lps_slab_sq_sub_le (hS2 n) (hS2 m) hq
    have h2 : ∫ z in vlSlab a b, (P n z - P m z) ^ 2 ≤ 2 * eP n + 2 * eP m :=
      lps_slab_sq_sub_le (hP n) (hP m) hp
    have h3 : ∫ z in vlSlab a b, (Q n z - Q m z) ^ 2 ≤ 2 * eQ n + 2 * eQ m :=
      lps_slab_sq_sub_le (hQ n) (hQ m) hq'
    have hpos : 0 ≤ (b - a)⁻¹ := inv_nonneg.2 (sub_pos.2 hab).le
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have hh := h
    simp only [C] at *
    have := mul_le_mul_of_nonneg_left h1 hpos
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hc0
    simp only [f]
    linarith only [hh, this, h4]
  have hUC : UniformCauchySeqOn C atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hev : ∀ᶠ n in atTop, f n < ε ^ 2 / 2 :=
      hf.eventually (gt_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun m hm n hn t _ => ?_⟩
    rw [dist_eq_norm]
    have h := hdist m n t
    have hm' := hN m hm
    have hn' := hN n hn
    have hsq : ‖C m t - C n t‖ ^ 2 < ε ^ 2 := by
      have hε2 : 0 < ε ^ 2 := by positivity
      linarith only [h, hm', hn', hε2]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq
  let L : Icc a b → Lp ℝ 2 (volume : Measure Vec3) := fun t => limUnder atTop fun n => C n t
  have hL : ∀ t, Tendsto (fun n => C n t) atTop (𝓝 (L t)) := by
    intro t
    have hc := hUC.cauchySeq (mem_univ t)
    obtain ⟨L₀, hL₀⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨L₀, hL₀⟩
  have hunif := hUC.tendstoUniformlyOn_of_tendsto (fun t _ => hL t)
  rw [tendstoUniformlyOn_univ] at hunif
  have hcont : Continuous L :=
    hunif.continuous (Frequently.of_forall fun n =>
      lpsCurve_continuous hab hwm hrm hw hr hweak (hk n))
  refine ⟨L, hcont, ?_, ?_⟩
  · -- identification with the limit field
    filter_upwards [ae_all_iff.2 (fun n => lps_prim_slice_ae hab hwm hrm hw hr hweak (hk n)),
      vlSlab_slice_memLp hqm hq, hSslice, ae_restrict_mem measurableSet_Ioo]
      with s hsl hqs hS hsI hs
    have hlim : Tendsto (fun n => C n ⟨s, hs⟩) atTop (𝓝 (hqs.toLp _)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hsq : ∀ n, ‖C n ⟨s, hs⟩ - hqs.toLp _‖ ^ 2 =
          ∫ x, (vlConvT (k n) w x s - q (x, s)) ^ 2 := by
        intro n
        have hmem := lps_prim_memLp hab hwm hrm hw hr hweak (hk n) hs
        have hCn : C n ⟨s, hs⟩ = hmem.toLp _ := lpsCurve_eq hab hwm hrm hw hr hweak (hk n) hs
        rw [hCn, ← MemLp.toLp_sub, vl_norm_toLp_sq]
        refine integral_congr_ae ?_
        filter_upwards [hsl n] with x hx
        simp only [Pi.sub_apply]
        rw [hx]
      have hroot : Tendsto (fun n => Real.sqrt
          (∫ x, (vlConvT (k n) w x s - q (x, s)) ^ 2)) atTop (𝓝 0) := by
        simpa using hS.sqrt
      refine hroot.congr (fun n => ?_)
      rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]
    have hLeq : L ⟨s, hs⟩ = hqs.toLp _ := tendsto_nhds_unique (hL _) hlim
    rw [hLeq]
    exact hqs.coeFn_toLp
  · intro s t hs ht hst
    have hsub : vlSlab s t ⊆ vlSlab a b :=
      prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)
    have hmono : ∀ {g : Vec3 × ℝ → ℝ}, MemLp g 2 (volume.restrict (vlSlab a b)) →
        MemLp g 2 (volume.restrict (vlSlab s t)) := fun hg =>
      hg.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hsl : ∀ {g h : ℕ → Vec3 × ℝ → ℝ} {gl : Vec3 × ℝ → ℝ},
        (∀ n, MemLp (g n) 2 (volume.restrict (vlSlab a b))) →
        MemLp gl 2 (volume.restrict (vlSlab a b)) →
        Tendsto (fun n => ∫ z in vlSlab a b, (g n z - gl z) ^ 2) atTop (𝓝 0) →
        Tendsto (fun n => ∫ z in vlSlab s t, (g n z - gl z) ^ 2) atTop (𝓝 0) := by
      intro g h gl hg hgl hlim
      refine squeeze_zero (fun n => integral_nonneg fun z => sq_nonneg _) (fun n => ?_) hlim
      exact setIntegral_mono_set ((hg n).sub hgl).integrable_sq
        (Eventually.of_forall fun z => sq_nonneg _) hsub.eventuallyLE
    have h1 : Tendsto (fun n => ‖C n ⟨t, ht⟩‖ ^ 2 - ‖C n ⟨s, hs⟩‖ ^ 2) atTop
        (𝓝 (‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2)) :=
      ((hL _).norm.pow 2).sub ((hL _).norm.pow 2)
    have h2 : Tendsto (fun n => 2 * c * ∫ z in vlSlab s t, P n z * Q n z) atTop
        (𝓝 (2 * c * ∫ z in vlSlab s t, p z * q' z)) := by
      refine (lps_integral_mul_tendsto (μ := volume.restrict (vlSlab s t))
        (fun n => hmono (hP n)) (fun n => hmono (hQ n)) (hmono hp) (hmono hq')
        (hsl (h := P) hP hp hPlim) (hsl (h := Q) hQ hq' hQlim)).const_mul _
    have h3 : ∀ n, ‖C n ⟨t, ht⟩‖ ^ 2 - ‖C n ⟨s, hs⟩‖ ^ 2 =
        2 * c * ∫ z in vlSlab s t, P n z * Q n z := fun n =>
      lpsCurve_energy_identity hab hwm hrm hw hr hweak (hk n) (hP n) (hQ n) c
        (hpairDiag n) hs ht hst
    exact tendsto_nhds_unique h1 (h2.congr fun n => (h3 n).symm)

end ESS.LPS

end

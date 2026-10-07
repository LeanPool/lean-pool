/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitPrimitive
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyCurve

/-!
# Continuous `L²` curves from mollified time primitives

The mollified primitives of a field with a square-integrable time derivative
are Hölder continuous `L²`-valued curves, with an explicit energy identity in
time (`prop:lps-local-strong`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

variable {a b : ℝ} {w r : Vec3 × ℝ → ℝ}

/-- The time slice of the mollified primitive as an element of `L²(ℝ³)`. -/
@[expose] def lpsCurve (a b : ℝ) (k : Vec3 → ℝ) (w r : Vec3 × ℝ → ℝ) (t : ℝ)
    (h : MemLp (fun x => lpsPrim a b k w r x t) 2 volume) : Lp ℝ 2 (volume : Measure Vec3) :=
  h.toLp _

theorem lps_prim_memLp (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) {t : ℝ} (ht : t ∈ Icc a b) :
    MemLp (fun x => lpsPrim a b k w r x t) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => lpsPrim a b k w r x t) volume :=
    ((lps_prim_stronglyMeasurable hwm hrm hk).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).2
    ((lps_prim_energy hab hwm hrm hw hr hweak hk).1 t ht)

theorem lpsCurve_eq (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) {t : ℝ} (ht : t ∈ Icc a b) :
    lpsCurve a b k w r t (lps_prim_memLp hab hwm hrm hw hr hweak hk ht) =
      (lps_prim_memLp hab hwm hrm hw hr hweak hk ht).toLp _ :=
  rfl

theorem lpsCurve_norm_sq (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖lpsCurve a b k w r t (lps_prim_memLp hab hwm hrm hw hr hweak hk ht)‖ ^ 2 =
      ∫ x, (lpsPrim a b k w r x t) ^ 2 := by
  rw [lpsCurve_eq hab hwm hrm hw hr hweak hk ht, vl_norm_toLp_sq]

theorem lpsCurve_sub_norm_sq (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k l : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖lpsCurve a b k w r t (lps_prim_memLp hab hwm hrm hw hr hweak hk ht) -
        lpsCurve a b l w r t (lps_prim_memLp hab hwm hrm hw hr hweak hl ht)‖ ^ 2 =
      ∫ x, (lpsPrim a b (k - l) w r x t) ^ 2 := by
  have hn := lps_prim_memLp hab hwm hrm hw hr hweak hk ht
  have hm := lps_prim_memLp hab hwm hrm hw hr hweak hl ht
  rw [lpsCurve_eq hab hwm hrm hw hr hweak hk ht, lpsCurve_eq hab hwm hrm hw hr hweak hl ht,
    ← MemLp.toLp_sub, vl_norm_toLp_sq]
  congr 1
  funext x
  rw [lps_prim_sub_kernel hab hwm hrm hw hr hk hl x ht]
  rfl

/-- The curve of a mollified primitive is Hölder continuous in time. -/
theorem lpsCurve_dist_sq_le_time (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) {t t' : ℝ} (ht : t ∈ Icc a b)
    (ht' : t' ∈ Icc a b) (htt : t' ≤ t) :
    ‖lpsCurve a b k w r t (lps_prim_memLp hab hwm hrm hw hr hweak hk ht) -
        lpsCurve a b k w r t' (lps_prim_memLp hab hwm hrm hw hr hweak hk ht')‖ ^ 2 ≤
      (t - t') * ∫ p in vlSlab a b, (vlConvT k r p.1 p.2) ^ 2 := by
  have hn := lps_prim_memLp hab hwm hrm hw hr hweak hk ht
  have hn' := lps_prim_memLp hab hwm hrm hw hr hweak hk ht'
  rw [lpsCurve_eq hab hwm hrm hw hr hweak hk ht, lpsCurve_eq hab hwm hrm hw hr hweak hk ht',
    ← MemLp.toLp_sub, vl_norm_toLp_sq]
  have hG2 := lps_slab_integrable_sq (vlConvT_memLp hk hrm hr)
  have hdiff : ∀ x, lpsPrim a b k w r x t - lpsPrim a b k w r x t' =
      ∫ s in Ioo t' t, vlConvT k r x s := by
    intro x
    rw [lps_prim_increment hr hab hk x t' ht' t ht,
      intervalIntegral.integral_of_le htt, integral_Ioc_eq_integral_Ioo]
  have hsubI : Ioo t' t ⊆ Ioo a b := Ioo_subset_Ioo ht'.1 ht.2
  have hpoint : ∀ᵐ x ∂(volume : Measure Vec3),
      (lpsPrim a b k w r x t - lpsPrim a b k w r x t') ^ 2 ≤
        (t - t') * ∫ s in Ioo a b, (vlConvT k r x s) ^ 2 := by
    have hG2' : Integrable (fun p : Vec3 × ℝ => (vlConvT k r p.1 p.2) ^ 2)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact hG2
    filter_upwards [hG2'.prod_right_ae] with x hx
    rw [hdiff x]
    have hxJ : IntegrableOn (fun s => (vlConvT k r x s) ^ 2) (Ioo a b) volume := hx
    refine (vl_sq_setIntegral_le htt ((vlConvT_integrableOn hr hk x).mono_set hsubI)
      (hxJ.mono_set hsubI)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 htt)
    exact setIntegral_mono_set hxJ (Eventually.of_forall fun s => sq_nonneg _)
      (Eventually.of_forall hsubI)
  have hG2' : Integrable (fun p : Vec3 × ℝ => (vlConvT k r p.1 p.2) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hG2
  have hRint : Integrable (fun x => (t - t') *
      ∫ s in Ioo a b, (vlConvT k r x s) ^ 2) volume :=
    hG2'.integral_prod_left.const_mul _
  refine (integral_mono_ae (hn.sub hn').integrable_sq hRint hpoint).trans_eq ?_
  rw [integral_const_mul]
  congr 1
  rw [vlSlab_measure, integral_prod _ hG2']

theorem lpsCurve_continuous (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) :
    Continuous (fun t : Icc a b =>
      lpsCurve a b k w r t.1 (lps_prim_memLp hab hwm hrm hw hr hweak hk t.2)) := by
  set K := ∫ p in vlSlab a b, (vlConvT k r p.1 p.2) ^ 2 with hK
  have hK0 : 0 ≤ K := integral_nonneg fun p => sq_nonneg _
  have hbound : ∀ t t' : Icc a b,
      dist (lpsCurve a b k w r t.1 (lps_prim_memLp hab hwm hrm hw hr hweak hk t.2))
        (lpsCurve a b k w r t'.1 (lps_prim_memLp hab hwm hrm hw hr hweak hk t'.2)) ≤
      Real.sqrt (K * |t.1 - t'.1|) := by
    intro t t'
    rw [dist_eq_norm]
    rcases le_total t'.1 t.1 with h | h
    · have := lpsCurve_dist_sq_le_time hab hwm hrm hw hr hweak hk t.2 t'.2 h
      rw [abs_of_nonneg (sub_nonneg.2 h)]
      apply Real.le_sqrt_of_sq_le
      linarith only [this]
    · have := lpsCurve_dist_sq_le_time hab hwm hrm hw hr hweak hk t'.2 t.2 h
      rw [abs_of_nonpos (sub_nonpos.2 h), norm_sub_rev]
      apply Real.le_sqrt_of_sq_le
      linarith only [this]
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  have hlim : Tendsto (fun t : Icc a b => Real.sqrt (K * |t.1 - t₀.1|)) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t : Icc a b => Real.sqrt (K * |t.1 - t₀.1|)) :=
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs)).sqrt
    have := hc.tendsto t₀
    simpa using this
  exact squeeze_zero (fun t => dist_nonneg) (fun t => hbound t t₀) hlim

/-- The uniform Cauchy estimate for two mollified curves, in terms of the
`L²` size of the convolved field and of a pair of dual fields whose slice
pairing represents the slice pairing of the convolutions. -/
theorem lps_curve_dist_sq_le (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k l : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l)
    {U V : Vec3 × ℝ → ℝ} (hUm : StronglyMeasurable U) (hVm : StronglyMeasurable V)
    (hU : MemLp U 2 (volume.restrict (vlSlab a b)))
    (hV : MemLp V 2 (volume.restrict (vlSlab a b))) (c : ℝ)
    (hpair : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT (k - l) w x s * vlConvT (k - l) r x s =
        c * ∫ x, U (x, s) * V (x, s))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖lpsCurve a b k w r t (lps_prim_memLp hab hwm hrm hw hr hweak hk ht) -
        lpsCurve a b l w r t (lps_prim_memLp hab hwm hrm hw hr hweak hl ht)‖ ^ 2 ≤
      (b - a)⁻¹ * (∫ p in vlSlab a b, (vlConvT (k - l) w p.1 p.2) ^ 2) +
        |c| * ((∫ p in vlSlab a b, (U p) ^ 2) + ∫ p in vlSlab a b, (V p) ^ 2) := by
  have hκ : IsVlKernel (k - l) := hk.sub hl
  rw [lpsCurve_sub_norm_sq hab hwm hrm hw hr hweak hk hl ht]
  obtain ⟨_, hjoint, hid⟩ := lps_prim_energy hab hwm hrm hw hr hweak hκ
  set E : ℝ → ℝ := fun s => ∫ x, (lpsPrim a b (k - l) w r x s) ^ 2 with hE
  set IU : ℝ → ℝ := fun q => ∫ x, (U (x, q)) ^ 2 with hIU
  set IV : ℝ → ℝ := fun q => ∫ x, (V (x, q)) ^ 2 with hIV
  have hIUint : IntegrableOn IU (Ioo a b) volume := vlSlab_sliceSq_integrableOn hU
  have hIVint : IntegrableOn IV (Ioo a b) volume := vlSlab_sliceSq_integrableOn hV
  have hslice := lps_prim_slice_ae hab hwm hrm hw hr hweak hκ
  -- slice bound of the pairing
  have hF : ∀ᵐ q ∂(volume.restrict (Ioo a b)),
      ‖∫ x, lpsPrim a b (k - l) w r x q * vlConvT (k - l) r x q‖ ≤
        |c| / 2 * (IU q + IV q) := by
    filter_upwards [hslice, hpair, vlSlab_slice_memLp hUm hU, vlSlab_slice_memLp hVm hV]
      with q hq hp hUq hVq
    have h1 : ∫ x, lpsPrim a b (k - l) w r x q * vlConvT (k - l) r x q =
        c * ∫ x, U (x, q) * V (x, q) := by
      rw [← hp]
      refine integral_congr_ae ?_
      filter_upwards [hq] with x hx
      rw [← hx]
    rw [h1, Real.norm_eq_abs, abs_mul]
    have h2 : |∫ x, U (x, q) * V (x, q)| ≤ (IU q + IV q) / 2 := by
      have hi1 : Integrable (fun x => U (x, q) * V (x, q)) volume :=
        hUq.integrable_mul hVq
      have hi2 : Integrable (fun x => (U (x, q) ^ 2 + V (x, q) ^ 2) / 2) volume :=
        (hUq.integrable_sq.add hVq.integrable_sq).div_const 2
      calc
        |∫ x, U (x, q) * V (x, q)| ≤ ∫ x, |U (x, q) * V (x, q)| := by
          have := norm_integral_le_integral_norm (μ := (volume : Measure Vec3))
            (fun x => U (x, q) * V (x, q))
          simpa [Real.norm_eq_abs] using this
        _ ≤ ∫ x, (U (x, q) ^ 2 + V (x, q) ^ 2) / 2 := by
          refine integral_mono hi1.abs hi2 fun x => ?_
          rw [abs_mul]
          nlinarith only [sq_nonneg (|U (x, q)| - |V (x, q)|), sq_abs (U (x, q)),
            sq_abs (V (x, q))]
        _ = (IU q + IV q) / 2 := by
          rw [integral_div, integral_add hUq.integrable_sq hVq.integrable_sq]
    calc
      |c| * |∫ x, U (x, q) * V (x, q)| ≤ |c| * ((IU q + IV q) / 2) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
      _ = |c| / 2 * (IU q + IV q) := by ring
  set ε : ℝ := |c| * ((∫ p in vlSlab a b, (U p) ^ 2) + ∫ p in vlSlab a b, (V p) ^ 2)
    with hε
  have hεeq : ε = |c| * ∫ q in Ioo a b, (IU q + IV q) := by
    rw [hε, vlSlab_integral_sq hU, vlSlab_integral_sq hV, integral_add hIUint hIVint]
  -- increments of the energy are bounded by ε
  have hcongr : volume.restrict (Ioo a b) = volume.restrict (Ioc a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hF' : ∀ᵐ q ∂(volume.restrict (Ioc a b)),
      ‖∫ x, lpsPrim a b (k - l) w r x q * vlConvT (k - l) r x q‖ ≤
        |c| / 2 * (IU q + IV q) := by
    rw [← hcongr]
    exact hF
  have hgIoc : IntegrableOn (fun q => |c| / 2 * (IU q + IV q)) (Ioc a b) volume := by
    have h0 : Integrable (fun q => |c| / 2 * (IU q + IV q)) (volume.restrict (Ioo a b)) :=
      (hIUint.add hIVint).const_mul _
    rw [hcongr] at h0
    exact h0
  have hnn : ∀ q, 0 ≤ |c| / 2 * (IU q + IV q) := fun q =>
    mul_nonneg (by positivity) (add_nonneg (integral_nonneg fun x => sq_nonneg _)
      (integral_nonneg fun x => sq_nonneg _))
  have hbound : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → |E t - E s| ≤ ε := by
    intro s hs t ht hst
    have hEq : E t - E s =
        2 * ∫ q in s..t, ∫ x, lpsPrim a b (k - l) w r x q * vlConvT (k - l) r x q :=
      hid s hs t ht hst
    rw [hEq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      intervalIntegral.integral_of_le hst]
    have hsub : Ioc s t ⊆ Ioc a b := Ioc_subset_Ioc hs.1 ht.2
    have hg : Integrable (fun q => |c| / 2 * (IU q + IV q)) (volume.restrict (Ioc s t)) :=
      hgIoc.mono_set hsub
    have h1 : ‖∫ q in Ioc s t, ∫ x, lpsPrim a b (k - l) w r x q *
        vlConvT (k - l) r x q‖ ≤ ∫ q in Ioc s t, |c| / 2 * (IU q + IV q) :=
      norm_integral_le_of_norm_le hg (ae_restrict_of_ae_restrict_of_subset hsub hF')
    have h2 : ∫ q in Ioc s t, |c| / 2 * (IU q + IV q) ≤
        ∫ q in Ioc a b, |c| / 2 * (IU q + IV q) :=
      setIntegral_mono_set hgIoc (Eventually.of_forall hnn) hsub.eventuallyLE
    have h3 : ∫ q in Ioc a b, |c| / 2 * (IU q + IV q) = |c| / 2 * ∫ q in Ioo a b, (IU q + IV q)
      := by
      rw [← hcongr, integral_const_mul]
    rw [Real.norm_eq_abs] at h1
    rw [hεeq]
    nlinarith only [h1, h2, h3]
  have hall : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, E t ≤ E s + ε := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · have := hbound s hs t ht hst
      have := (abs_le.1 this).2
      linarith only [this]
    · have := hbound t ht s hs hts
      have := (abs_le.1 this).1
      linarith only [this]
  -- average over the time slices
  have hEint : IntegrableOn E (Ioo a b) volume := by
    have h := hjoint.integral_prod_right
    rw [← hcongr] at h
    exact h
  have hEeq : ∫ s in Ioo a b, E s =
      ∫ p in vlSlab a b, (vlConvT (k - l) w p.1 p.2) ^ 2 := by
    rw [vlSlab_integral_sq (vlConvT_memLp hκ hwm hw)]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hslice] with s hs hsI
    refine integral_congr_ae ?_
    filter_upwards [hs hsI] with x hx
    rw [hx]
  have hlen : (b - a) * E t ≤ (∫ p in vlSlab a b, (vlConvT (k - l) w p.1 p.2) ^ 2) +
      (b - a) * ε := by
    have hmono : ∫ s in Ioo a b, E t ≤ ∫ s in Ioo a b, (E s + ε) :=
      setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo]))
        (hEint.add (integrableOn_const (by simp [Real.volume_Ioo]))) measurableSet_Ioo
        (fun s hs => hall s (Ioo_subset_Icc_self hs) t ht)
    rw [setIntegral_const, integral_add hEint (integrableOn_const (by simp [Real.volume_Ioo])),
      setIntegral_const, Real.volume_real_Ioo_of_le hab.le, hEeq] at hmono
    simp only [smul_eq_mul] at hmono
    linarith only [hmono]
  have hpos : 0 < b - a := sub_pos.2 hab
  have : E t ≤ (b - a)⁻¹ * (∫ p in vlSlab a b, (vlConvT (k - l) w p.1 p.2) ^ 2) + ε := by
    have h := div_le_div_of_nonneg_right hlen hpos.le
    have e1 : (b - a) * E t / (b - a) = E t := by field_simp
    have e2 : ((∫ p in vlSlab a b, (vlConvT (k - l) w p.1 p.2) ^ 2) + (b - a) * ε) / (b - a) =
        (b - a)⁻¹ * (∫ p in vlSlab a b, (vlConvT (k - l) w p.1 p.2) ^ 2) + ε := by
      field_simp
    rw [e1, e2] at h
    exact h
  exact this

/-- A slab integral of a square of a convolution difference is bounded by the
two distances to a common limit. -/
theorem lps_slab_sq_sub_le {a b : ℝ} {f g h : Vec3 × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hh : MemLp h 2 (volume.restrict (vlSlab a b))) :
    ∫ p in vlSlab a b, (f p - g p) ^ 2 ≤
      2 * (∫ p in vlSlab a b, (f p - h p) ^ 2) +
        2 * ∫ p in vlSlab a b, (g p - h p) ^ 2 := by
  have h1 : Integrable (fun p => (f p - h p) ^ 2) (volume.restrict (vlSlab a b)) :=
    (hf.sub hh).integrable_sq
  have h2 : Integrable (fun p => (g p - h p) ^ 2) (volume.restrict (vlSlab a b)) :=
    (hg.sub hh).integrable_sq
  have h3 : Integrable (fun p => (f p - g p) ^ 2) (volume.restrict (vlSlab a b)) :=
    (hf.sub hg).integrable_sq
  calc
    ∫ p in vlSlab a b, (f p - g p) ^ 2 ≤
        ∫ p in vlSlab a b, (2 * (f p - h p) ^ 2 + 2 * (g p - h p) ^ 2) := by
      refine integral_mono h3 ((h1.const_mul 2).add (h2.const_mul 2)) fun p => ?_
      nlinarith only [sq_nonneg (f p - h p + (g p - h p))]
    _ = 2 * (∫ p in vlSlab a b, (f p - h p) ^ 2) +
        2 * ∫ p in vlSlab a b, (g p - h p) ^ 2 := by
      rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul,
        integral_const_mul]

/-- The convolution with a difference of kernels is the difference of the
convolutions on almost every time slice. -/
theorem lps_slab_conv_sub_eq {a b : ℝ} {w : Vec3 × ℝ → ℝ}
    (hwm : StronglyMeasurable w) (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    {k l : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l) :
    ∫ p in vlSlab a b, (vlConvT (k - l) w p.1 p.2) ^ 2 =
      ∫ p in vlSlab a b, (vlConvT k w p.1 p.2 - vlConvT l w p.1 p.2) ^ 2 := by
  have hκ : IsVlKernel (k - l) := hk.sub hl
  have h1 := (vlConvT_memLp hκ hwm hw)
  have h2 : MemLp (fun p : Vec3 × ℝ => vlConvT k w p.1 p.2 - vlConvT l w p.1 p.2) 2
      (volume.restrict (vlSlab a b)) :=
    (vlConvT_memLp hk hwm hw).sub (vlConvT_memLp hl hwm hw)
  rw [vlSlab_integral_sq h1, vlSlab_integral_sq h2]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
    (vlConvT_sub_kernel_ae hk hl hwm hw)] with s hs hsI
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have := hs hsI x
  simp only [this]

/-- Convergence of the pairing of two `L²`-convergent sequences. -/
theorem lps_integral_mul_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : ℕ → α → ℝ} {f g : α → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : ∀ n, MemLp (G n) 2 μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hFf : Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂μ) atTop (𝓝 0))
    (hGg : Tendsto (fun n => ∫ x, (G n x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
  have hL : ∀ (H : ℕ → α → ℝ) (h : α → ℝ) (hH : ∀ n, MemLp (H n) 2 μ)
      (hh : MemLp h 2 μ),
      Tendsto (fun n => ∫ x, (H n x - h x) ^ 2 ∂μ) atTop (𝓝 0) →
      Tendsto (fun n => (hH n).toLp (H n)) atTop (𝓝 (hh.toLp h)) := by
    intro H h hH hh hlim
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hsq : ∀ n, ‖(hH n).toLp (H n) - hh.toLp h‖ ^ 2 = ∫ x, (H n x - h x) ^ 2 ∂μ := by
      intro n
      rw [← MemLp.toLp_sub, vl_norm_toLp_sq]
      rfl
    have hroot : Tendsto (fun n => Real.sqrt (∫ x, (H n x - h x) ^ 2 ∂μ)) atTop (𝓝 0) := by
      simpa using hlim.sqrt
    refine hroot.congr (fun n => ?_)
    rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]
  have h1 := hL F f hF hf hFf
  have h2 := hL G g hG hg hGg
  have h3 := h1.inner (𝕜 := ℝ) h2
  have hin : ∀ n, ∫ x, F n x * G n x ∂μ = inner ℝ ((hF n).toLp (F n)) ((hG n).toLp (G n)) :=
    fun n => vl_integral_mul_eq_inner (hF n) (hG n)
  simp_rw [hin]
  rw [vl_integral_mul_eq_inner hf hg]
  exact h3

/-- The energy identity of a mollified curve, expressed through the dual
pair. -/
theorem lpsCurve_energy_identity (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k)
    {P Q : Vec3 × ℝ → ℝ}
    (hP : MemLp P 2 (volume.restrict (vlSlab a b)))
    (hQ : MemLp Q 2 (volume.restrict (vlSlab a b))) (c : ℝ)
    (hpair : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      ∫ x, vlConvT k w x s * vlConvT k r x s = c * ∫ x, P (x, s) * Q (x, s))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    ‖lpsCurve a b k w r t (lps_prim_memLp hab hwm hrm hw hr hweak hk ht)‖ ^ 2 -
        ‖lpsCurve a b k w r s (lps_prim_memLp hab hwm hrm hw hr hweak hk hs)‖ ^ 2 =
      2 * c * ∫ z in vlSlab s t, P z * Q z := by
  rw [lpsCurve_norm_sq hab hwm hrm hw hr hweak hk ht,
    lpsCurve_norm_sq hab hwm hrm hw hr hweak hk hs]
  obtain ⟨_, _, hid⟩ := lps_prim_energy hab hwm hrm hw hr hweak hk
  rw [hid s hs t ht hst, intervalIntegral.integral_of_le hst]
  have hslice := lps_prim_slice_ae hab hwm hrm hw hr hweak hk
  have hcongr : volume.restrict (Ioo a b) = volume.restrict (Ioc a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hsub : Ioc s t ⊆ Ioc a b := Ioc_subset_Ioc hs.1 ht.2
  have hae : ∀ᵐ q ∂(volume.restrict (Ioc s t)),
      ∫ x, lpsPrim a b k w r x q * vlConvT k r x q = c * ∫ x, P (x, q) * Q (x, q) := by
    have h1 : ∀ᵐ q ∂(volume.restrict (Ioc a b)),
        ∫ x, lpsPrim a b k w r x q * vlConvT k r x q = c * ∫ x, P (x, q) * Q (x, q) := by
      rw [← hcongr]
      filter_upwards [hslice, hpair] with q hq hp
      rw [← hp]
      refine integral_congr_ae ?_
      filter_upwards [hq] with x hx
      rw [← hx]
    exact ae_restrict_of_ae_restrict_of_subset hsub h1
  rw [setIntegral_congr_ae measurableSet_Ioc (by
    filter_upwards [ae_restrict_iff' measurableSet_Ioc |>.1 hae] with q hq hqI using hq hqI)]
  rw [integral_const_mul]
  have hPst : MemLp P 2 (volume.restrict (vlSlab s t)) :=
    hP.mono_measure (Measure.restrict_mono (prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)) le_rfl)
  have hQst : MemLp Q 2 (volume.restrict (vlSlab s t)) :=
    hQ.mono_measure (Measure.restrict_mono (prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)) le_rfl)
  have hint : Integrable (fun z : Vec3 × ℝ => P z * Q z) (volume.restrict (vlSlab s t)) :=
    hPst.integrable_mul hQst
  rw [vlSlab_integral_eq hint, integral_Ioc_eq_integral_Ioo]
  ring

end ESS.LPS

end

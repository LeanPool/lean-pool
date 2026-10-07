/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitAC
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyMollifier
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyScalar

/-!
# Mollified time primitives of a field with a square-integrable time derivative

For a slab field `w` whose weak time derivative `r` is square integrable, and a
smooth compact spatial kernel `k`, the convolution `k ⋆ w` has, at every point
of space, the weak time derivative `k ⋆ r`. It is therefore an absolutely
continuous function of time, equal almost everywhere to an explicit primitive
with an averaged constant (`prop:lps-local-strong`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

variable {a b : ℝ} {w r : Vec3 × ℝ → ℝ}

/-- The spatial convolution of a slab field with a smooth compact kernel has,
at every point of space, the convolved time derivative as weak time derivative. -/
theorem lps_conv_hasWeakDeriv
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3) :
    HasWeakDerivOn (Ioo a b) (fun s => vlConvT k w x s)
      (fun s => vlConvT k r x s) := by
  intro θ hθ
  have hθc : Continuous θ := hθ.1.continuous
  have hθ'c : Continuous (deriv θ) := hθ.1.continuous_deriv (by simp)
  have hθb := hθc.bounded_above_of_compact_support hθ.2.1
  have hθ'b := hθ'c.bounded_above_of_compact_support (hθ.2.1.deriv (𝕜 := ℝ))
  have hθb' : ∃ C, ∀ s, |θ s| ≤ C := by
    obtain ⟨C, hC⟩ := hθb
    exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩
  have hθ'b' : ∃ C, ∀ s, |deriv θ s| ≤ C := by
    obtain ⟨C, hC⟩ := hθ'b
    exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩
  have h := hweak (vlTest k x θ) (vlTest_mem hk x hθ)
  have hA := vlSlab_integral_sep hw hk x hθ'c hθ'b'
  have hB := vlSlab_integral_sep hr hk x hθc hθb'
  have hL : ∫ p in vlSlab a b, w p * CKN.timePartial (vlTest k x θ) p =
      ∫ s in Ioo a b, deriv θ s * vlConvT k w x s := by
    rw [← hA.2]
    refine setIntegral_congr_fun (measurableSet_prod.2 (Or.inl ⟨MeasurableSet.univ,
      measurableSet_Ioo⟩)) fun p _ => ?_
    rw [vlTest_timePartial x hθ.1 p]
  have hR : ∫ p in vlSlab a b, r p * vlTest k x θ p =
      ∫ s in Ioo a b, θ s * vlConvT k r x s := by
    rw [← hB.2]
    rfl
  rw [hL, hR] at h
  have e1 : ∫ s in Ioo a b, vlConvT k w x s * deriv θ s =
      ∫ s in Ioo a b, deriv θ s * vlConvT k w x s := by
    refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    exact mul_comm _ _
  have e2 : ∫ s in Ioo a b, vlConvT k r x s * θ s =
      ∫ s in Ioo a b, θ s * vlConvT k r x s := by
    refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    exact mul_comm _ _
  rw [e1, e2]
  exact h

/-- The averaged constant of the mollified time primitive. -/
@[expose] def lpsPrimConst (a b : ℝ) (k : Vec3 → ℝ) (w r : Vec3 × ℝ → ℝ) (x : Vec3) : ℝ :=
  (b - a)⁻¹ * ∫ s in Ioo a b, (vlConvT k w x s - ∫ q in a..s, vlConvT k r x q)

/-- The mollified time primitive `x, t ↦ c(x) + ∫ₐᵗ (k ⋆ r)(x, q) dq`. -/
@[expose] def lpsPrim (a b : ℝ) (k : Vec3 → ℝ) (w r : Vec3 × ℝ → ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  lpsPrimConst a b k w r x + ∫ q in a..t, vlConvT k r x q

theorem lps_conv_intervalIntegrable
    (hr : MemLp r 2 (volume.restrict (vlSlab a b))) (hab : a < b)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3) :
    IntervalIntegrable (fun s => vlConvT k r x s) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
  exact vlConvT_integrableOn hr hk x

/-- The mollified primitive is an interval integral of the convolved time
derivative. -/
theorem lps_prim_increment
    (hr : MemLp r 2 (volume.restrict (vlSlab a b))) (hab : a < b)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      lpsPrim a b k w r x t - lpsPrim a b k w r x s =
        ∫ q in s..t, vlConvT k r x q := by
  intro s hs t ht
  have hI := lps_conv_intervalIntegrable hr hab hk x
  have hsub : ∀ u ∈ Icc a b, IntervalIntegrable (fun q => vlConvT k r x q) volume a u := by
    intro u hu
    exact hI.mono_set (uIcc_subset_uIcc (by simp [hab.le])
      (by simpa [uIcc_of_le hab.le] using hu))
  simp only [lpsPrim]
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (hsub t ht) (hsub s hs)

/-- The convolution of the field is, at every point and for almost every time,
the mollified primitive. -/
theorem lps_prim_ae_eq (hab : a < b)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      vlConvT k w x t = lpsPrim a b k w r x t := by
  have hAint := vlConvT_integrableOn hw hk x
  have hBint := vlConvT_integrableOn hr hk x
  have hBI := lps_conv_intervalIntegrable hr hab hk x
  have hweakAB := lps_conv_hasWeakDeriv hw hr hweak hk x
  set t₀ : ℝ := (a + b) / 2 with ht₀def
  have ht₀ : t₀ ∈ Ioo a b := ⟨by rw [ht₀def]; linarith only [hab],
    by rw [ht₀def]; linarith only [hab]⟩
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hab ht₀
    hAint.locallyIntegrableOn hBint.locallyIntegrableOn hweakAB
  set D : ℝ := C + ∫ q in t₀..a, vlConvT k r x q with hD
  have hsub : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      IntervalIntegrable (fun q => vlConvT k r x q) volume u v := by
    intro u hu v hv
    exact hBI.mono_set (uIcc_subset_uIcc (by simpa [uIcc_of_le hab.le] using hu)
      (by simpa [uIcc_of_le hab.le] using hv))
  have hconst : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      vlConvT k w x t - ∫ q in a..t, vlConvT k r x q = D := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hC] with t ht htI
    rw [ht htI, hD, ← intervalIntegral.integral_add_adjacent_intervals
      (hsub t₀ (Ioo_subset_Icc_self ht₀) a (left_mem_Icc.2 hab.le))
      (hsub a (left_mem_Icc.2 hab.le) t (Ioo_subset_Icc_self htI))]
    ring
  have havg : lpsPrimConst a b k w r x = D := by
    have hint : ∫ s in Ioo a b, (vlConvT k w x s - ∫ q in a..s, vlConvT k r x q) =
        ∫ s in Ioo a b, D := setIntegral_congr_ae measurableSet_Ioo
      ((ae_restrict_iff' measurableSet_Ioo).1 hconst)
    rw [lpsPrimConst, hint, setIntegral_const, Real.volume_real_Ioo_of_le hab.le,
      smul_eq_mul]
    have hne : b - a ≠ 0 := (sub_pos.2 hab).ne'
    field_simp
  filter_upwards [hconst] with t ht
  rw [lpsPrim, havg]
  linarith only [ht]

/-- Measurability of the primitive in the time variable of a jointly measurable
integrand. -/
theorem lps_stronglyMeasurable_timePrimitive {B : Vec3 × ℝ → ℝ} (hB : StronglyMeasurable B)
    (a : ℝ) :
    StronglyMeasurable (fun p : Vec3 × ℝ => ∫ q in a..p.2, B (p.1, q)) := by
  have hcomp : StronglyMeasurable (fun z : (Vec3 × ℝ) × ℝ => B (z.1.1, z.2)) :=
    hB.comp_measurable (measurable_fst.fst.prodMk measurable_snd)
  have h1 : StronglyMeasurable (fun p : Vec3 × ℝ => ∫ q in Ioc a p.2, B (p.1, q)) := by
    have hset : MeasurableSet {z : (Vec3 × ℝ) × ℝ | z.2 ∈ Ioc a z.1.2} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.snd)
    have hF : StronglyMeasurable (fun z : (Vec3 × ℝ) × ℝ =>
        (Ioc a z.1.2).indicator (fun q => B (z.1.1, q)) z.2) := by
      have heq : (fun z : (Vec3 × ℝ) × ℝ =>
          (Ioc a z.1.2).indicator (fun q => B (z.1.1, q)) z.2) =
          {z : (Vec3 × ℝ) × ℝ | z.2 ∈ Ioc a z.1.2}.indicator
            (fun z : (Vec3 × ℝ) × ℝ => B (z.1.1, z.2)) := by
        funext z
        simp only [indicator, mem_ofPred_eq]
      rw [heq]
      exact hcomp.indicator hset
    have h := hF.integral_prod_right' (ν := (volume : Measure ℝ))
    convert h using 1
    funext p
    exact (integral_indicator measurableSet_Ioc).symm
  have h2 : StronglyMeasurable (fun p : Vec3 × ℝ => ∫ q in Ioc p.2 a, B (p.1, q)) := by
    have hset : MeasurableSet {z : (Vec3 × ℝ) × ℝ | z.2 ∈ Ioc z.1.2 a} :=
      (measurableSet_lt measurable_fst.snd measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    have hF : StronglyMeasurable (fun z : (Vec3 × ℝ) × ℝ =>
        (Ioc z.1.2 a).indicator (fun q => B (z.1.1, q)) z.2) := by
      have heq : (fun z : (Vec3 × ℝ) × ℝ =>
          (Ioc z.1.2 a).indicator (fun q => B (z.1.1, q)) z.2) =
          {z : (Vec3 × ℝ) × ℝ | z.2 ∈ Ioc z.1.2 a}.indicator
            (fun z : (Vec3 × ℝ) × ℝ => B (z.1.1, z.2)) := by
        funext z
        simp only [indicator, mem_ofPred_eq]
      rw [heq]
      exact hcomp.indicator hset
    have h := hF.integral_prod_right' (ν := (volume : Measure ℝ))
    convert h using 1
    funext p
    exact (integral_indicator measurableSet_Ioc).symm
  exact h1.sub h2

theorem lps_prim_stronglyMeasurable
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) :
    StronglyMeasurable (fun p : Vec3 × ℝ => lpsPrim a b k w r p.1 p.2) := by
  have hA := vlConvT_stronglyMeasurable hk.continuous hwm
  have hB := vlConvT_stronglyMeasurable hk.continuous hrm
  have hE := lps_stronglyMeasurable_timePrimitive hB a
  have hint : StronglyMeasurable (fun x : Vec3 => lpsPrimConst a b k w r x) := by
    have hF : StronglyMeasurable (fun z : Vec3 × ℝ =>
        vlConvT k w z.1 z.2 - ∫ q in a..z.2, vlConvT k r z.1 q) := hA.sub hE
    have h := hF.integral_prod_right' (ν := volume.restrict (Ioo a b))
    exact h.const_mul (b - a)⁻¹
  exact (hint.comp_measurable measurable_fst).add hE

/-- A square-integrable slab field is square integrable for the product of
the spatial measure with the restriction to `(a, b]`. -/
theorem lps_slab_integrable_sq {g : Vec3 × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (vlSlab a b))) :
    Integrable (fun p : Vec3 × ℝ => g p ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) := by
  have h := hg.integrable_sq
  rw [vlSlab_measure] at h
  have hcongr : volume.restrict (Ioo a b) = volume.restrict (Ioc a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rwa [hcongr] at h

/-- For almost every time, the convolution of the time slice is the mollified
primitive almost everywhere in space. -/
theorem lps_prim_slice_ae (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      vlConvT k w x t = lpsPrim a b k w r x t := by
  have hmeas : MeasurableSet {p : Vec3 × ℝ |
      vlConvT k w p.1 p.2 = lpsPrim a b k w r p.1 p.2} :=
    measurableSet_eq_fun (vlConvT_stronglyMeasurable hk.continuous hwm).measurable
      (lps_prim_stronglyMeasurable hwm hrm hk).measurable
  have hx : ∀ᵐ x ∂(volume : Measure Vec3), ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      vlConvT k w x t = lpsPrim a b k w r x t :=
    Eventually.of_forall fun x => lps_prim_ae_eq hab hw hr hweak hk x
  exact (Measure.ae_ae_comm hmeas).1 hx

/-- Square integrability of the mollified primitive at every time and on the
slab, and its energy identity in time (`prop:lps-local-strong`). -/
theorem lps_prim_energy (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    {k : Vec3 → ℝ} (hk : IsVlKernel k) :
    (∀ t ∈ Icc a b, Integrable (fun x => lpsPrim a b k w r x t ^ 2) volume) ∧
    Integrable (fun p : Vec3 × ℝ => lpsPrim a b k w r p.1 p.2 ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) ∧
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      (∫ x, lpsPrim a b k w r x t ^ 2) - ∫ x, lpsPrim a b k w r x s ^ 2 =
        2 * ∫ q in s..t, ∫ x, lpsPrim a b k w r x q * vlConvT k r x q := by
  have hAm := vlConvT_stronglyMeasurable hk.continuous hwm
  have hBm := vlConvT_stronglyMeasurable hk.continuous hrm
  have hAL2 := vlConvT_memLp hk hwm hw
  have hBL2 := vlConvT_memLp hk hrm hr
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ∀ᵐ x ∂(volume : Measure Vec3),
        vlConvT k w x t = lpsPrim a b k w r x t :=
    lps_prim_slice_ae (a := a) (b := b) (w := w) (r := r)
      hab hwm hrm hw hr hweak (k := k) hk
  have hsliceL2 : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      MemLp (fun x => vlConvT k w x t) 2 volume :=
    vlSlab_slice_memLp (a := a) (τ := b)
      (g := fun p : Vec3 × ℝ => vlConvT k w p.1 p.2) hAm hAL2
  have hgood : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      (∀ᵐ x ∂(volume : Measure Vec3), vlConvT k w x t = lpsPrim a b k w r x t) ∧
      MemLp (fun x => vlConvT k w x t) 2 volume :=
    hslice.and hsliceL2
  have : NeBot (ae (volume.restrict (Ioo a b))) :=
    ae_restrict_neBot.2 (by simp [Real.volume_Ioo, hab])
  obtain ⟨s₀, ⟨hs₀ae, hs₀L2⟩, hs₀mem⟩ :=
    (hgood.and (ae_restrict_mem measurableSet_Ioo)).exists
  have hfc : Integrable (fun x => lpsPrim a b k w r x s₀ ^ 2) volume := by
    refine hs₀L2.integrable_sq.congr ?_
    filter_upwards [hs₀ae] with x hx
    rw [hx]
  have hsq := lps_ac_family_sq_integrable (μ := (volume : Measure Vec3)) hab.le
    (c := s₀) ⟨hs₀mem.1.le, hs₀mem.2.le⟩
    (f := fun x t => lpsPrim a b k w r x t) (g := fun x t => vlConvT k r x t)
    (lps_prim_stronglyMeasurable hwm hrm hk).measurable
    (fun x => lps_conv_intervalIntegrable hr hab hk x)
    (fun x => lps_prim_increment hr hab hk x)
    (lps_slab_integrable_sq hBL2) hfc
  refine ⟨hsq.1, hsq.2, ?_⟩
  exact lps_ac_family_energy_identity (μ := (volume : Measure Vec3)) hab.le
    (f := fun x t => lpsPrim a b k w r x t) (g := fun x t => vlConvT k r x t)
    (lps_prim_stronglyMeasurable hwm hrm hk).measurable hBm.measurable
    (fun x => lps_conv_intervalIntegrable hr hab hk x)
    (fun x => lps_prim_increment hr hab hk x) hsq.2
    (lps_slab_integrable_sq hBL2) hsq.1

/-- The mollified primitive is linear in the kernel. -/
theorem lps_prim_sub_kernel (hab : a < b)
    (hwm : StronglyMeasurable w) (hrm : StronglyMeasurable r)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    {k l : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l) (x : Vec3)
    {t : ℝ} (ht : t ∈ Icc a b) :
    lpsPrim a b (k - l) w r x t =
      lpsPrim a b k w r x t - lpsPrim a b l w r x t := by
  have hBae := vlConvT_sub_kernel_ae hk hl hrm hr
  have hAae := vlConvT_sub_kernel_ae hk hl hwm hw
  rw [ae_restrict_iff' measurableSet_Ioo] at hBae hAae
  have hBI := lps_conv_intervalIntegrable hr hab hk x
  have hBI' := lps_conv_intervalIntegrable hr hab hl x
  have hint : ∀ u ∈ Icc a b,
      ∫ q in a..u, vlConvT (k - l) r x q =
        (∫ q in a..u, vlConvT k r x q) - ∫ q in a..u, vlConvT l r x q := by
    intro u hu
    have hcongr : ∫ q in a..u, vlConvT (k - l) r x q =
        ∫ q in a..u, (vlConvT k r x q - vlConvT l r x q) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hBae, Measure.ae_ne volume b] with q hq hqb hqI
      rw [uIoc_of_le hu.1] at hqI
      exact hq ⟨hqI.1.trans_le' (le_refl a), lt_of_le_of_ne (hqI.2.trans hu.2) hqb⟩ x
    rw [hcongr]
    have hsub : ∀ m : Vec3 → ℝ, IsVlKernel m → IntervalIntegrable
        (fun q => vlConvT m r x q) volume a u := by
      intro m hm
      exact (lps_conv_intervalIntegrable hr hab hm x).mono_set
        (uIcc_subset_uIcc (by simp [hab.le]) (by simpa [uIcc_of_le hab.le] using hu))
    exact intervalIntegral.integral_sub (hsub k hk) (hsub l hl)
  have hEint : ∀ m : Vec3 → ℝ, IsVlKernel m →
      IntegrableOn (fun s => ∫ q in a..s, vlConvT m r x q) (Ioo a b) volume := by
    intro m hm
    have hI := lps_conv_intervalIntegrable hr hab hm x
    have hc := intervalIntegral.continuousOn_primitive_interval' (a := a) hI
      (by simp [hab.le])
    rw [uIcc_of_le hab.le] at hc
    exact (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hconst : lpsPrimConst a b (k - l) w r x =
      lpsPrimConst a b k w r x - lpsPrimConst a b l w r x := by
    unfold lpsPrimConst
    rw [← mul_sub]
    congr 1
    have hk' : IntegrableOn (fun s => vlConvT k w x s - ∫ q in a..s, vlConvT k r x q)
        (Ioo a b) volume := (vlConvT_integrableOn hw hk x).sub (hEint k hk)
    have hl' : IntegrableOn (fun s => vlConvT l w x s - ∫ q in a..s, vlConvT l r x q)
        (Ioo a b) volume := (vlConvT_integrableOn hw hl x).sub (hEint l hl)
    rw [← integral_sub hk' hl']
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hAae] with s hs hsI
    rw [hs hsI x, hint s (Ioo_subset_Icc_self hsI)]
    ring
  unfold lpsPrim
  rw [hconst, hint t ht]
  ring

end ESS.LPS

end

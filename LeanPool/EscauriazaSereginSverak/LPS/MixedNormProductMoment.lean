/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormProducts
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Products in finite mixed norms

Spatial Hölder followed by time Hölder puts products of two mixed-norm
fields in the mixed space with the reciprocal-sum exponents.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_ofReal_holder_triple {p q r : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hrecip : p⁻¹ + q⁻¹ = r⁻¹) :
    ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_inv_of_pos hr,
    ← ENNReal.ofReal_add (by positivity) (by positivity), hrecip]

/-- A spacetime `L²` scalar field has a finite `L²_t L²_x` moment on the
finite time slab. -/
theorem lps_mixed_two_moment_of_memLp_two
    {T : ℝ} {f : ParabolicPoint → ℝ}
    (hf : MemLp f 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,t)) 2 volume) ∧
    (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f (x,t)) 2 volume ^ (2 : ℝ)) < ⊤ := by
  have hslice := serrin_slice_memLp_ae (T := T) (q := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hf
  have hQfinite : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖f z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := hf.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hf.aestronglyMeasurable] at h
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num] at h
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  have hfν : AEStronglyMeasurable f ν := by
    change AEStronglyMeasurable f
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hf.aestronglyMeasurable
  have hpower : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ (2 : ℝ)) ν :=
    hfν.enorm.pow_const _
  have hsliceFormula : (fun t : ℝ => eLpNorm (fun x : Vec3 => f (x,t)) 2 volume ^
      (2 : ℝ)) =ᵐ[μt] fun t =>
      ∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ (2 : ℝ) ∂volume := by
    filter_upwards [hslice] with t ht
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      ht.aestronglyMeasurable]
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hEq : (∫⁻ t : ℝ, eLpNorm (fun x : Vec3 => f (x,t)) 2 volume ^
      (2 : ℝ) ∂μt) =
      ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), ‖f z‖ₑ ^ (2 : ℝ) := by
    calc
      _ = ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ (2 : ℝ) ∂volume ∂μt :=
        lintegral_congr_ae hsliceFormula
      _ = ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ‖f z‖ₑ ^ (2 : ℝ) := by
        rw [serrin_slab_measure_eq T]
        rw [← lintegral_prod_symm _ hpower]
        rfl
  refine ⟨hslice, ?_⟩
  rw [hEq]
  exact hQfinite

/-- A vector-valued mixed moment controls the corresponding mixed moments of
all coordinate functions. -/
theorem lps_vector_component_mixed_moment
    {T p q : ℝ} {F : ParabolicPoint → Vec3}
    (hp : 0 ≤ p)
    (hSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => F (x,t)) (ENNReal.ofReal q) volume)
    (hMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => F (x,t)) (ENNReal.ofReal q) volume ^ p) < ⊤) :
    ∀ i : Fin 3,
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        MemLp (fun x : Vec3 => F (x,t) i) (ENNReal.ofReal q) volume) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => F (x,t) i) (ENNReal.ofReal q) volume ^ p) < ⊤ := by
  intro i
  constructor
  · filter_upwards [hSlice] with t ht
    exact ht.eval i
  · have hdom : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        eLpNorm (fun x : Vec3 => F (x,t) i) (ENNReal.ofReal q) volume ^ p ≤
          eLpNorm (fun x : Vec3 => F (x,t)) (ENNReal.ofReal q) volume ^ p := by
      filter_upwards [hSlice] with t ht
      have hcoord := eLpNorm_mono_ae (p := ENNReal.ofReal q)
        (ht.eval i).aestronglyMeasurable
        (Eventually.of_forall fun x => norm_le_pi_norm (F (x,t)) i)
      exact ENNReal.rpow_le_rpow hcoord hp
    exact lt_of_le_of_lt (lintegral_mono_ae hdom) hMoment

/-- A raw vector-valued mixed moment is the corresponding moment of the
spatial `eLpNorm` on almost every slice. -/
theorem lps_vector_mixed_moment_of_raw
    {T p q : ℝ} {F : ParabolicPoint → Vec3}
    (hq : 0 < q)
    (hSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => F (x,t)) (ENNReal.ofReal q) volume)
    (hRaw : (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3, ‖F (x,t)‖ₑ ^ q ∂volume) ^ (p / q)) < ⊤) :
    (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => F (x,t)) (ENNReal.ofReal q) volume ^ p) < ⊤ := by
  have hFormula : (fun t : ℝ =>
      eLpNorm (fun x : Vec3 => F (x,t)) (ENNReal.ofReal q) volume ^ p) =ᵐ[
        volume.restrict (Ioo 0 T)] (fun t =>
      (∫⁻ x : Vec3, ‖F (x,t)‖ₑ ^ q ∂volume) ^ (p / q)) := by
    filter_upwards [hSlice] with t ht
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top ht.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq.le]
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [ne_of_gt hq]
  rw [lintegral_congr_ae hFormula]
  exact hRaw

/-- A finite raw mixed moment gives almost every vector slice membership in
the corresponding spatial `L^q` space. -/
theorem lps_vector_mixed_slice_memLp_of_raw
    {T p q : ℝ} {F : ParabolicPoint → Vec3}
    (hp : 0 < p) (hq : 0 < q)
    (hF : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hRaw : (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3, ‖F (x, t)‖ₑ ^ q ∂volume) ^ (p / q)) < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => F (x,t)) (ENNReal.ofReal q) volume := by
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  let R : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : Vec3, ‖F (x,t)‖ₑ ^ q ∂volume
  have hFν : AEStronglyMeasurable F ν := by
    change AEStronglyMeasurable F
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hF
  have hRmeas : AEMeasurable R μt := (hFν.enorm.pow_const q).lintegral_prod_left'
  have hRmoment : (∫⁻ t : ℝ, R t ^ (p / q) ∂μt) < ⊤ := by
    simpa [R, μt] using hRaw
  have hpq : 0 < p / q := div_pos hp hq
  have hpowAE : ∀ᵐ t ∂μt, R t ^ (p / q) < ⊤ :=
    ae_lt_top' (hRmeas.pow_const (p / q)) hRmoment.ne
  have hRAE : ∀ᵐ t ∂μt, R t < ⊤ := by
    filter_upwards [hpowAE] with t ht
    exact (ENNReal.rpow_lt_top_iff_of_pos hpq).mp ht
  have hFsliceMeas : ∀ᵐ t ∂μt,
      AEStronglyMeasurable (fun x : Vec3 => F (x,t)) volume := by
    rw [serrin_slab_measure_eq T] at hF
    exact hF.prodMk_right
  filter_upwards [hRAE, hFsliceMeas] with t ht hFm
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hFm,
    show (ENNReal.ofReal q).toReal = q from ENNReal.toReal_ofReal hq.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ht.ne

/-- Two finite mixed norms multiply into the mixed norm whose spatial and
time reciprocal exponents are the corresponding sums. -/
theorem lps_mixed_product_moment
    {T px qx rx pt qt rt : ℝ}
    (hpx : 1 ≤ px) (hqx : 1 ≤ qx) (hrx : 1 ≤ rx)
    (hpt : 1 ≤ pt) (hqt : 1 ≤ qt) (hrt : 1 ≤ rt)
    (hSpace : px⁻¹ + qx⁻¹ = rx⁻¹)
    (hTime : pt⁻¹ + qt⁻¹ = rt⁻¹)
    {f g : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hfSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume)
    (hgSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume)
    (hfMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume ^ pt) < ⊤)
    (hgMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume ^ qt) < ⊤) :
    (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,t) * g (x,t)) (ENNReal.ofReal rx) volume) ∧
    (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f (x,t) * g (x,t)) (ENNReal.ofReal rx) volume ^ rt) < ⊤ := by
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  let NF : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume
  let NG : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume
  let NP : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun x : Vec3 => f (x,t) * g (x,t)) (ENNReal.ofReal rx) volume
  have hpx0 : 0 < px := lt_of_lt_of_le (by norm_num) hpx
  have hqx0 : 0 < qx := lt_of_lt_of_le (by norm_num) hqx
  have hrx0 : 0 < rx := lt_of_lt_of_le (by norm_num) hrx
  have hpt0 : 0 < pt := lt_of_lt_of_le (by norm_num) hpt
  have hqt0 : 0 < qt := lt_of_lt_of_le (by norm_num) hqt
  have hrt0 : 0 < rt := lt_of_lt_of_le (by norm_num) hrt
  have hfν : AEStronglyMeasurable f ν := by
    change AEStronglyMeasurable f
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hf
  have hgν : AEStronglyMeasurable g ν := by
    change AEStronglyMeasurable g
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hg
  have hNf : AEMeasurable NF μt := by
    have hpw : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ px) ν :=
      hfν.enorm.pow_const _
    have hsl := hpw.lintegral_prod_left'
    have hformula : NF =ᵐ[μt] fun t =>
        (∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ px ∂volume) ^ (1 / px) := by
      filter_upwards [hfSlice] with t hft
      exact lps_mixed_eLpNorm_formula hpx0 hft.aestronglyMeasurable
    exact (hsl.pow_const (1 / px)).congr hformula.symm
  have hNg : AEMeasurable NG μt := by
    have hpg : AEMeasurable (fun z : Vec3 × ℝ => ‖g z‖ₑ ^ qx) ν :=
      hgν.enorm.pow_const _
    have hsl := hpg.lintegral_prod_left'
    have hformula : NG =ᵐ[μt] fun t =>
        (∫⁻ x : Vec3, ‖g (x,t)‖ₑ ^ qx ∂volume) ^ (1 / qx) := by
      filter_upwards [hgSlice] with t hgt
      exact lps_mixed_eLpNorm_formula hqx0 hgt.aestronglyMeasurable
    exact (hsl.pow_const (1 / qx)).congr hformula.symm
  have hPmeas : AEMeasurable NP μt := by
    have hprod : AEStronglyMeasurable (fun z : Vec3 × ℝ => f z * g z) ν := hfν.mul hgν
    have hpow : AEMeasurable (fun z : Vec3 × ℝ => ‖f z * g z‖ₑ ^ rx) ν :=
      hprod.enorm.pow_const _
    have hsl := hpow.lintegral_prod_left'
    have hformula : NP =ᵐ[μt] fun t =>
        (∫⁻ x : Vec3, ‖f (x,t) * g (x,t)‖ₑ ^ rx ∂volume) ^ (1 / rx) := by
      filter_upwards [hfSlice, hgSlice] with t hft hgt
      exact lps_mixed_eLpNorm_formula hrx0 (hft.aestronglyMeasurable.mul hgt.aestronglyMeasurable)
    exact (hsl.pow_const (1 / rx)).congr hformula.symm
  have hPmem : ∀ᵐ t ∂μt,
      MemLp (fun x : Vec3 => f (x,t) * g (x,t)) (ENNReal.ofReal rx) volume := by
    filter_upwards [hfSlice, hgSlice] with t hft hgt
    have htriple := lps_ofReal_holder_triple hpx0 hqx0 hrx0 hSpace
    exact hft.mul hgt
  have hSpaceBound : ∀ᵐ t ∂μt, NP t ≤ NF t * NG t := by
    filter_upwards [hfSlice, hgSlice] with t hft hgt
    have htriple := lps_ofReal_holder_triple hpx0 hqx0 hrx0 hSpace
    exact eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal px)
      (q := ENNReal.ofReal qx) (r := ENNReal.ofReal rx)
      hft.aestronglyMeasurable hgt.aestronglyMeasurable
  have hTimeHolder : (pt / rt).HolderConjugate (qt / rt) := by
    have hsum : (pt / rt)⁻¹ + (qt / rt)⁻¹ = 1 := by
      field_simp [ne_of_gt hpt0, ne_of_gt hqt0, ne_of_gt hrt0] at hTime ⊢
      nlinarith only [hTime]
    exact ⟨by simpa using hsum, div_pos hpt0 hrt0, div_pos hqt0 hrt0⟩
  have hTimeProdRaw :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μt hTimeHolder
      (hNf.pow_const rt) (hNg.pow_const rt)
  have hinvF : 1 / (pt / rt) = rt / pt := by
    field_simp [ne_of_gt hpt0, ne_of_gt hrt0]
  have hinvG : 1 / (qt / rt) = rt / qt := by
    field_simp [ne_of_gt hqt0, ne_of_gt hrt0]
  have hTimeProd : (∫⁻ t : ℝ, NF t ^ rt * NG t ^ rt ∂μt) ≤
      (∫⁻ t : ℝ, (NF t ^ rt) ^ (pt / rt) ∂μt) ^ (rt / pt) *
      (∫⁻ t : ℝ, (NG t ^ rt) ^ (qt / rt) ∂μt) ^ (rt / qt) := by
    simpa only [hinvF, hinvG, Pi.mul_apply] using hTimeProdRaw
  have hFfin : (∫⁻ t : ℝ, NF t ^ pt ∂μt) < ⊤ := by
    simpa [NF, μt] using hfMoment
  have hGfin : (∫⁻ t : ℝ, NG t ^ qt ∂μt) < ⊤ := by
    simpa [NG, μt] using hgMoment
  have hPointF (t : ℝ) : (NF t ^ rt) ^ (pt / rt) = NF t ^ pt := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [ne_of_gt hrt0]
  have hPointG (t : ℝ) : (NG t ^ rt) ^ (qt / rt) = NG t ^ qt := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [ne_of_gt hrt0]
  have hProdLin : (∫⁻ t : ℝ, NP t ^ rt ∂μt) ≤
      ∫⁻ t : ℝ, NF t ^ rt * NG t ^ rt ∂μt := by
    apply lintegral_mono_ae
    filter_upwards [hSpaceBound] with t ht
    calc
      NP t ^ rt ≤ (NF t * NG t) ^ rt := ENNReal.rpow_le_rpow ht (by positivity)
      _ = NF t ^ rt * NG t ^ rt := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
  have hProdFin : (∫⁻ t : ℝ, NP t ^ rt ∂μt) < ⊤ := by
    calc
      (∫⁻ t : ℝ, NP t ^ rt ∂μt) ≤
          ∫⁻ t : ℝ, NF t ^ rt * NG t ^ rt ∂μt := hProdLin
      _ ≤ (∫⁻ t : ℝ, (NF t ^ rt) ^ (pt / rt) ∂μt) ^ (rt / pt) *
          (∫⁻ t : ℝ, (NG t ^ rt) ^ (qt / rt) ∂μt) ^ (rt / qt) := hTimeProd
      _ < ⊤ := by
        rw [show (fun t : ℝ => (NF t ^ rt) ^ (pt / rt)) = fun t => NF t ^ pt from
          funext hPointF, show (fun t : ℝ => (NG t ^ rt) ^ (qt / rt)) = fun t => NG t ^ qt from
          funext hPointG]
        exact ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by positivity) hFfin.ne)
          (ENNReal.rpow_lt_top_of_nonneg (by positivity) hGfin.ne)
  refine ⟨hPmem, ?_⟩
  simpa [NP, μt] using hProdFin

end ESS

end

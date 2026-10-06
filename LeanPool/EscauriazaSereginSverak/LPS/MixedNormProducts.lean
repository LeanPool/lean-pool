/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Products in mixed Lebesgue spaces

Spatial and temporal Hölder inequalities show that conjugate mixed norms
control the space-time integral of a product.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `Lq` norm of a scalar function through the lower integral of its `q`-th power. -/
theorem lps_mixed_eLpNorm_formula
    {f : Vec3 → ℝ} {q : ℝ} (hq : 0 < q)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f (ENNReal.ofReal q) volume =
      (∫⁻ x, ‖f x‖ₑ ^ q ∂volume) ^ (1 / q) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le]

/-- A finite mixed-norm moment gives almost-everywhere finite spatial slices. -/
theorem lps_mixed_slice_memLp_ae
    {T p q : ℝ} {f : ParabolicPoint → ℝ}
    (hp : 0 < p) (hq : 0 < q)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume ^ p) < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume := by
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  let N : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal q) volume
  have hfProd : AEStronglyMeasurable f ν := by
    change AEStronglyMeasurable f
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hf
  have hFpower : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ q) ν :=
    hfProd.enorm.pow_const _
  have hFsliceIntegral : AEMeasurable
      (fun t : ℝ => ∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ q ∂volume) μt :=
    hFpower.lintegral_prod_left'
  have hSliceMeas : ∀ᵐ t ∂μt,
      AEStronglyMeasurable (fun x : Vec3 => f (x,t)) volume := by
    have h := hf
    rw [serrin_slab_measure_eq T] at h
    exact h.prodMk_right
  have hNformula : N =ᵐ[μt] fun t =>
      (∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ q ∂volume) ^ (1 / q) := by
    filter_upwards [hSliceMeas] with t ht
    exact lps_mixed_eLpNorm_formula hq ht
  have hNmeas : AEMeasurable N μt :=
    (hFsliceIntegral.pow_const (1 / q)).congr hNformula.symm
  have hNpowFinite : (∫⁻ t : ℝ, N t ^ p ∂μt) < ⊤ := by
    simpa [N, μt] using hMoment
  have hNpowFiniteAE : ∀ᵐ t ∂μt, N t ^ p < ⊤ :=
    ae_lt_top' (hNmeas.pow_const p) hNpowFinite.ne
  have hNfinite : ∀ᵐ t ∂μt, N t < ⊤ := by
    filter_upwards [hNpowFiniteAE] with t ht
    exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp ht
  filter_upwards [hSliceMeas, hNfinite] with t htₘ ht
  rw [memLp_iff]
  simpa [N] using ht

/-- Conjugate finite mixed norms make a product integrable on the space-time
slab, with its integral controlled by the product of the time mixed norms. -/
theorem lps_mixed_product_integrable
    {T px qx pt qt : ℝ}
    (hpx : 0 < px) (hqx : 0 < qx)
    (hpt : 0 < pt) (hqt : 0 < qt)
    (hSpace : px.HolderConjugate qx)
    (hTime : pt.HolderConjugate qt)
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
    Integrable (fun z : ParabolicPoint => f z * g z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖f z * g z‖ₑ) ≤
      (∫⁻ t : ℝ, eLpNorm (fun x : Vec3 => f (x,t))
        (ENNReal.ofReal px) volume ^ pt ∂(volume.restrict (Ioo 0 T))) ^ (1 / pt) *
      (∫⁻ t : ℝ, eLpNorm (fun x : Vec3 => g (x,t))
        (ENNReal.ofReal qx) volume ^ qt ∂(volume.restrict (Ioo 0 T))) ^ (1 / qt) := by
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  let NF : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume
  let NG : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume
  have hfProd : AEStronglyMeasurable f ν := by
    change AEStronglyMeasurable f
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hf
  have hgProd : AEStronglyMeasurable g ν := by
    change AEStronglyMeasurable g
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hg
  have hFpower : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ px) ν :=
    hfProd.enorm.pow_const _
  have hGpower : AEMeasurable (fun z : Vec3 × ℝ => ‖g z‖ₑ ^ qx) ν :=
    hgProd.enorm.pow_const _
  have hFsliceIntegral : AEMeasurable
      (fun t : ℝ => ∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ px ∂volume) μt :=
    hFpower.lintegral_prod_left'
  have hGsliceIntegral : AEMeasurable
      (fun t : ℝ => ∫⁻ x : Vec3, ‖g (x,t)‖ₑ ^ qx ∂volume) μt :=
    hGpower.lintegral_prod_left'
  have hNFformula : NF =ᵐ[μt] fun t =>
      (∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ px ∂volume) ^ (1 / px) := by
    filter_upwards [hfSlice] with t ht
    exact lps_mixed_eLpNorm_formula hpx ht.aestronglyMeasurable
  have hNGformula : NG =ᵐ[μt] fun t =>
      (∫⁻ x : Vec3, ‖g (x,t)‖ₑ ^ qx ∂volume) ^ (1 / qx) := by
    filter_upwards [hgSlice] with t ht
    exact lps_mixed_eLpNorm_formula hqx ht.aestronglyMeasurable
  have hNFmeas : AEMeasurable NF μt :=
    (hFsliceIntegral.pow_const (1 / px)).congr hNFformula.symm
  have hNGmeas : AEMeasurable NG μt :=
    (hGsliceIntegral.pow_const (1 / qx)).congr hNGformula.symm
  have hSpaceHolder (t : ℝ)
      (hft : MemLp (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume)
      (hgt : MemLp (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume) :
      (∫⁻ x : Vec3, ‖f (x,t) * g (x,t)‖ₑ ∂volume) ≤ NF t * NG t := by
    have hfFormula := lps_mixed_eLpNorm_formula hpx hft.aestronglyMeasurable
    have hgFormula := lps_mixed_eLpNorm_formula hqx hgt.aestronglyMeasurable
    calc
      _ = ∫⁻ x : Vec3, ‖f (x,t)‖ₑ * ‖g (x,t)‖ₑ ∂volume := by
        apply lintegral_congr
        intro x
        rw [enorm_mul]
      _ ≤ (∫⁻ x : Vec3, ‖f (x,t)‖ₑ ^ px ∂volume) ^ (1 / px) *
          (∫⁻ x : Vec3, ‖g (x,t)‖ₑ ^ qx ∂volume) ^ (1 / qx) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume hSpace
          (hft.aestronglyMeasurable.enorm)
          (hgt.aestronglyMeasurable.enorm)
      _ = NF t * NG t := by rw [← hfFormula, ← hgFormula]
  have hSpaceAE : ∀ᵐ t ∂μt,
      (∫⁻ x : Vec3, ‖f (x,t) * g (x,t)‖ₑ ∂volume) ≤ NF t * NG t := by
    filter_upwards [hfSlice, hgSlice] with t hft hgt
    exact hSpaceHolder t hft hgt
  have hTimeHolder :
      (∫⁻ t : ℝ, NF t * NG t ∂μt) ≤
        (∫⁻ t : ℝ, NF t ^ pt ∂μt) ^ (1 / pt) *
          (∫⁻ t : ℝ, NG t ^ qt ∂μt) ^ (1 / qt) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μt hTime hNFmeas hNGmeas
  have hMomentF : (∫⁻ t : ℝ, NF t ^ pt ∂μt) < ⊤ := by
    simpa [NF, μt] using hfMoment
  have hMomentG : (∫⁻ t : ℝ, NG t ^ qt ∂μt) < ⊤ := by
    simpa [NG, μt] using hgMoment
  have hTimeFinite : (∫⁻ t : ℝ, NF t * NG t ∂μt) < ⊤ := by
    apply lt_of_le_of_lt hTimeHolder
    apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hMomentF.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hMomentG.ne
  have hProdMeas : AEStronglyMeasurable (fun z : ParabolicPoint => f z * g z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    hf.mul hg
  have hProdMeasProd : AEStronglyMeasurable (fun z : Vec3 × ℝ => f z * g z) ν := by
    change AEStronglyMeasurable (fun z : ParabolicPoint => f z * g z)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)))
    rw [← serrin_slab_measure_eq T]
    exact hProdMeas
  have hProdEnorm : AEMeasurable (fun z : Vec3 × ℝ => ‖f z * g z‖ₑ) ν :=
    hProdMeasProd.enorm
  have hTonelli :
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖f z * g z‖ₑ) =
        ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖f (x,t) * g (x,t)‖ₑ ∂volume ∂μt := by
    rw [serrin_slab_measure_eq T]
    rw [← lintegral_prod_symm _ hProdEnorm]
    rfl
  have hProductEstimate :
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖f z * g z‖ₑ) ≤
        (∫⁻ t : ℝ, NF t ^ pt ∂μt) ^ (1 / pt) *
          (∫⁻ t : ℝ, NG t ^ qt ∂μt) ^ (1 / qt) := by
    calc
      _ = ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖f (x,t) * g (x,t)‖ₑ ∂volume ∂μt := hTonelli
      _ ≤ ∫⁻ t : ℝ, NF t * NG t ∂μt := lintegral_mono_ae hSpaceAE
      _ ≤ _ := hTimeHolder
  have hProductBoundFinite :
      (∫⁻ t : ℝ, NF t ^ pt ∂μt) ^ (1 / pt) *
        (∫⁻ t : ℝ, NG t ^ qt ∂μt) ^ (1 / qt) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hMomentF.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hMomentG.ne
  have hProdFinite :
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖f z * g z‖ₑ) < ⊤ := by
    exact lt_of_le_of_lt hProductEstimate hProductBoundFinite
  have hMem : MemLp (fun z : ParabolicPoint => f z * g z) 1
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hProdMeas]
    exact hProdFinite
  refine ⟨memLp_one_iff_integrable.mp hMem, ?_⟩
  simpa [NF, NG, μt] using hProductEstimate

end ESS

end

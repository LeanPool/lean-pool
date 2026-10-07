/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergySlice

/-!
# Weights and integrability for the local energy inequality

For a smooth compactly supported space-time weight `ψ`, the spatial first and
second partial derivatives and the time derivative of `ψ` are derivatives of
`ψ` on the product space, hence continuous, compactly supported and vanishing
off the support of `ψ`. The force pressure, which lies in `L²_t L⁶_x`, times
such a weight is square integrable on every slab. These are the integrability
inputs of `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

section Weights

variable {ψ : Vec3 × ℝ → ℝ}

theorem contDiff_fderiv_apply_prod (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : Vec3 × ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => fderiv ℝ ψ z v :=
  (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem spatialPartial_eq_fderiv_prod (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 3)
    (z : Vec3 × ℝ) : CKN.spatialPartial ψ i z = fderiv ℝ ψ z (CKN.basisVec i, 0) :=
  fderiv_scalar_slice hψ z.1 z.2 (CKN.basisVec i)

theorem spatialSecondPartial_eq_fderiv_prod (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 3)
    (z : Vec3 × ℝ) : CKN.spatialSecondPartial ψ i i z =
      fderiv ℝ (fun w => fderiv ℝ ψ w (CKN.basisVec i, 0)) z (CKN.basisVec i, 0) := by
  have h : (fun w : ParabolicPoint => CKN.spatialPartial ψ i w) =
      fun w => fderiv ℝ ψ w (CKN.basisVec i, 0) :=
    funext fun w => spatialPartial_eq_fderiv_prod hψ i w
  unfold CKN.spatialSecondPartial
  rw [h]
  exact spatialPartial_eq_fderiv_prod (contDiff_fderiv_apply_prod hψ _) i z

/-- The spatial Laplacian of a time slice of a smooth weight as a derivative
on the product space. -/
theorem spatialLaplacian_slice_eq (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : Vec3 × ℝ) :
    CKN.spatialLaplacian (fun y => ψ (y, z.2)) z.1 =
      ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ ψ w (CKN.basisVec i, 0)) z (CKN.basisVec i, 0) := by
  exact Finset.sum_congr rfl fun i _ => spatialSecondPartial_eq_fderiv_prod hψ i z

theorem continuous_fderiv_apply_prod (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : Vec3 × ℝ) :
    Continuous fun z => fderiv ℝ ψ z v :=
  (contDiff_fderiv_apply_prod hψ v).continuous

theorem continuous_laplacian_prod (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ ψ w (CKN.basisVec i, 0)) z (CKN.basisVec i, 0) :=
  continuous_finsetSum _ fun i _ =>
    continuous_fderiv_apply_prod (contDiff_fderiv_apply_prod hψ (CKN.basisVec i, 0))
      (CKN.basisVec i, 0)

theorem hasCompactSupport_laplacian_prod (hψc : HasCompactSupport ψ) :
    HasCompactSupport fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ ψ w (CKN.basisVec i, 0)) z (CKN.basisVec i, 0) := by
  simp only [Fin.sum_univ_three]
  have h : ∀ i : Fin 3, HasCompactSupport fun z : Vec3 × ℝ =>
      fderiv ℝ (fun w => fderiv ℝ ψ w (CKN.basisVec i, 0)) z (CKN.basisVec i, 0) := fun i =>
    (hψc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _
  exact ((h 0).add (h 1)).add (h 2)

/-- A continuous compactly supported function is bounded. -/
theorem exists_abs_le_of_compact {g : Vec3 × ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : ∃ M : ℝ, ∀ z, |g z| ≤ M := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  exact ⟨M, fun z => by rw [← Real.norm_eq_abs]; exact hM z⟩

/-- Off the support of the weight, its time derivative and its spatial first
and second derivatives vanish. -/
theorem weights_eq_zero_of_notMem_tsupport (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) :
    ψ z = 0 ∧ CKN.timePartial ψ z = 0 ∧ (∀ i : Fin 3, CKN.spatialPartial ψ i z = 0) ∧
      ∀ i : Fin 3, CKN.spatialSecondPartial ψ i i z = 0 := by
  have hd := fderiv_eq_zero_of_notMem_tsupport_scalar hz
  refine ⟨image_eq_zero_of_notMem_tsupport hz, ?_, fun i => ?_, fun i => ?_⟩
  · rw [timePartial_eq_fderiv hψ, hd]
    rfl
  · rw [spatialPartial_eq_fderiv_prod hψ, hd]
    rfl
  · rw [spatialSecondPartial_eq_fderiv_prod hψ]
    have hz' : z ∉ tsupport fun w => fderiv ℝ ψ w (CKN.basisVec i, 0) :=
      fun h => hz (tsupport_fderiv_apply_subset ℝ _ h)
    rw [fderiv_eq_zero_of_notMem_tsupport_scalar hz']
    rfl

end Weights

/-- A product of two square-integrable functions and an essentially bounded
measurable weight is integrable. -/
theorem integrable_mul_mul_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b c : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hc : AEStronglyMeasurable c μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, |c x| ≤ M) : Integrable (fun x => a x * (b x * c x)) μ := by
  refine ha.integrable_mul (hb.of_le_mul (c := M) (hb.aestronglyMeasurable.mul hc) ?_)
  filter_upwards [hM] with x hx
  rw [norm_mul, mul_comm, Real.norm_eq_abs (c x)]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- An `L⁶` function times a continuous compactly supported weight is square
integrable. -/
theorem memLp_mul_of_memLp_six {p h : Vec3 → ℝ} (hp : MemLp p (ENNReal.ofReal 6) volume)
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    MemLp (fun x => p x * h x) 2 volume := by
  obtain ⟨M, hM⟩ := hh.bounded_above_of_compact_support hhc
  refine (eLpNorm_mul_le_of_six hp.aestronglyMeasurable hh.aestronglyMeasurable
    (isClosed_tsupport h).measurableSet (M := M) (fun x => by rw [← Real.norm_eq_abs]; exact hM x)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx)).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hp.eLpNorm_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hhc.isCompact.measure_lt_top.ne))

section ForcePressure

variable {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

theorem stronglyMeasurable_forcePressure :
    StronglyMeasurable fun z : Vec3 × ℝ => forcePressure f hf z :=
  (Classical.choose_spec (exists_forcePressure f hf)).1

/-- On almost every time slice the force pressure lies in `L⁶`. -/
theorem ae_memLp_forcePressure_six {T : ℝ} (hT : 0 < T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      MemLp (fun x => forcePressure f hf (x, t)) (ENNReal.ofReal 6) volume := by
  obtain ⟨-, hfin, -, -⟩ := forcePressure_spec f hf T hT
  have hP := stronglyMeasurable_forcePressure hf
  have h6 : ENNReal.ofReal (6 : ℝ) ≠ 0 := by simp
  have hm : Measurable fun t => eLpNorm (fun x : Vec3 => forcePressure f hf (x, t))
      (ENNReal.ofReal (6 : ℝ)) volume ^ (2 : ℝ) :=
    (measurable_eLpNorm_slice hP h6 ENNReal.ofReal_ne_top volume).pow_const _
  filter_upwards [ae_lt_top' hm.aemeasurable hfin.ne] with t ht
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 ht

/-- The force pressure times a continuous compactly supported space-time
weight is square integrable on every slab. -/
theorem memLp_forcePressure_mul_prod {T : ℝ} (hT : 0 < T) {h : Vec3 × ℝ → ℝ}
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    MemLp (fun z : Vec3 × ℝ => forcePressure f hf z * h z) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  obtain ⟨-, hfin, -, -⟩ := forcePressure_spec f hf T hT
  have hP := stronglyMeasurable_forcePressure hf
  obtain ⟨M, hM⟩ := hh.bounded_above_of_compact_support hhc
  set K : Set Vec3 := Prod.fst '' tsupport h with hKdef
  have hK : IsCompact K := hhc.image continuous_fst
  have hsm : StronglyMeasurable fun z : Vec3 × ℝ => forcePressure f hf z * h z :=
    hP.mul hh.stronglyMeasurable
  have hlin := lintegral_eLpNorm_real_slice_sq hsm (μt := (volume : Measure ℝ).restrict (Ioo 0 T))
  set C : ℝ≥0∞ := ENNReal.ofReal M * volume K ^ (1 / 3 : ℝ) with hC
  have hCtop : C ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_lt_top.ne))
  have hslice : ∀ t, eLpNorm (fun x => forcePressure f hf (x, t) * h (x, t)) 2 volume ^ (2 : ℝ) ≤
      C ^ (2 : ℝ) * eLpNorm (fun x => forcePressure f hf (x, t)) (ENNReal.ofReal 6) volume ^
        (2 : ℝ) := by
    intro t
    have h1 := eLpNorm_mul_le_of_six (p := fun x => forcePressure f hf (x, t))
      (h := fun x => h (x, t))
      (hP.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (hh.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable hK.measurableSet
      (M := M) (fun x => by rw [← Real.norm_eq_abs]; exact hM (x, t))
      (fun x hx => show h (x, t) = 0 from
        image_eq_zero_of_notMem_tsupport fun hz => hx ⟨(x, t), hz, rfl⟩)
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    refine ENNReal.rpow_le_rpow (h1.trans (le_of_eq ?_)) (by norm_num)
    rw [hC]
    ring
  have hbound : eLpNorm (fun z : Vec3 × ℝ => forcePressure f hf z * h z) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) ^ (2 : ℝ) < ⊤ := by
    rw [← hlin]
    refine (lintegral_mono fun t => hslice t).trans_lt ?_
    rw [lintegral_const_mul' _ _ hCtop]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hCtop) hfin
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hbound

end ForcePressure

end CKN.Leray

end

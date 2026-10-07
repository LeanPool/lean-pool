/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumAssembly

/-!
# Almost every time slice of the forced regularized solution

On almost every time of a bounded interval the gradient slices of the forced
regularized solution are square integrable, the force slices are square
integrable and agree with the modification, and the force pressure is locally
integrable with its weak gradient. These are the slice hypotheses of the
momentum identity `eq:reg-momentum-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- Square integrability on a product with a time measure gives square
integrable time slices almost everywhere. -/
theorem ae_memLp_slice_of_memLp_prod {F : Vec3 × ℝ → ℝ} (hF : StronglyMeasurable F) {T : ℝ}
    (h2 : MemLp F 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => F (x, t)) 2 volume := by
  have hlin := lintegral_eLpNorm_real_slice_sq hF (μt := (volume : Measure ℝ).restrict (Ioo 0 T))
  have hfin : ∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => F (x, t)) 2 volume ^ (2 : ℝ) ≠ ⊤ := by
    rw [hlin]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top).ne
  have hm : Measurable fun t => eLpNorm (fun x : Vec3 => F (x, t)) 2 volume ^ (2 : ℝ) :=
    (measurable_eLpNorm_slice hF (by norm_num) (by norm_num) volume).pow_const _
  filter_upwards [ae_lt_top' hm.aemeasurable hfin] with t ht
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 ht

theorem ae_memLp_vector_slice_of_memLp_prod {F : Vec3 × ℝ → Vec3} (hF : StronglyMeasurable F)
    {T : ℝ}
    (h2 : MemLp F 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => F (x, t)) 2 volume := by
  have hlin := lintegral_eLpNorm_slice_sq_eq hF (μt := (volume : Measure ℝ).restrict (Ioo 0 T))
  have hfin : ∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => F (x, t)) 2 volume ^ (2 : ℝ) ≠ ⊤ := by
    rw [hlin]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top).ne
  have hm : Measurable fun t => eLpNorm (fun x : Vec3 => F (x, t)) 2 volume ^ (2 : ℝ) :=
    (measurable_eLpNorm_two_slice hF).pow_const _
  filter_upwards [ae_lt_top' hm.aemeasurable hfin] with t ht
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 ht

section Good

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f) {T : ℝ}

theorem ae_forcedRegGrad_slice (hT : 0 ≤ T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)), ∀ i j,
      MemLp (fun x => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (x, t) i j) 2 volume := by
  have hDu := memLp_forcedRegGrad_prod ρ ε hε ha hf T hT
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  exact ae_memLp_slice_of_memLp_prod (forcedMollifiedGrad_stronglyMeasurable
    (forcedRegRep_stronglyMeasurable ρ ε hε ha hf) (forcedRegRep_locallyIntegrable ρ ε hε ha hf)
    i j) ((hDu.eval i).eval j)

include hf in
theorem ae_forcedForceMod_slice (hT : 0 < T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      MemLp (fun x => forcedForceMod f hf (x, t)) 2 volume ∧
        (fun x => forcedForceMod f hf (x, t)) =ᵐ[volume] fun x => f (x, t) := by
  have h1 := ae_memLp_vector_slice_of_memLp_prod (forcedForceMod_stronglyMeasurable f hf)
    (memLp_forcedForceMod_prod f hf hT)
  have h0 := forcedForceMod_ae_eq f hf hT
  have h0' : ∀ᵐ z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))),
      forcedForceMod f hf z = f z := restrict_spaceTimeSet_eq_prod (Ioo 0 T) ▸ h0
  have hswap := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ).restrict (Ioo 0 T))
    (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae h0'
  have h2 := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [h1, h2] with t ht1 ht2
  exact ⟨ht1, ht2⟩

theorem ae_forcePressure_slice (hT : 0 < T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      LocallyIntegrable (fun x => forcePressure f hf (x, t)) volume ∧
      ∃ hft : MemLp (fun x : Vec3 => f (x, t)) 2 volume,
        CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, t))
          (forcePressureGradientFunction (fun y => f (y, t)) hft) := by
  obtain ⟨-, hfin, hgrad, -⟩ := forcePressure_spec f hf T hT
  have hP : StronglyMeasurable (fun z : Vec3 × ℝ => forcePressure f hf z) :=
    (Classical.choose_spec (exists_forcePressure f hf)).1
  have h6 : ENNReal.ofReal (6 : ℝ) ≠ 0 := by simp
  have hm : Measurable fun t => eLpNorm (fun x : Vec3 => forcePressure f hf (x, t))
      (ENNReal.ofReal (6 : ℝ)) volume ^ (2 : ℝ) :=
    (measurable_eLpNorm_slice hP h6 ENNReal.ofReal_ne_top volume).pow_const _
  filter_upwards [ae_lt_top' hm.aemeasurable hfin.ne, hgrad] with t ht hgt
  refine ⟨?_, hgt⟩
  have hmem : MemLp (fun x : Vec3 => forcePressure f hf (x, t)) (ENNReal.ofReal (6 : ℝ)) volume :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 ht
  exact hmem.locallyIntegrable (by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num))

end Good

end CKN.Leray

end

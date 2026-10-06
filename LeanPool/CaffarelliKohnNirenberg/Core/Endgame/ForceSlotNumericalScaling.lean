/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.MorreyScaling

/-!
# Morrey bounds under parabolic changes of variables

The numerical pressure and bootstrap bounds use unit cylinders. A positive
parabolic dilation transports their Morrey norms with the explicit factor
`a ^ (-5 / τ)`. The estimate below takes the supremum over every centre and
radius and does not impose integrability assumptions on the source.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
noncomputable section
namespace CKN.Core.Endgame

private theorem scaling_embedding {a : ℝ} (ha : 0 < a) (z₀ : ParabolicPoint) :
    MeasurableEmbedding (scalingParabolic a z₀) := by
  let e₁ : Vec3 ≃ₜ Vec3 :=
    (Homeomorph.smulOfNeZero a ha.ne').trans (Homeomorph.addLeft z₀.1)
  let e₂ : ℝ ≃ₜ ℝ :=
    (Homeomorph.smulOfNeZero (a ^ 2) (sq_pos_of_pos ha).ne').trans (Homeomorph.addLeft z₀.2)
  exact e₁.measurableEmbedding.prodMap e₂.measurableEmbedding

/-- A positive parabolic dilation is injective. -/
theorem force_slot_scaling_injective {a : ℝ} (ha : 0 < a) (z₀ : ParabolicPoint) :
    Function.Injective (scalingParabolic a z₀) :=
  (scaling_embedding ha z₀).injective

/-- A positive dilation maps each cylinder to the cylinder with scaled radius. -/
theorem force_slot_cylinder_image {a : ℝ} (ha : 0 < a)
    (z₀ z : ParabolicPoint) (r : ℝ) :
    scalingParabolic a z₀ '' parabolicCylinder z.1 z.2 r =
      parabolicCylinder (scalingParabolic a z₀ z).1 (scalingParabolic a z₀ z).2 (a * r) := by
  change (parabolicTranslate z₀.1 z₀.2 ∘ parabolicScale a) '' _ = _
  rw [Set.image_comp, parabolicCylinder_scale ha, parabolicCylinder_translate]
  rfl

/-- Real integrals transform by the parabolic Jacobian, without additional
measurability or integrability assumptions. -/
theorem force_slot_integral_scaling {a : ℝ} (ha : 0 < a)
    (z₀ : ParabolicPoint) (f : ParabolicPoint → ℝ) :
    (∫ w : ParabolicPoint, f (scalingParabolic a z₀ w)) =
      a⁻¹ ^ 5 * ∫ w : ParabolicPoint, f w := by
  have hpres : MeasurePreserving (scalingParabolic a z₀) volume
      (ENNReal.ofReal (a⁻¹ ^ 5) • (volume : Measure ParabolicPoint)) :=
    ⟨(scaling_embedding ha z₀).measurable, map_scalingParabolic a ha z₀⟩
  have h := hpres.integral_comp (scaling_embedding ha z₀) f
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h
  exact h

/-- A nonnegative cylinder integral transforms by the parabolic Jacobian. -/
theorem force_slot_lintegral_scaling {a : ℝ} (ha : 0 < a)
    (z₀ z : ParabolicPoint) (r : ℝ) (f : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, f (scalingParabolic a z₀ w)) =
      ENNReal.ofReal (a⁻¹ ^ 5) *
        ∫⁻ w in parabolicCylinder (scalingParabolic a z₀ z).1
          (scalingParabolic a z₀ z).2 (a * r), f w := by
  have hpres : MeasurePreserving (scalingParabolic a z₀) volume
      (ENNReal.ofReal (a⁻¹ ^ 5) • (volume : Measure ParabolicPoint)) :=
    ⟨(scaling_embedding ha z₀).measurable, map_scalingParabolic a ha z₀⟩
  have h := hpres.setLIntegral_comp_emb (scaling_embedding ha z₀) f
    (parabolicCylinder z.1 z.2 r)
  rw [force_slot_cylinder_image ha, Measure.restrict_smul, lintegral_smul_measure] at h
  exact h

/-- The integral in every Morrey cell transforms by the parabolic Jacobian. -/
theorem force_slot_power_integral_scaling {a : ℝ} (ha : 0 < a)
    (z₀ z : ParabolicPoint) (r P : ℝ) (f : ParabolicPoint → ℝ) :
    cylinderPowerIntegral P (fun w => f (scalingParabolic a z₀ w)) z r =
      ENNReal.ofReal (a⁻¹ ^ 5) *
        cylinderPowerIntegral P f (scalingParabolic a z₀ z) (a * r) := by
  exact force_slot_lintegral_scaling ha z₀ z r (fun w => ENNReal.ofReal |f w| ^ P)

/-- A positive parabolic dilation gives the all-centre numerical Morrey bound. -/
theorem force_slot_morrey_scaling_le {a P τ : ℝ} (ha : 0 < a) (hP : 0 < P)
    (z₀ : ParabolicPoint) (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun w => f (scalingParabolic a z₀ w)) ≤
      ENNReal.ofReal a ^ (-5 / τ : ℝ) * morreyNorm P τ f := by
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hat : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hJac : ENNReal.ofReal (a⁻¹ ^ 5) = ENNReal.ofReal a ^ (-5 : ℝ) := by
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr ha.le), ENNReal.ofReal_inv_of_pos ha,
      ← ENNReal.rpow_natCast, ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    norm_num
  have hcell (z : ParabolicPoint) (r : {r : ℝ // 0 < r}) :
      morreyCell P τ (fun w => f (scalingParabolic a z₀ w)) z r.1 =
        ENNReal.ofReal a ^ (-5 / τ : ℝ) *
          morreyCell P τ f (scalingParabolic a z₀ z) (a * r.1) := by
    unfold morreyCell
    rw [force_slot_power_integral_scaling ha, hJac,
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hP.le), ← ENNReal.rpow_mul,
      ENNReal.ofReal_mul ha.le, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    have hexp : (-5 : ℝ) * (1 / P) = -5 / τ + -(5 * (1 - P / τ) / P) := by
      field_simp [hP.ne']
      ring
    rw [hexp, ENNReal.rpow_add _ _ ha0 hat]
    ac_rfl
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  rw [hcell]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_iSup_of_le (scalingParabolic a z₀ z)
    (le_iSup (fun s : {s : ℝ // 0 < s} =>
      morreyCell P τ f (scalingParabolic a z₀ z) s.1) ⟨a * r.1, mul_pos ha r.2⟩)

/-- A numerical bound for an indicated source transports with both the
field amplitude and the parabolic Morrey scaling factor retained. -/
theorem force_slot_indicator_scaling_le
    (a c P τ : ℝ) (K : ℝ≥0∞) (ha : 0 < a) (hP : 0 < P)
    (z₀ : ParabolicPoint) (Q : Set ParabolicPoint) (f : ParabolicPoint → ℝ)
    (hN : morreyNorm P τ (Q.indicator f) ≤ K) :
    morreyNorm P τ ((scalingParabolic a z₀ ⁻¹' Q).indicator
      (fun w => c * f (scalingParabolic a z₀ w))) ≤
      ENNReal.ofReal |c| * (ENNReal.ofReal a ^ (-5 / τ : ℝ) * K) := by
  have heq : (scalingParabolic a z₀ ⁻¹' Q).indicator
      (fun w => c * f (scalingParabolic a z₀ w)) =
      (fun w => c * Q.indicator f (scalingParabolic a z₀ w)) := by
    funext w
    by_cases hw : scalingParabolic a z₀ w ∈ Q
    · rw [indicator_of_mem hw, indicator_of_mem (show w ∈ scalingParabolic a z₀ ⁻¹' Q from hw)]
    · rw [indicator_of_notMem hw,
        indicator_of_notMem (show w ∉ scalingParabolic a z₀ ⁻¹' Q from hw), mul_zero]
  rw [heq]
  apply (morreyNorm_const_mul_le hP c _).trans
  apply mul_le_mul_of_nonneg_left _ bot_le
  exact (force_slot_morrey_scaling_le ha hP z₀ (Q.indicator f)).trans
    (mul_le_mul_of_nonneg_left hN bot_le)

/-- Finite data remain finite under every positive parabolic rescaling. -/
theorem force_slot_scaling_bound_lt_top (a c τ : ℝ) {K : ℝ≥0∞}
    (ha : 0 < a) (hK : K < ⊤) :
    ENNReal.ofReal |c| * (ENNReal.ofReal a ^ (-5 / τ : ℝ) * K) < ⊤ := by
  have hpow : ENNReal.ofReal a ^ (-5 / τ : ℝ) < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hpow hK)

/-- The reverse change of variables recovers a bound on the original field
from a bound in normalized coordinates. -/
theorem force_slot_morrey_unscaling_le {a P τ : ℝ} (ha : 0 < a) (hP : 0 < P)
    (z₀ : ParabolicPoint) (f : ParabolicPoint → ℝ) :
    morreyNorm P τ f ≤ ENNReal.ofReal a ^ (5 / τ : ℝ) *
      morreyNorm P τ (fun w => f (scalingParabolic a z₀ w)) := by
  have hinv (w : ParabolicPoint) :
      scalingParabolic a z₀
        (scalingParabolic a⁻¹ (-(a⁻¹ • z₀.1), -(a ^ 2)⁻¹ * z₀.2) w) = w := by
    apply Prod.ext
    · funext i
      change z₀.1 i + a * (-(a⁻¹ * z₀.1 i) + a⁻¹ * w.1 i) = w.1 i
      field_simp
      ring
    · change z₀.2 + a ^ 2 * (-(a ^ 2)⁻¹ * z₀.2 + a⁻¹ ^ 2 * w.2) = w.2
      field_simp
      ring
  have h := force_slot_morrey_scaling_le (τ := τ) (inv_pos.mpr ha) hP
    (-(a⁻¹ • z₀.1), -(a ^ 2)⁻¹ * z₀.2) (fun w => f (scalingParabolic a z₀ w))
  simp only [hinv, ENNReal.ofReal_inv_of_pos ha, ENNReal.inv_rpow,
    ← ENNReal.rpow_neg, ← neg_div, neg_neg] at h
  exact h

/-- A normalized subcarrier inherits the explicit scaled bound on its
original carrier. -/
theorem force_slot_subcarrier_scaling_le
    (a c P τ : ℝ) (K : ℝ≥0∞) (ha : 0 < a) (hP : 0 < P)
    (z₀ : ParabolicPoint) (Q B : Set ParabolicPoint) (f : ParabolicPoint → ℝ)
    (hQB : scalingParabolic a z₀ '' Q ⊆ B)
    (hN : morreyNorm P τ (B.indicator f) ≤ K) :
    morreyNorm P τ (Q.indicator (fun w => c * f (scalingParabolic a z₀ w))) ≤
      ENNReal.ofReal |c| * (ENNReal.ofReal a ^ (-5 / τ : ℝ) * K) := by
  apply le_trans (morreyNorm_mono hP.le ?_)
    (force_slot_indicator_scaling_le a c P τ K ha hP z₀ B f hN)
  intro w
  by_cases hw : w ∈ Q
  · rw [indicator_of_mem hw, indicator_of_mem (show w ∈ scalingParabolic a z₀ ⁻¹' B from hQB ⟨w, hw, rfl⟩)]
  · rw [indicator_of_notMem hw, abs_zero]
    exact abs_nonneg _

/-- A nonzero field amplitude can be removed from a normalized Morrey bound,
retaining the inverse amplitude and dilation factors. -/
theorem force_slot_subcarrier_unscaling_le
    (a c P τ : ℝ) (K : ℝ≥0∞) (ha : 0 < a) (hc : c ≠ 0) (hP : 0 < P)
    (z₀ : ParabolicPoint) (Q B : Set ParabolicPoint) (f : ParabolicPoint → ℝ)
    (hBQ : scalingParabolic a z₀ ⁻¹' B ⊆ Q)
    (hN : morreyNorm P τ (Q.indicator
      (fun w => c * f (scalingParabolic a z₀ w))) ≤ K) :
    morreyNorm P τ (B.indicator f) ≤
      ENNReal.ofReal a ^ (5 / τ : ℝ) * (ENNReal.ofReal |c⁻¹| * K) := by
  apply (force_slot_morrey_unscaling_le ha hP z₀ (B.indicator f)).trans
  apply mul_le_mul_of_nonneg_left _ bot_le
  have hmul := (morreyNorm_const_mul_le hP c⁻¹
    (Q.indicator (fun w => c * f (scalingParabolic a z₀ w)))).trans
      (mul_le_mul_of_nonneg_left hN bot_le)
  apply le_trans (morreyNorm_mono hP.le ?_) hmul
  intro w
  by_cases hw : scalingParabolic a z₀ w ∈ B
  · rw [indicator_of_mem hw, indicator_of_mem (hBQ hw), ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]
  · rw [indicator_of_notMem hw, abs_zero]
    exact abs_nonneg _

end CKN.Core.Endgame

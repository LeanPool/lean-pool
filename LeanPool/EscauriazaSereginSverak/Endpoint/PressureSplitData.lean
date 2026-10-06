/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data
public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitHarmonic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS


/-- Local integrability data on compact subcylinders follows from the data in
`thm:ess-local`; it is used when testing the momentum equation in
`lem:pressure-split`. -/
theorem pressureSplit_localData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (hpmeas : AEStronglyMeasurable p (volume.restrict pressureSplitDomain))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict pressureSplitTime) < ⊤)
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict pressureSplitDomain))
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x, t) i)
        (fun x => Du (x, t) i)) :
    CKN.IsSuitableWeakSolutionData pressureSplitBall pressureSplitTime 3
      u Du p (fun _ => 0) := by
  refine ⟨isOpen_vec3Ball (0 : Vec3) 1, isOpen_Ioo, ordConnected_Ioo,
    by norm_num, ?_, ?_⟩
  · intro Ω' J hbox i
    simp [CKN.localLp]
  · intro Ω' J hbox
    rcases hbox with ⟨hΩ'open, hΩ'compact, hΩ'sub, hJord, hJcompact, hJsub⟩
    have hΩ'sub' : Ω' ⊆ pressureSplitBall :=
      subset_trans subset_closure hΩ'sub
    have hJsub' : J ⊆ pressureSplitTime :=
      subset_trans subset_closure hJsub
    have hdomain : spaceTimeSet Ω' J ⊆ pressureSplitDomain :=
      Set.prod_mono hΩ'sub' hJsub'
    have hμ : volume.restrict (spaceTimeSet Ω' J) ≤
        volume.restrict pressureSplitDomain :=
      Measure.restrict_mono_set volume hdomain
    have htimeμ : volume.restrict J ≤ volume.restrict pressureSplitTime :=
      Measure.restrict_mono_set volume hJsub'
    have hu' : AEStronglyMeasurable u
        (volume.restrict (spaceTimeSet Ω' J)) := hu.mono_measure hμ
    have hDu' : AEStronglyMeasurable Du
        (volume.restrict (spaceTimeSet Ω' J)) := hDu.mono_measure hμ
    have hpmeas' : AEStronglyMeasurable p
        (volume.restrict (spaceTimeSet Ω' J)) := hpmeas.mono_measure hμ
    have hsup : essSup (fun t : ℝ => ∫⁻ x in Ω',
        ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ⊤ := by
      refine (CKN.Foundation.Parabolic.Integration.essSup_mono_measure_and_ae
        htimeμ ?_).trans_lt hL2
      exact Filter.Eventually.of_forall fun t =>
        lintegral_mono_set hΩ'sub'
    have henergy' : (∫⁻ z in spaceTimeSet Ω' J,
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      refine (lintegral_mono_set hdomain).trans_lt henergy
    have hp' : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) := hp.mono_measure hμ
    have hgrad' : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict J),
        HasWeakGradientOn Ω' (fun x => u (x, t) i)
          (fun x => Du (x, t) i) := by
      intro i
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hJsub' hgrad]
        with t ht
      exact HasWeakGradientOn.restrict hΩ'open hΩ'sub' (ht i)
    exact ⟨hu', hDu', hpmeas', measurable_const.aestronglyMeasurable,
      hsup, henergy', hp', by simp, hgrad'⟩

end ESS

end

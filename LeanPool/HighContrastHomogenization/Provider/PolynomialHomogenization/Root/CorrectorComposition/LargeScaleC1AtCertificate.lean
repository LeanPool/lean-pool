/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalAssembly

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.LargeScaleC1AtCertificate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the large-scale C¹ slope approximation clause at an arbitrary certificate

The C¹ slope approximation at the exact-gauge terminal fixes
`reconciledRootGoodScale d cStar` in both its certificate slot and its terminal
premise.  The terminal is proved at the **event-retaining** certificate
`reconciledRootGoodScaleOn`, because the
pushforward marker's own carrier is only available on the invariant core the
event supplies.  This module is the same theorem with the certificate a
parameter; the proof body is the one, with `g` and `κc` already fixed.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

/-- **the large-scale C¹ slope approximation clause at a given certificate, from the exact-gauge
terminal.** -/
theorem largeScaleC1_of_terminal_atCertificate (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop)
    (CorrectorFamily : Mat d →
      (Vec d → CoeffSpace d → Vec d → ℝ) →
      (Vec d → CoeffSpace d → Vec d → Vec d) → Prop)
    (hposDef : ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ),
      GoodScale abar a x → (symmPart abar).PosDef)
    (hlinear : ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
      (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
      CorrectorFamily abar Phi gradPhi →
      ∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
        gradPhi (c • e + e') a =ᵐ[volume]
          fun y ↦ c • gradPhi e a y + gradPhi e' a y)
    (hterminal : ∀ eta : ℝ, eta ∈ Ioo (0 : ℝ) 1 →
      ExactRootGaugeTerminal d GoodScale CorrectorFamily eta) :
    ∃ C₁ : ℝ → ℝ, (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
      ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
        (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
        CorrectorFamily abar Phi gradPhi →
        ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
          GoodScale abar a x →
          ∀ R : ℝ, x ≤ R →
            ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
              MemH1a (fun y => a.1 y) (ellipsoid abar R) u Du →
              IsWeakSolutionOn (fun y => a.1 y) (ellipsoid abar R) Du →
                ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                  ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc x R →
                    weightedGradNorm (fun y => a.1 y) (ellipsoid abar r)
                        (fun y => Du y - (e + gradPhi e a y)) ≤
                      ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                        weightedGradNorm (fun y => a.1 y)
                          (ellipsoid abar R) Du := by
  classical
  have key : ∀ ϑ : ℝ, ϑ ∈ Ioo (0 : ℝ) 1 → ∃ K : ℝ, 0 < K ∧
      ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
        (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
        CorrectorFamily abar Phi gradPhi →
        ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
          GoodScale abar a x →
          ∀ R : ℝ, x ≤ R →
            ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
              MemH1a (fun y => a.1 y) (ellipsoid abar R) u Du →
              IsWeakSolutionOn (fun y => a.1 y) (ellipsoid abar R) Du →
                ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc x R →
                  weightedGradNorm (fun y => a.1 y) (ellipsoid abar r)
                      (fun y => Du y - (e + gradPhi e a y)) ≤
                    ENNReal.ofReal (K * (r / R) ^ ϑ) *
                      weightedGradNorm (fun y => a.1 y)
                        (ellipsoid abar R) Du := by
    intro ϑ hϑ
    obtain ⟨L, A, hA, hrow⟩ := hterminal ϑ hϑ
    obtain ⟨K, hK, hreturn⟩ :=
      Root.exists_rangeCompletePhysicalC1_of_exactRootGaugeTerminal
        (d := d) L ϑ A hϑ.1.le hA
    refine ⟨K, hK, ?_⟩
    intro abar Phi gradPhi hmarker a x hx hgood R hxR u Du hu hweak
    have hS : (symmPart abar).PosDef := hposDef abar a x hgood
    obtain ⟨PhiRef, hpullback, hball⟩ :=
      hrow abar hS Phi gradPhi hmarker a x hx hgood
    exact hreturn abar hS a x hx gradPhi
      (fun c e e' ↦ hlinear abar Phi gradPhi hmarker c e e' a)
      PhiRef hpullback R hxR u Du hu hweak
      (hball R u Du hu hweak)
  refine ⟨fun ϑ ↦ if hϑ : ϑ ∈ Ioo (0 : ℝ) 1 then
      Classical.choose (key ϑ hϑ) else 1, ?_, ?_⟩
  · intro ϑ
    dsimp only
    by_cases hϑ : ϑ ∈ Ioo (0 : ℝ) 1
    · rw [dite_eq_left hϑ]
      exact (Classical.choose_spec (key ϑ hϑ)).1
    · rw [dite_eq_right hϑ]
      norm_num
  · intro abar Phi gradPhi hmarker a x hx hgood R hxR u Du hu hweak ϑ hϑ
    have hmain := (Classical.choose_spec (key ϑ hϑ)).2
      abar Phi gradPhi hmarker a x hx hgood R hxR u Du hu hweak
    obtain ⟨e, he⟩ := hmain
    refine ⟨e, fun r hr ↦ ?_⟩
    have hval : (fun ϑ' ↦ if hϑ' : ϑ' ∈ Ioo (0 : ℝ) 1 then
        Classical.choose (key ϑ' hϑ') else 1) ϑ =
        Classical.choose (key ϑ hϑ) := dite_eq_left hϑ
    rw [hval]
    exact he r hr

end

end CorrectorComposition
end HighContrast
end HCPolySupport

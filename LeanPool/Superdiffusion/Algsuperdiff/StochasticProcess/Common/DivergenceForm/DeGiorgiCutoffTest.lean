/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.Basic

/-!
# DeGiorgiCutoffTest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Localized De Giorgi cutoff tests

This file packages the standard positive-part truncation multiplied by the square of a smooth,
compactly supported cutoff.  It only combines the existing truncation and `H¹₀` product APIs.
The localized product itself is recorded separately, since the weighted energy estimates use it
without any truncation.
-/

noncomputable section

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- The product of an `H¹` function with a smooth compactly supported
multiplier supported in the domain, as a zero-trace function. -/
noncomputable def localizedProductToH10
    (hU : IsOpenBoundedConvexDomain U) (v : H1Function U)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphiCompact : HasCompactSupport phi) (hphiU : tsupport phi ⊆ U) :
    H10Function U :=
  Classical.choose
    (memH10_mul_of_contDiff_hasCompactSupport
      hU hphi hphiCompact hphiU v.memH1)

/-- The localized product is pointwise the product of the multiplier with the
value of the `H¹` function. -/
theorem localizedProductToH10_toFun
    (hU : IsOpenBoundedConvexDomain U) (v : H1Function U)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphiCompact : HasCompactSupport phi) (hphiU : tsupport phi ⊆ U) :
    (localizedProductToH10 hU v hphi hphiCompact hphiU).toH1Function.toFun =
      fun x ↦ phi x * v.toFun x :=
  Classical.choose_spec
    (memH10_mul_of_contDiff_hasCompactSupport
      hU hphi hphiCompact hphiU v.memH1)

/-- The weak gradient of the localized product agrees almost everywhere with
the gradient of the pointwise product. -/
theorem localizedProductToH10_grad_ae
    (hU : IsOpenBoundedConvexDomain U) (v : H1Function U)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphiCompact : HasCompactSupport phi) (hphiU : tsupport phi ⊆ U) :
    ∀ᵐ x ∂volumeMeasureOn U,
      (localizedProductToH10 hU v hphi hphiCompact hphiU).toH1Function.grad x =
        (v.mulContDiffHasCompactSupport hphi hphiCompact).grad x := by
  let w := localizedProductToH10 hU v hphi hphiCompact hphiU
  let p := v.mulContDiffHasCompactSupport hphi hphiCompact
  have hfun : w.toH1Function.toFun = p.toFun := by
    rw [localizedProductToH10_toFun, H1Function.mulContDiffHasCompactSupport_toFun]
  have hcoord : ∀ i : Fin d,
      (fun x ↦ w.toH1Function.grad x i) =ᵐ[volumeMeasureOn U]
        fun x ↦ p.grad x i := by
    intro i
    apply HasWeakPartialDerivOn.ae_eq hU.isOpen
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict
        ((w.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num))
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict
        ((p.gradMemL2 i).locallyIntegrable (by norm_num))
    · exact w.toH1Function.hasWeakPartialDerivOn i
    · rw [hfun]
      exact p.hasWeakPartialDerivOn i
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  ext i
  exact hx i

end DivergenceFormProcess.Form

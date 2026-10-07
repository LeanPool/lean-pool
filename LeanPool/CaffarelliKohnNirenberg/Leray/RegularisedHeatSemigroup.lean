/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildInitialTrace

/-!
# Semigroup law for the Fourier heat flow

The Gaussian frequency multiplier obeys the additive-time composition law.
This identity is used when a mild trajectory is restarted at a later time.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Gaussian heat symbols multiply when nonnegative time intervals are
joined. -/
theorem heatSymbol_add (s t : ℝ) (ξ : L2Vec3) :
    heatSymbol (s + t) ξ = heatSymbol s ξ * heatSymbol t ξ := by
  simp only [heatSymbol, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 1
  ring_nf

/-- The complex Fourier heat flow composes across adjacent time intervals. -/
theorem regularisedHeatSemigroup_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : ComplexVectorL2) :
    heatSemigroup (s + t) (add_nonneg hs ht) f =
      heatSemigroup s hs (heatSemigroup t ht f) := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  apply ℱ.injective
  change ℱ (ℱ.symm (heatMultiplier (s + t) (add_nonneg hs ht) • ℱ f)) =
    ℱ (ℱ.symm (heatMultiplier s hs •
      ℱ (ℱ.symm (heatMultiplier t ht • ℱ f))))
  rw [ℱ.apply_symm_apply, ℱ.apply_symm_apply, ℱ.apply_symm_apply]
  apply Lp.ext
  have hsymbol (r : ℝ) (hr : 0 ≤ r) :
      (heatMultiplier r hr : Lp (α := L2Vec3) ℂ ∞) =ᵐ[volume]
        heatSymbol r := by
    unfold heatMultiplier
    exact MemLp.coeFn_toLp _
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) (heatMultiplier (s + t) (add_nonneg hs ht)) (ℱ f),
      Lp.coeFn_lpSMul (r := 2) (heatMultiplier s hs)
        (heatMultiplier t ht • ℱ f),
      Lp.coeFn_lpSMul (r := 2) (heatMultiplier t ht) (ℱ f),
      hsymbol (s + t) (add_nonneg hs ht), hsymbol s hs, hsymbol t ht]
    with ξ hleft hright hinner hsum hsξ htξ
  rw [hleft, hright]
  change (heatMultiplier (s + t) (add_nonneg hs ht) ξ) • ℱ f ξ =
    (heatMultiplier s hs ξ) • (heatMultiplier t ht • ℱ f) ξ
  rw [hsum, hsξ, hinner]
  change heatSymbol (s + t) ξ • ℱ f ξ =
    heatSymbol s ξ • ((heatMultiplier t ht ξ) • ℱ f ξ)
  rw [htξ, heatSymbol_add]
  exact mul_smul _ _ _

end CKN.Leray

end

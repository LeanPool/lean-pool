/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Extension.Reflect


/-!
# Translation of a weak gradient

The global approximation theorem shifts a function into the domain before mollifying it, so that
the mollification of the shift is defined on a neighbourhood of the piece of boundary in view.
The shift has to move the weak gradient with it, which is what this file records.

Translation is the second of the two rigid motions the extension operator runs on, beside the
reflection of `EllipticPdes.Extension.Reflect`. It is measure preserving and its derivative is
the identity, so it moves a weak gradient with no sign and no Jacobian.

## Main declarations

* `EllipticPdes.Extension.partialD_comp_translate`: the partial derivatives of a translate.
* `EllipticPdes.Extension.hasWeakGradOn_comp_translate`: the weak gradient of a translate.
* `EllipticPdes.Extension.eLpNorm_comp_translate`: translation preserves every `Lᵖ` seminorm.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.3, Theorem 3.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {d : ℕ}

/-! ### The translation -/

lemma measurePreserving_translate (h : EuclideanSpace ℝ (Fin d)) :
    MeasurePreserving (fun y : EuclideanSpace ℝ (Fin d) => y + h) volume volume :=
  measurePreserving_add_right volume h

lemma measurableEmbedding_translate (h : EuclideanSpace ℝ (Fin d)) :
    MeasurableEmbedding (fun y : EuclideanSpace ℝ (Fin d) => y + h) :=
  (Homeomorph.addRight h).measurableEmbedding

/-! ### Derivatives and supports -/

/-- **Partial derivatives of a translate.** Translation has derivative the identity, so a
partial derivative translates with no factor. -/
theorem partialD_comp_translate {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Differentiable ℝ φ)
    (h : EuclideanSpace ℝ (Fin d)) (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun y => φ (y + h)) x = partialD k φ (x + h) := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => y + h)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) x := (hasFDerivAt_id x).add_const h
  have hcomp : HasFDerivAt (fun y => φ (y + h))
      ((fderiv ℝ φ (x + h)).comp (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) x :=
    (hφ (x + h)).hasFDerivAt.comp x h1
  rw [partialD, hcomp.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, partialD]

lemma contDiff_comp_translate {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (h : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (y + h)) :=
  hφ.comp (contDiff_id.add contDiff_const)

lemma hasCompactSupport_comp_translate {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : HasCompactSupport φ) (h : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (fun y => φ (y + h)) :=
  hφ.comp_homeomorph (Homeomorph.addRight h)

lemma tsupport_comp_translate_subset {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))} (h : EuclideanSpace ℝ (Fin d))
    (hs : tsupport φ ⊆ (fun y : EuclideanSpace ℝ (Fin d) => y + h) ⁻¹' B) :
    tsupport (fun y => φ (y - h)) ⊆ B := by
  have hsub : tsupport (fun y : EuclideanSpace ℝ (Fin d) => φ (y - h))
      ⊆ (fun y : EuclideanSpace ℝ (Fin d) => y - h) ⁻¹' tsupport φ := by
    refine closure_minimal (fun y hy => ?_)
      (IsClosed.preimage (continuous_id.sub continuous_const) isClosed_closure)
    exact Set.mem_preimage.mpr (subset_closure hy)
  refine hsub.trans (fun y hy => ?_)
  have := hs (Set.mem_preimage.mp hy)
  simpa using this

/-! ### The weak gradient of a translate -/

/-- **Translation of a weak gradient.** If `u` has weak gradient `g` on `B`, then `u(· + h)` has
weak gradient `k ↦ gₖ(· + h)` on the preimage of `B` under the translation.

The proof is the change of variables under a measure-preserving translation, twice: once to move
the test function onto `B`, where the hypothesis applies, and once to move the conclusion back. -/
theorem hasWeakGradOn_comp_translate {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : HasWeakGradOn B u g) (h : EuclideanSpace ℝ (Fin d)) :
    HasWeakGradOn ((fun y : EuclideanSpace ℝ (Fin d) => y + h) ⁻¹' B)
      (fun y => u (y + h)) (fun k y => g k (y + h)) := by
  intro φ hφ hφc hφs k
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψs : tsupport (fun y => φ (y - h)) ⊆ B := tsupport_comp_translate_subset h hφs
  have hψcd : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (y - h)) := by
    have := contDiff_comp_translate hφ (-h)
    simpa only [sub_eq_add_neg] using this
  have hψcs : HasCompactSupport (fun y => φ (y - h)) := by
    have := hasCompactSupport_comp_translate hφc (-h)
    simpa only [sub_eq_add_neg] using this
  have hkey := hw (fun y => φ (y - h)) hψcd hψcs hψs k
  -- The test function's derivative, moved across the translation.
  have hpd : ∀ y, partialD k (fun z => φ (z - h)) y = partialD k φ (y - h) := by
    intro y
    have := partialD_comp_translate hφd (-h) k y
    simpa only [sub_eq_add_neg] using this
  have hkey' : ∫ y in B, u y * partialD k φ (y - h)
      = - ∫ y in B, g k y * φ (y - h) := by
    rw [← hkey]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    change u y * partialD k φ (y - h) = u y * partialD k (fun z => φ (z - h)) y
    rw [hpd y]
  -- Both sides move by the same change of variables.
  have hleft : ∫ x in (fun y : EuclideanSpace ℝ (Fin d) => y + h) ⁻¹' B,
        u (x + h) * partialD k φ x
      = ∫ y in B, u y * partialD k φ (y - h) := by
    have := (measurePreserving_translate h).setIntegral_preimage_emb
      (measurableEmbedding_translate h) (fun y => u y * partialD k φ (y - h)) B
    simpa using this
  have hright : ∫ x in (fun y : EuclideanSpace ℝ (Fin d) => y + h) ⁻¹' B,
        g k (x + h) * φ x
      = ∫ y in B, g k y * φ (y - h) := by
    have := (measurePreserving_translate h).setIntegral_preimage_emb
      (measurableEmbedding_translate h) (fun y => g k y * φ (y - h)) B
    simpa using this
  rw [hleft, hkey', hright]

/-- **Translation preserves every `Lᵖ` seminorm.** -/
theorem eLpNorm_comp_translate {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : AEStronglyMeasurable f volume) (h : EuclideanSpace ℝ (Fin d)) (p : ℝ≥0∞) :
    eLpNorm (fun y => f (y + h)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_translate h)

end EllipticPdes.Extension

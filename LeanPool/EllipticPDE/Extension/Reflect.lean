/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.WeakGradient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace


/-!
# Reflection in a coordinate hyperplane

Reflecting the `j`-th coordinate is the first step of the extension operator: a function on a
half-ball is continued across the flat piece of its boundary by composing with the reflection,
and the higher-order reflection that matches the normal derivative is a combination of two such
composites.

This file records what the reflection does to the three things the weak formulation sees. It is
a linear isometry, so it preserves Lebesgue measure and is a measurable embedding; it sends the
`k`-th partial derivative to `±` the `k`-th partial derivative of the composite, with the sign
negative exactly at `k = j`; and it therefore sends a weak gradient on a set to a weak gradient
on the preimage of that set, with the same signs.

Nothing here asks anything of the set, which is what makes it usable both on a half-ball and on
the image of one under a boundary chart.

## Main declarations

* `EllipticPdes.Extension.reflectLI`: the reflection, as a linear isometry equivalence.
* `EllipticPdes.Extension.partialD_comp_reflect`: the partial derivatives of a reflected
  function.
* `EllipticPdes.Extension.hasWeakGradOn_comp_reflect`: the weak gradient of a reflected
  function.
* `EllipticPdes.Extension.eLpNorm_comp_reflect`: reflection preserves every `Lᵖ` seminorm.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4, Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {d : ℕ}

/-! ### The reflection -/

/-- The sign the reflection in the `j`-th coordinate hyperplane attaches to the `k`-th
coordinate: negative exactly when the two agree. -/
def reflectSign (j k : Fin d) : ℝ := if k = j then -1 else 1

lemma reflectSign_mul_self (j k : Fin d) : reflectSign j k * reflectSign j k = 1 := by
  rw [reflectSign]
  split <;> norm_num

lemma reflectSign_ne_zero (j k : Fin d) : reflectSign j k ≠ 0 := by
  rw [reflectSign]
  split <;> norm_num

/-- **Reflection in the `j`-th coordinate hyperplane**, as a linear isometry equivalence of
Euclidean space. -/
def reflectLI (j : Fin d) : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = j then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] lemma reflectLI_apply (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) :
    reflectLI j x k = reflectSign j k * x k := by
  rw [reflectLI, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply, reflectSign]
  split <;> simp

@[simp] lemma reflectLI_involutive (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    reflectLI j (reflectLI j x) = x := by
  ext k
  rw [reflectLI_apply, reflectLI_apply, ← mul_assoc, reflectSign_mul_self, one_mul]

lemma reflectLI_preimage_preimage (j : Fin d) (B : Set (EuclideanSpace ℝ (Fin d))) :
    reflectLI j ⁻¹' (reflectLI j ⁻¹' B) = B := by
  ext x
  simp only [Set.mem_preimage, reflectLI_involutive]

lemma measurePreserving_reflectLI (j : Fin d) :
    MeasurePreserving (reflectLI j) volume volume :=
  (reflectLI j).measurePreserving

lemma measurableEmbedding_reflectLI (j : Fin d) :
    MeasurableEmbedding (reflectLI j) :=
  (reflectLI j).toHomeomorph.measurableEmbedding

/-! ### Derivatives and supports -/

/-- **Partial derivatives of a reflected function.** -/
theorem partialD_comp_reflect {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Differentiable ℝ φ)
    (j k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun y => φ (reflectLI j y)) x
      = reflectSign j k * partialD k φ (reflectLI j x) := by
  have hsingle : (reflectLI j) (EuclideanSpace.single k (1 : ℝ))
      = reflectSign j k • EuclideanSpace.single k (1 : ℝ) := by
    ext m
    rw [reflectLI_apply]
    by_cases hm : m = k
    · subst hm; simp
    · simp [hm]
  have hcomp : HasFDerivAt (φ ∘ (reflectLI j))
      ((fderiv ℝ φ (reflectLI j x)).comp
        ((reflectLI j).toContinuousLinearEquiv :
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) x :=
    (hφ (reflectLI j x)).hasFDerivAt.comp x
      (reflectLI j).toContinuousLinearEquiv.hasFDerivAt
  have hfun : (fun y => φ (reflectLI j y)) = φ ∘ (reflectLI j) := rfl
  rw [hfun, partialD, hcomp.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [show ((reflectLI j).toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (EuclideanSpace.single k (1 : ℝ)) = reflectLI j (EuclideanSpace.single k (1 : ℝ)) from rfl,
    hsingle, map_smul, smul_eq_mul, partialD]

lemma contDiff_comp_reflect {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (reflectLI j y)) :=
  hφ.comp (reflectLI j).toContinuousLinearEquiv.contDiff

lemma hasCompactSupport_comp_reflect {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : HasCompactSupport φ) (j : Fin d) :
    HasCompactSupport (fun y => φ (reflectLI j y)) :=
  hφ.comp_homeomorph (reflectLI j).toHomeomorph

lemma tsupport_comp_reflect_subset {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))} (j : Fin d)
    (h : tsupport φ ⊆ reflectLI j ⁻¹' B) :
    tsupport (fun y => φ (reflectLI j y)) ⊆ B := by
  have hsub : tsupport (fun y => φ (reflectLI j y)) ⊆ reflectLI j ⁻¹' tsupport φ := by
    refine closure_minimal (fun y hy => ?_)
      (IsClosed.preimage (reflectLI j).continuous isClosed_closure)
    exact Set.mem_preimage.mpr (subset_closure hy)
  refine hsub.trans ?_
  intro y hy
  have := h (Set.mem_preimage.mp hy)
  simpa only [Set.mem_preimage, reflectLI_involutive] using this

/-! ### The weak gradient of a reflected function -/

/-- **Reflection of a weak gradient.** If `u` has weak gradient `g` on `B`, then `u ∘ Rⱼ` has weak
gradient `k ↦ ±(gₖ ∘ Rⱼ)` on the preimage of `B`, with the sign negative exactly at `k = j`.

The proof is the change of variables under a measure-preserving involution, twice: once to move
the test function onto `B`, where the hypothesis applies, and once to move the conclusion back. -/
theorem hasWeakGradOn_comp_reflect {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) (j : Fin d) :
    HasWeakGradOn (reflectLI j ⁻¹' B) (fun y => u (reflectLI j y))
      (fun k y => reflectSign j k * g k (reflectLI j y)) := by
  intro φ hφ hφc hφs k
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψs : tsupport (fun y => φ (reflectLI j y)) ⊆ B := tsupport_comp_reflect_subset j hφs
  have hkey := h (fun y => φ (reflectLI j y)) (contDiff_comp_reflect hφ j)
    (hasCompactSupport_comp_reflect hφc j) hψs k
  -- The test function's derivative, moved across the reflection.
  have hpd : ∀ y, partialD k φ (reflectLI j y)
      = reflectSign j k * partialD k (fun z => φ (reflectLI j z)) y := by
    intro y
    rw [partialD_comp_reflect hφd j k y, ← mul_assoc, reflectSign_mul_self, one_mul]
  -- Both sides move by the same change of variables.
  have hleft : ∫ x in reflectLI j ⁻¹' B, u (reflectLI j x) * partialD k φ x
      = ∫ y in B, u y * partialD k φ (reflectLI j y) := by
    have := (measurePreserving_reflectLI j).setIntegral_preimage_emb
      (measurableEmbedding_reflectLI j)
      (fun y => u y * partialD k φ (reflectLI j y)) B
    simpa only [reflectLI_involutive] using this
  have hright : ∫ x in reflectLI j ⁻¹' B, g k (reflectLI j x) * φ x
      = ∫ y in B, g k y * φ (reflectLI j y) := by
    have := (measurePreserving_reflectLI j).setIntegral_preimage_emb
      (measurableEmbedding_reflectLI j)
      (fun y => g k y * φ (reflectLI j y)) B
    simpa only [reflectLI_involutive] using this
  have hmid : ∫ y in B, u y * partialD k φ (reflectLI j y)
      = reflectSign j k * ∫ y in B, u y * partialD k (fun z => φ (reflectLI j z)) y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    change u y * partialD k φ (reflectLI j y)
      = reflectSign j k * (u y * partialD k (fun z => φ (reflectLI j z)) y)
    rw [hpd y]; ring
  have hfin : ∫ x in reflectLI j ⁻¹' B,
        reflectSign j k * g k (reflectLI j x) * φ x
      = reflectSign j k * ∫ x in reflectLI j ⁻¹' B, g k (reflectLI j x) * φ x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change reflectSign j k * g k (reflectLI j x) * φ x
      = reflectSign j k * (g k (reflectLI j x) * φ x)
    ring
  rw [hleft, hmid, hkey, hfin, hright]
  ring

/-- **Reflection preserves every `Lᵖ` seminorm**, the reflection being measure preserving. This
is what makes the bound on an extension by reflection a bound with no loss. -/
theorem eLpNorm_comp_reflect {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : AEStronglyMeasurable f volume) (j : Fin d) (p : ℝ≥0∞) :
    eLpNorm (fun y => f (reflectLI j y)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_reflectLI j)

end EllipticPdes.Extension

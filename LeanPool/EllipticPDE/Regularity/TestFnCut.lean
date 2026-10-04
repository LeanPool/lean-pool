/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Caccioppoli


/-!
# Cutting a test function against a cutoff

The localised moves of `EllipticPdes.Regularity.DifferentiatedEquation` are stated for test
functions supported inside the region `V` where the weak-derivative data lives. The terms of
higher interior regularity (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem
2) instead pair against a test function on the whole domain, each term with a factor supported
inside a compact `K ⊆ V`. Replacing the test function `φ` by `χ · φ` for a cutoff `χ`
identically `1` near `K` and supported in `V` brings the two shapes together.

The replacement is invisible to any factor supported in `K`: there `χ = 1` and `∂ⱼχ = 0`, so
the Leibniz expansion of `∂ⱼ(χ φ)` collapses to `∂ⱼφ`. Both facts need `χ = 1` on a
*neighbourhood* of `K`, which is the form `CutoffTower` (`EllipticPdes.Regularity.CutoffTower`)
records its three cutoffs in.

## Main declarations

* `partialD_eq_zero_of_eventually_one`: a function identically `1` near `K` has vanishing
  partials on `K`.
* `isTestFn_cut`: `χ · φ` is a test function on `V` whenever `χ` is a compactly supported
  smooth function with `tsupport χ ⊆ V` and `φ` is smooth.
* `mul_cut_eq`, `mul_partialD_cut_eq`: the pointwise cutting identities.
* `setIntegral_mul_cut_eq`, `setIntegral_mul_partialD_cut_eq`: their integral forms, for a
  weight vanishing almost everywhere off `K`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace Topology

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Two pointwise facts -/

/-- **Vanishing partials on `K` of a cutoff identically `1` near it.** At a point of `K` the
function agrees with the constant `1` on a whole neighbourhood, so its Fréchet derivative is
the derivative of a constant. -/
theorem partialD_eq_zero_of_eventually_one {K : Set (EuclideanSpace ℝ (Fin d))}
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ∀ᶠ x in 𝓝ˢ K, χ x = 1)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ K) (j : Fin d) : partialD j χ x = 0 := by
  have hloc : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := nhds_le_nhdsSet hx hχ
  have hfd : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) x :=
    hloc.fderiv_eq
  simp [partialD, hfd]

/-- **Cut of a smooth function as a test function on `V`.** Smoothness is `ContDiff.mul`,
compact support comes from `χ`, and the support inclusion is the one `χ` has. Unlike
`isTestFn_mul`, the second factor need not be compactly supported. -/
theorem isTestFn_cut {V : Set (EuclideanSpace ℝ (Fin d))}
    {χ φ : EuclideanSpace ℝ (Fin d) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcs : HasCompactSupport χ) (hχV : tsupport χ ⊆ V) (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) :
    IsTestFn V (fun x => χ x * φ x) :=
  ⟨hχc.mul hφc, HasCompactSupport.mul_right (f := χ) (f' := φ) hχcs,
    (closure_mono (Function.support_mul_subset_left χ φ)).trans hχV⟩

/-- **Cutting is invisible to a weight supported in `K`**, at the level of the function
itself: `w · (χ φ) = w · φ` pointwise, because `χ = 1` on `K ⊇ tsupport w` and `w` vanishes
off its support. -/
theorem mul_cut_eq {K : Set (EuclideanSpace ℝ (Fin d))}
    {χ φ w : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ∀ᶠ x in 𝓝ˢ K, χ x = 1)
    (hw : tsupport w ⊆ K) (x : EuclideanSpace ℝ (Fin d)) :
    w x * (χ x * φ x) = w x * φ x := by
  by_cases hx : x ∈ tsupport w
  · rw [hχ.self_of_nhdsSet x (hw hx), one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- **Cutting is invisible to a weight supported in `K`**, at the level of the gradient:
`w · ∂ⱼ(χ φ) = w · ∂ⱼφ` pointwise. The Leibniz rule splits `∂ⱼ(χ φ)` into `χ ∂ⱼφ + (∂ⱼχ) φ`,
and on `K` the first factor is `∂ⱼφ` while the second vanishes. -/
theorem mul_partialD_cut_eq {K : Set (EuclideanSpace ℝ (Fin d))}
    {χ φ w : EuclideanSpace ℝ (Fin d) → ℝ} (hχd : Differentiable ℝ χ)
    (hφd : Differentiable ℝ φ) (hχ : ∀ᶠ x in 𝓝ˢ K, χ x = 1) (hw : tsupport w ⊆ K)
    (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    w x * partialD j (fun y => χ y * φ y) x = w x * partialD j φ x := by
  by_cases hx : x ∈ tsupport w
  · have hxK : x ∈ K := hw hx
    rw [congrFun (partialD_mul hχd hφd j) x,
      partialD_eq_zero_of_eventually_one hχ hxK j, hχ.self_of_nhdsSet x hxK]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-! ### Integral forms for an almost-everywhere supported weight -/

/-- **Integral form of `mul_cut_eq`.** The weight is only required to vanish almost
everywhere off `K`, which is the form an `L²` class supported in `K` supplies. -/
theorem setIntegral_mul_cut_eq {S K : Set (EuclideanSpace ℝ (Fin d))}
    {χ φ w : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ∀ᶠ x in 𝓝ˢ K, χ x = 1)
    (hw : ∀ᵐ x ∂(volume.restrict S), x ∉ K → w x = 0) :
    ∫ x in S, w x * (χ x * φ x) = ∫ x in S, w x * φ x := by
  refine integral_congr_ae ?_
  filter_upwards [hw] with x hx
  by_cases hxK : x ∈ K
  · rw [hχ.self_of_nhdsSet x hxK, one_mul]
  · rw [hx hxK, zero_mul, zero_mul]

/-- **Integral form of `mul_partialD_cut_eq`.** The weight is only required to vanish
almost everywhere off `K`. -/
theorem setIntegral_mul_partialD_cut_eq {S K : Set (EuclideanSpace ℝ (Fin d))}
    {χ φ w : EuclideanSpace ℝ (Fin d) → ℝ} (hχd : Differentiable ℝ χ)
    (hφd : Differentiable ℝ φ) (hχ : ∀ᶠ x in 𝓝ˢ K, χ x = 1)
    (hw : ∀ᵐ x ∂(volume.restrict S), x ∉ K → w x = 0) (j : Fin d) :
    ∫ x in S, w x * partialD j (fun y => χ y * φ y) x = ∫ x in S, w x * partialD j φ x := by
  refine integral_congr_ae ?_
  filter_upwards [hw] with x hx
  by_cases hxK : x ∈ K
  · rw [congrFun (partialD_mul hχd hφd j) x,
      partialD_eq_zero_of_eventually_one hχ hxK j, hχ.self_of_nhdsSet x hxK]
    ring
  · rw [hx hxK, zero_mul, zero_mul]

end EllipticPdes.Regularity

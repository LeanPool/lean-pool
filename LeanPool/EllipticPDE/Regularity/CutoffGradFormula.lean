/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.ExtendCutoff
public import LeanPool.EllipticPDE.Regularity.WeakDerivUnique
public import LeanPool.EllipticPDE.Regularity.CutoffDeriv


/-!
# Gradient of a cut-off function in closed form

`EllipticPdes.Regularity.interior_cutoffGrad_mem_H01` puts `ξ·∂_ℓu` in `H₀¹(Ω)` and says that
the gradient coordinates of the resulting element are its weak derivatives. It says nothing
about what they are, because the element is produced as a weak limit of difference quotients and
the limit has no formula.

Evans's step 3 needs the formula. Expanding `B[ξ·∂_ℓu, w]` asks for `∂ᵢ(ξ·∂_ℓu)` as a sum of a
term where the derivative lands on the cutoff and a term where it lands on the solution, and
only the second meets the differentiated equation.

The Leibniz rule across the cutoff supplies the candidate, and uniqueness of the whole-space
weak derivative identifies it with the coordinate. `HasWeakDeriv.unique` is the whole-space
statement, which is why `hasWeakDeriv_extend_mulTest` is stated on the whole space rather than
on `Ω`.

## Main declarations

* `extendL2_restrictL2_extendL2_ae`: cutting an `L²(Ω)` class down to `W ⊆ Ω` and extending
  again is the indicator of `W`.
* `extendL2_mulTest_eq`: a cut-off class is the cut-off restriction.
* `extendL2_cutoffGrad_eq`: the gradient coordinates of the cut-off element, in closed form.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Cutting down and extending again is the indicator.** For `W ⊆ Ω`, restricting an `L²(Ω)`
class to `W` and extending by zero gives the indicator of `W` applied to the class. -/
theorem extendL2_restrictL2_extendL2_ae {Ω W : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (hWΩ : W ⊆ Ω) (g : L2D Ω) :
    (extendL2 hWm (restrictL2 (Ω := W) (extendL2 hΩm g)) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] Set.indicator W (fun x => (g x : ℝ)) := by
  have hres : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ W →
      (restrictL2 (Ω := W) (extendL2 hΩm g) x : ℝ) = (extendL2 hΩm g x : ℝ) :=
    (ae_restrict_iff' hWm).mp (coeFn_restrictL2 (Ω := W) (extendL2 hΩm g))
  filter_upwards [coeFn_extendL2 hWm (restrictL2 (Ω := W) (extendL2 hΩm g)),
    coeFn_extendL2 hΩm g, hres] with x h1 h2 h3
  rw [h1]
  by_cases hxW : x ∈ W
  · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW, h3 hxW, h2,
      Set.indicator_of_mem (hWΩ hxW)]
  · rw [Set.indicator_of_notMem hxW, Set.indicator_of_notMem hxW]

/-- **Cut-off class as the cut-off restriction.** For a cutoff supported in `W ⊆ Ω`, the
whole-space extension of `ξ·g` is the whole-space extension of `ξ` against the restriction of
`g` to `W`. The cutoff kills everything outside `W`, so nothing is lost.

This is the function coordinate of `extendL2_cutoffGrad_eq`, stated on its own because the
zeroth-order block of the induction step needs exactly it. -/
theorem extendL2_mulTest_eq {Ω W : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hξΩ : IsTestFn Ω ξ) (hξW : IsTestFn W ξ) (g : L2D Ω) :
    extendL2 hΩm (mulTest hξΩ g)
      = extendL2 hWm (mulTest hξW (restrictL2 (Ω := W) (extendL2 hΩm g))) := by
  refine Lp.ext ?_
  have hmtΩ : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ Ω →
      (mulTest hξΩ g x : ℝ) = ξ x * (g x : ℝ) :=
    (ae_restrict_iff' hΩm).mp (mulTest_coeFn hξΩ g)
  have hmtW : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ W →
      (mulTest hξW (restrictL2 (Ω := W) (extendL2 hΩm g)) x : ℝ)
        = ξ x * (restrictL2 (Ω := W) (extendL2 hΩm g) x : ℝ) :=
    (ae_restrict_iff' hWm).mp (mulTest_coeFn hξW _)
  have hrW : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ W →
      (restrictL2 (Ω := W) (extendL2 hΩm g) x : ℝ) = (extendL2 hΩm g x : ℝ) :=
    (ae_restrict_iff' hWm).mp (coeFn_restrictL2 (Ω := W) (extendL2 hΩm g))
  filter_upwards [coeFn_extendL2 hΩm (mulTest hξΩ g),
    coeFn_extendL2 hWm (mulTest hξW (restrictL2 (Ω := W) (extendL2 hΩm g))),
    hmtΩ, hmtW, hrW, coeFn_extendL2 hΩm g] with x h1 h2 h3 h4 h5 h6
  rw [h1, h2]
  by_cases hxW : x ∈ W
  · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem (hWΩ hxW), h3 (hWΩ hxW), h4 hxW,
      h5 hxW, h6, Set.indicator_of_mem (hWΩ hxW)]
  · rw [Set.indicator_of_notMem hxW]
    have hξx : ξ x = 0 := image_eq_zero_of_notMem_tsupport (fun hc => hxW (hξW.2.2 hc))
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ, h3 hxΩ, hξx, zero_mul]
    · rw [Set.indicator_of_notMem hxΩ]

/-- **Gradient of a cut-off class in closed form.** Let `ξ` be a cutoff supported in
`W ⊆ Ω`, let `g ∈ L²(Ω)` have weak derivatives `Dg i` on `W`, and let `Uamb` be an ambient
element whose function coordinate is `ξ·g` and whose gradient coordinates are the weak
derivatives of that product. Then each gradient coordinate is `(∂ᵢξ)·g + ξ·(∂ᵢg)`.

The Leibniz rule across the cutoff (`hasWeakDeriv_extend_mulTest`) shows the right-hand side to
be a weak `i`-derivative of `ξ·g`, and the coordinate is one by hypothesis, so
`HasWeakDeriv.unique` identifies them. Both sides are extensions by zero from `W`, which is
where the derivative of `g` is known and where the cutoff lives. -/
theorem extendL2_cutoffGrad_eq {Ω W : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hξΩ : IsTestFn Ω ξ) (hξW : IsTestFn W ξ)
    (g : L2D Ω) {Uamb : H1amb Ω}
    (hUgrad : ∀ i : Fin d,
      HasWeakDeriv i (extendL2 hΩm (mulTest hξΩ g)) (extendL2 hΩm (Uamb i.succ)))
    {Dg : Fin d → L2D W}
    (hDg : ∀ i : Fin d,
      HasWeakDerivOn W i (restrictL2 (Ω := W) (extendL2 hΩm g)) (Dg i)) (i : Fin d) :
    extendL2 hΩm (Uamb i.succ)
      = extendL2 hWm (mulTest (isTestFn_partialD hξW i)
            (restrictL2 (Ω := W) (extendL2 hΩm g)) + mulTest hξW (Dg i)) := by
  set p : L2D W := restrictL2 (Ω := W) (extendL2 hΩm g) with hpdef
  have hEp := extendL2_restrictL2_extendL2_ae hΩm hWm hWΩ g
  -- The function coordinate, read through `W`.
  have hq : (extendL2 hΩm (mulTest hξΩ g) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x => ξ x * (extendL2 hWm p x : ℝ) := by
    have hmt : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ Ω →
        (mulTest hξΩ g x : ℝ) = ξ x * (g x : ℝ) :=
      (ae_restrict_iff' hΩm).mp (mulTest_coeFn hξΩ g)
    filter_upwards [coeFn_extendL2 hΩm (mulTest hξΩ g), hEp, hmt] with x h1 h2 h3
    rw [h1, h2]
    by_cases hxW : x ∈ W
    · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem (hWΩ hxW), h3 (hWΩ hxW)]
    · rw [Set.indicator_of_notMem hxW, mul_zero]
      have hξx : ξ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hc => hxW (hξW.2.2 hc))
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ, h3 hxΩ, hξx, zero_mul]
      · rw [Set.indicator_of_notMem hxΩ]
  -- The candidate derivative, read through `W`.
  have hq' : (extendL2 hWm (mulTest (isTestFn_partialD hξW i) p + mulTest hξW (Dg i))
        : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x =>
        partialD i ξ x * (extendL2 hWm p x : ℝ) + ξ x * (extendL2 hWm (Dg i) x : ℝ) := by
    have hsum : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ W →
        ((mulTest (isTestFn_partialD hξW i) p + mulTest hξW (Dg i)) x : ℝ)
          = partialD i ξ x * (p x : ℝ) + ξ x * (Dg i x : ℝ) := by
      refine (ae_restrict_iff' hWm).mp ?_
      filter_upwards [Lp.coeFn_add (mulTest (isTestFn_partialD hξW i) p) (mulTest hξW (Dg i)),
        mulTest_coeFn (isTestFn_partialD hξW i) p, mulTest_coeFn hξW (Dg i)] with x hadd h1 h2
      rw [hadd, Pi.add_apply, h1, h2]
    filter_upwards [coeFn_extendL2 hWm (mulTest (isTestFn_partialD hξW i) p
        + mulTest hξW (Dg i)),
      coeFn_extendL2 hWm p, coeFn_extendL2 hWm (Dg i), hsum] with x h1 h2 h3 h4
    rw [h1, h2, h3]
    by_cases hxW : x ∈ W
    · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW, Set.indicator_of_mem hxW, h4 hxW]
    · rw [Set.indicator_of_notMem hxW, Set.indicator_of_notMem hxW,
        Set.indicator_of_notMem hxW, mul_zero, mul_zero, add_zero]
  exact HasWeakDeriv.unique (hUgrad i)
    (hasWeakDeriv_extend_mulTest hWm hξW (hDg i) hq hq')

end EllipticPdes.Regularity

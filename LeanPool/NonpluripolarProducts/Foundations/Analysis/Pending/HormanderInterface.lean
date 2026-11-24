/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LeviWirtinger
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Hörmander's `L²` estimate for `∂bar` on convex domains: the statement

Weak `∂bar` is taken in the sense of distributions, with test functions smooth and compactly
supported in the domain:

* `WeakDbarEq D u f`: `∂bar_j u = f_j` on `D`, i.e. `∫ u ∂bar_j h = - ∫ f_j h` for all tests `h`;
* `WeakDbarClosed D f`: `∂bar_j f_k = ∂bar_k f_j` on `D`.

`HormanderL2Estimate n` is the form of Hörmander's theorem used for the Ohsawa--Takegoshi
extension (Hörmander, *An introduction to complex analysis in several variables*, §4.1--4.2,
with the cutoff weights of Lemma 4.1.3).  For every bounded convex `D` and compact `K ⊆ D`
and `t > 0` there are a smaller open set `D' ⊇ K` and two continuous shifts `0 ≤ lam₁ ≤ lam₂` of
    the weight,
vanishing near `K`, such that for every weight `Φ` smooth and plurisubharmonic on `D`:

* every `∂bar`-closed `f ∈ L²(D', e^{-Φ-lam₂})` whose pointwise Levi bound
  `|⟨f, ξ⟩|² ≤ g · Levi Φ (ξ)` (with `g ≥ 0`) has `∫ g e^{-Φ-lam₁} < ∞` is `∂bar u` for some
  `u ∈ L²(D', e^{-Φ-lam₁})` orthogonal to all `L²` weakly holomorphic functions; and
* every such orthogonal solution satisfies `∫ |u|² e^{-Φ-lam₁} ≤ (1 + t) ∫ g e^{-Φ-lam₁}`.

The data `D', lam₁, lam₂` may depend on a parameter `t > 0`.  The constant must be allowed to
approach `1`: the twisted estimate of Berndtsson--Charpentier--Chen subtracts a term whose
coefficient tends to `1` near the hyperplane.

This file only states the property.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate ContDiff

namespace SGPT.Foundations.Analysis.Pending.Hormander

noncomputable section

open FirstPass CauchyGreen

variable {n : ℕ}

/-- The `j`-th coordinate vector of `ℂⁿ`. -/
abbrev coordVec (j : Fin n) : ComplexModel n := EuclideanSpace.single j 1

/-- Smooth test functions compactly supported in `D`. -/
def IsTestFunctionOn (D : Set (ComplexModel n)) (h : ComplexModel n → ℂ) : Prop :=
  ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ D

/-- The measure `e^{-w} dλ` restricted to `D`. -/
def weightedVolume (D : Set (ComplexModel n)) (w : ComplexModel n → ℝ) :
    Measure (ComplexModel n) :=
  (volume.restrict D).withDensity fun x ↦ ENNReal.ofReal (Real.exp (-w x))

/-- `∂bar u = f` on `D` in the sense of distributions. -/
def WeakDbarEq (D : Set (ComplexModel n)) (u : ComplexModel n → ℂ)
    (f : Fin n → ComplexModel n → ℂ) : Prop :=
  ∀ h, IsTestFunctionOn D h → ∀ j,
    ∫ x, u x * dbarDir (coordVec j) h x = - ∫ x, f j x * h x

/-- `∂bar f = 0` on `D` in the sense of distributions, for a `(0,1)`-form `f`. -/
def WeakDbarClosed (D : Set (ComplexModel n)) (f : Fin n → ComplexModel n → ℂ) : Prop :=
  ∀ h, IsTestFunctionOn D h → ∀ j k,
    ∫ x, (f k x * dbarDir (coordVec j) h x - f j x * dbarDir (coordVec k) h x) = 0

/-- **Hörmander's `L²` estimate on convex domains**, in the form used for Ohsawa--Takegoshi. -/
def HormanderL2Estimate (n : ℕ) : Prop :=
  ∀ D : Set (ComplexModel n), IsOpen D → Convex ℝ D → Bornology.IsBounded D →
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D → ∀ t : ℝ, 0 < t →
  ∃ (D' U : Set (ComplexModel n)) (lam₁ lam₂ : ComplexModel n → ℝ),
    IsOpen D' ∧ Convex ℝ D' ∧ closure D' ⊆ D ∧ IsOpen U ∧ K ⊆ U ∧ U ⊆ D' ∧
    ContinuousOn lam₁ D' ∧ ContinuousOn lam₂ D' ∧
    (∀ x ∈ D', 0 ≤ lam₁ x ∧ lam₁ x ≤ lam₂ x) ∧ (∀ x ∈ U, lam₁ x = 0 ∧ lam₂ x = 0) ∧
    ∀ Φ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ Φ D → (∀ x ∈ D, ∀ ξ, 0 ≤ leviForm Φ x ξ) →
    ∀ f : Fin n → ComplexModel n → ℂ,
      (∀ j, MemLp (f j) 2 (weightedVolume D' fun x ↦ Φ x + lam₂ x)) → WeakDbarClosed D' f →
    ∀ g : ComplexModel n → ℝ, (∀ x ∈ D', 0 ≤ g x) →
      (∀ x ∈ D', ∀ ξ : Fin n → ℂ,
        ‖∑ j, conj (ξ j) * f j x‖ ^ 2 ≤ g x * leviForm Φ x (∑ j, ξ j • coordVec j)) →
      Integrable (fun x ↦ g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') →
    (∃ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) ∧
        WeakDbarEq D' u f ∧
        ∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
          WeakDbarEq D' h 0 →
          ∫ x in D', conj (h x) * u x * Real.exp (-(Φ x + lam₁ x)) = 0) ∧
    ∀ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
      WeakDbarEq D' u f →
      (∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
          WeakDbarEq D' h 0 →
          ∫ x in D', conj (h x) * u x * Real.exp (-(Φ x + lam₁ x)) = 0) →
      ∫ x in D', ‖u x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x)) ≤
        (1 + t) * ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x))

end

end SGPT.Foundations.Analysis.Pending.Hormander

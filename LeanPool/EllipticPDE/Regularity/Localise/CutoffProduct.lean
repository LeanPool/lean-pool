/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.LowerOrderWkInfty
public import LeanPool.EllipticPDE.Regularity.CutoffTower


/-!
# Cutting a locally smooth function off to a globally smooth one

The interior-regularity chain runs on a `FullEllipticOp`, whose coefficients are global on
`EuclideanSpace ℝ (Fin d)`, essentially bounded, and asked for no more. A datum smooth on an
open set `U` alone, or coefficients smooth on `U` alone with no bound off it, do not meet that
shape directly. Multiplying by a smooth cutoff supported in `U` and equal to `1` near the region
of interest repairs this: the product is globally smooth, compactly supported, and so lies in
`W^{k,∞}` at every order, with no bound needed on the factor itself.

This file supplies that cutting-off step in general, for a single scalar function; `LocalOp`
applies it entrywise to build a global operator out of one with coefficients smooth on `U` alone.

## Main declarations

* `contDiff_mul_of_contDiffOn`: a function smooth on `U`, cut off by a test function of `U`, is
  globally smooth.
* `hasCompactSupport_mul`: the product has compact support.
* `exists_iteratedFDeriv_bound`: a smooth compactly supported function has every iterated
  derivative uniformly bounded.
* `exists_iteratedFDeriv_bound_const_add`: the same for a constant shift of one, at every
  positive order.
* `nonempty_isWkInfty`: a smooth compactly supported function lies in `W^{k,∞}` at every order.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A function smooth on an open `U`, multiplied by a test function supported in `U`, is
globally smooth: away from the topological support of the cutoff the product is eventually zero,
and on that support the cutoff itself is smooth wherever `g` is, since the support sits inside
`U`. -/
theorem contDiff_mul_of_contDiffOn {U : Set E} (hU : IsOpen U) {χ g : E → ℝ}
    (hχ : IsTestFn U χ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ.1.contDiffAt).mul (hg.contDiffAt (hU.mem_nhds (hχ.2.2 hx)))
  · have h0 : χ =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).1 hx
    have h1 : (fun y => χ y * g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h1

/-- The product of a test function with any function has compact support: the topological
support of the product sits inside that of the cutoff. -/
theorem hasCompactSupport_mul {U : Set E} {χ g : E → ℝ} (hχ : IsTestFn U χ) :
    HasCompactSupport (fun x => χ x * g x) :=
  hχ.2.1.mul_right (f' := g)

/-- A smooth compactly supported function has every iterated derivative bounded, with a
nonnegative bound at each order: the derivative is continuous and vanishes off a compact set, so
it is bounded, and the bound is truncated at `0` to be usable at every order uniformly. -/
theorem exists_iteratedFDeriv_bound {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ m x, ‖iteratedFDeriv ℝ m g x‖ ≤ B m := by
  have h : ∀ m : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ m g x‖ ≤ C := fun m =>
    (hc.iteratedFDeriv m).exists_bound_of_continuous
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  choose C hC using h
  exact ⟨fun m => max (C m) 0, fun m => le_max_right _ _,
    fun m x => (hC m x).trans (le_max_left _ _)⟩

/-- A constant plus a smooth compactly supported function has every iterated derivative of
positive order bounded: the constant contributes nothing past order zero, so the bound of
`exists_iteratedFDeriv_bound` for the compactly supported part serves unchanged. -/
theorem exists_iteratedFDeriv_bound_const_add {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (c : ℝ) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ m, 1 ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ m (fun y => c + g y) x‖ ≤ B m := by
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_bound hg hc
  refine ⟨B, hB0, fun m hm x => ?_⟩
  have hadd : iteratedFDeriv ℝ m (fun y => c + g y) x
      = iteratedFDeriv ℝ m (fun _ : E => c) x + iteratedFDeriv ℝ m g x :=
    iteratedFDeriv_add_apply contDiffAt_const
      ((hg.of_le (by exact_mod_cast le_top)).contDiffAt)
  rw [hadd, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
  exact hB m x

/-- A smooth compactly supported function lies in `W^{k,∞}` at every order: its classical
iterated partials serve as the weak-derivative family, and `exists_iteratedFDeriv_bound` supplies
the uniform bound each order needs. -/
theorem nonempty_isWkInfty {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (k : ℕ) : Nonempty (IsWkInfty g k) := by
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_bound hg hc
  exact ⟨IsWkInfty.ofContDiff (hg.of_le (by exact_mod_cast le_top)) hB0
    (fun m _ x => hB m x)⟩

end EllipticPdes.Regularity

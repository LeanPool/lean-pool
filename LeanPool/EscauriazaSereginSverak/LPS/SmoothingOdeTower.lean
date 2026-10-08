/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Time regularity of a solution of an evolution equation in a tower of Banach spaces

`prop:lps-smoothing`: if a curve solves `u' = N(u)` in integral form in every space of a
tower `X_m`, with `N` smooth from `X_{m+2}` to `X_m`, then the curve is `C^∞` on the closed
interval in every `X_m`, with one-sided derivatives at the endpoints.
-/

public section

open MeasureTheory Set Filter Topology


noncomputable section

namespace ESS

/-- A curve in a Banach space that is a primitive of a function continuous on `[a,b]` on all
subintervals is differentiable within `[a,b]` with that derivative. -/
theorem lps_hasDerivWithinAt_Icc_of_integral_banach {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hg : ContinuousOn g (Icc a b))
    (hid : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → f t - f s = ∫ τ in s..t, g τ) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  intro t ht
  let G : ℝ → E := fun τ => g (Set.projIcc a b hab.le τ : ℝ)
  have hGc : Continuous G :=
    hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun τ => (Set.projIcc a b hab.le τ).2)
  have hGg : ∀ τ ∈ Icc a b, G τ = g τ := by
    intro τ hτ
    simp only [G, Set.projIcc_of_mem hab.le hτ]
  let F : ℝ → E := fun u => f a + ∫ τ in a..u, G τ
  have hF : ∀ u, HasDerivAt F (G u) u := fun u =>
    ((hGc.integral_hasStrictDerivAt a u).hasDerivAt).const_add (f a)
  have hfF : ∀ u ∈ Icc a b, f u = F u := by
    intro u hu
    have h1 := hid a ⟨le_rfl, hab.le⟩ u hu hu.1
    have h2 : ∫ τ in a..u, G τ = ∫ τ in a..u, g τ := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le hu.1] at hτ
      exact hGg τ ⟨hτ.1, hτ.2.trans hu.2⟩
    simp only [F, h2]
    rw [← h1]
    abel
  have := (hF t).hasDerivWithinAt (s := Icc a b)
  rw [hGg t ht] at this
  exact this.congr (fun y hy => hfF y hy) (hfF t ht)

/-- Tower of Banach spaces: a curve solving the evolution equation in integral form in every
space is `C^n` on the closed interval in every space, for every finite `n`
(`prop:lps-smoothing`). -/
theorem lps_ode_tower_contDiffOn {a b : ℝ} (hab : a < b) {X : ℕ → Type*}
    [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)] [∀ m, CompleteSpace (X m)]
    (N : ∀ m, X (m + 2) → X m) (hN : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (N m))
    (u : ∀ m, ℝ → X m) (hcont : ∀ m, ContinuousOn (u m) (Icc a b))
    (hint : ∀ m, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      u m t - u m s = ∫ τ in s..t, N m (u (m + 2) τ)) :
    ∀ n : ℕ, ∀ m, ContDiffOn ℝ n (u m) (Icc a b) := by
  intro n
  induction n with
  | zero => exact fun m => contDiffOn_zero.mpr (hcont m)
  | succ n ih =>
      intro m
      have huniq : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
      have hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt (u m) (N m (u (m + 2) t)) (Icc a b) t := by
        refine lps_hasDerivWithinAt_Icc_of_integral_banach hab ?_ (hint m)
        exact ((hN m).continuous.comp_continuousOn (hcont (m + 2)))
      have hcomp : ContDiffOn ℝ n (fun t => N m (u (m + 2) t)) (Icc a b) :=
        ((hN m).of_le (by exact_mod_cast le_top)).comp_contDiffOn (ih (m + 2))
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin huniq]
      refine ⟨fun t ht => (hderiv t ht).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
      refine hcomp.congr fun t ht => ?_
      exact (hderiv t ht).derivWithin (huniq t ht)

end ESS

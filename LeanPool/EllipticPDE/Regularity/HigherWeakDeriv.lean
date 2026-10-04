/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Interior


/-!
# Iterated weak derivatives on a region

The interior `H²` estimate `EllipticPdes.Regularity.interior_H2_estimate` produces one weak
derivative of one weak derivative, indexed by an explicit pair `(k, i)`. Higher regularity
iterates that step, so the pair has to become a list and the statement has to quantify over
its length. This file supplies the indexed object.

`HasIteratedWeakDerivOn V k u` names a family `D : List (Fin d) → L²(V)` with `D [] = u` and
each `D (l :: α)` a weak `l`-derivative of `D α`, for every list shorter than `k`. It is the
`L²`-level reading of `u ∈ H^k(V)`, given as data rather than as an existential, so that a proof
can name a particular derivative and hand it on.

## Choice of a list of directions

The same choice as in `EllipticPdes.Regularity.IsWkInftyCoeff`, and for the same reason: one
step of the recursion is `cons`. A multi-index in `Fin d →₀ ℕ` would need equality of mixed
partials before the recursion could even be stated, and that equality is a theorem about the
family rather than part of its definition. Nothing here presumes it.

## Main declarations

* `HasIteratedWeakDerivOn`: weak derivatives up to order `k` on `V`, given as a family.
* `HasIteratedWeakDerivOn.mono`: an order-`k` family is an order-`l` family for `l ≤ k`.
* `HasIteratedWeakDerivOn.deriv`: the order-`k` family of a first derivative, extracted from an
  order-`k+1` family by appending the direction on the right. This is the step the induction
  of Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem VIII.3.2
  (p. 65) runs on.
* `IteratedL2Bound`: a uniform bound on every member of the family up to order `k`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))} {k l : ℕ}

/-- **Iterated weak derivatives on a region.** A family of `L²(V)` classes indexed by lists of
directions, with the empty list the function itself and each `cons` a weak derivative of its
parent. Giving the family as data rather than asserting existence at each order lets a consumer
name `D [i, j]` and pass it on, which the induction of Guo, *Partial Differential Equations I
and II* (Course Lecture Notes), Theorem VIII.3.2 (p. 65) requires. -/
structure HasIteratedWeakDerivOn (V : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) (u : L2D V)
    where
  /-- The chosen representative of the iterated weak derivative along a list of directions. -/
  D : List (Fin d) → L2D V
  /-- The empty list of directions is the function itself. -/
  D_nil : D [] = u
  /-- Each successive entry is a weak derivative of its parent, up to order `k`. -/
  D_step : ∀ (m : Fin d) (α : List (Fin d)), α.length < k →
    HasWeakDerivOn V m (D α) (D (m :: α))

namespace HasIteratedWeakDerivOn

variable {u : L2D V}

/-- Every `L²` class has weak derivatives up to order zero, vacuously: the family is constant
and `D_step` is asked of no list. -/
def zero (u : L2D V) : HasIteratedWeakDerivOn V 0 u where
  D := fun _ => u
  D_nil := rfl
  D_step := fun _ _ h => absurd h (Nat.not_lt_zero _)

/-- An order-`k` family is an order-`l` family for every `l ≤ k`: the family is inherited and
`D_step` is asked of fewer lists. -/
def mono (hu : HasIteratedWeakDerivOn V k u) (hlk : l ≤ k) :
    HasIteratedWeakDerivOn V l u where
  D := hu.D
  D_nil := hu.D_nil
  D_step m α hα := hu.D_step m α (lt_of_lt_of_le hα hlk)

/-- **Transport along an equality of the subject.** The family is unchanged; only the proof
that its empty entry is the function moves. Stated because the induction reaches the derivative
of `u` through a cutoff, whose function coordinate agrees with the derivative on the region of
interest without being the same term. -/
def congr {g : L2D V} (hu : HasIteratedWeakDerivOn V k u) (h : u = g) :
    HasIteratedWeakDerivOn V k g where
  D := hu.D
  D_nil := hu.D_nil.trans h
  D_step := hu.D_step

/-- **Induction step.** From weak derivatives up to order `k + 1` of `u`, the direction
`l` first derivative `D [l]` has weak derivatives up to order `k`, with family
`α ↦ D (α ++ [l])`. Appending on the right rather than consing on the left is what makes the
lengths line up: `(α ++ [l]).length < k + 1` is exactly `α.length < k`, so every step the new
family needs is a step the old family already has.

This is the reduction that turns Guo's Theorem VIII.3.2 into an induction on `k`: an
`H^{k+2}` conclusion for `u` is an `H^{k+1}` conclusion for each `∂_l u`, and `∂_l u` solves a
differentiated equation of the same form. -/
def deriv (hu : HasIteratedWeakDerivOn V (k + 1) u) (l : Fin d) :
    HasIteratedWeakDerivOn V k (hu.D [l]) where
  D := fun α => hu.D (α ++ [l])
  D_nil := by simp
  D_step m α hα := by
    have hlen : (α ++ [l]).length < k + 1 := by
      simpa [List.length_append] using Nat.succ_lt_succ hα
    simpa using hu.D_step m (α ++ [l]) hlen

/-- **First derivative two orders down.** The datum of the induction step multiplies
derivatives of the solution of order at most two, and asks each of them for `k` weak
derivatives of its own. Naming the two cases here rather than inlining them keeps the
definitional unfolding of `deriv` out of the assembly, where it is repeated a dozen times. -/
def deriv₁ (hu : HasIteratedWeakDerivOn V (k + 2) u) (i : Fin d) :
    HasIteratedWeakDerivOn V k (hu.D [i]) :=
  (hu.deriv i).mono (Nat.le_succ k)

/-- A second derivative, at two orders down. -/
def deriv₂ (hu : HasIteratedWeakDerivOn V (k + 2) u) (i m : Fin d) :
    HasIteratedWeakDerivOn V k (hu.D [m, i]) :=
  (hu.deriv i).deriv m

/-- The order-one family of a function with derivatives to order `k + 1` records a weak
derivative in every direction. -/
theorem hasWeakDerivOn_D_singleton (hu : HasIteratedWeakDerivOn V (k + 1) u) (m : Fin d) :
    HasWeakDerivOn V m u (hu.D [m]) := by
  have h := hu.D_step m [] (Nat.succ_pos k)
  rwa [hu.D_nil] at h

/-- The assembly a family is read off: the empty list is the function, and a nonempty list is
the family of its last direction's derivative, indexed by what remains. Reversing is what makes
the last direction visible, since `D_step` conses on the left. -/
def famAux (u : L2D V) (E : Fin d → List (Fin d) → L2D V) :
    List (Fin d) → L2D V
  | [] => u
  | (ℓ :: βr) => E ℓ βr.reverse

/-- **Inverse of `deriv`.** Weak derivatives in every direction, each with its own order-`k`
family, assemble into an order-`k + 1` family of the function itself. The index of the assembled
family reads `β ++ [ℓ]` as the `β`-entry of the family of `∂_ℓ u`, which is the convention
`deriv` uses in the other direction.

This is the step that brings the conclusion of the induction of Guo, *Partial Differential
Equations I and II* (Course Lecture Notes), Theorem VIII.3.2 (p. 65) back to the solution:
the induction hypothesis is applied to each `∂_ℓ u` and its conclusions are reassembled here. -/
def ofDeriv {u : L2D V} {Du : Fin d → L2D V} (hu : ∀ ℓ, HasWeakDerivOn V ℓ u (Du ℓ))
    (H : ∀ ℓ, HasIteratedWeakDerivOn V k (Du ℓ)) :
    HasIteratedWeakDerivOn V (k + 1) u where
  D α := famAux u (fun ℓ => (H ℓ).D) α.reverse
  D_nil := rfl
  D_step m α hα := by
    rcases hcase : α.reverse with _ | ⟨ℓ, βr⟩
    · have hαnil : α = [] := by simpa using congrArg List.reverse hcase
      subst hαnil
      change HasWeakDerivOn V m u ((H m).D [])
      rw [(H m).D_nil]
      exact hu m
    · have hlen : βr.reverse.length < k := by
        have h := congrArg List.length hcase
        simp only [List.length_reverse] at h
        simp only [List.length_reverse]
        simp only [List.length_cons] at h
        omega
      have h2 : famAux u (fun ℓ => (H ℓ).D) (m :: α).reverse
          = (H ℓ).D (m :: βr.reverse) := by
        rw [List.reverse_cons, hcase]
        change (H ℓ).D ((βr ++ [m]).reverse) = _
        simp
      rw [h2]
      exact (H ℓ).D_step m βr.reverse hlen

end HasIteratedWeakDerivOn

/-- **Uniform `L²` bound on an iterated family.** Every derivative up to order `k` is
bounded by `C` in `L²(V)`. Kept apart from `HasIteratedWeakDerivOn` so that existence and
estimate can be proved and consumed separately, matching the shape of
`interior_H2_estimate`, which returns the derivative and its bound as separate conjuncts. -/
def IteratedL2Bound {u : L2D V} (hu : HasIteratedWeakDerivOn V k u) (C : ℝ) : Prop :=
  ∀ α : List (Fin d), α.length ≤ k → ‖hu.D α‖ ≤ C

namespace IteratedL2Bound

variable {u : L2D V} {C C' : ℝ}

/-- A bound at order `k` bounds the function itself. -/
theorem norm_le {hu : HasIteratedWeakDerivOn V k u} (hC : IteratedL2Bound hu C) : ‖u‖ ≤ C := by
  have h := hC [] (Nat.zero_le k)
  rwa [hu.D_nil] at h

/-- A bound is inherited by any larger constant. -/
theorem mono_const {hu : HasIteratedWeakDerivOn V k u} (hC : IteratedL2Bound hu C)
    (hCC : C ≤ C') : IteratedL2Bound hu C' := fun α hα => (hC α hα).trans hCC

/-- Transport preserves the bound: the family is unchanged. -/
theorem congr {g : L2D V} {hu : HasIteratedWeakDerivOn V k u} {h : u = g}
    (hC : IteratedL2Bound hu C) : IteratedL2Bound (hu.congr h) C := hC

/-- A bound at order `k` restricts to a bound on the order-`l` family for `l ≤ k`. -/
theorem mono_order {hu : HasIteratedWeakDerivOn V k u} (hC : IteratedL2Bound hu C)
    (hlk : l ≤ k) : IteratedL2Bound (hu.mono hlk) C := fun α hα => hC α (hα.trans hlk)

/-- The bound is inherited by the family of a derivative. -/
theorem deriv {hu : HasIteratedWeakDerivOn V (k + 1) u} (hC : IteratedL2Bound hu C)
    (l : Fin d) : IteratedL2Bound (hu.deriv l) C := fun α hα =>
  hC (α ++ [l]) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- The bound is inherited by the family of a first derivative. -/
theorem deriv₁ {hu : HasIteratedWeakDerivOn V (k + 2) u} (hC : IteratedL2Bound hu C)
    (i : Fin d) : IteratedL2Bound (hu.deriv₁ i) C := fun α hα =>
  hC (α ++ [i]) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- The bound is inherited by the family of a second derivative. -/
theorem deriv₂ {hu : HasIteratedWeakDerivOn V (k + 2) u} (hC : IteratedL2Bound hu C)
    (i m : Fin d) : IteratedL2Bound (hu.deriv₂ i m) C := fun α hα =>
  hC ((α ++ [m]) ++ [i])
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- The bound on an assembled family, read off the function and each first derivative's
family. -/
theorem ofDeriv {Du : Fin d → L2D V} {hu : ∀ ℓ, HasWeakDerivOn V ℓ u (Du ℓ)}
    {H : ∀ ℓ, HasIteratedWeakDerivOn V k (Du ℓ)} (hC : ‖u‖ ≤ C)
    (hF : ∀ ℓ, IteratedL2Bound (H ℓ) C) :
    IteratedL2Bound (HasIteratedWeakDerivOn.ofDeriv hu H) C := by
  intro α hα
  rcases hcase : α.reverse with _ | ⟨ℓ, βr⟩
  · have hαnil : α = [] := by simpa using congrArg List.reverse hcase
    subst hαnil
    exact hC
  · have hlen : βr.reverse.length ≤ k := by
      have h := congrArg List.length hcase
      simp only [List.length_reverse, List.length_cons] at h
      simp only [List.length_reverse]
      omega
    change ‖HasIteratedWeakDerivOn.famAux u (fun ℓ => (H ℓ).D) α.reverse‖ ≤ C
    rw [hcase]
    exact hF ℓ βr.reverse hlen

end IteratedL2Bound

end EllipticPdes.Regularity

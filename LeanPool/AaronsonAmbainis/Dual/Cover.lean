/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith
public import LeanPool.AaronsonAmbainis.Dual.Sets
public import LeanPool.AaronsonAmbainis.Dual.Functional
public import LeanPool.AaronsonAmbainis.Dual.Core

/-!
# Duality between packings and rows

`Dual.exists_cover` is Proposition 6.7 (Duality) of the paper. `coverDuality : CoverDuality`
follows from it: `CoverDuality` is the same statement with the two side hypotheses `0 ≤ K` and
`t ∅ ≤ 0` (neither is needed: the zero packing gives `0 ≤ K`, and `t ∅ ≤ 0` is the conclusion at
`S = ∅`).

Proof of `Dual.exists_cover`. Let `P = Dual.massSet ι K = {a ≥ 0, ∑ a ≤ K}` and
`Q = Dual.slack t '' P`, the set of all slack vectors `S ↦ a(S) - t S`; the claim is that `Q`
meets the nonnegative orthant of `Finset ι → ℝ`. If not, the geometric Hahn–Banach theorem
(`geometric_hahn_banach_compact_closed`: `Q` is compact and convex, the orthant is closed and
convex) gives a continuous linear functional `φ` and reals `u < r` with `φ < u` on `Q` and
`r < φ` on the orthant. Then `r < 0`, the coefficients `κ_S = φ (e_S)` are nonnegative
(`Dual.coeff_nonneg`), `φ v = ∑_S κ_S v_S` (`Dual.functional_eq_sum`), and
`∑_S κ_S (a(S) - t_S) < u < 0` for all `a ∈ P`, which `Dual.no_separator` excludes.

In the paper the set `Q` is called `C`, and the vector `κ` is obtained from Lemma 6.6 (Separation
from the orthant), for which the paper gives a short direct proof; here Mathlib's geometric
Hahn–Banach theorem takes the place of that lemma.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

namespace Dual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linear-programming duality between fractional packings and rows: if every fractional packing
`κ` has `∑_S κ_S t_S ≤ K`, then some `a ≥ 0` of total mass at most `K` has `t_S ≤ a(S)` for
every `S`. -/
theorem exists_cover (t : Finset ι → ℝ) (K : ℝ)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i := by
  -- the zero packing gives `0 ≤ K`
  have hK : 0 ≤ K := by
    have h := hpack 0 (fun _ => le_rfl) (fun i => by simp)
    simpa using h
  by_contra hne
  -- the set `Q` of slack vectors misses the orthant
  have hdisj : Disjoint (slack t '' massSet ι K) (orthant ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ⟨ha0, haK⟩, rfl⟩ hv
    refine hne ⟨a, ha0, haK, fun S => ?_⟩
    have h : 0 ≤ ∑ i ∈ S, a i - t S := hv S
    linarith
  -- strict separation of the compact convex `Q` from the closed convex orthant
  obtain ⟨φ, u, r, hQ, hur, hV⟩ :=
    geometric_hahn_banach_compact_closed (slackImage_convex t K)
      (slackImage_isCompact t K) orthant_convex orthant_isClosed hdisj
  -- `0` lies in the orthant, so `r < 0`
  have hr : r < 0 := by
    have h0 := hV 0 (fun _ => le_rfl)
    rwa [map_zero] at h0
  -- the coefficients of `φ` are nonnegative
  have hκ : ∀ S : Finset ι, 0 ≤ φ (Pi.single S 1) :=
    fun S => coeff_nonneg φ r hV S
  -- the finite core
  refine no_separator t K hK hpack (fun S => φ (Pi.single S 1)) hκ (fun a ha0 haK => ?_)
  have h1 : φ (slack t a) < u := hQ (slack t a) ⟨a, ⟨ha0, haK⟩, rfl⟩
  rw [functional_eq_sum φ (slack t a)] at h1
  have h2 : ∑ S, φ (Pi.single S 1) * slack t a S
      = ∑ S, φ (Pi.single S 1) * (∑ i ∈ S, a i - t S) := rfl
  rw [h2] at h1
  linarith

end Dual

theorem coverDuality : CoverDuality :=
  fun _ _ _ t K _ _ hpack => Dual.exists_cover t K hpack

end AaronsonAmbainis

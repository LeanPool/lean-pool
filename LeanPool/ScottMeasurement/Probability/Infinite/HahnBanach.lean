/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Cone.Basic

/-!
# Hahn--Banach separation above a closed cone

This is the analytic step used in the reconstructed infinite version of
Scott's Theorem 4.1.  A closed convex set which is stable under translation
by a closed cone and avoids zero admits a functional which is nonnegative on
the cone and strictly positive on the set.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures.Probability.Infinite

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyConvexSpace ℝ E]

/-- `K` is upward closed under translation by the cone `C`. -/
def ConeUpperSet (C : ProperCone ℝ E) (K : Set E) : Prop :=
  ∀ ⦃x c⦄, x ∈ K → c ∈ C → x + c ∈ K

/-- The Hahn--Banach separation lemma in the exact form needed for Kelley's
countable-cover argument. -/
theorem exists_positive_separator_of_coneUpper
    (C : ProperCone ℝ E) {K : Set E}
    (hKne : K.Nonempty) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKzero : (0 : E) ∉ K) (hupper : ConeUpperSet C K) :
    ∃ f : StrongDual ℝ E,
      (∀ c ∈ C, 0 ≤ f c) ∧ ∀ x ∈ K, 0 < f x := by
  obtain ⟨f, u, hfu, hfK⟩ :=
    geometric_hahn_banach_point_closed hKconv hKclosed hKzero
  have hu : 0 < u := by simpa using hfu
  rcases hKne with ⟨x₀, hx₀⟩
  have hcone : ∀ c ∈ C, 0 ≤ f c := by
    intro c hc
    by_contra hneg
    have hfc : f c < 0 := lt_of_not_ge hneg
    have hden : 0 < -f c := neg_pos.mpr hfc
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((f x₀ - u) / (-f c))
    have hn' : f x₀ - u < (n : ℝ) * (-f c) :=
      (div_lt_iff₀ hden).mp hn
    have hnc : (n : ℝ) • c ∈ C :=
      C.smul_mem hc (Nat.cast_nonneg n)
    have hxnc : x₀ + (n : ℝ) • c ∈ K := hupper hx₀ hnc
    have hsep := hfK _ hxnc
    rw [map_add, map_smul, smul_eq_mul] at hsep
    linarith
  refine ⟨f, hcone, ?_⟩
  intro x hx
  exact hu.trans (hfK x hx)

end

end Scott1964.MeasurementStructures.Probability.Infinite

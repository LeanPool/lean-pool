/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Universal adjoint and square graphs of a reflected selfadjoint operator

For conjugate-first inner products, the adjoint of an antilinear relation S
satisfies ⟨Sx,y⟩=⟨S*y,x⟩. Every graph vector is quantified; no test core or
unbounded-domain hypothesis is substituted for the actual adjoint condition.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Graph adjoint of an antilinear relation, defined by the inner-product identity on every pair in
the original graph. -/
def antilinearGraphAdjoint (S : Set (H × H)) : Set (H × H) :=
  {p | ∀ x y, (x, y) ∈ S → inner ℂ y p.1 = inner ℂ p.2 x}

/-- Set of points satisfying the antilinear graph square condition with membership specified by `{p
| ∃ y, (p.1, y) ∈ S ∧ (y, p.2) ∈ antilinearGraphAdjoint S}`. -/
def antilinearGraphSquare (S : Set (H × H)) : Set (H × H) :=
  {p | ∃ y, (p.1, y) ∈ S ∧ (y, p.2) ∈ antilinearGraphAdjoint S}

theorem antilinearGraphAdjoint_reflected_selfAdjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (J : H → H)
    (hJ : ∀ x, J (J x) = x)
    (hinner : ∀ x y, inner ℂ (J x) y = inner ℂ (J y) x) (y z : H) :
    (y, z) ∈ antilinearGraphAdjoint {p : H × H | (p.1, J p.2) ∈ A.graph} ↔
      (J y, z) ∈ A.graph := by
  have he : A.graph.adjoint = A.graph := by
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hA.dense_domain]
    exact congrArg LinearPMap.graph (show A.adjoint = A from hA)
  conv_rhs => rw [← he, Submodule.mem_adjoint_iff]
  constructor
  · intro h x v hxv
    have hs : (x, J v) ∈ {p : H × H | (p.1, J p.2) ∈ A.graph} := by
      change (x, J (J v)) ∈ A.graph
      rwa [hJ]
    have hh := h x (J v) hs
    rw [hinner v y] at hh
    have hc := congrArg conj hh
    rw [inner_conj_symm, inner_conj_symm] at hc
    exact sub_eq_zero.mpr hc
  · intro h x v hxv
    have hh := sub_eq_zero.mp (h x (J v) hxv)
    have hc := congrArg conj hh
    rw [inner_conj_symm, inner_conj_symm] at hc
    rw [← hinner (J v) y, hJ] at hc
    exact hc

theorem antilinearGraphSquare_reflected_selfAdjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (J : H → H)
    (hJ : ∀ x, J (J x) = x)
    (hinner : ∀ x y, inner ℂ (J x) y = inner ℂ (J y) x) (x z : H) :
    (x, z) ∈ antilinearGraphSquare {p : H × H | (p.1, J p.2) ∈ A.graph} ↔
      ∃ v, (x, v) ∈ A.graph ∧ (v, z) ∈ A.graph := by
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨J y, hxy, (antilinearGraphAdjoint_reflected_selfAdjoint A hA J hJ hinner y z).mp hyz⟩
  · rintro ⟨v, hxv, hvz⟩
    refine ⟨J v, ?_, ?_⟩
    · change (x, J (J v)) ∈ A.graph
      rwa [hJ]
    · apply (antilinearGraphAdjoint_reflected_selfAdjoint A hA J hJ hinner (J v) z).mpr
      rwa [hJ]

end VacuumBellSeparation

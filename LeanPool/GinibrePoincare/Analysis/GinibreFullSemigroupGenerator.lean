/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

/-! # The self-adjoint generator graph determined by an injective resolvent -/

@[expose] public section

open scoped LinearPMap Topology
namespace GinibrePoincare
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact graph of `1 - R⁻¹`, with domain the actual resolvent range. -/
def resolventGeneratorGraph (R : H →L[ℂ] H) : Submodule ℂ (H × H) where
  carrier := {p | R (p.1 - p.2) = p.1}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change R ((p.1 + q.1) - (p.2 + q.2)) = p.1 + q.1
    rw [show (p.1 + q.1) - (p.2 + q.2) = (p.1 - p.2) + (q.1 - q.2) by abel,
      map_add, hp, hq]
  smul_mem' := by
    intro c p hp
    change R (c • p.1 - c • p.2) = c • p.1
    rw [← smul_sub, map_smul, hp]

omit [CompleteSpace H] in
theorem resolventGeneratorGraph_singleValued (R : H →L[ℂ] H)
    (hInj : Function.Injective R) (p : H × H)
    (hp : p ∈ resolventGeneratorGraph R) (hx : p.1 = 0) : p.2 = 0 := by
  change R (p.1 - p.2) = p.1 at hp
  rw [hx, zero_sub] at hp
  have he := hInj (hp.trans (map_zero R).symm)
  exact neg_eq_zero.mp he

/-- The unbounded generator of an injective resolvent, defined by its single-valued graph. -/
def resolventGenerator (R : H →L[ℂ] H) (hInj : Function.Injective R) : H →ₗ.[ℂ] H where
  domain := (resolventGeneratorGraph R).map (LinearMap.fst ℂ H H)
  toFun := (resolventGeneratorGraph R).toLinearPMapAux (resolventGeneratorGraph_singleValued R hInj)

omit [CompleteSpace H] in
theorem resolventGenerator_graph (R : H →L[ℂ] H) (hInj : Function.Injective R) :
    (resolventGenerator R hInj).graph = resolventGeneratorGraph R := by
  have hsingle := resolventGeneratorGraph_singleValued R hInj
  have heq : resolventGenerator R hInj = (resolventGeneratorGraph R).toLinearPMap := by
    unfold resolventGenerator Submodule.toLinearPMap
    rw [dite_eq_left hsingle]
  exact heq ▸ Submodule.toLinearPMap_graph_eq _ hsingle

omit [CompleteSpace H] in
theorem resolventGenerator_range_pair (R : H →L[ℂ] H) (x : H) :
    (R x, R x - x) ∈ resolventGeneratorGraph R := by
  change R (R x - (R x - x)) = R x
  congr 1
  abel

omit [CompleteSpace H] in
theorem resolventGenerator_dense_domain (R : H →L[ℂ] H)
    (hInj : Function.Injective R) (hDense : DenseRange R) :
    Dense ((resolventGenerator R hInj).domain : Set H) := by
  apply hDense.mono
  rintro _ ⟨x, rfl⟩
  have hpair : (R x, R x - x) ∈ (resolventGenerator R hInj).graph := by
    rw [resolventGenerator_graph R hInj]
    exact resolventGenerator_range_pair R x
  exact LinearPMap.mem_domain_of_mem_graph hpair

theorem resolventGeneratorGraph_symmetric (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (p q : H × H) (hp : p ∈ resolventGeneratorGraph R)
    (hq : q ∈ resolventGeneratorGraph R) :
    inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR
  have h := hs (p.1 - p.2) (q.1 - q.2)
  change R (p.1 - p.2) = p.1 at hp
  change R (q.1 - q.2) = q.1 at hq
  change inner ℂ (R (p.1 - p.2)) (q.1 - q.2) =
    inner ℂ (p.1 - p.2) (R (q.1 - q.2)) at h
  rw [hp, hq, inner_sub_left, inner_sub_right] at h
  linear_combination h

theorem resolventGeneratorGraph_adjoint (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) :
    (resolventGeneratorGraph R).adjoint = resolventGeneratorGraph R := by
  ext p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR
    change R (p.1 - p.2) = p.1
    apply ext_inner_left ℂ
    intro x
    have h := hp (R x) (R x - x) (resolventGenerator_range_pair R x)
    rw [inner_sub_left] at h
    have he := hs x (p.1 - p.2)
    change inner ℂ (R x) (p.1 - p.2) = inner ℂ x (R (p.1 - p.2)) at he
    rw [inner_sub_right] at he
    linear_combination h - he
  · intro hp a b hab
    exact sub_eq_zero.mpr (resolventGeneratorGraph_symmetric R hR (a, b) p hab hp)

/-- Self-adjointness is derived from resolvent symmetry and dense range. -/
theorem resolventGenerator_selfAdjoint (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R) (hDense : DenseRange R) :
    IsSelfAdjoint (resolventGenerator R hInj) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (resolventGenerator_dense_domain R hInj hDense), resolventGenerator_graph R hInj,
    resolventGeneratorGraph_adjoint R hR]

theorem resolventGenerator_isClosed (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R) (hDense : DenseRange R) :
    (resolventGenerator R hInj).IsClosed :=
  (resolventGenerator_selfAdjoint R hR hInj hDense).isClosed

end
end GinibrePoincare

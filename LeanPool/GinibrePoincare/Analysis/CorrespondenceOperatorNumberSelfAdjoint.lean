/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberSelfAdjoint.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberResolvent
/-!
# Correspondence operator number self adjoint

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_isSelfAdjoint`.
-/

@[expose] public section
open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
theorem correspondenceOperatorNumberResolvent_denseRange (n : ℕ) (hn : 0 < n) :
    DenseRange (correspondenceOperatorNumberResolvent n hn) := by
  let R := correspondenceOperatorNumberResolvent n hn
  have hR : R.adjoint=R := correspondenceOperatorNumberResolvent_isSelfAdjoint n hn
  have hk : R.ker=⊥ := LinearMap.ker_eq_bot.mpr
    (correspondenceOperatorNumberResolvent_injective n hn)
  have he := R.orthogonal_ker
  rw [hR, hk, Submodule.bot_orthogonal_eq_top] at he
  change Dense (Set.range R)
  rw [dense_iff_closure_eq]
  change closure (R.range : Set (Lp ℂ 2 (complexGaussianMeasure n))) = Set.univ
  rw [← Submodule.topologicalClosure_coe,← he]
  rfl

theorem correspondenceOperatorNumber_range_pair (n : ℕ) (hn : 0 < n)
    (x : Lp ℂ 2 (complexGaussianMeasure n)) :
    (correspondenceOperatorNumberResolvent n hn x, x-correspondenceOperatorNumberResolvent n hn x)∈
      (correspondenceOperatorNumber n hn).graph := by
  rw [correspondenceOperatorNumber_graph_iff_resolvent]
  simp only [add_sub_cancel]

theorem correspondenceOperatorNumber_dense_domain (n : ℕ) (hn : 0 < n) :
    Dense ((correspondenceOperatorNumber n hn).domain : Set (Lp ℂ 2 (complexGaussianMeasure n))) :=
        by
  apply (correspondenceOperatorNumberResolvent_denseRange n hn).mono
  rintro _ ⟨x, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (correspondenceOperatorNumber_range_pair n hn x)

theorem correspondenceOperatorNumberGraph_symmetric (n : ℕ) (hn : 0 < n)
    (p q : Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n))
    (hp : p ∈ correspondenceOperatorNumberGraph n hn)
    (hq : q ∈ correspondenceOperatorNumberGraph n hn) :
    inner ℂ p.2 q.1=inner ℂ p.1 q.2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (correspondenceOperatorNumberResolvent_isSelfAdjoint n hn)
  have h := hs (p.1+p.2) (q.1+q.2)
  have hpR := (correspondenceOperatorNumber_graph_iff_resolvent n hn p.1 p.2).mp
    ((correspondenceOperatorNumber_graph n hn) ▸ hp)
  have hqR := (correspondenceOperatorNumber_graph_iff_resolvent n hn q.1 q.2).mp
    ((correspondenceOperatorNumber_graph n hn) ▸ hq)
  change inner ℂ (correspondenceOperatorNumberResolvent n hn (p.1+p.2)) (q.1+q.2)=
    inner ℂ (p.1+p.2) (correspondenceOperatorNumberResolvent n hn (q.1+q.2)) at h
  rw [hpR, hqR, inner_add_left, inner_add_right] at h
  linear_combination -h

theorem correspondenceOperatorNumberGraph_adjoint (n : ℕ) (hn : 0 < n) :
    (correspondenceOperatorNumberGraph n hn).adjoint=correspondenceOperatorNumberGraph n hn := by
  ext p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    rw [← correspondenceOperatorNumber_graph]
    rw [correspondenceOperatorNumber_graph_iff_resolvent]
    apply ext_inner_left ℂ
    intro x
    have hpair := correspondenceOperatorNumber_range_pair n hn x
    rw [correspondenceOperatorNumber_graph] at hpair
    have h := hp _ _ hpair
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (correspondenceOperatorNumberResolvent_isSelfAdjoint n hn)
    have he := hs x (p.1+p.2)
    change inner ℂ (correspondenceOperatorNumberResolvent n hn x) (p.1+p.2)=
      inner ℂ x (correspondenceOperatorNumberResolvent n hn (p.1+p.2)) at he
    rw [inner_sub_left] at h
    rw [inner_add_right] at he
    linear_combination -he-h
  · intro hp a b hab
    exact sub_eq_zero.mpr (correspondenceOperatorNumberGraph_symmetric n hn (a, b) p hab hp)

/-- The maximal Gaussian number operator is genuinely self-adjoint. -/
theorem correspondenceOperatorNumber_isSelfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (correspondenceOperatorNumber n hn) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (correspondenceOperatorNumber_dense_domain n hn),
    correspondenceOperatorNumber_graph, correspondenceOperatorNumberGraph_adjoint]
end
end GinibrePoincare

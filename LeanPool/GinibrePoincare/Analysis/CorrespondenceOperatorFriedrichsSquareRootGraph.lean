/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorFriedrichsSquareRootGraph.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorFriedrichsSquareRootCalculus
/-!
# Correspondence operator Friedrichs square root graph

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceFriedrichsSquareRoot_selfAdjoint`.
-/

@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section

section Generic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The graph `{(u, v) | B v = C u}`, as the kernel of `(u, v) ↦ B v - C u`. -/
def correspondenceSquareRootGraph (B C : H →L[ℂ] H) : Submodule ℂ (H×H) :=
  (B.comp (ContinuousLinearMap.snd ℂ H H)-C.comp (ContinuousLinearMap.fst ℂ H H)).ker

omit [CompleteSpace H] in
theorem correspondenceSquareRootGraph_mem (B C : H →L[ℂ] H) (u v : H) :
    (u, v)∈correspondenceSquareRootGraph B C ↔ B v=C u := by
  change B v-C u=0 ↔ _
  exact sub_eq_zero

omit [CompleteSpace H] in
theorem correspondenceSquareRootGraph_parametrize (B C : H →L[ℂ] H)
    (hcomm : Commute B C) (hs : ∀ x, B (B x) + C (C x) = x) (u v : H) :
    (u, v)∈correspondenceSquareRootGraph B C ↔ ∃x, B x=u ∧ C x=v := by
  have hc x : B (C x)=C (B x) := congrArg (fun L : H→L[ℂ]H=>L x) hcomm.eq
  rw [correspondenceSquareRootGraph_mem]
  constructor
  · intro h
    refine ⟨B u+C v,?_,?_⟩
    · rw [map_add, hc, h, hs]
    · rw [map_add,← hc,← h, hs]
  · rintro ⟨x, rfl, rfl⟩
    exact hc x

omit [CompleteSpace H] in
theorem correspondenceSquareRootGraph_singleValued (B C : H →L[ℂ] H)
    (hB : Function.Injective B) (p : H × H)
    (hp : p ∈ correspondenceSquareRootGraph B C) (hz : p.1 = 0) : p.2=0 := by
  have he := (correspondenceSquareRootGraph_mem B C p.1 p.2).mp hp
  rw [hz, map_zero] at he
  exact hB (he.trans (map_zero B).symm)

theorem correspondenceSquareRootGraph_adjoint (B C : H →L[ℂ] H)
    (hB : B.adjoint = B) (hC : C.adjoint = C)
    (hcomm : Commute B C) (hs : ∀ x, B (B x) + C (C x) = x) :
    (correspondenceSquareRootGraph B C).adjoint=correspondenceSquareRootGraph B C := by
  ext p
  rw [Submodule.mem_adjoint_iff, correspondenceSquareRootGraph_mem]
  constructor
  · intro hp
    apply ext_inner_left ℂ
    intro x
    have hpx : (B x, C x)∈correspondenceSquareRootGraph B C :=
      (correspondenceSquareRootGraph_parametrize B C hcomm hs _ _).mpr ⟨x, rfl, rfl⟩
    have h := hp (B x) (C x) hpx
    have h1 := B.adjoint_inner_right x p.2
    have h2 := C.adjoint_inner_right x p.1
    rw [hB] at h1
    rw [hC] at h2
    rw [h1, h2]
    exact (sub_eq_zero.mp h).symm
  · intro hp a b hab
    obtain ⟨x, hx, hx'⟩ := (correspondenceSquareRootGraph_parametrize B C hcomm hs a b).mp hab
    rw [← hx,← hx']
    have h1 := B.adjoint_inner_right x p.2
    have h2 := C.adjoint_inner_right x p.1
    rw [hB] at h1
    rw [hC] at h2
    rw [← h1,← h2, hp, sub_self]

end Generic

/-- The graph `correspondenceSquareRootGraph` built from the square roots
`correspondenceFriedrichsResolventSqrt n hn` and `correspondenceFriedrichsComplementSqrt n hn`. -/
def correspondenceFriedrichsSquareRootGraph (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (GinibreFullComplexL2 n×GinibreFullComplexL2 n) :=
  correspondenceSquareRootGraph (correspondenceFriedrichsResolventSqrt n hn)
      (correspondenceFriedrichsComplementSqrt n hn)

/-- The Friedrichs square root: the partial linear map whose graph is
`correspondenceFriedrichsSquareRootGraph n hn`. -/
def correspondenceFriedrichsSquareRoot (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n→ₗ.[ℂ]GinibreFullComplexL2 n :=
  (correspondenceFriedrichsSquareRootGraph n hn).toLinearPMap

theorem correspondenceFriedrichsSquareRoot_graph (n : ℕ) (hn : 0 < n) :
    (correspondenceFriedrichsSquareRoot n hn).graph=correspondenceFriedrichsSquareRootGraph n hn :=
  Submodule.toLinearPMap_graph_eq _
    (correspondenceSquareRootGraph_singleValued _ _ (correspondenceFriedrichsResolventSqrt_injective
        n hn))

theorem correspondenceFriedrichsSquareRoot_graph_parametrize (n : ℕ) (hn : 0 < n)
    (u v : GinibreFullComplexL2 n) :
    (u, v)∈(correspondenceFriedrichsSquareRoot n hn).graph ↔
      ∃x, correspondenceFriedrichsResolventSqrt n hn x=u ∧ correspondenceFriedrichsComplementSqrt n
          hn x=v := by
  rw [correspondenceFriedrichsSquareRoot_graph]
  exact correspondenceSquareRootGraph_parametrize _ _ (correspondenceFriedrichsSquareRoots_commute n
      hn)
    (correspondenceFriedrichsSquareRoots_sum_squares n hn) u v

theorem correspondenceFriedrichsSquareRoot_domain (n : ℕ) (hn : 0 < n) :
    ((correspondenceFriedrichsSquareRoot n hn).domain : Set (GinibreFullComplexL2 n))=
      range (correspondenceFriedrichsResolventSqrt n hn) := by
  ext u
  constructor
  · intro hu
    have hg := (correspondenceFriedrichsSquareRoot n hn).mem_graph ⟨u, hu⟩
    obtain ⟨x, hx, _⟩ := (correspondenceFriedrichsSquareRoot_graph_parametrize n hn _ _).mp hg
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((correspondenceFriedrichsSquareRoot_graph_parametrize n hn _ _).mpr ⟨x, rfl, rfl⟩)

theorem correspondenceFriedrichsSquareRoot_dense_domain (n : ℕ) (hn : 0 < n) :
    Dense ((correspondenceFriedrichsSquareRoot n hn).domain : Set (GinibreFullComplexL2 n)) := by
  rw [correspondenceFriedrichsSquareRoot_domain]
  exact correspondenceFriedrichsResolventSqrt_denseRange n hn

theorem correspondenceFriedrichsSquareRoot_selfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (correspondenceFriedrichsSquareRoot n hn) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (correspondenceFriedrichsSquareRoot_dense_domain n
      hn),
    correspondenceFriedrichsSquareRoot_graph]
  exact correspondenceSquareRootGraph_adjoint _ _ (correspondenceFriedrichsResolventSqrt_selfAdjoint
      n hn)
    (correspondenceFriedrichsComplementSqrt_selfAdjoint n hn)
        (correspondenceFriedrichsSquareRoots_commute n hn)
    (correspondenceFriedrichsSquareRoots_sum_squares n hn)

end
end GinibrePoincare

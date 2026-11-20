/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiBergmanMonomials.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiMultilinear
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticMultilinearClosure
public import LeanPool.GinibrePoincare.Analysis.GeneralRadialProjectionMonomials
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionPermutation
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticClosedSubmoduleIntegral

/-!
# Non quadratic pi Bergman monomials

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiBergmanProjection_range_eq_weighted_monomial_closure`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The tensor products, in `L²(ℂ^d)`, of `d` weighted monomial vectors from
`planarWeightedMonomialVectors n V`. -/
def planarPiWeightedMonomialVectors (d n : ℕ) (V : ℂ → ℝ) : Set (PlanarPiLebesgueL2 d) :=
  {F | ∃ u : Fin d → PlanarLebesgueL2, (∀ i, u i ∈ planarWeightedMonomialVectors n V) ∧
      l2PiProductVector (fun _ => (volume : Measure ℂ)) u = F}

theorem planarPiBergmanProjection_mem_weighted_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z) (F : PlanarPiLebesgueL2 (d+1)) :
    planarPiBergmanProjection n V hV F ∈
      (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure := by
  let K := (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure
  have hK : IsClosed (K : Set (PlanarPiLebesgueL2 (d+1))) :=
    (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).isClosed_topologicalClosure
  have hp (u : Fin (d+1) → PlanarLebesgueL2) :
      planarPiBergmanProjection n V hV (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) ∈ K :=
          by
    rw [planarPiBergmanProjection_pure]
    apply continuousMultilinear_mem_of_closed_factor_spans
      (l2PiProductContinuousMultilinear (fun _ : Fin (d+1) => (volume : Measure ℂ)))
      (fun _ => planarWeightedMonomialVectors n V) K hK
    · intro v hv
      exact (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).le_topologicalClosure
        (Submodule.subset_span ⟨v, hv, rfl⟩)
    · intro i
      exact planarBergmanKernel_le_weighted_monomial_closure n V hV hr
        (Submodule.starProjection_apply_mem (planarBergmanKernelClosed n V hV).toSubmodule (u i))
  let : IsClosed (K : Set (PlanarPiLebesgueL2 (d+1))) := hK
  have he : K.mkQL.comp (planarPiBergmanProjection n V hV) = 0 := by
    apply l2PiOperators_ext_on_pure (d+1) (fun _ => (volume : Measure ℂ))
    intro u
    change K.mkQL (planarPiBergmanProjection n V hV (l2PiProductVector (fun _ => (volume : Measure
        ℂ)) u)) = 0
    exact (Submodule.Quotient.mk_eq_zero K).mpr (hp u)
  have hz := DFunLike.congr_fun he F
  change K.mkQL (planarPiBergmanProjection n V hV F) = 0 at hz
  exact (Submodule.Quotient.mk_eq_zero K).mp hz

theorem planarPiBergmanProjection_idempotent {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    (planarPiBergmanProjection (m := d) n V hV).comp (planarPiBergmanProjection n V hV) =
      planarPiBergmanProjection n V hV := by
  apply l2PiOperators_ext_on_pure (d+1) (fun _ => (volume : Measure ℂ))
  intro u
  simp only [ContinuousLinearMap.comp_apply, planarPiBergmanProjection_pure]
  congr 1
  funext i
  exact DFunLike.congr_fun
    (planarBergmanKernelClosed n V hV).toSubmodule.isIdempotentElem_starProjection (u i)

/-- The fixed-point subspace of the product Bergman projection: the kernel of
`1 - planarPiBergmanProjection n V`. -/
def planarPiBergmanJointKernel {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    Submodule ℂ (PlanarPiLebesgueL2 (d+1)) :=
  (ContinuousLinearMap.id ℂ _ - planarPiBergmanProjection n V hV).ker

theorem planarPiWeightedMonomialVector_fixed {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z)
    (F : PlanarPiLebesgueL2 (d+1)) (hF : F ∈ planarPiWeightedMonomialVectors (d+1) n V) :
    planarPiBergmanProjection n V hV F = F := by
  obtain ⟨u, hu, rfl⟩ := hF
  rw [planarPiBergmanProjection_pure]
  congr 1
  funext i
  apply Submodule.starProjection_eq_self_iff.mpr
  change u i ∈ planarBergmanKernel n V hV
  rw [planarBergmanKernel_eq_weighted_monomial_closure n V hV hr]
  exact (Submodule.span ℂ (planarWeightedMonomialVectors n V)).le_topologicalClosure
    (Submodule.subset_span (hu i))

theorem planarPiBergmanJointKernel_eq_weighted_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z) :
    planarPiBergmanJointKernel (d := d) n V hV =
      (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure := by
  apply le_antisymm
  · intro F hF
    have hf : planarPiBergmanProjection n V hV F = F := by
      change F - planarPiBergmanProjection n V hV F = 0 at hF
      exact (sub_eq_zero.mp hF).symm
    rw [← hf]
    exact planarPiBergmanProjection_mem_weighted_monomial_closure n V hV hr F
  · apply (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro F hF
      change F - planarPiBergmanProjection n V hV F = 0
      rw [planarPiWeightedMonomialVector_fixed n V hV hr F hF, sub_self]
    · exact ContinuousLinearMap.isClosed_ker _

theorem planarPiBergmanProjection_range_eq_weighted_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z) :
    (planarPiBergmanProjection (m := d) n V hV).range =
      (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure := by
  rw [← planarPiBergmanJointKernel_eq_weighted_monomial_closure n V hV hr]
  apply le_antisymm
  · rintro F ⟨G, rfl⟩
    change planarPiBergmanProjection n V hV G -
      planarPiBergmanProjection n V hV (planarPiBergmanProjection n V hV G) = 0
    rw [show planarPiBergmanProjection n V hV (planarPiBergmanProjection n V hV G) =
      planarPiBergmanProjection n V hV G from DFunLike.congr_fun
          (planarPiBergmanProjection_idempotent n V hV) G]
    exact sub_self _
  · intro F hF
    refine ⟨F, ?_⟩
    change F - planarPiBergmanProjection n V hV F = 0 at hF
    exact (sub_eq_zero.mp hF).symm

end
end GinibrePoincare

/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Poincare.Domain
public import LeanPool.EllipticPDE.Sobolev.Basic


/-!
# Density extension to H₀¹ (dependency-chain step 4)

The Poincaré inequality, once established for every smooth compactly supported test
function, extends to all of `H₀¹(Ω)` by density. The key structural facts (proved in
`Sobolev/Basic.lean`) are that the test-function graphs already form a submodule
(`span_testGraphSet`) and that `H₀¹(Ω)` is their topological closure. The Poincaré
estimate is the condition `0 ≤ Φ` for a continuous function `Φ`, hence a closed
condition; holding on the dense test functions, it passes to the closure.

The base estimate on test functions is taken as a hypothesis here (it is supplied by the
domain Poincaré inequality `poincare_domain` rewritten through the `L²` norms). This keeps
the density mechanism independent of the geometry of `Ω`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Density Poincaré inequality on `H₀¹`.** If the Poincaré bound
`‖φ‖²_{L²} ≤ C · ∑ᵢ ‖∂ᵢφ‖²_{L²}` holds for every test function `φ` (phrased through the
graph coordinates `testGraph 0` and `testGraph i.succ`), then it holds for every element
of `H₀¹(Ω)`: the function part `U 0` is controlled by the gradient part `U ∘ Fin.succ`. -/
theorem poincare_H01 {Ω : Set (EuclideanSpace ℝ (Fin d))} (C : ℝ)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ C * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    ‖U 0‖ ^ 2 ≤ C * ∑ i : Fin d, ‖U i.succ‖ ^ 2 := by
  -- `Φ V ≥ 0` is exactly the Poincaré estimate at `V`; `Φ` is continuous.
  set Φ : H1amb Ω → ℝ := fun V => C * ∑ i : Fin d, ‖V i.succ‖ ^ 2 - ‖V 0‖ ^ 2 with hΦ
  have hcont : Continuous Φ := by rw [hΦ]; fun_prop
  have hclosed : IsClosed {V : H1amb Ω | 0 ≤ Φ V} := isClosed_le continuous_const hcont
  -- The estimate holds on the span of the test graphs (which equals the test graphs).
  have hspan : ((Submodule.span ℝ (testGraphSet Ω) : Submodule ℝ (H1amb Ω)) : Set (H1amb Ω))
      ⊆ {V | 0 ≤ Φ V} := by
    rw [span_testGraphSet]
    rintro U ⟨φ, h, rfl⟩
    simp only [Set.mem_ofPred_eq, hΦ, sub_nonneg]
    exact hbase h
  -- `H₀¹` is the closure of that span, so the closed estimate passes to all of it.
  have hsub : (H01 Ω : Set (H1amb Ω)) ⊆ {V | 0 ≤ Φ V} := by
    rw [H01, Submodule.topologicalClosure_coe]
    exact closure_minimal hspan hclosed
  have hUmem : 0 ≤ Φ U := hsub hU
  simp only [hΦ, sub_nonneg] at hUmem
  exact hUmem

end EllipticPdes.Poincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialGeneratorSymmetry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorClosure

/-! # Symmetry of the closed polynomial-sector generator

Symmetry is proved in the actual Ginibre L² scalar product and passes to the
actual graph closure. Self-adjointness and full diffusion identification are
not consequences asserted here.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

private theorem polynomialGeneratorGraph_symmetry (n : ℕ) (hn : 2 ≤ n)
    (p q : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
    (hp : p ∈ polynomialGeneratorGraph n hn)
    (hq : q ∈ polynomialGeneratorGraph n hn) :
    inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨j, rfl⟩ := hq
      change inner ℂ (-(eigenvalue n i.a i.b i.m : ℂ) • _) _ =
        inner ℂ _ (-(eigenvalue n j.a j.b j.m : ℂ) • _)
      rw [inner_smul_left, inner_smul_right]
      by_cases hij : i = j
      · subst j
        simp
      · have ho : inner ℂ (polynomialEigenfunctionL2 n hn i)
            (polynomialEigenfunctionL2 n hn j) = 0 := by
          rw [inner_polynomialEigenfunctionL2]
          apply polynomialEigenfunction_equilibrium_orthogonal n hn
          rintro ⟨ha, hb, hm⟩
          apply hij
          cases i
          cases j
          simp_all
        simp [ho]
    | zero => simp
    | add x y _ _ hx hy => simp_all [inner_add_right]
    | smul c x _ hx => simp_all [inner_smul_right]
  | zero => simp
  | add x y _ _ hx hy => simp_all [inner_add_left]
  | smul c x _ hx => simp_all [inner_smul_left]

/-- The graph-closed polynomial realization is symmetric in actual Ginibre L². -/
theorem closedPolynomialGenerator_graph_symmetric (n : ℕ) (hn : 2 ≤ n)
    (p q : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
    (hp : p ∈ (closedPolynomialGenerator n hn).graph)
    (hq : q ∈ (closedPolynomialGenerator n hn).graph) :
    inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
  rw [closedPolynomialGenerator_graph] at hp hq
  have hfinite (q : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
      (hq : q ∈ polynomialGeneratorGraph n hn) :
      inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
    have hc : IsClosed {p : GinibrePolynomialL2 n × GinibrePolynomialL2 n |
        inner ℂ p.2 q.1 = inner ℂ p.1 q.2} := by
      apply isClosed_eq <;> fun_prop
    exact closure_minimal (fun p hp => polynomialGeneratorGraph_symmetry n hn p q hp hq)
      hc hp
  have hc : IsClosed {q : GinibrePolynomialL2 n × GinibrePolynomialL2 n |
      inner ℂ p.2 q.1 = inner ℂ p.1 q.2} := by
    apply isClosed_eq <;> fun_prop
  exact closure_minimal (fun q hq => hfinite q hq) hc hq

/-- Domain-valued symmetry for the closed partial linear operator. -/
theorem closedPolynomialGenerator_symmetric (n : ℕ) (hn : 2 ≤ n)
    (u v : (closedPolynomialGenerator n hn).domain) :
    inner ℂ ((closedPolynomialGenerator n hn) u) v.1 =
      inner ℂ u.1 ((closedPolynomialGenerator n hn) v) := by
  apply closedPolynomialGenerator_graph_symmetric n hn
    (u.1, (closedPolynomialGenerator n hn) u)
    (v.1, (closedPolynomialGenerator n hn) v)
  · exact (LinearPMap.image_iff u.2).mp rfl
  · exact (LinearPMap.image_iff v.2).mp rfl

end
end GinibrePoincare

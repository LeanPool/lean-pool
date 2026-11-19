/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialGeneratorClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialEigenfunctionBasis
public import LeanPool.GinibrePoincare.Analysis.PolynomialEigenfunctionGenerator
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # Closed L² realization of the polynomial Ginibre restriction
The graph closure is taken in actual Ginibre L². Its input/output vectors
lie in the closed sum/radius polynomial sector. This construction does not
identify the operator with the full collision-free-core diffusion generator.
-/

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Complex `L²` of the Ginibre measure, the ambient space of the polynomial sector. -/
abbrev GinibrePolynomialL2 (n : ℕ) := Lp ℂ 2 (ginibreMeasure n)

/-- The Hermite–Laguerre polynomial eigenfunction with indices `i`, as a vector of Ginibre
`L²`. -/
def polynomialEigenfunctionL2 (n : ℕ) (hn : 2 ≤ n) (i : PolynomialEigenfunctionData n) :
    GinibrePolynomialL2 n :=
  (polynomialEigenfunction_memLp_two n hn i.a i.b i.m).toLp (polynomialEigenfunction n i)

theorem polynomialEigenfunctionL2_coeFn (n : ℕ) (hn : 2 ≤ n) (i : PolynomialEigenfunctionData n) :
    polynomialEigenfunctionL2 n hn i =ᵐ[ginibreMeasure n] polynomialEigenfunction n i :=
  (polynomialEigenfunction_memLp_two n hn i.a i.b i.m).coeFn_toLp

theorem inner_polynomialEigenfunctionL2 (n : ℕ) (hn : 2 ≤ n) (i j : PolynomialEigenfunctionData n) :
    inner ℂ (polynomialEigenfunctionL2 n hn i) (polynomialEigenfunctionL2 n hn j) =
      ∫ z, conj (polynomialEigenfunction n i z) * polynomialEigenfunction n j z ∂ginibreMeasure n :=
          by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [polynomialEigenfunctionL2_coeFn n hn i,
    polynomialEigenfunctionL2_coeFn n hn j] with z hi hj
  rw [hi, hj, RCLike.inner_apply]
  ring

/-- The generator eigenvalue `-eigenvalue n i.a i.b i.m` of the eigenfunction with indices `i`. -/
def polynomialGeneratorRate (n : ℕ) (i : PolynomialEigenfunctionData n) : ℂ :=
  -(eigenvalue n i.a i.b i.m : ℂ)

/-- Finite polynomial graph, using the already proved concrete generator eigenvalues. -/
def polynomialGeneratorGraph (n : ℕ) (hn : 2 ≤ n) :
    Submodule ℂ (GinibrePolynomialL2 n × GinibrePolynomialL2 n) :=
  Submodule.span ℂ (Set.range fun i =>
    (polynomialEigenfunctionL2 n hn i, polynomialGeneratorRate n i • polynomialEigenfunctionL2 n hn
        i))

/-- The L² closure of the polynomial sector. -/
def closedPolynomialSector (n : ℕ) (hn : 2 ≤ n) : Submodule ℂ (GinibrePolynomialL2 n) :=
  (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n hn))).topologicalClosure

private theorem graph_inner (n : ℕ) (hn : 2 ≤ n) (i : PolynomialEigenfunctionData n)
    (p : GinibrePolynomialL2 n × GinibrePolynomialL2 n) (hp : p ∈ polynomialGeneratorGraph n hn) :
    inner ℂ (polynomialEigenfunctionL2 n hn i) p.2 =
      polynomialGeneratorRate n i * inner ℂ (polynomialEigenfunctionL2 n hn i) p.1 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨j, rfl⟩ := hp
    rw [inner_smul_right]
    by_cases hij : i = j
    · subst j; rfl
    · have ho : inner ℂ (polynomialEigenfunctionL2 n hn i)
          (polynomialEigenfunctionL2 n hn j) = 0 := by
        rw [inner_polynomialEigenfunctionL2]
        apply polynomialEigenfunction_equilibrium_orthogonal n hn
        rintro ⟨ha, hb, hm⟩
        apply hij
        cases i; cases j; simp_all
      simp [ho]
  | zero => simp
  | add p q _ _ hp hq => simp_all [inner_add_right, mul_add]
  | smul c p _ hp => simp_all [inner_smul_right, mul_left_comm]

private theorem closure_graph_inner (n : ℕ) (hn : 2 ≤ n) (i : PolynomialEigenfunctionData n)
    (p : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
    (hp : p ∈ (polynomialGeneratorGraph n hn).topologicalClosure) :
    inner ℂ (polynomialEigenfunctionL2 n hn i) p.2 =
      polynomialGeneratorRate n i * inner ℂ (polynomialEigenfunctionL2 n hn i) p.1 := by
  have hc : IsClosed {p : GinibrePolynomialL2 n × GinibrePolynomialL2 n |
      inner ℂ (polynomialEigenfunctionL2 n hn i) p.2 =
        polynomialGeneratorRate n i * inner ℂ (polynomialEigenfunctionL2 n hn i) p.1} := by
    apply isClosed_eq <;> fun_prop
  exact closure_minimal (fun p hp => graph_inner n hn i p hp) hc hp

/-- Graph closure introduces no vertical vectors, so it is a genuine operator graph. -/
theorem polynomialGeneratorGraph_closure_singleValued (n : ℕ) (hn : 2 ≤ n)
    (p : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
    (hp : p ∈ (polynomialGeneratorGraph n hn).topologicalClosure) (hx : p.1 = 0) : p.2 = 0 := by
  have hs : p.2 ∈ closedPolynomialSector n hn := by
    have hc : IsClosed {q : GinibrePolynomialL2 n × GinibrePolynomialL2 n |
        q.2 ∈ closedPolynomialSector n hn} :=
      (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n
          hn))).isClosed_topologicalClosure.preimage continuous_snd
    apply closure_minimal (s := (polynomialGeneratorGraph n hn : Set _)) ?_ hc hp
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨i, rfl⟩ := hq
      exact (closedPolynomialSector n hn).smul_mem _
        ((Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n hn))).le_topologicalClosure
          (Submodule.subset_span ⟨i, rfl⟩))
    | zero => exact (closedPolynomialSector n hn).zero_mem
    | add p q _ _ hp hq => exact (closedPolynomialSector n hn).add_mem hp hq
    | smul c p _ hp => exact (closedPolynomialSector n hn).smul_mem c hp
  have hi (i : PolynomialEigenfunctionData n) : inner ℂ (polynomialEigenfunctionL2 n hn i) p.2 = 0
      := by
    have he := closure_graph_inner n hn i p hp
    simpa [hx] using he
  have hz : inner ℂ p.2 p.2 = 0 := by
    have hc : IsClosed {x : GinibrePolynomialL2 n | inner ℂ x p.2 = 0} := by
      apply isClosed_eq <;> fun_prop
    apply closure_minimal ?_ hc hs
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hi i
    | zero => simp
    | add x y _ _ hx hy =>
      change inner ℂ x p.2 = 0 at hx
      change inner ℂ y p.2 = 0 at hy
      simp [inner_add_left, hx, hy]
    | smul c x _ hx =>
      change inner ℂ x p.2 = 0 at hx
      simp [inner_smul_left, hx]
  exact inner_self_eq_zero.mp hz

/-- The graph-closed realization of the concrete polynomial restriction. -/
def closedPolynomialGenerator (n : ℕ) (hn : 2 ≤ n) :
    GinibrePolynomialL2 n →ₗ.[ℂ] GinibrePolynomialL2 n :=
  (polynomialGeneratorGraph n hn).topologicalClosure.toLinearPMap

theorem closedPolynomialGenerator_graph (n : ℕ) (hn : 2 ≤ n) :
    (closedPolynomialGenerator n hn).graph = (polynomialGeneratorGraph n hn).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (polynomialGeneratorGraph_closure_singleValued n hn)

theorem closedPolynomialGenerator_isClosed (n : ℕ) (hn : 2 ≤ n) :
    (closedPolynomialGenerator n hn).IsClosed := by
  rw [LinearPMap.IsClosed, closedPolynomialGenerator_graph]
  exact (polynomialGeneratorGraph n hn).isClosed_topologicalClosure

/-- The finite polynomial operator before graph closure. -/
def polynomialGenerator (n : ℕ) (hn : 2 ≤ n) :
    GinibrePolynomialL2 n →ₗ.[ℂ] GinibrePolynomialL2 n :=
  (polynomialGeneratorGraph n hn).toLinearPMap

/-- The concrete polynomial graph defines a closable operator. -/
theorem polynomialGenerator_isClosable (n : ℕ) (hn : 2 ≤ n) :
    (polynomialGenerator n hn).IsClosable := by
  have hg : (polynomialGenerator n hn).graph = polynomialGeneratorGraph n hn :=
    Submodule.toLinearPMap_graph_eq _ (fun p hp hx =>
      polynomialGeneratorGraph_closure_singleValued n hn p
        ((polynomialGeneratorGraph n hn).le_topologicalClosure hp) hx)
  exact ⟨closedPolynomialGenerator n hn, by rw [hg, closedPolynomialGenerator_graph]⟩

/-- The closed realization is precisely the graph closure of the polynomial operator. -/
theorem closedPolynomialGenerator_eq_closure (n : ℕ) (hn : 2 ≤ n) :
    closedPolynomialGenerator n hn = (polynomialGenerator n hn).closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (polynomialGenerator_isClosable n hn).graph_closure_eq_closure_graph,
    closedPolynomialGenerator_graph]
  congr 1
  exact (Submodule.toLinearPMap_graph_eq _ (fun p hp hx =>
    polynomialGeneratorGraph_closure_singleValued n hn p
      ((polynomialGeneratorGraph n hn).le_topologicalClosure hp) hx)).symm

/-- Every actual Hermite–Laguerre polynomial belongs to the closed domain with its eigenvalue. -/
theorem polynomialEigenfunction_mem_closedGenerator_graph (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    (polynomialEigenfunctionL2 n hn i,
      -(eigenvalue n i.a i.b i.m : ℂ) • polynomialEigenfunctionL2 n hn i) ∈
        (closedPolynomialGenerator n hn).graph := by
  rw [closedPolynomialGenerator_graph]
  exact (polynomialGeneratorGraph n hn).le_topologicalClosure (Submodule.subset_span ⟨i, rfl⟩)

/-- Membership in the actual closed operator domain, not merely an a.e. formula. -/
theorem polynomialEigenfunction_mem_closedGenerator_domain (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    polynomialEigenfunctionL2 n hn i ∈ (closedPolynomialGenerator n hn).domain :=
  LinearPMap.mem_domain_of_mem_graph (polynomialEigenfunction_mem_closedGenerator_graph n hn i)

/-- The closed operator has the paper's exact eigenvalue on every polynomial member. -/
theorem closedPolynomialGenerator_eigenvalue (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    (closedPolynomialGenerator n hn) ⟨polynomialEigenfunctionL2 n hn i,
      polynomialEigenfunction_mem_closedGenerator_domain n hn i⟩ =
        -(eigenvalue n i.a i.b i.m : ℂ) • polynomialEigenfunctionL2 n hn i := by
  exact ((LinearPMap.image_iff (polynomialEigenfunction_mem_closedGenerator_domain n hn i)).mpr
    (polynomialEigenfunction_mem_closedGenerator_graph n hn i)).symm

/-- The closed-operator output represents the actual differential pregenerator. -/
theorem closedPolynomialGenerator_agrees_concrete (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    (closedPolynomialGenerator n hn) ⟨polynomialEigenfunctionL2 n hn i,
      polynomialEigenfunction_mem_closedGenerator_domain n hn i⟩ =ᵐ[ginibreMeasure n]
        complexGinibrePregenerator n (polynomialEigenfunction n i) := by
  rw [closedPolynomialGenerator_eigenvalue]
  filter_upwards [Lp.coeFn_smul (-(eigenvalue n i.a i.b i.m : ℂ))
    (polynomialEigenfunctionL2 n hn i), polynomialEigenfunctionL2_coeFn n hn i,
    polynomialEigenfunction_eigenvalue_equation_ae n hn i.a i.b i.m] with z hs hp he
  rw [hs, Pi.smul_apply, smul_eq_mul, hp]
  simp only [eigenvalue] at *
  push_cast
  linear_combination he

end
end GinibrePoincare

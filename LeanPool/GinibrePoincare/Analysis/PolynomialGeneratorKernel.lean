/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialGeneratorKernel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorSymmetry

/-! # Kernel of the actual closed polynomial-sector generator -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Totality of the concrete eigenvectors in their actual closed L² sector. -/
theorem closedPolynomialSector_eq_zero_of_inner_eigenvectors_zero (n : ℕ) (hn : 2 ≤ n)
    (u : GinibrePolynomialL2 n) (hu : u ∈ closedPolynomialSector n hn)
    (hi : ∀ i, inner ℂ (polynomialEigenfunctionL2 n hn i) u = 0) : u = 0 := by
  have hz : inner ℂ u u = 0 := by
    have hc : IsClosed {x : GinibrePolynomialL2 n | inner ℂ x u = 0} := by
      apply isClosed_eq <;> fun_prop
    apply closure_minimal ?_ hc hu
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hi i
    | zero => simp
    | add x y _ _ hx hy => simp_all [inner_add_left]
    | smul c x _ hx => simp_all [inner_smul_left]
  exact inner_self_eq_zero.mp hz

/-- Every input of the graph-closed polynomial generator lies in the closed sector. -/
theorem closedPolynomialGenerator_input_mem_sector (n : ℕ) (hn : 2 ≤ n)
    (p : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
    (hp : p ∈ (closedPolynomialGenerator n hn).graph) :
    p.1 ∈ closedPolynomialSector n hn := by
  rw [closedPolynomialGenerator_graph] at hp
  have hc : IsClosed {p : GinibrePolynomialL2 n × GinibrePolynomialL2 n |
      p.1 ∈ closedPolynomialSector n hn} :=
    (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n
        hn))).isClosed_topologicalClosure.preimage
      continuous_fst
  apply closure_minimal ?_ hc hp
  intro p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n hn))).le_topologicalClosure
      (Submodule.subset_span ⟨i, rfl⟩)
  | zero => exact (closedPolynomialSector n hn).zero_mem
  | add p q _ _ hp hq => exact (closedPolynomialSector n hn).add_mem hp hq
  | smul c p _ hp => exact (closedPolynomialSector n hn).smul_mem c hp

/-- The zero index labels the constant Hermite–Laguerre mode. -/
def polynomialConstantIndex (n : ℕ) : PolynomialEigenfunctionData n := ⟨0, 0, 0⟩

/-- Only the constant index has zero generator eigenvalue. -/
theorem polynomialEigenvalue_eq_zero_iff (n : ℕ) (i : PolynomialEigenfunctionData n) :
    eigenvalue n i.a i.b i.m = 0 ↔ i = polynomialConstantIndex n := by
  constructor
  · intro h
    have ha : (i.a : ℝ) = 0 := by unfold eigenvalue at h; nlinarith [Nat.cast_nonneg (α := ℝ) i.a,
                                    Nat.cast_nonneg (α := ℝ) i.b, Nat.cast_nonneg (α := ℝ) i.m]
    have hb : (i.b : ℝ) = 0 := by unfold eigenvalue at h; nlinarith [Nat.cast_nonneg (α := ℝ) i.a,
                                    Nat.cast_nonneg (α := ℝ) i.b, Nat.cast_nonneg (α := ℝ) i.m]
    have hm : (i.m : ℝ) = 0 := by unfold eigenvalue at h; nlinarith [Nat.cast_nonneg (α := ℝ) i.a,
                                    Nat.cast_nonneg (α := ℝ) i.b, Nat.cast_nonneg (α := ℝ) i.m]
    have ha' : i.a = 0 := by exact_mod_cast ha
    have hb' : i.b = 0 := by exact_mod_cast hb
    have hm' : i.m = 0 := by exact_mod_cast hm
    cases i
    simp_all [polynomialConstantIndex]
  · rintro rfl
    simp [polynomialConstantIndex, eigenvalue]

/-- A zero generator output forces every positive-rate coefficient to vanish. -/
theorem closedPolynomialGenerator_kernel_inner_zero (n : ℕ) (hn : 2 ≤ n)
    (u : GinibrePolynomialL2 n) (hu : (u, 0) ∈ (closedPolynomialGenerator n hn).graph)
    (i : PolynomialEigenfunctionData n) (hi : i ≠ polynomialConstantIndex n) :
    inner ℂ (polynomialEigenfunctionL2 n hn i) u = 0 := by
  have h := closedPolynomialGenerator_graph_symmetric n hn
    (polynomialEigenfunctionL2 n hn i,
      -(eigenvalue n i.a i.b i.m : ℂ) • polynomialEigenfunctionL2 n hn i)
    (u, 0) (polynomialEigenfunction_mem_closedGenerator_graph n hn i) hu
  simp only [inner_smul_left, map_neg, Complex.conj_ofReal,
    inner_zero_right] at h
  apply (mul_eq_zero.mp h).resolve_left
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
    ((polynomialEigenvalue_eq_zero_iff n i).not.mpr hi))

/-- The kernel of the genuine closed polynomial operator is exactly its
one-dimensional zero mode. -/
theorem closedPolynomialGenerator_kernel_iff (n : ℕ) (hn : 2 ≤ n)
    (u : GinibrePolynomialL2 n) :
    (u, 0) ∈ (closedPolynomialGenerator n hn).graph ↔
      ∃ c : ℂ, u = c • polynomialEigenfunctionL2 n hn (polynomialConstantIndex n) := by
  classical
  let i₀ := polynomialConstantIndex n
  let e₀ := polynomialEigenfunctionL2 n hn i₀
  constructor
  · intro hu
    have hs := closedPolynomialGenerator_input_mem_sector n hn (u, 0) hu
    have he : e₀ ∈ closedPolynomialSector n hn :=
      (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n hn))).le_topologicalClosure
        (Submodule.subset_span ⟨i₀, rfl⟩)
    have hd : inner ℂ e₀ e₀ ≠ 0 := by
      rw [inner_polynomialEigenfunctionL2]
      exact polynomialEigenfunction_inner_self_ne_zero n hn i₀
    let c := inner ℂ e₀ u / inner ℂ e₀ e₀
    have hz : u - c • e₀ = 0 := by
      apply closedPolynomialSector_eq_zero_of_inner_eigenvectors_zero n hn _
        ((closedPolynomialSector n hn).sub_mem hs
          ((closedPolynomialSector n hn).smul_mem c he))
      intro i
      rw [inner_sub_right, inner_smul_right]
      by_cases hi : i = i₀
      · subst i
        change inner ℂ e₀ u - (inner ℂ e₀ u / inner ℂ e₀ e₀) * inner ℂ e₀ e₀ = 0
        rw [div_mul_cancel₀ _ hd, sub_self]
      · have hiu := closedPolynomialGenerator_kernel_inner_zero n hn u hu i hi
        have hie : inner ℂ (polynomialEigenfunctionL2 n hn i) e₀ = 0 := by
          rw [inner_polynomialEigenfunctionL2]
          apply polynomialEigenfunction_equilibrium_orthogonal n hn
          rintro ⟨ha, hb, hm⟩
          apply hi
          change i = polynomialConstantIndex n
          cases i
          simp only [polynomialConstantIndex, PolynomialEigenfunctionData.mk.injEq]
          exact ⟨ha, hb, hm⟩
        rw [hiu, hie, mul_zero, sub_self]
    exact ⟨c, sub_eq_zero.mp hz⟩
  · rintro ⟨c, rfl⟩
    have he := polynomialEigenfunction_mem_closedGenerator_graph n hn (polynomialConstantIndex n)
    have hc := (closedPolynomialGenerator n hn).graph.smul_mem c he
    simpa [polynomialConstantIndex, eigenvalue] using hc

/-- The zero mode is literally the constant function one. -/
@[simp] theorem polynomialEigenfunction_constantIndex (n : ℕ) (z : Configuration n) :
    polynomialEigenfunction n (polynomialConstantIndex n) z = 1 := by
  simp [polynomialEigenfunction, polynomialConstantIndex, ComplexHermite.normalizedEval,
    ComplexHermite.normalized, ComplexHermite.oneDimNormalization]

/-- Kernel vectors of the closed polynomial generator have constant actual
Ginibre representatives almost everywhere. -/
theorem closedPolynomialGenerator_kernel_ae_constant (n : ℕ) (hn : 2 ≤ n)
    (u : GinibrePolynomialL2 n) (hu : (u, 0) ∈ (closedPolynomialGenerator n hn).graph) :
    ∃ c : ℂ, u =ᵐ[ginibreMeasure n] fun _ => c := by
  obtain ⟨c, rfl⟩ := (closedPolynomialGenerator_kernel_iff n hn u).mp hu
  refine ⟨c, ?_⟩
  filter_upwards [Lp.coeFn_smul c (polynomialEigenfunctionL2 n hn (polynomialConstantIndex n)),
    polynomialEigenfunctionL2_coeFn n hn (polynomialConstantIndex n)] with z hs he
  rw [hs, Pi.smul_apply, he, polynomialEigenfunction_constantIndex, smul_eq_mul, mul_one]

end
end GinibrePoincare

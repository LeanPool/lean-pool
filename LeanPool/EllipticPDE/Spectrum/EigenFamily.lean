/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Spectrum.HigherEigenvalues


/-!
# Eigenvalue sequence by iterated constrained minimisation

`EllipticPdes.Sobolev.exists_higher_eigenpair` produces one eigenpair orthogonal to a given
finite family. Iterating it produces, for every `n`, an `L²`-orthonormal family of `n` weak
eigenfunctions whose eigenvalues increase. That is the variational construction of the Dirichlet
spectrum, and it names every eigenvalue by a Rayleigh quotient rather than one at a time through
the spectral theorem, which is what `EllipticPdes.Sobolev.solOp_spectral` does.

The induction records one thing beyond the conclusion: every eigenvalue produced so far is at
most the infimum over the current constraint submodule. That is what makes the next eigenvalue
the largest, since the next one is exactly that infimum, and the constraint submodule shrinks at
each step, so the infima increase.

The recursion needs a vector orthogonal to the family at every stage, which is infinite
dimensionality of the `L²` image of `H₀¹(Ω)`. It is a hypothesis here, stated as the existence
of a single vector at each stage rather than as a dimension count.

## Main declarations

* `EllipticPdes.Sobolev.eigenvalueOn_mono`: tightening the constraint raises the infimum.
* `EllipticPdes.Sobolev.orthSubmodule_snoc_subset`: appending shrinks the constraint.
* `EllipticPdes.Sobolev.exists_eigen_family`: the orthonormal family and its increasing
  eigenvalues.
* `EllipticPdes.Sobolev.principalEigenvalue_le_of_eigen_family`: every eigenvalue of such a
  family is at least the principal one.
* `EllipticPdes.Sobolev.dirichlet_eigen_family_of_bounded`: the instance at `-Δ` on a bounded
  measurable domain, reading `0 < λ₁ ≤ ⋯ ≤ λₙ`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 1; James Guo, *Partial
Differential Equations*, Section VII.5.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-! ### Monotonicity of the constrained infimum -/

/-- **Tightening the constraint raises the infimum.** -/
lemma eigenvalueOn_mono (hco : IsCoercive B) {S S' : Set (H01 Ω)} (hsub : S ⊆ S')
    (hne : (rayleighSphere Ω ∩ S).Nonempty) :
    eigenvalueOn B S' ≤ eigenvalueOn B S :=
  csInf_le_csInf (rayleighValuesOn_bddBelow hco S') (hne.image _)
    (Set.image_mono (Set.inter_subset_inter_right _ hsub))

/-- A submodule with a vector of nonzero `L²` class meets the unit `L²` sphere: rescale. -/
lemma rayleighSphere_inter_nonempty {K : Submodule ℝ (H01 Ω)}
    (h : ∃ U ∈ K, embL2 Ω U ≠ 0) : (rayleighSphere Ω ∩ (K : Set (H01 Ω))).Nonempty := by
  obtain ⟨U, hUK, hU⟩ := h
  have hpos : 0 < ‖embL2 Ω U‖ := norm_pos_iff.mpr hU
  refine ⟨‖embL2 Ω U‖⁻¹ • U, ?_, K.smul_mem _ hUK⟩
  simp only [rayleighSphere, Set.mem_ofPred_eq, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ hpos.ne'

/-- **Appending a vector shrinks the constraint submodule.** -/
lemma orthSubmodule_snoc_subset {n : ℕ} (w : Fin n → H01 Ω) (U : H01 Ω) :
    ((orthSubmodule (Fin.snoc w U : Fin (n + 1) → H01 Ω)) : Set (H01 Ω))
      ⊆ ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω)) := by
  intro V hV i
  have h := hV i.castSucc
  rwa [Fin.snoc_castSucc] at h

/-! ### The family -/

/-- **Eigenvalue sequence.** For every `n` there is an `L²`-orthonormal family of `n` weak
eigenfunctions of `B` whose eigenvalues increase with the index. The hypothesis `hdim` supplies,
at each stage, a vector of nonzero `L²` class orthogonal to the family built so far; on a bounded
domain it is the infinite dimensionality of `H₀¹(Ω)`.

The fifth conclusion is the induction's own invariant: every eigenvalue produced so far is at
most the infimum over the current constraint submodule, which is what the next step returns. -/
theorem exists_eigen_family (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω))
    (hdim : ∀ (m : ℕ) (v : Fin m → H01 Ω), ∃ U ∈ orthSubmodule v, embL2 Ω U ≠ 0) (n : ℕ) :
    ∃ (w : Fin n → H01 Ω) (lam : Fin n → ℝ),
      (∀ i, ‖embL2 Ω (w i)‖ = 1) ∧
      (∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0) ∧
      (∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫) ∧
      (∀ i j, i ≤ j → lam i ≤ lam j) ∧
      (∀ i, lam i ≤ eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω))) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨w, lam, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨U, hUnorm, hUmem, hUmin⟩ :=
      exists_rayleigh_minimiser_on hco hsymm hRellich (orthSubmodule_weaklyClosed w)
        (rayleighSphere_inter_nonempty (hdim n w))
    set μ : ℝ := eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω)) with hμ
    have hUeq : ∀ V : H01 Ω, B U V = μ * ⟪embL2 Ω U, embL2 Ω V⟫ := fun V =>
      euler_lagrange_of_orthogonal_eigen hco hsymm h1 h2 h3 hUnorm hUmem hUmin V
    have hmuv : μ ≤ eigenvalueOn B
        ((orthSubmodule (Fin.snoc w U : Fin (n + 1) → H01 Ω) : Submodule ℝ (H01 Ω)) :
          Set (H01 Ω)) :=
      eigenvalueOn_mono hco (orthSubmodule_snoc_subset w U)
        (rayleighSphere_inter_nonempty (hdim (n + 1) (Fin.snoc w U)))
    refine ⟨Fin.snoc w U, Fin.snoc lam μ, ?_, ?_, ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ ?_
      · rw [Fin.snoc_last]
        exact hUnorm
      · intro i
        rw [Fin.snoc_castSucc]
        exact h1 i
    · refine Fin.lastCases ?_ ?_
      · refine Fin.lastCases ?_ ?_
        · intro hij
          exact absurd rfl hij
        · intro j _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hUmem j
      · intro i
        refine Fin.lastCases ?_ ?_
        · intro _
          rw [Fin.snoc_castSucc, Fin.snoc_last, real_inner_comm]
          exact hUmem i
        · intro j hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact h2 i j (fun h => hij (by rw [h]))
    · refine Fin.lastCases ?_ ?_
      · intro V
        rw [Fin.snoc_last, Fin.snoc_last]
        exact hUeq V
      · intro i V
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact h3 i V
    · refine Fin.lastCases ?_ ?_
      · refine Fin.lastCases ?_ ?_
        · intro _
          exact le_rfl
        · intro j hji
          exact absurd (Fin.castSucc_lt_last j) (not_lt.mpr hji)
      · intro i
        refine Fin.lastCases ?_ ?_
        · intro _
          rw [Fin.snoc_castSucc, Fin.snoc_last]
          exact h5 i
        · intro j hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact h4 i j (by simpa using hij)
    · refine Fin.lastCases ?_ ?_
      · rw [Fin.snoc_last]
        exact hmuv
      · intro i
        rw [Fin.snoc_castSucc]
        exact (h5 i).trans hmuv

/-- **Every eigenvalue of an orthonormal family is at least the principal one.** A member of the
family has unit `L²` norm and so is nonzero, which is what
`principalEigenvalue_le_of_weak_eigen` asks for. -/
theorem principalEigenvalue_le_of_eigen_family (hco : IsCoercive B) {n : ℕ} {w : Fin n → H01 Ω}
    {lam : Fin n → ℝ} (hwnorm : ∀ i, ‖embL2 Ω (w i)‖ = 1)
    (hweig : ∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫) (i : Fin n) :
    principalEigenvalue B ≤ lam i := by
  refine principalEigenvalue_le_of_weak_eigen hco (fun h0 => ?_) (hweig i)
  have h := hwnorm i
  rw [h0] at h
  simp at h

/-- **Dirichlet eigenvalue sequence on a bounded domain.** For every `n` there is an
`L²`-orthonormal family of `n` weak solutions of `-Δw = λw` with `0 < λ₁ ≤ ⋯ ≤ λₙ`. Boundedness
and measurability of `Ω` discharge coercivity and the compact embedding; `hdim` is the infinite
dimensionality of `H₀¹(Ω)`, stated as a vector at each stage. -/
theorem dirichlet_eigen_family_of_bounded {m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (hdim : ∀ (k : ℕ) (v : Fin k → H01 Ω), ∃ U ∈ orthSubmodule v, embL2 Ω U ≠ 0) (n : ℕ) :
    ∃ (w : Fin n → H01 Ω) (lam : Fin n → ℝ),
      (∀ i, ‖embL2 Ω (w i)‖ = 1) ∧
      (∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0) ∧
      (∀ i, 0 < lam i) ∧
      (∀ i j, i ≤ j → lam i ≤ lam j) ∧
      (∀ i, ∀ V : H01 Ω, laplaceBilin Ω (w i) V
        = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫) := by
  have hco := EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded hΩb
  obtain ⟨U0, -, hU0⟩ := hdim 0 Fin.elim0
  have hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0 := ⟨U0, hU0⟩
  obtain ⟨w, lam, h1, h2, h3, h4, -⟩ :=
    exists_eigen_family hco (laplaceBilin_symm Ω) (embL2_isCompact hΩm hΩb) hdim n
  exact ⟨w, lam, h1, h2, fun i => lt_of_lt_of_le (principalEigenvalue_pos hco hne)
    (principalEigenvalue_le_of_eigen_family hco h1 h3 i), h4, h3⟩

end EllipticPdes.Sobolev

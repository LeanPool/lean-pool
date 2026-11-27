/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SkewBasisAssembly

/-!
# Full real skew normal form in finite dimension

An injective skew-adjoint real endomorphism has an actual orthonormal
basis of positive-frequency rotation pairs. The proof recursively removes
the constructed invariant plane and uses the actual restriction to its
orthogonal complement. In the ordered pair `(0,1)` the block is
`[[0,-ν],[ν,0]]`; this orientation is part of the public statement.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The real skew normal form, with a genuine orthonormal basis and strictly
positive rotation frequencies. The zero-dimensional case is included. -/
theorem exists_real_skew_normal_form (A : E →ₗ[ℝ] E)
    (hA : A.adjoint = -A) (hinj : Function.Injective A) :
    ∃ (m : ℕ) (ν : Fin m → ℝ) (b : OrthonormalBasis (Fin m × Fin 2) ℝ E),
      (∀ i, 0 < ν i) ∧
      ∀ i, A (b (i, 0)) = ν i • b (i, 1) ∧
        A (b (i, 1)) = (-ν i) • b (i, 0) := by
  classical
  suffices ∀ n, Module.finrank ℝ E = n →
      ∃ (m : ℕ) (ν : Fin m → ℝ) (b : OrthonormalBasis (Fin m × Fin 2) ℝ E),
        (∀ i, 0 < ν i) ∧
        ∀ i, A (b (i, 0)) = ν i • b (i, 1) ∧
          A (b (i, 1)) = (-ν i) • b (i, 0) from this _ rfl
  intro n hdim
  induction n using Nat.strong_induction_on generalizing E with
  | ind n ih =>
    by_cases hn : n = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp (hdim.trans hn)
      let f : Fin 0 × Fin 2 → E := fun i => Fin.elim0 i.1
      have hf : Orthonormal ℝ f := by
        rw [orthonormal_iff_ite]
        intro i
        exact Fin.elim0 i.1
      have hspan : ⊤ ≤ Submodule.span ℝ (Set.range f) := by
        intro x _
        have hx : x = 0 := Subsingleton.elim _ _
        rw [hx]
        exact Submodule.zero_mem _
      refine ⟨0, (fun i => Fin.elim0 i), OrthonormalBasis.mk hf hspan, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    · have : Nontrivial E := Module.nontrivial_of_finrank_pos
        (by rw [hdim]; exact Nat.pos_of_ne_zero hn)
      obtain ⟨a, x, y, ha, hx, hy, hxy, hAx, hAy⟩ :=
        exists_skew_rotation_plane A hA hinj
      let P := rotationPlane x y
      have hPdim : Module.finrank ℝ P = 2 := finrank_rotationPlane hx hy hxy
      have hP : ∀ z ∈ P, A z ∈ P := maps_rotationPlane A hAx hAy
      have hPo : ∀ z ∈ Pᗮ, A z ∈ Pᗮ := real_skew_maps_orthogonal A hA P hP
      have hlt : Module.finrank ℝ Pᗮ < n := by
        have hsum := P.finrank_add_finrank_orthogonal
        omega
      obtain ⟨m, ν, b, hν, hb⟩ := ih (Module.finrank ℝ Pᗮ) hlt
        (A.restrict hPo) (real_skew_restrict A hA Pᗮ hPo)
        (injective_restrict A hinj Pᗮ hPo) rfl
      refine ⟨m + 1, Fin.cases a ν, adjoinRotationBasis hx hy hxy b, ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero => exact ha
        | succ i => exact hν i
      · intro i
        induction i using Fin.cases with
        | zero => simpa using And.intro hAx hAy
        | succ i =>
          constructor
          · simpa only [Fin.cases_succ, adjoinRotationBasis_succ, LinearMap.restrict_apply,
              Submodule.coe_smul] using
              congrArg (fun z : Pᗮ => (z : E)) (hb i).1
          · simpa only [Fin.cases_succ, adjoinRotationBasis_succ, LinearMap.restrict_apply,
              Submodule.coe_smul] using
              congrArg (fun z : Pᗮ => (z : E)) (hb i).2

/-- In particular, an injective real skew-adjoint operator forces the
ambient real dimension to be even. -/
theorem even_finrank_of_injective_real_skew (A : E →ₗ[ℝ] E)
    (hA : A.adjoint = -A) (hinj : Function.Injective A) :
    Even (Module.finrank ℝ E) := by
  obtain ⟨m, ν, b, hν, hb⟩ := exists_real_skew_normal_form A hA hinj
  have hdim := Module.finrank_eq_card_basis b.toBasis
  simp only [Fintype.card_prod, Fintype.card_fin] at hdim
  exact ⟨m, by omega⟩

end VacuumBellSeparation.Gaussian

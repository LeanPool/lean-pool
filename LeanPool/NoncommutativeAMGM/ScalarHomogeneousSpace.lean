/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Data.Fintype.Powerset

/-! # Complex and real homogeneous incidence operators

Appendix C's adjoint and orthogonal splitting are constructed uniformly over every
`RCLike` scalar field, including the explicitly displayed complex coefficient space.
-/

@[expose] public section
namespace NoncommutativeAMGM

open scoped BigOperators

/-- The square-free monomials of exactly degree `r`. -/
abbrev HomogeneousIndex (n r : ℕ) := {S : Finset (Fin n) // S.card = r}

variable (𝕜 : Type*) [RCLike 𝕜]

/-- Euclidean coefficient space of homogeneous square-free polynomials. -/
abbrev ScalarHomogeneousSpace (n r : ℕ) := EuclideanSpace 𝕜 (HomogeneousIndex n r)

/-- The incidence operator adding one new variable to a square-free monomial. -/
noncomputable def scalarHomogeneousUp (n r : ℕ) :
    ScalarHomogeneousSpace 𝕜 n r →ₗ[𝕜] ScalarHomogeneousSpace 𝕜 n (r + 1) where
  toFun c := WithLp.toLp 2 (fun T ↦ ∑ S : HomogeneousIndex n r,
    if S.val ⊆ T.val then c S else 0)
  map_add' c d := by
    ext T
    simp only [PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp
  map_smul' a c := by
    ext T
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp

/-- The coefficient Laplacian, removing one variable from a square-free monomial. -/
noncomputable def scalarHomogeneousDown (n r : ℕ) :
    ScalarHomogeneousSpace 𝕜 n (r + 1) →ₗ[𝕜] ScalarHomogeneousSpace 𝕜 n r where
  toFun c := WithLp.toLp 2 (fun S ↦ ∑ T : HomogeneousIndex n (r + 1),
    if S.val ⊆ T.val then c T else 0)
  map_add' c d := by
    ext S
    simp only [PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp
  map_smul' a c := by
    ext S
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp

theorem scalarHomogeneousUp_apply {n r : ℕ} (c : ScalarHomogeneousSpace 𝕜 n r)
    (T : HomogeneousIndex n (r + 1)) :
    scalarHomogeneousUp 𝕜 n r c T = ∑ S : HomogeneousIndex n r,
      if S.val ⊆ T.val then c S else 0 := rfl

theorem scalarHomogeneousDown_apply {n r : ℕ} (c : ScalarHomogeneousSpace 𝕜 n (r + 1))
    (S : HomogeneousIndex n r) :
    scalarHomogeneousDown 𝕜 n r c S = ∑ T : HomogeneousIndex n (r + 1),
      if S.val ⊆ T.val then c T else 0 := rfl

/-- The actual subset-incidence up operator is the adjoint of the Laplacian. -/
theorem scalarHomogeneousUp_eq_adjoint (n r : ℕ) :
    scalarHomogeneousUp 𝕜 n r = (scalarHomogeneousDown 𝕜 n r).adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro c d
  simp only [PiLp.inner_apply, RCLike.inner_apply, scalarHomogeneousUp_apply,
    scalarHomogeneousDown_apply]
  simp_rw [map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

/-- Orthogonality to all raised polynomials is exactly harmonicity. -/
theorem scalarHomogeneousUp_range_orthogonal (n r : ℕ) :
    (scalarHomogeneousUp 𝕜 n r).rangeᗮ = (scalarHomogeneousDown 𝕜 n r).ker := by
  rw [scalarHomogeneousUp_eq_adjoint, LinearMap.orthogonal_range, LinearMap.adjoint_adjoint]

/-- Every homogeneous coefficient vector is a harmonic vector plus a raised vector. -/
theorem scalarHomogeneous_harmonic_decomposition {n r : ℕ}
    (c : ScalarHomogeneousSpace 𝕜 n (r + 1)) :
    ∃ h : ScalarHomogeneousSpace 𝕜 n (r + 1), ∃ q : ScalarHomogeneousSpace 𝕜 n r,
      scalarHomogeneousDown 𝕜 n r h = 0 ∧ c = h + scalarHomogeneousUp 𝕜 n r q := by
  obtain ⟨v, hv, h, hh, hc⟩ :=
    (scalarHomogeneousUp 𝕜 n r).range.exists_add_mem_mem_orthogonal c
  obtain ⟨q, rfl⟩ := hv
  rw [scalarHomogeneousUp_range_orthogonal] at hh
  exact ⟨h, q, hh, hc.trans (add_comm _ _)⟩

end NoncommutativeAMGM

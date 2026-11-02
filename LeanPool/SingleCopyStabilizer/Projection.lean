/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Symplectic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal


/-! Rank-nullity and the X-projection / diagonal-orthogonal identity. -/

@[expose] public section


namespace LeanPool.SingleCopyStabilizer

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate dot product regarded as a bilinear form. -/
def dotForm : LinearMap.BilinForm 𝕜 (Vec 𝕜 ι) := dotProductBilin 𝕜 𝕜

omit [DecidableEq ι] in
theorem dotForm_nondegenerate : (dotForm (𝕜 := 𝕜) (ι := ι)).Nondegenerate := by
  classical
  constructor
  · intro x hx
    funext i
    simpa [dotForm] using hx (Pi.single i 1)
  · intro x hx
    funext i
    simpa [dotForm] using hx (Pi.single i 1)

omit [DecidableEq ι] in
theorem dotForm_refl : (dotForm (𝕜 := 𝕜) (ι := ι)).IsRefl := by
  classical
  intro x y hxy
  change y ⬝ᵥ x = 0
  rw [dotProduct_comm]
  exact hxy
/-- The annihilator of a subspace under the coordinate dot product. -/
def dotOrthogonal (D : Submodule 𝕜 (Vec 𝕜 ι)) : Submodule 𝕜 (Vec 𝕜 ι) :=
  dotForm.orthogonal D

omit [DecidableEq ι] in
@[simp] theorem mem_dotOrthogonal (D : Submodule 𝕜 (Vec 𝕜 ι)) (x : Vec 𝕜 ι) :
    x ∈ dotOrthogonal D ↔ ∀ s ∈ D, x ⬝ᵥ s = 0 := by
  classical
  change (∀ s ∈ D, s ⬝ᵥ x = 0) ↔ _
  simp only [dotProduct_comm]

omit [DecidableEq ι] in
theorem finrank_dotOrthogonal (D : Submodule 𝕜 (Vec 𝕜 ι)) :
    Module.finrank 𝕜 (dotOrthogonal D) = Fintype.card ι - Module.finrank 𝕜 D := by
  classical
  rw [dotOrthogonal, LinearMap.BilinForm.finrank_orthogonal
    dotForm_nondegenerate]
  simp
/-- The X-coordinate image of a space of Pauli labels. -/
def xProjection (L : Submodule 𝕜 (Label 𝕜 ι)) : Submodule 𝕜 (Vec 𝕜 ι) :=
  L.map (LinearMap.fst 𝕜 (Vec 𝕜 ι) (Vec 𝕜 ι))

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem mem_xProjection (L : Submodule 𝕜 (Label 𝕜 ι)) (x : Vec 𝕜 ι) :
    x ∈ xProjection L ↔ ∃ z, (x, z) ∈ L := by
  classical
  constructor
  · rintro ⟨⟨y,z⟩, hyz, h⟩
    exact ⟨z, by simpa using h ▸ hyz⟩
  · rintro ⟨z, hz⟩
    exact ⟨(x, z), hz, rfl⟩
/-- The X projection with domain restricted to a given label space. -/
def xRestricted (L : Submodule 𝕜 (Label 𝕜 ι)) : L →ₗ[𝕜] Vec 𝕜 ι :=
  (LinearMap.fst 𝕜 (Vec 𝕜 ι) (Vec 𝕜 ι)).domRestrict L

/-- Identify diagonal labels with the kernel of the restricted X projection. -/
def diagonalKernelEquiv (L : Submodule 𝕜 (Label 𝕜 ι)) :
    diagonalSpace L ≃ₗ[𝕜] LinearMap.ker (xRestricted L) where
  toFun z := ⟨⟨(0,z),z.property⟩,rfl⟩
  invFun a := ⟨a.val.val.2, by
    have hx : a.val.val.1 = 0 := a.property
    change (0, a.val.val.2) ∈ L
    rw [← hx]
    exact a.val.property⟩
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact a.property.symm
    · rfl
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_smul' c z := by
    apply Subtype.ext
    apply Subtype.ext
    simp

omit [DecidableEq ι] [Fintype ι] in
/-- Rank-nullity with the diagonal kernel explicitly identified. -/
theorem finrank_xProjection_add_diagonal [Finite ι] (L : Submodule 𝕜 (Label 𝕜 ι)) :
    Module.finrank 𝕜 (xProjection L) + Module.finrank 𝕜 (diagonalSpace L) =
      Module.finrank 𝕜 L := by
  let := Fintype.ofFinite ι
  classical
  have h := (xRestricted L).finrank_range_add_finrank_ker
  rw [← (diagonalKernelEquiv L).finrank_eq] at h
  have hr : LinearMap.range (xRestricted L) = xProjection L := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a,ha⟩, rfl⟩
  rw [hr] at h
  exact h

omit [DecidableEq ι] in
theorem xProjection_le_orthogonal (L : Submodule 𝕜 (Label 𝕜 ι))
    (hL : IsIsotropic L) : xProjection L ≤ dotOrthogonal (diagonalSpace L) := by
  classical
  intro x hx
  obtain ⟨z, hz⟩ := (mem_xProjection L x).mp hx
  rw [mem_dotOrthogonal]
  intro s hs
  exact x_orthogonal_diagonal hL hz hs

omit [DecidableEq ι] in
/-- For a Lagrangian label space, the X projection is exactly the orthogonal
complement of the diagonal labels. -/
theorem lagrangian_xProjection_eq (L : Submodule 𝕜 (Label 𝕜 ι))
    (hL : IsIsotropic L) (hdim : Module.finrank 𝕜 L = Fintype.card ι) :
    xProjection L = dotOrthogonal (diagonalSpace L) := by
  classical
  apply Submodule.eq_of_le_of_finrank_eq (xProjection_le_orthogonal L hL)
  have h := finrank_xProjection_add_diagonal L
  rw [finrank_dotOrthogonal]
  omega

omit [DecidableEq ι] in
/-- The general dimension identity underlying the nullity argument. -/
theorem low_nullity_projection_codimension
    (L : Submodule 𝕜 (Label 𝕜 ι)) (r : ℕ)
    (hdim : Module.finrank 𝕜 L + r = Fintype.card ι) :
    Module.finrank 𝕜 (xProjection L) + r =
      Module.finrank 𝕜 (dotOrthogonal (diagonalSpace L)) := by
  classical
  have h := finrank_xProjection_add_diagonal L
  rw [finrank_dotOrthogonal]
  omega

omit [DecidableEq ι] in
/-- Isotropy bounds stabilizer dimension by the number of sites. -/
theorem isotropic_finrank_le (L : Submodule 𝕜 (Label 𝕜 ι)) (hL : IsIsotropic L) :
    Module.finrank 𝕜 L ≤ Fintype.card ι := by
  classical
  have h := finrank_xProjection_add_diagonal L
  have hle := Submodule.finrank_mono (xProjection_le_orthogonal L hL)
  rw [finrank_dotOrthogonal] at hle
  have hD : Module.finrank 𝕜 (diagonalSpace L) ≤ Fintype.card ι := by
    simpa using (diagonalSpace L).finrank_le
  omega

omit [DecidableEq ι] [Fintype ι] in
/-- When diagonal dimension reaches total stabilizer dimension, every
stabilizer is diagonal. This applies to the low-nullity stopping criterion. -/
theorem all_diagonal_of_max_dimension [Finite ι] (L : Submodule 𝕜 (Label 𝕜 ι))
    (hdim : Module.finrank 𝕜 (diagonalSpace L) = Module.finrank 𝕜 L) :
    ∀ a ∈ L, a.1 = 0 := by
  let := Fintype.ofFinite ι
  classical
  have h := finrank_xProjection_add_diagonal L
  have hzero : Module.finrank 𝕜 (xProjection L) = 0 := by omega
  have hbot := Submodule.finrank_eq_zero.mp hzero
  intro a ha
  have hx : a.1 ∈ xProjection L := (mem_xProjection L a.1).mpr ⟨a.2, ha⟩
  simpa [hbot] using hx

omit [DecidableEq ι] in
/-- Full diagonal dimension means all diagonal labels are present. -/
theorem diagonalSpace_eq_top_of_full_dimension (L : Submodule 𝕜 (Label 𝕜 ι))
    (hdim : Module.finrank 𝕜 (diagonalSpace L) = Fintype.card ι) :
    diagonalSpace L = ⊤ := by
  classical
  apply Submodule.eq_top_of_finrank_eq
  simpa using hdim

end LeanPool.SingleCopyStabilizer

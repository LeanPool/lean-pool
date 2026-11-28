/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-
Modified for Lean Pool: module names and imports adapted.

The adapted orthogonal-span proof is from `TauCeti/Analysis/InnerProductSpace/Spectrum.lean`.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Hilbert bases of eigenvectors of compact self-adjoint operators

Mathlib's spectral theorem for a compact self-adjoint operator `T` on a Hilbert space `E` says
that the orthogonal complement of the sum of all eigenspaces of `T` is `{0}`
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`).  This file turns it into
a **Hilbert basis of eigenvectors**.

Each eigenspace is closed, hence a Hilbert space.  For every choice of Hilbert bases of the
eigenspaces, the family indexed by the pairs `⟨μ, j⟩` of a scalar `μ` and an index `j` of the
basis of the eigenspace of `μ` is a Hilbert basis of `E`
(`ContinuousLinearMap.hilbertBasisOfEigenspaces`), so the eigenvalue of `⟨μ, j⟩` is `μ` itself:
the eigenspaces are mutually orthogonal, so the union of their bases is orthonormal, and a vector
orthogonal to all of it is orthogonal to every eigenspace, hence zero.  No separability is
assumed.  For injective `T` the eigenspace of `0` has an empty basis
(`ContinuousLinearMap.isEmpty_hilbertBasis_eigenspace_zero`).  The chosen bases
`ContinuousLinearMap.eigenspaceBasis` give the basis `ContinuousLinearMap.eigenHilbertBasis`
with the index `ContinuousLinearMap.eigenIndex`.

The construction follows the proof of
`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces` in TauCeti
(`TauCeti/Analysis/InnerProductSpace/Spectrum.lean`), turned into definitions.  The helper
`HilbertBasis.inner_eq_zero_of_forall_inner_eq_zero` (TauCeti
`Analysis/InnerProductSpace/HilbertBasis/Basic.lean`) is imported, along with
`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero` from `Spectrum.lean`.
Both were available at commit `463ab293` under Apache-2.0.
-/

@[expose] public section

open Module.End
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ContinuousLinearMap

variable [CompleteSpace E] (T : E →L[𝕜] E)

/-- An eigenspace of a bounded operator on a Hilbert space is complete, since it is closed. -/
instance completeSpace_eigenspace (μ : 𝕜) :
    CompleteSpace (eigenspace (T : Module.End 𝕜 E) μ) :=
  (isClosed_eigenspace T μ).completeSpace_coe

/-- The index set of the chosen Hilbert basis of the eigenspace of `μ`: a set of vectors of the
eigenspace, as in Mathlib's `exists_hilbertBasis`. -/
noncomputable def eigenspaceIndex (μ : 𝕜) : Set (eigenspace (T : Module.End 𝕜 E) μ) :=
  (exists_hilbertBasis 𝕜 (eigenspace (T : Module.End 𝕜 E) μ)).choose

/-- A chosen Hilbert basis of the eigenspace of `μ` (the empty family if `μ` is no
eigenvalue). -/
noncomputable def eigenspaceBasis (μ : 𝕜) :
    HilbertBasis (T.eigenspaceIndex μ) 𝕜 (eigenspace (T : Module.End 𝕜 E) μ) :=
  (exists_hilbertBasis 𝕜 (eigenspace (T : Module.End 𝕜 E) μ)).choose_spec.choose

/-- The index set of the eigenvector basis: pairs `⟨μ, j⟩` of a scalar `μ` and an index `j` of
the Hilbert basis of the eigenspace of `μ`. -/
abbrev eigenIndex : Type _ := Σ μ : 𝕜, T.eigenspaceIndex μ

/-- The eigenvector with index `⟨μ, j⟩`: the `j`-th vector of the basis of the eigenspace of
`μ`, as a vector of `E`. -/
noncomputable def eigenvector (i : T.eigenIndex) : E := (T.eigenspaceBasis i.1 i.2 : E)

/-- The eigenvector with index `⟨μ, j⟩` lies in the eigenspace of `μ`. -/
theorem eigenvector_mem (i : T.eigenIndex) :
    T.eigenvector i ∈ eigenspace (T : Module.End 𝕜 E) i.1 :=
  (T.eigenspaceBasis i.1 i.2).2

/-- `T e_{⟨μ, j⟩} = μ e_{⟨μ, j⟩}`. -/
theorem apply_eigenvector (i : T.eigenIndex) : T (T.eigenvector i) = i.1 • T.eigenvector i :=
  mem_eigenspace_iff.1 (T.eigenvector_mem i)

/-- The eigenvectors are unit vectors. -/
theorem norm_eigenvector (i : T.eigenIndex) : ‖T.eigenvector i‖ = 1 :=
  (T.eigenspaceBasis i.1).orthonormal.1 i.2

/-- The eigenvector with index `⟨μ, j⟩` is an eigenvector of `T` for the eigenvalue `μ`. -/
theorem hasEigenvector_eigenvector (i : T.eigenIndex) :
    HasEigenvector (T : Module.End 𝕜 E) i.1 (T.eigenvector i) :=
  ⟨T.eigenvector_mem i, fun h => by simpa [h] using T.norm_eigenvector i⟩

variable {T}

/-! ### Arbitrary Hilbert bases of the eigenspaces -/

omit [CompleteSpace E] in
/-- **For injective `T` the eigenspace of `0` has an empty Hilbert basis**: the eigenspace of `0`
is the kernel, which is `{0}`, while the members of a Hilbert basis are unit vectors. -/
theorem isEmpty_hilbertBasis_eigenspace_zero (hker : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥)
    {ι : Type*} (b : HilbertBasis ι 𝕜 (eigenspace (T : Module.End 𝕜 E) 0)) : IsEmpty ι := by
  refine ⟨fun j => ?_⟩
  have h0 : T (b j : E) = 0 := by simpa using mem_eigenspace_iff.1 (b j).2
  have hmem : (b j : E) ∈ LinearMap.ker (T : E →ₗ[𝕜] E) := h0
  rw [hker, Submodule.mem_bot] at hmem
  have h1 : ‖(b j : E)‖ = 1 := b.orthonormal.1 j
  rw [hmem, norm_zero] at h1
  exact zero_ne_one h1

omit [CompleteSpace E] in
/-- For every choice of Hilbert bases `(b μ)` of the eigenspaces of a symmetric operator, the
family of all their vectors, indexed by the pairs `⟨μ, j⟩`, is orthonormal: each `b μ` is
orthonormal and the eigenspaces are mutually orthogonal. -/
theorem orthonormal_sigma_eigenspaces (hT : (T : E →ₗ[𝕜] E).IsSymmetric) {w : 𝕜 → Type*}
    (b : ∀ μ, HilbertBasis (w μ) 𝕜 (eigenspace (T : Module.End 𝕜 E) μ)) :
    Orthonormal 𝕜 (fun i : Σ μ, w μ => (b i.1 i.2 : E)) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun μ => (b μ).orthonormal

omit [CompleteSpace E] in
/-- If the orthogonal complement of the sum of all eigenspaces is `{0}`, then for every choice of
Hilbert bases `(b μ)` of the eigenspaces the orthogonal complement of the span of all their
vectors is `{0}`: a vector orthogonal to every `b μ j` is orthogonal to every eigenspace
(`HilbertBasis.inner_eq_zero_of_forall_inner_eq_zero`). -/
theorem orthogonal_span_sigma_eigenspaces_eq_bot
    (hspan : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) {w : 𝕜 → Type*}
    (b : ∀ μ, HilbertBasis (w μ) 𝕜 (eigenspace (T : Module.End 𝕜 E) μ)) :
    (Submodule.span 𝕜 (Set.range fun i : Σ μ, w μ => (b i.1 i.2 : E)))ᗮ = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [← hspan, ← Submodule.iInf_orthogonal]
  intro x hx
  have hx' : ∀ i : Σ μ, w μ, ⟪x, (b i.1 i.2 : E)⟫_𝕜 = 0 := fun i =>
    (Submodule.mem_orthogonal' _ x).mp hx _ (Submodule.subset_span ⟨i, rfl⟩)
  simp only [Submodule.mem_iInf]
  intro μ
  rw [Submodule.mem_orthogonal']
  exact fun y hy => (b μ).inner_eq_zero_of_forall_inner_eq_zero (fun j => hx' ⟨μ, j⟩) hy

/-- **The Hilbert basis of eigenvectors** of a symmetric operator such that the orthogonal
complement of the sum of all eigenspaces is `{0}`, for a given choice of Hilbert bases `(b μ)` of
the eigenspaces: the family of all vectors of all `b μ`, indexed by the pairs `⟨μ, j⟩`.  For a
compact self-adjoint operator the hypothesis is Mathlib's spectral theorem
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`.  The construction follows the
proof of `ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces` in
TauCeti (`TauCeti/Analysis/InnerProductSpace/Spectrum.lean`, commit `463ab293`, Apache-2.0);
unlike Brezis 2011, Theorem 6.11, no separability is assumed. -/
noncomputable def hilbertBasisOfEigenspaces (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    {w : 𝕜 → Type*} (b : ∀ μ, HilbertBasis (w μ) 𝕜 (eigenspace (T : Module.End 𝕜 E) μ))
    (hspan : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) : HilbertBasis (Σ μ, w μ) 𝕜 E :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_sigma_eigenspaces hT b)
    (orthogonal_span_sigma_eigenspaces_eq_bot hspan b)

/-- The vector of `hilbertBasisOfEigenspaces` with index `⟨μ, j⟩` is the `j`-th vector of the
basis `b μ` of the eigenspace of `μ`. -/
@[simp]
theorem coe_hilbertBasisOfEigenspaces (hT : (T : E →ₗ[𝕜] E).IsSymmetric) {w : 𝕜 → Type*}
    (b : ∀ μ, HilbertBasis (w μ) 𝕜 (eigenspace (T : Module.End 𝕜 E) μ))
    (hspan : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) :
    ⇑(hilbertBasisOfEigenspaces hT b hspan) = fun i => (b i.1 i.2 : E) :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The vector of `hilbertBasisOfEigenspaces` with index `⟨μ, j⟩` is an eigenvector for `μ`:
`T e_{⟨μ, j⟩} = μ e_{⟨μ, j⟩}`. -/
theorem apply_hilbertBasisOfEigenspaces (hT : (T : E →ₗ[𝕜] E).IsSymmetric) {w : 𝕜 → Type*}
    (b : ∀ μ, HilbertBasis (w μ) 𝕜 (eigenspace (T : Module.End 𝕜 E) μ))
    (hspan : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) (i : Σ μ, w μ) :
    T (hilbertBasisOfEigenspaces hT b hspan i) = i.1 • hilbertBasisOfEigenspaces hT b hspan i := by
  rw [coe_hilbertBasisOfEigenspaces]
  exact mem_eigenspace_iff.1 (b i.1 i.2).2

/-! ### The chosen Hilbert bases of the eigenspaces -/

variable (T) in
/-- **For injective `T` every eigenvalue in the index is nonzero**, since the eigenspace of `0`
has an empty basis (`ContinuousLinearMap.isEmpty_hilbertBasis_eigenspace_zero`). -/
theorem eigenIndex_fst_ne_zero (hker : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) (i : T.eigenIndex) :
    i.1 ≠ 0 := by
  obtain ⟨μ, j⟩ := i
  intro h0
  simp only at h0
  subst h0
  exact (isEmpty_hilbertBasis_eigenspace_zero hker (T.eigenspaceBasis 0)).false j

/-- The eigenvectors of a symmetric operator form an orthonormal family
(`ContinuousLinearMap.orthonormal_sigma_eigenspaces` for the chosen bases). -/
theorem orthonormal_eigenvector (hT : (T : E →ₗ[𝕜] E).IsSymmetric) :
    Orthonormal 𝕜 T.eigenvector :=
  orthonormal_sigma_eigenspaces hT T.eigenspaceBasis

/-- If the orthogonal complement of the sum of all eigenspaces is `{0}`, so is the orthogonal
complement of the span of the eigenvectors
(`ContinuousLinearMap.orthogonal_span_sigma_eigenspaces_eq_bot` for the chosen bases). -/
theorem orthogonal_span_eigenvector_eq_bot
    (hspan : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) :
    (Submodule.span 𝕜 (Set.range T.eigenvector))ᗮ = ⊥ :=
  orthogonal_span_sigma_eigenspaces_eq_bot hspan T.eigenspaceBasis

/-- **The Hilbert basis of eigenvectors** of a symmetric operator such that the orthogonal
complement of the sum of all eigenspaces is `{0}`, for the chosen bases of the eigenspaces
(`ContinuousLinearMap.eigenspaceBasis`), indexed by `T.eigenIndex`. -/
noncomputable def eigenHilbertBasis (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hspan : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) : HilbertBasis T.eigenIndex 𝕜 E :=
  hilbertBasisOfEigenspaces hT T.eigenspaceBasis hspan

/-- The vectors of the eigenvector basis are the eigenvectors. -/
@[simp]
theorem coe_eigenHilbertBasis (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hspan : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) :
    ⇑(eigenHilbertBasis hT hspan) = T.eigenvector :=
  coe_hilbertBasisOfEigenspaces hT T.eigenspaceBasis hspan

end ContinuousLinearMap

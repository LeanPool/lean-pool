/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Modified for Lean/Mathlib 4.35.0: add the explicit inner-product Haar-measure import.

# The covolume of a lattice as a Gram determinant

For a `ℤ`-lattice `L` in a finite-dimensional real inner product space, the covolume of `L` — the
volume of a fundamental domain for the canonical measure, the one giving the parallelepiped of an
orthonormal basis volume `1` — is the square root of the Gram determinant `det ⟪b i, b j⟫` of any
`ℤ`-basis `b` of `L`.

This is the form in which a covolume is computed in the geometry of numbers whenever the lattice
is presented by generators rather than by a fundamental domain, and it is the step that turns the
covolume of a lattice of rational points into a sum of squares of maximal minors: composed with the
Cauchy–Binet identity it says that the squared covolume of the lattice spanned by the rows of a
matrix is the sum of the squares of its maximal minors.

Mathlib has `ZLattice.covolume_eq_det`, the corresponding statement in `ι → ℝ` with the Lebesgue
measure, where the answer is the determinant of the basis matrix; in an inner product space there
is no ambient basis to take a determinant against, and the Gram matrix is what replaces it.

## Main results

* `ZLattice.covolume_eq_abs_det_orthonormalBasis`: the covolume is the absolute determinant of the
  coordinate matrix of a `ℤ`-basis in any orthonormal basis of the ambient space.
* `ZLattice.covolume_sq_eq_det_gram`: the squared covolume is the Gram determinant of any
  `ℤ`-basis.
* `ZLattice.covolume_eq_sqrt_det_gram`: the covolume is the square root of that determinant.

## Implementation notes

Mathlib's naming convention in `Mathlib/Algebra/Module/ZLattice/Covolume.lean` is that a result
about `ι → ℝ` carries the plain name and its `InnerProductSpace` counterpart carries a prime. The
three results here are not primed counterparts of anything: `covolume_eq_det` has no Gram matrix
in it, and the Gram determinant is not available in `ι → ℝ` without choosing an inner product.

The index type of the `ℤ`-basis is arbitrary; the orthonormal basis of the ambient space is
obtained from `stdOrthonormalBasis` by reindexing along the equivalence that
`ZLattice.rank`— through `Basis.ofZLatticeBasis` — provides, so no hypothesis relating the index
type to `Module.finrank` is needed.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter I, §2.1,
pp. 9–10, defines the lattice determinant as the absolute determinant of a basis matrix.
The Gram formula proved here is the corresponding Euclidean computation for a lattice in a
subspace, using orthonormal coordinates on its span.

This is Layer 4.3 of the `ArithmeticHeights` roadmap, the infrastructure half: the covolume
identity of that milestone is proved by computing both sides of it against a Gram determinant.
-/

public section

noncomputable section

namespace ZLattice

open Module MeasureTheory Matrix Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The covolume against an orthonormal basis.** The parallelepiped of an orthonormal basis has
volume `1`, so the covolume of a lattice is the absolute determinant of the coordinates of any of
its `ℤ`-bases in any orthonormal basis of the ambient space. -/
theorem covolume_eq_abs_det_orthonormalBasis (b : Basis κ ℤ L) (o : OrthonormalBasis κ ℝ E) :
    covolume L = |(o.toBasis.toMatrix ((↑) ∘ b)).det| := by
  have hfd : (volume : Measure E).real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simp [measureReal_def, o.volume_parallelepiped]
  rw [covolume_eq_det_mul_measureReal L volume b o.toBasis, hfd, mul_one, Basis.det_apply]

/-- **The squared covolume is the Gram determinant of any `ℤ`-basis.** -/
theorem covolume_sq_eq_det_gram (b : Basis κ ℤ L) :
    covolume L ^ 2 = (Matrix.of fun i j ↦ inner ℝ (b i : E) (b j : E)).det := by
  have hcard : Fintype.card κ = finrank ℝ E :=
    (finrank_eq_card_basis (b.ofZLatticeBasis ℝ L)).symm
  let o : OrthonormalBasis κ ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hcard).symm
  have hG : (Matrix.of fun i j ↦ inner ℝ (b i : E) (b j : E))
      = (o.toBasis.toMatrix ((↑) ∘ b))ᵀ * o.toBasis.toMatrix ((↑) ∘ b) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Basis.toMatrix_apply, Function.comp_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Matrix.of_apply]
    rw [← o.sum_inner_mul_inner (b i : E) (b j : E)]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [real_inner_comm]
  rw [hG, covolume_eq_abs_det_orthonormalBasis L b o, Matrix.det_mul, Matrix.det_transpose, ← sq,
    sq_abs]

/-- **The covolume is the square root of the Gram determinant of any `ℤ`-basis.** -/
theorem covolume_eq_sqrt_det_gram (b : Basis κ ℤ L) :
    covolume L = √((Matrix.of fun i j ↦ inner ℝ (b i : E) (b j : E)).det) := by
  rw [← covolume_sq_eq_det_gram L b, Real.sqrt_sq (covolume_pos L volume).le]

section Comp

omit [MeasurableSpace E] [BorelSpace E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **A linear map multiplies a Gram determinant by the determinant of its Gram operator.** If
`A` satisfies `⟪f x, f y⟫ = ⟪A x, y⟫` — that is, `A = f* f` — then the Gram matrix of the image of
a basis is `Mᵀ G`, with `G` the Gram matrix of the basis and `M` the matrix of `A`. This is the
linear-algebra form of the statement that a linear map scales volume by `√(det (f* f))`, which is
the factor by which it scales a covolume. -/
theorem det_gram_of_inner (f : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E) (b : Basis κ ℝ E)
    (h : ∀ x y, inner ℝ (f x) (f y) = inner ℝ (A x) y) :
    (Matrix.of fun i j ↦ inner ℝ (f (b i)) (f (b j))).det
      = A.det * (Matrix.of fun i j ↦ inner ℝ (b i) (b j)).det := by
  classical
  set M := LinearMap.toMatrix b b A with hM
  have key : (Matrix.of fun i j ↦ inner ℝ (f (b i)) (f (b j)))
      = Mᵀ * (Matrix.of fun i j ↦ inner ℝ (b i) (b j)) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    rw [h (b i) (b j), ← b.sum_repr (A (b i)), sum_inner]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [real_inner_smul_left, hM, LinearMap.toMatrix_apply]
  rw [key, Matrix.det_mul, Matrix.det_transpose, hM, LinearMap.det_toMatrix]

/-- The adjoint form of `ZLattice.det_gram_of_inner`. -/
theorem det_gram_comp (f : E →ₗ[ℝ] F) (b : Basis κ ℝ E) :
    (Matrix.of fun i j ↦ inner ℝ (f (b i)) (f (b j))).det
      = (LinearMap.adjoint f ∘ₗ f).det * (Matrix.of fun i j ↦ inner ℝ (b i) (b j)).det :=
  det_gram_of_inner f _ b fun x y ↦ by simp [LinearMap.adjoint_inner_left]

variable [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] in
/-- **The covolume of the image of a lattice under a linear map.** If a `ℤ`-basis of a lattice
sitting in a subspace `W` of `F` is the image under `f` of an `ℝ`-basis `b`, then its squared
covolume is `det A` times the Gram determinant of `b`, for any `A` with `⟪f x, f y⟫ = ⟪A x, y⟫`.
This is the form in which the archimedean half of a covolume identity is computed: the lattice is
transported from a space where its covolume is known, and the transport factor is an operator
determinant. -/
theorem covolume_sq_eq_det_gram_comp {W : Submodule ℝ F} (L : Submodule ℤ ↥W)
    [DiscreteTopology L] [IsZLattice ℝ L] (c : Basis κ ℤ L) (f : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E)
    (b : Basis κ ℝ E) (h : ∀ x y, inner ℝ (f x) (f y) = inner ℝ (A x) y)
    (hc : ∀ i, ((c i : ↥W) : F) = f (b i)) :
    covolume L ^ 2 = A.det * (Matrix.of fun i j ↦ inner ℝ (b i) (b j)).det := by
  rw [covolume_sq_eq_det_gram L c, ← det_gram_of_inner f A b h]
  refine congrArg Matrix.det (Matrix.ext fun i j ↦ ?_)
  simp only [Matrix.of_apply]
  rw [← hc i, ← hc j]
  exact rfl

end Comp

end ZLattice

end

end

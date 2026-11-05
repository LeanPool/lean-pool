/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Zorn
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.PlaneSplitting
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The split composition algebras (`GPR 21.19`)

`GPR 21.19` lists one composition algebra in each of the ranks `1, 2, 4, 8` and calls it the
**split** algebra of that rank:

| rank | algebra | norm | trace | conjugation |
|---|---|---|---|---|
| `1` | `k` | `x ↦ x²` | `2x` | `x` |
| `2` | `k × k` | `(a, b) ↦ ab` | `a + b` | `(a, b) ↦ (b, a)` |
| `4` | `Mat₂(k)` | `det` | `trace` | `adjugate` |
| `8` | `Zor(k)` | `ρ₁ρ₂ + u₁ᵀu₂` | `ρ₁ + ρ₂` | diagonal swap |

Ranks `1` and `8` are already available — `ConicAlgebra.baseRing` and `ConicAlgebra.zor` — and this
file supplies the two in between: the **split quadratic étale algebra** `k × k` and the **split
quaternion algebra** `Mat₂(k)`. As with `Zor(k)`, and in contrast with the Cayley–Dickson tower of
`Composition/Octonion.lean`, each is a composition algebra over an *arbitrary* commutative ring,
with no hypothesis on `2`: their norms are hyperbolic, and hyperbolic forms are regular in every
characteristic.

## Main definitions

* `ConicAlgebra.splitEtale k` : `k × k` with norm the hyperbolic plane `(a, b) ↦ ab`
  (`GPR 21.19(b)`). The norm is mathlib-free but not new — it is `QuadraticForm.plane k`.
* `ConicAlgebra.splitQuaternionNorm k`, `ConicAlgebra.splitQuaternion k` : `Mat₂(k)` with norm the
  determinant (`GPR 21.19(c)`).

## Main results

* `ConicAlgebra.isComposition_splitEtale`, `ConicAlgebra.isComposition_splitQuaternion` : both are
  composition algebras over every commutative ring.
* `ConicAlgebra.finrank_splitEtale`, `ConicAlgebra.finrank_splitQuaternion` : of ranks `2` and `4`.
* `ConicAlgebra.conj_splitEtale_apply` : the conjugation of `k × k` is the exchange involution.
* `ConicAlgebra.conj_splitQuaternion_apply` : the conjugation of `Mat₂(k)` is the adjugate, so the
  conic identity `x (conj x) = n(x) 1` is the classical `A · adj A = det A · 1`.

## Implementation notes

Neither algebra needs a type synonym: unlike the Cayley–Dickson double and `Zor(k)`, the
multiplication is the one mathlib already puts on `k × k` and on `Matrix (Fin 2) (Fin 2) k`, so the
conic structure is extra data on an existing algebra and nothing has to be redefined. Both are
associative, so the four typeclasses a conic algebra needs come from their `Algebra k` instances.

The degree-two identity is, in the two cases, the componentwise identity `a² = (a + b)a - ab` and
the **Cayley–Hamilton theorem for `2 × 2` matrices**; the latter is proved here entrywise rather
than by invoking mathlib's general `Matrix.aeval_self_charpoly`, since at size `2` the entrywise
computation is four applications of `ring` and needs no characteristic-polynomial API.

Non-singularity is, in both cases, the observation that the norm is a sum of hyperbolic planes:
`(a, b) ↦ ab` is the pairing of `k` against `k`, and `det = a₀₀a₁₁ - a₀₁a₁₀` is the pairing of
`(a₀₀, a₀₁)` against `(a₁₁, -a₁₀)`. `QuadraticForm.isGPRNonsingular_of_basis_pairing` and its
equivalence-composed form read these off; no determinant criterion and no hypothesis on `2` enters.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 21.18, 21.19.
-/

@[expose] public section

universe u w

namespace ConicAlgebra

variable (k : Type u) [CommRing k]

/-! ### Rank two: the split quadratic étale algebra `k × k` -/

/-! The norm of `k × k` is mathlib-free but not new: it is the hyperbolic plane
`QuadraticForm.plane k` of `QuadraticForm/HyperbolicPair.lean`, `(a, b) ↦ ab`. Nothing is
redefined here. -/

variable {k}

variable (k)

/-- **`GPR 21.19(b)`: `k × k` is a conic algebra** with norm `(a, b) ↦ ab` and trace `a + b`. -/
def splitEtale : ConicAlgebra k (k × k) where
  norm := QuadraticForm.plane k
  norm_one := one_mul 1
  mul_self x := by
    refine Prod.ext ?_ ?_ <;> simp [Prod.smul_fst, Prod.smul_snd] <;> ring

variable {k}

@[simp] theorem splitEtale_norm : (splitEtale k).norm = QuadraticForm.plane k := rfl

/-- The trace of `k × k` is the sum of the two coordinates. -/
@[simp] theorem trace_splitEtale_apply (x : k × k) : (splitEtale k).trace x = x.1 + x.2 := by
  rw [ConicAlgebra.trace_apply, splitEtale_norm, QuadraticForm.polar_plane_one]

/-- **The conjugation of `k × k` is the exchange involution** `(a, b) ↦ (b, a)`, as `GPR 21.18`
requires of the split quadratic étale algebra. -/
@[simp] theorem conj_splitEtale_apply (x : k × k) : (splitEtale k).conj x = (x.2, x.1) := by
  refine Prod.ext ?_ ?_ <;> simp [ConicAlgebra.conj_apply]

/-- The norm of `k × k` permits composition: it is multiplicative because multiplication is
componentwise. -/
theorem isMultiplicative_splitEtale : (splitEtale k).IsMultiplicative := by
  intro x y
  simp only [splitEtale_norm, QuadraticForm.plane_apply, Prod.fst_mul, Prod.snd_mul]
  ring

variable (k)

/-- **`GPR 21.19(b)`: `k × k` is a composition algebra over every commutative ring**, the split
one of rank two. -/
theorem isComposition_splitEtale : (splitEtale k).IsComposition.{u, u, w} where
  isGPRNonsingular := QuadraticForm.isGPRNonsingular_plane.{u, w} k
  isMultiplicative := isMultiplicative_splitEtale

/-- `k × k` has rank `2`. (Not a `simp` lemma: mathlib's `Module.finrank_prod` already reduces the
left-hand side, to `1 + 1`.) -/
theorem finrank_splitEtale [Nontrivial k] : Module.finrank k (k × k) = 2 := by
  simp

/-! ### Rank four: the split quaternion algebra `Mat₂(k)` -/

/-- The bilinear form `(A, B) ↦ a₀₀b₁₁ - a₀₁b₁₀` on `Mat₂(k)`, whose associated quadratic form is
the determinant. -/
def splitQuaternionBilin : LinearMap.BilinForm k (Matrix (Fin 2) (Fin 2) k) :=
  LinearMap.mk₂ k (fun A B ↦ A 0 0 * B 1 1 - A 0 1 * B 1 0)
    (fun _ _ _ ↦ by simp; ring) (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring) (fun _ _ _ ↦ by simp; ring)

/-- The **norm of the split quaternion algebra** `Mat₂(k)` (`GPR 21.19(c)`): the determinant. -/
def splitQuaternionNorm : QuadraticForm k (Matrix (Fin 2) (Fin 2) k) :=
  (splitQuaternionBilin k).toQuadraticMap

variable {k}

theorem splitQuaternionNorm_apply' (A : Matrix (Fin 2) (Fin 2) k) :
    splitQuaternionNorm k A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := rfl

/-- **The norm of `Mat₂(k)` is the determinant.** -/
@[simp] theorem splitQuaternionNorm_apply (A : Matrix (Fin 2) (Fin 2) k) :
    splitQuaternionNorm k A = A.det := by
  rw [splitQuaternionNorm_apply', Matrix.det_fin_two]

theorem polar_splitQuaternionNorm (A B : Matrix (Fin 2) (Fin 2) k) :
    QuadraticMap.polar (splitQuaternionNorm k) A B =
      A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0 := by
  simp only [QuadraticMap.polar, splitQuaternionNorm_apply', Matrix.add_apply]
  ring

@[simp] theorem polar_splitQuaternionNorm_one (A : Matrix (Fin 2) (Fin 2) k) :
    QuadraticMap.polar (splitQuaternionNorm k) 1 A = A.trace := by
  rw [polar_splitQuaternionNorm, Matrix.trace_fin_two]
  simp
  ring

/-- **Cayley–Hamilton at size two**: `A² = tr(A)·A - det(A)·1`. Proved entrywise; this is the
degree-two identity that makes `Mat₂(k)` a conic algebra. -/
theorem mul_self_eq_trace_smul_sub_det_smul (A : Matrix (Fin 2) (Fin 2) k) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

variable (k)

/-- **`GPR 21.19(c)`: `Mat₂(k)` is a conic algebra** with norm the determinant and trace the matrix
trace. The degree-two identity is Cayley–Hamilton at size two. -/
def splitQuaternion : ConicAlgebra k (Matrix (Fin 2) (Fin 2) k) where
  norm := splitQuaternionNorm k
  norm_one := by simp
  mul_self A := by
    rw [polar_splitQuaternionNorm_one, splitQuaternionNorm_apply]
    exact mul_self_eq_trace_smul_sub_det_smul A

variable {k}

@[simp] theorem splitQuaternion_norm : (splitQuaternion k).norm = splitQuaternionNorm k := rfl

/-- The trace of the conic algebra `Mat₂(k)` is the trace of the matrix. -/
@[simp] theorem trace_splitQuaternion_apply (A : Matrix (Fin 2) (Fin 2) k) :
    (splitQuaternion k).trace A = A.trace := by
  rw [ConicAlgebra.trace_apply, splitQuaternion_norm, polar_splitQuaternionNorm_one]

/-- **The conjugation of `Mat₂(k)` is the adjugate.** Consequently the conic identity
`x (conj x) = n(x) 1` specializes to `A · adj A = det A · 1`. -/
@[simp] theorem conj_splitQuaternion_apply (A : Matrix (Fin 2) (Fin 2) k) :
    (splitQuaternion k).conj A = A.adjugate := by
  rw [ConicAlgebra.conj_apply, trace_splitQuaternion_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two]

/-- The norm of `Mat₂(k)` permits composition: this is multiplicativity of the determinant. -/
theorem isMultiplicative_splitQuaternion : (splitQuaternion k).IsMultiplicative := by
  intro A B
  simp [Matrix.det_mul]

variable (k)

/-- `Mat₂(k)` presented as `k² ⊕ k²`, by reading off the pair `(a₀₀, a₀₁)` and the pair
`(a₁₁, -a₁₀)`. Under this equivalence the determinant becomes the standard pairing of the two
factors, which is what exhibits it as two hyperbolic planes. -/
def splitQuaternionEquiv :
    Matrix (Fin 2) (Fin 2) k ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)) where
  toFun A := (![A 0 0, A 0 1], ![A 1 1, -A 1 0])
  map_add' A B := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> simp [add_comm]
  map_smul' c A := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> simp
  invFun p := Matrix.of ![![p.1 0, p.1 1], ![-p.2 1, p.2 0]]
  left_inv A := by ext i j; fin_cases i <;> fin_cases j <;> simp
  right_inv p := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> simp

/-- **The norm of `Mat₂(k)` is non-singular**: the determinant is two hyperbolic planes, pairing
`(a₀₀, a₀₁)` against `(a₁₁, -a₁₀)`. No hypothesis on `2`, and no determinant criterion — the
determinant here is the form, not the tool. -/
theorem isGPRNonsingular_splitQuaternionNorm :
    QuadraticForm.IsGPRNonsingular.{u, u, w} (splitQuaternionNorm k) :=
  QuadraticForm.isGPRNonsingular_of_linearEquiv_basis_pairing (Pi.basisFun k (Fin 2))
    (splitQuaternionEquiv k) fun A ↦ by
      simp [splitQuaternionEquiv, Fin.sum_univ_two, Matrix.det_fin_two]
      ring

/-- **`GPR 21.19(c)`: `Mat₂(k)` is a composition algebra over every commutative ring**, the split
one of rank four. -/
theorem isComposition_splitQuaternion : (splitQuaternion k).IsComposition.{u, u, w} where
  isGPRNonsingular := isGPRNonsingular_splitQuaternionNorm k
  isMultiplicative := isMultiplicative_splitQuaternion

/-- `Mat₂(k)` has rank `4`. -/
@[simp] theorem finrank_splitQuaternion [Nontrivial k] :
    Module.finrank k (Matrix (Fin 2) (Fin 2) k) = 4 := by
  rw [Module.finrank_matrix]
  simp

end ConicAlgebra

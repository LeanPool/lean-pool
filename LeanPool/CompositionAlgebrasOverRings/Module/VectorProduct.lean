/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Vector product pairs (`GPR 22.14`)

An **orientation** of a finitely generated projective `k`-module `M` of rank `3` is a `k`-linear
bijection `θ : ⋀³ M → k`. `GPR 22.14` uses `θ` and the induced orientation `θ*⁻¹`
of `M*`, only through the two **associated vector products**

  `M × M → M*`,     `(v, w) ↦ v ×θ w`,        `θ(u ∧ v ∧ w) = ⟨u ×θ v, w⟩`,
  `M* × M* → M`, `(φ, ψ) ↦ φ ×θ ψ`, `θ*⁻¹(φ ∧ ψ ∧ χ) = ⟨χ, φ ×θ ψ⟩`,

and it uses those only through three identities: both products are alternating, each is orthogonal
to its own arguments, and the two are linked by the Binet–Cauchy identity. This file packages
exactly that much data as `Module.VectorProductPair k M`. It constructs the pair both directly
from a basis of size three and from an orientation together with such a basis.

Isolating the identities rather than the orientation is the same move as `Module.IsRankOnePairing`
in `Module/Invertible.lean`, which isolates what `GPR 22.12`'s twisted matrices need a line bundle
for. It buys three things: the algebra `ConicAlgebra.TwistedZor` built on a pair is a composition
algebra with *no* hypothesis on the rank of `M` (rank three is what makes pairs exist, not what
makes the axioms work); the free case, which is where `GPR`'s localization argument lands, is
available directly as `Module.VectorProductPair.ofBasis`; and the converse direction of
`GPR 22.15`, where the vector products are *read off* from the multiplication of a reduced
octonion algebra, produces a pair directly and never has to exhibit `θ`.

## Main definitions

* `Module.VectorProductPair k M` : a pair of vector products `M × M → M*` and `M* × M* → M`
  satisfying the three identities of `GPR (22.14.2)` and Binet–Cauchy.
* `Module.VectorProductPair.ofBasis` : the pair attached to a basis `(u₁, u₂, u₃)` of `M`,
  whose orientation is `θ(u₁ ∧ u₂ ∧ u₃) = 1`.
* `Module.VectorProductPair.ofOrientationOfBasis` : the pair induced by an arbitrary orientation
  of a based rank-three module.
* `Module.Basis.dualCoord` : the coordinates of a functional along the dual basis,
  `M* ≃ (ι → k)`.

## Main results

* `Module.VectorProductPair.cross_swap`, `crossDual_swap` : the products are anticommutative.
* `Module.VectorProductPair.cross_apply_right`, `apply_crossDual_right` : orthogonality to the
  second argument as well as the first.
* `Module.Basis.apply_eq_dotProduct` : in the coordinates of a finite basis and its dual basis,
  the canonical pairing `M* × M → k` is the dot product. This is what makes a basis of size three
  produce a vector product pair, and it is stated for an arbitrary finite basis.
* `Module.orientationAlternating_mul_dualOrientationAlternating` : the primal and dual volume
  coefficients are inverse, the basis calculation behind Binet–Cauchy.
* `Module.Basis.det_mul_det_dualBasis` : for a finite basis, the product of the determinant forms
  of the basis and of its dual basis is the determinant of the matrix of pairings.

## Implementation notes

⚠ **The orientation is not part of the data.** `GPR 22.14` starts from `(M, θ)` with `M` of
rank three; a `VectorProductPair` is what `θ` produces. The construction here proves the based
calculation by dualizing `θ` through the canonical exterior-power pairing (`GPR 21.7`) and
checking that the two volume coefficients are inverse. The arbitrary finite-projective case is
proved by localization in `Composition.Reduced.Orientation`.

The three axioms are stated with the *left* argument in the degenerate position
(`cross_apply_left`, `apply_crossDual_left`); the right-hand versions follow from
anticommutativity, which in turn follows from `cross_self`. Anticommutativity is therefore not an
axiom, and neither is the alternating character of the trilinear form
`(u, v, w) ↦ ⟨u ×θ v, w⟩`, which is the conjunction of the two.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 21.7, 21.8, 22.14.
-/

@[expose] public section

universe u v

open Matrix

namespace Module

variable (k : Type u) (M : Type v) [CommRing k] [AddCommGroup M] [Module k M]

/-- A **pair of associated vector products** on a `k`-module `M` (`GPR 22.14`): `k`-bilinear maps

  `×  : M × M → M*`,      `×* : M* × M* → M`,

both alternating, each orthogonal to its own arguments, and linked by the Binet–Cauchy identity
`⟨v × w, φ ×* ψ⟩ = ⟨φ, v⟩⟨ψ, w⟩ - ⟨φ, w⟩⟨ψ, v⟩`.

`GPR 22.14` obtains such a pair from an orientation `θ : ⋀³ M ≅ k` of a rank-three projective
module, by `θ(u ∧ v ∧ w) = ⟨u × v, w⟩` and
`θ*⁻¹(φ ∧ ψ ∧ χ) = ⟨χ, φ ×* ψ⟩`; the identities below are exactly the alternating
character of the two orientations and `GPR (22.14.1)`. The rank
plays no role afterwards, so it is not part of this definition — see the module docstring. -/
structure VectorProductPair where
  /-- The vector product `M × M → M*`, `(v, w) ↦ v ×θ w`. -/
  cross : M →ₗ[k] M →ₗ[k] Module.Dual k M
  /-- The vector product `M* × M* → M`, `(φ, ψ) ↦ φ ×θ ψ`, of the induced orientation of
  `M*`. -/
  crossDual : Module.Dual k M →ₗ[k] Module.Dual k M →ₗ[k] M
  /-- The vector product is alternating. -/
  cross_self (v : M) : cross v v = 0
  /-- The dual vector product is alternating. -/
  crossDual_self (φ : Module.Dual k M) : crossDual φ φ = 0
  /-- `⟨v × w, v⟩ = θ(v ∧ w ∧ v) = 0`. -/
  cross_apply_left (v w : M) : cross v w v = 0
  /-- `⟨φ, φ ×* ψ⟩ = θ*⁻¹(φ ∧ ψ ∧ φ) = 0`. -/
  apply_crossDual_left (φ ψ : Module.Dual k M) : φ (crossDual φ ψ) = 0
  /-- The **Binet–Cauchy identity** linking the two products, `GPR (22.14.1)`. -/
  cross_apply_crossDual (v w : M) (φ ψ : Module.Dual k M) :
    cross v w (crossDual φ ψ) = φ v * ψ w - φ w * ψ v

/-- If a ternary function vanishes whenever any pair of its arguments agrees, then it vanishes on
a `Fin 3`-indexed tuple whenever two distinct entries agree. This is the combinatorial half of
`map_eq_zero_of_eq'` for both alternating forms below. For each vector product, two hypotheses
come from fields of `VectorProductPair`; the third is the derived right-orthogonality identity. -/
theorem fin_three_eq_zero_of_apply_eq {X N : Type*} [Zero N] (f : X → X → X → N)
    (h₁ : ∀ v w, f v v w = 0) (h₂ : ∀ v w, f v w v = 0) (h₃ : ∀ v w, f v w w = 0)
    (x : Fin 3 → X) {i j : Fin 3} (hij : x i = x j) (hne : i ≠ j) :
    f (x 0) (x 1) (x 2) = 0 := by
  fin_cases i <;> fin_cases j
  · exact (hne rfl).elim
  · rw [show x 0 = x 1 from hij]; exact h₁ _ _
  · rw [show x 0 = x 2 from hij]; exact h₂ _ _
  · rw [show x 1 = x 0 from hij]; exact h₁ _ _
  · exact (hne rfl).elim
  · rw [show x 1 = x 2 from hij]; exact h₃ _ _
  · rw [show x 2 = x 0 from hij]; exact h₂ _ _
  · rw [show x 2 = x 1 from hij]; exact h₃ _ _
  · exact (hne rfl).elim

namespace VectorProductPair

variable {k M} (P : VectorProductPair k M)

/-- Two vector-product pairs are equal when their two bilinear maps are equal. -/
@[ext] theorem ext {P Q : VectorProductPair k M} (hcross : P.cross = Q.cross)
    (hcrossDual : P.crossDual = Q.crossDual) : P = Q := by
  cases P
  cases Q
  dsimp only at hcross hcrossDual
  subst hcross
  subst hcrossDual
  rfl

/-- The vector product is anticommutative. -/
theorem cross_swap (v w : M) : P.cross v w = -P.cross w v := by
  have h := P.cross_self (v + w)
  simp only [map_add, LinearMap.add_apply, P.cross_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- The dual vector product is anticommutative. -/
theorem crossDual_swap (φ ψ : Module.Dual k M) : P.crossDual φ ψ = -P.crossDual ψ φ := by
  have h := P.crossDual_self (φ + ψ)
  simp only [map_add, LinearMap.add_apply, P.crossDual_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- `⟨v × w, w⟩ = θ(v ∧ w ∧ w) = 0`. -/
theorem cross_apply_right (v w : M) : P.cross v w w = 0 := by
  rw [P.cross_swap, LinearMap.neg_apply, P.cross_apply_left, neg_zero]

/-- `⟨ψ, φ ×* ψ⟩ = θ*⁻¹(φ ∧ ψ ∧ ψ) = 0`. -/
theorem apply_crossDual_right (φ ψ : Module.Dual k M) : ψ (P.crossDual φ ψ) = 0 := by
  rw [P.crossDual_swap, map_neg, P.apply_crossDual_left, neg_zero]

/-- The alternating trilinear form `(u, v, w) ↦ ⟨u × v, w⟩` associated to the first
vector product. -/
def crossAlternating : M [⋀^Fin 3]→ₗ[k] k where
  toMultilinearMap := MultilinearMap.mk' (fun x ↦ P.cross (x 0) (x 1) (x 2))
    (by intro x i y z; fin_cases i <;> simp [Function.update, Fin.ext_iff])
    (by intro x i r y; fin_cases i <;> simp [Function.update, Fin.ext_iff])
  map_eq_zero_of_eq' x i j hij hne :=
    fin_three_eq_zero_of_apply_eq (fun a b c ↦ P.cross a b c)
      (fun v w ↦ by rw [P.cross_self, LinearMap.zero_apply]) P.cross_apply_left
      P.cross_apply_right x hij hne

@[simp] theorem crossAlternating_apply (x : Fin 3 → M) :
    P.crossAlternating x = P.cross (x 0) (x 1) (x 2) := rfl

/-- The alternating trilinear form `(φ, ψ, χ) ↦ ⟨φ, ψ ×* χ⟩` associated to the
dual vector product. -/
def crossDualAlternating : Module.Dual k M [⋀^Fin 3]→ₗ[k] k where
  toMultilinearMap := MultilinearMap.mk' (fun x ↦ x 0 (P.crossDual (x 1) (x 2)))
    (by intro x i y z; fin_cases i <;> simp [Function.update, Fin.ext_iff])
    (by intro x i r y; fin_cases i <;> simp [Function.update, Fin.ext_iff])
  map_eq_zero_of_eq' x i j hij hne :=
    fin_three_eq_zero_of_apply_eq (fun a b c ↦ a (P.crossDual b c)) P.apply_crossDual_left
      (fun v w ↦ P.apply_crossDual_right w v)
      (fun v w ↦ by rw [P.crossDual_self, map_zero]) x hij hne

@[simp] theorem crossDualAlternating_apply (x : Fin 3 → Module.Dual k M) :
    P.crossDualAlternating x = x 0 (P.crossDual (x 1) (x 2)) := rfl

end VectorProductPair

/-! ### The pair attached to a basis

For a basis `(u₁, u₂, u₃)`, the orientation `θ(u₁ ∧ u₂ ∧ u₃) = 1` makes the basis
self-dual, and both vector products become the ordinary cross product of `k³` read in
coordinates. This is the case `GPR 22.14` reduces to, and it is the only construction of a pair
in this file. -/

namespace Basis

variable {k M} {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k M)

/-- The coordinates of a linear functional along the basis dual to `b`, as an equivalence
`M* ≃ (ι → k)`. Together with `b.equivFun : M ≃ (ι → k)` it makes `b` self-dual: the
canonical pairing becomes the dot product (`Module.Basis.apply_eq_dotProduct`). -/
noncomputable def dualCoord : Module.Dual k M ≃ₗ[k] (ι → k) := b.dualBasis.equivFun

@[simp] theorem dualCoord_apply (φ : Module.Dual k M) (i : ι) : b.dualCoord φ i = φ (b i) :=
  b.dualBasis_equivFun φ i

/-- **In the coordinates of a finite basis and its dual basis, the canonical pairing is the dot
product.** -/
theorem apply_eq_dotProduct (φ : Module.Dual k M) (u : M) :
    φ u = b.dualCoord φ ⬝ᵥ b.equivFun u := by
  conv_lhs => rw [← b.sum_repr u]
  rw [map_sum]
  simp [dotProduct, mul_comm]

theorem dualCoord_symm_apply (f : ι → k) (u : M) :
    b.dualCoord.symm f u = f ⬝ᵥ b.equivFun u := by
  rw [apply_eq_dotProduct b, LinearEquiv.apply_symm_apply]

theorem apply_equivFun_symm (φ : Module.Dual k M) (g : ι → k) :
    φ (b.equivFun.symm g) = b.dualCoord φ ⬝ᵥ g := by
  rw [apply_eq_dotProduct b, LinearEquiv.apply_symm_apply]

end Basis

section OfBasis

variable {k M} (b : Module.Basis (Fin 3) k M)

/-- The cross product of `M` induced by a basis of size three: the ordinary cross product of the
coordinate vectors, read back as a linear functional through the dual basis. -/
noncomputable def crossOfBasis : M →ₗ[k] M →ₗ[k] Module.Dual k M :=
  (crossProduct.compl₁₂ b.equivFun.toLinearMap b.equivFun.toLinearMap).compr₂
    b.dualCoord.symm.toLinearMap

/-- The cross product of `M*` induced by a basis of size three. -/
noncomputable def crossDualOfBasis : Module.Dual k M →ₗ[k] Module.Dual k M →ₗ[k] M :=
  (crossProduct.compl₁₂ b.dualCoord.toLinearMap b.dualCoord.toLinearMap).compr₂
    b.equivFun.symm.toLinearMap

@[simp] theorem crossOfBasis_apply (v w : M) :
    crossOfBasis b v w = b.dualCoord.symm (b.equivFun v ⨯₃ b.equivFun w) := rfl

@[simp] theorem crossDualOfBasis_apply (φ ψ : Module.Dual k M) :
    crossDualOfBasis b φ ψ = b.equivFun.symm (b.dualCoord φ ⨯₃ b.dualCoord ψ) := rfl

/-- **The vector product pair attached to a basis** `(u₁, u₂, u₃)` of `M`: the pair of the
orientation `θ` with `θ(u₁ ∧ u₂ ∧ u₃) = 1`. The products become the cross product in the
coordinates of `b`; this is self-dual for that orientation, so the axioms are the
classical identities
`u ⬝ᵥ (u ⨯₃ v) = 0` and the Binet–Cauchy identity `Matrix.cross_dot_cross`. -/
noncomputable def VectorProductPair.ofBasis : VectorProductPair k M where
  cross := crossOfBasis b
  crossDual := crossDualOfBasis b
  cross_self v := by simp
  crossDual_self φ := by simp
  cross_apply_left v w := by
    rw [crossOfBasis_apply, Basis.dualCoord_symm_apply, dotProduct_comm, dot_self_cross]
  apply_crossDual_left φ ψ := by
    rw [crossDualOfBasis_apply, Basis.apply_equivFun_symm, dot_self_cross]
  cross_apply_crossDual v w φ ψ := by
    rw [crossOfBasis_apply, crossDualOfBasis_apply, Basis.dualCoord_symm_apply,
      LinearEquiv.apply_symm_apply, cross_dot_cross, Basis.apply_eq_dotProduct b φ v,
      Basis.apply_eq_dotProduct b ψ w, Basis.apply_eq_dotProduct b φ w,
      Basis.apply_eq_dotProduct b ψ v,
      dotProduct_comm (b.equivFun v) (b.dualCoord φ),
      dotProduct_comm (b.equivFun v) (b.dualCoord ψ),
      dotProduct_comm (b.equivFun w) (b.dualCoord φ),
      dotProduct_comm (b.equivFun w) (b.dualCoord ψ)]
    ring

@[simp] theorem VectorProductPair.ofBasis_cross :
    (VectorProductPair.ofBasis b).cross = crossOfBasis b := rfl

@[simp] theorem VectorProductPair.ofBasis_crossDual :
    (VectorProductPair.ofBasis b).crossDual = crossDualOfBasis b := rfl

/-- The trilinear form of the basis-built vector product is the determinant form of the basis. -/
theorem VectorProductPair.crossAlternating_ofBasis :
    (VectorProductPair.ofBasis b).crossAlternating = b.det := by
  apply AlternatingMap.ext
  intro x
  rw [VectorProductPair.crossAlternating_apply, VectorProductPair.ofBasis_cross,
    crossOfBasis_apply, Basis.dualCoord_symm_apply, dotProduct_comm,
    triple_product_permutation,
    triple_product_eq_det, Basis.det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  fin_cases i <;> simp [Matrix.vecCons, Matrix.vecEmpty, Module.Basis.toMatrix]
  rfl

/-- The trilinear form of the basis-built dual vector product is the determinant form of the
dual basis. -/
theorem VectorProductPair.crossDualAlternating_ofBasis :
    (VectorProductPair.ofBasis b).crossDualAlternating = b.dualBasis.det := by
  apply AlternatingMap.ext
  intro x
  rw [VectorProductPair.crossDualAlternating_apply, VectorProductPair.ofBasis_crossDual,
    crossDualOfBasis_apply, Basis.apply_equivFun_symm, triple_product_eq_det,
    Basis.det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  fin_cases i
  · simp [Matrix.vecCons, Matrix.vecEmpty, Basis.dualCoord, Module.Basis.toMatrix]
  · simp [Matrix.vecCons, Matrix.vecEmpty, Basis.dualCoord, Module.Basis.toMatrix]
  · change b.dualBasis.repr (x 2) j = b.dualBasis.repr (x 2) j
    rfl

/-- Relative to a basis of size three, every first vector product is a scalar multiple of the
basis-built cross product. The scalar is its oriented volume on that basis. -/
theorem VectorProductPair.cross_eq_smul_crossOfBasis (P : VectorProductPair k M) :
    P.cross = P.crossAlternating b • crossOfBasis b := by
  ext u v w
  have h := DFunLike.congr_fun (P.crossAlternating.eq_smul_basis_det b) ![u, v, w]
  rw [← VectorProductPair.crossAlternating_ofBasis b] at h
  simpa using h

/-- Relative to the dual basis, every dual vector product is a scalar multiple of the
basis-built dual cross product. -/
theorem VectorProductPair.crossDual_eq_smul_crossDualOfBasis (P : VectorProductPair k M) :
    P.crossDual = P.crossDualAlternating b.dualBasis • crossDualOfBasis b := by
  ext φ ψ
  rw [b.ext_elem_iff]
  intro i
  have h := DFunLike.congr_fun
    (P.crossDualAlternating.eq_smul_basis_det b.dualBasis) ![b.dualBasis i, φ, ψ]
  rw [← VectorProductPair.crossDualAlternating_ofBasis b] at h
  fin_cases i <;>
    simpa [Basis.dualBasis_apply, crossDualOfBasis_apply, cross_apply,
      Fin.sum_univ_succ] using h

/-- The two scalar coefficients of a vector-product pair relative to a basis are inverse. This is
Binet–Cauchy evaluated on the first two basis vectors and their duals. -/
theorem VectorProductPair.cross_coeff_mul_crossDual_coeff (P : VectorProductPair k M) :
    P.crossAlternating b * P.crossDualAlternating b.dualBasis = 1 := by
  have hcross : P.cross (b 0) (b 1) =
      P.crossAlternating b • b.dualBasis 2 := by
    rw [P.cross_eq_smul_crossOfBasis b]
    simp only [LinearMap.smul_apply]
    congr 1
    apply b.dualCoord.injective
    rw [crossOfBasis_apply, LinearEquiv.apply_symm_apply]
    ext i
    fin_cases i <;> simp [cross_apply, Basis.dualCoord_apply]
  have hcrossDual : P.crossDual (b.dualBasis 0) (b.dualBasis 1) =
      P.crossDualAlternating b.dualBasis • b 2 := by
    rw [P.crossDual_eq_smul_crossDualOfBasis b]
    simp only [LinearMap.smul_apply]
    congr 1
    apply b.equivFun.injective
    ext i
    fin_cases i <;> simp [crossDualOfBasis_apply, cross_apply, Fin.sum_univ_succ]
  have h := P.cross_apply_crossDual (b 0) (b 1) (b.dualBasis 0) (b.dualBasis 1)
  rw [hcross, hcrossDual] at h
  simpa [Basis.dualBasis_apply, mul_comm] using h

/-- The volume coefficient of a vector-product pair in any basis is a unit. -/
theorem VectorProductPair.isUnit_crossAlternating_basis (P : VectorProductPair k M) :
    IsUnit (P.crossAlternating b) :=
  isUnit_iff_exists_inv.mpr
    ⟨P.crossDualAlternating b.dualBasis, P.cross_coeff_mul_crossDual_coeff b⟩

/-- Every vector-product pair on a free module of rank three is the pair attached to a suitably
rescaled basis. -/
theorem VectorProductPair.exists_eq_ofBasis (b : Module.Basis (Fin 3) k M)
    (P : VectorProductPair k M) :
    ∃ b' : Module.Basis (Fin 3) k M, P = VectorProductPair.ofBasis b' := by
  let hu := P.isUnit_crossAlternating_basis b
  let l : kˣ := hu.unit
  let w : Fin 3 → kˣ := fun i ↦ if i = 0 then l⁻¹ else 1
  let b' := b.unitsSMul w
  have hl : (l : k) = P.crossAlternating b := hu.unit_spec.symm
  have hw : ∏ i, w i = l⁻¹ := by
    simp [w]
  have hcoeff : (VectorProductPair.ofBasis b').crossAlternating b =
      P.crossAlternating b := by
    rw [VectorProductPair.crossAlternating_ofBasis, b.det_unitsSMul]
    simp [hw, hl, Basis.det_self]
  have hcross : (VectorProductPair.ofBasis b').cross = P.cross := by
    rw [(VectorProductPair.ofBasis b').cross_eq_smul_crossOfBasis b,
      P.cross_eq_smul_crossOfBasis b, hcoeff]
  have hdualCoeff : (VectorProductPair.ofBasis b').crossDualAlternating b.dualBasis =
      P.crossDualAlternating b.dualBasis := by
    apply hu.mul_left_cancel
    calc
      (l : k) * (VectorProductPair.ofBasis b').crossDualAlternating b.dualBasis =
          (VectorProductPair.ofBasis b').crossAlternating b *
            (VectorProductPair.ofBasis b').crossDualAlternating b.dualBasis := by
        rw [hl, hcoeff]
      _ = 1 := (VectorProductPair.ofBasis b').cross_coeff_mul_crossDual_coeff b
      _ = P.crossAlternating b * P.crossDualAlternating b.dualBasis :=
        (P.cross_coeff_mul_crossDual_coeff b).symm
      _ = (l : k) * P.crossDualAlternating b.dualBasis := by rw [hl]
  have hcrossDual : (VectorProductPair.ofBasis b').crossDual = P.crossDual := by
    rw [(VectorProductPair.ofBasis b').crossDual_eq_smul_crossDualOfBasis b,
      P.crossDual_eq_smul_crossDualOfBasis b, hdualCoeff]
  refine ⟨b', ?_⟩
  exact VectorProductPair.ext hcross.symm hcrossDual.symm

end OfBasis

/-! ### The pair attached to an orientation of a based module -/

section Orientation

variable {k M}

/-- A cyclic permutation of three arguments preserves an alternating trilinear map. -/
theorem alternating_fin_three_cycle {N : Type*} [AddCommGroup N] [Module k N]
    (a : M [⋀^Fin 3]→ₗ[k] N) (x y z : M) :
    a ![x, y, z] = a ![y, z, x] := by
  have h₁ := a.map_swap ![x, y, z] (show (0 : Fin 3) ≠ 1 by decide)
  have h₂ := a.map_swap ![y, x, z] (show (1 : Fin 3) ≠ 2 by decide)
  have heq₁ : ![x, y, z] ∘ Equiv.swap (0 : Fin 3) 1 = ![y, x, z] := by
    ext i
    fin_cases i <;> rfl
  have heq₂ : ![y, x, z] ∘ Equiv.swap (1 : Fin 3) 2 = ![y, z, x] := by
    ext i
    fin_cases i <;> rfl
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  rw [h₂, h₁, neg_neg]

/-- The alternating volume form obtained from an orientation `θ : ⋀³ M ≃ k`. -/
noncomputable def orientationAlternating
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) : M [⋀^Fin 3]→ₗ[k] k :=
  theta.toLinearMap.compAlternatingMap (exteriorPower.ιMulti k 3)

@[simp] theorem orientationAlternating_apply
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (x : Fin 3 → M) :
    orientationAlternating theta x = theta (exteriorPower.ιMulti k 3 x) := rfl

/-- The volume form on `M*` dual to an orientation of `M`. It evaluates the canonical pairing
with the oriented volume element `θ⁻¹(1)`; this is the duality of `GPR 21.7`. -/
noncomputable def dualOrientationAlternating
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    Module.Dual k M [⋀^Fin 3]→ₗ[k] k :=
  (Module.Dual.eval k (⋀[k]^3 M) (theta.symm 1)).compAlternatingMap
    (exteriorPower.alternatingMapToDual k M 3)

@[simp] theorem dualOrientationAlternating_apply
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (f : Fin 3 → Module.Dual k M) :
    dualOrientationAlternating theta f =
      exteriorPower.pairingDual k M 3 (exteriorPower.ιMulti k 3 f) (theta.symm 1) := by
  simp [dualOrientationAlternating, exteriorPower.pairingDual]

/-- The primal and dual volume forms defined by an orientation multiply to the determinant
pairing. This basis-free identity is the scalar form of the perfect exterior-power duality in
`GPR 21.7`. -/
theorem orientationAlternating_mul_dualOrientationAlternating_apply
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (x : Fin 3 → M) (f : Fin 3 → Module.Dual k M) :
    orientationAlternating theta x * dualOrientationAlternating theta f =
      Matrix.det (fun i j ↦ f i (x j)) := by
  have hx : exteriorPower.ιMulti k 3 x =
      theta (exteriorPower.ιMulti k 3 x) • theta.symm 1 := by
    apply theta.injective
    simp
  rw [orientationAlternating_apply, dualOrientationAlternating_apply]
  calc
    theta (exteriorPower.ιMulti k 3 x) *
        exteriorPower.pairingDual k M 3 (exteriorPower.ιMulti k 3 f) (theta.symm 1) =
      exteriorPower.pairingDual k M 3 (exteriorPower.ιMulti k 3 f)
        (theta (exteriorPower.ιMulti k 3 x) • theta.symm 1) := by
          rw [map_smul, smul_eq_mul]
    _ = exteriorPower.pairingDual k M 3 (exteriorPower.ιMulti k 3 f)
        (exteriorPower.ιMulti k 3 x) := by rw [← hx]
    _ = Matrix.det (fun i j ↦ f i (x j)) := by
      simp only [exteriorPower.pairingDual_ιMulti_ιMulti]
      rw [show (Matrix.of fun i j ↦ f j (x i)) =
        (Matrix.of fun i j ↦ f i (x j))ᵀ by rfl, Matrix.det_transpose]
      rfl

/-- The vector product `M × M → M*` induced by an orientation. -/
noncomputable def crossOfOrientation
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) : M →ₗ[k] M →ₗ[k] Module.Dual k M :=
  let z : M [⋀^Fin 0]→ₗ[k] k ≃ₗ[k] k :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y₁ : M [⋀^Fin 1]→ₗ[k] k →ₗ[k] Module.Dual k M :=
    LinearMap.llcomp k M (M [⋀^Fin 0]→ₗ[k] k) k z ∘ₗ
      AlternatingMap.curryLeftLinearMap
  let y₂ : M [⋀^Fin 2]→ₗ[k] k →ₗ[k] M →ₗ[k] Module.Dual k M :=
    LinearMap.llcomp k M (M [⋀^Fin 1]→ₗ[k] k) (Module.Dual k M) y₁ ∘ₗ
      AlternatingMap.curryLeftLinearMap
  LinearMap.llcomp k M (M [⋀^Fin 2]→ₗ[k] k) (M →ₗ[k] Module.Dual k M) y₂
    (orientationAlternating theta).curryLeft

@[simp] theorem crossOfOrientation_apply
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (v w x : M) :
    crossOfOrientation theta v w x = orientationAlternating theta ![v, w, x] := rfl

/-- The vector product `M* × M* → M` induced by the dual orientation. Projective
reflexivity identifies the bidual value of the curried volume form with an element of `M`. -/
noncomputable def crossDualOfOrientation [Module.Finite k M] [Module.Projective k M]
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    Module.Dual k M →ₗ[k] Module.Dual k M →ₗ[k] M :=
  let z : Module.Dual k M [⋀^Fin 0]→ₗ[k] k ≃ₗ[k] k :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y₁ : Module.Dual k M [⋀^Fin 1]→ₗ[k] k →ₗ[k]
      Module.Dual k (Module.Dual k M) :=
    LinearMap.llcomp k (Module.Dual k M) (Module.Dual k M [⋀^Fin 0]→ₗ[k] k) k z ∘ₗ
      AlternatingMap.curryLeftLinearMap
  let y₂ : Module.Dual k M [⋀^Fin 2]→ₗ[k] k →ₗ[k]
      Module.Dual k M →ₗ[k] Module.Dual k (Module.Dual k M) :=
    LinearMap.llcomp k (Module.Dual k M) (Module.Dual k M [⋀^Fin 1]→ₗ[k] k)
      (Module.Dual k (Module.Dual k M)) y₁ ∘ₗ AlternatingMap.curryLeftLinearMap
  let b : Module.Dual k M →ₗ[k] Module.Dual k M →ₗ[k]
      Module.Dual k (Module.Dual k M) :=
    LinearMap.llcomp k (Module.Dual k M) (Module.Dual k M [⋀^Fin 2]→ₗ[k] k)
      (Module.Dual k M →ₗ[k] Module.Dual k (Module.Dual k M)) y₂
        (dualOrientationAlternating theta).curryLeft
  b.compr₂ (Module.evalEquiv k M).symm.toLinearMap

@[simp] theorem apply_crossDualOfOrientation [Module.Finite k M] [Module.Projective k M]
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (f g h : Module.Dual k M) :
    h (crossDualOfOrientation theta f g) = dualOrientationAlternating theta ![f, g, h] := by
  simp [crossDualOfOrientation]

/-- In a basis, the orientation-induced vector product is its volume coefficient times the
standard basis cross product. -/
theorem crossOfOrientation_eq_smul_crossOfBasis
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (b : Module.Basis (Fin 3) k M) :
    crossOfOrientation theta = orientationAlternating theta b • crossOfBasis b := by
  ext u v w
  have h := DFunLike.congr_fun ((orientationAlternating theta).eq_smul_basis_det b) ![u, v, w]
  rw [← VectorProductPair.crossAlternating_ofBasis b] at h
  simpa using h

/-- In the dual basis, the dual orientation-induced product is its volume coefficient times the
standard dual cross product. -/
theorem crossDualOfOrientation_eq_smul_crossDualOfBasis
    [Module.Finite k M] [Module.Projective k M]
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (b : Module.Basis (Fin 3) k M) :
    crossDualOfOrientation theta =
      dualOrientationAlternating theta b.dualBasis • crossDualOfBasis b := by
  ext f g
  apply (Module.evalEquiv k M).injective
  ext h
  change h (crossDualOfOrientation theta f g) =
    h ((dualOrientationAlternating theta b.dualBasis • crossDualOfBasis b) f g)
  simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
  rw [apply_crossDualOfOrientation]
  rw [← alternating_fin_three_cycle (dualOrientationAlternating theta) h f g]
  have hdet := DFunLike.congr_fun
    ((dualOrientationAlternating theta).eq_smul_basis_det b.dualBasis) ![h, f, g]
  rw [← VectorProductPair.crossDualAlternating_ofBasis b] at hdet
  exact hdet

/-- The volume coefficients of an orientation and its dual are inverse. This is the based form
of exterior-power duality in `GPR 21.7` and the scalar identity behind `GPR (22.14.1)`. -/
theorem orientationAlternating_mul_dualOrientationAlternating
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (b : Module.Basis (Fin 3) k M) :
    orientationAlternating theta b * dualOrientationAlternating theta b.dualBasis = 1 := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  let s : Set.powersetCard (Fin 3) 3 :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.id (Fin 3))
  let omega : ⋀[k]^3 M := exteriorPower.ιMulti k 3 b
  have homega : exteriorPower.ιMulti_family k 3 b s = omega := by
    simp [s, omega, exteriorPower.ιMulti_family]
  have hdual : exteriorPower.ιMulti k 3 b.dualBasis =
      exteriorPower.ιMulti_family k 3 b.coord s := by
    simp [s, exteriorPower.ιMulti_family]
  have hm : (b.exteriorPower 3).repr (theta.symm 1) s =
      dualOrientationAlternating theta b.dualBasis := by
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual]
    simp only [dualOrientationAlternating_apply]
    rw [hdual]
  have hsmul : theta.symm 1 = dualOrientationAlternating theta b.dualBasis • omega := by
    apply (b.exteriorPower 3).repr.injective
    ext t
    have hts : t = s := by
      apply Subtype.ext
      rw [Finset.eq_univ_of_card t.val (t.prop.trans (Fintype.card_fin 3).symm)]
      simp [s, Set.powersetCard.ofFinEmbEquiv_apply]
    rw [hts, hm, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [← homega, ← exteriorPower.basis_apply k 3 b s, Module.Basis.repr_self,
      Finsupp.single_eq_same, mul_one]
  calc
    orientationAlternating theta b * dualOrientationAlternating theta b.dualBasis =
        dualOrientationAlternating theta b.dualBasis * orientationAlternating theta b :=
      mul_comm _ _
    _ = theta (dualOrientationAlternating theta b.dualBasis • omega) := by
      simp [omega, orientationAlternating_apply]
    _ = theta (theta.symm 1) := by rw [hsmul]
    _ = 1 := theta.apply_symm_apply 1

/-- **The based form of `GPR 22.14`.** An orientation of a finite projective module with a basis
of size three induces a pair of associated vector products. The products are defined directly
from the primal and dual volume forms; the basis is used only to prove Binet–Cauchy. -/
noncomputable def VectorProductPair.ofOrientationOfBasis
    [Module.Finite k M] [Module.Projective k M]
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (b : Module.Basis (Fin 3) k M) :
    VectorProductPair k M where
  cross := crossOfOrientation theta
  crossDual := crossDualOfOrientation theta
  cross_self v := by
    ext w
    rw [crossOfOrientation_apply]
    change orientationAlternating theta ![v, v, w] = 0
    exact (orientationAlternating theta).map_eq_zero_of_eq ![v, v, w]
      (by rfl) (show (0 : Fin 3) ≠ 1 by decide)
  crossDual_self f := by
    apply (Module.evalEquiv k M).injective
    ext h
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, map_zero]
    rw [apply_crossDualOfOrientation]
    exact (dualOrientationAlternating theta).map_eq_zero_of_eq ![f, f, h]
      (by rfl) (show (0 : Fin 3) ≠ 1 by decide)
  cross_apply_left v w := by
    rw [crossOfOrientation_apply]
    exact (orientationAlternating theta).map_eq_zero_of_eq ![v, w, v]
      (by rfl) (show (0 : Fin 3) ≠ 2 by decide)
  apply_crossDual_left f g := by
    rw [apply_crossDualOfOrientation]
    exact (dualOrientationAlternating theta).map_eq_zero_of_eq ![f, g, f]
      (by rfl) (show (0 : Fin 3) ≠ 2 by decide)
  cross_apply_crossDual v w f g := by
    rw [crossOfOrientation_eq_smul_crossOfBasis theta b,
      crossDualOfOrientation_eq_smul_crossDualOfBasis theta b]
    simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
    rw [← mul_assoc, mul_comm (dualOrientationAlternating theta b.dualBasis)
      (orientationAlternating theta b),
      orientationAlternating_mul_dualOrientationAlternating theta b, one_mul]
    exact (VectorProductPair.ofBasis b).cross_apply_crossDual v w f g

@[simp] theorem VectorProductPair.ofOrientationOfBasis_cross
    [Module.Finite k M] [Module.Projective k M]
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (b : Module.Basis (Fin 3) k M) :
    (VectorProductPair.ofOrientationOfBasis theta b).cross = crossOfOrientation theta := rfl

@[simp] theorem VectorProductPair.ofOrientationOfBasis_crossDual
    [Module.Finite k M] [Module.Projective k M]
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (b : Module.Basis (Fin 3) k M) :
    (VectorProductPair.ofOrientationOfBasis theta b).crossDual =
      crossDualOfOrientation theta := rfl

/-- The pair constructed from an orientation does not depend on the basis used to verify its
axioms. -/
theorem VectorProductPair.ofOrientationOfBasis_eq
    [Module.Finite k M] [Module.Projective k M]
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (b b' : Module.Basis (Fin 3) k M) :
    VectorProductPair.ofOrientationOfBasis theta b =
      VectorProductPair.ofOrientationOfBasis theta b' :=
  VectorProductPair.ext rfl rfl

end Orientation

/-- In the coordinates of a finite basis and its dual basis, the product of the two determinant
forms is the determinant of the matrix of pairings. -/
theorem Basis.det_mul_det_dualBasis {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N]
    [Module R N] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R N)
    (x : ι → N) (f : ι → Module.Dual R N) :
    b.det x * b.dualBasis.det f = Matrix.det (.of fun i j ↦ f i (x j)) := by
  rw [Basis.det_apply, Basis.det_apply, mul_comm,
    ← Matrix.det_transpose (b.dualBasis.toMatrix f), ← Matrix.det_mul]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.dualBasis_repr, Matrix.of_apply]
  conv_rhs => rw [← b.sum_repr (x j)]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

end Module

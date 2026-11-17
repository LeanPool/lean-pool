/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.QuadraticSubalgebra
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankOneTwoFourEight
public import LeanPool.CompositionAlgebrasOverRings.Composition.Tower
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDickson
public import LeanPool.CompositionAlgebrasOverRings.Conic.Division
public import LeanPool.CompositionAlgebrasOverRings.Conic.Projective
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.OrthogonalComplement
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.WittCancellation

/-!
# Algebra isomorphisms and norm isometries

The first direction of the classification of composition algebras by their norm forms says that
an algebra isomorphism is an isometry. The key input is that a conic norm on a finitely generated
projective algebra is intrinsic: two conic structures on the same algebra have the same norm.
This is the easy half of `GPR 23.4(a)`.

For the converse direction, the first step normalizes an arbitrary norm **similarity** to a unital
norm isometry (`GPR 23.3`). If its multiplier is `μ` and the image of `1` is `x`, left
multiplication by `conj x / μ` has the inverse multiplier and sends `x` to `1`. Such a normalized
map preserves the whole conic calculus — trace, conjugation and squares — which is `GPR 23.2`.

Over a nontrivial LG ring, the converse is completed without a constant-rank hypothesis; that
completion is the **norm equivalence theorem** `GPR 23.5`. The rank idempotents reduce it to the
constant-rank cases. In rank one,
`unitForm` canonically identifies the algebra with the base ring, even when its polar form is
nonregular in characteristic two. In ranks two, four, and eight, the proof starts from the
corresponding regular quadratic subalgebras of `GPR 19.16(b)`, uses Witt cancellation (`GN 6.5`)
to match successive doubling vectors, and iterates to regular full-rank subalgebras, which are the
ambient algebras.

## Main results

* `ConicAlgebra.norm_eq_of_projective` : two conic norms on the same finite projective algebra
  coincide.
* `ConicAlgebra.isometryEquivOfLinearEquiv` : **`GPR 23.4(a)`**, a unital multiplicative linear
  equivalence of conic algebras is an isometry of their norms.
* `ConicAlgebra.trace_map_of_linearEquiv`, `ConicAlgebra.conj_map_of_linearEquiv` : such an
  equivalence also preserves trace and conjugation.
* `ConicAlgebra.IsMultiplicative.exists_isometryEquiv_map_one_of_similarity` : full
  **`GPR 23.3`**, normalizing a norm similarity to a unital norm isometry.
* `ConicAlgebra.IsMultiplicative.exists_isometryEquiv_map_one` : its isometry special case.
* `ConicAlgebra.trace_map_of_isometryEquiv_map_one`, `.conj_map_of_isometryEquiv_map_one`,
  `.map_mul_self_of_isometryEquiv_map_one` : **`GPR 23.2`**, a unital norm isometry preserves the
  conic calculus and squaring.
* `ConicAlgebra.adjoinElementLinearEquivOfMapOne` : a unital norm isometry restricts to an algebra
  isomorphism `k[u] ≅ k[e u]` (expressed as a multiplicative unital linear equivalence).
* `ConicAlgebra.isRegularRankTwoComposition_map_of_isometryEquiv_map_one` : the regular quadratic
  starting subalgebra transfers across a unital norm isometry.
* `ConicAlgebra.cayAdjoinElementIsometryEquivOfMapOne` : the matched quadratic subalgebras can be
  doubled with a common Cayley–Dickson scalar, preserving the norm and multiplication.
* `ConicAlgebra.exists_doubledSubalgebras_isometryEquiv_of_isGPRRegular` : one internal matched
  doubling step carries equivalent regular subalgebras to equivalent doubled image subalgebras.
* `ConicAlgebra.IsComposition.exists_next_doubledSubalgebras_isometryEquiv` : unit representation,
  complement cancellation and internal doubling combined into one complete induction step.
* `ConicAlgebra.IsComposition.exists_next_isGPRRegular_rankAtStalk_two_mul` : the self-feeding
  version of that step, recording regularity and doubled rank for both new image subalgebras.
* `ConicAlgebra.exists_isometryEquiv_polarOrthogonal` : cancellation for arbitrary corresponding
  regular subalgebras.
* `ConicAlgebra.IsComposition.exists_isometryEquiv_map_one_map_mul` : **`GPR 23.5`**, the norm
  equivalence theorem over a nontrivial LG ring, with no constant-rank hypothesis.
* `ConicAlgebra.exists_isometryEquiv_polarOrthogonal_adjoinElement` : Witt cancellation identifies
  the orthogonal complements of the corresponding quadratic subalgebras.
* `ConicAlgebra.exists_polarOrthogonal_adjoinElement_eq_norm` : corresponding complement vectors
  give the same Cayley–Dickson parameter.
* `ConicAlgebra.isometryEquivOf_fullRank_subalgebras` : a matched equivalence of regular full-rank
  subalgebras assembles to an ambient equivalence.
* `ConicAlgebra.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk_eq_one` : the exceptional
  rank-one converse, proved directly through `unitForm`.
* `ConicAlgebra.IsComposition.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk` : the
  constant-rank-at-least-two step.
* `ConicAlgebra.IsComposition.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk_eq` : the
  constant-rank theorem used on each idempotent factor.

## Implementation notes

Mathlib's `AlgEquiv` applies only to associative semirings, while composition algebras need not be
associative.  Accordingly the second theorem accepts a `LinearEquiv` together with the two laws
that make it an isomorphism of unital non-associative algebras.  This avoids introducing a local
competitor to the `NonUnitalAlgEquiv` that mathlib itself records as a future TODO.

The uniqueness argument is elementary.  Subtracting the two degree-two identities gives

`(t_C(x) - t_D(x)) x = (n_C(x) - n_D(x)) 1`.

Applying a functional taking `1` to `1` shows that the trace difference annihilates its own
traceless argument.  The projective self-annihilation lemma then makes the traces equal, and the
same displayed identity makes the norms equal.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.7, 19.3,
  19.16(b), 19.18, 23.2, 23.3, 23.4(a), 23.5.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, 6.5.
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]

section Equiv

variable {B : Type w} [NonAssocRing B] [Module k B] [SMulCommClass k B B]
  [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B]

/-- **The engine of `GPR 23.4(a)`.** A unital linear equivalence between finitely generated
projective conic algebras that preserves squares, `e (x * x) = e x * e x`, is an isometry of their
norm forms: pulling the norm of `B` back along `e` gives a second conic norm on `A`, and the conic
norm of a finitely generated projective algebra is unique (`ConicAlgebra.norm_eq_of_projective`,
`GPR 16.16`). Isomorphisms (`isometryEquivOfLinearEquiv`) and anti-isomorphisms
(`isometryEquivOfLinearEquivOfMapMulRev`) both preserve squares. -/
noncomputable def isometryEquivOfLinearEquivOfMapMulSelf (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (e : A ≃ₗ[k] B) (map_one : e (1 : A) = 1)
    (map_mul_self : ∀ x, e (x * x) = e x * e x) : C.norm.IsometryEquiv D.norm := by
  let E : ConicAlgebra k A :=
    { norm := D.norm.comp e.toLinearMap
      norm_one := by simp [QuadraticMap.comp_apply, map_one, D.norm_one]
      mul_self := fun x ↦ e.injective (by
        simp only [map_mul_self, D.mul_self_eq, map_smul, map_sub, map_one,
          QuadraticMap.comp_apply]
        rw [QuadraticMap.polar]
        simp only [map_add, QuadraticMap.comp_apply]
        change D.trace (e x) • e x - D.norm (e x) • 1 =
          (D.norm (e 1 + e x) - D.norm (e 1) - D.norm (e x)) • e x -
            D.norm (e x) • 1
        rw [map_one]
        rfl) }
  exact
    { toLinearEquiv := e
      map_app' := fun x ↦ by
        change E.norm x = C.norm x
        rw [norm_eq_of_projective C E] }

/-- **`GPR 23.4(a)`, isomorphisms.** A unital multiplicative linear equivalence between conic
algebras is an isometry of their norm forms. In particular, every isomorphism of composition
algebras preserves the norm; the converse, in rank two, is `Composition/NormEquivalence.lean`.

⚠ Mathlib's `AlgEquiv` requires associative multiplication, so the non-associative algebra
isomorphism is deliberately expressed as a `LinearEquiv` plus `map_one` and `map_mul`. -/
noncomputable def isometryEquivOfLinearEquiv (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : A ≃ₗ[k] B) (map_one : e (1 : A) = 1) (map_mul : ∀ x y, e (x * y) = e x * e y) :
    C.norm.IsometryEquiv D.norm :=
  isometryEquivOfLinearEquivOfMapMulSelf C D e map_one fun x ↦ map_mul x x

/-- **`GPR 23.4(a)`, anti-isomorphisms.** A unital linear equivalence reversing multiplication,
`e (x * y) = e y * e x`, between conic algebras is an isometry of their norm forms. For example
the conjugation of a quaternion algebra is one. -/
noncomputable def isometryEquivOfLinearEquivOfMapMulRev (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (e : A ≃ₗ[k] B) (map_one : e (1 : A) = 1)
    (map_mul_rev : ∀ x y, e (x * y) = e y * e x) : C.norm.IsometryEquiv D.norm :=
  isometryEquivOfLinearEquivOfMapMulSelf C D e map_one fun x ↦ map_mul_rev x x

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B] in
/-- A unital multiplicative linear equivalence preserves the conic norm. -/
theorem norm_map_of_linearEquiv (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : A ≃ₗ[k] B) (map_one : e (1 : A) = 1) (map_mul : ∀ x y, e (x * y) = e x * e y)
    (x : A) : D.norm (e x) = C.norm x :=
  (isometryEquivOfLinearEquiv C D e map_one map_mul).map_app x

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B] in
/-- A unital linear equivalence reversing multiplication preserves the conic norm
(`GPR 23.4(a)` for anti-isomorphisms). -/
theorem norm_map_of_linearEquiv_of_map_mul_rev (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : A ≃ₗ[k] B) (map_one : e (1 : A) = 1) (map_mul_rev : ∀ x y, e (x * y) = e y * e x)
    (x : A) : D.norm (e x) = C.norm x :=
  (isometryEquivOfLinearEquivOfMapMulRev C D e map_one map_mul_rev).map_app x

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B] in
/-- A unital multiplicative linear equivalence preserves the trace derived from the conic norm. -/
theorem trace_map_of_linearEquiv (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : A ≃ₗ[k] B) (map_one : e (1 : A) = 1) (map_mul : ∀ x y, e (x * y) = e x * e y)
    (x : A) : D.trace (e x) = C.trace x := by
  rw [trace_apply, trace_apply, QuadraticMap.polar]
  rw [show (1 : B) = e (1 : A) from map_one.symm]
  rw [← map_add, norm_map_of_linearEquiv C D e map_one map_mul,
    norm_map_of_linearEquiv C D e map_one map_mul,
    norm_map_of_linearEquiv C D e map_one map_mul]
  rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B] in
/-- A unital multiplicative linear equivalence preserves the standard conjugation. -/
theorem conj_map_of_linearEquiv (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : A ≃ₗ[k] B) (map_one : e (1 : A) = 1) (map_mul : ∀ x y, e (x * y) = e x * e y)
    (x : A) : D.conj (e x) = e (C.conj x) := by
  rw [conj_apply, conj_apply, trace_map_of_linearEquiv C D e map_one map_mul, map_sub, map_smul,
    map_one]

section Associative

variable {A' : Type v} {B' : Type w} [Ring A'] [Ring B'] [Algebra k A'] [Algebra k B']
  [Module.Finite k A'] [Module.Projective k A'] [Module.Finite k B'] [Module.Projective k B']

/-- For associative conic algebras, the easy direction is available through mathlib's standard
`AlgEquiv` API. -/
noncomputable def isometryEquivOfAlgEquiv (C : ConicAlgebra k A') (D : ConicAlgebra k B')
    (e : A' ≃ₐ[k] B') : C.norm.IsometryEquiv D.norm :=
  isometryEquivOfLinearEquiv C D e.toLinearEquiv e.map_one e.map_mul

end Associative

end Equiv

section Normalize

variable {B : Type w} [NonAssocRing B] [Module k B] [SMulCommClass k B B]
  [IsScalarTower k B B] {D : ConicAlgebra k B}

/-- Left multiplication by `conj x` is a linear equivalence when `n(x) = 1`; its inverse is left
multiplication by `x`. -/
def leftMulConjLinearEquiv [IsAlternative B] (x : B) (hx : D.norm x = 1) : B ≃ₗ[k] B where
  toFun z := D.conj x * z
  invFun z := x * z
  map_add' y z := mul_add _ _ _
  map_smul' c z := mul_smul_comm _ _ _
  left_inv z := by
    change x * (D.conj x * z) = z
    rw [mul_conj_mul_of_isAlternative, hx, one_smul]
  right_inv z := by
    change D.conj x * (x * z) = z
    rw [conj_mul_mul_of_isAlternative, hx, one_smul]

/-- Left multiplication by `conj x`, followed by division by `n(x)`, is a linear equivalence when
`n(x)` is a unit. Its inverse is left multiplication by `x`. -/
def leftMulConjUnitLinearEquiv [IsAlternative B] (x : B) (μ : kˣ)
    (hx : D.norm x = (μ : k)) : B ≃ₗ[k] B where
  toFun z := (↑μ⁻¹ : k) • (D.conj x * z)
  invFun z := x * z
  map_add' y z := by rw [mul_add, smul_add]
  map_smul' c z := by simp only [mul_smul_comm, RingHom.id_apply, smul_smul, mul_comm]
  left_inv z := by
    change x * ((↑μ⁻¹ : k) • (D.conj x * z)) = z
    rw [mul_smul_comm, mul_conj_mul_of_isAlternative, hx, smul_smul, Units.inv_mul, one_smul]
  right_inv z := by
    change (↑μ⁻¹ : k) • (D.conj x * (x * z)) = z
    rw [conj_mul_mul_of_isAlternative, hx, smul_smul, Units.inv_mul, one_smul]

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
/-- For a norm-one element `x` in an alternative multiplicative conic algebra, left multiplication
by `conj x` is a self-isometry of the norm and carries `x` to `1`. -/
noncomputable def IsMultiplicative.leftMulConjIsometryEquiv [IsAlternative B]
    (h : D.IsMultiplicative) (x : B) (hx : D.norm x = 1) : D.norm.IsometryEquiv D.norm where
  toLinearEquiv := D.leftMulConjLinearEquiv x hx
  map_app' z := by
    change D.norm (D.conj x * z) = D.norm z
    rw [h.norm_mul, norm_conj, hx, one_mul]

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
@[simp] theorem IsMultiplicative.leftMulConjIsometryEquiv_apply_self [IsAlternative B]
    (h : D.IsMultiplicative) (x : B) (hx : D.norm x = 1) :
    h.leftMulConjIsometryEquiv x hx x = 1 := by
  change D.conj x * x = 1
  rw [D.conj_mul_self, hx, one_smul]

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
/-- **`GPR 23.3`, for norm similarities.** A similarity from the norm of `C` to the norm of an
alternative multiplicative conic algebra `D` can be normalized to a unital norm isometry.

Here a similarity is given by a linear equivalence `e` and its unit multiplier `μ`, with
`n_D(e x) = μ n_C(x)`. Postcomposition by `μ⁻¹ L_{conj (e 1)}` removes the multiplier and sends
`1` to `1`. -/
theorem IsMultiplicative.exists_isometryEquiv_map_one_of_similarity
    [IsAlternative B] (h : D.IsMultiplicative) (C : ConicAlgebra k A) (e : A ≃ₗ[k] B)
    (μ : kˣ) (he : ∀ x, D.norm (e x) = (μ : k) * C.norm x) :
    ∃ e' : C.norm.IsometryEquiv D.norm, e' (1 : A) = 1 := by
  have hx : D.norm (e (1 : A)) = (μ : k) := by rw [he, C.norm_one, mul_one]
  let f := e.trans (D.leftMulConjUnitLinearEquiv (e 1) μ hx)
  refine ⟨{ toLinearEquiv := f, map_app' := fun z ↦ ?_ }, ?_⟩
  · change D.norm ((↑μ⁻¹ : k) • (D.conj (e 1) * e z)) = C.norm z
    rw [QuadraticMap.map_smul, h.norm_mul, norm_conj, hx, he]
    simp only [smul_eq_mul]
    ring_nf
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    simp
  · change f (1 : A) = 1
    change (↑μ⁻¹ : k) • (D.conj (e 1) * e 1) = 1
    rw [D.conj_mul_self, hx, smul_smul, Units.inv_mul, one_smul]

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  [SMulCommClass k B B] [IsScalarTower k B B] in
/-- **`GPR 23.2`.** A unital norm isometry preserves the trace derived from the polar form. -/
theorem trace_map_of_isometryEquiv_map_one (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : C.norm.IsometryEquiv D.norm) (h1 : e (1 : A) = 1) (x : A) :
    D.trace (e x) = C.trace x := by
  rw [trace_apply, trace_apply, QuadraticMap.polar, QuadraticMap.polar]
  rw [show (1 : B) = e (1 : A) from h1.symm, ← map_add, e.map_app, e.map_app, e.map_app]

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  [SMulCommClass k B B] [IsScalarTower k B B] in
/-- **`GPR 23.2`.** A unital norm isometry commutes with standard conjugation. -/
theorem conj_map_of_isometryEquiv_map_one (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : C.norm.IsometryEquiv D.norm) (h1 : e (1 : A) = 1) (x : A) :
    D.conj (e x) = e (C.conj x) := by
  rw [conj_apply, conj_apply, trace_map_of_isometryEquiv_map_one C D e h1, map_sub, map_smul,
    h1]

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  [SMulCommClass k B B] [IsScalarTower k B B] in
/-- **`GPR 23.2`.** A unital norm isometry preserves squares. This is the multiplication that is
already forced by the degree-two identity before the Cayley–Dickson induction recovers mixed
products. -/
theorem map_mul_self_of_isometryEquiv_map_one (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (e : C.norm.IsometryEquiv D.norm) (h1 : e (1 : A) = 1) (x : A) :
    e (x * x) = e x * e x := by
  calc
    e (x * x) = e (C.trace x • x - C.norm x • (1 : A)) := by rw [C.mul_self_eq]
    _ = C.trace x • e x - C.norm x • e (1 : A) := by rw [map_sub, map_smul, map_smul]
    _ = D.trace (e x) • e x - D.norm (e x) • (1 : B) := by
      rw [trace_map_of_isometryEquiv_map_one C D e h1, e.map_app, h1]
    _ = e x * e x := (D.mul_self_eq (e x)).symm

/-- A unital linear equivalence restricts to a linear equivalence
`k[u] ≃ₗ[k] k[e u]` between the quadratic subalgebras generated by corresponding elements.

No discriminant or rank hypothesis is needed: both subalgebras are, by definition, the spans of
`1` and the indicated element. -/
noncomputable def adjoinElementLinearEquivOfMapOne (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (e : A ≃ₗ[k] B) (h1 : e (1 : A) = 1) (u : A) :
    C.adjoinElement u ≃ₗ[k] D.adjoinElement (e u) where
  toFun x := ⟨e x, by
    obtain ⟨a, b, hx⟩ := (C.mem_adjoinElement_iff u x).mp x.2
    apply (D.mem_adjoinElement_iff (e u) (e x)).mpr
    refine ⟨a, b, ?_⟩
    rw [← h1, ← map_smul, ← map_smul, ← map_add, hx]⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨a, b, hy⟩ := (D.mem_adjoinElement_iff (e u) y).mp y.2
    apply (C.mem_adjoinElement_iff u (e.symm y)).mpr
    refine ⟨a, b, ?_⟩
    rw [← hy, map_add, map_smul, map_smul,
      show e.symm (1 : B) = (1 : A) by rw [← h1, e.symm_apply_apply], e.symm_apply_apply]⟩
  map_add' x y := Subtype.ext (map_add e (x : A) (y : A))
  map_smul' c x := Subtype.ext (map_smul e c (x : A))
  left_inv x := Subtype.ext (e.symm_apply_apply (x : A))
  right_inv x := Subtype.ext (e.apply_symm_apply (x : B))

omit [Module.Finite k A] [Module.Projective k A] in
@[simp] theorem coe_adjoinElementLinearEquivOfMapOne_apply (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (e : A ≃ₗ[k] B) (h1 : e (1 : A) = 1) (u : A)
    (x : C.adjoinElement u) :
    (adjoinElementLinearEquivOfMapOne C D e h1 u x : B) = e (x : A) := rfl

omit [Module.Finite k A] [Module.Projective k A] in
/-- **The quadratic base case for Layer 9.** A unital norm isometry restricts to a unital
multiplicative linear equivalence `k[u] ≅ k[e u]`.

Multiplication in these monogenic conic algebras is the coefficient formula of `GPR 19.8`; its
only structure constants are `t(u)` and `n(u)`, both preserved by a unital norm isometry. -/
theorem adjoinElementLinearEquivOfIsometryEquiv_map_mul
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) (u : A) (x y : C.adjoinElement u) :
    adjoinElementLinearEquivOfMapOne C D e.toLinearEquiv h1 u (x * y) =
      adjoinElementLinearEquivOfMapOne C D e.toLinearEquiv h1 u x *
        adjoinElementLinearEquivOfMapOne C D e.toLinearEquiv h1 u y := by
  apply Subtype.ext
  change e ((x : A) * (y : A)) = e (x : A) * e (y : A)
  obtain ⟨a, b, hx⟩ := (C.mem_adjoinElement_iff u x).mp x.2
  obtain ⟨c, d, hy⟩ := (C.mem_adjoinElement_iff u y).mp y.2
  rw [← hx, ← hy]
  simp only [map_add, map_smul, h1]
  change e (spanOne k u (a, b) * spanOne k u (c, d)) =
    spanOne k (e u) (a, b) * spanOne k (e u) (c, d)
  rw [C.spanOne_mul, D.spanOne_mul]
  simp only [spanOne_apply, map_add, map_smul, h1]
  rw [trace_map_of_isometryEquiv_map_one C D e h1, e.map_app]

omit [Module.Finite k A] [Module.Projective k A] in
@[simp] theorem adjoinElementLinearEquivOfMapOne_apply_one
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : A ≃ₗ[k] B)
    (h1 : e (1 : A) = 1) (u : A) :
    adjoinElementLinearEquivOfMapOne C D e h1 u 1 = 1 :=
  Subtype.ext h1

omit [Module.Finite k A] [Module.Projective k A] in
/-- The quadratic base equivalence of Layer 9, including its norm-isometry structure. -/
noncomputable def adjoinElementIsometryEquivOfMapOne
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) (u : A) :
    (C.restrict (C.adjoinElement u)).norm.IsometryEquiv
      (D.restrict (D.adjoinElement (e u))).norm where
  toLinearEquiv := adjoinElementLinearEquivOfMapOne C D e.toLinearEquiv h1 u
  map_app' x := e.map_app (x : A)

omit [Module.Finite k A] [Module.Projective k A] in
/-- **The first Cayley–Dickson step in Layer 9.** The corresponding quadratic subalgebras
`k[u]` and `k[e u]` can be doubled by any common scalar `μ`; the componentwise equivalence is a
unital, multiplicative norm isometry.

The complement isometry obtained from Witt cancellation supplies such a common scalar by carrying
a chosen doubling vector to one with the same norm. -/
noncomputable def cayAdjoinElementIsometryEquivOfMapOne
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) (u : A) (μ : k) :
    ((C.restrict (C.adjoinElement u)).cay μ).norm.IsometryEquiv
      ((D.restrict (D.adjoinElement (e u))).cay μ).norm :=
  cayIsometryEquiv (D.restrict (D.adjoinElement (e u)))
    (adjoinElementIsometryEquivOfMapOne C D e h1 u)

omit [Module.Finite k A] [Module.Projective k A] in
/-- The matched equivalence between the first doubles preserves the identity. -/
theorem cayAdjoinElementIsometryEquivOfMapOne_map_one
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) (u : A) (μ : k) :
    cayAdjoinElementIsometryEquivOfMapOne C D e h1 u μ 1 = 1 :=
  cayIsometryEquiv_map_one (C := C.restrict (C.adjoinElement u)) (μ := μ)
    (D.restrict (D.adjoinElement (e u)))
    (adjoinElementIsometryEquivOfMapOne C D e h1 u)
    (adjoinElementLinearEquivOfMapOne_apply_one C D e.toLinearEquiv h1 u)

omit [Module.Finite k A] [Module.Projective k A] in
/-- The matched equivalence between the first doubles preserves multiplication. -/
theorem cayAdjoinElementIsometryEquivOfMapOne_map_mul
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) (u : A) (μ : k)
    (x y : Cay (C.restrict (C.adjoinElement u)) μ) :
    cayAdjoinElementIsometryEquivOfMapOne C D e h1 u μ (x * y) =
      cayAdjoinElementIsometryEquivOfMapOne C D e h1 u μ x *
        cayAdjoinElementIsometryEquivOfMapOne C D e h1 u μ y :=
  cayIsometryEquiv_map_mul (C := C.restrict (C.adjoinElement u)) (μ := μ)
    (D.restrict (D.adjoinElement (e u)))
    (adjoinElementIsometryEquivOfMapOne C D e h1 u)
    (adjoinElementLinearEquivOfMapOne_apply_one C D e.toLinearEquiv h1 u)
    (adjoinElementLinearEquivOfIsometryEquiv_map_mul C D e h1 u) x y

section MatchedDouble

variable [Module.Finite k B] [Module.Projective k B] [IsAlternative A] [IsAlternative B]

/-- **One internal matched-doubling step for Layer 9.** Suppose `S ⊆ A` and `T ⊆ B` are
already related by a unital multiplicative norm isometry. If `v ⊥ S` and `v' ⊥ T` have the
same norm, then the internal doubles `S + Sv` and `T + Tv'` are again related by such an
isometry, provided the two internal doubling maps are injective.

The resulting subalgebras are the images of `cayToAlgebra`. The equivalence is obtained by moving
back to the external double, applying `cayIsometryEquiv` componentwise, and moving into the other
image. -/
theorem exists_doubledSubalgebras_isometryEquiv_and_equiv_cay (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B)
    (hCmul : C.IsMultiplicative) (hDmul : D.IsMultiplicative)
    (e : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (h1 : e (1 : S) = 1) (hmul : ∀ x y, e (x * y) = e x * e y) {v : A} {v' : B}
    (hSv : ∀ s ∈ S, QuadraticMap.polar C.norm s v = 0)
    (hTv' : ∀ t ∈ T, QuadraticMap.polar D.norm t v' = 0)
    (hv : IsUnit (C.norm v)) (hnorm : D.norm v' = C.norm v)
    (hinjC : Function.Injective (cayToAlgebra C S v))
    (hinjD : Function.Injective (cayToAlgebra D T v')) :
    ∃ (S' : NonAssocSubalgebra k A) (T' : NonAssocSubalgebra k B)
      (iC : Cay (C.restrict S) (-C.norm v) ≃ₗ[k] S')
      (iD : Cay (D.restrict T) (-D.norm v') ≃ₗ[k] T')
      (f : (C.restrict S').norm.IsometryEquiv (D.restrict T').norm),
      (∀ p, ((iC p : S') : A) = cayToAlgebra C S v p) ∧
        (∀ p, ((iD p : T') : B) = cayToAlgebra D T v' p) ∧
          f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y := by
  have hv' : IsUnit (D.norm v') := hnorm.symm ▸ hv
  obtain ⟨S', iC, hiC⟩ := exists_subalgebra_equiv_cay hSv hv hinjC
  obtain ⟨T', iD, hiD⟩ := exists_subalgebra_equiv_cay hTv' hv' hinjD
  let esame := cayIsometryEquiv (C := C.restrict S) (μ := -C.norm v) (D.restrict T) e
  let eparam := cayIsometryEquivOfEq (D.restrict T) (congrArg Neg.neg hnorm.symm)
  let ecay := esame.trans eparam
  let fLinear : S' ≃ₗ[k] T' := iC.symm.trans (ecay.toLinearEquiv.trans iD)
  have hiC_one : iC 1 = 1 := by
    apply Subtype.ext
    change (iC 1 : A) = 1
    rw [hiC, cayToAlgebra_one]
  have hiD_one : iD 1 = 1 := by
    apply Subtype.ext
    change (iD 1 : B) = 1
    rw [hiD, cayToAlgebra_one]
  have hiC_mul (x y : Cay (C.restrict S) (-C.norm v)) : iC (x * y) = iC x * iC y := by
    apply Subtype.ext
    change (iC (x * y) : A) = (iC x : A) * (iC y : A)
    rw [hiC, hiC, hiC, cayToAlgebra_mul hSv C.conjIsInvolution_of_projective hv]
  have hiD_mul (x y : Cay (D.restrict T) (-D.norm v')) : iD (x * y) = iD x * iD y := by
    apply Subtype.ext
    change (iD (x * y) : B) = (iD x : B) * (iD y : B)
    rw [hiD, hiD, hiD,
      cayToAlgebra_mul hTv' D.conjIsInvolution_of_projective hv']
  have hiC_symm_one : iC.symm 1 = 1 := by
    rw [← hiC_one, iC.symm_apply_apply]
  have hiC_symm_mul (x y : S') : iC.symm (x * y) = iC.symm x * iC.symm y := by
    apply iC.injective
    rw [iC.apply_symm_apply, hiC_mul, iC.apply_symm_apply, iC.apply_symm_apply]
  let f : (C.restrict S').norm.IsometryEquiv (D.restrict T').norm :=
    { toLinearEquiv := fLinear
      map_app' := fun x ↦ by
        change D.norm (iD (ecay (iC.symm x)) : B) = C.norm (x : A)
        rw [hiD, norm_cayToAlgebra hTv' hDmul, ecay.map_app,
          ← norm_cayToAlgebra hSv hCmul, ← hiC, iC.apply_symm_apply] }
  refine ⟨S', T', iC, iD, f, hiC, hiD, ?_, ?_⟩
  · change iD (ecay (iC.symm 1)) = 1
    rw [hiC_symm_one, show ecay 1 = 1 by
      change eparam (esame 1) = 1
      rw [cayIsometryEquiv_map_one _ e h1, cayIsometryEquivOfEq_map_one], hiD_one]
  · intro x y
    change iD (ecay (iC.symm (x * y))) =
      iD (ecay (iC.symm x)) * iD (ecay (iC.symm y))
    rw [hiC_symm_mul, show ∀ p q, ecay (p * q) = ecay p * ecay q by
      intro p q
      change eparam (esame (p * q)) = eparam (esame p) * eparam (esame q)
      rw [cayIsometryEquiv_map_mul _ e h1 hmul, cayIsometryEquivOfEq_map_mul], hiD_mul]

/-- The internal matched-doubling step, with the external-to-image equivalences hidden. -/
theorem exists_doubledSubalgebras_isometryEquiv (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B)
    (hCmul : C.IsMultiplicative) (hDmul : D.IsMultiplicative)
    (e : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (h1 : e (1 : S) = 1) (hmul : ∀ x y, e (x * y) = e x * e y) {v : A} {v' : B}
    (hSv : ∀ s ∈ S, QuadraticMap.polar C.norm s v = 0)
    (hTv' : ∀ t ∈ T, QuadraticMap.polar D.norm t v' = 0)
    (hv : IsUnit (C.norm v)) (hnorm : D.norm v' = C.norm v)
    (hinjC : Function.Injective (cayToAlgebra C S v))
    (hinjD : Function.Injective (cayToAlgebra D T v')) :
    ∃ (S' : NonAssocSubalgebra k A) (T' : NonAssocSubalgebra k B)
      (f : (C.restrict S').norm.IsometryEquiv (D.restrict T').norm),
      f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y := by
  obtain ⟨S', T', _, _, f, _, _, h1, hmul⟩ :=
    exists_doubledSubalgebras_isometryEquiv_and_equiv_cay C D S T hCmul hDmul e h1 hmul
      hSv hTv' hv hnorm hinjC hinjD
  exact ⟨S', T', f, h1, hmul⟩

/-- The regular-base form of `exists_doubledSubalgebras_isometryEquiv`. Regularity makes both
internal doubling maps injective, so it is the form used by the Layer 9 induction. -/
theorem exists_doubledSubalgebras_isometryEquiv_of_isGPRRegular
    (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B)
    (hCmul : C.IsMultiplicative) (hDmul : D.IsMultiplicative)
    (hSreg : QuadraticForm.IsGPRRegular (C.restrict S).norm)
    (hTreg : QuadraticForm.IsGPRRegular (D.restrict T).norm)
    (e : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (h1 : e (1 : S) = 1) (hmul : ∀ x y, e (x * y) = e x * e y) {v : A} {v' : B}
    (hSv : ∀ s ∈ S, QuadraticMap.polar C.norm s v = 0)
    (hTv' : ∀ t ∈ T, QuadraticMap.polar D.norm t v' = 0)
    (hv : IsUnit (C.norm v)) (hnorm : D.norm v' = C.norm v) :
    ∃ (S' : NonAssocSubalgebra k A) (T' : NonAssocSubalgebra k B)
      (f : (C.restrict S').norm.IsometryEquiv (D.restrict T').norm),
      f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y := by
  have hv' : IsUnit (D.norm v') := hnorm.symm ▸ hv
  exact exists_doubledSubalgebras_isometryEquiv C D S T hCmul hDmul e h1 hmul hSv hTv' hv
    hnorm (cayToAlgebra_injective hSv hv hCmul hSreg)
      (cayToAlgebra_injective hTv' hv' hDmul hTreg)

end MatchedDouble

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The canonical linear equivalence from a rank-one conic algebra to its base ring. -/
noncomputable def unitFormLinearEquivOfRankAtStalkEqOne (C : ConicAlgebra k A)
    [Nontrivial k] (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) : A ≃ₗ[k] k where
  toLinearMap := C.unitForm
  invFun a := a • (1 : A)
  left_inv x := (eq_unitForm_smul_one_of_rankAtStalk_eq_one C hA x).symm
  right_inv a := by simp

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem unitFormLinearEquivOfRankAtStalkEqOne_apply_one
    (C : ConicAlgebra k A) [Nontrivial k]
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) :
    unitFormLinearEquivOfRankAtStalkEqOne C hA (1 : A) = 1 :=
  C.unitForm_one

omit [SMulCommClass k A A] [SMulCommClass k B B] in
/-- Every unital linear equivalence between constant-rank-one conic algebras is multiplicative. -/
theorem linearEquiv_map_mul_of_rankAtStalk_eq_one [Nontrivial k] (C : ConicAlgebra k A)
    (e : A ≃ₗ[k] B) (he1 : e (1 : A) = 1)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) (x y : A) :
    e (x * y) = e x * e y := by
  have hprod (a b : k) : (a • (1 : A)) * (b • 1) = (a * b) • (1 : A) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
  have hprodB (a b : k) : (a • (1 : B)) * (b • 1) = (a * b) • (1 : B) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
  rw [eq_unitForm_smul_one_of_rankAtStalk_eq_one C hA x,
    eq_unitForm_smul_one_of_rankAtStalk_eq_one C hA y, hprod, map_smul, he1, map_smul,
    map_smul, he1, hprodB]

omit [SMulCommClass k A A] [SMulCommClass k B B] in
/-- **The rank-one case of the converse direction in Layer 9.** Any two constant-rank-one conic
algebras over a nontrivial base are unital multiplicatively norm-isometric. Both are canonically
identified with the base ring by `unitForm`; this avoids imposing regularity on the polar form,
which can fail in characteristic two. -/
theorem exists_isometryEquiv_map_one_map_mul_of_rankAtStalk_eq_one
    [Module.Finite k B] [Module.Projective k B] [Nontrivial k]
    (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1)
    (hB : Module.rankAtStalk (R := k) B = fun _ ↦ 1) :
    ∃ e : C.norm.IsometryEquiv D.norm,
      e (1 : A) = 1 ∧ ∀ x y, e (x * y) = e x * e y := by
  let eA := unitFormLinearEquivOfRankAtStalkEqOne C hA
  let eB := unitFormLinearEquivOfRankAtStalkEqOne D hB
  let g : A ≃ₗ[k] B := eA.trans eB.symm
  have hg1 : g (1 : A) = 1 := by
    apply eB.injective
    simp [g, eA, eB]
  have hgmul : ∀ x y, g (x * y) = g x * g y :=
    linearEquiv_map_mul_of_rankAtStalk_eq_one C g hg1 hA
  exact ⟨isometryEquivOfLinearEquiv C D g hg1 hgmul, hg1, hgmul⟩

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- **Full-rank assembly for Layer 9.** A unital multiplicative norm isometry between regular
subalgebras of the same full rank extends to the ambient algebras, because each inclusion is then
a linear equivalence.

The full-rank assertion is converted to surjectivity by
`ConicAlgebra.mem_of_isGPRRegular_of_rankAtStalk_eq`; no choice of complements remains at this
stage. -/
theorem isometryEquivOf_fullRank_subalgebras [Module.Finite k B] [Module.Projective k B]
    (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B)
    (f : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (hf1 : f (1 : S) = 1) (hfmul : ∀ x y, f (x * y) = f x * f y)
    (hSreg : QuadraticForm.IsGPRRegular (C.restrict S).norm)
    (hTreg : QuadraticForm.IsGPRRegular (D.restrict T).norm) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hB : Module.rankAtStalk (R := k) B = fun _ ↦ r)
    (hS : Module.rankAtStalk (R := k) S.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ r)
    (hT : Module.rankAtStalk (R := k) T.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ r) :
    ∃ e : C.norm.IsometryEquiv D.norm,
      e (1 : A) = 1 ∧ ∀ x y, e (x * y) = e x * e y := by
  let incS : S →ₗ[k] A := S.toNonUnitalSubalgebra.toSubmodule.subtype
  let incT : T →ₗ[k] B := T.toNonUnitalSubalgebra.toSubmodule.subtype
  have hincS : Function.Bijective incS :=
    ⟨Subtype.val_injective, fun x ↦
      ⟨⟨x, mem_of_isGPRRegular_of_rankAtStalk_eq hSreg hA hS x⟩, rfl⟩⟩
  have hincT : Function.Bijective incT :=
    ⟨Subtype.val_injective, fun x ↦
      ⟨⟨x, mem_of_isGPRRegular_of_rankAtStalk_eq hTreg hB hT x⟩, rfl⟩⟩
  let eS : S ≃ₗ[k] A := LinearEquiv.ofBijective incS hincS
  let eT : T ≃ₗ[k] B := LinearEquiv.ofBijective incT hincT
  have eS_one : eS (1 : S) = 1 := rfl
  have eT_one : eT (1 : T) = 1 := rfl
  have eS_symm_one : eS.symm (1 : A) = 1 := by
    rw [← eS_one, eS.symm_apply_apply]
  have eS_symm_mul (x y : A) : eS.symm (x * y) = eS.symm x * eS.symm y := by
    apply eS.injective
    rw [eS.apply_symm_apply]
    change x * y = (eS (eS.symm x) : A) * eS (eS.symm y)
    rw [eS.apply_symm_apply, eS.apply_symm_apply]
  let eLinear : A ≃ₗ[k] B := eS.symm.trans (f.toLinearEquiv.trans eT)
  let e : C.norm.IsometryEquiv D.norm :=
    { toLinearEquiv := eLinear
      map_app' := fun x ↦
        calc
          D.norm (f (eS.symm x) : B) = (D.restrict T).norm (f (eS.symm x)) := rfl
          _ = (C.restrict S).norm (eS.symm x) := f.map_app _
          _ = C.norm (eS (eS.symm x)) := rfl
          _ = C.norm x := by rw [eS.apply_symm_apply] }
  refine ⟨e, ?_, ?_⟩
  · change eT (f (eS.symm 1)) = 1
    rw [eS_symm_one, hf1, eT_one]
  · intro x y
    change eT (f (eS.symm (x * y))) =
      eT (f (eS.symm x)) * eT (f (eS.symm y))
    rw [eS_symm_mul, hfmul]
    rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A]
  [Module.Projective k A] [SMulCommClass k B B] [IsScalarTower k B B] in
/-- A unital norm isometry preserves the element discriminant `t(u) ^ 2 - 4 * n(u)`. -/
theorem elementDiscriminant_map_of_isometryEquiv_map_one
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) (u : A) :
    D.elementDiscriminant (e u) = C.elementDiscriminant u := by
  rw [elementDiscriminant, elementDiscriminant,
    trace_map_of_isometryEquiv_map_one C D e h1, e.map_app]

omit [Module.Finite k A] [Module.Projective k A] in
/-- A unital norm isometry carries the regular rank-two composition subalgebra generated by `u`
to the one generated by `e u`. This is the base rung that the Layer 9 doubling induction uses. -/
theorem isRegularRankTwoComposition_map_of_isometryEquiv_map_one
    (C : ConicAlgebra k A) (D : ConicAlgebra k B) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) {u : A} (hu : C.IsRegularRankTwoComposition u) :
    D.IsRegularRankTwoComposition (e u) := by
  rw [D.isRegularRankTwoComposition_iff_isUnit_discriminant,
    elementDiscriminant_map_of_isometryEquiv_map_one C D e h1]
  exact (C.isRegularRankTwoComposition_iff_isUnit_discriminant u).mp hu

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- **The general Witt-cancellation step for Layer 9.** If an ambient norm isometry identifies
the regular restricted norm forms on `S ⊆ A` and `T ⊆ B`, then their orthogonal complements
are isometric over an LG ring.

This is the form needed after every matched doubling rung. The target ambient norm is assumed
non-singular in the GPR sense through `hD`; no composition hypothesis on `C` is used. -/
theorem exists_isometryEquiv_polarOrthogonal [Module.Finite k B] [Module.Projective k B]
    (hLG : IsLGRing k) (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hD : D.IsComposition.{u, w, u}) (S : NonAssocSubalgebra k A)
    (T : NonAssocSubalgebra k B) (hSreg : QuadraticForm.IsGPRRegular (C.restrict S).norm)
    (hTreg : QuadraticForm.IsGPRRegular (D.restrict T).norm)
    (eST : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (e : C.norm.IsometryEquiv D.norm) :
    Nonempty
      ((C.norm.comp
          (C.norm.polarOrthogonal S.toNonUnitalSubalgebra.toSubmodule).subtype).IsometryEquiv
        (D.norm.comp
          (D.norm.polarOrthogonal T.toNonUnitalSubalgebra.toSubmodule).subtype)) := by
  let NS := S.toNonUnitalSubalgebra.toSubmodule
  let NT := T.toNonUnitalSubalgebra.toSubmodule
  let qPS := C.norm.comp (C.norm.polarOrthogonal NS).subtype
  let qPT := D.norm.comp (D.norm.polarOrthogonal NT).subtype
  let : Module.Finite k NS := QuadraticForm.finite_of_comp_isGPRRegular hSreg
  let : Module.Projective k NS := QuadraticForm.projective_of_comp_isGPRRegular hSreg
  let : Module.Finite k (D.norm.polarOrthogonal NT) :=
    QuadraticForm.finite_polarOrthogonal hTreg
  let : Module.Projective k (D.norm.polarOrthogonal NT) :=
    QuadraticForm.projective_polarOrthogonal hTreg
  have hPT : QuadraticForm.IsGPRNonsingular.{u, w, u} qPT :=
    hD.isGPRNonsingular.comp_polarOrthogonal_subtype hTreg
  let total : (qPS.prod (C.norm.comp NS.subtype)).IsometryEquiv
      (qPT.prod (C.norm.comp NS.subtype)) :=
    (QuadraticMap.IsometryEquiv.prodComm _ _).trans
      ((QuadraticForm.orthogonalDecompositionIsometryEquiv hSreg).trans
        (e.trans ((QuadraticForm.orthogonalDecompositionIsometryEquiv hTreg).symm.trans
          ((QuadraticMap.IsometryEquiv.prod eST.symm
            (QuadraticMap.IsometryEquiv.refl qPT)).trans
              (QuadraticMap.IsometryEquiv.prodComm _ _)))))
  exact QuadraticForm.cancel hLG hPT hSreg ⟨total⟩

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- **Selecting matched doubling vectors at an arbitrary Layer 9 rung.** If the complement of
`S` has full support, it represents a unit over the LG ring. The general cancellation isometry
then carries that vector to the complement of `T`, preserving its norm exactly. -/
theorem IsComposition.exists_matched_isUnit_norm_orthogonal [Module.Finite k B]
    [Module.Projective k B] (hLG : IsLGRing k) (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (hC : C.IsComposition.{u, v, u})
    (hD : D.IsComposition.{u, w, u}) (S : NonAssocSubalgebra k A)
    (T : NonAssocSubalgebra k B) (hSreg : QuadraticForm.IsGPRRegular (C.restrict S).norm)
    (hTreg : QuadraticForm.IsGPRRegular (D.restrict T).norm)
    (eST : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (e : C.norm.IsometryEquiv D.norm)
    (hsupp : Module.HasFullSupport k
      (C.norm.polarOrthogonal S.toNonUnitalSubalgebra.toSubmodule)) :
    ∃ v : A, ∃ v' : B, IsUnit (C.norm v) ∧
      (∀ s ∈ S, QuadraticMap.polar C.norm s v = 0) ∧
      (∀ t ∈ T, QuadraticMap.polar D.norm t v' = 0) ∧ D.norm v' = C.norm v := by
  obtain ⟨v, hv, hSv⟩ := hC.exists_isUnit_norm_orthogonal hLG hSreg hsupp
  obtain ⟨g⟩ := exists_isometryEquiv_polarOrthogonal hLG C D hD S T hSreg hTreg eST e
  let vS : C.norm.polarOrthogonal S.toNonUnitalSubalgebra.toSubmodule :=
    ⟨v, fun s hs ↦ hSv s hs⟩
  refine ⟨v, (g vS : B), hv, hSv, ?_, g.map_app vS⟩
  exact fun t ht ↦ (g vS).2 t ht

/-- **One complete induction step for Layer 9.** Matched regular subalgebras with a proper source
complement can be enlarged simultaneously: unit representation and Witt cancellation choose
matched orthogonal vectors, and internal Cayley–Dickson doubling produces new image subalgebras
related by a unital multiplicative norm isometry. -/
theorem IsComposition.exists_next_doubledSubalgebras_isometryEquiv [Module.Finite k B]
    [Module.Projective k B] [IsAlternative A] [IsAlternative B]
    (hLG : IsLGRing k) (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B)
    (hSreg : QuadraticForm.IsGPRRegular (C.restrict S).norm)
    (hTreg : QuadraticForm.IsGPRRegular (D.restrict T).norm)
    (eST : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (h1 : eST (1 : S) = 1) (hmul : ∀ x y, eST (x * y) = eST x * eST y)
    (e : C.norm.IsometryEquiv D.norm)
    (hsupp : Module.HasFullSupport k
      (C.norm.polarOrthogonal S.toNonUnitalSubalgebra.toSubmodule)) :
    ∃ (S' : NonAssocSubalgebra k A) (T' : NonAssocSubalgebra k B)
      (f : (C.restrict S').norm.IsometryEquiv (D.restrict T').norm),
      f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y := by
  obtain ⟨v, v', hv, hSv, hTv', hnorm⟩ :=
    hC.exists_matched_isUnit_norm_orthogonal hLG C D hD S T hSreg hTreg eST e hsupp
  exact exists_doubledSubalgebras_isometryEquiv_of_isGPRRegular C D S T
    hC.isMultiplicative hD.isMultiplicative hSreg hTreg eST h1 hmul hSv hTv' hv hnorm

/-- **The self-feeding Layer 9 induction step.** If the matched input subalgebras both have
constant rank `s`, the enlarged subalgebras have regular restricted norms and constant rank `2s`,
in addition to carrying the new unital multiplicative norm isometry. Thus the output satisfies the
hypotheses needed for the next doubling rung. -/
theorem IsComposition.exists_next_isGPRRegular_rankAtStalk_two_mul
    [Module.Finite k B] [Module.Projective k B] [IsAlternative A] [IsAlternative B]
    (hLG : IsLGRing k) (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B)
    (hSreg : QuadraticForm.IsGPRRegular (C.restrict S).norm)
    (hTreg : QuadraticForm.IsGPRRegular (D.restrict T).norm)
    (eST : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm)
    (h1 : eST (1 : S) = 1) (hmul : ∀ x y, eST (x * y) = eST x * eST y)
    (e : C.norm.IsometryEquiv D.norm) {s : ℕ}
    (hSrank : Module.rankAtStalk (R := k) S.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ s)
    (hTrank : Module.rankAtStalk (R := k) T.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ s)
    (hsupp : Module.HasFullSupport k
      (C.norm.polarOrthogonal S.toNonUnitalSubalgebra.toSubmodule)) :
    ∃ (S' : NonAssocSubalgebra k A) (T' : NonAssocSubalgebra k B)
      (f : (C.restrict S').norm.IsometryEquiv (D.restrict T').norm),
      f 1 = 1 ∧ (∀ x y, f (x * y) = f x * f y) ∧
        QuadraticForm.IsGPRRegular (C.restrict S').norm ∧
        QuadraticForm.IsGPRRegular (D.restrict T').norm ∧
        (Module.rankAtStalk (R := k) S'.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ 2 * s) ∧
        (Module.rankAtStalk (R := k) T'.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ 2 * s) := by
  obtain ⟨v, v', hv, hSv, hTv', hnorm⟩ :=
    hC.exists_matched_isUnit_norm_orthogonal hLG C D hD S T hSreg hTreg eST e hsupp
  have hv' : IsUnit (D.norm v') := hnorm.symm ▸ hv
  obtain ⟨S', T', iC, iD, f, hiC, hiD, hf1, hfmul⟩ :=
    exists_doubledSubalgebras_isometryEquiv_and_equiv_cay C D S T hC.isMultiplicative
      hD.isMultiplicative eST h1 hmul hSv hTv' hv hnorm
        (cayToAlgebra_injective hSv hv hC.isMultiplicative hSreg)
        (cayToAlgebra_injective hTv' hv' hD.isMultiplicative hTreg)
  obtain ⟨hS'reg, hS'rank⟩ := isGPRRegular_restrict_and_rankAtStalk_of_equiv_cay
    hC hSreg hSv hv S' iC hiC hSrank
  obtain ⟨hT'reg, hT'rank⟩ := isGPRRegular_restrict_and_rankAtStalk_of_equiv_cay
    hD hTreg hTv' hv' T' iD hiD hTrank
  exact ⟨S', T', f, hf1, hfmul, hS'reg, hT'reg, hS'rank, hT'rank⟩

/-- The fuel-based finite iteration behind the converse direction of Layer 9. -/
private theorem IsComposition.exists_fullRank_subalgebras_isometryEquiv_aux
    [Nontrivial k] [Module.Finite k B] [Module.Projective k B]
    [IsAlternative A] [IsAlternative B] (hLG : IsLGRing k)
    (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u}) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hB : Module.rankAtStalk (R := k) B = fun _ ↦ r)
    (e : C.norm.IsometryEquiv D.norm) :
    ∀ (n s : ℕ) (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B),
      QuadraticForm.IsGPRRegular (C.restrict S).norm →
      QuadraticForm.IsGPRRegular (D.restrict T).norm →
      ∀ f : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm,
      f (1 : S) = 1 → (∀ x y, f (x * y) = f x * f y) →
      Module.rankAtStalk (R := k) S.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ s) →
      Module.rankAtStalk (R := k) T.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ s) →
      0 < s → s ≤ r → r - s ≤ n →
      ∃ (S' : NonAssocSubalgebra k A) (T' : NonAssocSubalgebra k B)
        (f' : (C.restrict S').norm.IsometryEquiv (D.restrict T').norm),
        f' 1 = 1 ∧ (∀ x y, f' (x * y) = f' x * f' y) ∧
          QuadraticForm.IsGPRRegular (C.restrict S').norm ∧
          QuadraticForm.IsGPRRegular (D.restrict T').norm ∧
          (Module.rankAtStalk (R := k) S'.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ r) ∧
          (Module.rankAtStalk (R := k) T'.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ r) := by
  intro n
  induction n with
  | zero =>
      intro s S T hSreg hTreg f hf1 hfmul hSrank hTrank hs0 hsr hfuel
      have hsr' : s = r := by omega
      subst r
      exact ⟨S, T, f, hf1, hfmul, hSreg, hTreg, hSrank, hTrank⟩
  | succ n ih =>
      intro s S T hSreg hTreg f hf1 hfmul hSrank hTrank hs0 hsr hfuel
      by_cases hfull : s = r
      · subst r
        exact ⟨S, T, f, hf1, hfmul, hSreg, hTreg, hSrank, hTrank⟩
      · have hlt : s < r := lt_of_le_of_ne hsr hfull
        have hsupp := hasFullSupport_polarOrthogonal_of_rankAtStalk_lt
          (C := C) hSreg hA hSrank hlt
        obtain ⟨S', T', f', hf1', hfmul', hS'reg, hT'reg, hS'rank, hT'rank⟩ :=
          hC.exists_next_isGPRRegular_rankAtStalk_two_mul hLG C D hD S T hSreg hTreg
            f hf1 hfmul e hSrank hTrank hsupp
        have hle : 2 * s ≤ r := by
          have hle' := rankAtStalk_le_of_isGPRRegular hS'reg
            (Classical.arbitrary (PrimeSpectrum k))
          rwa [hS'rank, hA] at hle'
        exact ih (2 * s) S' T' hS'reg hT'reg f' hf1' hfmul' hS'rank hT'rank
          (by omega) hle (by omega)

/-- **Finite matched doubling from rank two to full rank.** Starting from corresponding regular
quadratic subalgebras, the self-feeding step is iterated until both image subalgebras have the full
ambient rank. -/
theorem IsComposition.exists_fullRank_subalgebras_isometryEquiv
    [Nontrivial k] [Module.Finite k B] [Module.Projective k B]
    [IsAlternative A] [IsAlternative B] (hLG : IsLGRing k)
    (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (e : C.norm.IsometryEquiv D.norm) (he1 : e (1 : A) = 1) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hB : Module.rankAtStalk (R := k) B = fun _ ↦ r) (hr : 2 ≤ r) :
    ∃ (S : NonAssocSubalgebra k A) (T : NonAssocSubalgebra k B)
      (f : (C.restrict S).norm.IsometryEquiv (D.restrict T).norm),
      f 1 = 1 ∧ (∀ x y, f (x * y) = f x * f y) ∧
        QuadraticForm.IsGPRRegular (C.restrict S).norm ∧
        QuadraticForm.IsGPRRegular (D.restrict T).norm ∧
        (Module.rankAtStalk (R := k) S.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ r) ∧
        (Module.rankAtStalk (R := k) T.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ r) := by
  obtain ⟨u, hu⟩ := hC.exists_isRegularRankTwoComposition_of_rankAtStalk hLG fun p ↦ by
    rw [hA]
    exact hr
  have huD : D.IsRegularRankTwoComposition (e u) :=
    isRegularRankTwoComposition_map_of_isometryEquiv_map_one C D e he1 hu
  let S := C.adjoinElement u
  let T := D.adjoinElement (e u)
  have hdisc : IsUnit (C.elementDiscriminant u) :=
    (C.isRegularRankTwoComposition_iff_isUnit_discriminant u).mp hu
  have hdiscD : IsUnit (D.elementDiscriminant (e u)) :=
    (D.isRegularRankTwoComposition_iff_isUnit_discriminant (e u)).mp huD
  have hSreg : QuadraticForm.IsGPRRegular (C.restrict S).norm :=
    C.normAdjoinElement_isGPRRegular hdisc
  have hTreg : QuadraticForm.IsGPRRegular (D.restrict T).norm :=
    D.normAdjoinElement_isGPRRegular hdiscD
  let f := adjoinElementIsometryEquivOfMapOne C D e he1 u
  have hf1 : f (1 : S) = 1 :=
    adjoinElementLinearEquivOfMapOne_apply_one C D e.toLinearEquiv he1 u
  have hfmul : ∀ x y, f (x * y) = f x * f y :=
    adjoinElementLinearEquivOfIsometryEquiv_map_mul C D e he1 u
  have hSrank := C.rankAtStalk_adjoinElement hdisc
  have hTrank := D.rankAtStalk_adjoinElement hdiscD
  exact hC.exists_fullRank_subalgebras_isometryEquiv_aux hLG C D hD hA hB e
    (r - 2) 2 S T hSreg hTreg f hf1 hfmul hSrank hTrank (by omega) hr (by omega)

/-- **`GPR 23.5`, the norm equivalence theorem, in constant rank at least two.** Over a nontrivial
LG ring, composition algebras of the same constant rank `r ≥ 2` with isometric norm forms are
isomorphic as unital non-associative algebras. The isomorphism is expressed, as elsewhere in this
file, by a linear equivalence together with its unital and multiplicative laws.

The proof normalizes the norm isometry at `1`, matches the regular quadratic starting
subalgebras, iterates the matched Cayley–Dickson enlargement to full rank, and finally identifies
the full-rank image subalgebras with the ambient algebras. -/
theorem IsComposition.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk
    [Nontrivial k] [Module.Finite k B] [Module.Projective k B]
    (hLG : IsLGRing k) (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (e : C.norm.IsometryEquiv D.norm) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : 2 ≤ r) :
    ∃ e' : C.norm.IsometryEquiv D.norm,
      e' (1 : A) = 1 ∧ ∀ x y, e' (x * y) = e' x * e' y := by
  have hB : Module.rankAtStalk (R := k) B = fun _ ↦ r :=
    (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv).symm.trans hA
  have hCreg : C.norm.IsGPRRegular :=
    hC.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  have hDreg : D.norm.IsGPRRegular :=
    hD.isGPRRegular_of_rankAtStalk_ne_one hB (by omega)
  have hCnd : C.norm.IsGPRNondegenerate :=
    Submodule.eq_bot_iff _ |>.mpr fun _ hx ↦
      (injective_iff_map_eq_zero _).mp hCreg.1 _ hx.2
  have hDnd : D.norm.IsGPRNondegenerate :=
    Submodule.eq_bot_iff _ |>.mpr fun _ hx ↦
      (injective_iff_map_eq_zero _).mp hDreg.1 _ hx.2
  let : IsAlternative A := hC.isMultiplicative.isAlternative hCnd
  let : IsAlternative B := hD.isMultiplicative.isAlternative hDnd
  have hx : D.norm (e (1 : A)) = 1 := by rw [e.map_app, C.norm_one]
  let e1 := e.trans (hD.isMultiplicative.leftMulConjIsometryEquiv (e 1) hx)
  have he1 : e1 (1 : A) = 1 :=
    hD.isMultiplicative.leftMulConjIsometryEquiv_apply_self (e 1) hx
  obtain ⟨S, T, f, hf1, hfmul, hSreg, hTreg, hSrank, hTrank⟩ :=
    hC.exists_fullRank_subalgebras_isometryEquiv hLG C D hD e1 he1 hA hB hr
  exact isometryEquivOf_fullRank_subalgebras C D S T f hf1 hfmul hSreg hTreg
    hA hB hSrank hTrank

/-- **`GPR 23.5`, the norm equivalence theorem.** Over a nontrivial LG ring, composition algebras
of the same constant rank with isometric norm forms are isomorphic as unital
non-associative algebras.

By `GPR 19.18`, the common rank is `1`, `2`, `4`, or `8`. Rank one is handled directly through the
canonical `unitForm` coordinate, while the other three cases use the regular matched-doubling
argument based on `GPR 19.16(b)` and Witt cancellation (`GN 6.5`). -/
theorem IsComposition.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk_eq
    [Nontrivial k] [Module.Finite k B] [Module.Projective k B]
    (hLG : IsLGRing k) (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (e : C.norm.IsometryEquiv D.norm) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) :
    ∃ e' : C.norm.IsometryEquiv D.norm,
      e' (1 : A) = 1 ∧ ∀ x y, e' (x * y) = e' x * e' y := by
  have hB : Module.rankAtStalk (R := k) B = fun _ ↦ r :=
    (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv).symm.trans hA
  rcases hC.rankAtStalk_eq_one_or_two_or_four_or_eight hA with h1 | h2 | h4 | h8
  · subst r
    exact exists_isometryEquiv_map_one_map_mul_of_rankAtStalk_eq_one C D hA hB
  · subst r
    exact hC.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk hLG C D hD e hA (by omega)
  · subst r
    exact hC.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk hLG C D hD e hA (by omega)
  · subst r
    exact hC.exists_isometryEquiv_map_one_map_mul_of_rankAtStalk hLG C D hD e hA (by omega)

/-- **`GPR 23.5`, without a constant-rank hypothesis.** Over a nontrivial LG ring, composition
algebras with isometric norm forms are isomorphic as unital non-associative algebras.

The rank idempotents decompose both modules into the same constant-rank factors: a norm isometry
is in particular a linear equivalence, so the two rank functions agree. The constant-rank norm
equivalence theorem is applied on every idempotent factor, and the resulting isomorphisms are
glued through the module decomposition of `GPR Exc. 9.31`. -/
theorem IsComposition.exists_isometryEquiv_map_one_map_mul
    [Module.Finite k B] [Module.Projective k B]
    (hLG : IsLGRing k) (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hC : C.IsComposition.{u, v, u}) (hD : D.IsComposition.{u, w, u})
    (e : C.norm.IsometryEquiv D.norm) :
    ∃ e' : C.norm.IsometryEquiv D.norm,
      e' (1 : A) = 1 ∧ ∀ x y, e' (x * y) = e' x * e' y := by
  classical
  let I := Module.rankFinset k A
  let ε : I → k := fun i ↦ Module.rankIdempotent k A i
  let hε : CompleteOrthogonalIdempotents ε :=
    Module.completeOrthogonalIdempotents_rankIdempotent_rankFinset k A
  have hrankB : Module.rankAtStalk (R := k) B = Module.rankAtStalk (R := k) A :=
    (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv).symm
  have hrankA (i : I) :
      Module.rankAtStalk (R := (k ⧸ Ideal.span {1 - ε i}))
        (TensorProduct k (k ⧸ Ideal.span {1 - ε i}) A) = fun _ ↦ (i : ℕ) :=
    Module.rankAtStalk_quotientTensor_rankIdempotent k A i
  have hrankB' (i : I) :
      Module.rankAtStalk (R := (k ⧸ Ideal.span {1 - ε i}))
        (TensorProduct k (k ⧸ Ideal.span {1 - ε i}) B) = fun _ ↦ (i : ℕ) := by
    funext p
    rw [Module.rankAtStalk_baseChange, hrankB, ← Module.rankAtStalk_baseChange]
    exact congrFun (hrankA i) p
  have hlocal (i : I) :
      ∃ f : (C.baseChangeOfProjective (k ⧸ Ideal.span {1 - ε i})).norm.IsometryEquiv
          (D.baseChangeOfProjective (k ⧸ Ideal.span {1 - ε i})).norm,
        f (1 : TensorProduct k (k ⧸ Ideal.span {1 - ε i}) A) = 1 ∧
          ∀ x y, f (x * y) = f x * f y := by
    let S := k ⧸ Ideal.span {1 - ε i}
    rcases subsingleton_or_nontrivial S with hS | hS
    · let := hS
      let : Subsingleton (TensorProduct k S A) := Module.subsingleton S _
      let : Subsingleton (TensorProduct k S B) := Module.subsingleton S _
      exact ⟨⟨LinearEquiv.ofSubsingleton _ _, fun _ ↦ Subsingleton.elim _ _⟩,
        Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
    · let := hS
      have hLGi : IsLGRing S :=
        hLG.quotient_span_one_sub_of_isIdempotentElem
          (Module.isIdempotentElem_rankIdempotent k A i)
      have hei := QuadraticMap.IsometryEquiv.baseChangeOfProjective (A := S) C.norm D.norm e
      exact (hC.baseChangeOfProjective S).exists_isometryEquiv_map_one_map_mul_of_rankAtStalk_eq
          hLGi
          (C.baseChangeOfProjective S) (D.baseChangeOfProjective S)
          (hD.baseChangeOfProjective S) hei (hrankA i)
  choose f hf1 hfmul using hlocal
  let EA := hε.linearEquivPiQuotientTensor A ε
  let EB := hε.linearEquivPiQuotientTensor B ε
  let fp : (∀ i, TensorProduct k (k ⧸ Ideal.span {1 - ε i}) A) ≃ₗ[k]
      ∀ i, TensorProduct k (k ⧸ Ideal.span {1 - ε i}) B :=
    LinearEquiv.piCongrRight fun i ↦ f i |>.toLinearEquiv.restrictScalars k
  let g : A ≃ₗ[k] B := EA.trans (fp.trans EB.symm)
  have hcomponent (x : A) (i : I) : EB (g x) i = f i (EA x i) := by
    simp [g, fp]
  have hg1 : g (1 : A) = 1 :=
    EB.injective <| funext fun i ↦ by
      rw [hcomponent]
      exact hf1 i
  have hgmul : ∀ x y, g (x * y) = g x * g y := by
    intro x y
    apply EB.injective
    funext i
    rw [hcomponent]
    change f i (1 ⊗ₜ[k] (x * y)) = 1 ⊗ₜ[k] (g x * g y)
    rw [one_tmul_mul, hfmul, one_tmul_mul]
    have hx := hcomponent x i
    have hy := hcomponent y i
    simp only [EA, EB,
      CompleteOrthogonalIdempotents.linearEquivPiQuotientTensor_apply] at hx hy
    exact congrArg₂ (· * ·) hx.symm hy.symm
  refine ⟨{ toLinearEquiv := g, map_app' := fun x ↦ ?_ }, hg1, hgmul⟩
  apply hε.bijective_pi.1
  funext i
  have hi := (f i).map_app (EA x i)
  rw [← hcomponent] at hi
  simpa [EA, EB, QuadraticForm.baseChangeOfProjective_tmul, Algebra.smul_def] using hi

/-- **The Witt-cancellation step in `GPR 23.5`.** Let a unital norm isometry carry `u` to `e u`, and
suppose `k[u]` is a regular rank-two composition subalgebra. Then the orthogonal complements of
`k[u]` and `k[e u]` are isometric over an LG ring.

The ambient forms split as the regular quadratic summand plus its orthogonal complement. The
quadratic summands are isometric by `adjoinElementLinearEquivOfMapOne`; cancelling that common
regular summand with `GN 6.5` gives the result. -/
theorem exists_isometryEquiv_polarOrthogonal_adjoinElement [Module.Finite k B]
    [Module.Projective k B] (hLG : IsLGRing k) (C : ConicAlgebra k A) (D : ConicAlgebra k B)
    (hD : D.IsComposition.{u, w, u}) (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : A) = 1) {u : A} (hu : C.IsRegularRankTwoComposition u) :
    Nonempty
      ((C.norm.comp
          (C.norm.polarOrthogonal
            (C.adjoinElement u).toNonUnitalSubalgebra.toSubmodule).subtype).IsometryEquiv
        (D.norm.comp
          (D.norm.polarOrthogonal
            (D.adjoinElement (e u)).toNonUnitalSubalgebra.toSubmodule).subtype)) := by
  let NC := (C.adjoinElement u).toNonUnitalSubalgebra.toSubmodule
  let ND := (D.adjoinElement (e u)).toNonUnitalSubalgebra.toSubmodule
  have hdisc : IsUnit (C.elementDiscriminant u) :=
    (C.isRegularRankTwoComposition_iff_isUnit_discriminant u).mp hu
  have hdiscD : IsUnit (D.elementDiscriminant (e u)) :=
    elementDiscriminant_map_of_isometryEquiv_map_one C D e h1 u ▸ hdisc
  have hregC : QuadraticForm.IsGPRRegular (C.norm.comp NC.subtype) :=
    C.normAdjoinElement_isGPRRegular hdisc
  have hregD : QuadraticForm.IsGPRRegular (D.norm.comp ND.subtype) :=
    D.normAdjoinElement_isGPRRegular hdiscD
  exact exists_isometryEquiv_polarOrthogonal hLG C D hD (C.adjoinElement u)
    (D.adjoinElement (e u)) hregC hregD (adjoinElementIsometryEquivOfMapOne C D e h1 u) e

/-- **Matching the first doubling parameter in Layer 9.** Under the hypotheses of the complement
cancellation step, every vector in the complement of `k[u]` has a corresponding vector in the
complement of `k[e u]` with exactly the same norm. In particular, unit-norm doubling vectors give
the same Cayley–Dickson scalar on both sides. -/
theorem exists_polarOrthogonal_adjoinElement_eq_norm [Module.Finite k B]
    [Module.Projective k B] (hLG : IsLGRing k) (C : ConicAlgebra k A)
    (D : ConicAlgebra k B) (hD : D.IsComposition.{u, w, u})
    (e : C.norm.IsometryEquiv D.norm) (h1 : e (1 : A) = 1) {u : A}
    (hu : C.IsRegularRankTwoComposition u)
    (v : C.norm.polarOrthogonal
      (C.adjoinElement u).toNonUnitalSubalgebra.toSubmodule) :
    ∃ v' : D.norm.polarOrthogonal
        (D.adjoinElement (e u)).toNonUnitalSubalgebra.toSubmodule,
      D.norm (v' : B) = C.norm (v : A) := by
  obtain ⟨g⟩ := exists_isometryEquiv_polarOrthogonal_adjoinElement hLG C D hD e h1 hu
  exact ⟨g v, g.map_app v⟩

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
/-- **`GPR 23.3`, unital normalization of a norm isometry.** If `D` is alternative and
multiplicative, every isometry `n_C ≅ n_D` can be postcomposed with a self-isometry of `n_D` so
that it sends `1` to `1`. This is the first step of the norm equivalence theorem `GPR 23.5`. -/
theorem IsMultiplicative.exists_isometryEquiv_map_one [IsAlternative B]
    (h : D.IsMultiplicative) (C : ConicAlgebra k A) (e : C.norm.IsometryEquiv D.norm) :
    ∃ e' : C.norm.IsometryEquiv D.norm, e' (1 : A) = 1 := by
  have hx : D.norm (e (1 : A)) = 1 := by rw [e.map_app, C.norm_one]
  refine ⟨e.trans (h.leftMulConjIsometryEquiv (e 1) hx), ?_⟩
  exact h.leftMulConjIsometryEquiv_apply_self (e 1) hx

end Normalize

end ConicAlgebra

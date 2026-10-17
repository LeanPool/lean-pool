/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.BaseChange
public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative

/-!
# Base change preserves multiplicativity (`GPR 19.7`)

If the norm of a conic algebra `A` over `k` permits composition, then so does the norm of
`S ⊗[k] A` for every commutative `k`-algebra `S`. Together with the base-change stability of
non-singularity, which is built into `QuadraticForm.IsGPRNonsingular` by definition, this is what
makes `ConicAlgebra.IsComposition` stable under base change, and it is the step that lets a
statement about composition algebras over a ring be tested on the residue fields.

## Main results

* `ConicAlgebra.IsMultiplicative.baseChangeOfProjective` : `n(XY) = n(X) n(Y)` on `S ⊗[k] A`.

## Implementation notes

Multiplicativity is *quadratic*, so it does not reduce to pure tensors on its own: the additivity
step in an induction over `S ⊗[k] A` produces a cross term `n(X₁Y, X₂Y)`, which is not part of the
statement being proved. The proof therefore runs the three levels of linearization from
`Conic/Multiplicative.lean` in the reverse of the usual order, each one supplying the additivity
step of the next:

* `polar_mul_add_polar_mul_baseChangeOfProjective` (`n(XZ, YW) + n(XW, YZ) = n(X, Y) n(Z, W)`) is
  additive in each of its four arguments separately, so it *does* reduce to pure tensors, by four
  nested inductions;
* `polar_mul_mul_right_baseChangeOfProjective` and `polar_mul_mul_left_baseChangeOfProjective`
  (`n(XZ, YZ) = n(X, Y) n(Z)` and `n(XY, XZ) = n(X) n(Y, Z)`) are additive in two of their three
  arguments and quadratic in the third; the cross term of the quadratic one is the second
  linearization above;
* multiplicativity itself is quadratic in both arguments, and its two cross terms are the two
  first linearizations.

The two first linearizations are genuinely two statements: `A` is not assumed associative or
commutative, so neither follows from the other (`Conic/Multiplicative.lean` makes the same point
about `A` itself). Nothing here needs alternativity, regularity, or a hypothesis on `2`; the
finite projectivity is inherited from `ConicAlgebra.baseChangeOfProjective`, which needs it to base
change the norm at all.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.1, 19.7.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

open QuadraticMap (polar)

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
variable (S : Type w) [CommRing S] [Algebra k S] {C : ConicAlgebra k A}

namespace IsMultiplicative

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- Expanding the base-changed norm of a sum. This is `QuadraticMap.polar` read backwards, and is
the reason every induction below has a cross term. -/
private theorem norm_baseChangeOfProjective_add (x y : S ⊗[k] A) :
    (C.norm.baseChangeOfProjective S) (x + y) =
      (C.norm.baseChangeOfProjective S) x + (C.norm.baseChangeOfProjective S) y +
        polar (C.norm.baseChangeOfProjective S) x y := by
  simp only [QuadraticMap.polar]
  ring

/-- **The second linearization of multiplicativity, after base change**:
`n(XZ, YW) + n(XW, YZ) = n(X, Y) n(Z, W)` on `S ⊗[k] A`.

Both sides are additive in each of the four arguments separately, so four nested inductions reduce
this to pure tensors, where it is `ConicAlgebra.IsMultiplicative.polar_mul_add_polar_mul` in `A`
together with commutativity of `S`. -/
theorem polar_mul_add_polar_mul_baseChangeOfProjective (h : C.IsMultiplicative)
    (x y z w : S ⊗[k] A) :
    polar (C.norm.baseChangeOfProjective S) (x * z) (y * w) +
        polar (C.norm.baseChangeOfProjective S) (x * w) (y * z) =
      polar (C.norm.baseChangeOfProjective S) x y *
        polar (C.norm.baseChangeOfProjective S) z w := by
  induction x with
  | add x₁ x₂ h₁ h₂ =>
    simp only [add_mul, QuadraticMap.polar_add_left]
    linear_combination h₁ + h₂
  | tmul s a =>
    induction y with
    | add y₁ y₂ h₁ h₂ =>
      simp only [add_mul, QuadraticMap.polar_add_right]
      linear_combination h₁ + h₂
    | tmul s' a' =>
      induction z with
      | add z₁ z₂ h₁ h₂ =>
        simp only [mul_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
        linear_combination h₁ + h₂
      | tmul u c =>
        induction w with
        | add w₁ w₂ h₁ h₂ =>
          simp only [mul_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
          linear_combination h₁ + h₂
        | tmul u' c' =>
          have hS₁ : (s * u) * (s' * u') = (s * s') * (u * u') := by ring
          have hS₂ : (s * u') * (s' * u) = (s * s') * (u * u') := by ring
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            baseChangeOfProjective_polar_tmul, baseChangeOfProjective_polar_tmul,
            baseChangeOfProjective_polar_tmul, baseChangeOfProjective_polar_tmul,
            hS₁, hS₂, smul_mul_smul_comm, ← add_smul, h.polar_mul_add_polar_mul]

/-- **The first linearization of multiplicativity, after base change**, in the left variable:
`n(XZ, YZ) = n(X, Y) n(Z)` on `S ⊗[k] A`.

Additive in `X` and in `Y`, quadratic in `Z`; the cross term of the induction on `Z` is
`ConicAlgebra.IsMultiplicative.polar_mul_add_polar_mul_baseChangeOfProjective`. -/
theorem polar_mul_mul_right_baseChangeOfProjective (h : C.IsMultiplicative) (x y z : S ⊗[k] A) :
    polar (C.norm.baseChangeOfProjective S) (x * z) (y * z) =
      polar (C.norm.baseChangeOfProjective S) x y * (C.norm.baseChangeOfProjective S) z := by
  induction x with
  | add x₁ x₂ h₁ h₂ =>
    simp only [add_mul, QuadraticMap.polar_add_left]
    linear_combination h₁ + h₂
  | tmul s a =>
    induction y with
    | add y₁ y₂ h₁ h₂ =>
      simp only [add_mul, QuadraticMap.polar_add_right]
      linear_combination h₁ + h₂
    | tmul s' a' =>
      induction z with
      | add z₁ z₂ h₁ h₂ =>
        have key :=
          h.polar_mul_add_polar_mul_baseChangeOfProjective S (s ⊗ₜ[k] a) (s' ⊗ₜ[k] a')
            z₁ z₂
        simp only [mul_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          norm_baseChangeOfProjective_add]
        linear_combination h₁ + h₂ + key
      | tmul u c =>
        have hS : (s * u) * (s' * u) = (s * s') * (u * u) := by ring
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          baseChangeOfProjective_polar_tmul, baseChangeOfProjective_polar_tmul,
          baseChangeOfProjective_norm_tmul, hS, smul_mul_smul_comm, h.polar_mul_mul_right]

/-- **The first linearization of multiplicativity, after base change**, in the right variable:
`n(XY, XZ) = n(X) n(Y, Z)` on `S ⊗[k] A`.

Not a consequence of `polar_mul_mul_right_baseChangeOfProjective`, since `A` is not assumed
commutative, but proved the same way, with the roles of the additive and the quadratic arguments
exchanged. -/
theorem polar_mul_mul_left_baseChangeOfProjective (h : C.IsMultiplicative) (x y z : S ⊗[k] A) :
    polar (C.norm.baseChangeOfProjective S) (x * y) (x * z) =
      (C.norm.baseChangeOfProjective S) x * polar (C.norm.baseChangeOfProjective S) y z := by
  induction y with
  | add y₁ y₂ h₁ h₂ =>
    simp only [mul_add, QuadraticMap.polar_add_left]
    linear_combination h₁ + h₂
  | tmul t b =>
    induction z with
    | add z₁ z₂ h₁ h₂ =>
      simp only [mul_add, QuadraticMap.polar_add_right]
      linear_combination h₁ + h₂
    | tmul u c =>
      induction x with
      | add x₁ x₂ h₁ h₂ =>
        have key := h.polar_mul_add_polar_mul_baseChangeOfProjective S x₁ x₂ (t ⊗ₜ[k] b)
          (u ⊗ₜ[k] c)
        rw [QuadraticMap.polar_comm (C.norm.baseChangeOfProjective S) (x₁ * (u ⊗ₜ[k] c))
          (x₂ * (t ⊗ₜ[k] b))] at key
        simp only [add_mul, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          norm_baseChangeOfProjective_add]
        linear_combination h₁ + h₂ + key
      | tmul s a =>
        have hS : (s * t) * (s * u) = (s * s) * (t * u) := by ring
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          baseChangeOfProjective_polar_tmul, baseChangeOfProjective_polar_tmul,
          baseChangeOfProjective_norm_tmul, hS, smul_mul_smul_comm, h.polar_mul_mul_left]

/-- **Multiplicativity is stable under base change.** If the norm of `A` permits composition, so
does the norm of `S ⊗[k] A` for every commutative `k`-algebra `S`.

The induction on the left argument has cross term
`polar_mul_mul_right_baseChangeOfProjective`, the one on the right argument
`polar_mul_mul_left_baseChangeOfProjective`, and on pure tensors the identity is
`n(ab) = n(a) n(b)` in `A` times `(st)² = s²t²` in `S`. -/
theorem baseChangeOfProjective (h : C.IsMultiplicative) :
    (C.baseChangeOfProjective S).IsMultiplicative := by
  intro x y
  simp only [baseChangeOfProjective_norm]
  induction x with
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, norm_baseChangeOfProjective_add, norm_baseChangeOfProjective_add, h₁, h₂,
      h.polar_mul_mul_right_baseChangeOfProjective S]
    ring
  | tmul s a =>
    induction y with
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, norm_baseChangeOfProjective_add, norm_baseChangeOfProjective_add, h₁, h₂,
        h.polar_mul_mul_left_baseChangeOfProjective S]
      ring
    | tmul t b =>
      have hS : (s * t) * (s * t) = (s * s) * (t * t) := by ring
      rw [Algebra.TensorProduct.tmul_mul_tmul, baseChangeOfProjective_norm_tmul,
        baseChangeOfProjective_norm_tmul, baseChangeOfProjective_norm_tmul, hS,
        smul_mul_smul_comm, h.norm_mul]

end IsMultiplicative

end ConicAlgebra

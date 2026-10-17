/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Examples
public import Mathlib.Analysis.Quaternion

/-!
# The first two rungs are mathlib's `ℂ` and `ℍ`

The Cayley–Dickson tower over `ℝ` at `μᵢ = -1` produces algebras of dimension `2` and `4` which
*are* the complex numbers and the quaternions. mathlib has both, so the identification is a
theorem, not a definition: this file builds the two `AlgEquiv`s and checks that they carry the
conic norm to `Complex.normSq` and `Quaternion.normSq` and the conic conjugation to `star`.

Nothing else in the project depends on this file. It exists so that the tower is anchored to
mathlib's objects rather than merely resembling them, and so that a reader who knows
`Complex.normSq` can recognize `ConicAlgebra.norm`.

## The dictionary

`Cay₂ ℝ (-1)` is `ℝ × ℝ` with `(a, b)(c, d) = (ac - db, da + bc)` — the conjugation of the base
ring being the identity — which is multiplication of `a + bi`. So `(a, b) ↦ ⟨a, b⟩`.

`Cay₄ ℝ (-1) (-1)` is `ℂ × ℂ` with `(u₁, v₁)(u₂, v₂) = (u₁u₂ - (conj v₂)v₁, v₂u₁ + v₁(conj u₂))`,
which is multiplication of `u + vj`. Writing `u = a + bi` and `v = c + di` gives `a + bi + cj + dk`
with `k = ij`, so `((a, b), (c, d)) ↦ ⟨a, b, c, d⟩`. mathlib's `Quaternion ℝ` is
`QuaternionAlgebra ℝ (-1) 0 (-1)`, whose structure constants are exactly `i² = j² = -1`.

⚠ These are equivalences at `μ₁ = μ₂ = -1` over `ℝ` specifically. `Cay₄ k μ₁ μ₂` and
`QuaternionAlgebra k a b c` are **not** comparable in general — see overview trap 3:
`QuaternionAlgebra` takes arbitrary structure constants and always produces a free module, while
`Cay₄ k μ₁ μ₂` is a composition algebra when `2` and the `μᵢ` are units
(`ConicAlgebra.isComposition_cay₄`, which needs `Invertible (2 : k)`: in characteristic `2` the
polar form of the norm of `Cay₄ k μ₁ μ₂` is identically zero, so it is never a composition
algebra).

## Main results

* `ConicAlgebra.realComplexAlgEquiv` : `Cay₂ ℝ (-1) ≃ₐ[ℝ] ℂ`.
* `ConicAlgebra.realQuaternionAlgEquiv` : `Cay₄ ℝ (-1) (-1) ≃ₐ[ℝ] ℍ[ℝ]`.
* `ConicAlgebra.norm_realComplexAlgEquiv`, `ConicAlgebra.norm_realQuaternionAlgEquiv` : the
  equivalences are isometries for `Complex.normSq` and `Quaternion.normSq`.
* `ConicAlgebra.conj_realComplexAlgEquiv`, `ConicAlgebra.conj_realQuaternionAlgEquiv` : they carry
  `ConicAlgebra.conj` to `star`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.4, 19.18.
-/

@[expose] public section

namespace ConicAlgebra

open Quaternion

/-! ### `Cay₂ ℝ (-1) = ℂ` -/

/-- **The rank-two rung is `ℂ`.** `(a, b) ↦ a + bi`. -/
def realComplexAlgEquiv : RealComplex ≃ₐ[ℝ] ℂ where
  toFun x := ⟨x.1, x.2⟩
  invFun z := ((z.re, z.im) : ℝ × ℝ)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    refine Complex.ext ?_ ?_
    · change x.1 * y.1 + (-1 : ℝ) • ((baseRing ℝ).conj y.2 * x.2) = _
      rw [Complex.mul_re, baseRing_conj_apply]
      ring
    · change y.2 * x.1 + x.2 * (baseRing ℝ).conj y.1 = _
      rw [Complex.mul_im, baseRing_conj_apply]
      ring
  commutes' r := by
    refine Complex.ext ?_ ?_ <;>
      simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem realComplexAlgEquiv_apply (x : RealComplex) :
    realComplexAlgEquiv x = ⟨x.1, x.2⟩ := rfl

/-- The equivalence is an **isometry**: the conic norm of `Cay₂ ℝ (-1)` is `Complex.normSq`. -/
theorem norm_realComplexAlgEquiv (x : RealComplex) :
    (cay₂ ℝ (-1)).norm x = Complex.normSq (realComplexAlgEquiv x) := by
  rw [cay_norm_apply, Complex.normSq_apply]
  change (QuadraticMap.sq (R := ℝ)) x.1 - (-1 : ℝ) * (QuadraticMap.sq (R := ℝ)) x.2 = _
  simp only [QuadraticMap.sq_apply, realComplexAlgEquiv_apply]
  ring

/-- The equivalence carries the conic conjugation to complex conjugation. -/
theorem conj_realComplexAlgEquiv (x : RealComplex) :
    realComplexAlgEquiv ((cay₂ ℝ (-1)).conj x) = star (realComplexAlgEquiv x) := by
  refine Complex.ext ?_ ?_ <;>
    rw [realComplexAlgEquiv_apply, cay_conj_apply] <;>
    simp [baseRing_conj_apply]

/-! ### `Cay₄ ℝ (-1) (-1) = ℍ`

⚠ Two elaboration hazards meet here, and the proofs are shaped around both.

The first is the one documented in `Conic/CayleyDicksonAlternative.lean`:
`ConicAlgebra.cay_conj_apply` produces a pair *literal*, whose inferred type is `ℝ × ℝ` rather
than `Cay₂ ℝ μ`, and once such a literal sits inside a product the `Cay` simp lemmas no longer
unify. So the conjugation is only ever rewritten through its **components**, and
`cay_conj_apply` is removed from the default simp set with `-cay_conj_apply`.

The second is that `ℍ[ℝ]` is a `def` wrapping `QuaternionAlgebra ℝ (-1) 0 (-1)`. A goal mixing
that spelling with `RealQuaternion` is not type-correct at `rw`'s transparency, so all quaternion
arithmetic is done in `ConicAlgebra.quaternion_mk_mul` and `ConicAlgebra.quaternion_star_mk`,
whose statements mention no `Cay`, and then used as fully instantiated rewrites. -/

private theorem cay₂_conj_fst (μ : ℝ) (x : Cay₂ ℝ μ) :
    ((cay₂ ℝ μ).conj x).1 = x.1 := by
  rw [cay_conj_apply, baseRing_conj_apply]

private theorem cay₂_conj_snd (μ : ℝ) (x : Cay₂ ℝ μ) :
    ((cay₂ ℝ μ).conj x).2 = -x.2 := by
  rw [cay_conj_apply]

private theorem cay₄_conj_fst (x : RealQuaternion) :
    ((cay₄ ℝ (-1) (-1)).conj x).1 = (cay₂ ℝ (-1)).conj x.1 := by
  rw [cay_conj_apply]

private theorem cay₄_conj_snd (x : RealQuaternion) :
    ((cay₄ ℝ (-1) (-1)).conj x).2 = -x.2 := by
  rw [cay_conj_apply]

private theorem quaternion_mk_mul (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    (⟨a₁, b₁, c₁, d₁⟩ : ℍ[ℝ]) * ⟨a₂, b₂, c₂, d₂⟩ =
      ⟨a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂,
        a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂,
        a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂,
        a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂⟩ := by
  rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

private theorem quaternion_star_mk (a b c d : ℝ) :
    star (⟨a, b, c, d⟩ : ℍ[ℝ]) = ⟨a, -b, -c, -d⟩ := by
  rw [QuaternionAlgebra.star_mk, QuaternionAlgebra.mk.injEq]
  exact ⟨by ring, rfl, rfl, rfl⟩

/-- The underlying map `((a, b), (c, d)) ↦ a + bi + cj + dk`. -/
def toQuaternion (x : RealQuaternion) : ℍ[ℝ] := ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩

theorem toQuaternion_apply (x : RealQuaternion) :
    toQuaternion x = ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩ := rfl

theorem toQuaternion_mul (x y : RealQuaternion) :
    toQuaternion (x * y) = toQuaternion x * toQuaternion y := by
  change (⟨(x * y).1.1, (x * y).1.2, (x * y).2.1, (x * y).2.2⟩ : ℍ[ℝ, -1, 0, -1]) =
    (⟨x.1.1, x.1.2, x.2.1, x.2.2⟩ : ℍ[ℝ, -1, 0, -1]) * ⟨y.1.1, y.1.2, y.2.1, y.2.2⟩
  rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [-cay_conj_apply, Cay.fst_mul, Cay.snd_mul, cay₂_conj_fst, cay₂_conj_snd] <;>
    ring

/-- **The rank-four rung is `ℍ`.** `((a, b), (c, d)) ↦ a + bi + cj + dk`. -/
def realQuaternionAlgEquiv : RealQuaternion ≃ₐ[ℝ] ℍ[ℝ] where
  toFun := toQuaternion
  invFun q := (((q.re, q.imI) : ℝ × ℝ), ((q.imJ, q.imK) : ℝ × ℝ))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' := toQuaternion_mul
  commutes' r := by
    change (⟨(algebraMap ℝ RealQuaternion r).1.1, (algebraMap ℝ RealQuaternion r).1.2,
      (algebraMap ℝ RealQuaternion r).2.1, (algebraMap ℝ RealQuaternion r).2.2⟩ :
        ℍ[ℝ, -1, 0, -1]) = algebraMap ℝ ℍ[ℝ, -1, 0, -1] r
    rw [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem realQuaternionAlgEquiv_apply (x : RealQuaternion) :
    realQuaternionAlgEquiv x = ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩ := rfl

/-- The equivalence is an **isometry**: the conic norm of `Cay₄ ℝ (-1) (-1)` is
`Quaternion.normSq`. -/
theorem norm_realQuaternionAlgEquiv (x : RealQuaternion) :
    (cay₄ ℝ (-1) (-1)).norm x = Quaternion.normSq (realQuaternionAlgEquiv x) := by
  rw [cay_norm_apply, Quaternion.normSq_def']
  change (cay₂ ℝ (-1)).norm x.1 - (-1 : ℝ) * (cay₂ ℝ (-1)).norm x.2 = _
  rw [cay_norm_apply, cay_norm_apply]
  change (QuadraticMap.sq (R := ℝ)) x.1.1 - (-1 : ℝ) * (QuadraticMap.sq (R := ℝ)) x.1.2 -
    (-1 : ℝ) *
        ((QuadraticMap.sq (R := ℝ)) x.2.1 -
          (-1 : ℝ) * (QuadraticMap.sq (R := ℝ)) x.2.2) = _
  simp only [QuadraticMap.sq_apply, realQuaternionAlgEquiv_apply]
  ring

/-- The equivalence carries the conic conjugation to quaternionic conjugation. -/
theorem conj_realQuaternionAlgEquiv (x : RealQuaternion) :
    realQuaternionAlgEquiv ((cay₄ ℝ (-1) (-1)).conj x) = star (realQuaternionAlgEquiv x) := by
  change (⟨((cay₄ ℝ (-1) (-1)).conj x).1.1, ((cay₄ ℝ (-1) (-1)).conj x).1.2,
    ((cay₄ ℝ (-1) (-1)).conj x).2.1, ((cay₄ ℝ (-1) (-1)).conj x).2.2⟩ : ℍ[ℝ, -1, 0, -1]) =
      star (⟨x.1.1, x.1.2, x.2.1, x.2.2⟩ : ℍ[ℝ, -1, 0, -1])
  rw [QuaternionAlgebra.star_mk, QuaternionAlgebra.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [-cay_conj_apply, cay₄_conj_fst, cay₄_conj_snd, cay₂_conj_fst, cay₂_conj_snd]

end ConicAlgebra

/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Defs
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Defs
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Hyperbolic
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Zorn vector matrices (`GPR 21.18`)

The **algebra of Zorn vector matrices** `Zor(k)` is the `k`-module of formal matrices

  `[ρ₁  u₂]`
  `[u₁  ρ₂]`,   `ρᵢ ∈ k`, `uᵢ ∈ k³`,

with the multiplication built from the dot and cross products of `k³` (`GPR (21.18.4)`)

  `[ρ₁ u₂] [σ₁ v₂]   [ ρ₁σ₁ - u₂ᵀv₁       ρ₁v₂ + σ₂u₂ + u₁ ⨯ v₁ ]`
  `[u₁ ρ₂] [v₁ σ₂] = [ σ₁u₁ + ρ₂v₁ + u₂ ⨯ v₂    ρ₂σ₂ - u₁ᵀv₂     ]`,

the norm `n = ρ₁ρ₂ + u₁ᵀu₂`, the trace `t = ρ₁ + ρ₂` and the conjugation exchanging the diagonal
and negating the off-diagonal entries.

**This is the split octonion algebra, and it exists over every commutative ring.** That is the
point of the file: the Cayley–Dickson tower of `Composition/Octonion.lean` produces composition
algebras only when `2` is invertible — in characteristic `2` its very first rung `Cay(k, μ)` has
identically zero polar form, so its norm becomes degenerate over some extension field and is never
non-singular in the sense of `GPR 19.5` (`GPR 19.4`) — whereas `Zor(k)` is a composition
algebra of rank `8` over an arbitrary base, in every characteristic, with no unit scalars to
choose. It is therefore the first octonion algebra in this development available over, say, `𝔽₂`,
and it is the object the classification of *reduced* composition algebras (`GPR 22.15`) is stated
in terms of.

## Coordinates

`Zor k` is a type synonym for `(k × k³) × (k × k³)`, with `x.1 = (ρ₁, u₁)` the first column of the
matrix above and `x.2 = (ρ₂, u₂)` the second. The grouping is chosen so that the norm is literally
the pairing of `x.1` against `x.2`, which is what makes it visibly hyperbolic — the norm form of
`Zor(k)` is four hyperbolic planes, and that is the whole content of its non-singularity.

## Main definitions

* `ConicAlgebra.Zor k` : the underlying `k`-module of the algebra of Zorn vector matrices, with
  its multiplication.
* `ConicAlgebra.zorNorm k` : the norm `ρ₁ρ₂ + u₁ᵀu₂` (`GPR (21.18.6)`).
* `ConicAlgebra.zor k` : the conic structure (`GPR 21.18`).

## Main results

* `ConicAlgebra.isMultiplicative_zor` : the norm permits composition, `n(xy) = n(x) n(y)`.
* `ConicAlgebra.isGPRNonsingular_zorNorm` : the norm is non-singular, because it is hyperbolic.
* `ConicAlgebra.isComposition_zor` : **`Zor(k)` is a composition algebra over every commutative
  ring**, with no hypothesis on `2`.
* `ConicAlgebra.finrank_zor` : it has rank `8`, so it is an octonion algebra.
* `ConicAlgebra.instIsAlternativeZor` : it is alternative.
* `ConicAlgebra.trace_zor_apply`, `ConicAlgebra.conj_zor_apply` : `GPR (21.18.7)`, `(21.18.8)`.

## Implementation notes

The multiplication is *not* obtained from `GPR`'s ternary hermitian construction
`Ter(D; D³, h, Δ)`, of which `GPR 21.18` computes it to be a special case; it is taken as the
definition, and the identities `GPR 21.18` derives are proved here directly. Everything reduces to
polynomial identities in the sixteen coordinates of a pair of vector matrices, and the only two
facts about `k³` that are used are `u ⬝ᵥ (u ⨯₃ v) = 0` and the Binet–Cauchy identity
`(a ⨯₃ b) ⬝ᵥ (c ⨯₃ d) = (a ⬝ᵥ c) (b ⬝ᵥ d) - (a ⬝ᵥ d) (b ⬝ᵥ c)` — both of which `ring` supplies
after `Fin 3` is expanded.

⚠ **No hypothesis on `2` anywhere in this file**, and none is available: the whole reason for
constructing `Zor(k)` by hand rather than as `Cay(Cay(Cay(k, 1), 1), 1)` is that the
Cayley–Dickson double `Cay(k, 1)` is *not* the split quadratic étale algebra `k × k` when `2 = 0`
— it is `k[ε]`, whose norm has a radical. Splitting the hyperbolic plane `⟨1⟩ ⊥ ⟨-1⟩` off as
`xy` needs `2` invertible, and `Zor(k)` is precisely the object that does not.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 21.18, 21.19,
  22.15.
-/

@[expose] public section

universe u w

open Matrix

namespace ConicAlgebra

variable (k : Type u) [CommRing k]

/-- The `k`-module underlying the algebra of **Zorn vector matrices** `Zor(k)` (`GPR (21.18.5)`),
as a type synonym for `(k × k³) × (k × k³)`: the element `x` is the matrix

  `[x.1.1  x.2.2]`
  `[x.1.2  x.2.1]`

whose first column is `x.1 = (ρ₁, u₁)` and whose second column is `x.2 = (ρ₂, u₂)`. The synonym is
needed because the multiplication below is not the componentwise one. -/
def Zor : Type u := (k × (Fin 3 → k)) × (k × (Fin 3 → k))

namespace Zor

instance : AddCommGroup (Zor k) :=
  inferInstanceAs (AddCommGroup ((k × (Fin 3 → k)) × (k × (Fin 3 → k))))

instance : Module k (Zor k) :=
  inferInstanceAs (Module k ((k × (Fin 3 → k)) × (k × (Fin 3 → k))))

instance : Module.Finite k (Zor k) :=
  inferInstanceAs (Module.Finite k ((k × (Fin 3 → k)) × (k × (Fin 3 → k))))

instance : Module.Projective k (Zor k) :=
  inferInstanceAs (Module.Projective k ((k × (Fin 3 → k)) × (k × (Fin 3 → k))))

instance : Module.Free k (Zor k) :=
  inferInstanceAs (Module.Free k ((k × (Fin 3 → k)) × (k × (Fin 3 → k))))

variable {k}

omit [CommRing k] in
/-- Two Zorn vector matrices agree as soon as their four entries do. -/
theorem ext {x y : Zor k} (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2) (h₃ : x.2.1 = y.2.1)
    (h₄ : x.2.2 = y.2.2) : x = y :=
  Prod.ext (Prod.ext h₁ h₂) (Prod.ext h₃ h₄)

@[simp] theorem fst_add (x y : Zor k) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem snd_add (x y : Zor k) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem fst_zero : (0 : Zor k).1 = 0 := rfl
@[simp] theorem snd_zero : (0 : Zor k).2 = 0 := rfl
@[simp] theorem fst_neg (x : Zor k) : (-x).1 = -x.1 := rfl
@[simp] theorem snd_neg (x : Zor k) : (-x).2 = -x.2 := rfl
@[simp] theorem fst_sub (x y : Zor k) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem snd_sub (x y : Zor k) : (x - y).2 = x.2 - y.2 := rfl
@[simp] theorem fst_smul (c : k) (x : Zor k) : (c • x).1 = c • x.1 := rfl
@[simp] theorem snd_smul (c : k) (x : Zor k) : (c • x).2 = c • x.2 := rfl

variable (k)

/-- The **multiplication of Zorn vector matrices**, `GPR (21.18.4)`. -/
instance : Mul (Zor k) :=
  ⟨fun x y ↦
    (((x.1.1 * y.1.1 - x.2.2 ⬝ᵥ y.1.2, y.1.1 • x.1.2 + x.2.1 • y.1.2 + x.2.2 ⨯₃ y.2.2),
      (x.2.1 * y.2.1 - x.1.2 ⬝ᵥ y.2.2,
        x.1.1 • y.2.2 + y.2.1 • x.2.2 + x.1.2 ⨯₃ y.1.2)) :
      (k × (Fin 3 → k)) × (k × (Fin 3 → k)))⟩

/-- The identity matrix `diag(1, 1)`. -/
instance : One (Zor k) := ⟨(((1, 0), (1, 0)) : (k × (Fin 3 → k)) × (k × (Fin 3 → k)))⟩

variable {k}

@[simp] theorem mul_fst_fst (x y : Zor k) : (x * y).1.1 = x.1.1 * y.1.1 - x.2.2 ⬝ᵥ y.1.2 := rfl
@[simp] theorem mul_fst_snd (x y : Zor k) :
    (x * y).1.2 = y.1.1 • x.1.2 + x.2.1 • y.1.2 + x.2.2 ⨯₃ y.2.2 := rfl
@[simp] theorem mul_snd_fst (x y : Zor k) : (x * y).2.1 = x.2.1 * y.2.1 - x.1.2 ⬝ᵥ y.2.2 := rfl
@[simp] theorem mul_snd_snd (x y : Zor k) :
    (x * y).2.2 = x.1.1 • y.2.2 + y.2.1 • x.2.2 + x.1.2 ⨯₃ y.1.2 := rfl
@[simp] theorem one_fst_fst : (1 : Zor k).1.1 = 1 := rfl
@[simp] theorem one_fst_snd : (1 : Zor k).1.2 = 0 := rfl
@[simp] theorem one_snd_fst : (1 : Zor k).2.1 = 1 := rfl
@[simp] theorem one_snd_snd : (1 : Zor k).2.2 = 0 := rfl

variable (k)

instance : NonAssocRing (Zor k) :=
  { (inferInstance : AddCommGroup (Zor k)), (inferInstance : Mul (Zor k)),
    (inferInstance : One (Zor k)) with
    left_distrib := fun x y z ↦ Zor.ext (by simp [dotProduct_add]; ring)
      (by simp [smul_add, add_smul]; abel) (by simp [dotProduct_add]; ring)
      (by simp [smul_add, add_smul]; abel)
    right_distrib := fun x y z ↦ Zor.ext (by simp [add_dotProduct]; ring)
      (by simp [smul_add, add_smul]; abel) (by simp [add_dotProduct]; ring)
      (by simp [smul_add, add_smul]; abel)
    zero_mul := fun x ↦ Zor.ext (by simp) (by simp) (by simp) (by simp)
    mul_zero := fun x ↦ Zor.ext (by simp) (by simp) (by simp) (by simp)
    one_mul := fun x ↦ Zor.ext (by simp) (by simp) (by simp) (by simp)
    mul_one := fun x ↦ Zor.ext (by simp) (by simp) (by simp) (by simp) }

instance : SMulCommClass k (Zor k) (Zor k) :=
  ⟨fun c x y ↦ Zor.ext (by simp [dotProduct_smul]; ring) (by simp; module)
    (by simp [dotProduct_smul]; ring) (by simp; module)⟩

instance : IsScalarTower k (Zor k) (Zor k) :=
  ⟨fun c x y ↦ Zor.ext (by simp [smul_dotProduct]; ring) (by simp; module)
    (by simp [smul_dotProduct]; ring) (by simp; module)⟩

end Zor

/-- **`Zor(k)` has rank `8`**: it is an octonion algebra. -/
@[simp] theorem finrank_zor [Nontrivial k] : Module.finrank k (Zor k) = 8 := by
  change Module.finrank k ((k × (Fin 3 → k)) × (k × (Fin 3 → k))) = 8
  simp

/-! ### The norm

The norm `n(x) = ρ₁ρ₂ + u₁ᵀu₂` (`GPR (21.18.6)`) is the pairing of the two columns of the matrix
against each other, so it is built here from that pairing rather than written out as a polynomial:
this is what `QuadraticForm.isGPRNonsingular_of_basis_pairing` consumes, and it is why the norm is
hyperbolic. -/

/-- The **coordinate pairing** `⟪(ρ, u), (σ, v)⟫ = ρσ + uᵀv` on `k × k³`. -/
def zorPairing : LinearMap.BilinForm k (k × (Fin 3 → k)) :=
  LinearMap.mk₂ k (fun m n ↦ m.1 * n.1 + m.2 ⬝ᵥ n.2)
    (fun _ _ _ ↦ by simp [add_dotProduct]; ring)
    (fun _ _ _ ↦ by simp [smul_dotProduct]; ring)
    (fun _ _ _ ↦ by simp [dotProduct_add]; ring)
    (fun _ _ _ ↦ by simp [dotProduct_smul]; ring)

/-- The bilinear form pairing the first column of a Zorn vector matrix against its second. -/
def zorBilin : LinearMap.BilinForm k (Zor k) :=
  (zorPairing k).compl₁₂
    (LinearMap.fst k (k × (Fin 3 → k)) (k × (Fin 3 → k)))
    (LinearMap.snd k (k × (Fin 3 → k)) (k × (Fin 3 → k)))

/-- The **norm of a Zorn vector matrix**, `n(x) = ρ₁ρ₂ + u₁ᵀu₂` (`GPR (21.18.6)`): the
determinant-like pairing of the two columns. -/
def zorNorm : QuadraticForm k (Zor k) := (zorBilin k).toQuadraticMap

variable {k}

@[simp] theorem zorNorm_apply (x : Zor k) : zorNorm k x = x.1.1 * x.2.1 + x.1.2 ⬝ᵥ x.2.2 := rfl

theorem polar_zorNorm (x y : Zor k) :
    QuadraticMap.polar (zorNorm k) x y =
      x.1.1 * y.2.1 + y.1.1 * x.2.1 + x.1.2 ⬝ᵥ y.2.2 + y.1.2 ⬝ᵥ x.2.2 := by
  simp only [QuadraticMap.polar, zorNorm_apply, Zor.fst_add, Zor.snd_add, Prod.fst_add,
    Prod.snd_add, add_dotProduct, dotProduct_add]
  ring

@[simp] theorem polar_zorNorm_one (x : Zor k) :
    QuadraticMap.polar (zorNorm k) 1 x = x.1.1 + x.2.1 := by
  simp [polar_zorNorm, add_comm]

variable (k)

/-- **`GPR 21.18`: the Zorn vector matrices form a conic algebra**, with norm `ρ₁ρ₂ + u₁ᵀu₂` and
trace `ρ₁ + ρ₂`. Over an arbitrary commutative ring, with no hypothesis on `2`. -/
def zor : ConicAlgebra k (Zor k) where
  norm := zorNorm k
  norm_one := by simp
  mul_self x := by
    refine Zor.ext ?_ ?_ ?_ ?_
    · simp [dotProduct_comm x.2.2 x.1.2]; ring
    · simp [add_smul]
    · simp; ring
    · simp [add_smul]

variable {k}

@[simp] theorem zor_norm : (zor k).norm = zorNorm k := rfl

/-- **The trace of a Zorn vector matrix is the trace of the matrix**, `GPR (21.18.7)`. -/
@[simp] theorem trace_zor_apply (x : Zor k) : (zor k).trace x = x.1.1 + x.2.1 := by
  rw [ConicAlgebra.trace_apply, zor_norm, polar_zorNorm_one]

/-- **The conjugation exchanges the diagonal entries and negates the off-diagonal ones**,
`GPR (21.18.8)`. -/
@[simp] theorem conj_zor_apply (x : Zor k) :
    (zor k).conj x = (((x.2.1, -x.1.2), (x.1.1, -x.2.2)) :
      (k × (Fin 3 → k)) × (k × (Fin 3 → k))) := by
  refine Zor.ext ?_ ?_ ?_ ?_ <;> simp [ConicAlgebra.conj_apply]

/-! ### Multiplicativity of the norm

`n(xy) = n(x) n(y)` is a polynomial identity in the sixteen coordinates; after `Fin 3` is expanded
it is exactly the Binet–Cauchy identity plus the vanishing of `u ⬝ᵥ (u ⨯₃ v)`, and `ring` finds
both. -/

/-- **The norm of `Zor(k)` permits composition** (`GPR 19.1` for this algebra): `n(xy) = n(x) n(y)`
over any commutative ring. -/
theorem isMultiplicative_zor : (zor k).IsMultiplicative := by
  intro x y
  simp only [zor_norm, zorNorm_apply, Zor.mul_fst_fst, Zor.mul_fst_snd, Zor.mul_snd_fst,
    Zor.mul_snd_snd, dotProduct, cross_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-! ### Alternativity -/

/-- **`Zor(k)` is alternative.** Both alternative laws are polynomial identities in the sixteen
coordinates of two vector matrices; no regularity and no hypothesis on `2` is used, so this is
independent of `GPR 19.3`. -/
instance : IsAlternative (Zor k) where
  left_alt x y := by
    refine Zor.ext ?_ (funext fun i ↦ ?_) ?_ (funext fun i ↦ ?_)
    · simp [dotProduct, cross_apply, Fin.sum_univ_three]; ring
    · fin_cases i <;>
        (simp [dotProduct, cross_apply, Fin.sum_univ_three, vecHead, vecTail]; ring)
    · simp [dotProduct, cross_apply, Fin.sum_univ_three]; ring
    · fin_cases i <;>
        (simp [dotProduct, cross_apply, Fin.sum_univ_three, vecHead, vecTail]; ring)
  right_alt x y := by
    refine Zor.ext ?_ (funext fun i ↦ ?_) ?_ (funext fun i ↦ ?_)
    · simp [dotProduct, cross_apply, Fin.sum_univ_three]; ring
    · fin_cases i <;>
        (simp [dotProduct, cross_apply, Fin.sum_univ_three, vecHead, vecTail]; ring)
    · simp [dotProduct, cross_apply, Fin.sum_univ_three]; ring
    · fin_cases i <;>
        (simp [dotProduct, cross_apply, Fin.sum_univ_three, vecHead, vecTail]; ring)

/-! ### Non-singularity, and the composition algebra

The norm pairs the two columns of the matrix against each other in the coordinates of the standard
basis of `k × k³`, so it is a sum of four hyperbolic planes; that is all
`QuadraticForm.isGPRNonsingular_of_basis_pairing` needs. -/

variable (k)

/-- The standard basis of `k × k³`, indexed by `Unit ⊕ Fin 3`. -/
noncomputable def zorColumnBasis : Module.Basis (Unit ⊕ Fin 3) k (k × (Fin 3 → k)) :=
  (Module.Basis.singleton Unit k).prod (Pi.basisFun k (Fin 3))

/-- **The norm of `Zor(k)` is non-singular** — indeed hyperbolic, being the pairing of the first
column of the matrix against the second. No hypothesis on `2`. -/
theorem isGPRNonsingular_zorNorm :
    QuadraticForm.IsGPRNonsingular.{u, u, w} (zorNorm k) := by
  have h : ∀ x : Zor k, zorNorm k x =
      ∑ i, (zorColumnBasis k).repr x.1 i * (zorColumnBasis k).repr x.2 i := fun x ↦ by
    simp [zorColumnBasis, Fintype.sum_sum_type, dotProduct]
  exact QuadraticForm.isGPRNonsingular_of_basis_pairing (zorColumnBasis k) h

/-- **`Zor(k)` is a composition algebra over every commutative ring** (`GPR 21.18`, `21.19(d)`):
the split octonion algebra. Unlike `ConicAlgebra.isComposition_cay₈` this needs no hypothesis on
`2` and no choice of unit scalars. -/
theorem isComposition_zor : (zor k).IsComposition.{u, u, w} where
  isGPRNonsingular := isGPRNonsingular_zorNorm k
  isMultiplicative := isMultiplicative_zor

end ConicAlgebra

/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.TwistedMatrix
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Zorn
public import LeanPool.CompositionAlgebrasOverRings.Conic.Kirmse
public import LeanPool.CompositionAlgebrasOverRings.Module.VectorProduct

/-!
# Twisted Zorn vector matrices (`GPR 22.14`)

For `M` a `k`-module equipped with a pair of associated vector products
(`Module.VectorProductPair`), the **twisted Zorn vector matrices** are the formal matrices

  `[ρ₁  u*]`
  `[v   ρ₂]`,   `ρᵢ ∈ k`, `u* ∈ M*`, `v ∈ M`,

multiplied by `GPR (22.14.3)`

  `[ρ₁ v*] [σ₁ w*]   [ρ₁σ₁ - ⟨v*, w⟩    ρ₁w* + σ₂v* + v × w]`
  `[v  ρ₂] [w  σ₂] = [σ₁v + ρ₂w + v* × w*  ρ₂σ₂ - ⟨w*, v⟩ ]`,

Its norm is `ρ₁ρ₂ + ⟨u*, v⟩` and its trace is `ρ₁ + ρ₂`.
With the usual conjugation, it is the octonion analogue of
`Conic/../TwistedMatrix.lean`:
there the off-diagonal entries multiply through the canonical pairing alone, here they also
multiply through the two vector products.

`GPR 22.14` builds the pair of vector products from an orientation `θ : ⋀³ M ≅ k` of a
projective module of rank three, and calls the result `Zor(M, θ)`. By `GPR 22.15` (Petersson)
**every** reduced octonion algebra is one of these, and `Zor(M, θ)` is split when `M` is free
(`GPR` asserts only this implication).

## What is proved here

* the conic structure, its norm, trace and conjugation — for **any** `k`-module `M` with a vector
  product pair, and with no hypothesis on `2`;
* **regularity and non-singularity of the norm** for `M` finitely generated projective, and again
  not by a computation: the norm is the hyperbolic form of `k ⊕ M`, pairing `(ρ₁, u*)` against
  `(ρ₂, v)`, so the hyperbolic-form API applies with no basis and no rank hypothesis;
* **multiplicativity of the norm**, which consumes the vector-product axioms exactly: the four
  orthogonality identities kill four of the nine cross terms and Binet–Cauchy converts the ninth,
  after which `n(xy) - n(x)n(y)` is identically zero;
* hence that it is a **composition algebra**, and a **reduced** one: the matrix unit `e₁₁` of
  `GPR (22.14.7)` is an elementary idempotent, so `GPR 22.9` applies to it.
* **alternativity** for `M` finitely generated projective: regularity makes the radical zero, so
  Kirmse's theorem applies to the multiplicative conic algebra, without a hypothesis on `2`.

Combined with `Module.VectorProductPair.ofBasis`, this produces a composition algebra of rank
eight over any commutative ring out of any free module of rank three — the split case, and the
case `GPR 22.14`'s localization argument reduces to. The coordinate isomorphism
`isomorphic_twistedZor_ofBasis` proves that this free case is exactly `Zor(k)` from `GPR 21.18`.

## Main definitions

* `ConicAlgebra.TwistedZor P` : the module of twisted Zorn vector matrices, with its
  multiplication.
* `ConicAlgebra.twistedZorNorm P`, `ConicAlgebra.twistedZor P` : the norm and the conic structure.

## Main results

* `ConicAlgebra.isGPRNonsingular_twistedZorNorm` : the norm is hyperbolic, hence non-singular.
* `ConicAlgebra.isMultiplicative_twistedZor` : the norm permits composition.
* `ConicAlgebra.isAlternative_twistedZor` : the algebra is alternative for `M` finitely
  generated projective.
* `ConicAlgebra.isComposition_twistedZor` : it is a composition algebra.
* `ConicAlgebra.hasElementaryIdempotent_twistedZor` : it is reduced.
* `ConicAlgebra.isomorphic_twistedZor_ofBasis` : a pair built from a basis gives the split Zorn
  algebra.
* `ConicAlgebra.instIsAlternativeTwistedZorOfBasis` : the basis-built algebra is alternative.
* `ConicAlgebra.isSplitOfRank_twistedZor_ofBasis` : the basis-built algebra is split of rank eight.

## Implementation notes

⚠ **The sign of the norm.** `GPR (22.14.4)` prints `n = ρ₁ρ₂ - ⟨u*, v⟩`, but the norm of
these algebras is `ρ₁ρ₂ + ⟨u*, v⟩`, which is used here. The two cannot both be right:
the
multiplication `GPR (22.14.3)` specializes, for `M = k³` with the standard orientation, to the
multiplication `GPR (21.18.4)` of ordinary Zorn vector matrices, whose norm is
`ρ₁ρ₂ + u₁ᵀu₂` by `GPR (21.18.6)` — the sign difference from the quaternion case
`GPR (22.12.1)` is already present
in `GPR`, and comes from the diagonal entries of `(22.14.3)` carrying a minus sign where those of
`(22.12.1)` carry a plus. The `+` sign is also what the Peirce norm formula
`ConicAlgebra.IsElementaryIdempotent.norm_peirceElement` gives, under the identification of
`C₁₂` with `M*` by the *positive* polar duality that `GPR 22.15`'s own proof uses.

The multiplication is not the componentwise one, so `TwistedZor` is a type synonym; it is indexed
by the vector product pair `P`, not merely by `M`, because the multiplication depends on `P`. This
is the same device as `ConicAlgebra.Cay`, which is indexed by the conic structure and the scalar.

## Orientation and converse

`Composition/Reduced/Orientation.lean` constructs the pair from an orientation of a
constant-rank-three finite projective module over any commutative ring, by the unbased local
exterior-power duality argument in `GPR 21.7`. The converse `GPR 22.15` is proved in
`Composition/Reduced/RankEight.lean`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 21.18, 22.9, 22.12,
  22.14, 22.15.
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]

/-- The `k`-module of **twisted Zorn vector matrices** attached to a vector product pair
(`GPR 22.14`), as a type synonym for `(k × M*) × (k × M)`: the element `x` is the matrix

  `[x.1.1  x.1.2]`
  `[x.2.2  x.2.1]`

whose top row is `x.1 = (ρ₁, u*)` and whose bottom row is
`(x.2.2, x.2.1) = (v, ρ₂)`. The grouping puts the two diagonal entries first in their pairs, so
that the norm is visibly the pairing of `x.1` against `x.2`. -/
def TwistedZor (_P : Module.VectorProductPair k M) : Type max u v :=
  (k × Module.Dual k M) × (k × M)

namespace TwistedZor

variable (P : Module.VectorProductPair k M)

instance : AddCommGroup (TwistedZor P) :=
  inferInstanceAs (AddCommGroup ((k × Module.Dual k M) × (k × M)))

instance : Module k (TwistedZor P) :=
  inferInstanceAs (Module k ((k × Module.Dual k M) × (k × M)))

instance [Module.Finite k M] [Module.Projective k M] : Module.Finite k (TwistedZor P) :=
  inferInstanceAs (Module.Finite k ((k × Module.Dual k M) × (k × M)))

instance [Module.Finite k M] [Module.Projective k M] : Module.Projective k (TwistedZor P) :=
  inferInstanceAs (Module.Projective k ((k × Module.Dual k M) × (k × M)))

variable {P}

/-- Two twisted Zorn vector matrices agree as soon as their four entries do. -/
theorem ext {x y : TwistedZor P} (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2)
    (h₃ : x.2.1 = y.2.1) (h₄ : x.2.2 = y.2.2) : x = y :=
  Prod.ext (Prod.ext h₁ h₂) (Prod.ext h₃ h₄)

@[simp] theorem fst_zero : (0 : TwistedZor P).1 = 0 := rfl
@[simp] theorem snd_zero : (0 : TwistedZor P).2 = 0 := rfl
@[simp] theorem fst_add (x y : TwistedZor P) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem snd_add (x y : TwistedZor P) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem fst_neg (x : TwistedZor P) : (-x).1 = -x.1 := rfl
@[simp] theorem snd_neg (x : TwistedZor P) : (-x).2 = -x.2 := rfl
@[simp] theorem fst_sub (x y : TwistedZor P) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem snd_sub (x y : TwistedZor P) : (x - y).2 = x.2 - y.2 := rfl
@[simp] theorem fst_smul (c : k) (x : TwistedZor P) : (c • x).1 = c • x.1 := rfl
@[simp] theorem snd_smul (c : k) (x : TwistedZor P) : (c • x).2 = c • x.2 := rfl

variable (P)

/-- **Multiplication of twisted Zorn vector matrices**, `GPR (22.14.3)`: the entries of `M*` and of
`M` multiply through the canonical pairing on the diagonal and through the two vector products off
it. -/
instance : Mul (TwistedZor P) :=
  ⟨fun x y ↦
    (((x.1.1 * y.1.1 - x.1.2 y.2.2, x.1.1 • y.1.2 + y.2.1 • x.1.2 + P.cross x.2.2 y.2.2),
      (x.2.1 * y.2.1 - y.1.2 x.2.2, y.1.1 • x.2.2 + x.2.1 • y.2.2 + P.crossDual x.1.2 y.1.2)) :
      (k × Module.Dual k M) × (k × M))⟩

/-- The identity matrix. -/
instance : One (TwistedZor P) :=
  ⟨(((1, 0), (1, 0)) : (k × Module.Dual k M) × (k × M))⟩

variable {P}

@[simp] theorem mul_fst_fst (x y : TwistedZor P) :
    (x * y).1.1 = x.1.1 * y.1.1 - x.1.2 y.2.2 := rfl
@[simp] theorem mul_fst_snd (x y : TwistedZor P) :
    (x * y).1.2 = x.1.1 • y.1.2 + y.2.1 • x.1.2 + P.cross x.2.2 y.2.2 := rfl
@[simp] theorem mul_snd_fst (x y : TwistedZor P) :
    (x * y).2.1 = x.2.1 * y.2.1 - y.1.2 x.2.2 := rfl
@[simp] theorem mul_snd_snd (x y : TwistedZor P) :
    (x * y).2.2 = y.1.1 • x.2.2 + x.2.1 • y.2.2 + P.crossDual x.1.2 y.1.2 := rfl
@[simp] theorem one_fst_fst : (1 : TwistedZor P).1.1 = 1 := rfl
@[simp] theorem one_fst_snd : (1 : TwistedZor P).1.2 = 0 := rfl
@[simp] theorem one_snd_fst : (1 : TwistedZor P).2.1 = 1 := rfl
@[simp] theorem one_snd_snd : (1 : TwistedZor P).2.2 = 0 := rfl

variable (P)

instance : NonAssocRing (TwistedZor P) :=
  { (inferInstance : AddCommGroup (TwistedZor P)), (inferInstance : Mul (TwistedZor P)),
    (inferInstance : One (TwistedZor P)) with
    left_distrib := fun x y z ↦ TwistedZor.ext (by simp; ring) (by simp; module)
      (by simp; ring) (by simp; module)
    right_distrib := fun x y z ↦ TwistedZor.ext (by simp; ring) (by simp; module)
      (by simp; ring) (by simp; module)
    zero_mul := fun x ↦ TwistedZor.ext (by simp) (by simp) (by simp) (by simp)
    mul_zero := fun x ↦ TwistedZor.ext (by simp) (by simp) (by simp) (by simp)
    one_mul := fun x ↦ TwistedZor.ext (by simp) (by simp) (by simp) (by simp)
    mul_one := fun x ↦ TwistedZor.ext (by simp) (by simp) (by simp) (by simp) }

instance : SMulCommClass k (TwistedZor P) (TwistedZor P) :=
  ⟨fun c x y ↦ TwistedZor.ext (by simp; ring) (by simp; module) (by simp; ring)
    (by simp; module)⟩

instance : IsScalarTower k (TwistedZor P) (TwistedZor P) :=
  ⟨fun c x y ↦ TwistedZor.ext (by simp; ring) (by simp; module) (by simp; ring)
    (by simp; module)⟩

end TwistedZor

/-! ### The norm

`n = ρ₁ρ₂ + ⟨u*, v⟩` pairs the top row against the bottom row, with the bottom row read in
`k ⊕ M` and the top row in its dual. That is what makes it hyperbolic, and it is why
no rank hypothesis and no basis is needed for non-singularity. -/

variable (P : Module.VectorProductPair k M)

/-- The linear equivalence presenting a twisted Zorn vector matrix as an element of
`(k ⊕ M)* ⊕ (k ⊕ M)`, under which the norm becomes the hyperbolic form
`QuadraticForm.dualProd k (k × M)`. The sign on the dual coordinate compensates the one built into
`ConicAlgebra.dualProdEquiv`, which was chosen for the quaternion norm `ρ₁ρ₂ - ⟨u*, v⟩` of
`GPR (22.12.1)`. -/
def twistedZorDualProdEquiv : TwistedZor P ≃ₗ[k] (Module.Dual k (k × M) × (k × M)) :=
  (((LinearEquiv.refl k k).prodCongr (LinearEquiv.neg k)).trans (dualProdEquiv k M)).prodCongr
    (LinearEquiv.refl k (k × M))

@[simp] theorem twistedZorDualProdEquiv_apply (x : TwistedZor P) :
    twistedZorDualProdEquiv P x = (dualProdEquiv k M (x.1.1, -x.1.2), x.2) := rfl

/-- The **norm of a twisted Zorn vector matrix**, `GPR (22.14.4)`: `n = ρ₁ρ₂ + ⟨u*, v⟩`.

⚠ `GPR (22.14.4)` prints a minus sign; see the module docstring for why it must be a plus. -/
def twistedZorNorm : QuadraticForm k (TwistedZor P) :=
  (QuadraticForm.dualProd k (k × M)).comp (twistedZorDualProdEquiv P).toLinearMap

variable {P}

@[simp] theorem twistedZorNorm_apply (x : TwistedZor P) :
    twistedZorNorm P x = x.1.1 * x.2.1 + x.1.2 x.2.2 := by
  rw [twistedZorNorm, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    twistedZorDualProdEquiv_apply, QuadraticForm.dualProd_apply, dualProdEquiv_apply]
  simp

theorem polar_twistedZorNorm (x y : TwistedZor P) :
    QuadraticMap.polar (twistedZorNorm P) x y =
      x.1.1 * y.2.1 + y.1.1 * x.2.1 + x.1.2 y.2.2 + y.1.2 x.2.2 := by
  simp only [QuadraticMap.polar, twistedZorNorm_apply, TwistedZor.fst_add, TwistedZor.snd_add,
    Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
  ring

@[simp] theorem polar_twistedZorNorm_one (x : TwistedZor P) :
    QuadraticMap.polar (twistedZorNorm P) 1 x = x.1.1 + x.2.1 := by
  rw [polar_twistedZorNorm]
  simp [add_comm]

variable (P)

/-- **`GPR 22.14`: the twisted Zorn vector matrices form a conic algebra**, with norm
`ρ₁ρ₂ + ⟨u*, v⟩` and trace `ρ₁ + ρ₂`. The degree-two identity uses only that the two
products are alternating; no other axiom, no hypothesis on `M`, and none on `2`. -/
def twistedZor : ConicAlgebra k (TwistedZor P) where
  norm := twistedZorNorm P
  norm_one := by simp
  mul_self x := by
    refine TwistedZor.ext ?_ ?_ ?_ ?_
    · simp; ring
    · simp [P.cross_self, add_smul]
    · simp; ring
    · simp [P.crossDual_self, add_smul]

variable {P}

@[simp] theorem twistedZor_norm : (twistedZor P).norm = twistedZorNorm P := rfl

/-- **The trace of a twisted Zorn vector matrix is the trace of the matrix**, `GPR (22.14.5)`. -/
@[simp] theorem trace_twistedZor_apply (x : TwistedZor P) :
    (twistedZor P).trace x = x.1.1 + x.2.1 := by
  rw [ConicAlgebra.trace_apply, twistedZor_norm, polar_twistedZorNorm_one]

/-- **The conjugation exchanges the diagonal entries and negates the off-diagonal ones**,
`GPR (22.14.6)`. -/
@[simp] theorem conj_twistedZor_apply (x : TwistedZor P) :
    (twistedZor P).conj x = (((x.2.1, -x.1.2), (x.1.1, -x.2.2)) :
      (k × Module.Dual k M) × (k × M)) := by
  refine TwistedZor.ext ?_ ?_ ?_ ?_ <;> simp [ConicAlgebra.conj_apply]

/-! ### Non-singularity, multiplicativity, and the composition algebra -/

variable (P)

/-- **The norm of the twisted Zorn vector matrices is non-singular** for `M` finitely generated
projective: it *is* the hyperbolic form of `k ⊕ M`. No rank hypothesis and no hypothesis on
`2`. -/
theorem isGPRNonsingular_twistedZorNorm [Module.Finite k M] [Module.Projective k M] :
    QuadraticForm.IsGPRNonsingular.{u, max u v, w} (twistedZorNorm P) :=
  (QuadraticForm.isGPRNonsingular_dualProd k (k × M)).comp_linearEquiv _

/-- **The norm of the twisted Zorn vector matrices is regular** for `M` finitely generated
projective: it is the hyperbolic form of `k ⊕ M`, transported along a linear equivalence. This is
stronger than the non-singularity needed for composition and requires no hypothesis on `2`. -/
theorem isGPRRegular_twistedZorNorm [Module.Finite k M] [Module.Projective k M] :
    QuadraticForm.IsGPRRegular (twistedZorNorm P) :=
  (QuadraticForm.isGPRRegular_dualProd k (k × M)).comp_linearEquiv _

/-- The twisted Zorn norm has zero radical when `M` is finitely generated projective. -/
theorem isGPRNondegenerate_twistedZorNorm [Module.Finite k M] [Module.Projective k M] :
    QuadraticForm.IsGPRNondegenerate (twistedZorNorm P) := by
  rw [QuadraticForm.IsGPRNondegenerate]
  exact le_antisymm (QuadraticMap.radical_le_ker_polarBilin.trans
    (((LinearMap.ker_eq_bot).2 (isGPRRegular_twistedZorNorm P).1).le)) bot_le

variable {P}

/-- **The norm of the twisted Zorn vector matrices permits composition**, `n(xy) = n(x)n(y)`.

This is where the vector-product axioms are consumed, and they are consumed exactly: of the nine
terms of the off-diagonal pairing, four vanish by orthogonality of a product to its own arguments
and one is `⟨v × w, v* × w*⟩`, which Binet–Cauchy turns into the two remaining products of
pairings; what is left cancels identically. No hypothesis on `M`. -/
theorem isMultiplicative_twistedZor : (twistedZor P).IsMultiplicative := by
  intro x y
  simp only [twistedZor_norm, twistedZorNorm_apply, TwistedZor.mul_fst_fst,
    TwistedZor.mul_fst_snd, TwistedZor.mul_snd_fst, TwistedZor.mul_snd_snd, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, P.cross_apply_left, P.cross_apply_right,
    P.apply_crossDual_left, P.apply_crossDual_right, P.cross_apply_crossDual]
  ring

/-- **`GPR 22.14`: twisted Zorn vector matrices are alternative** when `M` is finitely generated
projective. The hyperbolic norm is regular, hence has zero radical, so Kirmse's theorem applies to
the multiplicative conic structure. No hypothesis on `2` and no direct Grassmann-identity
calculation is needed. -/
theorem isAlternative_twistedZor [Module.Finite k M] [Module.Projective k M] :
    IsAlternative (TwistedZor P) :=
  isMultiplicative_twistedZor.isAlternative (isGPRNondegenerate_twistedZorNorm P)

/-- **The twisted Zorn vector matrices form a composition algebra**, for `M` finitely generated
projective carrying a vector product pair. With `Module.VectorProductPair.ofBasis` this gives a
composition algebra of rank eight over any commutative ring, with no hypothesis on `2`; by
`GPR 22.14` it is `Zor(M, θ)` whenever the pair comes from an orientation of a rank-three
module. -/
theorem isComposition_twistedZor [Module.Finite k M] [Module.Projective k M] :
    (twistedZor P).IsComposition.{u, max u v, w} where
  isGPRNonsingular := isGPRNonsingular_twistedZorNorm.{u, v, w} P
  isMultiplicative := isMultiplicative_twistedZor

variable (P)

/-- **The twisted Zorn vector matrices are reduced.** The matrix unit `e₁₁` of
`GPR (22.14.7)` has norm `0` and trace `1`, so it is an elementary idempotent and `GPR 22.9`
applies: the norm is
isotropic and the algebra contains a split quadratic étale subalgebra. No hypothesis on `M`. -/
theorem hasElementaryIdempotent_twistedZor : (twistedZor P).HasElementaryIdempotent :=
  ⟨(((1, 0), (0, 0)) : (k × Module.Dual k M) × (k × M)),
    (twistedZorNorm_apply (((1, 0), (0, 0)) : TwistedZor P)).trans (by simp),
    (trace_twistedZor_apply (((1, 0), (0, 0)) : TwistedZor P)).trans (by simp)⟩

/-! ### The free case

When the vector product pair comes from a basis of `M`, reading the two off-diagonal entries in
the coordinates of that basis and its dual identifies the twisted construction with `Zor(k)`.
Thus `Module.VectorProductPair.ofBasis` produces exactly the split octonion algebra, independently
of the chosen basis. -/

variable (b : Module.Basis (Fin 3) k M)

/-- The coordinate equivalence from the twisted Zorn algebra attached to a basis to the split Zorn
algebra. The lower-left entry uses the coordinates of `b`, while the upper-right entry uses the
coordinates of the dual basis. -/
noncomputable def twistedZorOfBasisEquiv :
    TwistedZor (Module.VectorProductPair.ofBasis b) ≃ₗ[k] Zor k where
  toFun x := ((x.1.1, b.equivFun x.2.2), (x.2.1, b.dualCoord x.1.2))
  invFun x :=
    ((x.1.1, b.dualCoord.symm x.2.2), (x.2.1, b.equivFun.symm x.1.2))
  map_add' x y := by
    change
      ((x.1.1 + y.1.1, b.equivFun (x.2.2 + y.2.2)),
        (x.2.1 + y.2.1, b.dualCoord (x.1.2 + y.1.2))) =
      ((x.1.1 + y.1.1, b.equivFun x.2.2 + b.equivFun y.2.2),
        (x.2.1 + y.2.1, b.dualCoord x.1.2 + b.dualCoord y.1.2))
    rw [map_add, map_add]
  map_smul' c x := by
    change
      ((c • x.1.1, b.equivFun (c • x.2.2)),
        (c • x.2.1, b.dualCoord (c • x.1.2))) =
      ((c • x.1.1, c • b.equivFun x.2.2),
        (c • x.2.1, c • b.dualCoord x.1.2))
    rw [map_smul, map_smul]
  left_inv x := by
    refine TwistedZor.ext rfl ?_ rfl ?_
    · exact b.dualCoord.symm_apply_apply x.1.2
    · exact b.equivFun.symm_apply_apply x.2.2
  right_inv x := by
    refine Zor.ext rfl ?_ rfl ?_
    · exact b.equivFun.apply_symm_apply x.1.2
    · exact b.dualCoord.apply_symm_apply x.2.2

@[simp] theorem twistedZorOfBasisEquiv_apply
    (x : TwistedZor (Module.VectorProductPair.ofBasis b)) :
    twistedZorOfBasisEquiv b x =
      ((x.1.1, b.equivFun x.2.2), (x.2.1, b.dualCoord x.1.2)) :=
  rfl

/-- The coordinate equivalence preserves the norm. -/
theorem zorNorm_twistedZorOfBasisEquiv
    (x : TwistedZor (Module.VectorProductPair.ofBasis b)) :
    zorNorm k (twistedZorOfBasisEquiv b x) =
      twistedZorNorm (Module.VectorProductPair.ofBasis b) x := by
  rw [zorNorm_apply, twistedZorOfBasisEquiv_apply, twistedZorNorm_apply,
    b.apply_eq_dotProduct x.1.2 x.2.2]
  exact congrArg (x.1.1 * x.2.1 + ·)
    (dotProduct_comm (m := Fin 3) (b.equivFun x.2.2) (b.dualCoord x.1.2))

/-- The coordinate equivalence preserves the identity matrix. -/
theorem twistedZorOfBasisEquiv_one :
    twistedZorOfBasisEquiv b (1 : TwistedZor (Module.VectorProductPair.ofBasis b)) = 1 := by
  refine Zor.ext rfl ?_ rfl ?_
  · exact map_zero b.equivFun
  · exact map_zero b.dualCoord

/-- The coordinate equivalence preserves multiplication. -/
theorem twistedZorOfBasisEquiv_mul
    (x y : TwistedZor (Module.VectorProductPair.ofBasis b)) :
    twistedZorOfBasisEquiv b (x * y) =
      twistedZorOfBasisEquiv b x * twistedZorOfBasisEquiv b y := by
  refine Zor.ext ?_ ?_ ?_ ?_
  · change x.1.1 * y.1.1 - x.1.2 y.2.2 =
      x.1.1 * y.1.1 - b.dualCoord x.1.2 ⬝ᵥ b.equivFun y.2.2
    rw [b.apply_eq_dotProduct x.1.2 y.2.2]
  · change b.equivFun
        (y.1.1 • x.2.2 + x.2.1 • y.2.2 + Module.crossDualOfBasis b x.1.2 y.1.2) =
      y.1.1 • b.equivFun x.2.2 + x.2.1 • b.equivFun y.2.2 +
        crossProduct (b.dualCoord x.1.2) (b.dualCoord y.1.2)
    rw [map_add, map_add, map_smul, map_smul, Module.crossDualOfBasis_apply,
      LinearEquiv.apply_symm_apply]
  · change x.2.1 * y.2.1 - y.1.2 x.2.2 =
      x.2.1 * y.2.1 - b.equivFun x.2.2 ⬝ᵥ b.dualCoord y.1.2
    rw [b.apply_eq_dotProduct y.1.2 x.2.2,
      dotProduct_comm (m := Fin 3) (b.dualCoord y.1.2) (b.equivFun x.2.2)]
  · change b.dualCoord
        (x.1.1 • y.1.2 + y.2.1 • x.1.2 + Module.crossOfBasis b x.2.2 y.2.2) =
      x.1.1 • b.dualCoord y.1.2 + y.2.1 • b.dualCoord x.1.2 +
        crossProduct (b.equivFun x.2.2) (b.equivFun y.2.2)
    rw [map_add, map_add, map_smul, map_smul, Module.crossOfBasis_apply,
      LinearEquiv.apply_symm_apply]

/-- The norm isometry from the basis-built twisted Zorn algebra to the split Zorn algebra. -/
noncomputable def twistedZorOfBasisIsometryEquiv :
    (twistedZor (Module.VectorProductPair.ofBasis b)).norm.IsometryEquiv (zor k).norm where
  toLinearEquiv := twistedZorOfBasisEquiv b
  map_app' := zorNorm_twistedZorOfBasisEquiv b

/-- **The free case of `GPR 22.14`: a twisted Zorn algebra whose vector products come from a
basis is isomorphic to the split Zorn algebra `Zor(k)` of `GPR 21.18`.** -/
theorem isomorphic_twistedZor_ofBasis :
    (twistedZor (Module.VectorProductPair.ofBasis b)).Isomorphic (zor k) :=
  ⟨twistedZorOfBasisIsometryEquiv b, twistedZorOfBasisEquiv_one b,
    twistedZorOfBasisEquiv_mul b⟩

/-- Any twisted Zorn algebra on a module admitting a basis of size three is split. Binet–Cauchy
forces its vector-product pair to be the pair attached to a suitably rescaled basis. -/
theorem isomorphic_twistedZor_of_exists_basis (P : Module.VectorProductPair k M)
    (b : Module.Basis (Fin 3) k M) : (twistedZor P).Isomorphic (zor k) := by
  obtain ⟨b', rfl⟩ := P.exists_eq_ofBasis b
  exact isomorphic_twistedZor_ofBasis b'

/-- Any twisted Zorn algebra on a module admitting a basis of size three satisfies the
rank-eight splitness clause of `GPR 21.19(d)`. -/
theorem isSplitOfRank_twistedZor_of_exists_basis (P : Module.VectorProductPair k M)
    (b : Module.Basis (Fin 3) k M) : (twistedZor P).IsSplitOfRank 8 :=
  isomorphic_twistedZor_of_exists_basis P b

/-- A basis-built twisted Zorn algebra is alternative, because its coordinate equivalence
identifies its multiplication with that of the alternative algebra `Zor(k)`. This proves the free
case of the alternativity assertion in `GPR 22.14` without any hypothesis on `2`. -/
noncomputable instance instIsAlternativeTwistedZorOfBasis :
    IsAlternative (TwistedZor (Module.VectorProductPair.ofBasis b)) where
  left_alt x y := by
    apply (twistedZorOfBasisEquiv b).injective
    simpa only [twistedZorOfBasisEquiv_mul] using
      (IsAlternative.left_alt (twistedZorOfBasisEquiv b x) (twistedZorOfBasisEquiv b y))
  right_alt x y := by
    apply (twistedZorOfBasisEquiv b).injective
    simpa only [twistedZorOfBasisEquiv_mul] using
      (IsAlternative.right_alt (twistedZorOfBasisEquiv b x) (twistedZorOfBasisEquiv b y))

/-- A basis-built twisted Zorn algebra has rank eight. -/
@[simp] theorem finrank_twistedZor_ofBasis [Nontrivial k] :
    Module.finrank k (TwistedZor (Module.VectorProductPair.ofBasis b)) = 8 :=
  (twistedZorOfBasisEquiv b).finrank_eq.trans (finrank_zor (k := k))

/-- The basis-built twisted Zorn algebra satisfies the rank-eight splitness clause of
`GPR 21.19(d)`. -/
theorem isSplitOfRank_twistedZor_ofBasis :
    (twistedZor (Module.VectorProductPair.ofBasis b)).IsSplitOfRank 8 :=
  isomorphic_twistedZor_ofBasis b

end ConicAlgebra

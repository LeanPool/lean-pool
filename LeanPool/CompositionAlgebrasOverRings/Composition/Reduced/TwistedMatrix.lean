/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Defs
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Peirce
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Splitness
public import LeanPool.CompositionAlgebrasOverRings.Module.Invertible

/-!
# `L`-twisted 2-by-2 matrices (`GPR 22.12`, `22.13`)

For `L` a `k`-module, the **`L`-twisted 2-by-2 matrices** are the formal matrices

  `[ρ₁  u*]`
  `[v   ρ₂]`,   `ρᵢ ∈ k`, `u* ∈ L*`, `v ∈ L`,

multiplied as matrices, using the canonical pairing `L* × L → k` wherever a product of an entry
of `L*` with an entry of `L` occurs (`GPR 22.12`):

  `[ρ₁ u*] [σ₁ w*]   [ ρ₁σ₁ + ⟨u*, z⟩     ρ₁w* + σ₂u*   ]`
  `[v  ρ₂] [z  σ₂] = [ σ₁v + ρ₂z         ρ₂σ₂ + ⟨w*, v⟩ ]`,

with norm `ρ₁ρ₂ - ⟨u*, v⟩`, trace `ρ₁ + ρ₂` and conjugation exchanging the diagonal
and negating the off-diagonal entries — `GPR (22.12.1)`, `(22.12.2)`, `(22.12.3)`. When `L` is a
line bundle this is `GPR`'s presentation of `Endₖ(k ⊕ L)`, the quaternion algebra of `L`-twisted
matrices, and by `GPR 22.13` **every** reduced quaternion algebra is one of these.

## What is proved here

Both directions of `GPR 22.13`:

* the conic structure, its norm, trace and conjugation — for **any** `k`-module `L`;
* **non-singularity of the norm** for `L` finitely generated projective — and not by a
  computation: the norm is the hyperbolic form of `k ⊕ L`, pairing `(ρ₁, u*)` against
  `(ρ₂, -v)`, so `QuadraticForm.isGPRNonsingular_dualProd` applies with no basis, no rank
  hypothesis and no hypothesis on `2`;
* **multiplicativity of the norm** exactly under the identity `Module.IsRankOnePairing`,
  `⟨φ, x⟩⟨ψ, y⟩ = ⟨φ, y⟩⟨ψ, x⟩` — what the algebra needs `L` to have rank one for,
  and the only place the rank enters;
* hence that it is a **composition algebra**, and a **reduced** one: the matrix unit `e₁₁` is an
  elementary idempotent (`GPR (22.12.4)`), so `GPR 22.9` applies to it.
* conversely, a reduced composition algebra of constant rank four is isomorphic to the twisted
  matrices for its lower-left Peirce component. The Peirce rank count makes that component a line
  bundle, and the regular polar pairing identifies the upper-right component with its dual.

The general-purpose equivalence `Module.invertible_iff_isLocallyFreeRankOne` proves that a line
bundle satisfies `Module.IsRankOnePairing`. Thus the construction gives a composition algebra for
every invertible `L`, with no freeness assumption.

## Main definitions

* `Module.IsRankOnePairing k L` : the identity `⟨φ, x⟩⟨ψ, y⟩ = ⟨φ, y⟩⟨ψ, x⟩`.
* `ConicAlgebra.TwistedMat k L` : the module of `L`-twisted matrices, with its multiplication.
* `ConicAlgebra.twistedMatNorm k L`, `ConicAlgebra.twistedMat k L` : the norm and the conic
  structure.

## Main results

* `ConicAlgebra.isGPRNonsingular_twistedMatNorm` : the norm is hyperbolic, hence non-singular.
* `ConicAlgebra.isMultiplicative_twistedMat` : the norm permits composition, given the rank-one
  pairing identity.
* `ConicAlgebra.isComposition_twistedMat` : it is a composition algebra.
* `ConicAlgebra.isComposition_twistedMat_of_invertible` : the line-bundle form of `GPR 22.12`.
* `ConicAlgebra.hasElementaryIdempotent_twistedMat` : it is reduced — `GPR 22.13`'s easy half.
* `ConicAlgebra.IsElementaryIdempotent.isomorphic_twistedMat` : every reduced constant-rank-four
  composition algebra is a twisted-matrix algebra, the converse half of `GPR 22.13`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 22.9, 22.12, 22.13.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable (k : Type u) [CommRing k] (L : Type v) [AddCommGroup L] [Module k L]

/-- The `k`-module of **`L`-twisted 2-by-2 matrices** (`GPR 22.12`), as a type synonym for
`(k × L*) × (k × L)`: the element `x` is the matrix

  `[x.1.1  x.1.2]`
  `[x.2.2  x.2.1]`

whose top row is `x.1 = (ρ₁, u*)` and whose bottom row is `(x.2.2, x.2.1) = (v, ρ₂)`. The
synonym
is needed because the multiplication is not the componentwise one; the grouping puts the two
diagonal entries first in their pairs, so that the norm is visibly the pairing of `x.1` against
`x.2`. -/
def TwistedMat : Type max u v := (k × Module.Dual k L) × (k × L)

namespace TwistedMat

instance : AddCommGroup (TwistedMat k L) :=
  inferInstanceAs (AddCommGroup ((k × Module.Dual k L) × (k × L)))

instance : Module k (TwistedMat k L) :=
  inferInstanceAs (Module k ((k × Module.Dual k L) × (k × L)))

instance [Module.Finite k L] [Module.Projective k L] : Module.Finite k (TwistedMat k L) :=
  inferInstanceAs (Module.Finite k ((k × Module.Dual k L) × (k × L)))

instance [Module.Finite k L] [Module.Projective k L] : Module.Projective k (TwistedMat k L) :=
  inferInstanceAs (Module.Projective k ((k × Module.Dual k L) × (k × L)))

variable {k L}

/-- Two twisted matrices agree as soon as their four entries do. -/
theorem ext {x y : TwistedMat k L} (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2)
    (h₃ : x.2.1 = y.2.1)
    (h₄ : x.2.2 = y.2.2) : x = y :=
  Prod.ext (Prod.ext h₁ h₂) (Prod.ext h₃ h₄)

@[simp] theorem fst_zero : (0 : TwistedMat k L).1 = 0 := rfl
@[simp] theorem fst_neg (x : TwistedMat k L) : (-x).1 = -x.1 := rfl
@[simp] theorem snd_neg (x : TwistedMat k L) : (-x).2 = -x.2 := rfl
@[simp] theorem fst_sub (x y : TwistedMat k L) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem snd_sub (x y : TwistedMat k L) : (x - y).2 = x.2 - y.2 := rfl
@[simp] theorem snd_zero : (0 : TwistedMat k L).2 = 0 := rfl
@[simp] theorem fst_add (x y : TwistedMat k L) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem snd_add (x y : TwistedMat k L) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem fst_smul (c : k) (x : TwistedMat k L) : (c • x).1 = c • x.1 := rfl
@[simp] theorem snd_smul (c : k) (x : TwistedMat k L) : (c • x).2 = c • x.2 := rfl

variable (k L)

/-- **Matrix multiplication of twisted matrices**, `GPR 22.12`: the entries of `L*` and of `L`
multiply through the canonical pairing. -/
instance : Mul (TwistedMat k L) :=
  ⟨fun x y ↦
    (((x.1.1 * y.1.1 + x.1.2 y.2.2, x.1.1 • y.1.2 + y.2.1 • x.1.2),
      (x.2.1 * y.2.1 + y.1.2 x.2.2, y.1.1 • x.2.2 + x.2.1 • y.2.2)) :
      (k × Module.Dual k L) × (k × L))⟩

/-- The identity matrix. -/
instance : One (TwistedMat k L) :=
  ⟨(((1, 0), (1, 0)) : (k × Module.Dual k L) × (k × L))⟩

variable {k L}

@[simp] theorem mul_fst_fst (x y : TwistedMat k L) :
    (x * y).1.1 = x.1.1 * y.1.1 + x.1.2 y.2.2 := rfl
@[simp] theorem mul_fst_snd (x y : TwistedMat k L) :
    (x * y).1.2 = x.1.1 • y.1.2 + y.2.1 • x.1.2 := rfl
@[simp] theorem mul_snd_fst (x y : TwistedMat k L) :
    (x * y).2.1 = x.2.1 * y.2.1 + y.1.2 x.2.2 := rfl
@[simp] theorem mul_snd_snd (x y : TwistedMat k L) :
    (x * y).2.2 = y.1.1 • x.2.2 + x.2.1 • y.2.2 := rfl
@[simp] theorem one_fst_fst : (1 : TwistedMat k L).1.1 = 1 := rfl
@[simp] theorem one_fst_snd : (1 : TwistedMat k L).1.2 = 0 := rfl
@[simp] theorem one_snd_fst : (1 : TwistedMat k L).2.1 = 1 := rfl
@[simp] theorem one_snd_snd : (1 : TwistedMat k L).2.2 = 0 := rfl

variable (k L)

instance : NonAssocRing (TwistedMat k L) :=
  { (inferInstance : AddCommGroup (TwistedMat k L)), (inferInstance : Mul (TwistedMat k L)),
    (inferInstance : One (TwistedMat k L)) with
    left_distrib := fun x y z ↦ TwistedMat.ext (by simp; ring) (by simp; module)
      (by simp; ring) (by simp; module)
    right_distrib := fun x y z ↦ TwistedMat.ext (by simp; ring) (by simp; module)
      (by simp; ring) (by simp; module)
    zero_mul := fun x ↦ TwistedMat.ext (by simp) (by simp) (by simp) (by simp)
    mul_zero := fun x ↦ TwistedMat.ext (by simp) (by simp) (by simp) (by simp)
    one_mul := fun x ↦ TwistedMat.ext (by simp) (by simp) (by simp) (by simp)
    mul_one := fun x ↦ TwistedMat.ext (by simp) (by simp) (by simp) (by simp) }

instance : SMulCommClass k (TwistedMat k L) (TwistedMat k L) :=
  ⟨fun c x y ↦ TwistedMat.ext (by simp; ring) (by simp; module) (by simp; ring)
    (by simp; module)⟩

instance : IsScalarTower k (TwistedMat k L) (TwistedMat k L) :=
  ⟨fun c x y ↦ TwistedMat.ext (by simp; ring) (by simp; module) (by simp; ring)
    (by simp; module)⟩

end TwistedMat

/-! ### The norm

`n = ρ₁ρ₂ - ⟨u*, v⟩` is the pairing of the top row against the bottom row, once the
bottom row is
read in `k ⊕ L` and the top row in its dual. That is what makes it hyperbolic. -/

/-- The identification `k × L* ≃ (k ⊕ L)*` sending `(ρ, u*)` to
`(a, w) ↦ ρa - ⟨u*, w⟩`. The sign
is what turns the norm below into the hyperbolic pairing. -/
def dualProdEquiv : (k × Module.Dual k L) ≃ₗ[k] Module.Dual k (k × L) where
  toFun p := p.1 • (LinearMap.fst k k L) - p.2 ∘ₗ (LinearMap.snd k k L)
  map_add' p q := by
    ext w
    · simp
    · simp
      ring
  map_smul' c p := by ext w <;> simp
  invFun f := (f (1, 0), -(f ∘ₗ LinearMap.inr k k L))
  left_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · ext w; simp
  right_inv f := by
    refine LinearMap.ext fun w ↦ ?_
    have hw : f w = f (w.1, 0) + f (0, w.2) := by
      rw [← map_add]
      congr 1
      simp
    have h1 : f ((w.1 : k), (0 : L)) = w.1 * f (1, 0) := by
      rw [show ((w.1, (0 : L)) : k × L) = w.1 • (1, 0) by simp, map_smul, smul_eq_mul]
    simp [hw, h1]
    ring

variable {k L}

@[simp] theorem dualProdEquiv_apply (p : k × Module.Dual k L) (w : k × L) :
    dualProdEquiv k L p w = p.1 * w.1 - p.2 w.2 := by
  simp [dualProdEquiv]

variable (k L)

/-- The linear equivalence presenting a twisted matrix as an element of `(k ⊕ L)* ⊕ (k ⊕ L)`,
under which the norm becomes the hyperbolic form `QuadraticForm.dualProd k (k × L)`. -/
def twistedMatDualProdEquiv :
    TwistedMat k L ≃ₗ[k] (Module.Dual k (k × L) × (k × L)) :=
  (dualProdEquiv k L).prodCongr (LinearEquiv.refl k (k × L))

@[simp] theorem twistedMatDualProdEquiv_apply (x : TwistedMat k L) :
    twistedMatDualProdEquiv k L x = (dualProdEquiv k L x.1, x.2) := rfl

/-- The **norm of a twisted matrix**, `GPR (22.12.1)`:
`n = ρ₁ρ₂ - ⟨u*, v⟩`, the determinant. -/
def twistedMatNorm : QuadraticForm k (TwistedMat k L) :=
  (QuadraticForm.dualProd k (k × L)).comp (twistedMatDualProdEquiv k L).toLinearMap

variable {k L}

@[simp] theorem twistedMatNorm_apply (x : TwistedMat k L) :
    twistedMatNorm k L x = x.1.1 * x.2.1 - x.1.2 x.2.2 := by
  rw [twistedMatNorm, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    twistedMatDualProdEquiv_apply, QuadraticForm.dualProd_apply, dualProdEquiv_apply]

theorem polar_twistedMatNorm (x y : TwistedMat k L) :
    QuadraticMap.polar (twistedMatNorm k L) x y =
      x.1.1 * y.2.1 + y.1.1 * x.2.1 - x.1.2 y.2.2 - y.1.2 x.2.2 := by
  simp only [QuadraticMap.polar, twistedMatNorm_apply, TwistedMat.fst_add, TwistedMat.snd_add,
    Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
  ring

@[simp] theorem polar_twistedMatNorm_one (x : TwistedMat k L) :
    QuadraticMap.polar (twistedMatNorm k L) 1 x = x.1.1 + x.2.1 := by
  rw [polar_twistedMatNorm]
  simp [add_comm]

variable (k L)

/-- **`GPR 22.12`: the twisted matrices form a conic algebra**, with norm
`ρ₁ρ₂ - ⟨u*, v⟩` and
trace `ρ₁ + ρ₂`. No hypothesis on `L` at all, and none on `2`. -/
def twistedMat : ConicAlgebra k (TwistedMat k L) where
  norm := twistedMatNorm k L
  norm_one := by simp
  mul_self x := by
    refine TwistedMat.ext ?_ ?_ ?_ ?_
    · simp; ring
    · simp [add_smul]
    · simp; ring
    · simp [add_smul]

variable {k L}

@[simp] theorem twistedMat_norm : (twistedMat k L).norm = twistedMatNorm k L := rfl

/-- **The trace of a twisted matrix is the sum of its diagonal entries**, `GPR (22.12.2)`. -/
@[simp] theorem trace_twistedMat_apply (x : TwistedMat k L) :
    (twistedMat k L).trace x = x.1.1 + x.2.1 := by
  rw [ConicAlgebra.trace_apply, twistedMat_norm, polar_twistedMatNorm_one]

/-- **The conjugation exchanges the diagonal entries and negates the off-diagonal ones**,
`GPR (22.12.3)`. -/
@[simp] theorem conj_twistedMat_apply (x : TwistedMat k L) :
    (twistedMat k L).conj x = (((x.2.1, -x.1.2), (x.1.1, -x.2.2)) :
      (k × Module.Dual k L) × (k × L)) := by
  refine TwistedMat.ext ?_ ?_ ?_ ?_ <;> simp [ConicAlgebra.conj_apply]

/-! ### Non-singularity, multiplicativity, and the composition algebra -/

variable (k L)

/-- **The norm of the twisted matrices is non-singular** for `L` finitely generated projective: it
*is* the hyperbolic form of `k ⊕ L`. No rank hypothesis and no hypothesis on `2`. -/
theorem isGPRNonsingular_twistedMatNorm [Module.Finite k L] [Module.Projective k L] :
    QuadraticForm.IsGPRNonsingular.{u, max u v, w} (twistedMatNorm k L) :=
  (QuadraticForm.isGPRNonsingular_dualProd k (k × L)).comp_linearEquiv _

variable {k L}

/-- **The norm of the twisted matrices permits composition** exactly when `L` has the rank-one
pairing identity: expanding `n(xy)` and `n(x)n(y)` leaves precisely the difference
`⟨u*, z⟩⟨w*, v⟩ - ⟨u*, v⟩⟨w*, z⟩`. -/
theorem isMultiplicative_twistedMat (h : Module.IsRankOnePairing k L) :
    (twistedMat k L).IsMultiplicative := by
  intro x y
  simp only [twistedMat_norm, twistedMatNorm_apply, TwistedMat.mul_fst_fst,
    TwistedMat.mul_fst_snd, TwistedMat.mul_snd_fst, TwistedMat.mul_snd_snd, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul, smul_eq_mul]
  have hxy := h x.1.2 y.1.2 y.2.2 x.2.2
  linear_combination hxy

/-- **The twisted matrices form a composition algebra**, for `L` finitely generated projective with
the rank-one pairing identity — that is, for `L` a line bundle. This is the object of
`GPR 22.12`. -/
theorem isComposition_twistedMat [Module.Finite k L] [Module.Projective k L]
    (h : Module.IsRankOnePairing k L) : (twistedMat k L).IsComposition.{u, max u v, w} where
  isGPRNonsingular := isGPRNonsingular_twistedMatNorm.{u, v, w} k L
  isMultiplicative := isMultiplicative_twistedMat h

/-- **`GPR 22.12`.** Twisted matrices attached to an invertible module form a composition
algebra. The required rank-one pairing identity follows from
`Module.invertible_iff_isLocallyFreeRankOne`. -/
theorem isComposition_twistedMat_of_invertible [Module.Invertible k L] :
    (twistedMat k L).IsComposition.{u, max u v, w} :=
  isComposition_twistedMat Module.isRankOnePairing_of_invertible

variable (k L)

/-- **`GPR 22.13`, the easy half**: the algebra of `L`-twisted matrices is *reduced*. The matrix
unit `e₁₁` of `GPR (22.12.4)` has norm `0` and trace `1`, so it is an elementary idempotent and
`GPR 22.9` applies: the norm is isotropic and the algebra contains a split quadratic étale
subalgebra. No hypothesis on `L`. -/
theorem hasElementaryIdempotent_twistedMat : (twistedMat k L).HasElementaryIdempotent :=
  ⟨(((1, 0), (0, 0)) : (k × Module.Dual k L) × (k × L)),
    (twistedMatNorm_apply (((1, 0), (0, 0)) : TwistedMat k L)).trans (by simp),
    (trace_twistedMat_apply (((1, 0), (0, 0)) : TwistedMat k L)).trans (by simp)⟩

/-! ### `GPR 22.13`: every reduced quaternion algebra is twisted matrices -/

namespace IsElementaryIdempotent

variable {A : Type v} [NonAssocRing A] [Module k A] [SMulCommClass k A A]
  [IsScalarTower k A A] [IsAlternative A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A} {c : A}

/-- The lower-left Peirce component used as the twisting line bundle in `GPR 22.13`. -/
abbrev TwistingModule (c : A) :=
  IsAlternative.peirceComponent (R := k) c true false

/-- The Peirce-coordinate map from twisted matrices to a reduced rank-four composition algebra.
The upper-right coordinate uses the **negative** polar duality, matching the convention
`n([[a,φ],[v,b]]) = ab - φ(v)` in `GPR (22.12.1)`. -/
noncomputable def twistedMatToPeirce (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    TwistedMat k (TwistingModule (k := k) c) →ₗ[k] A := by
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let e := hc.offDiagonalDuality hcomp.isMultiplicative hreg
  exact
    { toFun := fun x ↦ peirceElement c x.1.1 x.2.1 (e.symm (-x.1.2)) x.2.2
      map_add' := fun x y ↦ by
        simp only [TwistedMat.fst_add, TwistedMat.snd_add, Prod.fst_add, Prod.snd_add,
          map_add, map_neg, neg_add_rev, peirceElement, add_smul, Submodule.coe_add]
        module
      map_smul' := fun a x ↦ by
        change peirceElement c (a * x.1.1) (a * x.2.1)
          (e.symm (-(a • x.1.2))) (a • x.2.2) =
            a • peirceElement c x.1.1 x.2.1 (e.symm (-x.1.2)) x.2.2
        rw [show -(a • x.1.2) = a • (-x.1.2) by module, map_smul]
        simp only [peirceElement, mul_smul, Submodule.coe_smul, smul_add] }

@[simp] theorem twistedMatToPeirce_apply (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4)
    (x : TwistedMat k (TwistingModule (k := k) c)) :
    twistedMatToPeirce (k := k) hc hcomp hA x = peirceElement c x.1.1 x.2.1
      ((hc.offDiagonalDuality hcomp.isMultiplicative
        (hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega))).symm (-x.1.2)) x.2.2 := rfl

/-- The Peirce-coordinate map is bijective. This is the additive decomposition and the regular
off-diagonal duality assembled into one map. -/
theorem bijective_twistedMatToPeirce (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    Function.Bijective (twistedMatToPeirce (k := k) hc hcomp hA) := by
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let e := hc.offDiagonalDuality hcomp.isMultiplicative hreg
  constructor
  · intro x y hxy
    have hproj (i j : Bool) := congrArg
      (IsAlternative.peirceProjection (R := k) c i j) hxy
    apply TwistedMat.ext
    · have h := congrArg C.trace (hproj false false)
      rw [twistedMatToPeirce_apply, twistedMatToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      simpa [hc.trace_eq_one] using h
    · have h := hproj false true
      rw [twistedMatToPeirce_apply, twistedMatToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      simpa using h
    · have h := congrArg C.trace (hproj true true)
      rw [twistedMatToPeirce_apply, twistedMatToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_self, false_and, and_false,
        ite_false] at h
      have ht : C.trace (IsAlternative.peirceIdempotent c true) = 1 :=
        (hc.peirceIdempotent true).trace_eq_one
      simpa only [map_smul, ht, smul_eq_mul, mul_one] using h
    · have h := hproj true false
      rw [twistedMatToPeirce_apply, twistedMatToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      simpa using h
  · intro a
    obtain ⟨a₁, a₂, x₁₂, x₂₁, ha⟩ :=
      hc.exists_eq_peirceElement hcomp.isMultiplicative a
    let x : TwistedMat k (TwistingModule (k := k) c) :=
      (((a₁, -(e x₁₂)), (a₂, x₂₁)) :
        (k × Module.Dual k (TwistingModule (k := k) c)) ×
          (k × TwistingModule (k := k) c))
    refine ⟨x, ?_⟩
    rw [ha, twistedMatToPeirce_apply]
    change peirceElement c a₁ a₂ (e.symm (-(-(e x₁₂)))) x₂₁ = _
    rw [neg_neg, e.symm_apply_apply]

/-- The linear equivalence underlying the converse half of `GPR 22.13`. -/
noncomputable def twistedMatEquiv (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    TwistedMat k (TwistingModule (k := k) c) ≃ₗ[k] A :=
  LinearEquiv.ofBijective (twistedMatToPeirce (k := k) hc hcomp hA)
    (bijective_twistedMatToPeirce (k := k) hc hcomp hA)

@[simp] theorem twistedMatEquiv_apply (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4)
    (x : TwistedMat k (TwistingModule (k := k) c)) :
    twistedMatEquiv (k := k) hc hcomp hA x =
      twistedMatToPeirce (k := k) hc hcomp hA x := rfl

/-- The equivalence of `GPR 22.13` preserves the norm. -/
theorem norm_twistedMatEquiv (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4)
    (x : TwistedMat k (TwistingModule (k := k) c)) :
    C.norm (twistedMatEquiv (k := k) hc hcomp hA x) =
      twistedMatNorm k (TwistingModule (k := k) c) x := by
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let e := hc.offDiagonalDuality hcomp.isMultiplicative hreg
  rw [twistedMatEquiv_apply, twistedMatToPeirce_apply,
    hc.norm_peirceElement hcomp.isMultiplicative, twistedMatNorm_apply]
  change x.1.1 * x.2.1 + e (e.symm (-x.1.2)) x.2.2 = _
  rw [e.apply_symm_apply]
  rw [sub_eq_add_neg]
  rfl

/-- The equivalence of `GPR 22.13` is unital. -/
theorem twistedMatEquiv_one (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    twistedMatEquiv (k := k) hc hcomp hA 1 = 1 := by
  rw [twistedMatEquiv_apply, twistedMatToPeirce_apply]
  simp only [TwistedMat.one_fst_fst, TwistedMat.one_fst_snd, TwistedMat.one_snd_fst,
    TwistedMat.one_snd_snd, neg_zero, map_zero]
  simp [peirceElement, IsAlternative.peirceIdempotent]

/-- The equivalence of `GPR 22.13` is multiplicative. -/
theorem twistedMatEquiv_mul (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4)
    (x y : TwistedMat k (TwistingModule (k := k) c)) :
    twistedMatEquiv (k := k) hc hcomp hA (x * y) =
      twistedMatEquiv (k := k) hc hcomp hA x *
        twistedMatEquiv (k := k) hc hcomp hA y := by
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let e := hc.offDiagonalDuality hcomp.isMultiplicative hreg
  rw [twistedMatEquiv_apply, twistedMatEquiv_apply, twistedMatEquiv_apply,
    twistedMatToPeirce_apply, twistedMatToPeirce_apply, twistedMatToPeirce_apply,
    hc.mul_peirceElement_of_rankAtStalk_eq_four hcomp hA]
  simp only [TwistedMat.mul_fst_fst, TwistedMat.mul_fst_snd, TwistedMat.mul_snd_fst,
    TwistedMat.mul_snd_snd]
  have hpolar (f : Module.Dual k (TwistingModule (k := k) c))
      (z : TwistingModule (k := k) c) :
      QuadraticMap.polar C.norm (e.symm (-f)) z = -f z := by
    change e (e.symm (-f)) z = -f z
    rw [e.apply_symm_apply]
    rfl
  congr 1
  · rw [hpolar]
    ring
  · rw [hpolar]
    ring
  · apply e.injective
    simp only [map_add, map_smul]
    ext z
    simp
    abel

/-- The lower-left Peirce component of a reduced rank-four composition algebra is a line bundle,
as required in `GPR 22.13`. -/
theorem invertible_twistingModule (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    Module.Invertible k (TwistingModule (k := k) c) :=
  Module.invertible_iff_isLocallyFreeRankOne.2
    (hc.isLocallyFreeRankOne_offDiagonal hcomp hA true)

/-- The norm isometry underlying the converse half of `GPR 22.13`. -/
noncomputable def twistedMatIsometryEquiv (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    (twistedMat k (TwistingModule (k := k) c)).norm.IsometryEquiv C.norm where
  toLinearEquiv := twistedMatEquiv (k := k) hc hcomp hA
  map_app' := norm_twistedMatEquiv (k := k) hc hcomp hA

/-- **`GPR 22.13`, the converse half**: a reduced composition algebra of constant rank four is
isomorphic to the twisted matrices attached to the line bundle `C₂₁`. -/
theorem isomorphic_twistedMat (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    (twistedMat k (TwistingModule (k := k) c)).Isomorphic C :=
  ⟨twistedMatIsometryEquiv (k := k) hc hcomp hA,
    twistedMatEquiv_one (k := k) hc hcomp hA,
    twistedMatEquiv_mul (k := k) hc hcomp hA⟩

end IsElementaryIdempotent

/-! ### A twisted matrix algebra on a free line is split -/

variable {L : Type v} [AddCommGroup L] [Module k L]

/-- Coordinates from twisted matrices on a based line to ordinary two-by-two matrices. -/
noncomputable def twistedMatOfBasisEquiv (b : Module.Basis Unit k L) :
    TwistedMat k L ≃ₗ[k] Matrix (Fin 2) (Fin 2) k where
  toFun x := !![x.1.1, x.1.2 (b ()); b.repr x.2.2 (), x.2.1]
  invFun A := ((A 0 0, A 0 1 • b.dualBasis ()), (A 1 1, A 1 0 • b ()))
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a x := by ext i j; fin_cases i <;> fin_cases j <;> simp
  left_inv x := by
    apply TwistedMat.ext
    · rfl
    · ext z
      rw [← b.sum_repr z]
      simp
    · rfl
    · rw [← b.sum_repr x.2.2]
      simp
  right_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

@[simp] theorem twistedMatOfBasisEquiv_apply (b : Module.Basis Unit k L)
    (x : TwistedMat k L) :
    twistedMatOfBasisEquiv k b x = !![x.1.1, x.1.2 (b ()); b.repr x.2.2 (), x.2.1] := rfl

/-- The coordinate equivalence from twisted matrices on a based line preserves the norm. -/
theorem det_twistedMatOfBasisEquiv (b : Module.Basis Unit k L) (x : TwistedMat k L) :
    Matrix.det (twistedMatOfBasisEquiv k b x) = twistedMatNorm k L x := by
  rw [twistedMatOfBasisEquiv_apply, Matrix.det_fin_two, twistedMatNorm_apply]
  have hv := b.sum_repr x.2.2
  simp only [Fintype.sum_unique] at hv
  rw [← hv]
  simp
  ring

/-- The coordinate equivalence from twisted matrices on a based line preserves the identity. -/
theorem twistedMatOfBasisEquiv_one (b : Module.Basis Unit k L) :
    twistedMatOfBasisEquiv k b (1 : TwistedMat k L) = 1 := by
  rw [twistedMatOfBasisEquiv_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The coordinate equivalence from twisted matrices on a based line preserves multiplication. -/
theorem twistedMatOfBasisEquiv_mul (b : Module.Basis Unit k L) (x y : TwistedMat k L) :
    twistedMatOfBasisEquiv k b (x * y) =
      twistedMatOfBasisEquiv k b x * twistedMatOfBasisEquiv k b y := by
  have hx := b.sum_repr x.2.2
  have hy := b.sum_repr y.2.2
  simp only [Fintype.sum_unique] at hx hy
  have hx_eval (f : Module.Dual k L) : f x.2.2 = b.repr x.2.2 () * f (b ()) := by
    rw [← hx]
    simp
  have hy_eval (f : Module.Dual k L) : f y.2.2 = b.repr y.2.2 () * f (b ()) := by
    rw [← hy]
    simp
  rw [twistedMatOfBasisEquiv_apply, twistedMatOfBasisEquiv_apply,
    twistedMatOfBasisEquiv_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hy_eval]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hx_eval]
    ring

/-- **The splitness assertion in `GPR 22.13`:** twisted matrices on a free line are the split
quaternion algebra. -/
theorem isomorphic_twistedMat_ofBasis (b : Module.Basis Unit k L) :
    (twistedMat k L).Isomorphic (splitQuaternion k) :=
  ⟨⟨twistedMatOfBasisEquiv k b, by
      intro x
      rw [splitQuaternion_norm, twistedMat_norm, splitQuaternionNorm_apply]
      exact det_twistedMatOfBasisEquiv k b x⟩,
    twistedMatOfBasisEquiv_one k b, twistedMatOfBasisEquiv_mul k b⟩

end ConicAlgebra

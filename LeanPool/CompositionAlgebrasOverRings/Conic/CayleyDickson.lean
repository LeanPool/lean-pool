/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The Cayley–Dickson construction (`GPR 18.3`, `GPR 18.4`)

Given a conic algebra `B` over `k` and a scalar `μ ∈ k`, the **Cayley–Dickson double**
`Cay(B, μ)` is the `k`-module `B ⊕ B`, written `u + v j`, with

  `(u₁ + v₁ j)(u₂ + v₂ j) = (u₁u₂ + μ (conj v₂)v₁) + (v₂u₁ + v₁(conj u₂)) j`,   `1 = 1_B + 0 j`,
  `n(u + v j) = n_B(u) - μ n_B(v)`.

It is again a conic algebra (`ConicAlgebra.cay`, `GPR 18.4`), and its trace and conjugation are

  `t(u + v j) = t_B(u)`,   `conj (u + v j) = conj u - v j`.

## Main definitions

* `ConicAlgebra.Cay C μ` : the underlying `k`-module `B ⊕ B`, as a type synonym carrying the
  Cayley–Dickson multiplication rather than the componentwise one.
* `ConicAlgebra.cay` : **`GPR 18.4`** — the conic algebra structure on `Cay C μ`.

## Main results

* `ConicAlgebra.cay_norm_apply`, `ConicAlgebra.cay_trace_apply`, `ConicAlgebra.cay_conj_apply` :
  the formulas `GPR 18.4(3)`, `(5)`, `(6)`.
* `ConicAlgebra.cayIsometryEquiv` : a norm isometry acts componentwise on doubles; if it is
  unital and multiplicative, so is the doubled equivalence.
* `ConicAlgebra.cayIsometryEquivOfEq` : transport between doubles whose parameters are equal.
* `ConicAlgebra.inl` : the embedding `B ↪ Cay C μ` of `GPR 18.3`, a unital algebra map.

## Implementation notes

**`μ` is an arbitrary scalar, not a unit.** Everything here holds for every `μ ∈ k`, including
`0`; hypotheses that `μ` be invertible belong to later theorems (`GPR 18.11` ff.), never to the
construction.

**No hypotheses on `B` beyond conic.** The degree-two identity for `Cay(B, μ)` needs exactly two
facts about `B`: `(conj v)v = n(v) · 1` (`ConicAlgebra.conj_mul_self`) and `u + conj u = t(u) · 1`
(`ConicAlgebra.add_conj`), both of which hold in every conic algebra with no regularity,
projectivity, alternativity or assumption on `2`. In particular the norm is written down directly,
so — unlike `ConicAlgebra.baseChangeOfProjective` — nothing here needs `B` to be projective.

**Why a type synonym.** `B × B` already carries the componentwise ring structure from mathlib, and
the Cayley–Dickson multiplication is a different one, so it must live on a synonym. The synonym
depends on the conic structure `C`, not just on `B`, because the multiplication uses the
conjugation of `B`; two conic structures on the same `B` double to genuinely different algebras.

**External, not internal.** `GPR 18.1` builds `B + Bl` inside an ambient algebra; `GPR 18.2` warns
that this sum need not be direct. The external construction on `B ⊕ B` has no such problem and is
the one used here and in `GPR 18.3` ff.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.1–18.4.
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {k : Type u} {B : Type v} [CommRing k] [NonAssocRing B] [Module k B]
  [SMulCommClass k B B] [IsScalarTower k B B]

/-- The underlying `k`-module `B ⊕ B` of the Cayley–Dickson double `Cay(B, μ)`, as a type synonym:
`B × B` already has the componentwise multiplication, and this one is different. The element
`(u, v)` is `GPR`'s `u + v j`.

The parameters `C` and `μ` are part of the type even though the underlying module does not depend
on them: the multiplication does, so distinct parameters must give distinct types for instance
resolution to be sound. -/
def Cay (_C : ConicAlgebra k B) (_μ : k) : Type v := B × B

variable (C : ConicAlgebra k B) (μ : k)

namespace Cay

omit [SMulCommClass k B B] [IsScalarTower k B B]

instance : AddCommGroup (Cay C μ) := inferInstanceAs (AddCommGroup (B × B))
instance : Module k (Cay C μ) := inferInstanceAs (Module k (B × B))

/-- The double of a finitely generated module is finitely generated: rank doubles, so a
composition algebra of rank `d` doubles to one of rank `2d`. -/
instance [Module.Finite k B] : Module.Finite k (Cay C μ) :=
  inferInstanceAs (Module.Finite k (B × B))

/-- The double of a projective module is projective, which is what keeps the Cayley–Dickson tower
inside the composition algebras. -/
instance [Module.Projective k B] : Module.Projective k (Cay C μ) :=
  inferInstanceAs (Module.Projective k (B × B))

/-- The double of a free module is free. -/
instance [Module.Free k B] : Module.Free k (Cay C μ) :=
  inferInstanceAs (Module.Free k (B × B))

/-- **The rank doubles.** This is what makes the Cayley–Dickson tower run through ranks
`1, 2, 4, 8` (`GPR 19.18`). -/
theorem finrank_cay [Nontrivial k] [Module.Free k B] [Module.Finite k B] :
    Module.finrank k (Cay C μ) = 2 * Module.finrank k B :=
  (Module.finrank_prod (R := k) (M := B) (M' := B)).trans (by ring)

variable {C μ}

@[simp] theorem fst_add (x y : Cay C μ) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem snd_add (x y : Cay C μ) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem fst_zero : (0 : Cay C μ).1 = 0 := rfl
@[simp] theorem snd_zero : (0 : Cay C μ).2 = 0 := rfl
@[simp] theorem fst_neg (x : Cay C μ) : (-x).1 = -x.1 := rfl
@[simp] theorem snd_neg (x : Cay C μ) : (-x).2 = -x.2 := rfl
@[simp] theorem fst_sub (x y : Cay C μ) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem snd_sub (x y : Cay C μ) : (x - y).2 = x.2 - y.2 := rfl
@[simp] theorem fst_smul (c : k) (x : Cay C μ) : (c • x).1 = c • x.1 := rfl
@[simp] theorem snd_smul (c : k) (x : Cay C μ) : (c • x).2 = c • x.2 := rfl

theorem ext {x y : Cay C μ} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := Prod.ext h₁ h₂

/-- The element `u + v j` of `Cay(B, μ)`, with components `u` and `v`. Writing explicit elements
with `Cay.mk` rather than as a bare pair keeps their type `Cay C μ` visible, so that the lemmas
about the doubled multiplication apply to them. -/
def mk (u v : B) : Cay C μ := (u, v)

@[simp] theorem fst_mk (u v : B) : (mk u v : Cay C μ).1 = u := rfl
@[simp] theorem snd_mk (u v : B) : (mk u v : Cay C μ).2 = v := rfl

variable (C μ)

/-- The **Cayley–Dickson multiplication** `GPR 18.3`:
`(u₁ + v₁j)(u₂ + v₂j) = (u₁u₂ + μ (conj v₂)v₁) + (v₂u₁ + v₁(conj u₂)) j`. -/
instance : Mul (Cay C μ) :=
  ⟨fun x y ↦ ((x.1 * y.1 + μ • (C.conj y.2 * x.2), y.2 * x.1 + x.2 * C.conj y.1) : B × B)⟩

instance : One (Cay C μ) := ⟨((1, 0) : B × B)⟩

variable {C μ}

@[simp] theorem fst_mul (x y : Cay C μ) : (x * y).1 = x.1 * y.1 + μ • (C.conj y.2 * x.2) := rfl
@[simp] theorem snd_mul (x y : Cay C μ) : (x * y).2 = y.2 * x.1 + x.2 * C.conj y.1 := rfl
@[simp] theorem fst_one : (1 : Cay C μ).1 = 1 := rfl
@[simp] theorem snd_one : (1 : Cay C μ).2 = 0 := rfl

variable (C μ)

instance : NonAssocRing (Cay C μ) :=
  { (inferInstance : AddCommGroup (Cay C μ)), (inferInstance : Mul (Cay C μ)),
    (inferInstance : One (Cay C μ)) with
    left_distrib := fun x y z ↦ Cay.ext (by simp [mul_add, add_mul, smul_add]; abel)
      (by simp [mul_add, add_mul]; abel)
    right_distrib := fun x y z ↦ Cay.ext (by simp [mul_add, add_mul, smul_add]; abel)
      (by simp [mul_add, add_mul]; abel)
    zero_mul := fun x ↦ Cay.ext (by simp) (by simp)
    mul_zero := fun x ↦ Cay.ext (by simp) (by simp)
    one_mul := fun x ↦ Cay.ext (by simp) (by simp)
    mul_one := fun x ↦ Cay.ext (by simp) (by simp) }

instance : SMulCommClass k (Cay C μ) (Cay C μ) :=
  ⟨fun c x y ↦ Cay.ext
    (by simp [mul_smul_comm, smul_mul_assoc, smul_comm c μ])
    (by simp [mul_smul_comm, smul_mul_assoc])⟩

instance : IsScalarTower k (Cay C μ) (Cay C μ) :=
  ⟨fun c x y ↦ Cay.ext
    (by simp [mul_smul_comm, smul_mul_assoc, smul_comm c μ])
    (by simp [mul_smul_comm, smul_mul_assoc])⟩

end Cay

/-! ### The conic structure -/

/-- The Cayley–Dickson norm `n(u + v j) = n_B(u) - μ n_B(v)`, i.e. `n_B ⊥ ⟨-μ⟩ n_B`. -/
noncomputable def cayNorm : QuadraticForm k (Cay C μ) :=
  (QuadraticMap.prod C.norm ((-μ) • C.norm) : QuadraticForm k (B × B))

variable {C μ}

omit [SMulCommClass k B B] [IsScalarTower k B B] in
@[simp] theorem cayNorm_apply (x : Cay C μ) :
    C.cayNorm μ x = C.norm x.1 - μ * C.norm x.2 := by
  change C.norm x.1 + ((-μ) • C.norm) x.2 = _
  rw [smul_apply, smul_eq_mul]
  ring

omit [SMulCommClass k B B] [IsScalarTower k B B] in
theorem polar_cayNorm (x y : Cay C μ) :
    QuadraticMap.polar (C.cayNorm μ) x y =
      QuadraticMap.polar C.norm x.1 y.1 - μ * QuadraticMap.polar C.norm x.2 y.2 := by
  simp only [QuadraticMap.polar, cayNorm_apply, Cay.fst_add, Cay.snd_add]
  ring

variable (C μ)

/-- **`GPR 18.4`: the Cayley–Dickson double of a conic algebra is a conic algebra.**

The first component of `x * x` is `u² + μ (conj v)v = t(u)·u - n(u)·1 + μ n(v)·1`, and the second is
`vu + v(conj u) = v(u + conj u) = t(u)·v`. No hypothesis on `B` or on `μ`. -/
noncomputable def cay : ConicAlgebra k (Cay C μ) where
  norm := C.cayNorm μ
  norm_one := by simp [C.norm_one]
  mul_self x := by
    have htrace : QuadraticMap.polar (C.cayNorm μ) 1 x = C.trace x.1 := by
      rw [polar_cayNorm]
      simp [trace_apply]
    refine Cay.ext ?_ ?_
    · rw [Cay.fst_mul, Cay.fst_sub, Cay.fst_smul, Cay.fst_smul, htrace, cayNorm_apply,
        Cay.fst_one, C.mul_self_eq x.1, C.conj_mul_self x.2]
      module
    · rw [Cay.snd_mul, Cay.snd_sub, Cay.snd_smul, Cay.snd_smul, htrace, Cay.snd_one,
        smul_zero, sub_zero, ← mul_add, C.add_conj x.1, mul_smul_comm, mul_one]

variable {C μ}

@[simp] theorem cay_norm_apply (x : Cay C μ) :
    (C.cay μ).norm x = C.norm x.1 - μ * C.norm x.2 :=
  cayNorm_apply x

/-- **`GPR 18.4(5)`.** The trace of `Cay(B, μ)` is the trace of `B` on the first component. -/
@[simp] theorem cay_trace_apply (x : Cay C μ) : (C.cay μ).trace x = C.trace x.1 := by
  rw [trace_apply]
  change QuadraticMap.polar (C.cayNorm μ) 1 x = _
  rw [polar_cayNorm]
  simp [trace_apply]

/-- **`GPR 18.4(6)`.** The conjugation of `Cay(B, μ)` is `u + v j ↦ conj u - v j`. -/
@[simp] theorem cay_conj_apply (x : Cay C μ) :
    (C.cay μ).conj x = ((C.conj x.1, -x.2) : Cay C μ) := by
  refine Cay.ext ?_ ?_
  · rw [conj_apply, Cay.fst_sub, Cay.fst_smul, cay_trace_apply, Cay.fst_one, conj_apply]
  · rw [conj_apply, Cay.snd_sub, Cay.snd_smul, Cay.snd_one, smul_zero, zero_sub]

/-- `GPR 18.4(6)` on an explicit element: the conjugate of `u + v j` is `conj u - v j`.

Not a simp lemma, since `cay_conj_apply` already rewrites its left-hand side; it is for `simp only`
calls that keep elements in `Cay.mk` form. -/
theorem cay_conj_mk (u v : B) :
    (C.cay μ).conj (Cay.mk u v) = Cay.mk (C.conj u) (-v) := by
  rw [cay_conj_apply]
  rfl

/-! ### Functoriality -/

section Functoriality

variable {B' : Type w} [NonAssocRing B'] [Module k B'] [SMulCommClass k B' B']
  [IsScalarTower k B' B'] (D : ConicAlgebra k B')

/-- Equal Cayley–Dickson parameters give canonically isometric doubles. This explicit transport is
needed because the parameter is part of the type `Cay C μ`. -/
noncomputable def cayIsometryEquivOfEq {a b : k} (h : a = b) :
    (D.cay a).norm.IsometryEquiv (D.cay b).norm := by
  subst b
  exact QuadraticMap.IsometryEquiv.refl _

@[simp] theorem cayIsometryEquivOfEq_map_one {a b : k} (h : a = b) :
    cayIsometryEquivOfEq D h (1 : Cay D a) = 1 := by
  subst b
  rfl

theorem cayIsometryEquivOfEq_map_mul {a b : k} (h : a = b) (x y : Cay D a) :
    cayIsometryEquivOfEq D h (x * y) =
      cayIsometryEquivOfEq D h x * cayIsometryEquivOfEq D h y := by
  subst b
  rfl

/-- A norm isometry acts componentwise on Cayley–Dickson doubles with the same parameter.

No unitality or multiplicativity is needed for this statement: the doubled norm is the
orthogonal product `n ⊥ (-μ)n`. -/
noncomputable def cayIsometryEquiv (e : C.norm.IsometryEquiv D.norm) :
    (C.cay μ).norm.IsometryEquiv (D.cay μ).norm where
  toLinearEquiv :=
    { toFun := fun x ↦ ((e x.1, e x.2) : Cay D μ)
      invFun := fun x ↦ ((e.symm x.1, e.symm x.2) : Cay C μ)
      map_add' := fun x y ↦ Cay.ext (map_add e x.1 y.1) (map_add e x.2 y.2)
      map_smul' := fun c x ↦ Cay.ext (map_smul e c x.1) (map_smul e c x.2)
      left_inv := fun x ↦ Cay.ext (e.symm_apply_apply x.1) (e.symm_apply_apply x.2)
      right_inv := fun x ↦ Cay.ext (e.apply_symm_apply x.1) (e.apply_symm_apply x.2) }
  map_app' x :=
    (cay_norm_apply ((e x.1, e x.2) : Cay D μ)).trans (by
      rw [e.map_app, e.map_app]
      exact (cay_norm_apply x).symm)

@[simp] theorem cayIsometryEquiv_apply (e : C.norm.IsometryEquiv D.norm) (x : Cay C μ) :
    cayIsometryEquiv D e x = ((e x.1, e x.2) : Cay D μ) := rfl

/-- The componentwise equivalence of doubles is unital when the original equivalence is. -/
theorem cayIsometryEquiv_map_one (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : B) = 1) : cayIsometryEquiv D e (1 : Cay C μ) = 1 :=
  Cay.ext h1 (map_zero e)

/-- The componentwise equivalence of doubles is multiplicative when the original equivalence is
unital and multiplicative. -/
theorem cayIsometryEquiv_map_mul (e : C.norm.IsometryEquiv D.norm)
    (h1 : e (1 : B) = 1) (hmul : ∀ x y, e (x * y) = e x * e y) (x y : Cay C μ) :
    cayIsometryEquiv D e (x * y) = cayIsometryEquiv D e x * cayIsometryEquiv D e y := by
  have htrace (z : B) : D.trace (e z) = C.trace z := by
    rw [trace_apply, trace_apply, QuadraticMap.polar, QuadraticMap.polar]
    rw [show (1 : B') = e (1 : B) from h1.symm, ← map_add, e.map_app, e.map_app, e.map_app]
  have hconj (z : B) : D.conj (e z) = e (C.conj z) := by
    rw [conj_apply, conj_apply, htrace, map_sub, map_smul, h1]
  apply Cay.ext
  · change e (x.1 * y.1 + μ • (C.conj y.2 * x.2)) =
      e x.1 * e y.1 + μ • (D.conj (e y.2) * e x.2)
    rw [map_add, map_smul, hmul, hmul, hconj]
  · change e (y.2 * x.1 + x.2 * C.conj y.1) =
      e y.2 * e x.1 + e x.2 * D.conj (e y.1)
    rw [map_add, hmul, hmul, hconj]

end Functoriality

/-! ### `GPR 18.11`: the conjugation of the double -/

/-- **`GPR 18.11`.** If the conjugation of `B` is an involution then so is the conjugation of
`Cay(B, μ)`. No associativity and no hypothesis on `μ`: the verification is the two component
identities `conj(u₁u₂ + μ (conj v₂)v₁) = (conj u₂)(conj u₁) + μ (conj v₁)v₂` and
`-(v₂u₁ + v₁(conj u₂)) = -v₂u₁ - v₁(conj u₂)`. -/
theorem ConjIsInvolution.cay (hconj : C.ConjIsInvolution) : (C.cay μ).ConjIsInvolution := by
  intro x y
  rw [cay_conj_apply, cay_conj_apply, cay_conj_apply]
  refine Cay.ext ?_ ?_
  · change C.conj (x.1 * y.1 + μ • (C.conj y.2 * x.2))
      = C.conj y.1 * C.conj x.1 + μ • (C.conj (-x.2) * -y.2)
    rw [map_add, map_smul, hconj, hconj, conj_conj, map_neg, neg_mul_neg]
  · change -(y.2 * x.1 + x.2 * C.conj y.1)
      = -x.2 * C.conj y.1 + -y.2 * C.conj (C.conj x.1)
    rw [conj_conj, neg_mul, neg_mul, neg_add]
    abel

/-! ### The embedding of `B` -/

variable (C μ)

/-- **`GPR 18.3`.** The embedding `u ↦ u + 0 j` of `B` into `Cay(B, μ)`. It is injective, unital
and multiplicative, so `B` is a unital subalgebra of its double. -/
def inl : B →ₗ[k] Cay C μ where
  toFun u := ((u, 0) : B × B)
  map_add' u u' := Cay.ext rfl (by change (0 : B) = 0 + 0; rw [add_zero])
  map_smul' c u := Cay.ext rfl (by change (0 : B) = c • (0 : B); rw [smul_zero])

variable {C μ}

omit [SMulCommClass k B B] [IsScalarTower k B B] in
@[simp] theorem inl_apply (u : B) : C.inl μ u = ((u, 0) : Cay C μ) := rfl

omit [SMulCommClass k B B] [IsScalarTower k B B] in
theorem inl_one : C.inl μ 1 = 1 := rfl

omit [SMulCommClass k B B] [IsScalarTower k B B] in
theorem inl_mul (u u' : B) : C.inl μ (u * u') = C.inl μ u * C.inl μ u' :=
  Cay.ext (by change u * u' = u * u' + μ • (C.conj 0 * 0); simp)
    (by change (0 : B) = 0 * u + 0 * C.conj u'; simp)

omit [SMulCommClass k B B] [IsScalarTower k B B] in
theorem inl_injective : Function.Injective (C.inl μ) := fun _ _ h ↦ congrArg Prod.fst h

theorem norm_inl (u : B) : (C.cay μ).norm (C.inl μ u) = C.norm u := by
  rw [cay_norm_apply]
  change C.norm u - μ * C.norm 0 = C.norm u
  simp

end ConicAlgebra

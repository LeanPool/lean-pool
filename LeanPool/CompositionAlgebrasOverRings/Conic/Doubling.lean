/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDickson
public import LeanPool.CompositionAlgebrasOverRings.Conic.Subalgebra
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Moufang
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity

/-!
# Doubling inside an ambient conic algebra (`GPR 18.1`)

Let `A` be a conic **alternative** algebra, `B ⊆ A` a unital subalgebra, and `v ∈ A` an element
**orthogonal to `B`** — `n(b, v) = 0` for every `b ∈ B` — whose norm is a unit. Then the three
identities

  `x(yv) = (yx)v`,   `(xv)y = (x (conj y))v`,   `(xv)(yv) = -n(v) ((conj y) x)`   (`x, y ∈ B`)

hold. They are exactly the three clauses of the Cayley–Dickson multiplication
`(u₁ + v₁j)(u₂ + v₂j) = (u₁u₂ + μ (conj v₂)v₁) + (v₂u₁ + v₁(conj u₂)) j` with `μ = -n(v)`, so
`B + Bv` is a copy of `Cay(B, μ)` sitting inside `A`. `Conic/CayleyDickson.lean` builds `Cay(B, μ)`
externally; this file is the internal counterpart, and the comparison between the two is
`ConicAlgebra.cayToAlgebra`.

## The mechanism

Everything rests on one unconditional observation. The linearized degree-two identity
`xy + yx = t(x)y + t(y)x - n(x,y)·1` (`ConicAlgebra.mul_add_mul`, valid in *every* conic algebra)
collapses, for `x ∈ B` and `v ⊥ B`, to

  `xv = v (conj x)`,   `vx = (conj x) v`

(`ConicAlgebra.mul_eq_mul_conj`, `ConicAlgebra.mul_eq_conj_mul`): orthogonality to `B` turns
multiplication by `v` into a twisted commutation rule. Note `1 ∈ B`, so `t(v) = n(1, v) = 0` and
hence `conj v = -v` and `v² = -n(v)·1`.

Given that rule, the three identities follow from the alternative laws alone — the alternating
property of the associator, the middle Moufang identity `(ab)(ca) = a(bc)a`, and flexibility —
together with `n(v)` being a unit, which lets right multiplication by `v` be cancelled:
`(zv)v = -n(v)z`.

## Why no regularity hypothesis

`GPR 19.3` produces alternativity of a composition algebra from the vanishing of the *radical* of
its norm, which over a general commutative ring is not implied by non-singularity (see
`Composition/Basic.lean`). Alternativity is therefore assumed here rather than derived, as an honest
hypothesis on a conic algebra. For a composition algebra it is automatic over every commutative ring
(`ConicAlgebra.IsComposition.isAlternative_general`, `Composition/Alternative.lean`, which this
layer may not import).

What is *not* assumed is any regularity of the norm — not on `A`, not on `B`. The three identities
below are cancellation statements proved by multiplying by `v` and using `n(v) ∈ kˣ`, so no
non-degeneracy of the ambient norm is used anywhere. Nor is `B` assumed associative, nor
multiplicativity of the norm; those enter only when the norm of the doubled algebra is computed.

## Main definitions

* `ConicAlgebra.cayToAlgebra` : the map `Cay(B, -n(v)) → A`, `u + wj ↦ u + wv`.

## Main results

* `ConicAlgebra.mul_eq_mul_conj`, `ConicAlgebra.mul_eq_conj_mul` : the commutation rule
  `xv = v (conj x)`, `vx = (conj x) v` for `x ∈ B`, in any conic algebra whatsoever.
* `ConicAlgebra.mul_mul_orthogonal` : `x(yv) = (yx)v`, `GPR 18.1(1)`.
* `ConicAlgebra.mul_orthogonal_mul` : `(xv)y = (x (conj y))v`, `GPR 18.1(2)`.
* `ConicAlgebra.mul_orthogonal_mul_mul_orthogonal` : `(xv)(yv) = -n(v)((conj y)x)`, `GPR 18.1(3)`.
* `ConicAlgebra.cayToAlgebra_mul` : **`GPR 18.1`** — the doubling map is multiplicative, so
  `B + Bv` is a copy of `Cay(B, -n(v))` inside `A`.
* `ConicAlgebra.norm_cayToAlgebra` : it is an isometry for the Cayley–Dickson norm. This is where
  multiplicativity of `n` is used, through `B ⊥ Bv`.
* `ConicAlgebra.cayToAlgebra_injective` : it is injective when `n|_B` is regular.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.1, 18.3.
-/

@[expose] public section

universe u v

open QuadraticMap (polar)

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] {C : ConicAlgebra k A} {v : A}

/-! ### An element of trace zero -/

section TraceZero

variable (htv : C.trace v = 0)
include htv

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- An element of trace zero is the negative of its conjugate. -/
theorem conj_eq_neg_of_trace_eq_zero : C.conj v = -v := by
  rw [conj_apply, htv, zero_smul, zero_sub]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The degree-two identity for an element of trace zero: `v² = -n(v)·1`. -/
theorem mul_self_of_trace_eq_zero : v * v = -(C.norm v • (1 : A)) := by
  rw [C.mul_self_eq, htv, zero_smul, zero_sub]

variable [IsAlternative A]

omit [IsScalarTower k A A] in
/-- **Right multiplication by `v` squares to `-n(v)`**: `(zv)v = -n(v)·z`, for `v` of trace zero
and *any* `z`. This is the cancellation device of the whole file; it consumes right alternativity
and nothing else. -/
theorem mul_mul_self_of_trace_eq_zero (z : A) : z * v * v = -(C.norm v • z) := by
  rw [IsAlternative.mul_self_mul_right, mul_self_of_trace_eq_zero htv, mul_neg, mul_smul_comm,
    mul_one]

omit [IsScalarTower k A A] in
/-- **Cancelling `v`.** If `n(v)` is a unit then right multiplication by `v` is injective, so an
element killed by `v` is zero. -/
theorem eq_zero_of_mul_eq_zero (hu : IsUnit (C.norm v)) {d : A} (hd : d * v = 0) : d = 0 := by
  have h := mul_mul_self_of_trace_eq_zero htv d
  rw [hd, zero_mul, eq_comm, neg_eq_zero] at h
  obtain ⟨w, hw⟩ := hu
  calc d = ((w⁻¹ : kˣ) : k) • ((w : k) • d) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = 0 := by rw [hw, h, smul_zero]

end TraceZero

/-! ### An element orthogonal to a subalgebra -/

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- A unital subalgebra is closed under conjugation, since `conj b = t(b)·1 - b`. -/
theorem conj_mem {B : NonAssocSubalgebra k A} {b : A} (hb : b ∈ B) : C.conj b ∈ B := by
  rw [conj_apply]
  exact sub_mem (SMulMemClass.smul_mem _ (show (1 : A) ∈ B from B.one_mem)) hb

section Orthogonal

variable {B : NonAssocSubalgebra k A} (hBv : ∀ b ∈ B, polar C.norm b v = 0)
include hBv

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- An element orthogonal to a unital subalgebra has trace zero: the unit lies in the
subalgebra, and `t(v) = n(1, v)`. -/
theorem trace_eq_zero_of_orthogonal : C.trace v = 0 :=
  (C.trace_apply v).trans (hBv 1 B.one_mem)

omit [IsScalarTower k A A] in
/-- **The commutation rule**, first form: `xv = v (conj x)` for `x ∈ B` and `v ⊥ B`.

This holds in every conic algebra — no alternativity, no regularity, no hypothesis on `2`. It is
the linearized degree-two identity `xy + yx = t(x)y + t(y)x - n(x,y)·1` with `y = v`, where both
`t(v)` and `n(x, v)` vanish. -/
theorem mul_eq_mul_conj {x : A} (hx : x ∈ B) : x * v = v * C.conj x := by
  have hlin := C.mul_add_mul x v
  rw [trace_eq_zero_of_orthogonal hBv, hBv x hx, zero_smul, zero_smul, sub_zero, add_zero] at hlin
  rw [conj_apply, mul_sub, mul_smul_comm, mul_one]
  linear_combination (norm := module) hlin

omit [SMulCommClass k A A] in
/-- **The commutation rule**, second form: `vx = (conj x) v` for `x ∈ B` and `v ⊥ B`. -/
theorem mul_eq_conj_mul {x : A} (hx : x ∈ B) : v * x = C.conj x * v := by
  have hlin := C.mul_add_mul x v
  rw [trace_eq_zero_of_orthogonal hBv, hBv x hx, zero_smul, zero_smul, sub_zero, add_zero] at hlin
  rw [conj_apply, sub_mul, smul_mul_assoc, one_mul]
  linear_combination (norm := module) hlin

variable [IsAlternative A]

/-- Conjugating by `v`: `(vc)v = -n(v) (conj c)` for `c ∈ B`. -/
theorem mul_mul_eq_neg_smul_conj {c : A} (hc : c ∈ B) :
    v * c * v = -(C.norm v • C.conj c) := by
  rw [mul_eq_conj_mul hBv hc,
    mul_mul_self_of_trace_eq_zero (trace_eq_zero_of_orthogonal hBv) (C.conj c)]

variable (hconj : C.ConjIsInvolution)
include hconj

omit [IsScalarTower k A A] [IsAlternative A] in
/-- `xv` has trace zero for `x ∈ B`: conjugation negates it. -/
theorem conj_mul_orthogonal {x : A} (hx : x ∈ B) : C.conj (x * v) = -(x * v) := by
  rw [hconj, conj_eq_neg_of_trace_eq_zero (trace_eq_zero_of_orthogonal hBv), neg_mul,
    ← mul_eq_mul_conj hBv hx]

/-- `(xv)(vy) = -n(v)(yx)` for `x, y ∈ B`.

The two commutation rules put the product in the shape `(vb)(cv)` of the middle Moufang identity
`(ab)(ca) = a(bc)a`, and flexibility then turns `v(bc)v` into a single conjugation by `v`. -/
theorem mul_orthogonal_mul_orthogonal_mul {x y : A} (hx : x ∈ B) (hy : y ∈ B) :
    x * v * (v * y) = -(C.norm v • (y * x)) := by
  rw [mul_eq_mul_conj hBv hx, mul_eq_conj_mul hBv hy, IsAlternative.middle_moufang,
    ← IsAlternative.flexible,
    mul_mul_eq_neg_smul_conj hBv (mul_mem (conj_mem hx) (conj_mem hy)), hconj, conj_conj,
    conj_conj]

/-- **`GPR 18.1(3)`**: `(xv)(yv) = -n(v)((conj y)x)` for `x, y ∈ B`.

This is the first component of the Cayley–Dickson product `(0 + v₁j)(0 + v₂j) = μ (conj v₂)v₁`, with
`μ = -n(v)`. -/
theorem mul_orthogonal_mul_mul_orthogonal {x y : A} (hx : x ∈ B) (hy : y ∈ B) :
    x * v * (y * v) = -(C.norm v • (C.conj y * x)) := by
  rw [mul_eq_mul_conj hBv hy, mul_orthogonal_mul_orthogonal_mul hBv hconj hx (conj_mem hy)]

variable (hu : IsUnit (C.norm v))
include hu

/-- **`GPR 18.1(1)`**: `x(yv) = (yx)v` for `x, y ∈ B`.

Both sides are cancelled against `v` on the right: `((yx)v)v = -n(v)(yx)` at once, while
`(x(yv))v` is unwound by moving the associator `⁅x, yv, v⁆` around its cyclic orbit to
`⁅yv, v, x⁆`, whose two terms are `-n(v)(yx)` and `-n(v)(xy)`. The `xy` terms cancel. -/
theorem mul_mul_orthogonal {x y : A} (hx : x ∈ B) (hy : y ∈ B) :
    x * (y * v) = y * x * v := by
  have htv := trace_eq_zero_of_orthogonal hBv
  refine sub_eq_zero.mp (eq_zero_of_mul_eq_zero htv hu ?_)
  have hcyc : associator x (y * v) v = associator (y * v) v x := by
    rw [IsAlternative.associator_swap_left, IsAlternative.associator_swap_right, neg_neg]
  simp only [associator] at hcyc
  rw [mul_mul_self_of_trace_eq_zero htv y,
    mul_orthogonal_mul_orthogonal_mul hBv hconj hy hx] at hcyc
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc] at hcyc
  have key : x * (y * v) * v = -(C.norm v • (y * x)) := by
    linear_combination (norm := module) hcyc
  rw [sub_mul, key, mul_mul_self_of_trace_eq_zero htv (y * x), sub_self]

/-- **`GPR 18.1(2)`**: `(xv)y = (x (conj y))v` for `x, y ∈ B`.

Conjugating `GPR 18.1(1)` at the pair `(conj y, x)` turns it into this, because conjugation is an
anti-homomorphism and negates every element of `Bv`. -/
theorem mul_orthogonal_mul {x y : A} (hx : x ∈ B) (hy : y ∈ B) :
    x * v * y = x * C.conj y * v := by
  have h := congrArg C.conj (mul_mul_orthogonal hBv hconj hu (conj_mem (C := C) hy) hx)
  have hl : C.conj (C.conj y * (x * v)) = -(x * v * y) := by
    rw [hconj, conj_mul_orthogonal hBv hconj hx, conj_conj, neg_mul]
  have hr : C.conj (x * C.conj y * v) = -(x * C.conj y * v) :=
    conj_mul_orthogonal hBv hconj (mul_mem hx (conj_mem (C := C) hy))
  rw [hl, hr] at h
  exact neg_inj.mp h

end Orthogonal

/-! ### The comparison with the external double -/

section Cay

/-- **The internal doubling map** `Cay(B, -n(v)) → A`, `u + wj ↦ u + wv` (`GPR 18.1`).

It is defined for every `v`, with no orthogonality or invertibility hypothesis; those are what make
it multiplicative (`ConicAlgebra.cayToAlgebra_mul`) and injective
(`ConicAlgebra.cayToAlgebra_injective`). The Cayley–Dickson scalar is forced to be `-n(v)`, which
is `GPR 18.1`'s `μ`. -/
def cayToAlgebra (C : ConicAlgebra k A) (B : NonAssocSubalgebra k A) (v : A) :
    Cay (C.restrict B) (-C.norm v) →ₗ[k] A where
  toFun p := (p.1 : A) + (p.2 : A) * v
  map_add' p q := by
    simp only [Cay.fst_add, Cay.snd_add, AddMemClass.coe_add, add_mul]
    abel
  map_smul' c p := by
    simp only [Cay.fst_smul, Cay.snd_smul, SetLike.val_smul, smul_add, smul_mul_assoc,
      RingHom.id_apply]

variable {B : NonAssocSubalgebra k A}

omit [SMulCommClass k A A] in
@[simp] theorem cayToAlgebra_apply (p : Cay (C.restrict B) (-C.norm v)) :
    cayToAlgebra C B v p = (p.1 : A) + (p.2 : A) * v := rfl

omit [SMulCommClass k A A] in
/-- The internal doubling map is unital. -/
theorem cayToAlgebra_one : cayToAlgebra C B v 1 = 1 := by
  rw [cayToAlgebra_apply]
  change ((1 : B) : A) + ((0 : B) : A) * v = 1
  rw [OneMemClass.coe_one, ZeroMemClass.coe_zero, zero_mul, add_zero]

variable (hBv : ∀ b ∈ B, polar C.norm b v = 0)
include hBv

omit [SMulCommClass k A A] in
/-- **`B ⊥ Bv`.** Norm-associativity moves the `v` across the polar form, where orthogonality to `B`
kills it: `n(b, wv) = n((conj w)b, v) = 0`. This is what makes the internal doubling map an isometry
onto its image, and needs the norm to be multiplicative. -/
theorem polar_mul_orthogonal (hmul : C.IsMultiplicative) {b w : A} (hb : b ∈ B) (hw : w ∈ B) :
    polar C.norm b (w * v) = 0 := by
  rw [QuadraticMap.polar_comm, hmul.polar_mul_left, QuadraticMap.polar_comm]
  exact hBv _ (mul_mem (conj_mem hw) hb)

/-- **The internal doubling map is an isometry**: it carries the Cayley–Dickson norm
`n_B ⊥ ⟨n(v)⟩ n_B` to the ambient norm. This is `GPR 18.1`'s norm formula, and it uses
multiplicativity (for `n(wv) = n(w)n(v)`) and `B ⊥ Bv`. -/
theorem norm_cayToAlgebra (hmul : C.IsMultiplicative) (p : Cay (C.restrict B) (-C.norm v)) :
    C.norm (cayToAlgebra C B v p) = ((C.restrict B).cay (-C.norm v)).norm p := by
  rw [cayToAlgebra_apply, C.norm_add, hmul.norm_mul,
    polar_mul_orthogonal hBv hmul (SetLike.coe_mem p.1) (SetLike.coe_mem p.2), cay_norm_apply,
    restrict_norm_apply, restrict_norm_apply]
  ring

/-- The polar form of the Cayley–Dickson norm is the ambient polar form, pulled back. -/
theorem polar_cayToAlgebra (hmul : C.IsMultiplicative)
    (p q : Cay (C.restrict B) (-C.norm v)) :
    polar C.norm (cayToAlgebra C B v p) (cayToAlgebra C B v q) =
      polar ((C.restrict B).cay (-C.norm v)).norm p q := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add,
    norm_cayToAlgebra hBv hmul, norm_cayToAlgebra hBv hmul, norm_cayToAlgebra hBv hmul]

variable [IsAlternative A] (hconj : C.ConjIsInvolution) (hu : IsUnit (C.norm v))
include hconj hu

/-- **`GPR 18.1`.** The internal doubling map is multiplicative: `B + Bv` really is a copy of
`Cay(B, -n(v))` inside `A`.

The three components of the Cayley–Dickson product are the three identities of this file, and
`μ = -n(v)` is forced by the last of them. -/
theorem cayToAlgebra_mul (p q : Cay (C.restrict B) (-C.norm v)) :
    cayToAlgebra C B v (p * q) = cayToAlgebra C B v p * cayToAlgebra C B v q := by
  have hi := mul_mul_orthogonal hBv hconj hu (SetLike.coe_mem p.1) (SetLike.coe_mem q.2)
  have hii := mul_orthogonal_mul hBv hconj hu (SetLike.coe_mem p.2) (SetLike.coe_mem q.1)
  have hiii := mul_orthogonal_mul_mul_orthogonal hBv hconj (SetLike.coe_mem p.2)
    (SetLike.coe_mem q.2)
  simp only [cayToAlgebra_apply, Cay.fst_mul, Cay.snd_mul, AddMemClass.coe_add,
    MulMemClass.coe_mul, SetLike.val_smul, coe_restrict_conj, add_mul, mul_add]
  rw [hi, hii, hiii]
  module

omit [IsAlternative A] hconj in
/-- **The internal doubling map is injective**, as soon as the radical of the restricted norm
vanishes and `n(v)` is a unit.

The map is an isometry, so its kernel lands in the radical of the Cayley–Dickson norm
`n_B ⊥ ⟨n(v)⟩ n_B`, which vanishes by `GN (C.8.3)`: the first summand has injective polar form and
rescaling by a unit does not change a radical.

⚠ Regularity of `n|_B` — not merely a vanishing radical — is what `GN (C.8.3)` consumes, and the
asymmetry is real: in characteristic 2 the non-singular form `⟨1⟩` doubles to `⟨1⟩ ⊥ ⟨1⟩`, whose
radical is nonzero. This is the same hypothesis `ConicAlgebra.IsComposition.cay` carries on the
constructive side. -/
theorem cayToAlgebra_injective (hmul : C.IsMultiplicative)
    (hreg : (C.restrict B).norm.IsGPRRegular) :
    Function.Injective (cayToAlgebra C B v) := by
  have hnd : (C.restrict B).norm.IsGPRNondegenerate :=
    Submodule.eq_bot_iff _ |>.mpr fun _ hx ↦
      (injective_iff_map_eq_zero _).mp hreg.1 _ hx.2
  have hrad : QuadraticMap.radical ((C.restrict B).cay (-C.norm v)).norm = ⊥ := by
    refine QuadraticMap.radical_prod_eq_bot hreg.1 ?_
    rw [neg_neg]
    exact (QuadraticMap.radical_smul hu _).trans hnd
  refine (injective_iff_map_eq_zero _).mpr fun p hp ↦ ?_
  have hmem : p ∈ QuadraticMap.radical ((C.restrict B).cay (-C.norm v)).norm := by
    refine ⟨?_, LinearMap.ext fun q ↦ ?_⟩
    · rw [← norm_cayToAlgebra hBv hmul, hp, map_zero]
    · rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply,
        ← polar_cayToAlgebra hBv hmul, hp, QuadraticMap.polar_zero_left]
  rw [hrad, Submodule.mem_bot] at hmem
  exact hmem

end Cay

end ConicAlgebra

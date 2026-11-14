/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAlternative
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAssociative
public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative
public import LeanPool.CompositionAlgebrasOverRings.Conic.Projective

/-!
# The converse halves of `GPR 18.14` and `GPR 18.15`

`Conic/CayleyDicksonAssociative.lean` proves the directions of `GPR 18.14(a),(b)` that *build*
algebras — if `B` is commutative with trivial conjugation then `Cay(B, μ)` is commutative, and if
`B` is commutative associative with involutive conjugation then `Cay(B, μ)` is associative — and
records two explicit failure witnesses. `Conic/CayleyDicksonAlternative.lean` proves both
directions of `GPR 18.14(c)`.

This file supplies the remaining implications, so that `GPR 18.14(a)` and `GPR 18.14(b)` become
equivalences, and then discharges their conjugation hypotheses over a projective module to obtain
`GPR 18.15`.

## Method

Nothing here needs the associator formulas of `GPR 18.13`. Each converse is read off from a single
well-chosen instance, exactly as in `GPR 18.14(c)`:

* `B` embeds in the double as the elements `(u, 0)`, and that embedding respects products. So any
  identity holding in `Cay(B, μ)` holds in `B` — this gives commutativity and associativity of `B`
  at once, with no hypothesis on `μ`.
* The conjugation is handled by the failure witnesses already available: `(u, 0)(0, 1) = (0, u)`
  while `(0, 1)(u, 0) = (0, conj u)`, so commutativity of the double forces `conj u = u`; and an
  associative double is alternative, so `ConicAlgebra.conjIsInvolution_of_isAlternative_cay`
  applies.
* Commutativity of `B` under an associative double is the contrapositive of
  `ConicAlgebra.exists_mul_mul_ne_mul_mul_cay`, whose conjugation hypothesis the previous point
  has just supplied.

## Main results

* `ConicAlgebra.mul_comm_of_mul_comm_cay`, `ConicAlgebra.conj_eq_id_of_mul_comm_cay` :
  **`GPR 18.14(a)`, `⇒`**.
* `ConicAlgebra.mul_comm_cay_iff` : **`GPR 18.14(a)`**, the equivalence.
* `ConicAlgebra.mul_assoc_of_mul_assoc_cay`, `ConicAlgebra.conjIsInvolution_of_mul_assoc_cay`,
  `ConicAlgebra.mul_comm_of_mul_assoc_cay` : **`GPR 18.14(b)`, `⇒`**.
* `ConicAlgebra.mul_assoc_cay_iff` : **`GPR 18.14(b)`**, the equivalence.
* `ConicAlgebra.isAlternative_cay_iff_of_projective`,
  `ConicAlgebra.mul_assoc_cay_iff_of_projective` : **`GPR 18.15`(b),(a)** — over a finitely
  generated projective module the hypothesis on the conjugation of `B` is automatic
  (`GPR 16.14(b)`), so the criteria become conditions on the multiplication of `B` alone.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.14, 18.15,
  16.14(b).
-/

@[expose] public section

universe u v

namespace ConicAlgebra

section General

variable {k : Type u} {B : Type v} [CommRing k] [NonAssocRing B] [Module k B]
  [instSMulComm : SMulCommClass k B B] [instTower : IsScalarTower k B B]
  (C : ConicAlgebra k B) (μ : k)

omit instSMulComm instTower in
/-- On elements with zero `j`-part the product of the double is the product of `B`: the `μ`-term
of the first component needs a nonzero `j`-part. -/
theorem Cay.fst_mul_of_snd_eq_zero {x y : Cay C μ} (hy : y.2 = 0) :
    (x * y).1 = x.1 * y.1 := by
  simp only [Cay.fst_mul, hy, map_zero, zero_mul, smul_zero, add_zero]

omit instSMulComm instTower in
/-- Elements with zero `j`-part are closed under multiplication. -/
theorem Cay.snd_mul_of_snd_eq_zero {x y : Cay C μ} (hx : x.2 = 0) (hy : y.2 = 0) :
    (x * y).2 = 0 := by
  simp only [Cay.snd_mul, hx, hy, zero_mul, add_zero]

omit instSMulComm instTower in
/-- **`GPR 18.14(a)`, `⇒`, first half.** A commutative double forces `B` commutative, since `B`
sits inside it as the elements with zero `j`-part. -/
theorem mul_comm_of_mul_comm_cay (h : ∀ x y : Cay C μ, x * y = y * x) (a b : B) :
    a * b = b * a := by
  obtain ⟨x, hx1, hx2⟩ : ∃ x : Cay C μ, x.1 = a ∧ x.2 = 0 := ⟨(a, 0), rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ : ∃ y : Cay C μ, y.1 = b ∧ y.2 = 0 := ⟨(b, 0), rfl, rfl⟩
  have key : (x * y).1 = (y * x).1 := by rw [h x y]
  rwa [Cay.fst_mul_of_snd_eq_zero C μ hy2, Cay.fst_mul_of_snd_eq_zero C μ hx2, hx1, hy1] at key

omit instSMulComm instTower in
/-- **`GPR 18.14(a)`, `⇒`, second half.** A commutative double forces the conjugation of `B` to be
the identity. This is the contrapositive of `ConicAlgebra.exists_mul_ne_mul_cay`. -/
theorem conj_eq_id_of_mul_comm_cay (h : ∀ x y : Cay C μ, x * y = y * x) (u : B) :
    C.conj u = u := by
  by_contra hu
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_mul_cay C μ hu
  exact hxy (h x y)

omit instSMulComm instTower in
/-- **`GPR 18.14(b)`, `⇒`, first half.** An associative double forces `B` associative, by the same
embedding. No hypothesis on `μ`. -/
theorem mul_assoc_of_mul_assoc_cay (h : ∀ x y z : Cay C μ, x * y * z = x * (y * z))
    (a b c : B) : a * b * c = a * (b * c) := by
  obtain ⟨x, hx1, hx2⟩ : ∃ x : Cay C μ, x.1 = a ∧ x.2 = 0 := ⟨(a, 0), rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ : ∃ y : Cay C μ, y.1 = b ∧ y.2 = 0 := ⟨(b, 0), rfl, rfl⟩
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Cay C μ, z.1 = c ∧ z.2 = 0 := ⟨(c, 0), rfl, rfl⟩
  have hxy : (x * y).2 = 0 := Cay.snd_mul_of_snd_eq_zero C μ hx2 hy2
  have hyz : (y * z).2 = 0 := Cay.snd_mul_of_snd_eq_zero C μ hy2 hz2
  have key : (x * y * z).1 = (x * (y * z)).1 := by rw [h x y z]
  rwa [Cay.fst_mul_of_snd_eq_zero C μ hz2, Cay.fst_mul_of_snd_eq_zero C μ hy2,
    Cay.fst_mul_of_snd_eq_zero C μ hyz, Cay.fst_mul_of_snd_eq_zero C μ hz2, hx1, hy1, hz1] at key

omit instSMulComm instTower in
/-- An associative double is alternative. -/
theorem isAlternative_cay_of_mul_assoc_cay (h : ∀ x y z : Cay C μ, x * y * z = x * (y * z)) :
    IsAlternative (Cay C μ) where
  left_alt a b := (h a a b).symm
  right_alt a b := h b a a

include instSMulComm instTower in
/-- **The converse of the multiplicativity criterion.** If the norm of `Cay(B, μ)` permits
composition then so does the norm of `B`, for every `μ`.

Same embedding: `n_{Cay}(u, 0) = n_B(u) - μ·n_B(0) = n_B(u)`, and `(u, 0)(v, 0) = (uv, 0)`.

⚠ This is the converse *implication*, not the sharp criterion. `GPR Exc. 18.18` says that for `B`
multiplicative, `Cay(B, μ)` is multiplicative **if and only if** `μ[B, B, B] ⊆ Rad(Dn_B)`; that
characterization needs the associator formulas of `GPR 18.13` and is not proved here. The forward
implication proved elsewhere (`ConicAlgebra.isMultiplicative_cay`) is the case `[B, B, B] = 0`. -/
theorem isMultiplicative_of_isMultiplicative_cay (h : (C.cay μ).IsMultiplicative) :
    C.IsMultiplicative := by
  intro a b
  obtain ⟨x, hx1, hx2⟩ : ∃ x : Cay C μ, x.1 = a ∧ x.2 = 0 := ⟨(a, 0), rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ : ∃ y : Cay C μ, y.1 = b ∧ y.2 = 0 := ⟨(b, 0), rfl, rfl⟩
  have hxy : (x * y).2 = 0 := Cay.snd_mul_of_snd_eq_zero C μ hx2 hy2
  have key := h x y
  simp only [cay, cayNorm_apply, hxy, hx2, hy2, map_zero, mul_zero, sub_zero,
    Cay.fst_mul_of_snd_eq_zero C μ hy2, hx1, hy1] at key
  exact key

include instSMulComm instTower in
/-- **`GPR 18.14(b)`, `⇒`, second half.** An associative double is alternative, so
`ConicAlgebra.conjIsInvolution_of_isAlternative_cay` applies. -/
theorem conjIsInvolution_of_mul_assoc_cay (h : ∀ x y z : Cay C μ, x * y * z = x * (y * z)) :
    C.ConjIsInvolution :=
  conjIsInvolution_of_isAlternative_cay C μ (isAlternative_cay_of_mul_assoc_cay C μ h)

include instSMulComm instTower in
/-- **`GPR 18.14(b)`, `⇒`, third half.** An associative double forces `B` *commutative*.

This is the one implication that is not an embedding argument. It is the contrapositive of
`ConicAlgebra.exists_mul_mul_ne_mul_mul_cay`, whose hypothesis that the conjugation of `B` be an
involution is supplied by `ConicAlgebra.conjIsInvolution_of_mul_assoc_cay`. -/
theorem mul_comm_of_mul_assoc_cay (h : ∀ x y z : Cay C μ, x * y * z = x * (y * z)) (a c : B) :
    a * c = c * a := by
  by_contra hac
  obtain ⟨x, y, z, hxyz⟩ :=
    exists_mul_mul_ne_mul_mul_cay C μ (conjIsInvolution_of_mul_assoc_cay C μ h) hac
  exact hxyz (h x y z)

end General

section CommRing

variable {k : Type u} {B : Type v} [CommRing k] [CommRing B] [Algebra k B]
  (C : ConicAlgebra k B) (μ : k)

/-- **`GPR 18.14(a)`.** For `B` commutative, the double `Cay(B, μ)` is commutative exactly when
the conjugation of `B` is the identity — for every scalar `μ`. -/
theorem mul_comm_cay_iff : (∀ x y : Cay C μ, x * y = y * x) ↔ ∀ u : B, C.conj u = u :=
  ⟨conj_eq_id_of_mul_comm_cay C μ, mul_comm_cay C μ⟩

/-- **`GPR 18.14(b)`.** For `B` commutative, the double `Cay(B, μ)` is associative exactly when
the conjugation of `B` is an involution — for every scalar `μ`. -/
theorem mul_assoc_cay_iff :
    (∀ x y z : Cay C μ, x * y * z = x * (y * z)) ↔ C.ConjIsInvolution :=
  ⟨conjIsInvolution_of_mul_assoc_cay C μ, mul_assoc_cay C μ⟩

end CommRing

/-! ### `GPR 18.15`: discharging the hypothesis on the conjugation

Over a finitely generated projective module the conjugation of an alternative conic algebra is
automatically an involution (`GPR 16.14(b)`, `ConicAlgebra.conjIsInvolution_of_projective`). Since
an associative `B` is alternative, that removes the conjugation hypothesis from both criteria and
leaves conditions on the multiplication of `B` alone. -/

section Projective

variable {k : Type u} {B : Type v} [CommRing k] [NonAssocRing B] [Module k B]
  [SMulCommClass k B B] [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B]
  (C : ConicAlgebra k B) (μ : k)

/-- **`GPR 18.15(b)`.** For `B` finitely generated projective, `Cay(B, μ)` is alternative exactly
when `B` is associative. -/
theorem isAlternative_cay_iff_of_projective :
    IsAlternative (Cay C μ) ↔ ∀ a b c : B, a * b * c = a * (b * c) := by
  refine ⟨mul_assoc_of_isAlternative_cay C μ, fun hassoc ↦ ?_⟩
  have : IsAlternative B := ⟨fun a b ↦ (hassoc a a b).symm, fun a b ↦ hassoc b a a⟩
  exact isAlternative_cay_of_mul_assoc C μ hassoc C.conjIsInvolution_of_projective

end Projective

section ProjectiveCommRing

variable {k : Type u} {B : Type v} [CommRing k] [CommRing B] [Algebra k B]
  [Module.Finite k B] [Module.Projective k B] (C : ConicAlgebra k B) (μ : k)

/-- **`GPR 18.15(a)`.** For `B` a finitely generated projective commutative algebra, `Cay(B, μ)`
is associative — unconditionally, the conjugation hypothesis of `GPR 18.14(b)` being automatic. -/
theorem mul_assoc_cay_of_projective (x y z : Cay C μ) : x * y * z = x * (y * z) :=
  mul_assoc_cay C μ C.conjIsInvolution_of_projective x y z

end ProjectiveCommRing

end ConicAlgebra

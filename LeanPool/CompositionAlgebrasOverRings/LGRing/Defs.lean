/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.FieldSimp

/-!
# LG rings

Defines `IsLGRing R` (`GPR 11.20`, `GN 2.1`): a commutative ring `R` is an **LG-ring**
("local–global ring") if, for every `n` and every `f ∈ R[X₁,…,Xₙ]`, `f` represents a unit over
`R` iff `f` represents a unit over every residue field `R/𝔪`, `𝔪` maximal. LG rings are the class
of commutative rings where most results of undergraduate linear algebra for vector spaces also
hold for finitely generated projective modules — see the overview's "Why LG rings" section.

## Main definitions

* `MvPolynomial.RepresentsUnit p S` : `p`, viewed as a polynomial over the `R`-algebra `S`,
  evaluates to a unit at some point of `S`.
* `IsLGRing R` : `GPR 11.20`.

## Main results

* `MvPolynomial.aeval_map_comm` : evaluation transports along a commuting square of ring
  homomorphisms. This is the workhorse behind every change-of-ring argument in this directory.
* `exists_isUnit_of_isUnit_quotient` : if `R` is LG, then for every `b : R`, every unit of
  `R ⧸ (b)` lifts to a unit of `R`. This is the key structural consequence used to build
  non-examples (`LGRing/NonExamples.lean`): a ring where `Rˣ → (R ⧸ (b))ˣ` fails to be surjective,
  for some choice of `b`, cannot be LG.

## Implementation notes

`GPR 11.20` states the defining biconditional using residue fields, and remarks that it is
equivalent to use the localization `R_𝔪` instead. `GN 2.1` adds a third equivalent formulation,
"represents a unit over every field `F ∈ R`-alg" — but this project does not reprove that
three-way equivalence, and an earlier version of this file took that third formulation as the
*definition*, which turned out to make `GPR 11.21` (`R` LG iff `R ⧸ Jac(R)` LG) genuinely harder
to prove: a field receiving `R` through a non-maximal prime need not have any relationship to a
residue field of `R`, so the bridge between the two rings' field-algebras breaks down. Residue
fields of `R` and of `R ⧸ Jac(R)` correspond exactly (every maximal ideal contains the Jacobson
radical), which is what makes `LGRing/Jacobson.lean` go through. So this file uses `GPR`'s own
formulation (residue fields), matching the primary source, not the alternative from `GN`.

Constructing the `Field (R ⧸ 𝔪)` instance from `𝔪.IsMaximal` (via `Ideal.Quotient.field`) is a
well-known mathlib performance/diamond hazard when combined with other instances derived from the
same quotient in the same context. We avoid it entirely by working with the `Prop`-valued
`IsField (R ⧸ 𝔪)` (via `Ideal.Quotient.maximal_ideal_iff_isField_quotient`) instead of the bundled
`Field` structure wherever we need "nonzero ⇒ invertible" — `IsField` carries no data, so there is
nothing for two different derivations of it to disagree about.

The forward direction of the biconditional (`RepresentsUnit p R → ∀ 𝔪, RepresentsUnit p (R ⧸ 𝔪)`)
holds for **any** commutative ring `R`, LG or not: `IsUnit` is preserved by every ring
homomorphism, so a witness over `R` pushes forward to a witness over any quotient. The entire
content of the LG axiom is in the converse.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.20.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, §2.1.
-/

@[expose] public section

universe u v

/-- `p`, viewed as a polynomial over the `R`-algebra `S`, represents a unit: it evaluates to a
unit at some point of `S`. -/
def MvPolynomial.RepresentsUnit {R : Type u} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R)
    (S : Type v) [CommRing S] [Algebra R S] : Prop :=
  ∃ s : Fin n → S, IsUnit (MvPolynomial.aeval s p)

/-- `R` is an **LG-ring** (`GPR 11.20`, "local–global ring"): a polynomial in finitely many
variables over `R` represents a unit over `R` iff it represents a unit over every residue field
`R ⧸ 𝔪`, `𝔪` maximal. See the implementation notes for why this formulation (rather than `GN`'s
"every field `F ∈ R`-alg" alternative) is taken as the definition. -/
def IsLGRing (R : Type u) [CommRing R] : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n) R),
    p.RepresentsUnit R ↔ ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], p.RepresentsUnit (R ⧸ 𝔪)

/-- If `ψ : S → S'` sits over `φ : R → R'` — that is, the square of structure maps commutes —
then evaluating `p` over `S` and transporting agrees with reducing `p`'s coefficients along `φ`
and evaluating over `S'`. Compare `aeval_map_quotient` in `LGRing/Jacobson.lean`, which is the
special case of reduction modulo an ideal.

Every transport of `MvPolynomial.RepresentsUnit` in this directory is an instance of this square:
see `MvPolynomial.RepresentsUnit.mapOfComm` and `MvPolynomial.RepresentsUnit.ofMapOfComm` in
`LGRing/Products.lean`. -/
theorem MvPolynomial.aeval_map_comm {R : Type*} [CommRing R] {R' : Type*} [CommRing R']
    (φ : R →+* R') {S : Type*} [CommRing S] [Algebra R S] {S' : Type*} [CommRing S']
    [Algebra R' S'] (ψ : S →+* S')
    (hcomm : ψ.comp (algebraMap R S) = (algebraMap R' S').comp φ)
    {n : ℕ} (s : Fin n → S) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.aeval (fun i ↦ ψ (s i)) (MvPolynomial.map φ p)
      = ψ (MvPolynomial.aeval s p) := by
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_map, MvPolynomial.hom_eval₂, hcomm]

/-! ### Units lift along quotients by a principal ideal

The test polynomial is `u + b·T` (one variable): linear, not quadratic, and the argument routes
entirely through the LG axiom rather than through any explicit field-case computation. -/

/-- The affine polynomial `u + b·T`, in one variable. -/
noncomputable def linUC {R : Type u} [CommRing R] (u b : R) : MvPolynomial (Fin 1) R :=
  MvPolynomial.C u + MvPolynomial.C b * MvPolynomial.X 0

@[simp]
theorem aeval_linUC {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (s : Fin 1 → S) (u b : R) :
    MvPolynomial.aeval s (linUC u b) = algebraMap R S u + algebraMap R S b * s 0 := by
  simp [linUC]

/-- **If `R` is LG, every unit of `R ⧸ (b)` lifts to a unit of `R`.**

Given `ū ∈ (R ⧸ (b))ˣ`, lift it (non-canonically) to `u, v : R` with `u ≡ ū`, `v ≡ ū⁻¹`, so that
`uv = 1 + bw` for some `w`. The polynomial `u + b·T` represents a unit over *every* residue field
`R ⧸ 𝔪`: if `b ↦ 0`, then `u ↦` a unit already (from `uv = 1 + bw` reducing to `uv = 1`), so
`T = 0` works; if `b ↦` something nonzero, `T = (1 - u)/b` gives `u + bT ↦ 1`. By the LG axiom this
descends to `R` itself: some `u + bt₀ ∈ Rˣ`, and it is `≡ u ≡ ū` mod `(b)`. -/
theorem exists_isUnit_of_isUnit_quotient {R : Type u} [CommRing R] (hLG : IsLGRing R) (b : R)
    (ū : (R ⧸ Ideal.span {b})ˣ) :
    ∃ u' : Rˣ, Ideal.Quotient.mk (Ideal.span {b}) (u' : R) = (ū : R ⧸ Ideal.span {b}) := by
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (ū : R ⧸ Ideal.span {b})
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (↑(ū⁻¹) : R ⧸ Ideal.span {b})
  have huv : Ideal.Quotient.mk (Ideal.span {b}) (u * v - 1) = 0 := by
    rw [map_sub, map_mul, hu, hv, map_one]
    exact_mod_cast sub_eq_zero.mpr ū.mul_inv
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at huv
  obtain ⟨w, hw⟩ := huv
  have hkey : (linUC u b).RepresentsUnit R := by
    apply (hLG 1 (linUC u b)).mpr
    intro 𝔪 hmax
    have hfield : IsField (R ⧸ 𝔪) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪).mp hmax
    by_cases hb : algebraMap R (R ⧸ 𝔪) b = 0
    · refine ⟨fun _ ↦ 0, ?_⟩
      rw [aeval_linUC, hb, zero_mul, add_zero]
      have hune : algebraMap R (R ⧸ 𝔪) u ≠ 0 := by
        intro hcontra
        have heq :
            algebraMap R (R ⧸ 𝔪) (u * v - 1) = algebraMap R (R ⧸ 𝔪) (w * b) := by
          rw [hw]
        simp only [map_sub, map_mul, map_one, hb, mul_zero, hcontra, zero_mul, zero_sub] at heq
        exact one_ne_zero (neg_eq_zero.mp heq)
      obtain ⟨c, hc⟩ := hfield.mul_inv_cancel hune
      exact IsUnit.of_mul_eq_one c hc
    · obtain ⟨c, hc⟩ := hfield.mul_inv_cancel hb
      refine ⟨fun _ ↦ c * (1 - algebraMap R (R ⧸ 𝔪) u), ?_⟩
      rw [aeval_linUC]
      have heq3 : algebraMap R (R ⧸ 𝔪) u +
          algebraMap R (R ⧸ 𝔪) b * (c * (1 - algebraMap R (R ⧸ 𝔪) u)) = 1 := by
        have hrw : algebraMap R (R ⧸ 𝔪) b * (c * (1 - algebraMap R (R ⧸ 𝔪) u)) =
            (algebraMap R (R ⧸ 𝔪) b * c) * (1 - algebraMap R (R ⧸ 𝔪) u) := by ring
        rw [hrw, hc, one_mul]; ring
      rw [heq3]
      exact isUnit_one
  obtain ⟨s, hs⟩ := hkey
  rw [aeval_linUC, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply] at hs
  refine ⟨hs.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hu, Ideal.Quotient.eq]
  have heq2 : u + b * s 0 - u = b * s 0 := by ring
  rw [heq2]
  exact Ideal.mem_span_singleton'.mpr ⟨s 0, mul_comm _ _⟩

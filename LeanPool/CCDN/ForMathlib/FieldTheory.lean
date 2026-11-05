/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Counting monic divisors and intermediate fields; Hilbert 90 for an involution

Monic divisors of a nonzero polynomial are determined by their multisets of roots in an
algebraic closure, so there are at most `2 ^ natDegree` of them. Through a primitive element,
the intermediate fields of a finite separable extension inject into the monic divisors of a
minimal polynomial.

## Main results

* `Polynomial.card_monic_dvd_le_two_pow_natDegree`: a nonzero polynomial `f` over a field has at
  most `2 ^ f.natDegree` monic divisors.
* `IntermediateField.card_le_two_pow_finrank`: a finite separable extension `E / F` has at most
  `2 ^ finrank F E` intermediate fields.
* `RingEquiv.hilbert90_of_involutive`: Hilbert 90 for a nontrivial involution `σ` of a field,
  with an explicit construction that also works in characteristic two: if `a σ(a) = 1`, then
  `a σ(b) = b` for some `b ≠ 0`. `RingEquiv.hilbert90_units_of_involutive` is the unit-group form.
* `RingEquiv.exists_invariant_of_involutive`: for a compatible homomorphism `P` from the units,
  an element `I` with `τ I = P a * I` and `a σ(a) = 1` has a `τ`-invariant multiple `P b * I`.
-/

@[expose] public section

section

open Module Polynomial IntermediateField

namespace Polynomial

/-- A nonzero polynomial over a field has at most `2 ^ natDegree` monic divisors. -/
theorem card_monic_dvd_le_two_pow_natDegree
    {K : Type*} [Field K] (f : K[X]) (hf : f ≠ 0) :
    Nat.card {g : K[X] // g.Monic ∧ g ∣ f} ≤ 2 ^ f.natDegree := by
  classical
  let L := AlgebraicClosure K
  let ι := algebraMap K L
  let P := ((f.map ι).roots.powerset).toFinset
  let e : {g : K[X] // g.Monic ∧ g ∣ f} → ↥P := fun g =>
    ⟨(g.1.map ι).roots, by
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_powerset.mpr
      exact Polynomial.roots.le_of_dvd (Polynomial.map_ne_zero hf)
        (Polynomial.map_dvd ι g.2.2)⟩
  have he : Function.Injective e := by
    intro g h hgh
    have hr : (g.1.map ι).roots = (h.1.map ι).roots := congrArg Subtype.val hgh
    apply Subtype.ext
    apply Polynomial.map_injective ι ι.injective
    rw [(IsAlgClosed.splits (g.1.map ι)).eq_prod_roots_of_monic (g.2.1.map ι),
      (IsAlgClosed.splits (h.1.map ι)).eq_prod_roots_of_monic (h.2.1.map ι), hr]
  calc
    Nat.card {g : K[X] // g.Monic ∧ g ∣ f} ≤ Nat.card ↥P :=
      Nat.card_le_card_of_injective e he
    _ = P.card := by simp
    _ ≤ (f.map ι).roots.powerset.card := Multiset.toFinset_card_le _
    _ = 2 ^ (f.map ι).roots.card := Multiset.card_powerset _
    _ ≤ 2 ^ f.natDegree :=
      Nat.pow_le_pow_right (by omega) (Polynomial.card_roots_map_le_natDegree _)

end Polynomial

namespace IntermediateField

/-- The number of intermediate fields depends only on the extension
degree, without a chosen normal closure or Galois-group estimate. -/
theorem card_le_two_pow_finrank
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Nat.card (IntermediateField F E) ≤ 2 ^ Module.finrank F E := by
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let f : E[X] := (minpoly F α).map (algebraMap F E)
  let G := {g : E[X] // g.Monic ∧ g ∣ f}
  let : Fintype G := fintypeSubtypeMonicDvd f
    (Polynomial.map_ne_zero (minpoly.ne_zero_of_finite F α))
  let g : IntermediateField F E → G := fun K =>
    ⟨(minpoly K α).map (algebraMap K E), (minpoly.monic (.of_finite K α)).map _, by
      convert Polynomial.map_dvd (algebraMap K E) (minpoly.dvd_map_of_isScalarTower F K α)
      rw [Polynomial.map_map]
      rfl⟩
  have hg : Function.Injective g := by
    intro K K' heq
    have heq' := congrArg Subtype.val heq
    dsimp [g] at heq'
    apply_fun fun p : E[X] => adjoin F (p.coeffs : Set E) at heq'
    simpa only [adjoin_minpoly_coeff_of_exists_primitive_element F hα] using heq'
  have hdeg : f.natDegree = Module.finrank F E := by
    rw [Polynomial.natDegree_map]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hα
  exact (Nat.card_le_card_of_injective g hg).trans
    (hdeg ▸ Polynomial.card_monic_dvd_le_two_pow_natDegree f
      (Polynomial.map_ne_zero (minpoly.ne_zero_of_finite F α)))

end IntermediateField

end

namespace RingEquiv

variable {K : Type*} [Field K]

/-- A norm-one scalar for a nontrivial involution is a multiplicative
coboundary. The explicit construction also works in characteristic two. -/
theorem hilbert90_of_involutive (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl K) {a : K} (ha : a * σ a = 1) :
    ∃ b : K, b ≠ 0 ∧ a * σ b = b := by
  by_cases h : 1 + a = 0
  · have ha' : a = -1 := by linear_combination h
    obtain ⟨z, hz⟩ : ∃ z : K, σ z ≠ z := by
      by_contra hn
      push Not at hn
      exact hσne (RingEquiv.ext hn)
    refine ⟨z - σ z, sub_ne_zero.mpr hz.symm, ?_⟩
    rw [ha', map_sub]
    change -1 * (σ z - σ (σ z)) = z - σ z
    rw [hσ]
    ring
  · refine ⟨1 + a, h, ?_⟩
    rw [map_add, map_one, mul_add, mul_one, ha, add_comm]

/-- Hilbert 90 for a nontrivial involution, in the unit group: a unit `a` with
`a σ(a) = 1` has the form `b / σ(b)` for some unit `b`. -/
theorem hilbert90_units_of_involutive (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl K) (a : Kˣ)
    (ha : (a : K) * σ (a : K) = 1) :
    ∃ b : Kˣ, a * Units.map σ.toMonoidHom b = b := by
  obtain ⟨b, hb, hab⟩ := hilbert90_of_involutive σ hσ hσne ha
  exact ⟨Units.mk0 b hb, Units.ext hab⟩

/-- If the scalar comparison of an element with its conjugate has norm
one, multiplication by a principal element produces an invariant
representative. Here the principal map is a homomorphism. -/
theorem exists_invariant_of_involutive
    {A : Type*} [CommGroup A]
    (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl K) (τ : A →* A) (P : Kˣ →* A)
    (hcompat : ∀ b : Kˣ, τ (P b) = P (Units.map σ.toMonoidHom b))
    (I : A) (a : Kˣ) (hI : τ I = P a * I)
    (ha : (a : K) * σ (a : K) = 1) :
    ∃ b : Kˣ, τ (P b * I) = P b * I := by
  obtain ⟨b, hb⟩ := hilbert90_units_of_involutive σ hσ hσne a ha
  refine ⟨b, ?_⟩
  rw [map_mul, hcompat, hI, ← mul_assoc, mul_comm (P _), ← map_mul, hb]

end RingEquiv

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.MultiplicationPairingProduct
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! A field basis containing one supplies the complement used by the
multiplication pairing. The resulting product inequality is independent
of the geometric construction of the basis or the length function. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {F K ι : Type*} [Field F] [Field K] [Algebra F K]

/-- The span of the basis vectors `b i` with `i ≠ p` and `i ≠ q` is the intersection of the kernels
of the coordinate functionals `b.coord q` and `b.coord p`. -/
theorem fieldBasisMiddle_span (b : Module.Basis ι F K) (p q : ι) :
    Submodule.span F (Set.range (fun i : {i : ι // i ≠ p ∧ i ≠ q} ↦ b i)) =
      hyperplaneComplement (b.coord q) (b.coord p) := by
  classical
  have hr : Set.range (fun i : {i : ι // i ≠ p ∧ i ≠ q} ↦ b i) =
      b '' {i : ι | i ≠ p ∧ i ≠ q} := by
    ext x
    simp
  rw [hr]
  ext x
  rw [b.mem_span_image]
  change (↑(b.repr x).support ⊆ {i : ι | i ≠ p ∧ i ≠ q}) ↔
    b.repr x q = 0 ∧ b.repr x p = 0
  constructor
  · intro hx
    constructor
    · by_contra hq
      exact (hx (Finsupp.mem_support_iff.mpr hq)).2 rfl
    · by_contra hp
      exact (hx (Finsupp.mem_support_iff.mpr hp)).1 rfl
  · rintro ⟨hq, hp⟩ i hi
    have hi' := Finsupp.mem_support_iff.mp hi
    exact ⟨fun h ↦ hi' (h ▸ hp), fun h ↦ hi' (h ▸ hq)⟩

/-- The original basis vectors other than the unit and the distinguished
last vector form a basis of the two coordinate kernels. -/
def fieldBasisMiddle (b : Module.Basis ι F K) (p q : ι) :
    Module.Basis {i : ι // i ≠ p ∧ i ≠ q} F
      (hyperplaneComplement (b.coord q) (b.coord p)) :=
  (Module.Basis.span
    (b.linearIndependent.comp (fun i : {i : ι // i ≠ p ∧ i ≠ q} ↦ (i : ι))
      Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (fieldBasisMiddle_span b p q))

/-- The vectors of `fieldBasisMiddle b p q` are the original basis vectors `b i`. -/
@[simp]
theorem fieldBasisMiddle_apply (b : Module.Basis ι F K) (p q : ι)
    (i : {i : ι // i ≠ p ∧ i ≠ q}) :
    (fieldBasisMiddle b p q i : K) = b i := by
  simp [fieldBasisMiddle]

section Finite
variable [Fintype ι] [DecidableEq ι]

private theorem fieldBasisMiddle_card (p q : ι) (hpq : p ≠ q) :
    Fintype.card {i : ι // i ≠ p ∧ i ≠ q} + 2 = Fintype.card ι := by
  have hs (i : ι) :
      i ∈ (Finset.univ.erase p).erase q ↔ i ≠ p ∧ i ≠ q := by
    simp [and_comm]
  rw [Fintype.card_of_subtype _ hs]
  have hq : q ∈ Finset.univ.erase p := by simp [hpq.symm]
  have h₁ := Finset.card_erase_add_one hq
  have h₂ := Finset.card_erase_add_one (Finset.mem_univ p)
  simpa only [Finset.card_univ] using (show
    ((Finset.univ.erase p).erase q).card + 2 = Finset.univ.card by omega)

private theorem fieldBasisMiddle_prod {R : Type*} [CommMonoid R]
    (w : ι → R) (p q : ι) (hpq : p ≠ q) :
    ∏ i, w i = w p * w q * ∏ i : {i : ι // i ≠ p ∧ i ≠ q}, w i := by
  have hs (i : ι) :
      i ∈ (Finset.univ.erase p).erase q ↔ i ≠ p ∧ i ≠ q := by
    simp [and_comm]
  rw [← Finset.prod_subtype _ hs]
  have hq : q ∈ Finset.univ.erase p := by simp [hpq.symm]
  rw [mul_assoc, Finset.mul_prod_erase _ _ hq,
    Finset.mul_prod_erase _ _ (Finset.mem_univ p)]

omit [DecidableEq ι] in
/-- A nonnegative submultiplicative length and a minimum condition on
products detected by the last coordinate give the field-basis product
bound. In lattice applications the minimum condition follows because a
detected product lies outside the preceding coordinate hyperplane. -/
theorem field_basis_multiplication_minimum_product
    (b : Module.Basis ι F K) (p q : ι) (hpq : p ≠ q) (hp : b p = 1)
    (N : K → ℝ) (hN : ∀ x, 0 ≤ N x)
    (hmul : ∀ x y, N (x * y) ≤ N x * N y) (hunit : 1 ≤ N (b p))
    (hminimum : ∀ i j : {i : ι // i ≠ p ∧ i ≠ q},
      b.coord q (b i * b j) ≠ 0 → N (b q) ≤ N (b i * b j)) :
    N (b q) ^ Fintype.card ι ≤ (∏ i, N (b i)) ^ 2 := by
  classical
  have hℓ : b.coord q ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h (b q)
    simp at hh
  have hℓ1 : b.coord q 1 = 0 := by
    rw [← hp]
    simp [Module.Basis.coord_apply, hpq]
  have hμ1 : b.coord p 1 = 1 := by
    rw [← hp]
    simp [Module.Basis.coord_apply]
  have hpair := hyperplane_multiplication_minimum_product
    (b.coord q) (b.coord p) hℓ hℓ1 hμ1 (fieldBasisMiddle b p q)
    (fun i ↦ N (b i)) (hN (b q)) (fun i j hij ↦
      (hminimum i j (by simpa only [fieldBasisMiddle_apply] using hij)).trans
        (hmul (b i) (b j)))
  rw [fieldBasisMiddle_card p q hpq] at hpair
  have hprod : 0 ≤ N (b q) * ∏ i : {i : ι // i ≠ p ∧ i ≠ q}, N (b i) :=
    mul_nonneg (hN _) (Finset.prod_nonneg (fun i _ ↦ hN _))
  have hfull :
      N (b q) * ∏ i : {i : ι // i ≠ p ∧ i ≠ q}, N (b i) ≤ ∏ i, N (b i) := by
    rw [fieldBasisMiddle_prod (fun i ↦ N (b i)) p q hpq, mul_assoc]
    exact le_mul_of_one_le_left hprod hunit
  exact hpair.trans (pow_le_pow_left₀ hprod hfull 2)

end Finite
end
end CCDN

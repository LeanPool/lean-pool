/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


/-!
# Amplitudes, Pauli eigenvectors, and computational measurement weights

An amplitude is a complex function on binary strings.  Computational outcome
weights are defined by the Born rule `Complex.normSq`; normalization is the
finite sum of those weights. The Pauli action is the explicit action of XᵘZᵛ
on amplitudes, not an assumed measurement-distribution property.
-/

@[expose] public section


noncomputable section

namespace LeanPool.SingleCopyStabilizer.Measurement

open scoped BigOperators

/-- Computational-basis strings indexed by qubit sites. -/
abbrev Bits (ι : Type*) := ι → ZMod 2
/-- Complex amplitudes on the computational basis. -/
abbrev Amplitude (ι : Type*) := Bits ι → ℂ

/-- The binary character `(-1)^a`, without choosing integer representatives. -/
def paritySign (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

@[simp] theorem paritySign_normSq (a : ZMod 2) :
    Complex.normSq (paritySign a) = 1 := by
  by_cases ha : a = 0 <;> simp [paritySign, ha]

theorem paritySign_injective : Function.Injective paritySign := by
  intro a b h
  have bits : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases bits a with rfl | rfl <;> rcases bits b with rfl | rfl <;>
    norm_num [paritySign] at *

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Born probability weight of a computational-basis outcome. -/
def bornWeight (ψ : Amplitude ι) (x : Bits ι) : ℝ := Complex.normSq (ψ x)

/-- Normalization of the finite Born weights to total mass one. -/
def IsNormalized (ψ : Amplitude ι) : Prop := ∑ x, bornWeight ψ x = 1

omit [DecidableEq ι] [Fintype ι] in
theorem bornWeight_nonneg (ψ : Amplitude ι) (x : Bits ι) :
    0 ≤ bornWeight ψ x := Complex.normSq_nonneg _

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem bornWeight_pos (ψ : Amplitude ι) (x : Bits ι) :
    0 < bornWeight ψ x ↔ ψ x ≠ 0 := Complex.normSq_pos

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem bornWeight_eq_zero (ψ : Amplitude ι) (x : Bits ι) :
    bornWeight ψ x = 0 ↔ ψ x = 0 := Complex.normSq_eq_zero

/-- Normalized amplitudes determine a mathlib probability mass function. -/
def bornPMF (ψ : Amplitude ι) (hψ : IsNormalized ψ) : PMF (Bits ι) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (bornWeight ψ x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => bornWeight_nonneg ψ x)]
    rw [hψ]
    exact ENNReal.ofReal_one)

@[simp] theorem bornPMF_apply (ψ : Amplitude ι) (hψ : IsNormalized ψ)
    (x : Bits ι) : bornPMF ψ hψ x = ENNReal.ofReal (bornWeight ψ x) := rfl

/-- `(Xᵘ Zᵛ ψ)(x) = (-1)^(v·(x-u)) ψ(x-u)`, in the conventional
operator order. The source basis vector `x-u` is first phased, then shifted. -/
def pauliAction (u v : Bits ι) (ψ : Amplitude ι) (x : Bits ι) : ℂ :=
  paritySign (v ⬝ᵥ (x - u)) * ψ (x - u)

/-- The explicit action is complex-linear. -/
def pauliOperator (u v : Bits ι) : Amplitude ι →ₗ[ℂ] Amplitude ι where
  toFun := pauliAction u v
  map_add' ψ φ := by
    ext x
    simp [pauliAction, mul_add]
  map_smul' c ψ := by
    ext x
    simp [pauliAction]
    ring

/-- The eigenvector premise is a pointwise equality of explicitly defined
linear-operator amplitudes. -/
def IsPauliEigenvector (ψ : Amplitude ι) (u v : Bits ι) (ζ : ℂ) : Prop :=
  ∀ x, pauliAction u v ψ x = ζ * ψ x

theorem pauliAction_norm_preserving (u v : Bits ι) (ψ : Amplitude ι) :
    (∑ x, bornWeight (pauliAction u v ψ) x) = ∑ x, bornWeight ψ x := by
  simp only [bornWeight, pauliAction, Complex.normSq_mul, paritySign_normSq, one_mul]
  exact Fintype.sum_equiv (Equiv.subRight u) _ _ (fun _ => rfl)

theorem pauliAction_preserves_normalization (u v : Bits ι) (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) : IsNormalized (pauliAction u v ψ) := by
  unfold IsNormalized
  rw [pauliAction_norm_preserving]
  exact hψ

/-- A normalized eigenvector of this explicit Pauli operator necessarily has
a unit-modulus eigenvalue. No unit-modulus assumption is required. -/
theorem eigenvalue_normSq_eq_one (ψ : Amplitude ι) (hψ : IsNormalized ψ)
    (u v : Bits ι) (ζ : ℂ) (heig : IsPauliEigenvector ψ u v ζ) :
    Complex.normSq ζ = 1 := by
  have h := pauliAction_norm_preserving u v ψ
  simp only [bornWeight] at h
  have heq : pauliAction u v ψ = fun x => ζ * ψ x := funext heig
  rw [heq] at h
  simp only [Complex.normSq_mul] at h
  rw [← Finset.mul_sum] at h
  change Complex.normSq ζ * (∑ x, bornWeight ψ x) = ∑ x, bornWeight ψ x at h
  rw [hψ, mul_one] at h
  exact h

/-- Stabilizer X labels act as translation symmetries of the computational
probabilities. This follows from the amplitude equation by taking norm squares. -/
theorem eigenvector_bornWeight_translation (ψ : Amplitude ι) (hψ : IsNormalized ψ)
    (u v : Bits ι) (ζ : ℂ) (heig : IsPauliEigenvector ψ u v ζ)
    (x : Bits ι) : bornWeight ψ (x + u) = bornWeight ψ x := by
  have h := congrArg Complex.normSq (heig (x + u))
  have hζ := eigenvalue_normSq_eq_one ψ hψ u v ζ heig
  simpa [pauliAction, Complex.normSq_mul, hζ, bornWeight] using h.symm

omit [DecidableEq ι] in
/-- At a nonzero amplitude of a diagonal Pauli eigenvector, the parity
character is forced to equal the eigenvalue. -/
theorem diagonal_eigenvalue_at_nonzero (ψ : Amplitude ι) (s : Bits ι) (ζ : ℂ)
    (heig : IsPauliEigenvector ψ 0 s ζ) (x : Bits ι) (hx : ψ x ≠ 0) :
    paritySign (s ⬝ᵥ x) = ζ := by
  classical
  have h := heig x
  simp only [pauliAction, sub_zero] at h
  exact mul_right_cancel₀ hx h

omit [DecidableEq ι] in
/-- Two outcomes in the amplitude support of a diagonal eigenvector have
the same parity, so their difference is orthogonal to its Z label. -/
theorem diagonal_eigenvector_difference (ψ : Amplitude ι) (s : Bits ι) (ζ : ℂ)
    (heig : IsPauliEigenvector ψ 0 s ζ) (x y : Bits ι)
    (hx : ψ x ≠ 0) (hy : ψ y ≠ 0) : s ⬝ᵥ (x - y) = 0 := by
  classical
  have hxζ := diagonal_eigenvalue_at_nonzero ψ s ζ heig x hx
  have hyζ := diagonal_eigenvalue_at_nonzero ψ s ζ heig y hy
  have hxy : s ⬝ᵥ x = s ⬝ᵥ y := paritySign_injective (hxζ.trans hyζ.symm)
  rw [dotProduct_sub, hxy, sub_self]

/-- The orthogonal complement written directly in binary dot products. -/
def orthogonalSet (D : Set (Bits ι)) : Set (Bits ι) :=
  {u | ∀ s ∈ D, s ⬝ᵥ u = 0}

/-- The diagonal annihilator is an additive subgroup, without needing to
assume that the supplied collection D is itself a subspace. -/
def orthogonalSubgroup (D : Set (Bits ι)) : AddSubgroup (Bits ι) where
  carrier := orthogonalSet D
  zero_mem' := by intro s _; simp
  add_mem' hu hv := by
    intro s hs
    rw [dotProduct_add, hu s hs, hv s hs, add_zero]
  neg_mem' hu := by
    intro s hs
    simpa only [dotProduct_neg, hu s hs] using (neg_zero : -(0 : ZMod 2) = 0)

omit [DecidableEq ι] in
@[simp] theorem mem_orthogonalSubgroup (D : Set (Bits ι)) (u : Bits ι) :
    u ∈ orthogonalSubgroup D ↔ u ∈ orthogonalSet D := Iff.rfl

omit [DecidableEq ι] in
/-- Every computational difference lies in the annihilator of all diagonal
stabilizers, even when the state has positive stabilizer nullity. -/
theorem supported_difference_orthogonal (ψ : Amplitude ι) (D : Set (Bits ι))
    (hD : ∀ s ∈ D, ∃ ζ, IsPauliEigenvector ψ 0 s ζ)
    (x y : Bits ι) (hx : ψ x ≠ 0) (hy : ψ y ≠ 0) :
    x - y ∈ orthogonalSet D := by
  classical
  intro s hs
  obtain ⟨ζ, heig⟩ := hD s hs
  exact diagonal_eigenvector_difference ψ s ζ heig x y hx hy

omit [DecidableEq ι] in
/-- The same guarantee stated in terms of positive-probability outcomes. -/
theorem positive_probability_difference_orthogonal (ψ : Amplitude ι)
    (D : Set (Bits ι)) (hD : ∀ s ∈ D, ∃ ζ, IsPauliEigenvector ψ 0 s ζ)
    (x y : Bits ι) (hx : 0 < bornWeight ψ x) (hy : 0 < bornWeight ψ y) :
    x - y ∈ orthogonalSet D :=
  supported_difference_orthogonal ψ D hD x y
    ((bornWeight_pos ψ x).mp hx) ((bornWeight_pos ψ y).mp hy)

omit [DecidableEq ι] in
/-- Choosing any supported basepoint places the entire amplitude support in
one affine coset of the diagonal annihilator. -/
theorem support_in_affine_annihilator (ψ : Amplitude ι) (D : Set (Bits ι))
    (hD : ∀ s ∈ D, ∃ ζ, IsPauliEigenvector ψ 0 s ζ)
    (z : Bits ι) (hz : ψ z ≠ 0) :
    ∀ x, ψ x ≠ 0 → x - z ∈ orthogonalSet D := by
  classical
  intro x hx
  exact supported_difference_orthogonal ψ D hD x z hx hz

/-- A collection of actual Pauli eigenlabels gives probability invariance
under every translation in their X projection. -/
theorem bornWeight_invariant_of_eigenlabels (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) (V : Set (Bits ι))
    (hV : ∀ u ∈ V, ∃ v ζ, IsPauliEigenvector ψ u v ζ) :
    ∀ u ∈ V, ∀ x, bornWeight ψ (x + u) = bornWeight ψ x := by
  intro u hu x
  obtain ⟨v, ζ, heig⟩ := hV u hu
  exact eigenvector_bornWeight_translation ψ hψ u v ζ heig x

/-- The finite affine coset `z + V`, expressed by subtraction. -/
def affineCoset (V : AddSubgroup (Bits ι)) (z : Bits ι) : Finset (Bits ι) := by
  classical
  exact Finset.univ.filter (fun x => x - z ∈ V)

@[simp] theorem mem_affineCoset (V : AddSubgroup (Bits ι)) (z x : Bits ι) :
    x ∈ affineCoset V z ↔ x - z ∈ V := by
  classical
  simp [affineCoset]

theorem affineCoset_card (V : AddSubgroup (Bits ι)) (z : Bits ι) :
    (affineCoset V z).card = Nat.card V := by
  classical
  let e : V ≃ ↥(affineCoset V z) := {
    toFun := fun u => ⟨z + u, by
      apply (mem_affineCoset V z _).mpr
      convert u.property using 1
      abel⟩
    invFun := fun x => ⟨x - z, (mem_affineCoset V z x).mp x.property⟩
    left_inv := by intro u; apply Subtype.ext; dsimp; abel
    right_inv := by intro x; apply Subtype.ext; dsimp; abel }
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using (Fintype.card_congr e).symm

/-- Invariance under all translations in V makes weights constant on every
affine V-coset, even if different cosets have different masses. -/
theorem bornWeight_constant_on_affineCoset (ψ : Amplitude ι)
    (V : AddSubgroup (Bits ι))
    (hinv : ∀ u ∈ V, ∀ x, bornWeight ψ (x + u) = bornWeight ψ x)
    (z x : Bits ι) (hx : x ∈ affineCoset V z) :
    bornWeight ψ x = bornWeight ψ z := by
  have h := hinv (x - z) ((mem_affineCoset V z x).mp hx) z
  have heq : z + (x - z) = x := by abel
  simpa only [heq] using h

/-- If the support is confined to one coset and every translation in its
direction space preserves probabilities, normalization forces the uniform
distribution on that coset. This is a derived Born-weight statement. -/
theorem bornWeight_uniform_affineCoset (ψ : Amplitude ι) (hψ : IsNormalized ψ)
    (V : AddSubgroup (Bits ι)) (z : Bits ι)
    (hsupp : ∀ x, ψ x ≠ 0 → x - z ∈ V)
    (hinv : ∀ u ∈ V, ∀ x, bornWeight ψ (x + u) = bornWeight ψ x)
    (x : Bits ι) (hx : x ∈ affineCoset V z) :
    bornWeight ψ x = 1 / (Nat.card V : ℝ) := by
  classical
  have hsum : (∑ y ∈ affineCoset V z, bornWeight ψ y) = 1 := by
    calc
      (∑ y ∈ affineCoset V z, bornWeight ψ y) = ∑ y, bornWeight ψ y := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro y _ hy
        apply (bornWeight_eq_zero ψ y).mpr
        by_contra hny
        exact hy ((mem_affineCoset V z y).mpr (hsupp y hny))
      _ = 1 := hψ
  have hconst : (∑ y ∈ affineCoset V z, bornWeight ψ y) =
      (Nat.card V : ℝ) * bornWeight ψ z := by
    calc
      (∑ y ∈ affineCoset V z, bornWeight ψ y) =
          ∑ _y ∈ affineCoset V z, bornWeight ψ z := by
        apply Finset.sum_congr rfl
        intro y hy
        exact bornWeight_constant_on_affineCoset ψ V hinv z y hy
      _ = _ := by simp [affineCoset_card, nsmul_eq_mul]
  have hc : (Nat.card V : ℝ) ≠ 0 := by
    simp only [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  rw [bornWeight_constant_on_affineCoset ψ V hinv z x hx]
  apply (eq_div_iff hc).mpr
  rw [mul_comm, ← hconst, hsum]

/-- The complete distribution, including its zero weights outside the coset. -/
theorem bornWeight_uniform_affineCoset_ite (ψ : Amplitude ι) (hψ : IsNormalized ψ)
    (V : AddSubgroup (Bits ι)) (z : Bits ι)
    (hsupp : ∀ x, ψ x ≠ 0 → x - z ∈ V)
    (hinv : ∀ u ∈ V, ∀ x, bornWeight ψ (x + u) = bornWeight ψ x)
    (x : Bits ι) :
    bornWeight ψ x = if x ∈ affineCoset V z then 1 / (Nat.card V : ℝ) else 0 := by
  classical
  by_cases hx : x ∈ affineCoset V z
  · rw [ite_eq_left hx]
    exact bornWeight_uniform_affineCoset ψ hψ V z hsupp hinv x hx
  · rw [ite_eq_right hx]
    apply (bornWeight_eq_zero ψ x).mpr
    by_contra hnx
    exact hx ((mem_affineCoset V z x).mpr (hsupp x hnx))

theorem normalized_has_nonzero_amplitude (ψ : Amplitude ι) (hψ : IsNormalized ψ) :
    ∃ z, ψ z ≠ 0 := by
  by_contra! hzero
  have hsum : (∑ x, bornWeight ψ x) = 0 := by simp [bornWeight, hzero]
  rw [hψ] at hsum
  norm_num at hsum

/-- Operational uniform-support consequence of a complete collection of
Pauli eigenlabels. Diagonal eigenlabels confine the support, and a Pauli
eigenlabel above every direction in their annihilator forces uniformity.
The latter existence premise is the algebraic X-projection theorem for a
maximal stabilizer space; no probability-uniformity hypothesis is assumed. -/
theorem uniform_bornWeight_of_complete_eigenlabels (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) (D : Set (Bits ι))
    (hD : ∀ s ∈ D, ∃ ζ, IsPauliEigenvector ψ 0 s ζ)
    (hX : ∀ u ∈ orthogonalSubgroup D, ∃ v ζ, IsPauliEigenvector ψ u v ζ) :
    ∃ z, ∀ x, bornWeight ψ x =
      if x ∈ affineCoset (orthogonalSubgroup D) z then
        1 / (Nat.card (orthogonalSubgroup D) : ℝ) else 0 := by
  classical
  obtain ⟨z, hz⟩ := normalized_has_nonzero_amplitude ψ hψ
  refine ⟨z, ?_⟩
  intro x
  apply bornWeight_uniform_affineCoset_ite ψ hψ (orthogonalSubgroup D) z
  · exact support_in_affine_annihilator ψ D hD z hz
  · intro u hu y
    obtain ⟨v, ζ, heig⟩ := hX u hu
    exact eigenvector_bornWeight_translation ψ hψ u v ζ heig y

end LeanPool.SingleCopyStabilizer.Measurement

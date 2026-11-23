/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.GeometricRotation

/-!
# The centered rotation group

All rotations about the origin preserving the real locus form a finite cyclic group obeying the
sharp bound.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- All rotations about zero preserving the whole real locus, represented by complex units. -/
noncomputable def centeredRotationGroup (P : BPoly) : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1 ∧ ∀ z : ℂ, (u : ℂ) * z ∈ realLocus P ↔ z ∈ realLocus P}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    refine ⟨by simp [hu.1, hv.1], ?_⟩
    intro z
    simpa only [Units.val_mul, mul_assoc] using (hu.2 ((v : ℂ) * z)).trans (hv.2 z)
  inv_mem' := by
    intro u hu
    refine ⟨by simpa using congrArg Inv.inv hu.1, ?_⟩
    intro z
    simpa [← mul_assoc] using (hu.2 ((↑u⁻¹ : ℂ) * z)).symm

/-- A centered rotation, viewed as its complex multiplier. -/
noncomputable def rotationValue (P : BPoly) : centeredRotationGroup P →* ℂ :=
  (Units.coeHom ℂ).comp (centeredRotationGroup P).subtype

lemma rotationValue_injective (P : BPoly) : Function.Injective (rotationValue P) := by
  intro u v h
  apply Subtype.ext
  exact Units.ext h

lemma exists_off_diagonal_coeff {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    ∃ a b : ℕ, a ≠ b ∧ P.coeff (exponent a b) ≠ 0 := by
  by_contra h
  push Not at h
  apply hcircle
  apply radial_realLocus_is_circle hinf
  apply irreducible_radial_form hP
  intro s hs
  by_contra hne
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  exact (mem_support_iff.mp hs) (by rw [he]; exact h (s 0) (s 1) hne)

lemma rotation_value_root {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) {a b : ℕ}
    (hc : P.coeff (exponent a b) ≠ 0) (u : centeredRotationGroup P) :
    (rotationValue P u) ^ (2 * a) = (rotationValue P u) ^ (2 * b) := by
  have hsign := rotation_sign_of_realLocus hP hinf u.prop.1
    (fun z hz => (u.prop.2 z).mpr hz)
  have hchar : (rotationValue P u) ^ a * (rotationValue P u)⁻¹ ^ b = 1 ∨
      (rotationValue P u) ^ a * (rotationValue P u)⁻¹ ^ b = -1 := by
    rcases hsign with h | h
    · left
      have he := congrArg (fun Q : BPoly => Q.coeff (exponent a b)) h
      rw [coeff_rotate] at he
      apply mul_left_cancel₀ hc
      simpa [rotationValue] using he
    · right
      have he := congrArg (fun Q : BPoly => Q.coeff (exponent a b)) h
      rw [coeff_rotate, coeff_neg] at he
      apply mul_left_cancel₀ hc
      simpa [rotationValue] using he
  have hs : ((rotationValue P u) ^ a * (rotationValue P u)⁻¹ ^ b) ^ 2 = 1 := by
    rcases hchar with h | h <;> rw [h] <;> norm_num
  have hne : rotationValue P u ≠ 0 := u.val.ne_zero
  rw [mul_pow, inv_pow, ← pow_mul, ← inv_pow, ← pow_mul] at hs
  have he : (rotationValue P u) ^ (a * 2) = (rotationValue P u) ^ (b * 2) := by
    apply (div_eq_one_iff_eq (pow_ne_zero _ hne)).mp
    simpa [div_eq_mul_inv] using hs
  simpa [Nat.mul_comm] using he

/-- Finiteness is proved from a nonzero one-variable polynomial containing every multiplier. -/
theorem centeredRotationGroup_finite {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    Finite (centeredRotationGroup P) := by
  classical
  obtain ⟨a, b, hab, hc⟩ := exists_off_diagonal_coeff hP hinf hcircle
  let q : Polynomial ℂ := Polynomial.X ^ (2 * a) - Polynomial.X ^ (2 * b)
  have hq : q ≠ 0 := by
    intro h
    have he := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
    simp only [Polynomial.natDegree_X_pow] at he
    omega
  have hroots : ∀ u : centeredRotationGroup P, q.IsRoot (rotationValue P u) := by
    intro u
    simpa [q, Polynomial.IsRoot] using sub_eq_zero.mpr (rotation_value_root hP hinf hc u)
  let : Fintype {z : ℂ // q.IsRoot z} := (Polynomial.finite_setOfPred_isRoot hq).fintype
  exact Finite.of_injective (fun u => (⟨rotationValue P u, hroots u⟩ : {z : ℂ // q.IsRoot z}))
    (fun _ _ h => rotationValue_injective P (congrArg Subtype.val h))

/-- The whole centered rotation group is finite cyclic and satisfies the sharp upper bound. -/
theorem centered_rotation_group_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    Finite (centeredRotationGroup P) ∧ IsCyclic (centeredRotationGroup P) ∧
      Nat.card (centeredRotationGroup P) ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  let := centeredRotationGroup_finite hP hinf hcircle
  let := isCyclic_of_injective_ringHom (rotationValue P) (rotationValue_injective P)
  refine ⟨inferInstance, inferInstance, ?_⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := centeredRotationGroup P)
  have hroot : IsPrimitiveRoot (rotationValue P u) (Nat.card (centeredRotationGroup P)) := by
    rw [← hu]
    exact (IsPrimitiveRoot.orderOf u).map_of_injective (rotationValue_injective P)
  exact geometric_rotation_order_bound hP hd hinf hcircle (Nat.card_pos.ne') hroot
    (fun z hz => (u.prop.2 z).mpr hz)

end CurveSymmetry

/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.EuclideanCenter

/-!
# Change of center

The translation `shift c` of plane polynomials, its composition law, and its effect on the total
degree.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Translation of a plane polynomial by `c`, in complex coordinates: `z ↦ z + c`. -/
noncomputable def shift (c : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => X i + C (if i = 0 then c else star c))

lemma shift_zero (P : BPoly) : shift 0 P = P := by
  simp [shift]

lemma shift_comp (c d : ℂ) (P : BPoly) : shift c (shift d P) = shift (c + d) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [shift]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [shift, star_add, map_add, add_assoc]

/-- `shift c` as a ring isomorphism, with inverse `shift (-c)`. -/
noncomputable def shiftEquiv (c : ℂ) : BPoly ≃+* BPoly :=
  { shift c with
    invFun := shift (-c)
    left_inv := fun P => by
      change shift (-c) (shift c P) = P
      rw [shift_comp, neg_add_cancel, shift_zero]
    right_inv := fun P => by
      change shift c (shift (-c) P) = P
      rw [shift_comp, add_neg_cancel, shift_zero] }

lemma totalDegree_sum_le {ι : Type*} (s : Finset ι) (F : ι → BPoly) (d : ℕ)
    (h : ∀ i ∈ s, (F i).totalDegree ≤ d) : (∑ i ∈ s, F i).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (totalDegree_add _ _).trans (max_le (h a (by simp))
        (ih (fun i hi => h i (by simp [hi]))))

lemma shift_monomial (c a : ℂ) (s : Exponent) :
    shift c (monomial s a) = C a * ((X 0 : BPoly) + C c) ^ s 0 *
      (X 1 + C (star c)) ^ s 1 := by
  simp only [shift, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp [mul_assoc]

lemma shift_degree_le (c : ℂ) (P : BPoly) : (shift c P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_sum_le
  intro s hs
  rw [shift_monomial]
  have h0 := totalDegree_add (X 0 : BPoly) (C c)
  have h1 := totalDegree_add (X 1 : BPoly) (C (star c))
  simp only [totalDegree_X, totalDegree_C, max_eq_left (by omega : 0 ≤ 1)] at h0 h1
  have hp0 := (totalDegree_pow ((X 0 : BPoly) + C c) (s 0)).trans
    (Nat.mul_le_mul_left (s 0) h0)
  have hp1 := (totalDegree_pow ((X 1 : BPoly) + C (star c)) (s 1)).trans
    (Nat.mul_le_mul_left (s 1) h1)
  have hm0 := totalDegree_mul (C (P.coeff s) : BPoly) ((X 0 + C c) ^ s 0)
  have hm1 := totalDegree_mul (C (P.coeff s) * (X 0 + C c) ^ s 0 : BPoly)
    ((X 1 + C (star c)) ^ s 1)
  simp only [totalDegree_C, zero_add, Nat.mul_one] at hp0 hp1 hm0
  have hd := support_degree hs
  omega

lemma shift_degree (c : ℂ) (P : BPoly) : (shift c P).totalDegree = P.totalDegree := by
  apply le_antisymm (shift_degree_le c P)
  have h := shift_degree_le (-c) (shift c P)
  simpa [shift_comp, shift_zero] using h

lemma eval_shift (c : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (shift c P) =
      eval (fun i : Fin 2 => if i = 0 then z + c else star (z + c)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [shift]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [shift, star_add]

lemma mem_realLocus_shift (c : ℂ) (P : BPoly) (z : ℂ) :
    z ∈ realLocus (shift c P) ↔ z + c ∈ realLocus P := by
  change eval _ (shift c P) = 0 ↔ _
  rw [eval_shift]
  rfl

lemma realLocus_shift_infinite (c : ℂ) {P : BPoly} (hinf : (realLocus P).Infinite) :
    (realLocus (shift c P)).Infinite := by
  have h := hinf.image (f := fun z : ℂ => z - c) (by
    intro x _ y _ h; exact sub_left_injective h)
  apply h.mono
  rintro _ ⟨z, hz, rfl⟩
  simpa [mem_realLocus_shift] using hz

/-- The real locus of `P` is not a circle of positive radius. -/
def NotCircle (P : BPoly) : Prop :=
  ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere c R

lemma shifted_not_circle (c : ℂ) {P : BPoly} (hcircle : NotCircle P) :
    ¬ ∃ R : ℝ, 0 < R ∧ realLocus (shift c P) = Metric.sphere (0 : ℂ) R := by
  rintro ⟨R, hR, he⟩
  apply hcircle
  refine ⟨c, R, hR, ?_⟩
  ext z
  have h := congrArg (fun S : Set ℂ => z - c ∈ S) he
  simpa [mem_realLocus_shift, Metric.mem_sphere, dist_eq_norm] using h

end CurveSymmetry

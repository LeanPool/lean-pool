/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Fermat

/-!
# Sharpness

`Re(z^d) = 1` attains the full Euclidean bound in every degree at least two, and the maximum
direct-symmetry count is attained in every degree.
-/

@[expose] public section

namespace CurveSymmetry

theorem fermat_not_circle {d : ℕ} (hd : 0 < d) : NotCircle (fermatPolynomial d) := by
  rintro ⟨c, R, hR, he⟩
  let t : ℝ := (‖c‖ + R) ^ d + 1
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (1 + (t : ℂ) * Complex.I) hd
  have hmem : z ∈ realLocus (fermatPolynomial d) := by
    change MvPolynomial.eval _ (fermatPolynomial d) = 0
    rw [eval_fermat, hz]
    simp [star_add, star_mul]
    ring
  rw [he, Metric.mem_sphere, dist_eq_norm] at hmem
  have hb := norm_add_le (z - c) c
  rw [sub_add_cancel, hmem] at hb
  have hpow := pow_le_pow_left₀ (norm_nonneg z) hb d
  have him := Complex.abs_im_le_norm (z ^ d)
  have him' : (z ^ d).im = t := by rw [hz]; simp
  rw [him', abs_of_pos ht, norm_pow] at him
  dsimp [t] at him
  have he' : R + ‖c‖ = ‖c‖ + R := add_comm _ _
  rw [he'] at hpow
  linarith

lemma fermat_root_symmetry {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hroot : ζ ^ d = 1) :
    DirectSymmetry (realLocus (fermatPolynomial d)) ζ 0 := by
  have hn : ‖ζ‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hd.ne').mp
    simpa using congrArg norm hroot
  refine ⟨hn, ?_⟩
  intro z
  simp only [add_zero]
  change MvPolynomial.eval _ (fermatPolynomial d) = 0 ↔ MvPolynomial.eval _ (fermatPolynomial d) = 0
  rw [eval_fermat, eval_fermat, mul_pow, hroot, one_mul]

lemma fermat_conjugation (d : ℕ) : OppositeSymmetry (realLocus (fermatPolynomial d)) 1 0 := by
  refine ⟨by simp, ?_⟩
  intro z
  simp only [one_mul, add_zero]
  change MvPolynomial.eval _ (fermatPolynomial d) = 0 ↔ MvPolynomial.eval _ (fermatPolynomial d) = 0
  rw [eval_fermat, eval_fermat]
  simp [add_comm]

theorem fermat_direct_card {d : ℕ} (hd : 2 ≤ d) :
    Nat.card (DirectSymmetries (fermatPolynomial d)) = d := by
  have hd' : 0 < d := by omega
  have hirr := fermat_irreducible hd'
  have hinf := fermat_realLocus_infinite hd'
  have hdeg : 2 ≤ (fermatPolynomial d).totalDegree := by rwa [fermat_degree hd']
  have hnc := fermat_not_circle hd'
  let := (direct_euclidean_bound hirr hdeg hinf hnc).1
  let : NeZero d := ⟨hd'.ne'⟩
  let f : rootsOfUnity d ℂ → DirectSymmetries (fermatPolynomial d) := fun u =>
    ⟨((u.val : ℂ), 0), fermat_root_symmetry hd' ((mem_rootsOfUnity' _ _).mp u.prop)⟩
  have hi : Function.Injective f := by
    intro u v h
    exact rootsOfUnity.coe_injective (congrArg (fun w => w.val.1) h)
  have hlo := Nat.card_le_card_of_injective f hi
  rw [Complex.card_rootsOfUnity] at hlo
  have hhi := direct_bound_with_opposite hirr hdeg hinf hnc ⟨(1, 0), fermat_conjugation d⟩
  rw [fermat_degree hd'] at hhi
  omega

/-- `Re(z^d) = 1` attains the full Euclidean bound in every degree at least two. -/
theorem fermat_full_card {d : ℕ} (hd : 2 ≤ d) :
    Nat.card (EuclideanSymmetries (fermatPolynomial d)) = 2 * d := by
  have hd' : 0 < d := by omega
  let := (direct_euclidean_bound (fermat_irreducible hd')
    (by rw [fermat_degree hd']; exact hd) (fermat_realLocus_infinite hd') (fermat_not_circle hd')).1
  let g : OppositeSymmetries (fermatPolynomial d) := ⟨(1, 0), fermat_conjugation d⟩
  let : Finite (OppositeSymmetries (fermatPolynomial d)) := Finite.of_injective
    (oppositeDirectEquiv _ g) (oppositeDirectEquiv _ g).injective
  change Nat.card
    (DirectSymmetries (fermatPolynomial d) ⊕ OppositeSymmetries (fermatPolynomial d)) = _
  rw [Nat.card_sum, Nat.card_congr (oppositeDirectEquiv _ g), fermat_direct_card hd]
  omega

/-- The exact maximum direct-symmetry count is attained in every degree. -/
theorem rotation_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : BPoly, Irreducible P ∧ P.totalDegree = d ∧ (realLocus P).Infinite ∧ NotCircle P ∧
      Nat.card (DirectSymmetries P) = max d (2 * d - 4) := by
  by_cases hsmall : d < 4
  · refine ⟨fermatPolynomial d, fermat_irreducible (by omega), fermat_degree (by omega),
      fermat_realLocus_infinite (by omega), fermat_not_circle (by omega), ?_⟩
    rw [fermat_direct_card hd]
    omega
  · have hm : 2 ≤ d - 2 := by omega
    have hm' : 0 < d - 2 := by omega
    have hI : Complex.I ≠ star Complex.I := by
      intro h
      have he := congrArg Complex.im h
      norm_num at he
    refine ⟨familyPolynomial (d - 2) Complex.I, familyPolynomial_irreducible hm' hI,
      ?_, family_realLocus_infinite hm' hI, family_not_circle hm' hI, ?_⟩
    · rw [family_degree hm']; omega
    · rw [family_direct_card hm hI]; omega

theorem full_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : BPoly, Irreducible P ∧ P.totalDegree = d ∧ (realLocus P).Infinite ∧ NotCircle P ∧
      Nat.card (EuclideanSymmetries P) = 2 * d := by
  exact ⟨fermatPolynomial d, fermat_irreducible (by omega), fermat_degree (by omega),
    fermat_realLocus_infinite (by omega), fermat_not_circle (by omega), fermat_full_card hd⟩

end CurveSymmetry

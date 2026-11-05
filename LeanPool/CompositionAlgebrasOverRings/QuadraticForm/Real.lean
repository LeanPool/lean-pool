/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Real

/-!
# Anisotropic real quadratic forms are definite, and determined by their dimension and sign

The existence half of Sylvester's law of inertia — mathlib's
`QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared` — writes a real quadratic form as
a weighted sum of squares with weights `-1`, `0`, `1`. Anisotropy
forbids the weight `0`, and forbids `-1` and `1` from occurring together — a weight `0` gives a null
basis vector, and opposite weights give a null sum of two basis vectors. So an anisotropic real form
is `± (x₁² + ⋯ + xₙ²)`, and the sign is decided by any single value.

Consequently two anisotropic real quadratic forms of the same dimension taking a positive value are
isometric. This is the classification input the real case of the composition-algebra classification
needs; the composition norm takes the value `1` at the identity element. TauCeti has the general
classification of real quadratic forms by signature
(`QuadraticForm.equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq`) and the definiteness
criterion used here (`QuadraticForm.anisotropic_iff_posDef_or_negDef`); this file records only the
corollary in the form the classification consumes.

## Main results

* `QuadraticForm.equivalent_sumSquares_of_anisotropic` : an anisotropic real form with a positive
  value is equivalent to the sum of `finrank` squares.
* `QuadraticForm.posDef_of_anisotropic` : such a form is positive definite.
* `QuadraticForm.equivalent_of_anisotropic_of_finrank_eq` : two anisotropic real forms of equal
  dimension, each taking a positive value, are equivalent.

## References

* Sylvester, *A demonstration of the theorem that every homogeneous quadratic polynomial is
  reducible by real orthogonal substitutions to the form of a sum of positive and negative
  squares*, Philosophical Magazine **4** (1852), 138–142.
-/

@[expose] public section

universe v w

open QuadraticMap

namespace QuadraticForm

variable {M : Type v} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  {N : Type w} [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ N] in
/-- Anisotropy transports backwards along an isometry. -/
private theorem anisotropic_of_isometryEquiv {Q : QuadraticForm ℝ M} {P : QuadraticForm ℝ N}
    (e : Q.IsometryEquiv P) (h : Q.Anisotropic) : P.Anisotropic := fun x hx ↦ by
  have hQ : Q (e.symm x) = 0 := by
    rw [← e.map_app (e.symm x), e.apply_symm_apply]; exact hx
  rw [← e.apply_symm_apply x, h _ hQ, map_zero]

/-- **An anisotropic real quadratic form taking a positive value is a sum of squares.** By
Sylvester's law it is a weighted sum of squares with weights in `{-1, 0, 1}`; a zero weight would
make a basis vector null, and a `-1` alongside a `1` would make the sum of the two corresponding
basis vectors null. A positive value forces the common weight to be `1`. -/
theorem equivalent_sumSquares_of_anisotropic (Q : QuadraticForm ℝ M) (hani : Q.Anisotropic)
    {v : M} (hv : 0 < Q v) :
    Q.Equivalent (weightedSumSquares ℝ (1 : Fin (Module.finrank ℝ M) → ℝ)) := by
  classical
  obtain ⟨w, hw, ⟨e⟩⟩ := Q.equivalent_one_zero_neg_one_weighted_sum_squared
  have hani' : (weightedSumSquares ℝ w).Anisotropic := anisotropic_of_isometryEquiv e hani
  -- The value of the weighted sum of squares at a single basis vector is the weight.
  have hsingle : ∀ i, weightedSumSquares ℝ w (Pi.single i (1 : ℝ)) = w i := by
    intro i
    rw [weightedSumSquares_apply]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hj
      simp [hj]
  -- The value at the sum of two distinct basis vectors is the sum of the two weights.
  have hpair : ∀ i j, i ≠ j →
      weightedSumSquares ℝ w (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) = w i + w j := by
    intro i j hij
    rw [weightedSumSquares_apply,
      ← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin (Module.finrank ℝ M))))
        (fun k _ hk ↦ by
          have hki : k ≠ i := fun h ↦ hk (by simp [h])
          have hkj : k ≠ j := fun h ↦ hk (by simp [h])
          simp [hki, hkj]),
      Finset.sum_pair hij]
    simp [hij, Ne.symm hij]
  -- Some weight is positive, since the form takes a positive value.
  have hpos : ∃ j, w j = 1 := by
    by_contra hcon
    have hcon' : ∀ j, w j ≠ 1 := fun j hj ↦ hcon ⟨j, hj⟩
    have hle : weightedSumSquares ℝ w (e v) ≤ 0 := by
      rw [weightedSumSquares_apply]
      refine Finset.sum_nonpos fun j _ ↦ ?_
      have : w j ≤ 0 := by rcases hw j with h | h | h <;> simp_all
      simpa using mul_nonpos_of_nonpos_of_nonneg this (mul_self_nonneg _)
    rw [e.map_app v] at hle
    exact absurd hv (not_lt.mpr hle)
  -- Every weight is `1`: none is `0`, and none is `-1`.
  have hone : ∀ i, w i = 1 := by
    intro i
    rcases hw i with h | h | h
    · exfalso
      obtain ⟨j, hj⟩ := hpos
      have hij : i ≠ j := fun hij ↦ by rw [hij, hj] at h; norm_num at h
      have hnull := hani' _ ((hpair i j hij).trans (by rw [h, hj]; ring))
      simpa [hij] using congrFun hnull i
    · exfalso
      have hnull := hani' _ ((hsingle i).trans h)
      simpa using congrFun hnull i
    · exact h
  have hw1 : w = 1 := funext hone
  subst hw1
  exact ⟨e⟩

omit [FiniteDimensional ℝ M] in
/-- An anisotropic real quadratic form taking a positive value is positive definite: by TauCeti's
`QuadraticForm.anisotropic_iff_posDef_or_negDef` it is positive or negative definite, and the
positive value rules out the second. -/
theorem posDef_of_anisotropic (Q : QuadraticForm ℝ M) (hani : Q.Anisotropic) {v : M}
    (hv : 0 < Q v) : Q.PosDef := by
  refine ((QuadraticForm.anisotropic_iff_posDef_or_negDef Q).mp hani).resolve_right fun hneg ↦ ?_
  have hv0 : v ≠ 0 := fun h ↦ by simp [h] at hv
  have := hneg v hv0
  simp only [neg_apply, Left.neg_pos_iff] at this
  exact absurd hv (not_lt.mpr this.le)

/-- **Anisotropic real quadratic forms are classified by their dimension and sign.** Two
anisotropic real forms of the same dimension, each taking a positive value, are isometric. The sign
hypothesis cannot be dropped: `x²` and `-x²` are anisotropic of the same dimension but not
isometric. -/
theorem equivalent_of_anisotropic_of_finrank_eq {Q : QuadraticForm ℝ M} {P : QuadraticForm ℝ N}
    (hQ : Q.Anisotropic) (hP : P.Anisotropic) {v : M} (hv : 0 < Q v) {u : N} (hu : 0 < P u)
    (hdim : Module.finrank ℝ M = Module.finrank ℝ N) : Q.Equivalent P := by
  have hmid : (weightedSumSquares ℝ (1 : Fin (Module.finrank ℝ M) → ℝ)).Equivalent
      (weightedSumSquares ℝ (1 : Fin (Module.finrank ℝ N) → ℝ)) := by
    rw [hdim]
    exact ⟨QuadraticMap.IsometryEquiv.refl _⟩
  exact ((Q.equivalent_sumSquares_of_anisotropic hQ hv).trans hmid).trans
    (P.equivalent_sumSquares_of_anisotropic hP hu).symm

end QuadraticForm

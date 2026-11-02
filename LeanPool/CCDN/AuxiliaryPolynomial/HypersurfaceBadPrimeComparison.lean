/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
public import LeanPool.CCDN.Determinant.HypersurfaceDeterminantRank
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceHeightComparison
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
import LeanPool.CCDN.Determinant.HomogeneousDeterminantComparison

/-! Preserve the bad-prime factor through the normalized no-auxiliary
comparison, as required by the coefficient-sensitive CCDN Theorem 3.1.1.

`AuxiliaryRankComparison order f d z bad` is the conclusion of the comparison for a
finite prime set `bad`. It follows from a determinant lower bound with the charge of
`bad` for every subfamily of the points (`auxiliaryRankComparison_of_determinant_lower`);
the hypersurface instance uses the exact geometric bad-prime set. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The dimension-dependent error term in the normalized no-auxiliary comparison that retains
the bad-prime charge, for forms in `n + 3` variables: the determinant error plus the
archimedean error normalized by $(n + 2) / ((n + 1)!)^{1/(n + 1)}$. -/
def hypersurfaceBadPrimeNormalizedError (n : ℕ) : ℝ :=
  hypersurfaceDeterminantError n +
    (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The normalized no-auxiliary comparison with the charge of a finite prime set `bad`:
for every radius `B ≥ 1` bounding the points `z` and every degree `M ≥ d` in which each
form vanishing on `z` is a multiple of `f`, the rank `s` of the evaluation matrix
satisfies the normalized comparison retaining `log b = ∑ p ∈ bad, log p / p`. -/
def AuxiliaryRankComparison {n t : ℕ} (order : MonomialOrder (Fin (n + 3)))
    (f : MvPolynomial (Fin (n + 3)) ℤ) (d : ℕ) (z : Fin t → IntPoint (n + 3))
    (bad : Finset ℕ) : Prop :=
  ∀ ⦃B : ℝ⦄, 1 ≤ B → (∀ i, InBox (z i) B) → ∀ ⦃M : ℕ⦄, d ≤ M →
    (∀ g : MvPolynomial (Fin (n + 3)) ℤ, g.IsHomogeneous M → (∀ i, eval (z i) g = 0) → f ∣ g) →
    ∃ s : ℕ, 0 < s ∧ s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M ∧
      factorialRoot n * (s : ℝ) ^ (1 / (n + 1 : ℝ)) / ((n + 2 : ℝ) * M) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + (∑ p ∈ bad, Real.log p / p)) -
          hypersurfaceBadPrimeNormalizedError n) ≤
        Real.log B - ((n + 2 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) *
          Real.log |((order.leadingCoeff f : ℤ) : ℝ)|

/-- The comparison follows from the rank-form determinant lower bound with the charge of
`bad`, for every subfamily of the points and every family of common-degree forms. -/
theorem auxiliaryRankComparison_of_determinant_lower {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (z : Fin t → IntPoint (n + 3)) (hz : ∀ i, eval (z i) f = 0) (bad : Finset ℕ)
    (hdet : ∀ ⦃s N M : ℕ⦄ (a : Fin s → Fin t) (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ),
      0 < s → (∀ j, (F j).IsHomogeneous M) →
      LinearIndependent ℚ ((Matrix.of fun i j => eval (z (a i)) (F j)).map ((↑) : ℤ → ℚ)).row →
      hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z (a i)) (F j)))) :
    AuxiliaryRankComparison order f d z bad := by
  intro B hB hbox M hdM hrel
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hz hB hbox hrel
  have hs := hypersurface_homogeneous_rank_pos hd hdM hr
  let F := fun j => (monomial (homogeneousMonomials (n + 2) M j) 1 : MvPolynomial (Fin (n + 3)) ℤ)
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree (n + 2) M j)
  have he : (Matrix.of fun i j => eval (z (a i)) (F j)) =
      evaluationMatrix (homogeneousMonomials (n + 2) M) (z ∘ a) := by
    ext i j
    simp [F, evaluationMatrix, eval_monomial]
  have hlower := hdet a F hs hF (by rw [he]; exact hi)
  rw [he] at hlower
  have hc := hlower.trans hupper
  refine ⟨s, hs, hr, ?_⟩
  have hnN : n + 1 + 1 = n + 2 := by omega
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hh := hypersurface_rank_comparison_normalized (r := n + 1) (by omega) hd hdM hr
    B |((order.leadingCoeff f : ℤ) : ℝ)| (primeSetFactor bad)
    (hypersurfaceDeterminantError n)
    (by simpa only [hypersurfaceRankLowerBound, hnN, Nat.cast_add, Nat.cast_one, hnR,
      Real.log_exp] using hc)
  simpa only [hypersurfaceBadPrimeNormalizedError, hnN, Nat.cast_add, Nat.cast_one, hnR,
    Real.log_exp] using hh

/-- The comparison retaining `log b(f)` for the exact geometric bad-prime set, rather
than replacing it by the coefficient-height upper bound. -/
theorem hypersurface_auxiliaryRankComparison {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) :
    AuxiliaryRankComparison order f d z bad :=
  auxiliaryRankComparison_of_determinant_lower order f hf hf0 hd z hz bad
    fun _ _ _ a F hs hF hi => hypersurface_determinant_log_lower_at_rank hs f hf hd F hF
      (z ∘ a) (fun i => hprim (a i)) (fun i => hz (a i)) hi bad
      fun p _ hp hcut => hasGoodReduction_of_not_mem hbad p (Finset.mem_sdiff.mp hp).2 hcut

end
end CCDN

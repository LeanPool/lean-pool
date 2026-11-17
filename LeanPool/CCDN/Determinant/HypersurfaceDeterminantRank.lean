/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import LeanPool.CCDN.Determinant.HypersurfaceLocalDivisor
import LeanPool.CCDN.Determinant.PrimeAggregation

/-! Choosing the prime endpoint at the dimension root of the row count
produces the exact rank power and leading constant in CCDN Proposition 3.2.6.
The aggregation step takes the local prime-power divisors as a hypothesis, so it
applies to minor gcds, determinant-family gcds and affine-chart reductions alike. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- An explicit error depending only on hypersurface dimension. -/
def hypersurfaceDeterminantError (n : ℕ) : ℝ :=
  (n + 1 : ℝ) *
      (Real.log 27 + 2 * mertensError + 2 * hypersurfaceCountConstant n * primeBlockMass) +
    (n + 2 : ℝ) ^ 2 / ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (Real.log 4 + 4)

/-- The rank form of the lower bound in CCDN Proposition 3.2.6 for `s` points on a
hypersurface of degree `d` with bad-prime charge `c`:
`((n+1)!)^(1/(n+1)) / (n+2) * s^(1+1/(n+1)) * (log s - (n+1) (4 log d + c) - E_n)`. -/
def hypersurfaceRankLowerBound (n s d : ℕ) (c : ℝ) : ℝ :=
  factorialRoot n / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
    (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + c) - hypersurfaceDeterminantError n)

private lemma hypersurface_rank_prime_endpoint (n s : ℕ) (hs : 0 < s) :
    1 ≤ (s : ℝ) ^ (1 / (n + 1 : ℝ)) := by
  apply Real.one_le_rpow
  · exact_mod_cast hs
  · positivity

private lemma hypersurface_determinant_rank_identity (n s d : ℕ) (hs : 0 < s) (charge : ℝ) :
    hypersurfaceDeterminantMain n s *
        (Real.log ((s : ℝ) ^ (1 / (n + 1 : ℝ))) - 4 * Real.log d - Real.log 27 -
          2 * mertensError - charge - 2 * hypersurfaceCountConstant n * primeBlockMass) -
        ((n + 2 : ℝ) * s) * ((Real.log 4 + 4) * (s : ℝ) ^ (1 / (n + 1 : ℝ))) =
      hypersurfaceRankLowerBound n s d charge := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  have hfac : ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) ≠ 0 := by positivity
  have hp : (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) =
      (s : ℝ) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [Real.rpow_add hs0, Real.rpow_one]
  rw [Real.log_rpow hs0]
  unfold hypersurfaceRankLowerBound hypersurfaceDeterminantMain hypersurfaceDeterminantError
  rw [hp]
  field_simp
  ring

/-- Prime aggregation at the rank endpoint `x = s ^ (1 / (n + 1))`. Local divisors of `D`
with the hypersurface exponent at every good prime above `27 d ^ 4`, together with
prescribed divisors at the primes of `P ⊆ bad`, give the rank form of
CCDN Proposition 3.2.6. -/
theorem hypersurface_log_lower_at_rank_of_local_divisors_congruence {n s d : ℕ}
    (hs : 0 < s) (hd : 0 < d) (bad P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hlocal : ∀ p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad,
      stepanovThreshold (d : ℝ) < p → ∃ e : ℕ, hypersurfaceDeterminantMain n s /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) - (n + 2 : ℝ) * s ≤ e ∧
        (p : ℤ) ^ e ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣ D) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  have h := determinant_log_lower_of_local_divisors_degree_four
    (hypersurface_rank_prime_endpoint n s hs) hd (hypersurfaceCountConstant_nonneg n)
    (hypersurfaceDeterminantMain_nonneg n s) (by positivity) bad P hPbad hP v hD hlocal hcong
  rwa [hypersurface_determinant_rank_identity n s d hs] at h

/-- `hypersurface_log_lower_at_rank_of_local_divisors_congruence` without prescribed
divisors. -/
theorem hypersurface_log_lower_at_rank_of_local_divisors {n s d : ℕ}
    (hs : 0 < s) (hd : 0 < d) (bad : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hlocal : ∀ p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad,
      stepanovThreshold (d : ℝ) < p → ∃ e : ℕ, hypersurfaceDeterminantMain n s /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) - (n + 2 : ℝ) * s ≤ e ∧
        (p : ℤ) ^ e ∣ D) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) ≤ Real.log D := by
  have h := hypersurface_log_lower_at_rank_of_local_divisors_congruence hs hd bad ∅
    (empty_subset bad) (by simp) 0 hD hlocal (by simp)
  rwa [sum_empty, add_zero] at h

/-- The higher-dimensional rank-cutoff form of Proposition 3.2.6 for
maximal minors and common-degree homogeneous evaluation columns. -/
theorem hypersurface_determinant_log_lower_at_rank {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    (bad : Finset ℕ)
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      stepanovThreshold (d : ℝ) < p →
      HasGoodReduction f p) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  refine hypersurface_log_lower_at_rank_of_local_divisors hs hd bad
    (one_pos.trans_le (Int.Matrix.one_le_minorGcd hrows)) fun p hp hcut => ?_
  have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
  obtain ⟨hf0, hir⟩ := hred p hp hcut
  simpa only [hypersurfaceDeterminantMain_div] using
    projective_hypersurface_minorGcd_dvd f hf hd hf0 hir hcut F hF z hprim hz

end
end CCDN

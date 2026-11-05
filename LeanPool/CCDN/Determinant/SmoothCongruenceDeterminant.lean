/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.HypersurfaceDeterminantRank
public import LeanPool.CCDN.Height.CountingHypotheses
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import LeanPool.CCDN.Determinant.HypersurfaceMultiplicityEstimate
import LeanPool.CCDN.Determinant.SmoothProjectiveCongruence

/-!
The global determinant bound with simultaneous smooth congruence
conditions. Bad reductions and local exponents are derived from the equation.

Congruence-refined global hypersurface determinant bounds.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The higher-dimensional rank-cutoff form of Proposition 3.2.6 for
maximal minors and common-degree homogeneous evaluation columns. -/
private theorem hypersurface_determinant_log_lower_at_rank_congruence {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    {F : Fin N → MvPolynomial (Fin (n + 3)) ℤ} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z)
    (bad : Finset ℕ)
    (P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℕ)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)))
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      stepanovThreshold (d : ℝ) < p →
      HasGoodReduction f p) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  refine hypersurface_log_lower_at_rank_of_local_divisors_congruence hs hd bad P hPbad hP v
    (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent))
    (fun p hp hcut => ?_) hcong
  have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
  obtain ⟨hf0, hir⟩ := hred p hp hcut
  simpa only [hypersurfaceDeterminantMain_div] using
    projective_hypersurface_minorGcd_dvd f hf hd hf0 hir hcut F hev.isHomogeneous z hev.primitive
      hev.eval_eq_zero

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The global determinant contribution and all prescribed smooth-prime
contributions hold simultaneously. -/
theorem exists_smooth_congruence_determinant_log_lower
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    {F : Fin N → MvPolynomial (Fin (n + 3)) ℤ} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ → Fin (n + 3)) (a : ℕ → Fin (n + 2) → ℤ)
    (ha : ∀ p ∈ P, eval₂ (Int.castRingHom (ZMod p)) (fun j => (a p j : ZMod p))
      (projectiveHypersurfaceChart (k p) f) = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, eval (fun i => (a p i : ZMod p)) (pderiv j
      (map (Int.castRingHom (ZMod p)) (projectiveHypersurfaceChart (k p) f))) ≠ 0)
    (hunit : ∀ p ∈ P, ∀ i, IsCoprime (p : ℤ) (z i (k p)))
    (hres : ∀ p ∈ P, ∀ i j, (p : ℤ) ∣
      z i (Equiv.swap 0 (k p) j.succ) - a p j * z i (k p)) :
    ∃ bad : Finset ℕ,
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      hypersurfaceRankLowerBound n s d (∑ p ∈ bad ∪ P, Real.log p / p) +
        (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) *
          (∑ p ∈ P, Real.log p) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  classical
  obtain ⟨bad, hmem⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
  have hcong (p : ℕ) (hp : p ∈ P) :
      (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
        Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
    let : Fact p.Prime := ⟨hP p hp⟩
    exact smooth_projective_hypersurface_congruence_minorGcd f hf F hev.isHomogeneous z
      (k p) (a p) (ha p hp) (hsmooth p hp) (hunit p hp) (hres p hp) hev.eval_eq_zero
  have hh := hypersurface_determinant_log_lower_at_rank_congruence hs f hf hd hev
    (bad ∪ P) P subset_union_right hP
    (fun _ => hypersurfaceMultiplicityExponent (n + 1) 1 s) hcong ?_
  · have he : hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s ≤
        (hypersurfaceMultiplicityExponent (n + 1) 1 s : ℝ) := by
      have he := hypersurfaceMultiplicityExponent_lower_bound (n + 1) s (by omega)
        (show 0 < (1 : ℕ) by omega)
      simpa only [Nat.cast_one, div_one, hypersurfaceDeterminantMain,
        Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using he
    have hsum : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) :=
      sum_nonneg fun p _ => Real.log_natCast_nonneg p
    have hmul := mul_le_mul_of_nonneg_right he hsum
    rw [← mul_sum] at hh
    exact ⟨bad, hmem, (add_le_add le_rfl hmul).trans hh⟩
  · intro p hpprime hp hcut
    apply hypersurface_good_reduction f p
    intro hb
    exact (mem_sdiff.mp hp).2 (mem_union_left P ((hmem p).mpr ⟨by exact_mod_cast hcut, hb⟩))

end
end CCDN

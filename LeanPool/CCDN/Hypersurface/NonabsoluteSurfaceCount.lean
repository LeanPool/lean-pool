/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Height
import LeanPool.CCDN.Algebra.PolynomialLinearDescent
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hypersurface.CurveBoxDegreeBound
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! CCDN Corollary 4.1.4 for irreducible affine hypersurfaces in three
variables. Splitting of the full equation over any field extension gives
an auxiliary equation of degree at most d. The prime curve
components of the resulting section have total degree at most d², giving
the sharp elementary bound d²(2B+1), whatever the highest homogeneous
component. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Linear descent of both proper factors produces a base-field auxiliary
equation vanishing at every base-field zero, with degree at most d. -/
theorem nonabsolute_affine_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k, q ≠ 0 ∧
      q.totalDegree ≤ f.totalDegree ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  have hd := totalDegree_pos_of_ne_zero_of_not_isUnit hir.ne_zero hir.not_isUnit
  have hmap0 : map (algebraMap k K) f ≠ 0 := by
    intro he
    apply hir.ne_zero
    exact map_injective (algebraMap k K) (algebraMap k K).injective (by simpa using he)
  have hmapd : (map (algebraMap k K) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective (algebraMap k K).injective _
  have hmapu : ¬ IsUnit (map (algebraMap k K) f) := by
    intro hu
    have he := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hmapd] at he
    omega
  have hfac : ∃ g h : MvPolynomial (Fin n) K,
      map (algebraMap k K) f = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! hn
    apply hred
    refine ⟨hmapu, ?_⟩
    intro g h he
    by_cases hu : IsUnit g
    · exact Or.inl hu
    · exact Or.inr (hn g h he hu)
  obtain ⟨g, h, hfac, hgu, hhu⟩ := hfac
  have hg0 : g ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hh0 : h ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hgd := totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
  have hhd := totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
  have hdegrees : g.totalDegree + h.totalDegree = f.totalDegree := by
    rw [hfac, totalDegree_mul_of_isDomain hg0 hh0] at hmapd
    exact hmapd
  obtain ⟨g₀, hg₀, hgd₀, hgz⟩ := exists_nonzero_polynomial_linear_descent (k := k) g hg0
  obtain ⟨h₀, hh₀, hhd₀, hhz⟩ := exists_nonzero_polynomial_linear_descent (k := k) h hh0
  refine ⟨g₀ * h₀, mul_ne_zero hg₀ hh₀, ?_, ?_, ?_⟩
  · rw [totalDegree_mul_of_isDomain hg₀ hh₀]
    omega
  · intro hdiv
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      omega
  · intro x hx
    have he := congrArg (algebraMap k K) hx
    rw [map_eval, hfac, eval_mul, map_zero] at he
    rw [eval_mul]
    rcases mul_eq_zero.mp he with hgzero | hhzero
    · rw [hgz x hgzero, zero_mul]
    · rw [hhz x hhzero, mul_zero]

/-- A finite union of affine curves in three-space, given by height-two primes `P` of degree
`d P`, has at most `(∑ P, d P) * (2 * B + 1)` integral points of height at most `B`. -/
theorem finite_curve_union_count_le_box_side
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (d : Ideal (CoordinatePolynomial 3) → ℕ)
    (hcurve : ∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P (d P))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
      (∑ P ∈ S, (d P : ℝ)) * (2 * B + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [count, integralPoints]
  | @insert P S hPS ih =>
    have hP := hcurve P (Finset.mem_insert_self _ _)
    have : P.IsPrime := hP.1
    have hS := ih (fun Q hQ => hcurve Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.set_biUnion_insert, Finset.sum_insert hPS, add_mul]
    have hcount : (count (idealZeroLocus P ∪ ⋃ Q ∈ S, idealZeroLocus Q) B : ℝ) ≤
        count (idealZeroLocus P) B + count (⋃ Q ∈ S, idealZeroLocus Q) B := by
      exact_mod_cast count_union_le (idealZeroLocus P) (⋃ Q ∈ S, idealZeroLocus Q) B
    exact hcount.trans (add_le_add (curve_count_le_degree_mul_box_side P hP.2.1 hP.2.2 hB) hS)

end
end CCDN

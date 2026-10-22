/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeComparison
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceSmallHeightDegree
public import LeanPool.CCDN.AuxiliaryPolynomial.Nonmultiple
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import LeanPool.CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary

/-! Higher-dimensional auxiliary polynomials in the small-height range, with exact
exponents, for any finite prime set whose normalized comparison holds. The
hypersurface instance retains the original geometric bad-prime factor. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient-sensitive threshold, with a dimension-only constant. -/
def hypersurfaceSmallThreshold (n d : ℕ) (B L A : ℝ) : ℝ :=
  Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * A *
      B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) /
        L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))))

/-- A degree above the proved threshold yields an integer homogeneous
nonmultiple vanishing at all given bounded points, for any finite prime set `bad`
for which the normalized comparison holds. -/
private theorem exists_auxiliary_small_height_of_comparison {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf0 : f ≠ 0) (hd : 0 < d) (hM : 2 * d ≤ M) (z : Fin t → IntPoint (n + 3))
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (bad : Finset ℕ) (hcomp : AuxiliaryRankComparison order f d z bad)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 2 * d * (n + 2 : ℝ) * Real.log B)
    (hscale : (d : ℝ) * Real.log B ≤ degreeRoot n d * M)
    (hthreshold : hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
      (primeSetFactor bad) < M) :
    ∃ g, IsPointAuxiliary f g M z := by
  classical
  have hdM : d ≤ M := by omega
  by_contra hnone
  obtain ⟨s, _, hr, hc⟩ := hcomp hB hbox hdM (dvd_of_not_exists_isPointAuxiliary hnone)
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hlog := hypersurface_small_height_log_degree_bound (r := n + 1) (by omega) hd hM hr
    B |((order.leadingCoeff f : ℤ) : ℝ)| (primeSetFactor bad)
    (hypersurfaceBadPrimeNormalizedError n) hB hL
    (by simpa only [Nat.cast_add, Nat.cast_one, hnR] using hheight)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hscale)
    (by simpa only [Nat.cast_add, Nat.cast_one, hnR, Real.log_exp] using hc)
  have hb := hypersurface_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM)
    (by linarith : 0 < B) (by linarith : 0 < |((order.leadingCoeff f : ℤ) : ℝ)|)
    (Real.exp_pos _) hlog
  have hb' : (M : ℝ) ≤ hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
      (primeSetFactor bad) := by
    simpa only [hypersurfaceSmallThreshold, Nat.cast_add, Nat.cast_one, hnR] using hb
  exact (not_lt_of_ge hb') hthreshold

/-- An integer auxiliary degree for any finite prime set `bad` for which the
normalized comparison holds. The bound keeps the leading-coefficient saving and
every radius exponent. -/
theorem auxiliary_small_height_degree_of_comparison {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf0 : f ≠ 0) (hd : 0 < d) (z : Fin t → IntPoint (n + 3))
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (bad : Finset ℕ) (hcomp : AuxiliaryRankComparison order f d z bad)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 2 * d * (n + 2 : ℝ) * Real.log B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ 2 * d + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
          (primeSetFactor bad) + 2 ∧
      ∃ g, IsPointAuxiliary f g M z := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let R := hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
    (primeSetFactor bad)
  have hR : 0 ≤ R := by dsimp only [R, hypersurfaceSmallThreshold]; positivity
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hdR.le _) (Real.log_nonneg hB)
  obtain ⟨M, hM, hscale, hthreshold, hbound⟩ := auxiliary_integer_degree_selection (2 * d) hl hR
  refine ⟨M, by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound, ?_⟩
  apply exists_auxiliary_small_height_of_comparison order f hf0 hd hM z hB hbox bad hcomp
    hheight _ hthreshold
  have hX : 0 < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
  dsimp only [l] at hscale
  rw [Real.rpow_sub hdR, Real.rpow_one] at hscale
  have hh := mul_le_mul_of_nonneg_right hscale hX.le
  have he : (d : ℝ) / (d : ℝ) ^ (1 / (n + 1 : ℝ)) * Real.log B *
      (d : ℝ) ^ (1 / (n + 1 : ℝ)) = d * Real.log B := by field_simp
  rw [he] at hh
  nlinarith

/-- The exact geometric bad-prime set together with an integer auxiliary
degree. The bound keeps the leading-coefficient saving and every radius exponent. -/
theorem hypersurface_auxiliary_small_height_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 2 * d * (n + 2 : ℝ) * Real.log B) :
    ∃ (bad : Finset ℕ) (M : ℕ),
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      (M : ℝ) ≤ 2 * d + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
          (primeSetFactor bad) + 2 ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  have hf0 := ne_zero_of_irreducible_map hir
  obtain ⟨bad, hbad⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
  obtain ⟨M, hM, g, hg⟩ := auxiliary_small_height_degree_of_comparison order f hf0 hd z hB hbox
    bad (hypersurface_auxiliaryRankComparison order f hf hf0 hd z hprim hz bad hbad) hheight
  exact ⟨bad, M, hbad, hM, g, isPointAuxiliary_iff.mp hg⟩

end
end CCDN

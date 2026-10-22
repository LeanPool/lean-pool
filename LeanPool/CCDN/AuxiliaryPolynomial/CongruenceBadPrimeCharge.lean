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
public import LeanPool.CCDN.Plane.IntegerPlaneLogHeight
import LeanPool.CCDN.AuxiliaryPolynomial.BadPrimeCharge
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeHeight

/-! A single logarithmic-height witness bounds the combined charge of
geometric bad primes and prescribed congruence primes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private theorem exists_fin_hypersurface_bad_prime_height_witness
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom L) f)) (hd : 0 < f.totalDegree)
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (f.totalDegree : ℝ) ^ 4) *
        (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) ∧
      ∀ p, f.totalDegree < p → HypersurfaceBadReduction f p → (p : ℤ) ∣ D := by
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (map (Int.castRingHom L) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv L e)).mpr hf
  have hgd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_hypersurface_bad_prime_height_witness g hg
    (hgd ▸ hd) H hH (polynomial_coefficient_bound_renameEquiv e f H hcoeff)
  refine ⟨D, hD, ?_, ?_⟩
  · simpa only [hgd, Fintype.card_option, Fintype.card_fin] using hheight
  · intro p hp hbad
    apply hdiv p (hgd ▸ hp)
    exact (hypersurfaceBadReduction_renameEquiv e f p).mpr hbad

/-- Multiplying a constructed bad-prime witness by the congruence modulus
keeps the combined prime charge within one logarithm of their log heights. -/
theorem hypersurface_and_congruence_prime_charge
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom L) f)) (hd : 0 < f.totalDegree)
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    (bad P : Finset ℕ)
    (hbad : ∀ p ∈ bad, stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ bad ∪ P, Real.log p / p) ≤
      Real.log (1 + 27 * (f.totalDegree : ℝ) ^ 4 *
        (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) +
        (∑ p ∈ P, Real.log p)) + 2 * mertensError + 1 := by
  classical
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_fin_hypersurface_bad_prime_height_witness f hf hd H hH hcoeff
  let q : ℤ := ∏ p ∈ P, (p : ℤ)
  have hq : 0 < q := prod_pos fun p hp => by exact_mod_cast (hP p hp).pos
  have hlogq : Real.log (q : ℝ) = ∑ p ∈ P, Real.log p := by
    dsimp only [q]
    rw [Int.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hP p hp).ne_zero)]
    simp only [Int.cast_natCast]
  have hprime (p : ℕ) (hp : p ∈ bad ∪ P) : p.Prime := by
    rcases mem_union.mp hp with hb | hp
    · exact (hbad p hb).2.choose
    · exact hP p hp
  have hdvd (p : ℕ) (hp : p ∈ bad ∪ P) : (p : ℤ) ∣ D * q := by
    rcases mem_union.mp hp with hb | hp
    · apply dvd_mul_of_dvd_left (hdiv p ?_ (hbad p hb).2)
      have hcut : 27 * f.totalDegree ^ 4 < p := (hbad p hb).1
      have h₁ := Nat.le_mul_self f.totalDegree
      have h₂ := Nat.le_mul_self (f.totalDegree * f.totalDegree)
      nlinarith
    · exact dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p : ℕ => (p : ℤ)) hp) D
  have hcharge := bad_prime_charge_of_height (bad ∪ P) (mul_pos hD hq) hprime hdvd
    (L := (1 : ℝ)) (H := 1 + 27 * (f.totalDegree : ℝ) ^ 4 *
      (hypersurfaceHeightConstant (n + 1) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + ∑ p ∈ P, Real.log p)
    (by norm_num) ?_ ?_ ?_
  · exact hcharge
  · have hlogH := Real.log_nonneg hH
    have hsum := sum_nonneg (s := P) (fun p _ => Real.log_natCast_nonneg p)
    have hC := (hypersurfaceHeightConstant_one_le (n + 1)).trans' zero_le_one
    have hterm : 0 ≤ 27 * (f.totalDegree : ℝ) ^ 4 *
        (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) := by positivity
    linarith
  · intro p hp
    exact_mod_cast (hprime p hp).one_lt
  · rw [Int.cast_mul, Real.log_mul (by exact_mod_cast hD.ne') (by exact_mod_cast hq.ne'),
      hlogq, one_mul]
    linarith

end
end CCDN

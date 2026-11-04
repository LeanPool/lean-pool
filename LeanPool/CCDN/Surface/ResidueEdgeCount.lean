/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Surface.ResidueBoundary
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Surface.CurveCrossing
import LeanPool.CCDN.Surface.NonlinearCount
import Mathlib.Algebra.Order.Star.Real

/-! Counting the proper sections attached to one residue-subset
edge, including the sum over all smooth residue tuples. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

open Classical in
/-- For a congruence family `F`, a set `R` of primes, a prime `p` and smooth residues `r`
modulo `R`, the rational points on curves `I ∈ S` whose ideal contains the auxiliary of
`R.erase p` but not the one of `R`, and at which the latter auxiliary vanishes. -/
def surfaceResidueCrossing {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (p : ℕ)
    (r : SmoothAffineResidueFamily f R) : Set (RatPoint 3) :=
  let g := map (Int.castRingHom ℚ)
    (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq))
      (r.restrict (erase_subset p R)))
  let h := map (Int.castRingHom ℚ) (F.auxiliary R hR r)
  ⋃ I ∈ S.filter (fun I => g ∈ I ∧ h ∉ I), idealZeroLocus I ∩ zeroLocus h

private theorem surface_residue_crossing_count_le
    {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I))
    (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (p : ℕ)
    (r : SmoothAffineResidueFamily f R) :
    count (surfaceResidueCrossing F S R hR p r) B ≤
      f.totalDegree *
        (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq))
          (r.restrict (erase_subset p R))).totalDegree *
        (F.auxiliary R hR r).totalDegree := by
  classical
  let g := map (Int.castRingHom ℚ)
    (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq))
      (r.restrict (erase_subset p R)))
  let h := map (Int.castRingHom ℚ) (F.auxiliary R hR r)
  have hh := surface_curve_crossing_count_le (map (Int.castRingHom ℚ) f) g h hir
    (F.proper _ _ _) (S.filter (fun I => g ∈ I)) δ
    (fun I hI => ⟨hS I (mem_filter.mp hI).1, (mem_filter.mp hI).2⟩) B
  have he : (S.filter (fun I => g ∈ I)).filter (fun I => h ∉ I) =
      S.filter (fun I => g ∈ I ∧ h ∉ I) := by ext I; simp only [mem_filter]; tauto
  rw [he] at hh
  change count (surfaceResidueCrossing F S R hR p r) B ≤ _ at hh
  simpa only [g, h, rational_map_totalDegree] using hh

private lemma SurfaceCongruenceFamily.scaled_degree_le
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (R : Finset ℕ) (hRW : R ⊆ congruencePrimeWindow L)
    (hR : ∀ p ∈ R, p.Prime) (r : SmoothAffineResidueFamily f R) :
    ((F.auxiliary R hR r).totalDegree : ℝ) * (∏ p ∈ R, (p : ℝ)) ≤
      A * (X + ∏ p ∈ R, (p : ℝ)) * surfaceResidueLogBudget B L := by
  have hlogB := Real.log_nonneg hB
  have hQ : 0 ≤ ∑ p ∈ R, Real.log p := sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hlog : (∑ p ∈ R, Real.log p) ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L :=
    (sum_le_sum_of_subset_of_nonneg hRW (fun p _ _ => Real.log_natCast_nonneg p)).trans
      (congruencePrimeWindow_log_upper hL)
  have hq : 0 < ∏ p ∈ R, (p : ℝ) :=
    prod_pos (fun p hp => by exact_mod_cast (hR p hp).pos)
  have hB0 : 0 < B := by linarith
  have hX0 : 0 ≤ X := (Real.rpow_nonneg hB0.le _).trans hX
  have hd := F.degree_le R hR r
  rw [exp_sum_log_primes R hR] at hd
  have hh := mul_le_mul_of_nonneg_right hd hq.le
  have he : A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      (∏ p ∈ R, (p : ℝ)) + 1) *
      (1 + Real.log B + ∑ p ∈ R, Real.log p) * (∏ p ∈ R, (p : ℝ)) =
      A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + (∏ p ∈ R, (p : ℝ))) *
        (1 + Real.log B + ∑ p ∈ R, Real.log p) := by field_simp
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (by linarith) hA
  · dsimp only [surfaceResidueLogBudget]; linarith
  · positivity
  · positivity

private theorem surface_residue_crossing_scaled_count
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hX0 : 0 ≤ X) (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I))
    (R : Finset ℕ) (hRW : R ⊆ congruencePrimeWindow L)
    (hR : ∀ p ∈ R, p.Prime) (p : ℕ) (hp : p ∈ R)
    (hq : (∏ q ∈ R, (q : ℝ)) ≤ scalingPrimeRatio * L * X)
    (r : SmoothAffineResidueFamily f R) :
    (count (surfaceResidueCrossing F S R hR p r) B : ℝ) *
        (∏ q ∈ R, (q : ℝ)) ^ 2 ≤
      2 * f.totalDegree * A ^ 2 * (surfaceResidueLogBudget B L) ^ 2 *
        (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2 := by
  let U := scalingPrimeRatio * L
  let T := surfaceResidueLogBudget B L
  let q : ℝ := ∏ t ∈ R, (t : ℝ)
  let g := F.auxiliary (R.erase p) (fun t ht => hR t (mem_of_mem_erase ht))
    (r.restrict (erase_subset p R))
  let h := F.auxiliary R hR r
  have hU : 0 ≤ U := by dsimp only [U]; have := scalingPrimeRatio_one_le; positivity
  have hT : 0 ≤ T := by
    dsimp only [T, surfaceResidueLogBudget]
    have := scalingPrimeRatio_one_le
    have := Real.log_nonneg hB
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hpU : (p : ℝ) ≤ U := ((mem_congruencePrimeWindow hL).mp (hRW hp)).2.2
  have hqp : (∏ t ∈ R.erase p, (t : ℝ)) * p = q := prod_erase_mul R _ hp
  have hpar := F.scaled_degree_le hA hB hL hX (R.erase p)
    ((erase_subset p R).trans hRW) (fun t ht => hR t (mem_of_mem_erase ht))
    (r.restrict (erase_subset p R))
  have hchild := F.scaled_degree_le hA hB hL hX R hRW hR r
  have hpar' : (g.totalDegree : ℝ) * q ≤ A * (X * p + q) * T := by
    have hh := mul_le_mul_of_nonneg_right hpar (Nat.cast_nonneg (α := ℝ) p)
    change (g.totalDegree : ℝ) * _ * p ≤ _ at hh
    calc
      _ = (g.totalDegree : ℝ) * (∏ t ∈ R.erase p, (t : ℝ)) * p := by rw [mul_assoc, hqp]
      _ ≤ _ := hh
      _ = _ := by dsimp only [T]; rw [← hqp]; ring
  have hchild' : (h.totalDegree : ℝ) * q ≤ A * (X + q) * T := hchild
  have hfirst : X * p + q ≤ 2 * (U + 1) * X := by
    have hpX := mul_le_mul_of_nonneg_left hpU hX0
    change q ≤ U * X at hq
    nlinarith
  have hsecond : X + q ≤ (U + 1) * X := by
    change q ≤ U * X at hq
    linarith
  have hpar'' : (g.totalDegree : ℝ) * q ≤ A * (2 * (U + 1) * X) * T :=
    hpar'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfirst hA) hT)
  have hchild'' : (h.totalDegree : ℝ) * q ≤ A * ((U + 1) * X) * T :=
    hchild'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsecond hA) hT)
  have hpair := mul_le_mul hpar'' hchild'' (by dsimp only [q]; positivity)
    (by positivity)
  have hcount : (count (surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
      (f.totalDegree : ℝ) * g.totalDegree * h.totalDegree := by
    exact_mod_cast surface_residue_crossing_count_le F hir S δ hS R hR p r
  have hc := mul_le_mul_of_nonneg_right hcount (sq_nonneg q)
  have hm := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg (α := ℝ) f.totalDegree)
  change _ ≤ 2 * f.totalDegree * A ^ 2 * T ^ 2 * (U + 1) ^ 2 * X ^ 2
  dsimp only [q] at hc hm
  nlinarith [hc, hm]

/-- Summing all smooth residue tuples cancels the square of the
modulus. Only d to the number of selected primes remains. -/
theorem surface_residue_edge_count_le
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hX0 : 0 ≤ X) (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I))
    (R : Finset ℕ) (hRW : R ⊆ congruencePrimeWindow L)
    (hR : ∀ p ∈ R, p.Prime) (p : ℕ) (hp : p ∈ R)
    (hq : (∏ q ∈ R, (q : ℝ)) ≤ scalingPrimeRatio * L * X) :
    (count (⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
      2 * (f.totalDegree : ℝ) ^ (R.card + 1) * A ^ 2 *
        (surfaceResidueLogBudget B L) ^ 2 * (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2 := by
  classical
  let (p : R) : NeZero p.val := ⟨(hR p.val p.property).ne_zero⟩
  let : Fintype (SmoothAffineResidueFamily f R) := Pi.instFintype
  let q : ℝ := ∏ p ∈ R, (p : ℝ)
  let C : ℝ := 2 * f.totalDegree * A ^ 2 * (surfaceResidueLogBudget B L) ^ 2 *
    (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2
  have hqpos : 0 < q := prod_pos (fun p hp => by exact_mod_cast (hR p hp).pos)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcard : (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) ≤
      (f.totalDegree : ℝ) ^ R.card * q ^ 2 := by
    have hh := smoothAffineResidueFamily_card_le (n := 2) f R hR
    rw [Nat.card_eq_fintype_card] at hh
    have hhR : (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) ≤
        ((f.totalDegree ^ R.card * (∏ p ∈ R, p) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hh
    dsimp only [q]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using hhR
  have hpoint (r : SmoothAffineResidueFamily f R) :
      (count (surfaceResidueCrossing F S R hR p r) B : ℝ) * q ^ 2 ≤ C :=
    surface_residue_crossing_scaled_count F hA hB hL hX0 hX hir S δ hS R hRW hR p hp hq r
  have hunion : (count (⋃ r : SmoothAffineResidueFamily f R,
      surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
      ∑ r : SmoothAffineResidueFamily f R, (count (surfaceResidueCrossing F S R hR p r) B : ℝ) := by
    have hh := count_biUnion_finset_le (univ : Finset (SmoothAffineResidueFamily f R))
      (fun r => surfaceResidueCrossing F S R hR p r) B
    have hh' : count (⋃ r : SmoothAffineResidueFamily f R,
        surfaceResidueCrossing F S R hR p r) B ≤
        ∑ r : SmoothAffineResidueFamily f R, count (surfaceResidueCrossing F S R hR p r) B := by
      simpa only [Finset.mem_univ, Set.iUnion_true] using hh
    exact_mod_cast hh'
  have hscaled :
      (count (⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hR p r) B : ℝ) *
        q ^ 2 ≤
      (2 * (f.totalDegree : ℝ) ^ (R.card + 1) * A ^ 2 *
        (surfaceResidueLogBudget B L) ^ 2 * (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2) * q ^ 2 := by
    calc
      _ ≤ (∑ r : SmoothAffineResidueFamily f R,
          (count (surfaceResidueCrossing F S R hR p r) B : ℝ)) * q ^ 2 :=
        mul_le_mul_of_nonneg_right hunion (sq_nonneg q)
      _ = ∑ r : SmoothAffineResidueFamily f R,
          (count (surfaceResidueCrossing F S R hR p r) B : ℝ) * q ^ 2 := sum_mul _ _ _
      _ ≤ ∑ _r : SmoothAffineResidueFamily f R, C := sum_le_sum (fun r _ => hpoint r)
      _ = (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) * C := by simp
      _ ≤ ((f.totalDegree : ℝ) ^ R.card * q ^ 2) * C :=
        mul_le_mul_of_nonneg_right hcard hC
      _ = _ := by dsimp only [C]; rw [pow_succ]; ring
  exact le_of_mul_le_mul_right hscaled (sq_pos_of_pos hqpos)

end
end CCDN

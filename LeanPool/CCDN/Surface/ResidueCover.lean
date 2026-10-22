/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Surface.ResidueEdgeCount
import LeanPool.CCDN.Surface.NonlinearCount

/-! The finite residue-edge cover and its complete counting bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- For a subset `R` of the prime window of logarithmic size `L` whose product is at most
`c L X` (with `c` the constant `scalingPrimeRatio`), the union over the primes `p ∈ R` and the
smooth residue families `r` modulo `R` of the crossing sets of the deletion edge
`R.erase p ⊂ R`; the empty set for every other `R`. -/
def surfaceResidueSubsetLocus {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3))) (L X : ℝ) (hL : 1 ≤ L)
    (R : Finset ℕ) : Set (RatPoint 3) :=
  if hR : R ⊆ congruencePrimeWindow L then
    if (∏ p ∈ R, (p : ℝ)) ≤ scalingPrimeRatio * L * X then
      ⋃ p ∈ R, ⋃ r : SmoothAffineResidueFamily f R,
        surfaceResidueCrossing F S R
          (fun _q hq => ((mem_congruencePrimeWindow hL).mp (hR hq)).1) p r
    else ∅
  else ∅

/-- The residual locus of the surface residue cover: the union of the edge crossing sets
`surfaceResidueSubsetLocus F S L X hL R` over all subsets `R` of the prime window of
logarithmic size `L`. -/
def surfaceResidueResidualLocus {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3))) (L X : ℝ) (hL : 1 ≤ L) :
    Set (RatPoint 3) :=
  ⋃ R ∈ (congruencePrimeWindow L).powerset, surfaceResidueSubsetLocus F S L X hL R

private theorem mem_surfaceResidueResidualLocus
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3))) (hL : 1 ≤ L)
    (R : Finset ℕ) (hRW : R ⊆ congruencePrimeWindow L)
    (hR : ∀ p ∈ R, p.Prime) (p : ℕ) (hp : p ∈ R)
    (hprod : (∏ q ∈ R, (q : ℝ)) ≤ scalingPrimeRatio * L * X)
    (r : SmoothAffineResidueFamily f R) {x : RatPoint 3}
    (hx : x ∈ surfaceResidueCrossing F S R hR p r) :
    x ∈ surfaceResidueResidualLocus F S L X hL := by
  apply Set.mem_iUnion.mpr
  refine ⟨R, Set.mem_iUnion.mpr ⟨mem_powerset.mpr hRW, ?_⟩⟩
  simp only [surfaceResidueSubsetLocus, dite_eq_left hRW, ite_eq_left hprod]
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, Set.mem_iUnion.mpr ⟨r, hx⟩⟩⟩

/-- For an irreducible surface `f = 0` of degree `d ≥ 1` with curves `S`, a congruence family
`F` with constant `A` and a cutoff `X ≥ B^(1/√d)`, the residual locus has at most
`2 d A² b² (c L + 1)² X² #W (2d)^#W` integral points of height at most `B`, where `b` is the
logarithmic budget `surfaceResidueLogBudget B L`, `c` is `scalingPrimeRatio` and `W` is the
prime window of logarithmic size `L`. -/
theorem surface_residue_residual_count_le
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hd : 1 ≤ f.totalDegree) (hX0 : 0 ≤ X)
    (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I)) :
    (count (surfaceResidueResidualLocus F S L X hL) B : ℝ) ≤
      2 * f.totalDegree * A ^ 2 * (surfaceResidueLogBudget B L) ^ 2 *
        (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2 *
        (congruencePrimeWindow L).card *
        (2 * f.totalDegree : ℝ) ^ (congruencePrimeWindow L).card := by
  let W := congruencePrimeWindow L
  let C : ℝ := 2 * f.totalDegree * A ^ 2 * (surfaceResidueLogBudget B L) ^ 2 *
    (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hsubset (R : Finset ℕ) (hRW : R ∈ W.powerset) :
      (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ) ≤
        C * W.card * (f.totalDegree : ℝ) ^ W.card := by
    have hRW' : R ⊆ congruencePrimeWindow L := mem_powerset.mp hRW
    have hcard : R.card ≤ W.card := card_le_card hRW'
    have hR (p : ℕ) (hp : p ∈ R) : p.Prime :=
      ((mem_congruencePrimeWindow hL).mp (hRW' hp)).1
    by_cases hq : (∏ p ∈ R, (p : ℝ)) ≤ scalingPrimeRatio * L * X
    · have hcount := count_biUnion_finset_le R
        (fun p => ⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hR p r) B
      have hcountR :
          (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ) ≤
          ∑ p ∈ R, (count (⋃ r : SmoothAffineResidueFamily f R,
            surfaceResidueCrossing F S R hR p r) B : ℝ) := by
        simp only [surfaceResidueSubsetLocus, dite_eq_left hRW', ite_eq_left hq]
        exact_mod_cast hcount
      calc
        _ ≤ ∑ p ∈ R, (count (⋃ r : SmoothAffineResidueFamily f R,
            surfaceResidueCrossing F S R hR p r) B : ℝ) := hcountR
        _ ≤ ∑ _p ∈ R, C * (f.totalDegree : ℝ) ^ R.card := by
          apply sum_le_sum
          intro p hp
          have hh := surface_residue_edge_count_le F hA hB hL hX0 hX hir S δ hS
            R hRW' hR p hp hq
          convert hh using 1
          dsimp only [C]
          rw [pow_succ]
          ring
        _ = C * R.card * (f.totalDegree : ℝ) ^ R.card := by simp; ring
        _ ≤ C * W.card * (f.totalDegree : ℝ) ^ W.card := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hC
          · exact pow_le_pow_right₀ hdR hcard
          · positivity
          · positivity
    · simp only [surfaceResidueSubsetLocus, dite_eq_left hRW', ite_eq_right hq]
      have hzero : count (∅ : Set (RatPoint 3)) B = 0 := by simp [count, integralPoints]
      rw [hzero, Nat.cast_zero]
      positivity
  have hunion :
      (count (surfaceResidueResidualLocus F S L X hL) B : ℝ) ≤
        ∑ R ∈ W.powerset, (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ) := by
    exact_mod_cast count_biUnion_finset_le W.powerset
      (surfaceResidueSubsetLocus F S L X hL) B
  calc
    _ ≤ ∑ R ∈ W.powerset, (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ) := hunion
    _ ≤ ∑ _R ∈ W.powerset, C * W.card * (f.totalDegree : ℝ) ^ W.card :=
      sum_le_sum hsubset
    _ = (2 : ℝ) ^ W.card * (C * W.card * (f.totalDegree : ℝ) ^ W.card) := by
      simp only [sum_const, card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = _ := by
      change _ = C * W.card * (2 * f.totalDegree : ℝ) ^ W.card
      rw [mul_pow]
      ring

/-- An integer point of the box at which the surface `f = 0` is nonsingular, lying on a curve
`I ∈ S` that contains the initial auxiliary and has degree greater than `2 d A` times the
logarithmic budget, belongs to the residual locus `surfaceResidueResidualLocus F S L X`. -/
theorem large_curve_point_mem_surfaceResidueResidualLocus
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    {A B H L X : ℝ} (hA : 0 ≤ A) (hW : IsSurfaceResidueWindow f B H L X)
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (I : Ideal (CoordinatePolynomial 3)) (hIS : I ∈ S) {d : ℕ}
    (hI : IsSurfaceCurve (map (Int.castRingHom ℚ) f) I d)
    (hinitI : map (Int.castRingHom ℚ) F.initial ∈ I)
    (hlarge : 2 * f.totalDegree * A * surfaceResidueLogBudget B L < d)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0)
    (hxI : rationalPoint x ∈ idealZeroLocus I)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    rationalPoint x ∈ surfaceResidueResidualLocus F S L X hW.one_le_window := by
  classical
  obtain ⟨R, hR, p, hp, r, hedge⟩ :=
    surface_residue_boundary_of_large_curve f hir hA hW F I hI hinitI hlarge x hx hxf hsmooth
  apply mem_surfaceResidueResidualLocus F S hW.one_le_window R hedge.subset_window hR p hp
    hedge.prod_lt.le r
  apply Set.mem_iUnion.mpr
  refine ⟨I, Set.mem_iUnion.mpr
    ⟨mem_filter.mpr ⟨hIS, hedge.parent_mem, hedge.child_not_mem⟩, hxI, ?_⟩⟩
  have hh := congrArg (Int.castRingHom ℚ) hedge.child_vanishes
  rw [map_eval, map_zero] at hh
  exact hh

end
end CCDN

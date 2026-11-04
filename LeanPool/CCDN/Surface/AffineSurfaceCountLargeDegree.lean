/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Height.Box
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.Surface.DegreeOneCount
import LeanPool.CCDN.Surface.TopFormSurfaceNonlinear

/-! The corrected large-degree surface bound. The auxiliary section's
nonlinear curves and its degree-one components together account
for every bounded integer zero of the original surface. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The degree threshold of the large-degree surface bound `affine_surface_count_large_degree`. It
comes from `surface_inverse_sqrt_le_quarter`: `1 / √d ≤ 1 / 4` once `16 ≤ d`. -/
def topFormSurfaceThreshold : ℕ := 16

/-- Corrected CCDN Proposition 4.3.4 for degrees at least sixteen and an
absolutely irreducible highest homogeneous part. The positive constant is
chosen before the integer polynomial and the real box radius. -/
theorem affine_surface_count_large_degree :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      topFormSurfaceThreshold ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 18 * B := by
  classical
  obtain ⟨A, hA, hnonlinear⟩ := top_form_surface_nonlinear_count
  obtain ⟨C, hC, hlines⟩ := surface_degree_one_component_contribution
  let K := topFormAuxiliaryConstant 1
  have hK : 0 < K := topFormAuxiliaryConstant_pos 1
  refine ⟨A + C + K, by positivity, ?_⟩
  intro f hir hd B hB
  unfold topFormSurfaceThreshold at hd
  obtain ⟨S, δ, hcomponents, _, hdegree, _, houtside⟩ :=
    hnonlinear f hir hd B hB
  let T := S.filter (fun P => δ P = 1)
  let L := ⋃ P ∈ T, idealZeroLocus P
  have hTcurve (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1 := by
    obtain ⟨hPS, hone⟩ := Finset.mem_filter.mp hP
    exact ⟨(hcomponents P hPS).1.isPrime, (hcomponents P hPS).1.height_eq,
      by simpa only [hone] using (hcomponents P hPS).1.degree⟩
  have hTsurface (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      map (Int.castRingHom ℚ) f ∈ P :=
    (hcomponents P (Finset.mem_filter.mp hP).1).1.mem
  have hlinecount : (count L B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + T.card :=
    hlines f hir (by omega) B (by linarith) T hTcurve hTsurface
  have hcard : T.card ≤ ∑ P ∈ S, δ P := by
    calc
      T.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = ∑ _P ∈ S, 1 := by simp
      _ ≤ ∑ P ∈ S, δ P := by
        apply Finset.sum_le_sum
        intro P hP
        exact (hcomponents P hP).2
  have hcardR : (T.card : ℝ) ≤ K * (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) *
      B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by
    have hh : (T.card : ℝ) ≤ ((∑ P ∈ S, δ P : ℕ) : ℝ) := by
      exact_mod_cast hcard
    exact hh.trans hdegree
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast (show 1 ≤ f.totalDegree by omega)
  have hroot : (1 : ℝ) ≤ (f.totalDegree : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hd1 (by norm_num)
  have hexp : 1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ) ≤ 1 :=
    (div_le_one (by positivity)).2 hroot
  have hBpower : B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hexp
  have hdpower : (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) ≤ (f.totalDegree : ℝ) ^ 18 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hd1 (show (9 / 2 : ℝ) ≤ 18 by norm_num)
  have hcardfinal : (T.card : ℝ) ≤ K * (f.totalDegree : ℝ) ^ 18 * B := by
    apply hcardR.trans
    gcongr
  have hdsix : (f.totalDegree : ℝ) ^ 6 ≤ (f.totalDegree : ℝ) ^ 18 :=
    pow_le_pow_right₀ hd1 (by omega)
  have hlinefinal : (count L B : ℝ) ≤ (C + K) * (f.totalDegree : ℝ) ^ 18 * B := by
    calc
      _ ≤ C * (f.totalDegree : ℝ) ^ 6 * B + T.card := hlinecount
      _ ≤ C * (f.totalDegree : ℝ) ^ 18 * B +
          K * (f.totalDegree : ℝ) ^ 18 * B := by gcongr
      _ = _ := by ring
  have hcover : zeroLocus (map (Int.castRingHom ℚ) f) ⊆
      (zeroLocus (map (Int.castRingHom ℚ) f) \ L) ∪ L := by
    intro x hx
    by_cases hxL : x ∈ L
    · exact Or.inr hxL
    · exact Or.inl ⟨hx, hxL⟩
  have htotal : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
      count (zeroLocus (map (Int.castRingHom ℚ) f) \ L) B + count L B :=
    (count_mono hcover le_rfl).trans (count_union_le _ _ B)
  calc
    _ ≤ (count (zeroLocus (map (Int.castRingHom ℚ) f) \ L) B : ℝ) + count L B := by
      exact_mod_cast htotal
    _ ≤ A * (f.totalDegree : ℝ) ^ 18 * B +
        (C + K) * (f.totalDegree : ℝ) ^ 18 * B :=
      add_le_add houtside hlinefinal
    _ = _ := by ring

end
end CCDN

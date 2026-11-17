/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hypersurface.IntegerHyperplaneSlices
public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Hypersurface.GoodHyperplane
import LeanPool.CCDN.Hypersurface.HyperplaneSliceCoordinates
import LeanPool.CCDN.Hypersurface.IntegerGoodHyperplaneSlices

/-!
A dimension induction with a cubic degree cost per hyperplane slice,
using the constructed universal Noether detector.

Integer equations for every parallel level of a good hyperplane whose
normal has cubic degree height.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem exists_good_integer_hyperplane_slices {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ) (g : ℤ → MvPolynomial (Fin (3 + n)) ℤ),
      D ≠ 0 ∧ |D| ≤ (f.totalDegree ^ 3 : ℕ) ∧
      (∀ i, |a i| ≤ (f.totalDegree ^ 3 : ℕ)) ∧
      ∀ k : ℤ, (g k).totalDegree = f.totalDegree ∧
        HasAbsIrreducibleTopForm (g k) ∧
        ∀ x : Option (Fin (3 + n)) → ℤ,
          D * x none - ∑ i, a i * x (some i) = k →
          eval x f = 0 → eval (fun i => x (some i)) (g k) = 0 := by
  obtain ⟨D, a, hD, hDb, hab, _, hgood⟩ := exists_geometrically_good_hyperplane
    (homogeneousComponent f.totalDegree f) f.totalDegree hd
    (homogeneousComponent_isHomogeneous _ _) hir
  obtain ⟨g, hg⟩ := exists_integer_hyperplane_slice_models f D a hD hgood
  exact ⟨D, a, g, hD, hDb, hab, hg⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- A normal of height at most `d^3` costs three powers of the degree
and one power of the box radius in a dimension induction. -/
private theorem count_le_of_good_integer_hyperplane_slices {n d e r : ℕ}
    (X : Set (RatPoint (n + 1))) (a : IntPoint (n + 1))
    (j : Fin (n + 1)) (hj : a j ≠ 0) (Y : ℤ → Set (RatPoint n))
    (hd : 1 ≤ d) {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (ha : InBox a ((d : ℝ) ^ 3))
    (hmap : ∀ k x, x ∈ integerSlicePoints X B a k →
      rationalPoint (deleteIntegerCoordinate j x) ∈ Y k)
    (hcount : ∀ k, (count (Y k) B : ℝ) ≤ C * (d : ℝ) ^ e * B ^ r) :
    (count X B : ℝ) ≤
      (2 * (n + 1 : ℕ) + 1) * C * (d : ℝ) ^ (e + 3) * B ^ (r + 1) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have hK : 0 ≤ C * (d : ℝ) ^ e * B ^ r := by positivity
  have hD : 1 ≤ (d : ℝ) ^ 3 := one_le_pow₀ hdR
  have hDB : 1 ≤ (d : ℝ) ^ 3 * B := one_le_mul_of_one_le_of_one_le hD hB
  have hfactor :
      2 * (n + 1 : ℕ) * ((d : ℝ) ^ 3) * B + 1 ≤
        (2 * (n + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B := by
    nlinarith
  calc
    _ ≤ (2 * (n + 1 : ℕ) * ((d : ℝ) ^ 3) * B + 1) *
        (C * (d : ℝ) ^ e * B ^ r) :=
      count_le_of_integer_hyperplane_slices X a j hj Y
        (by positivity) hB0 hK ha hmap hcount
    _ ≤ ((2 * (n + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B) *
        (C * (d : ℝ) ^ e * B ^ r) := mul_le_mul_of_nonneg_right hfactor hK
    _ = _ := by rw [pow_add, pow_succ]; ring

/-- One bounded good hyperplane slice: affine dimension growth in `n + 3` variables
gives it in `n + 4` variables, at the cost of three powers of the degree and one power of
the box radius. -/
private theorem AffineHypersurfaceGrowth.succ {n e : ℕ} (h : AffineHypersurfaceGrowth n e) :
    AffineHypersurfaceGrowth (n + 1) (e + 3) := by
  classical
  obtain ⟨C, hC, hbound⟩ := h
  rw [show n + 3 = 3 + n by omega] at hbound
  unfold AffineHypersurfaceGrowth
  rw [show n + 1 + 3 = 3 + n + 1 by omega]
  refine ⟨(2 * (3 + n + 1 : ℕ) + 1) * C, by positivity, ?_⟩
  intro f hir hd B hB
  let indexEquiv : Fin (3 + n + 1) ≃ Option (Fin (3 + n)) := finSuccEquiv' 0
  let F := rename indexEquiv f
  have hFdegree : F.totalDegree = f.totalDegree := totalDegree_renameEquiv indexEquiv f
  have hFir : HasAbsIrreducibleTopForm F := integer_top_irreducible_rename indexEquiv f hir
  obtain ⟨D, a, g, hD, hDb, hab, hg⟩ :=
    exists_good_integer_hyperplane_slices F hFir (by rw [hFdegree]; omega)
  rw [hFdegree] at hDb hab
  let b := graphIntegerNormal D a
  have hb0 : b 0 ≠ 0 := hD
  have hbheight (i : Fin (3 + n + 1)) :
      |(b i : ℝ)| ≤ (f.totalDegree : ℝ) ^ 3 := by
    simpa only [Nat.cast_pow] using graphIntegerNormal_height D a hDb hab i
  let Y : ℤ → Set (RatPoint (3 + n)) :=
    fun k => zeroLocus (map (Int.castRingHom ℚ) (g k))
  have hmap (k : ℤ) (x : IntPoint (3 + n + 1))
      (hx : x ∈ integerSlicePoints (zeroLocus (map (Int.castRingHom ℚ) f)) B b k) :
      rationalPoint (deleteIntegerCoordinate 0 x) ∈ Y k :=
    integer_slice_map_of_option_equations f D a g (fun k => (hg k).2.2) B k x hx
  have hcount (k : ℤ) :
      (count (Y k) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1) := by
    have hdegree : (g k).totalDegree = f.totalDegree := (hg k).1.trans hFdegree
    simpa only [hdegree, Y] using hbound (g k) (hg k).2.1 (by omega) B hB
  exact count_le_of_good_integer_hyperplane_slices
    (zeroLocus (map (Int.castRingHom ℚ) f)) b 0 hb0 Y
    (show 1 ≤ f.totalDegree by omega) hB hC.le hbheight hmap hcount

/-- Bounded good hyperplanes lift a surface bound with degree exponent `e` to every
higher dimension; each slice adds three to the exponent. -/
theorem affineHypersurfaceGrowth_of_surface {e : ℕ} (h : AffineHypersurfaceGrowth 0 e) :
    ∀ n, AffineHypersurfaceGrowth n (e + 3 * n)
  | 0 => h
  | n + 1 => (affineHypersurfaceGrowth_of_surface h n).succ

end
end CCDN

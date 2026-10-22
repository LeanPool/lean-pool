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
import LeanPool.CCDN.Hilbert.CompleteIntersectionGridBound
import LeanPool.CCDN.Hypersurface.NonabsoluteSurfaceCount

/-! Dimension growth for non-geometrically-irreducible rational
hypersurfaces in every ambient dimension. The dependence on the degree
is quadratic; the explicit constant depends only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If `f` is a prime rational polynomial in `n + 2` variables not dividing `g`, and both have
total degree at most `d`, then the common zero set of `f` and `g` has at most
`(n + 2) ^ n * d ^ 2 * (2 * B + 1) ^ n` integral points of height at most `B`. -/
theorem proper_intersection_count_le_box {n d : ℕ}
    (f g : CoordinatePolynomial (n + 2)) (hf : Prime f) (hfg : ¬ f ∣ g)
    (hfd : f.totalDegree ≤ d) (hgd : g.totalDegree ≤ d)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f ∩ zeroLocus g) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (d : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  classical
  let T := integralPoints (zeroLocus f ∩ zeroLocus g) B
  let S := (Finset.Icc (-⌊B⌋) ⌊B⌋).image (fun t : ℤ => (t : ℚ))
  let z : T → Fin (n + 2) → ℚ := fun x => rationalPoint x.val
  have hz : Function.Injective z := by
    intro x y h
    apply Subtype.ext
    funext j
    exact Int.cast_injective (congrFun h j)
  have hzS (x : T) (j : Fin (n + 2)) : z x j ∈ S := by
    apply Finset.mem_image.mpr
    refine ⟨x.val j, ?_, rfl⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp ((mem_integralPoints.mp x.property).1 j)
    have hn : -(x.val j) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact Finset.mem_Icc.mpr ⟨by omega, Int.le_floor.mpr hhi⟩
  have hzfg (x : T) : eval (z x) f = 0 ∧ eval (z x) g = 0 :=
    (mem_integralPoints.mp x.property).2
  have hgrid := proper_intersection_grid_card_le f g hf hfg hfd hgd S z hz hzS
    (fun x => (hzfg x).1) (fun x => (hzfg x).2)
  have hcard : (count (zeroLocus f ∩ zeroLocus g) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (d : ℝ) ^ 2 * (S.card : ℝ) ^ n := by
    exact_mod_cast (show T.card ≤ (n + 2) ^ n * d ^ 2 * S.card ^ n by
      simpa only [Fintype.card_coe] using hgrid)
  have hScard : (S.card : ℝ) ≤ 2 * B + 1 := by
    have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
    dsimp only [S]
    rw [Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    linarith [Int.floor_le B]
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hScard n) (by positivity))

/-- Rationally irreducible full equations which split over an
extension satisfy affine dimension growth with quadratic degree
dependence. The dimension-only factor here is not asserted to be the
sharp constant one in CCDN Corollary 4.1.4. -/
private theorem nonabsolute_hypersurface_count_le {K : Type*}
    [Field K] [Algebra ℚ K] {n : ℕ}
    (f : CoordinatePolynomial (n + 2)) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap ℚ K) f))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  obtain ⟨g, _, hgd, hfg, hzero⟩ := nonabsolute_affine_auxiliary f hir hred
  have hsubset : zeroLocus f ⊆ zeroLocus f ∩ zeroLocus g :=
    fun x hx => ⟨hx, hzero x hx⟩
  have hcount : (count (zeroLocus f) B : ℝ) ≤
      (count (zeroLocus f ∩ zeroLocus g) B : ℝ) := by
    exact_mod_cast count_mono hsubset (le_refl B)
  exact hcount.trans (proper_intersection_count_le_box f g hir.prime hfg le_rfl hgd hB)

/-- An irreducible rational polynomial `f` in `n + 2` variables that becomes reducible over some
extension field has at most `(3 * (n + 2)) ^ n * deg f ^ 2 * B ^ n` integral zeros of height
at most `B`, for every `B ≥ 1`. -/
theorem nonabsolute_hypersurface_dimension_growth {K : Type*}
    [Field K] [Algebra ℚ K] {n : ℕ}
    (f : CoordinatePolynomial (n + 2)) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap ℚ K) f))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  have hh := nonabsolute_hypersurface_count_le f hir hred (show 0 ≤ B by linarith)
  calc
    _ ≤ (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n := hh
    _ ≤ (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (3 * B) ^ n := by
      gcongr
      linarith
    _ = _ := by simp only [mul_pow]; ring

end
end CCDN

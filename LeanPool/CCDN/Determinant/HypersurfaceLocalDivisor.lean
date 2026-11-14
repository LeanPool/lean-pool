/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.DegreeBound
public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
public import LeanPool.CCDN.Plane.FiniteFieldConstants
import LeanPool.CCDN.Determinant.HypersurfaceCountNormalization
import LeanPool.CCDN.Hypersurface.ProjectiveHypersurfaceCount

/-! CCDN Lemma 2.8 and Corollary 2.9, including the finite-field count.
All constants depend only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Explicit dimension-only constant for the projective multiplicity count
(`projective_hypersurface_totalMultiplicity_bound`) in `n + 3` coordinates: the projective
point count contributes `projectiveHypersurfaceResidueConstant = 330`, and the multiplicities
of the singular points contribute `(n + 3) (n + 4)ⁿ`
(`projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error`). -/
def hypersurfaceCountConstant (n : ℕ) : ℝ :=
  projectiveHypersurfaceResidueConstant + ((n + 3) * (n + 4) ^ n : ℕ)

/-- The constant `hypersurfaceCountConstant n` is nonnegative. -/
lemma hypersurfaceCountConstant_nonneg (n : ℕ) : 0 ≤ hypersurfaceCountConstant n := by
  unfold hypersurfaceCountConstant
  exact add_nonneg projectiveHypersurfaceResidueConstant_pos.le (Nat.cast_nonneg _)

/-- The main local coefficient for projective hypersurfaces of dimension n+1. -/
def hypersurfaceDeterminantMain (n s : ℕ) : ℝ :=
  ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (n + 1 : ℝ) / (n + 2 : ℝ) *
    (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ))

/-- The main coefficient `hypersurfaceDeterminantMain n s` is nonnegative. -/
lemma hypersurfaceDeterminantMain_nonneg (n s : ℕ) : 0 ≤ hypersurfaceDeterminantMain n s := by
  unfold hypersurfaceDeterminantMain
  positivity

/-- The local exponent of `projective_hypersurface_minorGcd_dvd` in terms of
`hypersurfaceDeterminantMain`. -/
lemma hypersurfaceDeterminantMain_div (n s : ℕ) (m : ℝ) :
    factorialRoot n / m * (n + 1 : ℝ) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) = hypersurfaceDeterminantMain n s / m := by
  unfold hypersurfaceDeterminantMain
  ring

/-- CCDN Lemma 2.8: normalized multiplicity-root error O_n(d^2/sqrt(p)). -/
theorem projective_hypersurface_normalized_count_error {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ^ (1 / (n + 1 : ℝ)) / p - 1 ≤
      hypersurfaceCountConstant n * (d : ℝ) ^ 2 / Real.sqrt p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  let H := hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p
  have hH : 0 ≤ H :=
    mul_nonneg (mul_nonneg (hypersurfaceCountConstant_nonneg n) (sq_nonneg _)) hs.le
  have hc : (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤
      (p : ℝ) ^ (n + 1) + H * (p : ℝ) ^ n := by
    simpa only [H, hypersurfaceCountConstant, mul_assoc, mul_left_comm, mul_comm] using
      projective_hypersurface_totalMultiplicity_bound f hf hd hf0 hir hsize
  have h := hypersurface_count_normalized_root_error (n + 1) (by omega) hp hH
    (Nat.cast_nonneg (projectiveHypersurfaceTotalMultiplicity f hf hf0))
    (by simpa only [Nat.add_sub_cancel] using hc)
  have he : H / (p : ℝ) = hypersurfaceCountConstant n * (d : ℝ) ^ 2 / Real.sqrt p := by
    dsimp only [H]
    apply (div_eq_div_iff (ne_of_gt hp) (ne_of_gt hs)).mpr
    rw [mul_assoc, mul_assoc, ← pow_two, Real.sq_sqrt hp.le]
    ring
  rw [he] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- CCDN Corollary 2.9: the sharp single-prime divisor of every maximal minor
of a common-degree homogeneous evaluation matrix. The residue count, local
multiplicities and projective reduction are constructed from f and z. -/
theorem projective_hypersurface_minorGcd_dvd {n s N p d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0) :
    ∃ e : ℕ,
      factorialRoot n /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) *
        (n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) -
        (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd
        (Matrix.of fun i j => MvPolynomial.eval (z i) (F j)) := by
  apply projective_hypersurface_minorGcd_of_count_bound f hf hf0 F hF z hprim hz
  · exact mul_nonneg (mul_nonneg (hypersurfaceCountConstant_nonneg n) (sq_nonneg _))
      (Real.sqrt_nonneg _)
  · simpa only [hypersurfaceCountConstant, mul_assoc, mul_left_comm, mul_comm] using
      projective_hypersurface_totalMultiplicity_bound f hf hd hf0 hir hsize

end
end CCDN

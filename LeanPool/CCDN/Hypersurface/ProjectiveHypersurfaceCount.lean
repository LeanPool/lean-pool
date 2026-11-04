/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
public import LeanPool.CCDN.Height.ProjectiveZeroLocus
public import LeanPool.CCDN.Plane.FiniteFieldConstants
import LeanPool.CCDN.Algebra.FiniteFieldProjectiveCone
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceMultiplicity
import LeanPool.CCDN.Hypersurface.FiniteFieldCount

/-! The sharp projective finite-field count and its singular
multiplicity correction. This discharges the count in CCDN Lemma 2.7. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An absolutely irreducible form `f` of degree `d > 0` in `n + 3` variables over `ZMod p`, with
`p` above the threshold `27 * d ^ 4`, has at most
`p ^ (n + 1) + projectiveHypersurfaceResidueConstant * d ^ 2 * p ^ n * √p` projective zeros. -/
theorem projective_hypersurface_finite_field_bound {n d : ℕ}
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) (ZMod p))
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (Nat.card (projectiveZeroLocus f) : ℝ) ≤ (p : ℝ) ^ (n + 1) +
      projectiveHypersurfaceResidueConstant * (d : ℝ) ^ 2 * (p : ℝ) ^ n * Real.sqrt p := by
  rw [projectiveHypersurfaceResidueConstant_eq]
  have hi := mvPolynomial_irreducible_of_field_map _ f hir
  have hdeg : f.totalDegree = d := hf.totalDegree hi.ne_zero
  have hcone := affine_hypersurface_finite_field_bound p f hir (hdeg ▸ hsize)
  rw [hdeg, hypersurfaceResidueConstant_eq] at hcone
  have h := homogeneous_projective_count_of_cone_bound f hf hd
    (H := 164 * (d : ℝ) ^ 2 * Real.sqrt p) (by positivity) (by
      simpa only [ZMod.card, mul_assoc, mul_left_comm, mul_comm] using hcone)
  simp only [ZMod.card] at h
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hs : 1 ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by simpa using hp)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hds : (1 : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt p := by nlinarith
  have he : 2 * (164 * (d : ℝ) ^ 2 * Real.sqrt p + 1) ≤
      330 * (d : ℝ) ^ 2 * Real.sqrt p := by nlinarith
  have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ (p : ℝ) ^ n by positivity)
  apply h.trans
  nlinarith

/-- CCDN Lemma 2.7 for the total multiplicity of the projective residue
space. The constant depends only on dimension, and all counting inputs are
proved. Degree one is included using the exact multiplicity bounds. -/
theorem projective_hypersurface_totalMultiplicity_bound {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤ (p : ℝ) ^ (n + 1) +
      (projectiveHypersurfaceResidueConstant + ((n + 3) * (n + 4) ^ n : ℕ)) * (d : ℝ) ^ 2 *
        (p : ℝ) ^ n * Real.sqrt p := by
  have hi := mvPolynomial_irreducible_of_field_map _ _ hir
  have hc := projective_hypersurface_finite_field_bound p
    (map (Int.castRingHom (ZMod p)) f) (hf.map _) hd hir hsize
  change (Nat.card (ProjectiveHypersurfaceResidue f p) : ℝ) ≤ _ at hc
  rw [Nat.card_eq_fintype_card] at hc
  by_cases hd2 : 2 ≤ d
  · have hpN : 27 * d ^ 4 < p := by exact_mod_cast hsize
    have hs : d ^ 2 < p := by
      have hh : d ^ 2 ≤ d ^ 4 := by nlinarith [Nat.le_mul_self (d ^ 2)]
      nlinarith
    have hm := projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error f hf hd2 hi hs
    have hh := hm.trans (add_le_add hc le_rfl)
    convert hh using 1
    ring
  · have hd1 : d = 1 := by omega
    subst d
    have hm := (projectiveHypersurfaceTotalMultiplicity_bounds f hf hf0).2
    rw [Nat.mul_one] at hm
    have hmR : (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤
        Fintype.card (ProjectiveHypersurfaceResidue f p) := by exact_mod_cast hm
    apply (hmR.trans hc).trans
    have he : (0 : ℝ) ≤ (((n + 3) * (n + 4) ^ n : ℕ) : ℝ) * (p : ℝ) ^ n * Real.sqrt p := by
      positivity
    nlinarith

end
end CCDN

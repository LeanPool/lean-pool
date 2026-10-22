/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectivePlaneResidueDeterminant
public import LeanPool.CCDN.Determinant.SingularDeterminantCutoff
public import LeanPool.CCDN.Height.CountingHypotheses
import LeanPool.CCDN.Algebra.HomogeneousChartIrreducible
import LeanPool.CCDN.Determinant.PrimeAggregation
import LeanPool.CCDN.Determinant.ProjectiveMultiplicity
import LeanPool.CCDN.Determinant.ProjectiveResidueCardinality
import LeanPool.CCDN.Plane.CurveCount

/-!
Sharp prime-power and global prime-sum bounds for projective plane
evaluation matrices. The excluded-prime set is explicit.

A sharp finite-field count for an irreducible homogeneous plane
curve. Chart irreducibility, its full degree and the infinity correction
are proved; the affine input is the formalized Stepanov estimate.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For a homogeneous integer polynomial `f` of degree `d ≥ 2` with irreducible reduction modulo a
prime `p > 27 d⁴`, the reduced plane curve has at most `p + projectivePlaneResidueConstant · d² ·
√p` points over `𝔽_p`. -/
theorem projective_plane_finite_field_card_bound {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (Fintype.card (ProjectivePlaneResidue f p) : ℝ) ≤
      p + projectivePlaneResidueConstant * (d : ℝ) ^ 2 * Real.sqrt p := by
  classical
  rw [projectivePlaneResidueConstant_eq]
  let q := map (Int.castRingHom (ZMod p)) f
  have hX := variable_not_dvd_irreducible_homogeneous q (hf.map _) hir hd 0
  have hchart := affineChart_irreducible_of_not_variable_dvd q (hf.map _) hir hX
  have hdeg := affineChart_degree_of_not_variable_dvd q (hf.map _) hX
  have hproper := irreducible_homogeneous_not_dvd_variable q (hf.map _) hir hd 0
  have hcard := projectivePlaneResidue_card_le_affine_add_degree f hf hir hproper
  have hz (a : PlaneResidue (affineChart 2 f) p) :
      eval a.val (affineChart 2 q) = 0 := by
    rw [affineChart_map, eval_map]
    exact a.property
  have ha := plane_finite_field_card_bound p (affineChart 2 q) hchart
    (by rwa [hdeg]) (fun a : PlaneResidue (affineChart 2 f) p => a.val)
    Subtype.val_injective hz
  rw [hdeg, planeResidueConstant_eq] at ha
  have hcardR : (Fintype.card (ProjectivePlaneResidue f p) : ℝ) ≤
      Fintype.card (PlaneResidue (affineChart 2 f) p) + d := by exact_mod_cast hcard
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr
    (by exact_mod_cast (Fact.out : p.Prime).one_le)
  have hdsqrt : (d : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt p := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (d : ℝ))
    nlinarith
  linarith

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- For a homogeneous integer polynomial `f` of degree `d ≥ 2` with irreducible reduction modulo a
prime `p > 27 d⁴`, the total residue multiplicity of `f mod p` is at most `p +
(projectivePlaneDeterminantConstant + 1) · d² · √p`. -/
theorem projectivePlaneTotalMultiplicity_le {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      p + (projectivePlaneDeterminantConstant + 1) * (d : ℝ) ^ 2 * Real.sqrt p := by
  rw [projectivePlaneDeterminantConstant_eq]
  have hp : 27 * d ^ 4 < p := by exact_mod_cast hsize
  have hchar : d < p := by
    have h1 := Nat.le_mul_self d
    have h2 := Nat.le_mul_self (d * d)
    nlinarith only [hp, h1, h2]
  have hmass := projectivePlaneTotalMultiplicity_le_card_add_correction f hf hd hir hchar
  have hmassR : (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectivePlaneResidue f p) + (3 * d ^ 2 * (d - 1) : ℕ) := by
    exact_mod_cast hmass
  have hc := projective_plane_finite_field_card_bound f hf hd hir hsize
  rw [projectivePlaneResidueConstant_eq] at hc
  have hcorr := singular_correction_absorb (show 0 < d by omega)
    (L := 27 * (d : ℝ) ^ 4)
    (show (d : ℝ) ^ 4 ≤ 27 * (d : ℝ) ^ 4 by nlinarith [sq_nonneg ((d : ℝ) ^ 2)])
    hsize
  push_cast at hmassR hcorr
  nlinarith

/-- A uniform local exponent at primes `p > stepanovThreshold d` of irreducible reduction. -/
private theorem projective_plane_minorGcd_dvd {s N p d M : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : stepanovThreshold (d : ℝ) < p)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    ∃ e : ℕ, (s : ℝ) ^ 2 /
        (2 * (p + (projectivePlaneDeterminantConstant + 1) * (d : ℝ) ^ 2 * Real.sqrt p)) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  obtain ⟨hpos, e, _, he, hdiv⟩ := projective_reduction_minorGcd hs f hf hir.ne_zero
    F hF z hprim hz
  have hm := projectivePlaneTotalMultiplicity_le f hf hd hir hsize
  refine ⟨e, ?_, hdiv⟩
  apply le_trans (sub_le_sub_right ?_ (s : ℝ)) he
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

/-- Plane case of CCDN Proposition 3.2.6 at a single rank: for an independent evaluation of forms at
`s` primitive zeros of a degree-`d ≥ 2` plane curve whose reductions modulo primes `27 d⁴ < p ≤ s`
outside `bad` are irreducible, the logarithm of the gcd of the maximal minors is at least `s² / 2 ·
(log s - 4 log d - ∑_{p ∈ bad} log p / p - E)`, with the explicit constant `E =
degreeFourDeterminantError projectivePlaneDeterminantConstant`. -/
theorem projective_determinant_log_lower_at_rank {s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    {F : Fin N → MvPolynomial (Fin 3) ℤ} {z : Fin s → IntPoint 3}
    (hev : IsIndependentEvaluation f M F z) (bad : Finset ℕ)
    (hred : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ bad,
      stepanovThreshold (d : ℝ) < p → Irreducible (map (Int.castRingHom (ZMod p)) f)) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
      (∑ p ∈ bad, Real.log p / p) - degreeFourDeterminantError projectivePlaneDeterminantConstant) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := determinant_log_lower_of_local_divisors_degree_four (x := (s : ℝ))
    (by exact_mod_cast hs) (show 0 < d by omega)
    (by linarith [projectivePlaneDeterminantConstant_pos] :
      (0 : ℝ) ≤ projectivePlaneDeterminantConstant + 1)
    (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity) (Nat.cast_nonneg s) bad ∅ (empty_subset bad)
    (by simp) 0 (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent)) (by
      rw [Nat.floor_natCast]
      intro p hp hcut
      have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
      simpa only [div_div] using projective_plane_minorGcd_dvd hs f hf hd
        (hred p hp hcut) hcut F hev.isHomogeneous z hev.primitive hev.eval_eq_zero) (by simp)
  rw [sum_empty, add_zero] at h
  convert h using 1
  dsimp only [degreeFourDeterminantError]
  ring

end
end CCDN

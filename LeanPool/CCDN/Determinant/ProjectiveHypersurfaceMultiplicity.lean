/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import LeanPool.CCDN.Algebra.CharZeroOrGT
import LeanPool.CCDN.Algebra.HomogeneousChartIrreducible
import LeanPool.CCDN.Determinant.PlaneMultiplicitySmooth
import LeanPool.CCDN.Determinant.PlaneSingularities
import LeanPool.CCDN.ForMathlib.MvPolynomialDerivative
import LeanPool.CCDN.Height.FiniteFieldSectionCount
import Mathlib.RingTheory.SimpleRing.Principal

/-!
The singular multiplicity correction for projective hypersurfaces.
Chart coordinates inject each selected residue class into an affine
singular locus, whose codimension-two point bound is proved by interpolation.

The singular points of an irreducible hypersurface satisfy a
coefficient-uniform codimension-two finite-field bound.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A nonzero partial derivative cuts the irreducible hypersurface
properly. Fixed-degree finite-field interpolation bounds all its singular points. -/
private theorem hypersurface_singular_points_card_le {ι : Type*} [Fintype ι]
    {n p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin (n + 2)) (ZMod p))
    (hf : Irreducible f) (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin (n + 2) → ZMod p) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0) (hzsing : ∀ i j, eval (z i) (pderiv j f) = 0) :
    Fintype.card ι ≤ (n + 4) ^ n * f.totalDegree * (f.totalDegree - 1) * p ^ n := by
  classical
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hpos (CharZeroOrGT.of_charP hchar)
  have hdeg := pderiv_totalDegree_le f j
  have hnd := not_dvd_pderiv_of_pderiv_ne_zero hf.ne_zero hj
  have hdegrees : f.totalDegree + (pderiv j f).totalDegree ≤
      2 * (Fintype.card (ZMod p) - 1) := by
    rw [ZMod.card]
    omega
  have h := finite_field_common_zeros_card_le f (pderiv j f) hf.prime hnd hdegrees
    z hz hzf (fun i => hzsing i j)
  rw [ZMod.card] at h
  exact h.trans (Nat.mul_le_mul_right (p ^ n)
    (Nat.mul_le_mul_left ((n + 4) ^ n * f.totalDegree) hdeg))

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma projectiveHypersurfaceResidueMultiplicity_singular {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectiveHypersurfaceResidue f p)
    (hμ : 2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hf0 r) :
    ∀ j, eval (fun i => (hypersurfaceResidueChartLift r.val i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p))
        (projectiveHypersurfaceChart (hypersurfaceResiduePivot r.val) f))) = 0 := by
  have hp := (projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r).2.2.1
  change map (Int.castRingHom (ZMod p)) (originShift (hypersurfaceResidueChartLift r.val)
    (projectiveHypersurfaceChart (hypersurfaceResiduePivot r.val) f)) ∈ _ at hp
  rw [originShift_map] at hp
  exact singular_of_origin_order_ge_two _ _ hμ hp

/-- Count singular classes in their n+3 possible charts. The pivots and
multiplicities here are those of the reduced projective hypersurface. -/
private theorem projective_hypersurface_singular_residue_card_le {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    (Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
      2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r).card ≤
      (n + 3) * ((n + 4) ^ n * d * (d - 1) * p ^ n) := by
  classical
  let S := Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
    2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r
  let T (k : Fin (n + 3)) := S.filter fun r => hypersurfaceResiduePivot r.val = k
  have hk {k : Fin (n + 3)} (r : T k) : hypersurfaceResiduePivot r.val.val = k :=
    (Finset.mem_filter.mp r.property).2
  have hT (k : Fin (n + 3)) : (T k).card ≤ (n + 4) ^ n * d * (d - 1) * p ^ n := by
    let q := map (Int.castRingHom (ZMod p)) (projectiveHypersurfaceChart k f)
    have hq : Irreducible q ∧ q.totalDegree = d :=
      affineChart_rename_swap_irreducible_degree (Int.castRingHom (ZMod p)) f hf hd hir k
    let z : T k → Fin (n + 2) → ZMod p :=
      fun r j => (hypersurfaceResidueChartLift r.val.val j : ZMod p)
    have hz : Function.Injective z := by
      intro r t he
      apply Subtype.ext
      apply Subtype.ext
      exact projectiveResidueChart_injective_of_pivot_eq ((hk r).trans (hk t).symm) he
    have hzero (r : T k) : eval (z r) q = 0 := by
      have h := hypersurfaceResidueChartLift_zero f hf r.val.val r.val.property
      rw [hk r] at h
      simpa only [q, z, eval_map] using h
    have hsing (r : T k) (j : Fin (n + 2)) : eval (z r) (pderiv j q) = 0 := by
      have h := projectiveHypersurfaceResidueMultiplicity_singular f hf hir.ne_zero r.val
        (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2 j
      simpa only [hk r] using h
    have h := hypersurface_singular_points_card_le (p := p) q hq.1
      (by rw [hq.2]; omega) (by rwa [hq.2]) z hz hzero hsing
    simpa only [Fintype.card_coe, q, hq.2] using h
  have hsum : ∑ k : Fin (n + 3), (T k).card = S.card := by
    simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 3)))) => hT k)
  rw [hsum] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
    using h

/-- Singular classes contribute only a lower-order correction to the
projective point count; the leading term is not multiplied by the degree. -/
private theorem projectiveHypersurfaceTotalMultiplicity_le_card_add_correction {n p d : ℕ}
    [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hd : 2 ≤ d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        (n + 3) * (n + 4) ^ n * d ^ 2 * (d - 1) * p ^ n := by
  classical
  let S := Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
    2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r
  have hS : S.card ≤ (n + 3) * ((n + 4) ^ n * d * (d - 1) * p ^ n) :=
    projective_hypersurface_singular_residue_card_le f hf hd hir hchar
  have hpoint (r : ProjectiveHypersurfaceResidue f p) :
      projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r ≤
        1 + if r ∈ S then d else 0 := by
    have h := (projectiveHypersurfaceResidueMultiplicity_spec f hf hir.ne_zero r).2.1
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]; omega
    · rw [ite_eq_right hr]
      have hh : ¬ 2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hr
      omega
  have hsum : projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) + S.card * d := by
    calc _ ≤ ∑ r : ProjectiveHypersurfaceResidue f p, (1 + if r ∈ S then d else 0) :=
           Finset.sum_le_sum fun r _ => hpoint r
         _ = _ := by simp [Finset.sum_add_distrib]
  apply hsum.trans
  apply Nat.add_le_add_left
  convert Nat.mul_le_mul_right d hS using 1
  ring

/-- Above the square-degree cutoff the multiplicity correction has the
O_n(d^2 p^(dimension-1/2)) scale required by CCDN Lemma 2.7. -/
theorem projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error {n p d : ℕ}
    [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hd : 2 ≤ d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hsize : d ^ 2 < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 4) ^ n : ℕ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n * Real.sqrt p := by
  have hchar : d < p := (Nat.le_mul_self d).trans_lt (by simpa only [pow_two] using hsize)
  have h := projectiveHypersurfaceTotalMultiplicity_le_card_add_correction f hf hd hir hchar
  have hR : (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 4) ^ n * d ^ 2 * (d - 1) * p ^ n : ℕ) := by exact_mod_cast h
  have hs : (d : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by exact_mod_cast hsize.le)
  have hsub : ((d - 1 : ℕ) : ℝ) ≤ Real.sqrt p :=
    (by exact_mod_cast Nat.sub_le d 1 : ((d - 1 : ℕ) : ℝ) ≤ d).trans hs
  have hmul := mul_le_mul_of_nonneg_left hsub
    (show 0 ≤ (((n + 3) * (n + 4) ^ n : ℕ) : ℝ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n by positivity)
  apply hR.trans
  apply add_le_add le_rfl
  push_cast at hmul ⊢
  convert hmul using 1
  ring

end
end CCDN

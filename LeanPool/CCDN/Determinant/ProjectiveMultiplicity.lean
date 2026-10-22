/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectivePlaneResidueDeterminant
import LeanPool.CCDN.Algebra.HomogeneousChartIrreducible
import LeanPool.CCDN.Determinant.PlaneMultiplicitySmooth
import LeanPool.CCDN.Determinant.PlaneSingularities

/-! Singular projective residue classes are counted in their selected affine
charts. The correction is polynomial in the degree and does not change the
leading finite-field point-count term. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma projectivePlaneResidueMultiplicity_singular {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectivePlaneResidue f p)
    (hμ : 2 ≤ projectivePlaneResidueMultiplicity f hf hf0 r) :
    ∀ j, eval (fun i => (projectiveResidueChartLift r.val i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p))
        (projectivePlaneChart (projectiveResiduePivot r.val) f))) = 0 := by
  have hp := (projectivePlaneResidueMultiplicity_spec f hf hf0 r).2.2.1
  change map (Int.castRingHom (ZMod p)) (originShift (projectiveResidueChartLift r.val)
    (projectivePlaneChart (projectiveResiduePivot r.val) f)) ∈ _ at hp
  rw [originShift_map] at hp
  exact singular_of_origin_order_ge_two _ _ hμ hp

/-- Count singular classes in their three possible charts. The pivots and
multiplicities here are those of the reduced projective curve. -/
private theorem projective_singular_residue_card_le {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    (Finset.univ.filter fun r : ProjectivePlaneResidue f p =>
      2 ≤ projectivePlaneResidueMultiplicity f hf hir.ne_zero r).card ≤ 3 * d * (d - 1) := by
  classical
  let S := Finset.univ.filter fun r : ProjectivePlaneResidue f p =>
    2 ≤ projectivePlaneResidueMultiplicity f hf hir.ne_zero r
  let T (k : Fin 3) := S.filter fun r => projectiveResiduePivot r.val = k
  have hk {k : Fin 3} (r : T k) : projectiveResiduePivot r.val.val = k :=
    (Finset.mem_filter.mp r.property).2
  have hT (k : Fin 3) : (T k).card ≤ d * (d - 1) := by
    let q := map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f)
    have hq : Irreducible q ∧ q.totalDegree = d :=
      affineChart_rename_swap_irreducible_degree (Int.castRingHom (ZMod p)) f hf hd hir k
    let z : T k → Fin 2 → ZMod p := fun r j => (projectiveResidueChartLift r.val.val j : ZMod p)
    have hz : Function.Injective z := by
      intro r t he
      apply Subtype.ext
      apply Subtype.ext
      exact projectiveResidueChart_injective_of_pivot_eq ((hk r).trans (hk t).symm) he
    have hzero (r : T k) : eval (z r) q = 0 := by
      have h := projectiveResidueChartLift_zero f hf r.val.val r.val.property
      rw [hk r] at h
      simpa only [q, z, eval_map, projectivePlaneChart] using h
    have hsing (r : T k) (j : Fin 2) : eval (z r) (pderiv j q) = 0 := by
      have h := projectivePlaneResidueMultiplicity_singular f hf hir.ne_zero r.val
        (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2 j
      simpa only [hk r] using h
    have h := plane_singular_points_card_le (p := p) q hq.1
      (by rw [hq.2]; omega) (by rwa [hq.2]) z hz hzero hsing
    simpa only [Fintype.card_coe, q, hq.2] using h
  have hsum : ∑ k : Fin 3, (T k).card = S.card := by
    simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hT k)
  rw [hsum] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
    using h

/-- The singular correction does not multiply the leading point-count term. -/
theorem projectivePlaneTotalMultiplicity_le_card_add_correction {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    projectivePlaneTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectivePlaneResidue f p) + 3 * d ^ 2 * (d - 1) := by
  classical
  let S := Finset.univ.filter fun r : ProjectivePlaneResidue f p =>
    2 ≤ projectivePlaneResidueMultiplicity f hf hir.ne_zero r
  have hS : S.card ≤ 3 * d * (d - 1) :=
    projective_singular_residue_card_le f hf hd hir hchar
  have hpoint (r : ProjectivePlaneResidue f p) :
      projectivePlaneResidueMultiplicity f hf hir.ne_zero r ≤ 1 + if r ∈ S then d else 0 := by
    have h := (projectivePlaneResidueMultiplicity_spec f hf hir.ne_zero r).2.1
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]; omega
    · rw [ite_eq_right hr]
      have hh : ¬ 2 ≤ projectivePlaneResidueMultiplicity f hf hir.ne_zero r := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hr
      omega
  have hsum : projectivePlaneTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectivePlaneResidue f p) + S.card * d := by
    calc _ ≤ ∑ r : ProjectivePlaneResidue f p, (1 + if r ∈ S then d else 0) :=
           Finset.sum_le_sum fun r _ => hpoint r
         _ = _ := by simp [Finset.sum_add_distrib]
  have hmul := Nat.mul_le_mul_right d hS
  nlinarith

end
end CCDN

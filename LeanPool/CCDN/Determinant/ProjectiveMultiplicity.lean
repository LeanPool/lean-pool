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

private lemma projectiveResidueChart_normalized {p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace 2 p) :
    (Fin.cons 1 (fun j => (projectiveResidueChartLift r j : ZMod p))) ∘
      Equiv.swap 0 (projectiveResiduePivot r) =
        (r.rep (projectiveResiduePivot r))⁻¹ • r.rep := by
  have h : Fin.cons 1 (fun j => (projectiveResidueChartLift r j : ZMod p)) =
      (r.rep (projectiveResiduePivot r))⁻¹ • (r.rep ∘ Equiv.swap 0 (projectiveResiduePivot r)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [projectiveResiduePivot_ne_zero]
    · simp [cast_projectiveResidueChartLift, div_eq_mul_inv, mul_comm]
  rw [h]
  funext j
  simp

private theorem projectiveResidueChart_injective_of_pivot_eq {p : ℕ} [Fact p.Prime]
    {r t : ProjectiveResidueSpace 2 p}
    (hk : projectiveResiduePivot r = projectiveResiduePivot t)
    (ha : (fun j => (projectiveResidueChartLift r j : ZMod p)) =
      (fun j => (projectiveResidueChartLift t j : ZMod p))) : r = t := by
  have he : (r.rep (projectiveResiduePivot r))⁻¹ • r.rep =
      (t.rep (projectiveResiduePivot t))⁻¹ • t.rep := by
    rw [← projectiveResidueChart_normalized, ← projectiveResidueChart_normalized, hk, ha]
  have hh := congrArg (fun v : Fin 3 → ZMod p => r.rep (projectiveResiduePivot r) • v) he
  have hs : (r.rep (projectiveResiduePivot r) / t.rep (projectiveResiduePivot t)) • t.rep =
      r.rep := by
    simpa only [smul_smul, mul_inv_cancel₀ (projectiveResiduePivot_ne_zero r), one_smul,
      div_eq_mul_inv] using hh.symm
  calc
    r = Projectivization.mk (ZMod p) r.rep r.rep_nonzero := r.mk_rep.symm
    _ = Projectivization.mk (ZMod p) t.rep t.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨_, hs⟩
    _ = t := t.mk_rep

private theorem projectivePlaneChart_irreducible_degree {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (k : Fin 3) :
    Irreducible (map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f)) ∧
      (map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f)).totalDegree = d := by
  let q := rename (Equiv.swap 0 k) (map (Int.castRingHom (ZMod p)) f)
  have hq : q.IsHomogeneous d := (hf.map _).rename_isHomogeneous
  have hqi : Irreducible q :=
    (MulEquiv.irreducible_iff (f := renameEquiv (ZMod p) (Equiv.swap 0 k))).mpr hir
  have hX := variable_not_dvd_irreducible_homogeneous q hq hqi hd 0
  have he : map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f) = affineChart 2 q := by
    change map _ (affineChart 2 (rename (Equiv.swap 0 k) f)) = _
    rw [← affineChart_map, map_rename]
  rw [he]
  exact ⟨affineChart_irreducible_of_not_variable_dvd q hq hqi hX,
    affineChart_degree_of_not_variable_dvd q hq hX⟩

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
    have hq := projectivePlaneChart_irreducible_degree f hf hd hir k
    let z : T k → Fin 2 → ZMod p := fun r j => (projectiveResidueChartLift r.val.val j : ZMod p)
    have hz : Function.Injective z := by
      intro r t he
      apply Subtype.ext
      apply Subtype.ext
      exact projectiveResidueChart_injective_of_pivot_eq ((hk r).trans (hk t).symm) he
    have hzero (r : T k) : eval (z r) q = 0 := by
      have h := projectiveResidueChartLift_zero f hf r.val.val r.val.property
      rw [hk r] at h
      simpa only [q, z, eval_map] using h
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

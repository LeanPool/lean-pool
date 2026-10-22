/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.SingularReduction
import LeanPool.CCDN.Determinant.PlaneSingularities

/-! Multiplicity greater than one forces a singular point. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma origin_power_pderiv_zero {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} {μ : ℕ} (hμ : 2 ≤ μ)
    (hf : f ∈ idealOfVars σ K ^ μ) (j : σ) :
    eval (0 : σ → K) (pderiv j f) = 0 := by
  classical
  rw [mem_pow_idealOfVars_iff'] at hf
  have hc := hf (Finsupp.single j 1)
    (by simp; omega)
  simpa only [eval_zero, constantCoeff_eq, coeff_pderiv, zero_add,
    Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one] using hc

/-- Only singular points can have local order at least two. -/
theorem singular_of_origin_order_ge_two {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (a : σ → K) {μ : ℕ} (hμ : 2 ≤ μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ) :
    ∀ j, eval a (pderiv j f) = 0 := by
  intro j
  rw [← eval_zero_originShift, ← pderiv_originShift]
  exact origin_power_pderiv_zero hμ hf j

/-- In particular, every positive order at a smooth point is one. -/
theorem origin_order_eq_one_of_smooth {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (a : σ → K) {μ : ℕ} (hμ : 0 < μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ)
    (hs : ∃ j, eval a (pderiv j f) ≠ 0) : μ = 1 := by
  by_contra h
  obtain ⟨j, hj⟩ := hs
  exact hj (singular_of_origin_order_ge_two f a (by omega) hf j)

private lemma planeResidueMultiplicity_singular {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (a : PlaneResidue f p) (ha : 2 ≤ planeResidueMultiplicity f p hf a) :
    ∀ j, eval a.val (pderiv j (map (Int.castRingHom (ZMod p)) f)) = 0 := by
  have hp := (planeResidueMultiplicity_spec f p hf a).2.2.1
  change map (Int.castRingHom (ZMod p)) (originShift (planeResidueLift a) f) ∈ _ at hp
  rw [originShift_map] at hp
  have he : (fun j => (Int.castRingHom (ZMod p)) (planeResidueLift a j)) = a.val := by
    funext j
    exact cast_planeResidueLift a j
  rw [he] at hp
  exact singular_of_origin_order_ge_two _ a.val ha hp

/-- The multiplicity correction costs only a degree-dependent constant.
The leading term remains the number of finite-field points. -/
theorem planeTotalMultiplicity_le_card_add_correction {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ)
    (hf : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hpos : 0 < (map (Int.castRingHom (ZMod p)) f).totalDegree)
    (hchar : f.totalDegree < p) :
    planeTotalMultiplicity f p hf.ne_zero ≤
      Fintype.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) := by
  classical
  let S : Finset (PlaneResidue f p) :=
    Finset.univ.filter (fun a => 2 ≤ planeResidueMultiplicity f p hf.ne_zero a)
  have hd : (map (Int.castRingHom (ZMod p)) f).totalDegree ≤ f.totalDegree := by
    rw [map_eq_eval₂Hom_C_comp]
    exact linear_eval₂_totalDegree_le _ X (fun j => le_of_eq (totalDegree_X j)) f
  have hS : S.card ≤ f.totalDegree * (f.totalDegree - 1) := by
    have hc := plane_singular_points_card_le (p := p) _ hf hpos (hd.trans_lt hchar)
      (fun a : S => a.val.val)
      (fun a b h => Subtype.ext (Subtype.ext h))
      (fun a => by rw [eval_map]; exact a.val.property)
      (fun a j => planeResidueMultiplicity_singular f hf.ne_zero a.val
        (Finset.mem_filter.mp a.property).2 j)
    have hc' : S.card ≤ (map (Int.castRingHom (ZMod p)) f).totalDegree *
        ((map (Int.castRingHom (ZMod p)) f).totalDegree - 1) := by simpa using hc
    exact hc'.trans (Nat.mul_le_mul hd (Nat.sub_le_sub_right hd 1))
  have hpoint (a : PlaneResidue f p) : planeResidueMultiplicity f p hf.ne_zero a ≤
      1 + if a ∈ S then f.totalDegree else 0 := by
    have hbound := (planeResidueMultiplicity_spec f p hf.ne_zero a).2.1
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]; omega
    · rw [ite_eq_right ha]
      have hn : ¬2 ≤ planeResidueMultiplicity f p hf.ne_zero a := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      omega
  have hsum : planeTotalMultiplicity f p hf.ne_zero ≤
      Fintype.card (PlaneResidue f p) + S.card * f.totalDegree := by
    calc _ ≤ ∑ a : PlaneResidue f p, (1 + if a ∈ S then f.totalDegree else 0) :=
           Finset.sum_le_sum fun a _ => hpoint a
         _ = _ := by simp [Finset.sum_add_distrib]
  have hmul := Nat.mul_le_mul_right f.totalDegree hS
  nlinarith

end
end CCDN

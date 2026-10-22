/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hypersurface.GraphHyperplaneRestriction
import LeanPool.CCDN.Algebra.IntegerPolynomialAvoidance
import LeanPool.CCDN.Hypersurface.EffectiveHyperplaneAvoidance
import LeanPool.CCDN.Hypersurface.GoodHyperplaneReindex

/-! A good integer hyperplane normal of height at most d³, obtained from
the universal Noether detector and integer-grid avoidance. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma exists_good_hyperplane_double_option {n : ℕ}
    (f : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ (D : ℤ) (a : Option (Fin (2 + n)) → ℤ),
      D ≠ 0 ∧ |D| ≤ (d ^ 3 : ℕ) ∧ (∀ i, |a i| ≤ (d ^ 3 : ℕ)) ∧
      (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)).totalDegree = d ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)) := by
  obtain ⟨G, hG, hhom, _, hbad⟩ := exists_effective_hyperplane_avoidance f d hd hf hir
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hdeg : G.totalDegree ≤ d ^ 3 := by
    rw [hhom.totalDegree hG]
    have he : d * (d ^ 2 - 1) + d = d ^ 3 := by
      calc
        _ = d * ((d ^ 2 - 1) + 1) := by ring
        _ = d * d ^ 2 := by rw [Nat.sub_add_cancel hd2]
        _ = _ := by ring
    omega
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero G hG (d ^ 3) hdeg
  let A : Option (Option (Fin (2 + n))) → ℚ := fun i => v i
  have hvalueQ : eval₂ (Int.castRingHom ℚ) A G ≠ 0 := by
    have he : eval₂ (Int.castRingHom ℚ) A G = (eval v G : ℚ) := by
      rw [eval₂_eq_eval_map]
      exact (map_eval (Int.castRingHom ℚ) v G).symm
    rw [he]
    exact_mod_cast hvalue
  have hD : v none ≠ 0 := by
    intro hz
    apply hvalueQ
    exact hbad ℚ A (fun h => (h (by simp [A, hz])).elim)
  have hirA : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => -A (some i) / A none) (map (Int.castRingHom ℚ) f)) := by
    by_contra hn
    exact hvalueQ (hbad ℚ A (fun _ => hn))
  let a := fun i => -v (some i)
  have hα : (fun i => (a i : ℚ) / (v none : ℚ)) =
      (fun i => -A (some i) / A none) := by
    funext i
    simp [a, A]
  refine ⟨v none, a, hD, ?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (hv none).1]
    exact (hv none).2
  · intro i
    simpa only [a, abs_neg, abs_of_nonneg (hv (some i)).1] using (hv (some i)).2
  · rw [hα]
    apply (graphHyperplaneRestriction_homogeneous _ (hf.map (Int.castRingHom ℚ))).totalDegree
    intro hz
    exact hirA.ne_zero (by rw [hz, map_zero])
  · rwa [hα]

/-- Full-degree geometrically integral hyperplane restriction, with a cubic
integer normal bound independent of the coefficients and ambient dimension. -/
theorem exists_geometrically_good_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ),
      D ≠ 0 ∧ |D| ≤ (d ^ 3 : ℕ) ∧ (∀ i, |a i| ≤ (d ^ 3 : ℕ)) ∧
      (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)).totalDegree = d ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)) := by
  let e : Fin (3 + n) ≃ Option (Fin (2 + n)) :=
    (finCongr (by omega)).trans (_root_.finSuccEquiv (2 + n))
  let F := rename (Equiv.optionCongr e) f
  have hFir : AbsolutelyIrreducible F := by
    rw [AbsolutelyIrreducible, map_rename]
    exact (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) (Equiv.optionCongr e)).toMulEquiv)).mpr hir
  obtain ⟨D, a, hD, hDb, hab, _, hirA⟩ :=
    exists_good_hyperplane_double_option F d hd hf.rename_isHomogeneous hFir
  have hgood : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => ((a ∘ e) i : ℚ) / D) (map (Int.castRingHom ℚ) f)) := by
    have he := congrArg (map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (graphHyperplaneRestriction_rename e (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f))
    rw [map_rename] at he
    apply (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) e).toMulEquiv)).mp
    change Irreducible (rename e (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (graphHyperplaneRestriction ((fun i => (a i : ℚ) / D) ∘ e)
        (map (Int.castRingHom ℚ) f))))
    rw [he]
    simpa only [AbsolutelyIrreducibleRat, F, map_rename] using hirA
  refine ⟨D, a ∘ e, hD, hDb, fun i => hab (e i), ?_, ?_⟩
  · apply (graphHyperplaneRestriction_homogeneous _ (hf.map (Int.castRingHom ℚ))).totalDegree
    intro hz
    exact hgood.ne_zero (by rw [hz, map_zero])
  · exact hgood

end
end CCDN

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Plane.Bezout

/-! Distinct-point bounds obtained from the auxiliary polynomials and
Bézout. The sharp finite-field estimate remains an explicit hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Mapping an integer polynomial to `ℚ` preserves its total degree. -/
lemma rational_map_totalDegree {σ : Type*} (f : MvPolynomial σ ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective Int.cast_injective _

/-- If the image of an integer polynomial in a field `F` of characteristic zero is irreducible,
then its image over `ℚ` is irreducible. -/
lemma rational_irreducible_of_charZero_map {F σ : Type*} [Field F] [CharZero F]
    (f : MvPolynomial σ ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  apply mvPolynomial_irreducible_of_field_map (algebraMap ℚ F)
  rw [map_map]
  have he : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by ext; simp
  rw [he]
  exact hf

/-- The precise Bézout step for a homogeneous integer auxiliary
polynomial and a primitive equation whose chart has full degree. -/
theorem plane_chart_points_card_le_auxiliary_degree {d M t : ℕ}
    (f g : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hg : g.IsHomogeneous M) (hprim : PrimitiveIntegerPolynomial f)
    (hdchart : (affineChart 2 f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (affineChart 2 f)))
    (hnd : ¬ f ∣ g) (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hzf : ∀ i, eval (z i) (affineChart 2 f) = 0)
    (hzg : ∀ i, eval (Fin.cons 1 (z i)) g = 0) : t ≤ d * M := by
  let zQ : Fin t → Fin 2 → ℚ := fun i j => (z i j : ℚ)
  have hiQ : Function.Injective zQ := by
    intro i j he
    apply hinj
    funext k
    exact Int.cast_injective (congrFun he k)
  have hfQ : ∀ i, eval (zQ i) (MvPolynomial.map (Int.castRingHom ℚ) (affineChart 2 f)) = 0 := by
    intro i
    have h := congrArg (Int.castRingHom ℚ) (hzf i)
    rw [map_eval, map_zero] at h
    exact h
  have hgQ : ∀ i, eval (zQ i) (MvPolynomial.map (Int.castRingHom ℚ) (affineChart 2 g)) = 0 := by
    intro i
    have h := congrArg (Int.castRingHom ℚ) (hzg i)
    rw [← affineChart_eval] at h
    rw [map_eval, map_zero] at h
    exact h
  have hndQ : ¬ MvPolynomial.map (Int.castRingHom ℚ) (affineChart 2 f) ∣
      MvPolynomial.map (Int.castRingHom ℚ) (affineChart 2 g) :=
    rational_affineChart_not_dvd hf hf0 hg hprim hdchart hnd
  have h := plane_common_zeros_card_le _ _ hir hndQ zQ hiQ hfQ hgQ
  rw [Fintype.card_fin, rational_map_totalDegree, rational_map_totalDegree, hdchart] at h
  exact h.trans (Nat.mul_le_mul_left d ((affineChart_totalDegree_le g).trans hg.totalDegree_le))

/-- Enumerating the integer zeros transfers finite-family bounds to
the counting interface, including empty point sets. -/
lemma integer_zero_count_le_of_family_bound {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (B R : ℝ)
    (hbound : ∀ (t : ℕ) (z : Fin t → Fin n → ℤ), Function.Injective z →
      (∀ i, eval (z i) f = 0) → (∀ i, InBox (z i) B) → (t : ℝ) ≤ R) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B : ℝ) ≤ R := by
  classical
  let S := integralPoints (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → Fin n → ℤ := fun i => (e i).val
  have hinj : Function.Injective z := Subtype.val_injective.comp e.injective
  have hzero : ∀ i, eval (z i) f = 0 := by
    intro i
    apply Int.cast_injective (α := ℚ)
    have h := (mem_integralPoints.mp (e i).property).2
    change eval (fun j => (z i j : ℚ)) (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 at h
    change (Int.castRingHom ℚ) (eval (z i) f) = 0
    rw [map_eval]
    exact h
  have hbox : ∀ i, InBox (z i) B := fun i => (mem_integralPoints.mp (e i).property).1
  have h := hbound _ z hinj hzero hbox
  simpa only [Fintype.card_coe, S, count] using h

end
end CCDN

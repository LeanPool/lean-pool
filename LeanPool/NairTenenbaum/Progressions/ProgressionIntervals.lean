/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.IntegerIntervalDecomposition
public import LeanPool.NairTenenbaum.Progressions.AffineWeights

/-! # Arithmetic progressions as integer intervals after affine substitution -/

@[expose] public section

namespace NairTenenbaum

/-- The short sum restricted to the residue class `a` modulo `q`. -/
noncomputable def progressionSum {k : ℕ} (Q : Fin k → Polynomial ℤ) (F : ArithmeticMap k)
    (q a : ℕ) (x y : ℝ) : ℝ :=
  ∑ n ∈ (shortInterval x y).filter (fun n => Nat.ModEq q n a),
    extendArithmeticMap F (fun j => ((Q j).eval (n : ℤ)).natAbs)

/-- The main term in Corollary 1. -/
noncomputable def progressionMainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (q : ℕ) (x y : ℝ) : ℝ :=
  (y / q) * progressionSieveProduct P.total q x *
    ∑ N ∈ (positiveUpTo x).filter (fun N : ℕ+ => Nat.Coprime q N), P.weight F N

theorem PolynomialSystem.affine_mainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs)
    (F : ArithmeticMap k) (x y : ℝ) :
    mainTerm (P.affine q a hq hqa) F x (y / q) = progressionMainTerm P F q x y := by
  unfold mainTerm progressionMainTerm
  rw [P.affine_total, sieveProduct_comp_affine P.total q a x hqa, P.sum_affine_weight]

/-- Membership in the transformed interval is exactly membership of the
integer affine value in the original real interval. -/
theorem mem_affine_interval_iff {q : ℕ} (hq : 0 < q) (a : ℤ) (x y : ℝ) (t : ℤ) :
    t ∈ Finset.Ioc ⌊(x - a) / q⌋ ⌊(x + y - a) / q⌋ ↔
      x < (q : ℝ) * t + a ∧ (q : ℝ) * t + a ≤ x + y := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Finset.mem_Ioc, Int.floor_lt, Int.le_floor, div_lt_iff₀ hq₀, le_div_iff₀ hq₀]
  constructor <;> intro H <;> constructor <;> nlinarith [H.1, H.2]

/-- Integer rounding costs less than one unit of transformed length. -/
theorem affine_interval_endpoint_bounds {q : ℕ} (hq : 0 < q) (a : ℤ)
    {x y : ℝ} (hy : 0 ≤ y) (hyq : 1 ≤ y / q) :
    ⌊(x - a) / q⌋ ≤ ⌊(x + y - a) / q⌋ ∧
    y / q - 1 ≤ (⌊(x + y - a) / q⌋ : ℝ) - (⌊(x - a) / q⌋ : ℝ) ∧
    (⌊(x + y - a) / q⌋ : ℝ) - (⌊(x - a) / q⌋ : ℝ) ≤ 2 * (y / q) := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : (x + y - a) / q = (x - a) / q + y / q := by ring
  have ha := Int.floor_le ((x - a) / (q : ℝ))
  have ha' := Int.lt_floor_add_one ((x - a) / (q : ℝ))
  have hb := Int.floor_le ((x + y - a) / (q : ℝ))
  have hb' := Int.lt_floor_add_one ((x + y - a) / (q : ℝ))
  refine ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hq₀.le), ?_, ?_⟩ <;> linarith

/-- Reindexing by `(n-a)/q` bounds the progression sum by the integer sum of
the substituted family. Negative transformed indices are allowed. -/
theorem PolynomialSystem.progressionSum_le_affine_integerSum {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (q a : ℕ) (hq : 0 < q)
    (hqa : q.Coprime (P.total.eval (a : ℤ)).natAbs) {x y : ℝ} (hxy : 0 ≤ x + y) :
    progressionSum P.Q F q a x y ≤ (P.affine q a hq.ne' hqa).integerSum F
      ⌊(x - a) / q⌋ ⌊(x + y - a) / q⌋ := by
  classical
  let S := (shortInterval x y).filter (fun n => Nat.ModEq q n a)
  let f : ℕ → ℤ := fun n => ((n : ℤ) - a) / q
  have hf (n : ℕ) (hn : n ∈ S) : (q : ℤ) * f n + a = n := by
    have hd := (Finset.mem_filter.mp hn).2.symm.dvd
    dsimp only [f]
    rw [Int.mul_ediv_cancel' hd]
    ring
  have hinj : Set.InjOn f S := by
    intro m hm n hn heq
    have H : (m : ℤ) = n := (hf m hm).symm.trans ((congrArg (fun z : ℤ => (q : ℤ) * z + a)
        heq).trans (hf n hn))
    exact Int.ofNat_inj.mp H
  have hmap : ∀ n ∈ S, f n ∈ Finset.Ioc ⌊(x - (a : ℤ)) / q⌋ ⌊(x + y - (a : ℤ)) / q⌋ := by
    intro n hn
    apply (mem_affine_interval_iff hq a x y (f n)).mpr
    have hreal : (q : ℝ) * f n + a = n := by exact_mod_cast hf n hn
    have H := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    simp only [Int.cast_natCast]
    rw [hreal]
    exact ⟨Nat.lt_of_floor_lt H.1, (Nat.le_floor_iff hxy).mp H.2⟩
  unfold progressionSum PolynomialSystem.integerSum
  apply Finset.sum_le_sum_of_injOn f hinj (Finset.image_subset_iff.mpr hmap)
  · intro n hn
    have heq : (fun j => (((P.affine q a hq.ne' hqa).Q j).eval (f n)).natAbs) =
        (fun j => ((P.Q j).eval (n : ℤ)).natAbs) := by
      funext j
      change (((P.Q j).comp (affinePolynomial q a)).eval (f n)).natAbs = _
      rw [Polynomial.eval_comp, eval_affinePolynomial, hf n hn]
    rw [heq]
  · intro _ _ _
    exact extendArithmeticMap_nonneg hF _

end NairTenenbaum

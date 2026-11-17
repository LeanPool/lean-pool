/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Catalysts from additive completion certificates

Equality in the Grothendieck additive group means equality after adding a
common element of the original semiring. This gives catalytic inequalities
without assuming additive cancellation.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

open Algebra

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- A negative-unit certificate in the additive completion gives a catalytic
inequality in the original semiring, even when its addition is not cancellative. -/
theorem exists_catalyst_of_completion_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (m k : ℕ) (d X Y s : S) (hXY : X ≤ Y)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      GrothendieckAddGroup.of Y - GrothendieckAddGroup.of X +
        GrothendieckAddGroup.of (d * s) - k • GrothendieckAddGroup.of s) :
    ∃ D : S, D + (m : S) + d * s ≤ D + (k : S) * s := by
  let η : S →+ GrothendieckAddGroup S := GrothendieckAddGroup.of
  have hm : η (m : S) = m • η 1 := by
    rw [← nsmul_one m, map_nsmul]
  have hk : η ((k : S) * s) = k • η s := by
    rw [← nsmul_eq_mul, map_nsmul]
  have heq' : η ((m : S) + Y + d * s) = η (X + (k : S) * s) := by
    simp only [map_add, hm, hk]
    change -(m : ℤ) • η 1 = η Y - η X + η (d * s) - k • η s at heq
    simp only [neg_zsmul, natCast_zsmul] at heq
    calc
      m • η 1 + η Y + η (d * s) =
          m • η 1 + (η Y - η X + η (d * s) - k • η s) + η X + k • η s := by abel
      _ = m • η 1 + -(m • η 1) + η X + k • η s := by rw [← heq]
      _ = η X + k • η s := by abel
  obtain ⟨C, hC⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid S)).exists_of_eq heq'
  refine ⟨(C : S) + Y, ?_⟩
  calc
    ((C : S) + Y) + (m : S) + d * s = (C : S) + ((m : S) + Y + d * s) := by ac_rfl
    _ = (C : S) + (X + (k : S) * s) := hC
    _ ≤ (C : S) + (Y + (k : S) * s) :=
      hadd _ _ _ _ le_rfl (hadd _ _ _ _ hXY le_rfl)
    _ = ((C : S) + Y) + (k : S) * s := by ac_rfl

/-- A finite nonnegative integral combination of completion relations gives
one catalytic inequality. The catalyst absorbs the aggregate of the ordered
relations, and the resulting test element is the same combination of the
original test elements. -/
theorem exists_catalyst_of_completion_sum_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    {I : Type*} [Fintype I] (m k : ℕ) (d : S)
    (n : I → ℕ) (X Y Z : I → S) (hXY : ∀ i, X i ≤ Y i)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      ∑ i, n i • (GrothendieckAddGroup.of (Y i) - GrothendieckAddGroup.of (X i) +
        GrothendieckAddGroup.of (d * Z i) - k • GrothendieckAddGroup.of (Z i))) :
    ∃ D : S, D + (m : S) + d * (∑ i, n i • Z i) ≤
      D + (k : S) * (∑ i, n i • Z i) := by
  classical
  have hnsmul (a b : S) (hab : a ≤ b) (l : ℕ) : l • a ≤ l • b := by
    induction l with
    | zero => simp
    | succ l ih => simpa only [succ_nsmul] using hadd _ _ _ _ ih hab
  have hsum (t : Finset I) : ∑ i ∈ t, n i • X i ≤ ∑ i ∈ t, n i • Y i := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using
        hadd _ _ _ _ (hnsmul (X i) (Y i) (hXY i) (n i)) ih
  apply exists_catalyst_of_completion_eq hadd m k d
    (∑ i, n i • X i) (∑ i, n i • Y i) (∑ i, n i • Z i) (hsum Finset.univ)
  convert heq using 1
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    map_sum, map_nsmul, Finset.mul_sum, mul_smul_comm, ← smul_comm k]
  rw [Finset.smul_sum]

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields

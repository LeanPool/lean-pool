/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic

/-!
# The minimal majorant

Equations (11)–(13) and the submultiplicativity assertion following (13).
The paper's `max` is implemented as a supremum; no attainment is assumed.
Including zero makes the definition valid also for the identically zero function.
-/

@[expose] public section

namespace NairTenenbaum

/-- Ratios used to define `G_F`, together with zero. -/
def majorantRatios {k : ℕ} (F : ArithmeticMap k) (m : Tuple k) : Set ℝ :=
  {0} ∪ {t | ∃ n, Coprime m n ∧ F n ≠ 0 ∧ t = F (m * n) / F n}

/-- Equation (11), with the supremum convention described above. -/
noncomputable def minimalMajorant {k : ℕ} (F : ArithmeticMap k) (m : Tuple k) : ℝ :=
  sSup (majorantRatios F m)

theorem zero_mem_majorantRatios {k : ℕ} (F : ArithmeticMap k) (m : Tuple k) :
    0 ∈ majorantRatios F m := Or.inl rfl

theorem majorantRatios_nonempty {k : ℕ} (F : ArithmeticMap k) (m : Tuple k) :
    (majorantRatios F m).Nonempty := ⟨0, zero_mem_majorantRatios F m⟩

theorem Admissible.ratios_bounded {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B) (m : Tuple k) :
    ∀ t ∈ majorantRatios F m, t ≤ growthBound A B ε m := by
  intro t ht
  rcases ht with ht | ⟨n, hmn, hn, rfl⟩
  · have : t = 0 := ht
    simpa [this] using growthBound_nonneg hA hB m
  · exact (div_le_iff₀ (lt_of_le_of_ne (hF.nonneg n) (Ne.symm hn))).2
      (hF.growth m n hmn)

theorem Admissible.ratios_bddAbove {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B) (m : Tuple k) :
    BddAbove (majorantRatios F m) := ⟨_, hF.ratios_bounded hA hB m⟩

theorem Admissible.minimalMajorant_nonneg {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B) (m : Tuple k) :
    0 ≤ minimalMajorant F m :=
  le_csSup (hF.ratios_bddAbove hA hB m) (zero_mem_majorantRatios F m)

/-- Equation (13). -/
theorem Admissible.minimalMajorant_le {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B) (m : Tuple k) :
    minimalMajorant F m ≤ growthBound A B ε m :=
  csSup_le (majorantRatios_nonempty F m) (hF.ratios_bounded hA hB m)

/-- Equation (12), including the case `F n = 0`. -/
theorem Admissible.le_minimalMajorant_mul {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (m n : Tuple k) (hmn : Coprime m n) :
    F (m * n) ≤ minimalMajorant F m * F n := by
  by_cases hn : F n = 0
  · simpa [hn] using hF.growth m n hmn
  · apply (div_le_iff₀ (lt_of_le_of_ne (hF.nonneg n) (Ne.symm hn))).1
    exact le_csSup (hF.ratios_bddAbove hA hB m) (Or.inr ⟨n, hmn, hn, rfl⟩)

/-- `G_F` is pointwise the least nonnegative factor controlling all coprime translates. -/
theorem minimalMajorant_le_of_bound {k : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (m : Tuple k) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, Coprime m n → F (m * n) ≤ C * F n) :
    minimalMajorant F m ≤ C := by
  apply csSup_le (majorantRatios_nonempty F m)
  intro t ht
  rcases ht with ht | ⟨n, hmn, hn, rfl⟩
  · have : t = 0 := ht
    simpa [this] using hC
  · exact (div_le_iff₀ (lt_of_le_of_ne (hF n) (Ne.symm hn))).2 (h n hmn)

/-- Submultiplicativity of the minimal majorant under coordinatewise coprimality. -/
theorem Admissible.minimalMajorant_submultiplicative {k : ℕ} {A B ε : ℝ}
    {F : ArithmeticMap k} (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (a b : Tuple k) (hab : Coprime a b) :
    minimalMajorant F (a * b) ≤ minimalMajorant F a * minimalMajorant F b := by
  apply minimalMajorant_le_of_bound hF.nonneg (a * b)
    (mul_nonneg (hF.minimalMajorant_nonneg hA hB a) (hF.minimalMajorant_nonneg hA hB b))
  intro n hn
  obtain ⟨han, hbn⟩ := (coprime_mul_left a b n).1 hn
  calc
    F (a * b * n) = F (a * (b * n)) := by rw [mul_assoc]
    _ ≤ minimalMajorant F a * F (b * n) :=
      hF.le_minimalMajorant_mul hA hB a (b * n) ((coprime_mul_right a b n).2 ⟨hab, han⟩)
    _ ≤ minimalMajorant F a * (minimalMajorant F b * F n) :=
      mul_le_mul_of_nonneg_left (hF.le_minimalMajorant_mul hA hB b n hbn)
        (hF.minimalMajorant_nonneg hA hB a)
    _ = (minimalMajorant F a * minimalMajorant F b) * F n := by ring

/-- The assertion `G_F ∈ 𝓜ₖ(A,B,ε)` following (13). -/
theorem Admissible.minimalMajorant_admissible {k : ℕ} {A B ε : ℝ}
    {F : ArithmeticMap k} (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Admissible A B ε (minimalMajorant F) := by
  refine ⟨hF.minimalMajorant_nonneg hA hB, fun m n hmn => ?_⟩
  exact (hF.minimalMajorant_submultiplicative hA hB m n hmn).trans
    (mul_le_mul_of_nonneg_right (hF.minimalMajorant_le hA hB m)
      (hF.minimalMajorant_nonneg hA hB n))

end NairTenenbaum

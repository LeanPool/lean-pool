/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.ComparisonUniformity
public import LeanPool.NairTenenbaum.Smooth.TotientSmoothTail

/-! # Degree and discriminant uniformity of the smooth-tail constants

There are finitely many possible exponent totals and root bounds at a fixed
total degree and restricted discriminant. A finite envelope of the explicit
constants removes dependence on the individual factorization data. This does
not require monotonicity of the auxiliary cutoff chosen by absorption.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Represent a list of coordinate totals by a one-row exponent matrix. -/
def exponentRow {r : ℕ} (η : Fin r → ℕ) : Fin 1 → Fin r → ℕ := fun _ => η

@[simp] theorem totalExponent_exponentRow {r : ℕ} (η : Fin r → ℕ) (i : Fin r) :
    totalExponent (exponentRow η) i = η i := by simp [totalExponent, exponentRow]

theorem rootSmoothTailBound_congr_totals {k₁ k₂ r : ℕ} (A B κ : ℝ)
    (γ₁ : Fin k₁ → Fin r → ℕ) (γ₂ : Fin k₂ → Fin r → ℕ)
    (hγ : ∀ i, totalExponent γ₁ i = totalExponent γ₂ i) (C : Fin r → ℕ) (G : ℕ) :
    rootSmoothTailBound A B κ γ₁ C G = rootSmoothTailBound A B κ γ₂ C G := by
  simp only [rootSmoothTailBound, smoothTruncationBound, smoothTruncationThreshold,
    smoothTruncationScale, hγ]

theorem totientSmoothTailBound_congr_totals {k₁ k₂ r : ℕ} (A B κ : ℝ)
    (γ₁ : Fin k₁ → Fin r → ℕ) (γ₂ : Fin k₂ → Fin r → ℕ)
    (hγ : ∀ i, totalExponent γ₁ i = totalExponent γ₂ i) (C : Fin r → ℕ) (G g : ℕ) :
    totientSmoothTailBound A B κ γ₁ C G g = totientSmoothTailBound A B κ γ₂ C G g := by
  rw [totientSmoothTailBound, rootSmoothTailBound_congr_totals A B κ γ₁ γ₂ hγ]
  rfl

/-- A finite envelope depending only on degree and restricted discriminant.
The deliberately non-sharp constant simultaneously covers the root vector and
the totient-modified root vector with exponent equal to total degree. -/
noncomputable def smoothTailUniformBound (A B κ : ℝ) (g D : ℕ) : ℝ :=
  1 + ∑ r ∈ Finset.range (g + 1),
    ∑ η ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (g + 1)),
      ∑ C ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (max g (D ^ 3) + 1)),
        (|rootSmoothTailBound A B κ (exponentRow η) C g| +
          |totientSmoothTailBound A B κ (exponentRow η) C g g|)

theorem smoothTailUniformBound_pos (A B κ : ℝ) (g D : ℕ) : 0 < smoothTailUniformBound A B κ g D :=
    by
  apply add_pos_of_pos_of_nonneg zero_lt_one
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))))

/-- Every allowed tuple of factorization data occurs in the finite envelope. -/
theorem smoothTailBounds_le_uniform {k r : ℕ} (A B κ : ℝ) (g D : ℕ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) (hr : r ≤ g)
    (hγ : ∀ i, totalExponent γ i ≤ g) (hC : ∀ i, C i ≤ max g (D ^ 3)) :
    rootSmoothTailBound A B κ γ C g ≤ smoothTailUniformBound A B κ g D ∧
      totientSmoothTailBound A B κ γ C g g ≤ smoothTailUniformBound A B κ g D := by
  classical
  let η := totalExponent γ
  have hη : η ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (g + 1)) :=
    Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (Nat.lt_succ_of_le (hγ i)))
  have hCm : C ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (max g (D ^ 3) + 1)) :=
    Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (Nat.lt_succ_of_le (hC i)))
  have heq : ∀ i, totalExponent γ i = totalExponent (exponentRow η) i := by
    intro i
    simp only [totalExponent_exponentRow, η]
  have H : |rootSmoothTailBound A B κ (exponentRow η) C g| +
      |totientSmoothTailBound A B κ (exponentRow η) C g g| ≤ smoothTailUniformBound A B κ g D := by
    calc
      _ ≤ ∑ C' ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (max g (D ^ 3) + 1)),
          (|rootSmoothTailBound A B κ (exponentRow η) C' g| +
            |totientSmoothTailBound A B κ (exponentRow η) C' g g|) :=
        Finset.single_le_sum (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hCm
      _ ≤ ∑ η' ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (g + 1)),
          ∑ C' ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (max g (D ^ 3) + 1)),
            (|rootSmoothTailBound A B κ (exponentRow η') C' g| +
              |totientSmoothTailBound A B κ (exponentRow η') C' g g|) :=
        Finset.single_le_sum
          (f := fun η' : Fin r → ℕ =>
            ∑ C' ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (max g (D ^ 3) + 1)),
              (|rootSmoothTailBound A B κ (exponentRow η') C' g| +
                |totientSmoothTailBound A B κ (exponentRow η') C' g g|))
          (fun _ _ => Finset.sum_nonneg
            (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))) hη
      _ ≤ ∑ r' ∈ Finset.range (g + 1),
          ∑ η' ∈ Fintype.piFinset (fun _ : Fin r' => Finset.range (g + 1)),
            ∑ C' ∈ Fintype.piFinset (fun _ : Fin r' => Finset.range (max g (D ^ 3) + 1)),
              (|rootSmoothTailBound A B κ (exponentRow η') C' g| +
                |totientSmoothTailBound A B κ (exponentRow η') C' g g|) :=
        Finset.single_le_sum
          (f := fun r' : ℕ =>
            ∑ η' ∈ Fintype.piFinset (fun _ : Fin r' => Finset.range (g + 1)),
              ∑ C' ∈ Fintype.piFinset (fun _ : Fin r' => Finset.range (max g (D ^ 3) + 1)),
                (|rootSmoothTailBound A B κ (exponentRow η') C' g| +
                  |totientSmoothTailBound A B κ (exponentRow η') C' g g|))
          (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
            (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
      _ ≤ _ := le_add_of_nonneg_left zero_le_one
  rw [rootSmoothTailBound_congr_totals A B κ γ (exponentRow η) heq,
    totientSmoothTailBound_congr_totals A B κ γ (exponentRow η) heq]
  exact ⟨(le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans H),
    (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans H)⟩

/-- Root-vector smooth tail with a constant depending only on total degree
and restricted discriminant among the polynomial data. -/
theorem PolynomialSystem.root_smooth_tail_uniform {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z x : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then P.weight F m else 0
    Summable f ∧ (∑' m, f m) ≤
      smoothTailUniformBound A B κ P.total.natDegree P.badDiscriminant *
        Real.exp (-κ * Real.log x / Real.log z) * ∑ m ∈ positiveUpTo z, P.weight F m := by
  have H := P.root_smooth_tail hF hA hB hε hκ hz hx hzκ (fun i =>
    (mul_le_mul_of_nonneg_right (by exact_mod_cast P.totalExponent_le_degree i) hε.le).trans hgε)
  refine ⟨H.1, H.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (smoothTailBounds_le_uniform A B κ P.total.natDegree P.badDiscriminant P.exponent
    (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3)) P.factor_count_le_degree
    P.totalExponent_le_degree (fun i => max_le_max
      (Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero) le_rfl)).1

/-- The totient-modified smooth tail with the exact uniformity required in
the main theorem. Its right-hand weight is the original root vector. -/
theorem PolynomialSystem.totient_smooth_tail_uniform {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z x : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then NairTenenbaum.weight P.exponent P.discriminant F
        (fun i m => P.rootVector i m * totientTwist P.total.natDegree m) m else 0
    Summable f ∧ (∑' m, f m) ≤
      smoothTailUniformBound A B κ P.total.natDegree P.badDiscriminant *
        Real.exp (-κ * Real.log x / Real.log z) * ∑ m ∈ positiveUpTo z, P.weight F m := by
  have H := P.totient_smooth_tail hF hA hB hε hκ hz hx hzκ (fun i =>
    (mul_le_mul_of_nonneg_right (by exact_mod_cast P.totalExponent_le_degree i) hε.le).trans hgε)
    P.total.natDegree
  refine ⟨H.1, H.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (smoothTailBounds_le_uniform A B κ P.total.natDegree P.badDiscriminant P.exponent
    (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3)) P.factor_count_le_degree
    P.totalExponent_le_degree (fun i => max_le_max
      (Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero) le_rfl)).2

/-- Theorem 1's admissibility exponent satisfies the fixed small-exponent
condition needed by the smooth-tail argument. -/
theorem smooth_exponent_of_theoremOne {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 < ε) (hεg : ε < 1 / (8 * (g : ℝ) ^ 2)) (hδ : δ ≤ 1) :
    (g : ℝ) * (ε * δ / 3) ≤ 1 / 8 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hc : ε * (8 * (g : ℝ) ^ 2) < 1 :=
    (lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (g : ℝ) ^ 2)).mp hεg
  have hgg : (g : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hgg hε.le
  have hδ' : ε * δ / 3 ≤ ε := by nlinarith
  have H := mul_le_mul_of_nonneg_left hδ' (by positivity : (0 : ℝ) ≤ g)
  nlinarith

/-- The totient smooth tail can be used directly with Theorem 1's parameters,
without any additional local growth or root-count assumptions. -/
theorem PolynomialSystem.totient_smooth_tail_theoremOne_parameters {k r : ℕ} (P : PolynomialSystem
    k r)
    {A B ε δ κ z x : ℝ} {F : ArithmeticMap k} (hF : Admissible A B (ε * δ / 3) F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hg : 0 < P.total.natDegree) (hε : 0 < ε)
    (hεg : ε < 1 / (8 * (P.total.natDegree : ℝ) ^ 2)) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then NairTenenbaum.weight P.exponent P.discriminant F
        (fun i m => P.rootVector i m * totientTwist P.total.natDegree m) m else 0
    Summable f ∧ (∑' m, f m) ≤
      smoothTailUniformBound A B κ P.total.natDegree P.badDiscriminant *
        Real.exp (-κ * Real.log x / Real.log z) * ∑ m ∈ positiveUpTo z, P.weight F m :=
  P.totient_smooth_tail_uniform hF hA hB (by positivity) hκ hz hx hzκ
    (smooth_exponent_of_theoremOne hg hε hεg hδ₁)

end NairTenenbaum

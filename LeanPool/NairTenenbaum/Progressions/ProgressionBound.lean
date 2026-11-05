/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.IntegerIntervalBound
public import LeanPool.NairTenenbaum.Progressions.ProgressionIntervals

/-! # Uniform bounds in arithmetic progressions

The affine family is estimated at the original scale `x`, using the original
polynomial values. The bounded-scale estimate keeps the height threshold
independent of the progression-length parameter `β`.
-/

@[expose] public section

namespace NairTenenbaum

/-- The modulus restriction leaves enough transformed interval length for
the exponent `εβ`. -/
theorem progression_length_lower {g q : ℕ} {ε β x y : ℝ}
    (hq : 0 < q) (hx : 0 < x) (hβ : 0 ≤ β)
    (hy : x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y) (hqty : (q : ℝ) ≤ y ^ (1 - β)) :
    x ^ (4 * (g : ℝ) ^ 2 * (ε * β)) ≤ y / q := by
  have hy₀ : 0 < y := (Real.rpow_pos_of_pos hx _).trans_le hy
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ = (x ^ (4 * (g : ℝ) ^ 2 * ε)) ^ β := by
      rw [← Real.rpow_mul hx.le]
      congr 1
      ring
    _ ≤ y ^ β := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hy hβ
    _ = y / y ^ (1 - β) := by
      apply (eq_div_iff (Real.rpow_pos_of_pos hy₀ _).ne').mpr
      rw [← Real.rpow_add hy₀, add_sub_cancel, Real.rpow_one]
    _ ≤ y / q := div_le_div_of_nonneg_left hy₀.le hq₀ hqty

/-- The explicit value exponent and arithmetic growth satisfy the uniform
interval theorem's saving margin. -/
theorem progression_growth_margin {g : ℕ} (hg : 0 < g) {ε β δ : ℝ}
    (hε : 0 ≤ ε) (hβ : 0 ≤ β) (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) :
    ((g : ℝ) + 1 / (2 * δ) + 1) * (ε * β * δ / 6) ≤ (g : ℝ) * (ε * β) / 2 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have heq : ((g : ℝ) + 1 / (2 * δ) + 1) * (ε * β * δ / 6) =
      ((g : ℝ) * δ + 1 / 2 + δ) * (ε * β) / 6 := by field_simp
  rw [heq]
  have H : (g : ℝ) * δ ≤ (g : ℝ) / 2 := by nlinarith
  have H' : (g : ℝ) * δ + 1 / 2 + δ ≤ 3 * (g : ℝ) := by linarith
  have H'' := mul_le_mul_of_nonneg_right H' (mul_nonneg hε hβ)
  nlinarith

/-- Values in the transformed interval retain the original height bound. -/
theorem PolynomialSystem.affine_interval_value_bound {k r g : ℕ} (P : PolynomialSystem k r)
    (hdeg : P.total.natDegree = g) (q a : ℕ) (hq : 0 < q)
    (hqa : q.Coprime (P.total.eval (a : ℤ)).natAbs) {x y δ : ℝ}
    (hx : 1 ≤ x) (hyx : y ≤ x) (hδ : 0 < δ)
    (hheight : (polynomialHeight P.total : ℝ) ^ (2 * δ) ≤ x)
    (hlarge : ((g : ℝ) + 1) * 2 ^ g ≤ x) :
    ∀ t ∈ Finset.Ioc ⌊(x - a) / q⌋ ⌊(x + y - a) / q⌋,
      (((P.affine q a hq.ne' hqa).total.eval t).natAbs : ℝ) ≤
        x ^ ((g : ℝ) + 1 / (2 * δ) + 1) := by
  intro t ht
  have ht' := (mem_affine_interval_iff hq (a : ℤ) x y t).mp ht
  simp only [Int.cast_natCast] at ht'
  rw [P.affine_total, Polynomial.eval_comp, eval_affinePolynomial]
  apply eval_natAbs_le_rpow_of_height hdeg hx (by positivity : 0 < 2 * δ) hheight hlarge
  have hn : (0 : ℤ) ≤ (q : ℤ) * t + a := by
    have H : (0 : ℝ) ≤ (q : ℝ) * t + a := by linarith [ht'.1]
    exact_mod_cast H
  have heq : (((q : ℤ) * t + a).natAbs : ℝ) = ((q : ℤ) * t + a : ℤ) := by
    have H : (((q : ℤ) * t + a).natAbs : ℤ) = (q : ℤ) * t + a := by
      rw [Int.natCast_natAbs, abs_of_nonneg hn]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) H
  rw [heq]
  push_cast
  linarith [ht'.2]

/-- Corollary 1 with constants uniform also in the number of factors. The
height threshold is chosen before `β`; the bound constant may depend on it. -/
theorem exists_progressionSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ β : ℝ, 0 < β → β < 1 →
      ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
        ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * β * δ / 6) F →
        ∀ (q a : ℕ), 0 < q → q.Coprime (P.total.eval (a : ℤ)).natAbs →
        ∀ (x y : ℝ), c₁ * (polynomialHeight P.total : ℝ) ^ (2 * δ) < x →
          x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x → (q : ℝ) ≤ y ^ (1 - β) →
          progressionSum P.Q F q a x y ≤ C P.badDiscriminant * progressionMainTerm P F q x y := by
  let c₁ : ℝ := max 2 (((g : ℝ) + 1) * 2 ^ g)
  have hc₁ : 2 ≤ c₁ := le_max_left _ _
  refine ⟨c₁, by linarith, ?_⟩
  intro β hβ hβ₁
  let σ := ε * β * δ / 6
  let c := (g : ℝ) + 1 / (2 * δ) + 1
  have hepsB : 0 < ε * β := mul_pos hε hβ
  have hepsBsmall : (g : ℝ) ^ 2 * (ε * β) ≤ 1 / 8 := by
    have H := mul_le_of_le_one_right hε.le hβ₁.le
    exact (mul_le_mul_of_nonneg_left H (sq_nonneg _)).trans hsmall
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσepsB : σ ≤ ε * β := by dsimp [σ]; nlinarith
  have hσsmall : (g : ℝ) ^ 2 * σ ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hσepsB (sq_nonneg _)).trans hepsBsmall
  obtain ⟨C, hC, H⟩ := exists_integerSum_mainTerm_bound_all_scales hg hA hB hepsB hepsBsmall hσ
      hσsmall
    (by dsimp [c]; positivity : 0 ≤ c) (by
      have H := progression_growth_margin hg hε.le hβ.le hδ hδ₁
      have hgε : 0 ≤ (g : ℝ) * (ε * β) := mul_nonneg (Nat.cast_nonneg _) hepsB.le
      dsimp only [c, σ]
      linarith)
  let E : ℕ → ℝ := fun D => 1 + ∑ d ∈ Finset.range (D + 1), max 0 (C d)
  have hE (D : ℕ) : 0 < E D := by dsimp [E]; positivity
  have hCE {d D : ℕ} (hd : d ≤ D) : C d ≤ E D := by
    have Hsum := Finset.single_le_sum (s := Finset.range (D + 1))
      (f := fun e => max 0 (C e)) (fun e _ => le_max_left _ _) (Finset.mem_range.mpr (by
        omega : d < D + 1))
    exact (le_max_right 0 (C d)).trans (Hsum.trans (by dsimp [E]; linarith))
  refine ⟨E, hE, ?_⟩
  intro k r P hdeg F hF q a hq hqa x y hx hy hyx hqty
  have hH : (1 : ℝ) ≤ (polynomialHeight P.total : ℝ) := one_le_polynomialHeight P.total_ne_zero
  have hHδ : 1 ≤ (polynomialHeight P.total : ℝ) ^ (2 * δ) := Real.one_le_rpow hH (by positivity)
  have hcx : c₁ ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ c₁) hHδ).trans hx.le
  have hx₂ : 2 ≤ x := hc₁.trans hcx
  have hx₁ : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hheight : (polynomialHeight P.total : ℝ) ^ (2 * δ) ≤ x :=
    (le_mul_of_one_le_left (zero_le_one.trans hHδ) (by linarith : 1 ≤ c₁)).trans hx.le
  have hlarge : ((g : ℝ) + 1) * 2 ^ g ≤ x := (le_max_right _ _).trans hcx
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos _).trans_le hy
  have hlength := progression_length_lower hq hxpos hβ.le hy hqty
  have hyq : 1 ≤ y / q := (Real.one_le_rpow hx₁ (by
    positivity : 0 ≤ 4 * (g : ℝ) ^ 2 * (ε * β))).trans hlength
  obtain ⟨hab, hlen, hlen'⟩ := affine_interval_endpoint_bounds hq (a : ℤ) hypos.le hyq
  have Haffine := H k r (P.affine q a hq.ne' hqa) ((P.affine_degree q a hq.ne' hqa).trans hdeg)
    F hF x (y / q) _ _ hx₂ hlength hab hlen hlen'
    (P.affine_interval_value_bound hdeg q a hq hqa hx₁ hyx hδ hheight hlarge)
  rw [P.affine_mainTerm] at Haffine
  have HM : 0 ≤ progressionMainTerm P F q x y := by
    rw [← P.affine_mainTerm q (a : ℤ) hq.ne' hqa F x y]
    exact mainTerm_nonneg _ hF.nonneg x (by linarith : 0 ≤ y / q)
  have hD : (P.affine q a hq.ne' hqa).badDiscriminant ≤ P.badDiscriminant :=
    Nat.le_of_dvd P.badDiscriminant_pos (P.affine_badDiscriminant_dvd q a hq.ne' hqa)
  exact (P.progressionSum_le_affine_integerSum hF.nonneg q a hq hqa (by linarith)).trans
    (Haffine.trans (mul_le_mul_of_nonneg_right (hCE hD) HM))

end NairTenenbaum

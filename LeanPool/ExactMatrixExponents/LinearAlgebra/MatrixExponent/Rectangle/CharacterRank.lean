/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Support
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.DotsPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.FlatteningOrder
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.RectangularRank

/-!
# From the character estimate to rectangular algorithms

Each pairing belongs to the two legs other than its named leg. Reading
the first two legs as inputs and the third as output gives a rank bound
on the formal product. Ceiling costs at most a factor of two per pairing.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle
open Upper Upper.TensorClass

private abbrev dots := TensorSpectrum.TensorClass.dots (K := Coeff)

private theorem dots_power (i j k t : ℕ) :
    dots (i ^ t) (j ^ t) (k ^ t) = (dots i j k) ^ t :=
  TensorSpectrum.TensorClass.dots_power i j k t

private theorem rank_of_dots {i j k r : ℕ} (h : dots i j k ≤ (r : TensorClass)) :
    RankLE Coeff i j k r :=
  TensorSpectrum.TensorClass.rank_of_dots h

private theorem price_dots (f : Character) {n : ℕ} (hn : 0 < n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (f (dots (side n a) (side n b) (side n c)) : ℝ) ≤
      8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) :=
  TensorSpectrum.TensorClass.price_dots f hn ha hb hc

theorem exponent_le_of_characters {a b c s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : ∀ f : Character, b * f.pX + a * f.pY + c * f.pZ ≤ s) :
    exponent Coeff a b c ≤ s := by
  refine exponent_le_of_rank_powers ha hb hc hs ?_
  intro n r hn hlo hr
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hne : (r : TensorClass) ≠ 0 := by
    intro he
    have he' := (rank_eq_zero_iff _).mpr he
    rw [rank_natCast] at he'
    exact hr.ne' (by exact_mod_cast he')
  let M := dots (side n a) (side n b) (side n c)
  have hp (g : TensorClass →+* NNReal) (hg : Monotone g) : g M < g (r : TensorClass) := by
    let f : Character := ⟨g, hg⟩
    rw [map_natCast]
    apply NNReal.coe_lt_coe.mp
    calc
      (g M : ℝ) ≤ 8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) :=
        price_dots f (by omega) ha hb hc
      _ ≤ 8 * (n : ℝ) ^ s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn₁ (h f)) (by norm_num)
      _ < (r : ℝ) := hlo
  obtain ⟨C, hC⟩ := Spectrum.strictComparison
    (fun _ _ _ h => add_mono h le_rfl) (fun _ _ _ h => mul_mono le_rfl h)
    TensorClass.zero_le (fun _ => one_le_of_ne_zero) (fun A => ⟨rank A, le_rank_natCast A⟩) hne hp
  refine ⟨C, fun p => rank_of_dots ?_⟩
  rw [dots_power, Nat.cast_mul, Nat.cast_pow, mul_comm]
  exact hC p

theorem coeff_discrete
    (h : ∀ (f : Character) (A B C : ℕ), 0 < A → 0 < B → 0 < C →
      4 * (f.pX * B * C + f.pY * A * C + f.pZ * A * B) ≤ ((A : ℝ) + B + C) ^ 2) :
    DiscreteBound Coeff := by
  intro A B C hA hB hC
  apply exponent_le_of_characters (by positivity) (by positivity) (by positivity) (by positivity)
  intro f
  linarith only [h f B C A hB hC hA]

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle

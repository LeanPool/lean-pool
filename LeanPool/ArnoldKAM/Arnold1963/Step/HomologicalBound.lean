/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Homological
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierKernel

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set Complex
open scoped NNReal
namespace KamProject.Arnold1963

/-- The uniform norm bound for the finite homological generating function. -/
def homologicalBound (n : ℕ) (M K δ : ℝ) : ℝ :=
  M * constantL5 n / (K * δ ^ homologicalExponent n)

theorem constantL0_pos (n : ℕ) : 0 < constantL0 n := by
  unfold constantL0
  positivity

theorem constantL5_pos (n : ℕ) : 0 < constantL5 n :=
  mul_pos (by positivity) (constantL0_pos n)

theorem nat_pow_exp_bound {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (n : ℕ) :
    x ^ (n + 1) * Real.exp (-(x * δ)) ≤ constantL0 n / δ ^ (n + 1) := by
  have h := rpow_mul_exp_neg_mul_le hx
    (show (0 : ℝ) < (n + 1 : ℕ) by positivity) hδ
  rw [Real.rpow_neg hδ.le, Real.rpow_natCast, Real.rpow_natCast,
    Real.rpow_natCast] at h
  simpa only [constantL0, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using h

variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
  (f : AnalyticPhaseFunction n G ρ) {ω : ComplexSpace n → ComplexSpace n}
  {M K N δ : ℝ}

theorem norm_homologicalCoeff_le {p : ComplexSpace n} (hp : p ∈ G)
    (hM : f.uniformNorm ≤ M) (hK : 0 < K) (hnr : FiniteNonresonant (ω p) K N)
    {k : FourierIndex n} (hk : k ∈ lowModes n N) :
    ‖homologicalCoeff f ω p k‖ ≤
      M / K * indexLength k ^ (n + 1) * Real.exp (-(indexLength k * ρ)) := by
  have hM0 := (f.norm_le_iff.mp le_rfl).nonneg.trans hM
  have hpow : 0 < indexLength k ^ (n + 1) := pow_pos (mem_lowModes.mp hk).1 _
  have hf := (f.norm_fourierCoeff_le_exp hp k).trans
    (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)
  rw [homologicalCoeff, norm_div, norm_mul, norm_I, one_mul]
  calc
    _ ≤ (M * Real.exp (-(indexLength k * ρ))) / ‖indexPairing k (ω p)‖ :=
      div_le_div_of_nonneg_right hf (norm_nonneg _)
    _ ≤ (M * Real.exp (-(indexLength k * ρ))) / (K / indexLength k ^ (n + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hK hpow) (hnr k hk)
    _ = _ := by field_simp

theorem norm_homologicalTerm_le {p q : ComplexSpace n} (hp : p ∈ G)
    (hM : f.uniformNorm ≤ M) (hK : 0 < K) (hδ : 0 < δ)
    (hnr : FiniteNonresonant (ω p) K N) (hq : ‖imagPart q‖ ≤ (ρ : ℝ) - (δ + δ))
    {k : FourierIndex n} (hk : k ∈ lowModes n N) :
    ‖homologicalCoeff f ω p k * fourierMonomial k q‖ ≤
      (M / K * (constantL0 n / δ ^ (n + 1))) * Real.exp (-δ * indexLength k) := by
  have hM0 := (f.norm_le_iff.mp le_rfl).nonneg.trans hM
  have hlen := (mem_lowModes.mp hk).1
  rw [norm_mul]
  calc
    _ ≤ (M / K * indexLength k ^ (n + 1) * Real.exp (-(indexLength k * ρ))) *
        Real.exp (indexLength k * ‖imagPart q‖) :=
      mul_le_mul (norm_homologicalCoeff_le f hp hM hK hnr hk)
        (norm_fourierMonomial_le k q) (norm_nonneg _) (by positivity)
    _ = M / K * indexLength k ^ (n + 1) *
        Real.exp (-(indexLength k * ρ) + indexLength k * ‖imagPart q‖) := by
      rw [mul_assoc, ← Real.exp_add]
    _ ≤ M / K * indexLength k ^ (n + 1) * Real.exp (-(indexLength k * δ) - δ * indexLength k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hq hlen.le]
    _ = M / K * (indexLength k ^ (n + 1) * Real.exp (-(indexLength k * δ))) *
        Real.exp (-δ * indexLength k) := by
      rw [show -(indexLength k * δ) - δ * indexLength k =
        -(indexLength k * δ) + (-δ * indexLength k) by ring, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (nat_pow_exp_bound hlen hδ n) (by positivity))
      (Real.exp_pos _).le

theorem norm_homologicalGenerator_le {p q : ComplexSpace n} (hp : p ∈ G)
    (hM : f.uniformNorm ≤ M) (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hnr : FiniteNonresonant (ω p) K N) (hq : ‖imagPart q‖ ≤ (ρ : ℝ) - (δ + δ)) :
    ‖homologicalGenerator f ω N (p, q)‖ ≤ homologicalBound n M K δ := by
  have hM0 := (f.norm_le_iff.mp le_rfl).nonneg.trans hM
  let C := M / K * (constantL0 n / δ ^ (n + 1))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg hM0 hK.le)
      (div_nonneg (constantL0_pos n).le (pow_nonneg hδ.le _))
  calc
    _ ≤ ∑ k ∈ lowModes n N, ‖homologicalCoeff f ω p k * fourierMonomial k q‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ lowModes n N, C * Real.exp (-δ * indexLength k) :=
      Finset.sum_le_sum fun k hk => norm_homologicalTerm_le f hp hM hK hδ hnr hq hk
    _ = C * ∑ k ∈ lowModes n N, Real.exp (-δ * indexLength k) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (4 / δ) ^ n := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact ((summable_exp_indexLength n hδ).sum_le_tsum (lowModes n N)
        (fun _ _ => (Real.exp_pos _).le)).trans (tsum_exp_indexLength_le n hδ hδ1)
    _ = _ := by
      dsimp [C, homologicalBound, constantL5, homologicalExponent]
      rw [div_pow]
      have he : δ ^ (2 * n + 1) = δ ^ (n + 1) * δ ^ n := by
        rw [← pow_add]; congr 1; omega
      rw [he]
      field_simp

end KamProject.Arnold1963

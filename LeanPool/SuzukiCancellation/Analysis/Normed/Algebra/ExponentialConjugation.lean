/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.RealScalar
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Commutator
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialCalculus
public import LeanPool.SuzukiCancellation.Analysis.SpecialFunctions.Integrals.IteratedBounds

/-!
# Single-layer conjugation

Single-layer conjugation results for the Trotter error theory (arXiv:1912.08854): the Taylor
expansion and norm bounds of the single conjugation `exp (τ • A) * X * exp (-τ • A)`
(theory.tex:137-155), before the multi-layer induction.

## Main definitions

* `expSMulConj`: the single conjugation `e^{τA} X e^{-τA} = exp (τ • A) * X * exp ((-τ) • A)`.

## Main results

* `expSMulConj_hasDerivAt`: `d/dτ expSMulConj A X τ = expSMulConj A ⁅A, X⁆ τ`.
* `expSMulConj_sub_eq_integral`: the fundamental-theorem identity
  `expSMulConj A X τ - X = ∫₀^τ expSMulConj A ⁅A, X⁆ s ds`.
* `iteratedDeriv_expSMulConj_zero`: `iteratedDeriv j (expSMulConj A X) 0 = adPow A j X`.
* `expSMulConj_taylor`: the single-layer Taylor expansion with integral remainder.
* `isometry_expSMulConj_of_le_one`: conjugation preserves distances under two-sided
  exponential contraction bounds.
* `norm_list_exp_conj_eq_of_le_one`: an ordered list of such conjugations preserves the norm.
* `norm_expSMulConj_le`, `norm_expSMulConj_remainder_le`: norm bounds for the conjugation
  and its remainder (theory.tex:151-155).
* `norm_expSMulConj_eq_of_skewAdjoint`: the conjugation preserves the norm when the
  generator is anti-Hermitian (the exponential factors are unitary).
-/

@[expose] public section

open scoped RealScalar

namespace TrotterError

open NormedSpace MeasureTheory
open scoped ContDiff algebraMap

/-- Single conjugation `e^{τA} X e^{-τA} = exp (τ • A) * X * exp ((-τ) • A)`. -/
noncomputable def expSMulConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (τ : ℝ) : 𝔸 :=
  exp (τ • A) * X * exp ((-τ) • A)

/-- The conjugation `t ↦ expSMulConj A Y t` is smooth. -/
lemma contDiff_expSMulConj {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A Y : 𝔸) :
    ContDiff ℝ ∞ (fun t : ℝ => expSMulConj A Y t) := by
  unfold expSMulConj
  exact ((contDiff_exp_smul_const A).mul contDiff_const).mul
    ((contDiff_exp_smul_const A).comp contDiff_neg)

/-- The conjugation `t ↦ expSMulConj A Y t` is continuous. -/
@[fun_prop]
lemma continuous_expSMulConj {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A Y : 𝔸) :
    Continuous (fun t : ℝ => expSMulConj A Y t) :=
  (contDiff_expSMulConj A Y).continuous

/-- Derivative of the conjugation:
`d/dτ expSMulConj A X τ = expSMulConj A ⁅A, X⁆ τ`
(i.e. `e^{τA} [A, X] e^{-τA}`). -/
theorem expSMulConj_hasDerivAt {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (τ : ℝ) :
    HasDerivAt (fun s => expSMulConj A X s) (expSMulConj A ⁅A, X⁆ τ) τ := by
  have hneg : HasDerivAt (fun s : ℝ => exp ((-s) • A)) (-A * exp ((-τ) • A)) τ := by
    have h := hasDerivAt_exp_smul_const' (-A) τ
    convert h using 2 <;> simp
  have hmain : HasDerivAt (fun s : ℝ => exp (s • A) * X * exp ((-s) • A))
      (exp (τ • A) * (A * X - X * A) * exp ((-τ) • A)) τ := by
    have h' : HasDerivAt (fun s : ℝ => exp (s • A) * X * exp ((-s) • A))
        (((A * exp (τ • A)) * X) * exp ((-τ) • A) +
          (exp (τ • A) * X) * (-A * exp ((-τ) • A))) τ :=
      (hasDerivAt_exp_smul_const' A τ).mul_const X |>.mul hneg
    convert h' using 1
    noncomm_ring [((Commute.refl A).smul_right τ).exp_right.eq,
      ((Commute.refl A).smul_right (-τ)).exp_right.eq]
  simpa [expSMulConj, Ring.lie_def] using hmain

/-- Fundamental theorem of calculus for the conjugation:
`expSMulConj A X τ - X = ∫ s in 0..τ, expSMulConj A ⁅A, X⁆ s`. -/
theorem expSMulConj_sub_eq_integral {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (τ : ℝ) :
    expSMulConj A X τ - X = ∫ s in 0..τ, expSMulConj A ⁅A, X⁆ s := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) τ,
      HasDerivAt (fun s => expSMulConj A X s) (expSMulConj A ⁅A, X⁆ x) x :=
    fun x _ => expSMulConj_hasDerivAt A X x
  have hint : IntervalIntegrable (fun s => expSMulConj A ⁅A, X⁆ s) volume 0 τ :=
    (continuous_expSMulConj A ⁅A, X⁆).intervalIntegrable 0 τ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => expSMulConj A X s) (f' := fun s => expSMulConj A ⁅A, X⁆ s)
    (a := 0) (b := τ) hderiv hint
  rw [h]; simp [expSMulConj]

/-- The `j`-th iterated derivative of `τ ↦ expSMulConj A X τ` is
`τ ↦ expSMulConj A (adPow A j X) τ`. -/
lemma iteratedDeriv_expSMulConj {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (j : ℕ) :
    iteratedDeriv j (fun τ => expSMulConj A X τ) = fun τ => expSMulConj A (adPow A j X) τ := by
  induction j with
  | zero => simp [iteratedDeriv_zero]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [(expSMulConj_hasDerivAt A (adPow A j X) t).deriv, ad_pow_succ]

/-- The `j`-th iterated derivative of `τ ↦ expSMulConj A X τ` at `0` is `adPow A j X`. -/
theorem iteratedDeriv_expSMulConj_zero {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (j : ℕ) :
    iteratedDeriv j (fun τ => expSMulConj A X τ) 0 = adPow A j X := by
  rw [iteratedDeriv_expSMulConj]; simp [expSMulConj]

/-- At `τ = 0`, the Taylor polynomial `∑_{j<p} (j! : ℝ)⁻¹ • (adPow A j X * 0^j)` equals `X`. -/
lemma taylor_poly_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (p : ℕ) (hp : 1 ≤ p) :
    (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X * (0 : 𝔸) ^ j)) = X := by
  simpa [adPow] using (Finset.sum_eq_single_of_mem (s := Finset.range p)
    (a := 0) (f := fun j => (Nat.factorial j : ℝ)⁻¹ • (adPow A j X * (0 : 𝔸) ^ j))
    (Finset.mem_range.mpr (lt_of_lt_of_le zero_lt_one hp))
    (by intro b _ hb0; rw [zero_pow hb0, mul_zero, smul_zero]))

/-- Single-layer Taylor expansion (theory.tex:137-150):
`expSMulConj A X τ = Σ_{j<p} adPow A j X τ^j/j! +
  ∫₀^τ expSMulConj A (adPow A p X) (τ-s) s^{p-1}/(p-1)!`. -/
theorem expSMulConj_taylor {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    expSMulConj A X τ =
      (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X) * (τ ^ j : 𝔸))
      + ∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) *
          ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) := by
  let f : ℝ → 𝔸 := fun s => expSMulConj A X s
  let Y : 𝔸 := adPow A p X
  have hf : ContDiff ℝ ∞ f := contDiff_expSMulConj A X
  by_cases hτ : τ = 0
  · subst τ
    simp only [expSMulConj, zero_smul, neg_zero, exp_zero, one_mul, mul_one,
      intervalIntegral.integral_same, add_zero, smul_mul_assoc, map_zero]
    exact (taylor_poly_zero A X p hp).symm
  · have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) τ) := uniqueDiffOn_uIcc (Ne.symm hτ)
    have hfOn : ContDiffOn ℝ p f (Set.uIcc (0 : ℝ) τ) :=
      (hf.contDiffOn.mono (Set.subset_univ _)).of_le (mod_cast le_top)
    have hTaylor := taylor_integral_remainder (f := f) (x₀ := 0) (x := τ) (n := p - 1)
      (by simpa [Nat.sub_add_cancel hp] using hfOn)
    rw [Nat.sub_add_cancel hp] at hTaylor
    have hTaylor' : f τ = taylorWithinEval f (p - 1) (Set.uIcc (0 : ℝ) τ) 0 τ
        + ∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
            iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s := by
      rw [← hTaylor]
      abel
    have hpoly : taylorWithinEval f (p - 1) (Set.uIcc (0 : ℝ) τ) 0 τ
        = ∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X) * (τ ^ j : 𝔸) := by
      rw [taylor_within_apply, Nat.sub_add_cancel hp]
      simp only [sub_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le (mod_cast le_top))
        (by simp)]
      rw [iteratedDeriv_expSMulConj_zero, pow_smul_eq_smul_mul]
    have hintegral : (∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
          iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s) =
        ∫ s in 0..τ, expSMulConj A Y (τ - s) *
          ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) := by
      calc
        (∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
              iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s)
            = ∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
                iteratedDeriv p f s := by
                apply intervalIntegral.integral_congr_uIoo
                intro s hs
                change ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
                    iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s =
                  ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • iteratedDeriv p f s
                rw [iteratedDerivWithin_eq_iteratedDeriv hud
                  (hf.contDiffAt.of_le (mod_cast le_top)) (Set.uIoo_subset_uIcc_self hs)]
        _ = ∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
              expSMulConj A Y s := by
                apply intervalIntegral.integral_congr_uIoo
                intro s _
                change ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • iteratedDeriv p f s =
                  ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • expSMulConj A Y s
                rw [show iteratedDeriv p f s = expSMulConj A Y s by
                  simpa [f, Y] using congr_fun (iteratedDeriv_expSMulConj A X p) s]
        _ = ∫ s in 0..τ, expSMulConj A Y (τ - s) *
              ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) :=
                integral_smul_eq_integral_mul_sub (fun s => expSMulConj A Y s) (p - 1) τ
    change f τ = (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X) * (τ ^ j : 𝔸))
      + ∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) *
          ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)
    rw [hTaylor', hpoly, hintegral]

/-- The norm of a single conjugation is bounded by `‖Y‖ * exp (2 * |t| * ‖A‖)`. -/
theorem norm_expSMulConj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormOneClass 𝔸] (A Y : 𝔸) (t : ℝ) :
    ‖expSMulConj A Y t‖ ≤ ‖Y‖ * Real.exp (2 * |t| * ‖A‖) := by
  calc
    ‖exp (t • A) * Y * exp ((-t) • A)‖
        ≤ ‖exp (t • A)‖ * ‖Y‖ * ‖exp ((-t) • A)‖ :=
            (norm_mul_le (exp (t • A) * Y) (exp ((-t) • A))).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le (exp (t • A)) Y) (norm_nonneg _))
    _ ≤ Real.exp (|t| * ‖A‖) * ‖Y‖ * Real.exp (|t| * ‖A‖) := by
            have h1 : ‖exp (t • A)‖ ≤ Real.exp (|t| * ‖A‖) := by
              simpa [norm_smul] using FQFP.norm_exp_le (t • A)
            have h2 : ‖exp ((-t) • A)‖ ≤ Real.exp (|t| * ‖A‖) := by
              simpa [norm_smul] using FQFP.norm_exp_le ((-t) • A)
            exact mul_le_mul (mul_le_mul h1 (le_refl ‖Y‖) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
    _ = ‖Y‖ * Real.exp (2 * |t| * ‖A‖) := by
            calc
              Real.exp (|t| * ‖A‖) * ‖Y‖ * Real.exp (|t| * ‖A‖)
                  = ‖Y‖ * (Real.exp (|t| * ‖A‖) * Real.exp (|t| * ‖A‖)) := by ring
              _ = ‖Y‖ * Real.exp (|t| * ‖A‖ + |t| * ‖A‖) := by rw [Real.exp_add]
              _ = ‖Y‖ * Real.exp (2 * |t| * ‖A‖) := by ring_nf

/-- Conjugation by the exponential of a skew-adjoint element preserves the norm. -/
lemma norm_expSMulConj_eq_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [StarModule ℝ 𝔸]
    (A X : 𝔸) (hskew : star A = -A) (u : ℝ) :
    ‖expSMulConj A X u‖ = ‖X‖ := by
  unfold expSMulConj
  rw [CStarRing.norm_mul_mem_unitary _ (exp_smul_mem_unitary_of_skewAdjoint hskew (-u)),
    CStarRing.norm_mem_unitary_mul _ (exp_smul_mem_unitary_of_skewAdjoint hskew u)]

/-- Norm bound of the single-layer remainder (theory.tex:151-155):
`‖∫₀^τ expSMulConj A (adPow A p X) (τ-s) * s^{p-1}/(p-1)!‖ ≤
  ‖adPow A p X‖ * |τ|^p/p! * e^{2|τ|‖A‖}`. -/
theorem norm_expSMulConj_remainder_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (A X : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    ‖∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) *
        ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
      ≤ ‖adPow A p X‖ * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ‖A‖) := by
  let Y : 𝔸 := adPow A p X
  let C : ℝ := ‖Y‖ * Real.exp (2 * |τ| * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg Y) (Real.exp_nonneg _)
  have hpoint : ∀ s ∈ Set.uIoc (0 : ℝ) τ,
      ‖expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
        ≤ C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) := by
    intro s hs
    have habs : |τ - s| ≤ |τ| :=
      (by simpa [sub_zero] using Set.abs_sub_right_of_mem_uIcc (Set.uIoc_subset_uIcc hs))
    have hsmul : expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) =
        (s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • expSMulConj A Y (τ - s) :=
      (smul_eq_mul_right (s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) (expSMulConj A Y (τ - s))).symm
    have hnormY : ‖expSMulConj A Y (τ - s)‖ ≤ ‖Y‖ * Real.exp (2 * |τ| * ‖A‖) := by
      refine (norm_expSMulConj_le A Y (τ - s)).trans ?_
      have harg : 2 * |τ - s| * ‖A‖ ≤ 2 * |τ| * ‖A‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs (by norm_num)) (norm_nonneg A)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (norm_nonneg Y)
    calc
      ‖expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
          = ‖(s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • expSMulConj A Y (τ - s)‖ := by rw [hsmul]
      _ = |s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)| * ‖expSMulConj A Y (τ - s)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) * ‖expSMulConj A Y (τ - s)‖ := by
            rw [abs_div, abs_pow, abs_of_pos (by positivity : 0 < (Nat.factorial (p - 1) : ℝ))]
      _ ≤ (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) *
            (‖Y‖ * Real.exp (2 * |τ| * ‖A‖)) := by gcongr
      _ = C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) := by dsimp [C]; ring
  have hcont_g : Continuous (fun s : ℝ => C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))) := by
    fun_prop
  calc
    ‖∫ s in 0..τ, expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
        ≤ |∫ s in 0..τ, C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun s => expSMulConj A Y (τ - s) *
                ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸))
              (g := fun s => C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with s hs
              exact hpoint s hs
            · exact hcont_g.intervalIntegrable 0 τ
    _ = C * (|τ| ^ p / (Nat.factorial p : ℝ)) := by
            rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hC,
              abs_integral_abs_pow_div_factorial p τ hp]
    _ = ‖Y‖ * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ‖A‖) := by dsimp [C]; ring

/-- The single conjugation `expSMulConj A · τ` as an ℝ-linear endomorphism of `𝔸`. -/
noncomputable def expSMulConjLin {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸)
    (τ : ℝ) : 𝔸 →ₗ[ℝ] 𝔸 where
  toFun := fun X => expSMulConj A X τ
  map_add' _ _ := by unfold expSMulConj; noncomm_ring
  map_smul' _ _ := by simp [expSMulConj]

end TrotterError

namespace TrotterError

open NormedSpace

/-- A two-sided contraction bound for the exponential makes left multiplication isometric.
The hypothesis applies to all real parameters, including negative ones. -/
theorem norm_exp_smul_mul_eq_of_le_one {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸)
    (hA : ∀ t : ℝ, ‖exp (t • A)‖ ≤ 1) (t : ℝ) :
    ‖exp (t • A) * X‖ = ‖X‖ := by
  have bound (s : ℝ) (Y : 𝔸) : ‖exp (s • A) * Y‖ ≤ ‖Y‖ := by
    simpa only [one_mul] using norm_mul_le_of_le (hA s) (le_refl ‖Y‖)
  refine le_antisymm (bound t X) ?_
  simpa only [← mul_assoc, neg_smul, exp_neg_mul_self, one_mul] using
    bound (-t) (exp (t • A) * X)

/-- A two-sided contraction bound for the exponential makes right multiplication isometric. -/
theorem norm_mul_exp_smul_eq_of_le_one {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸)
    (hA : ∀ t : ℝ, ‖exp (t • A)‖ ≤ 1) (t : ℝ) :
    ‖X * exp (t • A)‖ = ‖X‖ := by
  have bound (s : ℝ) (Y : 𝔸) : ‖Y * exp (s • A)‖ ≤ ‖Y‖ := by
    simpa only [mul_one] using norm_mul_le_of_le (le_refl ‖Y‖) (hA s)
  refine le_antisymm (bound t X) ?_
  simpa only [mul_assoc, neg_smul, exp_mul_neg_self, mul_one] using
    bound (-t) (X * exp (t • A))

/-- Two-sided exponential bounds give an isometric conjugation in a normed algebra. -/
theorem norm_expSMulConj_eq_of_le_one {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸)
    (hA : ∀ t : ℝ, ‖exp (t • A)‖ ≤ 1) (t : ℝ) :
    ‖expSMulConj A X t‖ = ‖X‖ := by
  rw [expSMulConj, norm_mul_exp_smul_eq_of_le_one A _ hA (-t),
    norm_exp_smul_mul_eq_of_le_one A X hA t]

/-- A finite ordered composition of conjugations preserves the norm under
two-sided exponential contraction bounds, including for the empty list. -/
theorem norm_list_exp_conj_eq_of_le_one {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] {ι : Type*} (A : ι → 𝔸)
    (hA : ∀ i (t : ℝ), ‖exp (t • A i)‖ ≤ 1) (l : List ι) (B : 𝔸) (t : ℝ) :
    ‖(l.map (fun i ↦ exp (t • A i))).reverse.prod * B *
      (l.map (fun i ↦ exp ((-t) • A i))).prod‖ = ‖B‖ := by
  induction l generalizing B with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [show (l.map (fun i ↦ exp (t • A i))).reverse.prod * exp (t • A i) * B *
          (exp ((-t) • A i) * (l.map (fun i ↦ exp ((-t) • A i))).prod) =
        (l.map (fun i ↦ exp (t • A i))).reverse.prod * expSMulConj (A i) B t *
          (l.map (fun i ↦ exp ((-t) • A i))).prod by
            simp only [expSMulConj, mul_assoc]]
      rw [ih, norm_expSMulConj_eq_of_le_one (A i) B (hA i) t]

/-- At fixed time, conjugation preserves distances if the exponential is contractive
for all real times. -/
theorem isometry_expSMulConj_of_le_one {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A : 𝔸)
    (hA : ∀ t : ℝ, ‖exp (t • A)‖ ≤ 1) (t : ℝ) :
    Isometry (fun X ↦ expSMulConj A X t) :=
  AddMonoidHomClass.isometry_of_norm (expSMulConjLin A t) fun X ↦
    norm_expSMulConj_eq_of_le_one A X hA t

end TrotterError

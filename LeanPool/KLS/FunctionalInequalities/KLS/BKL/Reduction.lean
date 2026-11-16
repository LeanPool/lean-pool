/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.TaylorBound
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.IsotropicReduction

/-!
# BKL p. 30: reduction of Theorem 1.1 to Theorems 3.1, 4.1 and Proposition 7.1

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 30 (proof of Theorem 1.1). Given the universal cumulant
bound of Theorem 4.1, `R^ν_{d+1} ≤ (d!)² K^d · Id` for all `d ≥ 2` (`CumulantBound d ((d!)² K^d)`,
`K ≥ 1`), Proposition 7.1 gives `|T_d f|² ≤ 2K^d ‖f‖² ≤ (2K)^d ‖f‖²` for every isotropic regular
law,
isotropy gives `|T_1 f| ≤ ‖f‖`, and Theorem 3.1 with `R = √(2K)` yields `C_P(μ) ≤ 2 C_{3.1} K`.
This module contains the reduction only; its hypothesis is not discharged here. The closed producers
are `BKL.Localization.exists_isotropicBound` and `conjecture` (`KLS/BKL/Poincare.lean`); Section 2's
regular approximation is separate.
-/

@[expose] public section

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS

/--
Entries of the coordinate array of `T_1 f` for a centered law: `(T_1 f)_j = ∫ ⟪e_j, x⟫ f(x) dμ`. -/
theorem coordTensor_taylorTensor_one_apply {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hμ2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (hμ0 : ∫ x, x ∂μ = 0) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (i : Fin 1 → Fin n) :
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f 1) i =
      ∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x ∂μ := by
  rw [coordTensor_apply]
  have hfun :
    (fun j : Fin 1 => EuclideanSpace.basisFun (Fin n) ℝ (i j)) =
      (fun _ : Fin 1 => EuclideanSpace.basisFun (Fin n) ℝ (i 0)) := by
    funext j
    rw [Subsingleton.elim j 0]
  rw [hfun]
  rw [Analysis.BakryEmery.taylorTensor_one_apply μ hexp hf
      (EuclideanSpace.basisFun (Fin n) ℝ (i 0))]
  have hmean :=
    _root_.integral_inner (𝕜 := ℝ) (hμ2.integrable one_le_two)
      (EuclideanSpace.basisFun (Fin n) ℝ (i 0))
  simp only [id_eq] at hmean
  rw [hμ0, inner_zero_right] at hmean
  rw [hmean, mul_zero, sub_zero]

/--
**The `d = 1` Taylor bound from isotropy** (Bessel): `‖T_1 f‖_HS ≤ ‖f‖_{L²(μ)}`, given the entry
formula of the coordinate array. -/
theorem Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : Isotropic μ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hentry :
      ∀ i : Fin 1 → Fin n,
        coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
            (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i =
          ∫ x,
            ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ *
              f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
          (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1)‖ ≤
      (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal := by
  have hdecomp :=
    L2.integral_sq_eq_affine_decomposition (μ : Measure (EuclideanSpace ℝ (Fin n)))
      hiso.memLp_two hiso.mean_zero hiso.integral_inner_mul_inner hf
  have hnonneg :
    0 ≤
      ∫ x,
        (L2.affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n))) f x) ^
          2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integral_nonneg
    intro x
    exact sq_nonneg _
  have hbessel :
    ∑ j : Fin n,
        (∫ x,
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
              f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^
          2 ≤
      ∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    nlinarith [sq_nonneg (∫ x, f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))), hnonneg]
  have hnorm :
    (∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 := by
    let G := hf.toLp f
    have hG : G =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin n)))] f := hf.coeFn_toLp
    calc
      (∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, (G x) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        filter_upwards [hG] with x hx
        rw [hx]
      _ = ∫ x, ⟪G x, G x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [Real.norm_eq_abs, sq_abs]
      _ = ⟪G, G⟫ := by rw [MeasureTheory.L2.inner_def]
      _ = ‖G‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 := by
        rw [Lp.norm_toLp]
  have hsum :
    ∑ i : Fin 1 → Fin n,
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
              (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^
          2 =
      ∑ j : Fin n,
        (∫ x,
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
              f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^
          2 := by
    calc
      ∑ i : Fin 1 → Fin n,
            ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                  (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^
              2 =
          ∑ i : Fin 1 → Fin n,
            (∫ x,
                ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ *
                  f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^
              2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hentry i, Real.norm_eq_abs, sq_abs]
      _ =
          ∑ j : Fin n,
            (∫ x,
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                  f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^
              2 := by
        exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun i => rfl)
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt
          (∑ i : Fin 1 → Fin n,
            ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                  (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^
              2) ≤
        Real.sqrt ((eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2) := by
      apply Real.sqrt_le_sqrt
      calc
        ∑ i : Fin 1 → Fin n,
              ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                    (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i‖ ^
                2 =
            ∑ j : Fin n,
              (∫ x,
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ *
                    f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^
                2 :=
          hsum
        _ ≤ ∫ x, f x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := hbessel
        _ = (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 := hnorm
    _ = (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal := by
      rw [Real.sqrt_sq (ENNReal.toReal_nonneg)]

/--
**BKL p. 30, the case `d = 1`**: for an isotropic law on `ℝⁿ` with all exponential moments and
`f ∈ L²(μ)`, `‖T_1 f‖_HS ≤ ‖f‖_{L²(μ)}` (Bessel; assembly of the two previous lemmas). -/
theorem Isotropic.norm_coordTensor_taylorTensor_one_le {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : Isotropic μ)
    (hexp :
      ∀ r : ℝ,
        Integrable (fun x => Real.exp (r * ‖x‖)) (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
          (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1)‖ ≤
      (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal :=
  hiso.norm_coordTensor_taylorTensor_one_le_of_entries hf fun i =>
    coordTensor_taylorTensor_one_apply (μ : Measure (EuclideanSpace ℝ (Fin n))) hexp
      hiso.memLp_two hiso.mean_zero hf i

end FunctionalInequalities.KLS

namespace FunctionalInequalities.KLS.RegularPotential

/-- `2 K^d ≤ (2K)^d` for `d ≥ 1` and `K ≥ 0` (numeric step of BKL p. 30). -/
theorem two_mul_pow_le_two_mul_pow {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (hd : 1 ≤ d) :
    2 * K ^ d ≤ (2 * K) ^ d := by
    have hpow : (2 : ℝ) ≤ 2 ^ d :=
      le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : d ≠ 0)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hK d)

/-- **BKL p. 30: Theorem 1.1 for regular isotropic laws, conditional on the cumulant bounds of
Theorem 4.1.** If `R^ν_{d+1} ≤ (d!)² K^d · Id` for every isotropic log-concave `ν` in every
dimension
and every `d ≥ 2` (`CumulantBound d ((d!)² K^d)`, `K ≥ 1`), then every isotropic regular law on `ℝⁿ`
has literature Poincaré constant at most `2 C K`, where `C` is the constant of Theorem 3.1
(`poincare_le_of_taylor`): Proposition 7.1 gives `|T_d f|² ≤ 2K^d‖f‖² ≤ (2K)^d‖f‖²` for `d ≥ 2`,
isotropy gives `|T_1 f| ≤ ‖f‖`, and Theorem 3.1 applies with `R = √(2K)`. The hypothesis is the
source's Theorem 4.1, discharged in the closed producer `BKL.Localization.exists_isotropicBound`. -/
theorem poincare_le_of_cumulantBound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ K : ℝ,
          1 ≤ K →
            (∀ d : ℕ, 2 ≤ d → CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
              ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
                (hV : KLS.RegularPotential V a b),
                KLS.Isotropic hV.law →
                  Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ ENNReal.ofReal (2 * C * K) := by
  obtain ⟨C, hC, hT⟩ := poincare_le_of_taylor
  refine ⟨C, hC, fun K hK hcb n V a b hV hiso => ?_⟩
  let E := EuclideanSpace ℝ (Fin n)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let R : ℝ := Real.sqrt (2 * K)
  have hR2 : R ^ 2 = 2 * K := by
    dsimp [R]
    exact Real.sq_sqrt (by positivity)
  have hR1 : 1 ≤ R := by
    have hRnonneg : 0 ≤ R := by
      dsimp [R]
      exact Real.sqrt_nonneg _
    nlinarith [hR2]
  have hmean : (∫ x : E, x ∂(hV.law : Measure E)) = 0 := by exact hiso.mean_zero
  have hcov : ∀ v : E, (∫ x : E, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure E)) ≤ ‖v‖ ^ 2 := by
    intro v
    have hv := hiso.integral_inner_mul_inner v v
    have hv' : (∫ x : E, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure E)) = ‖v‖ ^ 2 := by
      simpa [pow_two, real_inner_self_eq_norm_sq] using hv
    exact hv'.le
  have htaylor :
    ∀ f,
      MemLp f 2 (hV.law : Measure E) →
        ∀ d : ℕ,
          1 ≤ d →
            ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                  (taylorTensor (hV.law : Measure E) f d)‖ ≤
              R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal := by
    intro f hf d hd
    rcases Nat.lt_or_ge d 2 with hlt | hge
    · have hd1 : d = 1 := by omega
      subst d
      have hone := hiso.norm_coordTensor_taylorTensor_one_le hV.integrable_exp_mul_norm hf
      have hE : 0 ≤ (eLpNorm f 2 (hV.law : Measure E)).toReal := ENNReal.toReal_nonneg
      have hR1' : 1 ≤ R ^ (1 : ℕ) := by simpa using hR1
      exact hone.trans (le_mul_of_one_le_left hE hR1')
    · have hparam : 0 < (d.factorial : ℝ) ^ 2 * K ^ d := by positivity
      have hsquare :=
        norm_coordTensor_taylorTensor_sq_le_two_mul hge hparam (hcb d hge) V hV hiso f hf
      have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero d)
      have hcancel :
        2 * ((d.factorial : ℝ) ^ 2 * K ^ d) / (d.factorial : ℝ) ^ 2 *
            (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 =
          2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
        field_simp [hfac]
      have hsq :
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (taylorTensor (hV.law : Measure E) f d)‖ ^
            2 ≤
          2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
        calc
          ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                    (taylorTensor (hV.law : Measure E) f d)‖ ^
                2 ≤
              2 * ((d.factorial : ℝ) ^ 2 * K ^ d) / (d.factorial : ℝ) ^ 2 *
                (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 :=
            hsquare
          _ = 2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := hcancel
      have hpow : 2 * K ^ d ≤ (2 * K) ^ d := two_mul_pow_le_two_mul_pow (le_of_lt hKpos) hd
      have hsq' :
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (taylorTensor (hV.law : Measure E) f d)‖ ^
            2 ≤
          (R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal) ^ 2 := by
        calc
          ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                    (taylorTensor (hV.law : Measure E) f d)‖ ^
                2 ≤
              2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 :=
            hsq
          _ ≤ (2 * K) ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
            exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
          _ = (R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal) ^ 2 := by
            have hp : (2 * K) ^ d = (R ^ d) ^ 2 := by
              calc
                (2 * K) ^ d = (R ^ 2) ^ d := by rw [hR2]
                _ = R ^ (2 * d) := by rw [pow_mul]
                _ = R ^ (d * 2) := by rw [show 2 * d = d * 2 by omega]
                _ = (R ^ d) ^ 2 := by rw [pow_mul]
            rw [hp]
            ring
      have hnonneg :
        0 ≤
          ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
              (taylorTensor (hV.law : Measure E) f d)‖ :=
        norm_nonneg _
      have hright : 0 ≤ R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal := by
        exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
      nlinarith
  have hmain := hT n V a b hV hmean hcov R hR1 htaylor
  calc
    Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ ENNReal.ofReal (C * R ^ 2) := hmain
    _ = ENNReal.ofReal (2 * C * K) := by
      rw [hR2]
      congr 1
      ring

end FunctionalInequalities.KLS.RegularPotential

namespace FunctionalInequalities.KLS

universe u

/-- **BKL Theorem 1.1, conditional on Theorem 4.1**: under the universal cumulant bounds
`CumulantBound d ((d!)² K^d)` for all `d ≥ 2` (`K ≥ 1`), every isotropic log-concave law in every
finite-dimensional inner product space has literature Poincaré constant at most `2·C_{3.1}·K`
(the p. 30 reduction for regular laws plus the Section 2 regular approximation). The closed
producer `BKL.Localization.exists_isotropicBound` discharges the hypothesis and proves Theorem 1.1.
-/
theorem localSlope_le_of_cumulantBound_all :
    ∃ C : ℝ,
      0 < C ∧
        ∀ K : ℝ,
          1 ≤ K →
            (∀ d : ℕ, 2 ≤ d → CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
              ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
                [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
                [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E),
                KLS.LogConcave μ →
                  KLS.Isotropic μ →
                    Poincare.LocalSlope.Intrinsic.optimalConstant μ ≤ ENNReal.ofReal (2 * C * K) := by
  obtain ⟨C, hC, hRegular⟩ := KLS.RegularPotential.poincare_le_of_cumulantBound
  refine ⟨C, hC, ?_⟩
  intro K hK hcb E _ _ _ _ _ _ _ μ hLC hiso
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : NNReal := ⟨2 * C * K, by positivity⟩
  have hB : (B : ENNReal) = ENNReal.ofReal (2 * C * K) := ENNReal.ofReal_coe_nnreal.symm
  have hEuro :
    ∀ (n : ℕ),
      0 < n →
        ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : KLS.RegularPotential V a b),
          0 < b →
            KLS.Isotropic hV.law →
              Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤ (B : ENNReal) := by
    intro n _hn V a b hV _hb hViso
    rw [hB]
    exact hRegular K hK hcb n V a b hV hViso
  rw [← hB]
  exact LogConcave.localSlope_le_of_euclidean_regular_isotropic_bound hEuro μ hLC hiso

/-- The conditional implication to the project's `KLS.Conjecture`: the universal cumulant bounds of
Theorem 4.1 (an explicit hypothesis `hSource`) imply the dimension-free KLS bound. `KLS.kls`
(`KLS/Target.lean`) is proved through the closed producer `BKL.Localization.conjecture`. -/
theorem conjecture_of_cumulantBound
    (hSource : ∃ K : ℝ, 1 ≤ K ∧
      ∀ d : ℕ, 2 ≤ d → CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) :
    KLS.Conjecture := by
  obtain ⟨C, hC, hAll⟩ := localSlope_le_of_cumulantBound_all.{0}
  obtain ⟨K, hK, hcb⟩ := hSource
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : NNReal := ⟨2 * C * K, by positivity⟩
  have hB : (B : ENNReal) = ENNReal.ofReal (2 * C * K) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hIB : KLS.IsotropicBound.{0} B := by
    intro E _ _ _ _ _ _ _ μ hLC hiso
    rw [hB]
    exact hAll K hK hcb E μ hLC hiso
  exact KLS.conjecture_of_affineBound (KLS.affineBound_of_isotropicBound hIB)

end FunctionalInequalities.KLS

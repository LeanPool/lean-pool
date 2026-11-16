/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Temperate
public import LeanPool.KLS.FunctionalInequalities.L2.Pairing
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Inverse
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.TensorEnergy

/-!
# Temperate functions in the generator domain (BKL Lemma 2.1, classical-to-`L²` bridge)

In the heat model `ν = m.tilted (-U)` with `U` of temperate growth and all exponential moments, the
`L²` class of a function `f` of temperate growth (the source class `𝒜`) lies in the domain of the
closed
unit gradient with `Tbar [f] = [∇f]`, and in the domain of the generator `A = Tbar†Tbar` with
`A [f] =
[-ℒf]`.
Hence a centered temperate solution of `-ℒu = g` is the centered operator-domain inverse of `[g]`
(Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Lemma 2.1). With `C_P(ν) ≤ C`, the Poincaré inequality
holds on `𝒜` for scalar and tensor fields, `‖∇h‖² ≤ C ‖ℒh‖²` (the energy bound corresponding to BKL
(20)), the source's (32) `1 ≤ C α²` for a pair satisfying (30), (33) with `∇h ≠ 0`, and Lemma 3.2
and
Lemma 3.3 for `q = 2` with the bound `C χ` (`λ = 1/C ≤ λ₁`, equality for `C = C_P`). The
existence of temperate solutions for `g ∈ 𝒜₀` (smoothness and growth of the inverse) and the
source's
iterates are not proved here.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory

namespace FunctionalInequalities.KLS.LogConcave

open Analysis.Semigroup Analysis.BakryEmery

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))

open scoped ContDiff
open Filter Topology Energy Energy.WeightedGradient

section StructuredSpace

variable {F : Type*}
  [NormedAddCommGroup F]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
private theorem q_memLp_of_polynomial_bound {g : V → F}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (hg : AEStronglyMeasurable g (ν : Measure V)) {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) : MemLp g 2 (ν : Measure V) := by
  apply (memLp_two_iff_integrable_sq_norm hg).mpr
  apply
    FunctionalInequalities.Probability.integrable_of_norm_le_pow (ν : Measure V) hexp
      (hg.norm.pow 2) (C := C ^ 2) (k := k * 2)
  intro x
  change ‖‖g x‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem q_tendsto_toLp [InnerProductSpace ℝ F]
    {a : ℕ → V → F} {b : V → F}
    (ha : ∀ n, MemLp (a n) 2 (ν : Measure V))
    (hb : MemLp b 2 (ν : Measure V))
    {D : V → ℝ} (hD : Integrable D (ν : Measure V))
    (hbound : ∀ n x, ‖a n x - b x‖ ^ 2 ≤ D x)
    (hlocal : ∀ x, ∀ᶠ n : ℕ in atTop, a n x = b x) :
    Tendsto (fun n => (ha n).toLp (a n)) atTop (𝓝 (hb.toLp b)) := by
  have ht : Tendsto (fun n => ∫ x, ‖a n x - b x‖ ^ 2 ∂(ν : Measure V))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_integral_of_dominated_convergence
      (F := fun n x => ‖a n x - b x‖ ^ 2) (f := fun _ => (0 : ℝ)) D
      (fun n => ((ha n).aestronglyMeasurable.sub hb.aestronglyMeasurable).norm.pow 2) hD
      (fun n => ae_of_all _ (fun x => by
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound n x))
      (ae_of_all _ (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hlocal x] with n hn
        simp [hn]))
  have heq (n : ℕ) :
      ‖(ha n).toLp (a n) - hb.toLp b‖ ^ 2 =
        ∫ x, ‖a n x - b x‖ ^ 2 ∂(ν : Measure V) := by
    rw [← real_inner_self_eq_norm_sq, ← (ha n).toLp_sub hb, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((ha n).sub hb).coeFn_toLp] with x hx
    rw [hx, Pi.sub_apply, real_inner_self_eq_norm_sq]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ← heq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hs

private theorem q_sq_sub_le {u v : F} {B : ℝ}
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) : ‖u - v‖ ^ 2 ≤ (2 * B) ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add hu hv
    _ = 2 * B := by ring

end StructuredSpace

include hexp in
/--
A function of temperate growth has its `L²(ν)` class in the domain of the closed unit gradient,
which sends it to the class of `∇f` (only the exponential moments of `ν` are used). -/
theorem exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth {f : V → ℝ}
    (hf : f.HasTemperateGrowth) :
    ∃ (hf2 : MemLp f 2 (ν : Measure V)) (hg2 : MemLp (gradient f) 2 (ν : Measure V)) (hmem :
      hf2.toLp f ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem⟩ =
        hg2.toLp (gradient f) := by
  obtain ⟨k, C, hC, hb⟩ := hf.norm_iteratedFDeriv_le_uniform 1
  have hfb (x : V) : ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 (by omega) x
  have hgb (x : V) : ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using hb 1 le_rfl x
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf2 := q_memLp_of_polynomial_bound hexp hf.1.continuous.aestronglyMeasurable hfb
  have hg2 :=
    q_memLp_of_polynomial_bound hexp (continuous_gradient hf1).aestronglyMeasurable hgb
  obtain ⟨K₀, hK₀⟩ := norm_iteratedFDeriv_cutoff_le (E := V) 1
  let K : ℝ := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  let A : ℝ := C + C * K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCA : C ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (mul_nonneg hC hK)
  let a : ℕ → V → ℝ := fun n x => cutoff ((n : ℝ) + 1) x * f x
  have ha (n : ℕ) : ContDiff ℝ ∞ (a n) := (contDiff_cutoff _).mul hf.1
  have hac (n : ℕ) : HasCompactSupport (a n) :=
    (hasCompactSupport_cutoff (by positivity : 0 < (n : ℝ) + 1)).mul_right
  have hab (n : ℕ) (x : V) : ‖a n x‖ ≤ A * (1 + ‖x‖) ^ k := by
    dsimp only [a]
    rw [norm_mul]
    calc
      _ ≤ 1 * (C * (1 + ‖x‖) ^ k) :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using abs_cutoff_le_one _ _) (hfb x)
          (norm_nonneg _) zero_le_one
      _ ≤ A * (1 + ‖x‖) ^ k := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right hCA (by positivity)
  have hgab (n : ℕ) (x : V) : ‖gradient (a n) x‖ ≤ A * (1 + ‖x‖) ^ k := by
    have hc1 : ContDiff ℝ 1 (cutoff ((n : ℝ) + 1) : V → ℝ) :=
      (contDiff_cutoff _).of_le (WithTop.coe_le_coe.mpr le_top)
    have hcut : ‖gradient (cutoff ((n : ℝ) + 1)) x‖ ≤ K := by
      rw [norm_gradient_eq_norm_iteratedFDeriv_one]
      exact
        (hK₀ _ (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 1) x).trans
          (le_max_left _ _)
    dsimp only [a]
    rw [gradient_mul (hc1.differentiable (by norm_num) x) (hf1.differentiable (by norm_num) x)]
    calc
      _ ≤ ‖cutoff ((n : ℝ) + 1) x • gradient f x‖ + ‖f x • gradient (cutoff ((n : ℝ) + 1)) x‖ :=
        norm_add_le _ _
      _ =
          |cutoff ((n : ℝ) + 1) x| * ‖gradient f x‖ +
            |f x| * ‖gradient (cutoff ((n : ℝ) + 1)) x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (C * (1 + ‖x‖) ^ k) + (C * (1 + ‖x‖) ^ k) * K := by
        gcongr
        · exact abs_cutoff_le_one _ _
        · exact hgb x
        · simpa only [Real.norm_eq_abs] using hfb x
      _ = _ := by dsimp [A]; ring
  have hfA (x : V) : ‖f x‖ ≤ A * (1 + ‖x‖) ^ k :=
    (hfb x).trans (mul_le_mul_of_nonneg_right hCA (by positivity))
  have hgA (x : V) : ‖gradient f x‖ ≤ A * (1 + ‖x‖) ^ k :=
    (hgb x).trans (mul_le_mul_of_nonneg_right hCA (by positivity))
  let D : V → ℝ := fun x => (2 * A) ^ 2 * (1 + ‖x‖) ^ (k * 2)
  have hD : Integrable D (ν : Measure V) := by
    apply
      FunctionalInequalities.Probability.integrable_of_norm_le_pow _ hexp (by fun_prop) (C :=
        (2 * A) ^ 2) (k := k * 2)
    intro x
    exact Real.norm_of_nonneg (by dsimp [D]; positivity) |>.le
  have hlocal (x : V) : ∀ᶠ n : ℕ in atTop, a n =ᶠ[𝓝 x] f := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    dsimp only [a]
    rw [cutoff_eq_one (by positivity) hy.le, one_mul]
  have hat :=
    q_tendsto_toLp (fun n => memLp_of_contDiff_hasCompactSupport ν (ha n) (hac n)) hf2 hD
      (fun n x => by
        simpa only [D, mul_pow, pow_mul, mul_assoc] using q_sq_sub_le (hab n x) (hfA x))
      (fun x => (hlocal x).mono (fun _ hn => hn.eq_of_nhds))
  have hgat :=
    q_tendsto_toLp (fun n => memLp_gradient_of_contDiff_hasCompactSupport (ha n) (hac n)) hg2 hD
      (fun n x => by
        simpa only [D, mul_pow, pow_mul, mul_assoc] using q_sq_sub_le (hgab n x) (hgA x))
      (fun x => (hlocal x).mono (fun _ hn => hn.gradient_eq))
  have hmem (n : ℕ) := hν.toLp_mem_closedWeightedOperator_domain m hi (ha n) (hac n)
  have hgt :
    Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem n⟩)
      atTop (𝓝 (hg2.toLp (gradient f))) := by
    convert hgat using 1
    apply funext
    intro n
    exact hν.closedWeightedOperator_toLp_eq m hi (ha n) (hac n)
  obtain ⟨hmemf, heq⟩ :=
    exists_mem_domain_apply_eq_of_tendsto
      (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi) hmem hat hgt
  exact ⟨hf2, hg2, hmemf, heq⟩

include hνU hU hexp in
/--
**The generator on the class `𝒜`**: a function of temperate growth has its `L²(ν)` class in the
domain of `A = Tbar†Tbar`, and `A [f] = [-ℒf]`. -/
theorem exists_toLp_mem_adjointComp_domain_of_hasTemperateGrowth {f : V → ℝ}
    (hf : f.HasTemperateGrowth) :
    ∃ (hf2 : MemLp f 2 (ν : Measure V)) (hL2 :
      MemLp (fun x => -weightedLaplacian U f x) 2 (ν : Measure V)) (hmem :
      hf2.toLp f ∈
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain),
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hmem⟩ =
        hL2.toLp (fun x => -weightedLaplacian U f x) := by
  obtain ⟨hf2, hg2, hmem, hT⟩ :=
    exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth m hν hi hexp hf
  have hU1 : ContDiff ℝ 1 U := hU.1.of_le (by simp)
  have hL2 : MemLp (fun x => -weightedLaplacian U f x) 2 (ν : Measure V) :=
    FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth (ν : Measure V) hexp
      (hasTemperateGrowth_weightedLaplacian hU hf).neg
  have hweak :
    ∀ x : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      ⟪hL2.toLp (fun y => -weightedLaplacian U f y), (x : Lp ℝ 2 (ν : Measure V))⟫ =
        ⟪hg2.toLp (gradient f),
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi x⟫ := by
    have hSclos :
      ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
            (Energy.WeightedGradient.smoothCore ν)).closure =
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi :=
      hν.closure_domRestrict_eq_of_smoothCore_le m (ContinuousLinearMap.id ℝ V) hi le_rfl
        (Energy.WeightedGradient.smoothCore_le_domain_operator ν (ContinuousLinearMap.id ℝ V) _)
    have hSc :
      ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
          (Energy.WeightedGradient.smoothCore ν)).IsClosable :=
      (hν.weightedOperator_isClosable m (ContinuousLinearMap.id ℝ V) hi).leIsClosable
        LinearPMap.domRestrict_le
    have hcore :
      ∀ y :
        ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
            (Energy.WeightedGradient.smoothCore ν)).domain,
        ⟪hL2.toLp (fun y => -weightedLaplacian U f y), (y : Lp ℝ 2 (ν : Measure V))⟫ =
          ⟪hg2.toLp (gradient f),
            (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
              (Energy.WeightedGradient.smoothCore ν) y⟫ := by
      rintro ⟨y, hy⟩
      have hy1 : y ∈ Energy.WeightedGradient.smoothCore ν := (Submodule.mem_inf.mp hy).1
      have hy2 : y ∈ (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
        (Submodule.mem_inf.mp hy).2
      obtain ⟨g, hg, hgc, rfl⟩ := hy1
      have htest :=
        Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν
          (ContinuousLinearMap.id ℝ V) hg hgc
      have hSy :
        (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
            (Energy.WeightedGradient.smoothCore ν) ⟨_, hy⟩ =
          htest.memLp_apply.toLp
            (Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) g) := by
        erw [LinearPMap.domRestrict_apply (x := ⟨_, hy⟩) (y := ⟨_, hy2⟩) rfl]
        exact
          Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) _
            (hν.frontier_support_eq_zero hi) htest hy2 rfl
      rw [hSy, L2.inner_def, L2.inner_def]
      have h1 :
        (fun a =>
            ⟪(hL2.toLp (fun y => -weightedLaplacian U f y) : Lp ℝ 2 (ν : Measure V)) a,
              ((Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hg hgc).toLp g :
                  Lp ℝ 2 (ν : Measure V))
                a⟫) =ᵐ[(ν : Measure V)]
          fun a => -weightedLaplacian U f a * g a := by
        filter_upwards [hL2.coeFn_toLp,
          (Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hg
              hgc).coeFn_toLp] with
          a ha hb
        rw [ha, hb, Real.inner_apply]
      have h2 :
        (fun a =>
            ⟪(hg2.toLp (gradient f) : Lp V 2 (ν : Measure V)) a,
              (htest.memLp_apply.toLp
                    (Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) g) :
                  Lp V 2 (ν : Measure V))
                a⟫) =ᵐ[(ν : Measure V)]
          fun a => ⟪gradient f a, gradient g a⟫ := by
        filter_upwards [hg2.coeFn_toLp, htest.memLp_apply.coeFn_toLp] with a ha hb
        rw [ha, hb, Energy.WeightedGradient.apply_id]
      rw [integral_congr_ae h1, integral_congr_ae h2]
      have hibp :=
        integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport m hU1
          (hf.1.of_le (WithTop.coe_le_coe.mpr le_top))
          (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgc
      rw [← hνU] at hibp
      simp only [neg_mul, integral_neg, hibp, neg_neg]
    have := inner_eq_inner_closure_apply hSc hcore
    rw [hSclos] at this
    exact this
  refine ⟨hf2, hL2, ⟨mem_adjointCompDomain.mpr ⟨hmem, ?_⟩, hmem⟩, ?_⟩
  · rw [hT]
    exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, hweak⟩
  · rw [adjointComp_apply]
    refine
      LinearPMap.adjoint_apply_eq
        (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) _ fun x => ?_
    rw [hweak x]
    congr 1
    exact hT.symm

include hνU hU hexp in
/--
**Identification of the centered inverse on `𝒜`**: if `C_P(ν) ≤ C` and a centered function `u` of
temperate growth solves `-ℒu = g` pointwise, then the centered `L²` inverse of `[g]` (BKL Lemma 2.1,
operator-domain part) is the class of `u`. -/
theorem centered_inverse_eq_toLp_of_hasTemperateGrowth {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal)) {u : V → ℝ}
    (hu : u.HasTemperateGrowth) (hmean : ∫ x, u x ∂(ν : Measure V) = 0)
    (w : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hw : L2.mean ν (w : Lp ℝ 2 (ν : Measure V)) = 0)
    (hL2 : MemLp (fun x => -weightedLaplacian U u x) 2 (ν : Measure V))
    (hAw :
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) w =
        hL2.toLp (fun x => -weightedLaplacian U u x)) :
    ∃ hu2 : MemLp u 2 (ν : Measure V), (w : Lp ℝ 2 (ν : Measure V)) = hu2.toLp u := by
  obtain ⟨hu2, hL2', hmem, hA⟩ :=
    exists_toLp_mem_adjointComp_domain_of_hasTemperateGrowth m hν hi hνU hU hexp hu
  refine ⟨hu2, ?_⟩
  have hU2 : ContDiff ℝ 2 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : L2.mean ν (hL2.toLp (fun x => -weightedLaplacian U u x)) = 0 := by
    have hU1 : ContDiff ℝ 1 U := hU.1.of_le (by simp)
    obtain ⟨k, Cb, hCb⟩ := hU.2 1
    have hUg : ∀ x : V, ‖gradient U x‖ ≤ Cb * (1 + ‖x‖) ^ k := by
      intro x
      rw [norm_gradient_eq_norm_iteratedFDeriv_one]
      exact hCb x
    have hexp' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-U)) := by
      rw [← hνU]
      exact hexp
    have hibp :=
      integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth m hU1 hUg hexp' hu
        (Function.HasTemperateGrowth.const (1 : ℝ))
    have h0 : ∀ x, gradient (fun _ : V => (1 : ℝ)) x = 0 := fun x => by simp [gradient]
    simp only [mul_one, h0, inner_zero_right, integral_zero, neg_zero] at hibp
    rw [L2.mean_eq_integral, integral_congr_ae hL2.coeFn_toLp, integral_neg, hνU, hibp,
      neg_zero]
  obtain ⟨v, -, huniq⟩ := existsUnique_centered_adjointComp_eq m hν hi hνU hU2 hC _ hg
  have h1 := huniq w ⟨hw, hAw⟩
  have hmu : L2.mean ν (hu2.toLp u) = 0 := by
    rw [L2.mean_eq_integral]
    rw [← hmean]
    exact integral_congr_ae hu2.coeFn_toLp
  have h2 := huniq ⟨hu2.toLp u, hmem⟩ ⟨hmu, by rw [hA]⟩
  exact congrArg Subtype.val (h1.trans h2.symm)

section Spectral

variable {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))

section InnerProduct

variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section FiniteDimensional

variable [FiniteDimensional ℝ F]

omit [SecondCountableTopology V] in
private theorem integrable_norm_sq_weightedLaplacianVec (μ : Measure V)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {U : V → ℝ}
    (hU : U.HasTemperateGrowth) {h : V → F} (hh : h.HasTemperateGrowth) :
    Integrable (fun x => ‖weightedLaplacianVec U h x‖ ^ 2) μ := by
  classical
  let b := stdOrthonormalBasis ℝ F
  have hcomp :
    ∀ k x, ⟪b k, weightedLaplacianVec U h x⟫ = weightedLaplacian U (fun y => ⟪b k, h y⟫) x :=
    fun k x =>
    clm_apply_weightedLaplacianVec U (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
      (innerSL ℝ (b k)) x
  have hpt :
    ∀ x,
      ‖weightedLaplacianVec U h x‖ ^ 2 =
        ∑ k, (weightedLaplacian U (fun y => ⟪b k, h y⟫) x) ^ 2 := by
    intro x
    rw [← b.sum_sq_norm_inner_right (weightedLaplacianVec U h x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcomp k x, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt]
  refine integrable_finsetSum _ fun k _ => ?_
  have hk :=
    hasTemperateGrowth_weightedLaplacian hU (hasTemperateGrowth_inner_left_comp hh (b k))
  have hm := FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth μ hexp hk
  simpa only [Real.norm_eq_abs, sq_abs] using
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm

include m hν hi hexp hC in
/-- **Poincaré on `𝒜`**: `Var_ν f ≤ C ∫ ‖∇f‖²` for `f` of temperate growth. -/
theorem integral_sq_sub_integral_le_of_hasTemperateGrowth {f : V → ℝ} (hf : f.HasTemperateGrowth) :
    ∫ x, (f x - ∫ y, f y ∂(ν : Measure V)) ^ 2 ∂(ν : Measure V) ≤
      (C : ℝ) * ∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V) := by
  obtain ⟨hf2, hg2, hmem, hT⟩ :=
    exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth m hν hi hexp hf
  have hgap := hν.closedWeightedOperator_id_gap_of_literature_le m hi C hC ⟨_, hmem⟩
  rw [hT] at hgap
  have h1 : ‖L2.center ν (hf2.toLp f)‖ ^ 2 =
      ∫ x, (f x - ∫ y, f y ∂(ν : Measure V)) ^ 2 ∂(ν : Measure V) := by
    rw [L2.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [L2.center_coeFn ν (hf2.toLp f), hf2.coeFn_toLp] with x hx hx'
    rw [hx, hx', L2.mean_eq_integral, integral_congr_ae hf2.coeFn_toLp, Real.norm_eq_abs, sq_abs]
  have h2 : ‖hg2.toLp (gradient f)‖ ^ 2 = ∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V) := by
    rw [L2.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    rw [hx]
  rw [h1, h2] at hgap
  exact hgap

include m hν hi hexp hC in
/--
**Poincaré for tensor fields on `𝒜`**: `∫ ‖h - ∫ h‖² ≤ C ∫ ‖∇h‖²` (Hilbert–Schmidt norms). -/
theorem integral_norm_sq_sub_integral_le_of_hasTemperateGrowth {h : V → F}
    (hh : h.HasTemperateGrowth) :
    ∫ x, ‖h x - ∫ y, h y ∂(ν : Measure V)‖ ^ 2 ∂(ν : Measure V) ≤
      (C : ℝ) * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) := by
  classical
  let b := stdOrthonormalBasis ℝ F
  let e := stdOrthonormalBasis ℝ V
  set c := ∫ y, h y ∂(ν : Measure V) with hc
  have hfk : ∀ k, (fun x => ⟪b k, h x⟫).HasTemperateGrowth := fun k =>
    hasTemperateGrowth_inner_left_comp hh (b k)
  have hhi : Integrable h (ν : Measure V) :=
    (FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth (ν : Measure V) hexp
          hh).integrable
      (by norm_num)
  have hmean : ∀ k, ∫ y, ⟪b k, h y⟫ ∂(ν : Measure V) = ⟪b k, c⟫ := fun k =>
    integral_inner hhi (b k)
  have hA : ∀ x, ‖h x - c‖ ^ 2 = ∑ k, (⟪b k, h x⟫ - ∫ y, ⟪b k, h y⟫ ∂(ν : Measure V)) ^ 2 := by
    intro x
    rw [← b.sum_sq_norm_inner_right (h x - c)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmean k, inner_sub_right, Real.norm_eq_abs, sq_abs]
  have hD : ∀ k x v, fderiv ℝ (fun y => ⟪b k, h y⟫) x v = ⟪b k, fderiv ℝ h x v⟫ := by
    intro k x v
    have hd : DifferentiableAt ℝ h x := hh.1.differentiable (by simp) x
    have := ((innerSL ℝ (b k)).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    simp only [Function.comp_def, innerSL_apply_apply] at this
    rw [this]
    rfl
  have hB : ∀ x, ‖gradCoord h x‖ ^ 2 = ∑ k, ‖gradient (fun y => ⟪b k, h y⟫) x‖ ^ 2 := by
    intro x
    rw [norm_sq_gradCoord]
    have h1 :
      ∀ k, ‖gradient (fun y => ⟪b k, h y⟫) x‖ ^ 2 = ∑ i, ⟪b k, fderiv ℝ h x (e i)⟫ ^ 2 := by
      intro k
      rw [← e.sum_sq_norm_inner_right (gradient (fun y => ⟪b k, h y⟫) x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs, gradient, real_inner_comm,
        InnerProductSpace.toDual_symm_apply, hD k x (e i)]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← b.sum_sq_norm_inner_right (fderiv ℝ h x (e i))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hI1 :
    ∀ k,
      Integrable (fun x => (⟪b k, h x⟫ - ∫ y, ⟪b k, h y⟫ ∂(ν : Measure V)) ^ 2)
        (ν : Measure V) := by
    intro k
    have hm :=
      FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth (ν : Measure V) hexp
        ((hfk k).sub (Function.HasTemperateGrowth.const (∫ y, ⟪b k, h y⟫ ∂(ν : Measure V))))
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  have hI2 :
    ∀ k, Integrable (fun x => ‖gradient (fun y => ⟪b k, h y⟫) x‖ ^ 2) (ν : Measure V) := by
    intro k
    have hm :=
      FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth (ν : Measure V) hexp
        (hasTemperateGrowth_gradient (hfk k))
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  simp_rw [hA, hB]
  rw [integral_finsetSum _ fun k _ => hI1 k, integral_finsetSum _ fun k _ => hI2 k,
    Finset.mul_sum]
  exact
    Finset.sum_le_sum fun k _ =>
      integral_sq_sub_integral_le_of_hasTemperateGrowth m hν hi hexp hC (hfk k)

include hν hi hνU hU hexp hC in
/--
**The energy bound corresponding to BKL (20)**, on `𝒜`: `∫ ‖∇h‖² ≤ C ∫ ‖ℒh‖²` for tensor fields `h`
of temperate growth (the gradient-energy part of (20) with `g = -ℒ(h - ∫ h)`). -/
theorem integral_norm_sq_gradCoord_le_of_hasTemperateGrowth {h : V → F}
    (hh : h.HasTemperateGrowth) :
    ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) ≤
      (C : ℝ) * ∫ x, ‖weightedLaplacianVec U h x‖ ^ 2 ∂(ν : Measure V) := by
  set c := ∫ y, h y ∂(ν : Measure V) with hc
  have hU1 : ContDiff ℝ 1 U := hU.1.of_le (by simp)
  obtain ⟨k, Cb, hCb⟩ := hU.2 1
  have hUg : ∀ x : V, ‖gradient U x‖ ≤ Cb * (1 + ‖x‖) ^ k := fun x => by
    rw [norm_gradient_eq_norm_iteratedFDeriv_one]; exact hCb x
  have hexp' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-U)) := by
    rw [← hνU]; exact hexp
  have hhc : (fun x => h x - c).HasTemperateGrowth :=
    hh.sub (Function.HasTemperateGrowth.const c)
  have hibp := integral_inner_weightedLaplacianVec_eq_neg m hU1 hUg hexp' hh hhc
  rw [← hνU] at hibp
  have hd : ∀ x, fderiv ℝ (fun y => h y - c) x = fderiv ℝ h x := fun x => by
    rw [fderiv_sub_const]
  simp only [hd, real_inner_self_eq_norm_sq] at hibp
  have hXeq :
    ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) =
      ∫ x, -⟪weightedLaplacianVec U h x, h x - c⟫ ∂(ν : Measure V) := by
    rw [integral_neg, hibp, neg_neg]
    congr 1
    funext x
    rw [norm_sq_gradCoord]
  have hY := integral_norm_sq_sub_integral_le_of_hasTemperateGrowth m hν hi hexp hC hh
  rw [← hc] at hY
  have hLi := integrable_norm_sq_weightedLaplacianVec (ν : Measure V) hexp hU hh
  have hmc :=
    FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth (ν : Measure V) hexp hhc
  have hYi := (memLp_two_iff_integrable_sq_norm hmc.aestronglyMeasurable).1 hmc
  set X := ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V)
  set L := ∫ x, ‖weightedLaplacianVec U h x‖ ^ 2 ∂(ν : Measure V)
  set Y := ∫ x, ‖h x - c‖ ^ 2 ∂(ν : Measure V)
  have hL0 : 0 ≤ L := integral_nonneg fun x => by positivity
  have hX0 : 0 ≤ X := integral_nonneg fun x => by positivity
  have key : ∀ t : ℝ, 0 < t → X ≤ t / 2 * L + 1 / (2 * t) * Y := by
    intro t ht
    have hpt :
      ∀ x,
        -⟪weightedLaplacianVec U h x, h x - c⟫ ≤
          t / 2 * ‖weightedLaplacianVec U h x‖ ^ 2 + 1 / (2 * t) * ‖h x - c‖ ^ 2 := by
      intro x
      have h1 :
        -⟪weightedLaplacianVec U h x, h x - c⟫ ≤ ‖weightedLaplacianVec U h x‖ * ‖h x - c‖ := by
        have := abs_real_inner_le_norm (weightedLaplacianVec U h x) (h x - c)
        linarith [neg_abs_le (⟪weightedLaplacianVec U h x, h x - c⟫)]
      have h2 :
        ‖weightedLaplacianVec U h x‖ * ‖h x - c‖ ≤
          t / 2 * ‖weightedLaplacianVec U h x‖ ^ 2 + 1 / (2 * t) * ‖h x - c‖ ^ 2 := by
        have he :
          t / 2 * ‖weightedLaplacianVec U h x‖ ^ 2 + 1 / (2 * t) * ‖h x - c‖ ^ 2 -
              ‖weightedLaplacianVec U h x‖ * ‖h x - c‖ =
            (t * ‖weightedLaplacianVec U h x‖ - ‖h x - c‖) ^ 2 / (2 * t) := by
          field_simp
          ring
        have : 0 ≤ (t * ‖weightedLaplacianVec U h x‖ - ‖h x - c‖) ^ 2 / (2 * t) := by positivity
        linarith
      linarith
    have hint :
      Integrable
        (fun x => t / 2 * ‖weightedLaplacianVec U h x‖ ^ 2 + 1 / (2 * t) * ‖h x - c‖ ^ 2)
        (ν : Measure V) :=
      (hLi.const_mul _).add (hYi.const_mul _)
    by_cases hI : Integrable (fun x => -⟪weightedLaplacianVec U h x, h x - c⟫) (ν : Measure V)
    · calc
        X = ∫ x, -⟪weightedLaplacianVec U h x, h x - c⟫ ∂(ν : Measure V) := hXeq
        _ ≤
            ∫ x,
              (t / 2 * ‖weightedLaplacianVec U h x‖ ^ 2 +
                1 / (2 * t) * ‖h x - c‖ ^ 2) ∂(ν : Measure V) :=
          integral_mono hI hint hpt
        _ = t / 2 * L + 1 / (2 * t) * Y := by
          rw [integral_add (hLi.const_mul _) (hYi.const_mul _), integral_const_mul,
            integral_const_mul]
    · have hX : X = 0 := by rw [hXeq, integral_undef hI]
      have hYnn : 0 ≤ Y := integral_nonneg fun x => by positivity
      rw [hX]
      positivity
  have hYnn : 0 ≤ Y := integral_nonneg fun x => by positivity
  by_cases hC0 : (C : ℝ) = 0
  · have hY0 : Y = 0 := le_antisymm (by rw [hC0, zero_mul] at hY; exact hY) hYnn
    have hXle : X ≤ 0 := by
      by_contra hpos'
      have hpos : 0 < X := lt_of_not_ge hpos'
      have h1 := key (X / (L + 1)) (div_pos hpos (by linarith))
      rw [hY0, mul_zero, add_zero] at h1
      have h2 : X / (L + 1) / 2 * L < X := by
        have hL1 : 0 < L + 1 := by linarith
        rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    rw [hC0, zero_mul]
    exact hXle
  · have hCpos : 0 < (C : ℝ) := lt_of_le_of_ne C.2 (Ne.symm hC0)
    have h1 := key C hCpos
    have h2 : 1 / (2 * (C : ℝ)) * Y ≤ X / 2 := by
      calc
        1 / (2 * (C : ℝ)) * Y ≤ 1 / (2 * (C : ℝ)) * ((C : ℝ) * X) :=
          mul_le_mul_of_nonneg_left hY (by positivity)
        _ = X / 2 := by field_simp
    linarith

end FiniteDimensional

end InnerProduct

section FiniteDimensional

variable {G : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

include hν hi hνU hU hexp hC in
/-- **BKL (32)** for a supplied pair: if `-ℒh = α ∇₀g`, `‖∇h‖² = ‖∇₀g‖²` (33) and `∇h ≠ 0` in `L²`,
then `1 ≤ C α²` (that is, `α² ≥ λ₁` when `C = 1/λ₁`). -/
theorem one_le_mul_sq_of_poisson {g : V → G}
    {h : V → PiLp 2 (fun _ : Fin (Module.finrank ℝ V) => G)} {α : ℝ}
    (hh : h.HasTemperateGrowth)
    (h30 : ∀ x, -weightedLaplacianVec U h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(ν : Measure V)))
    (h33 : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) =
      ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(ν : Measure V)‖ ^ 2 ∂(ν : Measure V))
    (hne : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) ≠ 0) :
    1 ≤ (C : ℝ) * α ^ 2 := by
  have hX0 : 0 ≤ ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) := integral_nonneg fun x => by positivity
  have hX : 0 < ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) := lt_of_le_of_ne hX0 (Ne.symm hne)
  have h3 := integral_norm_sq_gradCoord_le_of_hasTemperateGrowth m hν hi hνU hU hexp hC hh
  have hL : ∫ x, ‖weightedLaplacianVec U h x‖ ^ 2 ∂(ν : Measure V) =
      α ^ 2 * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) := by
    rw [h33, ← integral_const_mul]
    congr 1
    funext x
    rw [← norm_neg, h30 x, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hL] at h3
  nlinarith

include hν hi hνU hU hexp hC in
/--
**BKL Lemma 3.2** in the heat model, in squared form with the bound `C χ` (that is `χ / λ` with
`λ = 1/C ≤ λ₁` when `C > 0`, equality for `C = C_P`): for a pair satisfying (30) and (33), `∇₀h`
lies
within squared `L²` distance `C χ` of a tensor field symmetric in its first two indices. -/
theorem exists_symm_integral_norm_sq_sub_le_mul {g : V → G}
    {h : V → PiLp 2 (fun _ : Fin (Module.finrank ℝ V) => G)} {α : ℝ} (hg : g.HasTemperateGrowth)
    (hh : h.HasTemperateGrowth)
    (h30 :
      ∀ x,
        -weightedLaplacianVec U h x = α • (gradCoord g x - ∫ y, gradCoord g y ∂(ν : Measure V)))
    (h33 :
      ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) =
        ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(ν : Measure V)‖ ^ 2 ∂(ν : Measure V)) :
    ∃ T :
      V →
        PiLp 2
          (fun _ : Fin (Module.finrank ℝ V) => PiLp 2 (fun _ : Fin (Module.finrank ℝ V) => G)),
      (∀ x i j, T x i j = T x j i) ∧
        Integrable (fun x => ‖(gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V)) - T x‖ ^ 2)
            (ν : Measure V) ∧
          ∫ x,
              ‖(gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V)) - T x‖ ^
                2 ∂(ν : Measure V) ≤
            (C : ℝ) *
              ∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂(ν : Measure V) := by
  by_cases hX : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) = 0
  · have hgh := hasTemperateGrowth_gradCoord hh
    have hm :=
      FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth (ν : Measure V) hexp
        hgh
    have hi2 := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    have hae : (fun x => ‖gradCoord h x‖ ^ 2) =ᵐ[(ν : Measure V)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi2).1 hX
    have hae' : gradCoord h =ᵐ[(ν : Measure V)] 0 := by
      filter_upwards [hae] with x hx
      simpa using hx
    have hc : ∫ y, gradCoord h y ∂(ν : Measure V) = 0 := by
      rw [integral_congr_ae hae']
      simp
    have hz :
      (fun x =>
          ‖(gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V)) - 0‖ ^ 2) =ᵐ[(ν : Measure V)]
        0 := by
      filter_upwards [hae'] with x hx
      simp [hx, hc]
    refine ⟨fun _ => 0, fun _ _ _ => rfl, (integrable_zero _ _ _).congr hz.symm, ?_⟩
    rw [integral_congr_ae hz]
    simp only [Pi.zero_apply, integral_zero]
    exact mul_nonneg C.2 (integral_nonneg fun x => by positivity)
  · have h1 := one_le_mul_sq_of_poisson m hν hi hνU hU hexp hC hh h30 h33 hX
    have hCpos : 0 < (C : ℝ) := by
      by_contra hc
      have h0 : (C : ℝ) = 0 := le_antisymm (not_lt.mp hc) C.2
      rw [h0, zero_mul] at h1
      linarith
    have hP : IsProbabilityMeasure (m.tilted (-U)) :=
      hνU ▸ (inferInstance : IsProbabilityMeasure (ν : Measure V))
    have hexp' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-U)) := by
      rw [← hνU]; exact hexp
    have h30' :
      ∀ x,
        -weightedLaplacianVec U h x =
          α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-U))) := by
      rw [← hνU]; exact h30
    obtain ⟨T, hT1, hT2, hT3⟩ :=
      exists_symm_integral_norm_sq_sub_le m hU hexp' hg hh h30' (lam := (C : ℝ)⁻¹)
        (inv_pos.mpr hCpos) (fun _ => by rw [inv_le_iff_one_le_mul₀ hCpos, mul_comm]; exact h1)
    refine ⟨T, hT1, ?_, ?_⟩
    · rw [hνU]; exact hT2
    · rw [hνU]
      calc
        _ ≤ _ := hT3
        _ = _ := by rw [div_inv_eq_mul, mul_comm]

include hν hi hνU hU hexp hC in
/-- **BKL Lemma 3.3 in the case `q = 2`** in the heat model: for a pair satisfying (30) and (33),
`‖∇₀h - S₂∇₀h‖² ≤ C χ`. -/
theorem integral_norm_sq_sub_symmetrizeFirstTwo_le_mul {g : V → G}
    {h : V → PiLp 2 (fun _ : Fin (Module.finrank ℝ V) => G)} {α : ℝ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (h30 : ∀ x, -weightedLaplacianVec U h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(ν : Measure V)))
    (h33 : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(ν : Measure V) =
      ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(ν : Measure V)‖ ^ 2 ∂(ν : Measure V)) :
    ∫ x, ‖(gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V)) -
        symmetrizeFirstTwo (gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V))‖ ^ 2
        ∂(ν : Measure V) ≤
      (C : ℝ) * ∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂(ν : Measure V) := by
  obtain ⟨T, hT1, hT2, hT3⟩ :=
    exists_symm_integral_norm_sq_sub_le_mul m hν hi hνU hU hexp hC hg hh h30 h33
  have hpt : ∀ x, ‖(gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V)) -
      symmetrizeFirstTwo (gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V))‖ ^ 2 ≤
        ‖(gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V)) - T x‖ ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_symmetrizeFirstTwo_le _ _ (hT1 x)) 2
  by_cases hI : Integrable (fun x => ‖(gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V)) -
      symmetrizeFirstTwo (gradCoord h x - ∫ y, gradCoord h y ∂(ν : Measure V))‖ ^ 2) (ν : Measure V)
  · exact (integral_mono hI hT2 hpt).trans hT3
  · rw [integral_undef hI]
    exact mul_nonneg C.2 (integral_nonneg fun x => by positivity)

end FiniteDimensional

end Spectral

end FunctionalInequalities.KLS.LogConcave

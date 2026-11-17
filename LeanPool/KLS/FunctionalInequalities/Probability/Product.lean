/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent coordinates of product measures

Factorization of lower integrals of products over `μ^N`, and second-moment calculus on finite
products `μ^N = Measure.pi (fun _ => μ)` and on binary products
`μ ⊗ ν`: normalized sums of independent copies, products of coordinates, and sums of independent
observables. Only `L²` hypotheses are used. These are the moment computations behind the isotropy
of the suspension in Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 28.
The lower-integral factorization is `lintegral_pi_prod_fin`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace FunctionalInequalities.Probability

section MeasurableSpace

variable {E : Type*}
  [MeasurableSpace E]

/-- `∫⁻ Π_i g_i(x_i) d(⊗_i μ) = Π_i ∫⁻ g_i dμ` over `Fin N`. -/
theorem lintegral_pi_prod_fin
    (μ : Measure E) [SigmaFinite μ] (k : ℕ) (g : Fin k → E → ENNReal)
    (hg : ∀ i, Measurable (g i)) :
    (∫⁻ x, ∏ i : Fin k, g i (x i) ∂(Measure.pi fun _ : Fin k => μ)) =
      ∏ i : Fin k, ∫⁻ x, g i x ∂μ := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      let e :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => E) 0
      let ν := Measure.pi (fun _ : Fin k => μ)
      have he :
          MeasurePreserving e
            (Measure.pi (fun _ : Fin (k + 1) => μ)) (μ.prod ν) :=
        measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
      have htail :
          Measurable (fun y : Fin k → E => ∏ i : Fin k, g i.succ (y i)) := by
        apply Finset.measurable_prod
        intro i hi
        exact (hg i.succ).comp (measurable_pi_apply i)
      have hcomp :
          (fun a : E × (Fin k → E) =>
              ∏ i : Fin (k + 1), g i ((e.symm a) i)) =
            (fun a : E × (Fin k → E) =>
              g 0 a.1 * ∏ i : Fin k, g i.succ (a.2 i)) := by
        funext a
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.prod_univ_succ, Fin.insertNthEquiv, Fin.cons_zero,
          Fin.cons_succ, Fin.zero_succAbove]
      calc
        (∫⁻ x, ∏ i : Fin (k + 1), g i (x i)
            ∂Measure.pi (fun _ : Fin (k + 1) => μ)) =
            ∫⁻ a, ∏ i : Fin (k + 1), g i ((e.symm a) i) ∂(μ.prod ν) :=
          MeasurePreserving.lintegral_map_equiv
            (fun x => ∏ i : Fin (k + 1), g i (x i)) e.symm he.symm
        _ = ∫⁻ a, g 0 a.1 * ∏ i : Fin k, g i.succ (a.2 i) ∂(μ.prod ν) := by
          rw [hcomp]
        _ = (∫⁻ x, g 0 x ∂μ) *
              ∫⁻ y, ∏ i : Fin k, g i.succ (y i) ∂ν :=
          lintegral_prod_mul (hg 0).aemeasurable htail.aemeasurable
        _ = (∫⁻ x, g 0 x ∂μ) *
              ∏ i : Fin k, ∫⁻ x, g i.succ x ∂μ := by
          rw [ih (fun i => g i.succ) (fun i => hg i.succ)]
        _ = ∏ i : Fin (k + 1), ∫⁻ x, g i x ∂μ := by
          rw [Fin.prod_univ_succ]

/-- **Normalized sums of independent copies.** If `f ∈ L²(μ)` has mean `0` and second moment `1`,
then `(Σ_i f(x_i))/√N` has mean `0` and second moment `1` under `μ^N` (`N > 0`). -/
theorem pi_normalizedSum_moments
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (N : ℕ) (hN : 0 < N) :
    MemLp (fun x : Fin N → E => (∑ i, f (x i)) / Real.sqrt N) 2
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, (∑ i, f (x i)) / Real.sqrt N
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
      (∫ x : Fin N → E, ((∑ i, f (x i)) / Real.sqrt N) ^ 2
        ∂(Measure.pi (fun _ : Fin N => μ))) = 1 := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let S : (Fin N → E) → ℝ := fun x => ∑ i, f (x i)
  have hEval2 (i : Fin N) : MemLp (fun x : Fin N → E => f (x i)) 2 ν := by
    exact hf2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hS2 : MemLp S 2 ν := by
    exact memLp_finsetSum Finset.univ (fun i _ => hEval2 i)
  have hEval0 (i : Fin N) : (∫ x : Fin N → E, f (x i) ∂ν) = 0 := by
    have he := measurePreserving_eval (fun _ : Fin N => μ) i
    have hm : AEStronglyMeasurable f (ν.map (Function.eval i)) := by
      rw [he.map_eq]
      exact hf2.aestronglyMeasurable
    calc
      (∫ x : Fin N → E, f (x i) ∂ν) =
          ∫ x, f x ∂(ν.map (Function.eval i)) := (integral_map he.measurable.aemeasurable hm).symm
      _ = 0 := by rw [he.map_eq]; exact hf0
  have hS0 : (∫ x, S x ∂ν) = 0 := by
    calc
      (∫ x, S x ∂ν) = ∑ i : Fin N, ∫ x, f (x i) ∂ν :=
        integral_finsetSum _ (fun i _ => (hEval2 i).integrable one_le_two)
      _ = 0 := by simp_rw [hEval0]; simp
  have hVarf : variance f μ = 1 := by
    rw [variance_eq_sub hf2]
    simp only [Pi.pow_apply]
    rw [hf1, hf0]
    norm_num
  have hVarS : variance S ν = (N : ℝ) := by
    have h := variance_sum_pi (μ := fun _ : Fin N => μ) (X := fun _ => f) (fun _ => hf2)
    have heq : (∑ i : Fin N, fun x : Fin N → E => f (x i)) = S := by
      funext x
      simp [S]
    rw [heq] at h
    simpa [ν, hVarf] using h
  have hSsq : (∫ x, S x ^ 2 ∂ν) = (N : ℝ) := by
    rw [variance_eq_sub hS2, hS0] at hVarS
    simpa using hVarS
  have hNormalized2 : MemLp (fun x : Fin N → E => S x / Real.sqrt N) 2 ν := by
    simpa [div_eq_mul_inv] using hS2.mul_const (Real.sqrt N)⁻¹
  refine ⟨hNormalized2, ?_, ?_⟩
  · change (∫ x, S x / Real.sqrt N ∂ν) = 0
    rw [integral_div, hS0]
    simp
  · change (∫ x, (S x / Real.sqrt N) ^ 2 ∂ν) = 1
    simp_rw [div_pow]
    rw [integral_div, hSsq, Real.sq_sqrt (Nat.cast_nonneg N)]
    exact div_self (by exact_mod_cast hN.ne')

/-- A coordinate of `μ^N` has law `μ`. -/
theorem integral_comp_eval_pi
    (μ : Measure E) [IsProbabilityMeasure μ] (a : E → ℝ)
    (ha : AEStronglyMeasurable a μ) (N : ℕ) (i : Fin N) :
    (∫ x : Fin N → E, a (x i) ∂(Measure.pi (fun _ : Fin N => μ))) = ∫ x, a x ∂μ := by
  have he := measurePreserving_eval (fun _ : Fin N => μ) i
  have hm : AEStronglyMeasurable a
      ((Measure.pi (fun _ : Fin N => μ)).map (Function.eval i)) := by
    rw [he.map_eq]
    exact ha
  calc
    _ = ∫ x, a x ∂((Measure.pi (fun _ : Fin N => μ)).map (Function.eval i)) :=
      (integral_map he.measurable.aemeasurable hm).symm
    _ = ∫ x, a x ∂μ := by rw [he.map_eq]

/-- **Products of coordinates.** For `f, g ∈ L²(μ)`, `∫ f(x_i) g(x_j) dμ^N` is `∫ f g dμ` when
`i = j` and `(∫ f dμ)(∫ g dμ)` otherwise. -/
theorem integral_mul_comp_eval_pi
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (N : ℕ) (i j : Fin N) :
    Integrable (fun x : Fin N → E => f (x i) * g (x j))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, f (x i) * g (x j) ∂(Measure.pi (fun _ : Fin N => μ))) =
        if i = j then ∫ x, f x * g x ∂μ
          else (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  have hF2 : MemLp (fun x : Fin N → E => f (x i)) 2 ν :=
    hf2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hG2 : MemLp (fun x : Fin N → E => g (x j)) 2 ν :=
    hg2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) j)
  have hprod : MemLp (fun x : Fin N → E => f (x i) * g (x j)) 1 ν :=
    hF2.fun_mul hG2
  refine ⟨hprod.integrable le_rfl, ?_⟩
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact integral_comp_eval_pi μ (fun x => f x * g x)
      (hf2.aestronglyMeasurable.mul hg2.aestronglyMeasurable) N i
  · rw [ite_eq_right hij]
    let X : Fin N → E → ℝ := fun k => if k = i then f else g
    have hX : ∀ k : Fin N, AEMeasurable (X k) μ := by
      intro k
      by_cases hk : k = i
      · simpa [X, hk] using hf2.aemeasurable
      · simpa [X, hk] using hg2.aemeasurable
    have hind : iIndepFun (fun k (x : Fin N → E) => X k (x k)) ν :=
      iIndepFun_pi (μ := fun _ : Fin N => μ) hX
    have hfg : IndepFun (fun x : Fin N → E => f (x i))
        (fun x : Fin N → E => g (x j)) ν := by
      have hji : j ≠ i := fun h => hij h.symm
      simpa [X, hji] using hind.indepFun hij
    have h := hfg.integral_mul_eq_mul_integral
      hF2.aestronglyMeasurable hG2.aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [integral_comp_eval_pi μ f hf2.aestronglyMeasurable N i,
      integral_comp_eval_pi μ g hg2.aestronglyMeasurable N j] at h
    exact h

/-- The normalized sum of `f` is orthogonal to every coordinate `g(x_i)` when `f` and `g` are
centered and `∫ f g dμ = 0`. -/
theorem integral_normalizedSum_mul_comp_eval_pi
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hg0 : ∫ x, g x ∂μ = 0)
    (hfg0 : ∫ x, f x * g x ∂μ = 0) (N : ℕ) (hN : 0 < N) (i : Fin N) :
    Integrable (fun x : Fin N → E => ((∑ k, f (x k)) / Real.sqrt N) * g (x i))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, ((∑ k, f (x k)) / Real.sqrt N) * g (x i)
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let R : (Fin N → E) → ℝ := fun x => ∑ k, f (x k) * g (x i)
  have hprod (k : Fin N) : Integrable (fun x : Fin N → E => f (x k) * g (x i)) ν :=
    (integral_mul_comp_eval_pi μ f g hf2 hg2 N k i).1
  have hRint : Integrable R ν :=
    integrable_finsetSum Finset.univ (fun k _ => hprod k)
  have hzero (k : Fin N) : (∫ x : Fin N → E, f (x k) * g (x i) ∂ν) = 0 := by
    rw [(integral_mul_comp_eval_pi μ f g hf2 hg2 N k i).2]
    by_cases hki : k = i
    · rw [ite_eq_left hki, hfg0]
    · rw [ite_eq_right hki, hf0, hg0]
      simp
  have hR0 : (∫ x, R x ∂ν) = 0 := by
    calc
      _ = ∑ k : Fin N, ∫ x, f (x k) * g (x i) ∂ν :=
        integral_finsetSum _ (fun k _ => hprod k)
      _ = 0 := by simp_rw [hzero]; simp
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have heq (x : Fin N → E) :
      ((∑ k, f (x k)) / Real.sqrt N) * g (x i) = R x / Real.sqrt N := by
    dsimp [R]
    rw [← Finset.sum_mul]
    field_simp [hsqrt]
  have heqfun : (fun x : Fin N → E => ((∑ k, f (x k)) / Real.sqrt N) * g (x i)) =
      (fun x => R x / Real.sqrt N) := funext heq
  rw [heqfun]
  refine ⟨hRint.div_const _, ?_⟩
  rw [integral_div, hR0]
  simp

end MeasurableSpace

section MeasurableSpace

variable {A B : Type*}
  [MeasurableSpace A] [MeasurableSpace B]

/-- **Independent sums.** Under `μ ⊗ ν`, centered `X ∈ L²(μ)` and `Y ∈ L²(ν)` give a centered
sum `X + Y` with second moment `∫ X² dμ + ∫ Y² dν`. -/
theorem prod_add_moments
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : A → ℝ) (Y : B → ℝ) (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 ν)
    (hX0 : ∫ x, X x ∂μ = 0) (hY0 : ∫ y, Y y ∂ν = 0) :
    MemLp (fun p : A × B => X p.1 + Y p.2) 2 (μ.prod ν) ∧
      (∫ p : A × B, X p.1 + Y p.2 ∂(μ.prod ν)) = 0 ∧
      (∫ p : A × B, (X p.1 + Y p.2) ^ 2 ∂(μ.prod ν)) =
        (∫ x, X x ^ 2 ∂μ) + (∫ y, Y y ^ 2 ∂ν) := by
  have hXfirst : MemLp (fun p : A × B => X p.1) 2 (μ.prod ν) := hX2.comp_fst ν
  have hYsecond : MemLp (fun p : A × B => Y p.2) 2 (μ.prod ν) := hY2.comp_snd μ
  have hsum2 : MemLp (fun p : A × B => X p.1 + Y p.2) 2 (μ.prod ν) :=
    hXfirst.add hYsecond
  have hsum0 : (∫ p : A × B, X p.1 + Y p.2 ∂(μ.prod ν)) = 0 := by
    rw [integral_add (hXfirst.integrable one_le_two) (hYsecond.integrable one_le_two),
      integral_fun_fst X, integral_fun_snd Y, hX0, hY0]
    simp
  refine ⟨hsum2, hsum0, ?_⟩
  have hv := variance_add_prod hX2 hY2
  rw [variance_eq_sub hsum2, hsum0, variance_eq_sub hX2, variance_eq_sub hY2,
    hX0, hY0] at hv
  simpa only [Pi.pow_apply, zero_pow (by norm_num : 2 ≠ 0), sub_zero] using hv

/-- Under `μ ⊗ ν`, `∫ (X + Y) Z = 0` when `∫ X Z dμ = 0` and `Y` is centered. -/
theorem integral_prod_add_mul_eq_zero
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X Z : A → ℝ) (Y : B → ℝ)
    (hX2 : MemLp X 2 μ) (hZ2 : MemLp Z 2 μ) (hY2 : MemLp Y 2 ν)
    (hXZ0 : ∫ x, X x * Z x ∂μ = 0) (hY0 : ∫ y, Y y ∂ν = 0) :
    Integrable (fun p : A × B => (X p.1 + Y p.2) * Z p.1) (μ.prod ν) ∧
      (∫ p : A × B, (X p.1 + Y p.2) * Z p.1 ∂(μ.prod ν)) = 0 := by
  have hXfirst : MemLp (fun p : A × B => X p.1) 2 (μ.prod ν) := hX2.comp_fst ν
  have hZfirst : MemLp (fun p : A × B => Z p.1) 2 (μ.prod ν) := hZ2.comp_fst ν
  have hYsecond : MemLp (fun p : A × B => Y p.2) 2 (μ.prod ν) := hY2.comp_snd μ
  have hXZ : MemLp (fun p : A × B => X p.1 * Z p.1) 1 (μ.prod ν) :=
    hXfirst.fun_mul hZfirst
  have hZY : MemLp (fun p : A × B => Z p.1 * Y p.2) 1 (μ.prod ν) :=
    hZfirst.fun_mul hYsecond
  have hmixed : MemLp (fun p : A × B => (X p.1 + Y p.2) * Z p.1) 1 (μ.prod ν) :=
    (hXfirst.add hYsecond).fun_mul hZfirst
  refine ⟨hmixed.integrable le_rfl, ?_⟩
  have heq : (fun p : A × B => (X p.1 + Y p.2) * Z p.1) =
      (fun p => X p.1 * Z p.1 + Z p.1 * Y p.2) := by
    funext p
    ring
  rw [heq, integral_add (hXZ.integrable le_rfl) (hZY.integrable le_rfl),
    integral_fun_fst (fun x => X x * Z x), integral_prod_mul Z Y, hXZ0, hY0]
  simp

end MeasurableSpace

end FunctionalInequalities.Probability

/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Law
public import LeanPool.KLS.FunctionalInequalities.Probability.Product
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic

/-!
# Second moments of the BKL suspension

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 28: for `f` satisfying
(108) and an isotropic centered `μ`, the coordinates of the joint law of `(S, X_1, …, X_N)` are
centered and uncorrelated with unit variance. This module proves the scalar pieces: the copy
statistic `F_N`, the suspension coordinate `S = (F_N + η)/σ_β`, and their cross moments with the
copies, and assembles them into the second moments and the isotropy of the joint law
(`isotropic_jointLaw`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-- The copy statistic `F_N = (Σ_i f(X_i))/√N` has mean `0` and second moment `1`. -/
theorem copyStat_moments {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) :
    MemLp (copyStat f N) 2 (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x, copyStat f N x ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
      (∫ x, (copyStat f N x) ^ 2 ∂(Measure.pi (fun _ : Fin N => μ))) = 1 := by
  exact pi_normalizedSum_moments μ f hf2 hf0 hf1 N hN

/-- Linear functionals of a law with finite second moment are in `L²`. -/
private theorem memLp_inner {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => ⟪u, x⟫) 2 μ := by
  simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2

/-- Linear functionals of a centered law are centered. -/
private theorem integral_inner_eq_zero {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (u : EuclideanSpace ℝ (Fin n)) : (∫ x, ⟪u, x⟫ ∂μ) = 0 := by
  calc
    _ = ⟪u, ∫ x, x ∂μ⟫ :=
      (innerSL ℝ u).integral_comp_comm (hμ2.integrable one_le_two)
    _ = 0 := by rw [hμ0]; simp

/-- `E[F_N ⟪u, X_i⟫] = 0` when `f` is orthogonal to the linear functions. -/
theorem integral_copyStat_mul_inner {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x : Fin N → EuclideanSpace ℝ (Fin n) => copyStat f N x * ⟪u, x i⟫)
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ (Fin n), copyStat f N x * ⟪u, x i⟫
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 := by
  have hfg : (∫ x, f x * ⟪u, x⟫ ∂μ) = 0 := by
    calc
      _ = ∫ x, ⟪u, x⟫ * f x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
      _ = 0 := hfx u
  exact integral_normalizedSum_mul_comp_eval_pi μ f (fun x => ⟪u, x⟫) hf2
    (memLp_inner μ hμ2 u) hf0 (integral_inner_eq_zero μ hμ2 hμ0 u) hfg N hN i

/-- `E[⟪u, X_i⟫ ⟪v, X_j⟫] = δ_ij ⟪u, v⟫` for independent isotropic copies. -/
theorem integral_inner_mul_inner_pi {n N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n),
      ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    (i j : Fin N) (u v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x : Fin N → EuclideanSpace ℝ (Fin n) => ⟪u, x i⟫ * ⟪v, x j⟫)
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ (Fin n), ⟪u, x i⟫ * ⟪v, x j⟫
        ∂(Measure.pi (fun _ : Fin N => μ))) = if i = j then ⟪u, v⟫ else 0 := by
  classical
  have h := integral_mul_comp_eval_pi μ (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
    (memLp_inner μ hμ2 u) (memLp_inner μ hμ2 v) N i j
  refine ⟨h.1, ?_⟩
  rw [h.2, hμcov u v, integral_inner_eq_zero μ hμ2 hμ0 u, integral_inner_eq_zero μ hμ2 hμ0 v]
  simp

/-- **The suspension coordinate** `S = (F_N + η)/σ_β` has mean `0` and second moment `1`. -/
theorem scalar_moments {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
    (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2) :
    MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      (copyStat f N q.1 + q.2) / sigma β) 2
      ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        (copyStat f N q.1 + q.2) / sigma β
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 0 ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((copyStat f N q.1 + q.2) / sigma β) ^ 2
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 1 := by
  have hF := copyStat_moments hN μ f hf2 hf0 hf1
  have hηL2 : MemLp (fun s : ℝ => s) 2 (laplaceMeasure β) :=
    (memLp_two_iff_integrable_sq_norm hη1.aestronglyMeasurable).mpr
      (by simpa only [Real.norm_eq_abs, sq_abs] using hη2)
  have hsum := prod_add_moments (Measure.pi (fun _ : Fin N => μ))
    (laplaceMeasure β) (copyStat f N) (fun s : ℝ => s) hF.1 hηL2 hF.2.1 hη0
  have hβsq : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hsumpos : 0 < 1 + 2 / β ^ 2 := add_pos (by norm_num) (div_pos (by norm_num) hβsq)
  have hσsq : (sigma β) ^ 2 = 1 + 2 / β ^ 2 := by
    exact Real.sq_sqrt hsumpos.le
  have hS2 : MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      (copyStat f N q.1 + q.2) / sigma β) 2
      ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) := by
    simpa [div_eq_mul_inv] using hsum.1.mul_const (sigma β)⁻¹
  refine ⟨hS2, ?_, ?_⟩
  · rw [integral_div, hsum.2.1]
    simp
  · simp_rw [div_pow]
    rw [integral_div, hsum.2.2, hF.2.2, hηv, hσsq]
    exact div_self hsumpos.ne'

/-- `E[S ⟪u, X_i⟫] = 0`. -/
theorem integral_scalar_mul_inner {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
    (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫)
      ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 0 := by
  have hF := copyStat_moments hN μ f hf2 hf0 hf1
  have hS := scalar_moments hN μ f hf2 hf0 hf1 hβ hη1 hη2 hη0 hηv
  have hZμ2 : MemLp (fun x => ⟪u, x⟫) 2 μ := by
    simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2
  have hZ2 : MemLp (fun x : Fin N → EuclideanSpace ℝ (Fin n) => ⟪u, x i⟫) 2
      (Measure.pi (fun _ : Fin N => μ)) :=
    hZμ2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hZprod2 := hZ2.comp_fst (laplaceMeasure β)
  have hprod : MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫) 1
      ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) :=
    hS.1.fun_mul hZprod2
  have hηL2 : MemLp (fun s : ℝ => s) 2 (laplaceMeasure β) :=
    (memLp_two_iff_integrable_sq_norm hη1.aestronglyMeasurable).mpr
      (by simpa only [Real.norm_eq_abs, sq_abs] using hη2)
  have hCX := integral_copyStat_mul_inner hN μ hμ2 hμ0 f hf2 hf0 hfx i u
  have hbase := integral_prod_add_mul_eq_zero (Measure.pi (fun _ : Fin N => μ)) (laplaceMeasure β)
    (copyStat f N) (fun x => ⟪u, x i⟫) (fun s : ℝ => s) hF.1 hZ2 hηL2 hCX.2 hη0
  refine ⟨hprod.integrable le_rfl, ?_⟩
  have heq : (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫) =
      (fun q => ((copyStat f N q.1 + q.2) * ⟪u, q.1 i⟫) / sigma β) := by
    funext q
    ring
  rw [heq, integral_div, hbase.2]
  simp


/-! ### The joint law is isotropic -/

private theorem innerCoordinates {I : Type*} [Fintype I]
    (u p : EuclideanSpace ℝ I) : ⟪u, p⟫ = ∑ i, u i * p i := by
  simpa using ((EuclideanSpace.basisFun I ℝ).sum_inner_mul_inner u p).symm

private theorem euclideanMomentsFromCoordinates {A I : Type*} [MeasurableSpace A] [Fintype I]
    [DecidableEq I] (ν : Measure A) [IsProbabilityMeasure ν] (Y : A → EuclideanSpace ℝ I)
    (hY : Measurable Y) (h2 : ∀ i, MemLp (fun x => Y x i) 2 ν) (h0 : ∀ i, (∫ x, Y x i ∂ν) = 0)
    (hcov : ∀ i j, (∫ x, Y x i * Y x j ∂ν) = if i = j then 1 else 0) :
    MemLp Y 2 ν ∧
      (∫ x, Y x ∂ν) = 0 ∧ ∀ u v : EuclideanSpace ℝ I, (∫ x, ⟪u, Y x⟫ * ⟪v, Y x⟫ ∂ν) = ⟪u, v⟫ := by
  classical
  have hsq (i : I) : Integrable (fun x => (Y x i) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (h2 i).aestronglyMeasurable).mp (h2 i)
  have hY2 : MemLp Y 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr
    simpa only [EuclideanSpace.real_norm_sq_eq] using
      integrable_finsetSum Finset.univ (fun i _ => hsq i)
  have hY0 : (∫ x, Y x ∂ν) = 0 := by
    ext i
    have hi :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ I →L[ℝ] ℝ).integral_comp_comm
        (hY2.integrable one_le_two)
    change (∫ x, Y x i ∂ν) = (∫ x, Y x ∂ν) i at hi
    rw [← hi, h0 i]
    rfl
  refine ⟨hY2, hY0, ?_⟩
  intro u v
  have hprod (i j : I) : Integrable (fun x => Y x i * Y x j) ν := by
    have h : MemLp (fun x => Y x i * Y x j) 1 ν := (h2 i).fun_mul (h2 j)
    exact h.integrable le_rfl
  have hterm (i j : I) : Integrable (fun x => (u i * v j) * (Y x i * Y x j)) ν :=
    (hprod i j).const_mul _
  have hexpand (x : A) :
    ⟪u, Y x⟫ * ⟪v, Y x⟫ = ∑ i : I, ∑ j : I, (u i * v j) * (Y x i * Y x j) := by
    rw [innerCoordinates, innerCoordinates, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∫ x, ⟪u, Y x⟫ * ⟪v, Y x⟫ ∂ν) = ∫ x, ∑ i : I, ∑ j : I, (u i * v j) * (Y x i * Y x j) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i : I, ∑ j : I, ∫ x, (u i * v j) * (Y x i * Y x j) ∂ν := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum _ (fun j _ => hterm i j)
    _ = ∑ i : I, ∑ j : I, (u i * v j) * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, hcov i j]
    _ = ∑ i : I, u i * v i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ = ⟪u, v⟫ := (innerCoordinates u v).symm




/--
**Second moments of the joint law** (BKL p. 28, isotropy from (108)): under the explicit Laplace
moment data, the joint law of `(S, X₁, …, X_N)` has finite second moment, mean `0` and identity
covariance.
-/
theorem jointLaw_moments_of_laplace {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ)
    (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
    (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2) :
    MemLp id 2 (jointLaw μ f β (sigma β) N) ∧
      ∫ p, p ∂(jointLaw μ f β (sigma β) N) = 0 ∧
        ∀ u v : JointSpace N n, ∫ p, ⟪u, p⟫ * ⟪v, p⟫ ∂(jointLaw μ f β (sigma β) N) = ⟪u, v⟫ := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let P := ν.prod (laplaceMeasure β)
  let Y : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) → JointSpace N n := embed f (sigma β) N
  have hYmeas : Measurable Y := by
    have hg :
      Measurable
        (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ => fun o : Option (Fin N × Fin n) =>
          o.elim ((copyStat f N q.1 + q.2) / sigma β) (fun ij => (q.1 ij.1).ofLp ij.2)) := by
      rw [measurable_pi_iff]
      intro o
      cases o with
      | none => unfold copyStat; measurability
      | some ij => measurability
    exact (WithLp.measurable_toLp 2 _).comp hg
  have hS := scalar_moments hN μ f hf2 hf0 hf1 hβ hη1 hη2 hη0 hηv
  have hcoord2 (o : Option (Fin N × Fin n)) : MemLp (fun q => Y q o) 2 P := by
    cases o with
    | none => exact hS.1
    | some
      ij =>
      have hB2 : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x ij.2) 2 μ := by
        exact (EuclideanSpace.proj ij.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp_memLp' hμ2
      have hXi2 : MemLp (fun x : Fin N → EuclideanSpace ℝ (Fin n) => x ij.1 ij.2) 2 ν :=
        hB2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) ij.1)
      exact hXi2.comp_fst (laplaceMeasure β)
  have hcoord0 (o : Option (Fin N × Fin n)) : (∫ q, Y q o ∂P) = 0 := by
    cases o with
    | none => exact hS.2.1
    | some
      ij =>
      have hB2 : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x ij.2) 2 μ :=
        (EuclideanSpace.proj ij.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp_memLp' hμ2
      have hB0 : (∫ x : EuclideanSpace ℝ (Fin n), x ij.2 ∂μ) = 0 := by
        have h :=
          (EuclideanSpace.proj ij.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).integral_comp_comm
            (hμ2.integrable one_le_two)
        simpa [hμ0] using h
      have hXi0 : (∫ x : Fin N → EuclideanSpace ℝ (Fin n), x ij.1 ij.2 ∂ν) = 0 := by
        rw [Probability.integral_comp_eval_pi μ (fun x => x ij.2) hB2.aestronglyMeasurable N
            ij.1]
        exact hB0
      change (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ, q.1 ij.1 ij.2 ∂P) = 0
      rw [integral_fun_fst (fun x : Fin N → EuclideanSpace ℝ (Fin n) => x ij.1 ij.2), hXi0]
      simp
  have hcoordcov (o r : Option (Fin N × Fin n)) :
    (∫ q, Y q o * Y q r ∂P) = if o = r then 1 else 0 := by
    cases o with
    | none =>
      cases r with
      |
        none =>
        change
          (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
              ((copyStat f N q.1 + q.2) / sigma β) * ((copyStat f N q.1 + q.2) / sigma β) ∂P) =
            1
        simpa only [pow_two] using hS.2.2
      | some
        ij =>
        have h :=
          integral_scalar_mul_inner hN μ hμ2 hμ0 f hf2 hf0 hf1 hfx hβ hη1 hη2 hη0 hηv ij.1
            (EuclideanSpace.basisFun (Fin n) ℝ ij.2)
        change
          (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
              ((copyStat f N q.1 + q.2) / sigma β) * q.1 ij.1 ij.2 ∂P) =
            0
        simpa only [EuclideanSpace.basisFun_inner] using h.2
    | some ij =>
      cases r with
      |
        none =>
        have h :=
          integral_scalar_mul_inner hN μ hμ2 hμ0 f hf2 hf0 hf1 hfx hβ hη1 hη2 hη0 hηv ij.1
            (EuclideanSpace.basisFun (Fin n) ℝ ij.2)
        change
          (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
              q.1 ij.1 ij.2 * ((copyStat f N q.1 + q.2) / sigma β) ∂P) =
            0
        calc
          _ =
              ∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
                ((copyStat f N q.1 + q.2) / sigma β) * q.1 ij.1 ij.2 ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
          _ = 0 := by simpa only [EuclideanSpace.basisFun_inner] using h.2
      | some kl =>
        let b := EuclideanSpace.basisFun (Fin n) ℝ
        have h := integral_inner_mul_inner_pi μ hμ2 hμ0 hμcov ij.1 kl.1 (b ij.2) (b kl.2)
        have hraw :
          (∫ x : Fin N → EuclideanSpace ℝ (Fin n), x ij.1 ij.2 * x kl.1 kl.2 ∂ν) =
            if ij.1 = kl.1 then ⟪b ij.2, b kl.2⟫ else 0 := by
          simpa only [b, EuclideanSpace.basisFun_inner] using h.2
        change
          (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ, q.1 ij.1 ij.2 * q.1 kl.1 kl.2 ∂P) =
            if some ij = some kl then 1 else 0
        rw [integral_fun_fst
            (fun x : Fin N → EuclideanSpace ℝ (Fin n) => x ij.1 ij.2 * x kl.1 kl.2),
          hraw]
        have hmass : (laplaceMeasure β).real Set.univ = 1 := by simp
        rw [hmass, one_smul]
        rw [b.inner_eq_ite]
        by_cases hik : ij.1 = kl.1 <;> by_cases hjl : ij.2 = kl.2 <;>
          simp [Prod.ext_iff, hik, hjl]
  have hbase := euclideanMomentsFromCoordinates P Y hYmeas hcoord2 hcoord0 hcoordcov
  have hmap2 : MemLp id 2 (P.map Y) := by
    apply (memLp_map_measure_iff (continuous_id.aestronglyMeasurable) hYmeas.aemeasurable).mpr
    exact hbase.1
  refine ⟨hmap2, ?_, ?_⟩
  · change (∫ p : JointSpace N n, p ∂P.map Y) = 0
    have hm : AEStronglyMeasurable (fun p : JointSpace N n => p) (P.map Y) :=
      continuous_id.aestronglyMeasurable
    exact (integral_map hYmeas.aemeasurable hm).trans hbase.2.1
  · intro u v
    change (∫ p : JointSpace N n, ⟪u, p⟫ * ⟪v, p⟫ ∂P.map Y) = ⟪u, v⟫
    have hm : AEStronglyMeasurable (fun p : JointSpace N n => ⟪u, p⟫ * ⟪v, p⟫) (P.map Y) := by
      exact
        (show Continuous (fun p : JointSpace N n => ⟪u, p⟫ * ⟪v, p⟫) by
            fun_prop).aestronglyMeasurable
    rw [integral_map hYmeas.aemeasurable hm]
    exact hbase.2.2 u v

/-- **Isotropy of the joint law** (BKL p. 28), with the Laplace data discharged by
`laplaceMeasure_moments`. -/
theorem isotropic_jointLaw {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) {β : ℝ} (hβ : 0 < β) :
    FunctionalInequalities.KLS.Isotropic
      (⟨jointLaw μ f β (sigma β) N,
        isProbabilityMeasure_jointLaw_of_pos μ hf hβ (sigma β) N⟩ :
        ProbabilityMeasure (JointSpace N n)) := by
  have : IsProbabilityMeasure (laplaceMeasure β) := isProbabilityMeasure_laplaceMeasure hβ
  obtain ⟨hη1, hη2, hη0, hηv⟩ := laplaceMeasure_moments hβ
  have h := jointLaw_moments_of_laplace hN μ hμ2 hμ0 hμcov hf hf2 hf0 hf1 hfx
    hβ hη1 hη2 hη0 hηv
  exact FunctionalInequalities.KLS.isotropic_of_moments
    (⟨jointLaw μ f β (sigma β) N,
      isProbabilityMeasure_jointLaw_of_pos μ hf hβ (sigma β) N⟩ :
      ProbabilityMeasure (JointSpace N n)) h.1 h.2.1 h.2.2

end FunctionalInequalities.KLS.LogConcave.Suspension

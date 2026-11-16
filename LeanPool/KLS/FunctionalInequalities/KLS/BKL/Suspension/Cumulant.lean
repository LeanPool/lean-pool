/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Law
public import LeanPool.KLS.FunctionalInequalities.Probability.Product
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Coefficients

/-!
# Cumulants of the suspension (BKL Proposition 7.1)

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 29: the mixed cumulants of
the joint law `ν` of `(S, X₁, …, X_N)` and the Hilbert–Schmidt lower bound that follows from (112),
`|κ(e₀)|² ≥ (d!)²/σ² |T_d f|²`.

* `sum_sq_cumulant_ge_of_entries`: if the entries satisfy (112), the lower bound holds; the copy
  blocks are selected by `card_mul_sq_mul_sum_sq_le_of_blocks`.

* `lintegral_exp_inner_jointLaw`, `joint_integrability_factorization` and
  `logLaplace_jointLaw_factorization`: the joint Laplace transform factorizes, in extended,
  real and logarithmic form, with every factor's integrability derived from the joint one.

(111) and (112) themselves are not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-- **Hilbert–Schmidt lower bound from (112)** (BKL p. 29). -/
theorem sum_sq_cumulant_ge_of_entries {n N : ℕ} (hN : 0 < N) (ν : Measure (JointSpace N n))
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) {σ : ℝ} (hσ : 0 < σ)
    {d : ℕ} (hd : 1 ≤ d)
    (h112 : ∀ (I : Fin d → Fin N) (J : Fin d → Fin n),
      cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (some (I k, J k)) 1) =
        if ∀ k k', I k = I k' then
          (d.factorial : ℝ) / (σ * Real.sqrt N) *
            taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
        else 0) :
    (d.factorial : ℝ) ^ 2 / σ ^ 2 *
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f d)‖ ^ 2 ≤
      ∑ K : Fin d → Option (Fin N × Fin n),
        cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (K k) 1) ^ 2 := by
  classical
  have h := card_mul_sq_mul_sum_sq_le_of_blocks (κ := Fin N) (ι := Fin n) (by omega)
    (fun K => cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
      EuclideanSpace.single (K k) 1))
    ((d.factorial : ℝ) / (σ * Real.sqrt N))
    (fun J => taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
    (fun i j => by simpa using h112 (fun _ => i) j)
  have hnorm : ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f d)‖ ^ 2 =
      ∑ J : Fin d → Fin n,
        (taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [coordTensor_apply]
  have hsqrt : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hc : (Fintype.card (Fin N) : ℝ) * ((d.factorial : ℝ) / (σ * Real.sqrt N)) ^ 2 =
      (d.factorial : ℝ) ^ 2 / σ ^ 2 := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Fintype.card_fin, div_pow, mul_pow, hsqrt]
    field_simp
  rw [hc] at h
  rw [hnorm]
  exact h

open scoped RealInnerProductSpace

/-- **Factorization of the joint Laplace transform** (BKL p. 28), in extended nonnegative form:
`∫⁻ e^{⟪z, p⟫} dν = (∫⁻ e^{(z₀/σ) s} dη_β) · Π_i ∫⁻ e^{(z₀/(σ√N)) f + ⟪z_i, x⟫} dμ`. -/
theorem lintegral_exp_inner_jointLaw {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [SigmaFinite μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (β σ : ℝ)
    [SigmaFinite (laplaceMeasure β)] (z : JointSpace N n) :
    ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂(jointLaw μ f β σ N) =
      (∫⁻ s, ENNReal.ofReal (Real.exp (z none / σ * s)) ∂laplaceMeasure β) *
        ∏ i : Fin N, ∫⁻ x, ENNReal.ofReal (Real.exp (z none / (σ * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫)) ∂μ := by
    classical
    have hinner :
        ∀ (x : Fin N → EuclideanSpace ℝ (Fin n)) (s : ℝ),
          ⟪z, embed f σ N (x, s)⟫ =
            z none / σ * s +
              ∑ i : Fin N,
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫) := by
      intro x s
      simp only [embed, copyStat, PiLp.inner_apply, Fintype.sum_option,
        Fintype.sum_prod_type, Option.elim_none, Option.elim_some,
        Real.inner_apply, div_eq_mul_inv, mul_inv_rev]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hintegrand :
        ∀ (x : Fin N → EuclideanSpace ℝ (Fin n)) (s : ℝ),
          ENNReal.ofReal (Real.exp ⟪z, embed f σ N (x, s)⟫) =
            ENNReal.ofReal (Real.exp (z none / σ * s)) *
              ∏ i : Fin N, ENNReal.ofReal (Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) := by
      intro x s
      rw [hinner, Real.exp_add, Real.exp_sum,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hfin :
          ENNReal.ofReal
              (∏ i : Fin N, Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) =
            ∏ i : Fin N, ENNReal.ofReal (Real.exp
                (z none / (σ * Real.sqrt N) * f (x i) +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                      EuclideanSpace ℝ (Fin n)), x i⟫)) := by
        simpa using
          (ENNReal.ofReal_prod_of_nonneg
            (s := (Finset.univ : Finset (Fin N)))
            (fun i _ => (Real.exp_pos
              (z none / (σ * Real.sqrt N) * f (x i) +
                ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
                    EuclideanSpace ℝ (Fin n)), x i⟫)).le))
      rw [hfin]
    have hmeas :
        Measurable (embed f σ N) := by
      have hg :
          Measurable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
            fun o : Option (Fin N × Fin n) =>
              o.elim ((copyStat f N q.1 + q.2) / σ)
                (fun ij => (q.1 ij.1).ofLp ij.2)) := by
        rw [measurable_pi_iff]
        intro o
        cases o with
        | none =>
            unfold copyStat
            measurability
        | some ij =>
            measurability
      unfold embed
      exact (WithLp.measurable_toLp 2 _).comp hg
    rw [jointLaw, lintegral_map (by fun_prop) hmeas]
    simp_rw [hintegrand]
    let gi : Fin N → EuclideanSpace ℝ (Fin n) → ENNReal := fun i x =>
      ENNReal.ofReal (Real.exp
        (z none / (σ * Real.sqrt N) * f x +
          ⟪(WithLp.toLp 2 fun j => z (some (i, j)) :
              EuclideanSpace ℝ (Fin n)), x⟫))
    let G : (Fin N → EuclideanSpace ℝ (Fin n)) → ENNReal := fun x =>
      ∏ i : Fin N, gi i (x i)
    let H : ℝ → ENNReal := fun s =>
      ENNReal.ofReal (Real.exp (z none / σ * s))
    have hG : Measurable G := by
      dsimp [G, gi]
      measurability
    have hH : Measurable H := by
      dsimp [H]
      fun_prop
    have hpi :
        (∫⁻ x, G x ∂(Measure.pi fun _ : Fin N => μ)) =
          ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
      simpa [G] using
        (Probability.lintegral_pi_prod_fin μ N gi (by
          intro i
          dsimp [gi]
          measurability))
    have hmain :
        (∫⁻ a, H a.2 * G a.1
            ∂((Measure.pi fun _ : Fin N => μ).prod (laplaceMeasure β))) =
          (∫⁻ s, H s ∂laplaceMeasure β) *
            ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
      calc
        (∫⁻ a, H a.2 * G a.1
            ∂((Measure.pi fun _ : Fin N => μ).prod (laplaceMeasure β))) =
            ∫⁻ a, G a.1 * H a.2
              ∂((Measure.pi fun _ : Fin N => μ).prod (laplaceMeasure β)) :=
          lintegral_congr fun a => mul_comm _ _
        _ = (∫⁻ x, G x ∂(Measure.pi fun _ : Fin N => μ)) *
            (∫⁻ s, H s ∂laplaceMeasure β) :=
          lintegral_prod_mul hG.aemeasurable hH.aemeasurable
        _ = (∫⁻ s, H s ∂laplaceMeasure β) *
            ∏ i : Fin N, ∫⁻ x, gi i x ∂μ := by
          rw [hpi, mul_comm]
    simpa [G, H, gi] using hmain

private theorem lintegral_exp_pos_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Measurable g) :
    0 < ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂μ := by
  have hs : Function.support (fun x => ENNReal.ofReal (Real.exp (g x))) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos (g x))).ne'
  rw [lintegral_pos_iff_support (hg.exp.ennreal_ofReal), hs, measure_univ]
  norm_num

private theorem fin_prod_factor_ne_top {ι : Type*} [Fintype ι]
    (b : ι → ENNReal) (hb : ∀ i, b i ≠ 0) (hprod : (∏ i, b i) ≠ ⊤) (i : ι) :
    b i ≠ ⊤ := by
  classical
  have hrest : (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  have hmul : (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) * b i ≠ ⊤ := by
    rw [Finset.prod_erase_mul _ _ (by simp)]
    exact hprod
  exact (ENNReal.lt_top_of_mul_ne_top_right hmul hrest).ne

/-- Joint integrability forces every strictly positive Laplace product factor to be finite. -/
theorem joint_integrability_factorization {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {β : ℝ}
    (hβ : 0 < β) (_hN : 0 < N) (z : JointSpace N n)
    (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (jointLaw μ f β (sigma β) N)) :
    Integrable (fun s : ℝ => Real.exp (z none / sigma β * s)) (laplaceMeasure β) ∧
      (∀ i : Fin N,
          Integrable
            (fun x =>
              Real.exp
                (z none / (sigma β * Real.sqrt N) * f x +
                  ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫))
            μ) ∧
        (∫ p, Real.exp ⟪z, p⟫ ∂jointLaw μ f β (sigma β) N) =
          (∫ s : ℝ, Real.exp (z none / sigma β * s) ∂laplaceMeasure β) *
            ∏ i : Fin N,
              ∫ x,
                Real.exp
                  (z none / (sigma β * Real.sqrt N) * f x +
                    ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)),
                      x⟫) ∂μ := by
  classical
  let _ : IsProbabilityMeasure (laplaceMeasure β) := isProbabilityMeasure_laplaceMeasure hβ
  let noise : ℝ → ℝ := fun s => z none / sigma β * s
  let copy : Fin N → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    z none / (sigma β * Real.sqrt N) * f x +
      ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫
  let A : ENNReal := ∫⁻ s, ENNReal.ofReal (Real.exp (noise s)) ∂laplaceMeasure β
  let B : Fin N → ENNReal := fun i => ∫⁻ x, ENNReal.ofReal (Real.exp (copy i x)) ∂μ
  let J : ENNReal := ∫⁻ p, ENNReal.ofReal (Real.exp ⟪z, p⟫) ∂jointLaw μ f β (sigma β) N
  have hmNoise : Measurable noise := by dsimp [noise]; fun_prop
  have hmCopy (i : Fin N) : Measurable (copy i) := by dsimp [copy]; measurability
  have hApos : 0 < A := lintegral_exp_pos_probability (laplaceMeasure β) noise hmNoise
  have hBpos (i : Fin N) : 0 < B i := lintegral_exp_pos_probability μ (copy i) (hmCopy i)
  have hJfinite : J ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hInt.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr
      hInt
  have hfactor : J = A * ∏ i, B i := by exact lintegral_exp_inner_jointLaw μ hf β (sigma β) z
  have htotal : A * ∏ i, B i ≠ ⊤ := hfactor.symm ▸ hJfinite
  have hprodNonzero : (∏ i, B i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hBpos i).ne')
  have hAfinite : A ≠ ⊤ := (ENNReal.lt_top_of_mul_ne_top_left htotal hprodNonzero).ne
  have hprodFinite : (∏ i, B i) ≠ ⊤ := (ENNReal.lt_top_of_mul_ne_top_right htotal hApos.ne').ne
  have hBfinite (i : Fin N) : B i ≠ ⊤ :=
    fin_prod_factor_ne_top B (fun i => (hBpos i).ne') hprodFinite i
  have hNoise : Integrable (fun s => Real.exp (noise s)) (laplaceMeasure β) :=
    (lintegral_ofReal_ne_top_iff_integrable hmNoise.exp.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp
      hAfinite
  have hCopy (i : Fin N) : Integrable (fun x => Real.exp (copy i x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hmCopy i).exp.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp
      (hBfinite i)
  have hJreal : J.toReal = ∫ p, Real.exp ⟪z, p⟫ ∂jointLaw μ f β (sigma β) N :=
    (integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
        hInt.aestronglyMeasurable).symm
  have hAreal : A.toReal = ∫ s, Real.exp (noise s) ∂laplaceMeasure β :=
    (integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
        hNoise.aestronglyMeasurable).symm
  have hBreal (i : Fin N) : (B i).toReal = ∫ x, Real.exp (copy i x) ∂μ :=
    (integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
        (hCopy i).aestronglyMeasurable).symm
  have hreal := congrArg ENNReal.toReal hfactor
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, hJreal, hAreal] at hreal
  simp_rw [hBreal] at hreal
  exact ⟨hNoise, hCopy, hreal⟩

/-- The real logarithmic Laplace factorization at any genuinely integrable joint parameter. -/
theorem logLaplace_jointLaw_factorization {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (hN : 0 < N) (z : JointSpace N n)
    (hInt : Integrable (fun p => Real.exp ⟪z, p⟫) (jointLaw μ f β (sigma β) N)) :
    FunctionalInequalities.Analysis.BakryEmery.logLaplace (jointLaw μ f β (sigma β) N) z =
      Real.log (∫ s : ℝ, Real.exp (z none / sigma β * s) ∂laplaceMeasure β) +
        ∑ i : Fin N, Real.log (∫ x, Real.exp
          (z none / (sigma β * Real.sqrt N) * f x +
            ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ) := by
  let _ : IsProbabilityMeasure (laplaceMeasure β) := isProbabilityMeasure_laplaceMeasure hβ
  obtain ⟨hNoise, hCopy, hreal⟩ := joint_integrability_factorization μ hf hβ hN z hInt
  have hNoisepos : 0 < ∫ s : ℝ, Real.exp (z none / sigma β * s) ∂laplaceMeasure β :=
    integral_exp_pos hNoise
  have hCopypos (i : Fin N) : 0 < ∫ x, Real.exp
      (z none / (sigma β * Real.sqrt N) * f x +
        ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ :=
    integral_exp_pos (hCopy i)
  have hprod : (∏ i : Fin N, ∫ x, Real.exp
      (z none / (sigma β * Real.sqrt N) * f x +
        ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hCopypos i).ne')
  rw [FunctionalInequalities.Analysis.BakryEmery.logLaplace, hreal,
    Real.log_mul hNoisepos.ne' hprod, Real.log_prod (fun i _ => (hCopypos i).ne')]

/-! ### Exponential moments of `f` and of the graph law

The factorization above supplies exponential-moment inputs for the local smoothness of `Λ` in (111).
-/

/-- **Exponential moment of `f` from the joint law.** If the joint law has an exponential moment
`e^{r‖p‖}` and `N > 0`, then `f` has the exponential moment `e^{t|f|}` with
`t = r/(2σ_β√N)` (testing the factorization at `±(r/2) e_none`). -/
theorem exists_f_abs_exponential_moment {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hexp : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N)) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun x => Real.exp (t * |f x|)) μ := by
  let ν := jointLaw μ f β (sigma β) N
  have hσ : 0 < sigma β := by
    unfold sigma
    apply Real.sqrt_pos.mpr
    positivity
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  let t := r / (2 * sigma β * Real.sqrt N)
  have ht : 0 < t := div_pos hr (mul_pos (mul_pos (by norm_num) hσ) hroot)
  have hcoef : (r / 2) / (sigma β * Real.sqrt N) = t := by
    dsimp [t]
    rw [div_div]
    congr 1
    ring
  let e0 : JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  let zp : JointSpace N n := (r / 2) • e0
  let zm : JointSpace N n := -zp
  have hhalf : 0 < r / 2 := by positivity
  have he0norm : ‖e0‖ = 1 :=
    (EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ).norm_eq_one none
  have hzp : ‖zp‖ ≤ r := by
    dsimp [zp]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf, he0norm, mul_one]
    linarith
  have hzm : ‖zm‖ ≤ r := by simpa only [zm, norm_neg] using hzp
  have hjoint (z : JointSpace N n) (hz : ‖z‖ ≤ r) :
      Integrable (fun p => Real.exp ⟪z, p⟫) ν := by
    have hm : Continuous (fun p : JointSpace N n => Real.exp ⟪z, p⟫) := by fun_prop
    refine hexp.mono' hm.aestronglyMeasurable ?_
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ((real_inner_le_norm z p).trans
      (mul_le_mul_of_nonneg_right hz (norm_nonneg p)))
  let i0 : Fin N := ⟨0, hN⟩
  have hp := (joint_integrability_factorization μ hf hβ hN zp (hjoint zp hzp)).2.1 i0
  have hn := (joint_integrability_factorization μ hf hβ hN zm (hjoint zm hzm)).2.1 i0
  have hzero : (WithLp.toLp 2 (fun _ : Fin n => (0 : ℝ)) : EuclideanSpace ℝ (Fin n)) = 0 := rfl
  have hplus : Integrable (fun x => Real.exp (t * f x)) μ := by
    simpa [zp, e0, hcoef, hzero] using hp
  have hminus : Integrable (fun x => Real.exp (-t * f x)) μ := by
    simpa [zm, zp, e0, neg_div, hcoef, hzero] using hn
  refine ⟨t, ht, ?_⟩
  refine (hplus.add hminus).mono'
    ((by fun_prop : Measurable (fun x => Real.exp (t * |f x|))).aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases le_total 0 (f x) with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- **Exponential moment of the graph law** `x ↦ (f x, x)` from exponential moments of `|f|` and
`‖x‖` (Cauchy–Schwarz in `L²`, at rate `min a s / 2`). -/
theorem exists_graph_norm_moment_of_local_moments {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hfa : Integrable (fun x => Real.exp (a * |f x|)) μ)
    (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Option (Fin n)) :=
    fun x => WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j
  have hgm : Measurable g := by
    dsimp [g]
    apply (WithLp.measurable_toLp 2 _).comp
    rw [measurable_pi_iff]
    intro o
    cases o with
    | none => exact hf
    | some j => exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  have hsq (x : EuclideanSpace ℝ (Fin n)) : ‖g x‖ ^ 2 = |f x| ^ 2 + ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
    change (f x) ^ 2 + ∑ j : Fin n, (x j) ^ 2 = |f x| ^ 2 + ‖x‖ ^ 2
    rw [sq_abs, ← EuclideanSpace.real_norm_sq_eq]
  have hbound (x : EuclideanSpace ℝ (Fin n)) : ‖g x‖ ≤ |f x| + ‖x‖ := by
    nlinarith [hsq x, norm_nonneg (g x), abs_nonneg (f x), norm_nonneg x,
      mul_nonneg (abs_nonneg (f x)) (norm_nonneg x)]
  let t : ℝ := min a s / 2
  have ht : 0 < t := div_pos (lt_min ha hs) (by norm_num)
  have h2a : 2 * t ≤ a := by dsimp [t]; linarith [min_le_left a s]
  have h2s : 2 * t ≤ s := by dsimp [t]; linarith [min_le_right a s]
  let U : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (t * |f x|)
  let V : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (t * ‖x‖)
  have hmU : AEStronglyMeasurable U μ :=
    (by fun_prop : Measurable U).aestronglyMeasurable
  have hmV : AEStronglyMeasurable V μ :=
    (by fun_prop : Continuous V).aestronglyMeasurable
  have hU2 : Integrable (fun x => U x ^ 2) μ := by
    refine hfa.mono' ((by fun_prop : Measurable (fun x => U x ^ 2)).aestronglyMeasurable) ?_
    filter_upwards [] with x
    dsimp [U]
    rw [abs_of_nonneg (sq_nonneg _), pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      t * |f x| + t * |f x| = (2 * t) * |f x| := by ring
      _ ≤ a * |f x| := mul_le_mul_of_nonneg_right h2a (abs_nonneg _)
  have hV2 : Integrable (fun x => V x ^ 2) μ := by
    refine hxs.mono' ((by fun_prop : Continuous (fun x => V x ^ 2)).aestronglyMeasurable) ?_
    filter_upwards [] with x
    dsimp [V]
    rw [abs_of_nonneg (sq_nonneg _), pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      t * ‖x‖ + t * ‖x‖ = (2 * t) * ‖x‖ := by ring
      _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right h2s (norm_nonneg _)
  have hULp : MemLp U 2 μ := (memLp_two_iff_integrable_sq hmU).mpr hU2
  have hVLp : MemLp V 2 μ := (memLp_two_iff_integrable_sq hmV).mpr hV2
  have hUV : Integrable (fun x => U x * V x) μ := hULp.integrable_mul hVLp
  have hgint : Integrable (fun x => Real.exp (t * ‖g x‖)) μ := by
    refine hUV.mono'
      ((by fun_prop : Measurable (fun x => Real.exp (t * ‖g x‖))).aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [U, V]
    calc
      Real.exp (t * ‖g x‖) ≤ Real.exp (t * (|f x| + ‖x‖)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbound x) ht.le)
      _ = Real.exp (t * |f x|) * Real.exp (t * ‖x‖) := by rw [mul_add, Real.exp_add]
  refine ⟨t, ht, ?_⟩
  exact (integrable_map_measure
    ((by fun_prop : Continuous
      (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))).aestronglyMeasurable)
    hgm.aemeasurable).mpr hgint

/-- The graph law has an exponential moment when the joint law and `μ` do; no moment of `f` is
assumed. -/
theorem exists_graph_norm_moment_from_joint {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r s : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) (hs : 0 < s)
    (hexp : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by
  obtain ⟨a, ha, hfa⟩ := exists_f_abs_exponential_moment μ hf hβ hN hr hexp
  exact exists_graph_norm_moment_of_local_moments μ hf ha hs hfa hxs

/-- The graph map `x ↦ (f x, x)` is measurable. -/
theorem graph_map_measurable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
        EuclideanSpace ℝ (Option (Fin n)))) := by
  apply (WithLp.measurable_toLp 2 _).comp
  rw [measurable_pi_iff]
  intro o
  cases o with
  | none => exact hf
  | some j => exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)

/-- The graph law of a probability measure is a probability measure. -/
theorem graph_map_probability {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) :
    IsProbabilityMeasure (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
        EuclideanSpace ℝ (Option (Fin n))))) :=
  (Measure.isProbabilityMeasure_map_iff (graph_map_measurable hf).aemeasurable).2 inferInstance

/-- **The copy factor is the Laplace transform of the graph law** `(f(x), x)_* μ` at `(c, z)`. -/
theorem integral_exp_add_inner_eq_graph {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (c : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    (∫ x, Real.exp (c * f x + ⟪z, x⟫) ∂μ) =
      ∫ y, Real.exp ⟪(WithLp.toLp 2 fun o => Option.elim o c fun j => z j :
          EuclideanSpace ℝ (Option (Fin n))), y⟫
        ∂(μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by
    let φ : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Option (Fin n)) :=
      fun x => WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j
    let v : EuclideanSpace ℝ (Option (Fin n)) :=
      WithLp.toLp 2 fun o => Option.elim o c fun j => z j
    have hφ : Measurable φ := by
      simpa [φ] using graph_map_measurable hf
    have hg :
        AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Option (Fin n)) =>
          Real.exp ⟪v, y⟫) (μ.map φ) := by
      exact
        (Real.continuous_exp.comp
          (continuous_const.inner continuous_id)).aestronglyMeasurable
    have hmap :
        (∫ y, Real.exp ⟪v, y⟫ ∂(μ.map φ)) =
          ∫ x, Real.exp ⟪v, φ x⟫ ∂μ :=
      MeasureTheory.integral_map hφ.aemeasurable hg
    calc
      (∫ x, Real.exp (c * f x + ⟪z, x⟫) ∂μ) =
          ∫ x, Real.exp ⟪v, φ x⟫ ∂μ := by
            congr 1
            funext x
            simp [v, φ, PiLp.inner_apply, Fintype.sum_option, mul_comm]
      _ = ∫ y, Real.exp ⟪v, y⟫ ∂(μ.map φ) := hmap.symm

/-- **The tilt average of the `none` coordinate of the graph law at `(0, z)` is `F_f(z)`**. -/
theorem tiltAverage_graph_none {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    (z : EuclideanSpace ℝ (Fin n)) :
    tiltAverage (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n)))))
        (fun y => ⟪EuclideanSpace.single none 1, y⟫)
        (WithLp.toLp 2 fun o => Option.elim o 0 fun j => z j) =
      tiltAverage μ f z := by
    unfold tiltAverage expTilt
    rw [MeasureTheory.integral_tilted, MeasureTheory.integral_tilted]
    have hnorm :=
      (integral_exp_add_inner_eq_graph μ hf 0 z).symm
    rw [hnorm]
    simp only [zero_mul, zero_add]
    rw [integral_map (graph_map_measurable hf).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have hp (x : EuclideanSpace ℝ (Fin n)) :
        ⟪(WithLp.toLp 2 fun o => Option.elim o 0 (fun j => z j) :
            EuclideanSpace ℝ (Option (Fin n))),
          (WithLp.toLp 2 fun o => Option.elim o (f x) (fun j => x j) :
            EuclideanSpace ℝ (Option (Fin n)))⟫ =
          ⟪z, x⟫ := by
      simp [PiLp.inner_apply, Fintype.sum_option, RCLike.inner_apply]
    have he (x : EuclideanSpace ℝ (Fin n)) :
        ⟪EuclideanSpace.single none 1,
          (WithLp.toLp 2 fun o => Option.elim o (f x) (fun j => x j) :
            EuclideanSpace ℝ (Option (Fin n)))⟫ =
          f x := by
      simp [EuclideanSpace.inner_single_left]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hp x, he x]

/--
**Derivative of a copy term of (111) at `w = 0`**: `d/dw log ∫ e^{c w f + ⟪z, x⟫} dμ = c F_f(z)`,
through the graph law. -/
theorem hasDerivAt_log_integral_exp_copy {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {t : ℝ}
    (ht : 0 < t)
    (hγ :
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
              EuclideanSpace ℝ (Option (Fin n))))))
    (c : ℝ) {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ < t) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp (c * w * f x + ⟪z, x⟫) ∂μ))
      (c * tiltAverage μ f z) 0 := by
  let γ : Measure (EuclideanSpace ℝ (Option (Fin n))) :=
    μ.map
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))
  let _ : IsProbabilityMeasure γ := by simpa [γ] using (graph_map_probability μ hf)
  let p : EuclideanSpace ℝ (Option (Fin n)) :=
    WithLp.toLp 2 fun o => Option.elim o 0 fun j => z j
  let e₀ : EuclideanSpace ℝ (Option (Fin n)) := EuclideanSpace.single none 1
  have hγ' : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖)) γ := by
    simpa [γ] using hγ
  have hpnorm : ‖p‖ = ‖z‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [p, Fintype.sum_option]
  have hp : ‖p‖ < t := by simpa [hpnorm] using hz
  have hpball : p ∈ Metric.ball 0 t := by
    rw [mem_ball_zero_iff]
    exact hp
  have hpoint (w : ℝ) :
    (WithLp.toLp 2 fun o => Option.elim o (c * w) fun j => z j :
        EuclideanSpace ℝ (Option (Fin n))) =
      p + w • (c • e₀) := by
    ext o
    cases o with
    | none =>
      simp [p, e₀]
      ring
    | some j => simp [p, e₀]
  have hfun :
    (fun w : ℝ => Real.log (∫ x, Real.exp (c * w * f x + ⟪z, x⟫) ∂μ)) =
      (fun w : ℝ => logLaplace γ (p + w • (c • e₀))) := by
    funext w
    rw [integral_exp_add_inner_eq_graph μ hf (c * w) z]
    simp only [logLaplace]
    rw [hpoint w]
  have hcont :=
    (contDiffOn_logLaplace_ball γ ht hγ').contDiffAt (Metric.isOpen_ball.mem_nhds hpball)
  have hd : HasFDerivAt (logLaplace γ) (fderiv ℝ (logLaplace γ) p) p :=
    (hcont.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun w : ℝ => p + w • (c • e₀)) (c • e₀) 0 := by
    simpa using ((hasDerivAt_id (x := (0 : ℝ))).smul_const (c • e₀)).const_add p
  have hd0 : HasFDerivAt (logLaplace γ) (fderiv ℝ (logLaplace γ) p) (p + (0 : ℝ) • (c • e₀)) := by
    convert hd using 1
    simp
  have hcomp :
    HasDerivAt (logLaplace γ ∘ (fun w : ℝ => p + w • (c • e₀)))
      (fderiv ℝ (logLaplace γ) p (c • e₀)) 0 :=
    hd0.comp_hasDerivAt 0 hline
  have htilt : tiltAverage γ (fun y => ⟪e₀, y⟫) p = tiltAverage μ f z := by
    simpa [γ, p, e₀] using (tiltAverage_graph_none μ hf z)
  have hder : fderiv ℝ (logLaplace γ) p (c • e₀) = c * tiltAverage μ f z := by
    calc
      fderiv ℝ (logLaplace γ) p (c • e₀) = c * fderiv ℝ (logLaplace γ) p e₀ := by
        simp [map_smul, smul_eq_mul]
      _ = c * tiltAverage γ (fun y => ⟪e₀, y⟫) p := by
        rw [← tiltAverage_inner_eq_fderiv_logLaplace_of_lt γ hγ' hp e₀]
      _ = c * tiltAverage μ f z := by rw [htilt]
  rw [hfun]
  rw [Function.comp_def] at hcomp
  rw [hder] at hcomp
  exact hcomp

end FunctionalInequalities.KLS.LogConcave.Suspension

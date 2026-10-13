/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.MgfProduct

/-!
# Chernoff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — Steps 4–5 (MGF assembly + Chernoff)

This module carries the universal constants `C₅, C₆, Cstar`, the independence
hypothesis `ColumnsIndep`, the MGF integrand `expZfun`, the within-class
independence factorization `lintegral_prod_class`, the fully-proved **Step 4
residue-class MGF bound** `full_mgf_bound`, and the **Step 5 Chernoff bound**
`count_chernoff_bound`.  Both steps are `sorry`-free; the generic Step-4 analytic
and combinatorial helpers live in `MgfProduct.lean`.

## Integrand `expZfun`

`expZfun X p s lam r m ω = ⨆_N ∏_{j ∈ [-N,N]} e_r^{Z_j(ω)}`, where
`e_r = ofReal(exp(a/r))` and `a = ⅛(log 3) s p = mgfRate s p`.  This is the
`ℝ≥0∞` realization of `exp((a/r) ∑_j Z_j)` as a monotone limit of finite-window
products — clean under Chernoff's Markov step and free of `toReal` pitfalls.

## `full_mgf_bound` (Step 4, `e.full.mgf.bound`) —

`∫⁻ expZfun ≤ ofReal(exp((m+1)/r · θ log 3 / 16))`.  The is the paper's `exp(C₆
r⁻¹ (3/λ)^p (m+1))` after substituting `λ = 3 Cstar^{1/p} θ^{-1/p}`: with
`Cstar = 16 C₆/log 3` one has `C₆ (3/λ)^p = θ log 3 / 16` (as `(3/λ)^p =
θ/Cstar`).  The proof: monotone convergence (`lintegral_iSup`) over the
`[−N,N]` exhaustion; residue split + Hölder over the `r` classes
(`ENNReal.lintegral_prod_norm_pow_le`); within-class independence factorization
(`lintegral_prod_class`, from `ColumnsIndep` via `iIndepFun.comp`); insert the
integer MGF `Zj_mgf`; `∏(1+c_j) ≤ exp(∑ c_j)` and the two-sided geometric
`ℤ`-sum (`MgfProduct.lean`).

## Step 5 (proved here)

`count_chernoff_bound` derives the Chernoff bound from `full_mgf_bound` by
Markov (`mul_meas_ge_le_lintegral₀`) with `ε = ofReal(exp((a/r) θ (m+1)))` and
the set inclusion `{ofReal(θ(m+1)) < ∑_j Z_j} ⊆ {ε ≤ expZfun}`.  The final rate
uses `(log 3)(2sp−1) ≥ sp` (from `sp ≥ 1`, `log 3 > 1`) to reach
`exp(−spθ(m+1)/(16r))`.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal NNReal

/-- `C₅`: the universal bound for `∑_j 3^{-(sp/2) d_j} ≤ C₅ (m+1)` (Step 4). -/
noncomputable def C₅ : ℝ := 3

/-- `C₆ = C₃ C₅` (Step 4). -/
noncomputable def C₆ : ℝ := C₃ * C₅

lemma C₆_pos : 0 < C₆ := mul_pos C₃_pos (by norm_num [C₅])

/-- The universal constant `C = 16 C₆ / log 3`. -/
noncomputable def Cstar : ℝ := 16 * C₆ / Real.log 3

lemma Cstar_pos : 0 < Cstar :=
  div_pos (mul_pos (by norm_num) C₆_pos) (Real.log_pos (by norm_num))

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Within each residue class modulo `r`, the columns of `X` (as `(ℤ→ℝ)`-valued
random variables) are mutually independent.  Implied by
`e.independent.columns.twosided`; see `Defs.lean`. -/
def ColumnsIndep (P : Measure Ω) (X : ℤ → ℤ → Ω → ℝ) (r : ℕ) : Prop :=
  ∀ b : ℤ, iIndepFun (fun (j : ℤ) => fun (ω : Ω) (k : ℤ) => X k (j * r + b) ω) P

/-- The MGF integrand `⨆_N ∏_{j∈[-N,N]} e_r^{Z_j}`. -/
noncomputable def expZfun (X : ℤ → ℤ → Ω → ℝ) (p s lam : ℝ) (r m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ N : ℕ, ∏ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ (Zcount X s lam m j ω)

/-- Any finite set of integers lies inside some symmetric window `[-N, N]`. -/
lemma exists_icc_superset (t : Finset ℤ) :
    ∃ N : ℕ, t ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  refine ⟨t.sup Int.natAbs, fun x hx => ?_⟩
  have hle : x.natAbs ≤ t.sup Int.natAbs := Finset.le_sup hx
  rw [Finset.mem_Icc]
  omega

variable {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → ℤ → Ω → ℝ}
  {p s : ℝ} {r : ℕ}

/-- Measurability of the column count `Z_j`. -/
lemma measurable_Zcount (hXmeas : ∀ k j, Measurable (X k j)) (lam : ℝ) (m : ℕ) (j : ℤ) :
    Measurable (fun ω => Zcount X s lam m j ω) := by
  classical
  unfold Zcount
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const (hXmeas k j))
    measurable_const measurable_const

/-- Measurability of the MGF integrand `expZfun`. -/
lemma measurable_expZfun (hXmeas : ∀ k j, Measurable (X k j)) (lam : ℝ) (m : ℕ) :
    Measurable (fun ω => expZfun X p s lam r m ω) := by
  unfold expZfun
  refine Measurable.iSup (fun N => ?_)
  refine Finset.measurable_prod _ (fun j _ => ?_)
  exact (Measurable.of_discrete).comp (measurable_Zcount hXmeas lam m j)

omit [IsProbabilityMeasure P] in
/-- **Within-class independence factorization (Step 4, sub-part (c)).**  For a
finite set `fib` of columns all congruent to `b` modulo `r` (so `r ∣ j - b`), the
`ℤ`-reindexed family `i ↦ B^{Z_{ir+b}}` is mutually independent via `ColumnsIndep`,
so the `∫⁻` of the product factors into the product of `∫⁻`'s. -/
lemma lintegral_prod_class
    (hr : 1 ≤ r) (hindep : ColumnsIndep P X r) (hXmeas : ∀ k j, Measurable (X k j))
    (a lam : ℝ) (m : ℕ) (b : ℤ) (fib : Finset ℤ)
    (hdvd : ∀ j ∈ fib, (r : ℤ) ∣ (j - b)) :
    ∫⁻ ω, ∏ j ∈ fib, (ENNReal.ofReal (Real.exp a)) ^ (Zcount X s lam m j ω) ∂P
      = ∏ j ∈ fib, ∫⁻ ω, (ENNReal.ofReal (Real.exp a)) ^ (Zcount X s lam m j ω) ∂P := by
  classical
  set B := ENNReal.ofReal (Real.exp a) with hB
  set ψ : ℤ → ℤ := fun j => (j - b) / (r : ℤ) with hψ
  have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hr
  -- reconstruction ψ j * r + b = j
  have hrecon : ∀ j ∈ fib, ψ j * (r : ℤ) + b = j := by
    intro j hj
    obtain ⟨c, hc⟩ := hdvd j hj
    have hψj : ψ j = c := by
      simp only [hψ]; rw [hc, Int.mul_ediv_cancel_left c hrne]
    rw [hψj]; linarith [hc]
  have hinj : ∀ x ∈ fib, ∀ y ∈ fib, ψ x = ψ y → x = y := by
    intro x hx y hy hxy
    have hrx := hrecon x hx
    have hry := hrecon y hy
    rw [hxy] at hrx
    exact hrx.symm.trans hry
  -- position-indexed family
  set Y : ℤ → Ω → ℝ≥0∞ := fun i ω => B ^ (Zcount X s lam m (i * (r : ℤ) + b) ω) with hYdef
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    exact Measurable.of_discrete.comp (measurable_Zcount hXmeas lam m (i * (r : ℤ) + b))
  -- measurability of the coordinate maps for `iIndepFun.comp`
  have hgmeas : ∀ i : ℤ, Measurable (fun c : ℤ → ℝ => B ^ (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
      if thr s lam k (i * (r : ℤ) + b) < c k then (1 : ℕ) else 0)) := by
    intro i
    refine Measurable.of_discrete.comp ?_
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply k))
      measurable_const measurable_const
  have hYindep : iIndepFun Y P := by
    have hcomp := (hindep b).comp
      (fun (i : ℤ) (c : ℤ → ℝ) => B ^ (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
        if thr s lam k (i * (r : ℤ) + b) < c k then (1 : ℕ) else 0)) hgmeas
    have hEq : (fun (i : ℤ) => (fun (c : ℤ → ℝ) => B ^ (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
        if thr s lam k (i * (r : ℤ) + b) < c k then (1 : ℕ) else 0))
        ∘ (fun (ω : Ω) (k : ℤ) => X k (i * (r : ℤ) + b) ω)) = Y := by
      funext i ω
      simp only [Function.comp_apply, hYdef, Zcount]
    rwa [hEq] at hcomp
  -- reindex products through ψ
  have hprodω : ∀ ω, ∏ j ∈ fib, B ^ (Zcount X s lam m j ω)
      = ∏ i ∈ fib.image ψ, Y i ω := by
    intro ω
    rw [Finset.prod_image hinj]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    simp only [hYdef]; rw [hrecon j hj]
  have hprodInt : ∏ j ∈ fib, ∫⁻ ω, B ^ (Zcount X s lam m j ω) ∂P
      = ∏ i ∈ fib.image ψ, ∫⁻ ω, Y i ω ∂P := by
    rw [Finset.prod_image hinj]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    simp only [hYdef]; rw [hrecon j hj]
  calc ∫⁻ ω, ∏ j ∈ fib, B ^ (Zcount X s lam m j ω) ∂P
      = ∫⁻ ω, ∏ i ∈ fib.image ψ, Y i ω ∂P := by
        refine lintegral_congr (fun ω => ?_); rw [hprodω ω]
    _ = ∏ i ∈ fib.image ψ, ∫⁻ ω, Y i ω ∂P :=
        lintegral_prod_eq_prod_lintegral_of_indepFun _ Y hYindep hYmeas
    _ = ∏ j ∈ fib, ∫⁻ ω, B ^ (Zcount X s lam m j ω) ∂P := hprodInt.symm

/-- **Step 4 (`e.full.mgf.bound`).**

`∫⁻ expZfun ≤ ofReal(exp((m+1)/r · θ log 3 / 16))`.  Assembled from monotone
convergence, Hölder over the `r` residue classes, within-class independence
(`lintegral_prod_class`), the integer MGF `Zj_mgf`, and the `MgfProduct`
helpers. -/
theorem full_mgf_bound
    (hp : 1 ≤ p) (hs : 0 < s) (hs1 : s ≤ 1) (hsp : 1 ≤ s * p) (hr : 1 ≤ r)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hmomL : ∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1)
    (hindep : ColumnsIndep P X r)
    (m : ℕ) (θ : ℝ) (hrm : (r : ℤ) ≤ (m : ℤ)) (hθ0 : 0 < θ) :
    ∫⁻ ω, expZfun X p s (3 * Cstar ^ (1 / p) * θ ^ (-1 / p)) r m ω ∂P
      ≤ ENNReal.ofReal (Real.exp (((m : ℝ) + 1) / (r : ℝ) * (θ * Real.log 3 / 16))) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr
  have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hr
  have hm1 : 1 ≤ m := by
    have : (1 : ℤ) ≤ (m : ℤ) := le_trans (by exact_mod_cast hr) hrm
    exact_mod_cast this
  set lam : ℝ := 3 * Cstar ^ (1 / p) * θ ^ (-1 / p) with hlamdef
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    have h1 : (0 : ℝ) < Cstar ^ (1 / p) := Real.rpow_pos_of_pos Cstar_pos _
    have h2 : (0 : ℝ) < θ ^ (-1 / p) := Real.rpow_pos_of_pos hθ0 _
    positivity
  have hmgf : 0 ≤ mgfRate s p := (mgfRate_pos hs hp0).le
  -- constant identity  C₆ (3/λ)^p = θ log 3 / 16
  have hlam_pow : (3 / lam) ^ p = θ / Cstar := three_div_lam_rpow Cstar_pos hθ0 hp0
  have hlogpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hC6lam : C₆ * (3 / lam) ^ p = θ * Real.log 3 / 16 := by
    rw [hlam_pow, Cstar]
    have := C₆_pos.ne'
    have := hlogpos.ne'
    field_simp
  -- the coefficient  c_j = C₃ (3/λ)^p 3^{-(sp/2) d_j}
  set hcoef : ℤ → ℝ := fun j =>
    C₃ * (3 / lam) ^ p * (3 : ℝ) ^ (-(s * p / 2 * (dcol m j : ℝ))) with hcoefdef
  have h3lam0 : (0 : ℝ) ≤ (3 / lam) ^ p := Real.rpow_nonneg (by positivity) _
  have hcoef_nn : ∀ j, 0 ≤ hcoef j := by
    intro j; rw [hcoefdef]
    exact mul_nonneg (mul_nonneg C₃_pos.le h3lam0) (Real.rpow_nonneg (by norm_num) _)
  -- ∑_{j∈[-N,N]} c_j ≤ C₆ (3/λ)^p (m+1)
  have hsumcoef : ∀ N : ℕ, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), hcoef j
      ≤ C₆ * (3 / lam) ^ p * ((m : ℝ) + 1) := by
    intro N
    have hgeom := sum_three_dcol_le hsp m N hm1
    calc ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), hcoef j
        = C₃ * (3 / lam) ^ p
            * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (3 : ℝ) ^ (-(s * p / 2 * (dcol m j : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ C₃ * (3 / lam) ^ p * (3 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hgeom (mul_nonneg C₃_pos.le h3lam0)
      _ = C₆ * (3 / lam) ^ p * ((m : ℝ) + 1) := by rw [C₆, C₅]; ring
  -- expose the iSup and abbreviate e_r
  simp only [expZfun]
  set er : ℝ≥0∞ := ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ))) with her
  set B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (mgfRate s p)) with hBdef
  have her1 : (1 : ℝ≥0∞) ≤ er := by
    rw [her, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.2 (div_nonneg hmgf hrpos.le))
  -- measurability & monotonicity of the window products
  have hFmeas : ∀ N : ℕ, Measurable
      (fun ω => ∏ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), er ^ (Zcount X s lam m j ω)) := by
    intro N
    exact Finset.measurable_prod _
      (fun j _ => Measurable.of_discrete.comp (measurable_Zcount hXmeas lam m j))
  have hmono : Monotone
      (fun (N : ℕ) ω => ∏ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), er ^ (Zcount X s lam m j ω)) := by
    intro N₁ N₂ hN ω
    refine Finset.prod_le_prod_of_subset_of_one_le ?_ (fun j _ _ => one_le_pow_of_one_le' her1 _)
    intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  -- per-window bound  ∫⁻ ∏ e_r^{Z_j} ≤ ofReal(exp((1/r) ∑ c_j))
  have hFN : ∀ N : ℕ, ∫⁻ ω, ∏ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        er ^ (Zcount X s lam m j ω) ∂P
      ≤ ENNReal.ofReal (Real.exp ((1 / (r : ℝ))
          * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), hcoef j)) := by
    intro N
    set W := Finset.Icc (-(N : ℤ)) (N : ℤ) with hW
    set g : ℤ → ℕ := fun j => (j % (r : ℤ)).toNat with hg
    set Gb : ℕ → Ω → ℝ≥0∞ :=
      fun b ω => ∏ j ∈ W.filter (fun j => g j = b), B ^ (Zcount X s lam m j ω) with hGb
    have hmaps : ∀ j ∈ W, g j ∈ Finset.range r := by
      intro j _
      simp only [hg, Finset.mem_range]
      have h1 : j % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos j (by exact_mod_cast hr.trans_lt' Nat.zero_lt_one)
      have h2 : (0 : ℤ) ≤ j % (r : ℤ) := Int.emod_nonneg j hrne
      omega
    have hdvdfib : ∀ b : ℕ, ∀ j ∈ W.filter (fun j => g j = b), (r : ℤ) ∣ (j - (b : ℤ)) := by
      intro b j hj
      rw [Finset.mem_filter] at hj
      have hgj : g j = b := hj.2
      simp only [hg] at hgj
      have hnn : (0 : ℤ) ≤ j % (r : ℤ) := Int.emod_nonneg j hrne
      have hjmod : j % (r : ℤ) = (b : ℤ) := by rw [← Int.toNat_of_nonneg hnn, hgj]
      refine ⟨j / (r : ℤ), ?_⟩
      have hkey := Int.mul_ediv_add_emod j (r : ℤ)
      rw [hjmod] at hkey
      linarith [hkey]
    have hGbmeas : ∀ b : ℕ, Measurable (Gb b) := by
      intro b
      exact Finset.measurable_prod _
        (fun j _ => Measurable.of_discrete.comp (measurable_Zcount hXmeas lam m j))
    -- residue-split of the window product
    have hprodsplit : ∀ ω, ∏ j ∈ W, er ^ (Zcount X s lam m j ω)
        = ∏ b ∈ Finset.range r, (Gb b ω) ^ ((1 : ℝ) / r) := by
      intro ω
      rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun j => er ^ (Zcount X s lam m j ω))]
      refine Finset.prod_congr rfl (fun b _ => ?_)
      rw [hGb, ← ENNReal.prod_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / r)]
      exact Finset.prod_congr rfl (fun j _ => er_npow (mgfRate s p) r (Zcount X s lam m j ω))
    -- each class integral bounded by exp of the class coefficient sum
    have hGbBound : ∀ b : ℕ, ∫⁻ ω, Gb b ω ∂P
        ≤ ENNReal.ofReal (Real.exp (∑ j ∈ W.filter (fun j => g j = b), hcoef j)) := by
      intro b
      rw [hGb, lintegral_prod_class hr hindep hXmeas (mgfRate s p) lam m (b : ℤ)
        (W.filter (fun j => g j = b)) (hdvdfib b)]
      calc ∏ j ∈ W.filter (fun j => g j = b),
              ∫⁻ ω, B ^ (Zcount X s lam m j ω) ∂P
          ≤ ∏ j ∈ W.filter (fun j => g j = b), ENNReal.ofReal (1 + hcoef j) := by
            refine Finset.prod_le_prod (fun j _ => ?_)
            rw [hBdef, hcoefdef]
            exact Zj_mgf (P := P) (X := X) hs hs1 hp hsp hlam0 hXmeas hmomL m j
              (dcol m j) (fun k hk => dcol_le hk)
        _ ≤ ENNReal.ofReal (Real.exp (∑ j ∈ W.filter (fun j => g j = b), hcoef j)) :=
            prod_add_one_le_exp_ofReal _ hcoef (fun j _ => hcoef_nn j)
    -- assemble via Hölder over the residue classes
    calc ∫⁻ ω, ∏ j ∈ W, er ^ (Zcount X s lam m j ω) ∂P
        = ∫⁻ ω, ∏ b ∈ Finset.range r, (Gb b ω) ^ ((1 : ℝ) / r) ∂P :=
          lintegral_congr (fun ω => hprodsplit ω)
      _ ≤ ∏ b ∈ Finset.range r, (∫⁻ ω, Gb b ω ∂P) ^ ((1 : ℝ) / r) := by
          refine ENNReal.lintegral_prod_norm_pow_le (Finset.range r)
            (fun b _ => (hGbmeas b).aemeasurable) ?_ (fun b _ => by positivity)
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
      _ ≤ ∏ b ∈ Finset.range r,
            (ENNReal.ofReal (Real.exp (∑ j ∈ W.filter (fun j => g j = b), hcoef j))) ^ ((1 : ℝ) / r) := by
          refine Finset.prod_le_prod (fun b _ => ?_)
          exact ENNReal.rpow_le_rpow (hGbBound b) (by positivity)
      _ = ∏ b ∈ Finset.range r,
            ENNReal.ofReal (Real.exp ((1 / (r : ℝ)) * ∑ j ∈ W.filter (fun j => g j = b), hcoef j)) := by
          refine Finset.prod_congr rfl (fun b _ => ?_)
          rw [mul_comm (1 / (r : ℝ)) (∑ j ∈ W.filter (fun j => g j = b), hcoef j),
            Real.exp_mul, ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (by positivity)]
      _ = ENNReal.ofReal (Real.exp
            (∑ b ∈ Finset.range r, (1 / (r : ℝ)) * ∑ j ∈ W.filter (fun j => g j = b), hcoef j)) := by
          rw [← ENNReal.ofReal_prod_of_nonneg (fun b _ => (Real.exp_pos _).le), ← Real.exp_sum]
      _ = ENNReal.ofReal (Real.exp ((1 / (r : ℝ)) * ∑ j ∈ W, hcoef j)) := by
          rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps hcoef]
  -- monotone convergence + uniform bound
  rw [lintegral_iSup hFmeas hmono]
  refine iSup_le (fun N => (hFN N).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hle : (1 / (r : ℝ)) * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), hcoef j
      ≤ (1 / (r : ℝ)) * (C₆ * (3 / lam) ^ p * ((m : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (hsumcoef N) (by positivity)
  refine hle.trans (le_of_eq ?_)
  rw [show C₆ * (3 / lam) ^ p * ((m : ℝ) + 1) = (C₆ * (3 / lam) ^ p) * ((m : ℝ) + 1) from rfl,
    hC6lam]
  field_simp

/-- The final rate inequality `(log 3)(2sp − 1) ≥ sp`, from `sp ≥ 1`, `log 3 > 1`. -/
lemma rate_key (hsp : 1 ≤ s * p) : s * p ≤ Real.log 3 * (2 * (s * p) - 1) := by
  have hL := log_three_gt_one
  nlinarith [hL, hsp,
    mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 3 - 1) (by linarith : (0 : ℝ) ≤ s * p - 1)]

/-- The Chernoff exponent comparison `A − B ≤ D`, where `A = (m+1)/r·θlog3/16`,
`B = mgfRate/r·θ(m+1)`, `D = −spθ/(16r)·(m+1)`, using
`D − (A − B) = ((m+1)θ/16r)·(log3(2sp−1) − sp) ≥ 0`. -/
lemma rate_arith (hrpos : 0 < (r : ℝ)) (θ : ℝ) (hθ0 : 0 < θ) (m : ℕ)
    (hsp : 1 ≤ s * p) :
    ((m : ℝ) + 1) / (r : ℝ) * (θ * Real.log 3 / 16)
        - 1 / 8 * Real.log 3 * s * p / (r : ℝ) * (θ * ((m : ℝ) + 1))
      ≤ -(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1) := by
  rw [← sub_nonneg]
  have hrne : (r : ℝ) ≠ 0 := hrpos.ne'
  have heq : -(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1)
        - (((m : ℝ) + 1) / (r : ℝ) * (θ * Real.log 3 / 16)
          - 1 / 8 * Real.log 3 * s * p / (r : ℝ) * (θ * ((m : ℝ) + 1)))
      = ((m : ℝ) + 1) * θ / (16 * (r : ℝ)) * (Real.log 3 * (2 * (s * p) - 1) - s * p) := by
    field_simp
    ring
  rw [heq]
  exact mul_nonneg (by positivity) (by linarith [rate_key hsp])

/-- **Step 5 (Chernoff).**  The Chernoff bound on the aggregated column count,
obtained from `full_mgf_bound` by Markov's inequality. -/
theorem count_chernoff_bound
    (hp : 1 ≤ p) (hs : 0 < s) (hs1 : s ≤ 1) (hsp : 1 ≤ s * p) (hr : 1 ≤ r)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hmomL : ∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1)
    (hindep : ColumnsIndep P X r)
    (m : ℕ) (θ : ℝ) (hrm : (r : ℤ) ≤ (m : ℤ)) (hθ0 : 0 < θ) :
    P {ω | ENNReal.ofReal (θ * ((m : ℝ) + 1))
        < ∑' j : ℤ, (Zcount X s (3 * Cstar ^ (1 / p) * θ ^ (-1 / p)) m j ω : ℝ≥0∞)}
      ≤ ENNReal.ofReal (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1))) := by
  classical
  have hp0 : 0 < p := by linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr
  set lam : ℝ := 3 * Cstar ^ (1 / p) * θ ^ (-1 / p) with hlam
  have hMr : 0 < mgfRate s p / (r : ℝ) := div_pos (mgfRate_pos hs hp0) hrpos
  set ε : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ) * (θ * ((m : ℝ) + 1)))) with hε
  have hεpos : 0 < ε := ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hεtop : ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hexpZmeas : Measurable (fun ω => expZfun X p s lam r m ω) :=
    measurable_expZfun hXmeas lam m
  -- set inclusion into {ε ≤ expZfun}
  have hsub : {ω | ENNReal.ofReal (θ * ((m : ℝ) + 1))
        < ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞)}
      ⊆ {ω | ε ≤ expZfun X p s lam r m ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [ENNReal.tsum_eq_iSup_sum' (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ))
      exists_icc_superset] at hω
    obtain ⟨N, hN⟩ := lt_iSup_iff.1 hω
    set n : ℕ := ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Zcount X s lam m j ω with hn
    have hcast : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (Zcount X s lam m j ω : ℝ≥0∞)
        = (n : ℝ≥0∞) := by rw [hn]; push_cast; ring
    rw [hcast] at hN
    have hθn : θ * ((m : ℝ) + 1) < (n : ℝ) := by
      rw [← ENNReal.ofReal_natCast] at hN
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 hN
    have hprod : ∏ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ (Zcount X s lam m j ω)
        = (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ n := by
      rw [Finset.prod_pow_eq_pow_sum]
    have her_n : (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ n
        = ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ) * (n : ℝ))) := by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
      congr 2; ring
    have hεle : ε ≤ (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ n := by
      rw [hε, her_n]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      exact mul_le_mul_of_nonneg_left hθn.le hMr.le
    calc ε ≤ (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ n := hεle
      _ = ∏ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ (Zcount X s lam m j ω) :=
          hprod.symm
      _ ≤ expZfun X p s lam r m ω :=
          le_iSup (fun N : ℕ => ∏ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (ENNReal.ofReal (Real.exp (mgfRate s p / (r : ℝ)))) ^ (Zcount X s lam m j ω)) N
  -- Markov + full_mgf_bound
  have hmarkov := mul_meas_ge_le_lintegral₀ (hexpZmeas.aemeasurable (μ := P)) ε
  have hfull := full_mgf_bound (P := P) (X := X) hp hs hs1 hsp hr hXmeas hmomL hindep
    m θ hrm hθ0
  have hchain : ε * P {ω | ENNReal.ofReal (θ * ((m : ℝ) + 1))
        < ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞)}
      ≤ ENNReal.ofReal (Real.exp (((m : ℝ) + 1) / (r : ℝ) * (θ * Real.log 3 / 16))) := by
    calc ε * P {ω | ENNReal.ofReal (θ * ((m : ℝ) + 1))
            < ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞)}
        ≤ ε * P {ω | ε ≤ expZfun X p s lam r m ω} := mul_le_mul_right (measure_mono hsub) ε
      _ ≤ ∫⁻ ω, expZfun X p s lam r m ω ∂P := hmarkov
      _ ≤ _ := hfull
  -- divide by ε and compare exponents
  have hdiv : P {ω | ENNReal.ofReal (θ * ((m : ℝ) + 1))
        < ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞)}
      ≤ ENNReal.ofReal (Real.exp (((m : ℝ) + 1) / (r : ℝ) * (θ * Real.log 3 / 16))) / ε := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hεpos.ne') (Or.inl hεtop), mul_comm]
    exact hchain
  refine hdiv.trans ?_
  rw [hε, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  -- A − B ≤ D
  simp only [mgfRate]
  exact rate_arith hrpos θ hθ0 m hsp

end Algsuperdiff.Section4.Probability.ScalesConcentration

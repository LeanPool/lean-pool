/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.MvPowerSeriesPDeriv
public import LeanPool.HyperellipticCurves.Series.PSeries
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Substitution

import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The p-adic kit: multivariate evaluation

Evaluation of a multivariate power series `h ∈ O⟦z_s : s ∈ σ⟧` at a family of points of
the maximal ideal (`ChabautyColeman.MvPSeries.eval`), as a thin layer over Mathlib's
`MvPowerSeries.eval₂`, in the standing setting of the `p`-adic kit
(`LeanPool.HyperellipticCurves.Series.PSeries`). For a finite index type, any family in the maximal
ideal is
a legitimate evaluation point (`ChabautyColeman.MvPSeries.hasEval_of_mem`); evaluation is a ring
homomorphism (`ChabautyColeman.MvPSeries.evalRingHom`) computed by a convergent sum
(`ChabautyColeman.MvPSeries.hasSum_eval`).

Composition: Mathlib's formal substitution `MvPowerSeries.subst` is continuous for the
product topologies (`MvPowerSeries.continuous_subst'` — each coefficient of
`subst a f` is a fixed finite linear combination of coefficients of `f`, by
`MvPowerSeries.coeff_subst_finite` applied to the all-ones series), whence evaluation of
a substitution is evaluation at the evaluated family
(`ChabautyColeman.MvPSeries.eval_subst`, via uniqueness of continuous algebra
homomorphisms `MvPowerSeries.aeval_unique`), and the evaluated family is itself a
legitimate evaluation point (`ChabautyColeman.MvPSeries.hasEval_eval`).

The chain rule for formal partial derivatives under substitution is `MvPowerSeries.pderiv_subst`
(`LeanPool.HyperellipticCurves.ForMathlib.MvPowerSeriesPDeriv`).

For power series whose coefficients *decay* (tend to `0` cofinitely), evaluation
converges at *any* family of points of `O` — not only those in the maximal ideal —
because the terms tend to `0` for a bounded point family; this is
`ChabautyColeman.MvPSeries.evalT`, agreeing with `eval` where the latter converges
(`ChabautyColeman.MvPSeries.evalT_eq_eval`).

Blueprint nodes: `def:mv-eval`, `def:mv-evalT`.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology

/-- On `ι →₀ ℕ` with `ι` finite, the total degree tends to `∞` along the cofinite
filter: only finitely many multi-indices have degree below any bound. -/
theorem Finsupp.tendsto_degree_cofinite {ι : Type*} [Finite ι] :
    Filter.Tendsto (Finsupp.degree : (ι →₀ ℕ) → ℕ) Filter.cofinite Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_cofinite]
  exact (Finsupp.finite_of_degree_le b).subset fun d hd ↦ le_of_lt (by simpa using hd)

namespace ChabautyColeman

namespace MvPSeries

variable {σ : Type*} {O : Type*} [CommRing O] [UniformSpace O]

/-- Evaluation of a multivariate power series at a family of points of the maximal
ideal: the convergent sum `∑ a_d z₀^d` (junk if the series does not converge). -/
noncomputable def eval (z₀ : σ → O) (h : MvPowerSeries σ O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) z₀ h

theorem eval_eq_eval₂ (z₀ : σ → O) (h : MvPowerSeries σ O) :
    eval z₀ h = MvPowerSeries.eval₂ (RingHom.id O) z₀ h :=
  rfl

@[simp]
theorem eval_coe (f : MvPolynomial σ O) (z₀ : σ → O) :
    eval z₀ (f : MvPowerSeries σ O) = MvPolynomial.eval z₀ f := by
  rw [eval_eq_eval₂, eval₂_coe, MvPolynomial.eval₂_id]

@[simp]
theorem eval_C (r : O) (z₀ : σ → O) : eval z₀ (C r) = r :=
  eval₂_C _ _ r

@[simp]
theorem eval_X (z₀ : σ → O) (s : σ) : eval z₀ (X s) = z₀ s :=
  eval₂_X _ _ s

@[simp]
theorem eval_zero (z₀ : σ → O) : eval z₀ (0 : MvPowerSeries σ O) = 0 := by simpa using eval_C 0 z₀

/-- Evaluation of a multivariate power series with decaying coefficients at an arbitrary
family of points of `O` (junk if the defining series does not converge). Unlike
`MvPSeries.eval`, the evaluation points need not lie in the maximal ideal; convergence is
supplied instead by the decay of the coefficients. -/
noncomputable def evalT (z : σ → O) (h : MvPowerSeries σ O) : O :=
  ∑' d : σ →₀ ℕ, coeff d h * d.prod fun s e ↦ z s ^ e

theorem evalT_eq_tsum (z : σ → O) (h : MvPowerSeries σ O) :
    evalT z h = ∑' d : σ →₀ ℕ, coeff d h * d.prod fun s e ↦ z s ^ e :=
  rfl

@[simp]
theorem evalT_zero (z : σ → O) : evalT z (0 : MvPowerSeries σ O) = 0 := by simp [evalT_eq_tsum]

@[simp]
theorem evalT_C (z : σ → O) (r : O) : evalT z (C r) = r := by
  classical
  rw [evalT_eq_tsum, tsum_eq_single 0]
  · simp
  · intro d hd
    rw [coeff_C, ite_eq_right hd, zero_mul]

@[simp]
theorem evalT_X (z : σ → O) (s : σ) : evalT z (X s : MvPowerSeries σ O) = z s := by
  classical
  rw [evalT_eq_tsum, tsum_eq_single (Finsupp.single s 1)]
  · simp [coeff_X, Finsupp.prod_single_index]
  · intro d hd
    rw [coeff_X, ite_eq_right hd, zero_mul]

@[simp]
theorem evalT_one (z : σ → O) : evalT z (1 : MvPowerSeries σ O) = 1 := by
  rw [show (1 : MvPowerSeries σ O) = C 1 from (map_one _).symm, evalT_C]

/-- The constant power series `1` has decaying coefficients. -/
theorem decay_one : Tendsto (fun d ↦ coeff d (1 : MvPowerSeries σ O)) cofinite (𝓝 0) := by
  classical
  refine tendsto_nhds_of_eventually_eq ?_
  rw [eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton 0) fun d hd ↦ ?_
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_singleton_iff]
  by_contra hne
  exact hd (by rw [coeff_one, ite_eq_right hne])

/-- A variable has decaying coefficients. -/
theorem decay_X (s : σ) : Tendsto (fun d ↦ coeff d (X s : MvPowerSeries σ O)) cofinite (𝓝 0) := by
  classical
  refine tendsto_nhds_of_eventually_eq ?_
  rw [eventually_cofinite]
  refine (Set.finite_singleton (Finsupp.single s 1)).subset fun d hd ↦ ?_
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_singleton_iff]
  by_contra hne; exact hd (by rw [coeff_X, ite_eq_right hne])

/-- Coefficient decay is preserved by renaming the variables along an injection. -/
theorem decay_rename {τ : Type*} {e : σ → τ} (he : Function.Injective e) [TendstoCofinite e]
    {h : MvPowerSeries σ O} (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    Tendsto (fun x ↦ coeff x (rename e h)) cofinite (𝓝 0) := by
  refine tendsto_def.mpr fun U hU ↦ mem_cofinite.mpr ?_
  have h1 : {d : σ →₀ ℕ | coeff d h ∉ U}.Finite := eventually_cofinite.mp (hh.eventually_mem hU)
  refine (h1.image (Finsupp.mapDomain e)).subset fun x hx ↦ ?_
  rw [Set.mem_compl_iff, Set.mem_preimage] at hx
  by_cases hxr : x ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨d, rfl⟩ := hxr
    refine ⟨d, ?_, rfl⟩
    rwa [Set.mem_ofPred_eq, ← coeff_embDomain_rename ⟨e, he⟩ h d,
      Finsupp.embDomain_eq_mapDomain]
  · rw [coeff_rename_eq_zero e h hxr] at hx
    exact absurd (mem_of_mem_nhds hU) hx

section topologicalRing

variable [IsTopologicalRing O]

/-- Coefficient decay is preserved by natural-number multiples. -/
theorem decay_nsmul {h : MvPowerSeries σ O} (n : ℕ)
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    Tendsto (fun d ↦ coeff d (n • h)) cofinite (𝓝 0) := by
  simpa only [map_nsmul, smul_zero] using hh.const_smul n

private lemma continuous_substAlgHom {τ : Type*} {a : τ → MvPowerSeries σ O}
    (ha : MvPowerSeries.HasSubst a) :
    Continuous (MvPowerSeries.substAlgHom (R := O) (S := O) ha) := by
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.continuous_subst' ha

end topologicalRing

variable [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))]

/-- Families of points of the maximal ideal, indexed by a finite type, are legitimate
evaluation points for multivariate power series. -/
theorem hasEval_of_mem [Finite σ] {z₀ : σ → O} (hz₀ : ∀ i, z₀ i ∈ maximalIdeal O) :
    MvPowerSeries.HasEval z₀ where
  hpow i := (Fact.out : IsAdic (maximalIdeal O)).isTopologicallyNilpotent_of_mem (hz₀ i)
  tendsto_zero := by
    rw [Filter.cofinite_eq_bot]
    exact tendsto_bot

/-- A sufficient condition for the coefficients of a multivariate power series to decay
(hence for `evalT` to converge): each coefficient lies in a power of the maximal ideal
whose exponent tends to `∞` cofinitely. -/
theorem tendsto_coeff_zero_of_mem_pow {h : MvPowerSeries σ O} {e : (σ →₀ ℕ) → ℕ}
    (hmem : ∀ d, coeff d h ∈ maximalIdeal O ^ e d) (he : Tendsto e cofinite atTop) :
    Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0) :=
  (Fact.out : IsAdic (maximalIdeal O)).tendsto_zero_of_mem_pow hmem he

variable [IsUniformAddGroup O] [CompleteSpace O]

/-- The defining series of `evalT` is summable when the coefficients of `h` decay. -/
theorem summable_evalT (z : σ → O) {h : MvPowerSeries σ O}
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    Summable fun d : σ →₀ ℕ ↦ coeff d h * d.prod fun s e ↦ z s ^ e :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (PSeries.tendsto_mul_zero_of_tendsto_zero hh)

theorem hasSum_evalT (z : σ → O) {h : MvPowerSeries σ O}
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    HasSum (fun d : σ →₀ ℕ ↦ coeff d h * d.prod fun s e ↦ z s ^ e) (evalT z h) :=
  (summable_evalT z hh).hasSum

variable [T2Space O] [IsTopologicalRing O]

/-- `evalT` is additive on power series with decaying coefficients. -/
theorem evalT_add (z : σ → O) {h₁ h₂ : MvPowerSeries σ O}
    (hh₁ : Tendsto (fun d ↦ coeff d h₁) cofinite (𝓝 0))
    (hh₂ : Tendsto (fun d ↦ coeff d h₂) cofinite (𝓝 0)) :
    evalT z (h₁ + h₂) = evalT z h₁ + evalT z h₂ := by
  have hsum := (hasSum_evalT z hh₁).add (hasSum_evalT z hh₂)
  simp only [← add_mul, ← map_add] at hsum
  exact hsum.tsum_eq

theorem evalT_nsmul (z : σ → O) (n : ℕ) {h : MvPowerSeries σ O}
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    evalT z (n • h) = n • evalT z h := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, evalT_add z (decay_nsmul n hh) hh, ih]

theorem evalT_natCast_smul (z : σ → O) (n : ℕ) {h : MvPowerSeries σ O}
    (hh : Tendsto (fun d ↦ coeff d h) cofinite (𝓝 0)) :
    evalT z ((n : O) • h) = (n : O) • evalT z h := by
  rw [Nat.cast_smul_eq_nsmul, evalT_nsmul z n hh, Nat.cast_smul_eq_nsmul]

/-- The product of two coefficient-decaying power series again has decaying coefficients
(the coefficients are the Cauchy convolution of two null sequences). -/
theorem decay_mul {g₁ g₂ : MvPowerSeries σ O}
    (hh₁ : Tendsto (fun d ↦ coeff d g₁) cofinite (𝓝 0))
    (hh₂ : Tendsto (fun d ↦ coeff d g₂) cofinite (𝓝 0)) :
    Tendsto (fun d ↦ coeff d (g₁ * g₂)) cofinite (𝓝 0) := by
  classical
  have s₁ : Summable fun d ↦ coeff d g₁ :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hh₁
  have s₂ : Summable fun d ↦ coeff d g₂ :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hh₂
  have hs : Summable fun n ↦ coeff n (g₁ * g₂) :=
    (summable_sum_mul_antidiagonal_of_summable_mul (s₁.mul_of_nonarchimedean s₂)).congr
      fun n ↦ (coeff_mul n g₁ g₂).symm
  exact hs.tendsto_cofinite_zero

/-- `evalT` is multiplicative on power series with decaying coefficients: the Cauchy product
of the two convergent value series. -/
theorem evalT_mul (z : σ → O) {g₁ g₂ : MvPowerSeries σ O}
    (hh₁ : Tendsto (fun d ↦ coeff d g₁) cofinite (𝓝 0))
    (hh₂ : Tendsto (fun d ↦ coeff d g₂) cofinite (𝓝 0)) :
    evalT z (g₁ * g₂) = evalT z g₁ * evalT z g₂ := by
  classical
  have hprod := (hasSum_evalT z hh₁).mul_of_nonarchimedean (hasSum_evalT z hh₂)
  have hsig := (Equiv.hasSum_iff
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := σ →₀ ℕ))).mpr hprod
  have hg : HasSum (fun n : σ →₀ ℕ ↦ ∑ kl ∈ Finset.antidiagonal n,
      (coeff kl.1 g₁ * kl.1.prod fun s e ↦ z s ^ e)
        * (coeff kl.2 g₂ * kl.2.prod fun s e ↦ z s ^ e)) (evalT z g₁ * evalT z g₂) := by
    refine hsig.sigma fun n ↦ ?_
    rw [← Finset.sum_attach (Finset.antidiagonal n) fun kl ↦
      (coeff kl.1 g₁ * kl.1.prod fun s e ↦ z s ^ e)
        * (coeff kl.2 g₂ * kl.2.prod fun s e ↦ z s ^ e)]
    exact hasSum_fintype _
  have hfun : (fun n : σ →₀ ℕ ↦ ∑ kl ∈ Finset.antidiagonal n,
      (coeff kl.1 g₁ * kl.1.prod fun s e ↦ z s ^ e)
        * (coeff kl.2 g₂ * kl.2.prod fun s e ↦ z s ^ e))
      = fun n ↦ coeff n (g₁ * g₂) * n.prod fun s e ↦ z s ^ e := by
    funext n
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [Finset.mem_antidiagonal] at hkl
    rw [← hkl, Finsupp.prod_add_index' (fun a ↦ pow_zero (z a)) (fun a b1 b2 ↦ pow_add (z a) b1 b2)]
    ring
  rw [hfun] at hg
  exact (hasSum_evalT z (decay_mul hh₁ hh₂)).unique hg

theorem decay_pow {g : MvPowerSeries σ O}
    (hh : Tendsto (fun d ↦ coeff d g) cofinite (𝓝 0)) (n : ℕ) :
    Tendsto (fun d ↦ coeff d (g ^ n)) cofinite (𝓝 0) := by
  induction n with
  | zero => simpa using decay_one
  | succ n ih => rw [pow_succ]; exact decay_mul ih hh

/-- A product `∏ᵢ (b i)^{mᵢ}` of coefficient-decaying series has decaying coefficients. -/
theorem decay_prod {ι : Type*} {b : ι → MvPowerSeries σ O}
    (hb : ∀ s, Tendsto (fun d ↦ coeff d (b s)) cofinite (𝓝 0)) (m : ι →₀ ℕ) :
    Tendsto (fun d ↦ coeff d (m.prod fun s e ↦ b s ^ e)) cofinite (𝓝 0) := by
  classical
  induction m using Finsupp.induction with
  | zero => simpa using decay_one
  | single_add s n m' hs hn ih =>
    have hsplit : (Finsupp.single s n + m').prod (fun s' e ↦ b s' ^ e)
        = b s ^ n * m'.prod (fun s' e ↦ b s' ^ e) := by
      rw [Finsupp.prod_add_index' (fun a ↦ pow_zero (b a)) (fun a b1 b2 ↦ pow_add (b a) b1 b2)]
      congr 1
      exact Finsupp.prod_single_index (pow_zero (b s))
    rw [hsplit]
    exact decay_mul (decay_pow (hb s) n) ih

theorem evalT_pow (z : σ → O) {g : MvPowerSeries σ O}
    (hh : Tendsto (fun d ↦ coeff d g) cofinite (𝓝 0)) (n : ℕ) :
    evalT z (g ^ n) = evalT z g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, evalT_one]
  | succ n ih => rw [pow_succ, pow_succ, evalT_mul z (decay_pow hh n) hh, ih]

/-- `evalT` is multiplicative on products of powers of decaying series: it evaluates
`∏ᵢ (b i)^{mᵢ}` at the family of values `evalT z (b i)`. -/
theorem evalT_prod (z : σ → O) {ι : Type*} {b : ι → MvPowerSeries σ O}
    (hb : ∀ s, Tendsto (fun d ↦ coeff d (b s)) cofinite (𝓝 0)) (m : ι →₀ ℕ) :
    evalT z (m.prod fun s e ↦ b s ^ e) = m.prod fun s e ↦ evalT z (b s) ^ e := by
  classical
  induction m using Finsupp.induction with
  | zero => rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index, evalT_one]
  | single_add s n m' hs hn ih =>
    have hsplitb : (Finsupp.single s n + m').prod (fun s' e ↦ b s' ^ e)
        = b s ^ n * m'.prod (fun s' e ↦ b s' ^ e) := by
      rw [Finsupp.prod_add_index' (fun a ↦ pow_zero (b a)) (fun a b1 b2 ↦ pow_add (b a) b1 b2)]
      congr 1
      exact Finsupp.prod_single_index (pow_zero (b s))
    have hsplite : (Finsupp.single s n + m').prod (fun s' e ↦ evalT z (b s') ^ e)
        = evalT z (b s) ^ n * m'.prod (fun s' e ↦ evalT z (b s') ^ e) := by
      rw [Finsupp.prod_add_index' (fun a ↦ pow_zero (evalT z (b a)))
        (fun a b1 b2 ↦ pow_add (evalT z (b a)) b1 b2)]
      congr 1
      exact Finsupp.prod_single_index (pow_zero (evalT z (b s)))
    rw [hsplitb, hsplite, evalT_mul z (decay_pow (hb s) n) (decay_prod hb m'),
      evalT_pow z (hb s) n, ih]

variable {τ : Type*}

/-- Joint summability of the substitution terms `coeff_m g · coeff_e(∏ aᵐ) · zᵉ` over
`(m, e)`, by a two-regime argument: for each `𝔪ᵏ`, the `m` with `coeff_m g ∉ 𝔪ᵏ` are finite
(`g` decays), and for each such `m` the `e` with the term `∉ 𝔪ᵏ` are finite (`∏ aᵐ` decays). -/
private theorem summable_subst_terms (z : τ → O) {a : σ → MvPowerSeries τ O}
    {g : MvPowerSeries σ O} (hg : Tendsto (fun d ↦ coeff d g) cofinite (𝓝 0))
    (ha : ∀ s, Tendsto (fun d ↦ coeff d (a s)) cofinite (𝓝 0)) :
    Summable fun p : (σ →₀ ℕ) × (τ →₀ ℕ) ↦
      coeff p.1 g * (coeff p.2 (p.1.prod fun s e ↦ a s ^ e) * p.2.prod fun s e ↦ z s ^ e) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [(Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  rw [eventually_cofinite]
  have hgk : {m : σ →₀ ℕ | coeff m g ∉ (maximalIdeal O ^ k : Ideal O)}.Finite := by
    have h := (Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff.mp hg k
      trivial
    rwa [eventually_cofinite] at h
  have hEk : ∀ m : σ →₀ ℕ, {e : τ →₀ ℕ |
      coeff e (m.prod fun s e ↦ a s ^ e) * e.prod (fun s e ↦ z s ^ e)
        ∉ (maximalIdeal O ^ k : Ideal O)}.Finite := by
    intro m
    have hd : Tendsto (fun e ↦ coeff e (m.prod fun s e ↦ a s ^ e) * e.prod fun s e' ↦ z s ^ e')
        cofinite (𝓝 0) := PSeries.tendsto_mul_zero_of_tendsto_zero (decay_prod ha m)
    have h := (Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff.mp hd k
      trivial
    rwa [eventually_cofinite] at h
  refine Set.Finite.subset (hgk.biUnion fun m _ ↦ (hEk m).image (Prod.mk m)) ?_
  intro ⟨m, e⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, Prod.mk.injEq]
  refine ⟨m, fun hmem ↦ hp (Ideal.mul_mem_right _ _ hmem), e,
    fun hmem ↦ hp (Ideal.mul_mem_left _ _ hmem), rfl, rfl⟩

/-- **`evalT` composes with substitution**: evaluating a formal substitution at `z` is
evaluating the outer series at the family of values of the inner series. Both `g` and each
`a s` must have decaying coefficients. -/
theorem evalT_subst (z : τ → O) {a : σ → MvPowerSeries τ O} (ha_subst : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ O} (hg : Tendsto (fun d ↦ coeff d g) cofinite (𝓝 0))
    (ha : ∀ s, Tendsto (fun d ↦ coeff d (a s)) cofinite (𝓝 0)) :
    evalT z (subst a g) = evalT (fun s ↦ evalT z (a s)) g := by
  classical
  have hsum := (summable_subst_terms z hg ha).hasSum
  have hbym := hsum.prod_fiberwise fun m ↦ (hasSum_evalT z (decay_prod ha m)).mul_left (coeff m g)
  have hw : HasSum (fun m ↦ coeff m g * evalT z (m.prod fun s e ↦ a s ^ e))
      (evalT (fun s ↦ evalT z (a s)) g) := by
    refine (hasSum_evalT (fun s ↦ evalT z (a s)) hg).congr_fun fun m ↦ ?_
    rw [evalT_prod z ha m]
  have hswap := (Equiv.prodComm (τ →₀ ℕ) (σ →₀ ℕ)).hasSum_iff.mpr hsum
  have hbye := hswap.prod_fiberwise fun e ↦ by
    have hFS := coeff_subst_finite ha_subst g e
    have hFin : (Function.support fun m ↦ coeff m g •
        coeff e (m.prod fun s e' ↦ a s ^ e')).Finite := by
      simpa only [Function.HasFiniteSupport] using hFS
    have hce : HasSum (fun m ↦ coeff m g * coeff e (m.prod fun s e' ↦ a s ^ e'))
        (coeff e (subst a g)) := by
      have hkey : HasSum (fun m ↦ coeff m g • coeff e (m.prod fun s e' ↦ a s ^ e'))
          (coeff e (subst a g)) := by
        rw [show coeff e (subst a g)
            = ∑' m, coeff m g • coeff e (m.prod fun s e' ↦ a s ^ e') by
          rw [tsum_eq_finsum hFin]; exact coeff_subst ha_subst g e]
        exact (summable_of_hasFiniteSupport hFS).hasSum
      simpa only [smul_eq_mul] using hkey
    exact (funext fun m ↦ mul_assoc (coeff m g) (coeff e (m.prod fun s e' ↦ a s ^ e'))
      (e.prod fun s e' ↦ z s ^ e')) ▸ hce.mul_right (e.prod fun s e' ↦ z s ^ e')
  exact hbye.tsum_eq.trans (hbym.unique hw)

variable {z₀ : σ → O} (hz₀ : MvPowerSeries.HasEval z₀)

include hz₀ in
/-- The defining series of `MvPSeries.eval` converges. -/
theorem hasSum_eval (h : MvPowerSeries σ O) :
    HasSum (fun d : σ →₀ ℕ ↦ coeff d h * d.prod fun s e ↦ z₀ s ^ e) (eval z₀ h) :=
  hasSum_eval₂ continuous_id hz₀ h

include hz₀ in
theorem eval_eq_tsum (h : MvPowerSeries σ O) :
    eval z₀ h = ∑' d : σ →₀ ℕ, coeff d h * d.prod fun s e ↦ z₀ s ^ e :=
  (hasSum_eval hz₀ h).tsum_eq.symm

include hz₀ in
/-- On a legitimate (point-nilpotent) evaluation point, `evalT` agrees with `eval`. -/
theorem evalT_eq_eval (h : MvPowerSeries σ O) : evalT z₀ h = eval z₀ h :=
  (hasSum_eval hz₀ h).tsum_eq

/-- Evaluation at a legitimate point, as a ring homomorphism. -/
noncomputable def evalRingHom (hz₀ : MvPowerSeries.HasEval z₀) : MvPowerSeries σ O →+* O :=
  MvPowerSeries.eval₂Hom (φ := RingHom.id O) continuous_id hz₀

theorem coe_evalRingHom : ⇑(evalRingHom hz₀) = eval z₀ :=
  coe_eval₂Hom (φ := RingHom.id O) continuous_id hz₀

@[simp]
theorem evalRingHom_apply (h : MvPowerSeries σ O) : evalRingHom hz₀ h = eval z₀ h :=
  congrFun (coe_evalRingHom hz₀) h

theorem evalRingHom_comp_C :
    (evalRingHom hz₀).comp (MvPowerSeries.C : O →+* MvPowerSeries σ O) = RingHom.id O :=
  RingHom.ext fun a ↦ by simp

/-- A homomorphism out of `O` composed with evaluation still fixes the constants. -/
theorem comp_evalRingHom_comp_C {T : Type*} [Semiring T] (φ : O →+* T) :
    (φ.comp (evalRingHom hz₀)).comp (MvPowerSeries.C : O →+* MvPowerSeries σ O) = φ := by
  rw [RingHom.comp_assoc, evalRingHom_comp_C, RingHom.comp_id]

theorem continuous_evalRingHom : Continuous (evalRingHom hz₀) := by
  rw [coe_evalRingHom]
  exact continuous_eval₂ (φ := RingHom.id O) continuous_id hz₀

include hz₀

theorem eval_add (h₁ h₂ : MvPowerSeries σ O) :
    eval z₀ (h₁ + h₂) = eval z₀ h₁ + eval z₀ h₂ := by
  simpa using map_add (evalRingHom hz₀) h₁ h₂

theorem eval_mul (h₁ h₂ : MvPowerSeries σ O) :
    eval z₀ (h₁ * h₂) = eval z₀ h₁ * eval z₀ h₂ := by
  simpa using map_mul (evalRingHom hz₀) h₁ h₂

theorem eval_pow (h : MvPowerSeries σ O) (n : ℕ) : eval z₀ (h ^ n) = eval z₀ h ^ n := by
  simpa using map_pow (evalRingHom hz₀) h n

theorem eval_sub (h₁ h₂ : MvPowerSeries σ O) :
    eval z₀ (h₁ - h₂) = eval z₀ h₁ - eval z₀ h₂ := by
  simpa using map_sub (evalRingHom hz₀) h₁ h₂

/-- The value of a multivariate power series at a point of the maximal ideal is
congruent to its constant coefficient modulo the maximal ideal. -/
theorem eval_sub_constantCoeff_mem (hmem : ∀ i, z₀ i ∈ maximalIdeal O)
    (h : MvPowerSeries σ O) :
    eval z₀ h - constantCoeff h ∈ maximalIdeal O := by
  classical
  have htot := hasSum_eval hz₀ h
  have hupd := htot.update 0 0
  have hval (d : σ →₀ ℕ) : Function.update
      (fun d : σ →₀ ℕ ↦ coeff d h * d.prod fun s e ↦ z₀ s ^ e) 0 0 d
        ∈ maximalIdeal O := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [Function.update_of_ne hd]
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hi]
      refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ?_ _ ?_))
      · exact hmem i
      · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hmemsum : (∑' d, Function.update
      (fun d : σ →₀ ℕ ↦ coeff d h * d.prod fun s e ↦ z₀ s ^ e) 0 0 d)
        ∈ maximalIdeal O :=
    tsum_mem PSeries.isClosed_maximalIdeal hval
  rw [hupd.tsum_eq] at hmemsum
  simpa [Finsupp.prod_zero_index, zero_sub, neg_add_eq_sub] using hmemsum

include hz₀ in
/-- Values of a power series with constant coefficient in the maximal ideal lie in the
maximal ideal. -/
theorem eval_mem_maximalIdeal (hmem : ∀ i, z₀ i ∈ maximalIdeal O)
    (h : MvPowerSeries σ O) (hcc : constantCoeff h ∈ maximalIdeal O) :
    eval z₀ h ∈ maximalIdeal O := by
  simpa using Ideal.add_mem _ (eval_sub_constantCoeff_mem hz₀ hmem h) hcc

section algHomCompat

variable {τ : Type*} {ψ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O} (hψ : Continuous ψ)

include hψ

/-- The values of a continuous algebra homomorphism of power series rings at the
variables form a legitimate evaluation point. -/
theorem hasEval_eval_algHom :
    MvPowerSeries.HasEval fun s ↦ eval z₀ (ψ (MvPowerSeries.X s)) := by
  have hcont : Continuous ((MvPowerSeries.aeval hz₀).comp ψ) := by
    rw [AlgHom.coe_comp]
    exact (MvPowerSeries.continuous_aeval hz₀).comp hψ
  have hXs : (fun s ↦ ((MvPowerSeries.aeval hz₀).comp ψ) (MvPowerSeries.X s))
      = fun s ↦ eval z₀ (ψ (MvPowerSeries.X s)) := by
    funext s
    rw [AlgHom.comp_apply]
    exact congrFun (MvPowerSeries.coe_aeval hz₀) _
  exact hXs ▸ MvPowerSeries.HasEval.X.map hcont

/-- Evaluation along a continuous algebra homomorphism of power series rings is
evaluation at the images of the variables (by uniqueness of continuous algebra
homomorphisms). -/
theorem eval_algHom (h : MvPowerSeries τ O) :
    eval z₀ (ψ h) = eval (fun s ↦ eval z₀ (ψ (MvPowerSeries.X s))) h := by
  have hcont : Continuous ((MvPowerSeries.aeval hz₀).comp ψ) := by
    rw [AlgHom.coe_comp]
    exact (MvPowerSeries.continuous_aeval hz₀).comp hψ
  have happ := congrFun (congrArg DFunLike.coe (MvPowerSeries.aeval_unique hcont)) h
  have hXs : (fun s ↦ ((MvPowerSeries.aeval hz₀).comp ψ) (MvPowerSeries.X s))
      = fun s ↦ eval z₀ (ψ (MvPowerSeries.X s)) := by
    funext s
    rw [AlgHom.comp_apply]
    exact congrFun (MvPowerSeries.coe_aeval hz₀) _
  have h1 : ((MvPowerSeries.aeval hz₀).comp ψ) h = eval z₀ (ψ h) := by
    rw [AlgHom.comp_apply]
    exact congrFun (MvPowerSeries.coe_aeval hz₀) _
  have h2 : (MvPowerSeries.aeval (MvPowerSeries.HasEval.X.map hcont)) h
      = eval (fun s ↦ eval z₀ (ψ (MvPowerSeries.X s))) h := by
    rw [← hXs]
    exact congrFun (MvPowerSeries.coe_aeval _) h
  rw [← h1, ← happ, h2]

end algHomCompat

section subst

variable {τ : Type*} {a : τ → MvPowerSeries σ O} (ha : MvPowerSeries.HasSubst a)

include ha

/-- The family of values of a substitutable family is a legitimate evaluation point. -/
theorem hasEval_eval : MvPowerSeries.HasEval fun s ↦ eval z₀ (a s) := by
  have := hasEval_eval_algHom hz₀ (continuous_substAlgHom ha)
  simpa [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X ha] using this

/-- Evaluation of a (formal) substitution is evaluation at the evaluated family. -/
theorem eval_subst (h : MvPowerSeries τ O) :
    eval z₀ (MvPowerSeries.subst a h) = eval (fun s ↦ eval z₀ (a s)) h := by
  have := eval_algHom hz₀ (continuous_substAlgHom ha) h
  simpa [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X ha] using this

end subst

end MvPSeries

end ChabautyColeman

end

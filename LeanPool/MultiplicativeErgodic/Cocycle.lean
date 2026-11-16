/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.StrongMeasurability
public import LeanPool.MultiplicativeErgodic.Tempered
public import LeanPool.MultiplicativeErgodic.DetGrowth
public import LeanPool.MultiplicativeErgodic.BalancedKingman

/-!
# Cocycles, Lyapunov exponents, and the decomposition into fast/slow spaces

Corresponds to the "Growth statistics of a given cocycle" material and Section 5
("Decomposing a cocycle") of `proof_met.tex`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- A strongly measurable, forward-integrable random linear dynamical system
`(Ω, σ, μ, X, L)` with ergodic invertible base, i.e. a *cocycle* in the sense of the paper's
Introduction.

**The base is a Lebesgue probability space.** `[StandardBorelSpace Ω]` is a parameter and
`isProbability`/`nullSingleton` are fields, because the paper works throughout on "an ergodic
system on a Lebesgue probability space" and the cocycle results genuinely consume that: `χ_k` is
shown a.e. constant via `kingsyn`, which routes through `balancedKingman` and hence
`backwardVitali`, and those require exactly `[StandardBorelSpace Ω]`, `[IsProbabilityMeasure μ]`
and `[NullSingletonClass μ]`.

`isProbability` in particular was a genuine gap rather than an added restriction: `Ergodic σ μ`
unfolds to `MeasurePreserving + PreErgodic` and bundles no finiteness at all, so before this the
structure could not discharge `kingsyn`'s hypotheses — a working-practice note 4 defect (a
statement no intended caller can supply).

Carrying them as fields rather than as hypotheses on each theorem keeps the ripple to zero: every
`R : Cocycle Ω X` supplies them by `attribute [instance]` below, so no downstream signature in
`Cocycle.lean`, `Main.lean` or `Appendix.lean` changes. -/
structure Cocycle (Ω X : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] where
  /-- The invertible measurable base transformation. -/
  σ : Ω ≃ᵐ Ω
  /-- The invariant probability measure on the base. -/
  μ : Measure Ω
  /-- The strongly measurable forward-integrable operator family. -/
  L : Ω → X →L[ℝ] X
  isProbability : IsProbabilityMeasure μ
  nullSingleton : NullSingletonClass μ
  ergodic : Ergodic σ μ
  stronglyMeasurable : ∀ x : X, Measurable (fun ω => L ω x)
  forwardIntegrable : Integrable (fun ω => Real.log (max ‖L ω‖ 1)) μ

attribute [instance] Cocycle.isProbability Cocycle.nullSingleton

/-- `𝓛^{(n)}_ω`: the `n`-fold composition of the cocycle along the orbit of `ω`. -/
noncomputable def Cocycle.iterate (R : Cocycle Ω X) : ℕ → Ω → X →L[ℝ] X
  | 0, _ => ContinuousLinearMap.id ℝ X
  | n + 1, ω => (R.L (R.σ^[n] ω)).comp (R.iterate n ω)

/-- **The cocycle law.** `𝓛^{(m+n)}_ω = 𝓛^{(m)}_{σⁿω} ∘ 𝓛^{(n)}_ω`. -/
theorem Cocycle.iterate_add (R : Cocycle Ω X) (m n : ℕ) (ω : Ω) :
    R.iterate (m + n) ω = (R.iterate m (R.σ^[n] ω)).comp (R.iterate n ω) := by
  induction m with
  | zero => simp [Cocycle.iterate]
  | succ m ih =>
      have hstep : m + 1 + n = (m + n) + 1 := by omega
      rw [hstep]
      change (R.L (R.σ^[m + n] ω)).comp (R.iterate (m + n) ω) = _
      rw [ih]
      change _ = ((R.L (R.σ^[m] (R.σ^[n] ω))).comp (R.iterate m (R.σ^[n] ω))).comp
        (R.iterate n ω)
      rw [← Function.iterate_add_apply, ContinuousLinearMap.comp_assoc]

/-- `𝓛^{(1)}_ω = 𝓛_ω`. -/
theorem Cocycle.iterate_one (R : Cocycle Ω X) (ω : Ω) : R.iterate 1 ω = R.L ω := by
  change (R.L (R.σ^[0] ω)).comp (R.iterate 0 ω) = R.L ω
  simp [Cocycle.iterate]

/-- `𝓛^{(n+1)}_ω = 𝓛^{(n)}_{σω} ∘ 𝓛_ω`: the cocycle law read from the *left*, which is the form
that compares `ω` with `σω` (the definition of `iterate` peels off the last factor instead). -/
theorem Cocycle.iterate_succ_left (R : Cocycle Ω X) (n : ℕ) (ω : Ω) :
    R.iterate (n + 1) ω = (R.iterate n (R.σ ω)).comp (R.L ω) := by
  rw [R.iterate_add n 1 ω, R.iterate_one, Function.iterate_one]

/-- `log` valued in `EReal`, with `log 0 = ⊥`.

Mathlib's `Real.log 0 = 0` is a junk value, which is exactly wrong here: a Bernstein number
`ρ_k(T)` vanishes as soon as `k` exceeds the rank of `T`, and the exponent there is genuinely
`-∞`, not `0`. A finite-rank cocycle on an infinite-dimensional space hits this immediately. -/
noncomputable def logEReal (r : ℝ) : EReal := if r ≤ 0 then ⊥ else (Real.log r : EReal)

/-- The (limsup) growth rate of a single vector, `λ_ω(x) = limsup (1/n) log‖𝓛^{(n)}_ω x‖`, with
`log 0 = -∞` (`logEReal`).

**Corrected from `Real.log`.** Lean's `Real.log 0 = 0` is a junk value, and with it `λ_ω(0) = 0`,
as is `λ_ω(x)` for any `x` the cocycle eventually kills. The characterisation
`V(ω) = {x : λ_ω(x) ≤ λ₂}` (`cor:V-characterisation`, and the same clause of `mainres`) was
then false whenever `λ₂ < 0`: `0 ∈ V(ω)` but `λ_ω(0) = 0 > λ₂`. -/
noncomputable def Cocycle.lambdaAt (R : Cocycle Ω X) (ω : Ω) (x : X) : EReal :=
  Filter.limsup (fun n : ℕ => logEReal ‖R.iterate n ω x‖ / (n : EReal)) atTop

theorem logEReal_of_pos {r : ℝ} (hr : 0 < r) : logEReal r = (Real.log r : EReal) :=
  ite_eq_right (not_le.mpr hr)

theorem logEReal_of_nonpos {r : ℝ} (hr : r ≤ 0) : logEReal r = ⊥ := ite_eq_left hr

/-- `⊥ / n = ⊥` for `n ≥ 1`. Needed because `EReal` division sends `x / 0` to `0`, so the
`n = 0` term of a `limsup` over `atTop` carries no information and has to be stepped past. -/
theorem bot_div_natCast {n : ℕ} (hn : 1 ≤ n) : (⊥ : EReal) / (n : EReal) = ⊥ := by
  have hcoe : ((n : ℕ) : EReal) = (((n : ℝ)) : EReal) := (EReal.coe_coe_eq_natCast n).symm
  have h0 : (0 : EReal) < (n : EReal) := by
    rw [hcoe]
    exact_mod_cast (by exact_mod_cast hn : (1:ℝ) ≤ (n:ℝ)).trans_lt' zero_lt_one
  have ht : (n : EReal) ≠ ⊤ := by rw [hcoe]; exact EReal.coe_ne_top _
  exact EReal.bot_div_of_pos_ne_top h0 ht

/-- `log x / n ≤ r  ↔  x ≤ e^{rn}`, the bridge from the `EReal` exponent to a real inequality
about the Bernstein numbers themselves. The `x ≤ 0` branch is not a degenerate case to be
avoided: `ρ_k(T) = 0` is exactly the finite-rank situation, and there both sides hold. -/
theorem logEReal_div_le_iff {x : ℝ} {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    logEReal x / (n : EReal) ≤ (r : EReal) ↔ x ≤ Real.exp (r * n) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [logEReal_of_nonpos hx, bot_div_natCast hn]
    simp only [bot_le, true_iff]
    exact hx.trans (Real.exp_pos _).le
  · rw [logEReal_of_pos hx]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [show ((Real.log x : EReal) / (n : EReal)) = ((Real.log x / (n : ℝ) : ℝ) : EReal) from rfl,
      EReal.coe_le_coe_iff, div_le_iff₀ hn0, ← Real.log_le_iff_le_exp hx]

/-- Strict form of `logEReal_div_le_iff`. -/
theorem logEReal_div_lt_iff {x : ℝ} {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    logEReal x / (n : EReal) < (r : EReal) ↔ x < Real.exp (r * n) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [logEReal_of_nonpos hx, bot_div_natCast hn]
    simp only [bot_lt_iff_ne_bot, ne_eq, EReal.coe_ne_bot, not_false_eq_true, true_iff]
    exact hx.trans_lt (Real.exp_pos _)
  · rw [logEReal_of_pos hx]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [show ((Real.log x : EReal) / (n : EReal)) = ((Real.log x / (n : ℝ) : ℝ) : EReal) from rfl,
      EReal.coe_lt_coe_iff, div_lt_iff₀ hn0, ← Real.log_lt_iff_lt_exp hx]

/-- **The exponent is monotone under a one-step shift with a multiplicative slack.**

If `u_{n+1} ≤ c·v_n` for a fixed `c ≥ 0`, then `limsup (log u_n)/n ≤ limsup (log v_n)/n`. The
constant `c` and the index shift both wash out in the limit, but neither can be handled by
`EReal` arithmetic directly (`c` may force `log c = -∞`, and `(v_n + log c)/(n+1)` is not
comparable to `v_n/n` termwise when `v_n` is very negative). The argument therefore never
divides: it compares `u` and `v` against the real thresholds `e^{Mn}` supplied by
`logEReal_div_le_iff`.

This is what makes `χ_k(ω) ≤ χ_k(σω)`, via `ρ_k(𝓛^{(n+1)}_ω) ≤ ρ_k(𝓛^{(n)}_{σω})‖𝓛_ω‖`. -/
theorem limsup_logEReal_div_le {u v : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, u (n + 1) ≤ v n * c) :
    limsup (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop
      ≤ limsup (fun n : ℕ => logEReal (v n) / (n : EReal)) atTop := by
  set U := limsup (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop with hU
  set V := limsup (fun n : ℕ => logEReal (v n) / (n : EReal)) atTop with hV
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨M, hVM, hMU⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨M₀, hVM₀, hM₀M⟩ := EReal.lt_iff_exists_real_btwn.1 hVM
  have hM₀M' : M₀ < M := by exact_mod_cast hM₀M
  -- eventually `v n < e^{M₀ n}`
  have hev : ∀ᶠ n : ℕ in atTop, logEReal (v n) / (n : EReal) < (M₀ : EReal) :=
    eventually_lt_of_limsup_lt (hV ▸ hVM₀)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  -- eventually `c ≤ e^{(M - M₀)n + M}`
  have htend : Tendsto (fun n : ℕ => (M - M₀) * n + M) atTop atTop := by
    refine tendsto_atTop_add_const_right _ M ?_
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
  have hexp : ∀ᶠ n : ℕ in atTop, c ≤ Real.exp ((M - M₀) * n + M) :=
    (Real.tendsto_exp_atTop.comp htend).eventually_ge_atTop c
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hexp
  have hfin : ∀ᶠ m : ℕ in atTop, logEReal (u m) / (m : EReal) ≤ (M : EReal) := by
    refine eventually_atTop.2 ⟨N₁ + N₂ + 2, fun m hm => ?_⟩
    have hm1 : 1 ≤ m := by omega
    have hp1 : 1 ≤ m - 1 := by omega
    have hpN₁ : N₁ ≤ m - 1 := by omega
    have hpN₂ : N₂ ≤ m - 1 := by omega
    have hsub : m - 1 + 1 = m := by omega
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm1]; norm_num
    have hvn : v (m - 1) ≤ Real.exp (M₀ * ((m - 1 : ℕ) : ℝ)) :=
      ((logEReal_div_lt_iff hp1 M₀).1 (hN₁ _ hpN₁)).le
    have hstep : u m ≤ Real.exp (M * (m : ℝ)) := by
      have h1 : u m ≤ v (m - 1) * c := by
        have := h (m - 1); rwa [hsub] at this
      calc u m ≤ v (m - 1) * c := h1
        _ ≤ Real.exp (M₀ * ((m - 1 : ℕ) : ℝ)) * c := mul_le_mul_of_nonneg_right hvn hc
        _ ≤ Real.exp (M₀ * ((m - 1 : ℕ) : ℝ)) *
              Real.exp ((M - M₀) * ((m - 1 : ℕ) : ℝ) + M) :=
            mul_le_mul_of_nonneg_left (hN₂ _ hpN₂) (Real.exp_pos _).le
        _ = Real.exp (M * (m : ℝ)) := by
            rw [← Real.exp_add, hcast]; ring_nf
    exact (logEReal_div_le_iff hm1 M).2 hstep
  have hle : U ≤ (M : EReal) := by
    calc U ≤ limsup (fun _ : ℕ => (M : EReal)) atTop := limsup_le_limsup hfin
      _ = (M : EReal) := limsup_const _
  exact absurd hle (not_le.2 hMU)

namespace ChiOrder

/-! ### Order-theoretic input to `chi_antitone`

The growth/Bernstein facts below would sit naturally in `ProofMet/GrowthFunction.lean`; they
are kept here, in their own namespace, so that adding them cannot collide with that file. -/

/-- `logEReal` is monotone. Below `0` it is constantly `⊥`, which is what makes this true
without a positivity hypothesis. -/
theorem logEReal_mono {r s : ℝ} (h : r ≤ s) : logEReal r ≤ logEReal s := by
  rcases le_or_gt r 0 with hr | hr
  · rw [logEReal_of_nonpos hr]; exact bot_le
  · rw [logEReal_of_pos hr, logEReal_of_pos (hr.trans_le h)]
    exact_mod_cast Real.log_le_log hr h

omit [MeasurableSpace X] in
/-- `g_T` is antitone in the subspace: a larger subspace offers more unit vectors for the
infimum to run over.

`W ≠ ⊥` is load-bearing rather than decorative: `g_T(⊥) = sInf ∅ = 0`, so for `W = ⊥` the
conclusion would say `g_T(V) ≤ 0`, false for any `T` with `g_T(V) > 0`. -/
theorem growth_le_growth {T : X →L[ℝ] X} {W V : Submodule ℝ X} (hWV : W ≤ V) (hW : W ≠ ⊥) :
    growth T V ≤ growth T W := by
  have hne : (Metric.sphere (0 : X) 1 ∩ (W : Set X)).Nonempty := by
    obtain ⟨x0, hx0W, hx0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨‖x0‖⁻¹ • x0,
      mem_sphere_zero_iff_norm.2
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0ne)]),
      W.smul_mem _ hx0W⟩
  apply le_csInf (hne.image _)
  rintro _ ⟨x, ⟨hxs, hxW⟩, rfl⟩
  exact csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨x, ⟨hxs, hWV hxW⟩, rfl⟩

omit [MeasurableSpace X] in
/-- `0 ≤ ρ_k(T)`, junk case included: when `dim X < k` the supremum is over `∅` and equals `0`. -/
theorem bernsteinNumber_nonneg (T : X →L[ℝ] X) (k : ℕ) : 0 ≤ bernsteinNumber T k :=
  MultiplicativeErgodic.bernsteinNumber_nonneg T k

omit [MeasurableSpace X] in
/-- A `(k+2)`-dimensional subspace contains a nonzero `(k+1)`-dimensional one: span all but the
last vector of a basis. Phrased with `k + 1 + 1` / `k + 1` rather than `k + 1` / `k` because
the `k = 0` instance is exactly the one the caller must not have (see
`bernsteinNumber_succ_le`). -/
theorem exists_finrank_succ_le {V : Submodule ℝ X} (hfd : FiniteDimensional ℝ V) {k : ℕ}
    (hV : Module.finrank ℝ V = k + 1 + 1) :
    ∃ W : Submodule ℝ X, W ≤ V ∧ FiniteDimensional ℝ W ∧
      Module.finrank ℝ W = k + 1 ∧ W ≠ ⊥ := by
  have := hfd
  obtain ⟨W, hWV, hWfd, hWdim⟩ :=
    exists_le_finrank_eq' V (l := k + 1) (by omega)
  refine ⟨W, hWV, hWfd, hWdim, ?_⟩
  intro hbot
  rw [hbot, finrank_bot] at hWdim
  omega

omit [MeasurableSpace X] in
/-- **`ρ` is antitone from index `1` on.** Every `(k+2)`-dimensional subspace contains a
`(k+1)`-dimensional one, on which `g_T` is at least as large, so the supremum over
`𝒢_{k+2}` is at most the supremum over `𝒢_{k+1}`.

The shift is not cosmetic: `ρ_0(T) = g_T(⊥) = 0`, so `ρ_1 ≤ ρ_0` fails for every `T ≠ 0`.
This is the same junk index `χ_0 = ⊥` that `Cocycle.chi`'s statements are shifted past. -/
theorem bernsteinNumber_succ_le (T : X →L[ℝ] X) (k : ℕ) :
    bernsteinNumber T (k + 1 + 1) ≤ bernsteinNumber T (k + 1) := by
  refine Real.sSup_le ?_ (bernsteinNumber_nonneg T (k + 1))
  rintro _ ⟨V, rfl⟩
  obtain ⟨W, hWV, hWfd, hWrank, hWne⟩ := exists_finrank_succ_le V.2.1 V.2.2
  refine le_trans (growth_le_growth hWV hWne) ?_
  refine le_csSup ⟨‖T‖, ?_⟩ ⟨⟨W, hWfd, hWrank⟩, rfl⟩
  rintro _ ⟨U, rfl⟩
  exact growth_le_opNorm T _

end ChiOrder

/-- **`χ_k`: the `k`-th Lyapunov exponent, counted with multiplicity.**

`χ_k(ω) = limsup_n (1/n) log ρ_k(𝓛^{(n)}_ω)`, where `ρ_k` is the `k`-th Bernstein number
(`bernsteinNumber`). This is part of the *definition* of the cocycle's growth data: it is a
total function `ℕ → Ω → EReal`, defined for every `ω` with no hypothesis and no choice.

**`EReal`-valued, and genuinely so.** `ρ_k(𝓛^{(n)}_ω) = 0` forces `χ_k(ω) = ⊥`, and that is
attained in finite time rather than only in the limit: once `ρ_k` vanishes at some `n₀`,
submultiplicativity keeps it zero forever. Restricting to `ℝ` would either exclude
finite-rank cocycles or (with `Real.log 0 = 0`) silently compute the wrong number.

**Index convention.** `k` counts from `1`. `χ_0` is the junk value `⊥`, because
`GrassmannianFin X 0` contributes only the zero subspace, whose unit sphere is empty, so
`ρ_0 = 0`. Statements about `χ` are therefore phrased over `χ (k + 1)`.

That `χ_k` is a.e.\ *constant* is a theorem about ergodic systems, not part of this definition —
see `Cocycle.exists_chi_ae_const`. -/
noncomputable def Cocycle.chi (R : Cocycle Ω X) (k : ℕ) (ω : Ω) : EReal :=
  Filter.limsup
    (fun n : ℕ => logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal)) atTop

/-- **The index at which `λ_i` first occurs.** `lambdaIdx R 0 ω = 1`, and `lambdaIdx R (i+1) ω`
is the least `t ≥ 1` with `χ_t(ω) < χ_{lambdaIdx R i ω}(ω)`.

Introducing the indices explicitly, rather than only the values `λ_i`, is what makes the
multiplicities `m_i` definable at the same time (`Cocycle.mult`) instead of being pulled out of
the air later. When the defining set is empty — the list of distinct exponents has ended —
`Nat.sInf ∅ = 0`, and that `0` propagates to `mult` as the marker "no further exponent". -/
noncomputable def Cocycle.lambdaIdx (R : Cocycle Ω X) : ℕ → Ω → ℕ
  | 0, _ => 1
  | (i + 1), ω => sInf {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx i ω) ω}

/-- **`λ_i`: the *distinct* Lyapunov exponents.** `Cocycle.lambda R i` is the paper's
`λ_{i+1}`, so `lambda R 0 = λ₁ = χ₁`.

Like `χ` this is a total `EReal`-valued function of `ω`, with no finiteness assumed. When the
list of distinct exponents has ended the index is `0` and the value is `χ_0 = ⊥`; that junk
value is the intended reading. The paper's recursion is recovered as `Cocycle.lambda_succ`. -/
noncomputable def Cocycle.lambda (R : Cocycle Ω X) (i : ℕ) (ω : Ω) : EReal :=
  R.chi (R.lambdaIdx i ω) ω

@[simp] theorem Cocycle.lambda_zero (R : Cocycle Ω X) (ω : Ω) : R.lambda 0 ω = R.chi 1 ω := rfl

/-- The paper's recursion `λ_{i+1} = χ_{inf{t ≥ 1 : χ_t < λ_i}}`, now a consequence of the
index-based definition rather than the definition itself. -/
theorem Cocycle.lambda_succ (R : Cocycle Ω X) (i : ℕ) (ω : Ω) :
    R.lambda (i + 1) ω = R.chi (sInf {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.lambda i ω}) ω := rfl

/-- **`m_i`: the multiplicity of the `i`-th distinct Lyapunov exponent**, i.e. the number of `k`
with `χ_k = λ_i`. Because `χ` is antitone (`Cocycle.chi_antitone`) that set is the index interval
`[lambdaIdx i, lambdaIdx (i+1))`, so the multiplicity is the difference of consecutive indices.

`m_i = 0` is the junk value marking "there is no `(i+1)`-st distinct exponent", i.e. `λ_i` is the
last one and occurs with infinite multiplicity. For a quasicompact cocycle `m_1 ≥ 1`
(`Cocycle.mult_zero_pos`); how many of the later `m_i` are nonzero — finitely or infinitely many
— is not determined by quasicompactness alone. -/
noncomputable def Cocycle.mult (R : Cocycle Ω X) (i : ℕ) (ω : Ω) : ℕ :=
  R.lambdaIdx (i + 1) ω - R.lambdaIdx i ω

/-- `ν(ω) = lim_{k→∞} χ_k(ω)`, realised as the infimum of the antitone sequence `χ_{k+1}`. -/
noncomputable def Cocycle.nu (R : Cocycle Ω X) (ω : Ω) : EReal := ⨅ k : ℕ, R.chi (k + 1) ω

/-- **Definition.** `𝓛` is quasicompact iff `ν < χ_1` almost everywhere (recall
`ρ_1(T) = ‖T‖`, so `χ_1 = λ_1` is the top Lyapunov exponent).

Stated a.e.\ rather than pointwise because `χ` and `ν` are not yet known to be constant; under
`Cocycle.exists_chi_ae_const` the two readings agree. -/
def Cocycle.IsQuasicompact (R : Cocycle Ω X) : Prop :=
  ∀ᵐ ω ∂(R.μ), R.nu ω < R.chi 1 ω

/-- **`χ_k` is sub-invariant:** `χ_k(ω) ≤ χ_k(σω)`, pointwise and with no hypotheses.

The reverse inequality is *not* available — it would need `𝓛_ω` to be invertible, which the
semi-invertible setting explicitly does not assume — and is not needed:
`exists_ae_const_of_le_comp` upgrades sub-invariance to a.e. invariance using only that `σ`
preserves `μ`. -/
theorem Cocycle.chi_le_chi_shift (R : Cocycle Ω X) (k : ℕ) (ω : Ω) :
    R.chi k ω ≤ R.chi k (R.σ ω) :=
  limsup_logEReal_div_le (norm_nonneg (R.L ω)) fun n => by
    rw [R.iterate_succ_left n ω]
    exact bernsteinNumber_comp_le_mul_norm _ _ k

/-- Each iterate of a strongly measurable cocycle is strongly measurable, by induction on `n`
through `measurable_apply_of_weak`. -/
theorem Cocycle.measurable_iterate_apply (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (n : ℕ) (x : X) : Measurable fun ω => R.iterate n ω x := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable fun ω => R.L (R.σ^[n] ω) (R.iterate n ω x)
      exact measurable_apply_of_weak
        (fun y => (R.stronglyMeasurable y).comp (R.σ.measurable.iterate n)) ih

/-- `r ↦ (log r)/n` as a map `ℝ → EReal` is measurable. Both branches of `logEReal` are handled
uniformly: `coe_div_natCast` is definitional, so the positive branch is literally the coercion of
a real quotient, and the nonpositive branch is the constant `⊥/n`. -/
theorem measurable_logEReal_div (n : ℕ) :
    Measurable fun r : ℝ => logEReal r / (n : EReal) := by
  have heq : ∀ r : ℝ, logEReal r / (n : EReal)
      = if r ≤ 0 then ((⊥ : EReal) / (n : EReal)) else (((Real.log r / n : ℝ)) : EReal) := by
    intro r
    by_cases hr : r ≤ 0
    · rw [ite_eq_left hr, logEReal_of_nonpos hr]
    · rw [ite_eq_right hr, logEReal_of_pos (not_le.1 hr)]
      rfl
  simp_rw [heq]
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  exact (Real.measurable_log.div_const _).coe_real_ereal

/-- `χ_k` is measurable. This is where separability of `X` is used twice over: once for the
Grassmannian (a countable dense family of subspaces) and once for each unit sphere. -/
theorem Cocycle.measurable_chi (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] (k : ℕ)
    [NeZero k] : Measurable (R.chi k) :=
  Measurable.limsup fun n =>
    (measurable_logEReal_div n).comp
      (measurable_bernstein_of_weak k (R.measurable_iterate_apply n))

/-- `χ_0 = ⊥` everywhere: the junk index. -/
theorem Cocycle.chi_zero (R : Cocycle Ω X) (ω : Ω) : R.chi 0 ω = ⊥ := by
  have heq : ∀ᶠ n : ℕ in atTop,
      logEReal (bernsteinNumber (R.iterate n ω) 0) / (n : EReal) = ⊥ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [bernsteinNumber_zero, logEReal_of_nonpos le_rfl, bot_div_natCast hn]
  change limsup _ atTop = ⊥
  rw [limsup_congr heq]
  exact limsup_const _

/-- **Degeneracy is forward-absorbing.** If `ρ_k(𝓛^{(n₀)}_ω) = 0` then `ρ_k(𝓛^{(n)}_ω) = 0` for
every `n ≥ n₀`: the later iterate factors through the degenerate one. -/
theorem Cocycle.bernstein_eq_zero_of_le (R : Cocycle Ω X) (k : ℕ) (ω : Ω) {n₀ n : ℕ}
    (h₀ : bernsteinNumber (R.iterate n₀ ω) k = 0) (hn : n₀ ≤ n) :
    bernsteinNumber (R.iterate n ω) k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + n₀ := ⟨n - n₀, by omega⟩
  refine le_antisymm ?_ (bernsteinNumber_nonneg _ k)
  rw [R.iterate_add m n₀ ω]
  have := bernsteinNumber_comp_le_norm_mul (R.iterate m (R.σ^[n₀] ω)) (R.iterate n₀ ω) k
  rw [h₀, mul_zero] at this
  exact this

/-- The set where the cocycle is eventually `ρ_k`-degenerate. -/
def Cocycle.degenerate (R : Cocycle Ω X) (k : ℕ) : Set Ω :=
  {ω | ∃ n : ℕ, 1 ≤ n ∧ bernsteinNumber (R.iterate n ω) k = 0}

/-- `σ⁻¹(degenerate) ⊆ degenerate`: if `𝓛^{(n)}_{σω}` is degenerate then so is `𝓛^{(n+1)}_ω`,
which factors through it. Equivalently the *complement* is forward invariant, which is what makes
the dichotomy below available. -/
theorem Cocycle.preimage_degenerate_subset (R : Cocycle Ω X) (k : ℕ) :
    (R.σ) ⁻¹' (R.degenerate k) ⊆ R.degenerate k := by
  rintro ω ⟨n, hn1, hn0⟩
  refine ⟨n + 1, by omega, ?_⟩
  refine le_antisymm ?_ (bernsteinNumber_nonneg _ k)
  rw [R.iterate_succ_left n ω]
  have := bernsteinNumber_comp_le_mul_norm (R.iterate n (R.σ ω)) (R.L ω) k
  rw [hn0, zero_mul] at this
  exact this

/-- On the degenerate set the exponent sequence is eventually `⊥`, so it converges — trivially —
and `χ_k = ⊥` there. -/
theorem Cocycle.tendsto_chi_of_degenerate (R : Cocycle Ω X) (k : ℕ) {ω : Ω}
    (hω : ω ∈ R.degenerate k) :
    Tendsto (fun n : ℕ => logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal))
      atTop (nhds ⊥) ∧ R.chi k ω = ⊥ := by
  obtain ⟨n₀, hn₀1, hn₀⟩ := hω
  have hev : ∀ᶠ n : ℕ in atTop,
      logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal) = ⊥ := by
    filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
    rw [R.bernstein_eq_zero_of_le k ω hn₀ (le_trans (le_max_left _ _) hn),
      logEReal_of_nonpos le_rfl, bot_div_natCast (le_trans (le_max_right _ _) hn)]
  constructor
  · exact Tendsto.congr' (hev.mono fun n h => h.symm) tendsto_const_nhds
  · change limsup _ atTop = ⊥
    rw [limsup_congr hev]
    exact limsup_const _

theorem Cocycle.measurableSet_degenerate (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k : ℕ) [NeZero k] : MeasurableSet (R.degenerate k) := by
  have heq : R.degenerate k
      = ⋃ n : ℕ, {ω | 1 ≤ n ∧ bernsteinNumber (R.iterate n ω) k = 0} := by
    ext ω
    simp [Cocycle.degenerate]
  rw [heq]
  refine MeasurableSet.iUnion fun n => ?_
  by_cases h : 1 ≤ n
  · simp only [h, true_and]
    exact measurableSet_eq_fun
      (measurable_bernstein_of_weak k (R.measurable_iterate_apply n)) measurable_const
  · simp [h]

/-- **Degeneracy is an all-or-nothing property of the cocycle.** The degenerate set is
backward-invariant, so ergodicity makes it null or conull. -/
theorem Cocycle.measure_degenerate_eq_zero_or_one (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] (k : ℕ) [NeZero k] :
    R.μ (R.degenerate k) = 0 ∨ R.μ (R.degenerate k) = 1 := by
  rcases R.ergodic.ae_empty_or_univ_of_preimage_ae_le
      (R.measurableSet_degenerate k).nullMeasurableSet
      (LE.le.eventuallyLE (R.preimage_degenerate_subset k)) with h | h
  · exact Or.inl (by rw [measure_congr h, measure_empty])
  · exact Or.inr (by rw [measure_congr h, measure_univ])

/-- In `EReal`, a `limsup` of `⊥` is already a limit. -/
theorem tendsto_of_limsup_eq_bot {u : ℕ → EReal} (h : limsup u atTop = ⊥) :
    Tendsto u atTop (nhds ⊥) := by
  have hli : liminf u atTop = ⊥ :=
    le_bot_iff.1 (h ▸ liminf_le_limsup)
  exact tendsto_of_liminf_eq_limsup hli h

/-- **The `⊥` case of `chi-converges` is free.** Whenever `χ_k(ω) = ⊥` the exponent sequence
converges to `χ_k(ω)` with no Kingman input at all, because a `limsup` of `⊥` is a limit.

This is what reduces `Cocycle.ae_tendsto_chi` to the case `χ_k > ⊥`: it covers the degenerate
set `Cocycle.degenerate` and also the non-degenerate `ω` at which the products
`∏_{i≤k} ρ_i(𝓛^{(n)}_ω)` stay positive but decay super-exponentially. -/
theorem Cocycle.tendsto_chi_of_eq_bot (R : Cocycle Ω X) (k : ℕ) {ω : Ω} (h : R.chi k ω = ⊥) :
    Tendsto (fun n : ℕ => logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal))
      atTop (nhds (R.chi k ω)) := by
  rw [h]
  exact tendsto_of_limsup_eq_bot h

/-- The real-analysis core of the truncated family's subadditivity: a floor `a*b` splits as
`a` and `b`, so flooring a submultiplicative quantity keeps it submultiplicative. -/
theorem log_max_le_of_le_mul {K P Q R a b : ℝ} (hK : 1 ≤ K) (hR : 0 ≤ R)
    (ha : 0 < a) (hb : 0 < b) (h : P ≤ K * (Q * R)) :
    Real.log (max P (a * b)) ≤ Real.log (max Q a) + Real.log (max R b) + Real.log K := by
  have hQa : 0 < max Q a := lt_of_lt_of_le ha (le_max_right _ _)
  have hRb : 0 < max R b := lt_of_lt_of_le hb (le_max_right _ _)
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
  have hmul : max P (a * b) ≤ K * (max Q a * max R b) := by
    refine max_le ?_ ?_
    · refine h.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hKpos.le
      exact mul_le_mul (le_max_left _ _) (le_max_left _ _) hR (le_of_lt hQa)
    · refine le_trans ?_ (le_mul_of_one_le_left (by positivity) hK)
      exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hb.le (le_of_lt hQa)
  have hpos : (0 : ℝ) < max P (a * b) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  calc Real.log (max P (a * b)) ≤ Real.log (K * (max Q a * max R b)) :=
        Real.log_le_log hpos hmul
    _ = Real.log K + (Real.log (max Q a) + Real.log (max R b)) := by
        rw [Real.log_mul (ne_of_gt hKpos) (by positivity),
          Real.log_mul (ne_of_gt hQa) (ne_of_gt hRb)]
    _ = Real.log (max Q a) + Real.log (max R b) + Real.log K := by ring

/-- `∏_{i≤k} ρ_i(𝓛^{(n)}_ω)`. -/
noncomputable def Cocycle.prodBern (R : Cocycle Ω X) (k n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range k, bernsteinNumber (R.iterate n ω) (i + 1)

theorem Cocycle.prodBern_nonneg (R : Cocycle Ω X) (k n : ℕ) (ω : Ω) : 0 ≤ R.prodBern k n ω :=
  Finset.prod_nonneg fun _i _ => bernsteinNumber_nonneg _ _

/-- `log` of the Bernstein product, floored at `e^{-Mn}` so that it is real-valued *everywhere*,
including where the cocycle degenerates. The floor is exactly Kingman's own truncation
`max (f n ω) (-(M n))` transported through `log`. -/
noncomputable def Cocycle.logProdTrunc (R : Cocycle Ω X) (k M n : ℕ) (ω : Ω) : ℝ :=
  Real.log (max (R.prodBern k n ω) (Real.exp (-(M : ℝ) * n)))

/-- **The truncated Bernstein-product family is weakly subadditive, with a slack constant that
does not depend on the truncation level `M`.** This is what lets Kingman be applied at every `M`
at once, which is the shape `ae_tendsto_of_ae_tendsto_max` consumes. -/
theorem Cocycle.exists_logProdTrunc_subadditive (R : Cocycle Ω X) (k : ℕ) :
    ∃ c : ℝ, ∀ (M m n : ℕ) (ω : Ω),
      R.logProdTrunc k M (m + n) ω
        ≤ R.logProdTrunc k M m (R.σ^[n] ω) + R.logProdTrunc k M n ω + c := by
  obtain ⟨K, hKpos, hK⟩ := exists_prod_bernstein_submultiplicative (X := X) k
  refine ⟨Real.log (max K 1), fun M m n ω => ?_⟩
  have hK1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  have hsub : R.prodBern k (m + n) ω
      ≤ max K 1 * (R.prodBern k m (R.σ^[n] ω) * R.prodBern k n ω) := by
    have h := hK (R.iterate m (R.σ^[n] ω)) (R.iterate n ω)
    rw [← R.iterate_add m n ω] at h
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact mul_nonneg (R.prodBern_nonneg k m _) (R.prodBern_nonneg k n ω)
  have hexp : Real.exp (-(M : ℝ) * (m + n : ℕ))
      = Real.exp (-(M : ℝ) * m) * Real.exp (-(M : ℝ) * n) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  change Real.log (max (R.prodBern k (m + n) ω) (Real.exp (-(M : ℝ) * (m + n : ℕ)))) ≤ _
  rw [hexp]
  exact log_max_le_of_le_mul hK1 (R.prodBern_nonneg k n ω)
    (Real.exp_pos _) (Real.exp_pos _) hsub

/-- `ρ_k(T) ≤ ‖T‖` with no nonemptiness hypothesis: when `𝒢_kX` is empty the supremum is over
`∅` and equals `0`. -/
theorem bernsteinNumber_le_opNorm' {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : Y →L[ℝ] Y) (k : ℕ) : bernsteinNumber T k ≤ ‖T‖ :=
  bernsteinNumber_le_opNorm T k

/-- `∏_{i≤k} ρ_i(T) ≤ ‖T‖^k`. -/
theorem prod_bernstein_le_opNorm_pow {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : Y →L[ℝ] Y) (k : ℕ) :
    ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) ≤ ‖T‖ ^ k := by
  calc ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1)
      ≤ ∏ _i ∈ Finset.range k, ‖T‖ :=
        Finset.prod_le_prod₀ (fun i _ => bernsteinNumber_nonneg _ _)
          (fun i _ => bernsteinNumber_le_opNorm' T (i + 1))
    _ = ‖T‖ ^ k := by rw [Finset.prod_const, Finset.card_range]

/-- The truncated family is measurable in `ω`. -/
theorem Cocycle.measurable_logProdTrunc (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k M n : ℕ) : Measurable (R.logProdTrunc k M n) := by
  have hprod : Measurable (R.prodBern k n) := by
    refine Finset.measurable_prod _ fun i _ => ?_
    have : NeZero (i + 1) := ⟨Nat.succ_ne_zero i⟩
    exact measurable_bernstein_of_weak (i + 1) (fun x => R.measurable_iterate_apply n x)
  exact Real.measurable_log.comp (hprod.max measurable_const)

/-- **The one-step truncated value is dominated by `k·log⁺‖𝓛_ω‖`**, which is integrable by the
cocycle's `forwardIntegrable` field. This is Kingman's sharp hypothesis `∫ (f_1)⁺ < ∞`. -/
theorem Cocycle.logProdTrunc_one_le (R : Cocycle Ω X) (k M : ℕ) (ω : Ω) :
    R.logProdTrunc k M 1 ω ≤ (k : ℝ) * Real.log (max ‖R.L ω‖ 1) := by
  have hmax1 : (1 : ℝ) ≤ max ‖R.L ω‖ 1 := le_max_right _ _
  have hiter : R.iterate 1 ω = R.L ω := R.iterate_one ω
  have hprod : R.prodBern k 1 ω ≤ (max ‖R.L ω‖ 1) ^ k := by
    change ∏ i ∈ Finset.range k, bernsteinNumber (R.iterate 1 ω) (i + 1) ≤ _
    rw [hiter]
    refine (prod_bernstein_le_opNorm_pow (R.L ω) k).trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) k
  have hfloor : Real.exp (-(M : ℝ) * (1 : ℕ)) ≤ (max ‖R.L ω‖ 1) ^ k := by
    refine le_trans ?_ (one_le_pow₀ hmax1)
    rw [Real.exp_le_one_iff]
    push_cast
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hle : max (R.prodBern k 1 ω) (Real.exp (-(M : ℝ) * (1 : ℕ)))
      ≤ (max ‖R.L ω‖ 1) ^ k := max_le hprod hfloor
  have hpos : (0 : ℝ) < max (R.prodBern k 1 ω) (Real.exp (-(M : ℝ) * (1 : ℕ))) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  change Real.log (max (R.prodBern k 1 ω) (Real.exp (-(M : ℝ) * (1 : ℕ)))) ≤ _
  calc Real.log (max (R.prodBern k 1 ω) (Real.exp (-(M : ℝ) * (1 : ℕ))))
      ≤ Real.log ((max ‖R.L ω‖ 1) ^ k) := Real.log_le_log hpos hle
    _ = (k : ℝ) * Real.log (max ‖R.L ω‖ 1) := by
        rw [Real.log_pow]

theorem Cocycle.integrable_logProdTrunc_posPart (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] (k M : ℕ) :
    Integrable (fun ω => max (R.logProdTrunc k M 1 ω) 0) R.μ := by
  have hg : Integrable (fun ω => (k : ℝ) * Real.log (max ‖R.L ω‖ 1)) R.μ :=
    R.forwardIntegrable.const_mul _
  refine Integrable.mono' hg
    (((R.measurable_logProdTrunc k M 1).max measurable_const).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine max_le (R.logProdTrunc_one_le k M ω) ?_
  have h1 : (0 : ℝ) ≤ Real.log (max ‖R.L ω‖ 1) := Real.log_nonneg (le_max_right _ _)
  positivity

omit [MeasurableSpace X] in
/-- The Bernstein product vanishes exactly when its last factor does, `ρ` being antitone. -/
theorem prod_bernstein_eq_zero_iff (T : X →L[ℝ] X) {k : ℕ} (hk : 1 ≤ k) :
    (∏ i ∈ Finset.range k, bernsteinNumber T (i + 1)) = 0 ↔ bernsteinNumber T k = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi, hzero⟩ := Finset.prod_eq_zero_iff.1 h
    rw [Finset.mem_range] at hi
    refine le_antisymm ?_ (bernsteinNumber_nonneg T k)
    rw [← hzero]
    -- `ρ` is antitone from index 1 on, so `ρ_k ≤ ρ_{i+1}` for `i + 1 ≤ k`
    have hanti : ∀ p q : ℕ, 1 ≤ p → p ≤ q → bernsteinNumber T q ≤ bernsteinNumber T p := by
      intro p q hp hpq
      induction q with
      | zero => omega
      | succ q ih =>
          rcases Nat.lt_or_ge p (q + 1) with hlt | hge
          · refine le_trans ?_ (ih (by omega))
            obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
            exact ChiOrder.bernsteinNumber_succ_le T j
          · have : p = q + 1 := by omega
            rw [this]
    exact hanti (i + 1) k (by omega) (by omega)
  · intro h
    refine Finset.prod_eq_zero (Finset.mem_range.2 (by omega : k - 1 < k)) ?_
    rw [show k - 1 + 1 = k from by omega]
    exact h

theorem Cocycle.logProdTrunc_ge (R : Cocycle Ω X) (k M n : ℕ) (ω : Ω) :
    -((M : ℝ) * n) ≤ R.logProdTrunc k M n ω := by
  have h1 : Real.exp (-(M : ℝ) * n) ≤ max (R.prodBern k n ω) (Real.exp (-(M : ℝ) * n)) :=
    le_max_right _ _
  have h2 : (0 : ℝ) < Real.exp (-(M : ℝ) * n) := Real.exp_pos _
  change -((M : ℝ) * n) ≤ Real.log (max (R.prodBern k n ω) (Real.exp (-(M : ℝ) * n)))
  calc -((M : ℝ) * n) = Real.log (Real.exp (-(M : ℝ) * n)) := by rw [Real.log_exp]; ring
    _ ≤ _ := Real.log_le_log h2 h1

/-- **Kingman at one truncation level.** The truncated family is weakly subadditive with a flat
slack, so shifting by that slack makes it a genuine `SubadditiveFamily`; its one-step positive
part is integrable, and the limit is finite because the family is bounded below by `-Mn`. -/
theorem Cocycle.exists_logProdTrunc_limit (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k M : ℕ) :
    ∃ r : ℝ, (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => R.logProdTrunc k M n ω / n) atTop (nhds r)) ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        R.logProdTrunc k M (2 * n) (zIter R.σ (-(n : ℤ)) ω) / (2 * n)) atTop (nhds r)) ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        R.logProdTrunc k M n (zIter R.σ (-(n : ℤ)) ω) / n) atTop (nhds r)) := by
  obtain ⟨c₀, hc₀⟩ := R.exists_logProdTrunc_subadditive k
  set f : ℕ → Ω → ℝ := fun n ω => R.logProdTrunc k M n ω + c₀ with hfdef
  have hsub : SubadditiveFamily (⇑R.σ) f := by
    refine ⟨fun n => (R.measurable_logProdTrunc k M n).add_const c₀, fun m n ω => ?_⟩
    have := hc₀ M m n ω
    simp only [hfdef]
    linarith
  have h1 : Integrable (fun ω => max (f 1 ω) 0) R.μ := by
    have hbase := R.integrable_logProdTrunc_posPart k M
    refine Integrable.mono' (hbase.add (integrable_const |c₀|))
      (((R.measurable_logProdTrunc k M 1).add_const c₀).max
        measurable_const).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have hA : R.logProdTrunc k M 1 ω ≤ max (R.logProdTrunc k M 1 ω) 0 := le_max_left _ _
    have hB : (0 : ℝ) ≤ max (R.logProdTrunc k M 1 ω) 0 := le_max_right _ _
    have hC : c₀ ≤ |c₀| := le_abs_self c₀
    have hD : (0 : ℝ) ≤ |c₀| := abs_nonneg c₀
    refine max_le ?_ ?_
    · change R.logProdTrunc k M 1 ω + c₀ ≤ max (R.logProdTrunc k M 1 ω) 0 + |c₀|
      linarith
    · exact add_nonneg hB hD
  obtain ⟨C, hCtop, hCae, -, hCmean⟩ := kingman R.μ (⇑R.σ) R.ergodic f hsub h1
  -- the limit is finite: the family is bounded below by `-(M n) + c₀`
  obtain ⟨ω₀, hω₀⟩ := hCae.exists
  have hlow : ∀ᶠ n : ℕ in atTop, ((-(M : ℝ) - |c₀| : ℝ) : EReal) ≤ (f n ω₀ / n : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hge : -((M : ℝ) * n) + c₀ ≤ f n ω₀ := by
      have := R.logProdTrunc_ge k M n ω₀
      simp only [hfdef]; linarith
    have hdiv : (-(M : ℝ) - |c₀|) ≤ f n ω₀ / n := by
      rw [le_div_iff₀ hnpos]
      have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [le_abs_self c₀, neg_abs_le c₀, abs_nonneg c₀]
    change ((-(M : ℝ) - |c₀| : ℝ) : EReal) ≤ ((f n ω₀ / n : ℝ) : EReal)
    exact_mod_cast hdiv
  have hCbot : ((-(M : ℝ) - |c₀| : ℝ) : EReal) ≤ C := ge_of_tendsto hω₀ hlow
  have hCne : C ≠ ⊥ := by
    intro h
    rw [h] at hCbot
    exact absurd (le_bot_iff.1 hCbot) (EReal.coe_ne_bot _)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, C = (r : EReal) := ⟨C.toReal, (EReal.coe_toReal hCtop.ne hCne).symm⟩
  obtain ⟨-, hbal⟩ := SubadditiveFamily.three_limits_ereal R.ergodic hsub h1 C hCae
  obtain ⟨C', -, hC'ae, hC'mean⟩ := kingman_backward R.μ R.σ R.ergodic f hsub h1
  have hCC : C' = C := tendsto_nhds_unique hC'mean hCmean
  rw [hCC] at hC'ae
  refine ⟨r, ?_, ?_, ?_⟩
  · filter_upwards [hCae] with ω hω
    rw [hr] at hω
    have hreal : Tendsto (fun n : ℕ => f n ω / n) atTop (nhds r) := EReal.tendsto_coe.1 hω
    have hshift : Tendsto (fun n : ℕ => c₀ / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat c₀
    have heq : ∀ n : ℕ, R.logProdTrunc k M n ω / n = f n ω / n - c₀ / n := by
      intro n
      simp only [hfdef]
      ring
    simp_rw [heq]
    simpa using hreal.sub hshift
  · filter_upwards [hbal] with ω hω
    rw [hr] at hω
    have hreal : Tendsto (fun n : ℕ => f (2 * n) (zIter R.σ (-(n : ℤ)) ω) / (2 * n)) atTop
        (nhds r) := EReal.tendsto_coe.1 hω
    have hshift : Tendsto (fun n : ℕ => c₀ / ((2 * n : ℕ) : ℝ)) atTop (nhds 0) := by
      refine (tendsto_const_div_atTop_nhds_zero_nat (c₀ / 2)).congr fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        push_cast
        field_simp
    have heq : ∀ n : ℕ, R.logProdTrunc k M (2 * n) (zIter R.σ (-(n : ℤ)) ω) / (2 * n)
        = f (2 * n) (zIter R.σ (-(n : ℤ)) ω) / (2 * n) - c₀ / ((2 * n : ℕ) : ℝ) := by
      intro n
      simp only [hfdef]
      push_cast
      ring
    simp_rw [heq]
    simpa using hreal.sub hshift
  · filter_upwards [hC'ae] with ω hω
    rw [hr] at hω
    have hreal : Tendsto (fun n : ℕ => f n (zIter R.σ (-(n : ℤ)) ω) / n) atTop (nhds r) :=
      EReal.tendsto_coe.1 hω
    have hshift : Tendsto (fun n : ℕ => c₀ / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat c₀
    have heq : ∀ n : ℕ, R.logProdTrunc k M n (zIter R.σ (-(n : ℤ)) ω) / n
        = f n (zIter R.σ (-(n : ℤ)) ω) / n - c₀ / n := by
      intro n
      simp only [hfdef]
      ring
    simp_rw [heq]
    simpa using hreal.sub hshift

/-- Raising the truncation level lowers the family. -/
theorem Cocycle.logProdTrunc_antitone (R : Cocycle Ω X) (k : ℕ) {M M' : ℕ} (h : M ≤ M')
    (n : ℕ) (ω : Ω) : R.logProdTrunc k M' n ω ≤ R.logProdTrunc k M n ω := by
  have hexp : Real.exp (-(M' : ℝ) * n) ≤ Real.exp (-(M : ℝ) * n) := by
    refine Real.exp_le_exp.2 ?_
    have hMM : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hmax : max (R.prodBern k n ω) (Real.exp (-(M' : ℝ) * n))
      ≤ max (R.prodBern k n ω) (Real.exp (-(M : ℝ) * n)) :=
    max_le_max le_rfl hexp
  have hpos : (0 : ℝ) < max (R.prodBern k n ω) (Real.exp (-(M' : ℝ) * n)) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  exact Real.log_le_log hpos hmax

/-- **Kingman at every truncation level at once**, with the limits antitone in the level. This
is precisely the input `ae_tendsto_of_ae_tendsto_max` consumes. -/
theorem Cocycle.exists_logProdTrunc_limits (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k : ℕ) :
    ∃ c : ℕ → ℝ, (∀ M M' : ℕ, M ≤ M' → c M' ≤ c M) ∧
      (∀ M : ℕ, ∀ᵐ ω ∂(R.μ),
        Tendsto (fun n : ℕ => R.logProdTrunc k M n ω / n) atTop (nhds (c M))) ∧
      (∀ M : ℕ, ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        R.logProdTrunc k M (2 * n) (zIter R.σ (-(n : ℤ)) ω) / (2 * n)) atTop (nhds (c M))) ∧
      (∀ M : ℕ, ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        R.logProdTrunc k M n (zIter R.σ (-(n : ℤ)) ω) / n) atTop (nhds (c M))) := by
  choose c hc hcbal hcback using fun M => R.exists_logProdTrunc_limit k M
  refine ⟨c, fun M M' hMM' => ?_, hc, hcbal, hcback⟩
  obtain ⟨ω, hω1, hω2⟩ := ((hc M).and (hc M')).exists
  refine le_of_tendsto_of_tendsto hω2 hω1 ?_
  filter_upwards with n
  exact div_le_div_of_nonneg_right (R.logProdTrunc_antitone k hMM' n ω) (Nat.cast_nonneg n)

theorem Real.log_max_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (max a b) = max (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]

theorem max_div_of_nonneg {a b c : ℝ} (hc : 0 ≤ c) : max a b / c = max (a / c) (b / c) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hc)]
  · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h hc)]

/-- **The floored family is Kingman's truncation of the exponent.** Where the Bernstein product
is positive, `logProdTrunc/n` is exactly `max (log ∏ρ_i / n) (-M)` — which is the shape
`ae_tendsto_of_ae_tendsto_max` consumes. Stated separately from
`Cocycle.ae_tendsto_logProd` because the backward and balanced versions of that lemma (needed by
`Cocycle.exists_topFastSpace`) reuse it at the shifted points `σⁿω` and `σ^{-n}ω`. -/
theorem Cocycle.logProdTrunc_div_eq_max (R : Cocycle Ω X) (k M : ℕ) {n : ℕ} (hn : 1 ≤ n)
    {ω : Ω} (hpos : 0 < R.prodBern k n ω) :
    R.logProdTrunc k M n ω / n = max (Real.log (R.prodBern k n ω) / n) (-(M : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : R.logProdTrunc k M n ω
      = max (Real.log (R.prodBern k n ω)) (-((M : ℝ) * n)) := by
    change Real.log (max (R.prodBern k n ω) (Real.exp (-(M : ℝ) * n))) = _
    rw [Real.log_max_of_pos hpos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hlog, max_div_of_nonneg hnpos.le]
  congr 1
  field_simp

/-- **The Bernstein product has a genuine exponential growth rate.** On a non-degenerate cocycle
the truncated limits of `Cocycle.exists_logProdTrunc_limits` assemble, via
`ae_tendsto_of_ae_tendsto_max`, into `EReal` convergence of `(1/n) log ∏_{i≤k} ρ_i(𝓛^{(n)}_ω)`. -/
theorem Cocycle.ae_tendsto_logProd (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {k : ℕ} (hk : 1 ≤ k) (hZ : R.μ (R.degenerate k) = 0) :
    ∃ A : EReal, A < ⊤ ∧ ∀ᵐ ω ∂(R.μ),
      Tendsto (fun n : ℕ => ((Real.log (R.prodBern k n ω) / n : ℝ) : EReal)) atTop (nhds A) := by
  obtain ⟨c, hcanti, hcae, -, -⟩ := R.exists_logProdTrunc_limits k
  refine ⟨⨅ M : ℕ, (c M : EReal),
    lt_of_le_of_lt (iInf_le _ 0) (EReal.coe_lt_top _),
    ae_tendsto_of_ae_tendsto_max hcanti fun M => ?_⟩
  have hnd : ∀ᵐ ω ∂(R.μ), ω ∉ R.degenerate k := by
    rw [ae_iff]
    simpa using hZ
  filter_upwards [hcae M, hnd] with ω hω hnondeg
  refine Tendsto.congr' ?_ hω
  filter_upwards with n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hPpos : 0 < R.prodBern k n ω := by
      rcases (R.prodBern_nonneg k n ω).lt_or_eq with h | h
      · exact h
      · exfalso
        exact hnondeg ⟨n, hn, (prod_bernstein_eq_zero_iff (R.iterate n ω) hk).1 h.symm⟩
    exact R.logProdTrunc_div_eq_max k M hn hPpos

omit [MeasurableSpace X] in
/-- `ρ` is antitone from index `1` on. -/
theorem bernsteinNumber_antitone (T : X →L[ℝ] X) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    bernsteinNumber T q ≤ bernsteinNumber T p := by
  induction q with
  | zero => omega
  | succ q ih =>
      rcases Nat.lt_or_ge p (q + 1) with hlt | hge
      · refine le_trans ?_ (ih (by omega))
        obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
        exact ChiOrder.bernsteinNumber_succ_le T j
      · have : p = q + 1 := by omega
        rw [this]

omit [MeasurableSpace X] in
/-- `ρ_{j+1}(T)^j ≤ ∏_{i≤j} ρ_i(T)`: every factor dominates the last Bernstein number. -/
theorem pow_bernstein_le_prod (T : X →L[ℝ] X) (j : ℕ) :
    bernsteinNumber T (j + 1) ^ j ≤ ∏ i ∈ Finset.range j, bernsteinNumber T (i + 1) := by
  calc bernsteinNumber T (j + 1) ^ j
      = ∏ _i ∈ Finset.range j, bernsteinNumber T (j + 1) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range j, bernsteinNumber T (i + 1) :=
        Finset.prod_le_prod₀ (fun i _ => bernsteinNumber_nonneg _ _)
          (fun i hi => bernsteinNumber_antitone T (by omega)
            (by rw [Finset.mem_range] at hi; omega))

theorem tendsto_atBot_of_tendsto_coe_bot {u : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => ((u n : ℝ) : EReal)) atTop (nhds ⊥)) :
    Tendsto u atTop atBot := by
  rw [tendsto_atBot]
  intro b
  have hlt : ((⊥ : EReal)) < ((b : ℝ) : EReal) := bot_lt_iff_ne_bot.2 (EReal.coe_ne_bot b)
  have hev := h.eventually_lt_const hlt
  filter_upwards [hev] with n hn
  exact le_of_lt (EReal.coe_lt_coe_iff.1 hn)

/-- The `EReal` limit of a difference of coerced real sequences, named rather than merely
asserted to exist, so that two applications with the same `A`, `B` give the *same* limit. -/
theorem tendsto_coe_sub_spec {u v : ℕ → ℝ} {A B : EReal} (hAtop : A < ⊤) (hBtop : B < ⊤)
    (hBbot : B ≠ ⊥)
    (hu : Tendsto (fun n : ℕ => ((u n : ℝ) : EReal)) atTop (nhds A))
    (hv : Tendsto (fun n : ℕ => ((v n : ℝ) : EReal)) atTop (nhds B)) :
    Tendsto (fun n : ℕ => ((u n - v n : ℝ) : EReal)) atTop
      (nhds (if A = ⊥ then ⊥ else ((A.toReal - B.toReal : ℝ) : EReal))) := by
  have hBr : B = ((B.toReal : ℝ) : EReal) := (EReal.coe_toReal hBtop.ne hBbot).symm
  have hvr : Tendsto v atTop (nhds B.toReal) := by
    refine EReal.tendsto_coe.1 ?_
    rw [← hBr]; exact hv
  by_cases hA : A = ⊥
  · rw [ite_eq_left hA]
    rw [hA] at hu
    have hub : Tendsto u atTop atBot := tendsto_atBot_of_tendsto_coe_bot hu
    have hsub : Tendsto (fun n : ℕ => u n - v n) atTop atBot := by
      have hneg : Tendsto (fun n : ℕ => -v n) atTop (nhds (-B.toReal)) := hvr.neg
      simpa [sub_eq_add_neg] using hub.atBot_add hneg
    exact EReal.tendsto_coe_atBot.comp hsub
  · rw [ite_eq_right hA]
    have hAr : A = ((A.toReal : ℝ) : EReal) := (EReal.coe_toReal hAtop.ne hA).symm
    have hus : Tendsto u atTop (nhds A.toReal) := by
      refine EReal.tendsto_coe.1 ?_
      rw [← hAr]; exact hu
    exact EReal.tendsto_coe.2 (hus.sub hvr)

omit [MeasurableSpace X] in
/-- **From the two product rates to the rate of `ρ_{j+1}`, along any sequence of operators and
times.** Both the forward and the balanced averages of `Cocycle.exists_topFastSpace` are
instances: the forward one takes `T n = 𝓛^{(n)}_ω`, `m n = n`, the balanced one
`T n = 𝓛^{(2n)}_{σ^{-n}ω}`, `m n = 2n`. Naming the limit (rather than asserting one exists) is
what makes the two instances share it. -/
theorem tendsto_logEReal_bernstein_of_prod_limits {T : ℕ → (X →L[ℝ] X)} {m : ℕ → ℕ}
    {j : ℕ} {Ak Aj : EReal} (hAktop : Ak < ⊤) (hAjtop : Aj < ⊤)
    (hev : ∀ᶠ n in atTop, 1 ≤ m n ∧
      0 < ∏ i ∈ Finset.range (j + 1), bernsteinNumber (T n) (i + 1))
    (hu : Tendsto (fun n : ℕ => ((Real.log
      (∏ i ∈ Finset.range (j + 1), bernsteinNumber (T n) (i + 1)) / m n : ℝ) : EReal))
      atTop (nhds Ak))
    (hv : Tendsto (fun n : ℕ => ((Real.log
      (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / m n : ℝ) : EReal))
      atTop (nhds Aj)) :
    Tendsto (fun n : ℕ => logEReal (bernsteinNumber (T n) (j + 1)) / ((m n : ℕ) : EReal))
      atTop (nhds (if Aj = ⊥ then ⊥ else
        if Ak = ⊥ then ⊥ else ((Ak.toReal - Aj.toReal : ℝ) : EReal))) := by
  -- positivity of the two factors, eventually
  have hfac : ∀ᶠ n in atTop, 1 ≤ m n ∧
      0 < ∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1) ∧
      0 < bernsteinNumber (T n) (j + 1) := by
    filter_upwards [hev] with n ⟨hmn, hP⟩
    have hsplit : ∏ i ∈ Finset.range (j + 1), bernsteinNumber (T n) (i + 1)
        = (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1))
          * bernsteinNumber (T n) (j + 1) := Finset.prod_range_succ _ _
    rw [hsplit] at hP
    refine ⟨hmn, ?_, ?_⟩
    · rcases (Finset.prod_nonneg fun i _ => bernsteinNumber_nonneg (T n) (i + 1)).lt_or_eq with
        h | h
      · exact h
      · rw [← h, zero_mul] at hP; exact absurd hP (lt_irrefl 0)
    · rcases (bernsteinNumber_nonneg (T n) (j + 1)).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hP; exact absurd hP (lt_irrefl 0)
  -- the goal sequence is the coerced difference, eventually
  have hterm : ∀ᶠ n in atTop,
      ((Real.log (∏ i ∈ Finset.range (j + 1), bernsteinNumber (T n) (i + 1)) / m n
        - Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / m n : ℝ) : EReal)
      = logEReal (bernsteinNumber (T n) (j + 1)) / ((m n : ℕ) : EReal) := by
    filter_upwards [hfac] with n ⟨hmn, hQ, hr⟩
    have hsplit : ∏ i ∈ Finset.range (j + 1), bernsteinNumber (T n) (i + 1)
        = (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1))
          * bernsteinNumber (T n) (j + 1) := Finset.prod_range_succ _ _
    rw [logEReal_of_pos hr, hsplit, Real.log_mul (ne_of_gt hQ) (ne_of_gt hr)]
    change _ = ((Real.log (bernsteinNumber (T n) (j + 1)) / (m n : ℝ) : ℝ) : EReal)
    congr 1
    ring
  refine Tendsto.congr' hterm ?_
  by_cases hAj : Aj = ⊥
  · rw [ite_eq_left hAj]
    -- `j = 0` would force `Aj = 0`, so `j ≥ 1` and the squeeze applies
    have hj1 : 1 ≤ j := by
      by_contra hcon
      have hj0 : j = 0 := by omega
      subst hj0
      have hz : ∀ n : ℕ, ((Real.log
          (∏ i ∈ Finset.range 0, bernsteinNumber (T n) (i + 1)) / m n : ℝ) : EReal) = 0 := by
        intro n; simp
      simp_rw [hz] at hv
      have := tendsto_nhds_unique hv tendsto_const_nhds
      rw [hAj] at this
      exact absurd this.symm (by simp)
    rw [hAj] at hv
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hvbot : Tendsto (fun n : ℕ => Real.log
        (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / m n) atTop atBot :=
      tendsto_atBot_of_tendsto_coe_bot hv
    have hdiv := hvbot.atBot_div_const hjpos
    have hmono : ∀ᶠ n in atTop,
        Real.log (∏ i ∈ Finset.range (j + 1), bernsteinNumber (T n) (i + 1)) / m n
          - Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / m n
        ≤ (Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / m n) / (j : ℝ) := by
      filter_upwards [hfac] with n ⟨hmn, hQ, hr⟩
      have hmpos : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hmn
      have hsplit : ∏ i ∈ Finset.range (j + 1), bernsteinNumber (T n) (i + 1)
          = (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1))
            * bernsteinNumber (T n) (j + 1) := Finset.prod_range_succ _ _
      have hkey : (j : ℝ) * Real.log (bernsteinNumber (T n) (j + 1))
          ≤ Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) := by
        have hle := pow_bernstein_le_prod (T n) j
        have hppos : (0 : ℝ) < bernsteinNumber (T n) (j + 1) ^ j := pow_pos hr j
        calc (j : ℝ) * Real.log (bernsteinNumber (T n) (j + 1))
            = Real.log (bernsteinNumber (T n) (j + 1) ^ j) := by rw [Real.log_pow]
          _ ≤ _ := Real.log_le_log hppos hle
      have hlr : Real.log (bernsteinNumber (T n) (j + 1))
          ≤ Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / (j : ℝ) := by
        rw [le_div_iff₀ hjpos]; nlinarith [hkey]
      rw [hsplit, Real.log_mul (ne_of_gt hQ) (ne_of_gt hr)]
      have hstep : (Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1))
            + Real.log (bernsteinNumber (T n) (j + 1))) / (m n : ℝ)
          - Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / (m n : ℝ)
          = Real.log (bernsteinNumber (T n) (j + 1)) / (m n : ℝ) := by
        rw [div_sub_div_same]; congr 1; ring
      rw [hstep]
      calc Real.log (bernsteinNumber (T n) (j + 1)) / (m n : ℝ)
          ≤ (Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / (j : ℝ))
              / (m n : ℝ) := div_le_div_of_nonneg_right hlr hmpos.le
        _ = (Real.log (∏ i ∈ Finset.range j, bernsteinNumber (T n) (i + 1)) / (m n : ℝ))
              / (j : ℝ) := by ring
    exact EReal.tendsto_coe_atBot.comp (tendsto_atBot_mono' atTop hmono hdiv)
  · rw [ite_eq_right hAj]
    exact tendsto_coe_sub_spec hAktop hAjtop hAj hu hv

/-- The difference of two sequences whose `EReal` limits exist, the subtrahend's being finite,
converges in `EReal`. -/
theorem exists_tendsto_coe_sub {u v : ℕ → ℝ} {A B : EReal} (hAtop : A < ⊤)
    (hBtop : B < ⊤) (hBbot : B ≠ ⊥)
    (hu : Tendsto (fun n : ℕ => ((u n : ℝ) : EReal)) atTop (nhds A))
    (hv : Tendsto (fun n : ℕ => ((v n : ℝ) : EReal)) atTop (nhds B)) :
    ∃ L : EReal, Tendsto (fun n : ℕ => ((u n - v n : ℝ) : EReal)) atTop (nhds L) := by
  exact ⟨_, tendsto_coe_sub_spec hAtop hBtop hBbot hu hv⟩

/-- Degeneracy at a lower index forces it at a higher one, `ρ` being antitone. -/
theorem Cocycle.degenerate_mono (R : Cocycle Ω X) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    R.degenerate p ⊆ R.degenerate q := by
  rintro ω ⟨n, hn, h0⟩
  refine ⟨n, hn, le_antisymm ?_ (bernsteinNumber_nonneg _ _)⟩
  rw [← h0]
  exact bernsteinNumber_antitone (R.iterate n ω) hp hpq

/-- The `⊥`-limit of the Bernstein product at index `j` drags `ρ_{j+1}` down with it. -/
theorem Cocycle.log_bernstein_le_of_prod (R : Cocycle Ω X) (j n : ℕ) (ω : Ω)
    (hpos : 0 < bernsteinNumber (R.iterate n ω) (j + 1)) :
    (j : ℝ) * Real.log (bernsteinNumber (R.iterate n ω) (j + 1))
      ≤ Real.log (R.prodBern j n ω) := by
  have hle := pow_bernstein_le_prod (R.iterate n ω) j
  have hppos : (0 : ℝ) < bernsteinNumber (R.iterate n ω) (j + 1) ^ j := pow_pos hpos j
  calc (j : ℝ) * Real.log (bernsteinNumber (R.iterate n ω) (j + 1))
      = Real.log (bernsteinNumber (R.iterate n ω) (j + 1) ^ j) := by
        rw [Real.log_pow]
    _ ≤ Real.log (R.prodBern j n ω) := Real.log_le_log hppos hle

/-- **Lemma `chi-converges`.** The normalized logarithms of the Bernstein numbers converge
almost surely to the `limsup` defining `χ_k`.

Ergodicity makes the backward-invariant degeneracy set null or conull. In the conull case the
sequence is eventually `⊥`. In the null case, truncated product families give the two adjacent
product limits. `tendsto_logEReal_bernstein_of_prod_limits` recovers the individual Bernstein
rate: it subtracts a finite predecessor limit and uses the Bernstein-number ordering to squeeze
the rate to `⊥` when the predecessor limit is `⊥`. This also covers `k = 1`, whose predecessor
product is the constant `1`.

Convergence is separate from almost-everywhere constancy of `chi`: the latter follows from
its shift inequality and ergodicity, whereas this statement uses Kingman's theorem. -/
theorem Cocycle.ae_tendsto_chi (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] (k : ℕ)
    [NeZero k] :
    ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal)) atTop (nhds (R.chi k ω)) := by
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases R.measure_degenerate_eq_zero_or_one (j + 1) with hZ | hZ
  · obtain ⟨Ak, hAktop, hAk⟩ := R.ae_tendsto_logProd (k := j + 1) (by omega) hZ
    obtain ⟨Aj, hAjtop, hAj⟩ : ∃ Aj : EReal, Aj < ⊤ ∧ ∀ᵐ ω ∂(R.μ),
        Tendsto (fun n : ℕ => ((Real.log (R.prodBern j n ω) / n : ℝ) : EReal))
          atTop (nhds Aj) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, by simp, ?_⟩
        filter_upwards with ω
        have hz : ∀ n : ℕ, ((Real.log (R.prodBern 0 n ω) / n : ℝ) : EReal) = 0 := by
          intro n
          simp [Cocycle.prodBern]
        simp_rw [hz]
        exact tendsto_const_nhds
      · have : NeZero j := ⟨by omega⟩
        have hsub := measure_mono (μ := R.μ)
          (R.degenerate_mono (p := j) (q := j + 1) (by omega) (by omega))
        rw [hZ] at hsub
        exact R.ae_tendsto_logProd (k := j) (by omega) (nonpos_iff_eq_zero.1 hsub)
    have hnd : ∀ᵐ ω ∂(R.μ), ω ∉ R.degenerate (j + 1) := by
      rw [ae_iff]; simpa using hZ
    filter_upwards [hAk, hAj, hnd] with ω hu hv hnondeg
    have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
        0 < ∏ i ∈ Finset.range (j + 1), bernsteinNumber (R.iterate n ω) (i + 1) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      refine ⟨hn, ?_⟩
      change 0 < R.prodBern (j + 1) n ω
      rcases (R.prodBern_nonneg (j + 1) n ω).lt_or_eq with hp | hp
      · exact hp
      · exact False.elim (hnondeg ⟨n, hn,
          (prod_bernstein_eq_zero_iff (R.iterate n ω) (by omega)).1 hp.symm⟩)
    have hgoal := tendsto_logEReal_bernstein_of_prod_limits
      (T := fun n => R.iterate n ω) (m := fun n => n) hAktop hAjtop hev
      (by simpa only [Cocycle.prodBern] using hu)
      (by simpa only [Cocycle.prodBern] using hv)
    have hchi : R.chi (j + 1) ω = _ := hgoal.limsup_eq
    rw [hchi]
    exact hgoal
  · -- the degenerate set is conull
    have hae : ∀ᵐ ω ∂(R.μ), ω ∈ R.degenerate (j + 1) := by
      rw [ae_iff]
      have hc : R.μ (R.degenerate (j + 1))ᶜ = 0 := by
        rw [measure_compl (R.measurableSet_degenerate (j + 1)) (measure_ne_top _ _), hZ,
          measure_univ, tsub_self]
      exact hc
    filter_upwards [hae] with ω hω
    obtain ⟨htend, hchi⟩ := R.tendsto_chi_of_degenerate (j + 1) hω
    rw [hchi]
    exact htend

/-- **Lemma.** `χ_k` is almost-everywhere constant: its measurable shift inequality and
ergodicity imply constancy, independently of the convergence theorem above.

The `EReal` value includes finite-rank cocycles, where the constant can be `⊥`. -/
theorem Cocycle.exists_chi_ae_const (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k : ℕ) : ∃ c : EReal, ∀ᵐ ω ∂(R.μ), R.chi k ω = c := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨⊥, Filter.Eventually.of_forall fun ω => R.chi_zero ω⟩
  · have : NeZero k := ⟨hk.ne'⟩
    exact exists_ae_const_of_le_comp R.ergodic (R.measurable_chi k) (R.chi_le_chi_shift k)

/-- The `χ_k` are (weakly) decreasing in `k`, since `ρ_k` is. Pointwise in `ω`: no ergodicity
needed. Shifted by one to skip the junk index `χ_0 = ⊥`. -/
theorem Cocycle.chi_antitone (R : Cocycle Ω X) (ω : Ω) :
    Antitone fun k : ℕ => R.chi (k + 1) ω := by
  refine antitone_nat_of_succ_le fun k => ?_
  refine Filter.limsup_le_limsup ?_
  filter_upwards with n
  have hn : (0 : EReal) ≤ (n : ℕ) := by
    rw [← EReal.coe_coe_eq_natCast]
    exact EReal.coe_nonneg.2 (Nat.cast_nonneg n)
  exact EReal.div_le_div_right_of_nonneg hn
    (ChiOrder.logEReal_mono (ChiOrder.bernsteinNumber_succ_le (R.iterate n ω) k))

/-- `χ_{k+1}(ω) ↓ ν(ω)`, pointwise in `ω`, by antitonicity. -/
theorem Cocycle.nu_isLimit (R : Cocycle Ω X) (ω : Ω) :
    Filter.Tendsto (fun k : ℕ => R.chi (k + 1) ω) atTop (nhds (R.nu ω)) := by
  change Filter.Tendsto (fun k : ℕ => R.chi (k + 1) ω) atTop (nhds (⨅ k : ℕ, R.chi (k + 1) ω))
  exact tendsto_atTop_iInf (R.chi_antitone ω)

/-- `ν ≤ χ_k` for every `k ≥ 1`: `ν` is the infimum of exactly those `χ_k`. -/
theorem Cocycle.nu_le_chi (R : Cocycle Ω X) (ω : Ω) {k : ℕ} (hk : 1 ≤ k) :
    R.nu ω ≤ R.chi k ω := by
  have h1 : R.nu ω ≤ R.chi (k - 1 + 1) ω := by
    change (⨅ j : ℕ, R.chi (j + 1) ω) ≤ _
    exact iInf_le _ (k - 1)
  rwa [Nat.sub_add_cancel hk] at h1

/-- **Lemma** (`proof_met.tex`, "Further, `λ₂` exists if and only if `λ₁ > ν`", proved there
from `ν = lim χ_n` and `λ₂ = χ_{min{t : χ_t < χ₁}}`).

"`λ₂` exists" is precisely "the set `{t ≥ 1 : χ_t < χ₁}` defining it is nonempty" — the paper
claims nothing about where `λ₂` sits relative to `ν`, and `λ₂ = ν` is a genuine possibility
(see the note on `Cocycle.lambda2_exists_iff`). In that form the equivalence is a consequence
of the definitions alone. -/
theorem Cocycle.exists_chi_lt_chi_one_iff_isQuasicompact (R : Cocycle Ω X) :
    (∀ᵐ ω ∂(R.μ), ∃ k, 1 ≤ k ∧ R.chi k ω < R.chi 1 ω) ↔ R.IsQuasicompact := by
  constructor
  · intro h
    filter_upwards [h] with ω hω
    obtain ⟨k, hk1, hk2⟩ := hω
    exact lt_of_le_of_lt (R.nu_le_chi ω hk1) hk2
  · intro h
    filter_upwards [h] with ω hω
    have hlt : (⨅ j : ℕ, R.chi (j + 1) ω) < R.chi 1 ω := hω
    obtain ⟨j, hj⟩ := iInf_lt_iff.1 hlt
    exact ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j), hj⟩

/-- **Lemma.** A second distinct Lyapunov exponent `λ₂` exists — i.e. the set
`{t ≥ 1 : χ_t < χ₁}` defining it is nonempty — if and only if `𝓛` is quasicompact.

**Statement corrected.** This previously read `∃ k, 1 ≤ k ∧ χ_k < χ₁ ∧ ν < χ_k`, and the extra
conjunct `ν < χ_k` made the `←` direction *false*, not merely unproved. Counterexample: take
`X = ℓ²(ℕ)`, any ergodic base, and the constant cocycle `𝓛_ω = A = diag(2, 1, 1, 1, …)`. Then
`ρ₁(Aⁿ) = 2ⁿ`, while `ρ_k(Aⁿ) = 1` for every `k ≥ 2` — a `k`-dimensional subspace with `k ≥ 2`
meets `{x₁ = 0}` in dimension `≥ 1`, so contains a unit vector fixed by `Aⁿ` and its growth is
`≤ 1`; and `Aⁿ` is expansive, so it is `≥ 1`. Hence `χ₁ = log 2`, `χ_k = 0` for `k ≥ 2`, and
`ν = 0`. This cocycle is quasicompact (`0 < log 2`), yet no `k` satisfies the old left-hand
side: `k = 1` fails `χ_k < χ₁`, and every `k ≥ 2` has `χ_k = 0 = ν`, failing `ν < χ_k`.

The paper never claims `ν < λ₂`: `proof_met.tex` l.645 asserts only that `λ₂` exists iff
`λ₁ > ν`, and `λ₂ = ν` is explicitly one of the three cases listed at l.150. `ν ≤ χ_k` does
hold for every `k ≥ 1` — that is `Cocycle.nu_le_chi` — and is all the argument ever needed. -/
theorem Cocycle.lambda2_exists_iff (R : Cocycle Ω X) :
    (∀ᵐ ω ∂(R.μ), ∃ k, 1 ≤ k ∧ R.chi k ω < R.chi 1 ω) ↔ R.IsQuasicompact :=
  R.exists_chi_lt_chi_one_iff_isQuasicompact

/-- **A quasicompact cocycle has a genuine top multiplicity `m_1 ≥ 1`.** Quasicompactness gives
some `χ_k < χ_1`, so the defining set of `lambdaIdx 1` is nonempty and its infimum is at least
`2` (the value `1` is excluded because `χ_1 < χ_1` is false). -/
theorem Cocycle.mult_zero_pos (R : Cocycle Ω X) (hqc : R.IsQuasicompact) :
    ∀ᵐ ω ∂(R.μ), 0 < R.mult 0 ω := by
  have hex := R.lambda2_exists_iff.2 hqc
  filter_upwards [hex] with ω hω
  obtain ⟨k, hk1, hklt⟩ := hω
  set S : Set ℕ := {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx 0 ω) ω} with hS
  have hkS : k ∈ S := ⟨hk1, hklt⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨k, hkS⟩
  have h1le : 1 ≤ sInf S := hmem.1
  have hne1 : sInf S ≠ 1 := by
    intro h1
    have hlt := hmem.2
    rw [h1] at hlt
    exact lt_irrefl _ hlt
  change 0 < R.lambdaIdx 1 ω - R.lambdaIdx 0 ω
  change 0 < sInf S - 1
  omega

/-- **Predicate.** `E` is a (the) top fast space of multiplicity `k` growing at rate `lam`:
measurable, equivariant, and every nonzero vector in `E(ω)` grows at exactly rate `lam`,
uniformly. Corresponds to the three bullet points of the first Lemma of Section 5. -/
def Cocycle.IsFastSpace (R : Cocycle Ω X) (k : ℕ) [NeZero k] (lam : ℝ)
    (E : Ω → GrassmannianFin X k) : Prop :=
  Measurable E ∧
  (∀ᵐ ω ∂(R.μ), ∀ x ∈ (E ω).1, x ≠ 0 → R.lambdaAt ω x = (lam : EReal)) ∧
  (∀ᵐ ω ∂(R.μ), (E ω).1.map (R.L ω : X →ₗ[ℝ] X) = (E (R.σ ω)).1) ∧
  (∀ᵐ ω ∂(R.μ), Tendsto (fun n => Real.log (growth (R.iterate n ω) (E ω).1) / n) atTop (nhds lam))

/-- `𝓛^{(2n)}_{σ^{-n}ω} = 𝓛^{(n)}_ω ∘ 𝓛^{(n)}_{σ^{-n}ω}`: the balanced window splits at time `0`. -/
theorem Cocycle.iterate_two_mul_shift (R : Cocycle Ω X) (n : ℕ) (ω : Ω) :
    R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)
      = (R.iterate n ω).comp (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) := by
  have hsplit : 2 * n = n + n := by omega
  rw [hsplit, R.iterate_add n n (zIter R.σ (-(n : ℤ)) ω)]
  congr 2
  rw [zIter_neg_natCast]
  exact Function.LeftInverse.iterate (fun x => R.σ.apply_symm_apply x) n ω

/-- On the degenerate set the balanced sequence is eventually `⊥` too: the balanced window
factors through `𝓛^{(n)}_ω`, which is degenerate for large `n`. -/
theorem Cocycle.tendsto_chi_balanced_of_degenerate (R : Cocycle Ω X) (k : ℕ) {ω : Ω}
    (hω : ω ∈ R.degenerate k) :
    Tendsto (fun n : ℕ => logEReal
      (bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) k) / ((2 * n : ℕ) : EReal))
      atTop (nhds ⊥) := by
  obtain ⟨n₀, hn₀1, hn₀⟩ := hω
  have hev : ∀ᶠ n : ℕ in atTop, logEReal
      (bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) k) / ((2 * n : ℕ) : EReal)
      = ⊥ := by
    filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
    have hzero : bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) k = 0 := by
      refine le_antisymm ?_ (bernsteinNumber_nonneg _ k)
      rw [R.iterate_two_mul_shift n ω]
      have hfac := bernsteinNumber_comp_le_mul_norm (R.iterate n ω)
        (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) k
      have hn0 : bernsteinNumber (R.iterate n ω) k = 0 :=
        R.bernstein_eq_zero_of_le k ω hn₀ (le_trans (le_max_left _ _) hn)
      rw [hn0, zero_mul] at hfac
      exact hfac
    rw [hzero, logEReal_of_nonpos le_rfl, bot_div_natCast (by omega : 1 ≤ 2 * n)]
  exact Tendsto.congr' (hev.mono fun n h => h.symm) tendsto_const_nhds

/-- **The degenerate set can be dodged along the whole backward orbit.** `Cocycle.degenerate` is
backward-invariant but not forward-invariant, so one cannot argue pointwise; instead each
`σ^{-n}` preimage is null because `σ⁻¹` preserves `μ`, and there are countably many. -/
theorem Cocycle.ae_all_shift_notMem_degenerate (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] (k : ℕ) [NeZero k] (hZ : R.μ (R.degenerate k) = 0) :
    ∀ᵐ ω ∂(R.μ), ∀ n : ℕ, zIter R.σ (-(n : ℤ)) ω ∉ R.degenerate k := by
  refine ae_all_iff.2 fun n => ?_
  have hmp : MeasurePreserving (⇑R.σ.symm) R.μ R.μ :=
    MeasurePreserving.symm R.σ R.ergodic.toMeasurePreserving
  have hiter : MeasurePreserving ((⇑R.σ.symm)^[n]) R.μ R.μ := hmp.iterate n
  have hpre : R.μ (((⇑R.σ.symm)^[n]) ⁻¹' (R.degenerate k)) = 0 := by
    rw [hiter.measure_preimage (R.measurableSet_degenerate k).nullMeasurableSet, hZ]
  rw [ae_iff]
  have hset : {ω : Ω | ¬ zIter R.σ (-(n : ℤ)) ω ∉ R.degenerate k}
      = ((⇑R.σ.symm)^[n]) ⁻¹' (R.degenerate k) := by
    ext ω
    simp only [Set.mem_ofPred_eq, not_not, Set.mem_preimage, zIter_neg_natCast]
  rw [hset, hpre]

/-- **The balanced companion of `Cocycle.ae_tendsto_logProd`.** The same truncated families feed
`SubadditiveFamily.three_limits_ereal`, so the balanced averages `(1/2n) log
∏ρ_i(𝓛^{(2n)}_{σ^{-n}ω})`
converge to the *same* constant. This is the form the equivariance step of
`Cocycle.exists_topFastSpace` runs on. -/
theorem Cocycle.ae_tendsto_logProd_balanced (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {k : ℕ} (hk : 1 ≤ k) [NeZero k] (hZ : R.μ (R.degenerate k) = 0) :
    ∃ A : EReal, A < ⊤ ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        ((Real.log (R.prodBern k n ω) / n : ℝ) : EReal)) atTop (nhds A)) ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        ((Real.log (R.prodBern k (2 * n) (zIter R.σ (-(n : ℤ)) ω)) / (2 * n) : ℝ) : EReal))
        atTop (nhds A)) ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
        ((Real.log (R.prodBern k n (zIter R.σ (-(n : ℤ)) ω)) / n : ℝ) : EReal))
        atTop (nhds A)) := by
  obtain ⟨c, hcanti, hcae, hcbal, hcback⟩ := R.exists_logProdTrunc_limits k
  have hnd : ∀ᵐ ω ∂(R.μ), ω ∉ R.degenerate k := by
    rw [ae_iff]; simpa using hZ
  have hshiftnd := R.ae_all_shift_notMem_degenerate k hZ
  refine ⟨⨅ M : ℕ, (c M : EReal), lt_of_le_of_lt (iInf_le _ 0) (EReal.coe_lt_top _), ?_, ?_, ?_⟩
  · refine ae_tendsto_of_ae_tendsto_max hcanti fun M => ?_
    filter_upwards [hcae M, hnd] with ω hω hnondeg
    refine Tendsto.congr' ?_ hω
    filter_upwards with n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hPpos : 0 < R.prodBern k n ω := by
        rcases (R.prodBern_nonneg k n ω).lt_or_eq with h | h
        · exact h
        · exact absurd ⟨n, hn, (prod_bernstein_eq_zero_iff (R.iterate n ω) hk).1 h.symm⟩ hnondeg
      exact R.logProdTrunc_div_eq_max k M hn hPpos
  · refine ae_tendsto_of_ae_tendsto_max hcanti fun M => ?_
    filter_upwards [hcbal M, hshiftnd] with ω hω hnondeg
    refine Tendsto.congr' ?_ hω
    filter_upwards with n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h2n : 1 ≤ 2 * n := by omega
      have hPpos : 0 < R.prodBern k (2 * n) (zIter R.σ (-(n : ℤ)) ω) := by
        rcases (R.prodBern_nonneg k (2 * n) (zIter R.σ (-(n : ℤ)) ω)).lt_or_eq with h | h
        · exact h
        · exact absurd ⟨2 * n, h2n,
            (prod_bernstein_eq_zero_iff (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) hk).1 h.symm⟩
            (hnondeg n)
      have := R.logProdTrunc_div_eq_max k M h2n hPpos
      push_cast at this ⊢
      exact this
  · refine ae_tendsto_of_ae_tendsto_max hcanti fun M => ?_
    filter_upwards [hcback M, hshiftnd] with ω hω hnondeg
    refine Tendsto.congr' ?_ hω
    filter_upwards with n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hPpos : 0 < R.prodBern k n (zIter R.σ (-(n : ℤ)) ω) := by
        rcases (R.prodBern_nonneg k n (zIter R.σ (-(n : ℤ)) ω)).lt_or_eq with h | h
        · exact h
        · exact absurd ⟨n, hn,
            (prod_bernstein_eq_zero_iff (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) hk).1 h.symm⟩
            (hnondeg n)
      exact R.logProdTrunc_div_eq_max k M hn hPpos

/-- **The exponent indices, and hence the multiplicities, are a.e. constant.** Each `χ_t` is
a.e. constant (`exists_chi_ae_const`); there are countably many of them, so on the intersection
of those conull sets every `lambdaIdx` and every `mult` is pinned to a single value. -/
theorem Cocycle.exists_lambdaIdx_ae_eq (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (i : ℕ) : ∃ N : ℕ, ∀ᵐ ω ∂(R.μ), R.lambdaIdx i ω = N := by
  choose c hc using fun t : ℕ => R.exists_chi_ae_const t
  have hall : ∀ᵐ ω ∂(R.μ), ∀ t : ℕ, R.chi t ω = c t := ae_all_iff.2 hc
  induction i with
  | zero => exact ⟨1, Filter.Eventually.of_forall fun ω => rfl⟩
  | succ i ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨sInf {t : ℕ | 1 ≤ t ∧ c t < c N}, ?_⟩
      filter_upwards [hall, hN] with ω hω hωN
      change sInf {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx i ω) ω} = _
      congr 1
      ext t
      simp only [Set.mem_ofPred_eq, hω t, hωN, hω N]

theorem Cocycle.exists_mult_ae_eq (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] (i : ℕ) :
    ∃ m : ℕ, ∀ᵐ ω ∂(R.μ), R.mult i ω = m := by
  obtain ⟨N, hN⟩ := R.exists_lambdaIdx_ae_eq i
  obtain ⟨N', hN'⟩ := R.exists_lambdaIdx_ae_eq (i + 1)
  refine ⟨N' - N, ?_⟩
  filter_upwards [hN, hN'] with ω h1 h2
  change R.lambdaIdx (i + 1) ω - R.lambdaIdx i ω = N' - N
  rw [h1, h2]

/-- **A quasicompact cocycle has a well-defined top multiplicity `m₁ ≥ 1`.** -/
theorem Cocycle.exists_mult_zero (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (hqc : R.IsQuasicompact) :
    ∃ m1 : ℕ, 0 < m1 ∧ ∀ᵐ ω ∂(R.μ), R.mult 0 ω = m1 := by
  obtain ⟨m1, hm1⟩ := R.exists_mult_ae_eq 0
  refine ⟨m1, ?_, hm1⟩
  obtain ⟨ω, hω, hωpos⟩ := (hm1.and (R.mult_zero_pos hqc)).exists
  rwa [hω] at hωpos

/-- `𝓛^{(n)}_{σ^{-n}ω} = 𝓛^{(p)}_{σ^{-p}ω} ∘ 𝓛^{(n-p)}_{σ^{-n}ω}` for `p ≤ n`: the backward window
ends with the last `p` steps, which are the *same* operators for every `n`. This is why
degeneracy propagates along the backward sequence, where the forward argument does not apply. -/
theorem Cocycle.iterate_shift_split (R : Cocycle Ω X) {p n : ℕ} (hpn : p ≤ n) (ω : Ω) :
    R.iterate n (zIter R.σ (-(n : ℤ)) ω)
      = (R.iterate p (zIter R.σ (-(p : ℤ)) ω)).comp
          (R.iterate (n - p) (zIter R.σ (-(n : ℤ)) ω)) := by
  have hsplit : n = p + (n - p) := by omega
  rw [show R.iterate n = R.iterate (p + (n - p)) from by rw [← hsplit],
    R.iterate_add p (n - p) (zIter R.σ (-(n : ℤ)) ω)]
  congr 2
  rw [zIter_neg_natCast, zIter_neg_natCast]
  have hiter : ((⇑R.σ.symm)^[n]) ω = ((⇑R.σ.symm)^[n - p]) (((⇑R.σ.symm)^[p]) ω) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [hiter]
  exact Function.LeftInverse.iterate (fun x => R.σ.apply_symm_apply x) (n - p) _

/-- The backward-degenerate set: some backward window is already `ρ_k`-degenerate. -/
def Cocycle.degenerateBack (R : Cocycle Ω X) (k : ℕ) : Set Ω :=
  {ω | ∃ p : ℕ, 1 ≤ p ∧ bernsteinNumber (R.iterate p (zIter R.σ (-(p : ℤ)) ω)) k = 0}

theorem Cocycle.tendsto_chi_backward_of_degenerateBack (R : Cocycle Ω X) (k : ℕ) {ω : Ω}
    (hω : ω ∈ R.degenerateBack k) :
    Tendsto (fun n : ℕ =>
      logEReal (bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) k) / (n : EReal))
      atTop (nhds ⊥) := by
  obtain ⟨p, hp1, hp0⟩ := hω
  have hev : ∀ᶠ n : ℕ in atTop,
      logEReal (bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) k) / (n : EReal) = ⊥ := by
    filter_upwards [eventually_ge_atTop (max p 1)] with n hn
    have hzero : bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) k = 0 := by
      refine le_antisymm ?_ (bernsteinNumber_nonneg _ k)
      rw [R.iterate_shift_split (le_trans (le_max_left _ _) hn) ω]
      have hfac := bernsteinNumber_comp_le_norm_mul
        (R.iterate p (zIter R.σ (-(p : ℤ)) ω))
        (R.iterate (n - p) (zIter R.σ (-(n : ℤ)) ω)) k
      have hfac2 := bernsteinNumber_comp_le_mul_norm
        (R.iterate p (zIter R.σ (-(p : ℤ)) ω))
        (R.iterate (n - p) (zIter R.σ (-(n : ℤ)) ω)) k
      rw [hp0, zero_mul] at hfac2
      exact hfac2
    rw [hzero, logEReal_of_nonpos le_rfl, bot_div_natCast (le_trans (le_max_right _ _) hn)]
  exact Tendsto.congr' (hev.mono fun n h => h.symm) tendsto_const_nhds

theorem Cocycle.measurableSet_degenerateBack (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k : ℕ) [NeZero k] : MeasurableSet (R.degenerateBack k) := by
  have heq : R.degenerateBack k
      = ⋃ p : ℕ, {ω | 1 ≤ p ∧
          bernsteinNumber (R.iterate p (zIter R.σ (-(p : ℤ)) ω)) k = 0} := by
    ext ω; simp [Cocycle.degenerateBack]
  rw [heq]
  refine MeasurableSet.iUnion fun p => ?_
  by_cases h : 1 ≤ p
  · simp only [h, true_and]
    have hmp : Measurable (fun ω : Ω => zIter R.σ (-(p : ℤ)) ω) := by
      simp only [zIter_neg_natCast]
      exact R.σ.symm.measurable.iterate p
    exact measurableSet_eq_fun
      ((measurable_bernstein_of_weak k
        (fun x => (R.measurable_iterate_apply p x).comp hmp))) measurable_const
  · simp [h]

/-- **If the forward degenerate set is conull so is the backward one.** The sets
`Z_p = {ρ_k(𝓛^{(p)}) = 0}` increase to the forward degenerate set, and `σ^{-p}` pulls `Z_p` back
into the backward degenerate set without changing its measure. -/
theorem Cocycle.measure_degenerateBack_eq_one (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k : ℕ) [NeZero k] (hZ : R.μ (R.degenerate k) = 1) :
    R.μ (R.degenerateBack k) = 1 := by
  set Zp : ℕ → Set Ω := fun p => {ω | bernsteinNumber (R.iterate p ω) k = 0} with hZpdef
  have hmono : Monotone Zp := fun p q hpq ω hω => R.bernstein_eq_zero_of_le k ω hω hpq
  have hunion : R.degenerate k ⊆ ⋃ p, Zp p := by
    rintro ω ⟨n, -, h0⟩
    exact Set.mem_iUnion.2 ⟨n, h0⟩
  have hlim : Tendsto (fun p => R.μ (Zp p)) atTop (nhds (R.μ (⋃ p, Zp p))) :=
    tendsto_measure_iUnion_atTop hmono
  have htop : R.μ (⋃ p, Zp p) = 1 :=
    le_antisymm (prob_le_one) (by rw [← hZ]; exact measure_mono hunion)
  rw [htop] at hlim
  refine le_antisymm prob_le_one (le_of_tendsto hlim ?_)
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hmp : MeasurePreserving (fun ω : Ω => zIter R.σ (-(p : ℤ)) ω) R.μ R.μ := by
    simp only [zIter_neg_natCast]
    exact (MeasurePreserving.symm R.σ R.ergodic.toMeasurePreserving).iterate p
  have hmeas : MeasurableSet (Zp p) :=
    measurableSet_eq_fun (measurable_bernstein_of_weak k (R.measurable_iterate_apply p))
      measurable_const
  have hsub : (fun ω : Ω => zIter R.σ (-(p : ℤ)) ω) ⁻¹' (Zp p) ⊆ R.degenerateBack k := by
    intro ω hω
    exact ⟨p, hp, hω⟩
  calc R.μ (Zp p) = R.μ ((fun ω : Ω => zIter R.σ (-(p : ℤ)) ω) ⁻¹' (Zp p)) :=
        (hmp.measure_preimage hmeas.nullMeasurableSet).symm
    _ ≤ R.μ (R.degenerateBack k) := measure_mono hsub

/-- The preceding product has all three limits, including the empty product at index zero. -/
private theorem Cocycle.ae_tendsto_logProd_predecessor (R : Cocycle Ω X)
    [SeparableSpace X] [BorelSpace X] (j : ℕ)
    (hZ : R.μ (R.degenerate (j + 1)) = 0) :
    ∃ Aj : EReal, Aj < ⊤ ∧
        (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
          ((Real.log (R.prodBern j n ω) / n : ℝ) : EReal)) atTop (nhds Aj)) ∧
        (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
          ((Real.log (R.prodBern j (2 * n) (zIter R.σ (-(n : ℤ)) ω)) / (2 * n) : ℝ) : EReal))
          atTop (nhds Aj)) ∧
        (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
          ((Real.log (R.prodBern j n (zIter R.σ (-(n : ℤ)) ω)) / n : ℝ) : EReal))
          atTop (nhds Aj)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨0, by simp, ?_, ?_, ?_⟩
    · filter_upwards with ω
      have hz : ∀ n : ℕ, ((Real.log (R.prodBern 0 n ω) / n : ℝ) : EReal) = 0 := by
        intro n; simp [Cocycle.prodBern]
      simp_rw [hz]; exact tendsto_const_nhds
    · filter_upwards with ω
      have hz : ∀ n : ℕ, ((Real.log
          (R.prodBern 0 (2 * n) (zIter R.σ (-(n : ℤ)) ω)) / (2 * n) : ℝ) : EReal) = 0 := by
        intro n; simp [Cocycle.prodBern]
      simp_rw [hz]; exact tendsto_const_nhds
    · filter_upwards with ω
      have hz : ∀ n : ℕ, ((Real.log
          (R.prodBern 0 n (zIter R.σ (-(n : ℤ)) ω)) / n : ℝ) : EReal) = 0 := by
        intro n; simp [Cocycle.prodBern]
      simp_rw [hz]; exact tendsto_const_nhds
  · have : NeZero j := ⟨by omega⟩
    have hsub := measure_mono (μ := R.μ)
      (R.degenerate_mono (p := j) (q := j + 1) (by omega) (by omega))
    rw [hZ] at hsub
    exact R.ae_tendsto_logProd_balanced (k := j) (by omega) (nonpos_iff_eq_zero.1 hsub)

/-- **The balanced exponent.** `(1/2n) log ρ_k(𝓛^{(2n)}_{σ^{-n}ω}) → χ_k` almost surely --- the
third of the three limits opening `proof_met.tex` l.695--700, and the one the equivariance step
of `Cocycle.exists_topFastSpace` runs on. It comes from the same truncated families as
`Cocycle.ae_tendsto_chi` via `SubadditiveFamily.three_limits_ereal`. -/
theorem Cocycle.ae_tendsto_chi_balanced (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k : ℕ) [NeZero k] :
    ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
      (bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) k) / ((2 * n : ℕ) : EReal))
      atTop (nhds (R.chi k ω)) := by
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases R.measure_degenerate_eq_zero_or_one (j + 1) with hZ | hZ
  · obtain ⟨Ak, hAktop, hAkf, hAkb, -⟩ := R.ae_tendsto_logProd_balanced (k := j + 1) (by omega) hZ
    obtain ⟨Aj, hAjtop, hAjf, hAjb, -⟩ := R.ae_tendsto_logProd_predecessor j hZ
    have hnd : ∀ᵐ ω ∂(R.μ), ω ∉ R.degenerate (j + 1) := by rw [ae_iff]; simpa using hZ
    have hshiftnd := R.ae_all_shift_notMem_degenerate (j + 1) hZ
    filter_upwards [hAkf, hAkb, hAjf, hAjb, hnd, hshiftnd] with ω h1 h2 h3 h4 h5 h6
    have hevf : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
        0 < ∏ i ∈ Finset.range (j + 1), bernsteinNumber (R.iterate n ω) (i + 1) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      refine ⟨hn, ?_⟩
      rcases (R.prodBern_nonneg (j + 1) n ω).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨n, hn,
          (prod_bernstein_eq_zero_iff (R.iterate n ω) (by omega)).1 h.symm⟩ h5
    have hevb : ∀ᶠ n : ℕ in atTop, 1 ≤ 2 * n ∧
        0 < ∏ i ∈ Finset.range (j + 1),
          bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) (i + 1) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      refine ⟨by omega, ?_⟩
      rcases (R.prodBern_nonneg (j + 1) (2 * n) (zIter R.σ (-(n : ℤ)) ω)).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨2 * n, by omega, (prod_bernstein_eq_zero_iff
          (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) (by omega)).1 h.symm⟩ (h6 n)
    have h4' : Tendsto (fun n : ℕ => ((Real.log (∏ i ∈ Finset.range j,
        bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) (i + 1))
        / ((2 * n : ℕ) : ℝ) : ℝ) : EReal)) atTop (nhds Aj) := by
      refine h4.congr fun n => ?_
      push_cast
      rfl
    have h2' : Tendsto (fun n : ℕ => ((Real.log (∏ i ∈ Finset.range (j + 1),
        bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) (i + 1))
        / ((2 * n : ℕ) : ℝ) : ℝ) : EReal)) atTop (nhds Ak) := by
      refine h2.congr fun n => ?_
      push_cast
      rfl
    have hfwd := tendsto_logEReal_bernstein_of_prod_limits (T := fun n => R.iterate n ω)
      (m := fun n => n) hAktop hAjtop hevf h1 h3
    have hbal := tendsto_logEReal_bernstein_of_prod_limits
      (T := fun n => R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω))
      (m := fun n => 2 * n) hAktop hAjtop hevb h2' h4'
    have hchi : R.chi (j + 1) ω = _ := hfwd.limsup_eq
    rw [hchi]
    exact hbal
  · have hae : ∀ᵐ ω ∂(R.μ), ω ∈ R.degenerate (j + 1) := by
      rw [ae_iff]
      have hc : R.μ (R.degenerate (j + 1))ᶜ = 0 := by
        rw [measure_compl (R.measurableSet_degenerate (j + 1)) (measure_ne_top _ _), hZ,
          measure_univ, tsub_self]
      exact hc
    filter_upwards [hae] with ω hω
    obtain ⟨-, hchi⟩ := R.tendsto_chi_of_degenerate (j + 1) hω
    rw [hchi]
    exact R.tendsto_chi_balanced_of_degenerate (j + 1) hω

/-- **The backward exponent.** `(1/n) log ρ_k(𝓛^{(n)}_{σ^{-n}ω}) → χ_k` almost surely --- the
first of the three limits opening `proof_met.tex` l.695--700, from `kingman_backward` applied to
the same truncated families. With `Cocycle.ae_tendsto_chi` and
`Cocycle.ae_tendsto_chi_balanced` this completes the trio `exists_topFastSpace` opens with. -/
theorem Cocycle.ae_tendsto_chi_backward (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (k : ℕ) [NeZero k] :
    ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) k) / (n : EReal))
      atTop (nhds (R.chi k ω)) := by
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases R.measure_degenerate_eq_zero_or_one (j + 1) with hZ | hZ
  · obtain ⟨Ak, hAktop, hAkf, -, hAkbk⟩ :=
      R.ae_tendsto_logProd_balanced (k := j + 1) (by omega) hZ
    obtain ⟨Aj, hAjtop, hAjf, -, hAjbk⟩ := R.ae_tendsto_logProd_predecessor j hZ
    have hnd : ∀ᵐ ω ∂(R.μ), ω ∉ R.degenerate (j + 1) := by rw [ae_iff]; simpa using hZ
    have hshiftnd := R.ae_all_shift_notMem_degenerate (j + 1) hZ
    filter_upwards [hAkf, hAkbk, hAjf, hAjbk, hnd, hshiftnd] with ω h1 h2 h3 h4 h5 h6
    have hevf : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
        0 < ∏ i ∈ Finset.range (j + 1), bernsteinNumber (R.iterate n ω) (i + 1) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      refine ⟨hn, ?_⟩
      rcases (R.prodBern_nonneg (j + 1) n ω).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨n, hn,
          (prod_bernstein_eq_zero_iff (R.iterate n ω) (by omega)).1 h.symm⟩ h5
    have hevb : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
        0 < ∏ i ∈ Finset.range (j + 1),
          bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (i + 1) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      refine ⟨hn, ?_⟩
      rcases (R.prodBern_nonneg (j + 1) n (zIter R.σ (-(n : ℤ)) ω)).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨n, hn, (prod_bernstein_eq_zero_iff
          (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (by omega)).1 h.symm⟩ (h6 n)
    have hfwd := tendsto_logEReal_bernstein_of_prod_limits (T := fun n => R.iterate n ω)
      (m := fun n => n) hAktop hAjtop hevf h1 h3
    have hbk := tendsto_logEReal_bernstein_of_prod_limits
      (T := fun n => R.iterate n (zIter R.σ (-(n : ℤ)) ω))
      (m := fun n => n) hAktop hAjtop hevb h2 h4
    have hchi : R.chi (j + 1) ω = _ := hfwd.limsup_eq
    rw [hchi]
    exact hbk
  · have hback : R.μ (R.degenerateBack (j + 1)) = 1 :=
      R.measure_degenerateBack_eq_one (j + 1) hZ
    have hae : ∀ᵐ ω ∂(R.μ), ω ∈ R.degenerate (j + 1) ∧ ω ∈ R.degenerateBack (j + 1) := by
      refine Filter.Eventually.and ?_ ?_
      · rw [ae_iff]
        have hc : R.μ (R.degenerate (j + 1))ᶜ = 0 := by
          rw [measure_compl (R.measurableSet_degenerate (j + 1)) (measure_ne_top _ _), hZ,
            measure_univ, tsub_self]
        exact hc
      · rw [ae_iff]
        have hc : R.μ (R.degenerateBack (j + 1))ᶜ = 0 := by
          rw [measure_compl (R.measurableSet_degenerateBack (j + 1)) (measure_ne_top _ _), hback,
            measure_univ, tsub_self]
        exact hc
    filter_upwards [hae] with ω hω
    obtain ⟨-, hchi⟩ := R.tendsto_chi_of_degenerate (j + 1) hω.1
    rw [hchi]
    exact R.tendsto_chi_backward_of_degenerateBack (j + 1) hω.2

theorem Cocycle.measurable_norm_L (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] :
    Measurable fun ω => ‖R.L ω‖ := by
  have h : ∀ ω, ‖R.L ω‖ = bernsteinNumber (R.L ω) 1 := fun ω => (bernsteinNumber_one (R.L ω)).symm
  simp_rw [h]
  exact measurable_bernstein_of_weak 1 (fun x => R.stronglyMeasurable x)

/-- **The generator is tempered along the backward orbit**, `(1/n) log⁺‖𝓛_{σ^{-n}ω}‖ → 0`.
`proof_met.tex` uses it as "`‖𝓛_{σ^{-(n+1)}ω}‖ < e^{nε}` for `n ≥ M_ω`". It is `L1_orbit_decay`
applied to `σ⁻¹`, which is ergodic because `σ` is. -/
theorem Cocycle.ae_tempered_backward (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] :
    ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      Real.log (max ‖R.L (zIter R.σ (-(n : ℤ)) ω)‖ 1) / n) atTop (nhds 0) := by
  have hg : Measurable fun ω : Ω => Real.log (max ‖R.L ω‖ 1) :=
    Real.measurable_log.comp (R.measurable_norm_L.max measurable_const)
  have hL :=
    L1_orbit_decay R.μ (⇑R.σ.symm) R.ergodic.symm.toMeasurePreserving _ hg R.forwardIntegrable
  filter_upwards [hL] with ω hω
  simpa [zIter_neg_natCast] using hω

omit [StandardBorelSpace Ω] in
/-- **A measurable near-optimal subspace.** For a strongly measurable family `A` there is a
measurable `F : Ω → 𝒢_mX` with `g_{A(ω)}(F ω) > e^{-ε} ρ_m(A ω)` wherever `ρ_m(A ω) ≠ 0`.

This is the selection `ι^{(n)}` of `proof_met.tex` l.686: the sets where a fixed member of a
countable dense family is within `e^{-ε}` of optimal are measurable and cover `Ω` (by density of
the family and continuity of `g` in the subspace), so `measurable_of_countable_cover` picks the
first index measurably. The degenerate alternative `ρ_m(A ω) = 0` is what makes the cover total
rather than merely a.e.; it is a null set in every intended application. -/
theorem exists_measurable_near_optimal [SeparableSpace X] [BorelSpace X]
    (m : ℕ) [NeZero m] [Nonempty (GrassmannianFin X m)]
    {A : Ω → X →L[ℝ] X} (hA : ∀ x : X, Measurable fun ω => A ω x) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Ω → GrassmannianFin X m, Measurable F ∧
      ∀ ω, bernsteinNumber (A ω) m = 0 ∨
        Real.exp (-ε) * bernsteinNumber (A ω) m < growth (A ω) ((F ω).1 : Submodule ℝ X) := by
  classical
  have := grassmannianFin_separable (X := X) m
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (GrassmannianFin X m)
  have : Countable D := hDcount.to_subtype
  have : Nonempty D := by
    obtain ⟨V, hV, -⟩ := hDdense.exists_mem_open isOpen_univ Set.univ_nonempty
    exact ⟨⟨V, hV⟩⟩
  obtain ⟨e, hesurj⟩ : ∃ e : ℕ → D, Function.Surjective e := exists_surjective_nat _
  set g : ℕ → GrassmannianFin X m := fun i => ((e i : D) : GrassmannianFin X m) with hg
  set S : ℕ → Set Ω := fun i => {ω | bernsteinNumber (A ω) m = 0 ∨
    Real.exp (-ε) * bernsteinNumber (A ω) m < growth (A ω) ((g i).1 : Submodule ℝ X)} with hS
  have hSmeas : ∀ i, MeasurableSet (S i) := by
    intro i
    refine MeasurableSet.union ?_ ?_
    · exact measurableSet_eq_fun (measurable_bernstein_of_weak m hA) measurable_const
    · refine measurableSet_lt ((measurable_bernstein_of_weak m hA).const_mul _) ?_
      exact measurable_growth_of_weak hA _ (sphere_inter_nonempty_of_finrank _)
  have hcover : (⋃ i, S i) = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    rcases eq_or_ne (bernsteinNumber (A ω) m) 0 with h0 | h0
    · exact Set.mem_iUnion.2 ⟨0, Or.inl h0⟩
    · have hpos : 0 < bernsteinNumber (A ω) m :=
        lt_of_le_of_ne (bernsteinNumber_nonneg _ _) (Ne.symm h0)
      have hlt : Real.exp (-ε) * bernsteinNumber (A ω) m < bernsteinNumber (A ω) m := by
        have : Real.exp (-ε) < 1 := by
          rw [Real.exp_lt_one_iff]; linarith
        nlinarith
      obtain ⟨_, ⟨V, rfl⟩, hV⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hlt
      have hopen : IsOpen {W : GrassmannianFin X m |
          Real.exp (-ε) * bernsteinNumber (A ω) m < growth (A ω) (W.1 : Submodule ℝ X)} :=
        isOpen_lt continuous_const ((growth_continuous m).comp
          (continuous_const.prodMk continuous_id))
      obtain ⟨W, hWD, hWmem⟩ := hDdense.exists_mem_open hopen ⟨V, hV⟩
      obtain ⟨i, hi⟩ := hesurj ⟨W, hWD⟩
      refine Set.mem_iUnion.2 ⟨i, Or.inr ?_⟩
      have : g i = W := by rw [hg]; simp only []; rw [hi]
      rw [this]
      exact hWmem
  obtain ⟨N, hNmeas, hFmeas, hN⟩ := measurable_of_countable_cover g S hSmeas hcover
  refine ⟨fun ω => g (N ω), hFmeas, fun ω => ?_⟩
  exact (hN ω).1

omit [StandardBorelSpace Ω] in
/-- **The pushforward as a total measurable map.** `A(ω)E(ω)` is `k`-dimensional exactly where
`A(ω)` is injective on `E(ω)`; `proof_met.tex` only ever uses it on the full-measure set where
that holds, so off a measurable `G` carrying that guarantee we plant a constant. Measurability is
`measurable_of_measurable_infDist` glued piecewise, the good branch being
`measurable_infDist_map`. -/
theorem exists_measurable_pushforward_on [SeparableSpace X] [CompleteSpace X]
    [OpensMeasurableSpace X] (k : ℕ) [NeZero k] [Nonempty (GrassmannianFin X k)]
    {B : Ω → X →L[ℝ] X} (hB : ∀ x : X, Measurable fun ω => B ω x)
    {E : Ω → GrassmannianFin X k} (hE : Measurable E)
    {G : Set Ω} (hG : MeasurableSet G)
    (hpos : ∀ ω ∈ G, 0 < growth (B ω) ((E ω).1 : Submodule ℝ X)) :
    ∃ F : Ω → GrassmannianFin X k, Measurable F ∧
      ∀ ω ∈ G, ((F ω).1 : Submodule ℝ X)
        = Submodule.map ((B ω : X →ₗ[ℝ] X)) ((E ω).1 : Submodule ℝ X) := by
  classical
  set c : GrassmannianFin X k := Classical.arbitrary _ with hc
  set F : Ω → GrassmannianFin X k := fun ω =>
    if h : ω ∈ G then GrassmannianFin.pushforward (B ω) (E ω) (hpos ω h) else c with hF
  have hFeq : ∀ ω ∈ G, ((F ω).1 : Submodule ℝ X)
      = Submodule.map ((B ω : X →ₗ[ℝ] X)) ((E ω).1 : Submodule ℝ X) := by
    intro ω hω
    rw [hF]
    simp only [dite_eq_left hω]
    rfl
  refine ⟨F, ?_, hFeq⟩
  refine measurable_of_measurable_infDist k fun x => ?_
  have hpiece : (fun ω => Metric.infDist x (((F ω).1 : Submodule ℝ X) : Set X))
      = G.piecewise (fun ω => Metric.infDist x ((B ω) '' (((E ω).1 : Submodule ℝ X) : Set X)))
          (fun _ => Metric.infDist x ((c.1 : Submodule ℝ X) : Set X)) := by
    funext ω
    by_cases hω : ω ∈ G
    · rw [Set.piecewise_eq_of_mem _ _ _ hω]
      congr 1
      rw [hFeq ω hω]
      ext z
      simp []
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω, hF]
      simp only [dite_eq_right hω]
  rw [hpiece]
  exact Measurable.piecewise hG (measurable_infDist_map k hE hB x) measurable_const

theorem Cocycle.measurable_zIter_neg (R : Cocycle Ω X) (n : ℕ) :
    Measurable fun ω : Ω => zIter R.σ (-(n : ℤ)) ω := by
  simp only [zIter_neg_natCast]
  exact R.σ.symm.measurable.iterate n

/-- **The approximating spaces of `proof_met.tex` l.680--692.** For each `n`, `E_tilde⁽ⁿ⁾` is a
measurable choice of `m`-dimensional subspace within `e^{-ε}` of optimal for
`𝓛^{(2n)}_{σ^{-n}ω}`, and `E⁽ⁿ⁾ = 𝓛^{(n)}_{σ^{-n}ω} E_tilde⁽ⁿ⁾` is its pushforward, measurable by
`lem:GXpush`. Both are total functions; the identities hold on the measurable set
`G n = {ρ_m(𝓛^{(2n)}_{σ^{-n}ω}) ≠ 0}`, which is conull in every intended application. -/
theorem Cocycle.exists_approx_spaces (R : Cocycle Ω X) [SeparableSpace X] [CompleteSpace X]
    [BorelSpace X] (m : ℕ) [NeZero m] [Nonempty (GrassmannianFin X m)] {ε : ℝ} (hε : 0 < ε) :
    ∃ Etil E : ℕ → Ω → GrassmannianFin X m,
      (∀ n, Measurable (Etil n)) ∧ (∀ n, Measurable (E n)) ∧
      (∀ n ω, bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 →
        (Real.exp (-ε) * bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m
            < growth (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω))
              ((Etil n ω).1 : Submodule ℝ X)) ∧
          ((E n ω).1 : Submodule ℝ X)
            = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
              ((Etil n ω).1 : Submodule ℝ X)) := by
  classical
  have hwk2 : ∀ n : ℕ, ∀ x : X,
      Measurable fun ω => R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω) x := fun n x =>
    (R.measurable_iterate_apply (2 * n) x).comp (R.measurable_zIter_neg n)
  have hwk1 : ∀ n : ℕ, ∀ x : X,
      Measurable fun ω => R.iterate n (zIter R.σ (-(n : ℤ)) ω) x := fun n x =>
    (R.measurable_iterate_apply n x).comp (R.measurable_zIter_neg n)
  choose Etil hEtilmeas hEtilnear using fun n : ℕ =>
    exists_measurable_near_optimal (Ω := Ω) m (hwk2 n) hε
  have hGmeas : ∀ n : ℕ, MeasurableSet
      {ω : Ω | bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0} := by
    intro n
    exact (measurableSet_eq_fun (measurable_bernstein_of_weak m (hwk2 n)) measurable_const).compl
  have hpos : ∀ n : ℕ, ∀ ω ∈ {ω : Ω |
      bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0},
      0 < growth (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) ((Etil n ω).1 : Submodule ℝ X) := by
    intro n ω hω
    have hne : bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 := hω
    have hnear := (hEtilnear n ω).resolve_left hne
    have hρpos : 0 < bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m :=
      lt_of_le_of_ne (bernsteinNumber_nonneg _ _) (Ne.symm hne)
    have h2n : 0 < growth (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω))
        ((Etil n ω).1 : Submodule ℝ X) :=
      lt_of_lt_of_le (by positivity) hnear.le
    by_contra hcon
    rw [not_lt] at hcon
    have hzero : growth (R.iterate n (zIter R.σ (-(n : ℤ)) ω))
        ((Etil n ω).1 : Submodule ℝ X) = 0 :=
      le_antisymm hcon (growth_nonneg _ _)
    have hsplit := R.iterate_two_mul_shift n ω
    have hle := (growth_ineq (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (R.iterate n ω)
      ((Etil n ω).1 : Submodule ℝ X)).2
    rw [← hsplit] at hle
    have := le_trans hle (min_le_right _ _)
    rw [hzero, zero_mul] at this
    exact absurd (le_antisymm this (growth_nonneg _ _)) (ne_of_gt h2n)
  choose E hEmeas hEeq using fun n : ℕ =>
    exists_measurable_pushforward_on (Ω := Ω) m (hwk1 n) (hEtilmeas n) (hGmeas n) (hpos n)
  refine ⟨Etil, E, hEtilmeas, hEmeas, fun n ω hne => ⟨(hEtilnear n ω).resolve_left hne, ?_⟩⟩
  exact hEeq n ω hne

/-- Lower companion of `logEReal_div_le_iff`. -/
theorem lt_logEReal_div_iff {x : ℝ} {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    (r : EReal) < logEReal x / (n : EReal) ↔ Real.exp (r * n) < x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [logEReal_of_nonpos hx, bot_div_natCast hn]
    simp only [not_lt_bot, false_iff, not_lt]
    exact hx.trans (Real.exp_pos _).le
  · rw [logEReal_of_pos hx]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [show ((Real.log x : EReal) / (n : EReal)) = ((Real.log x / (n : ℝ) : ℝ) : EReal) from rfl,
      EReal.coe_lt_coe_iff, lt_div_iff₀ hn0, ← Real.lt_log_iff_exp_lt hx]

/-- **Two-sided exponential bounds from an exponent limit.** If `(1/n) log u_n → c` and
`a < c < b` then eventually `e^{an} < u_n < e^{bn}`. This is how every estimate in
`proof_met.tex` l.700--712 is obtained. -/
theorem eventually_exp_bounds_of_tendsto {u : ℕ → ℝ} {c : EReal} {a b : ℝ}
    (hac : (a : EReal) < c) (hcb : c < (b : EReal))
    (h : Tendsto (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop (nhds c)) :
    ∀ᶠ n : ℕ in atTop, Real.exp (a * n) < u n ∧ u n < Real.exp (b * n) := by
  filter_upwards [h.eventually_const_lt hac, h.eventually_lt_const hcb,
    eventually_ge_atTop 1] with n h1 h2 hn
  exact ⟨(lt_logEReal_div_iff hn a).1 h1, (logEReal_div_lt_iff hn b).1 h2⟩

/-- The one-sided form, which is all that is available when the exponent is `-∞`. -/
theorem eventually_lt_exp_of_tendsto {u : ℕ → ℝ} {c : EReal} {b : ℝ} (hcb : c < (b : EReal))
    (h : Tendsto (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop (nhds c)) :
    ∀ᶠ n : ℕ in atTop, u n < Real.exp (b * n) := by
  filter_upwards [h.eventually_lt_const hcb, eventually_ge_atTop 1] with n h2 hn
  exact (logEReal_div_lt_iff hn b).1 h2

/-- **Every index up to `m₁` carries the top exponent.** `m₁` is by construction one less than
the first index at which `χ` drops, so `χ_t = χ_1` for `1 ≤ t ≤ m₁` — `χ` being antitone gives
`≤`, and minimality of the drop gives `≥`. -/
theorem Cocycle.chi_eq_chi_one_of_le_mult (R : Cocycle Ω X) (ω : Ω) {t : ℕ} (h1 : 1 ≤ t)
    (ht : t ≤ R.mult 0 ω) : R.chi t ω = R.chi 1 ω := by
  set S : Set ℕ := {s : ℕ | 1 ≤ s ∧ R.chi s ω < R.chi (R.lambdaIdx 0 ω) ω} with hS
  have hidx : R.lambdaIdx 1 ω = sInf S := rfl
  have hmult : R.mult 0 ω = sInf S - 1 := rfl
  have hlt : t < sInf S := by omega
  have hnot : t ∉ S := fun hmem => absurd (Nat.sInf_le hmem) (not_le.2 hlt)
  simp only [hS, Set.mem_ofPred_eq, not_and, not_lt] at hnot
  have hge : R.chi (R.lambdaIdx 0 ω) ω ≤ R.chi t ω := hnot h1
  have hle : R.chi t ω ≤ R.chi 1 ω := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact R.chi_antitone ω (by omega : 0 ≤ s)
  exact le_antisymm hle hge

/-- **And the next index does not.** -/
theorem Cocycle.chi_mult_succ_lt (R : Cocycle Ω X) (ω : Ω) (h : 0 < R.mult 0 ω) :
    R.chi (R.mult 0 ω + 1) ω < R.chi 1 ω := by
  set S : Set ℕ := {s : ℕ | 1 ≤ s ∧ R.chi s ω < R.chi (R.lambdaIdx 0 ω) ω} with hS
  have hmult : R.mult 0 ω = sInf S - 1 := rfl
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmult
    simp at hmult
    omega
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  have heq : R.mult 0 ω + 1 = sInf S := by
    have : 1 ≤ sInf S := hmem.1
    omega
  rw [heq]
  exact hmem.2

omit [MeasurableSpace X] in
/-- `g_{S∘T}(V) ≤ g_T(V)‖S‖`: the named half of `growth_ineq` that transfers a growth estimate
for a long window back to its *first* factor. `proof_met.tex` l.710 uses it as
`g(𝓛^{(n)}_{σ^{-n}ω}, E_tilde) ≥ g(𝓛^{(2n)}_{σ^{-n}ω}, E_tilde)/‖𝓛^{(n)}_ω‖`. -/
theorem growth_comp_le_mul_norm (T S : X →L[ℝ] X) (V : Submodule ℝ X) :
    growth (S.comp T) V ≤ growth T V * ‖S‖ :=
  le_trans (growth_ineq T S V).2 (min_le_right _ _)

omit [MeasurableSpace X] in
/-- `g_{S∘T}(V) ≤ ‖T‖ g_S(TV)`: the half that transfers to the *second* factor, on the pushed
subspace. `proof_met.tex` l.712 uses it as
`g(𝓛^{(n)}_ω, E^{(n)}(ω)) ≥ g(𝓛^{(2n)}_{σ^{-n}ω}, E_tilde)/‖𝓛^{(n)}_{σ^{-n}ω}‖`. -/
theorem growth_comp_le_norm_mul (T S : X →L[ℝ] X) (V : Submodule ℝ X) :
    growth (S.comp T) V ≤ ‖T‖ * growth S (V.map (T : X →ₗ[ℝ] X)) :=
  le_trans (growth_ineq T S V).2 (min_le_left _ _)

omit [MeasurableSpace X] in
/-- Division form of `growth_comp_le_mul_norm`. -/
theorem div_norm_le_growth (T S : X →L[ℝ] X) (V : Submodule ℝ X) (hS : 0 < ‖S‖) :
    growth (S.comp T) V / ‖S‖ ≤ growth T V := by
  rw [div_le_iff₀ hS]
  exact growth_comp_le_mul_norm T S V

omit [MeasurableSpace X] in
/-- Division form of `growth_comp_le_norm_mul`. -/
theorem div_norm_le_growth_map (T S : X →L[ℝ] X) (V : Submodule ℝ X) (hT : 0 < ‖T‖) :
    growth (S.comp T) V / ‖T‖ ≤ growth S (V.map (T : X →ₗ[ℝ] X)) := by
  rw [div_le_iff₀ hT, mul_comm]
  exact growth_comp_le_norm_mul T S V

omit [MeasurableSpace X] in
/-- **Geometric form of `pushclose`.** Once the gap factor `ρ_{m+1}(T)/Θ` is at most `1/2`, the
`4/(1-·)` in `pushclose` is at most `8`, so the estimate is a clean geometric one. This is the
form the Cauchy argument of `proof_met.tex` l.730--735 uses. -/
theorem pushclose_geom (m : ℕ) [NeZero m] (T : X →L[ℝ] X) (Θ : ℝ) (hΘpos : 0 < Θ)
    (hhalf : bernsteinNumber T (m + 1) ≤ Θ / 2) (V W : GrassmannianFin X m)
    (hV : Θ < growth T (V.1 : Submodule ℝ X)) (hW : Θ < growth T (W.1 : Submodule ℝ X)) :
    dist (GrassmannianFin.pushforward T V
            (lt_of_le_of_lt (bernsteinNumber_nonneg T (m + 1))
              ((lt_of_le_of_lt hhalf (by linarith)).trans hV)))
         (GrassmannianFin.pushforward T W
            (lt_of_le_of_lt (bernsteinNumber_nonneg T (m + 1))
              ((lt_of_le_of_lt hhalf (by linarith)).trans hW)))
      ≤ 8 * (bernsteinNumber T (m + 1) / Θ) := by
  have hΘ : bernsteinNumber T (m + 1) < Θ := lt_of_le_of_lt hhalf (by linarith)
  have hratio : bernsteinNumber T (m + 1) / Θ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hΘpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hrnn : 0 ≤ bernsteinNumber T (m + 1) / Θ :=
    div_nonneg (bernsteinNumber_nonneg _ _) hΘpos.le
  refine le_trans (pushclose m T Θ hΘ V W hV hW) ?_
  have hden : (1 : ℝ) / 2 ≤ 1 - bernsteinNumber T (m + 1) / Θ := by linarith
  have hdenpos : (0 : ℝ) < 1 - bernsteinNumber T (m + 1) / Θ := by linarith
  have hfour : 4 / (1 - bernsteinNumber T (m + 1) / Θ) ≤ 8 := by
    rw [div_le_iff₀ hdenpos]
    linarith
  exact mul_le_mul_of_nonneg_right hfour hrnn

/-- `𝓛^{(n+1)}_{σ^{-(n+1)}ω} = 𝓛^{(n)}_{σ^{-n}ω} ∘ 𝓛_{σ^{-(n+1)}ω}`: the two consecutive backward
windows differ by one step at the far end. This is what puts `E^{(n)}(ω)` and `E^{(n+1)}(ω)` in
the range of the *same* operator, which is what lets `pushclose` compare them. -/
theorem Cocycle.iterate_shift_succ (R : Cocycle Ω X) (n : ℕ) (ω : Ω) :
    R.iterate (n + 1) (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)
      = (R.iterate n (zIter R.σ (-(n : ℤ)) ω)).comp
          (R.L (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)) := by
  have hsplit := R.iterate_shift_split (p := n) (n := n + 1) (by omega) ω
  rw [hsplit]
  congr 1
  rw [show n + 1 - n = 1 from by omega]
  exact R.iterate_one _

omit [MeasurableSpace X] in
/-- Pushing forward in two steps is pushing forward by the composite. -/
theorem GrassmannianFin.pushforward_comp {m : ℕ} (T S : X →L[ℝ] X) (V : GrassmannianFin X m)
    (hS : 0 < growth S (V.1 : Submodule ℝ X))
    (hT : 0 < growth T (((GrassmannianFin.pushforward S V hS).1 : Submodule ℝ X)))
    (hTS : 0 < growth (T.comp S) (V.1 : Submodule ℝ X)) :
    GrassmannianFin.pushforward T (GrassmannianFin.pushforward S V hS) hT
      = GrassmannianFin.pushforward (T.comp S) V hTS := by
  apply Subtype.ext
  change Submodule.map (T.toLinearMap) (Submodule.map (S.toLinearMap) (V.1 : Submodule ℝ X))
    = Submodule.map ((T.comp S).toLinearMap) (V.1 : Submodule ℝ X)
  rw [← Submodule.map_comp]
  rfl

omit [MeasurableSpace X] in
/-- **The Cauchy step of `proof_met.tex` l.730--735, as a statement about two subspaces.**
`E^{(n)}(ω)` is `T V` and `E^{(n+1)}(ω)` is `(T∘S) V'`, with `T = 𝓛^{(n)}_{σ^{-n}ω}` and
`S = 𝓛_{σ^{-(n+1)}ω}`; rewriting the latter as `T (S V')` puts both in the range of the same `T`,
and `pushclose` then compares them. -/
theorem dist_pushforward_le_of_estimates (m : ℕ) [NeZero m]
    {T S : X →L[ℝ] X} {V V' : GrassmannianFin X m} {Θ : ℝ}
    (hΘpos : 0 < Θ)
    (hρ : bernsteinNumber T (m + 1) ≤ Θ / 2)
    (hV : Θ < growth T (V.1 : Submodule ℝ X))
    (hSpos : 0 < growth S (V'.1 : Submodule ℝ X))
    (hSV' : Θ < growth T (((GrassmannianFin.pushforward S V' hSpos).1 : Submodule ℝ X))) :
    dist (GrassmannianFin.pushforward T V (hΘpos.trans hV))
         (GrassmannianFin.pushforward (T.comp S) V'
            (lt_of_lt_of_le (mul_pos hSpos (hΘpos.trans hSV'))
              (growth_ineq S T (V'.1 : Submodule ℝ X)).1))
      ≤ 8 * (bernsteinNumber T (m + 1) / Θ) := by
  rw [← GrassmannianFin.pushforward_comp T S V' hSpos (hΘpos.trans hSV')]
  exact pushclose_geom m T Θ hΘpos hρ V (GrassmannianFin.pushforward S V' hSpos) hV hSV'

/-- **The threshold `Θ_n` of the Cauchy step, with the paper's sign condition removed.**
`proof_met.tex` takes `Θ = e^{n(λ₁-4ε)}`, which makes the second bound below require
`λ₁ ≥ 3ε` --- true only when `λ₁ > 0`, which is not assumed. Multiplying by
`C₀ = min(1, e^{λ₁-4ε}) ≤ 1` repairs it: the second bound then holds with equality in the
exponent, and `C₀` is a constant, so it is absorbed into the geometric rate. -/
theorem theta_le_bounds (lam eps : ℝ) (heps : 0 < eps) {n : ℕ} (hn : 1 ≤ n) :
    (0 : ℝ) < min 1 (Real.exp (lam - 4 * eps)) * Real.exp (n * (lam - 4 * eps)) ∧
    min 1 (Real.exp (lam - 4 * eps)) * Real.exp (n * (lam - 4 * eps))
      ≤ Real.exp ((n : ℝ) * (lam - 3 * eps) - eps) ∧
    min 1 (Real.exp (lam - 4 * eps)) * Real.exp (n * (lam - 4 * eps))
      ≤ Real.exp (((n : ℝ) + 1) * (lam - 3 * eps) - eps - (n : ℝ) * eps) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hCpos : (0 : ℝ) < min 1 (Real.exp (lam - 4 * eps)) :=
    lt_min one_pos (Real.exp_pos _)
  refine ⟨by positivity, ?_, ?_⟩
  · calc min 1 (Real.exp (lam - 4 * eps)) * Real.exp ((n : ℝ) * (lam - 4 * eps))
        ≤ 1 * Real.exp ((n : ℝ) * (lam - 4 * eps)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) * (lam - 4 * eps)) := one_mul _
      _ ≤ Real.exp ((n : ℝ) * (lam - 3 * eps) - eps) := by
          refine Real.exp_le_exp.2 ?_
          nlinarith
  · calc min 1 (Real.exp (lam - 4 * eps)) * Real.exp ((n : ℝ) * (lam - 4 * eps))
        ≤ Real.exp (lam - 4 * eps) * Real.exp ((n : ℝ) * (lam - 4 * eps)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
      _ = Real.exp (((n : ℝ) + 1) * (lam - 3 * eps) - eps - (n : ℝ) * eps) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- The geometric decay that makes the Cauchy estimate summable: `ρ_{m+1}(T) < e^{n λ₂}` is
eventually below `Θ_n/2`. -/
theorem eventually_exp_le_half {lam lam2 eps C0 : ℝ} (hC0 : 0 < C0) (heps : 0 < eps)
    (hgap : lam2 + 6 * eps < lam) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ) * lam2) ≤ C0 * Real.exp ((n : ℝ) * (lam - 4 * eps)) / 2 := by
  have hc : 0 < lam - 4 * eps - lam2 := by linarith
  have htend : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * (lam - 4 * eps - lam2))))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => -((n : ℝ) * (lam - 4 * eps - lam2))) atTop atBot := by
      refine tendsto_neg_atTop_atBot.comp ?_
      exact tendsto_natCast_atTop_atTop.atTop_mul_const hc
    exact Real.tendsto_exp_atBot.comp h1
  filter_upwards [htend.eventually_le_const (show (0 : ℝ) < C0 / 2 by positivity)] with n hn
  have hkey : Real.exp ((n : ℝ) * lam2)
      = Real.exp ((n : ℝ) * (lam - 4 * eps)) * Real.exp (-((n : ℝ) * (lam - 4 * eps - lam2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hkey]
  have hpos : (0 : ℝ) < Real.exp ((n : ℝ) * (lam - 4 * eps)) := Real.exp_pos _
  calc Real.exp ((n : ℝ) * (lam - 4 * eps)) * Real.exp (-((n : ℝ) * (lam - 4 * eps - lam2)))
      ≤ Real.exp ((n : ℝ) * (lam - 4 * eps)) * (C0 / 2) :=
        mul_le_mul_of_nonneg_left hn hpos.le
    _ = C0 * Real.exp ((n : ℝ) * (lam - 4 * eps)) / 2 := by ring

/-- A sequence whose consecutive distances are *eventually* dominated by a geometric series is
Cauchy. Mathlib's `cauchySeq_of_le_geometric` wants the bound at every index; the topfast
construction only gets it past a measurable, unbounded threshold `M_ω`. -/
theorem cauchySeq_of_eventually_dist_le_geom {Y : Type*} [MetricSpace Y] (f : ℕ → Y)
    {C r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (h : ∀ᶠ n in atTop, dist (f n) (f (n + 1)) ≤ C * r ^ n) : CauchySeq f := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  apply cauchySeq_of_summable_dist
  rw [← summable_nat_add_iff N]
  have hC' : 0 ≤ C * r ^ N := le_trans dist_nonneg (hN N le_rfl)
  refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_)
    ((summable_geometric_of_lt_one hr0 hr).mul_left (C * r ^ N))
  have hle := hN (n + N) (Nat.le_add_left _ _)
  calc dist (f (n + N)) (f (n + N + 1)) ≤ C * r ^ (n + N) := hle
    _ = C * r ^ N * r ^ n := by rw [pow_add]; ring

omit [StandardBorelSpace Ω] [MeasurableSpace X] in
/-- An a.e.-Cauchy sequence of measurable Grassmannian-valued functions has a measurable a.e.
limit. -/
theorem exists_measurable_limit_of_ae_cauchy [CompleteSpace X] {m : ℕ} [NeZero m]
    {μ : Measure Ω} (F : ℕ → Ω → GrassmannianFin X m) (hmeas : ∀ n, Measurable (F n))
    (hcauchy : ∀ᵐ ω ∂μ, CauchySeq (fun n => F n ω)) :
    ∃ E : Ω → GrassmannianFin X m, Measurable E ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (nhds (E ω)) := by
  have := grassmannianFin_complete (X := X) m
  refine measurable_limit_of_tendsto_metrizable_ae (fun n => (hmeas n).aemeasurable) ?_
  filter_upwards [hcauchy] with ω hω
  exact ⟨_, hω.tendsto_limUnder⟩

omit [MeasurableSpace X] in
/-- Transfer a growth lower bound for a window `S∘T` back to the *first* factor, dividing by a
bound on `‖S‖`: the division form of `proof_met.tex` l.710. -/
theorem lt_growth_of_lt_comp {T S : X →L[ℝ] X} {V : Submodule ℝ X} {a b : ℝ} (hb0 : 0 < b)
    (hS : ‖S‖ ≤ b) (ha : a < growth (S.comp T) V) : a / b < growth T V := by
  rw [div_lt_iff₀ hb0]
  refine ha.trans_le (le_trans (growth_comp_le_mul_norm T S V) ?_)
  exact mul_le_mul_of_nonneg_left hS (growth_nonneg _ _)

omit [MeasurableSpace X] in
/-- Transfer a growth lower bound for a window `S∘T` to the *second* factor, on the pushed
subspace: the division form of `proof_met.tex` l.712. -/
theorem lt_growth_map_of_lt_comp {T S : X →L[ℝ] X} {V : Submodule ℝ X} {a b : ℝ} (hb0 : 0 < b)
    (hT : ‖T‖ ≤ b) (ha : a < growth (S.comp T) V) :
    a / b < growth S (V.map (T : X →ₗ[ℝ] X)) := by
  rw [div_lt_iff₀ hb0, mul_comm]
  refine ha.trans_le (le_trans (growth_comp_le_norm_mul T S V) ?_)
  exact mul_le_mul_of_nonneg_right hT (growth_nonneg _ _)

/-- The balanced-window companion of `eventually_exp_bounds_of_tendsto`: the balanced Kingman
limit divides by `2n`, not `n`. -/
theorem eventually_exp_bounds_of_tendsto_two_mul {u : ℕ → ℝ} {c : EReal} {a b : ℝ}
    (hac : (a : EReal) < c) (hcb : c < (b : EReal))
    (h : Tendsto (fun n : ℕ => logEReal (u n) / ((2 * n : ℕ) : EReal)) atTop (nhds c)) :
    ∀ᶠ n : ℕ in atTop, Real.exp (a * (2 * n : ℕ)) < u n ∧ u n < Real.exp (b * (2 * n : ℕ)) := by
  filter_upwards [h.eventually_const_lt hac, h.eventually_lt_const hcb,
    eventually_ge_atTop 1] with n h1 h2 hn
  have hn' : 1 ≤ 2 * n := by omega
  exact ⟨(lt_logEReal_div_iff hn' a).1 h1, (logEReal_div_lt_iff hn' b).1 h2⟩

/-- **The five eventual estimates of `proof_met.tex` l.700--712, packaged.**

The paper chooses a threshold `M_ω` and lists the estimates that hold beyond it. Here the
threshold stays implicit inside `∀ᶠ n in atTop`, which is what keeps the argument pointwise: it
is *not* uniform in `ω`, and a uniform version is false.

`lam` is `λ₁`; `lam2` is any real strictly above `χ_{m+1}` (it may be `⊥`, so `λ₂` itself need
not be a real). The tempering estimate is stated at the shifted index `-(n+1)` and with the
paper's `e^{nε}` replaced by `e^{ε(n+1)}`, which is what `ae_tempered_backward` actually gives
and is absorbed by the same arithmetic. -/
theorem Cocycle.ae_eventually_estimates (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (m : ℕ) [NeZero m] {lam lam2 eps : ℝ} (heps : 0 < eps)
    (hchim : ∀ᵐ ω ∂(R.μ), R.chi m ω = (lam : EReal))
    (hchi1 : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = (lam : EReal))
    (hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω < (lam2 : EReal)) :
    ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
          < bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ∧
      ‖R.iterate n ω‖ < Real.exp ((lam + eps) * n) ∧
      ‖R.iterate n (zIter R.σ (-(n : ℤ)) ω)‖ < Real.exp ((lam + eps) * n) ∧
      max ‖R.L (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)‖ 1 < Real.exp (eps * ((n : ℝ) + 1)) ∧
      bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (m + 1)
          < Real.exp (lam2 * n) := by
  have hlow : (lam - eps : EReal) < (lam : EReal) := by
    exact_mod_cast (by linarith : lam - eps < lam)
  have hhigh : (lam : EReal) < ((lam + eps : ℝ) : EReal) := by
    exact_mod_cast (by linarith : lam < lam + eps)
  filter_upwards [hchim, hchi1, hchi2, R.ae_tendsto_chi_balanced m, R.ae_tendsto_chi 1,
    R.ae_tendsto_chi_backward 1, R.ae_tendsto_chi_backward (m + 1), R.ae_tempered_backward]
    with ω hm h1 h2 hbal hfwd hback hback2 htemp
  -- the balanced estimate
  have e1 : ∀ᶠ n : ℕ in atTop, Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
      < bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m := by
    filter_upwards [eventually_exp_bounds_of_tendsto_two_mul (a := lam - eps) (b := lam + eps)
      (by rw [hm]; exact hlow) (by rw [hm]; exact hhigh) hbal] with n hn using hn.1
  -- the forward norm estimate
  have e2 : ∀ᶠ n : ℕ in atTop, ‖R.iterate n ω‖ < Real.exp ((lam + eps) * n) := by
    have := eventually_exp_bounds_of_tendsto (a := lam - eps) (b := lam + eps)
      (by rw [h1]; exact hlow) (by rw [h1]; exact hhigh) hfwd
    filter_upwards [this] with n hn
    simpa [bernsteinNumber_one] using hn.2
  -- the backward norm estimate
  have e3 : ∀ᶠ n : ℕ in atTop,
      ‖R.iterate n (zIter R.σ (-(n : ℤ)) ω)‖ < Real.exp ((lam + eps) * n) := by
    have := eventually_exp_bounds_of_tendsto (a := lam - eps) (b := lam + eps)
      (by rw [h1]; exact hlow) (by rw [h1]; exact hhigh) hback
    filter_upwards [this] with n hn
    simpa [bernsteinNumber_one] using hn.2
  -- the tempering estimate, shifted by one
  have e4 : ∀ᶠ n : ℕ in atTop,
      max ‖R.L (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)‖ 1 < Real.exp (eps * ((n : ℝ) + 1)) := by
    have hbase : ∀ᶠ k : ℕ in atTop,
        max ‖R.L (zIter R.σ (-(k : ℤ)) ω)‖ 1 < Real.exp (eps * k) := by
      filter_upwards [htemp.eventually_lt_const heps, eventually_ge_atTop 1] with k hk hk1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hpos : (0 : ℝ) < max ‖R.L (zIter R.σ (-(k : ℤ)) ω)‖ 1 :=
        lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hlog : Real.log (max ‖R.L (zIter R.σ (-(k : ℤ)) ω)‖ 1) < eps * k := by
        rw [div_lt_iff₀ hk0] at hk
        linarith
      calc max ‖R.L (zIter R.σ (-(k : ℤ)) ω)‖ 1
          = Real.exp (Real.log (max ‖R.L (zIter R.σ (-(k : ℤ)) ω)‖ 1)) := (Real.exp_log hpos).symm
        _ < Real.exp (eps * k) := Real.exp_lt_exp.2 hlog
    have := (tendsto_add_atTop_nat 1).eventually hbase
    filter_upwards [this] with n hn
    simpa using hn
  -- the gap estimate
  have e5 : ∀ᶠ n : ℕ in atTop,
      bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (m + 1) < Real.exp (lam2 * n) :=
    eventually_lt_exp_of_tendsto h2 hback2
  filter_upwards [e1, e2, e3, e4, e5] with n h h' h'' h''' h'''' using ⟨h, h', h'', h''', h''''⟩

/-- **The Cauchy step of `proof_met.tex` l.710--735, at one `ω`.** -/
theorem Cocycle.eventually_dist_approx_le (R : Cocycle Ω X) (m : ℕ) [NeZero m]
    {lam lam2 eps : ℝ} (heps : 0 < eps) (hgap : lam2 + 6 * eps < lam)
    (Etil E : ℕ → Ω → GrassmannianFin X m) (ω : Ω)
    (hnear : ∀ n : ℕ, bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 →
        (Real.exp (-eps) * bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m
            < growth (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) ((Etil n ω).1 : Submodule ℝ X)) ∧
        (((E n ω).1 : Submodule ℝ X)
            = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
              ((Etil n ω).1 : Submodule ℝ X)))
    (hest : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
          < bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ∧
      ‖R.iterate n ω‖ < Real.exp ((lam + eps) * n) ∧
      ‖R.iterate n (zIter R.σ (-(n : ℤ)) ω)‖ < Real.exp ((lam + eps) * n) ∧
      max ‖R.L (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)‖ 1 < Real.exp (eps * ((n : ℝ) + 1)) ∧
      bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (m + 1) < Real.exp (lam2 * n)) :
    ∀ᶠ n : ℕ in atTop, dist (E n ω) (E (n + 1) ω)
      ≤ 8 * (Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps)))⁻¹
          * Real.exp (-(lam - 4 * eps - lam2)) ^ n := by
  have hC0pos : (0 : ℝ) < Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps)) :=
    mul_pos (Real.exp_pos _) (lt_min one_pos (Real.exp_pos _))
  have hest1 := (tendsto_add_atTop_nat 1).eventually hest
  have hhalf := eventually_exp_le_half (lam := lam) (lam2 := lam2) (eps := eps)
    (C0 := Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps))) hC0pos heps hgap
  filter_upwards [hest, hest1, hhalf, eventually_ge_atTop 1] with n hn hn1 hhn hn0
  obtain ⟨hbal, hfwd, -, htemp, hgapn⟩ := hn
  obtain ⟨hbal1, hfwd1, -, -, -⟩ := hn1
  set T : X →L[ℝ] X := R.iterate n (zIter R.σ (-(n : ℤ)) ω) with hTdef
  set S : X →L[ℝ] X := R.L (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω) with hSdef
  set V : Submodule ℝ X := ((Etil n ω).1 : Submodule ℝ X) with hVdef
  set V' : Submodule ℝ X := ((Etil (n + 1) ω).1 : Submodule ℝ X) with hV'def
  set C0 : ℝ := Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps)) with hC0def
  set Θ : ℝ := C0 * Real.exp ((n : ℝ) * (lam - 4 * eps)) with hΘdef
  have hΘpos : 0 < Θ := by rw [hΘdef]; positivity
  have hb := theta_le_bounds lam eps heps hn0
  -- the near-optimal choices at `n` and at `n+1`
  have hne : bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 :=
    ne_of_gt ((Real.exp_pos _).trans hbal)
  obtain ⟨hnearn, hEeq⟩ := hnear n hne
  have hne1 : bernsteinNumber (R.iterate (2 * (n + 1)) (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)) m ≠ 0 :=
    ne_of_gt ((Real.exp_pos _).trans hbal1)
  obtain ⟨hnear1, hEeq1⟩ := hnear (n + 1) hne1
  -- Step A: `E_tilde^{(n)}` grows fast under the backward window `T`
  have hWsplit := R.iterate_two_mul_shift n ω
  have hA1 : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
      < growth ((R.iterate n ω).comp T) V := by
    rw [← hWsplit]
    exact lt_trans (by gcongr) hnearn
  have hA2 := lt_growth_of_lt_comp (b := Real.exp ((lam + eps) * n)) (Real.exp_pos _)
    hfwd.le hA1
  have hAval : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
      / Real.exp ((lam + eps) * n) = Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [hAval] at hA2
  have hVgrow : Θ < growth T V := by
    refine lt_of_le_of_lt ?_ hA2
    rw [hΘdef, hC0def, mul_assoc]
    calc Real.exp (-eps) * (min 1 (Real.exp (lam - 4 * eps)) * Real.exp ((n : ℝ) * (lam - 4 * eps)))
        ≤ Real.exp (-eps) * Real.exp ((n : ℝ) * (lam - 3 * eps) - eps) :=
          mul_le_mul_of_nonneg_left hb.2.1 (Real.exp_pos _).le
      _ = Real.exp (-eps + ((n : ℝ) * (lam - 3 * eps) - eps)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) := Real.exp_le_exp.2 (by linarith)
  -- Step B: `𝓛_{σ^{-(n+1)}ω} E_tilde^{(n+1)}` also grows fast under `T`
  have hWsplit1 := R.iterate_two_mul_shift (n + 1) ω
  have hTsucc := R.iterate_shift_succ n ω
  have hB1 : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * (n + 1) : ℕ) : ℝ))
      < growth ((R.iterate (n + 1) ω).comp (T.comp S)) V' := by
    rw [← hTsucc, ← hWsplit1]
    exact lt_trans (by gcongr) hnear1
  have hB2 := lt_growth_of_lt_comp (b := Real.exp ((lam + eps) * ((n : ℝ) + 1)))
    (Real.exp_pos _) (by push_cast at hfwd1 ⊢; exact hfwd1.le) hB1
  have hB3 := lt_growth_map_of_lt_comp (b := Real.exp (eps * ((n : ℝ) + 1)))
    (Real.exp_pos _) ((le_max_left _ _).trans htemp.le) hB2
  have hBval : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * (n + 1) : ℕ) : ℝ))
      / Real.exp ((lam + eps) * ((n : ℝ) + 1)) / Real.exp (eps * ((n : ℝ) + 1))
      = Real.exp (-eps + ((n : ℝ) + 1) * (lam - 4 * eps)) := by
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [hBval] at hB3
  have hΘB : Θ ≤ Real.exp (-eps + ((n : ℝ) + 1) * (lam - 4 * eps)) := by
    rw [hΘdef, hC0def, mul_assoc]
    calc Real.exp (-eps) * (min 1 (Real.exp (lam - 4 * eps)) * Real.exp ((n : ℝ) * (lam - 4 * eps)))
        ≤ Real.exp (-eps)
            * Real.exp (((n : ℝ) + 1) * (lam - 3 * eps) - eps - (n : ℝ) * eps) :=
          mul_le_mul_of_nonneg_left hb.2.2 (Real.exp_pos _).le
      _ = Real.exp (-eps + (((n : ℝ) + 1) * (lam - 3 * eps) - eps - (n : ℝ) * eps)) :=
          (Real.exp_add _ _).symm
      _ = Real.exp (-eps + ((n : ℝ) + 1) * (lam - 4 * eps)) := by congr 1; ring
  -- Step C: `S` is injective on `E_tilde^{(n+1)}`
  have hcomp_pos : 0 < growth (T.comp S) V' := lt_trans (by positivity) hB2
  have hSpos : 0 < growth S V' := by
    by_contra hcon
    rw [not_lt] at hcon
    have h0 : growth S V' = 0 := le_antisymm hcon (growth_nonneg _ _)
    have hle := growth_comp_le_mul_norm S T V'
    rw [h0, zero_mul] at hle
    linarith
  have hSV' : Θ < growth T (((GrassmannianFin.pushforward S (Etil (n + 1) ω) hSpos).1 :
      Submodule ℝ X)) := lt_of_le_of_lt hΘB hB3
  -- Step D: the gap factor is below `Θ/2`
  have hρhalf : bernsteinNumber T (m + 1) ≤ Θ / 2 := by
    refine le_trans hgapn.le ?_
    rw [hΘdef, hC0def]
    calc Real.exp (lam2 * n) = Real.exp ((n : ℝ) * lam2) := by rw [mul_comm]
      _ ≤ Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps))
            * Real.exp ((n : ℝ) * (lam - 4 * eps)) / 2 := hhn
  -- Step E: the contraction estimate
  have hmain := dist_pushforward_le_of_estimates m (T := T) (S := S) (V := Etil n ω)
    (V' := Etil (n + 1) ω) (Θ := Θ) hΘpos hρhalf hVgrow hSpos hSV'
  -- Step F: identify the two pushforwards with `E^{(n)}` and `E^{(n+1)}`
  have hEn : E n ω = GrassmannianFin.pushforward T (Etil n ω) (hΘpos.trans hVgrow) :=
    Subtype.ext hEeq
  have hEn1 : E (n + 1) ω = GrassmannianFin.pushforward (T.comp S) (Etil (n + 1) ω) hcomp_pos := by
    refine Subtype.ext ?_
    change ((E (n + 1) ω).1 : Submodule ℝ X)
        = Submodule.map ((T.comp S : X →L[ℝ] X) : X →ₗ[ℝ] X) V'
    rw [hEeq1, hTsucc]
  rw [hEn, hEn1]
  refine le_trans hmain ?_
  -- Step G: the bound is geometric in `n`
  have hgeom : bernsteinNumber T (m + 1) / Θ
      ≤ C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n := by
    rw [div_le_iff₀ hΘpos, hΘdef]
    have hstep : Real.exp (lam2 * n) ≤ C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n
        * (C0 * Real.exp ((n : ℝ) * (lam - 4 * eps))) := by
      rw [← Real.exp_nat_mul]
      have : C0⁻¹ * Real.exp ((n : ℝ) * -(lam - 4 * eps - lam2))
          * (C0 * Real.exp ((n : ℝ) * (lam - 4 * eps)))
          = Real.exp ((n : ℝ) * -(lam - 4 * eps - lam2)) *
              Real.exp ((n : ℝ) * (lam - 4 * eps)) := by
        field_simp
      rw [this, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by ring_nf; linarith)
    exact le_trans hgapn.le hstep
  calc 8 * (bernsteinNumber T (m + 1) / Θ)
      ≤ 8 * (C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n) := by
        exact mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = 8 * C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n := by ring

/-- **The approximating family `E^{(n)}` converges.** `proof_met.tex` l.735: the Cauchy estimate
plus completeness of `𝒢_{m}X` give a measurable limit `E`. Everything the later steps need about
the approximants — near-optimality and the pushforward identity — is carried along, so that
equivariance and fastness can be read off the same family. -/
theorem Cocycle.exists_limit_approx (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] (m : ℕ) [NeZero m] [Nonempty (GrassmannianFin X m)]
    {lam lam2 eps : ℝ} (heps : 0 < eps) (hgap : lam2 + 6 * eps < lam)
    (hchim : ∀ᵐ ω ∂(R.μ), R.chi m ω = (lam : EReal))
    (hchi1 : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = (lam : EReal))
    (hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω < (lam2 : EReal)) :
    ∃ (Etil E : ℕ → Ω → GrassmannianFin X m) (Elim : Ω → GrassmannianFin X m),
      (∀ n, Measurable (Etil n)) ∧ (∀ n, Measurable (E n)) ∧ Measurable Elim ∧
      (∀ n ω, bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 →
        (Real.exp (-eps) * bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m
            < growth (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) ((Etil n ω).1 : Submodule ℝ X)) ∧
          ((E n ω).1 : Submodule ℝ X)
            = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
              ((Etil n ω).1 : Submodule ℝ X)) ∧
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n => E n ω) atTop (nhds (Elim ω))) := by
  obtain ⟨Etil, E, hEtilmeas, hEmeas, hspec⟩ := R.exists_approx_spaces m heps
  have hr0 : (0 : ℝ) ≤ Real.exp (-(lam - 4 * eps - lam2)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(lam - 4 * eps - lam2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hcauchy : ∀ᵐ ω ∂(R.μ), CauchySeq (fun n => E n ω) := by
    filter_upwards [R.ae_eventually_estimates m heps hchim hchi1 hchi2] with ω hω
    exact cauchySeq_of_eventually_dist_le_geom _ hr0 hr1
      (R.eventually_dist_approx_le m heps hgap Etil E ω (fun n => hspec n ω) hω)
  obtain ⟨Elim, hElimmeas, hElim⟩ := exists_measurable_limit_of_ae_cauchy E hEmeas hcauchy
  exact ⟨Etil, E, Elim, hEtilmeas, hEmeas, hElimmeas, fun n ω => hspec n ω, hElim⟩

/-- The eventual form of Mathlib's `dist_le_of_le_geometric_of_tendsto`: the tail bound survives
a threshold, which is all the topfast construction can supply. -/
theorem dist_le_geom_of_eventually {Y : Type*} [MetricSpace Y] {f : ℕ → Y} {g : Y} {C r : ℝ}
    (hr : r < 1)
    (h : ∀ᶠ n : ℕ in atTop, dist (f n) (f (n + 1)) ≤ C * r ^ n)
    (hlim : Tendsto f atTop (nhds g)) :
    ∀ᶠ n : ℕ in atTop, dist (f n) g ≤ C * r ^ n / (1 - r) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hshift : ∀ k : ℕ, dist (f (k + N)) (f (k + 1 + N)) ≤ C * r ^ N * r ^ k := by
    intro k
    have hk := hN (k + N) (Nat.le_add_left _ _)
    rw [show k + 1 + N = k + N + 1 from by omega]
    refine hk.trans_eq ?_
    rw [pow_add]; ring
  have hlim' : Tendsto (fun k : ℕ => f (k + N)) atTop (nhds g) :=
    hlim.comp (tendsto_add_atTop_nat N)
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
  refine (dist_le_of_le_geometric_of_tendsto (r := r) (C := C * r ^ N) hr hshift hlim' k).trans_eq
    ?_
  rw [pow_add]; ring

/-- **`proof_met.tex` l.712.** The pushed-forward approximant `E^{(n)}(ω)` grows fast under the
*forward* window `𝓛^{(n)}_ω`: the `2n`-window estimate is transferred to its second factor. -/
theorem Cocycle.eventually_growth_approx_ge (R : Cocycle Ω X) (m : ℕ)
    {lam lam2 eps : ℝ}
    (Etil E : ℕ → Ω → GrassmannianFin X m) (ω : Ω)
    (hnear : ∀ n : ℕ, bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 →
        (Real.exp (-eps) * bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m
            < growth (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) ((Etil n ω).1 : Submodule ℝ X)) ∧
        (((E n ω).1 : Submodule ℝ X)
            = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
              ((Etil n ω).1 : Submodule ℝ X)))
    (hest : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
          < bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ∧
      ‖R.iterate n ω‖ < Real.exp ((lam + eps) * n) ∧
      ‖R.iterate n (zIter R.σ (-(n : ℤ)) ω)‖ < Real.exp ((lam + eps) * n) ∧
      max ‖R.L (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)‖ 1 < Real.exp (eps * ((n : ℝ) + 1)) ∧
      bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (m + 1) < Real.exp (lam2 * n)) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-eps + (n : ℝ) * (lam - 3 * eps))
        < growth (R.iterate n ω) ((E n ω).1 : Submodule ℝ X) := by
  filter_upwards [hest] with n hn
  obtain ⟨hbal, -, hback, -, -⟩ := hn
  have hne : bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 :=
    ne_of_gt ((Real.exp_pos _).trans hbal)
  obtain ⟨hnearn, hEeq⟩ := hnear n hne
  have hWsplit := R.iterate_two_mul_shift n ω
  have hA1 : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
      < growth ((R.iterate n ω).comp (R.iterate n (zIter R.σ (-(n : ℤ)) ω)))
          ((Etil n ω).1 : Submodule ℝ X) := by
    rw [← hWsplit]
    exact lt_trans (by gcongr) hnearn
  have hA2 := lt_growth_map_of_lt_comp (b := Real.exp ((lam + eps) * n)) (Real.exp_pos _)
    hback.le hA1
  have hAval : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
      / Real.exp ((lam + eps) * n) = Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [hAval, ← hEeq] at hA2
  exact hA2

/-- A strictly slower exponential is eventually dominated, whatever the constants. -/
theorem eventually_mul_exp_le_exp {a b c D : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, D * Real.exp (a * n) ≤ Real.exp (c + b * n) := by
  have h1 : Tendsto (fun n : ℕ => (a - b) * (n : ℝ)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : a - b < 0)).2 tendsto_natCast_atTop_atTop
  have hbot : Tendsto (fun n : ℕ => (a - b) * (n : ℝ) - c) atTop atBot := by
    simpa [sub_eq_add_neg] using Filter.tendsto_atBot_add_const_right atTop (-c) h1
  have h : Tendsto (fun n : ℕ => D * Real.exp ((a - b) * (n : ℝ) - c)) atTop (nhds 0) := by
    have := (Real.tendsto_exp_atBot.comp hbot).const_mul D
    simpa using this
  filter_upwards [h.eventually_le_const (zero_lt_one' ℝ)] with n hn
  have hpos : (0 : ℝ) < Real.exp (c + b * n) := Real.exp_pos _
  have hkey : D * Real.exp ((a - b) * (n : ℝ) - c) * Real.exp (c + b * n)
      = D * Real.exp (a * n) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc D * Real.exp (a * n) =
      D * Real.exp ((a - b) * (n : ℝ) - c) * Real.exp (c + b * n) := hkey.symm
    _ ≤ 1 * Real.exp (c + b * n) := by gcongr
    _ = Real.exp (c + b * n) := one_mul _

/-- **`proof_met.tex` l.752--758: the limit inherits the fast growth.** A vector of `𝕊_{E(ω)}`
is within `D r^n` of `𝕊_{E^{(n)}(ω)}`, and `‖𝓛^{(n)}_ω‖ ≤ e^{n(λ₁+ε)}` turns that into an error
term `D e^{n(λ₂+5ε)}`, which the gap `λ₂ + 10ε < λ₁` makes negligible beside `e^{n(λ₁-3ε)}`.
The paper's factor `½` is kept. -/
theorem Cocycle.eventually_growth_limit_ge (R : Cocycle Ω X) (m : ℕ) [NeZero m]
    {lam lam2 eps D : ℝ} (heps : 0 < eps) (hgap : lam2 + 10 * eps < lam) (hD : 0 ≤ D)
    (E : ℕ → Ω → GrassmannianFin X m) (Elim : Ω → GrassmannianFin X m) (ω : Ω)
    (hgrow : ∀ᶠ n : ℕ in atTop, Real.exp (-eps + (n : ℝ) * (lam - 3 * eps))
        < growth (R.iterate n ω) ((E n ω).1 : Submodule ℝ X))
    (hnorm : ∀ᶠ n : ℕ in atTop, ‖R.iterate n ω‖ < Real.exp ((lam + eps) * n))
    (hdist : ∀ᶠ n : ℕ in atTop,
        dist (E n ω) (Elim ω) ≤ D * Real.exp (-(lam - 4 * eps - lam2)) ^ n) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) / 2
        < growth (R.iterate n ω) ((Elim ω).1 : Submodule ℝ X) := by
  have hdom := eventually_mul_exp_le_exp (a := lam2 + 5 * eps) (b := lam - 3 * eps)
    (c := -eps - Real.log 2) (D := D) (by linarith)
  filter_upwards [hgrow, hnorm, hdist, hdom] with n hg hn hd hdm
  set T : X →L[ℝ] X := R.iterate n ω with hTdef
  set δ : ℝ := D * Real.exp (-(lam - 4 * eps - lam2)) ^ n with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hlip := growth_le_growth_add_of_dist_le m T (Elim ω) (E n ω)
    (δ := δ) (by rw [dist_comm]; exact hd)
  -- the error term is at most half the main term
  have herr : ‖T‖ * δ ≤ Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) / 2 := by
    have h1 : ‖T‖ * δ ≤ Real.exp ((lam + eps) * n) * δ :=
      mul_le_mul_of_nonneg_right hn.le hδ0
    have h2 : Real.exp ((lam + eps) * n) * δ = D * Real.exp ((lam2 + 5 * eps) * (n : ℝ)) := by
      rw [hδdef, ← Real.exp_nat_mul]
      rw [show Real.exp ((lam + eps) * (n : ℝ)) * (D * Real.exp ((n : ℝ) * -(lam - 4 * eps - lam2)))
          = D * (Real.exp ((lam + eps) * (n : ℝ))
              * Real.exp ((n : ℝ) * -(lam - 4 * eps - lam2))) from by ring,
        ← Real.exp_add]
      congr 2
      ring
    have h3 : Real.exp (-eps - Real.log 2 + (lam - 3 * eps) * (n : ℝ))
        = Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) / 2 := by
      rw [show (-eps - Real.log 2 + (lam - 3 * eps) * (n : ℝ))
          = (-eps + (n : ℝ) * (lam - 3 * eps)) + (-Real.log 2) from by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log two_pos]
      ring
    calc ‖T‖ * δ ≤ Real.exp ((lam + eps) * n) * δ := h1
      _ = D * Real.exp ((lam2 + 5 * eps) * (n : ℝ)) := h2
      _ ≤ Real.exp (-eps - Real.log 2 + (lam - 3 * eps) * (n : ℝ)) := hdm
      _ = Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) / 2 := h3
  linarith

omit [StandardBorelSpace Ω] in
/-- `σⁿ` undoes `σ^{-n}`: the forward iterate returns the base point of a backward window. -/
theorem zIter_forward_neg (σ : Ω ≃ᵐ Ω) (n : ℕ) (ω : Ω) :
    (σ : Ω → Ω)^[n] (zIter σ (-(n : ℤ)) ω) = ω := by
  rw [zIter_neg_natCast]
  exact (Function.LeftInverse.iterate (fun x => σ.toEquiv.apply_symm_apply x) n) ω

omit [StandardBorelSpace Ω] in
/-- The backward window of length `n+1` based at `σω` starts where the one of length `n` based
at `ω` starts. This is what lets the equivariance step compare `E_tilde^{(n+1)}(σω)` with
`E_tilde^{(n)}(ω)` under one and the same operator. -/
theorem zIter_neg_succ_apply (σ : Ω ≃ᵐ Ω) (n : ℕ) (ω : Ω) :
    zIter σ (-((n + 1 : ℕ) : ℤ)) (σ ω) = zIter σ (-(n : ℤ)) ω := by
  rw [zIter_neg_natCast, zIter_neg_natCast, Function.iterate_succ_apply]
  congr 1
  exact σ.toEquiv.symm_apply_apply ω

omit [MeasurableSpace X] in
/-- Distance to a subspace does not increase by more than `‖T‖` under `T`. -/
theorem infDist_map_le (T : X →L[ℝ] X) (V : Submodule ℝ X) (x : X) :
    Metric.infDist (T x) ((V.map (T : X →ₗ[ℝ] X) : Submodule ℝ X) : Set X)
      ≤ ‖T‖ * Metric.infDist x (V : Set X) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hVne : (V : Set X).Nonempty := ⟨0, V.zero_mem⟩
  have hηpos : (0 : ℝ) < ε / (‖T‖ + 1) := by positivity
  obtain ⟨y, hyV, hy⟩ := (Metric.infDist_lt_iff hVne).1
    (lt_add_of_pos_right (Metric.infDist x (V : Set X)) hηpos)
  have hmem : T y ∈ (V.map (T : X →ₗ[ℝ] X) : Submodule ℝ X) := Submodule.mem_map_of_mem hyV
  have h1 : Metric.infDist (T x) ((V.map (T : X →ₗ[ℝ] X) : Submodule ℝ X) : Set X)
      ≤ dist (T x) (T y) := Metric.infDist_le_dist_of_mem hmem
  have h2 : dist (T x) (T y) ≤ ‖T‖ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact T.le_opNorm _
  have h3 : ‖T‖ * (ε / (‖T‖ + 1)) ≤ ε := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg T, hε.le]
  calc Metric.infDist (T x) ((V.map (T : X →ₗ[ℝ] X) : Submodule ℝ X) : Set X)
      ≤ ‖T‖ * dist x y := h1.trans h2
    _ ≤ ‖T‖ * (Metric.infDist x (V : Set X) + ε / (‖T‖ + 1)) := by
        exact mul_le_mul_of_nonneg_left hy.le (norm_nonneg T)
    _ = ‖T‖ * Metric.infDist x (V : Set X) + ‖T‖ * (ε / (‖T‖ + 1)) := by ring
    _ ≤ ‖T‖ * Metric.infDist x (V : Set X) + ε := by linarith

/-- **`proof_met.tex` l.710.** The selected space `E_tilde^{(n)}(ω)` grows fast under the *backward*
window `𝓛^{(n)}_{σ^{-n}ω}`. This is the first half of the Cauchy step, isolated because the
equivariance step needs it at `σω` as well. -/
theorem Cocycle.eventually_growth_etil_ge (R : Cocycle Ω X) (m : ℕ)
    {lam lam2 eps : ℝ}
    (Etil E : ℕ → Ω → GrassmannianFin X m) (ω : Ω)
    (hnear : ∀ n : ℕ, bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 →
        (Real.exp (-eps) * bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m
            < growth (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) ((Etil n ω).1 : Submodule ℝ X)) ∧
        (((E n ω).1 : Submodule ℝ X)
            = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
              ((Etil n ω).1 : Submodule ℝ X)))
    (hest : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
          < bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ∧
      ‖R.iterate n ω‖ < Real.exp ((lam + eps) * n) ∧
      ‖R.iterate n (zIter R.σ (-(n : ℤ)) ω)‖ < Real.exp ((lam + eps) * n) ∧
      max ‖R.L (zIter R.σ (-((n + 1 : ℕ) : ℤ)) ω)‖ 1 < Real.exp (eps * ((n : ℝ) + 1)) ∧
      bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (m + 1) < Real.exp (lam2 * n)) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-eps + (n : ℝ) * (lam - 3 * eps))
        < growth (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) ((Etil n ω).1 : Submodule ℝ X) := by
  filter_upwards [hest] with n hn
  obtain ⟨hbal, hfwd, -, -, -⟩ := hn
  have hne : bernsteinNumber (R.iterate (2 * n) (zIter R.σ (-(n : ℤ)) ω)) m ≠ 0 :=
    ne_of_gt ((Real.exp_pos _).trans hbal)
  obtain ⟨hnearn, -⟩ := hnear n hne
  have hWsplit := R.iterate_two_mul_shift n ω
  have hA1 : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
      < growth ((R.iterate n ω).comp (R.iterate n (zIter R.σ (-(n : ℤ)) ω)))
          ((Etil n ω).1 : Submodule ℝ X) := by
    rw [← hWsplit]
    exact lt_trans (by gcongr) hnearn
  have hA2 := lt_growth_of_lt_comp (b := Real.exp ((lam + eps) * n)) (Real.exp_pos _)
    hfwd.le hA1
  have hAval : Real.exp (-eps) * Real.exp ((lam - eps) * ((2 * n : ℕ) : ℝ))
      / Real.exp ((lam + eps) * n) = Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rwa [hAval] at hA2

/-- **`proof_met.tex` l.740--748: the equivariance estimate.**

`E_tilde^{(n+1)}(σω)` is based at `σ^{-(n+1)}(σω) = σ^{-n}ω`, the same point as
`E_tilde^{(n)}(ω)`, so both
can be pushed forward by *one* operator `T = 𝓛^{(n)}_{σ^{-n}ω}` and compared by `pushclose`.
The paper instead compares `E^{(n+1)}(σω)` with `𝓛_ω E^{(n)}(ω)` and appeals to a Lipschitz
property of `V ↦ 𝓛_ω V` that it never states; taking the comparison one step earlier removes
the need for it, since `𝓛_ω` is then applied to both sides at once.

The resulting family `G` satisfies `𝓛_ω G^{(n)} = E^{(n+1)}(σω)` by construction. -/
theorem Cocycle.exists_shift_family (R : Cocycle Ω X) (m : ℕ) [NeZero m]
    {lam lam2 eps : ℝ} (heps : 0 < eps) (hgap : lam2 + 6 * eps < lam)
    (Etil E : ℕ → Ω → GrassmannianFin X m) (ω : Ω)
    (hpush : ∀ᶠ n : ℕ in atTop, ((E n ω).1 : Submodule ℝ X)
        = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
          ((Etil n ω).1 : Submodule ℝ X))
    (hgrowω : ∀ᶠ n : ℕ in atTop, Real.exp (-eps + (n : ℝ) * (lam - 3 * eps))
        < growth (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) ((Etil n ω).1 : Submodule ℝ X))
    (hgrowσ : ∀ᶠ n : ℕ in atTop, Real.exp (-eps + (n : ℝ) * (lam - 3 * eps))
        < growth (R.iterate n (zIter R.σ (-(n : ℤ)) (R.σ ω))) ((Etil n (R.σ ω)).1 : Submodule ℝ X))
    (hgapn : ∀ᶠ n : ℕ in atTop,
        bernsteinNumber (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (m + 1) < Real.exp (lam2 * n)) :
    ∃ G : ℕ → GrassmannianFin X m, ∀ᶠ n : ℕ in atTop,
      ((G n).1 : Submodule ℝ X)
          = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
            ((Etil (n + 1) (R.σ ω)).1 : Submodule ℝ X)
      ∧ dist (E n ω) (G n)
          ≤ 8 * (Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps)))⁻¹
              * Real.exp (-(lam - 4 * eps - lam2)) ^ n := by
  classical
  set C0 : ℝ := Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps)) with hC0def
  have hC0pos : (0 : ℝ) < C0 :=
    mul_pos (Real.exp_pos _) (lt_min one_pos (Real.exp_pos _))
  refine ⟨fun n => if h : 0 < growth (R.iterate n (zIter R.σ (-(n : ℤ)) ω))
      ((Etil (n + 1) (R.σ ω)).1 : Submodule ℝ X) then
      GrassmannianFin.pushforward (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) (Etil (n + 1) (R.σ ω)) h
    else E n ω, ?_⟩
  have hgrowσ1 := (tendsto_add_atTop_nat 1).eventually hgrowσ
  have hhalf := eventually_exp_le_half (lam := lam) (lam2 := lam2) (eps := eps) (C0 := C0)
    hC0pos heps hgap
  have hLω : ∀ᶠ n : ℕ in atTop, ‖R.L ω‖ ≤ Real.exp (eps * n) := by
    have := eventually_mul_exp_le_exp (a := 0) (b := eps) (c := 0) (D := ‖R.L ω‖) heps
    simpa using this
  filter_upwards [hgrowω, hgrowσ1, hgapn, hhalf, hLω, hpush, eventually_ge_atTop 1]
    with n hgω hgσ hgap' hhn hLn hEeq hn0
  set T : X →L[ℝ] X := R.iterate n (zIter R.σ (-(n : ℤ)) ω) with hTdef
  set Θ : ℝ := C0 * Real.exp ((n : ℝ) * (lam - 4 * eps)) with hΘdef
  have hΘpos : 0 < Θ := by rw [hΘdef]; positivity
  have hb := theta_le_bounds lam eps heps hn0
  -- `E_tilde^{(n)}(ω)` is `Θ`-fast under `T`
  have hVgrow : Θ < growth T ((Etil n ω).1 : Submodule ℝ X) := by
    refine lt_of_le_of_lt ?_ hgω
    rw [hΘdef, hC0def, mul_assoc]
    calc Real.exp (-eps) * (min 1 (Real.exp (lam - 4 * eps)) * Real.exp ((n : ℝ) * (lam - 4 * eps)))
        ≤ Real.exp (-eps) * Real.exp ((n : ℝ) * (lam - 3 * eps) - eps) :=
          mul_le_mul_of_nonneg_left hb.2.1 (Real.exp_pos _).le
      _ = Real.exp (-eps + ((n : ℝ) * (lam - 3 * eps) - eps)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) := Real.exp_le_exp.2 (by linarith)
  -- `E_tilde^{(n+1)}(σω)` lives over the same base point, and is `Θ`-fast under `T` too
  have hbase : R.iterate (n + 1) (zIter R.σ (-((n + 1 : ℕ) : ℤ)) (R.σ ω)) = (R.L ω).comp T := by
    rw [zIter_neg_succ_apply]
    rw [show n + 1 = 1 + n from by omega, R.iterate_add 1 n (zIter R.σ (-(n : ℤ)) ω),
      R.iterate_one]
    rw [zIter_forward_neg]
  rw [hbase] at hgσ
  push_cast at hgσ
  have hWgrow0 := lt_growth_of_lt_comp (b := Real.exp (eps * n)) (Real.exp_pos _) hLn hgσ
  have hWval : Real.exp (-eps + ((n : ℕ) + 1 : ℝ) * (lam - 3 * eps)) / Real.exp (eps * n)
      = Real.exp (-eps + (((n : ℝ) + 1) * (lam - 3 * eps) - (n : ℝ) * eps)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hWgrow : Θ < growth T ((Etil (n + 1) (R.σ ω)).1 : Submodule ℝ X) := by
    refine lt_of_le_of_lt ?_ (by rw [hWval] at hWgrow0; exact hWgrow0)
    rw [hΘdef, hC0def, mul_assoc]
    calc Real.exp (-eps) * (min 1 (Real.exp (lam - 4 * eps)) * Real.exp ((n : ℝ) * (lam - 4 * eps)))
        ≤ Real.exp (-eps)
            * Real.exp (((n : ℝ) + 1) * (lam - 3 * eps) - eps - (n : ℝ) * eps) :=
          mul_le_mul_of_nonneg_left hb.2.2 (Real.exp_pos _).le
      _ = Real.exp (-eps + (((n : ℝ) + 1) * (lam - 3 * eps) - eps - (n : ℝ) * eps)) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp (-eps + (((n : ℝ) + 1) * (lam - 3 * eps) - (n : ℝ) * eps)) :=
          Real.exp_le_exp.2 (by linarith)
  have hWpos : 0 < growth T ((Etil (n + 1) (R.σ ω)).1 : Submodule ℝ X) := hΘpos.trans hWgrow
  -- the gap factor
  have hρhalf : bernsteinNumber T (m + 1) ≤ Θ / 2 := by
    refine le_trans hgap'.le ?_
    rw [hΘdef, hC0def]
    calc Real.exp (lam2 * n) = Real.exp ((n : ℝ) * lam2) := by rw [mul_comm]
      _ ≤ Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps))
            * Real.exp ((n : ℝ) * (lam - 4 * eps)) / 2 := hhn
  have hmain := pushclose_geom m T Θ hΘpos hρhalf (Etil n ω) (Etil (n + 1) (R.σ ω))
    hVgrow hWgrow
  have hEn : E n ω = GrassmannianFin.pushforward T (Etil n ω)
      (lt_of_le_of_lt (bernsteinNumber_nonneg T (m + 1))
        ((lt_of_le_of_lt hρhalf (by linarith)).trans hVgrow)) := Subtype.ext hEeq
  refine ⟨?_, ?_⟩
  · rw [dite_eq_left hWpos]
    rfl
  · rw [dite_eq_left hWpos, hEn]
    refine le_trans hmain ?_
    have hgeom : bernsteinNumber T (m + 1) / Θ
        ≤ C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n := by
      rw [div_le_iff₀ hΘpos, hΘdef]
      have hstep : Real.exp (lam2 * n) ≤ C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n
          * (C0 * Real.exp ((n : ℝ) * (lam - 4 * eps))) := by
        rw [← Real.exp_nat_mul]
        have : C0⁻¹ * Real.exp ((n : ℝ) * -(lam - 4 * eps - lam2))
            * (C0 * Real.exp ((n : ℝ) * (lam - 4 * eps)))
            = Real.exp ((n : ℝ) * -(lam - 4 * eps - lam2))
              * Real.exp ((n : ℝ) * (lam - 4 * eps)) := by
          field_simp
        rw [this, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by ring_nf; linarith)
      exact le_trans hgap'.le hstep
    calc 8 * (bernsteinNumber T (m + 1) / Θ)
        ≤ 8 * (C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n) :=
          mul_le_mul_of_nonneg_left hgeom (by norm_num)
      _ = 8 * C0⁻¹ * Real.exp (-(lam - 4 * eps - lam2)) ^ n := by ring

omit [MeasurableSpace X] in
/-- **Passing `T` to the limit.** If `G n → V`, `F n → W` and `F n = T G n` for all large `n`,
and `T` is injective on `V`, then `T V = W`.

This is the step `proof_met.tex` l.748 takes as read (`𝓛_ω E(ω) = lim 𝓛_ω E^{(n)}(ω)`), which
needs `V ↦ TV` to be continuous on `𝒢_mX` — a fact the paper never states and which is false
without a positive growth hypothesis. It is avoided here: distances to *subspaces* are
`2‖x‖`-Lipschitz in the subspace (`infDist_subspace_le`) and do not increase by more than `‖T‖`
under `T` (`infDist_map_le`), which places `Tx` in the closed subspace `W` for every `x ∈ V`;
equality then comes from both sides having dimension `m`. -/
theorem map_eq_of_dist_tendsto {m : ℕ} [NeZero m] (T : X →L[ℝ] X)
    (G F : ℕ → GrassmannianFin X m) (V W : GrassmannianFin X m)
    (hGV : Tendsto (fun n => dist V (G n)) atTop (nhds 0))
    (hFW : Tendsto (fun n => dist (F n) W) atTop (nhds 0))
    (hmap : ∀ᶠ n : ℕ in atTop, ((F n).1 : Submodule ℝ X)
        = Submodule.map (T : X →ₗ[ℝ] X) ((G n).1 : Submodule ℝ X))
    (hTpos : 0 < growth T (V.1 : Submodule ℝ X)) :
    Submodule.map (T : X →ₗ[ℝ] X) (V.1 : Submodule ℝ X) = (W.1 : Submodule ℝ X) := by
  have hWclosed : IsClosed (((W.1 : Submodule ℝ X)) : Set X) := by
    have : FiniteDimensional ℝ (W.1 : Submodule ℝ X) := W.2.1
    exact Submodule.closed_of_finiteDimensional _
  -- every `Tx` with `x ∈ V` lies in `W`
  have hsub : Submodule.map (T : X →ₗ[ℝ] X) (V.1 : Submodule ℝ X) ≤ (W.1 : Submodule ℝ X) := by
    rintro _ ⟨x, hxV, rfl⟩
    have hxzero : Metric.infDist x ((V.1 : Submodule ℝ X) : Set X) = 0 := by
      refine le_antisymm ?_ Metric.infDist_nonneg
      simpa using Metric.infDist_le_dist_of_mem (x := x) hxV
    have hbound : ∀ᶠ n : ℕ in atTop,
        Metric.infDist (T x) (((W.1 : Submodule ℝ X)) : Set X)
          ≤ ‖T‖ * (2 * ‖x‖ * dist V (G n)) + 2 * ‖T x‖ * dist (F n) W := by
      filter_upwards [hmap] with n hn
      have h1 := infDist_subspace_le m (T x) (F n) W
      have h2 : Metric.infDist (T x) (((F n).1 : Submodule ℝ X) : Set X)
          ≤ ‖T‖ * Metric.infDist x (((G n).1 : Submodule ℝ X) : Set X) := by
        rw [hn]
        exact infDist_map_le T ((G n).1 : Submodule ℝ X) x
      have h3 := infDist_subspace_le m x V (G n)
      rw [hxzero, zero_add] at h3
      have h4 : ‖T‖ * Metric.infDist x (((G n).1 : Submodule ℝ X) : Set X)
          ≤ ‖T‖ * (2 * ‖x‖ * dist V (G n)) := mul_le_mul_of_nonneg_left h3 (norm_nonneg T)
      linarith
    have hlim : Tendsto (fun n : ℕ =>
        ‖T‖ * (2 * ‖x‖ * dist V (G n)) + 2 * ‖T x‖ * dist (F n) W) atTop (nhds 0) := by
      have hA : Tendsto (fun n : ℕ => ‖T‖ * (2 * ‖x‖ * dist V (G n))) atTop (nhds 0) := by
        simpa using ((hGV.const_mul (2 * ‖x‖)).const_mul ‖T‖)
      have hB : Tendsto (fun n : ℕ => 2 * ‖T x‖ * dist (F n) W) atTop (nhds 0) := by
        simpa using hFW.const_mul (2 * ‖T x‖)
      simpa using hA.add hB
    have hzero : Metric.infDist (T x) (((W.1 : Submodule ℝ X)) : Set X) ≤ 0 :=
      ge_of_tendsto hlim hbound
    have hmem : T x ∈ closure (((W.1 : Submodule ℝ X)) : Set X) := by
      rw [Metric.mem_closure_iff_infDist_zero ⟨0, (W.1 : Submodule ℝ X).zero_mem⟩]
      exact le_antisymm hzero Metric.infDist_nonneg
    rwa [hWclosed.closure_eq] at hmem
  -- and the dimensions agree
  have : FiniteDimensional ℝ (W.1 : Submodule ℝ X) := W.2.1
  refine Submodule.eq_of_le_of_finrank_eq hsub ?_
  have := (GrassmannianFin.pushforward T V hTpos).2.2
  rw [W.2.2]
  exact this

/-- **The top fast space, at one fixed `ε`.** `proof_met.tex` l.680--760 with the exponents
`λ₁ = lam` and a real `lam2` strictly above `χ_{m+1}`, separated by `10ε`.

This is the whole geometric content of `lem:topfast`: a measurable, forward-equivariant family
of `m`-dimensional subspaces growing at least like `½e^{-ε}e^{n(λ₁-3ε)}`. Pinning the growth rate
to `λ₁` exactly is a separate `ε → 0` step, which goes through uniqueness. -/
theorem Cocycle.exists_fastSpace_of_gap (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] (m : ℕ) [NeZero m] [Nonempty (GrassmannianFin X m)]
    {lam lam2 eps : ℝ} (heps : 0 < eps) (hgap : lam2 + 10 * eps < lam)
    (hchim : ∀ᵐ ω ∂(R.μ), R.chi m ω = (lam : EReal))
    (hchi1 : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = (lam : EReal))
    (hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω < (lam2 : EReal)) :
    ∃ E : Ω → GrassmannianFin X m, Measurable E ∧
      (∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
          = ((E (R.σ ω)).1 : Submodule ℝ X)) ∧
      (∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, Real.exp (-eps + (n : ℝ) * (lam - 3 * eps)) / 2
          < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) := by
  have hgap6 : lam2 + 6 * eps < lam := by linarith
  obtain ⟨Etil, E, Elim, hEtilm, hEm, hElimm, hspec, hlim⟩ :=
    R.exists_limit_approx m heps hgap6 hchim hchi1 hchi2
  set C0 : ℝ := Real.exp (-eps) * min 1 (Real.exp (lam - 4 * eps)) with hC0def
  have hC0pos : (0 : ℝ) < C0 := mul_pos (Real.exp_pos _) (lt_min one_pos (Real.exp_pos _))
  set r : ℝ := Real.exp (-(lam - 4 * eps - lam2)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hrdef, Real.exp_lt_one_iff]; linarith
  have hD : (0 : ℝ) ≤ 8 * C0⁻¹ / (1 - r) := by
    have : (0 : ℝ) < 1 - r := by linarith
    positivity
  refine ⟨Elim, hElimm, ?_, ?_⟩
  · -- equivariance
    have hestσ := R.ergodic.toMeasurePreserving.quasiMeasurePreserving.ae
      (R.ae_eventually_estimates m heps hchim hchi1 hchi2)
    have hlimσ := R.ergodic.toMeasurePreserving.quasiMeasurePreserving.ae hlim
    filter_upwards [R.ae_eventually_estimates m heps hchim hchi1 hchi2, hestσ, hlim, hlimσ]
      with ω hest hestσω hlimω hlimσω
    -- the pushforward identity, as an eventual fact
    have hpush : ∀ᶠ n : ℕ in atTop, ((E n ω).1 : Submodule ℝ X)
        = Submodule.map ((R.iterate n (zIter R.σ (-(n : ℤ)) ω) : X →ₗ[ℝ] X))
          ((Etil n ω).1 : Submodule ℝ X) := by
      filter_upwards [hest] with n hn
      exact (hspec n ω (ne_of_gt ((Real.exp_pos _).trans hn.1))).2
    have hpushσ : ∀ᶠ n : ℕ in atTop, ((E (n + 1) (R.σ ω)).1 : Submodule ℝ X)
        = Submodule.map ((R.iterate (n + 1) (zIter R.σ (-((n + 1 : ℕ) : ℤ)) (R.σ ω))
            : X →ₗ[ℝ] X)) ((Etil (n + 1) (R.σ ω)).1 : Submodule ℝ X) := by
      filter_upwards [(tendsto_add_atTop_nat 1).eventually hestσω] with n hn
      exact (hspec (n + 1) (R.σ ω) (ne_of_gt ((Real.exp_pos _).trans hn.1))).2
    obtain ⟨G, hG⟩ := R.exists_shift_family m heps hgap6 Etil E ω hpush
      (R.eventually_growth_etil_ge m Etil E ω (fun n => hspec n ω) hest)
      (R.eventually_growth_etil_ge m Etil E (R.σ ω) (fun n => hspec n (R.σ ω)) hestσω)
      (by filter_upwards [hest] with n hn using hn.2.2.2.2)
    -- `E^{(n)}(ω) → E(ω)` and `d(E^{(n)}(ω), G^{(n)}) → 0`, so `G^{(n)} → E(ω)`
    have hdEn : Tendsto (fun n : ℕ => dist (E n ω) (Elim ω)) atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.1 hlimω
    have hgeom : Tendsto (fun n : ℕ => 8 * C0⁻¹ * r ^ n) atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (8 * C0⁻¹)
      simpa using this
    have hdG : Tendsto (fun n : ℕ => dist (Elim ω) (G n)) atTop (nhds 0) := by
      refine squeeze_zero (fun n => dist_nonneg)
        (fun n => dist_triangle (Elim ω) (E n ω) (G n)) ?_
      have hbound : ∀ᶠ n : ℕ in atTop,
          dist (Elim ω) (E n ω) + dist (E n ω) (G n)
            ≤ dist (E n ω) (Elim ω) + 8 * C0⁻¹ * r ^ n := by
        filter_upwards [hG] with n hn
        rw [dist_comm (Elim ω) (E n ω)]
        linarith [hn.2]
      have hsum : Tendsto (fun n : ℕ => dist (E n ω) (Elim ω) + 8 * C0⁻¹ * r ^ n)
          atTop (nhds 0) := by
        simpa using hdEn.add hgeom
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall fun n => by positivity) hbound
    have hdF : Tendsto (fun n : ℕ => dist (E (n + 1) (R.σ ω)) (Elim (R.σ ω))) atTop (nhds 0) :=
      (tendsto_iff_dist_tendsto_zero.1 hlimσω).comp (tendsto_add_atTop_nat 1)
    -- the images match
    have hmapF : ∀ᶠ n : ℕ in atTop, ((E (n + 1) (R.σ ω)).1 : Submodule ℝ X)
        = Submodule.map ((R.L ω : X →ₗ[ℝ] X)) ((G n).1 : Submodule ℝ X) := by
      filter_upwards [hG, hpushσ] with n hn hpn
      have hbase : R.iterate (n + 1) (zIter R.σ (-((n + 1 : ℕ) : ℤ)) (R.σ ω))
          = (R.L ω).comp (R.iterate n (zIter R.σ (-(n : ℤ)) ω)) := by
        rw [zIter_neg_succ_apply, show n + 1 = 1 + n from by omega,
          R.iterate_add 1 n (zIter R.σ (-(n : ℤ)) ω), R.iterate_one, zIter_forward_neg]
      rw [hpn, hbase, hn.1, ← Submodule.map_comp]
      rfl
    -- `𝓛_ω` is injective on `E(ω)`
    have hfast := R.eventually_growth_limit_ge m heps hgap hD E Elim ω
      (R.eventually_growth_approx_ge m Etil E ω (fun n => hspec n ω) hest)
      (by filter_upwards [hest] with n hn using hn.2.1)
      (by
        filter_upwards [dist_le_geom_of_eventually hr1
          (R.eventually_dist_approx_le m heps hgap6 Etil E ω (fun n => hspec n ω) hest) hlimω]
          with n hn
        calc dist (E n ω) (Elim ω) ≤ 8 * C0⁻¹ * r ^ n / (1 - r) := hn
          _ = 8 * C0⁻¹ / (1 - r) * r ^ n := by ring)
    obtain ⟨N, hN⟩ := (hfast.and (eventually_ge_atTop 1)).exists
    have hTpos : 0 < growth (R.L ω) ((Elim ω).1 : Submodule ℝ X) := by
      have hpos : 0 < growth (R.iterate N ω) ((Elim ω).1 : Submodule ℝ X) :=
        lt_trans (by positivity) hN.1
      obtain ⟨p, rfl⟩ : ∃ p, N = p + 1 := ⟨N - 1, by omega⟩
      rw [R.iterate_succ_left p ω] at hpos
      by_contra hcon
      rw [not_lt] at hcon
      have h0 : growth (R.L ω) ((Elim ω).1 : Submodule ℝ X) = 0 :=
        le_antisymm hcon (growth_nonneg _ _)
      have hle := growth_comp_le_mul_norm (R.L ω) (R.iterate p (R.σ ω))
        ((Elim ω).1 : Submodule ℝ X)
      rw [h0, zero_mul] at hle
      linarith
    exact map_eq_of_dist_tendsto (R.L ω) G (fun n => E (n + 1) (R.σ ω)) (Elim ω) (Elim (R.σ ω))
      hdG hdF hmapF hTpos
  · -- fastness
    filter_upwards [R.ae_eventually_estimates m heps hchim hchi1 hchi2, hlim] with ω hest hlimω
    exact R.eventually_growth_limit_ge m heps hgap hD E Elim ω
      (R.eventually_growth_approx_ge m Etil E ω (fun n => hspec n ω) hest)
      (by filter_upwards [hest] with n hn using hn.2.1)
      (by
        filter_upwards [dist_le_geom_of_eventually hr1
          (R.eventually_dist_approx_le m heps hgap6 Etil E ω (fun n => hspec n ω) hest) hlimω]
          with n hn
        calc dist (E n ω) (Elim ω) ≤ 8 * C0⁻¹ * r ^ n / (1 - r) := hn
          _ = 8 * C0⁻¹ / (1 - r) * r ^ n := by ring)

/-- Equivariance one step at a time gives equivariance along the whole orbit. -/
theorem Cocycle.map_iterate_of_equivariant (R : Cocycle Ω X) {m : ℕ}
    (E : Ω → GrassmannianFin X m) (ω : Ω)
    (h : ∀ k : ℕ, Submodule.map (R.L (R.σ^[k] ω) : X →ₗ[ℝ] X)
        ((E (R.σ^[k] ω)).1 : Submodule ℝ X) = ((E (R.σ^[k + 1] ω)).1 : Submodule ℝ X))
    (n : ℕ) :
    Submodule.map (R.iterate n ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
      = ((E (R.σ^[n] ω)).1 : Submodule ℝ X) := by
  induction n with
  | zero => simp [Cocycle.iterate]
  | succ n ih =>
      have hstep : R.iterate (n + 1) ω = (R.L (R.σ^[n] ω)).comp (R.iterate n ω) := rfl
      rw [hstep]
      rw [show ((((R.L (R.σ^[n] ω)).comp (R.iterate n ω)) : X →L[ℝ] X) : X →ₗ[ℝ] X)
          = ((R.L (R.σ^[n] ω) : X →ₗ[ℝ] X).comp (R.iterate n ω : X →ₗ[ℝ] X)) from rfl,
        Submodule.map_comp, ih]
      exact h n

/-- The a.e. equivariance identity holds simultaneously at every point of the orbit. -/
theorem Cocycle.ae_all_shift_equivariant (R : Cocycle Ω X) {m : ℕ}
    (E : Ω → GrassmannianFin X m)
    (h : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
        = ((E (R.σ ω)).1 : Submodule ℝ X)) :
    ∀ᵐ ω ∂(R.μ), ∀ k : ℕ, Submodule.map (R.L (R.σ^[k] ω) : X →ₗ[ℝ] X)
        ((E (R.σ^[k] ω)).1 : Submodule ℝ X) = ((E (R.σ^[k + 1] ω)).1 : Submodule ℝ X) := by
  rw [ae_all_iff]
  intro k
  have := ((R.ergodic.toMeasurePreserving.iterate k).quasiMeasurePreserving).ae h
  filter_upwards [this] with ω hω
  simpa [Function.iterate_succ_apply'] using hω

/-- **`proof_met.tex` l.762--772: uniqueness of the fast space.** Two equivariant families, each
eventually growing faster than `e^{an}` with `a` above `χ_{m+1}`, are pushed together by
`pushclose` along every orbit, so `ω ↦ d(E ω, E' ω)` tends to `0` along all orbits. Measure
preservation then makes its distribution constant in `n`, and a.e. convergence on a probability
space is convergence in measure, so that distribution is concentrated at `0`. -/
theorem Cocycle.ae_eq_of_fast (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (m : ℕ) [NeZero m] {a b : ℝ} (hab : b < a)
    (hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω < (b : EReal))
    (E E' : Ω → GrassmannianFin X m) (hEm : Measurable E) (hE'm : Measurable E')
    (hEeq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
        = ((E (R.σ ω)).1 : Submodule ℝ X))
    (hE'eq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E' ω).1 : Submodule ℝ X)
        = ((E' (R.σ ω)).1 : Submodule ℝ X))
    (hEfast : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        Real.exp (a * n) < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X))
    (hE'fast : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        Real.exp (a * n) < growth (R.iterate n ω) ((E' ω).1 : Submodule ℝ X)) :
    ∀ᵐ ω ∂(R.μ), E ω = E' ω := by
  -- the orbit-wise contraction
  have hgap : ∀ᶠ n : ℕ in atTop, Real.exp (b * n) ≤ Real.exp (a * n) / 2 := by
    have := eventually_mul_exp_le_exp (a := b) (b := a) (c := -Real.log 2) (D := 1) hab
    filter_upwards [this] with n hn
    have heq : Real.exp (-Real.log 2 + a * n) = Real.exp (a * n) / 2 := by
      rw [Real.exp_add, Real.exp_neg, Real.exp_log two_pos]
      ring
    rw [← heq]
    simpa using hn
  have hρ : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
      bernsteinNumber (R.iterate n ω) (m + 1) < Real.exp (b * n) := by
    filter_upwards [hchi2, R.ae_tendsto_chi (m + 1)] with ω h2 hc
    exact eventually_lt_exp_of_tendsto h2 hc
  have hzero : ∀ᵐ ω ∂(R.μ),
      Tendsto (fun n : ℕ => dist (E (R.σ^[n] ω)) (E' (R.σ^[n] ω))) atTop (nhds 0) := by
    filter_upwards [hEfast, hE'fast, hρ, R.ae_all_shift_equivariant E hEeq,
      R.ae_all_shift_equivariant E' hE'eq] with ω hf hf' hr hs hs'
    have hbound : ∀ᶠ n : ℕ in atTop,
        dist (E (R.σ^[n] ω)) (E' (R.σ^[n] ω))
          ≤ 8 * (bernsteinNumber (R.iterate n ω) (m + 1) / Real.exp (a * n)) := by
      filter_upwards [hf, hf', hr, hgap] with n hn hn' hrn hgn
      have hhalf : bernsteinNumber (R.iterate n ω) (m + 1) ≤ Real.exp (a * n) / 2 :=
        le_trans hrn.le hgn
      have hmain := pushclose_geom m (R.iterate n ω) (Real.exp (a * n)) (Real.exp_pos _)
        hhalf (E ω) (E' ω) hn hn'
      have h1 : E (R.σ^[n] ω) = GrassmannianFin.pushforward (R.iterate n ω) (E ω)
          (lt_of_le_of_lt (bernsteinNumber_nonneg (R.iterate n ω) (m + 1))
            ((lt_of_le_of_lt hhalf (by linarith [Real.exp_pos (a * n)])).trans hn)) :=
        Subtype.ext (R.map_iterate_of_equivariant E ω hs n).symm
      have h2 : E' (R.σ^[n] ω) = GrassmannianFin.pushforward (R.iterate n ω) (E' ω)
          (lt_of_le_of_lt (bernsteinNumber_nonneg (R.iterate n ω) (m + 1))
            ((lt_of_le_of_lt hhalf (by linarith [Real.exp_pos (a * n)])).trans hn')) :=
        Subtype.ext (R.map_iterate_of_equivariant E' ω hs' n).symm
      rw [h1, h2]
      exact hmain
    have hlim : Tendsto (fun n : ℕ =>
        8 * (bernsteinNumber (R.iterate n ω) (m + 1) / Real.exp (a * n))) atTop (nhds 0) := by
      have hsq : ∀ᶠ n : ℕ in atTop,
          8 * (bernsteinNumber (R.iterate n ω) (m + 1) / Real.exp (a * n))
            ≤ 8 * Real.exp ((b - a) * n) := by
        filter_upwards [hr] with n hn
        have hpos : (0 : ℝ) < Real.exp (a * n) := Real.exp_pos _
        have : bernsteinNumber (R.iterate n ω) (m + 1) / Real.exp (a * n)
            ≤ Real.exp (b * n) / Real.exp (a * n) := by gcongr
        rw [← Real.exp_sub] at this
        have heq : b * (n : ℝ) - a * n = (b - a) * n := by ring
        rw [heq] at this
        linarith
      have htend : Tendsto (fun n : ℕ => 8 * Real.exp ((b - a) * (n : ℝ))) atTop (nhds 0) := by
        have hbot : Tendsto (fun n : ℕ => (b - a) * (n : ℝ)) atTop atBot :=
          (tendsto_const_mul_atBot_of_neg (by linarith : b - a < 0)).2 tendsto_natCast_atTop_atTop
        have := (Real.tendsto_exp_atBot.comp hbot).const_mul (8 : ℝ)
        simpa using this
      refine squeeze_zero' ?_ hsq htend
      filter_upwards [hr] with n hn
      have := bernsteinNumber_nonneg (R.iterate n ω) (m + 1)
      positivity
    exact squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) hbound hlim
  -- a.e. convergence along the orbit forces `d(Eω, E'ω) = 0`
  have := grassmannianFin_separable (X := X) m
  have : SecondCountableTopology (GrassmannianFin X m) :=
    UniformSpace.secondCountable_of_separable _
  have hφmeas : Measurable fun ω => dist (E ω) (E' ω) := hEm.dist hE'm
  have hnull : ∀ δ : ℝ, 0 < δ → R.μ {ω | δ ≤ dist (E ω) (E' ω)} = 0 := by
    intro δ hδ
    have hmeasn : ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => dist (E ((R.σ : Ω → Ω)^[n] ω)) (E' ((R.σ : Ω → Ω)^[n] ω))) R.μ :=
      fun n => (hφmeas.comp (R.σ.measurable.iterate n)).aestronglyMeasurable
    have htim := tendstoInMeasure_of_tendsto_ae hmeasn hzero
    have hconv := htim (ENNReal.ofReal δ) (by simpa using hδ)
    have hconst : ∀ n : ℕ,
        R.μ {ω | ENNReal.ofReal δ ≤
            edist (dist (E ((R.σ : Ω → Ω)^[n] ω)) (E' ((R.σ : Ω → Ω)^[n] ω))) (0 : ℝ)}
          = R.μ {ω | δ ≤ dist (E ω) (E' ω)} := by
      intro n
      have hset : {ω | ENNReal.ofReal δ ≤
            edist (dist (E ((R.σ : Ω → Ω)^[n] ω)) (E' ((R.σ : Ω → Ω)^[n] ω))) (0 : ℝ)}
          = ((R.σ : Ω → Ω)^[n]) ⁻¹' {ω | δ ≤ dist (E ω) (E' ω)} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, edist_dist, Real.dist_eq, sub_zero,
          abs_of_nonneg dist_nonneg, ENNReal.ofReal_le_ofReal_iff dist_nonneg]
      rw [hset]
      exact (R.ergodic.toMeasurePreserving.iterate n).measure_preimage
        (hφmeas measurableSet_Ici).nullMeasurableSet
    rw [funext hconst] at hconv
    exact tendsto_nhds_unique tendsto_const_nhds hconv
  have hcover : {ω | dist (E ω) (E' ω) ≠ 0}
      = ⋃ k : ℕ, {ω | (1 : ℝ) / (k + 1) ≤ dist (E ω) (E' ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      have hpos : 0 < dist (E ω) (E' ω) := lt_of_le_of_ne dist_nonneg (Ne.symm h)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      exact ⟨k, hk.le⟩
    · rintro ⟨k, hk⟩
      have hp : (0 : ℝ) < 1 / (k + 1) := by positivity
      exact ne_of_gt (lt_of_lt_of_le hp hk)
  have hae : R.μ {ω | dist (E ω) (E' ω) ≠ 0} = 0 := by
    rw [hcover]
    exact measure_iUnion_null fun k => hnull _ (by positivity)
  filter_upwards [hae] with ω hω
  exact dist_eq_zero.1 hω

omit [MeasurableSpace X] in
/-- `g_T(V) ≤ ρ_m(T)` for `V ∈ 𝒢_mX`: the Bernstein number is the supremum of the growths. -/
theorem growth_le_bernsteinNumber {m : ℕ} (T : X →L[ℝ] X) (V : GrassmannianFin X m) :
    growth T (V.1 : Submodule ℝ X) ≤ bernsteinNumber T m :=
  le_csSup ⟨‖T‖, by rintro _ ⟨U, rfl⟩; exact growth_le_opNorm T _⟩ ⟨V, rfl⟩

/-- **`proof_met.tex` l.758--760, the `ε → 0` step.** The construction of
`Cocycle.exists_fastSpace_of_gap` runs for every small `ε`, and uniqueness
(`Cocycle.ae_eq_of_fast`) identifies all of the resulting families with a single one. That one
family therefore carries the lower bound `e^{n(λ₁-3ε)}` for *every* `ε`, which together with the
upper bound `g ≤ ρ_{m}(𝓛^{(n)}_ω)` pins its growth rate to `λ₁` exactly. -/
theorem Cocycle.exists_fastSpace (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] (m : ℕ) [NeZero m] [Nonempty (GrassmannianFin X m)]
    {lam lam2 : ℝ} (hlt : lam2 < lam)
    (hchim : ∀ᵐ ω ∂(R.μ), R.chi m ω = (lam : EReal))
    (hchi1 : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = (lam : EReal))
    (hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω < (lam2 : EReal)) :
    ∃ E : Ω → GrassmannianFin X m, Measurable E ∧
      (∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
          = ((E (R.σ ω)).1 : Submodule ℝ X)) ∧
      (∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
          0 < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) ∧
      (∀ᵐ ω ∂(R.μ), Tendsto
        (fun n : ℕ => Real.log (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / n)
        atTop (nhds lam)) := by
  set eps : ℕ → ℝ := fun j => (lam - lam2) / (11 * (j + 1)) with hepsdef
  have hepspos : ∀ j, 0 < eps j := by
    intro j
    rw [hepsdef]
    have : (0 : ℝ) < 11 * ((j : ℝ) + 1) := by positivity
    exact div_pos (by linarith) this
  have hepsgap : ∀ j, lam2 + 10 * eps j < lam := by
    intro j
    have hd : (0 : ℝ) < 11 * ((j : ℝ) + 1) := by positivity
    have h1 : (1 : ℝ) ≤ 11 * ((j : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have : 10 * eps j < lam - lam2 := by
      rw [hepsdef]
      rw [show (10 : ℝ) * ((lam - lam2) / (11 * ((j : ℝ) + 1)))
          = (lam - lam2) * (10 / (11 * ((j : ℝ) + 1))) from by ring]
      have hfrac : 10 / (11 * ((j : ℝ) + 1)) < 1 := by
        rw [div_lt_one hd]; linarith
      nlinarith [hlt]
    linarith
  have hepstend : Tendsto eps atTop (nhds 0) := by
    have hj : Tendsto (fun j : ℕ => 11 * ((j : ℝ) + 1)) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 11) ?_
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hj
  choose E hEm hEeq hEfast using fun j : ℕ =>
    R.exists_fastSpace_of_gap m (hepspos j) (hepsgap j) hchim hchi1 hchi2
  -- each family is `e^{n(λ₁-4ε_j)}`-fast
  have hfast4 : ∀ j : ℕ, ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam - 4 * eps j) * n) < growth (R.iterate n ω) ((E j ω).1 : Submodule ℝ X) := by
    intro j
    filter_upwards [hEfast j] with ω hω
    have hdom := eventually_mul_exp_le_exp (a := lam - 4 * eps j) (b := lam - 3 * eps j)
      (c := -eps j - Real.log 2) (D := 1) (by linarith [hepspos j])
    filter_upwards [hω, hdom] with n hn hd
    refine lt_of_le_of_lt ?_ hn
    have heq : Real.exp (-eps j + (n : ℝ) * (lam - 3 * eps j)) / 2
        = Real.exp (-eps j - Real.log 2 + (lam - 3 * eps j) * n) := by
      have h2 : Real.exp (-eps j - Real.log 2 + (lam - 3 * eps j) * (n : ℝ))
          = Real.exp (-eps j + (n : ℝ) * (lam - 3 * eps j)) * Real.exp (-Real.log 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h2, Real.exp_neg, Real.exp_log two_pos]
      ring
    rw [heq]
    simpa using hd
  -- uniqueness identifies them all with `E 0`
  have hsame : ∀ᵐ ω ∂(R.μ), ∀ j : ℕ, E j ω = E 0 ω := by
    rw [ae_all_iff]
    intro j
    refine R.ae_eq_of_fast m (a := lam - 4 * max (eps j) (eps 0)) (b := lam2)
      (by
        have h1 : 0 < max (eps j) (eps 0) := lt_max_of_lt_left (hepspos j)
        rcases max_cases (eps j) (eps 0) with ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]; linarith [hepsgap j, hepspos j]
        · rw [h]; linarith [hepsgap 0, hepspos 0])
      hchi2 (E j) (E 0) (hEm j) (hEm 0) (hEeq j) (hEeq 0) ?_ ?_
    · filter_upwards [hfast4 j] with ω hω
      filter_upwards [hω] with n hn
      refine lt_of_le_of_lt ?_ hn
      exact Real.exp_le_exp.2 (by
        nlinarith [Nat.cast_nonneg (α := ℝ) n, le_max_left (eps j) (eps 0)])
    · filter_upwards [hfast4 0] with ω hω
      filter_upwards [hω] with n hn
      refine lt_of_le_of_lt ?_ hn
      exact Real.exp_le_exp.2 (by
        nlinarith [Nat.cast_nonneg (α := ℝ) n, le_max_right (eps j) (eps 0)])
  have hall : ∀ᵐ ω ∂(R.μ), ∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam - 4 * eps j) * n) < growth (R.iterate n ω) ((E 0 ω).1 : Submodule ℝ X) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hfast4 j, hsame] with ω hω hs
    filter_upwards [hω] with n hn
    rwa [← hs j]
  have hpos : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
      0 < growth (R.iterate n ω) ((E 0 ω).1 : Submodule ℝ X) := by
    filter_upwards [hall] with ω hlow
    filter_upwards [hlow 0] with n hn
    exact lt_trans (Real.exp_pos _) hn
  refine ⟨E 0, hEm 0, hEeq 0, hpos, ?_⟩
  filter_upwards [hall, hchim, R.ae_tendsto_chi m] with ω hlow heq hchi
  refine (tendsto_order (f := fun n : ℕ =>
    Real.log (growth (R.iterate n ω) ((E 0 ω).1 : Submodule ℝ X)) / n)).2 ⟨?_, ?_⟩
  · -- lower bound: choose `ε_j` small
    intro a ha
    obtain ⟨j, hj⟩ := (hepstend.eventually_lt_const
      (show (0 : ℝ) < (lam - a) / 4 by linarith)).exists
    have hja : a < lam - 4 * eps j := by linarith
    filter_upwards [hlow j, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hgpos : 0 < growth (R.iterate n ω) ((E 0 ω).1 : Submodule ℝ X) :=
      lt_trans (Real.exp_pos _) hn
    rw [lt_div_iff₀ hn0]
    have hlog : (lam - 4 * eps j) * (n : ℝ)
        < Real.log (growth (R.iterate n ω) ((E 0 ω).1 : Submodule ℝ X)) :=
      (Real.lt_log_iff_exp_lt hgpos).2 hn
    nlinarith [hlog, hja, hn0]
  · -- upper bound: `g ≤ ρ_m`
    intro b hb
    have hbchi : R.chi m ω < ((b : ℝ) : EReal) := by
      rw [heq]; exact_mod_cast hb
    filter_upwards [eventually_lt_exp_of_tendsto hbchi hchi, hlow 0, eventually_ge_atTop 1]
      with n hρ hg hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hgpos : 0 < growth (R.iterate n ω) ((E 0 ω).1 : Submodule ℝ X) :=
      lt_trans (Real.exp_pos _) hg
    have hle : growth (R.iterate n ω) ((E 0 ω).1 : Submodule ℝ X) < Real.exp (b * n) :=
      lt_of_le_of_lt (growth_le_bernsteinNumber _ (E 0 ω)) hρ
    rw [div_lt_iff₀ hn0]
    exact (Real.log_lt_iff_lt_exp hgpos).2 hle

/-- An `EReal` exponent limit with a *real* value is a real limit of `log u_n / n`. The route is
through the two-sided exponential bounds, which sidesteps every coercion. -/
theorem tendsto_log_div_of_tendsto_logEReal {u : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop (nhds (c : EReal))) :
    Tendsto (fun n : ℕ => Real.log (u n) / n) atTop (nhds c) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_exp_bounds_of_tendsto (a := a) (b := c + 1)
      (by exact_mod_cast ha) (by exact_mod_cast lt_add_one c) h, eventually_ge_atTop 1]
      with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hu : 0 < u n := lt_trans (Real.exp_pos _) hn.1
    rw [lt_div_iff₀ hn0]
    exact (Real.lt_log_iff_exp_lt hu).2 hn.1
  · intro b hb
    filter_upwards [eventually_exp_bounds_of_tendsto (a := c - 1) (b := b)
      (by exact_mod_cast sub_one_lt c) (by exact_mod_cast hb) h, eventually_ge_atTop 1]
      with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hu : 0 < u n := lt_trans (Real.exp_pos _) hn.1
    rw [div_lt_iff₀ hn0]
    exact (Real.log_lt_iff_lt_exp hu).2 hn.2

omit [MeasurableSpace X] in
/-- A positive Bernstein number witnesses that `𝒢_mX` is inhabited: over an empty index type the
supremum defining `ρ_m` would be `sSup ∅ = 0`. -/
theorem nonempty_grassmannianFin_of_bernstein_pos {T : X →L[ℝ] X} {m : ℕ}
    (h : 0 < bernsteinNumber T m) : Nonempty (GrassmannianFin X m) := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  have hrange : (Set.range fun V : GrassmannianFin X m => growth T (V.1 : Submodule ℝ X)) = ∅ :=
    Set.range_eq_empty _
  have : bernsteinNumber T m = 0 := by
    change sSup _ = 0
    rw [hrange, Real.sSup_empty]
  rw [this] at h
  exact lt_irrefl 0 h

/-- **`proof_met.tex` l.759.** Uniform fast growth of the subspace gives the exponent of *each*
of its nonzero vectors: the growth function is the infimum over the unit sphere and `‖𝓛^{(n)}_ω‖`
is the supremum, and both have exponent `λ₁`, so every unit vector is squeezed between them. -/
theorem Cocycle.lambdaAt_eq_of_growth (R : Cocycle Ω X) {m : ℕ} {lam : ℝ}
    (E : Ω → GrassmannianFin X m) (ω : Ω)
    (hgrow : Tendsto (fun n : ℕ =>
        Real.log (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / n) atTop (nhds lam))
    (hnorm : Tendsto (fun n : ℕ => Real.log ‖R.iterate n ω‖ / n) atTop (nhds lam))
    (hgpos : ∀ᶠ n : ℕ in atTop, 0 < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X))
    {x : X} (hx : x ∈ ((E ω).1 : Submodule ℝ X)) (hx0 : x ≠ 0) :
    R.lambdaAt ω x = (lam : EReal) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set y : X := ‖x‖⁻¹ • x with hy
  have hymem : y ∈ (Metric.sphere (0 : X) 1 ∩ (((E ω).1 : Submodule ℝ X) : Set X)) := by
    refine ⟨?_, ((E ω).1 : Submodule ℝ X).smul_mem _ hx⟩
    rw [mem_sphere_zero_iff_norm, hy, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
  have hxy : x = ‖x‖ • y := by
    rw [hy, smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
  -- the unit vector `y` is squeezed between `g` and `‖·‖`
  have hlow : ∀ n : ℕ, growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X) ≤ ‖R.iterate n ω y‖ :=
    fun n => csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩ ⟨y, hymem, rfl⟩
  have hhigh : ∀ n : ℕ, ‖R.iterate n ω y‖ ≤ ‖R.iterate n ω‖ := by
    intro n
    have := (R.iterate n ω).le_opNorm y
    rwa [mem_sphere_zero_iff_norm.1 hymem.1, mul_one] at this
  have hysq : Tendsto (fun n : ℕ => Real.log ‖R.iterate n ω y‖ / n) atTop (nhds lam) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hgrow hnorm ?_ ?_
    · filter_upwards [hgpos, eventually_ge_atTop 1] with n hn hn1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      gcongr
      exact hlow n
    · filter_upwards [hgpos, eventually_ge_atTop 1] with n hn hn1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hy0 : 0 < ‖R.iterate n ω y‖ := hn.trans_le (hlow n)
      gcongr
      exact hhigh n
  -- and `x` differs from `y` by a constant factor
  have hxeq : ∀ᶠ n : ℕ in atTop, Real.log ‖R.iterate n ω x‖ / n
      = Real.log ‖x‖ / n + Real.log ‖R.iterate n ω y‖ / n := by
    filter_upwards [hgpos] with n hn
    have hy0 : 0 < ‖R.iterate n ω y‖ := hn.trans_le (hlow n)
    have : ‖R.iterate n ω x‖ = ‖x‖ * ‖R.iterate n ω y‖ := by
      conv_lhs => rw [hxy]
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hxn]
    rw [this, Real.log_mul hxn.ne' hy0.ne']
    ring
  have hxtend : Tendsto (fun n : ℕ => Real.log ‖R.iterate n ω x‖ / n) atTop (nhds lam) := by
    refine Tendsto.congr' (EventuallyEq.symm hxeq) ?_
    have h0 : Tendsto (fun n : ℕ => Real.log ‖x‖ / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using h0.add hysq
  have : Tendsto (fun n : ℕ => logEReal ‖R.iterate n ω x‖ / (n : EReal)) atTop
      (nhds (lam : EReal)) := by
    refine (EReal.tendsto_coe.2 hxtend).congr' ?_
    filter_upwards [hgpos] with n hn
    have hy0 : 0 < ‖R.iterate n ω y‖ := hn.trans_le (hlow n)
    have hx0' : 0 < ‖R.iterate n ω x‖ := by
      have : ‖R.iterate n ω x‖ = ‖x‖ * ‖R.iterate n ω y‖ := by
        conv_lhs => rw [hxy]
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hxn]
      rw [this]; exact mul_pos hxn hy0
    rw [logEReal_of_pos hx0']
    rfl
  exact this.limsup_eq

/-- `Cocycle.exists_topFastSpace`, also recording that the growth of the fast space is eventually
positive. `IsFastSpace` cannot imply this (`Real.log 0 = 0` is a junk value), and the slow
projection of `lem:topdecomp` needs it to turn the growth limit into exponential lower bounds. -/
theorem Cocycle.exists_topFastSpace_pos (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] (hqc : R.IsQuasicompact)
    (lam : ℝ) (hlam : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = (lam : EReal)) :
    ∃ (m1 : ℕ) (_ : NeZero m1) (E : Ω → GrassmannianFin X m1),
      (∀ᵐ ω ∂(R.μ), R.mult 0 ω = m1) ∧ R.IsFastSpace m1 lam E ∧
      (∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        0 < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) := by
  obtain ⟨m1, hm1pos, hmult⟩ := R.exists_mult_zero hqc
  have : NeZero m1 := ⟨hm1pos.ne'⟩
  have hchim : ∀ᵐ ω ∂(R.μ), R.chi m1 ω = (lam : EReal) := by
    filter_upwards [hmult, hlam] with ω hm hl
    rw [R.chi_eq_chi_one_of_le_mult ω hm1pos (by rw [hm]), hl]
  have hchi2lt : ∀ᵐ ω ∂(R.μ), R.chi (m1 + 1) ω < (lam : EReal) := by
    filter_upwards [hmult, hlam] with ω hm hl
    have h := R.chi_mult_succ_lt ω (by rw [hm]; exact hm1pos)
    rwa [hm, hl] at h
  obtain ⟨c, hc⟩ := R.exists_chi_ae_const (m1 + 1)
  have hclt : c < (lam : EReal) := by
    obtain ⟨ω, h1, h2⟩ := (hc.and hchi2lt).exists
    rwa [h1] at h2
  obtain ⟨lam2, hlam2c, hlam2lt'⟩ := EReal.lt_iff_exists_real_btwn.1 hclt
  have hlam2lt : lam2 < lam := by exact_mod_cast hlam2lt'
  have hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m1 + 1) ω < (lam2 : EReal) := by
    filter_upwards [hc] with ω h
    rw [h]; exact hlam2c
  have : Nonempty (GrassmannianFin X m1) := by
    obtain ⟨ω, hω1, hω2⟩ := (hchim.and (R.ae_tendsto_chi m1)).exists
    have hb := eventually_exp_bounds_of_tendsto (a := lam - 1) (b := lam + 1)
      (by rw [hω1]; exact_mod_cast (by linarith : lam - 1 < lam))
      (by rw [hω1]; exact_mod_cast (by linarith : lam < lam + 1)) hω2
    obtain ⟨n, hn⟩ := hb.exists
    exact nonempty_grassmannianFin_of_bernstein_pos (lt_trans (Real.exp_pos _) hn.1)
  obtain ⟨E, hEm, hEeq, hEpos, hEtend⟩ := R.exists_fastSpace m1 hlam2lt hchim hlam hchi2
  have hnormtend : ∀ᵐ ω ∂(R.μ),
      Tendsto (fun n : ℕ => Real.log ‖R.iterate n ω‖ / n) atTop (nhds lam) := by
    filter_upwards [R.ae_tendsto_chi 1, hlam] with ω hcv hl
    rw [hl] at hcv
    simp only [bernsteinNumber_one] at hcv
    exact tendsto_log_div_of_tendsto_logEReal hcv
  refine ⟨m1, inferInstance, E, hmult, ⟨hEm, ?_, hEeq, hEtend⟩, hEpos⟩
  filter_upwards [hEtend, hnormtend, hEpos] with ω h1 h2 h3
  intro x hx hx0
  exact R.lambdaAt_eq_of_growth E ω h1 h2 h3 hx hx0

/-- **Lemma** (existence of the top fast space), first unnumbered lemma of Section 5 (blueprint
node `lem:topfast`, rendered as Lemma 4.5): for a quasicompact cocycle on a separable Banach
space there is a fast space of multiplicity `m₁` growing at rate `λ₁ = χ₁`. **Proved.**

**Statement corrected twice.** `m₁` is *produced*, not accepted: an earlier version took it as a
hypothesis, and since `m1` occurred only in the conclusion that claimed a fast space of every
dimension. And `[BorelSpace X]`, `[CompleteSpace X]` were missing — the construction needs the
Grassmannian to be Polish and the selection to be Borel.

`m₁` is `Cocycle.mult 0`, defined alongside `Cocycle.lambda`; `Cocycle.mult_zero_pos` makes it at
least `1` under quasicompactness. How many further multiplicities are nonzero is not settled by
quasicompactness: there may be finitely or infinitely many distinct exponents above `ν`.

**The construction, and the four places it departs from `proof_met.tex`.**

The chain is `exists_approx_spaces` (the greedy selection `E_tilde^{(n)}` and its pushforward
`E^{(n)}`) → `ae_eventually_estimates` (l.700--712) → `eventually_dist_approx_le` (the Cauchy
step, l.730--735) → `exists_limit_approx` (l.735) → `exists_shift_family` and
`map_eq_of_dist_tendsto` (equivariance, l.740--748) → `eventually_growth_limit_ge` (fastness,
l.752--758) → `ae_eq_of_fast` (uniqueness, l.762--772) → `exists_fastSpace` (the `ε → 0` step).

1. *The threshold.* The paper takes `Θ = e^{n(λ₁-4ε)}`, which makes the second fastness bound
   read `e^{(n+1)(λ₁-3ε)}e^{-nε} ≥ e^{n(λ₁-4ε)}` and so needs `λ₁ ≥ 3ε` — true only when
   `λ₁ > 0`, which is not assumed. `Θ_n = min(1, e^{λ₁-4ε})·e^{n(λ₁-4ε)}` repairs it at no cost:
   the constant is absorbed into the geometric rate (`theta_le_bounds`).
2. *Equivariance needs no Lipschitz property of `V ↦ 𝓛_ω V`.* The paper compares
   `E^{(n+1)}(σω)` with `𝓛_ω E^{(n)}(ω)` and bounds `d(𝓛_ω A, 𝓛_ω B)` by `e^{nε}d(A,B)`, a fact
   it never states and which fails without a positive growth hypothesis. Taking the comparison
   one step earlier (`exists_shift_family`) puts *both* spaces under one operator
   `𝓛^{(n)}_{σ^{-n}ω}`, because `E_tilde^{(n+1)}(σω)` is based at `σ^{-(n+1)}(σω) = σ^{-n}ω`;
   `𝓛_ω` is
   then applied to both sides at once. Passing to the limit is `map_eq_of_dist_tendsto`, which
   uses only that distance-to-a-subspace is `2‖x‖`-Lipschitz in the subspace and does not grow by
   more than `‖T‖` under `T`.
3. *The rate is pinned by uniqueness, not by one `ε`.* The paper's fastness bound
   `g(𝓛^{(n)}_ω, E(ω)) > e^{n(λ₁-ε)}` is for the `ε` the construction was run with, so it gives
   `liminf ≥ λ₁ - 3ε` and not the limit. Running the construction for every `ε_j → 0` and
   identifying all the resulting families by `ae_eq_of_fast` gives one family carrying the bound
   for every `j` (`exists_fastSpace`).
4. *Uniqueness needs the spectral gap explicitly*, which is why `topFastSpace_unique` carries a
   hypothesis the paper leaves implicit. It also needs the growth to be eventually positive:
   `IsFastSpace`'s limit clause alone does not give that, since `Real.log 0 = 0` is a junk value
   and `(log 0)/n → 0` is consistent with `λ₁ = 0`. -/
theorem Cocycle.exists_topFastSpace (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] (hqc : R.IsQuasicompact)
    (lam : ℝ) (hlam : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = (lam : EReal)) :
    ∃ (m1 : ℕ) (_ : NeZero m1) (E : Ω → GrassmannianFin X m1),
      (∀ᵐ ω ∂(R.μ), R.mult 0 ω = m1) ∧ R.IsFastSpace m1 lam E := by
  obtain ⟨m1, hm1, E, hmult, hE, -⟩ := R.exists_topFastSpace_pos hqc lam hlam
  exact ⟨m1, hm1, E, hmult, hE⟩

/-- **Lemma** (uniqueness of the top fast space), `proof_met.tex` l.762--772. **Proved**, with
two hypotheses the paper leaves implicit: the spectral gap `χ_{m₁+1} < λ₁` (without which the
statement is false — `pushclose` has nothing to contract with) and eventual positivity of the
growth, which `IsFastSpace` does not imply because `Real.log 0 = 0` is a junk value. The
construction supplies both. The underlying statement, free of `IsFastSpace`, is
`Cocycle.ae_eq_of_fast`. -/
theorem Cocycle.topFastSpace_unique (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (m1 : ℕ) [NeZero m1] (lam : ℝ)
    (hgap : ∀ᵐ ω ∂(R.μ), R.chi (m1 + 1) ω < (lam : EReal))
    (E E' : Ω → GrassmannianFin X m1) (hE : R.IsFastSpace m1 lam E)
    (hE' : R.IsFastSpace m1 lam E')
    (hEpos : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        0 < growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X))
    (hE'pos : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        0 < growth (R.iterate n ω) ((E' ω).1 : Submodule ℝ X)) :
    ∀ᵐ ω ∂(R.μ), E ω = E' ω := by
  obtain ⟨c, hc⟩ := R.exists_chi_ae_const (m1 + 1)
  have hclt : c < (lam : EReal) := by
    obtain ⟨ω, h1, h2⟩ := (hc.and hgap).exists
    rwa [h1] at h2
  obtain ⟨b, hcb, hblam'⟩ := EReal.lt_iff_exists_real_btwn.1 hclt
  have hblam : b < lam := by exact_mod_cast hblam'
  set a : ℝ := (b + lam) / 2 with hadef
  have hba : b < a := by rw [hadef]; linarith
  have halam : a < lam := by rw [hadef]; linarith
  have hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m1 + 1) ω < (b : EReal) := by
    filter_upwards [hc] with ω h
    rw [h]; exact hcb
  have hstep : ∀ (F : Ω → GrassmannianFin X m1),
      (∀ᵐ ω ∂(R.μ), Tendsto
        (fun n : ℕ => Real.log (growth (R.iterate n ω) ((F ω).1 : Submodule ℝ X)) / n)
        atTop (nhds lam)) →
      (∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        0 < growth (R.iterate n ω) ((F ω).1 : Submodule ℝ X)) →
      ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        Real.exp (a * n) < growth (R.iterate n ω) ((F ω).1 : Submodule ℝ X) := by
    intro F htend hpos
    filter_upwards [htend, hpos] with ω ht hp
    filter_upwards [ht.eventually_const_lt halam, hp, eventually_ge_atTop 1] with n hn hg hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hn0] at hn
    exact (Real.lt_log_iff_exp_lt hg).1 hn
  exact R.ae_eq_of_fast m1 hba hchi2 E E' hE.1 hE'.1 hE.2.2.1 hE'.2.2.1
    (hstep E hE.2.2.2 hEpos) (hstep E' hE'.2.2.2 hE'pos)

/-- **Predicate.** `P` is a tempered family of projections: `(1/n) log‖P_{σⁿω}‖ → 0` a.e.
An abbreviation for `Tempered R.σ R.μ (log ‖P ·‖)`: temperedness depends only on the base
`(σ, μ)`, not on the cocycle.
(`Π` is reserved Lean/Mathlib notation, so we use `P` for projections throughout the Lean
code; the paper's `Π` notation is kept in the prose and in `blueprint/src/content.tex`.) -/
abbrev Cocycle.IsTempered (R : Cocycle Ω X) (P : Ω → X →L[ℝ] X) : Prop :=
  Tempered R.σ R.μ (fun ω => Real.log ‖P ω‖)

end MultiplicativeErgodic

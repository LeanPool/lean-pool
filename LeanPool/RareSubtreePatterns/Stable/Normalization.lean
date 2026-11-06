/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.Convergence
public import LeanPool.RareSubtreePatterns.RegularVariation.Consequences
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Regular variation of the normalizing sequence (Stage 2)

Source lines 846–853 (inventory B06): under `(H_α)` the normalizing sequence `(a_n)` is regularly
varying of index `1/α`, i.e. `a_n / n^{1/α}` is slowly varying. The paper cites Feller; here it
is *derived* from the convergence `S_n / a_n → Y_α` by a convergence-of-types argument on the
moduli of characteristic functions:

* `PoissonDeclumping.Stable.tendsto_div_of_tendsto_div`: if `m'_n / n → κ > 0` then
  `a_n / a_{m'_n} → κ^{-1/α}` (Bolzano–Weierstrass on `u/(1+u)`, identification of the limit
  through `|φ(1/a_{m'})|^{m'} = (|φ(u/a_n)|^n)^{m'/n}` and `|E e^{itY_α}| = exp(cos(πα/2)|t|^α)`);
* `PoissonDeclumping.Stable.regularlyVaryingSeq`: `RegularlyVaryingSeq (1/α) a`;
* `PoissonDeclumping.Stable.slowlyVarying`: `x ↦ a_{⌊x⌋} / x^{1/α}` is slowly varying;
* `PoissonDeclumping.Stable.tendsto_atTop`: `a_n → ∞`.

No truncated-second-moment criterion is assumed; the proof starts from normalized weak convergence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

lemma rpow_pow_div {x : ℝ} (hx : 0 ≤ x) {n m : ℕ} (hn : n ≠ 0) :
    (x ^ n) ^ ((m : ℝ) / n) = x ^ m := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx, mul_div_cancel₀ _ (by exact_mod_cast hn),
    Real.rpow_natCast]

lemma tendsto_natCast_of_div {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) : Tendsto m' atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (m' n : ℝ) / n * n) atTop atTop :=
    Tendsto.pos_mul_atTop hκ hm' tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (m' n : ℝ)) atTop atTop := by
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  exact tendsto_natCast_atTop_iff.1 h2

/-- **Convergence of types** for the normalizing sequence: if `m'_n / n → κ > 0` then
`a_n / a_{m'_n} → κ^{-1/α}`. -/
theorem tendsto_div_of_tendsto_div (h : StableDomain μ α a) {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => a n / a (m' n)) atTop (𝓝 (κ ^ (-(1 / α)))) := by
  have hα := h.alpha_mem
  have hα0 : 0 < α := by linarith
  set c0 : ℝ := Real.cos (Real.pi * α / 2) with hc0
  have hc0neg : c0 < 0 := cos_pi_mul_div_two_neg hα
  set G : ℝ → ℝ := fun s => Real.exp (c0 * |s| ^ α) with hG
  have hm'top := tendsto_natCast_of_div hκ hm'
  set u : ℕ → ℝ := fun n => a n / a (m' n) with hu
  have hpos : ∀ᶠ n in atTop, 1 ≤ n ∧ 1 ≤ m' n :=
    (eventually_ge_atTop 1).and (hm'top.eventually (eventually_ge_atTop 1))
  have hupos : ∀ᶠ n in atTop, 0 < u n := by
    filter_upwards [hpos] with n hn
    exact div_pos (h.pos n hn.1) (h.pos _ hn.2)
  -- the two identities
  have E1 : ∀ᶠ n in atTop, ‖stepCF μ (1 / a (m' n))‖ ^ m' n =
      (‖stepCF μ (u n / a n)‖ ^ n) ^ ((m' n : ℝ) / n) := by
    filter_upwards [hpos] with n hn
    have ha := (h.pos n hn.1).ne'
    have ha' := (h.pos _ hn.2).ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]; field_simp
  have E2 : ∀ᶠ n in atTop, ‖stepCF μ (1 / a n)‖ ^ n =
      (‖stepCF μ ((1 / u n) / a (m' n))‖ ^ m' n) ^ ((n : ℝ) / m' n) := by
    filter_upwards [hpos] with n hn
    have ha := (h.pos n hn.1).ne'
    have ha' := (h.pos _ hn.2).ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]; field_simp
  have hG1 : G 1 < 1 := by
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    exact Real.exp_lt_one_iff.2 hc0neg
  apply tendsto_of_subseq_tendsto
  intro ns hns
  set v : ℕ → ℝ := fun k => u (ns k) / (1 + u (ns k)) with hv
  have hvmem : ∃ᶠ k in atTop, v k ∈ Icc (0 : ℝ) 1 := by
    apply Eventually.frequently
    filter_upwards [hns.eventually hupos] with k hk
    refine ⟨div_nonneg hk.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  obtain ⟨w, hw, φ, hφ, hvφ⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc 0 1) hvmem
  rw [closure_Icc] at hw
  set ψ : ℕ → ℕ := ns ∘ φ with hψ
  have hψtop : Tendsto ψ atTop atTop := hns.comp hφ.tendsto_atTop
  have huψpos : ∀ᶠ k in atTop, 0 < u (ψ k) := hψtop.eventually hupos
  have hrecov : ∀ᶠ k in atTop, u (ψ k) = v (φ k) / (1 - v (φ k)) := by
    filter_upwards [huψpos] with k hk
    have hk' : 0 < u (ns (φ k)) := hk
    simp only [hv, hψ, Function.comp]
    have h2 : 1 - u (ns (φ k)) / (1 + u (ns (φ k))) = 1 / (1 + u (ns (φ k))) := by
      field_simp; ring
    rw [h2, div_div_div_cancel_right₀ (by positivity)]
    simp
  have hratio : Tendsto (fun k => (m' (ψ k) : ℝ) / ψ k) atTop (𝓝 κ) := hm'.comp hψtop
  rcases hw.2.lt_or_eq with hw1 | hw1
  · -- bounded case
    set ustar : ℝ := w / (1 - w) with hustar
    have hu_t : Tendsto (fun k => u (ψ k)) atTop (𝓝 ustar) := by
      have : Tendsto (fun k => v (φ k) / (1 - v (φ k))) atTop (𝓝 (w / (1 - w))) :=
        hvφ.div (tendsto_const_nhds.sub hvφ) (by linarith)
      exact this.congr' (hrecov.mono fun k hk => hk.symm)
    have hustar0 : 0 ≤ ustar := div_nonneg hw.1 (by linarith)
    have L1 : Tendsto (fun k => ‖stepCF μ (1 / a (m' (ψ k)))‖ ^ m' (ψ k)) atTop (𝓝 (G 1)) :=
      tendsto_norm_stepCF_pow h (hm'top.comp hψtop) tendsto_const_nhds
    have L2 : Tendsto (fun k => (‖stepCF μ (u (ψ k) / a (ψ k))‖ ^ ψ k) ^ ((m' (ψ k) : ℝ) / ψ k))
        atTop (𝓝 (G ustar ^ κ)) :=
      (tendsto_norm_stepCF_pow h hψtop hu_t).rpow hratio (Or.inl (Real.exp_pos _).ne')
    have heq : G 1 = G ustar ^ κ :=
      tendsto_nhds_unique L1 (L2.congr' ((hψtop.eventually E1).mono fun k hk => hk.symm))
    have hval : ustar = κ ^ (-(1 / α)) := by
      simp only [hG, abs_one, Real.one_rpow, mul_one, ← Real.exp_mul] at heq
      have h1 : c0 = c0 * |ustar| ^ α * κ := Real.exp_injective heq
      have h2 : |ustar| ^ α * κ = 1 := by
        have : c0 * (|ustar| ^ α * κ - 1) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hc0neg.ne
        · linarith
      rw [abs_of_nonneg hustar0] at h2
      have h3 : ustar ^ α = κ⁻¹ := by field_simp; linarith
      calc ustar = (ustar ^ α) ^ (1 / α) := by
            rw [← Real.rpow_mul hustar0, mul_one_div_cancel hα0.ne', Real.rpow_one]
        _ = κ ^ (-(1 / α)) := by rw [h3, Real.rpow_neg hκ.le, Real.inv_rpow hκ.le]
    refine ⟨φ, ?_⟩
    rw [← hval]
    exact hu_t
  · -- unbounded case: contradiction
    exfalso
    have hinv : Tendsto (fun k => 1 / u (ψ k)) atTop (𝓝 0) := by
      have : Tendsto (fun k => (1 - v (φ k)) / v (φ k)) atTop (𝓝 ((1 - w) / w)) :=
        (tendsto_const_nhds.sub hvφ).div hvφ (by rw [hw1]; norm_num)
      rw [hw1, sub_self, zero_div] at this
      refine this.congr' ?_
      filter_upwards [hrecov, huψpos] with k hk hk'
      rw [hk]
      have hv1 : v (φ k) ≠ 1 := by
        intro h1; rw [h1, sub_self, div_zero] at hk; linarith
      have hv0 : v (φ k) ≠ 0 := by
        intro h0; rw [h0, zero_div] at hk; linarith
      have : 1 - v (φ k) ≠ 0 := sub_ne_zero.2 (Ne.symm hv1)
      field_simp
    have L1 : Tendsto (fun k => ‖stepCF μ (1 / a (ψ k))‖ ^ ψ k) atTop (𝓝 (G 1)) :=
      tendsto_norm_stepCF_pow h hψtop tendsto_const_nhds
    have hratio' : Tendsto (fun k => (ψ k : ℝ) / m' (ψ k)) atTop (𝓝 κ⁻¹) := by
      have := hratio.inv₀ hκ.ne'
      refine this.congr fun k => ?_
      simp [inv_div]
    have L2 : Tendsto (fun k => (‖stepCF μ ((1 / u (ψ k)) / a (m' (ψ k)))‖ ^ m' (ψ k)) ^
        ((ψ k : ℝ) / m' (ψ k))) atTop (𝓝 (G 0 ^ κ⁻¹)) :=
      (tendsto_norm_stepCF_pow h (hm'top.comp hψtop) hinv).rpow hratio'
        (Or.inl (Real.exp_pos _).ne')
    have heq : G 1 = G 0 ^ κ⁻¹ :=
      tendsto_nhds_unique L1 (L2.congr' ((hψtop.eventually E2).mono fun k hk => hk.symm))
    have hG0 : G 0 = 1 := by simp [hG, Real.zero_rpow hα0.ne']
    rw [hG0, Real.one_rpow] at heq
    linarith

/-- `a_{m'_n} / a_n → κ^{1/α}` when `m'_n / n → κ > 0`. -/
theorem tendsto_div_of_tendsto_div' (h : StableDomain μ α a) {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => a (m' n) / a n) atTop (𝓝 (κ ^ (1 / α))) := by
  have := (tendsto_div_of_tendsto_div h hκ hm').inv₀ (Real.rpow_pos_of_pos hκ _).ne'
  rw [Real.rpow_neg hκ.le, inv_inv] at this
  exact this.congr fun n => by simp [inv_div]

/-- **Regular variation of `(a_n)`** (source lines 850–851): `a_{⌊cn⌋} / a_n → c^{1/α}`. -/
theorem regularlyVaryingSeq (h : StableDomain μ α a) : RegularlyVaryingSeq (1 / α) a := by
  intro c hc
  apply tendsto_div_of_tendsto_div' h hc
  have := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc.le).comp tendsto_natCast_atTop_atTop
  exact this

/-- `a_n → ∞`. -/
theorem tendsto_atTop (h : StableDomain μ α a) : Tendsto a atTop atTop :=
  (regularlyVaryingSeq h).tendsto_atTop h.monotone h.pos
    (one_div_pos.2 (by linarith [h.alpha_mem.1]))

/-- `a_{n+1} / a_n → 1`. -/
theorem tendsto_succ_div (h : StableDomain μ α a) :
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    push_cast; field_simp
  have := tendsto_div_of_tendsto_div' h one_pos h1
  rwa [Real.one_rpow] at this

/-- **`a_n / n^{1/α}` is slowly varying** (source line 850, in the sense of
`PoissonDeclumping.SlowlyVarying`, with `a_x := a_{⌊x⌋}` for real `x`). -/
theorem slowlyVarying (h : StableDomain μ α a) :
    SlowlyVarying (fun x : ℝ => a ⌊x⌋₊ / x ^ (1 / α)) := by
  intro c hc
  set ρ : ℝ := 1 / α
  have hrv := regularlyVaryingSeq h
  -- two monotone bounds along `n = ⌊x⌋`
  have f1 : Tendsto (fun n : ℕ => a ⌊c * n⌋₊ / a n) atTop (𝓝 (c ^ ρ)) := hrv c hc
  have f2 : Tendsto (fun n : ℕ => a ⌊c * (n + 1 : ℕ)⌋₊ / a n) atTop (𝓝 (c ^ ρ)) := by
    apply tendsto_div_of_tendsto_div' h hc
    have g1 := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc.le).comp tendsto_natCast_atTop_atTop
    have g2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      push_cast; field_simp
    have g3 := (g1.comp (tendsto_add_atTop_nat 1)).mul g2
    rw [mul_one] at g3
    refine g3.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Function.comp]
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hfl := tendsto_nat_floor_atTop (α := ℝ)
  have hratio : Tendsto (fun x : ℝ => a ⌊c * x⌋₊ / a ⌊x⌋₊) atTop (𝓝 (c ^ ρ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f1.comp hfl) (f2.comp hfl) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
      simp only [Function.comp]
      apply div_le_div_of_nonneg_right _ (h.pos _ hn).le
      apply h.monotone
      apply Nat.floor_le_floor
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) hc.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
      simp only [Function.comp]
      apply div_le_div_of_nonneg_right _ (h.pos _ hn).le
      apply h.monotone
      apply Nat.floor_le_floor
      apply mul_le_mul_of_nonneg_left _ hc.le
      push_cast
      exact (Nat.lt_floor_add_one x).le
  have hfin := hratio.mul_const (c ^ (-ρ))
  rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero] at hfin
  refine hfin.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have ha := (h.pos _ hn).ne'
  rw [Real.mul_rpow hc.le hx0.le, Real.rpow_neg hc.le]
  have h1 : (0 : ℝ) < c ^ ρ := Real.rpow_pos_of_pos hc _
  have h2 : (0 : ℝ) < x ^ ρ := Real.rpow_pos_of_pos hx0 _
  field_simp

end PoissonDeclumping.Stable

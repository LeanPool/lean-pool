/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Duality
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.TestFunctions.One

/-!
# Dragičević's lower bounds for `‖𝓑‖_p` and `‖𝓑²‖_p`

With the Pochhammer symbol `(a)_n = a (a + 1) ⋯ (a + n − 1)` and `q = p / (p − 1)`, Dragičević's
constant is `κ_n (p) = (1/q)_n / (1/p)_n` (`HarmonicAnalysis.beurlingKappa`); `κ₁ (p) = p − 1`
and `κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`. Let `p* = max (p, q)` (`HarmonicAnalysis.pStar`).

## Main results

* `HarmonicAnalysis.tendsto_eLpNorm_div_of_lintegral_ball`: the limit of the ratio of the norms in
  Dragičević's proof, from the integrals over the unit disc and those outside it.
* `HarmonicAnalysis.tendsto_eLpNorm_div_testFunOne`, `HarmonicAnalysis.tendsto_eLpNorm_div_testFun`
  (Dragičević's limit, `n = 1` and `n = 2`): for the test functions
  `f_{1,α} (z) = z |z|^{−2α} g₂ (|z|)` and `f_{2,α} (z) = z² |z|^{−2α} g₂ (|z|)`,
  `‖∂f_{1,α}‖_p / ‖∂_zbar f_{1,α}‖_p → κ₁ (p)` and `‖∂²f_{2,α}‖_p / ‖∂_zbar²f_{2,α}‖_p → κ₂ (p)` as
  `α → 1/p` from below. On the unit disc, `f_{1,α}` is the function `f_α` of
  Baernstein–Montgomery-Smith (1999, §1), and the limit for `n = 1` is theirs.
* `HarmonicAnalysis.eLpNorm_div_le_beurlingPowNorm_one`,
  `HarmonicAnalysis.eLpNorm_div_le_beurlingPowNorm_two`:
  `‖∂^n f_{n,α}‖_p / ‖∂_zbar^n f_{n,α}‖_p ≤ ‖𝓑^n‖_p` for `0 < α < 1/p`, by Schwartz approximations
  of
  `f_{n,α}` and `𝓑^n (∂_zbar^n φ) = ∂^n φ` for these.
* `HarmonicAnalysis.beurlingKappa_one_le_beurlingPowNorm_one`,
  `HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two` (Dragičević's theorem, `n = 1` and
  `n = 2`): `κ_n (p) ≤ ‖𝓑^n‖_p` for `1 < p < ∞`; for `n = 1`, `p − 1 ≤ ‖𝓑‖_p`
  (`HarmonicAnalysis.sub_one_le_beurlingPowNorm_one`).
* `HarmonicAnalysis.beurlingKappa_two_pStar_le_beurlingPowNorm_two`: `κ₂ (p*) ≤ ‖𝓑²‖_p` for
  `1 < p < ∞`. Dragičević's Theorem 1.1 is for `p > 2`, and the article does not state the bound
  with `κ_n` for `p < 2`; that case is `‖𝓑²‖_p = ‖𝓑²‖_q`
  (`HarmonicAnalysis.beurlingPowNorm_conjExponent`), the reduction to `p ≥ 2` of
  Carbonaro–Dragičević–Kovač §1.3.1 (for `R^k`, `𝓑 = R²`). The article recalls (p. 463), and the
  lecture notes' Corollary 4.8 states, the weaker asymptotic form
  `‖T^n‖_p ≳ n^{1−2/p*}(p* − 1)` for every `p`.
* Corollaries: `p* − 1 < ‖𝓑²‖_p` for `p ≠ 2`
  (`HarmonicAnalysis.pStar_sub_one_lt_beurlingPowNorm_two`), since
  `κ₂ (p*) − (p* − 1) = (p* − 1)(p* − 2) / (p* + 1) > 0`; and `21/5 = κ₂ (4) ≤ ‖𝓑²‖₄`
  (`HarmonicAnalysis.twentyOne_div_five_le_beurlingPowNorm_two_four`).

Dragičević's Theorem 1.1 is `‖T^n‖_p ≥ κ_n (p)` for every `n` and `p > 2` (the article's standing
assumption, p. 464), where it is the informative bound; the same argument gives
`κ_n (p) ≤ ‖𝓑^n‖_p` for every `p > 1`. Only `n = 1` and `n = 2` are proved here; general `n` is a
planned extension.

The proof is the article's (pp. 466–467; repeated in the lecture notes, Proposition 4.2), with its
test functions (`HarmonicAnalysis.BeurlingAhlfors.testFun`; for `n = 1`,
`HarmonicAnalysis.BeurlingAhlfors.testFunOne`, with the cutoff `g₂` in place of the article's
example `g₁`, which is not `C¹` at `1`): explicit integrals over the unit disc, of order
`(1 − αp)⁻¹`, and integrals outside it that stay bounded, in the identity (2.1) for the ratio of
the `p`-th powers of the norms. The norm `‖𝓑^n‖_p` is a supremum over Schwartz functions, and
`f_{n,α}` is not one. The article asserts without proof that `f_{n,α}` "belongs to `W^{n,p}`,
which ensures that `T^n (∂_zbar^n f) = ∂^n f`" (p. 465; lecture notes, §4.1 and Exercise 4.1; for
`n = 1`, Exercise 2.19, whose hint is to approximate by smooth functions). What is used of it,
`‖∂^n f‖_p ≤ ‖𝓑^n‖_p ‖∂_zbar^n f‖_p`, is proved here by the density step
`HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto`, applied to Schwartz approximations of
`f_{n,α}` in `W^{n,p}` (`HarmonicAnalysis.BeurlingAhlfors.exists_schwartz_tendsto_testFunOne`,
`HarmonicAnalysis.BeurlingAhlfors.exists_schwartz_tendsto_testFun`).

## References

* O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471: Theorem 1.1 (p. 465), proof pp. 466–467.
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555): Proposition 4.2 (Theorem 1.1 of the
  previous reference, with the same proof), Exercises 2.19 and 4.1.
* A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), 1081–1125,
  [arXiv:2109.08369](https://arxiv.org/abs/2109.08369), §1.3.1 and §2.1.
* A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
  `∂_zbar f`*, in: Complex analysis and differential equations (Uppsala, 1997), ed. C. Kiselman,
  Acta
  Univ. Upsaliensis C 64 (1999), 92–109, [arXiv:math/9709215](https://arxiv.org/abs/math/9709215),
  §1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HarmonicAnalysis

open BeurlingAhlfors

/-- `κ₁ (p) = p − 1`. -/
theorem beurlingKappa_one {p : ℝ} (hp : p ≠ 0) : beurlingKappa 1 p = p - 1 := by
  simp only [beurlingKappa, ascPochhammer_one, Polynomial.eval_X]
  field_simp

/-- `κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`. -/
theorem beurlingKappa_two {p : ℝ} (hp : 0 < p) :
    beurlingKappa 2 p = (p - 1) * (2 * p - 1) / (p + 1) := by
  simp only [beurlingKappa, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one,
    one_mul]
  field_simp
  ring

/-- `κ₂ (4) = 21/5`. -/
theorem beurlingKappa_two_four : beurlingKappa 2 4 = 21 / 5 := by
  simp only [beurlingKappa, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one,
    one_mul]
  norm_num

theorem pStar_of_two_le {p : ℝ} (hp : 2 ≤ p) : pStar p = p :=
  max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)

theorem pStar_of_lt_two {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : pStar p = p / (p - 1) :=
  max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)

theorem two_lt_pStar {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) : 2 < pStar p := by
  rcases lt_or_gt_of_ne hp2 with h | h
  · rw [pStar_of_lt_two hp h, lt_div_iff₀ (by linarith)]
    linarith
  · rw [pStar_of_two_le h.le]
    exact h

/-! ### The limit of the ratio -/

/-- `αp < 1` for `0 < α < 1/p`. -/
theorem mul_lt_one_of_mem_Ioo_inv {p α : ℝ} (hp : 0 < p) (hα : α ∈ Set.Ioo 0 p⁻¹) : α * p < 1 :=
  calc α * p < p⁻¹ * p := mul_lt_mul_of_pos_right hα.2 hp
    _ = 1 := inv_mul_cancel₀ hp.ne'

/-- The limit in Dragičević's proof of Theorem 1.1 (pp. 466–467, with the identity (2.1)): if, for
`0 < α < 1/p`, `∫_Δ |u_α|^p = π / (1 − αp) a (α)^p` and `∫_Δ |v_α|^p = π / (1 − αp) b (α)^p` on
the unit disc `Δ`, and the integrals of `|u_α|^p` and `|v_α|^p` outside `Δ` stay bounded, then
`‖u_α‖_p / ‖v_α‖_p → a (1/p) / b (1/p)` as `α → 1/p` from below (`a`, `b` continuous, `a ≥ 0`
and `b > 0` on `(0, 1/p]`): the integrals over `Δ` grow like `(1 − αp)⁻¹`, and the others
disappear in the ratio. -/
theorem tendsto_eLpNorm_div_of_lintegral_ball {p : ℝ} (hp : 1 < p) {u v : ℝ → ℂ → ℂ}
    {a b : ℝ → ℝ} (hu : ∀ α, Measurable (u α)) (hv : ∀ α, Measurable (v α))
    (ha : Continuous a) (hb : Continuous b) (ha0 : ∀ α ∈ Set.Ioc 0 p⁻¹, 0 ≤ a α)
    (hb0 : ∀ α ∈ Set.Ioc 0 p⁻¹, 0 < b α)
    (huB : ∀ α ∈ Set.Ioo 0 p⁻¹, ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖u α z‖ₑ ^ p =
      ENNReal.ofReal (Real.pi / (1 - α * p) * a α ^ p))
    (hvB : ∀ α ∈ Set.Ioo 0 p⁻¹, ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖v α z‖ₑ ^ p =
      ENNReal.ofReal (Real.pi / (1 - α * p) * b α ^ p))
    (hC : ∃ C : ℝ, ∀ α ∈ Set.Ioo 0 p⁻¹,
      ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖u α z‖ₑ ^ p ≤ ENNReal.ofReal C ∧
        ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖v α z‖ₑ ^ p ≤ ENNReal.ofReal C) :
    Tendsto (fun α => eLpNorm (u α) (ENNReal.ofReal p) volume /
        eLpNorm (v α) (ENNReal.ofReal p) volume)
      (𝓝[<] p⁻¹) (𝓝 (ENNReal.ofReal (a p⁻¹ / b p⁻¹))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hB : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  -- the integrals over `Δᶜ`, bounded uniformly in `α`
  obtain ⟨C, hC⟩ := hC
  obtain ⟨iOut, hiOut⟩ : ∃ g : ℝ → ℝ, ∀ α, g α =
      (∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖u α z‖ₑ ^ p).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jOut, hjOut⟩ : ∃ g : ℝ → ℝ, ∀ α, g α =
      (∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖v α z‖ₑ ^ p).toReal :=
    ⟨_, fun _ => rfl⟩
  -- the article's (2.1): the ratio of the `p`-th powers of the norms, with numerator and
  -- denominator multiplied by `1 − αp`
  have heq : ∀ α ∈ Set.Ioo 0 p⁻¹,
      eLpNorm (u α) (ENNReal.ofReal p) volume / eLpNorm (v α) (ENNReal.ofReal p) volume =
        ENNReal.ofReal (((Real.pi * a α ^ p + (1 - α * p) * iOut α) /
          (Real.pi * b α ^ p + (1 - α * p) * jOut α)) ^ (1 / p)) := by
    intro α hα
    obtain ⟨hI, hJ⟩ := hC α hα
    have hε : 0 < 1 - α * p := by linarith [mul_lt_one_of_mem_Ioo_inv hp0 hα]
    have hα' : α ∈ Set.Ioc 0 p⁻¹ := Set.Ioo_subset_Ioc_self hα
    have ha : 0 ≤ Real.pi / (1 - α * p) * a α ^ p :=
      mul_nonneg (div_pos Real.pi_pos hε).le (Real.rpow_nonneg (ha0 α hα') _)
    have hb : 0 < Real.pi / (1 - α * p) * b α ^ p :=
      mul_pos (div_pos Real.pi_pos hε) (Real.rpow_pos_of_pos (hb0 α hα') _)
    have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp' ENNReal.ofReal_ne_top
        (hu α).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp' ENNReal.ofReal_ne_top
        (hv α).aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le, ← lintegral_add_compl (μ := volume) _ hB,
      ← lintegral_add_compl (μ := volume) _ hB, huB α hα, hvB α hα,
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI),
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJ),
      ← ENNReal.ofReal_add ha ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_add hb.le ENNReal.toReal_nonneg,
      ← ENNReal.div_rpow_of_nonneg _ _ (one_div_nonneg.2 hp0.le),
      ← ENNReal.ofReal_div_of_pos (add_pos_of_pos_of_nonneg hb ENNReal.toReal_nonneg),
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (add_nonneg ha ENNReal.toReal_nonneg)
        (add_nonneg hb.le ENNReal.toReal_nonneg)) (one_div_nonneg.2 hp0.le)]
    congr 2
    rw [hiOut, hjOut]
    field_simp
  -- as `α → 1/p`, `1 − αp → 0`, and the integrals over `Δᶜ` disappear
  have hev : ∀ᶠ α in 𝓝[<] p⁻¹, α ∈ Set.Ioo 0 p⁻¹ := Ioo_mem_nhdsLT (inv_pos.2 hp0)
  have hε : Tendsto (fun α : ℝ => 1 - α * p) (𝓝[<] p⁻¹) (𝓝 0) := by
    have h : Tendsto (fun α : ℝ => 1 - α * p) (𝓝 p⁻¹) (𝓝 (1 - p⁻¹ * p)) :=
      (continuous_const.sub (continuous_id.mul continuous_const)).tendsto p⁻¹
    rw [inv_mul_cancel₀ hp0.ne', sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hvanish : ∀ g : ℝ → ℝ,
      (∀ α ∈ Set.Ioo 0 p⁻¹, 0 ≤ g α ∧ g α ≤ (ENNReal.ofReal C).toReal) →
        Tendsto (fun α => (1 - α * p) * g α) (𝓝[<] p⁻¹) (𝓝 0) := by
    intro g hg
    have h0 := hε.mul_const (ENNReal.ofReal C).toReal
    rw [zero_mul] at h0
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [hev] with α hα
      exact mul_nonneg (by linarith [mul_lt_one_of_mem_Ioo_inv hp0 hα]) (hg α hα).1
    · filter_upwards [hev] with α hα
      exact mul_le_mul_of_nonneg_left (hg α hα).2
        (by linarith [mul_lt_one_of_mem_Ioo_inv hp0 hα])
  have hi := hvanish iOut fun α hα => ⟨(hiOut α).symm ▸ ENNReal.toReal_nonneg,
    (hiOut α).symm ▸ ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC α hα).1⟩
  have hj := hvanish jOut fun α hα => ⟨(hjOut α).symm ▸ ENNReal.toReal_nonneg,
    (hjOut α).symm ▸ ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC α hα).2⟩
  have hcont : ∀ g : ℝ → ℝ, Continuous g →
      Tendsto (fun α => Real.pi * g α ^ p) (𝓝[<] p⁻¹) (𝓝 (Real.pi * g p⁻¹ ^ p)) := fun g hg =>
    ((continuous_const.mul (hg.rpow_const fun _ => Or.inr hp0.le)).tendsto p⁻¹).mono_left
      nhdsWithin_le_nhds
  have hp1 : p⁻¹ ∈ Set.Ioc 0 p⁻¹ := ⟨inv_pos.2 hp0, le_rfl⟩
  have ha1 := ha0 _ hp1
  have hb1 := hb0 _ hp1
  have hlim := (((hcont a ha).add hi).div ((hcont b hb).add hj) (by
    rw [add_zero]
    exact (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hb1 p)).ne')).rpow_const
    (Or.inr (one_div_nonneg.2 hp0.le))
  -- the limit is `a (1/p) / b (1/p)`
  have hval : ((Real.pi * a p⁻¹ ^ p + 0) / (Real.pi * b p⁻¹ ^ p + 0)) ^ (1 / p) =
      a p⁻¹ / b p⁻¹ := by
    rw [add_zero, add_zero, mul_div_mul_left _ _ Real.pi_ne_zero, ← Real.div_rpow ha1 hb1.le,
      ← Real.rpow_mul (div_nonneg ha1 hb1.le), mul_one_div_cancel hp0.ne', Real.rpow_one]
  rw [hval] at hlim
  refine (ENNReal.tendsto_ofReal hlim).congr' ?_
  filter_upwards [hev] with α hα
  exact (heq α hα).symm

/-! ### `n = 1` -/

/-- Dragičević's limit (Theorem 1.1, for `p > 2`), `n = 1`:
`‖∂f_{1,α}‖_p / ‖∂_zbar f_{1,α}‖_p → κ₁ (p) = p − 1` as `α → 1/p` from below, for `1 < p < ∞`, by
the article's argument (`HarmonicAnalysis.tendsto_eLpNorm_div_of_lintegral_ball`). It is the limit
that Baernstein–Montgomery-Smith (1999, §1) compute for their `f_α`, equal to `f_{1,α}` on the unit
disc and to `1/(conj z)` outside it. -/
theorem tendsto_eLpNorm_div_testFunOne {p : ℝ} (hp : 1 < p) :
    Tendsto (fun α : ℝ =>
        eLpNorm (dz (testFunOne α)) (ENNReal.ofReal p) volume /
          eLpNorm (dzbar (testFunOne α)) (ENNReal.ofReal p) volume)
      (𝓝[<] p⁻¹) (𝓝 (ENNReal.ofReal (beurlingKappa 1 p))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpi : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  obtain ⟨C, hC⟩ := exists_bound_testFunOne_compl_ball hp0
  have h := tendsto_eLpNorm_div_of_lintegral_ball hp (u := fun α => dz (testFunOne α))
    (v := fun α => dzbar (testFunOne α)) (a := fun α => 1 - α) (b := fun α => α)
    (fun _ => measurable_dz _) (fun _ => measurable_dzbar _) (by fun_prop) (by fun_prop)
    (fun α hα => by linarith [hα.2]) (fun α hα => hα.1)
    (fun α hα => lintegral_dz_testFunOne_ball hp hα.1 (mul_lt_one_of_mem_Ioo_inv hp0 hα))
    (fun α hα => lintegral_dzbar_testFunOne_ball hp hα.1 (mul_lt_one_of_mem_Ioo_inv hp0 hα))
    ⟨C, fun α hα => hC α ⟨hα.1.le, (hα.2.trans hpi).le⟩⟩
  rwa [show (1 - p⁻¹) / p⁻¹ = beurlingKappa 1 p by
    rw [beurlingKappa_one hp0.ne']
    field_simp] at h

/-- `‖∂f_{1,α}‖_p / ‖∂_zbar f_{1,α}‖_p ≤ ‖𝓑‖_p` for `1 < p < ∞` and `0 < α < 1/p`: Schwartz
approximations of `f_{1,α}` and `𝓑 ∂_zbar = ∂` on Schwartz functions. -/
theorem eLpNorm_div_le_beurlingPowNorm_one {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    eLpNorm (dz (testFunOne α)) (ENNReal.ofReal p) volume /
        eLpNorm (dzbar (testFunOne α)) (ENNReal.ofReal p) volume ≤
      beurlingPowNorm 1 p := by
  obtain ⟨φ, hu, hv⟩ := exists_schwartz_tendsto_testFunOne hp.le hα0 hα
  exact div_le_beurlingPowNorm_of_tendsto 1 hp.le hu hv

/-- Dragičević's lower bound (Theorem 1.1, for `p > 2`), the case `n = 1`:
`κ₁ (p) ≤ ‖𝓑‖_{L^p}` for `1 < p < ∞`. -/
theorem beurlingKappa_one_le_beurlingPowNorm_one {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 1 p) ≤ beurlingPowNorm 1 p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  refine le_of_tendsto (tendsto_eLpNorm_div_testFunOne hp) ?_
  filter_upwards [Ioo_mem_nhdsLT (inv_pos.mpr hp0)] with α hα
  exact eLpNorm_div_le_beurlingPowNorm_one hp hα.1 (mul_lt_one_of_mem_Ioo_inv hp0 hα)

/-- `p − 1 ≤ ‖𝓑‖_{L^p}` for `1 < p < ∞`: Dragičević's lower bound for `n = 1`,
`κ₁ (p) = p − 1`. -/
theorem sub_one_le_beurlingPowNorm_one {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (p - 1) ≤ beurlingPowNorm 1 p := by
  rw [← beurlingKappa_one (zero_lt_one.trans hp).ne']
  exact beurlingKappa_one_le_beurlingPowNorm_one hp

/-! ### `n = 2` -/

/-- Dragičević's limit (Theorem 1.1, for `p > 2`), `n = 2`:
`‖∂²f_{2,α}‖_p / ‖∂_zbar²f_{2,α}‖_p → κ₂ (p)` as `α → 1/p` from below, for `1 < p < ∞`. -/
theorem tendsto_eLpNorm_div_testFun {p : ℝ} (hp : 1 < p) :
    Tendsto (fun α : ℝ =>
        eLpNorm (dz (dz (testFun 2 α))) (ENNReal.ofReal p) volume /
          eLpNorm (dzbar (dzbar (testFun 2 α))) (ENNReal.ofReal p) volume)
      (𝓝[<] p⁻¹) (𝓝 (ENNReal.ofReal (beurlingKappa 2 p))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpi : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  obtain ⟨C, hC⟩ := exists_bound_testFun_compl_ball hp0
  have h := tendsto_eLpNorm_div_of_lintegral_ball hp (u := fun α => dz (dz (testFun 2 α)))
    (v := fun α => dzbar (dzbar (testFun 2 α))) (a := fun α => (2 - α) * (1 - α))
    (b := fun α => α * (α + 1)) (fun _ => measurable_dz _) (fun _ => measurable_dzbar _)
    (by fun_prop) (by fun_prop)
    (fun α hα => mul_nonneg (by linarith [hα.2]) (by linarith [hα.2]))
    (fun α hα => mul_pos hα.1 (by linarith [hα.1]))
    (fun α hα => lintegral_dz_dz_testFun_ball hp hα.1 (mul_lt_one_of_mem_Ioo_inv hp0 hα))
    (fun α hα => lintegral_dzbar_dzbar_testFun_ball hp hα.1 (mul_lt_one_of_mem_Ioo_inv hp0 hα))
    ⟨C, fun α hα => hC α ⟨hα.1.le, (hα.2.trans hpi).le⟩⟩
  rwa [show (2 - p⁻¹) * (1 - p⁻¹) / (p⁻¹ * (p⁻¹ + 1)) = beurlingKappa 2 p by
    simp only [beurlingKappa, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one,
      one_mul]
    push_cast
    ring] at h

/-- `‖∂²f_{2,α}‖_p / ‖∂_zbar²f_{2,α}‖_p ≤ ‖𝓑²‖_p` for `1 < p < ∞` and `0 < α < 1/p`: Schwartz
approximations of `f_{2,α}` and `𝓑² ∂_zbar² = ∂²` on Schwartz functions. -/
theorem eLpNorm_div_le_beurlingPowNorm_two {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    eLpNorm (dz (dz (testFun 2 α))) (ENNReal.ofReal p) volume /
        eLpNorm (dzbar (dzbar (testFun 2 α))) (ENNReal.ofReal p) volume ≤
      beurlingPowNorm 2 p := by
  obtain ⟨φ, hu, hv⟩ := exists_schwartz_tendsto_testFun hp.le hα0 hα
  exact div_le_beurlingPowNorm_of_tendsto 2 hp.le hu hv

/-- Dragičević's lower bound (Theorem 1.1, for `p > 2`), the case `n = 2`:
`κ₂ (p) ≤ ‖𝓑²‖_{L^p}` for `1 < p < ∞`. -/
theorem beurlingKappa_two_le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 p) ≤ beurlingPowNorm 2 p := by
  refine le_of_tendsto (tendsto_eLpNorm_div_testFun hp) ?_
  filter_upwards [Ioo_mem_nhdsLT (inv_pos.mpr (zero_lt_one.trans hp))] with α hα
  refine eLpNorm_div_le_beurlingPowNorm_two hp hα.1 ?_
  have hp0 : 0 < p := zero_lt_one.trans hp
  calc α * p < p⁻¹ * p := mul_lt_mul_of_pos_right hα.2 hp0
    _ = 1 := inv_mul_cancel₀ hp0.ne'

/-- `κ₂ (p*) ≤ ‖𝓑²‖_{L^p}` for `1 < p < ∞`: for `p < 2`, `‖𝓑²‖_p = ‖𝓑²‖_q`
(Carbonaro–Dragičević–Kovač, §1.3.1) and `p* = q`. -/
theorem beurlingKappa_two_pStar_le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 (pStar p)) ≤ beurlingPowNorm 2 p := by
  rcases le_or_gt 2 p with h2 | h2
  · rw [pStar_of_two_le h2]
    exact beurlingKappa_two_le_beurlingPowNorm_two hp
  · rw [pStar_of_lt_two hp h2, beurlingPowNorm_conjExponent 2 hp]
    exact beurlingKappa_two_le_beurlingPowNorm_two (by rw [lt_div_iff₀ (by linarith)]; linarith)

/-- `(p* − 1)(2p* − 1) / (p* + 1) ≤ ‖𝓑²‖_{L^p}` for `1 < p < ∞`. -/
theorem le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal ((pStar p - 1) * (2 * pStar p - 1) / (pStar p + 1)) ≤ beurlingPowNorm 2 p := by
  have h : 0 < pStar p := lt_of_lt_of_le (by linarith) (le_max_left p _)
  rw [← beurlingKappa_two h]
  exact beurlingKappa_two_pStar_le_beurlingPowNorm_two hp

/-- `p* − 1 < κ₂ (p*)` for `1 < p < ∞`, `p ≠ 2`. -/
theorem pStar_sub_one_lt_beurlingKappa_two {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    pStar p - 1 < beurlingKappa 2 (pStar p) := by
  have h := two_lt_pStar hp hp2
  rw [beurlingKappa_two (by linarith), lt_div_iff₀ (by linarith)]
  nlinarith

/-- `p* − 1 < ‖𝓑²‖_{L^p}` for `1 < p < ∞`, `p ≠ 2`. -/
theorem pStar_sub_one_lt_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    ENNReal.ofReal (pStar p - 1) < beurlingPowNorm 2 p := by
  have h := pStar_sub_one_lt_beurlingKappa_two hp hp2
  refine lt_of_lt_of_le ?_ (beurlingKappa_two_pStar_le_beurlingPowNorm_two hp)
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [two_lt_pStar hp hp2])).mpr h

/-- `21/5 ≤ ‖𝓑²‖_{L⁴}`. -/
theorem twentyOne_div_five_le_beurlingPowNorm_two_four :
    ENNReal.ofReal (21 / 5) ≤ beurlingPowNorm 2 4 := by
  rw [← beurlingKappa_two_four]
  exact beurlingKappa_two_le_beurlingPowNorm_two (by norm_num)

end HarmonicAnalysis

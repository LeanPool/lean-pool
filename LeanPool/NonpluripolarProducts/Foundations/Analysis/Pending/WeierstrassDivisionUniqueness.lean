/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AnalyticProjectionWeierstrass

/-!
# Uniqueness of Weierstrass division

The uniqueness part of the Weierstrass division theorem appears in Gunning–Rossi,
[*Analytic functions of several complex variables*, II.B.3, p. 70](
https://www.math.ens.psl.eu/~benoist/refs/GunningRossi.pdf#page=83). The Lean result is stated for
germs over a complex normed space. It is used for local parametrization.

* `eq_zero_of_eval_eq_mul_eval`: if a polynomial `R` of degree `< deg W`, `W` monic, agrees
  with `h · W` on an open set containing every root of `W`, with `h` continuous there, then
  `R = 0`.  Induction on `deg W`, dividing out one root at a time; at the root itself the
  identity is recovered by continuity.
* `weierstrass_division_unique`: if `q W + ∑_{k<d} r_k(z) t^k = 0` near `0`, for a
  Weierstrass polynomial `W = t^d + ∑_{k<d} a_k(z) t^k`, then all `r_k` and `q` vanish near
  `0`.  For small `z` the roots of `W(z, ·)` lie in a small disc, so the remainder vanishes
  as a polynomial; then `q(z, ·) = 0` off the finitely many roots, hence everywhere.
-/

@[expose] public section

open Filter Topology Polynomial Metric

namespace SGPT.Foundations.Analysis.Pending.WeierstrassDivisionUniqueness

open AnalyticProjectionWeierstrass HolomorphicCoefficientPolynomials

noncomputable section

/-- Two functions continuous at `a` which agree on an open neighbourhood of `a` minus `a`
agree at `a`. -/
theorem eq_at_of_eq_off {U : Set ℂ} (hU : IsOpen U) {a : ℂ} (ha : a ∈ U)
    {f g : ℂ → ℂ} (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (heq : ∀ t ∈ U, t ≠ a → f t = g t) : f a = g a := by
  have hev : f =ᶠ[𝓝[≠] a] g := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds ha), self_mem_nhdsWithin] with t ht hta
    exact heq t ht hta
  exact tendsto_nhds_unique ((hf.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
    (hg.tendsto.mono_left nhdsWithin_le_nhds)

/-- **A remainder divisible by `W` on a neighbourhood of its roots is zero.** -/
theorem eq_zero_of_eval_eq_mul_eval {U : Set ℂ} (hU : IsOpen U) :
    ∀ (d : ℕ) {W R : ℂ[X]}, W.Monic → W.natDegree = d → R.degree < d →
      (∀ a, W.IsRoot a → a ∈ U) → ∀ {h : ℂ → ℂ}, ContinuousOn h U →
        (∀ t ∈ U, R.eval t = h t * W.eval t) → R = 0 := by
  intro d
  induction d with
  | zero =>
      intro W R _ _ hR _ _ _ _
      exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (by simpa using hR))
  | succ d ih =>
      intro W R hW hWd hR hroots h hh heq
      -- `W` has a root `a`, which lies in `U` and is a root of `R`
      obtain ⟨a, ha⟩ := Complex.exists_root (by
        rw [degree_eq_natDegree hW.ne_zero, hWd]; exact_mod_cast Nat.succ_pos d)
      have haU : a ∈ U := hroots a ha
      have hRa : R.IsRoot a := by
        rw [IsRoot, heq a haU, ha.eq_zero, mul_zero]
      -- divide both by `X - a`
      set W' := W /ₘ (X - C a) with hW'
      set R' := R /ₘ (X - C a) with hR'
      have hWfac : (X - C a) * W' = W := mul_divByMonic_eq_iff_isRoot.mpr ha
      have hRfac : (X - C a) * R' = R := mul_divByMonic_eq_iff_isRoot.mpr hRa
      have hW'monic : W'.Monic := by
        have := hW
        rw [← hWfac] at this
        exact (monic_X_sub_C a).of_mul_monic_left this
      have hW'deg : W'.natDegree = d := by
        have := congrArg natDegree hWfac
        rw [(monic_X_sub_C a).natDegree_mul hW'monic, natDegree_X_sub_C, hWd] at this
        omega
      have hR'deg : R'.degree < d := by
        by_cases hR0 : R' = 0
        · rw [hR0, degree_zero]; exact WithBot.bot_lt_coe d
        · have hR0' : R ≠ 0 := by
            rw [← hRfac]; exact mul_ne_zero (X_sub_C_ne_zero a) hR0
          have := congrArg natDegree hRfac
          rw [natDegree_mul (X_sub_C_ne_zero a) hR0, natDegree_X_sub_C] at this
          rw [degree_eq_natDegree hR0]
          have hRlt : R.natDegree < d + 1 := by
            have := hR
            rw [degree_eq_natDegree hR0'] at this
            exact_mod_cast this
          exact_mod_cast (by omega : R'.natDegree < d)
      have hroots' : ∀ b, W'.IsRoot b → b ∈ U := by
        intro b hb
        apply hroots
        rw [← hWfac, IsRoot, eval_mul, hb.eq_zero, mul_zero]
      have heq' : ∀ t ∈ U, R'.eval t = h t * W'.eval t := by
        intro t ht
        by_cases hta : t = a
        · subst hta
          refine eq_at_of_eq_off hU ht (R'.continuous.continuousAt)
            ((hh.continuousAt (hU.mem_nhds ht)).mul W'.continuous.continuousAt) ?_
          intro s hs hst
          have h1 := heq s hs
          rw [← hRfac, ← hWfac, eval_mul, eval_mul, eval_sub, eval_X, eval_C] at h1
          have hne : s - t ≠ 0 := sub_ne_zero.mpr hst
          apply mul_left_cancel₀ hne
          simp only [Pi.mul_apply]
          rw [h1]
          ring
        · have h1 := heq t ht
          rw [← hRfac, ← hWfac, eval_mul, eval_mul, eval_sub, eval_X, eval_C] at h1
          have hne : t - a ≠ 0 := sub_ne_zero.mpr hta
          apply mul_left_cancel₀ hne
          rw [h1]
          ring
      have := ih hW'monic hW'deg hR'deg hroots' hh heq'
      rw [← hRfac, this, mul_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Uniqueness of Weierstrass division.**  If `q W + ∑_{k<d} r_k(z) t^k = 0` near `0` for
the Weierstrass polynomial `W = t^d + ∑_{k<d} a_k(z) t^k` (`a_k` holomorphic, `a_k(0) = 0`)
and `q` holomorphic, then every `r_k` and `q` vanish near `0`. -/
theorem weierstrass_division_unique {d : ℕ} {a : ℕ → E → ℂ}
    (ha : ∀ k, ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (a k) z) (ha0 : ∀ k < d, a k 0 = 0)
    {q : E × ℂ → ℂ} (hq : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ q x) {r : ℕ → E → ℂ}
    (h : ∀ᶠ x in 𝓝 (0 : E × ℂ),
      q x * weierstrassFun d a x + ∑ k ∈ Finset.range d, r k x.1 * x.2 ^ k = 0) :
    (∀ k < d, ∀ᶠ z in 𝓝 (0 : E), r k z = 0) ∧ ∀ᶠ x in 𝓝 (0 : E × ℂ), q x = 0 := by
  obtain ⟨r1, hr1, hball1⟩ := Metric.mem_nhds_iff.mp (hq.and h)
  set ε : ℝ := min r1 1 with hεdef
  have hε : 0 < ε := lt_min hr1 one_pos
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε21 : ε / 2 ≤ 1 := by
    have := min_le_right r1 1
    linarith
  have hN2 : ∀ᶠ z in 𝓝 (0 : E), ∀ k ∈ Finset.range d, ‖a k z‖ * d < (ε / 2) ^ d := by
    refine (eventually_all_finset _).mpr fun k hk => ?_
    have hc : ContinuousAt (fun z => ‖a k z‖ * d) 0 :=
      (continuousAt_zero_of_eventually_differentiableAt (ha k)).norm.mul continuousAt_const
    refine hc.eventually_lt continuousAt_const ?_
    simp only [ha0 k (Finset.mem_range.mp hk), norm_zero, zero_mul]
    exact pow_pos hε2 d
  obtain ⟨r2, hr2, hball2⟩ := Metric.mem_nhds_iff.mp hN2
  set δ : ℝ := min r1 r2 with hδdef
  have hδ : 0 < δ := lt_min hr1 hr2
  set U : Set ℂ := ball (0 : ℂ) ε with hUdef
  have hmem : ∀ z ∈ ball (0 : E) δ, ∀ t ∈ U, ((z, t) : E × ℂ) ∈ ball (0 : E × ℂ) r1 := by
    intro z hz t ht
    rw [mem_ball_zero_iff, Prod.norm_def]
    exact max_lt ((mem_ball_zero_iff.mp hz).trans_le (min_le_left _ _))
      ((mem_ball_zero_iff.mp ht).trans_le (min_le_left _ _))
  -- the polynomial picture over a fixed small `z`
  have key : ∀ z ∈ ball (0 : E) δ, (∀ k < d, r k z = 0) ∧ ∀ t ∈ U, q (z, t) = 0 := by
    intro z hz
    set Wz : ℂ[X] := X ^ d + ∑ k ∈ Finset.range d, C (a k z) * X ^ k with hWz
    set Rz : ℂ[X] := ∑ k ∈ Finset.range d, C (r k z) * X ^ k with hRz
    obtain ⟨hWm, hWd⟩ := monic_X_pow_add_sum d fun k => a k z
    have hWeval : ∀ t, Wz.eval t = weierstrassFun d a (z, t) := by
      intro t
      simp [Wz, weierstrassFun, eval_finsetSum]
    have hReval : ∀ t, Rz.eval t = ∑ k ∈ Finset.range d, r k z * t ^ k := by
      intro t
      simp [Rz, eval_finsetSum]
    have hroots : ∀ t, Wz.IsRoot t → t ∈ U := by
      intro t ht
      have hW : weierstrassFun d a (z, t) = 0 := by rw [← hWeval]; exact ht
      have := norm_lt_of_weierstrass_root hε2 hε21
        (fun k hk => hball2 (ball_subset_ball (min_le_right _ _) hz) k
          (Finset.mem_range.mpr hk)) hW
      exact mem_ball_zero_iff.mpr (by linarith)
    have hcont : ContinuousOn (fun t => -q (z, t)) U := by
      intro t ht
      have hd := (hball1 (hmem z hz t ht)).1
      exact (hd.continuousAt.comp (by fun_prop : ContinuousAt (fun t : ℂ => (z, t)) t)).neg
        |>.continuousWithinAt
    have hid : ∀ t ∈ U, Rz.eval t = -q (z, t) * Wz.eval t := by
      intro t ht
      have := (hball1 (hmem z hz t ht)).2
      rw [hReval, hWeval]
      simp only at this
      linear_combination this
    have hR0 := eq_zero_of_eval_eq_mul_eval isOpen_ball d hWm hWd
      (degree_sum_range_lt d _) hroots hcont hid
    have hr0 : ∀ k < d, r k z = 0 := by
      intro k hk
      have := congrArg (fun P : ℂ[X] => P.coeff k) hR0
      simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
      rwa [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hk)] at this
    refine ⟨hr0, fun t ht => ?_⟩
    have hqW : ∀ s ∈ U, q (z, s) * Wz.eval s = 0 := by
      intro s hs
      have := (hball1 (hmem z hz s hs)).2
      simp only at this
      rw [hWeval]
      rwa [Finset.sum_eq_zero fun k hk => by rw [hr0 k (Finset.mem_range.mp hk), zero_mul],
        add_zero] at this
    -- off the finitely many roots `q (z, ·)` vanishes; conclude by continuity
    have hfin : (Wz.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
    have hnear : ∀ᶠ s in 𝓝[≠] t, Wz.eval s ≠ 0 := by
      have hcl : IsClosed ((Wz.roots.toFinset : Set ℂ) \ {t}) := (hfin.sdiff).isClosed
      have hnt : t ∉ (Wz.roots.toFinset : Set ℂ) \ {t} := fun h => h.2 rfl
      filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds hnt),
        self_mem_nhdsWithin] with s hs hst
      intro hs0
      exact hs ⟨Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((mem_roots hWm.ne_zero).mpr hs0)),
        hst⟩
    have hct : ContinuousAt (fun s => q (z, s)) t :=
      (hball1 (hmem z hz t ht)).1.continuousAt.comp
        (by fun_prop : ContinuousAt (fun s : ℂ => (z, s)) t)
    have hev : ∀ᶠ s in 𝓝[≠] t, q (z, s) = 0 := by
      filter_upwards [hnear, nhdsWithin_le_nhds (isOpen_ball.mem_nhds ht)] with s hs hsU
      exact (mul_eq_zero.mp (hqW s hsU)).resolve_right hs
    exact tendsto_nhds_unique (hct.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  refine ⟨fun k hk => ?_, ?_⟩
  · filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz
    exact (key z hz).1 k hk
  · have hprod : ball (0 : E) δ ×ˢ U ∈ 𝓝 ((0 : E), (0 : ℂ)) :=
      prod_mem_nhds (ball_mem_nhds _ hδ) (ball_mem_nhds _ hε)
    rw [Prod.mk_zero_zero] at hprod
    filter_upwards [hprod] with x hx
    exact (key x.1 hx.1).2 x.2 hx.2

end

end SGPT.Foundations.Analysis.Pending.WeierstrassDivisionUniqueness

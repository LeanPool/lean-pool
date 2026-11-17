/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RegularVariation.Potter

/-!
# Analytic consequences of regular variation of the normalizing sequence

Consequences of regular variation of `(a_n)` used in the source (lines 1015–1050, 1080–1110,
1136–1251, 1747–1790, 2233–2298), for a monotone `a : ℕ → ℝ`, positive at `n ≥ 1`, with
`RegularlyVaryingSeq ρ a`:

* `tendsto_ratio_of_tendsto_div`: if `k n / n → c > 0` then `a (k n) / a n → c ^ ρ`
  (covers `a_{⌊εn⌋}/a_n → ε^ρ`, `a_{n-o(n)}/a_n → 1`, `a_{n-1}/a_n → 1`).
* `eventually_rpow_le_le`: `a_n = n^{ρ+o(1)}`.
* `tendsto_div_self`, `tendsto_atTop`, `exists_le_mul`, `exists_le_mul_of_le_mul`:
  `a_n = o(n)`, `a_n → ∞`, `a_n ≤ C n`, and `a_y ≤ C a_x` whenever `y ≤ K x`.
* `tendsto_ratio_zero_of_isLittleO`: `M_n = o(n)` gives `a_{M_n} / a_n → 0`.
* `tendsto_sub_ratio`, `tendsto_add_ratio`, `eventually_uniform_sub_add`:
  `a_{n ∓ m_n} / a_n → 1` for `m_n = o(n)`, uniformly over `m ≤ M_n`.
* `tendsto_sqrt_div`: for `r_n = √(a_{M_n} a_n)`, `r_n / a_{M_n} → ∞` and `r_n / a_n → 0`.
* `eventually_floor_rpow_bounds`, `eventually_floor_rpow_div_le`,
  `eventually_div_floor_rpow_le`: polynomial cutoffs `M_n = ⌊n^θ⌋₊`.
* `tendsto_mul_div_floor_rpow`, `tendsto_div_floor_rpow`: the two limits in the proof of
  Lemma `lem:critM` (source lines 1087–1105), for an `n^{o(1)}` numerator.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PoissonDeclumping

/-- `⌊x⌋₊ ≥ x / 2` for `x ≥ 1`. -/
theorem half_le_natFloor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    exact_mod_cast Nat.le_floor (by simpa using hx)
  linarith

/-- If `0 ≤ f n ≤ C n ^ γ` eventually along `l ≤ atTop`, with `γ < 0`, then `f → 0` along `l`. -/
theorem tendsto_zero_of_le_mul_rpow {l : Filter ℕ} (hl : l ≤ atTop) {f : ℕ → ℝ} {C γ : ℝ}
    (hγ : γ < 0) (h0 : ∀ᶠ n in l, 0 ≤ f n) (h : ∀ᶠ n in l, f n ≤ C * (n : ℝ) ^ γ) :
    Tendsto f l (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => C * (n : ℝ) ^ γ) atTop (𝓝 (C * 0)) := by
    have := (tendsto_rpow_neg_atTop (neg_pos.2 hγ)).comp tendsto_natCast_atTop_atTop
    simp only [neg_neg] at this
    exact tendsto_const_nhds.mul this
  rw [mul_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ht.mono_left hl) h0 h

namespace RegularlyVaryingSeq

variable {ρ : ℝ} {a : ℕ → ℝ}

/-- If `k n / n → c > 0`, then `a (k n) / a n → c ^ ρ`. -/
theorem tendsto_ratio_of_tendsto_div (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {k : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => a (k n) / a n) atTop (𝓝 (c ^ ρ)) := by
  have hcont : Tendsto (fun x : ℝ => x ^ ρ) (𝓝 c) (𝓝 (c ^ ρ)) :=
    (Real.continuousAt_rpow_const c ρ (Or.inl hc.ne')).tendsto
  rw [tendsto_order]
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[<] c, l < x ^ ρ :=
      (hcont.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hl)
    have h2 : ∀ᶠ x in 𝓝[<] c, 0 < x :=
      nhdsWithin_le_nhds (lt_mem_nhds hc)
    have h3 : ∀ᶠ x in 𝓝[<] c, x < c := self_mem_nhdsWithin
    obtain ⟨c', hc'l, hc'0, hc'c⟩ := (h1.and (h2.and h3)).exists
    have e1 := (hrv c' hc'0).eventually (lt_mem_nhds hc'l)
    have e2 := hk.eventually (lt_mem_nhds hc'c)
    filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn1
    have han := hpos n hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hfl : ⌊c' * n⌋₊ ≤ k n := by
      apply Nat.floor_le_of_le
      have := (lt_div_iff₀ hnR).1 h2
      linarith
    calc l < a ⌊c' * n⌋₊ / a n := h1
      _ ≤ a (k n) / a n := div_le_div_of_nonneg_right (hmono hfl) han.le
  · have h1 : ∀ᶠ x in 𝓝[>] c, x ^ ρ < u :=
      (hcont.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hu)
    have h3 : ∀ᶠ x in 𝓝[>] c, c < x := self_mem_nhdsWithin
    obtain ⟨c'', hc''u, hcc''⟩ := (h1.and h3).exists
    have hc''0 : 0 < c'' := hc.trans hcc''
    have e1 := (hrv c'' hc''0).eventually (gt_mem_nhds hc''u)
    have e2 := hk.eventually (gt_mem_nhds hcc'')
    filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn1
    have han := hpos n hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hfl : k n ≤ ⌊c'' * n⌋₊ := by
      apply Nat.le_floor
      have := (div_lt_iff₀ hnR).1 h2
      linarith
    calc a (k n) / a n ≤ a ⌊c'' * n⌋₊ / a n := div_le_div_of_nonneg_right (hmono hfl) han.le
      _ < u := h1

/-- For fixed `ε > 0`, `a ⌊ε n⌋₊ / a n → ε ^ ρ` (the definition, restated). -/
theorem tendsto_floor_mul (hrv : RegularlyVaryingSeq ρ a) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => a ⌊ε * n⌋₊ / a n) atTop (𝓝 (ε ^ ρ)) :=
  hrv ε hε

/-- `a_n = n^{ρ + o(1)}`: for every `δ > 0`, eventually `n^(ρ-δ) ≤ a n ≤ n^(ρ+δ)`. -/
theorem eventually_rpow_le_le (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (ρ - δ) ≤ a n ∧ a n ≤ (n : ℝ) ^ (ρ + δ) := by
  obtain ⟨C, hC, hCb⟩ := hrv.exists_potter_global hmono hpos hρ (half_pos hδ)
  have ha1 : 0 < a 1 := hpos 1 le_rfl
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (max (C * a 1) (C / a 1)), eventually_ge_atTop 1]
    with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hu, hl⟩ := hCb 1 n le_rfl hn1
  simp only [Nat.cast_one, div_one] at hu hl
  have hsplit1 : (n : ℝ) ^ (ρ + δ) = (n : ℝ) ^ (ρ + δ / 2) * (n : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hsplit2 : (n : ℝ) ^ (ρ - δ / 2) = (n : ℝ) ^ (ρ - δ) * (n : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hp2 : 0 < (n : ℝ) ^ (ρ - δ) := by positivity
  have hn1' : C * a 1 ≤ (n : ℝ) ^ (δ / 2) := le_trans (le_max_left _ _) hn
  have hn2' : C / a 1 ≤ (n : ℝ) ^ (δ / 2) := le_trans (le_max_right _ _) hn
  constructor
  · rw [hsplit2] at hl
    have hC' : C ≤ (n : ℝ) ^ (δ / 2) * a 1 := by rwa [div_le_iff₀ ha1] at hn2'
    have h3 : C * (n : ℝ) ^ (ρ - δ) ≤ C * a n :=
      calc C * (n : ℝ) ^ (ρ - δ) ≤ ((n : ℝ) ^ (δ / 2) * a 1) * (n : ℝ) ^ (ρ - δ) :=
            mul_le_mul_of_nonneg_right hC' hp2.le
        _ = (n : ℝ) ^ (ρ - δ) * (n : ℝ) ^ (δ / 2) * a 1 := by ring
        _ ≤ C * a n := hl
    exact le_of_mul_le_mul_left h3 hC
  · calc a n ≤ C * (n : ℝ) ^ (ρ + δ / 2) * a 1 := hu
      _ = (n : ℝ) ^ (ρ + δ / 2) * (C * a 1) := by ring
      _ ≤ (n : ℝ) ^ (ρ + δ / 2) * (n : ℝ) ^ (δ / 2) :=
          mul_le_mul_of_nonneg_left hn1' (by positivity)
      _ = (n : ℝ) ^ (ρ + δ) := hsplit1.symm

/-- `a n → ∞` (positive index). -/
theorem tendsto_atTop (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) : Tendsto a atTop atTop := by
  have h := hrv.eventually_rpow_le_le hmono hpos hρ.le (half_pos hρ)
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (ρ - ρ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' atTop (h.mono fun n hn => hn.1) htend

/-- `a_n = o(n)` (index `ρ < 1`): `a n / n → 0`. -/
theorem tendsto_div_self (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℕ => a n / n) atTop (𝓝 0) := by
  have hδ : 0 < (1 - ρ) / 2 := by linarith
  have h := hrv.eventually_rpow_le_le hmono hpos hρ0 hδ
  apply tendsto_zero_of_le_mul_rpow le_rfl (C := 1) (γ := -((1 - ρ) / 2)) (by linarith)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (hpos n hn).le (Nat.cast_nonneg _)
  · filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_le_iff₀ hnR, one_mul, ← Real.rpow_add_one hnR.ne']
    calc a n ≤ (n : ℝ) ^ (ρ + (1 - ρ) / 2) := hn.2
      _ = (n : ℝ) ^ (-((1 - ρ) / 2) + 1) := by congr 1; ring

/-- `a n ≤ C n` for all `n ≥ 1` (index `ρ < 1`). -/
theorem exists_le_mul (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → a n ≤ C * n := by
  obtain ⟨C, hC, hCb⟩ := hrv.exists_potter_global hmono hpos hρ0 (sub_pos.2 hρ1)
  have ha1 : 0 < a 1 := hpos 1 le_rfl
  refine ⟨C * a 1, by positivity, fun n hn => ?_⟩
  have h := (hCb 1 n le_rfl hn).1
  rw [show ρ + (1 - ρ) = 1 by ring, Real.rpow_one, Nat.cast_one, div_one] at h
  linarith

/-- Comparability: for every `K`, there is `C > 0` with `a y ≤ C a x` whenever `1 ≤ x` and
`y ≤ K x` (e.g. `a_q ≍ a_n` for `n/2 ≤ q ≤ n`). -/
theorem exists_le_mul_of_le_mul (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ, 1 ≤ x → (y : ℝ) ≤ K * x → a y ≤ C * a x := by
  obtain ⟨C, hC, hCb⟩ := hrv.exists_potter_global hmono hpos hρ one_pos
  set K' : ℝ := max K 1
  refine ⟨max 1 (C * K' ^ (ρ + 1)), lt_max_of_lt_left one_pos, fun x y hx hyK => ?_⟩
  have hax := hpos x hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  rcases le_total y x with hyx | hxy
  · calc a y ≤ a x := hmono hyx
      _ = 1 * a x := (one_mul _).symm
      _ ≤ max 1 (C * K' ^ (ρ + 1)) * a x := by gcongr; exact le_max_left _ _
  · have h := (hCb x y hx hxy).1
    have hq : (y : ℝ) / x ≤ K' := by
      rw [div_le_iff₀ hxR]
      exact hyK.trans (by gcongr; exact le_max_left _ _)
    have hpow : ((y : ℝ) / x) ^ (ρ + 1) ≤ K' ^ (ρ + 1) :=
      Real.rpow_le_rpow (by positivity) hq (by linarith)
    calc a y ≤ C * ((y : ℝ) / x) ^ (ρ + 1) * a x := h
      _ ≤ C * K' ^ (ρ + 1) * a x := by gcongr
      _ ≤ max 1 (C * K' ^ (ρ + 1)) * a x := by gcongr; exact le_max_right _ _

/-- If `M_n = o(n)` then `a (M n) / a n → 0` (positive index). -/
theorem tendsto_ratio_zero_of_isLittleO (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) {M : ℕ → ℕ}
    (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    Tendsto (fun n => a (M n) / a n) atTop (𝓝 0) := by
  have hMr : Tendsto (fun n => (M n : ℝ) / n) atTop (𝓝 0) := hM.tendsto_div_nhds_zero
  have ha0 : Tendsto (fun n => a 0 / a n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hrv.tendsto_atTop hmono hpos hρ)
  rw [tendsto_order]
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · filter_upwards [ha0.eventually (lt_mem_nhds hl), eventually_ge_atTop 1] with n hn hn1
    calc l < a 0 / a n := hn
      _ ≤ a (M n) / a n := div_le_div_of_nonneg_right (hmono (Nat.zero_le _)) (hpos n hn1).le
  · set c : ℝ := (u / 2) ^ (1 / ρ) with hcdef
    have hc : 0 < c := by positivity
    have hcρ : c ^ ρ = u / 2 := by
      rw [hcdef, ← Real.rpow_mul (by linarith), one_div_mul_cancel hρ.ne', Real.rpow_one]
    have e1 := (hrv c hc).eventually (gt_mem_nhds (show c ^ ρ < u by rw [hcρ]; linarith))
    have e2 := hMr.eventually (gt_mem_nhds hc)
    filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hMn : M n ≤ ⌊c * n⌋₊ := by
      apply Nat.le_floor
      have := (div_lt_iff₀ hnR).1 h2
      linarith
    calc a (M n) / a n ≤ a ⌊c * n⌋₊ / a n :=
          div_le_div_of_nonneg_right (hmono hMn) (hpos n hn1).le
      _ < u := h1

/-- `a_{n - m_n} / a_n → 1` for `m_n = o(n)` (natural subtraction). -/
theorem tendsto_sub_ratio (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {m : ℕ → ℕ}
    (hm : (fun n => (m n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    Tendsto (fun n => a (n - m n) / a n) atTop (𝓝 1) := by
  have hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 0) := hm.tendsto_div_nhds_zero
  have hk : Tendsto (fun n : ℕ => ((n - m n : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => 1 - (m n : ℝ) / n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hmr
    rw [sub_zero] at hlow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : (n : ℝ) ≤ ((n - m n : ℕ) : ℝ) + m n := by exact_mod_cast le_tsub_add
      rw [one_sub_div hnR.ne', div_le_div_iff_of_pos_right hnR]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_one hnR]
      exact_mod_cast Nat.sub_le n (m n)
  have := hrv.tendsto_ratio_of_tendsto_div hmono hpos one_pos hk
  rwa [Real.one_rpow] at this

/-- `a_{n + m_n} / a_n → 1` for `m_n = o(n)`. -/
theorem tendsto_add_ratio (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {m : ℕ → ℕ}
    (hm : (fun n => (m n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    Tendsto (fun n => a (n + m n) / a n) atTop (𝓝 1) := by
  have hmr : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 0) := hm.tendsto_div_nhds_zero
  have hk : Tendsto (fun n : ℕ => ((n + m n : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) + (m n : ℝ) / n) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hmr
    rw [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have := hrv.tendsto_ratio_of_tendsto_div hmono hpos one_pos hk
  rwa [Real.one_rpow] at this

/-- Uniform version: for `M_n = o(n)` and `ε > 0`, eventually for all `j ≤ M n`,
`(1-ε) a n ≤ a (n-j) ≤ a n ≤ a (n+j) ≤ (1+ε) a n`. -/
theorem eventually_uniform_sub_add (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {M : ℕ → ℕ}
    (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ M n →
      (1 - ε) * a n ≤ a (n - j) ∧ a (n - j) ≤ a n ∧ a n ≤ a (n + j) ∧
        a (n + j) ≤ (1 + ε) * a n := by
  have h1 := (hrv.tendsto_sub_ratio hmono hpos hM).eventually
    (lt_mem_nhds (show 1 - ε < 1 by linarith))
  have h2 := (hrv.tendsto_add_ratio hmono hpos hM).eventually
    (gt_mem_nhds (show 1 < 1 + ε by linarith))
  filter_upwards [h1, h2, eventually_ge_atTop 1] with n h1 h2 hn1 j hj
  have han := hpos n hn1
  rw [lt_div_iff₀ han] at h1
  rw [div_lt_iff₀ han] at h2
  refine ⟨?_, hmono (Nat.sub_le _ _), hmono (Nat.le_add_right _ _), ?_⟩
  · calc (1 - ε) * a n ≤ a (n - M n) := h1.le
      _ ≤ a (n - j) := hmono (by omega)
  · calc a (n + j) ≤ a (n + M n) := hmono (by omega)
      _ ≤ (1 + ε) * a n := h2.le

/-- Source lines 1747–1750: with `r_n = √(a_{M_n} a_n)`, `M_n → ∞` and `M_n = o(n)`,
`r_n / a_{M_n} → ∞` and `r_n / a_n → 0`. -/
theorem tendsto_sqrt_div (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) {M : ℕ → ℕ}
    (hMtop : Tendsto M atTop atTop)
    (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    Tendsto (fun n => √(a (M n) * a n) / a (M n)) atTop atTop ∧
      Tendsto (fun n => √(a (M n) * a n) / a n) atTop (𝓝 0) := by
  have hr := hrv.tendsto_ratio_zero_of_isLittleO hmono hpos hρ hM
  have hev : ∀ᶠ n in atTop, 1 ≤ M n ∧ 1 ≤ n :=
    (hMtop.eventually_ge_atTop 1).and (eventually_ge_atTop 1)
  have hsq : ∀ x y : ℝ, 0 < x → 0 < y → √(x * y) / y = √(x / y) := by
    intro x y hx hy
    have hsy : 0 < √y := Real.sqrt_pos.2 hy
    rw [Real.sqrt_mul hx.le, Real.sqrt_div hx.le]
    field_simp
    exact Real.sq_sqrt hy.le
  constructor
  · have hr' : Tendsto (fun n => a (M n) / a n) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hr, ?_⟩
      filter_upwards [hev] with n hn
      exact div_pos (hpos _ hn.1) (hpos _ hn.2)
    have hinv := hr'.inv_tendsto_nhdsGT_zero
    have hinv' : Tendsto (fun n => a n / a (M n)) atTop atTop := by
      refine hinv.congr' (Eventually.of_forall fun n => ?_)
      simp only [Pi.inv_apply, inv_div]
    refine (Real.tendsto_sqrt_atTop.comp hinv').congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp_apply]
    rw [mul_comm, hsq _ _ (hpos _ hn.2) (hpos _ hn.1)]
  · have h0 : Tendsto (fun n => √(a (M n) / a n)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hr
      rwa [Real.sqrt_zero] at this
    refine h0.congr' ?_
    filter_upwards [hev] with n hn
    rw [hsq _ _ (hpos _ hn.1) (hpos _ hn.2)]

/-- Polynomial cutoffs: for `θ > 0` and `δ > 0`, eventually
`n^(θρ - δ) ≤ a ⌊n^θ⌋₊ ≤ n^(θρ + δ)`, i.e. `a_{⌊n^θ⌋} = n^{θρ + o(1)}`. -/
theorem eventually_floor_rpow_bounds (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (θ * ρ - δ) ≤ a ⌊(n : ℝ) ^ θ⌋₊ ∧
      a ⌊(n : ℝ) ^ θ⌋₊ ≤ (n : ℝ) ^ (θ * ρ + δ) := by
  set δ' : ℝ := min (δ / (2 * θ)) ρ with hδ'def
  have hδ' : 0 < δ' := lt_min (by positivity) hρ
  have hδ'1 : δ' ≤ δ / (2 * θ) := min_le_left _ _
  have hδ'2 : δ' ≤ ρ := min_le_right _ _
  have hθδ' : θ * δ' ≤ δ / 2 :=
    calc θ * δ' ≤ θ * (δ / (2 * θ)) := by gcongr
      _ = δ / 2 := by field_simp
  have hpowtend : Tendsto (fun n : ℕ => (n : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hMtop : Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ θ⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hpowtend
  have hA := hMtop.eventually (hrv.eventually_rpow_le_le hmono hpos hρ.le hδ')
  have hδ2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hA, hδ2.eventually_ge_atTop ((2 : ℝ) ^ ρ), eventually_ge_atTop 1]
    with n hA hn2 hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hx1 : 1 ≤ (n : ℝ) ^ θ := Real.one_le_rpow hnR hθ.le
  have hM_le : (⌊(n : ℝ) ^ θ⌋₊ : ℝ) ≤ (n : ℝ) ^ θ := Nat.floor_le (by positivity)
  have hM_ge : (n : ℝ) ^ θ / 2 ≤ (⌊(n : ℝ) ^ θ⌋₊ : ℝ) := half_le_natFloor hx1
  constructor
  · have e1 : (n : ℝ) ^ (θ * (ρ - δ')) = (n : ℝ) ^ (θ * ρ - δ) * (n : ℝ) ^ (δ - θ * δ') := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have e2 : (n : ℝ) ^ (δ / 2) ≤ (n : ℝ) ^ (δ - θ * δ') :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have e3 : (2 : ℝ) ^ (ρ - δ') ≤ (2 : ℝ) ^ ρ :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc (n : ℝ) ^ (θ * ρ - δ) ≤ (n : ℝ) ^ (θ * (ρ - δ')) / (2 : ℝ) ^ (ρ - δ') := by
          rw [le_div_iff₀ (by positivity), e1]
          exact mul_le_mul_of_nonneg_left (e3.trans (hn2.trans e2)) (by positivity)
      _ = ((n : ℝ) ^ θ / 2) ^ (ρ - δ') := by
          rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hn0.le]
      _ ≤ (⌊(n : ℝ) ^ θ⌋₊ : ℝ) ^ (ρ - δ') :=
          Real.rpow_le_rpow (by positivity) hM_ge (by linarith)
      _ ≤ a ⌊(n : ℝ) ^ θ⌋₊ := hA.1
  · calc a ⌊(n : ℝ) ^ θ⌋₊ ≤ (⌊(n : ℝ) ^ θ⌋₊ : ℝ) ^ (ρ + δ') := hA.2
      _ ≤ ((n : ℝ) ^ θ) ^ (ρ + δ') := Real.rpow_le_rpow (Nat.cast_nonneg _) hM_le (by linarith)
      _ = (n : ℝ) ^ (θ * ρ + θ * δ') := by
          rw [← Real.rpow_mul hn0.le]
          congr 1
          ring
      _ ≤ (n : ℝ) ^ (θ * ρ + δ) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)

/-- Polynomial cutoff `M_n = ⌊n^(1-η)⌋₊`, `η < 1`: for every `δ > 0`, eventually
`a_{M_n} / a_n ≤ n^(-ρη + δ)`. -/
theorem eventually_floor_rpow_div_le (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) {η δ : ℝ} (hη : η < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, a ⌊(n : ℝ) ^ (1 - η)⌋₊ / a n ≤ (n : ℝ) ^ (-(ρ * η) + δ) := by
  filter_upwards [hrv.eventually_floor_rpow_bounds hmono hpos hρ (sub_pos.2 hη) (half_pos hδ),
    hrv.eventually_rpow_le_le hmono hpos hρ.le (half_pos hδ), eventually_ge_atTop 1]
    with n h1 h2 hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have han := hpos n hn1
  rw [div_le_iff₀ han]
  calc a ⌊(n : ℝ) ^ (1 - η)⌋₊ ≤ (n : ℝ) ^ ((1 - η) * ρ + δ / 2) := h1.2
    _ = (n : ℝ) ^ (-(ρ * η) + δ) * (n : ℝ) ^ (ρ - δ / 2) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
    _ ≤ (n : ℝ) ^ (-(ρ * η) + δ) * a n := mul_le_mul_of_nonneg_left h2.1 (by positivity)

/-- Polynomial cutoff `M_n = ⌊n^θ⌋₊`, `θ > 0`: for every `δ > 0`, eventually
`a_n / M_n ≤ n^(ρ - θ + δ)`. -/
theorem eventually_div_floor_rpow_le (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, a n / (⌊(n : ℝ) ^ θ⌋₊ : ℝ) ≤ (n : ℝ) ^ (ρ - θ + δ) := by
  have hδ2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hrv.eventually_rpow_le_le hmono hpos hρ (half_pos hδ),
    hδ2.eventually_ge_atTop 2, eventually_ge_atTop 1] with n h1 h2 hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hx1 : 1 ≤ (n : ℝ) ^ θ := Real.one_le_rpow hnR hθ.le
  have hM_ge : (n : ℝ) ^ θ / 2 ≤ (⌊(n : ℝ) ^ θ⌋₊ : ℝ) := half_le_natFloor hx1
  have hMpos : (0 : ℝ) < (⌊(n : ℝ) ^ θ⌋₊ : ℝ) := by
    have : (0 : ℝ) < (n : ℝ) ^ θ / 2 := by positivity
    linarith
  have e : (n : ℝ) ^ (ρ + δ / 2) * (n : ℝ) ^ (δ / 2) = (n : ℝ) ^ (ρ - θ + δ) * (n : ℝ) ^ θ := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1
    ring
  rw [div_le_iff₀ hMpos]
  calc a n ≤ (n : ℝ) ^ (ρ + δ / 2) := h1.2
    _ ≤ (n : ℝ) ^ (ρ + δ / 2) * ((n : ℝ) ^ (δ / 2) / 2) :=
        le_mul_of_one_le_right (by positivity) (by rw [le_div_iff₀ (by norm_num)]; linarith)
    _ = ((n : ℝ) ^ (ρ + δ / 2) * (n : ℝ) ^ (δ / 2)) / 2 := by ring
    _ = (n : ℝ) ^ (ρ - θ + δ) * ((n : ℝ) ^ θ / 2) := by rw [e]; ring
    _ ≤ (n : ℝ) ^ (ρ - θ + δ) * (⌊(n : ℝ) ^ θ⌋₊ : ℝ) :=
        mul_le_mul_of_nonneg_left hM_ge (by positivity)

/-- Lemma `lem:critM` (source lines 1090–1097): if `η < 1 - ρ`, `ε > 0`, and `e_n ≥ 0` is
`n^{o(1)}` along a filter `l ≤ atTop`, then `a_n e_n / (ε ⌊n^(1-η)⌋₊) → 0` along `l`. -/
theorem tendsto_mul_div_floor_rpow (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {η : ℝ} (hη : η < 1 - ρ)
    {l : Filter ℕ} (hl : l ≤ atTop) {e : ℕ → ℝ} (he0 : ∀ᶠ n in l, 0 ≤ e n)
    (he : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in l, e n ≤ (n : ℝ) ^ δ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => a n * e n / (ε * (⌊(n : ℝ) ^ (1 - η)⌋₊ : ℝ))) l (𝓝 0) := by
  set δ : ℝ := (1 - ρ - η) / 3 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hθ : 0 < 1 - η := by linarith
  have h1 := hrv.eventually_div_floor_rpow_le hmono hpos hρ hθ hδ
  apply tendsto_zero_of_le_mul_rpow hl (C := 1 / ε) (γ := -δ) (by linarith)
  · filter_upwards [he0, hl (eventually_ge_atTop 1)] with n hn hn1
    exact div_nonneg (mul_nonneg (hpos n hn1).le hn) (by positivity)
  · filter_upwards [he0, he δ hδ, hl h1, hl (eventually_ge_atTop 1)] with n he0n hen h1n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hx1 : 1 ≤ (n : ℝ) ^ (1 - η) := Real.one_le_rpow (by exact_mod_cast hn1) hθ.le
    have hMpos : (0 : ℝ) < (⌊(n : ℝ) ^ (1 - η)⌋₊ : ℝ) := by
      have := half_le_natFloor hx1
      have : (0 : ℝ) < (n : ℝ) ^ (1 - η) / 2 := by positivity
      linarith
    have han := hpos n hn1
    calc a n * e n / (ε * (⌊(n : ℝ) ^ (1 - η)⌋₊ : ℝ))
        = (a n / (⌊(n : ℝ) ^ (1 - η)⌋₊ : ℝ)) * e n / ε := by field_simp
      _ ≤ (n : ℝ) ^ (ρ - (1 - η) + δ) * (n : ℝ) ^ δ / ε := by
          gcongr
      _ = 1 / ε * (n : ℝ) ^ (-δ) := by
          rw [← Real.rpow_add hn0]
          rw [show ρ - (1 - η) + δ + δ = -δ by rw [hδdef]; ring]
          ring

/-- Lemma `lem:critM` (source lines 1099–1105): if `η < 1` and `e_n ≥ 0` is `n^{o(1)}` along
a filter `l ≤ atTop`, then `e_n / a_{⌊n^(1-η)⌋} → 0` along `l`. -/
theorem tendsto_div_floor_rpow (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 < ρ) {η : ℝ} (hη : η < 1)
    {l : Filter ℕ} (hl : l ≤ atTop) {e : ℕ → ℝ} (he0 : ∀ᶠ n in l, 0 ≤ e n)
    (he : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in l, e n ≤ (n : ℝ) ^ δ) :
    Tendsto (fun n => e n / a ⌊(n : ℝ) ^ (1 - η)⌋₊) l (𝓝 0) := by
  have hθ : 0 < 1 - η := by linarith
  set δ : ℝ := (1 - η) * ρ / 3 with hδdef
  have hδ : 0 < δ := by positivity
  have h1 := hrv.eventually_floor_rpow_bounds hmono hpos hρ hθ hδ
  apply tendsto_zero_of_le_mul_rpow hl (C := 1) (γ := -δ) (by linarith)
  · filter_upwards [he0, hl h1, hl (eventually_ge_atTop 1)] with n hn h1n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have : 0 < a ⌊(n : ℝ) ^ (1 - η)⌋₊ := lt_of_lt_of_le (by positivity) h1n.1
    positivity
  · filter_upwards [he δ hδ, hl h1, hl (eventually_ge_atTop 1)] with n hen h1n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hp : 0 < (n : ℝ) ^ ((1 - η) * ρ - δ) := by positivity
    have hapos : 0 < a ⌊(n : ℝ) ^ (1 - η)⌋₊ := lt_of_lt_of_le hp h1n.1
    rw [div_le_iff₀ hapos]
    calc e n ≤ (n : ℝ) ^ δ := hen
      _ = 1 * (n : ℝ) ^ (-δ) * (n : ℝ) ^ ((1 - η) * ρ - δ) := by
          rw [one_mul, ← Real.rpow_add hn0]
          congr 1
          rw [hδdef]
          ring
      _ ≤ 1 * (n : ℝ) ^ (-δ) * a ⌊(n : ℝ) ^ (1 - η)⌋₊ :=
          mul_le_mul_of_nonneg_left h1n.1 (by positivity)

end RegularlyVaryingSeq

end PoissonDeclumping

/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.FieldTheory.Perfect

/-!
# The image of Frobenius in a normed field of characteristic `p`

Let `K` be a nontrivially normed field of characteristic `p` and `Kᵖ` the image of `x ↦ xᵖ`.
If `K` is complete then `Kᵖ` is closed, and if `Kᵖ ≠ K` it has empty interior. A function with
values in `Kᵖ` has zero derivative, and the coefficients of a power series with values in `Kᵖ`
lie in `Kᵖ` and vanish outside the multiples of `p`. In one variable, if `h ^ p` is analytic then
so is `h`.

## Main statements

* `CharP.isClosed_range_pow`: if `K` is complete, `Kᵖ` is closed.
* `CharP.interior_range_pow_eq_empty`: if `Kᵖ ≠ K`, then `Kᵖ` has empty interior.
* `CharP.hasDerivAt_eq_zero_of_mem_range_pow`: if `Kᵖ` is closed and `π ∉ Kᵖ`, a function
  with values in `Kᵖ` has derivative `0` wherever it is differentiable.
* `HasFPowerSeriesAt.tendsto_sub_partialSum_div_pow`: Taylor's formula along `y = cᵖ w`.
* `CharP.coeff_mem_range_pow`: if `Kᵖ` is closed, `π ∉ Kᵖ` and a power series `Σ aₙ yⁿ` takes
  values in `Kᵖ` near its centre, then every `aₙ` is in `Kᵖ` and `aₙ = 0` unless `p ∣ n`.
* `CharP.analyticAt_of_analyticAt_pow`: if `K` is complete, `Kᵖ ≠ K` and `t ↦ h(t)ᵖ` is
  analytic at `x`, then `h` is analytic at `x`.
-/

public section

open Filter Topology NNReal ENNReal

noncomputable section

namespace CharP

variable {K : Type*} (p : ℕ)

variable [NontriviallyNormedField K] [CharP K p] [hp : Fact p.Prime]

/-- Two `p`-th powers differ by a `p`-th power. -/
private theorem sub_mem_range_pow {a b : K} (ha : a ∈ Set.range (· ^ p : K → K))
    (hb : b ∈ Set.range (· ^ p : K → K)) : a - b ∈ Set.range (· ^ p : K → K) := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  exact ⟨c - d, sub_pow_char c d⟩

/-- In a complete normed field of characteristic `p`, the subfield `Kᵖ` is closed. -/
theorem isClosed_range_pow [CompleteSpace K] : IsClosed (Set.range (· ^ p : K → K)) := by
  have hp0 : 0 < p := hp.out.pos
  refine isClosed_iff_clusterPt.2 fun y hy ↦ ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (mem_closure_iff_clusterPt.2 hy)
  choose c hc using hu
  have hcau : CauchySeq c := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq (ε ^ p) (pow_pos hε p)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm, ← hc m, ← hc n, ← sub_pow_char, norm_pow] at h
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ p hε.le h
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨z, tendsto_nhds_unique ((hz.pow p).congr fun n ↦ ?_) hlim⟩
  exact hc n

/-- If `Kᵖ ≠ K`, then `Kᵖ` has empty interior. -/
theorem interior_range_pow_eq_empty {π : K} (hπ : π ∉ Set.range (· ^ p : K → K)) :
    interior (Set.range (· ^ p : K → K)) = ∅ := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  by_contra hne
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max 1 (‖π‖ / r))
  have hc1 : 1 < ‖c‖ := lt_of_le_of_lt (le_max_left _ _) hc
  have hc0 : c ≠ 0 := norm_pos_iff.1 (lt_trans one_pos hc1)
  have hcp : ‖c‖ ≤ ‖c‖ ^ p := le_self_pow₀ hc1.le (by omega)
  have hmem : a + π / c ^ p ∈ Set.range (· ^ p : K → K) := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_div, norm_pow,
      div_lt_iff₀ (pow_pos (lt_trans one_pos hc1) p)]
    have : ‖π‖ / r < ‖c‖ ^ p := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hc) hcp
    rwa [div_lt_iff₀ hr, mul_comm] at this
  have ha' : a ∈ Set.range (· ^ p : K → K) := interior_subset ha
  obtain ⟨e, he⟩ := sub_mem_range_pow p hmem ha'
  apply hπ
  refine ⟨c * e, ?_⟩
  simp only at he ⊢
  rw [mul_pow, he, add_sub_cancel_left, mul_div_cancel₀ _ (pow_ne_zero p hc0)]

/-- If `Kᵖ` is closed and `π ∉ Kᵖ`, a `Kᵖ`-valued function has zero derivative wherever it is
differentiable: the difference quotients along `cᵖ` lie in `Kᵖ`, those along `π cᵖ` in
`π⁻¹ Kᵖ`, and these two closed sets meet only in `0`. -/
theorem hasDerivAt_eq_zero_of_mem_range_pow (hS : IsClosed (Set.range (· ^ p : K → K)))
    {π : K} (hπ : π ∉ Set.range (· ^ p : K → K)) {g : K → K}
    (hg : ∀ y, g y ∈ Set.range (· ^ p : K → K)) {t d : K} (hd : HasDerivAt g d t) : d = 0 := by
  set S := Set.range (· ^ p : K → K) with hSdef
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hπ0 : π ≠ 0 := fun h ↦ hπ ⟨0, by simp [h, zero_pow hp0]⟩
  have hslope := hd.tendsto_slope
  -- along `t + (a c)ᵖ`, for a fixed `a ≠ 0`
  have key : ∀ a : K, a ≠ 0 →
      Tendsto (fun c : K ↦ slope g t (t + a * c ^ p)) (𝓝[≠] 0) (𝓝 d) := by
    intro a ha
    refine hslope.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun c : K ↦ t + a * c ^ p) (𝓝 0) (𝓝 (t + a * 0 ^ p)) :=
        (continuous_const.add (continuous_const.mul (continuous_pow p))).tendsto 0
      simpa [zero_pow hp0] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      simp [ha, pow_ne_zero p (show c ≠ 0 from hc)]
  have hval : ∀ a c : K, a ≠ 0 → c ≠ 0 →
      a * slope g t (t + a * c ^ p) ∈ S := by
    intro a c ha hc
    obtain ⟨e, he⟩ := sub_mem_range_pow p (hg (t + a * c ^ p)) (hg t)
    refine ⟨e / c, ?_⟩
    simp only at he ⊢
    rw [slope_def_field, add_sub_cancel_left, div_pow, he]
    field_simp
  have hmem : ∀ a : K, a ≠ 0 → a * d ∈ S := by
    intro a ha
    refine hS.mem_of_tendsto (((key a ha).const_mul a)) ?_
    filter_upwards [self_mem_nhdsWithin] with c hc using hval a c ha hc
  obtain ⟨u, hu⟩ := hmem 1 one_ne_zero
  obtain ⟨v, hv⟩ := hmem π hπ0
  by_contra hd0
  apply hπ
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [zero_pow hp0] at hu
    exact hd0 hu.symm
  refine ⟨v / u, ?_⟩
  simp only at hu hv ⊢
  rw [div_pow, hu, hv, one_mul, mul_div_cancel_right₀ _ hd0]

/-- The subfield `Kᵖ`, as the field range of Frobenius. -/
private theorem mem_fieldRange_frobenius_iff {a : K} :
    a ∈ (frobenius K p).fieldRange ↔ a ∈ Set.range (· ^ p : K → K) := by
  simp [RingHom.mem_fieldRange, frobenius_def]

omit [CharP K p] hp in
/-- Taylor's formula along `y = cᵖ w`: if `g` has the power series `P = Σ aₙ yⁿ` at `x`, then
`(g (x + cᵖ w) - Σ_{k<m} a_k (cᵖ w)ᵏ) / (cᵖ)ᵐ` tends to `wᵐ aₘ` as `c → 0`. -/
theorem _root_.HasFPowerSeriesAt.tendsto_sub_partialSum_div_pow (hp0 : p ≠ 0) {g : K → K}
    {P : FormalMultilinearSeries K K K} {x : K} (hP : HasFPowerSeriesAt g P x) (m : ℕ) (w : K) :
    Tendsto (fun c : K ↦ (g (x + c ^ p * w) - P.partialSum m (c ^ p * w)) / (c ^ p) ^ m)
      (𝓝[≠] 0) (𝓝 (w ^ m * P.coeff m)) := by
  set E : K → K := fun y ↦ g (x + y) - P.partialSum (m + 1) y with hE
  have hφ : Tendsto (fun c : K ↦ c ^ p * w) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun c : K ↦ c ^ p * w) := by fun_prop
    simpa [zero_pow hp0] using h.tendsto 0
  have hO : (fun c : K ↦ E (c ^ p * w)) =O[𝓝 0] fun c ↦ c ^ (p * (m + 1)) := by
    refine ((hP.isBigO_sub_partialSum_pow (m + 1)).comp_tendsto hφ).trans ?_
    refine Asymptotics.IsBigO.of_bound (‖w‖ ^ (m + 1)) (Eventually.of_forall fun c ↦ ?_)
    refine le_of_eq ?_
    simp only [Function.comp_apply, norm_pow, norm_norm, norm_mul, mul_pow, ← pow_mul]
    ring
  have ho : (fun c : K ↦ E (c ^ p * w)) =o[𝓝 0] fun c ↦ (c ^ p) ^ m := by
    refine hO.trans_isLittleO ?_
    simp_rw [← pow_mul]
    exact Asymptotics.isLittleO_pow_pow (by have := Nat.pos_of_ne_zero hp0; nlinarith)
  have hmain := (ho.tendsto_div_nhds_zero.mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))).const_add (w ^ m * P.coeff m)
  rw [add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc' : (c ^ p) ^ m ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hc)
  simp only [hE, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    P.apply_eq_pow_smul_coeff, smul_eq_mul]
  field_simp
  ring

/-- Let `Kᵖ` be closed and `π ∉ Kᵖ`. If `g` has the power series
`Σ aₙ yⁿ` at `x` and takes values in `Kᵖ` near `x`, then every `aₙ` lies in `Kᵖ`, and `aₙ = 0`
unless `p ∣ n`. By induction on `m`: the remainder of order `m`, evaluated at `cᵖ w` and divided
by `(cᵖ)ᵐ`, lies in `Kᵖ` and tends to `wᵐ aₘ`; take `w = 1`, then `w = π`. -/
theorem coeff_mem_range_pow (hS : IsClosed (Set.range (· ^ p : K → K))) {π : K}
    (hπ : π ∉ Set.range (· ^ p : K → K)) {g : K → K} {P : FormalMultilinearSeries K K K}
    {x : K} (hP : HasFPowerSeriesAt g P x)
    (hg : ∀ᶠ y in 𝓝 x, g y ∈ Set.range (· ^ p : K → K)) (m : ℕ) :
    P.coeff m ∈ Set.range (· ^ p : K → K) ∧ (¬ p ∣ m → P.coeff m = 0) := by
  set F := (frobenius K p).fieldRange
  have hF : ∀ a : K, a ∈ F ↔ a ∈ Set.range (· ^ p : K → K) := fun a ↦
    mem_fieldRange_frobenius_iff p
  have hFc : IsClosed (F : Set K) := by
    convert hS using 1
    ext a
    exact hF a
  simp_rw [← hF] at hπ hg ⊢
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hπ0 : π ≠ 0 := fun h ↦ hπ (h ▸ F.zero_mem)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hw : ∀ w : K, w ^ m * P.coeff m ∈ F := by
    intro w
    refine hFc.mem_of_tendsto (HasFPowerSeriesAt.tendsto_sub_partialSum_div_pow p hp0 hP m w) ?_
    have hφ : Tendsto (fun c : K ↦ x + c ^ p * w) (𝓝[≠] 0) (𝓝 x) := by
      have h : Continuous (fun c : K ↦ x + c ^ p * w) := by fun_prop
      simpa [zero_pow hp0] using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    filter_upwards [hφ.eventually hg] with c hc
    refine F.div_mem (F.sub_mem hc ?_) (F.pow_mem ((hF _).2 ⟨c, rfl⟩) m)
    refine F.sum_mem fun k hk ↦ ?_
    rw [P.apply_eq_pow_smul_coeff, smul_eq_mul]
    by_cases hpk : p ∣ k
    · obtain ⟨j, rfl⟩ := hpk
      refine F.mul_mem ?_ (ih _ (Finset.mem_range.1 hk)).1
      rw [pow_mul']
      exact (hF _).2 ⟨_, rfl⟩
    · rw [(ih k (Finset.mem_range.1 hk)).2 hpk, mul_zero]
      exact F.zero_mem
  have ha : P.coeff m ∈ F := by simpa using hw 1
  refine ⟨ha, fun hpm ↦ ?_⟩
  by_contra ha0
  apply hπ
  have hπm : π ^ m ∈ F := by
    have := F.mul_mem (hw π) (F.inv_mem ha)
    rwa [mul_assoc, mul_inv_cancel₀ ha0, mul_one] at this
  have hπp : π ^ p ∈ F := (hF _).2 ⟨π, rfl⟩
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm).symm
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  obtain ⟨N, hN⟩ : ∃ N, p * N + 1 = m * k := by
    have := Nat.div_add_mod (m * k) p
    rw [hk] at this
    exact ⟨_, this⟩
  have hπeq : π = (π ^ m) ^ k / (π ^ p) ^ N := by
    rw [← pow_mul, ← pow_mul, ← hN, pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero _ hπ0)]
  rw [hπeq]
  exact F.div_mem (F.pow_mem hπm _) (F.pow_mem hπp _)

/-- Let `K` be complete of characteristic `p` with `Kᵖ ≠ K`. If `t ↦ h(t)ᵖ` is
analytic at `x`, then `h` is analytic at `x`: writing `h(x + y)ᵖ = Σ a_{pn} y^{pn}` with
`a_{pn} = b_nᵖ`, the series `Σ b_n yⁿ` has positive radius, and its `p`-th power is
`Σ b_nᵖ y^{pn}` because Frobenius is additive and continuous. One variable only. -/
theorem analyticAt_of_analyticAt_pow [CompleteSpace K] {π : K}
    (hπ : π ∉ Set.range (· ^ p : K → K)) {h : K → K} {x : K}
    (hg : AnalyticAt K (fun t ↦ h t ^ p) x) : AnalyticAt K h x := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨P, r, hP⟩ := hg
  have hcoef := coeff_mem_range_pow p (isClosed_range_pow p) hπ hP.hasFPowerSeriesAt
    (Eventually.of_forall fun y ↦ ⟨h y, rfl⟩)
  choose b hb using fun n ↦ (hcoef (p * n)).1
  set Q := FormalMultilinearSeries.ofScalars K b with hQdef
  obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hP.r_pos.trans_le hP.r_le)
  obtain ⟨C, -, hC⟩ := P.norm_mul_pow_le_of_lt_radius hρr
  have hQ : (ρ : ℝ≥0∞) ≤ Q.radius := by
    refine Q.le_radius_of_bound (max 1 C) fun n ↦ ?_
    rw [hQdef, FormalMultilinearSeries.ofScalars_norm]
    have h1 := hC (p * n)
    rw [P.norm_apply_eq_norm_coef, ← hb n, norm_pow, pow_mul', ← mul_pow] at h1
    by_cases h' : ‖b n‖ * (ρ : ℝ) ^ n ≤ 1
    · exact h'.trans (le_max_left _ _)
    · exact (le_self_pow₀ (by linarith) hp0.ne').trans (h1.trans (le_max_right _ _))
  have hQpos : 0 < Q.radius := lt_of_lt_of_le (by exact_mod_cast hρ0) hQ
  have hfrob : Continuous (frobenius K p) := by
    show Continuous fun a ↦ frobenius K p a
    simp only [frobenius_def]
    exact continuous_pow p
  have heq : ∀ᶠ y in 𝓝 (0 : K), h (x + y) = Q.sum y := by
    have hball : Metric.eball (0 : K) (min r ρ) ∈ 𝓝 (0 : K) :=
      Metric.eball_mem_nhds _ (lt_min hP.r_pos (by exact_mod_cast hρ0))
    filter_upwards [hball] with y hy
    have hyr : y ∈ Metric.eball (0 : K) r := Metric.eball_subset_eball (min_le_left _ _) hy
    have hyQ : y ∈ Metric.eball (0 : K) Q.radius :=
      Metric.eball_subset_eball ((min_le_right _ _).trans hQ) hy
    have h1 := hP.hasSum hyr
    have h2 := (Q.hasFPowerSeriesOnBall hQpos).hasSum hyQ
    rw [zero_add] at h2
    have h3 : HasSum (fun n ↦ (Q n fun _ ↦ y) ^ p) (Q.sum y ^ p) := by
      simpa [Function.comp_def, frobenius_def] using h2.map (frobenius K p) hfrob
    have h4 : HasSum (fun n ↦ P n fun _ ↦ y) (Q.sum y ^ p) := by
      refine ((mul_right_injective₀ hp0.ne').hasSum_iff ?_).1 ?_
      · rintro n hn
        rw [P.apply_eq_pow_smul_coeff, (hcoef n).2 ?_, smul_zero]
        rintro ⟨j, rfl⟩
        exact hn ⟨j, rfl⟩
      · convert h3 using 1
        funext n
        rw [Function.comp_apply, P.apply_eq_pow_smul_coeff, hQdef,
          FormalMultilinearSeries.ofScalars_apply_eq, ← hb n, smul_eq_mul, smul_eq_mul,
          mul_pow, pow_mul']
        ring
    exact frobenius_inj K p (by simpa [frobenius_def] using h1.unique h4)
  have hA := (Q.hasFPowerSeriesOnBall hQpos).hasFPowerSeriesAt.comp_sub x
  rw [zero_add] at hA
  refine ⟨Q, hA.congr ?_⟩
  have hx : Tendsto (fun z ↦ z - x) (𝓝 x) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
  filter_upwards [hx.eventually heq] with z hz
  simpa using hz.symm

end CharP

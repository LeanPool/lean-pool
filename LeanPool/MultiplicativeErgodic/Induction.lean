/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.SlowProjection

/-!
# The inductive step of the main result

`proof_met.tex` §6 proves `mainres` by induction on the number of fast spaces split off. At each
stage the slow space `V(ω)` of codimension `M` comes with the projection `Q_ω` onto it, and the
cocycle is replaced by `𝓛' = 𝓛 ∘ Q` on a set `A` where `Q` is bounded (`Cocycle.modify`). The
top fast space of `𝓛'` is the next fast space of `𝓛`.

The key estimate is that the exponents of `𝓛'` are those of `𝓛` shifted by `M`:
`χ'_k = χ_{M+k}` (`Cocycle.chi_modify`). One inequality is `Tsmallgrow`; the other is `Tbiggrow`
together with temperedness of `Q`, which absorbs the factor `‖Q_{σⁿω}‖`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open Filter Topology MeasureTheory TopologicalSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace X]

/-- A `limsup` exponent is at most `c` as soon as the sequence is eventually below `e^{nb}` for
every real `b > c`. -/
theorem limsup_logEReal_div_le_of_forall {u : ℕ → ℝ} {c : EReal}
    (h : ∀ b : ℝ, c < b → ∀ᶠ n : ℕ in atTop, u n ≤ Real.exp (n * b)) :
    limsup (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop ≤ c := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨M, hcM, hMlt⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hev : ∀ᶠ n : ℕ in atTop, logEReal (u n) / (n : EReal) ≤ (M : EReal) := by
    filter_upwards [h M hcM, eventually_ge_atTop 1] with n hn hn1
    exact (logEReal_div_le_iff hn1 M).2 (by rwa [mul_comm])
  exact absurd ((limsup_le_limsup hev).trans (limsup_const _).le) (not_le.2 hMlt)

/-- A `limsup` exponent below `b` gives `u_n < e^{nb}` eventually. -/
theorem eventually_lt_exp_of_limsup_lt {u : ℕ → ℝ} {b : ℝ}
    (h : limsup (fun n : ℕ => logEReal (u n) / (n : EReal)) atTop < b) :
    ∀ᶠ n : ℕ in atTop, u n < Real.exp (n * b) := by
  filter_upwards [eventually_lt_of_limsup_lt h, eventually_ge_atTop 1] with n hn hn1
  rw [mul_comm]
  exact (logEReal_div_lt_iff hn1 b).1 hn

/-- A tempered family of operators grows subexponentially along the orbit. -/
theorem Cocycle.eventually_norm_le_of_isTempered (R : Cocycle Ω X) {Q : Ω → X →L[ℝ] X}
    (h : R.IsTempered Q) :
    ∀ᵐ ω ∂(R.μ), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ‖Q (R.σ^[n] ω)‖ ≤ Real.exp (n * ε) := by
  filter_upwards [show ∀ᵐ ω ∂(R.μ), _ from h] with ω hω ε hε
  filter_upwards [hω.eventually_lt_const hε, eventually_ge_atTop 1] with n hn hn1
  rcases eq_or_lt_of_le (norm_nonneg (Q (R.σ^[n] ω))) with h0 | hpos
  · rw [← h0]; exact (Real.exp_pos _).le
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_lt_iff₀ hn0] at hn
    rw [mul_comm]
    exact ((Real.log_lt_iff_lt_exp hpos).1 hn).le

/-- **`χ'_k = χ_{M+k}` for the modified cocycle** (`proof_met.tex` l.1016--1022).

`Q_ω` is the projection onto the codimension-`M` slow space `V(ω)` along `F(ω)`, equivariant and
tempered, and `F` grows strictly faster than `𝓛^{(n)}_ω ∘ Q_ω`. Once the orbit has visited `A`,
`𝓛'^{(n)}_ω = 𝓛^{(n)}_ω ∘ Q_ω`, and then
`ρ_{M+k}(𝓛^{(n)}_ω) ≤ ρ_k(𝓛^{(n)}_ω Q_ω) ≤ 4‖Q_ω‖‖Q_{σⁿω}‖ ρ_{M+k}(𝓛^{(n)}_ω)`
by `Tsmallgrow` and `Tbiggrow`; temperedness makes `‖Q_{σⁿω}‖` subexponential. -/
theorem Cocycle.chi_modify (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] {M : ℕ}
    (F : Ω → Submodule ℝ X) (V : Ω → GrassmannianCofin X M) (Q : Ω → X →L[ℝ] X)
    (hQm : ∀ x, Measurable fun ω => Q ω x) {A : Set Ω} (hA : MeasurableSet A)
    (hApos : R.μ A ≠ 0) {C : ℝ} (hC : ∀ ω ∈ A, ‖Q ω‖ ≤ C)
    (hidem : ∀ᵐ ω ∂(R.μ), (Q ω).comp (Q ω) = Q ω)
    (hrange : ∀ᵐ ω ∂(R.μ), LinearMap.range (Q ω : X →ₗ[ℝ] X) = ((V ω).1.1 : Submodule ℝ X))
    (hker : ∀ᵐ ω ∂(R.μ), LinearMap.ker (Q ω : X →ₗ[ℝ] X) = F ω)
    (heq : ∀ᵐ ω ∂(R.μ), (Q (R.σ ω)).comp (R.L ω) = (R.L ω).comp (Q ω))
    (htemp : R.IsTempered Q)
    (hgap : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
      ‖(R.iterate n ω).comp (Q ω)‖ < growth (R.iterate n ω) (F ω)) :
    ∀ᵐ ω ∂(R.μ), ∀ k : ℕ, 1 ≤ k →
      (R.modify Q hQm A hA C hC).chi k ω = R.chi (M + k) ω := by
  classical
  have horb := R.ae_forall_iterate ((hidem.and heq).and hrange)
  have hvisit := ae_exists_mem_iterate R.ergodic hA hApos
  filter_upwards [horb, hvisit, R.eventually_norm_le_of_isTempered htemp, hgap, hker]
    with ω ho hv ht hg hkω
  have hid : ∀ i : ℕ, (Q (R.σ^[i] ω)).comp (Q (R.σ^[i] ω)) = Q (R.σ^[i] ω) :=
    fun i => (ho i).1.1
  have hcomm : ∀ i : ℕ, (Q (R.σ^[i + 1] ω)).comp (R.L (R.σ^[i] ω)) =
      (R.L (R.σ^[i] ω)).comp (Q (R.σ^[i] ω)) := fun i => by
    rw [Function.iterate_succ_apply']; exact (ho i).1.2
  have hit := R.modify_iterate hQm hA hC ω hid hcomm
  obtain ⟨i, hi⟩ := hv
  have hT' : ∀ᶠ n : ℕ in atTop,
      (R.modify Q hQm A hA C hC).iterate n ω = (R.iterate n ω).comp (Q ω) :=
    (eventually_gt_atTop i).mono fun n hn => (hit n).2.1 i hn hi
  have hproj : ∀ j : ℕ, LinearMap.IsProj ((V (R.σ^[j] ω)).1.1 : Submodule ℝ X)
      (Q (R.σ^[j] ω) : X →ₗ[ℝ] X) := by
    intro j
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [← (ho j).2]; exact ⟨x, rfl⟩
    · rw [← (ho j).2] at hx
      obtain ⟨z, rfl⟩ := hx
      exact congrArg (fun T : X →L[ℝ] X => T z) (hid j)
  intro k hk
  apply le_antisymm
  · -- `χ'_k ≤ χ_{M+k}`, by `Tbiggrow` and temperedness
    refine limsup_logEReal_div_le_of_forall fun b hb => ?_
    obtain ⟨b', hb'1, hb'2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    have hbb : b' < b := by exact_mod_cast hb'2
    set ε := (b - b') / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hρ : ∀ᶠ n : ℕ in atTop, bernsteinNumber (R.iterate n ω) (M + k) < Real.exp (n * b') :=
      eventually_lt_exp_of_limsup_lt hb'1
    filter_upwards [hT', hρ, ht ε hε, hg,
      eventually_mul_exp_le_exp (a := b' + ε) (b := b) (c := 0) (D := 4 * ‖Q ω‖)
        (by rw [hεdef]; linarith)] with n hn hρn htn hgn hD
    rw [zero_add] at hD
    rw [hn]
    have hfast : growth (R.iterate n ω) (F ω) >
        ‖(R.iterate n ω).comp ((V ω).1.1 : Submodule ℝ X).subtypeL‖ := by
      refine lt_of_le_of_lt ?_ hgn
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
      have hv : Q ω v = v := (hproj 0).map_id v v.2
      calc ‖(R.iterate n ω).comp ((V ω).1.1 : Submodule ℝ X).subtypeL v‖
          = ‖(R.iterate n ω).comp (Q ω) v‖ := by simp [hv]
        _ ≤ ‖(R.iterate n ω).comp (Q ω)‖ * ‖(v : X)‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖(R.iterate n ω).comp (Q ω)‖ * ‖v‖ := rfl
    have hbig := Tbiggrow M k (V ω) (V (R.σ^[n] ω)) (F ω) (Q ω) (Q (R.σ^[n] ω))
      (R.iterate n ω) (hproj 0) hkω (hproj n) (hit n).1 hfast
    rw [add_comm k M] at hbig
    have hρ0 := bernsteinNumber_nonneg (R.iterate n ω) (M + k)
    calc bernsteinNumber ((R.iterate n ω).comp (Q ω)) k
        ≤ 4 * ‖Q ω‖ * ‖Q (R.σ^[n] ω)‖ * bernsteinNumber (R.iterate n ω) (M + k) := hbig
      _ ≤ 4 * ‖Q ω‖ * Real.exp (n * ε) * Real.exp (n * b') := by gcongr
      _ = 4 * ‖Q ω‖ * Real.exp ((b' + ε) * n) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ Real.exp (b * n) := hD
      _ = Real.exp (n * b) := by rw [mul_comm]
  · -- `χ_{M+k} ≤ χ'_k`, by `Tsmallgrow`
    refine limsup_le_limsup ?_
    filter_upwards [hT'] with n hn
    change logEReal (bernsteinNumber (R.iterate n ω) (M + k)) / (n : EReal) ≤
      logEReal (bernsteinNumber ((R.modify Q hQm A hA C hC).iterate n ω) k) / (n : EReal)
    rw [hn]
    refine EReal.div_le_div_right_of_nonneg (by positivity) (ChiOrder.logEReal_mono ?_)
    exact Tsmallgrow M k (by omega) (V ω) (Q ω) (hproj 0).map_id (R.iterate n ω)

/-! ### Shifting the exponent indices -/

/-- `χ` is antitone on `k ≥ 1`, in the form used for index comparisons. -/
theorem Cocycle.chi_le_of_le (R : Cocycle Ω X) (ω : Ω) {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    R.chi t ω ≤ R.chi s ω := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact R.chi_antitone ω (by omega)

/-- **The distinct-exponent indices of a cocycle whose `χ` is shifted by `M`.** If
`χ'_k = χ_{M+k}` for `k ≥ 1` and the `L`-th index of `χ` is `M + 1`, then the `i`-th index of `χ'`
is the `(L+i)`-th index of `χ` minus `M` — or both are the junk value `0`. -/
theorem Cocycle.lambdaIdx_shift (R R' : Cocycle Ω X) (ω ω' : Ω) {M L : ℕ}
    (hχ : ∀ k : ℕ, 1 ≤ k → R'.chi k ω' = R.chi (M + k) ω)
    (hL : R.lambdaIdx L ω = M + 1) (i : ℕ) :
    (1 ≤ R'.lambdaIdx i ω' ∧ R'.lambdaIdx i ω' + M = R.lambdaIdx (L + i) ω) ∨
      (R'.lambdaIdx i ω' = 0 ∧ R.lambdaIdx (L + i) ω = 0) := by
  induction i with
  | zero =>
    refine Or.inl ⟨le_rfl, ?_⟩
    change 1 + M = R.lambdaIdx (L + 0) ω
    rw [add_zero, hL, add_comm]
  | succ i ih =>
    change (1 ≤ sInf {t : ℕ | 1 ≤ t ∧ R'.chi t ω' < R'.chi (R'.lambdaIdx i ω') ω'} ∧
        sInf {t : ℕ | 1 ≤ t ∧ R'.chi t ω' < R'.chi (R'.lambdaIdx i ω') ω'} + M =
          sInf {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx (L + i) ω) ω}) ∨
      (sInf {t : ℕ | 1 ≤ t ∧ R'.chi t ω' < R'.chi (R'.lambdaIdx i ω') ω'} = 0 ∧
        sInf {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx (L + i) ω) ω} = 0)
    rcases ih with ⟨hs1, hsI⟩ | ⟨hs0, hI0⟩
    · set s := R'.lambdaIdx i ω' with hsdef
      set I := R.lambdaIdx (L + i) ω with hIdef
      have hχs : R'.chi s ω' = R.chi I ω := by rw [hχ s hs1, ← hsI, add_comm]
      set S' := {t : ℕ | 1 ≤ t ∧ R'.chi t ω' < R'.chi s ω'} with hS'
      set S := {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi I ω} with hS
      have hSgt : ∀ u ∈ S, M < u := by
        rintro u ⟨hu1, hu⟩
        by_contra hle
        rw [not_lt] at hle
        exact absurd (R.chi_le_of_le ω hu1 (by omega : u ≤ I)) (not_le.2 hu)
      have hS'S : ∀ t, t ∈ S' ↔ M + t ∈ S := by
        intro t
        simp only [hS', hS, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨ht1, ht⟩
          exact ⟨by omega, by rwa [hχ t ht1, hχs] at ht⟩
        · rintro ⟨hMt, ht⟩
          have ht1 : 1 ≤ t := by
            have := hSgt (M + t) ⟨hMt, ht⟩
            omega
          exact ⟨ht1, by rwa [hχ t ht1, hχs]⟩
      by_cases hne : S.Nonempty
      · have hmemS := Nat.sInf_mem hne
        have hgt := hSgt _ hmemS
        have hmemS' : sInf S - M ∈ S' := by
          rw [hS'S, show M + (sInf S - M) = sInf S by omega]; exact hmemS
        have hne' : S'.Nonempty := ⟨_, hmemS'⟩
        have h1 := Nat.sInf_le hmemS'
        have h2 := Nat.sInf_le ((hS'S _).1 (Nat.sInf_mem hne'))
        have h3 := (Nat.sInf_mem hne').1
        exact Or.inl ⟨h3, by omega⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        have hne' : S' = ∅ := Set.eq_empty_of_forall_notMem fun t ht => by
          have := (hS'S t).1 ht
          rw [hne] at this
          exact this
        exact Or.inr ⟨by rw [hne', Nat.sInf_empty], by rw [hne, Nat.sInf_empty]⟩
    · have h1 : {t : ℕ | 1 ≤ t ∧ R'.chi t ω' < R'.chi (R'.lambdaIdx i ω') ω'} = ∅ := by
        rw [hs0, R'.chi_zero]
        exact Set.eq_empty_of_forall_notMem fun t ht => not_lt_bot ht.2
      have h2 : {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx (L + i) ω) ω} = ∅ := by
        rw [hI0, R.chi_zero]
        exact Set.eq_empty_of_forall_notMem fun t ht => not_lt_bot ht.2
      exact Or.inr ⟨by rw [h1, Nat.sInf_empty], by rw [h2, Nat.sInf_empty]⟩

/-- Once the index sequence hits the junk value `0`, it stays there. -/
theorem Cocycle.lambdaIdx_succ_eq_zero (R : Cocycle Ω X) (ω : Ω) {i : ℕ}
    (h : R.lambdaIdx i ω = 0) : R.lambdaIdx (i + 1) ω = 0 := by
  change sInf {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx i ω) ω} = 0
  rw [h, R.chi_zero]
  have : {t : ℕ | 1 ≤ t ∧ R.chi t ω < ⊥} = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => not_lt_bot ht.2
  rw [this, Nat.sInf_empty]

/-- Under the shift, the `i`-th multiplicity and exponent of `χ'` are the `(L+i)`-th of `χ`. -/
theorem Cocycle.mult_lambda_shift (R R' : Cocycle Ω X) (ω ω' : Ω) {M L : ℕ}
    (hχ : ∀ k : ℕ, 1 ≤ k → R'.chi k ω' = R.chi (M + k) ω)
    (hL : R.lambdaIdx L ω = M + 1) (i : ℕ) :
    R'.mult i ω' = R.mult (L + i) ω ∧ R'.lambda i ω' = R.lambda (L + i) ω := by
  have hi := R.lambdaIdx_shift R' ω ω' hχ hL i
  have hi1 := R.lambdaIdx_shift R' ω ω' hχ hL (i + 1)
  refine ⟨?_, ?_⟩
  · unfold Cocycle.mult
    rw [show L + i + 1 = L + (i + 1) by omega]
    have hz := fun h => R'.lambdaIdx_succ_eq_zero ω' (i := i) h
    generalize R'.lambdaIdx (i + 1) ω' = a at hi1 hz ⊢
    generalize R'.lambdaIdx i ω' = b at hi hz ⊢
    generalize R.lambdaIdx (L + (i + 1)) ω = c at hi1 ⊢
    generalize R.lambdaIdx (L + i) ω = d at hi ⊢
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · change R'.chi (R'.lambdaIdx i ω') ω' = R.chi (R.lambdaIdx (L + i) ω) ω
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hχ _ h1, ← h2, add_comm]
    · rw [h1, h2, R'.chi_zero, R.chi_zero]

theorem Cocycle.lambdaIdx_lt_succ (R : Cocycle Ω X) (ω : Ω) {i : ℕ}
    (h : R.lambdaIdx (i + 1) ω ≠ 0) : R.lambdaIdx i ω < R.lambdaIdx (i + 1) ω := by
  set S := {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx i ω) ω} with hS
  have hdef : R.lambdaIdx (i + 1) ω = sInf S := rfl
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    exact h (by rw [hdef, hcon, Nat.sInf_empty])
  have hmem := Nat.sInf_mem hne
  rw [hdef]
  by_contra hle
  rw [not_lt] at hle
  exact absurd (R.chi_le_of_le ω hmem.1 hle) (not_le.2 hmem.2)

/-- A nonzero multiplicity forces all earlier ones to be nonzero. -/
theorem Cocycle.mult_ne_zero_of_succ (R : Cocycle Ω X) (ω : Ω) {i : ℕ}
    (h : R.mult (i + 1) ω ≠ 0) : R.mult i ω ≠ 0 := by
  unfold Cocycle.mult at h ⊢
  have h2 : R.lambdaIdx (i + 1 + 1) ω ≠ 0 := by omega
  have h1 : R.lambdaIdx (i + 1) ω ≠ 0 := fun h0 => h2 (R.lambdaIdx_succ_eq_zero ω h0)
  have := R.lambdaIdx_lt_succ ω h1
  omega

/-- `𝓛` is quasicompact exactly when the top multiplicity is nonzero. -/
theorem Cocycle.isQuasicompact_iff_mult_zero (R : Cocycle Ω X) :
    R.IsQuasicompact ↔ ∀ᵐ ω ∂(R.μ), R.mult 0 ω ≠ 0 := by
  refine ⟨fun h => (R.mult_zero_pos h).mono fun ω h => h.ne', fun h => ?_⟩
  refine R.exists_chi_lt_chi_one_iff_isQuasicompact.1 ?_
  filter_upwards [h] with ω hω
  have h1 : R.lambdaIdx 1 ω ≠ 0 := by
    have h' : R.lambdaIdx (0 + 1) ω - R.lambdaIdx 0 ω ≠ 0 := hω
    rw [zero_add] at h'
    omega
  set S := {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx 0 ω) ω} with hS
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    exact h1 (show sInf S = 0 by rw [hcon, Nat.sInf_empty])
  exact ⟨_, (Nat.sInf_mem hne).1, (Nat.sInf_mem hne).2⟩

/-- Each distinct exponent is a.e. constant. -/
theorem Cocycle.exists_lambda_ae_eq (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] (i : ℕ) :
    ∃ c : EReal, ∀ᵐ ω ∂(R.μ), R.lambda i ω = c := by
  obtain ⟨N, hN⟩ := R.exists_lambdaIdx_ae_eq i
  obtain ⟨c, hc⟩ := R.exists_chi_ae_const N
  refine ⟨c, ?_⟩
  filter_upwards [hN, hc] with ω h1 h2
  change R.chi (R.lambdaIdx i ω) ω = c
  rw [h1, h2]

/-- The top exponent is never `+∞`: `‖𝓛^{(n)}_ω‖` is dominated by the floored log-norm family,
whose exponent is a real number. -/
theorem Cocycle.ae_chi_one_lt_top (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] :
    ∀ᵐ ω ∂(R.μ), R.chi 1 ω < ⊤ := by
  obtain ⟨c, -, hc, -, -⟩ := R.exists_logProdTrunc_limits 1
  filter_upwards [hc 0] with ω hω
  have hle : R.chi 1 ω ≤ (c 0 : EReal) := by
    refine limsup_logEReal_div_le_of_forall fun b hb => ?_
    have hb' : c 0 < b := by exact_mod_cast hb
    filter_upwards [hω.eventually_lt_const hb', eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_lt_iff₀ hn0] at hn
    have hmaxpos : 0 < max (R.prodBern 1 n ω) (Real.exp (-((0 : ℕ) : ℝ) * n)) :=
      lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
    have hlt := (Real.log_lt_iff_lt_exp hmaxpos).1 (by simpa [Cocycle.logProdTrunc] using hn)
    have hprod : R.prodBern 1 n ω = bernsteinNumber (R.iterate n ω) 1 := by
      simp [Cocycle.prodBern]
    rw [hprod] at hlt
    rw [mul_comm (n : ℝ)]
    exact (le_max_left _ _).trans hlt.le
  exact lt_of_le_of_lt hle (EReal.coe_lt_top _)

omit [MeasurableSpace X] in
/-- **A projection commutes with an operator respecting both halves of its splitting.** -/
theorem proj_comp_eq_of_maps {L P P' : X →L[ℝ] X} {F V F' V' : Submodule ℝ X}
    (hc : IsCompl F V) (hPV : ∀ v ∈ V, P v = v) (hPF : ∀ f ∈ F, P f = 0)
    (hP'V : ∀ v ∈ V', P' v = v) (hP'F : ∀ f ∈ F', P' f = 0)
    (hLF : ∀ f ∈ F, L f ∈ F') (hLV : ∀ v ∈ V, L v ∈ V') : P'.comp L = L.comp P := by
  ext x
  have hx : x ∈ F ⊔ V := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨f, hf, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, map_add, hPF f hf, hPV v hv,
    hP'F _ (hLF f hf), hP'V _ (hLV v hv), zero_add, map_zero]

omit [MeasurableSpace X] in
/-- `g_T(E) ≤ ‖T|_E‖ ≤ ‖T‖` for a nonzero finite-dimensional `E`. -/
theorem growth_le_norm_comp_subtypeL {m : ℕ} [NeZero m] (T : X →L[ℝ] X) (E : GrassmannianFin X m) :
    growth T (E.1 : Submodule ℝ X) ≤ ‖T.comp ((E.1 : Submodule ℝ X)).subtypeL‖ := by
  obtain ⟨x, hx1, hxE⟩ := sphere_inter_nonempty_of_finrank E
  change sInf ((fun y : X => ‖T y‖) '' (Metric.sphere (0 : X) 1 ∩ ((E.1 : Submodule ℝ X) : Set X)))
    ≤ _
  have hbdd : BddBelow
      ((fun y : X => ‖T y‖) '' (Metric.sphere (0 : X) 1 ∩ ((E.1 : Submodule ℝ X) : Set X))) :=
    ⟨0, by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _⟩
  refine (csInf_le hbdd (Set.mem_image_of_mem _ ⟨hx1, hxE⟩)).trans ?_
  have := (T.comp ((E.1 : Submodule ℝ X)).subtypeL).le_opNorm ⟨x, hxE⟩
  have hnorm : ‖(⟨x, hxE⟩ : (E.1 : Submodule ℝ X))‖ = 1 := mem_sphere_zero_iff_norm.1 hx1
  rw [hnorm, mul_one] at this
  simpa using this

omit [MeasurableSpace X] in
theorem norm_comp_subtypeL_le (T : X →L[ℝ] X) (E : Submodule ℝ X) :
    ‖T.comp E.subtypeL‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using T.le_opNorm (x : X)

/-! ### Tools for the inductive step -/

/-- **A property that holds eventually along almost every orbit holds almost everywhere**, for a
measurable property of a measure-preserving system: `μ(Gᶜ) = μ(σ⁻ⁿGᶜ) ≤ μ(⋃_{m ≥ n} σ⁻ᵐGᶜ)`,
and the last set shrinks to the null set of orbits visiting `Gᶜ` infinitely often. -/
theorem Cocycle.ae_mem_of_ae_eventually_iterate_mem (R : Cocycle Ω X) {G : Set Ω}
    (hG : MeasurableSet G) (h : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, R.σ^[n] ω ∈ G) :
    ∀ᵐ ω ∂(R.μ), ω ∈ G := by
  have hmp := R.ergodic.toMeasurePreserving
  set B := Gᶜ with hBdef
  have hB : MeasurableSet B := hG.compl
  set U : ℕ → Set Ω := fun N => ⋃ n ≥ N, (⇑R.σ)^[n] ⁻¹' B with hUdef
  have hUm : ∀ N, MeasurableSet (U N) := fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      (R.σ.measurable.iterate n) hB
  have hanti : Antitone U := fun N N' hNN' ω hω => by
    simp only [hUdef, Set.mem_iUnion] at hω ⊢
    obtain ⟨n, hn, hω⟩ := hω
    exact ⟨n, le_trans hNN' hn, hω⟩
  have hlim := tendsto_measure_iInter_atTop (μ := R.μ) (fun N => (hUm N).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hnull : R.μ (⋂ N, U N) = 0 := by
    rw [← nonpos_iff_eq_zero, ← ae_iff.1 h]
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_iInter, hUdef, Set.mem_iUnion, Set.mem_preimage] at hω
    simp only [Set.mem_ofPred_eq, eventually_atTop, not_exists, not_forall]
    intro N
    obtain ⟨n, hn, hB'⟩ := hω N
    exact ⟨n, hn, hB'⟩
  rw [hnull] at hlim
  have hle : ∀ N, R.μ B ≤ R.μ (U N) := fun N => by
    rw [← (hmp.iterate N).measure_preimage hB.nullMeasurableSet]
    exact measure_mono fun ω hω => Set.mem_iUnion₂.2 ⟨N, le_rfl, hω⟩
  have h0 : R.μ B ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hle)
  rw [ae_iff]
  exact le_antisymm h0 bot_le

omit [MeasurableSpace X] in
/-- Two operators that agree on `E` have the same growth on `E`. -/
theorem growth_congr {T T' : X →L[ℝ] X} {E : Submodule ℝ X} (h : ∀ y ∈ E, T y = T' y) :
    growth T E = growth T' E := by
  change sInf _ = sInf _
  congr 1
  ext r
  simp only [Set.mem_image]
  exact ⟨fun ⟨y, hy, hr⟩ => ⟨y, hy, by rw [← h y hy.2]; exact hr⟩,
    fun ⟨y, hy, hr⟩ => ⟨y, hy, by rw [h y hy.2]; exact hr⟩⟩

/-- Growth rates of a vector agree for two cocycles whose iterates eventually agree on it. -/
theorem Cocycle.lambdaAt_congr (R R' : Cocycle Ω X) {ω : Ω} {x : X}
    (h : ∀ᶠ n : ℕ in atTop, R'.iterate n ω x = R.iterate n ω x) :
    R'.lambdaAt ω x = R.lambdaAt ω x :=
  limsup_congr (h.mono fun n hn => by rw [hn])

/-- The `i`-th distinct exponent strictly exceeds the next one while its multiplicity is
nonzero. -/
theorem Cocycle.lambda_succ_lt (R : Cocycle Ω X) (ω : Ω) {i : ℕ} (h : R.mult i ω ≠ 0) :
    R.lambda (i + 1) ω < R.lambda i ω := by
  set S := {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx i ω) ω} with hS
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h0 : R.lambdaIdx (i + 1) ω = 0 := show sInf S = 0 by rw [hcon, Nat.sInf_empty]
    exact h (by unfold Cocycle.mult; omega)
  exact (Nat.sInf_mem hne).2

/-- A family of operators is bounded on a set of positive measure. -/
theorem Cocycle.exists_bounded_set (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {Q : Ω → X →L[ℝ] X} (hQm : ∀ x, Measurable fun ω => Q ω x) :
    ∃ (A : Set Ω) (C : ℝ), MeasurableSet A ∧ R.μ A ≠ 0 ∧ ∀ ω ∈ A, ‖Q ω‖ ≤ C := by
  have hQnorm : Measurable fun ω => ‖Q ω‖ := by
    have h := measurable_bernstein_of_weak (X := X) 1 hQm
    simpa only [bernsteinNumber_one] using h
  obtain ⟨M, hM⟩ : ∃ M : ℕ, R.μ {ω | ‖Q ω‖ ≤ (M : ℝ)} ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hU : (⋃ M : ℕ, {ω | ‖Q ω‖ ≤ (M : ℝ)}) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact exists_nat_ge _
    have h0 := measure_iUnion_null h
    rw [hU, measure_univ] at h0
    exact one_ne_zero h0
  exact ⟨_, M, measurableSet_le hQnorm measurable_const, hM, fun ω h => h⟩

omit [MeasurableSpace X] in
/-- **The algebra of two nested projections.** `Q` projects onto `V` along `F`, `P'` onto `V'` along
`E'`, with `E' ≤ V` and `F ≤ V'`. Then `Q` and `P'` commute, and their product projects onto
`V ⊓ V'` along `F ⊔ E'`. -/
theorem proj_pair {Q P' : X →L[ℝ] X} {F V E' V' : Submodule ℝ X}
    (hQidem : Q.comp Q = Q) (hQrange : LinearMap.range (Q : X →ₗ[ℝ] X) = V)
    (hQker : LinearMap.ker (Q : X →ₗ[ℝ] X) = F)
    (hPidem : P'.comp P' = P') (hPrange : LinearMap.range (P' : X →ₗ[ℝ] X) = V')
    (hPkill : ∀ e ∈ E', P' e = 0) (hc' : IsCompl E' V')
    (hE'V : E' ≤ V) (hFV' : F ≤ V') :
    (Q.comp P').comp (Q.comp P') = Q.comp P' ∧
      LinearMap.range ((Q.comp P' : X →L[ℝ] X) : X →ₗ[ℝ] X) = V ⊓ V' ∧
      LinearMap.ker ((Q.comp P' : X →L[ℝ] X) : X →ₗ[ℝ] X) = F ⊔ E' ∧
      IsCompl (F ⊔ E') (V ⊓ V') ∧ Disjoint F E' := by
  have hQfix : ∀ v ∈ V, Q v = v := fun v hv => by
    rw [← hQrange] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hQidem
  have hQF : ∀ f ∈ F, Q f = 0 := fun f hf => by rw [← hQker] at hf; exact hf
  have hPfix : ∀ v ∈ V', P' v = v := fun v hv => by
    rw [← hPrange] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hPidem
  have hQV : ∀ x, Q x ∈ V := fun x => hQrange ▸ ⟨x, rfl⟩
  have hPV' : ∀ x, P' x ∈ V' := fun x => hPrange ▸ ⟨x, rfl⟩
  have hPE' : ∀ x, x - P' x ∈ E' := by
    intro x
    have hx : x ∈ E' ⊔ V' := by rw [hc'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨e, he, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hPkill e he, hPfix v hv, zero_add, add_sub_cancel_right]
    exact he
  have hQx : ∀ x, x - Q x ∈ F := by
    intro x
    rw [← hQker]
    change Q (x - Q x) = 0
    rw [map_sub, hQfix _ (hQV x), sub_self]
  -- every vector splits as `f + e' + w`
  have hsplit : ∀ x, ∃ f ∈ F, ∃ e ∈ E', ∃ w ∈ V ⊓ V', x = f + e + w := by
    intro x
    refine ⟨x - Q x, hQx x, Q x - P' (Q x), hPE' _, P' (Q x), ⟨?_, hPV' _⟩, by abel⟩
    have : P' (Q x) = Q x - (Q x - P' (Q x)) := by abel
    rw [this]
    exact V.sub_mem (hQV x) (hE'V (hPE' _))
  have hval : ∀ f ∈ F, ∀ e ∈ E', ∀ w ∈ V ⊓ V', Q (P' (f + e + w)) = w := by
    intro f hf e he w hw
    simp only [map_add, hPfix f (hFV' hf), hPkill e he, hPfix w hw.2, hQF f hf, hQfix w hw.1,
      add_zero, zero_add]
  have hdisjF : Disjoint F E' := by
    rw [Submodule.disjoint_def]
    intro x hxF hxE
    have := hQF x hxF
    rwa [hQfix x (hE'V hxE)] at this
  refine ⟨?_, ?_, ?_, ?_, hdisjF⟩
  · ext x
    obtain ⟨f, hf, e, he, w, hw, rfl⟩ := hsplit x
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hval f hf e he w hw]
    have := hval 0 F.zero_mem 0 E'.zero_mem w hw
    simpa using this
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨f, hf, e, he, w, hw, rfl⟩ := hsplit x
      change Q (P' _) ∈ V ⊓ V'
      rw [hval f hf e he w hw]; exact hw
    · intro hy
      refine ⟨y, ?_⟩
      have := hval 0 F.zero_mem 0 E'.zero_mem y hy
      simpa using this
  · ext x
    constructor
    · intro hx
      obtain ⟨f, hf, e, he, w, hw, rfl⟩ := hsplit x
      have h0 : Q (P' (f + e + w)) = 0 := hx
      rw [hval f hf e he w hw] at h0
      subst h0
      rw [add_zero]
      exact Submodule.add_mem_sup hf he
    · intro hx
      obtain ⟨f, hf, e, he, rfl⟩ := Submodule.mem_sup.1 hx
      change Q (P' (f + e)) = 0
      have := hval f hf e he 0 (Submodule.zero_mem _)
      simpa using this
  · constructor
    · rw [Submodule.disjoint_def]
      intro x hx hw
      obtain ⟨f, hf, e, he, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 := hval f hf e he 0 (Submodule.zero_mem _)
      have h2 := hval 0 F.zero_mem 0 E'.zero_mem (f + e) hw
      simp only [add_zero, zero_add] at h1 h2
      rw [h1] at h2
      exact h2.symm
    · rw [codisjoint_iff, eq_top_iff]
      rintro x -
      obtain ⟨f, hf, e, he, w, hw, rfl⟩ := hsplit x
      exact Submodule.mem_sup.2 ⟨f + e, Submodule.add_mem_sup hf he, w, hw, rfl⟩

omit [MeasurableSpace X] in
/-- **Growth of the enlarged fast sum.** If `Q` kills `F`, fixes `E'`, and `Q_n T = T Q` with
`‖Q_n‖ ≤ c`, then `T` grows `F ⊔ E'` at least at `g/(3c)` when it grows both at `g`. -/
theorem le_growth_sup {T Q Qn : X →L[ℝ] X} {F E' : Submodule ℝ X}
    (hQF : ∀ f ∈ F, Q f = 0) (hQE : ∀ e ∈ E', Q e = e) (hcompat : Qn.comp T = T.comp Q)
    {g c : ℝ} (hg : 0 < g) (hc : 1 ≤ c) (hQn : ‖Qn‖ ≤ c)
    (hgF : g ≤ growth T F) (hgE : g ≤ growth T E')
    (hne : (Metric.sphere (0 : X) 1 ∩ ((F ⊔ E' : Submodule ℝ X) : Set X)).Nonempty) :
    g / (3 * c) ≤ growth T (F ⊔ E') := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨x, ⟨hx1, hx⟩, rfl⟩
  have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx1
  obtain ⟨f, hf, e, he, rfl⟩ := Submodule.mem_sup.1 hx
  have hTe : ‖T e‖ ≤ c * ‖T (f + e)‖ := by
    have : T e = Qn (T (f + e)) := by
      have h := congrArg (fun S : X →L[ℝ] X => S (f + e)) hcompat
      have hQfe : Q (f + e) = e := by rw [map_add, hQF f hf, hQE e he, zero_add]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h
      rw [hQfe] at h
      exact h.symm
    rw [this]
    exact (Qn.le_opNorm _).trans (by gcongr)
  have hTf : ‖T f‖ ≤ (1 + c) * ‖T (f + e)‖ := by
    have : T f = T (f + e) - T e := by rw [map_add]; abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have h1 := (growth_mul_norm_le T hf)
  have h2 := (growth_mul_norm_le T he)
  have hfe : 1 ≤ ‖f‖ + ‖e‖ := hxn ▸ norm_add_le f e
  have hTx := norm_nonneg (T (f + e))
  have hg3 : g * 1 ≤ (1 + 2 * c) * ‖T (f + e)‖ := by
    have hf' : g * ‖f‖ ≤ (1 + c) * ‖T (f + e)‖ :=
      (mul_le_mul_of_nonneg_right hgF (norm_nonneg f)).trans (h1.trans hTf)
    have he' : g * ‖e‖ ≤ c * ‖T (f + e)‖ :=
      (mul_le_mul_of_nonneg_right hgE (norm_nonneg e)).trans (h2.trans hTe)
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Temperedness of a product of projections.** -/
theorem Cocycle.isTempered_comp (R : Cocycle Ω X) {Q P : Ω → X →L[ℝ] X}
    (hQ : R.IsTempered Q) (hP : R.IsTempered P)
    (hQidem : ∀ᵐ ω ∂(R.μ), (Q ω).comp (Q ω) = Q ω)
    (hPidem : ∀ᵐ ω ∂(R.μ), (P ω).comp (P ω) = P ω)
    (hQPidem : ∀ᵐ ω ∂(R.μ), ((Q ω).comp (P ω)).comp ((Q ω).comp (P ω)) = (Q ω).comp (P ω)) :
    R.IsTempered fun ω => (Q ω).comp (P ω) := by
  have hlog0 : ∀ S : X →L[ℝ] X, S.comp S = S → 0 ≤ Real.log ‖S‖ := by
    intro S hS
    by_cases h0 : S = 0
    · simp [h0]
    · exact Real.log_nonneg (one_le_norm_of_isIdempotent hS h0)
  have horb := R.ae_forall_iterate ((hQidem.and hPidem).and hQPidem)
  change ∀ᵐ ω ∂(R.μ), _
  filter_upwards [horb, show ∀ᵐ ω ∂(R.μ), _ from hQ, show ∀ᵐ ω ∂(R.μ), _ from hP]
    with ω ho hq hp
  have hsum := hq.add hp
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => ?_)
    (fun n => ?_)
  · exact div_nonneg (hlog0 _ (ho n).2) (Nat.cast_nonneg _)
  · simp only
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    by_cases h0 : (Q (R.σ^[n] ω)).comp (P (R.σ^[n] ω)) = 0
    · rw [h0, norm_zero, Real.log_zero]
      exact add_nonneg (hlog0 _ (ho n).1.1) (hlog0 _ (ho n).1.2)
    · have hQ0 : Q (R.σ^[n] ω) ≠ 0 := fun h => h0 (by rw [h]; simp)
      have hP0 : P (R.σ^[n] ω) ≠ 0 := fun h => h0 (by rw [h]; simp)
      rw [← Real.log_mul (norm_ne_zero_iff.2 hQ0) (norm_ne_zero_iff.2 hP0)]
      exact Real.log_le_log (norm_pos_iff.2 h0) (ContinuousLinearMap.opNorm_comp_le _ _)

/-! ### Levels of the decomposition -/

/-- The data of the decomposition after the fast spaces `E_0, …, E_l`: the newest fast space
`E = E_l` (of dimension `d + 1`), the sum `F` of all of them (dimension `M`), the slow space `V`,
and the projection `Q` onto `V` along `F`. -/
structure LevelData (Ω X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- Dimension of the sum of the fast spaces constructed so far. -/
  M : ℕ
  /-- One less than the dimension of the newest fast space. -/
  d : ℕ
  /-- The newest fast space. -/
  E : Ω → GrassmannianFin X (d + 1)
  /-- The sum of all fast spaces constructed so far. -/
  F : Ω → GrassmannianFin X M
  /-- The complementary slow space. -/
  V : Ω → GrassmannianCofin X M
  /-- The projection onto the slow space along the fast sum. -/
  Q : Ω → X →L[ℝ] X

/-- **The inductive hypothesis**: `D` is the decomposition after `E_0, …, E_l`, where `lam i` is the
`i`-th distinct exponent. -/
structure Cocycle.IsLevel (R : Cocycle Ω X) (lam : ℕ → EReal) (l : ℕ) (D : LevelData Ω X) :
    Prop where
  lambdaIdx_eq : ∀ᵐ ω ∂(R.μ), R.lambdaIdx (l + 1) ω = D.M + 1
  lam_real : ∃ r : ℝ, lam l = r
  lam_gap : lam (l + 1) < lam l
  Q_meas : ∀ x, Measurable fun ω => D.Q ω x
  Q_temp : R.IsTempered D.Q
  Q_idem : ∀ᵐ ω ∂(R.μ), (D.Q ω).comp (D.Q ω) = D.Q ω
  Q_range : ∀ᵐ ω ∂(R.μ),
    LinearMap.range (D.Q ω : X →ₗ[ℝ] X) = ((D.V ω).1.1 : Submodule ℝ X)
  Q_ker : ∀ᵐ ω ∂(R.μ), LinearMap.ker (D.Q ω : X →ₗ[ℝ] X) = ((D.F ω).1 : Submodule ℝ X)
  Q_equiv : ∀ᵐ ω ∂(R.μ), (D.Q (R.σ ω)).comp (R.L ω) = (R.L ω).comp (D.Q ω)
  E_meas : Measurable D.E
  E_equiv : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((D.E ω).1 : Submodule ℝ X)
    = ((D.E (R.σ ω)).1 : Submodule ℝ X)
  E_dim : ∀ᵐ ω ∂(R.μ), R.mult l ω = D.d + 1
  E_norm : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
    ‖(R.iterate n ω).comp (((D.E ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal)) atTop
    (𝓝 (lam l))
  E_growth : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
    (growth (R.iterate n ω) ((D.E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop (𝓝 (lam l))
  E_le_F : ∀ᵐ ω ∂(R.μ), ((D.E ω).1 : Submodule ℝ X) ≤ ((D.F ω).1 : Submodule ℝ X)
  F_growth : ∀ᵐ ω ∂(R.μ), ∀ b : ℝ, (b : EReal) < lam l → ∀ᶠ n : ℕ in atTop,
    Real.exp (n * b) ≤ growth (R.iterate n ω) ((D.F ω).1 : Submodule ℝ X)
  slow_rate : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
    logEReal ‖(R.iterate n ω).comp (D.Q ω)‖ / (n : EReal)) atTop (𝓝 (lam (l + 1)))
  slow_char : ∀ᵐ ω ∂(R.μ),
    (((D.V ω).1.1 : Submodule ℝ X) : Set X) = {x : X | R.lambdaAt ω x ≤ lam (l + 1)}

/-- **Base case**: the top fast space and its slow complement, from `Cocycle.topdecomp`. -/
theorem Cocycle.exists_level_zero (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i)
    (hqc : R.IsQuasicompact) :
    ∃ D : LevelData Ω X, R.IsLevel lam 0 D ∧
      ∀ᵐ ω ∂(R.μ), ((D.F ω).1 : Submodule ℝ X) = ((D.E ω).1 : Submodule ℝ X) := by
  classical
  -- the top exponent is real
  have hchi1 : ∀ᵐ ω ∂(R.μ), R.chi 1 ω = lam 0 := by
    filter_upwards [hlam 0] with ω h using h
  obtain ⟨lam0, hlam0⟩ : ∃ r : ℝ, lam 0 = r := by
    obtain ⟨ω, ⟨h1, h2⟩, h3⟩ := ((hchi1.and R.ae_chi_one_lt_top).and hqc).exists
    have hbot : R.chi 1 ω ≠ ⊥ := (lt_of_le_of_lt bot_le h3).ne'
    exact ⟨(lam 0).toReal, (EReal.coe_toReal (h1 ▸ h2).ne (h1 ▸ hbot)).symm⟩
  obtain ⟨m1, hm1, E, V, P, hmult, hE, hEpos, hPm, hidem, hcompl, hPV, hVeq, htemp, hrate⟩ :=
    R.topdecomp hqc lam0 (lam 1) (by rw [← hlam0]; exact hchi1) (hlam 1)
  obtain ⟨d, rfl⟩ : ∃ d, m1 = d + 1 := ⟨m1 - 1, by have := NeZero.ne m1; omega⟩
  have hmp := R.ergodic.toMeasurePreserving
  have hker : ∀ᵐ ω ∂(R.μ), LinearMap.ker (P ω : X →ₗ[ℝ] X) = ((E ω).1 : Submodule ℝ X) := by
    filter_upwards [hcompl, hPV, hidem] with ω hc hpv hid
    obtain ⟨hrange, hkill⟩ := hpv
    refine le_antisymm (fun x hx => ?_) (fun e he => hkill e he)
    have hxs : x ∈ ((E ω).1 : Submodule ℝ X) ⊔ ((V ω).1.1 : Submodule ℝ X) := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨e, he, v, hv, rfl⟩ := Submodule.mem_sup.1 hxs
    have hfix : P ω v = v := by
      rw [← hrange] at hv
      obtain ⟨z, rfl⟩ := hv
      exact congrArg (fun T : X →L[ℝ] X => T z) hid
    have h0 : P ω (e + v) = 0 := hx
    rw [map_add, hkill e he, hfix, zero_add] at h0
    rw [h0, add_zero]; exact he
  have hQequiv : ∀ᵐ ω ∂(R.μ), (P (R.σ ω)).comp (R.L ω) = (R.L ω).comp (P ω) := by
    filter_upwards [hcompl, hPV, hidem, hmp.quasiMeasurePreserving.ae hPV,
      hmp.quasiMeasurePreserving.ae hidem, hE.2.2.1, hVeq] with ω hc hpv hid hpvσ hidσ hEe hVe
    have hfix : ∀ ω', (P ω').comp (P ω') = P ω' →
        LinearMap.range (P ω' : X →ₗ[ℝ] X) = ((V ω').1.1 : Submodule ℝ X) →
        ∀ v ∈ ((V ω').1.1 : Submodule ℝ X), P ω' v = v := by
      intro ω' hid' hr v hv
      rw [← hr] at hv
      obtain ⟨z, rfl⟩ := hv
      exact congrArg (fun T : X →L[ℝ] X => T z) hid'
    exact proj_comp_eq_of_maps hc (hfix ω hid hpv.1) hpv.2 (hfix _ hidσ hpvσ.1) hpvσ.2
      (fun f hf => hEe ▸ Submodule.mem_map_of_mem hf)
      (fun v hv => hVe (Submodule.mem_map_of_mem hv))
  have hTnorm : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal ‖R.iterate n ω‖ / (n : EReal))
      atTop (𝓝 (lam 0)) := by
    filter_upwards [R.ae_tendsto_chi 1, hchi1] with ω h hc
    rw [hc] at h
    simpa only [bernsteinNumber_one] using h
  have hEgrowth : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
      (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop (𝓝 (lam 0)) := by
    filter_upwards [hE.2.2.2, hEpos] with ω h hp
    rw [hlam0]; exact tendsto_logEReal_div_of_tendsto_log hp h
  refine ⟨⟨d + 1, d, E, E, V, P⟩, ⟨?_, ⟨lam0, hlam0⟩, ?_, hPm, htemp, hidem, ?_, hker, hQequiv,
    hE.1, hE.2.2.1, hmult, ?_, hEgrowth, Eventually.of_forall fun ω => le_rfl, ?_, hrate, ?_⟩,
    Eventually.of_forall fun ω => rfl⟩
  · filter_upwards [hmult] with ω hm
    have h0 : R.lambdaIdx 0 ω = 1 := rfl
    have h1 : R.mult 0 ω = R.lambdaIdx (0 + 1) ω - R.lambdaIdx 0 ω := rfl
    have hpos : 0 < R.mult 0 ω := by omega
    have := R.lambdaIdx_lt_succ ω (i := 0) (by omega)
    change R.lambdaIdx (0 + 1) ω = d + 1 + 1
    omega
  · obtain ⟨ω, hm, h2, h3⟩ := (hmult.and ((hlam 1).and (hlam 0))).exists
    have hlt := R.chi_mult_succ_lt ω (by rw [hm]; omega)
    have hidx : R.lambdaIdx 1 ω = R.mult 0 ω + 1 := by
      have h0 : R.lambdaIdx 0 ω = 1 := rfl
      have hm' : R.mult 0 ω = R.lambdaIdx (0 + 1) ω - R.lambdaIdx 0 ω := rfl
      rw [zero_add] at hm'
      omega
    rw [← h2, ← h3]
    change R.chi (R.lambdaIdx 1 ω) ω < R.chi 1 ω
    rwa [hidx]
  · filter_upwards [hPV] with ω h using h.1
  · filter_upwards [hTnorm, hEgrowth] with ω hT hg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg hT (fun n => ?_) (fun n => ?_)
    · exact EReal.div_le_div_right_of_nonneg (by positivity)
        (ChiOrder.logEReal_mono (growth_le_norm_comp_subtypeL _ _))
    · exact EReal.div_le_div_right_of_nonneg (by positivity)
        (ChiOrder.logEReal_mono (norm_comp_subtypeL_le _ _))
  · filter_upwards [hEgrowth] with ω hg b hb
    filter_upwards [(eventually_exp_bounds_of_tendsto (a := b) (b := lam0 + 1) hb
      (by rw [hlam0]; exact_mod_cast (by linarith : lam0 < lam0 + 1)) hg)] with n hn
    rw [mul_comm]; exact hn.1.le
  · exact R.V_characterisation (hlam0 ▸ (show lam 1 < lam 0 by
      obtain ⟨ω, hm, h1, h2⟩ := (hmult.and ((hlam 1).and (hlam 0))).exists
      have hlt := R.chi_mult_succ_lt ω (by rw [hm]; omega)
      have hidx : R.lambdaIdx 1 ω = R.mult 0 ω + 1 := by
        have h0 : R.lambdaIdx 0 ω = 1 := rfl
        have hm' : R.mult 0 ω = R.lambdaIdx (0 + 1) ω - R.lambdaIdx 0 ω := rfl
        rw [zero_add] at hm'
        omega
      rw [← h1, ← h2]
      change R.chi (R.lambdaIdx 1 ω) ω < R.chi 1 ω
      rwa [hidx])) E hE V P hidem hcompl hPV hrate

omit [StandardBorelSpace Ω] [MeasurableSpace X] in
/-- Extend almost-everywhere complementary finite-dimensional data to total families. -/
private theorem exists_total_complement_families (μ : Measure Ω) [NeZero μ]
    {m k : ℕ} (F : Ω → GrassmannianFin X m) (E : Ω → GrassmannianFin X k)
    (V : Ω → GrassmannianCofin X m) (W : Ω → GrassmannianCofin X k)
    (Q P : Ω → X →L[ℝ] X)
    (hgood : ∀ᵐ ω ∂μ, ((Q ω).comp (P ω)).comp ((Q ω).comp (P ω)) = (Q ω).comp (P ω) ∧
      LinearMap.range (((Q ω).comp (P ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
        ((V ω).1.1 : Submodule ℝ X) ⊓ ((W ω).1.1 : Submodule ℝ X) ∧
      LinearMap.ker (((Q ω).comp (P ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
        ((F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X) ∧
      IsCompl (((F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X))
        (((V ω).1.1 : Submodule ℝ X) ⊓ ((W ω).1.1 : Submodule ℝ X)) ∧
      Disjoint ((F ω).1 : Submodule ℝ X) ((E ω).1 : Submodule ℝ X)) :
    ∃ (Fnew : Ω → GrassmannianFin X (m + k)) (Vnew : Ω → GrassmannianCofin X (m + k)),
      (∀ᵐ ω ∂μ, ((Fnew ω).1 : Submodule ℝ X) =
        ((F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X)) ∧
      ∀ᵐ ω ∂μ, ((Vnew ω).1.1 : Submodule ℝ X) =
        ((V ω).1.1 : Submodule ℝ X) ⊓ ((W ω).1.1 : Submodule ℝ X) := by
  classical
  have hrankF : ∀ ω, Disjoint ((F ω).1 : Submodule ℝ X) ((E ω).1 : Submodule ℝ X) →
      FiniteDimensional ℝ ↥(((F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X)) ∧
      Module.finrank ℝ ↥(((F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X)) =
        m + k := by
    intro ω hdisj
    have := (F ω).2.1
    have := (E ω).2.1
    refine ⟨inferInstance, ?_⟩
    have := Submodule.finrank_sup_add_finrank_inf_eq ((F ω).1 : Submodule ℝ X)
      ((E ω).1 : Submodule ℝ X)
    rw [hdisj.eq_bot, finrank_bot, add_zero, (F ω).2.2, (E ω).2.2] at this
    exact this
  have hneF : Nonempty (GrassmannianFin X (m + k)) := by
    obtain ⟨ω, hω⟩ := hgood.exists
    exact ⟨⟨_, hrankF ω hω.2.2.2.2⟩⟩
  let Fnew : Ω → GrassmannianFin X (m + k) := fun ω =>
    if h : Disjoint ((F ω).1 : Submodule ℝ X) ((E ω).1 : Submodule ℝ X)
    then ⟨_, hrankF ω h⟩ else Classical.choice hneF
  let Qnew : Ω → X →L[ℝ] X := fun ω => (Q ω).comp (P ω)
  have hneV : Nonempty (GrassmannianCofin X (m + k)) := by
    obtain ⟨ω, hω⟩ := hgood.exists
    have hF : (Fnew ω).1 = ((F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X) := by
      change (dite _ (fun h => (⟨_, hrankF ω h⟩ : GrassmannianFin X (m + k)))
        (fun _ => Classical.choice hneF)).1 = _
      rw [dite_eq_left hω.2.2.2.2]
    refine ⟨rangeCofin (Qnew ω) (Fnew ω) ⟨hω.1, ?_⟩⟩
    rw [hF]
    change IsCompl _ (LinearMap.range (((Q ω).comp (P ω) : X →L[ℝ] X) : X →ₗ[ℝ] X))
    rw [hω.2.1]; exact hω.2.2.2.1
  let Vnew : Ω → GrassmannianCofin X (m + k) := fun ω =>
    if h : (Qnew ω).comp (Qnew ω) = Qnew ω ∧
        IsCompl ((Fnew ω).1 : Submodule ℝ X) (LinearMap.range (Qnew ω : X →ₗ[ℝ] X))
    then rangeCofin (Qnew ω) (Fnew ω) h else Classical.choice hneV
  have hFnew : ∀ᵐ ω ∂(μ), ((Fnew ω).1 : Submodule ℝ X) =
      ((F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X) := by
    filter_upwards [hgood] with ω hω
    change (dite _ (fun h => (⟨_, hrankF ω h⟩ : GrassmannianFin X (m + k)))
      (fun _ => Classical.choice hneF)).1 = _
    rw [dite_eq_left hω.2.2.2.2]
  have hVnew : ∀ᵐ ω ∂(μ), ((Vnew ω).1.1 : Submodule ℝ X) =
      ((V ω).1.1 : Submodule ℝ X) ⊓ ((W ω).1.1 : Submodule ℝ X) := by
    filter_upwards [hgood, hFnew] with ω hω hF
    have hcond : (Qnew ω).comp (Qnew ω) = Qnew ω ∧
        IsCompl ((Fnew ω).1 : Submodule ℝ X) (LinearMap.range (Qnew ω : X →ₗ[ℝ] X)) := by
      refine ⟨hω.1, ?_⟩
      rw [hF]
      change IsCompl _ (LinearMap.range (((Q ω).comp (P ω) : X →L[ℝ] X) : X →ₗ[ℝ] X))
      rw [hω.2.1]; exact hω.2.2.2.1
    change ((dite _ (fun h => rangeCofin (Qnew ω) (Fnew ω) h)
      (fun _ => Classical.choice hneV)).1.1 : Submodule ℝ X) = _
    rw [dite_eq_left hcond, rangeCofin_coe]
    exact hω.2.1
  exact ⟨Fnew, Vnew, hFnew, hVnew⟩

/-- Eventual intertwining forces an equivariant fast family into the projection range. -/
private theorem ae_fastSpace_le_projection_range (R R' : Cocycle Ω X)
    [SeparableSpace X] [BorelSpace X] [CompleteSpace X]
    (hσ : R'.σ = R.σ) (hμ : R'.μ = R.μ) {m : ℕ} [NeZero m]
    (E : Ω → GrassmannianFin X m) (Q : Ω → X →L[ℝ] X)
    (hQmeas : ∀ x, Measurable fun ω => Q ω x)
    (hidem : ∀ᵐ ω ∂(R.μ), (Q ω).comp (Q ω) = Q ω)
    (hTQ : ∀ᵐ ω ∂(R.μ),
      (∀ n, (Q (R.σ^[n] ω)).comp (R.iterate n ω) = (R.iterate n ω).comp (Q ω)) ∧
      ∀ᶠ n : ℕ in atTop, R'.iterate n ω = (R.iterate n ω).comp (Q ω))
    (hEmeas : Measurable E)
    (hEeq : ∀ᵐ ω ∂(R'.μ), Submodule.map (R'.L ω : X →ₗ[ℝ] X)
      ((E ω).1 : Submodule ℝ X) = ((E (R'.σ ω)).1 : Submodule ℝ X)) :
    ∀ᵐ ω ∂(R.μ), ((E ω).1 : Submodule ℝ X) ≤ LinearMap.range (Q ω : X →ₗ[ℝ] X) := by
  classical
  have horbQ := R.ae_forall_iterate hidem
  have hEqAll := R'.ae_all_shift_equivariant E hEeq
  rw [hμ, hσ] at hEqAll
  obtain ⟨b, hbm, hbspan⟩ := measbase (X := X) m
  set G : Set Ω := {ω | ∀ i, Q ω (b (E ω) i) = b (E ω) i} with hGdef
  have hbi : ∀ i, Measurable fun ω => b (E ω) i := fun i =>
    (measurable_pi_apply i).comp (hbm.comp hEmeas)
  have hGm : MeasurableSet G := by
    rw [hGdef, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (measurable_apply_of_weak hQmeas (hbi i)) (hbi i)
  have hGiff : ∀ ω, (∀ x ∈ ((E ω).1 : Submodule ℝ X), Q ω x = x) ↔ ω ∈ G := by
    intro ω
    constructor
    · intro h i
      exact h _ (by rw [hbspan (E ω)]; exact Submodule.subset_span ⟨i, rfl⟩)
    · intro h x hx
      rw [hbspan (E ω)] at hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
      simp only [map_sum, map_smul]
      exact Finset.sum_congr rfl fun i _ => by rw [h i]
  have hev : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, R.σ^[n] ω ∈ G := by
    filter_upwards [hTQ, hEqAll, horbQ] with ω hT hEq ho
    filter_upwards [hT.2] with n hn
    rw [← hGiff]
    intro y hy
    have hy' : y ∈ Submodule.map (R'.iterate n ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X) := by
      have hmap : Submodule.map (R'.iterate n ω : X →ₗ[ℝ] X)
          ((E ω).1 : Submodule ℝ X) = ((E (R.σ^[n] ω)).1 : Submodule ℝ X) := by
        simpa only [hσ] using R'.map_iterate_of_equivariant E ω
          (by simpa only [hσ] using hEq) n
      rw [hmap]
      exact hy
    obtain ⟨x, -, rfl⟩ := hy'
    have hcomp := congrArg (fun S : X →L[ℝ] X => S x) (hT.1 n)
    have hid := congrArg (fun S : X →L[ℝ] X => S (R.iterate n ω x)) (ho n)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hcomp hid
    change Q (R.σ^[n] ω) (R'.iterate n ω x) = R'.iterate n ω x
    rw [hn]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [← hcomp, hid]
  filter_upwards [R.ae_mem_of_ae_eventually_iterate_mem hGm hev] with ω hω x hx
  exact ⟨x, (hGiff ω).2 hω x hx⟩

omit [MeasurableSpace X] in
/-- A tempered separating projection preserves every rate below the slower summand's rate. -/
private theorem eventually_exp_le_growth_sup (F E : Submodule ℝ X)
    (T : ℕ → X →L[ℝ] X) (Q : X →L[ℝ] X) (Qn : ℕ → X →L[ℝ] X)
    {a c : ℝ} (hac : a < c)
    (hE : Tendsto (fun n : ℕ => logEReal (growth (T n) E) / (n : EReal))
      atTop (𝓝 (a : EReal)))
    (hF : ∀ b : ℝ, b < c → ∀ᶠ n : ℕ in atTop, Real.exp (n * b) ≤ growth (T n) F)
    (hQF : ∀ f ∈ F, Q f = 0) (hQE : ∀ e ∈ E, Q e = e)
    (hcomm : ∀ n, (Qn n).comp (T n) = (T n).comp Q)
    (htemp : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ‖Qn n‖ ≤ Real.exp (n * ε))
    (hne : (Metric.sphere (0 : X) 1 ∩ ((F ⊔ E : Submodule ℝ X) : Set X)).Nonempty)
    (b : ℝ) (hb : b < a) :
    ∀ᶠ n : ℕ in atTop, Real.exp (n * b) ≤ growth (T n) (F ⊔ E) := by
  set b' := (b + a) / 2 with hb'def
  set ε := (a - b) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hb'c : b' < c := by rw [hb'def]; linarith
  have hEgrow := eventually_exp_bounds_of_tendsto (a := b') (b := a + 1)
    (by exact_mod_cast (show b' < a by rw [hb'def]; linarith))
    (by exact_mod_cast (by linarith : a < a + 1)) hE
  filter_upwards [hEgrow, hF b' hb'c, htemp ε hε,
    eventually_mul_exp_le_exp (a := b) (b := b' - ε) (c := 0) (D := 3)
      (by rw [hb'def, hεdef]; linarith)] with n h1 h2 h3 h4
  rw [zero_add] at h4
  have hle := le_growth_sup (T := T n) (Q := Q) (Qn := Qn n)
    hQF hQE (hcomm n) (Real.exp_pos (n * b'))
    (Real.one_le_exp (by positivity)) h3 h2 (by rw [mul_comm]; exact h1.1.le) hne
  refine le_trans ?_ hle
  rw [le_div_iff₀ (by positivity)]
  calc Real.exp (n * b) * (3 * Real.exp (n * ε)) =
      3 * Real.exp (b * n) * Real.exp (n * ε) := by rw [mul_comm (n : ℝ) b]; ring
    _ ≤ Real.exp ((b' - ε) * n) * Real.exp (n * ε) := by gcongr
    _ = Real.exp (n * b') := by rw [← Real.exp_add]; congr 1; ring

/-- Complementary invariant summands make the composed slow projection equivariant. -/
private theorem ae_projection_extension_equivariant (R : Cocycle Ω X)
    {lam : ℕ → EReal} {l : ℕ} {D : LevelData Ω X} (hD : R.IsLevel lam l D)
    {k : ℕ} (E : Ω → GrassmannianFin X k) (W : Ω → GrassmannianCofin X k)
    (P Lmod : Ω → X →L[ℝ] X)
    (hgood : ∀ᵐ ω ∂(R.μ), ((D.Q ω).comp (P ω)).comp ((D.Q ω).comp (P ω)) =
        (D.Q ω).comp (P ω) ∧
      LinearMap.range (((D.Q ω).comp (P ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
        ((D.V ω).1.1 : Submodule ℝ X) ⊓ ((W ω).1.1 : Submodule ℝ X) ∧
      LinearMap.ker (((D.Q ω).comp (P ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
        ((D.F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X) ∧
      IsCompl (((D.F ω).1 : Submodule ℝ X) ⊔ ((E ω).1 : Submodule ℝ X))
        (((D.V ω).1.1 : Submodule ℝ X) ⊓ ((W ω).1.1 : Submodule ℝ X)) ∧
      Disjoint ((D.F ω).1 : Submodule ℝ X) ((E ω).1 : Submodule ℝ X))
    (hQF : ∀ᵐ ω ∂(R.μ), ∀ f ∈ ((D.F ω).1 : Submodule ℝ X), D.Q ω f = 0)
    (hQfix : ∀ᵐ ω ∂(R.μ), ∀ v ∈ ((D.V ω).1.1 : Submodule ℝ X), D.Q ω v = v)
    (hEV : ∀ᵐ ω ∂(R.μ), ((E ω).1 : Submodule ℝ X) ≤ ((D.V ω).1.1 : Submodule ℝ X))
    (hEeq : ∀ᵐ ω ∂(R.μ), Submodule.map (Lmod ω : X →ₗ[ℝ] X)
      ((E ω).1 : Submodule ℝ X) = ((E (R.σ ω)).1 : Submodule ℝ X))
    (hWeq : ∀ᵐ ω ∂(R.μ), Submodule.map (Lmod ω : X →ₗ[ℝ] X)
      ((W ω).1.1 : Submodule ℝ X) ≤ ((W (R.σ ω)).1.1 : Submodule ℝ X))
    (hLeq : ∀ ω x, D.Q ω x = x → Lmod ω x = R.L ω x) :
    ∀ᵐ ω ∂(R.μ), ((D.Q (R.σ ω)).comp (P (R.σ ω))).comp (R.L ω) =
      (R.L ω).comp ((D.Q ω).comp (P ω)) := by
  let Qnew : Ω → X →L[ℝ] X := fun ω => (D.Q ω).comp (P ω)
  have hmp := R.ergodic.toMeasurePreserving
  have hfixOf : ∀ (P : X →L[ℝ] X) (W : Submodule ℝ X), P.comp P = P →
      LinearMap.range (P : X →ₗ[ℝ] X) = W → ∀ v ∈ W, P v = v := by
    intro P W hid hr v hv
    rw [← hr] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hid
  have hq := hmp.quasiMeasurePreserving
  filter_upwards [hgood, hq.ae hgood, hD.Q_equiv, hQF, hq.ae hD.Q_ker, hQfix,
    hq.ae hD.Q_range, hEV, hEeq, hWeq] with ω hg hgσ hQe hqF hkσ hqV hrσ hEV hEeq hVe
  refine proj_comp_eq_of_maps (P := Qnew ω) (P' := Qnew (R.σ ω))
    (F' := ((D.F (R.σ ω)).1 : Submodule ℝ X) ⊔ ((E (R.σ ω)).1 : Submodule ℝ X))
    (V' := ((D.V (R.σ ω)).1.1 : Submodule ℝ X) ⊓ ((W (R.σ ω)).1.1 : Submodule ℝ X))
    hg.2.2.2.1 (hfixOf _ _ hg.1 hg.2.1)
    (fun f hf => by rw [← hg.2.2.1] at hf; exact hf)
    (hfixOf _ _ hgσ.1 hgσ.2.1) (fun f hf => by rw [← hgσ.2.2.1] at hf; exact hf) ?_ ?_
  · intro y hy
    obtain ⟨f, hf, e, he, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [← hkσ]
      change D.Q (R.σ ω) (R.L ω f) = 0
      have := congrArg (fun S : X →L[ℝ] X => S f) hQe
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at this
      rw [this, hqF f hf, map_zero]
    · have hEeq' : Submodule.map (((Lmod ω) : X →L[ℝ] X) : X →ₗ[ℝ] X)
          ((E ω).1 : Submodule ℝ X) = ((E (R.σ ω)).1 : Submodule ℝ X) := hEeq
      rw [← hLeq ω e (hqV e (hEV he)), ← hEeq']
      exact Submodule.mem_map_of_mem he
  · rintro w ⟨hwV, hwW⟩
    refine ⟨?_, ?_⟩
    · rw [← hrσ]
      refine ⟨R.L ω w, ?_⟩
      have := congrArg (fun S : X →L[ℝ] X => S w) hQe
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at this
      simp only [ContinuousLinearMap.coe_coe]
      rw [this, hqV w hwV]
    · rw [← hLeq ω w (hqV w hwV)]
      exact hVe (Submodule.mem_map_of_mem hwW)

/-- The slow projected iterates eventually grow strictly slower than the fast subspace. -/
theorem Cocycle.IsLevel.ae_eventually_norm_comp_lt_growth (R : Cocycle Ω X)
    {lam : ℕ → EReal} {l : ℕ} {D : LevelData Ω X} (hD : R.IsLevel lam l D) :
    ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, ‖(R.iterate n ω).comp (D.Q ω)‖ <
      growth (R.iterate n ω) ((D.F ω).1 : Submodule ℝ X) := by
  obtain ⟨b1, hb1, hb1'⟩ := EReal.lt_iff_exists_real_btwn.1 hD.lam_gap
  obtain ⟨b2, hb2, hb2'⟩ := EReal.lt_iff_exists_real_btwn.1 hb1'
  have hb12 : b1 < b2 := by exact_mod_cast hb2
  filter_upwards [hD.slow_rate, hD.F_growth] with ω hs hF
  filter_upwards [eventually_lt_exp_of_tendsto hb1 hs, hF b2 hb2'] with n h1 h2
  refine lt_of_lt_of_le h1 (le_trans ?_ h2)
  rw [mul_comm]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hb12.le (Nat.cast_nonneg _))

/-- The modified cocycle has the original level's shifted spectrum and a real next exponent. -/
theorem Cocycle.IsLevel.modified_level_spectrum (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i)
    {l : ℕ} {D : LevelData Ω X} (hD : R.IsLevel lam l D)
    (hm : ∀ᵐ ω ∂(R.μ), R.mult (l + 1) ω ≠ 0)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : R.μ A ≠ 0)
    (C : ℝ) (hC : ∀ ω ∈ A, ‖D.Q ω‖ ≤ C) :
    let R' := R.modify D.Q hD.Q_meas A hA C hC
    (∀ᵐ ω ∂(R.μ), ∀ i, R'.mult i ω = R.mult (l + 1 + i) ω ∧
      R'.lambda i ω = R.lambda (l + 1 + i) ω) ∧
    (∀ i, ∀ᵐ ω ∂(R.μ), R'.lambda i ω = lam (l + 1 + i)) ∧
    (∀ᵐ ω ∂(R.μ), R'.mult 0 ω ≠ 0) ∧
    lam (l + 1 + 1) < lam (l + 1) ∧ ∃ r : ℝ, lam (l + 1) = r := by
  classical
  let R' := R.modify D.Q hD.Q_meas A hA C hC
  obtain ⟨lamL, hlamL⟩ := hD.lam_real
  -- `𝓛 ∘ Q` grows slower than `F`
  have hgapR := Cocycle.IsLevel.ae_eventually_norm_comp_lt_growth R hD
  have hχ := R.chi_modify (fun ω => ((D.F ω).1 : Submodule ℝ X)) D.V D.Q hD.Q_meas hA hApos hC
    hD.Q_idem hD.Q_range hD.Q_ker hD.Q_equiv hD.Q_temp hgapR
  -- the exponents of `𝓛'` are those of `𝓛`, shifted
  have hshift : ∀ᵐ ω ∂(R.μ), ∀ i, R'.mult i ω = R.mult (l + 1 + i) ω ∧
      R'.lambda i ω = R.lambda (l + 1 + i) ω := by
    filter_upwards [hχ, hD.lambdaIdx_eq] with ω h1 h2 i
    exact R.mult_lambda_shift R' ω ω h1 h2 i
  have hlamR' : ∀ i, ∀ᵐ ω ∂(R.μ), R'.lambda i ω = lam (l + 1 + i) := fun i => by
    filter_upwards [hshift, hlam (l + 1 + i)] with ω h1 h2
    rw [(h1 i).2, h2]
  have hmult' : ∀ᵐ ω ∂(R.μ), R'.mult 0 ω ≠ 0 := by
    filter_upwards [hshift, hm] with ω h1 h2
    rw [(h1 0).1]; simpa using h2
  have hgapL : lam (l + 1 + 1) < lam (l + 1) := by
    obtain ⟨ω, h0, h1, h2⟩ := ((hlamR' 0).and ((hlamR' 1).and hmult')).exists
    have := R'.lambda_succ_lt ω h2
    rw [h0, h1] at this
    simpa using this
  obtain ⟨lam1, hlam1⟩ : ∃ r : ℝ, lam (l + 1) = r := by
    have htop : lam (l + 1) < ⊤ := lt_trans hD.lam_gap (by rw [hlamL]; exact EReal.coe_lt_top _)
    have hbot : lam (l + 1) ≠ ⊥ := (lt_of_le_of_lt bot_le hgapL).ne'
    exact ⟨(lam (l + 1)).toReal, (EReal.coe_toReal htop.ne hbot).symm⟩
  exact ⟨hshift, hlamR', hmult', hgapL, lam1, hlam1⟩

/-- **Inductive step**: split the next fast space off the slow space, by applying
`Cocycle.topdecomp` to the modified cocycle `𝓛 ∘ Q`. -/
theorem Cocycle.exists_level_succ (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i)
    {l : ℕ} {D : LevelData Ω X} (hD : R.IsLevel lam l D)
    (hm : ∀ᵐ ω ∂(R.μ), R.mult (l + 1) ω ≠ 0) :
    ∃ D' : LevelData Ω X, R.IsLevel lam (l + 1) D' ∧
      ∀ᵐ ω ∂(R.μ), ((D'.F ω).1 : Submodule ℝ X) = ((D.F ω).1 : Submodule ℝ X) ⊔
        ((D'.E ω).1 : Submodule ℝ X) := by
  classical
  obtain ⟨A, C, hA, hApos, hC⟩ := R.exists_bounded_set hD.Q_meas
  let R' : Cocycle Ω X := R.modify D.Q hD.Q_meas A hA C hC
  obtain ⟨lamL, hlamL⟩ := hD.lam_real
  obtain ⟨hshift, hlamR', hmult', hgapL, lam1, hlam1⟩ :=
    Cocycle.IsLevel.modified_level_spectrum R hlam hD hm A hA hApos C hC
  have hqc' : R'.IsQuasicompact := R'.isQuasicompact_iff_mult_zero.2 hmult'
  have hlam1L : lam1 < lamL := by
    have := hD.lam_gap; rw [hlam1, hlamL] at this; exact_mod_cast this
  have hchi1' : ∀ᵐ ω ∂(R'.μ), R'.chi 1 ω = (lam1 : EReal) := by
    filter_upwards [hlamR' 0] with ω h
    rw [← hlam1]; simpa using h
  have hlam2' : ∀ᵐ ω ∂(R'.μ), R'.lambda 1 ω = lam (l + 1 + 1) := hlamR' 1
  obtain ⟨m', hm'ne, E', V', P', hmult'', hE', hEpos', hP'm, hidem', hcompl', hPV', hVeq', htemp',
    hrate'⟩ := R'.topdecomp hqc' lam1 (lam (l + 1 + 1)) hchi1' hlam2'
  obtain ⟨d', rfl⟩ : ∃ d', m' = d' + 1 := ⟨m' - 1, by have := NeZero.ne m'; omega⟩
  have hgap' : lam (l + 1 + 1) < (lam1 : EReal) := hlam1 ▸ hgapL
  -- iterates of `𝓛'` along the orbit
  have horbQ := R.ae_forall_iterate (hD.Q_idem.and hD.Q_equiv)
  have hvisit := ae_exists_mem_iterate R.ergodic hA hApos
  have hTQ : ∀ᵐ ω ∂(R.μ), (∀ n, (D.Q (R.σ^[n] ω)).comp (R.iterate n ω) =
      (R.iterate n ω).comp (D.Q ω)) ∧
      ∀ᶠ n : ℕ in atTop, R'.iterate n ω = (R.iterate n ω).comp (D.Q ω) := by
    filter_upwards [horbQ, hvisit] with ω ho hv
    have hcomm : ∀ i : ℕ, (D.Q (R.σ^[i + 1] ω)).comp (R.L (R.σ^[i] ω)) =
        (R.L (R.σ^[i] ω)).comp (D.Q (R.σ^[i] ω)) := fun i => by
      rw [Function.iterate_succ_apply']; exact (ho i).2
    have hit := R.modify_iterate hD.Q_meas hA hC ω (fun i => (ho i).1) hcomm
    obtain ⟨i, hi⟩ := hv
    exact ⟨fun n => (hit n).1, (eventually_gt_atTop i).mono fun n hn => (hit n).2.1 i hn hi⟩
  have hQfix : ∀ᵐ ω ∂(R.μ), ∀ v ∈ ((D.V ω).1.1 : Submodule ℝ X), D.Q ω v = v := by
    filter_upwards [hD.Q_range, hD.Q_idem] with ω hr hid v hv
    rw [← hr] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hid
  have hQF : ∀ᵐ ω ∂(R.μ), ∀ f ∈ ((D.F ω).1 : Submodule ℝ X), D.Q ω f = 0 := by
    filter_upwards [hD.Q_ker] with ω hk f hf
    rw [← hk] at hf; exact hf
  -- the new fast space lies in the old slow space
  have hErange := ae_fastSpace_le_projection_range R R' rfl rfl E' D.Q
    hD.Q_meas hD.Q_idem hTQ hE'.1 hE'.2.2.1
  have hE'V : ∀ᵐ ω ∂(R.μ), ((E' ω).1 : Submodule ℝ X) ≤
      ((D.V ω).1.1 : Submodule ℝ X) := by
    filter_upwards [hErange, hD.Q_range] with ω hE hr
    rwa [← hr]
  -- on the old slow space, `𝓛'` and `𝓛` eventually agree
  have hagree : ∀ᵐ ω ∂(R.μ), ∀ x, D.Q ω x = x →
      ∀ᶠ n : ℕ in atTop, R'.iterate n ω x = R.iterate n ω x := by
    filter_upwards [hTQ] with ω hT x hx
    filter_upwards [hT.2] with n hn
    rw [hn]; simp [hx]
  -- the old fast sum lies in the new slow space
  have hchar' := R'.V_characterisation hgap' E' hE' V' P' hidem' hcompl' hPV' hrate'
  have hFV' : ∀ᵐ ω ∂(R.μ), ((D.F ω).1 : Submodule ℝ X) ≤ ((V' ω).1.1 : Submodule ℝ X) := by
    filter_upwards [hchar', hTQ, hQF] with ω hc hT hF f hf
    have hmem : f ∈ (((V' ω).1.1 : Submodule ℝ X) : Set X) := by
      rw [hc]
      change R'.lambdaAt ω f ≤ lam (l + 1 + 1)
      have hbot : R'.lambdaAt ω f = ⊥ := by
        have hev : ∀ᶠ n : ℕ in atTop, logEReal ‖R'.iterate n ω f‖ / (n : EReal) = ⊥ := by
          filter_upwards [hT.2, eventually_ge_atTop 1] with n hn hn1
          rw [hn]
          simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hF f hf, map_zero,
            norm_zero, logEReal_of_nonpos le_rfl, bot_div_natCast hn1]
        change limsup _ atTop = ⊥
        rw [limsup_congr hev, limsup_const]
      rw [hbot]; exact bot_le
    exact hmem
  -- the new data
  have hgood : ∀ᵐ ω ∂(R.μ), ((D.Q ω).comp (P' ω)).comp ((D.Q ω).comp (P' ω)) =
        (D.Q ω).comp (P' ω) ∧
      LinearMap.range (((D.Q ω).comp (P' ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
        ((D.V ω).1.1 : Submodule ℝ X) ⊓ ((V' ω).1.1 : Submodule ℝ X) ∧
      LinearMap.ker (((D.Q ω).comp (P' ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
        ((D.F ω).1 : Submodule ℝ X) ⊔ ((E' ω).1 : Submodule ℝ X) ∧
      IsCompl (((D.F ω).1 : Submodule ℝ X) ⊔ ((E' ω).1 : Submodule ℝ X))
        (((D.V ω).1.1 : Submodule ℝ X) ⊓ ((V' ω).1.1 : Submodule ℝ X)) ∧
      Disjoint ((D.F ω).1 : Submodule ℝ X) ((E' ω).1 : Submodule ℝ X) := by
    filter_upwards [hD.Q_idem, hD.Q_range, hD.Q_ker, hidem', hPV', hcompl', hE'V, hFV']
      with ω h1 h2 h3 h4 h5 h6 h7 h8
    exact proj_pair h1 h2 h3 h4 h5.1 h5.2 h6 h7 h8
  obtain ⟨Fnew, Vnew, hFnew, hVnew⟩ :=
    exists_total_complement_families R.μ D.F E' D.V V' D.Q P' hgood
  let Qnew : Ω → X →L[ℝ] X := fun ω => (D.Q ω).comp (P' ω)
  -- `𝓛'` and `𝓛` agree on the old slow space
  have hLeq : ∀ ω x, D.Q ω x = x → R'.L ω x = R.L ω x := by
    intro ω x hx
    change R.modL D.Q A ω x = R.L ω x
    unfold Cocycle.modL
    split_ifs <;> simp [hx]
  -- rates of `E'`, first under `𝓛'`, then under `𝓛`
  have hE'growth' : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
      (growth (R'.iterate n ω) ((E' ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
      (𝓝 (lam (l + 1))) := by
    filter_upwards [hE'.2.2.2, hEpos'] with ω h hp
    rw [hlam1]; exact tendsto_logEReal_div_of_tendsto_log hp h
  have hT'norm : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal ‖R'.iterate n ω‖ / (n : EReal))
      atTop (𝓝 (lam (l + 1))) := by
    filter_upwards [R'.ae_tendsto_chi 1, hchi1'] with ω h hc
    rw [hc] at h
    rw [hlam1]
    simpa only [bernsteinNumber_one] using h
  have hE'norm' : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
      ‖(R'.iterate n ω).comp (((E' ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal)) atTop
      (𝓝 (lam (l + 1))) := by
    filter_upwards [hT'norm, hE'growth'] with ω hT hg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg hT (fun n => ?_) (fun n => ?_)
    · exact EReal.div_le_div_right_of_nonneg (by positivity)
        (ChiOrder.logEReal_mono (growth_le_norm_comp_subtypeL _ _))
    · exact EReal.div_le_div_right_of_nonneg (by positivity)
        (ChiOrder.logEReal_mono (norm_comp_subtypeL_le _ _))
  have hE'normR : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
      ‖(R.iterate n ω).comp (((E' ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal)) atTop
      (𝓝 (lam (l + 1))) := by
    filter_upwards [hE'norm', hTQ, hE'V, hQfix] with ω h hT hEV hfix
    refine h.congr' ?_
    filter_upwards [hT.2] with n hn
    congr 3
    ext y
    simp [hn, hfix _ (hEV y.2)]
  have hE'growthR : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
      (growth (R.iterate n ω) ((E' ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
      (𝓝 (lam (l + 1))) := by
    filter_upwards [hE'growth', hTQ, hE'V, hQfix] with ω h hT hEV hfix
    refine h.congr' ?_
    filter_upwards [hT.2] with n hn
    rw [growth_congr (T := R'.iterate n ω) (T' := R.iterate n ω) fun y hy => by
      rw [hn]; simp [hfix _ (hEV hy)]]
  -- the enlarged fast sum grows at rate `λ_{l+1}`
  have hFgrowthNew : ∀ᵐ ω ∂(R.μ), ∀ b : ℝ, (b : EReal) < lam (l + 1) → ∀ᶠ n : ℕ in atTop,
      Real.exp (n * b) ≤ growth (R.iterate n ω) ((Fnew ω).1 : Submodule ℝ X) := by
    filter_upwards [hFnew, hE'growthR, hD.F_growth, hTQ, hQF, hQfix, hE'V,
      R.eventually_norm_le_of_isTempered hD.Q_temp] with ω hF hgE hgF hT hqF hqV hEV htemp b hb
    have hb1 : b < lam1 := by rw [hlam1] at hb; exact_mod_cast hb
    have hne : (Metric.sphere (0 : X) 1 ∩ ((((D.F ω).1 : Submodule ℝ X) ⊔
        ((E' ω).1 : Submodule ℝ X) : Submodule ℝ X) : Set X)).Nonempty := by
      obtain ⟨x, hx1, hxE⟩ := sphere_inter_nonempty_of_finrank (E' ω)
      exact ⟨x, hx1, Submodule.mem_sup_right hxE⟩
    rw [hF]
    exact eventually_exp_le_growth_sup ((D.F ω).1 : Submodule ℝ X)
      ((E' ω).1 : Submodule ℝ X) (fun n => R.iterate n ω) (D.Q ω)
      (fun n => D.Q (R.σ^[n] ω)) hlam1L (by simpa only [hlam1] using hgE)
      (fun b hb => hgF b (by rw [hlamL]; exact_mod_cast hb)) hqF
      (fun e he => hqV e (hEV he)) hT.1 htemp hne b hb1
  -- equivariance of the new projection
  have hQnewEquiv := ae_projection_extension_equivariant R hD E' V' P'
    (fun ω => R'.L ω) hgood hQF hQfix hE'V hE'.2.2.1 hVeq' hLeq
  refine ⟨⟨D.M + (d' + 1), d', E', Fnew, Vnew, Qnew⟩, ⟨?_, ⟨lam1, hlam1⟩, hgapL,
    fun x => measurable_apply_of_weak hD.Q_meas (hP'm x),
    R.isTempered_comp hD.Q_temp htemp' hD.Q_idem hidem' (hgood.mono fun ω h => h.1),
    hgood.mono fun ω h => h.1, ?_, ?_, hQnewEquiv, hE'.1, ?_, ?_, hE'normR, hE'growthR, ?_,
    hFgrowthNew, ?_, ?_⟩, hFnew⟩
  · filter_upwards [hD.lambdaIdx_eq, hmult'', hshift] with ω h1 h2 h3
    have hmu : R.mult (l + 1) ω = d' + 1 := by
      have := (h3 0).1; rw [add_zero] at this; rw [← this]; exact h2
    have hdef : R.mult (l + 1) ω = R.lambdaIdx (l + 1 + 1) ω - R.lambdaIdx (l + 1) ω := rfl
    change R.lambdaIdx (l + 1 + 1) ω = D.M + (d' + 1) + 1
    omega
  · filter_upwards [hgood, hVnew] with ω hg hV
    change LinearMap.range (((D.Q ω).comp (P' ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
      ((Vnew ω).1.1 : Submodule ℝ X)
    rw [hV]; exact hg.2.1
  · filter_upwards [hgood, hFnew] with ω hg hF
    change LinearMap.ker (((D.Q ω).comp (P' ω) : X →L[ℝ] X) : X →ₗ[ℝ] X) =
      ((Fnew ω).1 : Submodule ℝ X)
    rw [hF]; exact hg.2.2.1
  · filter_upwards [hE'.2.2.1, hE'V, hQfix] with ω hEq hEV hfix
    have hEq' : Submodule.map ((R'.L ω : X →L[ℝ] X) : X →ₗ[ℝ] X)
        ((E' ω).1 : Submodule ℝ X) = ((E' (R.σ ω)).1 : Submodule ℝ X) := hEq
    rw [← hEq']
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hLeq ω x (hfix x (hEV hx)))⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hLeq ω x (hfix x (hEV hx))).symm⟩
  · filter_upwards [hmult'', hshift] with ω h2 h3
    have := (h3 0).1; rw [add_zero] at this; rw [← this]; exact h2
  · filter_upwards [hFnew] with ω hF
    rw [hF]; exact le_sup_right
  · filter_upwards [hrate', hTQ] with ω h hT
    refine h.congr' ?_
    filter_upwards [hT.2] with n hn
    change _ = logEReal ‖(R.iterate n ω).comp ((D.Q ω).comp (P' ω))‖ / (n : EReal)
    rw [hn, ContinuousLinearMap.comp_assoc]
  · filter_upwards [hVnew, hchar', hD.slow_char, hagree, hQfix] with ω hV hc' hc hag hfix
    rw [hV]
    ext x
    simp only [Submodule.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hxV, hxV'⟩
      have hx' : x ∈ (((V' ω).1.1 : Submodule ℝ X) : Set X) := hxV'
      rw [hc'] at hx'
      rw [← R.lambdaAt_congr R' (hag x (hfix x hxV))]
      exact hx'
    · intro hx
      have hxV : x ∈ (((D.V ω).1.1 : Submodule ℝ X) : Set X) := by
        rw [hc]; exact hx.trans hgapL.le
      have heq := R.lambdaAt_congr R' (hag x (hfix x hxV))
      refine ⟨hxV, ?_⟩
      have hmem : x ∈ (((V' ω).1.1 : Submodule ℝ X) : Set X) := by
        rw [hc']
        change R'.lambdaAt ω x ≤ _
        rw [heq]; exact hx
      exact hmem


end MultiplicativeErgodic

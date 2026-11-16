/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Existence

/-!
# Uniqueness of the Oseledets decomposition

`mainres` is existential. This file shows its witnesses are unique: any two agree on the number
of exponents, the exponents, the dimensions and — almost everywhere — on every fast space
`E_i`, slow space `V_{i+1}` and projection `P_{i+1}` that `mainres` constrains
(`Cocycle.IsOseledets.unique`).

The slow spaces and projections are pinned by `mainres`'s own clauses. The fast spaces are not
pinned by any single clause; they are compared level by level with the decomposition the proof
of `mainres` builds, using `Cocycle.ae_eq_of_fast` on the modified cocycle `𝓛 ∘ Q` of
`Cocycle.exists_level_succ` (`Cocycle.IsLevel.fast_unique`, `Cocycle.fast_space_unique`).
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace
open scoped Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- **Uniqueness of a fast family, from growth rates.** Two measurable equivariant families of
`m`-dimensional subspaces whose growth rates are both a real `c` coincide a.e., provided
`χ_{m+1} < c`. This is `Cocycle.ae_eq_of_fast` with the eventual exponential lower bound read
off a `logEReal` limit. -/
theorem Cocycle.ae_eq_of_growth_tendsto (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    (m : ℕ) [NeZero m] {c : ℝ} {β : EReal} (hβ : β < c)
    (hchi : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω = β)
    (E E' : Ω → GrassmannianFin X m) (hEm : Measurable E) (hE'm : Measurable E')
    (hEeq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
        = ((E (R.σ ω)).1 : Submodule ℝ X))
    (hE'eq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E' ω).1 : Submodule ℝ X)
        = ((E' (R.σ ω)).1 : Submodule ℝ X))
    (hEg : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop (𝓝 (c : EReal)))
    (hE'g : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((E' ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (c : EReal))) :
    ∀ᵐ ω ∂(R.μ), E ω = E' ω := by
  obtain ⟨b, hβb, hbc⟩ := EReal.lt_iff_exists_real_btwn.1 hβ
  have hbc' : b < c := by exact_mod_cast hbc
  have hba : b < (b + c) / 2 := by linarith
  have hac : ((((b + c) / 2 : ℝ)) : EReal) < (c : EReal) := by
    exact_mod_cast (show (b + c) / 2 < c by linarith)
  have hstep : ∀ F : Ω → GrassmannianFin X m,
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((F ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (c : EReal))) →
      ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
        Real.exp ((b + c) / 2 * n) < growth (R.iterate n ω) ((F ω).1 : Submodule ℝ X) := by
    intro F hF
    filter_upwards [hF] with ω h
    filter_upwards [h.eventually_const_lt hac, eventually_ge_atTop 1] with n hn hn1
    exact (lt_logEReal_div_iff hn1 _).1 hn
  have hchi2 : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω < (b : EReal) := by
    filter_upwards [hchi] with ω h
    rw [h]; exact hβb
  exact R.ae_eq_of_fast m hba hchi2 E E' hEm hE'm hEeq hE'eq (hstep E hEg) (hstep E' hE'g)

/-- A vector in a subspace on which `𝓛^{(n)}_ω` has norm rate `c` grows at rate at most `c`. -/
theorem Cocycle.lambdaAt_le_of_norm_tendsto (R : Cocycle Ω X) {ω : Ω} {E : Submodule ℝ X}
    {c : EReal}
    (h : Tendsto (fun n : ℕ => logEReal ‖(R.iterate n ω).comp E.subtypeL‖ / (n : EReal)) atTop
      (𝓝 c)) {x : X} (hx : x ∈ E) :
    R.lambdaAt ω x ≤ c := by
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  refine R.lambdaAt_le_of_eventually_le (K := ‖x‖) ?_
  filter_upwards [eventually_lt_exp_of_tendsto hz h] with n hn
  have h1 : ‖R.iterate n ω x‖ ≤ ‖(R.iterate n ω).comp E.subtypeL‖ * ‖x‖ := by
    have := ((R.iterate n ω).comp E.subtypeL).le_opNorm ⟨x, hx⟩
    simpa using this
  calc ‖R.iterate n ω x‖ ≤ ‖(R.iterate n ω).comp E.subtypeL‖ * ‖x‖ := h1
    _ ≤ Real.exp (z * n) * ‖x‖ := by gcongr
    _ = ‖x‖ * Real.exp (n * z) := by rw [mul_comm, mul_comm z]

/-- `λ_1 = χ_{m+1}` once `m = m_0 ≠ 0`: the second distinct exponent sits at index `m_0 + 1`. -/
theorem Cocycle.lambda_one_eq_chi (R : Cocycle Ω X) {ω : Ω} {m : ℕ} (hm : R.mult 0 ω = m)
    (hm0 : m ≠ 0) : R.lambda 1 ω = R.chi (m + 1) ω := by
  have h : R.lambdaIdx 1 ω = m + 1 := by
    have : R.mult 0 ω = R.lambdaIdx 1 ω - 1 := rfl
    omega
  change R.chi (R.lambdaIdx 1 ω) ω = _
  rw [h]

/-- **Uniqueness of the fast space at level `l + 1`.** Inside the slow space `V` of a level-`l`
decomposition, two measurable equivariant families of dimension `m = m_{l+2}` growing at rate
`λ_{l+2}` coincide a.e. Run `ae_eq_of_growth_tendsto` on the modified cocycle `𝓛 ∘ Q`, whose
exponents are those of `𝓛` shifted past the fast sum (`chi_modify`), and on which `𝓛` and
`𝓛 ∘ Q` eventually agree along `V`. -/
theorem Cocycle.IsLevel.fast_unique (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i)
    {l : ℕ} {D : LevelData Ω X} (hD : R.IsLevel lam l D) {m : ℕ} [NeZero m]
    (hdim : ∀ᵐ ω ∂(R.μ), R.mult (l + 1) ω = m)
    (E E' : Ω → GrassmannianFin X m) (hEm : Measurable E) (hE'm : Measurable E')
    (hEeq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
        = ((E (R.σ ω)).1 : Submodule ℝ X))
    (hE'eq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E' ω).1 : Submodule ℝ X)
        = ((E' (R.σ ω)).1 : Submodule ℝ X))
    (hEV : ∀ᵐ ω ∂(R.μ), ((E ω).1 : Submodule ℝ X) ≤ ((D.V ω).1.1 : Submodule ℝ X))
    (hE'V : ∀ᵐ ω ∂(R.μ), ((E' ω).1 : Submodule ℝ X) ≤ ((D.V ω).1.1 : Submodule ℝ X))
    (hEg : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (lam (l + 1))))
    (hE'g : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((E' ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (lam (l + 1)))) :
    ∀ᵐ ω ∂(R.μ), E ω = E' ω := by
  classical
  obtain ⟨A, C, hA, hApos, hC⟩ := R.exists_bounded_set hD.Q_meas
  let R' : Cocycle Ω X := R.modify D.Q hD.Q_meas A hA C hC
  obtain ⟨lamL, hlamL⟩ := hD.lam_real
  -- `𝓛 ∘ Q` grows slower than `F` (as in `exists_level_succ`)
  have hgapR : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, ‖(R.iterate n ω).comp (D.Q ω)‖ <
      growth (R.iterate n ω) ((D.F ω).1 : Submodule ℝ X) := by
    obtain ⟨b1, hb1, hb1'⟩ := EReal.lt_iff_exists_real_btwn.1 hD.lam_gap
    obtain ⟨b2, hb2, hb2'⟩ := EReal.lt_iff_exists_real_btwn.1 hb1'
    have hb12 : b1 < b2 := by exact_mod_cast hb2
    filter_upwards [hD.slow_rate, hD.F_growth] with ω hs hF
    filter_upwards [eventually_lt_exp_of_tendsto hb1 hs, hF b2 hb2'] with n h1 h2
    refine lt_of_lt_of_le h1 (le_trans ?_ h2)
    rw [mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hb12.le (Nat.cast_nonneg _))
  have hχ := R.chi_modify (fun ω => ((D.F ω).1 : Submodule ℝ X)) D.V D.Q hD.Q_meas hA hApos hC
    hD.Q_idem hD.Q_range hD.Q_ker hD.Q_equiv hD.Q_temp hgapR
  have hshift : ∀ᵐ ω ∂(R.μ), ∀ i, R'.mult i ω = R.mult (l + 1 + i) ω ∧
      R'.lambda i ω = R.lambda (l + 1 + i) ω := by
    filter_upwards [hχ, hD.lambdaIdx_eq] with ω h1 h2 i
    exact R.mult_lambda_shift R' ω ω h1 h2 i
  have hlamR' : ∀ i, ∀ᵐ ω ∂(R.μ), R'.lambda i ω = lam (l + 1 + i) := fun i => by
    filter_upwards [hshift, hlam (l + 1 + i)] with ω h1 h2
    rw [(h1 i).2, h2]
  have hmult' : ∀ᵐ ω ∂(R.μ), R'.mult 0 ω = m := by
    filter_upwards [hshift, hdim] with ω h1 h2
    rw [(h1 0).1]; simpa using h2
  have hgapL : lam (l + 1 + 1) < lam (l + 1) := by
    obtain ⟨ω, h0, h1, h2⟩ := ((hlamR' 0).and ((hlamR' 1).and hmult')).exists
    have := R'.lambda_succ_lt ω (i := 0) (by rw [h2]; exact NeZero.ne m)
    rw [h0, h1] at this
    simpa using this
  obtain ⟨lam1, hlam1⟩ : ∃ r : ℝ, lam (l + 1) = r := by
    have htop : lam (l + 1) < ⊤ := lt_trans hD.lam_gap (by rw [hlamL]; exact EReal.coe_lt_top _)
    have hbot : lam (l + 1) ≠ ⊥ := (lt_of_le_of_lt bot_le hgapL).ne'
    exact ⟨(lam (l + 1)).toReal, (EReal.coe_toReal htop.ne hbot).symm⟩
  -- the relevant exponent of `𝓛'`
  have hchi' : ∀ᵐ ω ∂(R'.μ), R'.chi (m + 1) ω = lam (l + 1 + 1) := by
    filter_upwards [hlamR' 1, hmult'] with ω h1 h2
    rw [← R'.lambda_one_eq_chi h2 (NeZero.ne m), h1]
  -- iterates of `𝓛'` along the orbit
  have horbQ := R.ae_forall_iterate (hD.Q_idem.and hD.Q_equiv)
  have hvisit := ae_exists_mem_iterate R.ergodic hA hApos
  have hTQ : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, R'.iterate n ω = (R.iterate n ω).comp (D.Q ω) := by
    filter_upwards [horbQ, hvisit] with ω ho hv
    have hcomm : ∀ i : ℕ, (D.Q (R.σ^[i + 1] ω)).comp (R.L (R.σ^[i] ω)) =
        (R.L (R.σ^[i] ω)).comp (D.Q (R.σ^[i] ω)) := fun i => by
      rw [Function.iterate_succ_apply']; exact (ho i).2
    have hit := R.modify_iterate hD.Q_meas hA hC ω (fun i => (ho i).1) hcomm
    obtain ⟨i, hi⟩ := hv
    exact (eventually_gt_atTop i).mono fun n hn => (hit n).2.1 i hn hi
  have hQfix : ∀ᵐ ω ∂(R.μ), ∀ v ∈ ((D.V ω).1.1 : Submodule ℝ X), D.Q ω v = v := by
    filter_upwards [hD.Q_range, hD.Q_idem] with ω hr hid v hv
    rw [← hr] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hid
  -- transfer the hypotheses on a family inside `V` from `𝓛` to `𝓛'`
  have htransfer : ∀ F : Ω → GrassmannianFin X m,
      (∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((F ω).1 : Submodule ℝ X)
        = ((F (R.σ ω)).1 : Submodule ℝ X)) →
      (∀ᵐ ω ∂(R.μ), ((F ω).1 : Submodule ℝ X) ≤ ((D.V ω).1.1 : Submodule ℝ X)) →
      (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((F ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (lam (l + 1)))) →
      (∀ᵐ ω ∂(R'.μ), Submodule.map (R'.L ω : X →ₗ[ℝ] X) ((F ω).1 : Submodule ℝ X)
        = ((F (R'.σ ω)).1 : Submodule ℝ X)) ∧
      (∀ᵐ ω ∂(R'.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R'.iterate n ω) ((F ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (lam1 : EReal))) := by
    intro F hFeq hFV hFg
    refine ⟨?_, ?_⟩
    · filter_upwards [hFeq, hFV, hQfix] with ω heq hV hfix
      change Submodule.map (R.modL D.Q A ω : X →ₗ[ℝ] X) ((F ω).1 : Submodule ℝ X) =
        ((F (R.σ ω)).1 : Submodule ℝ X)
      rw [← heq]
      unfold Cocycle.modL
      split_ifs
      · ext y
        simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe,
          ContinuousLinearMap.coe_comp, Function.comp_apply]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hfix x (hV hx)]⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hfix x (hV hx)]⟩
      · rfl
    · filter_upwards [hFg, hFV, hQfix, hTQ] with ω hg hV hfix hT
      rw [← hlam1]
      refine hg.congr' ?_
      filter_upwards [hT] with n hn
      show logEReal (growth (R.iterate n ω) _) / (n : EReal) =
        logEReal (growth (R'.iterate n ω) _) / (n : EReal)
      rw [hn, growth_congr (T := R.iterate n ω)
        (T' := (R.iterate n ω).comp (D.Q ω)) (E := ((F ω).1 : Submodule ℝ X))
        (fun y hy => by simp [hfix y (hV hy)])]
  obtain ⟨h1, h2⟩ := htransfer E hEeq hEV hEg
  obtain ⟨h1', h2'⟩ := htransfer E' hE'eq hE'V hE'g
  exact R'.ae_eq_of_growth_tendsto m (β := lam (l + 1 + 1)) (by rw [← hlam1]; exact hgapL)
    hchi' E E' hEm hE'm h1 h1' h2 h2'

/-- Every level of the decomposition exists while the multiplicities are nonzero. -/
theorem Cocycle.exists_isLevel (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i) :
    ∀ l, (∀ᵐ ω ∂(R.μ), R.mult l ω ≠ 0) → ∃ D : LevelData Ω X, R.IsLevel lam l D := by
  intro l hl
  induction l with
  | zero =>
    obtain ⟨D, hD, -⟩ := R.exists_level_zero hlam ((R.isQuasicompact_iff_mult_zero).2 hl)
    exact ⟨D, hD⟩
  | succ l ih =>
    obtain ⟨D, hD⟩ := ih (hl.mono fun ω h => R.mult_ne_zero_of_succ ω h)
    obtain ⟨D', hD', -⟩ := R.exists_level_succ hlam hD hl
    exact ⟨D', hD'⟩

/-- **Uniqueness of the `i`-th fast space.** Two measurable equivariant families of dimension
`m_{i+1}`, each with norm rate and growth rate `λ_{i+1}`, coincide a.e. (The dimensions are
allowed to be given by different numerals, which the hypotheses then force to agree.)

For `i = 0` this is `ae_eq_of_growth_tendsto` directly, with `χ_{m+1} = λ_2`. For `i = l + 1`
both families lie in the slow space `V_{l+1} = {λ ≤ λ_{l+2}}` of the level-`l` decomposition,
since their norm rate is `λ_{l+2}`, and `IsLevel.fast_unique` applies. -/
theorem Cocycle.fast_space_unique (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i)
    (i : ℕ) {m m' : ℕ} [NeZero m] [NeZero m']
    (hm : ∀ᵐ ω ∂(R.μ), R.mult i ω = m) (hm' : ∀ᵐ ω ∂(R.μ), R.mult i ω = m')
    (E : Ω → GrassmannianFin X m) (E' : Ω → GrassmannianFin X m')
    (hEm : Measurable E) (hE'm : Measurable E')
    (hEeq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
        = ((E (R.σ ω)).1 : Submodule ℝ X))
    (hE'eq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E' ω).1 : Submodule ℝ X)
        = ((E' (R.σ ω)).1 : Submodule ℝ X))
    (hEn : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        ‖(R.iterate n ω).comp (((E ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal)) atTop
        (𝓝 (lam i)))
    (hE'n : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        ‖(R.iterate n ω).comp (((E' ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal)) atTop
        (𝓝 (lam i)))
    (hEg : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop (𝓝 (lam i)))
    (hE'g : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((E' ω).1 : Submodule ℝ X)) / (n : EReal)) atTop
        (𝓝 (lam i))) :
    ∀ᵐ ω ∂(R.μ), ((E ω).1 : Submodule ℝ X) = ((E' ω).1 : Submodule ℝ X) := by
  obtain rfl : m = m' := by
    obtain ⟨ω, h1, h2⟩ := (hm.and hm').exists
    rw [← h1, ← h2]
  have hmi : ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0 := by
    filter_upwards [hm] with ω h
    rw [h]; exact NeZero.ne m
  suffices h : ∀ᵐ ω ∂(R.μ), E ω = E' ω by
    filter_upwards [h] with ω h
    rw [h]
  cases i with
  | zero =>
    -- `λ_1` is real and strictly above `λ_2 = χ_{m+1}`
    have hgap : lam 1 < lam 0 := by
      obtain ⟨ω, h0, h1, h2⟩ := ((hlam 0).and ((hlam 1).and hmi)).exists
      have := R.lambda_succ_lt ω h2
      rwa [h0, h1] at this
    obtain ⟨c, hc⟩ : ∃ r : ℝ, lam 0 = r := by
      obtain ⟨ω, h0, h1⟩ := ((hlam 0).and R.ae_chi_one_lt_top).exists
      have htop : lam 0 < ⊤ := by rw [← h0]; exact h1
      have hbot : lam 0 ≠ ⊥ := (lt_of_le_of_lt bot_le hgap).ne'
      exact ⟨(lam 0).toReal, (EReal.coe_toReal htop.ne hbot).symm⟩
    have hchi : ∀ᵐ ω ∂(R.μ), R.chi (m + 1) ω = lam 1 := by
      filter_upwards [hm, hlam 1] with ω h1 h2
      rw [← R.lambda_one_eq_chi h1 (NeZero.ne m), h2]
    rw [hc] at hEg hE'g hgap
    exact R.ae_eq_of_growth_tendsto m hgap hchi E E' hEm hE'm hEeq hE'eq hEg hE'g
  | succ l =>
    obtain ⟨D, hD⟩ := R.exists_isLevel hlam l (hmi.mono fun ω h => R.mult_ne_zero_of_succ ω h)
    have hV : ∀ F : Ω → GrassmannianFin X m,
        (∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
          ‖(R.iterate n ω).comp (((F ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal)) atTop
          (𝓝 (lam (l + 1)))) →
        ∀ᵐ ω ∂(R.μ), ((F ω).1 : Submodule ℝ X) ≤ ((D.V ω).1.1 : Submodule ℝ X) := by
      intro F hF
      filter_upwards [hF, hD.slow_char] with ω h hc x hx
      change x ∈ (((D.V ω).1.1 : Submodule ℝ X) : Set X)
      rw [hc]
      exact R.lambdaAt_le_of_norm_tendsto h hx
    exact hD.fast_unique R hlam hm E E' hEm hE'm hEeq hE'eq (hV E hEn) (hV E' hE'n) hEg hE'g

/-- **The conclusion of `mainres`, as a predicate on its witnesses.** `R.IsOseledets Lval lam mdim
E V P` says verbatim what `mainres` asserts of the data it produces; `mainres` is
`∃ Lval lam mdim E V P, R.IsOseledets Lval lam mdim E V P` (`Cocycle.exists_isOseledets`), and
`Cocycle.IsOseledets.unique` says those witnesses are unique. -/
def Cocycle.IsOseledets (R : Cocycle Ω X) (Lval : ℕ∞) (lam : ℕ → EReal) (mdim : ℕ → ℕ)
    (E : ∀ i : ℕ, Ω → GrassmannianFin X (mdim i + 1))
    (V : ℕ → Ω → Submodule ℝ X) (P : ℕ → Ω → X →L[ℝ] X) : Prop :=
  1 ≤ Lval ∧
  (∀ i : ℕ, (i : ℕ∞) < Lval → ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i) ∧
  (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval ↔ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0) ∧
  ((2 : ℕ∞) ≤ Lval ↔ R.IsQuasicompact) ∧
  (∀ i, Measurable (E i)) ∧
  (∀ i, ∀ x : X, Measurable fun ω => P i ω x) ∧
  (∀ i, R.IsTempered (P i)) ∧
  (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval → ∀ᵐ ω ∂(R.μ),
    R.mult i ω = mdim i + 1 ∧
    Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E i ω).1 : Submodule ℝ X)
      = ((E i (R.σ ω)).1 : Submodule ℝ X) ∧
    Tendsto (fun n : ℕ => logEReal
        ‖(R.iterate n ω).comp (((E i ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal))
      atTop (nhds (lam i)) ∧
    Tendsto (fun n : ℕ => logEReal
        (growth (R.iterate n ω) ((E i ω).1 : Submodule ℝ X)) / (n : EReal))
      atTop (nhds (lam i))) ∧
  (∀ l : ℕ, ((l + 2 : ℕ) : ℕ∞) ≤ Lval → ∀ᵐ ω ∂(R.μ),
    IsCompl (⨆ i ∈ Finset.range (l + 1), ((E i ω).1 : Submodule ℝ X)) (V (l + 1) ω) ∧
    Submodule.map (R.L ω : X →ₗ[ℝ] X) (V (l + 1) ω) ≤ V (l + 1) (R.σ ω) ∧
    (P (l + 1) ω).comp (P (l + 1) ω) = P (l + 1) ω ∧
    V (l + 1) ω = LinearMap.range ((P (l + 1) ω : X →ₗ[ℝ] X)) ∧
    (∀ x ∈ ⨆ i ∈ Finset.range (l + 1), ((E i ω).1 : Submodule ℝ X), P (l + 1) ω x = 0) ∧
    (V (l + 1) ω : Set X) = {x : X | R.lambdaAt ω x ≤ lam (l + 1)})

/-- `mainres`, restated through `Cocycle.IsOseledets`. -/
theorem Cocycle.exists_isOseledets (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] [Nontrivial X] :
    ∃ (Lval : ℕ∞) (lam : ℕ → EReal) (mdim : ℕ → ℕ)
      (E : ∀ i : ℕ, Ω → GrassmannianFin X (mdim i + 1))
      (V : ℕ → Ω → Submodule ℝ X) (P : ℕ → Ω → X →L[ℝ] X),
      R.IsOseledets Lval lam mdim E V P :=
  mainres_existence R

/-- An `ℕ∞` that is at least `1` is determined by which `i + 2` lie below it. -/
theorem ENat.eq_of_forall_add_two_le_iff {L L' : ℕ∞} (h1 : 1 ≤ L) (h1' : 1 ≤ L')
    (h : ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ L ↔ ((i + 2 : ℕ) : ℕ∞) ≤ L') : L = L' := by
  have key : ∀ {A B : ℕ∞}, 1 ≤ B →
      (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ A → ((i + 2 : ℕ) : ℕ∞) ≤ B) → A ≤ B := by
    intro A B hB hAB
    by_contra hlt
    rw [not_le] at hlt
    lift B to ℕ using hlt.ne_top
    have hB1 : 1 ≤ B := by exact_mod_cast hB
    have hle : ((B + 1 : ℕ) : ℕ∞) ≤ A := by
      push_cast
      exact Order.add_one_le_of_lt hlt
    have := hAB (B - 1) (by rw [show B - 1 + 2 = B + 1 by omega]; exact hle)
    rw [show B - 1 + 2 = B + 1 by omega, Nat.cast_le] at this
    omega
  exact le_antisymm (key h1' fun i hi => (h i).1 hi) (key h1 fun i hi => (h i).2 hi)

omit [MeasurableSpace X] in
/-- Two idempotents with the same range `V`, both killing a complement `F` of it, agree. -/
theorem proj_eq_of_isCompl {P P' : X →L[ℝ] X} {F V : Submodule ℝ X} (hc : IsCompl F V)
    (hP : P.comp P = P) (hP' : P'.comp P' = P')
    (hr : LinearMap.range (P : X →ₗ[ℝ] X) = V) (hr' : LinearMap.range (P' : X →ₗ[ℝ] X) = V)
    (hk : ∀ x ∈ F, P x = 0) (hk' : ∀ x ∈ F, P' x = 0) : P = P' := by
  have hfix : ∀ Q : X →L[ℝ] X, Q.comp Q = Q → LinearMap.range (Q : X →ₗ[ℝ] X) = V →
      ∀ v ∈ V, Q v = v := by
    intro Q hQ hQr v hv
    rw [← hQr] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hQ
  ext x
  have hx : x ∈ F ⊔ V := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨f, hf, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, map_add, hk f hf, hk' f hf, hfix P hP hr v hv, hfix P' hP' hr' v hv]

/-- **Uniqueness in the main theorem.** Any two witnesses to `mainres` agree: the number `L` of
distinct exponents, the exponents themselves, the dimensions, and — almost everywhere — every
fast space `E_i`, slow space `V_{i+1}` and projection `P_{i+1}` that the theorem constrains
(those with `i + 2 ≤ L`). Nothing is claimed about indices past `L`, which `mainres` leaves
unconstrained.

The slow spaces are pinned by their characterisation `{x : λ_ω(x) ≤ λ_{i+2}}`, and the
projections by their range and kernel. The fast spaces are the substance: they are compared
level by level with the decomposition the proof of `mainres` builds (`Cocycle.fast_space_unique`).
-/
theorem Cocycle.IsOseledets.unique (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X]
    {L L' : ℕ∞} {lam lam' : ℕ → EReal} {mdim mdim' : ℕ → ℕ}
    {E : ∀ i : ℕ, Ω → GrassmannianFin X (mdim i + 1)}
    {E' : ∀ i : ℕ, Ω → GrassmannianFin X (mdim' i + 1)}
    {V V' : ℕ → Ω → Submodule ℝ X} {P P' : ℕ → Ω → X →L[ℝ] X}
    (h : R.IsOseledets L lam mdim E V P) (h' : R.IsOseledets L' lam' mdim' E' V' P') :
    L = L' ∧ (∀ i : ℕ, (i : ℕ∞) < L → lam i = lam' i) ∧
    ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ L → mdim i = mdim' i ∧ ∀ᵐ ω ∂(R.μ),
      ((E i ω).1 : Submodule ℝ X) = ((E' i ω).1 : Submodule ℝ X) ∧
      V (i + 1) ω = V' (i + 1) ω ∧ P (i + 1) ω = P' (i + 1) ω := by
  obtain ⟨h1, hlam, hL, -, hEm, -, -, hE, hdec⟩ := h
  obtain ⟨h1', hlam', hL', -, hEm', -, -, hE', hdec'⟩ := h'
  have hLL : L = L' :=
    ENat.eq_of_forall_add_two_le_iff h1 h1' fun i => (hL i).trans (hL' i).symm
  subst hLL
  -- the canonical exponents
  choose c hc using R.exists_lambda_ae_eq
  have hlamc : ∀ i : ℕ, (i : ℕ∞) < L → lam i = c i := fun i hi => by
    obtain ⟨ω, h1, h2⟩ := ((hlam i hi).and (hc i)).exists
    rw [← h1, h2]
  have hlamc' : ∀ i : ℕ, (i : ℕ∞) < L → lam' i = c i := fun i hi => by
    obtain ⟨ω, h1, h2⟩ := ((hlam' i hi).and (hc i)).exists
    rw [← h1, h2]
  have hlt : ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ L → ((i + 1 : ℕ) : ℕ∞) < L := fun i hi =>
    lt_of_lt_of_le (by exact_mod_cast (show i + 1 < i + 2 by omega)) hi
  have hlt0 : ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ L → (i : ℕ∞) < L := fun i hi =>
    lt_of_lt_of_le (by exact_mod_cast (show i < i + 2 by omega)) hi
  have hEeq : ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ L → ∀ᵐ ω ∂(R.μ),
      ((E i ω).1 : Submodule ℝ X) = ((E' i ω).1 : Submodule ℝ X) := by
    intro i hi
    have hA := hE i hi
    have hB := hE' i hi
    rw [hlamc i (hlt0 i hi)] at hA
    rw [hlamc' i (hlt0 i hi)] at hB
    exact R.fast_space_unique hc i (hA.mono fun ω h => h.1) (hB.mono fun ω h => h.1) (E i) (E' i)
      (hEm i) (hEm' i) (hA.mono fun ω h => h.2.1) (hB.mono fun ω h => h.2.1)
      (hA.mono fun ω h => h.2.2.1) (hB.mono fun ω h => h.2.2.1)
      (hA.mono fun ω h => h.2.2.2) (hB.mono fun ω h => h.2.2.2)
  refine ⟨rfl, fun i hi => (hlamc i hi).trans (hlamc' i hi).symm, fun i hi => ⟨?_, ?_⟩⟩
  · obtain ⟨ω, h1, h2⟩ := ((hE i hi).and (hE' i hi)).exists
    have := h1.1.symm.trans h2.1
    omega
  · have hall : ∀ᵐ ω ∂(R.μ), ∀ j : ℕ, j ∈ Finset.range (i + 1) →
        ((E j ω).1 : Submodule ℝ X) = ((E' j ω).1 : Submodule ℝ X) := by
      rw [ae_all_iff]
      intro j
      by_cases hj : j ∈ Finset.range (i + 1)
      · have hj' : j < i + 1 := Finset.mem_range.1 hj
        have hj2 : ((j + 2 : ℕ) : ℕ∞) ≤ L :=
          le_trans (by exact_mod_cast (show j + 2 ≤ i + 2 by omega)) hi
        filter_upwards [hEeq j hj2] with ω h _
        exact h
      · exact Eventually.of_forall fun ω h => absurd h hj
    filter_upwards [hall, hdec i hi, hdec' i hi] with ω hall hd hd'
    have hsup : (⨆ j ∈ Finset.range (i + 1), ((E j ω).1 : Submodule ℝ X)) =
        ⨆ j ∈ Finset.range (i + 1), ((E' j ω).1 : Submodule ℝ X) :=
      iSup_congr fun j => iSup_congr fun hj => hall j hj
    have hVV : V (i + 1) ω = V' (i + 1) ω := by
      apply SetLike.coe_injective
      rw [hd.2.2.2.2.2, hd'.2.2.2.2.2, hlamc (i + 1) (hlt i hi), hlamc' (i + 1) (hlt i hi)]
    refine ⟨hall i (Finset.self_mem_range_succ i), hVV, ?_⟩
    obtain ⟨hc1, -, hid, hr, hk, -⟩ := hd
    obtain ⟨-, -, hid', hr', hk', -⟩ := hd'
    rw [← hsup] at hk'
    exact proj_eq_of_isCompl hc1 hid hid' hr.symm (hr'.symm.trans hVV.symm) hk hk'

end MultiplicativeErgodic

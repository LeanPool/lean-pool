/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module


public import LeanPool.Vlasov.OT.FlowDifferentiability
import all LeanPool.Vlasov.OT.FlowDifferentiability
public import LeanPool.Vlasov.OT.TestApproximation
import all LeanPool.Vlasov.OT.TestApproximation
import all LeanPool.Vlasov.OT.FrozenField
import all LeanPool.Vlasov.ForMathlib.VariationalEquation

/-!
# Weak ⟹ Lagrangian: every weak Vlasov solution is transported by its characteristic flow

(tex: thm:weak-lagrangian)

The forward direction — a Lagrangian solution is weak — is immediate
(`IsLagrangianVlasovSolution.1`; the substantive pushforward-solves-weak content is
`vlasovSolutionViaPushforward_isVlasovSolutionOn`, `CharacteristicFlow.lean`).  This file builds
the **converse**: under the strengthened assumption `AssW2` (`W ∈ C²`, see `Basic.lean`), every
**weak** Vlasov solution on a window `[0,T]` is **Lagrangian** — i.e. it is the pushforward of its
initial datum under the characteristic flow it generates.  This is the superposition /
probabilistic-representation principle for the phase-space continuity equation
`∂_t f + div_{(x,v)}(b_f · f) = 0` with the Lipschitz field
`b_f(t,x,v) = (v, −(∇W ∗ ρ_t)(x))`, `ρ_t = spatialMarginal (f t)`.

It upgrades the project's uniqueness from "unique *Lagrangian* solution" to "unique *weak* (PDE)
solution".  The marquee `vlasovWellPosedness` / `dobrushin` are untouched and stay at `AssW`.

## Strategy (three ingredients)

Freeze the field at `ρ^f_t := spatialMarginal (f t)` (the field
`vlasovVectorField gradW ρ t z = (z.2, −(∇W ∗ ρ_t)(z.1))` is already parametric in `ρ`).  Let
`g_t := (Φ_t)_# (f 0)` be the pushforward along the flow `Φ` of this *frozen* field.  Then `f`
and `g` solve the **same linear** continuity equation with the same datum, so `f = g`, and `g` is
Lagrangian by construction.

1. **Flow existence for the frozen `ρ^f`** — reuse `exists_vlasov_characteristicFlow_global_smallT`.
2. **Pushforward solves the frozen linear weak eq** — reuse the *generic* helpers SC.1–SC.4
   (`vlasov_traj_chain_rule` etc., stated over an arbitrary `ρ`) at `ρ := ρ^f`, bypassing the
   self-consistent wrapper `vlasovSolutionViaPushforward_isVlasovSolutionOn`.
3. **Linear continuity-equation uniqueness `f = g`** — the crux (absent from Mathlib).  Dual
   transported test function `ψ_s(z) := φ(Φ_{s→T}(z))`: `s ↦ ∫ ψ_s dμ_s` is constant (the
   `∂_sψ + ⟨b,∇ψ⟩ = 0` cancellation), so `∫φ dμ_T = ∫ψ_0 dμ_0`, equal for `f` and `g` (shared
   `μ_0`); ranging over `φ` gives `f T = g T`.

## Decomposition roadmap (sub-lemmas added per build-layer)

Setup layer (C1):
* #1 `vlasov_frozenField_pushforward_isWeakSolOn` — `g` solves the frozen linear weak eq on
  `Ioo 0 T`; recompose SC.1 + SC.2 at `ρ := ρ^f`.
* #2 `exists_frozenField_charFlow_On` — instantiate `exists_vlasov_characteristicFlow_global_smallT`
  at `ρ := ρ^f`, discharging the integrability / continuity / moment hypotheses.

Final-step layer (C2, crux-independent):
* #7 `transportedIntegral_const_On` — zero derivative on `Ioo` + `ContinuousOn` on `Icc` ⟹ const.
* #9 `measure_eq_of_forall_Cc_integral_eq` — `∫φ dμ = ∫φ dν` for all `C_c^∞ φ` ⟹ `μ = ν`, via
  smooth approximation + `ext_of_forall_integral_eq_of_IsFiniteMeasure` (cf. `Wasserstein.lean`).

Crux layer (C3):
* #3 `charFlow_hasFDerivAt_in_initialPoint` — **the variational equation**: `z ↦ Φ_{s→T}(z)` is C¹
  (`HasFDerivAt`), derivative solving `M' = (D_z b)·M`.  Sub-steps: 3.1 variational-ODE existence /
  uniqueness, 3.2 joint `(t,z)` continuity, 3.3 difference-quotient `o(‖h‖)` via Gronwall (the
  heart), 3.4 assemble `HasFDerivAt` → C¹.  Needs `AssW2.gradContDiff`.
* #4 `weakSolOn_test_C1c_of_Cinftyc` — extend `IsVlasovSolutionOn`'s test class from `C_c^∞` to
  `C¹_c` (mollification + DCT), since `ψ_s = φ∘Φ_{s→T}` is only `C¹_c` with a C¹ flow.
* #5 `transportedTestFunction_props` — `ψ_s` is `C¹`, compactly supported, with
  `∂_sψ_s + ⟨b,∇ψ_s⟩ = 0`.
* #6 `transportedIntegral_hasDerivWithinAt_zero` — `s ↦ ∫ ψ_s dμ_s` has zero derivative on
  `Ioo 0 T` for both `μ = f` and `μ = g`.

Assembly (C4):
* #8 `finalTime_integral_eq_of_weak` — combine #7 for `f` and `g` ⟹ `∫φ df_T = ∫φ dg_T` ∀ `C_c^∞ φ`.
* #10 the top theorem below — package `g`'s flow witness + `f = g` into
  `IsLagrangianVlasovSolutionOn`.

Universal (non-`_On`) form via window-gluing is a deferred follow-on (C5).
-/

@[expose] public section

namespace Vlasov

open MeasureTheory

-- Retain the compiled auxiliary theorem names from before the analysis module was extracted.
private alias picardIter_continuousOn_and_bound._simp_1_1 :=
  _root_.Vlasov.picardIter_continuousOn_and_bound._simp_1_1

private alias picardIter_continuousOn_and_bound._simp_1_2 :=
  _root_.Vlasov.picardIter_continuousOn_and_bound._simp_1_2

private alias picardIter_continuousOn_and_bound._simp_1_3 :=
  _root_.Vlasov.picardIter_continuousOn_and_bound._simp_1_3

private alias picardIter_continuousOn_and_bound._simp_1_4 :=
  _root_.Vlasov.picardIter_continuousOn_and_bound._simp_1_4

private alias picardIter_continuousOn_and_bound._simp_1_5 :=
  _root_.Vlasov.picardIter_continuousOn_and_bound._simp_1_5

private alias picardIter_continuousOn_and_bound._simp_1_6 :=
  _root_.Vlasov.picardIter_continuousOn_and_bound._simp_1_6

private alias picardIter_continuousOn_and_bound._simp_1_7 :=
  _root_.Vlasov.picardIter_continuousOn_and_bound._simp_1_7

private alias hasFDerivAt_of_continuous_partials._abel_1_1 :=
  _root_.Vlasov.hasFDerivAt_of_continuous_partials._abel_1_1

private alias hasFDerivAt_of_continuous_partials_open._abel_1_1 :=
  _root_.Vlasov.hasFDerivAt_of_continuous_partials_open._abel_1_1


variable {d : ℕ} [NeZero d]

private alias convolveFunctionMeasure_hasFDerivAt._abel_1_2 :=
  _root_.Vlasov.convolveFunctionMeasure_hasFDerivAt._abel_1_2

private alias exists_frozenField_charFlow_On._simp_1_1 :=
  _root_.Vlasov.exists_frozenField_charFlow_On._simp_1_1

private alias charFlow_hasFDerivAt_of_fundamentalMatrix._simp_1_1 :=
  _root_.Vlasov.charFlow_hasFDerivAt_of_fundamentalMatrix._simp_1_1

private alias vlasovField_taylorRemainder_uniform._abel_1_4 :=
  _root_.Vlasov.vlasovField_taylorRemainder_uniform._abel_1_4

private alias vlasovField_taylorRemainder_uniform._simp_1_2 :=
  _root_.Vlasov.vlasovField_taylorRemainder_uniform._simp_1_2

private alias vlasovField_taylorRemainder_uniform._simp_1_3 :=
  _root_.Vlasov.vlasovField_taylorRemainder_uniform._simp_1_3

private alias inner_integrand_integrable._simp_1_1 :=
  _root_.Vlasov.inner_integrand_integrable._simp_1_1

private alias inner_integrand_integrable._simp_1_2 :=
  _root_.Vlasov.inner_integrand_integrable._simp_1_2

-- ── Helpers for `transportedIntegral_hasDerivAt_zero`, extracted from its proof body. ──

omit [NeZero d] in
/-- Per-`z` phase-space ODE of a characteristic flow on the open window, in
`vlasovVectorField` form. -/
lemma charFlow_ode_of_isCharacteristicFlowOn
    (gradW : PhysSpace d → PhysSpace d) (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ) :
    ∀ z : PhaseSpace d, ∀ s' ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s'' => (charX s'' z, charV s'' z))
        (vlasovVectorField gradW ρ s' (charX s' z, charV s' z)) s' := by
  intro z s' hs'
  have hX := hflow.2.1 s' hs' z (Set.mem_univ z)
  have hV := hflow.2.2 s' hs' z (Set.mem_univ z)
  simpa [vlasovVectorField] using hX.prodMk hV

omit [NeZero d] in
/-- A Fréchet derivative applied to a phase-space vector decomposes as inner
products against the two partial-gradient slices. -/
lemma fderiv_apply_eq_inner_gradientSlices (θ : PhaseSpace d → ℝ) (z : PhaseSpace d)
    (hθ : DifferentiableAt ℝ θ z) (p q : PhysSpace d) :
    (fderiv ℝ θ z) ((p, q) : PhaseSpace d)
      = @inner ℝ (PhysSpace d) _ p (gradient (fun x => θ (x, z.2)) z.1)
        + @inner ℝ (PhysSpace d) _ q (gradient (fun v => θ (z.1, v)) z.2) := by
  have hin_X : HasFDerivAt (fun x : PhysSpace d => ((x, z.2) : PhaseSpace d))
      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  have hin_V : HasFDerivAt (fun v : PhysSpace d => ((z.1, v) : PhaseSpace d))
      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have hX_fd : HasFDerivAt (fun x => θ (x, z.2))
      ((fderiv ℝ θ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) z.1 := by
    have h := (hθ.hasFDerivAt).comp z.1 hin_X
    simpa only [Function.comp_def] using h
  have hV_fd : HasFDerivAt (fun v => θ (z.1, v))
      ((fderiv ℝ θ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) z.2 := by
    have h := (hθ.hasFDerivAt).comp z.2 hin_V
    simpa only [Function.comp_def] using h
  have hdecomp : (fderiv ℝ θ z) ((p, q) : PhaseSpace d)
      = (fderiv ℝ θ z) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) p)
        + (fderiv ℝ θ z) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) q) := by
    rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add]
    congr 1
    ext <;> simp
  have hX_inner : (fderiv ℝ θ z) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) p)
      = @inner ℝ (PhysSpace d) _ p (gradient (fun x => θ (x, z.2)) z.1) := by
    have hstep : (fderiv ℝ θ z) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) p)
        = fderiv ℝ (fun x => θ (x, z.2)) z.1 p := by rw [hX_fd.fderiv]; rfl
    rw [hstep, ← inner_gradient_left, real_inner_comm]
  have hV_inner : (fderiv ℝ θ z) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) q)
      = @inner ℝ (PhysSpace d) _ q (gradient (fun v => θ (z.1, v)) z.2) := by
    have hstep : (fderiv ℝ θ z) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) q)
        = fderiv ℝ (fun v => θ (z.1, v)) z.2 q := by rw [hV_fd.fderiv]; rfl
    rw [hstep, ← inner_gradient_left, real_inner_comm]
  rw [hdecomp, hX_inner, hV_inner]

/-- FTC bound on the linearization remainder of a real function: if `F` has
derivative `D r` along the segment and `D` stays within `ε` of `D s` there,
then `|F σ − F s − (σ−s)·D s| ≤ ε·|σ−s|`. -/
lemma abs_linearization_remainder_le (F D : ℝ → ℝ) (s σ ε : ℝ)
    (hderiv : ∀ r ∈ Set.uIcc s σ, HasDerivAt F (D r) r)
    (hD_cont : ContinuousOn D (Set.uIcc s σ))
    (hD_close : ∀ r ∈ Set.uIoc s σ, |D r - D s| ≤ ε) :
    |F σ - F s - (σ - s) * D s| ≤ ε * |σ - s| := by
  have hD_ii : IntervalIntegrable D MeasureTheory.volume s σ := hD_cont.intervalIntegrable
  have hFTC1 : ∫ r in s..σ, D r = F σ - F s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hderiv r hr) hD_ii
  have hFTC2 : ∫ _r in s..σ, D s = (σ - s) * D s := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hdiff : F σ - F s - (σ - s) * D s = ∫ r in s..σ, (D r - D s) := by
    rw [intervalIntegral.integral_sub hD_ii intervalIntegrable_const, hFTC1, hFTC2]
  rw [hdiff]
  have hbnd : ∀ r ∈ Set.uIoc s σ, ‖D r - D s‖ ≤ ε := fun r hr => by
    rw [Real.norm_eq_abs]; exact hD_close r hr
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rwa [Real.norm_eq_abs] at hle

omit [NeZero d] in
open Filter Topology Asymptotics in
/-- The transported-integral difference `σ ↦ ∫ ψ_σ d(f σ) − ∫ ψ_s d(f σ)` has
derivative `−Vb = ∫ D d(f s)` at `s`, from a uniform linearization of `r ↦ ψ_r`
(term `T1`) and narrow continuity of `σ ↦ ∫ D d(f σ)` (term `T2`). -/
lemma hasDerivAt_integral_sub_of_uniform_linearization
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (ψ : ℝ → PhaseSpace d → ℝ) (D : PhaseSpace d → ℝ) (s a b : ℝ)
    (hs_ab : s ∈ Set.Ioo a b)
    (hab_sub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (hψr_int : ∀ r ∈ Set.Icc a b, ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable (ψ r) (f σ))
    (hD_int : ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable D (f σ))
    (hunif : ∀ ε > 0, ∀ᶠ σ in 𝓝 s, ∀ z, |ψ σ z - ψ s z - (σ - s) * D z| ≤ ε * |σ - s|)
    (hnarrow : ContinuousWithinAt (fun σ => ∫ z, D z ∂(f σ)) (Set.Icc 0 T) s)
    (hsIoo : s ∈ Set.Ioo (0 : ℝ) T)
    (Vb : ℝ) (hVb : Vb = -∫ z, D z ∂(f s)) :
    HasDerivAt (fun σ => (∫ z, ψ σ z ∂(f σ)) - ∫ z, ψ s z ∂(f σ)) (-Vb) s := by
  rw [hasDerivAt_iff_isLittleO]
  have hT1 : (fun σ => ∫ z, (ψ σ z - ψ s z - (σ - s) * D z) ∂(f σ))
      =o[𝓝 s] (fun σ => σ - s) := by
    rw [isLittleO_iff]
    intro ε hε
    filter_upwards [hunif ε hε, isOpen_Ioo.mem_nhds hs_ab] with σ hunif_σ hσab
    have hσIcc : σ ∈ Set.Icc (0 : ℝ) T :=
      ⟨(hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).1.le,
        (hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).2.le⟩
    have hσab' : σ ∈ Set.Icc a b := ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩
    have := (hf_mom σ hσIcc).1
    have hint : Integrable (fun z => ψ σ z - ψ s z - (σ - s) * D z) (f σ) :=
      ((hψr_int σ hσab' σ hσIcc).sub (hψr_int s
        ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩ σ hσIcc)).sub ((hD_int σ hσIcc).const_mul _)
    calc ‖∫ z, (ψ σ z - ψ s z - (σ - s) * D z) ∂(f σ)‖
        ≤ ∫ z, ‖ψ σ z - ψ s z - (σ - s) * D z‖ ∂(f σ) := norm_integral_le_integral_norm _
      _ ≤ ∫ _z, ε * |σ - s| ∂(f σ) :=
          integral_mono hint.norm (integrable_const _)
            (fun z => by simpa only [Real.norm_eq_abs] using hunif_σ z)
      _ = ε * |σ - s| := by simp
      _ = ε * ‖σ - s‖ := by rw [Real.norm_eq_abs]
  have hE : Tendsto (fun σ => (∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)) (𝓝 s) (𝓝 0) := by
    have hcont := hnarrow.continuousAt (Icc_mem_nhds hsIoo.1 hsIoo.2)
    have h2 : Tendsto (fun σ => (∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)) (𝓝 s)
        (𝓝 ((∫ z, D z ∂(f s)) - ∫ z, D z ∂(f s))) := hcont.tendsto.sub tendsto_const_nhds
    rwa [sub_self] at h2
  have hT2 : (fun σ => (σ - s) * ((∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)))
      =o[𝓝 s] (fun σ => σ - s) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hE ε hε] with σ hσ
    have hEσ : ‖(∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)‖ ≤ ε := by
      rw [Real.norm_eq_abs]; rw [Real.dist_eq, sub_zero] at hσ; exact le_of_lt hσ
    calc ‖(σ - s) * ((∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s))‖
        = ‖σ - s‖ * ‖(∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)‖ := norm_mul _ _
      _ ≤ ‖σ - s‖ * ε := by gcongr
      _ = ε * ‖σ - s‖ := by ring
  refine (hT1.add hT2).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [isOpen_Ioo.mem_nhds hs_ab] with σ hσab
  have hσIcc : σ ∈ Set.Icc (0 : ℝ) T :=
    ⟨(hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).1.le,
      (hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).2.le⟩
  have hσab' : σ ∈ Set.Icc a b := ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩
  have := (hf_mom σ hσIcc).1
  have hi1 : Integrable (ψ σ) (f σ) := hψr_int σ hσab' σ hσIcc
  have hi2 : Integrable (ψ s) (f σ) := hψr_int s ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩ σ hσIcc
  have hi3 : Integrable D (f σ) := hD_int σ hσIcc
  have hia : Integrable (fun z => ψ σ z - ψ s z) (f σ) := hi1.sub hi2
  have hib : Integrable (fun z => (σ - s) * D z) (f σ) := hi3.const_mul _
  have hL1 : ∫ z, (ψ σ z - ψ s z - (σ - s) * D z) ∂(f σ)
      = (∫ z, ψ σ z ∂(f σ)) - (∫ z, ψ s z ∂(f σ)) - (σ - s) * ∫ z, D z ∂(f σ) := by
    rw [integral_sub hia hib, integral_sub hi1 hi2, integral_const_mul]
  rw [hL1, hVb]
  simp only [smul_eq_mul]
  ring

open Filter Topology Asymptotics in
omit [NeZero d] in
/-- **#6a (Step 6, the diagonal chain rule) — `s ↦ ∫ ψ_s d(f s)` has zero `σ`-derivative.**

The analytic heart of the dual core: for the backward-transported test
`ψ_σ(w) := φ(Φ_t(Ψ_σ w))`, the diagonal map `I(σ) := ∫ ψ_σ d(f σ)` (both the integrand *and* the
measure move with `σ`) has `HasDerivAt I 0` on `Ioo 0 t`.  The two `σ`-dependencies cancel.

Strategy (the measure `f` is a bare weak solution, so there is no joint Fréchet structure to lean
on — the two partials are combined by hand):
* Split `I = Bint + q` with `Bint σ := ∫ ψ_s d(f σ)` (integrand frozen at `s`) and
  `q σ := ∫ (ψ_σ − ψ_s) d(f σ)`.
* `HasDerivAt Bint Vb s` via the `C¹_c`-extended weak equation `weakEvolution_test_C1c_On` (#4)
  tested against the fixed `C¹_c` function `ψ_s` (this is why #4 had to land first).
* `HasDerivAt q (−Vb) s` via the little-o definition: writing
  `DQ_r z := ∂_r ψ_r(z)`, the remainder splits as `T1 + T2` where
  `T1 = ∫ (ψ_σ − ψ_s − (σ−s)·DQ_s) d(f σ)` is `o(σ−s)` by **uniform differentiability of `r ↦ ψ_r`
  over a fixed compact `K`** (FTC + Heine–Cantor; `K` is the flow image of `[a,b] × Ψ_t(tsupport φ)`
  — this is what `hflowjoint` is for: bounding the *moving* support of `ψ_r`), and
  `T2 = (σ−s)·(∫ DQ_s d(f σ) − ∫ DQ_s d(f s))` is `o(σ−s)` by narrow continuity (`hf_narrow`).
* The cancellation `Vb = −∫ DQ_s d(f s)` comes from the Step-4 transport identity
  (`transportedTest_transport_identity`, giving `DQ_s = −(fderiv ψ_s)·b_s`) composed with the
  gradient↔fderiv partial decomposition (matching #4's RHS). -/
theorem transportedIntegral_hasDerivAt_zero
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    -- B2 enrichment: threaded through to `weakEvolution_test_C1c_On` (#4), whose mollification
    -- proof needs the uniform field bound (`hL` + `hM_ρ`).
    (L : NNReal) (hL : LipschitzWith L gradW)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    -- B2 enrichment: joint flow continuity gives a fixed compact containing tsupport(ψ_r) for all
    -- `r` near `s` (the moving support of the transported test), needed for the uniform
    -- differentiability over a fixed compact in the little-o argument.
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) t) :
    HasDerivAt (fun σ => ∫ z, φ (charX t (Ψ σ z), charV t (Ψ σ z)) ∂(f σ)) 0 s := by
  classical
  have hsIoo : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  -- the uncurried two-time test g and its slice ψ
  set g : ℝ × PhaseSpace d → ℝ :=
    fun p => φ (charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) with hg_def
  set ψ : ℝ → PhaseSpace d → ℝ :=
    fun r w => φ (charX t (Ψ r w), charV t (Ψ r w)) with hψ_def
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hg_cd : ContDiffOn ℝ 1 g (Set.Ioo 0 T ×ˢ Set.univ) :=
    hφ1.comp_contDiffOn (twoTimeFlow_contDiffOn_joint charX charV T t Ψ hΨ_C1 hΦt_C1)
  ---------------------------------------------------------------------------
  -- closed neighbourhood [a,b] ⊂ Ioo 0 T of s
  obtain ⟨a, b, hab_lt, hs_ab, hab_sub⟩ :
      ∃ a b, a < b ∧ s ∈ Set.Ioo a b ∧ Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    refine ⟨s/2, (s+T)/2, by linarith [hsIoo.1, hsIoo.2],
      ⟨by linarith [hsIoo.1], by linarith [hsIoo.2]⟩, fun r hr => ⟨?_, ?_⟩⟩
    · linarith [hsIoo.1, hr.1]
    · linarith [hsIoo.2, hr.2]
  ---------------------------------------------------------------------------
  -- Ψ_t continuous, support set C, fixed compact K
  have hΨt_cont : Continuous (fun w : PhaseSpace d => Ψ t w) := by
    have hc : Continuous (fun w : PhaseSpace d => ((t, w) : ℝ × PhaseSpace d)) :=
      continuous_const.prodMk continuous_id
    exact hΨ_C1.continuousOn.comp_continuous hc (fun w => ⟨ht, Set.mem_univ _⟩)
  set C : Set (PhaseSpace d) := (fun w => Ψ t w) '' (tsupport φ) with hC_def
  have hC_compact : IsCompact C := hφc.image hΨt_cont
  set K : Set (PhaseSpace d) :=
    (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2)) '' (Set.Icc a b ×ˢ C) with hK_def
  have hsub_abC : Set.Icc a b ×ˢ C ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) :=
    fun p hp => ⟨⟨(hab_sub hp.1).1.le, (hab_sub hp.1).2.le⟩, Set.mem_univ _⟩
  have hK_compact : IsCompact K :=
    (isCompact_Icc.prod hC_compact).image_of_continuousOn (hflowjoint.mono hsub_abC)
  -- support confinement: ψ r z ≠ 0 ⟹ z ∈ K  (for r ∈ [a,b])
  have hsupp : ∀ r ∈ Set.Icc a b, ∀ z, ψ r z ≠ 0 → z ∈ K := by
    intro r hr z hz
    have hrIoo : r ∈ Set.Ioo 0 T := hab_sub hr
    have hmem : (charX t (Ψ r z), charV t (Ψ r z)) ∈ tsupport φ :=
      subset_tsupport _ (by simpa [Function.mem_support] using hz)
    have hΨrz_C : Ψ r z ∈ C := ⟨(charX t (Ψ r z), charV t (Ψ r z)), hmem, hΨ_left t ht (Ψ r z)⟩
    exact ⟨(r, Ψ r z), ⟨hr, hΨrz_C⟩, hΨ_right r hrIoo z⟩
  ---------------------------------------------------------------------------
  -- the r-directional derivative DQ of ψ, and its properties
  set DQ : ℝ → PhaseSpace d → ℝ :=
    fun r z => fderiv ℝ g (r, z) ((1:ℝ), (0:PhaseSpace d)) with hDQ_def
  have hg_hasfderiv : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      HasFDerivAt g (fderiv ℝ g p) p := fun p hp =>
    (hg_cd.differentiableOn_one.differentiableAt (hopen.mem_nhds hp)).hasFDerivAt
  have hψ_deriv : ∀ r ∈ Set.Ioo (0 : ℝ) T, ∀ z, HasDerivAt (fun r' => ψ r' z) (DQ r z) r := by
    intro r hr z
    have hcurve : HasDerivAt (fun r' => ((r', z) : ℝ × PhaseSpace d)) ((1:ℝ), (0:PhaseSpace d)) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r z)
    have := (hg_hasfderiv (r, z) ⟨hr, Set.mem_univ _⟩).comp_hasDerivAt r hcurve
    simpa only [Function.comp_def] using this
  -- DQ continuous on the open window, hence uniformly continuous on Icc a b ×ˢ K
  have hDQ_contOn : ContinuousOn (fun p : ℝ × PhaseSpace d => DQ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ) := by
    have hfd := hg_cd.continuousOn_fderiv_of_isOpen hopen le_rfl
    have heval : Continuous
        (fun M : (ℝ × PhaseSpace d) →L[ℝ] ℝ => M ((1:ℝ), (0:PhaseSpace d))) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ), (0:PhaseSpace d))).continuous
    exact heval.comp_continuousOn hfd
  have hDQ_uc : UniformContinuousOn (fun p : ℝ × PhaseSpace d => DQ p.1 p.2)
      (Set.Icc a b ×ˢ K) :=
    (isCompact_Icc.prod hK_compact).uniformContinuousOn_of_continuous
      (hDQ_contOn.mono (fun p hp => ⟨hab_sub hp.1, Set.mem_univ _⟩))
  rw [Metric.uniformContinuousOn_iff] at hDQ_uc
  -- DQ s vanishes off K
  have hDQ_zero : ∀ z ∉ K, DQ s z = 0 := by
    intro z hzK
    have h0 : HasDerivAt (fun r' => ψ r' z) 0 s := by
      have hconst : (fun r' => ψ r' z) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hs_ab] with r' hr'
        by_contra h
        exact hzK (hsupp r' ⟨le_of_lt hr'.1, le_of_lt hr'.2⟩ z h)
      exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hconst
    exact (hψ_deriv s hsIoo z).unique h0
  ---------------------------------------------------------------------------
  -- continuity / integrability bookkeeping
  have hψr_cont : ∀ r ∈ Set.Ioo (0 : ℝ) T, Continuous (ψ r) := fun r hr =>
    hg_cd.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun w => ⟨hr, Set.mem_univ _⟩)
  have hψr_cs : ∀ r ∈ Set.Icc a b, HasCompactSupport (ψ r) := by
    intro r hr
    apply hK_compact.of_isClosed_subset (isClosed_tsupport _)
    exact closure_minimal (fun z hz => hsupp r hr z (Function.mem_support.mp hz))
      hK_compact.isClosed
  have hψr_int : ∀ r ∈ Set.Icc a b, ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable (ψ r) (f σ) := by
    intro r hr σ hσ
    have := (hf_mom σ hσ).1
    exact (hψr_cont r (hab_sub hr)).integrable_of_hasCompactSupport (hψr_cs r hr)
  have hDQs_cont : Continuous (DQ s) :=
    hDQ_contOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hsIoo, Set.mem_univ _⟩)
  have hDQs_cs : HasCompactSupport (DQ s) := by
    apply hK_compact.of_isClosed_subset (isClosed_tsupport _)
    refine closure_minimal (fun z hz => ?_) hK_compact.isClosed
    by_contra hzK
    exact (Function.mem_support.mp hz) (hDQ_zero z hzK)
  have hDQs_int : ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable (DQ s) (f σ) := by
    intro σ hσ
    have := (hf_mom σ hσ).1
    exact hDQs_cont.integrable_of_hasCompactSupport hDQs_cs
  have hnarrow : ContinuousWithinAt (fun σ => ∫ z, DQ s z ∂(f σ)) (Set.Icc 0 T) s :=
    (hf_narrow (DQ s) hDQs_cont hDQs_cs) s ⟨hsIoo.1.le, hsIoo.2.le⟩
  ---------------------------------------------------------------------------
  -- the two-sided ODE on Ioo (feeds 4b)
  have hflow_ode := charFlow_ode_of_isCharacteristicFlowOn gradW
    (fun τ => spatialMarginal (f τ)) charX charV T hflow
  ---------------------------------------------------------------------------
  -- the #4 derivative of the fixed-integrand integral  Bint σ = ∫ ψ_s d(f σ)
  set gXψs : PhaseSpace d → PhysSpace d := fun z => gradient (fun x => ψ s (x, z.2)) z.1
    with hgX_def
  set gVψs : PhaseSpace d → PhysSpace d := fun z => gradient (fun v => ψ s (z.1, v)) z.2
    with hgV_def
  set field_s : PhysSpace d → PhysSpace d :=
    fun x => convolveFunctionMeasure gradW (spatialMarginal (f s)) x with hfield_def
  have hψs_C1 : ContDiff ℝ 1 (ψ s) := by
    rw [contDiff_iff_contDiffAt]
    intro w
    exact (hg_cd.contDiffAt (hopen.mem_nhds ⟨hsIoo, Set.mem_univ _⟩)).comp w
      (contDiffAt_const.prodMk contDiffAt_id)
  have hψs_cs : HasCompactSupport (ψ s) := hψr_cs s ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩
  set Vb : ℝ := ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gXψs z)
      - @inner ℝ (PhysSpace d) _ (field_s z.1) (gVψs z)) ∂(f s) with hVb_def
  have hBint : HasDerivAt (fun σ => ∫ z, ψ s z ∂(f σ)) Vb s :=
    weakEvolution_test_C1c_On gradW f T hf_weak hf_mom L hL M_ρ hM_ρ_nn hM_ρ
      (ψ s) hψs_C1 hψs_cs gXψs gVψs (fun z => rfl) (fun z => rfl) s hsIoo
  ---------------------------------------------------------------------------
  -- the cancellation identity  Vb = - ∫ DQ_s d(f s)
  have hpt : ∀ z, DQ s z = -(@inner ℝ (PhysSpace d) _ z.2 (gXψs z)
      - @inner ℝ (PhysSpace d) _ (field_s z.1) (gVψs z)) := by
    intro z
    have h4b := transportedTest_transport_identity gradW (fun τ => spatialMarginal (f τ))
      charX charV T t φ hφ Ψ hΨ_left hΨ_right hΨ_C1 hΦt_C1 hflow_ode s hsIoo z
    have huniq : DQ s z
        = -(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) z)
            (vlasovVectorField gradW (fun τ => spatialMarginal (f τ)) s z) :=
      (hψ_deriv s hsIoo z).unique h4b
    rw [huniq]
    congr 1
    -- bridge:  (fderiv (ψ s) z)(b_s z) = ⟪z.2, gXψs z⟫ - ⟪field_s z.1, gVψs z⟫
    have hb : vlasovVectorField gradW (fun τ => spatialMarginal (f τ)) s z
        = ((z.2 : PhysSpace d), (-field_s z.1 : PhysSpace d)) := rfl
    rw [hb]
    have hdiffφ : DifferentiableAt ℝ (ψ s) z := hψs_C1.differentiable (by norm_num) z
    rw [fderiv_apply_eq_inner_gradientSlices (ψ s) z hdiffφ z.2 (-field_s z.1)]
    simp only [hgX_def, hgV_def]
    rw [inner_neg_left]
    ring
  have hcancel : Vb = - ∫ z, DQ s z ∂(f s) := by
    have heq : ∫ z, DQ s z ∂(f s) = ∫ z, -(@inner ℝ (PhysSpace d) _ z.2 (gXψs z)
        - @inner ℝ (PhysSpace d) _ (field_s z.1) (gVψs z)) ∂(f s) :=
      integral_congr_ae (Eventually.of_forall hpt)
    rw [heq, integral_neg, ← hVb_def, neg_neg]
  ---------------------------------------------------------------------------
  -- uniform differentiability of ψ in r over K, near s
  have hunif : ∀ ε > 0, ∀ᶠ σ in 𝓝 s,
      ∀ z, |ψ σ z - ψ s z - (σ - s) * DQ s z| ≤ ε * |σ - s| := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hDQ_uc ε hε
    filter_upwards [Metric.ball_mem_nhds s hδpos, isOpen_Ioo.mem_nhds hs_ab] with σ hσδ hσab
    rw [Metric.mem_ball] at hσδ
    intro z
    have hσab' : σ ∈ Set.Icc a b := ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩
    have hs_ab' : s ∈ Set.Icc a b := ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩
    have hseg : Set.uIcc s σ ⊆ Set.Ioo (0 : ℝ) T := fun r hr =>
      hab_sub (Set.uIcc_subset_Icc hs_ab' hσab' hr)
    by_cases hzK : z ∈ K
    · -- FTC route via `abs_linearization_remainder_le`; the ε-closeness of `DQ · z`
      -- along the segment comes from uniform continuity on `[a,b] × K`.
      have hD_close : ∀ r ∈ Set.uIoc s σ, |DQ r z - DQ s z| ≤ ε := by
        intro r hr
        have hr_uIcc : r ∈ Set.uIcc s σ := Set.uIoc_subset_uIcc hr
        have hrab : r ∈ Set.Icc a b := Set.uIcc_subset_Icc hs_ab' hσab' hr_uIcc
        have habs : |r - s| ≤ |σ - s| := by
          rcases le_total s σ with hsσ | hσs
          · rw [Set.uIcc_of_le hsσ] at hr_uIcc
            rw [abs_of_nonneg (by linarith [hr_uIcc.1] : (0 : ℝ) ≤ r - s),
                abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - s)]
            linarith [hr_uIcc.2]
          · rw [Set.uIcc_of_ge hσs] at hr_uIcc
            rw [abs_of_nonpos (by linarith [hr_uIcc.2] : r - s ≤ 0),
                abs_of_nonpos (by linarith : σ - s ≤ 0)]
            linarith [hr_uIcc.1]
        have hdist : dist ((r, z) : ℝ × PhaseSpace d) (s, z) < δ := by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
          calc |r - s| ≤ |σ - s| := habs
            _ = dist σ s := (Real.dist_eq σ s).symm
            _ < δ := hσδ
        have hlt := hδ (r, z) ⟨hrab, hzK⟩ (s, z) ⟨hs_ab', hzK⟩ hdist
        rw [Real.dist_eq] at hlt
        exact le_of_lt hlt
      have hmapsTo : Set.MapsTo (fun r => ((r, z) : ℝ × PhaseSpace d)) (Set.uIcc s σ)
          (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := fun r hr => ⟨hseg hr, Set.mem_univ _⟩
      exact abs_linearization_remainder_le (fun r => ψ r z) (fun r => DQ r z) s σ ε
        (fun r hr => hψ_deriv r (hseg hr) z)
        (hDQ_contOn.comp (continuous_id.prodMk continuous_const).continuousOn hmapsTo)
        hD_close
    · have hψσ : ψ σ z = 0 := by
        by_contra h
        exact hzK (hsupp σ ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩ z h)
      have hψs0 : ψ s z = 0 := by
        by_contra h
        exact hzK (hsupp s ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩ z h)
      rw [hψσ, hψs0, hDQ_zero z hzK]
      simp only [sub_zero, mul_zero, abs_zero]
      positivity
  ---------------------------------------------------------------------------
  -- the q-derivative  q σ = ∫ ψ_σ d(f σ) - ∫ ψ_s d(f σ)  has derivative  -Vb
  have hq : HasDerivAt (fun σ => (∫ z, ψ σ z ∂(f σ)) - ∫ z, ψ s z ∂(f σ)) (-Vb) s :=
    hasDerivAt_integral_sub_of_uniform_linearization f T hf_mom ψ (DQ s) s a b
      hs_ab hab_sub hψr_int hDQs_int hunif hnarrow hsIoo Vb hcancel
  ---------------------------------------------------------------------------
  -- assemble the diagonal
  have hfinal : HasDerivAt (fun σ => ∫ z, ψ σ z ∂(f σ)) (-Vb + Vb) s := by
    refine (hq.add hBint).congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
    simp only [Pi.add_apply]; ring
  rw [neg_add_cancel] at hfinal
  exact hfinal

-- #6b: the transported integral (with the s=0 endpoint patched to the RHS value) is
-- continuous on the closed interval [0,t].
open Filter Topology in
omit [NeZero d] in
theorem transportedIntegral_continuousOn
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    (L : NNReal)
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (hanti : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        * Real.exp (((max 1 L : NNReal) : ℝ) * s)) :
    ContinuousOn (fun s => if s = 0 then ∫ z, φ (charX t z, charV t z) ∂(f 0)
        else ∫ z, φ (charX t (Ψ s z), charV t (Ψ s z)) ∂(f s)) (Set.Icc (0 : ℝ) t) := by
  classical
  have hT0 : (0 : ℝ) < T := lt_trans ht.1 ht.2
  -- the terminal map and the transported integrand g = φ ∘ Φ_t
  have hΦt_cont : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := hΦt_C1.continuous
  set g : PhaseSpace d → ℝ := fun z => φ (charX t z, charV t z) with hg_def
  have hg_cont : Continuous g := hφ.continuous.comp hΦt_cont
  -- Ψ_t continuous (t-slice of the joint C¹ inverse) and the support set S := Ψ_t '' (tsupport φ)
  have htIoo : t ∈ Set.Ioo (0 : ℝ) T := ht
  have hΨt_cont : Continuous (fun z => Ψ t z) := by
    have hcont_on : ContinuousOn (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
        (Set.Ioo 0 T ×ˢ Set.univ) := hΨ_C1.continuousOn
    have : Continuous (fun z : PhaseSpace d => (t, z)) := continuous_const.prodMk continuous_id
    refine (hcont_on.comp_continuous this (fun z => ?_))
    exact ⟨ht, Set.mem_univ _⟩
  set S : Set (PhaseSpace d) := (fun z => Ψ t z) '' (tsupport φ) with hS_def
  have hS_compact : IsCompact S := hφc.image hΨt_cont
  -- g is supported in S, hence has compact support
  have hg_supp_S : ∀ z ∉ S, g z = 0 := by
    intro z hz
    by_contra hgz
    -- g z ≠ 0 ⟹ (charX t z, charV t z) ∈ support φ ⊆ tsupport φ ⟹ z = Ψ_t(Φ_t z) ∈ S
    have hφne : φ (charX t z, charV t z) ≠ 0 := hgz
    have hmem : (charX t z, charV t z) ∈ tsupport φ :=
      subset_tsupport _ (by simpa [Function.mem_support] using hφne)
    have hzeq : Ψ t (charX t z, charV t z) = z := hΨ_left t ht z
    exact hz ⟨(charX t z, charV t z), hmem, hzeq⟩
  have hg_csupp : HasCompactSupport g := by
    have hsub : tsupport g ⊆ S :=
      closure_minimal (fun z hz => by
        by_contra hzS; exact hz (hg_supp_S z hzS)) hS_compact.isClosed
    exact hS_compact.of_isClosed_subset (isClosed_tsupport _) hsub
  have hg_unif : UniformContinuous g := hg_csupp.uniformContinuous_of_continuous hg_cont
  -- the initial condition Φ_0 = id (from hflow.1)
  have hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext (hflow.1 z (Set.mem_univ z)).1 (hflow.1 z (Set.mem_univ z)).2
  -- clamp u : ℝ → ℝ into [0,t]
  set u : ℝ → ℝ := fun s => max 0 (min s t) with hu_def
  have hu_cont : Continuous u := continuous_const.max (continuous_id.min continuous_const)
  have hu0 : u 0 = 0 := by simp [hu_def, min_eq_left ht.1.le]
  have hu_lb : ∀ s, 0 ≤ u s := fun s => le_max_left _ _
  have hu_ub : ∀ s, u s ≤ T := fun s =>
    max_le hT0.le (le_trans (min_le_right _ _) ht.2.le)
  have hu_pos_of_pos : ∀ s, 0 < s → u s = min s t := by
    intro s hs
    have : 0 ≤ min s t := le_min hs.le ht.1.le
    simp [hu_def, max_eq_right this]
  -- the globally-continuous, uniformly-compactly-supported integrand G'
  set G' : ℝ → PhaseSpace d → ℝ := fun s z => if s ≤ 0 then g z else g (Ψ (min s t) z) with hG'_def
  -- (A) joint flow tendsto used at the s=0 seam: (p ↦ Φ_{u p.1} p.2) → z₀
  have hΦu_tendsto : ∀ z₀ : PhaseSpace d,
      Tendsto (fun p : ℝ × PhaseSpace d => (charX (u p.1) p.2, charV (u p.1) p.2))
        (𝓝 (0, z₀)) (𝓝 z₀) := by
    intro z₀
    have hcwa : ContinuousWithinAt (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2))
        (Set.Icc 0 T ×ˢ Set.univ) (0, z₀) :=
      hflowjoint (0, z₀) ⟨⟨le_refl 0, hT0.le⟩, Set.mem_univ _⟩
    have hval : (charX 0 z₀, charV 0 z₀) = z₀ := hinit z₀
    have hinner : Tendsto (fun p : ℝ × PhaseSpace d => (u p.1, p.2))
        (𝓝 (0, z₀)) (𝓝[Set.Icc 0 T ×ˢ Set.univ] (0, z₀)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall (fun p => ⟨⟨hu_lb p.1, hu_ub p.1⟩, Set.mem_univ _⟩)⟩
      have hc : Continuous (fun p : ℝ × PhaseSpace d => (u p.1, p.2)) :=
        (hu_cont.comp continuous_fst).prodMk continuous_snd
      exact hc.tendsto' (0, z₀) (0, z₀) (by simp [hu0])
    have hcomp := (hval ▸ hcwa.tendsto).comp hinner
    simpa [Function.comp_def] using hcomp
  -- (B) G' is globally continuous
  have hG'_cont : Continuous (fun p : ℝ × PhaseSpace d => G' p.1 p.2) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨s₀, z₀⟩
    rcases lt_trichotomy s₀ 0 with hs₀ | hs₀ | hs₀
    · -- s₀ < 0: locally G' = g ∘ snd
      have heq : (fun p : ℝ × PhaseSpace d => G' p.1 p.2) =ᶠ[𝓝 (s₀, z₀)]
          (fun p => g p.2) := by
        have hmem : {p : ℝ × PhaseSpace d | p.1 < 0} ∈ 𝓝 (s₀, z₀) :=
          (isOpen_lt continuous_fst continuous_const).mem_nhds hs₀
        filter_upwards [hmem] with p hp
        simp only [hG'_def, ite_eq_left hp.le]
      exact (hg_cont.comp continuous_snd).continuousAt.congr heq.symm
    · -- s₀ = 0: the confinement seam
      subst hs₀
      rw [ContinuousAt]
      have hval0 : G' (0 : ℝ) z₀ = g z₀ := by simp [hG'_def]
      change Tendsto (fun p : ℝ × PhaseSpace d => G' p.1 p.2) (𝓝 ((0 : ℝ), z₀)) (𝓝 (G' 0 z₀))
      rw [hval0, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hg_unif ε hε
      -- eventually: dist(p.2, z₀) < δ/2  and  exp(K u p.1)·dist(p.2, Φ_{u p.1} p.2) < δ/2
      have hKpos : (0 : ℝ) < δ/2 := by positivity
      have hfact1 : ∀ᶠ p : ℝ × PhaseSpace d in 𝓝 (0, z₀), dist p.2 z₀ < δ/2 := by
        have : Tendsto (fun p : ℝ × PhaseSpace d => p.2) (𝓝 (0, z₀)) (𝓝 z₀) :=
          continuous_snd.continuousAt
        exact (Metric.tendsto_nhds.mp this) (δ/2) hKpos
      have hfact2 : ∀ᶠ p : ℝ × PhaseSpace d in 𝓝 (0, z₀),
          Real.exp (((max 1 L : NNReal) : ℝ) * u p.1) *
            dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)
            < δ/2 := by
        have hd : Tendsto (fun p : ℝ × PhaseSpace d =>
            Real.exp (((max 1 L : NNReal) : ℝ) * u p.1)
              * dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)) (𝓝 (0, z₀)) (𝓝 0) := by
          have hexp : Tendsto (fun p : ℝ × PhaseSpace d =>
              Real.exp (((max 1 L : NNReal) : ℝ) * u p.1)) (𝓝 (0, z₀))
              (𝓝 (Real.exp (((max 1 L : NNReal) : ℝ) * u 0))) :=
            ((Real.continuous_exp.comp (continuous_const.mul (hu_cont.comp continuous_fst))))
              |>.continuousAt.tendsto
          have hdist : Tendsto (fun p : ℝ × PhaseSpace d =>
              dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)) (𝓝 (0, z₀)) (𝓝 0) := by
            have h2 : Tendsto (fun p : ℝ × PhaseSpace d => p.2) (𝓝 (0, z₀)) (𝓝 z₀) :=
              continuous_snd.continuousAt
            have := (h2.dist (hΦu_tendsto z₀))
            simpa using this
          have := hexp.mul hdist
          simpa [hu0] using this
        filter_upwards [(Metric.tendsto_nhds.mp hd) (δ/2) hKpos] with p hp
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hp
      filter_upwards [hfact1, hfact2] with p hp1 hp2
      by_cases hps : p.1 ≤ 0
      · -- branch g p.2
        simp only [hG'_def, ite_eq_left hps]
        exact hδg (lt_of_lt_of_le hp1 (by linarith))
      · -- branch g (Ψ (min p.1 t) p.2)
        rw [not_le] at hps
        have humin : u p.1 = min p.1 t := hu_pos_of_pos p.1 hps
        have hminIoo : min p.1 t ∈ Set.Ioo (0 : ℝ) T :=
          ⟨lt_min hps ht.1, lt_of_le_of_lt (min_le_right _ _) ht.2⟩
        simp only [hG'_def, ite_eq_right (not_le.mpr hps)]
        apply hδg
        -- dist (Ψ (min p.1 t) p.2) z₀ < δ
        have hright : (charX (min p.1 t) (Ψ (min p.1 t) p.2),
            charV (min p.1 t) (Ψ (min p.1 t) p.2)) = p.2 := hΨ_right (min p.1 t) hminIoo p.2
        have hbound : dist (Ψ (min p.1 t) p.2) p.2
            ≤ dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)
              * Real.exp (((max 1 L : NNReal) : ℝ) * (min p.1 t)) := by
          have hkey := hanti (min p.1 t) hminIoo (Ψ (min p.1 t) p.2) p.2
          rw [hright] at hkey
          rw [humin]
          exact hkey
        calc dist (Ψ (min p.1 t) p.2) z₀
            ≤ dist (Ψ (min p.1 t) p.2) p.2 + dist p.2 z₀ := dist_triangle _ _ _
          _ < δ/2 + δ/2 := by
              refine add_lt_add_of_le_of_lt ?_ hp1
              refine le_of_lt (lt_of_le_of_lt hbound ?_)
              rw [humin] at hp2 ⊢
              rw [mul_comm] at hp2
              exact hp2
          _ = δ := by ring
    · -- s₀ > 0: locally G' = g (Ψ (min · t) ·)
      have heq : (fun p : ℝ × PhaseSpace d => G' p.1 p.2) =ᶠ[𝓝 (s₀, z₀)]
          (fun p => g (Ψ (min p.1 t) p.2)) := by
        have hmem : {p : ℝ × PhaseSpace d | 0 < p.1} ∈ 𝓝 (s₀, z₀) :=
          (isOpen_lt continuous_const continuous_fst).mem_nhds hs₀
        filter_upwards [hmem] with p hp
        simp only [hG'_def, ite_eq_right (not_le.mpr hp)]
      refine ContinuousAt.congr ?_ heq.symm
      -- continuity of g (Ψ (min p.1 t) p.2) at (s₀, z₀), s₀ > 0
      have hmin_s₀ : min s₀ t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_min hs₀ ht.1, lt_of_le_of_lt (min_le_right _ _) ht.2⟩
      have hΨcont_at : ContinuousAt (fun p : ℝ × PhaseSpace d => Ψ (min p.1 t) p.2) (s₀, z₀) := by
        have hcont_on : ContinuousOn (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
            (Set.Ioo 0 T ×ˢ Set.univ) := hΨ_C1.continuousOn
        have hmapcont : Continuous (fun p : ℝ × PhaseSpace d => (min p.1 t, p.2)) :=
          ((continuous_fst.min continuous_const)).prodMk continuous_snd
        have hopen : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) ∈
            𝓝 ((min s₀ t, z₀) : ℝ × PhaseSpace d) :=
          (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hmin_s₀, Set.mem_univ _⟩
        have hca : ContinuousAt (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2) (min s₀ t, z₀) :=
          hcont_on.continuousAt hopen
        exact hca.comp_of_eq hmapcont.continuousAt rfl
      exact hg_cont.continuousAt.comp hΨcont_at
  -- (C) the fixed compact K_total containing all supports of G'
  set Ktot : Set (PhaseSpace d) :=
    (fun q : ℝ × PhaseSpace d ↦ (charX q.1 q.2, charV q.1 q.2)) '' (Set.Icc 0 t ×ˢ S) with hKtot_def
  have hKtot_compact : IsCompact Ktot :=
    (isCompact_Icc.prod hS_compact).image_of_continuousOn
      (hflowjoint.mono (Set.prod_mono (Set.Icc_subset_Icc_right ht.2.le) (Set.subset_univ S)))
  have hS_sub_Ktot : S ⊆ Ktot := by
    intro p hp
    refine ⟨(0, p), ⟨⟨le_refl 0, ht.1.le⟩, hp⟩, ?_⟩
    simp [hinit p]
  have hG'_supp : ∀ s, ∀ z ∉ Ktot, G' s z = 0 := by
    intro s z hz
    simp only [hG'_def]
    split_ifs with hs
    · -- s ≤ 0: G' = g z; z ∉ Ktot ⟹ z ∉ S ⟹ g z = 0
      exact hg_supp_S z (fun hzS => hz (hS_sub_Ktot hzS))
    · -- s > 0: G' = g (Ψ (min s t) z); nonzero ⟹ Ψ(min s t) z ∈ S ⟹ z ∈ Ktot
      by_contra hgz
      rw [not_le] at hs
      have hminIoo : min s t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_min hs ht.1, lt_of_le_of_lt (min_le_right _ _) ht.2⟩
      have hΨz_S : Ψ (min s t) z ∈ S := by
        by_contra hΨz
        exact hgz (hg_supp_S _ hΨz)
      have hright : (charX (min s t) (Ψ (min s t) z), charV (min s t) (Ψ (min s t) z)) = z :=
        hΨ_right (min s t) hminIoo z
      exact hz ⟨(min s t, Ψ (min s t) z),
        ⟨⟨(lt_min hs ht.1).le, min_le_right _ _⟩, hΨz_S⟩, hright⟩
  -- (D) apply NC and transfer to I on Icc 0 t
  have hNC := vlasovSolutionOn_integral_continuousOn f T hf_mom hf_narrow G'
    hG'_cont Ktot hKtot_compact hG'_supp
  refine (hNC.mono (Set.Icc_subset_Icc_right ht.2.le)).congr ?_
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · -- s = 0
    subst h0
    simp only [ite_true]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hG'_def, ite_eq_left (le_refl (0 : ℝ)), hg_def]
  · -- s > 0
    have hsne : s ≠ 0 := ne_of_gt h0
    have hsle : s ≤ t := hs.2
    simp only [ite_eq_right hsne, hG'_def, ite_eq_right (not_le.mpr h0), min_eq_left hsle, hg_def]

-- dualCore_main: the dual core for 0 < t ≤ T (subsumes the t = T terminal via the same
-- if-patched constancy argument).  Obtains Ψ from item (iv), assembles #6a + #6b +
-- transportedIntegral_const_On + the endpoint identities.
omit [NeZero d] in
theorem dualCore_main
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (hanti : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        * Real.exp (((max 1 L : NNReal) : ℝ) * s)) :
    ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by
  -- the if-patched transported integral
  set I : ℝ → ℝ := fun s => if s = 0 then ∫ z, φ (charX t z, charV t z) ∂(f 0)
      else ∫ z, φ (charX t (Ψ s z), charV t (Ψ s z)) ∂(f s) with hI_def
  -- endpoint values
  have hI0 : I 0 = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by simp [hI_def]
  have htne : t ≠ 0 := ne_of_gt ht.1
  have hIt : I t = ∫ z, φ z ∂(f t) := by
    simp only [hI_def, ite_eq_right htne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change φ (charX t (Ψ t z), charV t (Ψ t z)) = φ z
    have hri : (charX t (Ψ t z), charV t (Ψ t z)) = z := hΨ_right t ht z
    rw [hri]
  -- zero derivative on Ioo 0 t (the un-patched form agrees with I near interior s)
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t, HasDerivAt I 0 s := by
    intro s hs
    have hbase := transportedIntegral_hasDerivAt_zero gradW f T hf_weak hf_mom hf_narrow
      L hL M_ρ hM_ρ_nn hM_ρ charX charV
      hflow t ht φ hφ hφc Ψ hΨ_left hΨ_right hΨ_C1 hΦt_C1 hflowjoint s hs
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs' using by
      simp only [hI_def, ite_eq_right (ne_of_gt hs'.1)]
  -- continuity on Icc 0 t
  have hcont : ContinuousOn I (Set.Icc (0 : ℝ) t) :=
    transportedIntegral_continuousOn gradW f T hf_mom hf_narrow charX charV hflow t ht
      φ hφ hφc Ψ hΨ_left hΨ_right hΨ_C1 hΦt_C1 L hflowjoint hanti
  -- constancy: I 0 = I t
  have hconst : I 0 = I t := transportedIntegral_const_On ht.1 hcont hderiv
  rw [hI0, hIt] at hconst
  exact hconst.symm

-- frozenFlow_inverse_On: the item-(iv) discharge — produces the jointly-C¹ inverse Ψ + the
-- four facts dualCore_main consumes, from the raw dual core hypotheses (L11 clamp for the
-- universal probability instance, h_int from hL + moments, etc.).
omit [NeZero d] in
theorem frozenFlow_inverse_On
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ Ψ : ℝ → PhaseSpace d → PhaseSpace d,
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2) (Set.Ioo 0 T ×ˢ Set.univ) ∧
      ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)) ∧
      ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
        (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
        dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
          * Real.exp (((max 1 L : NNReal) : ℝ) * s)) := by
  classical
  have hgradW_C1 : ContDiff ℝ 1 gradW := assW2_contDiff_gradW W gradW hgradW
  -- window force-integrability from finite moment + Lipschitz (h_int_helper template)
  have h_int_win : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f s)) := by
    intro s hs x_pt
    have : IsProbabilityMeasure (f s) := (hf_mom s hs).1
    have : IsProbabilityMeasure (spatialMarginal (f s)) :=
      (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal (f s)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f s)) := by
      unfold spatialMarginal
      rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
      refine Integrable.mono' (hf_mom s hs).2
        ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      change |‖z.1‖| ≤ ‖z‖
      rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
    have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x_pt - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
        (spatialMarginal (f s)) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
          (spatialMarginal (f s)) := h_y_int.const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  -- L11 clamp into [0,T]
  set clampT : ℝ → ℝ := fun s => max 0 (min s T) with hclampT_def
  have hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T := by
    intro s; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s := by
    intro s hs; simp only [hclampT_def, min_eq_left hs.2, max_eq_right hs.1]
  have hclampT_cont : Continuous clampT := by
    simp only [hclampT_def]; exact continuous_const.max (continuous_id.min continuous_const)
  set ρ' : ℝ → Measure (PhysSpace d) := fun s => spatialMarginal (f (clampT s)) with hρ'_def
  have hρ'_prob : ∀ s, IsProbabilityMeasure (ρ' s) := by
    intro s
    have : IsProbabilityMeasure (f (clampT s)) := (hf_mom (clampT s) (hclampT_mem s)).1
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have h_int' : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' s) :=
    fun s x => h_int_win (clampT s) (hclampT_mem s) x
  have hf_cont' : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ' s) x) :=
    fun x => (hf_cont x).comp hclampT_cont
  have hρD_cont' : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ' p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) := by
    refine hf_cont_deriv.congr (fun p hp => ?_)
    simp only [hρ'_def, hclampT_id p.1 hp.1]
  have hflow' : IsCharacteristicFlowOn gradW ρ' charX charV (Set.Ioo 0 T) Set.univ := by
    refine ⟨hflow.1, hflow.2.1, fun s hs z hz => ?_⟩
    have h := hflow.2.2 s hs z hz
    have hρeq : ρ' s = spatialMarginal (f s) := by
      simp only [hρ'_def, hclampT_id s (Set.Ioo_subset_Icc_self hs)]
    rw [hρeq]; exact h
  -- the per-slice inverse + joint C¹ (Step 3 item iv), ρ-free conclusion
  obtain ⟨Ψ, hLeft, hRight, hC1⟩ := charFlow_inverse_contDiffOn_joint gradW hgradW_C1 L hL ρ'
    charX charV T hT hflow' h_int' hf_cont' hρD_cont' hcontIcc
  -- hΦt_C1: the t-slice ContDiff from joint ContDiffAt
  have hcdaj := charFlow_contDiffAt_joint gradW hgradW_C1 L hL ρ' charX charV T hT
    hflow' h_int' hf_cont' hρD_cont' hcontIcc
  have hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hjoint : ContDiffAt ℝ 1
        (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (t, z) :=
      hcdaj (t, z) ⟨ht, Set.mem_univ _⟩
    have hinner : ContDiffAt ℝ 1 (fun z' : PhaseSpace d => ((t : ℝ), z')) z :=
      (contDiffAt_const).prodMk contDiffAt_id
    exact hjoint.comp z hinner
  -- joint flow continuity + antilipschitz (enrichment for #6b's s=0 endpoint)
  have hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext (hflow'.1 z (Set.mem_univ z)).1 (hflow'.1 z (Set.mem_univ z)).2
  have h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ' s (charX s z, charV s z)) s :=
    fun z s hs => (hflow'.2.1 s hs z (Set.mem_univ z)).prodMk (hflow'.2.2 s hs z (Set.mem_univ z))
  have hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    charFlow_continuousOn_joint gradW L hL ρ' h_int' charX charV T hT.le hinit hcontIcc
      (fun z s hs => (h_deriv2 z s hs).hasDerivWithinAt)
  have hanti : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        * Real.exp (((max 1 L : NNReal) : ℝ) * s) := by
    intro s hs z₁ z₂
    have := charFlow_antilipschitzInZ_via_gronwall_Ioo gradW L hL ρ' h_int' charX charV T
      hinit hcontIcc h_deriv2 s hs z₁ z₂
    simpa using this
  exact ⟨Ψ, hLeft, hRight, hC1, hΦt_C1, hflowjoint, hanti⟩

-- dualCore_terminal: the t = T endpoint, by a t → T⁻ limit of the Ioo dual core `hIoo`.
-- LHS continuity at T via narrow continuity (hf_narrow); RHS via filter-DCT against the fixed
-- measure f 0 (joint flow continuity for measurability + per-z continuity for the pointwise limit).
open Filter Topology in
omit [NeZero d] in
theorem dualCore_terminal
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hIoo : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0)) :
    ∫ z, φ z ∂(f T) = ∫ z, φ (charX T z, charV T z) ∂(f 0) := by
  classical
  have : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  -- the limit filter, nonempty since T is a left limit point of Ioo 0 T
  have hl_neBot : (𝓝[Set.Ioo (0 : ℝ) T] T).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (ne_of_lt hT)]
    exact ⟨hT.le, le_refl T⟩
  -- (1) LHS continuity at T (narrow continuity of f against φ)
  have hClaim1 : Tendsto (fun t => ∫ z, φ z ∂(f t)) (𝓝[Set.Ioo (0 : ℝ) T] T)
      (𝓝 (∫ z, φ z ∂(f T))) := by
    have hcwa : ContinuousWithinAt (fun s => ∫ z, φ z ∂(f s)) (Set.Icc 0 T) T :=
      (hf_narrow φ hφ.continuous hφc) T ⟨hT.le, le_refl T⟩
    exact hcwa.tendsto.mono_left (nhdsWithin_mono T Set.Ioo_subset_Icc_self)
  -- (2) RHS continuity at T against the fixed measure f 0 (filter DCT)
  obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖φ z‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hφ.continuous.norm).bddAbove_range_of_hasCompactSupport hφc.norm
    exact ⟨C, fun z => hC ⟨z, rfl⟩⟩
  have hClaim2 : Tendsto (fun t => ∫ z, φ (charX t z, charV t z) ∂(f 0))
      (𝓝[Set.Ioo (0 : ℝ) T] T) (𝓝 (∫ z, φ (charX T z, charV T z) ∂(f 0))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ ?_ ?_
    · -- AEStronglyMeasurable eventually
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
      have hslice : Continuous (fun z => (charX t z, charV t z)) :=
        hflowjoint.comp_continuous (continuous_const.prodMk continuous_id)
          (fun z => ⟨htIcc, Set.mem_univ _⟩)
      exact (hφ.continuous.comp hslice).aestronglyMeasurable
    · exact Eventually.of_forall (fun t => Eventually.of_forall (fun z => hC _))
    · exact integrable_const C
    · refine Eventually.of_forall (fun z => ?_)
      have hzcwa : ContinuousWithinAt (fun s => (charX s z, charV s z)) (Set.Icc 0 T) T :=
        (hcontIcc z) T ⟨hT.le, le_refl T⟩
      have hcomp : ContinuousWithinAt (fun s => φ (charX s z, charV s z)) (Set.Icc 0 T) T :=
        hφ.continuous.continuousAt.comp_continuousWithinAt hzcwa
      exact hcomp.tendsto.mono_left (nhdsWithin_mono T Set.Ioo_subset_Icc_self)
  -- (3) the two limits agree via hIoo, so the targets are equal
  have hEqOn : (fun t => ∫ z, φ z ∂(f t)) =ᶠ[𝓝[Set.Ioo (0 : ℝ) T] T]
      (fun t => ∫ z, φ (charX t z, charV t z) ∂(f 0)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht using hIoo t ht
  exact tendsto_nhds_unique (hClaim1.congr' hEqOn) hClaim2

omit [NeZero d] in
/-- **C3 #8 (dual-transport core) — `∫ φ d(f t) = ∫ φ∘Φ_t d(f 0)` for every `C_c^∞` test.**

The dual transported-test-function argument showing the weak solution `f` transports along its
frozen-field characteristics.  Fix a terminal `t ∈ [0,T]` and a `C_c^∞` test `φ`.  Let `Φ_{s→t}`
be the two-time flow (forward from time `s` to time `t` along the frozen-field characteristics)
and `ψ_s := φ ∘ Φ_{s→t}` the backward-transported test (so `ψ_t = φ` and `ψ_0 = φ ∘ Φ_t`).  Then:
**Proven, axiom-clean** (this body composes the six leaves below).  The two-time flow
`Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is jointly `C¹` (Steps 1–4, proven: `charFlow_inverse_contDiffOn_joint` +
`transportedTest_transport_identity`).  The constancy of `I(s) := ∫ ψ_s d(f s)` on `[0,t]` is
assembled by `dualCore_main` (sorry-free): the `if`-patched `I` (the left endpoint `s = 0`, where
item-(iv) `Ψ_s` is junk, is set directly to `∫ φ∘Φ_t d(f 0)`), endpoint identities
`I 0 = ∫ φ∘Φ_t d(f 0)` and `I t = ∫ φ d(f t)` (via the right-inverse `Ψ_t`), then
`transportedIntegral_const_On` (#7).  `t = 0` is trivial (`Φ_0 = id`); `t = T` goes through
`dualCore_terminal` (a `t → T⁻` limit).

The constancy rests on six leaves (all proven, axiom-clean):
* **`weakEvolution_test_C1c_On`** (#4 = **Step 5**) — the linear weak equation extended from the
  `C_c^∞` test class to `C¹_c` (so it can be tested against the only-`C¹` `ψ_r`).
* **`vlasovSolutionOn_integral_continuousOn`** (NC) — `s ↦ ∫ G s · d(f s)` is continuous for a
  jointly-continuous, uniformly-compactly-supported family `G` (narrow continuity of the weak
  solution, consumption form; derivable from the weak eq + moments).
* **`transportedIntegral_hasDerivAt_zero`** (#6a) — `HasDerivAt I 0` on `Ioo 0 t`, the diagonal
  chain rule: `∂_σ` via #4 + `∂_r` via differentiation-under-the-integral against `f s` + the
  transport-identity cancellation; assembles via the Step-3 continuous-partials gating theorem.
* **`transportedIntegral_continuousOn`** (#6b) — `ContinuousOn I (Icc 0 t)`, via NC + Step-4 joint
  continuity (the `s → 0⁺` endpoint is the load-bearing case).
* **`frozenFlow_inverse_On`** — the item-(iv) discharge producing `Ψ` + its four facts (L11 clamp
  for the universal probability instance).
* **`dualCore_terminal`** — the `t = T` endpoint.

The pushforward side is `integral_map` by definition, so the dual argument is needed only for `f`
(the plan's `#1` pushforward-solves-linear lemma is not on this path). -/
theorem weak_eq_frozenField_pushforward_dualCore
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : PhaseSpace d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by
  intro t ht φ hφ hφc
  -- the Ioo dual core (this φ): frozenFlow inverse + dualCore_main per interior point
  have hIoo : ∀ τ ∈ Set.Ioo (0 : ℝ) T,
      ∫ z, φ z ∂(f τ) = ∫ z, φ (charX τ z, charV τ z) ∂(f 0) := by
    intro τ hτ
    obtain ⟨Ψ, hl, hr, hc, hΦ, hfj, ha⟩ := frozenFlow_inverse_On W gradW hgradW L hL f T hT hf_mom
      hf_cont hf_cont_deriv charX charV hflow hcontIcc τ hτ
    exact dualCore_main gradW L hL f T hf_weak hf_mom hf_narrow
      M_ρ hM_ρ_nn hM_ρ charX charV hflow τ hτ φ hφ hφc
      Ψ hl hr hc hΦ hfj ha
  -- joint flow continuity (τ-independent; extract from one interior frozenFlow call)
  have hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) := by
    obtain ⟨_, _, _, _, _, hfj, _⟩ := frozenFlow_inverse_On W gradW hgradW L hL f T hT hf_mom
      hf_cont hf_cont_deriv charX charV hflow hcontIcc (T/2) ⟨by linarith, by linarith⟩
    exact hfj
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · -- t = 0 : trivial, `Φ_0 = id` (hinit)
    rw [← h0]
    simp only [hinit]
  · rcases eq_or_lt_of_le ht.2 with hTe | hlt
    · -- t = T : terminal endpoint via the `t → T⁻` limit
      rw [hTe]
      exact dualCore_terminal f T hT hf_mom hf_narrow charX charV hcontIcc hflowjoint φ hφ hφc hIoo
    · -- t ∈ Ioo 0 T
      exact hIoo t ⟨h0, hlt⟩

omit [NeZero d] in
/-- **C3 #8 — the weak solution equals its frozen-field pushforward on the window.**

`f t = (Φ_t)_# (f 0)` on `[0,T]`.  Skeleton: `measure_eq_of_forall_Cc_integral_eq` (#9) reduces
this to per-`C_c^∞`-test integral equality, and `integral_map` turns the pushforward side into
`∫ φ∘Φ_t d(f 0)` — leaving exactly the dual-transport core
`weak_eq_frozenField_pushforward_dualCore`.  Flow measurability on the window (needed by
`integral_map` and the probability-measure instances) comes from an L11 clamp of `ρ^f` into
`[0,T]` + `charFlow_measurable_via_gronwall_Ioo`. -/
theorem weak_eq_frozenField_pushforward_On
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hderivIco : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW (fun t => spatialMarginal (f t)) s (charX s z, charV s z))
        (Set.Ici s) s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) := by
  classical
  -- L11 clamp `ρ^f := spatialMarginal ∘ f` into the window so the universal-instance
  -- measurability lemma `charFlow_measurable_via_gronwall_Ioo` applies.
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht; simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  have h_int_window : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f t)) :=
    fun t ht => (convolveField_window_setup gradW L hL f T hf_mom M_ρ hM_ρ
      (‖gradW 0‖ + (L : ℝ) * M_ρ) rfl t ht).2.1
  -- Clamped curve `ρ'` with the universal probability instance + force integrability.
  set ρ' : ℝ → Measure (PhysSpace d) := fun t => spatialMarginal (f (clampT t)) with hρ'_def
  have hρ'_prob : ∀ t, IsProbabilityMeasure (ρ' t) := by
    intro t
    have : IsProbabilityMeasure (f (clampT t)) := (hf_mom (clampT t) (hclampT_mem t)).1
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have h_int' : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' t) :=
    fun t x => h_int_window (clampT t) (hclampT_mem t) x
  -- `ρ'`-flavoured velocity ODE on `Ioo 0 T` (clamp = id there, so the field is unchanged).
  have h_deriv_Ioo' : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ' s (charX s z, charV s z)) (Set.Ici s) s := by
    intro z s hs
    have h := hderivIco z s (Set.Ioo_subset_Ico_self hs)
    have hρeq : ρ' s = spatialMarginal (f s) := by
      simp only [hρ'_def, hclampT_id s (Set.Ioo_subset_Icc_self hs)]
    have hfield : vlasovVectorField gradW ρ' s (charX s z, charV s z)
        = vlasovVectorField gradW (fun t => spatialMarginal (f t)) s (charX s z, charV s z) := by
      simp only [vlasovVectorField, hρeq]
    rw [hfield]; exact h
  -- Flow measurability on the window.
  have hΦ_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL ρ' h_int' charX charV T hT.le
      hinit hcontIcc h_deriv_Ioo'
  -- Main reduction: `#9` + `integral_map` ⟹ the dual-transport core.
  intro t ht
  have hft_prob : IsProbabilityMeasure (f t) := (hf_mom t ht).1
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hΦt_aem : AEMeasurable (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) :=
    (hΦ_meas t ht).aemeasurable
  have hmap_prob :
      IsProbabilityMeasure (Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) :=
    (Measure.isProbabilityMeasure_map_iff hΦt_aem).mpr inferInstance
  refine measure_eq_of_forall_Cc_integral_eq (fun φ hφ hφc => ?_)
  rw [integral_map hΦt_aem hφ.continuous.aestronglyMeasurable]
  exact weak_eq_frozenField_pushforward_dualCore W gradW hgradW L hL f T hT hf_weak hf_mom hf_narrow
    hf_cont hf_cont_deriv M_ρ hM_ρ_nn hM_ρ charX charV hflow hinit hcontIcc t ht φ hφ hφc

omit [NeZero d] in
/-- **Weak ⟹ Lagrangian on `[0,T]`** (tex: thm:weak-lagrangian).

Under `AssW2` (`W ∈ C²`) and a per-window smallness, every weak Vlasov solution on `[0,T]` with
finite first moments (and the ρ-regularity the frozen-field flow construction needs) is the
pushforward of its initial datum under the characteristic flow it generates — i.e. it is
Lagrangian.  This is the localized, forward-window form matching `vlasovWellPosedness`'s
architecture; the universal form is obtained by window-gluing (deferred).

Hypotheses mirror what `exists_vlasov_characteristicFlow_global_smallT` consumes for the frozen
curve `ρ^f := fun t => spatialMarginal (f t)`.

`hf_cont_deriv` (joint continuity of the convolution-*derivative* field
`∫ fderiv gradW (x−y) ∂ρ^f_s`) is the regularity threaded down to the variational equation (`#3`);
like `hf_cont` it is *assumed* at the bridge boundary (**Option A**).  In the complete theory it is
derivable from `hf_weak` + `hf_mom` (tightness) via a narrow-continuity upgrade — the **Option-B**
extension that would let the bridge assume only the weak solution + moments; see `#3`'s docstring.

Proof (complete, axiom-clean; built over C1–C4 per the roadmap above):
freeze the field at `ρ^f`, build its flow `Φ` (#2) and the pushforward `g := (Φ_t)_# (f 0)` which
solves the frozen linear weak eq (#1); show `f = g` by the dual-transported-test-function
uniqueness (#3–#9, the variational-equation crux); conclude `f` is Lagrangian (#10). -/
theorem weak_isLagrangianVlasovSolutionOn
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (hTL_PL : LocalSmallnessPLBuffer L T) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  classical
  -- Frozen field `ρ^f := spatialMarginal ∘ f`: discharge the flow-construction hypotheses of #2.
  have hρ_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (spatialMarginal (f t)) := by
    intro t ht
    have : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have hsetup := convolveField_window_setup gradW L hL f T hf_mom M_ρ hM_ρ
    (‖gradW 0‖ + (L : ℝ) * M_ρ) rfl
  have h_y_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f t)) :=
    fun t ht => (hsetup t ht).1
  have h_int : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f t)) :=
    fun t ht => (hsetup t ht).2.1
  have hρ_cont : ∀ x : PhysSpace d,
      ContinuousOn (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x)
        (Set.Icc (0 : ℝ) T) :=
    fun x => (hf_cont x).continuousOn
  -- #2: build the frozen-field characteristic flow on the window.
  obtain ⟨charX, charV, hflow, hinit, hcontIcc, hderivIco⟩ :=
    exists_frozenField_charFlow_On W gradW hgradW L hL (fun t => spatialMarginal (f t))
      T hT hTL_PL hρ_prob h_int hρ_cont h_y_int M_ρ hM_ρ_nn hM_ρ
  -- #8: `f` equals its frozen-field pushforward on the window (the dual-argument crux).
  have hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) :=
    weak_eq_frozenField_pushforward_On W gradW hgradW L hL f T hT hf_weak hf_mom hf_narrow hf_cont
      hf_cont_deriv M_ρ hM_ρ_nn hM_ρ charX charV hflow hinit hcontIcc hderivIco
  -- Assemble the localized Lagrangian witness.
  refine ⟨hf_weak, charX, charV, hflow, hpush, ?_, hcontIcc⟩
  -- AEMeasurability of the flow at each window time, from the Grönwall Lipschitz-in-`z`
  -- bound (`charFlow_measurable_via_gronwall_Ioo`), applied to the frozen field clamped
  -- into the window (L11) so that its universal-in-`t` hypotheses are available.
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht; simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  set ρ' : ℝ → Measure (PhysSpace d) := fun t => spatialMarginal (f (clampT t)) with hρ'_def
  have hρ'_prob : ∀ t, IsProbabilityMeasure (ρ' t) := by
    intro t; simp only [hρ'_def]; exact hρ_prob (clampT t) (hclampT_mem t)
  have h_int' : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' t) :=
    fun t x => h_int (clampT t) (hclampT_mem t) x
  have h_deriv_Ioo' : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ' s (charX s z, charV s z)) (Set.Ici s) s := by
    intro z s hs
    have h := hderivIco z s (Set.Ioo_subset_Ico_self hs)
    have hρeq : ρ' s = spatialMarginal (f s) := by
      simp only [hρ'_def, hclampT_id s (Set.Ioo_subset_Icc_self hs)]
    have hfield : vlasovVectorField gradW ρ' s (charX s z, charV s z)
        = vlasovVectorField gradW (fun t => spatialMarginal (f t)) s (charX s z, charV s z) := by
      simp only [vlasovVectorField, hρeq]
    rw [hfield]; exact h
  exact fun s hs => (charFlow_measurable_via_gronwall_Ioo gradW L hL ρ' h_int' charX charV T hT.le
    hinit hcontIcc h_deriv_Ioo' s hs).aemeasurable

end Vlasov

/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Martingales.MartingaleSetIntegral
public import LeanPool.MathFin.Probability.Martingales.StoppedProcessPaths
public import LeanPool.MathFin.Probability.Support.LocalMartingale
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded local martingales and smaller filtrations

Promotion is proved by dominated convergence of localized set integrals. The file lives in
`Probability/` because the promotion is general: the American-put stopping development and the
localisation of Lévy's characterisation (`LevyCharacterization`) both use it.
No unproved upstream optional-sampling or uniform-integrability result is used.
Adaptation to the target filtration is explicit; a local property alone is
not silently treated as pointwise adaptation on exceptional null outcomes.

## Main results

* `martingale_smaller_filtration`: a martingale for `𝓖` that is adapted to a smaller filtration
  `𝓕 ≤ 𝓖` is a martingale for `𝓕`.
* `locally_bounded_localMartingale_is_martingale`: an adapted local martingale that is bounded on
  `[0,T]` for each `T` is a martingale.
* `bounded_localMartingale_is_martingale`: an adapted local martingale bounded by a constant is a
  martingale.
* `martingale_stoppedProcess_of_locally_bounded`: an adapted continuous-path local martingale
  stopped at a stopping time `ρ` with `⊥ < ρ` everywhere, whose stopped process is bounded on
  `[0,T]` for each `T`, is a martingale.
* `exists_martingale_eqOn`: a continuous-path local martingale with `X 0 = 0` almost surely has a
  localising sequence `σ` such that each `N` has a continuous-path martingale `Y` agreeing almost
  surely with `X` at each time `t ≤ σ N`.
* `isLocalMartingale_congr_ae`: a process `Y` adapted with càdlàg paths and almost surely equal
  to a local martingale `X` (`X ≡ᵐ[P] Y`) is a local martingale.

## Tags

local martingale, localization, dominated convergence, martingale property, smaller filtration,
MSC 60G44, MSC 60G48
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {𝓕 𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X : ℝ≥0 → Ω → ℝ}

theorem martingale_smaller_filtration (hFG : 𝓕 ≤ 𝓖) (hX : Martingale X 𝓖 P)
    (hadapt : StronglyAdapted 𝓕 X) : Martingale X 𝓕 P :=
  martingale_iff_setIntegral_eq.2 ⟨hadapt, hX.integrable,
    fun _ _ hij _ hs => hX.setIntegral_eq hij (hFG _ _ hs)⟩

theorem locally_bounded_localMartingale_is_martingale (hX : IsLocalMartingale X 𝓕 P)
    (hadapt : StronglyAdapted 𝓕 X)
    (hbound : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t, t ≤ T → ∀ ω, ‖X t ω‖ ≤ C) :
    Martingale X 𝓕 P := by
  obtain ⟨τ,hτ,hloc⟩ := hX
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n =>
    stoppedProcess (fun t => {ω | ⊥ < τ n ω}.indicator (X t)) (τ n)
  have hY : ∀ n, Martingale (Y n) 𝓕 P := fun n => (hloc n).1
  have hYbound : ∀ t, ∃ C : ℝ, ∀ n ω, ‖Y n t ω‖ ≤ C := by
    intro t
    obtain ⟨C,hC⟩ := hbound t
    refine ⟨C,fun n ω => ?_⟩
    have hu : (min (t : WithTop ℝ≥0) (τ n ω)).untopA ≤ t :=
      WithTop.untopA_le (min_le_left _ _)
    exact (norm_indicator_le_norm_self _ _).trans (hC _ hu ω)
  have hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Y n t ω) atTop (𝓝 (X t ω)) := by
    intro t
    filter_upwards [hτ.tendsto_top] with ω hω
    have hlarge : ∀ᶠ n in atTop, ((t+1 : ℝ≥0) : WithTop ℝ≥0) < τ n ω :=
      hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top (t+1)))
    have heq : (fun n => Y n t ω) =ᶠ[atTop] (fun _ => X t ω) := by
      filter_upwards [hlarge] with n hn
      have hle : (t : WithTop ℝ≥0) ≤ τ n ω :=
        (show (t : WithTop ℝ≥0) ≤
            (t+1 : ℝ≥0) by exact_mod_cast le_add_of_nonneg_right zero_le).trans hn.le
      have hpos : (⊥ : WithTop ℝ≥0) < τ n ω :=
        (show (⊥ : WithTop ℝ≥0) < (t+1 : ℝ≥0) by
          change (0 : WithTop ℝ≥0) < _
          exact_mod_cast (show (0 : ℝ≥0) < t+1 by positivity)).trans hn
      exact (stoppedProcess_eq_of_le hle).trans
        (indicator_of_mem (show ω ∈ {ω | ⊥ < τ n ω} from hpos) _)
    exact tendsto_const_nhds.congr' heq.symm
  have hint : ∀ t, Integrable (X t) P := by
    intro t
    obtain ⟨C,hC⟩ := hbound t
    exact (integrable_const C).mono' ((hadapt t).mono (𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall (hC t le_rfl))
  refine martingale_iff_setIntegral_eq.2 ⟨hadapt, hint, fun i j hij s hs ↦ ?_⟩
  have hconv (t : ℝ≥0) : Tendsto (fun n => ∫ ω in s, Y n t ω ∂P) atTop
      (𝓝 (∫ ω in s, X t ω ∂P)) := by
    obtain ⟨C,hC⟩ := hYbound t
    exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((hY n).integrable t).aestronglyMeasurable.restrict) (integrable_const C)
      (fun n => Eventually.of_forall (hC n)) (ae_restrict_of_ae (hlim t))
  have hi := hconv i
  have heq : (fun n => ∫ ω in s, Y n i ω ∂P) = (fun n => ∫ ω in s, Y n j ω ∂P) :=
    funext (fun n => (hY n).setIntegral_eq hij hs)
  rw [heq] at hi
  exact tendsto_nhds_unique hi (hconv j)

theorem bounded_localMartingale_is_martingale (hX : IsLocalMartingale X 𝓕 P)
    (hadapt : StronglyAdapted 𝓕 X) {C : ℝ}
    (hbound : ∀ t ω, ‖X t ω‖ ≤ C) : Martingale X 𝓕 P :=
  locally_bounded_localMartingale_is_martingale hX hadapt
    (fun _ => ⟨C,fun t _ ω => hbound t ω⟩)

/-- **A continuous adapted local martingale stopped at a positive stopping time where it is
locally bounded is a martingale.** Stopping a local martingale keeps it a local martingale
(`IsStable.locally`); at a positive `ρ` the stopping indicator is inert
(`stoppedProcess_indicator_eq`), so this is `locally_bounded_localMartingale_is_martingale`. -/
theorem martingale_stoppedProcess_of_locally_bounded {ρ : Ω → WithTop ℝ≥0}
    (hX : IsLocalMartingale X 𝓕 P) (hXad : StronglyAdapted 𝓕 X)
    (hXc : ∀ ω, Continuous fun t ↦ X t ω) (hρ : IsStoppingTime 𝓕 ρ) (hpos : ∀ ω, ⊥ < ρ ω)
    (hbound : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t, t ≤ T → ∀ ω, ‖stoppedProcess X ρ t ω‖ ≤ C) :
    Martingale (stoppedProcess X ρ) 𝓕 P := by
  have hloc := (isStable_martingale (𝓕 := 𝓕) (P := P)).locally X hX _ hρ
  rw [stoppedProcess_indicator_eq hpos] at hloc
  have had := hXad.stoppedProcess_indicator (fun ω ↦ (hXc ω).isCadlag.isRightContinuous) hρ
  rw [stoppedProcess_indicator_eq hpos] at had
  exact locally_bounded_localMartingale_is_martingale hloc had hbound

omit [IsFiniteMeasure P] in
/-- **A continuous local martingale is, along its localising sequence, a continuous martingale.**
For `σ` the localising sequence of `X`, each `N` has a continuous martingale `Y` (`X` stopped at
`σ N`, zeroed where `σ N = 0`) with `X t = Y t` almost surely on `{t ≤ σ N}`. The zeroing is
invisible because `X 0 = 0` almost surely. -/
theorem exists_martingale_eqOn (hX : IsLocalMartingale X 𝓕 P)
    (hXc : ∀ ω, Continuous fun t ↦ X t ω) (hX0 : ∀ᵐ ω ∂P, X 0 ω = 0) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence 𝓕 σ P ∧ ∀ N, ∃ Y : ℝ≥0 → Ω → ℝ,
      Martingale Y 𝓕 P ∧ (∀ ω, Continuous fun t ↦ Y t ω) ∧
        ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (t : WithTop ℝ≥0) ≤ σ N ω → X t ω = Y t ω := by
  obtain ⟨σ, hσ, hloc⟩ := hX
  refine ⟨σ, hσ, fun N ↦ ⟨_, (hloc N).1, fun ω ↦ ?_, fun t ↦ hX0.mono fun ω h0 hle ↦ ?_⟩⟩
  · by_cases hpos : ⊥ < σ N ω
    · simp only [stoppedProcess, Set.indicator_of_mem (show ω ∈ {ω | ⊥ < σ N ω} from hpos)]
      exact (hXc ω).comp (continuous_untopA_min _)
    · simp only [stoppedProcess, Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < σ N ω} from hpos)]
      exact continuous_const
  · by_cases hpos : ⊥ < σ N ω
    · rw [stoppedProcess_eq_of_le hle, Set.indicator_of_mem (show ω ∈ {ω | ⊥ < σ N ω} from hpos)]
    · obtain rfl : t = 0 := le_antisymm (WithTop.coe_le_coe.1 (hle.trans (not_lt.1 hpos))) zero_le
      rw [h0]
      simp only [stoppedProcess]
      rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < σ N ω} from hpos)]

omit [IsFiniteMeasure P] in
/-- **A process indistinguishable from a local martingale is one**, provided it is adapted with
cadlag paths: the stopped processes are almost surely equal at each time, hence have the same
conditional expectations, and the stopped `Y` is adapted. -/
theorem isLocalMartingale_congr_ae {Y : ℝ≥0 → Ω → ℝ} (hX : IsLocalMartingale X 𝓕 P)
    (hY : StronglyAdapted 𝓕 Y) (hYc : ∀ ω, IsCadlag fun t ↦ Y t ω)
    (hXY : X ≡ᵐ[P] Y) : IsLocalMartingale Y 𝓕 P := by
  obtain ⟨τ, hτ, hloc⟩ := hX
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  obtain ⟨hmart, -⟩ := hloc n
  have ht (t : ℝ≥0) : (fun ω ↦ stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) t ω)
      =ᵐ[P] fun ω ↦ stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (Y i)) (τ n) t ω := by
    filter_upwards [hXY] with ω h
    simp only [stoppedProcess, Set.indicator_apply, h]
  exact ⟨⟨hY.stoppedProcess_indicator (fun ω ↦ (hYc ω).isRightContinuous) (hτ.isStoppingTime n),
    fun i j hij ↦ (condExp_congr_ae (ht j).symm).trans ((hmart.2 i j hij).trans (ht i))⟩,
    isStable_isCadlag Y hYc _ (hτ.isStoppingTime n)⟩

end MathFin

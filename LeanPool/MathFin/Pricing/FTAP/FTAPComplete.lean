/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.FTAP.FTAPDiscrete

/-!
# Second FTAP on a finite probability space: complete ↔ unique equivalent martingale measure

For the finite-Ω, finite-horizon, single-asset market of `FTAPDiscrete.lean` (a full-support
probability `P`, an adapted discounted price `S`, a horizon `T`), a market with no arbitrage and
full information at the horizon (`𝓕 T = ⊤`) is **complete** (`IsCompleteMarket`: every claim is
the terminal wealth of a predictable strategy started from some initial wealth) **iff** its
equivalent martingale measure is **unique**.

* `complete ⇒ unique` is general (`IsEMM.measure_eq_of_isCompleteMarket`, `Pricing/FTAP/FTAP.lean`):
  replicate the indicator of an event and read off its probability.
* `unique ⇒ complete` is the geometric half, by contraposition. The claims replicable from some
  wealth are `constants ⊔ gainsSubspace`. If that subspace is proper, a nonzero functional `η`
  vanishes on it, i.e. `∑ η = 0` and `η` annihilates every gain. Perturbing the strictly positive
  weights of an equivalent martingale measure `Q₀` by a small multiple of `η` keeps them strictly
  positive and still annihilating, so they build a second equivalent martingale measure
  (`exists_isEMM_of_pos_dual`), different from `Q₀` because `η ≠ 0`.

## Main results

* `isCompleteMarket_of_unique` — a unique equivalent martingale measure makes the market complete.
* `ftap_two` — under no arbitrage, and with full information `𝓕 T = ⊤` at the horizon, the market
  is complete iff the equivalent martingale measure is unique.

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  Theorem 5.30
* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]

## Tags

second fundamental theorem, market completeness, unique martingale measure, replication,
finite probability space, JEL G13, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω}
  [MeasurableSingletonClass Ω] (𝓕 : Filtration ℕ mΩ) (P : Measure Ω) (S : ℕ → Ω → ℝ) (T : ℕ)

variable {𝓕 P S T} in
/-- **Gains are a fair game under an equivalent martingale measure**: every element of the
attainable-gains subspace has `Q`-mean zero. -/
theorem IsEMM.sum_mul_eq_zero_of_mem_gainsSubspace {Q : Measure Ω} (hQ : IsEMM 𝓕 P S T Q)
    {g : Ω → ℝ} (hg : g ∈ gainsSubspace 𝓕 S T) : ∑ ω, Q.real {ω} * g ω = 0 := by
  have := hQ.isProb
  obtain ⟨φ, hφ, rfl⟩ := mem_gains_imp_predictable 𝓕 S T hg
  have h := hQ.integral_martingaleTransform (fun t _ ↦ hφ t) (exists_bound_horizon T φ)
  rw [integral_fintype Integrable.of_finite] at h
  simpa using h

omit [Fintype Ω] in
/-- **Second FTAP, `unique ⇒ complete`**: if the market has an equivalent martingale measure and
only one, every claim is replicated by a predictable strategy from some initial wealth. -/
theorem isCompleteMarket_of_unique [Finite Ω] [Nonempty Ω] (hS : StronglyAdapted 𝓕 S)
    (hP : ∀ ω, 0 < P {ω})
    {Q₀ : Measure Ω} (h₀ : IsEMM 𝓕 P S T Q₀) (hu : ∀ Q, IsEMM 𝓕 P S T Q → Q = Q₀) :
    IsCompleteMarket 𝓕 P S T := by
  classical
  cases nonempty_fintype Ω
  have := h₀.isProb
  have hW : Submodule.span ℝ {fun _ : Ω ↦ (1 : ℝ)} ⊔ gainsSubspace 𝓕 S T = ⊤ := by
    by_contra hne
    obtain ⟨η, hη0, hη⟩ := exists_ne_zero_sum_mul_eq_zero (lt_top_iff_ne_top.2 hne)
    have hsum : ∑ ω, η ω = 0 := by
      simpa using hη _ (Submodule.mem_sup_left (Submodule.subset_span rfl))
    -- the weights of `Q₀`
    set p : Ω → ℝ := fun ω ↦ Q₀.real {ω}
    have hp_pos (ω : Ω) : 0 < p ω :=
      ENNReal.toReal_pos (fun h ↦ (hP ω).ne' (h₀.ac' h)) (measure_ne_top _ _)
    have hp_sum : ∑ ω, p ω = 1 := by simp [p]
    -- a small perturbation of the weights in the direction `η` keeps them positive
    obtain ⟨ε, hεpos, hq_pos⟩ := exists_pos_add_mul_pos hp_pos η
    have hq_dual (g : Ω → ℝ) (hg : g ∈ gainsSubspace 𝓕 S T) :
        ∑ ω, (p ω + ε * η ω) * g ω = 0 := by
      have : ∑ ω, (p ω + ε * η ω) * g ω = ∑ ω, p ω * g ω + ε * ∑ ω, g ω * η ω := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ω _ ↦ by ring
      rw [this, h₀.sum_mul_eq_zero_of_mem_gainsSubspace hg, hη g (Submodule.mem_sup_right hg)]
      simp
    obtain ⟨Q', hQ', hQ's⟩ := exists_isEMM_of_pos_dual 𝓕 P S T hS hP hq_pos hq_dual
    have hZ : ∑ ω, (p ω + ε * η ω) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hp_sum]
      simp
    refine hη0 (funext fun ω ↦ ?_)
    have h2 := hQ's ω
    rw [hZ, div_one, hu Q' hQ'] at h2
    have h3 : p ω + ε * η ω = p ω :=
      (ENNReal.ofReal_eq_ofReal_iff (hq_pos ω).le (hp_pos ω).le).1
        (h2.symm.trans (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm)
    exact (mul_eq_zero.1 (by linarith : ε * η ω = 0)).resolve_left hεpos.ne'
  intro H _ _
  obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 (hW ▸ Submodule.mem_top : H ∈ _)
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨φ, hφ, rfl⟩ := mem_gains_imp_predictable 𝓕 S T hg
  exact ⟨x, φ, fun t _ ↦ hφ t, exists_bound_horizon T φ,
    Filter.Eventually.of_forall fun ω ↦ by simp⟩

omit [Fintype Ω] in
/-- **The Second Fundamental Theorem of Asset Pricing on a finite probability space.** For a
single-asset, finite-horizon market on a finite full-support space with no arbitrage and full
information at the horizon (`𝓕 T = ⊤`), the market is complete iff its equivalent martingale
measure is unique. -/
theorem ftap_two [Finite Ω] [Nonempty Ω] (hS : StronglyAdapted 𝓕 S) (hP : ∀ ω, 0 < P {ω})
    (hT : 𝓕 T = mΩ)
    (hNA : NoArbitrage 𝓕 P S T) : IsCompleteMarket 𝓕 P S T ↔ ∃! Q, IsEMM 𝓕 P S T Q := by
  refine ⟨fun hc ↦ ?_, fun ⟨Q₀, h₀, hu⟩ ↦ isCompleteMarket_of_unique 𝓕 P S T hS hP h₀ hu⟩
  obtain ⟨Q₀, h₀⟩ := exists_isEMM_of_noArbitrage 𝓕 P S T hS hP hNA
  exact ⟨Q₀, h₀, fun Q hQ ↦ Measure.ext fun A hA ↦
    hQ.measure_eq_of_isCompleteMarket hc h₀ (by rw [hT]; exact hA)⟩

end MathFin

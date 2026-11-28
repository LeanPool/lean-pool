/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Bounded in `L²` ⟹ uniformly integrable in `L¹` (a finite-measure Vitali producer)

Mathlib provides the Vitali *consumer* `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`
(uniform integrability + convergence in measure ⟹ `L¹` convergence) but **no producer** of uniform
integrability from an `Lᵖ` bound with `p > 1`. This file supplies the `p = 2` case (the truncation
producer needs no finiteness of `μ` — only the downstream Vitali consumer does):

* `MathFin.unifIntegrable_one_of_sq_integral_le` — a family `f : ι → α → ℝ` with `f i ∈ L²` and a
  **uniform** second-moment bound `∫ (f i)² ≤ M` is `UnifIntegrable f 1 μ`.

The proof is a Chebyshev truncation fed to `MeasureTheory.unifIntegrable_of`: on `{‖f i‖ ≥ C}` one
has `C·‖f i‖ ≤ ‖f i‖²`, so the truncated `L¹` tail `∫_{‖f i‖≥C} ‖f i‖ ≤ C⁻¹·∫‖f i‖² ≤ C⁻¹·M`, which
is `≤ ε` once `C ≥ M/ε` — uniformly in `i`.

The intended use is the `L²→L¹` limit of Girsanov Doléans densities `Z⁽ⁿ⁾_T`, whose uniform bound
`∫ (Z⁽ⁿ⁾)² ≤ exp(K²T)` comes from the `Z² = E^{−2c}·exp(∑ c²Δτ)` identity; this lemma is the piece
that lets convergence in measure upgrade to `L¹` (hence `∫ Z⁽ⁿ⁾ → ∫ Z`, delivering unit mean).

## Main results

* `unifIntegrable_one_of_sq_integral_le`: a family in `L²` with a uniform bound
  `∫ (f i)² ≤ M` on second moments is uniformly integrable in `L¹`.
* `tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound`: on a finite measure, an `L²`-bounded
  sequence converging in measure to `g ∈ L¹` has set integrals converging to those of `g`.
* `tendsto_setIntegral_of_subseq_ae_of_sq_bound`: the same conclusion from the a.e.-subsequence
  principle in place of convergence in measure.
* `memLp_two_of_subseq_ae_of_sq_bound`: an a.e.-subsequence limit of an `L²`-bounded sequence of
  measurable functions is in `L²` (Fatou).

## Tags

uniform integrability, Vitali convergence, Chebyshev truncation, second-moment bound,
L1 convergence, MSC 28A25, MSC 60E15
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MathFin

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {ι : Type*} {f : ι → α → ℝ}

/-- **Bounded in `L²` ⟹ uniformly integrable in `L¹`.** If every `f i` is in `L²` and their second
moments are uniformly bounded (`∫ (f i)² ≤ M`), then `f` is uniformly integrable in `L¹`. Chebyshev
truncation: `∫_{‖f i‖≥C} ‖f i‖ ≤ C⁻¹·M ≤ ε` for `C ≥ M/ε`, uniformly in `i` — no finiteness of `μ`
is needed for the truncation bound itself. -/
theorem unifIntegrable_one_of_sq_integral_le (hf : ∀ i, MemLp (f i) 2 μ)
    {M : ℝ} (hM : ∀ i, ∫ x, (f i x) ^ 2 ∂μ ≤ M) :
    UnifIntegrable f 1 μ := by
  refine unifIntegrable_of le_rfl (by norm_num) (fun i ↦ (hf i).aestronglyMeasurable) ?_
  intro ε' hε'
  rcases eq_or_ne ε' ⊤ with rfl | hε'top
  · exact ⟨0, fun _ ↦ le_top⟩
  obtain ⟨ε, hε, rfl⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε = ε' :=
    ⟨ε'.toReal, ENNReal.toReal_pos hε'.ne' hε'top, ENNReal.ofReal_toReal hε'top⟩
  refine ⟨Real.toNNReal (M / ε) + 1, fun i ↦ ?_⟩
  set C : ℝ≥0 := Real.toNNReal (M / ε) + 1 with hCdef
  have hCpos : (0 : ℝ≥0∞) < (C : ℝ≥0∞) := by
    rw [ENNReal.coe_pos, hCdef]; positivity
  -- `∫⁻ ‖f i‖ₑ² = ofReal (∫ (f i)²) ≤ ofReal M`.
  have hlint_sq : ∫⁻ x, ‖f i x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal M := by
    have hpt : ∀ x, ‖f i x‖ₑ ^ 2 = ENNReal.ofReal ((f i x) ^ 2) := fun x ↦ by
      rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    calc ∫⁻ x, ‖f i x‖ₑ ^ 2 ∂μ = ∫⁻ x, ENNReal.ofReal ((f i x) ^ 2) ∂μ := by simp_rw [hpt]
      _ = ENNReal.ofReal (∫ x, (f i x) ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal ((hf i).integrable_sq)
            (ae_of_all _ fun x ↦ sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (hM i)
  -- `eLpNorm (indicator …) 1 = ∫⁻ over the truncation set of `‖f i‖ₑ`.
  rw [eLpNorm_one_eq_lintegral_eNorm ((hf i).aestronglyMeasurable.indicator₀
    (nullMeasurableSet_le aemeasurable_const (hf i).aestronglyMeasurable.nnNorm.aemeasurable))]
  set S : Set α := {x | C ≤ ‖f i x‖₊}
  have henorm_ind : ∀ x, ‖S.indicator (f i) x‖ₑ = S.indicator (fun x ↦ ‖f i x‖ₑ) x := fun x ↦ by
    by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [henorm_ind]
  -- Chebyshev: `C · S.indicator ‖f i‖ₑ ≤ ‖f i‖ₑ²` pointwise.
  have hpt_cheb : ∀ x, (C : ℝ≥0∞) * S.indicator (fun x ↦ ‖f i x‖ₑ) x ≤ ‖f i x‖ₑ ^ 2 := fun x ↦ by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, sq]
      have hCx : (C : ℝ≥0∞) ≤ ‖f i x‖ₑ := by
        rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.norm_eq_abs, ← coe_nnNorm]
        exact_mod_cast hx
      exact mul_le_mul' hCx le_rfl
    · rw [Set.indicator_of_notMem hx, mul_zero]; exact zero_le
  have hchain : (C : ℝ≥0∞) * ∫⁻ x, S.indicator (fun x ↦ ‖f i x‖ₑ) x ∂μ ≤ ENNReal.ofReal M := by
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact (lintegral_mono hpt_cheb).trans hlint_sq
  -- `C · I ≤ ofReal M ≤ C · ofReal ε`, then cancel `C`.
  have hMCε : ENNReal.ofReal M ≤ (C : ℝ≥0∞) * ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (C : ℝ))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : M / ε ≤ (C : ℝ) := by
      rw [hCdef]; push_cast [Real.coe_toNNReal']; linarith [le_max_left (M / ε) (0 : ℝ)]
    calc M = M / ε * ε := by rw [div_mul_cancel₀ _ hε.ne']
      _ ≤ (C : ℝ) * ε := mul_le_mul_of_nonneg_right hle hε.le
  have hcancel := hchain.trans hMCε
  rw [mul_comm (C : ℝ≥0∞), mul_comm (C : ℝ≥0∞)] at hcancel
  exact (ENNReal.mul_le_mul_iff_left hCpos.ne' ENNReal.coe_ne_top).mp hcancel

/-- **Set-integral `L¹`-convergence from an `L²` bound + convergence in measure.** On a finite
measure, a family `f : ℕ → α → ℝ` with `f n ∈ L²`, a **uniform** second-moment bound
`∫ (f n)² ≤ M`, and convergence in measure `f n → g` (with `g ∈ L¹`) satisfies
`∫_A f n → ∫_A g` on every set `A`. The `L²` bound produces uniform integrability
(`unifIntegrable_one_of_sq_integral_le`), which upgrades convergence in measure to `L¹`
(the Vitali consumer `tendsto_Lp_finite_of_tendstoInMeasure`), and `L¹` convergence transfers
to (set-)integrals (`tendsto_setIntegral_of_L1`). This is the endpoint the Girsanov continuous
Doléans limit consumes: `Z⁽ⁿ⁾ → Z` in measure with `∫ (Z⁽ⁿ⁾)² ≤ exp(K²T)` gives
`∫_A f(B^θⁿ) Z⁽ⁿ⁾ → ∫_A f(B^θ) Z` for every `𝓕`-set `A`. -/
theorem tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    {M : ℝ} (hM : ∀ n, ∫ x, (f n x) ^ 2 ∂μ ≤ M) (hg : MemLp g 1 μ)
    (hconv : TendstoInMeasure μ f atTop g) (A : Set α) :
    Tendsto (fun n ↦ ∫ x in A, f n x ∂μ) atTop (𝓝 (∫ x in A, g x ∂μ)) := by
  have hui : UnifIntegrable f 1 μ := unifIntegrable_one_of_sq_integral_le hf hM
  have hL1 : Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      (fun n ↦ (hf n).aestronglyMeasurable) hg hui hconv
  refine tendsto_setIntegral_of_L1 g hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun n ↦ (hf n).integrable (by norm_num)) ?_ A
  exact hL1.congr fun n ↦
    eLpNorm_one_eq_lintegral_eNorm ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable)

/-- **Set-integral limit from the a.e.-subsequence principle + an `L²` bound.** On a finite measure,
a family `f : ℕ → α → ℝ` with `f n ∈ L²`, a uniform second-moment bound `∫ (f n)² ≤ M`, a limit
`g ∈ L¹`, and the hypothesis that **every subsequence has a further subsequence converging to `g`
a.e.** satisfies `∫_A f n → ∫_A g`. This routes the composition of convergences (exp, sums,
products) through the a.e. level — where continuity is free — instead of through a
`TendstoInMeasure` algebra that Mathlib does not provide. The real sequence `∫_A f n` converges by
the subsequence principle (`tendsto_of_subseq_tendsto`): each subsequence's a.e.-sub-subsequence
gives convergence in measure (`tendstoInMeasure_of_tendsto_ae`), which
`tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound` turns into the set-integral limit. This is the
endpoint the continuous-Girsanov Doléans limit consumes: `f n = exp(a·B^θⁿ)·Z⁽ⁿ⁾`, whose stochastic
part converges in measure (brick b) so every subsequence has an a.e.-convergent one, while the drift
parts converge everywhere. -/
theorem tendsto_setIntegral_of_subseq_ae_of_sq_bound [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    {M : ℝ} (hM : ∀ n, ∫ x, (f n x) ^ 2 ∂μ ≤ M) (hg : MemLp g 1 μ)
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, ∀ᵐ x ∂μ, Tendsto (fun k ↦ f (ns (ms k)) x) atTop (𝓝 (g x)))
    (A : Set α) :
    Tendsto (fun n ↦ ∫ x in A, f n x ∂μ) atTop (𝓝 (∫ x in A, g x ∂μ)) := by
  refine tendsto_of_subseq_tendsto (fun ns hns ↦ ?_)
  obtain ⟨ms, hae⟩ := hsub ns hns
  refine ⟨ms, ?_⟩
  have hconv : TendstoInMeasure μ (fun k ↦ f (ns (ms k))) atTop g :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (hf _).aestronglyMeasurable) hae
  exact tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound
    (fun k ↦ hf (ns (ms k))) (fun k ↦ hM (ns (ms k))) hg hconv A

/-- **Fatou `L²`-membership of an a.e.-subsequence limit.** If every `f n ∈ L²` with a uniform
second moment `∫ (f n)² ≤ M`, and some subsequence has `f (msₖ) → g` a.e., then `g ∈ L²`: Fatou on
the squared enorms, `∫⁻ ‖g²‖ₑ ≤ liminf ∫⁻ ‖f(msₖ)²‖ₑ = liminf ∫ f(msₖ)² ≤ M < ∞`. No finiteness of
`μ` is needed (pure Fatou) — the limit-side companion to the finite-measure Vitali producers above,
and the single principle behind an a.e.-subsequential `L²` limit inheriting its family's uniform
second moment (both the Girsanov continuous and predictable Doléans densities consume it). -/
theorem memLp_two_of_subseq_ae_of_sq_bound {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hmeas : ∀ n, Measurable (f n))
    {M : ℝ} (hM : ∀ n, ∫ x, (f n x) ^ 2 ∂μ ≤ M)
    (hsub : ∃ ms : ℕ → ℕ, ∀ᵐ x ∂μ, Tendsto (fun k ↦ f (ms k) x) atTop (𝓝 (g x))) :
    MemLp g 2 μ := by
  obtain ⟨ms, hae⟩ := hsub
  have hgmeas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k ↦ (hmeas (ms k)).aestronglyMeasurable) hae
  rw [memLp_two_iff_integrable_sq hgmeas]
  refine ⟨hgmeas.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have hsqbnd : ∀ k, ∫⁻ x, ‖(f (ms k) x) ^ 2‖ₑ ∂μ ≤ ENNReal.ofReal M := fun k ↦ by
    have hint_sq := (memLp_two_iff_integrable_sq (hf (ms k)).aestronglyMeasurable).mp (hf (ms k))
    calc ∫⁻ x, ‖(f (ms k) x) ^ 2‖ₑ ∂μ
        = ∫⁻ x, ENNReal.ofReal ((f (ms k) x) ^ 2) ∂μ :=
          lintegral_congr fun x ↦ by rw [Real.eNorm_eq_ofReal (sq_nonneg _)]
      _ = ENNReal.ofReal (∫ x, (f (ms k) x) ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint_sq (ae_of_all _ fun x ↦ sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (hM (ms k))
  have hlim : (fun x ↦ ‖(g x) ^ 2‖ₑ)
      =ᵐ[μ] fun x ↦ Filter.liminf (fun k ↦ ‖(f (ms k) x) ^ 2‖ₑ) atTop := by
    filter_upwards [hae] with x hx
    exact ((hx.pow 2).eNorm.liminf_eq).symm
  rw [lintegral_congr_ae hlim]
  exact ((lintegral_liminf_le (fun k ↦ ((hmeas (ms k)).pow_const 2).eNorm)).trans
    ((liminf_le_liminf (Filter.Eventually.of_forall hsqbnd)).trans (liminf_const _).le)).trans_lt
    ENNReal.ofReal_lt_top

end MathFin

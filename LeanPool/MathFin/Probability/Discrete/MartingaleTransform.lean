/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Martingale.Basic

/-!
# Martingale transform (Theorem 2.2.9)

The martingale transform of a martingale by a bounded predictable process is
itself a martingale (the discrete stochastic integral).

The price `M` and the holding `A` take values in a real inner-product space `F`, and a step's
gain is the pairing `⟪A_{k+1}, M_{k+1} − M_k⟫` (a portfolio of several assets against the vector
of their price increments), so the transform is real-valued. The scalar theorem is the case
`F = ℝ`, where `⟪a, b⟫ = a * b` (`Real.inner_apply`): `A_{k+1} * (M_{k+1} − M_k)`.

## Main definitions

* `martingaleTransform`: the discrete stochastic integral
  `(A · M)_n = ∑_{k<n} ⟪A_{k+1}, M_{k+1} − M_k⟫` for `A`, `M` valued in a real inner-product space.

## Main results

* `martingaleTransform_real`: for `F = ℝ` the transform is `∑_{k<n} A_{k+1} * (M_{k+1} − M_k)`.
* `integral_inner_sub_eq_zero`: a bounded `𝓖 s`-measurable weight `φ` against a martingale
  increment has zero mean, `∫ ⟪φ, N t − N s⟫ dμ = 0` for `s ≤ t`.
* `martingaleTransform_isMartingale`: the transform of a martingale `M` by a bounded process `A`
  with `A (n + 1)` adapted is a martingale (Theorem 2.2.9).

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 2.2.9

## Tags

martingale transform, discrete stochastic integral, predictable strategy, self-financing gains,
betting system, MSC 60G42, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {Ω : Type*} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The discrete stochastic integral / martingale-transform process
`(A · M)_n ω := ∑_{k=0}^{n−1} ⟪A_{k+1}(ω), M_{k+1}(ω) − M_k(ω)⟫`. For `F = ℝ` this is
`∑ A_{k+1} * (M_{k+1} − M_k)`. -/
noncomputable def martingaleTransform (A M : ℕ → Ω → F) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, ⟪A (k + 1) ω, M (k + 1) ω - M k ω⟫_ℝ

/-- **The scalar martingale transform** (`F = ℝ`): `∑_{k<n} A_{k+1}(ω) * (M_{k+1}(ω) − M_k(ω))`,
the textbook discrete stochastic integral. -/
theorem martingaleTransform_real (A M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    martingaleTransform A M n ω = ∑ k ∈ Finset.range n, A (k + 1) ω * (M (k + 1) ω - M k ω) := by
  simp only [martingaleTransform, Real.inner_apply]

@[simp] lemma martingaleTransform_zero (A M : ℕ → Ω → F) :
    martingaleTransform A M 0 = 0 := by
  funext ω; simp [martingaleTransform]

/-- Successor expansion for the martingale transform. -/
private lemma martingaleTransform_succ (A M : ℕ → Ω → F) (n : ℕ) :
    martingaleTransform A M (n + 1) =
      martingaleTransform A M n + fun ω ↦ ⟪A (n + 1) ω, M (n + 1) ω - M n ω⟫_ℝ := by
  funext ω
  change ∑ k ∈ Finset.range (n + 1), _ = _
  rw [Finset.sum_range_succ]
  rfl

variable [CompleteSpace F] [m0 : MeasurableSpace Ω] {μ : Measure Ω}
  {𝓕 : Filtration ℕ m0} {M A : ℕ → Ω → F}

section Increment

variable {ι : Type*} [Preorder ι] {𝓖 : Filtration ι m0} {N : ι → Ω → F} {φ : Ω → F}
  {s t : ι} {K : ℝ}

/-- **A bounded `𝓖 s`-measurable weight against a martingale increment is integrable**:
`⟪φ, N t − N s⟫` for a martingale `N` and a weight `‖φ‖ ≤ K` a.e. Cauchy–Schwarz bounds the
pairing by `K · ‖N t − N s‖`, which is integrable. -/
theorem integrable_inner_sub (hN : Martingale N 𝓖 μ) (hφ : StronglyMeasurable[𝓖 s] φ)
    (hK : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ K) : Integrable (fun ω ↦ ⟪φ ω, N t ω - N s ω⟫_ℝ) μ := by
  have hΔ : Integrable (fun ω ↦ N t ω - N s ω) μ := (hN.integrable t).sub (hN.integrable s)
  refine Integrable.mono' (hΔ.norm.const_mul K)
    (((hφ.mono (𝓖.le s)).aestronglyMeasurable).inner hΔ.aestronglyMeasurable) ?_
  filter_upwards [hK] with ω hω
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))

variable [IsFiniteMeasure μ]

/-- **A bounded `𝓖 s`-measurable weight against a martingale increment has vanishing conditional
expectation**: `μ[⟪φ, N t − N s⟫ | 𝓖 s] = 0` for `s ≤ t`. Pull `φ` out of the conditional
expectation and use `μ[N t − N s | 𝓖 s] = 0`. This is the one-step fact behind the martingale
transform (`martingaleTransform_isMartingale`, over `ℕ`) and behind the zero mean of a
simple-strategy gain in continuous time. -/
theorem condExp_inner_sub_eq_zero (hN : Martingale N 𝓖 μ) (hst : s ≤ t)
    (hφ : StronglyMeasurable[𝓖 s] φ) (hK : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ K) :
    μ[fun ω ↦ ⟪φ ω, N t ω - N s ω⟫_ℝ | 𝓖 s] =ᵐ[μ] (0 : Ω → ℝ) := by
  have hcond0 : μ[fun ω ↦ N t ω - N s ω | 𝓖 s] =ᵐ[μ] 0 := by
    have hsub : μ[fun ω ↦ N t ω - N s ω | 𝓖 s] =ᵐ[μ] μ[N t | 𝓖 s] - μ[N s | 𝓖 s] :=
      condExp_sub (hN.integrable t) (hN.integrable s) _
    have h1 : μ[N t | 𝓖 s] =ᵐ[μ] N s := hN.2 s t hst
    have h2 : μ[N s | 𝓖 s] = N s :=
      condExp_of_stronglyMeasurable (𝓖.le s) (hN.1 s) (hN.integrable s)
    filter_upwards [hsub, h1] with ω hω h1ω
    rw [hω, Pi.zero_apply, Pi.sub_apply, h1ω, h2, sub_self]
  refine (condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hφ (integrable_inner_sub hN hφ hK)
    ((hN.integrable t).sub (hN.integrable s))).trans ?_
  filter_upwards [hcond0] with ω hω
  have hω' : (μ[fun ω ↦ N t ω - N s ω | 𝓖 s]) ω = 0 := hω
  simp [hω']

/-- **A bounded `𝓖 s`-measurable weight against a martingale increment has zero mean**:
`∫ ⟪φ, N t − N s⟫ dμ = 0` for `s ≤ t` (`condExp_inner_sub_eq_zero` and `integral_condExp`). -/
theorem integral_inner_sub_eq_zero (hN : Martingale N 𝓖 μ) (hst : s ≤ t)
    (hφ : StronglyMeasurable[𝓖 s] φ) (hK : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ K) :
    ∫ ω, ⟪φ ω, N t ω - N s ω⟫_ℝ ∂μ = 0 := by
  rw [← integral_condExp (𝓖.le s), integral_congr_ae (condExp_inner_sub_eq_zero hN hst hφ hK)]
  simp

end Increment

omit [CompleteSpace F] in
/-- Each summand `⟪A_{k+1}(ω), M_{k+1}(ω) − M_k(ω)⟫` is `𝓕 n`-measurable when `k < n`. -/
lemma stronglyMeasurable_inner_succ_sub
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (n k : ℕ) (hk : k < n) :
    StronglyMeasurable[𝓕 n] (fun ω ↦ ⟪A (k + 1) ω, M (k + 1) ω - M k ω⟫_ℝ) :=
  (hA.stronglyMeasurable_le hk.le).inner
    ((hM.stronglyAdapted.stronglyMeasurable_le (Nat.succ_le_of_lt hk)).sub
      (hM.stronglyAdapted.stronglyMeasurable_le hk.le))

omit [CompleteSpace F] in
/-- The martingale transform is adapted. -/
private lemma martingaleTransform_adapted
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1))) :
    StronglyAdapted 𝓕 (martingaleTransform A M) := fun n ↦
  Finset.stronglyMeasurable_fun_sum (m := 𝓕 n) (M := ℝ) (Finset.range n) fun k hk ↦
    stronglyMeasurable_inner_succ_sub hM hA n k (Finset.mem_range.mp hk)

/-- Each summand is integrable (bounded `A` paired with an integrable martingale increment). -/
lemma integrable_inner_succ_sub
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ᵐ ω ∂μ, ∀ n, ‖A n ω‖ ≤ K) (k : ℕ) :
    Integrable (fun ω ↦ ⟪A (k + 1) ω, M (k + 1) ω - M k ω⟫_ℝ) μ :=
  let ⟨_, hK⟩ := hA_bdd
  integrable_inner_sub hM (hA k) (hK.mono fun _ hω ↦ hω (k + 1))

/-- `(A · M)_n` is integrable. -/
private lemma integrable_martingaleTransform
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ᵐ ω ∂μ, ∀ n, ‖A n ω‖ ≤ K) (n : ℕ) :
    Integrable (martingaleTransform A M n) μ :=
  integrable_finsetSum _ fun k _ ↦ integrable_inner_succ_sub hM hA hA_bdd k

variable [IsFiniteMeasure μ]

/-- The martingale-transform increment has vanishing conditional expectation:
`μ[(A · M)_{n+1} − (A · M)_n | 𝓕 n] =ᵐ 0`. This is the single fact the
`martingale_of_condExp_sub_eq_zero_nat` characterisation needs. -/
private lemma martingaleTransform_condExp_increment
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ᵐ ω ∂μ, ∀ n, ‖A n ω‖ ≤ K) (n : ℕ) :
    μ[martingaleTransform A M (n + 1) - martingaleTransform A M n | 𝓕 n] =ᵐ[μ]
      (0 : Ω → ℝ) := by
  rw [show martingaleTransform A M (n + 1) - martingaleTransform A M n =
      fun ω ↦ ⟪A (n + 1) ω, M (n + 1) ω - M n ω⟫_ℝ by
    rw [martingaleTransform_succ, add_sub_cancel_left]]
  obtain ⟨_, hK⟩ := hA_bdd
  exact condExp_inner_sub_eq_zero hM n.le_succ (hA n) (hK.mono fun _ hω ↦ hω (n + 1))

/-- Theorem 2.2.9: the martingale transform of a martingale `M` by a bounded
predictable process `A` is itself a martingale. -/
theorem martingaleTransform_isMartingale
    (hM : Martingale M 𝓕 μ) (hA : StronglyAdapted 𝓕 (fun n ↦ A (n + 1)))
    (hA_bdd : ∃ K : ℝ, ∀ᵐ ω ∂μ, ∀ n, ‖A n ω‖ ≤ K) :
    Martingale (martingaleTransform A M) 𝓕 μ :=
  martingale_of_condExp_sub_eq_zero_nat (martingaleTransform_adapted hM hA)
    (integrable_martingaleTransform hM hA hA_bdd)
    (martingaleTransform_condExp_increment hM hA hA_bdd)

end MathFin

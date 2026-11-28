/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivatives
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkin
public import LeanPool.FunctionSpaces.Analysis.Maximal.DyadicGrid
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Mathlib's Sobolev spaces `H^s(V)` by Littlewood–Paley blocks

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure.
Mathlib's Sobolev space `H^s(V)` consists of the tempered distributions `u` whose Bessel potential
`J_s u = 𝓕⁻¹(⟨ξ⟩^s 𝓕u)`, `⟨ξ⟩^s = (1 + ‖ξ‖²)^(s/2)` (`Rd.besselWeight`), is an `L_2` function
(`TemperedDistribution.MemSobolev s 2`). For `s ≥ 0` this file identifies `H^s(V)` with the
Triebel–Lizorkin space `F^s_{2,2}(V)`, and for `s > 0` with the Besov space `B^s_{2,2}(V)`, with
explicit constants, and proves `W^1_2(V) = H^1(V) = B^1_{2,2}(V)`.

* **Plancherel for the blocks**: `𝓕(K ⋆ f) = 𝓕K · 𝓕f` for an integrable `K` and `f ∈ L_2(V)`
  (`Rd.fourier_convLp`), so `‖K ⋆ f‖_2² = ∫ |𝓕K|² |𝓕f|²` (`Rd.enorm_convLp_sq`), in particular
  `‖ψ_j ⋆ f‖_2² = ∫ |𝓕ψ_j|² |𝓕f|²` (`Rd.enorm_lpBlock_sq`).
* **The Bessel potential on Schwartz functions**: `J_t u = 𝓕⁻(⟨ξ⟩^t 𝓕u)` (`Rd.besselSchwartz`)
  is Mathlib's `J_t` on the tempered distribution of `u` (`Rd.besselPotential_schwartz`), with
  inverse `J_{-t}` (`Rd.besselSchwartz_besselSchwartz_neg`).
  Mathlib's Fourier multiplier `m(D)` of a temperate symbol `m` multiplies the Fourier transform
  of a Schwartz function by `m` (`Rd.fourier_fourierMultiplierCLM_apply`); for even `m` it acts
  on tempered distributions by
  the transpose, `(m(D) T)(u) = T(m(D) u)` (`Rd.fourierMultiplierCLM_apply_apply_of_even`); for
  the even Bessel weight this is `(J_t T)(u) = T(J_t u)` (`Rd.besselPotential_apply_apply`), so
  `J_t` is symmetric on Schwartz functions (`Rd.integral_besselSchwartz_mul`).
* **The weight comparison**: at every frequency at most two blocks are nonzero, and their
  Fourier transforms add up to `1` (`Rd.exists_fourier_psi_window`, in
  `FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels`); hence, for `s ≥ 0`,
  `∑_j 2^{2js} |𝓕ψ_j(ξ)|² ≤ 2 · 4^s ⟨ξ⟩^{2s}` and `⟨ξ⟩^{2s} ≤ 2 · 5^s ∑_j 2^{2js} |𝓕ψ_j(ξ)|²`
  (`Rd.tsum_dyadicWeight_fourier_psi_sq_le`, `Rd.ofReal_besselWeight_sq_le_tsum`).
* **`H^s = F^s_{2,2}`** (`Rd.memSobolev_two_iff_memTriebelLizorkin`): if `J_s f = h` with
  `f, h ∈ L_2(V)`, then `‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖h‖_2` and
  `‖h‖_2 ≤ (2 · 5^s)^{1/2} ‖f‖_{F^s_{2,2}}`; the Besov form
  (`Rd.memSobolev_two_iff_exists_memApprox`) and the bundled space `H^{s}(V)`
  (`Rd.exists_eq_toDistr_two`) follow.
* **`W^1_2 = H^1`** (`Rd.memSobolev_one_iff`), with `‖∂_v f‖_2 ≤ 2π ‖v‖ ‖J_1 f‖_2` and
  `(2π)² ‖J_1 f‖_2² = (2π)² ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²` for an orthonormal basis `(e_i)`
  (`Rd.sq_norm_besselPotential_one_eq`), hence
  `‖J_1 f‖_2² ≤ ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²` (`Rd.sq_norm_besselPotential_one_le`).
* **`W^1_2 = B^1_{2,2}`** (`Rd.memSobolev_one_iff_memApprox`, `Rd.memSobolev_one_iff_modulus`):
  `F ∈ W^1_2(V)` iff `‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2} < ∞`, for every order `r ≥ 2`.

Two facts about tempered distributions carry the proofs: the product of a temperate weight `w`
with the distribution of an `L_p` function `g` is the distribution of `w g` when `w g` lies in
`L_q` (`Rd.smulLeftCLM_toTemperedDistribution_eq`), and an identity `w g = h` of distributions,
with `g` and `h` in `L_p` spaces, holds almost everywhere (`Rd.ae_eq_of_smulLeftCLM_eq`). An
`L_p` function is determined by its tempered distribution (`Rd.eq_of_toTemperedDistribution_eq`),
almost everywhere equal `L_p` and `L_r` classes have the same tempered distribution
(`Rd.toTemperedDistribution_eq_of_ae_eq`), and the norm of Mathlib's `H^{s,p}` is the `L_p` norm
of `J_s U`, also in `ℝ≥0∞` (`BesselPotentialSpace.enorm_toLp_eq`).
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal SchwartzMap FourierTransform LineDeriv Real BesselPotentialSpace
open TemperedDistribution (besselPotential)

namespace BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [NormedSpace ℂ F]
  {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- `‖J_s U‖_p = ‖U‖` in `ℝ≥0∞`, for `U ∈ H^{s,p}(E, F)`: the norm of the Bessel potential space
is the norm of the `L_p` function `J_s U` (Mathlib's `BesselPotentialSpace.norm_toLp_eq`). -/
theorem enorm_toLp_eq (U : H^{s, p}(E, F)) : ‖U.toLp‖ₑ = ‖U‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_toLp_eq]

end BesselPotentialSpace

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Fourier transform of convolutions on `L_2` -/

/-- `2 ≠ ∞` in `ℝ≥0∞` (Mathlib's `ENNReal.ofNat_ne_top` at `2`): the hypothesis `p ≠ ∞` of the
blocks and the band-limited scheme on `L_2`. Its type fixes `p = 2` before the remaining
arguments are elaborated. -/
theorem two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top

/-- `L_p` functions are determined by their tempered distributions (Mathlib's
`Lp.ker_toTemperedDistributionCLM_eq_bot`). -/
theorem eq_of_toTemperedDistribution_eq {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g : Lp ℂ p (volume : Measure V)} (h : (f : 𝓢'(V, ℂ)) = g) : f = g :=
  LinearMap.ker_eq_bot.1 (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
    (μ := (volume : Measure V)) (p := p)) h

/-- **Almost everywhere equal classes are the same tempered distribution**: if `f ∈ L_p(V)` and
`g ∈ L_r(V)`, `1 ≤ p, r ≤ ∞`, have almost everywhere equal representatives, then
`∫ u g = ∫ u f` for every Schwartz function `u` (Mathlib's
`MeasureTheory.Lp.toTemperedDistribution_apply`, `MeasureTheory.integral_congr_ae`). -/
theorem toTemperedDistribution_eq_of_ae_eq {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    {f : Lp ℂ p (volume : Measure V)} {g : Lp ℂ r (volume : Measure V)}
    (h : (g : V → ℂ) =ᵐ[volume] f) : (g : 𝓢'(V, ℂ)) = (f : 𝓢'(V, ℂ)) := by
  ext u
  simp only [Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- **`𝓕(K ⋆ φ) = 𝓕K · 𝓕φ` for Schwartz functions `φ`**, as an identity in `L_2(V)`: the `L_2`
Fourier transform of `K ⋆ φ` is the product of the bounded function `𝓕K` with the `L_2` Fourier
transform of `φ`, for every integrable `K`. Both sides are tested against Schwartz functions
(`Rd.eq_of_toTemperedDistribution_eq`): `K ⋆ φ` is integrable, so the duality
for `𝓕` (the multiplication formula) and the pointwise convolution theorem `Rd.fourier_conv`
apply. -/
theorem fourier_convLp_toLp {K : V → ℂ} (hK : Integrable K) (φ : 𝓢(V, ℂ)) :
    𝓕 (convLp two_ne_top hK (φ.toLp 2 (volume : Measure V))) =
      (ContinuousLinearMap.mul ℂ ℂ).holder 2 ((memLp_top_fourier hK).toLp _)
        (𝓕 (φ.toLp 2 (volume : Measure V))) := by
  apply eq_of_toTemperedDistribution_eq
  ext u
  simp only [← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  have hc : Integrable (conv K φ volume) := integrable_conv hK φ.integrable
  have hF : ((𝓕 (φ.toLp 2 (volume : Measure V)) : Lp ℂ 2 (volume : Measure V)) : V → ℂ)
      =ᵐ[volume] 𝓕 (φ : V → ℂ) := by
    rw [SchwartzMap.toLp_fourier_eq, ← SchwartzMap.fourier_coe]
    exact (𝓕 φ).coeFn_toLp 2 volume
  calc ∫ x, 𝓕 u x • (convLp two_ne_top hK (φ.toLp 2 (volume : Measure V)) : V → ℂ) x
      = ∫ x, 𝓕 u x • conv K φ volume x := by
        refine integral_congr_ae ?_
        filter_upwards [convLp_apply_ae two_ne_top hK (φ.toLp 2 volume)] with x hx
        rw [hx, conv_congr_ae (φ.coeFn_toLp 2 volume)]
    _ = ∫ x, u x • 𝓕 (conv K φ volume) x := integral_fourier_smul_eq_of_integrable u hc
    _ = ∫ x, u x • (𝓕 K x * 𝓕 (φ : V → ℂ) x) := by
        congr 1
        ext x
        rw [fourier_conv hK φ.integrable x]
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [ContinuousLinearMap.coeFn_holder (r := 2) (ContinuousLinearMap.mul ℂ ℂ)
          ((memLp_top_fourier hK).toLp _) (𝓕 (φ.toLp 2 (volume : Measure V))),
          (memLp_top_fourier hK).coeFn_toLp, hF] with x h1 h2 h3
        rw [h1, ContinuousLinearMap.mul_apply', h2, h3]

/-- **The convolution theorem on `L_2`**: for every integrable `K` and every `f ∈ L_2(V)`,
`𝓕(K ⋆ f) = 𝓕K · 𝓕f` almost everywhere, where `𝓕` on `L_2` is Plancherel's Fourier transform.
Both sides are continuous in `f` (Young's inequality, and multiplication by the bounded `𝓕K`), and
they agree on the dense set of Schwartz functions (`Rd.fourier_convLp_toLp`). The Fourier
transform on `L_2(V)` is continuous by Mathlib's `FourierTransform.continuous_fourier`. -/
theorem fourier_convLp {K : V → ℂ} (hK : Integrable K) (f : Lp ℂ 2 (volume : Measure V)) :
    ((𝓕 (convLp two_ne_top hK f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 K ξ * (𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ := by
  set a : Lp ℂ ∞ (volume : Measure V) := (memLp_top_fourier hK).toLp _
  have hF : Continuous (𝓕 : Lp ℂ 2 (volume : Measure V) → Lp ℂ 2 (volume : Measure V)) :=
    FourierTransform.continuous_fourier
  have key : 𝓕 (convLp two_ne_top hK f) =
      (ContinuousLinearMap.mul ℂ ℂ).holder 2 a (𝓕 f) := by
    refine DenseRange.induction_on (p := fun f : Lp ℂ 2 (volume : Measure V) =>
      𝓕 (convLp two_ne_top hK f) = (ContinuousLinearMap.mul ℂ ℂ).holder 2 a (𝓕 f))
      (SchwartzMap.denseRange_toLpCLM (p := 2) two_ne_top) f ?_ ?_
    · exact isClosed_eq (hF.comp (convLp two_ne_top hK).continuous)
        ((((ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2) a).continuous.comp hF)
    · intro φ
      exact fourier_convLp_toLp hK φ
  rw [key]
  filter_upwards [ContinuousLinearMap.coeFn_holder (r := 2) (ContinuousLinearMap.mul ℂ ℂ) a
    (𝓕 f), (memLp_top_fourier hK).coeFn_toLp] with x h1 h2
  rw [h1, ContinuousLinearMap.mul_apply', h2]

/-- **The Fourier transform of a block**: for `f ∈ L_2(V)`, `𝓕(Δ_j f) = 𝓕ψ_j · 𝓕f` almost
everywhere. -/
theorem fourier_lpBlock (f : Lp ℂ 2 (volume : Measure V)) (j : ℕ) :
    ((𝓕 (lpBlock two_ne_top j f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 (psi (V := V) j) ξ * (𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ :=
  fourier_convLp (integrable_psi j) f

/-- **Plancherel's theorem** in `ℝ≥0∞`: `‖𝓕F‖_2 = ‖F‖_2` for `F ∈ L_2(V)` (Mathlib's
`Lp.norm_fourier_eq`). -/
theorem enorm_fourier_Lp_two (F : Lp ℂ 2 (volume : Measure V)) :
    ‖(𝓕 F : Lp ℂ 2 (volume : Measure V))‖ₑ = ‖F‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Lp.norm_fourier_eq]

/-- The square of the `L_2` norm is an integral: `‖F‖_2² = ∫ |F|²`, on every measure space. -/
theorem enorm_sq_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : Lp ℂ 2 μ) : ‖F‖ₑ ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
  have h := eLpNorm_rpow_eq (Lp.aestronglyMeasurable F) two_ne_zero two_ne_top
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  rw [Lp.eNorm_def, h]

/-- **The `L_2` norm of a function through its class**: for a function `f` with
`∫ |f|² < ∞` (`MemLp f 2 μ`), `∫ |f|² = ‖[f]‖_2²` for the class `[f] = hf.toLp f` of `f` in
`L_2(μ)`, on every measure space (`Rd.enorm_sq_eq_lintegral` and `[f] = f` almost everywhere). -/
theorem lintegral_enorm_sq_eq_enorm_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ‖hf.toLp f‖ₑ ^ 2 := by
  rw [enorm_sq_eq_lintegral]
  exact lintegral_congr_ae (hf.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])

/-- **Plancherel for a convolution**: for integrable `K` and `f ∈ L_2(V)`,
`‖K ⋆ f‖_2² = ∫ |𝓕K(ξ)|² |𝓕f(ξ)|² dξ`, where `𝓕f` is the `L_2` Fourier transform
(`Rd.fourier_convLp` and Plancherel's theorem `Rd.enorm_fourier_Lp_two`). -/
theorem enorm_convLp_sq {K : V → ℂ} (hK : Integrable K) (f : Lp ℂ 2 (volume : Measure V)) :
    ‖convLp two_ne_top hK f‖ₑ ^ 2 =
      ∫⁻ ξ, ‖𝓕 K ξ‖ₑ ^ 2 * ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
  rw [← enorm_fourier_Lp_two, enorm_sq_eq_lintegral]
  refine lintegral_congr_ae ?_
  filter_upwards [fourier_convLp hK f] with ξ hξ
  rw [hξ, eNorm_mul, mul_pow]

/-- **Plancherel for a block**: for `f ∈ L_2(V)`,
`‖Δ_j f‖_2² = ∫ |𝓕ψ_j(ξ)|² |𝓕f(ξ)|² dξ`, the case `K = ψ_j` of `Rd.enorm_convLp_sq`. -/
theorem enorm_lpBlock_sq (f : Lp ℂ 2 (volume : Measure V)) (j : ℕ) :
    ‖lpBlock two_ne_top j f‖ₑ ^ 2 =
      ∫⁻ ξ, ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 * ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 :=
  enorm_convLp_sq (integrable_psi j) f

/-! ### The Bessel weight and the Littlewood–Paley weights -/

/-- The **Bessel weight** `⟨ξ⟩^s = (1 + ‖ξ‖²)^(s/2)`, the symbol of Mathlib's Bessel potential
`J_s = TemperedDistribution.besselPotential V ℂ s`. -/
noncomputable def besselWeight (s : ℝ) (ξ : V) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (s / 2)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Bessel weight is nonnegative. -/
theorem besselWeight_nonneg (s : ℝ) (ξ : V) : 0 ≤ besselWeight s ξ :=
  Real.rpow_nonneg (by positivity) _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Bessel weight is even: `⟨-ξ⟩^s = ⟨ξ⟩^s`. -/
theorem besselWeight_neg (s : ℝ) (ξ : V) : besselWeight s (-ξ) = besselWeight s ξ := by
  rw [besselWeight, besselWeight, norm_neg]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Bessel weight is smooth with polynomially bounded derivatives, so it multiplies tempered
distributions. -/
theorem hasTemperateGrowth_besselWeight (s : ℝ) :
    (fun ξ : V => (besselWeight s ξ : ℂ)).HasTemperateGrowth := by
  unfold besselWeight
  fun_prop

/-- **The Bessel potential on Schwartz functions**: `J_t u = 𝓕⁻(⟨ξ⟩^t 𝓕u)` with the weight
`⟨ξ⟩^t = (1 + ‖ξ‖²)^{t/2}` (`Rd.besselWeight`), a continuous linear map of the Schwartz space
(Mathlib's `SchwartzMap.fourierMultiplierCLM`). -/
noncomputable def besselSchwartz (t : ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ fun ξ => (besselWeight t ξ : ℂ)

/-- The Bessel potential `J_t` of Mathlib's tempered distributions restricts to `J_t` on Schwartz
functions (Mathlib's `TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq`). -/
theorem besselPotential_schwartz (t : ℝ) (u : 𝓢(V, ℂ)) :
    besselPotential V ℂ t (u : 𝓢'(V, ℂ)) = (besselSchwartz t u : 𝓢'(V, ℂ)) :=
  TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (hasTemperateGrowth_besselWeight t) u

/-- **`J_{-t}` inverts `J_t` on Schwartz functions**: `J_t (J_{-t} u) = u`, since the product of
the Bessel weights is `⟨ξ⟩^t ⟨ξ⟩^{-t} = 1` (Mathlib's
`SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply` and
`SchwartzMap.fourierMultiplierCLM_const`). -/
theorem besselSchwartz_besselSchwartz_neg (t : ℝ) (u : 𝓢(V, ℂ)) :
    besselSchwartz t (besselSchwartz (-t) u) = u := by
  rw [besselSchwartz, besselSchwartz, SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_besselWeight t) (hasTemperateGrowth_besselWeight (-t))]
  have h : ((fun ξ : V => (besselWeight t ξ : ℂ)) * fun ξ => (besselWeight (-t) ξ : ℂ)) =
      fun _ => (1 : ℂ) := funext fun ξ => by
    have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
    rw [Pi.mul_apply, besselWeight, besselWeight, ← Complex.ofReal_mul, ← Real.rpow_add hpos,
      show t / 2 + -t / 2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one]
  rw [h, SchwartzMap.fourierMultiplierCLM_const, one_smul]
  rfl

/-- `J_t u(x) = 𝓕⁻(⟨ξ⟩^t 𝓕u)(x)`, with the Fourier integrals of functions. -/
theorem besselSchwartz_apply (t : ℝ) (u : 𝓢(V, ℂ)) (x : V) :
    besselSchwartz t u x = 𝓕⁻ (fun ξ => (besselWeight t ξ : ℂ) * 𝓕 (u : V → ℂ) ξ) x := by
  rw [besselSchwartz, SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe,
    SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_besselWeight t), SchwartzMap.fourier_coe]
  rfl

/-- **Fourier multipliers multiply the Fourier transform**: `𝓕(m(D) u)(ξ) = m(ξ) 𝓕u(ξ)` for a
symbol `m` of temperate growth and a Schwartz function `u` (Fourier inversion on Schwartz
functions). -/
theorem fourier_fourierMultiplierCLM_apply {m : V → ℂ} (hm : m.HasTemperateGrowth)
    (u : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (SchwartzMap.fourierMultiplierCLM ℂ m u) ξ = m ξ * 𝓕 u ξ := by
  rw [SchwartzMap.fourierMultiplierCLM_apply, FourierInvPair.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply hm, smul_eq_mul]

/-- **The transpose form of an even Fourier multiplier**: for an even symbol `m` of temperate
growth, `m(-ξ) = m(ξ)`, Mathlib's Fourier multiplier `m(D) u = 𝓕⁻(m 𝓕u)` on Schwartz functions
is also `m(D) u(x) = 𝓕(m 𝓕⁻u)(x)`, since `𝓕⁻ h(x) = 𝓕 h(-x)` (Mathlib's
`Real.fourierInv_eq_fourier_comp_neg`, `Real.fourierInv_eq_fourier_neg`). -/
theorem fourierMultiplierCLM_apply_eq_fourier {m : V → ℂ} (hm : m.HasTemperateGrowth)
    (heven : ∀ ξ, m (-ξ) = m ξ) (u : 𝓢(V, ℂ)) (x : V) :
    SchwartzMap.fourierMultiplierCLM ℂ m u x = 𝓕 (fun ξ => m ξ * 𝓕⁻ (u : V → ℂ) ξ) x := by
  rw [SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe,
    SchwartzMap.smulLeftCLM_apply hm, SchwartzMap.fourier_coe,
    Real.fourierInv_eq_fourier_comp_neg]
  refine congrFun (congrArg _ (funext fun ξ => ?_)) x
  rw [smul_eq_mul, heven, Real.fourierInv_eq_fourier_neg]

/-- **Even Fourier multipliers act by the transpose**: for an even symbol `m` of temperate growth,
every tempered distribution `T` and every Schwartz function `u`, `(m(D) T)(u) = T(m(D) u)`.
Mathlib defines `(m(D) T)(u) = T(𝓕(m 𝓕⁻u))`, and `𝓕(m 𝓕⁻u) = m(D) u`
(`Rd.fourierMultiplierCLM_apply_eq_fourier`). -/
theorem fourierMultiplierCLM_apply_apply_of_even {m : V → ℂ} (hm : m.HasTemperateGrowth)
    (heven : ∀ ξ, m (-ξ) = m ξ) (T : 𝓢'(V, ℂ)) (u : 𝓢(V, ℂ)) :
    TemperedDistribution.fourierMultiplierCLM ℂ m T u =
      T (SchwartzMap.fourierMultiplierCLM ℂ m u) := by
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply]
  congr 1
  ext x
  rw [fourierMultiplierCLM_apply_eq_fourier hm heven, SchwartzMap.fourier_coe,
    SchwartzMap.smulLeftCLM_apply hm, SchwartzMap.fourierInv_coe]
  rfl

/-- **The transpose form of `J_t`**: `J_t u(x) = 𝓕(⟨ξ⟩^t 𝓕⁻u)(x)`, since the Bessel weight is
even (`Rd.besselWeight_neg`, `Rd.fourierMultiplierCLM_apply_eq_fourier`). -/
theorem besselSchwartz_apply_eq_fourier (t : ℝ) (u : 𝓢(V, ℂ)) (x : V) :
    besselSchwartz t u x = 𝓕 (fun ξ => (besselWeight t ξ : ℂ) * 𝓕⁻ (u : V → ℂ) ξ) x :=
  fourierMultiplierCLM_apply_eq_fourier (hasTemperateGrowth_besselWeight t)
    (fun ξ => by rw [besselWeight_neg]) u x

/-- **Mathlib's Bessel potential acts by the transpose**: for every tempered distribution `T`
and every Schwartz function `u`, `(J_t T)(u) = T(J_t u)`, since the Bessel weight is even
(`Rd.besselWeight_neg`, `Rd.fourierMultiplierCLM_apply_apply_of_even`). -/
theorem besselPotential_apply_apply (t : ℝ) (T : 𝓢'(V, ℂ)) (u : 𝓢(V, ℂ)) :
    besselPotential V ℂ t T u = T (besselSchwartz t u) :=
  fourierMultiplierCLM_apply_apply_of_even (hasTemperateGrowth_besselWeight t)
    (fun ξ => by rw [besselWeight_neg]) T u

/-- **`J_t` is symmetric on Schwartz functions**: `∫ J_t φ · u = ∫ φ · J_t u` for Schwartz
functions `φ`, `u`. Both sides are `(J_t φ)(u)` for the tempered distribution of `φ`
(`Rd.besselPotential_apply_apply`, `Rd.besselPotential_schwartz`). -/
theorem integral_besselSchwartz_mul (t : ℝ) (φ u : 𝓢(V, ℂ)) :
    ∫ x, besselSchwartz t φ x * u x = ∫ x, φ x * besselSchwartz t u x := by
  have h := besselPotential_apply_apply t (φ : 𝓢'(V, ℂ)) u
  rw [besselPotential_schwartz, SchwartzMap.coe_apply, SchwartzMap.coe_apply] at h
  simp only [smul_eq_mul] at h
  calc ∫ x, besselSchwartz t φ x * u x = ∫ x, u x * besselSchwartz t φ x := by
        congr 1
        funext x
        ring
    _ = ∫ x, besselSchwartz t u x * φ x := h
    _ = ∫ x, φ x * besselSchwartz t u x := by
        congr 1
        funext x
        ring

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Bessel weight as a complex number has absolute value `⟨ξ⟩^s`. -/
theorem enorm_besselWeight (s : ℝ) (ξ : V) :
    ‖(besselWeight s ξ : ℂ)‖ₑ = ENNReal.ofReal (besselWeight s ξ) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (besselWeight_nonneg s ξ)]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `(⟨ξ⟩^s)² = (1 + ‖ξ‖²)^s`. -/
theorem ofReal_besselWeight_sq (s : ℝ) (ξ : V) :
    ENNReal.ofReal (besselWeight s ξ) ^ 2 = ENNReal.ofReal (1 + ‖ξ‖ ^ 2) ^ s := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_pow (besselWeight_nonneg s ξ),
    besselWeight, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  ring

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `‖ξ‖ ≤ ⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. -/
theorem norm_le_besselWeight_one (ξ : V) : ‖ξ‖ ≤ besselWeight 1 ξ := by
  rw [besselWeight, ← Real.sqrt_eq_rpow, Real.le_sqrt (norm_nonneg ξ) (by positivity)]
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- If `‖ξ‖ < 2^(j+1)`, then `1 + ‖ξ‖² ≤ 5 · 4^j`. -/
theorem one_add_norm_sq_le_of_norm_lt {j : ℕ} {ξ : V} (h : ‖ξ‖ < 2 ^ (j + 1)) :
    1 + ‖ξ‖ ^ 2 ≤ 5 * (4 : ℝ) ^ j := by
  have h4 : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * (4 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
    ring
  have h1 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  nlinarith [norm_nonneg ξ]

/-- **Upper weight bound**: for `s ≥ 0`, if `𝓕ψ_j(ξ) ≠ 0`, then
`2^(2js) ≤ 4^s ⟨ξ⟩^{2s}`. -/
theorem dyadicWeight_sq_le_of_fourier_psi_ne_zero {s : ℝ} (hs : 0 ≤ s) {j : ℕ} {ξ : V}
    (h : 𝓕 (psi (V := V) j) ξ ≠ 0) :
    dyadicWeight s j ^ 2 ≤ 4 ^ s * ENNReal.ofReal (besselWeight s ξ) ^ 2 := by
  rw [ENNReal.dyadicWeight_sq, ofReal_besselWeight_sq, ← ENNReal.mul_rpow_of_nonneg _ _ hs]
  refine ENNReal.rpow_le_rpow ?_ hs
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (four_pow_le_of_fourier_psi_ne_zero h)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Lower weight bound**: for `s ≥ 0`, if `‖ξ‖ < 2^(j+1)`, then
`⟨ξ⟩^{2s} ≤ 5^s 2^(2js)`. -/
theorem ofReal_besselWeight_sq_le_of_norm_lt {s : ℝ} (hs : 0 ≤ s) {j : ℕ} {ξ : V}
    (h : ‖ξ‖ < 2 ^ (j + 1)) :
    ENNReal.ofReal (besselWeight s ξ) ^ 2 ≤ 5 ^ s * dyadicWeight s j ^ 2 := by
  rw [ENNReal.dyadicWeight_sq, ofReal_besselWeight_sq, ← ENNReal.mul_rpow_of_nonneg _ _ hs]
  refine ENNReal.rpow_le_rpow ?_ hs
  rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num,
    show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (one_add_norm_sq_le_of_norm_lt h)

/-- **The Littlewood–Paley symbol is at most the Bessel weight**: for `s ≥ 0` and every `ξ ∈ V`,
`∑_j 2^(2js) |𝓕ψ_j(ξ)|² ≤ 2 · 4^s ⟨ξ⟩^{2s}`. At most two terms are nonzero
(`Rd.exists_fourier_psi_window`), each at most `4^s ⟨ξ⟩^{2s}`. -/
theorem tsum_dyadicWeight_fourier_psi_sq_le {s : ℝ} (hs : 0 ≤ s) (ξ : V) :
    ∑' j, dyadicWeight s j ^ 2 * ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 ≤
      2 * 4 ^ s * ENNReal.ofReal (besselWeight s ξ) ^ 2 := by
  obtain ⟨a, -, hwin, -⟩ := exists_fourier_psi_window ξ
  have hterm : ∀ j, dyadicWeight s j ^ 2 * ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 ≤
      4 ^ s * ENNReal.ofReal (besselWeight s ξ) ^ 2 := by
    intro j
    by_cases h : 𝓕 (psi (V := V) j) ξ = 0
    · simp [h]
    · calc _ ≤ (4 ^ s * ENNReal.ofReal (besselWeight s ξ) ^ 2) * 1 := by
            gcongr
            · exact dyadicWeight_sq_le_of_fourier_psi_ne_zero hs h
            · exact pow_le_one₀ (by positivity) (enorm_fourier_psi_le_one j ξ)
        _ = _ := mul_one _
  rw [tsum_eq_sum (s := {a, a + 1}) (fun j hj => ?_), Finset.sum_pair (by omega)]
  · calc _ ≤ 4 ^ s * ENNReal.ofReal (besselWeight s ξ) ^ 2 +
          4 ^ s * ENNReal.ofReal (besselWeight s ξ) ^ 2 := add_le_add (hterm a) (hterm (a + 1))
      _ = _ := by ring
  · have : 𝓕 (psi (V := V) j) ξ = 0 := by
      by_contra h
      rcases hwin j h with rfl | rfl <;> simp at hj
    simp [this]

/-- Two complex numbers with `x + y = 1` satisfy `1 ≤ 2(|x|² + |y|²)`: `1 ≤ |x| + |y|` by the
triangle inequality, and `(a + b)² ≤ 2(a² + b²)` (Mathlib's `add_sq_le`). -/
theorem one_le_two_mul_enorm_sq_add {x y : ℂ} (h : x + y = 1) :
    1 ≤ 2 * (‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2) := by
  have h1 : 1 ≤ ‖x‖ + ‖y‖ := by simpa [h] using norm_add_le x y
  have h2 : (1 : ℝ) ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := (one_le_pow₀ h1).trans add_sq_le
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h2

/-- **The Bessel weight is at most the Littlewood–Paley symbol**: for `s ≥ 0` and every `ξ ∈ V`,
`⟨ξ⟩^{2s} ≤ 2 · 5^s ∑_j 2^(2js) |𝓕ψ_j(ξ)|²`. The two blocks `a`, `a + 1` of
`Rd.exists_fourier_psi_window` have `|𝓕ψ_a(ξ)|² + |𝓕ψ_{a+1}(ξ)|² ≥ 1/2`, and
`⟨ξ⟩^{2s} ≤ 5^s 2^(2js)` for both. -/
theorem ofReal_besselWeight_sq_le_tsum {s : ℝ} (hs : 0 ≤ s) (ξ : V) :
    ENNReal.ofReal (besselWeight s ξ) ^ 2 ≤
      2 * 5 ^ s * ∑' j, dyadicWeight s j ^ 2 * ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 := by
  obtain ⟨a, ha, -, hsum⟩ := exists_fourier_psi_window ξ
  have h1 := ofReal_besselWeight_sq_le_of_norm_lt hs (j := a) ha
  have h2 := ofReal_besselWeight_sq_le_of_norm_lt hs (j := a + 1)
    (ha.trans (pow_lt_pow_right₀ one_lt_two (by omega)))
  calc ENNReal.ofReal (besselWeight s ξ) ^ 2
      ≤ ENNReal.ofReal (besselWeight s ξ) ^ 2 *
          (2 * (‖𝓕 (psi (V := V) a) ξ‖ₑ ^ 2 + ‖𝓕 (psi (V := V) (a + 1)) ξ‖ₑ ^ 2)) :=
        le_mul_of_one_le_right' (one_le_two_mul_enorm_sq_add hsum)
    _ = 2 * (ENNReal.ofReal (besselWeight s ξ) ^ 2 * ‖𝓕 (psi (V := V) a) ξ‖ₑ ^ 2 +
          ENNReal.ofReal (besselWeight s ξ) ^ 2 * ‖𝓕 (psi (V := V) (a + 1)) ξ‖ₑ ^ 2) := by ring
    _ ≤ 2 * (5 ^ s * dyadicWeight s a ^ 2 * ‖𝓕 (psi (V := V) a) ξ‖ₑ ^ 2 +
          5 ^ s * dyadicWeight s (a + 1) ^ 2 * ‖𝓕 (psi (V := V) (a + 1)) ξ‖ₑ ^ 2) := by
        gcongr
    _ = 2 * 5 ^ s * ∑ j ∈ {a, a + 1}, dyadicWeight s j ^ 2 * ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 := by
        rw [Finset.sum_pair (by omega)]
        ring
    _ ≤ _ := by
        gcongr
        exact sum_le_tsum _

/-! ### Temperate weights and Bessel potentials of `L_2` functions -/

/-- **Multiplying an `L_p` function by a temperate weight**: if `w` has temperate growth,
`g ∈ L_p(V)` and `w g ∈ L_q(V)`, `1 ≤ p, q ≤ ∞`, then the product of `w` with the tempered
distribution of `g` is the tempered distribution of `w g`. -/
theorem smulLeftCLM_toTemperedDistribution_eq {w : V → ℂ} (hw : w.HasTemperateGrowth)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (g : Lp ℂ p (volume : Measure V))
    (hg : MemLp (fun ξ => w ξ * g ξ) q volume) :
    TemperedDistribution.smulLeftCLM ℂ w (g : 𝓢'(V, ℂ)) =
      ((hg.toLp _ : Lp ℂ q (volume : Measure V)) : 𝓢'(V, ℂ)) := by
  ext u
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply_apply hw]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Identities between weighted `L_p` functions hold almost everywhere**: if `w` has temperate
growth, `G ∈ L_p(V)`, `H ∈ L_q(V)`, `1 ≤ p, q ≤ ∞`, and `w G = H` as tempered distributions,
then `w G = H` almost everywhere. Both sides are locally integrable and have the same integrals
against smooth compactly supported functions (Mathlib's `ae_eq_of_integral_contDiff_smul_eq`). -/
theorem ae_eq_of_smulLeftCLM_eq {w : V → ℂ} (hw : w.HasTemperateGrowth)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {G : Lp ℂ p (volume : Measure V)}
    {H : Lp ℂ q (volume : Measure V)}
    (h : TemperedDistribution.smulLeftCLM ℂ w (G : 𝓢'(V, ℂ)) = (H : 𝓢'(V, ℂ))) :
    (fun x => w x * G x) =ᵐ[volume] H := by
  refine ae_eq_of_integral_contDiff_smul_eq
    (((Lp.memLp G).locallyIntegrable Fact.out).continuous_mul hw.1.continuous)
    ((Lp.memLp H).locallyIntegrable Fact.out) fun φ hφ hφc => ?_
  have hφ₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hφ₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ φ) := by fun_prop
  have := DFunLike.congr_fun h (hφ₁.toSchwartzMap hφ₂)
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply_apply hw] at this
  convert this using 2 with x x
  · ext x
    simp [Complex.real_smul]
    ring
  · simp [Complex.real_smul]

/-- **The Bessel potential on the Fourier side**: if `J_s f = h` with `f, h ∈ L_2(V)`, then
`𝓕h = ⟨ξ⟩^s 𝓕f` almost everywhere. -/
theorem fourier_ae_eq_of_besselPotential_eq {s : ℝ} {f h : Lp ℂ 2 (volume : Measure V)}
    (hfh : besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    (fun ξ => (besselWeight s ξ : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ) =ᵐ[volume]
      (𝓕 h : Lp ℂ 2 (volume : Measure V)) := by
  refine ae_eq_of_smulLeftCLM_eq (hasTemperateGrowth_besselWeight s) ?_
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq, ← hfh,
    TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
  rfl

/-- **Plancherel for the Bessel potential**: if `J_s f = h` with `f, h ∈ L_2(V)`, then
`‖h‖_2² = ∫ ⟨ξ⟩^{2s} |𝓕f(ξ)|² dξ`. -/
theorem enorm_sq_eq_lintegral_of_besselPotential_eq {s : ℝ}
    {f h : Lp ℂ 2 (volume : Measure V)}
    (hfh : besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    ‖h‖ₑ ^ 2 = ∫⁻ ξ, ENNReal.ofReal (besselWeight s ξ) ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
  rw [← enorm_fourier_Lp_two, enorm_sq_eq_lintegral]
  refine lintegral_congr_ae ?_
  filter_upwards [fourier_ae_eq_of_besselPotential_eq hfh] with ξ hξ
  rw [← hξ, eNorm_mul, mul_pow, enorm_besselWeight]

/-- If `∫ ⟨ξ⟩^{2s} |𝓕f(ξ)|² dξ < ∞` for `f ∈ L_2(V)`, then `⟨ξ⟩^s 𝓕f ∈ L_2(V)`. -/
theorem memLp_besselWeight_mul_fourier (s : ℝ) (f : Lp ℂ 2 (volume : Measure V))
    (hf : ∫⁻ ξ, ENNReal.ofReal (besselWeight s ξ) ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 < ∞) :
    MemLp (fun ξ => (besselWeight s ξ : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ) 2
      volume := by
  have hm : AEStronglyMeasurable
      (fun ξ => (besselWeight s ξ : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ) volume :=
    (hasTemperateGrowth_besselWeight s).1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)
  refine memLp_iff.2 ?_
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero two_ne_top hm]
  simpa [eNorm_mul, mul_pow, enorm_besselWeight, ENNReal.rpow_two] using hf

/-- **A sufficient condition for `H^s`**: if `f ∈ L_2(V)` has
`∫ ⟨ξ⟩^{2s} |𝓕f(ξ)|² dξ < ∞`, then `f ∈ H^s(V)`. -/
theorem memSobolev_two_of_lintegral_lt_top {s : ℝ} (f : Lp ℂ 2 (volume : Measure V))
    (hf : ∫⁻ ξ, ENNReal.ofReal (besselWeight s ξ) ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 < ∞) :
    TemperedDistribution.MemSobolev s 2 (f : 𝓢'(V, ℂ)) := by
  rw [TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier]
  refine ⟨(memLp_besselWeight_mul_fourier s f hf).toLp _, ?_⟩
  rw [Lp.fourier_toTemperedDistribution_eq]
  exact smulLeftCLM_toTemperedDistribution_eq (hasTemperateGrowth_besselWeight s) _ _

/-- **Elements of `H^s`, `s ≥ 0`, are `L_2` functions**: if `J_s u = h` for a tempered
distribution `u` and `h ∈ L_2(V)`, then `u` is an `L_2(V)` function, namely `J_{-s} h`
(Mathlib's `TemperedDistribution.MemSobolev.mono`: `H^0 ⊆ H^{-s}`). -/
theorem exists_toTemperedDistribution_eq_of_besselPotential_eq {s : ℝ} (hs : 0 ≤ s)
    {u : 𝓢'(V, ℂ)} {h : Lp ℂ 2 (volume : Measure V)}
    (hu : besselPotential V ℂ s u = (h : 𝓢'(V, ℂ))) :
    ∃ f : Lp ℂ 2 (volume : Measure V), (f : 𝓢'(V, ℂ)) = u := by
  obtain ⟨f, hf⟩ := (TemperedDistribution.memSobolev_zero_iff.2 ⟨h, rfl⟩ :
    TemperedDistribution.MemSobolev 0 2 (h : 𝓢'(V, ℂ))).mono (by linarith : -s ≤ 0)
  exact ⟨f, hf.symm.trans ((TemperedDistribution.besselPotential_neg_apply_eq_iff s _ _).2 hu)⟩

/-! ### `H^s = F^s_{2,2}` -/

/-- **The Triebel–Lizorkin norm for `p = q = 2` on the Fourier side**: for `f ∈ L_2(V)`,
`‖f‖_{F^s_{2,2}}² = ∫ (∑_j 2^(2js) |𝓕ψ_j(ξ)|²) |𝓕f(ξ)|² dξ`, by
`‖f‖_{F^s_{2,2}} = ‖(2^(js) ‖Δ_j f‖_2)_j‖_{ℓ_2}`, Plancherel for each block and Tonelli. -/
theorem triebelLizorkinNorm_two_sq (s : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    triebelLizorkinNorm s 2 f ^ 2 = ∫⁻ ξ, (∑' j, dyadicWeight s j ^ 2 *
      ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2) * ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
  have hl := ENNReal.lqNorm_two_sq (fun j => dyadicWeight s j * ‖lpBlock two_ne_top j f‖ₑ)
  have hm : ∀ j, AEMeasurable (fun ξ => dyadicWeight s j ^ 2 * ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2) volume := fun j =>
    ((((continuous_fourier_of_integrable (integrable_psi j)).measurable.eNorm.pow_const
      2).aemeasurable.const_mul _).mul ((Lp.aestronglyMeasurable _).eNorm.pow_const 2))
  rw [triebelLizorkinNorm_eq_littlewoodPaleyNorm two_ne_top, littlewoodPaleyNorm, hl]
  calc ∑' j, (dyadicWeight s j * ‖lpBlock two_ne_top j f‖ₑ) ^ 2
      = ∑' j, ∫⁻ ξ, dyadicWeight s j ^ 2 * ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 *
          ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
        congr 1
        ext j
        rw [mul_pow, enorm_lpBlock_sq, ← lintegral_const_mul' _ _
          (ENNReal.pow_ne_top (ENNReal.dyadicWeight_ne_top s j))]
        simp_rw [mul_assoc]
    _ = _ := by
        rw [← lintegral_tsum hm]
        congr 1
        ext ξ
        rw [ENNReal.tsum_mul_right]

/-- For `s ≥ 0` and `f ∈ L_2(V)`,
`‖f‖_{F^s_{2,2}}² ≤ 2 · 4^s ∫ ⟨ξ⟩^{2s} |𝓕f(ξ)|² dξ`. -/
theorem triebelLizorkinNorm_two_sq_le {s : ℝ} (hs : 0 ≤ s) (f : Lp ℂ 2 (volume : Measure V)) :
    triebelLizorkinNorm s 2 f ^ 2 ≤ 2 * 4 ^ s * ∫⁻ ξ, ENNReal.ofReal (besselWeight s ξ) ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
  rw [triebelLizorkinNorm_two_sq, ← lintegral_const_mul' _ _ (by finiteness)]
  refine lintegral_mono fun ξ => ?_
  rw [← mul_assoc]
  gcongr
  exact tsum_dyadicWeight_fourier_psi_sq_le hs ξ

/-- For `s ≥ 0` and `f ∈ L_2(V)`,
`∫ ⟨ξ⟩^{2s} |𝓕f(ξ)|² dξ ≤ 2 · 5^s ‖f‖_{F^s_{2,2}}²`. -/
theorem lintegral_besselWeight_sq_le {s : ℝ} (hs : 0 ≤ s) (f : Lp ℂ 2 (volume : Measure V)) :
    ∫⁻ ξ, ENNReal.ofReal (besselWeight s ξ) ^ 2 *
        ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 ≤
      2 * 5 ^ s * triebelLizorkinNorm s 2 f ^ 2 := by
  rw [triebelLizorkinNorm_two_sq, ← lintegral_const_mul' _ _ (by finiteness)]
  refine lintegral_mono fun ξ => ?_
  rw [← mul_assoc]
  gcongr
  exact ofReal_besselWeight_sq_le_tsum hs ξ

/-- Taking square roots in `ℝ≥0∞`: `a² ≤ c b²` implies `a ≤ c^(1/2) b`. -/
theorem le_rpow_half_mul_of_sq_le {a b c : ℝ≥0∞} (h : a ^ 2 ≤ c * b ^ 2) :
    a ≤ c ^ (1 / 2 : ℝ) * b := by
  have h2 : (c ^ (1 / 2 : ℝ) * b) ^ 2 = c * b ^ 2 := by
    rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 (h.trans h2.ge)

/-- **`H^s ⊆ F^s_{2,2}` with norms**: for `s ≥ 0` and `f, h ∈ L_2(V)` with `J_s f = h`,
`‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖h‖_2`. -/
theorem triebelLizorkinNorm_le_of_besselPotential_eq {s : ℝ} (hs : 0 ≤ s)
    {f h : Lp ℂ 2 (volume : Measure V)}
    (hfh : besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    triebelLizorkinNorm s 2 f ≤ (2 * 4 ^ s) ^ (1 / 2 : ℝ) * ‖h‖ₑ :=
  le_rpow_half_mul_of_sq_le ((triebelLizorkinNorm_two_sq_le hs f).trans_eq
    (by rw [enorm_sq_eq_lintegral_of_besselPotential_eq hfh]))

/-- **`F^s_{2,2} ⊆ H^s` with norms**: for `s ≥ 0` and `f, h ∈ L_2(V)` with `J_s f = h`,
`‖h‖_2 ≤ (2 · 5^s)^{1/2} ‖f‖_{F^s_{2,2}}`. -/
theorem enorm_besselPotential_le_triebelLizorkinNorm {s : ℝ} (hs : 0 ≤ s)
    {f h : Lp ℂ 2 (volume : Measure V)}
    (hfh : besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    ‖h‖ₑ ≤ (2 * 5 ^ s) ^ (1 / 2 : ℝ) * triebelLizorkinNorm s 2 f :=
  le_rpow_half_mul_of_sq_le ((enorm_sq_eq_lintegral_of_besselPotential_eq hfh).trans_le
    (lintegral_besselWeight_sq_le hs f))

/-- **`H^s = F^s_{2,2}`**: for `s ≥ 0`, a tempered distribution `u` lies in Mathlib's Sobolev
space `H^s(V)` iff it is an `L_2(V)` function in the Triebel–Lizorkin space `F^s_{2,2}(V)`. -/
theorem memSobolev_two_iff_memTriebelLizorkin {s : ℝ} (hs : 0 ≤ s) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s 2 u ↔
      ∃ f : Lp ℂ 2 (volume : Measure V), (f : 𝓢'(V, ℂ)) = u ∧ MemTriebelLizorkin s 2 f := by
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨f, rfl⟩ := exists_toTemperedDistribution_eq_of_besselPotential_eq hs hh
    refine ⟨f, rfl, (triebelLizorkinNorm_le_of_besselPotential_eq hs hh).trans_lt ?_⟩
    exact ENNReal.mul_lt_top (by finiteness) eNorm_lt_top
  · rintro ⟨f, rfl, hf⟩
    refine memSobolev_two_of_lintegral_lt_top f ((lintegral_besselWeight_sq_le hs f).trans_lt ?_)
    exact ENNReal.mul_lt_top (by finiteness) (ENNReal.pow_lt_top hf)

/-- **`H^s = B^s_{2,2}`**: for `s > 0`, a tempered distribution `u` lies in `H^s(V)` iff it is an
`L_2(V)` function in the approximation space `A^s_2` of the band-limited scheme, the Besov space
`B^s_{2,2}(V)`. -/
theorem memSobolev_two_iff_exists_memApprox {s : ℝ} (hs : 0 < s) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure V),
      (f : 𝓢'(V, ℂ)) = u ∧ (bandScheme two_ne_top).MemApprox s 2 f := by
  simp_rw [memSobolev_two_iff_memTriebelLizorkin hs.le,
    memTriebelLizorkin_iff_memApprox two_ne_top hs]

/-- **`H^s` by the Littlewood–Paley norm**: for `s ≥ 0`, a tempered distribution `u` lies in
`H^s(V)` iff it is an `L_2(V)` function with `‖(2^(js) ‖Δ_j f‖_2)_j‖_{ℓ_2} < ∞`. -/
theorem memSobolev_two_iff_littlewoodPaleyNorm_lt_top {s : ℝ} (hs : 0 ≤ s) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure V),
      (f : 𝓢'(V, ℂ)) = u ∧ littlewoodPaleyNorm two_ne_top s 2 f < ∞ := by
  simp_rw [memSobolev_two_iff_memTriebelLizorkin hs, MemTriebelLizorkin,
    triebelLizorkinNorm_eq_littlewoodPaleyNorm two_ne_top]

/-- **The bundled space `H^s(V)`**: for `s ≥ 0`, every `F ∈ H^{s}(V)` (Mathlib's
`BesselPotentialSpace`) is an `L_2(V)` function `f` in `F^s_{2,2}(V)` with
`‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖F‖_{H^s}`. -/
theorem exists_eq_toDistr_two {s : ℝ} (hs : 0 ≤ s) (F : H^{s}(V)) :
    ∃ f : Lp ℂ 2 (volume : Measure V), (f : 𝓢'(V, ℂ)) = F.toDistr ∧
      MemTriebelLizorkin s 2 f ∧
      triebelLizorkinNorm s 2 f ≤ (2 * 4 ^ s) ^ (1 / 2 : ℝ) * ‖F‖ₑ := by
  obtain ⟨f, hf⟩ := exists_toTemperedDistribution_eq_of_besselPotential_eq hs
    F.bessel_toDistr_eq_toLp
  have hb := triebelLizorkinNorm_le_of_besselPotential_eq hs (f := f)
    (hf ▸ F.bessel_toDistr_eq_toLp)
  rw [BesselPotentialSpace.enorm_toLp_eq] at hb
  exact ⟨f, hf, hb.trans_lt (ENNReal.mul_lt_top (by finiteness) eNorm_lt_top), hb⟩

/-! ### `W^1_2 = H^1` -/

/-- **A derivative on the Fourier side**: if `∂_v f = g` as tempered distributions with
`f, g ∈ L_2(V)`, then `𝓕g(ξ) = 2πi ⟪ξ, v⟫ 𝓕f(ξ)` almost everywhere (Mathlib's
`TemperedDistribution.fourier_lineDerivOp_eq`). -/
theorem fourier_ae_eq_of_lineDerivOp_eq {v : V} {f g : Lp ℂ 2 (volume : Measure V)}
    (h : ∂_{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ))) :
    (fun ξ => 2 * π * Complex.I * (inner ℝ ξ v : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ)
      =ᵐ[volume] (𝓕 g : Lp ℂ 2 (volume : Measure V)) := by
  refine ae_eq_of_smulLeftCLM_eq (w := fun ξ => 2 * π * Complex.I * (inner ℝ ξ v : ℂ))
    (by fun_prop) ?_
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq, ← h,
    TemperedDistribution.fourier_lineDerivOp_eq, ← smul_apply,
    ← TemperedDistribution.smulLeftCLM_smul (by fun_prop)]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|2πi ⟪ξ, v⟫| ≤ 2π ‖v‖ ⟨ξ⟩`, by Cauchy–Schwarz and `‖ξ‖ ≤ ⟨ξ⟩`. -/
theorem norm_two_pi_I_inner_le (ξ v : V) :
    ‖2 * π * Complex.I * (inner ℝ ξ v : ℂ)‖ ≤ 2 * π * ‖v‖ * besselWeight 1 ξ := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs, mul_one]
  have h1 := abs_real_inner_le_norm ξ v
  have h2 := norm_le_besselWeight_one ξ
  have h3 : ‖ξ‖ * ‖v‖ ≤ ‖v‖ * besselWeight 1 ξ := by nlinarith [norm_nonneg v]
  calc 2 * π * |inner ℝ ξ v| ≤ 2 * π * (‖v‖ * besselWeight 1 ξ) := by gcongr; linarith
    _ = _ := by ring

/-- **Weak derivatives are bounded by the `H^1` norm**: if `g` is the weak derivative `∂_v f` on
`V` of `f ∈ L_2(V)`, `g ∈ L_2(V)`, and `J_1 f = h ∈ L_2(V)`, then
`‖g‖_2 ≤ 2π ‖v‖ ‖h‖_2`. -/
theorem enorm_le_of_hasWeakLineDeriv {v : V} {f g h : Lp ℂ 2 (volume : Measure V)}
    (hfg : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) f g)
    (hfh : besselPotential V ℂ 1 (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    ‖g‖ₑ ≤ ENNReal.ofReal (2 * π) * ‖v‖ₑ * ‖h‖ₑ := by
  have h1 := fourier_ae_eq_of_lineDerivOp_eq (hasWeakLineDeriv_top_iff.1 hfg)
  have h2 := fourier_ae_eq_of_besselPotential_eq hfh
  rw [← enorm_fourier_Lp_two g, ← enorm_fourier_Lp_two h, Lp.eNorm_def, Lp.eNorm_def]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ (Lp.aestronglyMeasurable _) ?_
  filter_upwards [h1, h2] with ξ e1 e2
  rw [← e1, ← e2, eNorm_mul (2 * π * Complex.I * (inner ℝ ξ v : ℂ)),
    eNorm_mul (besselWeight 1 ξ : ℂ), ← mul_assoc]
  gcongr
  rw [← ofReal_norm, ← ofReal_norm, enorm_besselWeight, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (norm_two_pi_I_inner_le ξ v)

/-- **A directional derivative by Plancherel**: if `∂_v f = g` as tempered distributions with
`f, g ∈ L_2(V)`, then `(2π)² ∫ ⟪ξ, v⟫² |𝓕f(ξ)|² dξ = ‖g‖_2²`. -/
theorem lintegral_inner_sq_eq {v : V} {f g : Lp ℂ 2 (volume : Measure V)}
    (h : ∂_{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ))) :
    ENNReal.ofReal (2 * π) ^ 2 * ∫⁻ ξ, ‖(inner ℝ ξ v : ℂ)‖ₑ ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
  rw [← enorm_fourier_Lp_two g, enorm_sq_eq_lintegral,
    ← lintegral_const_mul' _ _ (by finiteness)]
  refine lintegral_congr_ae ?_
  filter_upwards [fourier_ae_eq_of_lineDerivOp_eq h] with ξ hξ
  rw [← hξ, eNorm_mul, eNorm_mul, mul_pow, mul_pow, ← mul_assoc]
  congr 2
  rw [← ofReal_norm]
  congr 1
  simp [abs_of_pos Real.pi_pos]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Parseval for the Bessel weight**: `⟨ξ⟩² = 1 + ∑_i ⟪ξ, e_i⟫²` for every orthonormal basis
`(e_i)` of `V` (Mathlib's `OrthonormalBasis.sum_sq_inner_left`). -/
theorem ofReal_besselWeight_one_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (ξ : V) :
    ENNReal.ofReal (besselWeight 1 ξ) ^ 2 = 1 + ∑ i, ‖(inner ℝ ξ (b i) : ℂ)‖ₑ ^ 2 := by
  rw [ofReal_besselWeight_sq, ENNReal.rpow_one, ← b.sum_sq_inner_left ξ,
    ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun i _ => sq_nonneg _),
    ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
    sq_abs]

/-- **The `H^1` integral by the gradient**: let `(e_i)` be an orthonormal basis of `V`. If
`∂_{e_i} f = g_i` as tempered distributions for every `i`, with `f, g_i ∈ L_2(V)`, then
`(2π)² ∫ ⟨ξ⟩² |𝓕f(ξ)|² dξ = (2π)² ‖f‖_2² + ∑_i ‖g_i‖_2²`. -/
theorem lintegral_besselWeight_one_sq_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f : Lp ℂ 2 (volume : Measure V)} {g : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, ∂_{b i} (f : 𝓢'(V, ℂ)) = (g i : 𝓢'(V, ℂ))) :
    ENNReal.ofReal (2 * π) ^ 2 * ∫⁻ ξ, ENNReal.ofReal (besselWeight 1 ξ) ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 =
      ENNReal.ofReal (2 * π) ^ 2 * ‖f‖ₑ ^ 2 + ∑ i, ‖g i‖ₑ ^ 2 := by
  have hF : AEMeasurable (fun ξ => ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2) volume :=
    (Lp.aestronglyMeasurable _).eNorm.pow_const 2
  simp_rw [ofReal_besselWeight_one_sq b, add_mul, one_mul, Finset.sum_mul]
  rw [lintegral_add_left' hF, lintegral_finsetSum' _ fun i _ => ?_, mul_add, Finset.mul_sum,
    ← enorm_sq_eq_lintegral, enorm_fourier_Lp_two]
  · congr 1
    exact Finset.sum_congr rfl fun i _ => lintegral_inner_sq_eq (hg i)
  · exact ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).measurable.eNorm
      |>.pow_const 2).aemeasurable.mul hF

/-- **A gradient in `L_2` gives `H^1`**: let `(e_i)` be an orthonormal basis of `V`. If
`∂_{e_i} f = g_i` as tempered distributions for every `i`, with `f, g_i ∈ L_2(V)`, then
`f ∈ H^1(V)`, since `(2π)² ∫ ⟨ξ⟩² |𝓕f|² = (2π)² ‖f‖_2² + ∑_i ‖g_i‖_2² < ∞`
(`Rd.lintegral_besselWeight_one_sq_eq`, `Rd.memSobolev_two_of_lintegral_lt_top`). -/
theorem memSobolev_one_two_of_lineDerivOp_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {f : Lp ℂ 2 (volume : Measure V)}
    {g : ι → Lp ℂ 2 (volume : Measure V)} (hg : ∀ i, ∂_{b i} (f : 𝓢'(V, ℂ)) = (g i : 𝓢'(V, ℂ))) :
    TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(V, ℂ)) := by
  refine memSobolev_two_of_lintegral_lt_top f (ENNReal.lt_top_of_mul_ne_top_right ?_
    (ENNReal.pow_ne_zero (by simp [Real.pi_pos]) 2 : ENNReal.ofReal (2 * π) ^ 2 ≠ 0))
  rw [lintegral_besselWeight_one_sq_eq b hg]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by finiteness)
    (ENNReal.pow_ne_top eNorm_ne_top), ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.pow_ne_top eNorm_ne_top⟩

/-- **`W^1_2 = H^1`**: a function `f ∈ L_2(V)` lies in the Sobolev space `W^1_2(V)` of weak
derivatives (`Rd.MemSobolev 1 f`) iff it lies in Mathlib's Sobolev space `H^1(V)`
(`TemperedDistribution.MemSobolev 1 2`). `⇒`: the weak derivatives along the orthonormal basis
`Rd.gridBasis V` give `f ∈ H^1` (`Rd.memSobolev_one_two_of_lineDerivOp_eq`); `⇐`: Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp` maps `H^1` to `H^0 = L_2`. -/
theorem memSobolev_one_iff (f : Lp ℂ 2 (volume : Measure V)) :
    MemSobolev 1 f ↔ TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(V, ℂ)) := by
  rw [memSobolev_iff_tempered]
  constructor
  · intro hf
    choose g hg using fun i : Fin (finrank ℝ V) => hf 1 le_rfl (fun _ => gridBasis V i)
    exact memSobolev_one_two_of_lineDerivOp_eq (gridBasis V) (g := g) hg
  · intro hf k hk v
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
    · exact ⟨f, rfl⟩
    · exact TemperedDistribution.memSobolev_zero_iff.1
        (by simpa using hf.lineDerivOp (m := v 0))

/-- **The `H^1` norm by the weak gradient**: let `(e_i)` be an orthonormal basis of `V`. If
`g_i ∈ L_2(V)` is the weak derivative `∂_{e_i} f` on `V` of `f ∈ L_2(V)` for every `i`, and
`J_1 f = h ∈ L_2(V)`, then `(2π)² ‖h‖_2² = (2π)² ‖f‖_2² + ∑_i ‖g_i‖_2²`. -/
theorem enorm_besselPotential_one_sq_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f h : Lp ℂ 2 (volume : Measure V)} {g : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) f (g i))
    (hfh : besselPotential V ℂ 1 (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    ENNReal.ofReal (2 * π) ^ 2 * ‖h‖ₑ ^ 2 =
      ENNReal.ofReal (2 * π) ^ 2 * ‖f‖ₑ ^ 2 + ∑ i, ‖g i‖ₑ ^ 2 := by
  rw [enorm_sq_eq_lintegral_of_besselPotential_eq hfh]
  exact lintegral_besselWeight_one_sq_eq b fun i => hasWeakLineDeriv_top_iff.1 (hg i)

/-- **The `H^1` norm is at most the `W^1_2` norm**: under the hypotheses of
`Rd.enorm_besselPotential_one_sq_eq`, `‖J_1 f‖_2² ≤ ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²`, since
`(2π)² ≥ 1`. -/
theorem enorm_besselPotential_one_sq_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f h : Lp ℂ 2 (volume : Measure V)} {g : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) f (g i))
    (hfh : besselPotential V ℂ 1 (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    ‖h‖ₑ ^ 2 ≤ ‖f‖ₑ ^ 2 + ∑ i, ‖g i‖ₑ ^ 2 := by
  have hc1 : 1 ≤ ENNReal.ofReal (2 * π) ^ 2 := one_le_pow₀ (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.one_le_pi_div_two]))
  refine (ENNReal.mul_le_mul_iff_right (zero_lt_one.trans_le hc1).ne' (by finiteness)).1 ?_
  rw [enorm_besselPotential_one_sq_eq b hg hfh, mul_add]
  gcongr
  exact le_mul_of_one_le_left (by positivity) hc1

/-- `‖J_1 f‖_2² ≤ ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²` in `ℝ` (`Rd.enorm_besselPotential_one_sq_le`). -/
theorem sq_norm_besselPotential_one_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f h : Lp ℂ 2 (volume : Measure V)} {g : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) f (g i))
    (hfh : besselPotential V ℂ 1 (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    ‖h‖ ^ 2 ≤ ‖f‖ ^ 2 + ∑ i, ‖g i‖ ^ 2 := by
  have hle := enorm_besselPotential_one_sq_le b hg hfh
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] at hle
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle

/-- **The `H^1` norm by the weak gradient, in `ℝ`**: under the hypotheses of
`Rd.enorm_besselPotential_one_sq_eq`, `(2π)² ‖h‖_2² = (2π)² ‖f‖_2² + ∑_i ‖g_i‖_2²`. -/
theorem sq_norm_besselPotential_one_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f h : Lp ℂ 2 (volume : Measure V)} {g : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) f (g i))
    (hfh : besselPotential V ℂ 1 (f : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ))) :
    (2 * π) ^ 2 * ‖h‖ ^ 2 = (2 * π) ^ 2 * ‖f‖ ^ 2 + ∑ i, ‖g i‖ ^ 2 := by
  have he := enorm_besselPotential_one_sq_eq b hg hfh
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * π)] at he
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 he

/-! ### `W^1_2(V)` as a Besov space -/

/-- **`W^1_2 = B^1_{2,2}`**: `F ∈ L_2(V)` lies in the Sobolev space `W^1_2(V)` iff it lies in the
approximation space `A^1_2` of the band-limited functions, the Besov space `B^1_{2,2}(V)`. This
combines `W^1_2 = H^1` (`Rd.memSobolev_one_iff`) and `H^1 = B^1_{2,2}`
(`Rd.memSobolev_two_iff_exists_memApprox`); an `L_2` function is determined by its tempered
distribution (`Rd.eq_of_toTemperedDistribution_eq`). -/
theorem memSobolev_one_iff_memApprox (F : Lp ℂ 2 (volume : Measure V)) :
    MemSobolev 1 F ↔ (bandScheme two_ne_top).MemApprox 1 2 F := by
  rw [memSobolev_one_iff, memSobolev_two_iff_exists_memApprox one_pos]
  refine ⟨fun ⟨f, hf, hfa⟩ => ?_, fun h => ⟨F, rfl, h⟩⟩
  rwa [← eq_of_toTemperedDistribution_eq hf]

/-- **`W^1_2 = B^1_{2,2}` by differences**: for every order `r ≥ 2`, `F ∈ L_2(V)` lies in
`W^1_2(V)` iff `‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2} < ∞`
(`Rd.memApprox_bandScheme_iff_modulus` with `s = 1 < r`). -/
theorem memSobolev_one_iff_modulus {r : ℕ} (hr : 2 ≤ r) (F : Lp ℂ 2 (volume : Measure V)) :
    MemSobolev 1 F ↔ ‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 r F k) < ∞ := by
  rw [memSobolev_one_iff_memApprox]
  have hr' : (1 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hr
  exact memApprox_bandScheme_iff_modulus two_ne_top zero_le_one hr' one_le_two F

end Rd

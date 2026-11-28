/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.BesselPotentials.UniformSchwartzFamilies
public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevTriebelLizorkin

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Bessel potential spaces `H^{s,p} = F^s_{p,2}`

Let `V` have dimension `n ≥ 1` and `1 < p < ∞`. Mathlib's Bessel potential `J_s`
(`TemperedDistribution.besselPotential`) multiplies the Fourier transform of a tempered
distribution by `⟨ξ⟩^s = (1 + ‖ξ‖²)^{s/2}`, and `f` lies in Mathlib's Bessel potential space
`H^{s,p}(V)` (`TemperedDistribution.MemSobolev s p`) iff `J_s f ∈ L_p(V)`. This file proves
`H^{s,p}(V) ∩ L_p(V) = F^s_{p,2}(V)` for every real `s` and `H^{s,p}(V) = F^s_{p,2}(V)` for
`s ≥ 0`, with existential constants, and hence `W^m_p(V) = H^{m,p}(V)` (Calderón).

* **Even Fourier multipliers and convolutions**: for an even symbol `m` of temperate growth,
  `m(D)` commutes with translations and reflections of Schwartz functions
  (`Rd.fourierMultiplierCLM_compSubConstCLM`, `Rd.fourierMultiplierCLM_shiftReflect`), so
  `((m(D) η) ⋆ h)(x) = (m(D) h)(y ↦ η(x - y))` for `h ∈ L_r` (`Rd.conv_fourierMultiplierCLM_eq`)
  and `η ⋆ g = (m(D) η) ⋆ h` whenever `g = m(D) h` (`Rd.conv_eq_conv_fourierMultiplierCLM`); for
  the Bessel weight, `Rd.conv_eq_conv_besselSchwartz`. Moreover `J_s (η ⋆ F) = (J_s η) ⋆ F`
  (`Rd.besselPotential_toLp_conv`).
* **Bessel kernels of the Littlewood–Paley kernels**: `J_σ` maps the dilates of `psiBase j`
  and `psiDualBase j` to dyadic multiples of dilated Bessel kernels (`Rd.besselBase`), which form
  Calderón–Zygmund families (`Rd.exists_isCZFamily_besselBase_psiBase`,
  `Rd.exists_isCZFamily_besselBase_psiDualBase`).
* **`F^s_{p,2} ⊆ H^{s,p}` for every real `s`**
  (`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`), also in Mathlib's bundled space
  (`Rd.exists_enorm_toBesselPotentialSpace_le`): `J_s f` is the `L_p` limit of the synthesis
  sums `∑_{j < J} (J_s ψTilde_j) ⋆ (ψ_j ⋆ f)` (`Rd.exists_tendsto_sum_conv_blockFun`,
  `Rd.besselPotential_eq_of_tendsto`).
* **`H^{s,p} ⊆ F^s_{p,2}`**: `‖g‖_{F^s_{p,2}} ≤ C ‖J_s g‖_p` for `g ∈ L_p` and every real `s`
  (`Rd.exists_triebelLizorkinNorm_le_of_besselPotential_eq`), and for `s ≥ 0` every `f` with
  `J_s f ∈ L_p` is an `L_p` function (`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`), also
  for Mathlib's bundled space (`Rd.exists_memTriebelLizorkin_toDistr`).
* **The identities**: `Rd.memTriebelLizorkin_iff_memSobolev_bessel` (`f ∈ L_p`, every real `s`)
  and `Rd.memSobolev_iff_memSobolev_bessel` (`W^m_p = H^{m,p}`).
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal Topology SchwartzMap FourierTransform RealInnerProductSpace
  BesselPotentialSpace
open ENNReal (lqNorm dyadicWeight)
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Even Fourier multipliers on Schwartz functions -/

/-- `𝓕(J_t u)(ξ) = ⟨ξ⟩^t 𝓕u(ξ)` for Schwartz functions `u`
(`Rd.fourier_fourierMultiplierCLM_apply`). -/
theorem fourier_besselSchwartz_apply (t : ℝ) (u : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (besselSchwartz t u) ξ = (besselWeight t ξ : ℂ) * 𝓕 u ξ :=
  fourier_fourierMultiplierCLM_apply (hasTemperateGrowth_besselWeight t) u ξ

/-- **Translation becomes modulation**: `𝓕(φ(· - y))(ξ) = e^{-2πi⟨y, ξ⟩} 𝓕φ(ξ)` for Schwartz
functions `φ` (Mathlib's `VectorFourier.fourierIntegral_comp_add_right`). -/
theorem fourier_compSubConstCLM_apply (φ : 𝓢(V, ℂ)) (y ξ : V) :
    𝓕 (φ.compSubConstCLM ℂ y) ξ = (𝐞 (-⟪y, ξ⟫) : ℂ) * 𝓕 φ ξ := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ V) (φ : V → ℂ) (-y)) ξ
  have hφ : (φ.compSubConstCLM ℂ y : V → ℂ) = (φ : V → ℂ) ∘ fun v => v + -y := by
    funext x
    simp [sub_eq_add_neg]
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hφ]
  refine h.trans ?_
  rw [Circle.smul_def, innerₗ_apply_apply, inner_neg_left, smul_eq_mul]
  rfl

/-- **Fourier multipliers commute with translations**: `m(D) (φ(· - y)) = (m(D) φ)(· - y)` for a
symbol `m` of temperate growth, since the Fourier transforms of both sides are
`m(ξ) e^{-2πi⟨y, ξ⟩} 𝓕φ(ξ)` and the Fourier transform is injective on Schwartz functions. -/
theorem fourierMultiplierCLM_compSubConstCLM {m : V → ℂ} (hm : m.HasTemperateGrowth)
    (φ : 𝓢(V, ℂ)) (y : V) :
    SchwartzMap.fourierMultiplierCLM ℂ m (φ.compSubConstCLM ℂ y) =
      (SchwartzMap.fourierMultiplierCLM ℂ m φ).compSubConstCLM ℂ y := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).injective
  simp only [FourierTransform.fourierCLE_apply]
  ext ξ
  rw [fourier_fourierMultiplierCLM_apply hm, fourier_compSubConstCLM_apply,
    fourier_compSubConstCLM_apply, fourier_fourierMultiplierCLM_apply hm]
  ring

/-- **`J_t` commutes with translations**: `J_t (φ(· - y)) = (J_t φ)(· - y)`
(`Rd.fourierMultiplierCLM_compSubConstCLM`). -/
theorem besselSchwartz_compSubConstCLM (t : ℝ) (φ : 𝓢(V, ℂ)) (y : V) :
    besselSchwartz t (φ.compSubConstCLM ℂ y) = (besselSchwartz t φ).compSubConstCLM ℂ y :=
  fourierMultiplierCLM_compSubConstCLM (hasTemperateGrowth_besselWeight t) φ y

/-- **Even Fourier multipliers commute with the reflection** `φ ↦ φ(-·)`: for an even symbol `m`
of temperate growth, the Fourier transforms of both sides are `m(ξ) 𝓕φ(-ξ)`
(`Rd.fourier_reflect`). -/
theorem fourierMultiplierCLM_schwartzReflect {m : V → ℂ} (hm : m.HasTemperateGrowth)
    (heven : ∀ ξ, m (-ξ) = m ξ) (φ : 𝓢(V, ℂ)) :
    SchwartzMap.fourierMultiplierCLM ℂ m (schwartzReflect φ) =
      schwartzReflect (SchwartzMap.fourierMultiplierCLM ℂ m φ) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).injective
  simp only [FourierTransform.fourierCLE_apply]
  ext ξ
  have hr : ∀ G : 𝓢(V, ℂ), 𝓕 (schwartzReflect G) ξ = 𝓕 G (-ξ) := fun G => by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, coe_schwartzReflect]
    exact fourier_reflect (G : V → ℂ) ξ
  rw [fourier_fourierMultiplierCLM_apply hm, hr, hr, fourier_fourierMultiplierCLM_apply hm,
    heven]

/-- **Even Fourier multipliers commute with reflected translates**: for an even symbol `m` of
temperate growth, `m(D) (y ↦ η(x - y)) = (y ↦ (m(D) η)(x - y))`
(`Rd.fourierMultiplierCLM_compSubConstCLM`, `Rd.fourierMultiplierCLM_schwartzReflect`). -/
theorem fourierMultiplierCLM_shiftReflect {m : V → ℂ} (hm : m.HasTemperateGrowth)
    (heven : ∀ ξ, m (-ξ) = m ξ) (η : 𝓢(V, ℂ)) (x : V) :
    SchwartzMap.fourierMultiplierCLM ℂ m (shiftReflect η x) =
      shiftReflect (SchwartzMap.fourierMultiplierCLM ℂ m η) x := by
  rw [shiftReflect, shiftReflect, fourierMultiplierCLM_compSubConstCLM hm,
    fourierMultiplierCLM_schwartzReflect hm heven]

/-! ### Even Fourier multipliers and convolutions -/

/-- **Convolution as a tempered distribution**: for `g ∈ L_r(V)` and a Schwartz function `η`,
`(η ⋆ g)(x)` is the tempered distribution of `g` at the reflected translate `y ↦ η(x - y)`. -/
theorem conv_eq_toTemperedDistribution_shiftReflect {r : ℝ≥0∞} [Fact (1 ≤ r)] (η : 𝓢(V, ℂ))
    (g : Lp ℂ r (volume : Measure V)) (x : V) :
    conv η g volume x = (g : 𝓢'(V, ℂ)) (shiftReflect η x) := by
  rw [Lp.toTemperedDistribution_apply, conv_eq_integral_shiftReflect]
  simp only [smul_eq_mul]

/-- **Convolution with a multiplied kernel**: for an even symbol `m` of temperate growth,
`h ∈ L_r(V)`, a Schwartz function `η` and every `x`, `((m(D) η) ⋆ h)(x)` is the tempered
distribution `m(D) h` at the reflected translate `y ↦ η(x - y)`
(`Rd.fourierMultiplierCLM_apply_apply_of_even`, `Rd.fourierMultiplierCLM_shiftReflect`). -/
theorem conv_fourierMultiplierCLM_eq {r : ℝ≥0∞} [Fact (1 ≤ r)] {m : V → ℂ}
    (hm : m.HasTemperateGrowth) (heven : ∀ ξ, m (-ξ) = m ξ) (η : 𝓢(V, ℂ))
    (h : Lp ℂ r (volume : Measure V)) (x : V) :
    conv (SchwartzMap.fourierMultiplierCLM ℂ m η) h volume x =
      TemperedDistribution.fourierMultiplierCLM ℂ m (h : 𝓢'(V, ℂ)) (shiftReflect η x) := by
  rw [fourierMultiplierCLM_apply_apply_of_even hm heven,
    fourierMultiplierCLM_shiftReflect hm heven, conv_eq_toTemperedDistribution_shiftReflect]

/-- **Blocks of a multiplied function**: for an even symbol `m` of temperate growth, if
`g ∈ L_q(V)` and `h ∈ L_r(V)` satisfy `g = m(D) h` as tempered distributions, then
`η ⋆ g = (m(D) η) ⋆ h` at every point, for every Schwartz function `η`
(`Rd.conv_eq_toTemperedDistribution_shiftReflect`, `Rd.conv_fourierMultiplierCLM_eq`). -/
theorem conv_eq_conv_fourierMultiplierCLM {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    {m : V → ℂ} (hm : m.HasTemperateGrowth) (heven : ∀ ξ, m (-ξ) = m ξ)
    {g : Lp ℂ q (volume : Measure V)} {h : Lp ℂ r (volume : Measure V)}
    (hgh : (g : 𝓢'(V, ℂ)) = TemperedDistribution.fourierMultiplierCLM ℂ m (h : 𝓢'(V, ℂ)))
    (η : 𝓢(V, ℂ)) (x : V) :
    conv η g volume x = conv (SchwartzMap.fourierMultiplierCLM ℂ m η) h volume x := by
  rw [conv_fourierMultiplierCLM_eq hm heven, ← hgh, conv_eq_toTemperedDistribution_shiftReflect]

/-- **Blocks of a Bessel potential**: if `g ∈ L_q(V)` and `h ∈ L_r(V)` satisfy `g = J_t h` as
tempered distributions, then `η ⋆ g = (J_t η) ⋆ h` at every point, for every Schwartz function
`η` (`Rd.conv_eq_conv_fourierMultiplierCLM`, `Rd.besselWeight_neg`). -/
theorem conv_eq_conv_besselSchwartz {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] {t : ℝ}
    {g : Lp ℂ q (volume : Measure V)} {h : Lp ℂ r (volume : Measure V)}
    (hgh : (g : 𝓢'(V, ℂ)) = besselPotential V ℂ t (h : 𝓢'(V, ℂ))) (η : 𝓢(V, ℂ)) (x : V) :
    conv η g volume x = conv (besselSchwartz t η) h volume x :=
  conv_eq_conv_fourierMultiplierCLM (hasTemperateGrowth_besselWeight t)
    (fun ξ => by rw [besselWeight_neg]) hgh η x

/-! ### Bessel potentials of convolutions -/

/-- **`J_t` moves through a convolution, tested**: for `F ∈ L_p(V)`, `1 ≤ p < ∞`, and Schwartz
functions `η`, `u`, `∫ J_t u · (η ⋆ F) = ∫ u · ((J_t η) ⋆ F)`. Both sides are pairings of `F`
with reflected convolutions (`Rd.integral_conv_mul`), and
`∫ η(z - y) J_t u(z) dz = ∫ (J_t η)(z - y) u(z) dz` by the symmetry of `J_t` and its commuting
with translations (`Rd.integral_besselSchwartz_mul`, `Rd.besselSchwartz_compSubConstCLM`). -/
theorem integral_besselSchwartz_mul_conv {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {F : V → ℂ}
    (hF : MemLp F p volume) (t : ℝ) (η u : 𝓢(V, ℂ)) :
    ∫ x, besselSchwartz t u x * conv η F volume x =
      ∫ x, u x * conv (besselSchwartz t η) F volume x := by
  have := ENNReal.HolderConjugate.conjExponent hp1
  have hL : ∫ x, besselSchwartz t u x * conv η F volume x =
      ∫ x, conv η F volume x * besselSchwartz t u x := by
    congr 1
    funext x
    ring
  have hR : ∫ x, u x * conv (besselSchwartz t η) F volume x =
      ∫ x, conv (besselSchwartz t η) F volume x * u x := by
    congr 1
    funext x
    ring
  rw [hL, hR, integral_conv_mul (q := p.conjExponent) hp η.integrable hF
      ((besselSchwartz t u).memLp _),
    integral_conv_mul (q := p.conjExponent) hp (besselSchwartz t η).integrable hF (u.memLp _)]
  congr 1
  funext y
  congr 1
  rw [conv_reflect_apply, conv_reflect_apply]
  have h := integral_besselSchwartz_mul t (η.compSubConstCLM ℂ y) u
  rw [besselSchwartz_compSubConstCLM] at h
  simp only [SchwartzMap.compSubConstCLM_apply] at h
  exact h.symm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`J_t` of a convolution**: for `F ∈ L_p(V)`, `1 ≤ p < ∞`, and a Schwartz function `η`,
Mathlib's Bessel potential maps the tempered distribution of `η ⋆ F` to that of `(J_t η) ⋆ F`
(`Rd.besselPotential_apply_apply`, `Rd.integral_besselSchwartz_mul_conv`). -/
theorem besselPotential_toLp_conv (hp : p ≠ ∞) (t : ℝ) (η : 𝓢(V, ℂ)) {F : V → ℂ}
    (hF : MemLp F p volume) :
    besselPotential V ℂ t ((memLp_conv Fact.out η.integrable hF).toLp _ : 𝓢'(V, ℂ)) =
      ((memLp_conv Fact.out (besselSchwartz t η).integrable hF).toLp _ : 𝓢'(V, ℂ)) := by
  ext u
  rw [besselPotential_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc ∫ x, besselSchwartz t u x • (memLp_conv Fact.out η.integrable hF).toLp _ x
      = ∫ x, besselSchwartz t u x * conv η F volume x := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_conv Fact.out η.integrable hF)] with x hx
        rw [hx, smul_eq_mul]
    _ = ∫ x, u x * conv (besselSchwartz t η) F volume x :=
        integral_besselSchwartz_mul_conv Fact.out hp hF t η u
    _ = ∫ x, u x • (memLp_conv Fact.out (besselSchwartz t η).integrable hF).toLp _ x := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_conv Fact.out (besselSchwartz t η).integrable
          hF)] with x hx
        rw [hx, smul_eq_mul]

/-- **Limits of synthesis sums**: let `1 ≤ p < ∞`, let `η_j` be Schwartz functions and
`F_j ∈ L_p(V)`. If `∑_{j < J} η_j ⋆ F_j → f` and `∑_{j < J} (J_t η_j) ⋆ F_j → g` in `L_p(V)`,
then `J_t f = g` as tempered distributions. The partial sums satisfy this identity
(`Rd.besselPotential_toLp_conv`), `J_t` and the embedding of `L_p` into tempered distributions
are continuous, and limits in the tempered distributions are unique. -/
theorem besselPotential_eq_of_tendsto (hp : p ≠ ∞) (t : ℝ) {η : ℕ → 𝓢(V, ℂ)}
    {F : ℕ → V → ℂ} (hF : ∀ j, MemLp (F j) p volume) {f g : Lp ℂ p (volume : Measure V)}
    (hT : Tendsto (fun J => eLpNorm ((fun x => ∑ j ∈ Finset.range J,
      conv (η j) (F j) volume x) - ⇑f) p volume) atTop (𝓝 0))
    (hS : Tendsto (fun J => eLpNorm ((fun x => ∑ j ∈ Finset.range J,
      conv (besselSchwartz t (η j)) (F j) volume x) - ⇑g) p volume) atTop (𝓝 0)) :
    besselPotential V ℂ t (f : 𝓢'(V, ℂ)) = g := by
  set P : (ℕ → 𝓢(V, ℂ)) → ℕ → Lp ℂ p (volume : Measure V) := fun K J =>
    ∑ j ∈ Finset.range J, (memLp_conv Fact.out (K j).integrable (hF j)).toLp _ with hPdef
  have hcoe : ∀ (K : ℕ → 𝓢(V, ℂ)) (J : ℕ),
      ⇑(P K J) =ᵐ[volume] fun x => ∑ j ∈ Finset.range J, conv (K j) (F j) volume x := by
    intro K J
    have h1 : ∀ᵐ x ∂volume, ∀ j,
        (memLp_conv Fact.out (K j).integrable (hF j)).toLp _ x = conv (K j) (F j) volume x :=
      ae_all_iff.2 fun j => MemLp.coeFn_toLp _
    filter_upwards [h1, Lp.coeFn_fun_finsetSum (Finset.range J) fun j =>
      (memLp_conv Fact.out (K j).integrable (hF j)).toLp _] with x hx1 hx2
    rw [hPdef, hx2]
    exact Finset.sum_congr rfl fun j _ => hx1 j
  have hlim : ∀ (K : ℕ → 𝓢(V, ℂ)) (k : Lp ℂ p (volume : Measure V)),
      Tendsto (fun J => eLpNorm ((fun x => ∑ j ∈ Finset.range J,
        conv (K j) (F j) volume x) - ⇑k) p volume) atTop (𝓝 0) →
      Tendsto (P K) atTop (𝓝 k) := fun K k hK =>
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (P K) k).2
      (hK.congr fun J => (eLpNorm_congr_ae ((hcoe K J).sub EventuallyEq.rfl)).symm)
  have hPJ : ∀ J, besselPotential V ℂ t (P η J : 𝓢'(V, ℂ)) =
      (P (fun j => besselSchwartz t (η j)) J : 𝓢'(V, ℂ)) := fun J => by
    rw [← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, hPdef]
    simp only [map_sum, Lp.toTemperedDistributionCLM_apply]
    exact Finset.sum_congr rfl fun j _ => besselPotential_toLp_conv hp t (η j) (hF j)
  have h1 : Tendsto (fun J => besselPotential V ℂ t (P η J : 𝓢'(V, ℂ))) atTop
      (𝓝 (besselPotential V ℂ t (f : 𝓢'(V, ℂ)))) :=
    ((besselPotential V ℂ t).continuous.comp
      (Lp.toTemperedDistributionCLM ℂ volume p).continuous).continuousAt.tendsto.comp
      (hlim η f hT)
  have h2 : Tendsto (fun J => (P (fun j => besselSchwartz t (η j)) J : 𝓢'(V, ℂ))) atTop
      (𝓝 (g : 𝓢'(V, ℂ))) :=
    (Lp.toTemperedDistributionCLM ℂ volume p).continuous.continuousAt.tendsto.comp
      (hlim _ g hS)
  exact tendsto_nhds_unique (h1.congr hPJ) h2

/-! ### The Bessel kernels of the Littlewood–Paley kernels -/

/-- The **Bessel kernels of a family** `(ω_j)` of Schwartz functions:
`K^σ_j = 𝓕⁻¹[(2^{-2j} + ‖ζ‖²)^{σ/2} 𝓕ω_j]`, the Bessel kernels of `𝓕ω_j` at the scale `j`
(`Rd.besselKernelFamily`), so that `J_σ (ω_j)_{2^j} = 2^{jσ} (K^σ_j)_{2^j}`
(`Rd.besselSchwartz_schwartzDilate`). -/
noncomputable def besselBase (σ : ℝ) (ω : ℕ → 𝓢(V, ℂ)) (j : ℕ) : 𝓢(V, ℂ) :=
  besselKernelFamily (𝓕 (ω j)) σ j

/-- **The dilated Bessel kernels of a family form a Calderón–Zygmund family** when the family
is constant from `M` on, `ω_j = ω_M` for `j ≥ M`, and `𝓕ω_M` vanishes outside the annulus
`{a ≤ ‖ζ‖ ≤ 2^N a}`, `a > 0`: for every real `σ` there are finite `B`, `H` such that
`((K^σ_j)_{2^j})_j` is a Calderón–Zygmund family with overlap `B` and Hörmander constant `H`.
From `M` on, the kernels are the Bessel kernels of `𝓕ω_M`
(`Rd.exists_isUniformSchwartz_besselKernelFamily`,
`Rd.tsum_fourier_dilate_besselKernelFamily_sq_le`); the first `M` kernels are exceptional
members (`Rd.IsCZFamily.of_dilation_of_forall_ge_eq`). -/
theorem exists_isCZFamily_besselBase {ω : ℕ → 𝓢(V, ℂ)} {M N : ℕ} {a : ℝ} (ha : 0 < a)
    (hω : ∀ j, M ≤ j → ω j = ω M)
    (hann : ∀ ζ, 𝓕 (ω M) ζ ≠ 0 → a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 ^ N * a) (σ : ℝ) :
    ∃ B H : ℝ≥0∞, B ≠ ∞ ∧ H ≠ ∞ ∧
      IsCZFamily (fun j => dilate (2 ^ j) (besselBase σ ω j : V → ℂ)) B H := by
  obtain ⟨A, hA⟩ := exists_isUniformSchwartz_besselKernelFamily ha hann σ
  refine ⟨_, _, ?_, ?_, IsCZFamily.of_dilation_of_forall_ge_eq hA
    (tsum_fourier_dilate_besselKernelFamily_sq_le ha hann σ) (N := M) fun j hj => ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨besselOverlap_ne_top a N σ _,
      ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top ENNReal.ofReal_ne_top⟩
  · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _)
  · rw [besselBase, hω j hj]

/-- **The Bessel kernels of the synthesis kernels form a Calderón–Zygmund family**: for every
real `σ` there are finite `B`, `H` such that the dilated Bessel kernels of `psiDualBase` form a
Calderón–Zygmund family with overlap `B` and Hörmander constant `H`. The family `psiDualBase` is
constant from `2` on, with Fourier transform in `{1/4 ≤ ‖ζ‖ ≤ 2^4 · 1/4}`
(`Rd.mem_annulus_of_fourier_psiDualBase_ne_zero`). -/
theorem exists_isCZFamily_besselBase_psiDualBase (σ : ℝ) :
    ∃ B H : ℝ≥0∞, B ≠ ∞ ∧ H ≠ ∞ ∧
      IsCZFamily (fun j => dilate (2 ^ j) (besselBase σ (psiDualBase (V := V)) j : V → ℂ))
        B H :=
  exists_isCZFamily_besselBase (M := 2) (N := 4) (by norm_num : (0 : ℝ) < 4⁻¹)
    (fun j hj => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
      rfl)
    (fun _ h => mem_annulus_of_fourier_psiDualBase_ne_zero (j := 0) h) σ

/-- **The Bessel kernels of the blocks form a Calderón–Zygmund family**: for every real `σ`
there are finite `B`, `H` such that the dilated Bessel kernels of `psiBase` form a
Calderón–Zygmund family with overlap `B` and Hörmander constant `H`. The family `psiBase` is
constant from `1` on, with Fourier transform in `{1/2 ≤ ‖ζ‖ ≤ 2^2 · 1/2}`
(`Rd.mem_annulus_of_fourier_psiBase_ne_zero`). -/
theorem exists_isCZFamily_besselBase_psiBase (σ : ℝ) :
    ∃ B H : ℝ≥0∞, B ≠ ∞ ∧ H ≠ ∞ ∧
      IsCZFamily (fun j => dilate (2 ^ j) (besselBase σ (psiBase (V := V)) j : V → ℂ)) B H :=
  exists_isCZFamily_besselBase (M := 1) (N := 2) (by norm_num : (0 : ℝ) < 2⁻¹)
    (fun j hj => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
      rfl)
    (fun _ h => mem_annulus_of_fourier_psiBase_ne_zero (j := 0) h) σ

omit [Fact (1 ≤ p)] in
/-- **Convolution with the Bessel potential of a dilate**: for a family `(ω_j)` of Schwartz
functions, `(J_σ (ω_j)_{2^j}) ⋆ F = (K^σ_j)_{2^j} ⋆ ((2^j)^σ F)` at every point
(`Rd.besselSchwartz_schwartzDilate`). -/
theorem conv_besselSchwartz_schwartzDilate (σ : ℝ) (ω : ℕ → 𝓢(V, ℂ)) (j : ℕ) (F : V → ℂ)
    (x : V) :
    conv (besselSchwartz σ (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (ω j))) F volume
        x =
      conv (dilate (2 ^ j) (besselBase σ ω j : V → ℂ)) (((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) • F)
        volume x := by
  rw [besselSchwartz_schwartzDilate, FunLike.coe_smul, smul_conv, conv_smul,
    coe_schwartzDilate, besselBase]

omit [Fact (1 ≤ p)] in
/-- **The synthesis bound for Bessel potentials of dilates**: in dimension `n ≥ 1`, for
`1 < p < ∞`, real `σ`, a family `(ω_j)` of Schwartz functions whose dilated Bessel kernels
`((K^σ_j)_{2^j})_j` form a Calderón–Zygmund family with overlap `B` and Hörmander constant `H`,
every finite set `t ⊆ ℕ` and functions `g_j ∈ L_p(V)`,
`‖∑_{j ∈ t} (J_σ (ω_j)_{2^j}) ⋆ g_j‖_p ≤ S ‖ x ↦ ‖(1_t(j) 2^{jσ} |g_j(x)|)_j‖_{ℓ_2} ‖_p`
with `S = Rd.czConst V p B H` (`Rd.conv_besselSchwartz_schwartzDilate`,
`Rd.IsCZFamily.eLpNorm_sum_conv_smul_le` with the coefficients `(2^j)^σ`). For the blocks
`g_j = ψ_j ⋆ f` of `f ∈ L_p(V)` this bounds the synthesis sums of `F^σ_{p,2} ⊆ H^{σ,p}`. -/
theorem eLpNorm_sum_conv_besselSchwartz_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {σ : ℝ} {ω : ℕ → 𝓢(V, ℂ)} {B H : ℝ≥0∞}
    (hθ : IsCZFamily (fun j => dilate (2 ^ j) (besselBase σ ω j : V → ℂ)) B H)
    (t : Finset ℕ) {g : ℕ → V → ℂ} (hg : ∀ j, MemLp (g j) p volume) :
    eLpNorm (fun x => ∑ j ∈ t, conv (besselSchwartz σ
        (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (ω j))) (g j) volume x)
        p volume ≤
      czConst V p B H * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ t then dyadicWeight σ j * ‖g j x‖ₑ else 0) p volume := by
  have hsum : (fun x => ∑ j ∈ t, conv (besselSchwartz σ
      (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (ω j))) (g j) volume x) =
      fun x => ∑ j ∈ t, conv (dilate (2 ^ j) (besselBase σ ω j : V → ℂ))
        (((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) • g j) volume x := by
    funext x
    exact Finset.sum_congr rfl fun j _ => conv_besselSchwartz_schwartzDilate σ ω j _ x
  rw [hsum]
  exact hθ.eLpNorm_sum_conv_smul_le hp1 hp
    (c := fun j => ((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ)) (fun j => enorm_two_pow_rpow j σ) t hg

/-! ### `F^s_{p,2} ⊆ H^{s,p}` -/

/-- **`F^s_{p,2} ⊆ H^{s,p}` with norm bound**: in dimension `n ≥ 1`, for `1 < p < ∞` and every
real `s` there is a finite constant `C` such that for every `f ∈ F^s_{p,2}(V)` the Bessel
potential `J_s f` is an `L_p` function `h` with `‖h‖_p ≤ C ‖f‖_{F^s_{p,2}}`; the constant is
existential. The function `h` is the limit of the synthesis sums
`∑_{j < J} (J_s ψTilde_j) ⋆ (ψ_j ⋆ f)`, which converge by the synthesis bound of the dilated Bessel
kernels of `psiDualBase` (`Rd.exists_isCZFamily_besselBase_psiDualBase`,
`Rd.eLpNorm_sum_conv_besselSchwartz_le`, `Rd.exists_tendsto_sum_conv_blockFun`); the sums
without `J_s` tend to `f` (`Rd.tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub`), so
`J_s f = h` (`Rd.besselPotential_eq_of_tendsto`). -/
theorem exists_besselPotential_eq_of_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V), MemTriebelLizorkin s 2 f →
      ∃ h : Lp ℂ p (volume : Measure V), besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = h ∧
        ‖h‖ₑ ≤ C * triebelLizorkinNorm s 2 f := by
  obtain ⟨B, H, hB, hH, hθ⟩ := exists_isCZFamily_besselBase_psiDualBase (V := V) s
  refine ⟨czConst V p B H, czConst_ne_top hp1 hp hB hH, fun f hf => ?_⟩
  obtain ⟨h, hlim, hnorm⟩ := exists_tendsto_sum_conv_blockFun hp
    (K := fun j => besselSchwartz s (psiDualS j)) (czConst_ne_top hp1 hp hB hH) hf
    fun t => eLpNorm_sum_conv_besselSchwartz_le hp1 hp hθ t fun j => memLp_blockFun j f
  refine ⟨h, besselPotential_eq_of_tendsto hp s (η := psiDualS)
    (fun j => memLp_blockFun j f) ?_ hlim, hnorm⟩
  simpa only [coe_psiDualS] using tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub hp f

/-- **`F^s_{p,2} ⊆ H^{s,p}`**: in dimension `n ≥ 1`, for `1 < p < ∞` and real `s`, every
`f ∈ F^s_{p,2}(V)` lies in Mathlib's Bessel potential space: `J_s f ∈ L_p(V)`
(`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`). -/
theorem memSobolev_bessel_of_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {s : ℝ} {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin s 2 f) :
    TemperedDistribution.MemSobolev s p (f : 𝓢'(V, ℂ)) := by
  obtain ⟨C, -, hC⟩ := exists_besselPotential_eq_of_memTriebelLizorkin (V := V) hp1 hp s
  obtain ⟨h, hh, -⟩ := hC f hf
  exact ⟨h, hh⟩

/-! ### `H^{s,p} ⊆ F^s_{p,2}` -/

/-- **The blocks of a Bessel potential**: if `g ∈ L_q(V)` and `h ∈ L_r(V)` satisfy
`g = J_{-s} h` as tempered distributions, then for every `j` and `x`,
`2^{js} |(ψ_j ⋆ g)(x)| = |((K^{-s}_j)_{2^j} ⋆ h)(x)|` with the Bessel kernels `K^{-s}_j` of
`psiBase` (`Rd.conv_eq_conv_besselSchwartz`, `Rd.conv_besselSchwartz_schwartzDilate`). -/
theorem dyadicWeight_mul_enorm_blockFun_eq {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] {s : ℝ}
    {g : Lp ℂ q (volume : Measure V)} {h : Lp ℂ r (volume : Measure V)}
    (hgh : (g : 𝓢'(V, ℂ)) = besselPotential V ℂ (-s) (h : 𝓢'(V, ℂ))) (j : ℕ) (x : V) :
    dyadicWeight s j * ‖blockFun j g x‖ₑ =
      ‖conv (dilate (2 ^ j) (besselBase (-s) (psiBase (V := V)) j : V → ℂ)) h volume x‖ₑ := by
  rw [blockFun, ← coe_psiS, psiS, conv_eq_conv_besselSchwartz hgh,
    conv_besselSchwartz_schwartzDilate, conv_smul, Pi.smul_apply, smul_eq_mul, eNorm_mul,
    enorm_two_pow_rpow, ← mul_assoc, ENNReal.dyadicWeight_neg,
    ENNReal.mul_inv_cancel (ENNReal.dyadicWeight_ne_zero s j) (ENNReal.dyadicWeight_ne_top s j),
    one_mul]

/-- **`H^{s,p} ⊆ F^s_{p,2}` on `L_p`, with norm bound**: in dimension `n ≥ 1`, for `1 < p < ∞`
and every real `s` there is a finite constant `C` such that `‖g‖_{F^s_{p,2}} ≤ C ‖h‖_p` for all
`g, h ∈ L_p(V)` with `J_s g = h`; the constant is existential. Since `g = J_{-s} h` (Mathlib's
`TemperedDistribution.besselPotential_neg_apply_eq_iff`), the weighted blocks of `g` are the
convolutions of `h` with the dilated Bessel kernels of `psiBase` of order `-s`
(`Rd.dyadicWeight_mul_enorm_blockFun_eq`), a Calderón–Zygmund family
(`Rd.exists_isCZFamily_besselBase_psiBase`), and the analysis bound applies
(`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`). -/
theorem exists_triebelLizorkinNorm_le_of_besselPotential_eq [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g h : Lp ℂ p (volume : Measure V),
      besselPotential V ℂ s (g : 𝓢'(V, ℂ)) = h → triebelLizorkinNorm s 2 g ≤ C * ‖h‖ₑ := by
  obtain ⟨B, H, hB, hH, hθ⟩ := exists_isCZFamily_besselBase_psiBase (V := V) (-s)
  refine ⟨czConst V p B H, czConst_ne_top hp1 hp hB hH, fun g h hgh => ?_⟩
  have hg : (g : 𝓢'(V, ℂ)) = besselPotential V ℂ (-s) (h : 𝓢'(V, ℂ)) :=
    ((TemperedDistribution.besselPotential_neg_apply_eq_iff s _ _).2 hgh).symm
  rw [triebelLizorkinNorm, Lp.eNorm_def]
  simp_rw [dyadicWeight_mul_enorm_blockFun_eq hg]
  exact hθ.eLpNorm_lqNorm_conv_le hp1 hp (Lp.memLp h)

/-- **`H^{s,p} ⊆ F^s_{p,2}` for `s ≥ 0`**: in dimension `n ≥ 1`, for `1 < p < ∞` and real
`s ≥ 0` there is a finite constant `C` such that every tempered distribution `f` with
`J_s f = h ∈ L_p(V)` is an `L_p` function `g ∈ F^s_{p,2}(V)` with `‖g‖_{F^s_{p,2}} ≤ C ‖h‖_p`; the
constant is existential. Since `h ∈ L_p = F^0_{p,2} ⊆ F^{-s}_{p,2}`
(`Rd.memTriebelLizorkin_zero_two`), `J_{-s} h` is an `L_p` function `g`
(`Rd.exists_besselPotential_eq_of_memTriebelLizorkin` with `-s`), `J_{-s} h = f` (Mathlib's
`TemperedDistribution.besselPotential_neg_apply_eq_iff`), and
`Rd.exists_triebelLizorkinNorm_le_of_besselPotential_eq` bounds the norm of `g`. -/
theorem exists_memTriebelLizorkin_of_besselPotential_eq [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (f : 𝓢'(V, ℂ)) (h : Lp ℂ p (volume : Measure V)),
      besselPotential V ℂ s f = h → ∃ g : Lp ℂ p (volume : Measure V), (g : 𝓢'(V, ℂ)) = f ∧
        MemTriebelLizorkin s 2 g ∧ triebelLizorkinNorm s 2 g ≤ C * ‖h‖ₑ := by
  obtain ⟨C₁, -, hC₁⟩ := exists_besselPotential_eq_of_memTriebelLizorkin (V := V) hp1 hp (-s)
  obtain ⟨C, hC, hC₂⟩ := exists_triebelLizorkinNorm_le_of_besselPotential_eq (V := V) hp1 hp s
  refine ⟨C, hC, fun f h hfh => ?_⟩
  obtain ⟨g, hg, -⟩ :=
    hC₁ h ((memTriebelLizorkin_zero_two hp1 hp h).mono_smoothness (by linarith))
  have hgf : (g : 𝓢'(V, ℂ)) = f :=
    hg.symm.trans ((TemperedDistribution.besselPotential_neg_apply_eq_iff s _ _).2 hfh)
  have hb := hC₂ g h (by rw [hgf, hfh])
  exact ⟨g, hgf, hb.trans_lt (ENNReal.mul_lt_top hC.lt_top eNorm_lt_top), hb⟩

/-! ### The bundled spaces and `W^m_p = H^{m,p}` -/

/-- **`F^s_{p,2} ⊆ H^{s,p}` in Mathlib's bundled space**: in dimension `n ≥ 1`, for `1 < p < ∞`
and every real `s` there is a finite constant `C` such that every `f ∈ F^s_{p,2}(V)`, as an element
of Mathlib's `H^{s,p}(V)`, has `‖f‖_{H^{s,p}} ≤ C ‖f‖_{F^s_{p,2}}`; the constant is existential.
The `L_p` function of the bundled element is the function `h` of
`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`, since both represent `J_s f`
(`Rd.eq_of_toTemperedDistribution_eq`, `BesselPotentialSpace.enorm_toLp_eq`). -/
theorem exists_enorm_toBesselPotentialSpace_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (f : Lp ℂ p (volume : Measure V)) (hf : MemTriebelLizorkin s 2 f),
      ‖(memSobolev_bessel_of_memTriebelLizorkin hp1 hp hf).toBesselPotentialSpace‖ₑ ≤
        C * triebelLizorkinNorm s 2 f := by
  obtain ⟨C, hC, hC₁⟩ := exists_besselPotential_eq_of_memTriebelLizorkin (V := V) hp1 hp s
  refine ⟨C, hC, fun f hf => ?_⟩
  obtain ⟨h, hh, hnorm⟩ := hC₁ f hf
  set X := (memSobolev_bessel_of_memTriebelLizorkin hp1 hp hf).toBesselPotentialSpace
  have hX : X.toLp = h := eq_of_toTemperedDistribution_eq (by
    rw [← X.bessel_toDistr_eq_toLp, ← hh,
      TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr])
  rw [← BesselPotentialSpace.enorm_toLp_eq, hX]
  exact hnorm

/-- **`H^{s,p} ⊆ F^s_{p,2}` in Mathlib's bundled space, for `s ≥ 0`**: in dimension `n ≥ 1`, for
`1 < p < ∞` and real `s ≥ 0` there is a finite constant `C` such that every element `F` of
Mathlib's `H^{s,p}(V)` is an `L_p` function `g ∈ F^s_{p,2}(V)` with
`‖g‖_{F^s_{p,2}} ≤ C ‖F‖_{H^{s,p}}`; the constant is existential
(`Rd.exists_memTriebelLizorkin_of_besselPotential_eq` for the distribution and the `L_p` function
of `F`, `BesselPotentialSpace.enorm_toLp_eq`). -/
theorem exists_memTriebelLizorkin_toDistr [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 ≤ s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : H^{s, p}(V, ℂ), ∃ g : Lp ℂ p (volume : Measure V),
      (g : 𝓢'(V, ℂ)) = F.toDistr ∧ MemTriebelLizorkin s 2 g ∧
        triebelLizorkinNorm s 2 g ≤ C * ‖F‖ₑ := by
  obtain ⟨C, hC, hC₂⟩ := exists_memTriebelLizorkin_of_besselPotential_eq (V := V) hp1 hp hs
  refine ⟨C, hC, fun F => ?_⟩
  rw [← BesselPotentialSpace.enorm_toLp_eq]
  exact hC₂ F.toDistr F.toLp F.bessel_toDistr_eq_toLp

/-- **`F^s_{p,2} = H^{s,p} ∩ L_p` for every real `s`**: in dimension `n ≥ 1`, for `1 < p < ∞`
and real `s`, an `L_p` function `f` lies in `F^s_{p,2}(V)` iff it lies in Mathlib's Bessel
potential space, `J_s f ∈ L_p(V)` (`Rd.memSobolev_bessel_of_memTriebelLizorkin`,
`Rd.exists_triebelLizorkinNorm_le_of_besselPotential_eq`). -/
theorem memTriebelLizorkin_iff_memSobolev_bessel [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {s : ℝ} (f : Lp ℂ p (volume : Measure V)) :
    MemTriebelLizorkin s 2 f ↔ TemperedDistribution.MemSobolev s p (f : 𝓢'(V, ℂ)) := by
  refine ⟨memSobolev_bessel_of_memTriebelLizorkin hp1 hp, fun ⟨h, hh⟩ => ?_⟩
  obtain ⟨C, hC, hC₂⟩ := exists_triebelLizorkinNorm_le_of_besselPotential_eq (V := V) hp1 hp s
  exact (hC₂ f h hh).trans_lt (ENNReal.mul_lt_top hC.lt_top eNorm_lt_top)

/-- **`W^m_p = H^{m,p}` (Calderón)**: in dimension `n ≥ 1`, for `1 < p < ∞`, `m ∈ ℕ` and
`f ∈ L_p(V)`, `f` lies in the Sobolev space `W^m_p(V)` of weak derivatives iff it lies in
Mathlib's Bessel potential space `H^{m,p}(V)`: both are `F^m_{p,2}(V)`
(`Rd.memSobolev_iff_memTriebelLizorkin`, `Rd.memTriebelLizorkin_iff_memSobolev_bessel`). -/
theorem memSobolev_iff_memSobolev_bessel [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (f : Lp ℂ p (volume : Measure V)) :
    MemSobolev m f ↔ TemperedDistribution.MemSobolev (m : ℝ) p (f : 𝓢'(V, ℂ)) := by
  rw [memSobolev_iff_memTriebelLizorkin hp1 hp,
    memTriebelLizorkin_iff_memSobolev_bessel hp1 hp]

end Rd

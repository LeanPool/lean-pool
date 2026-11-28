/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinDistributions
public import LeanPool.FunctionSpaces.Rd.FourierMultipliers.SymbolKernels
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Fourier multipliers on Triebel–Lizorkin spaces

A symbol `m` of order `σ` (`Rd.HasSymbolGrowth σ m`) maps `F^s_{p,q}` to `F^{s-σ}_{p,q}`, for
tempered distributions, every real `s`, `1 < p < ∞` and `1 < q ≤ ∞`, with an existential
constant (`Rd.exists_triebelLizorkinNormDistr_fourierMultiplier_le`); on `L_p` functions this is a
bound for the Triebel–Lizorkin quasi-norm
(`Rd.exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq`). For a given uniform family `(G_j)`
with `m(D) ψTilde_j = 2^{jσ} (G_j)_{2^j}` the constant is `C_{n,N} C_{A,0,N} C_{FS}`
(`Rd.triebelLizorkinNormDistr_fourierMultiplier_le`), and `m(D)` maps `F^s_{p,q}` into
`F^{s-σ}_{p,q}` (`Rd.MemTriebelLizorkinDistr.fourierMultiplierCLM`).

The proof is pointwise. Since `𝓕ψTilde_j 𝓕ψ_j = 𝓕ψ_j`, the block of `m(D) u` is the multiplier
`𝓕(m(D) ψTilde_j)` applied to the block of `u` (`Rd.distribBlock_fourierMultiplierCLM`), so when
`Δ_j u = g_j ∈ L_p` it is the convolution `(m(D) ψTilde_j) ⋆ g_j`
(`Rd.distribBlock_fourierMultiplierCLM_eq_convLp`). Here `m(D) ψTilde_j = 2^{jσ} (G_j)_{2^j}` with a
uniform family `(G_j)` (`Rd.HasSymbolGrowth.exists_isUniformSchwartz_psiDualS`), so
`2^{j(s-σ)} |Δ_j(m(D) u)| ≤ C M(2^{js} |g_j|)` (`Rd.dyadicWeight_mul_enorm_conv_le_maximal`), and
the Fefferman–Stein inequality (`Rd.eLpNorm_le_of_le_lqNorm_maximal`) finishes.
-/

@[expose] public section

open MeasureTheory Module Filter
open scoped ENNReal SchwartzMap FourierTransform

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {σ : ℝ} {m : V → ℂ}

/-! ### The blocks of a Fourier multiplier -/

/-- **The blocks of a Fourier multiplier**: for `m` of temperate growth and every tempered
distribution `u`, `Δ_j(m(D) u) = 𝓕(m(D) ψTilde_j)(D) Δ_j u`. Both sides are Fourier multipliers of
`u` (Mathlib's `TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`), with the
symbols `m 𝓕ψ_j` and `𝓕ψ_j m 𝓕ψTilde_j`, equal since `𝓕ψTilde_j 𝓕ψ_j = 𝓕ψ_j`
(`Rd.fourier_psiDual_mul_psi`). -/
theorem distribBlock_fourierMultiplierCLM (hm : m.HasTemperateGrowth) (u : 𝓢'(V, ℂ)) (j : ℕ) :
    distribBlock j (TemperedDistribution.fourierMultiplierCLM ℂ m u) =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ m (psiDualS (V := V) j)) : 𝓢(V, ℂ))
        (distribBlock j u) := by
  rw [distribBlock, TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hm
      (𝓕 (psiS (V := V) j)).hasTemperateGrowth,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (𝓕 (psiS (V := V) j)).hasTemperateGrowth
      (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ m (psiDualS (V := V) j))).hasTemperateGrowth]
  refine congrArg (fun f => TemperedDistribution.fourierMultiplierCLM ℂ f u) (funext fun ξ => ?_)
  rw [Pi.mul_apply, Pi.mul_apply, fourier_fourierMultiplierCLM_apply hm, fourier_psiS_apply,
    SchwartzMap.fourier_coe, coe_psiDualS]
  linear_combination (-(m ξ)) * fourier_psiDual_mul_psi (V := V) j ξ

/-- **The blocks of a Fourier multiplier as convolutions**: if `m` has temperate growth,
`1 ≤ p < ∞` and the block `Δ_j u` of a tempered distribution is an `L_p` function `g`, then
`Δ_j(m(D) u)` is the `L_p` function `(m(D) ψTilde_j) ⋆ g` (`Rd.distribBlock_fourierMultiplierCLM`,
`Rd.fourierMultiplierCLM_fourier_toLp_eq_conv`). -/
theorem distribBlock_fourierMultiplierCLM_eq_convLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hm : m.HasTemperateGrowth) {u : 𝓢'(V, ℂ)} {j : ℕ} {g : Lp ℂ p (volume : Measure V)}
    (hg : distribBlock j u = (g : 𝓢'(V, ℂ))) :
    distribBlock j (TemperedDistribution.fourierMultiplierCLM ℂ m u) =
      (convLp hp (SchwartzMap.fourierMultiplierCLM ℂ m (psiDualS (V := V) j)).integrable g :
        𝓢'(V, ℂ)) := by
  rw [distribBlock_fourierMultiplierCLM hm, hg, fourierMultiplierCLM_fourier_toLp_eq_conv hp]

/-! ### The pointwise bound -/

/-- **Weighted convolutions with a symbol kernel below the maximal function**: let `(G_j)` be
uniformly Schwartz with bounds `A`, `N > n` and `K = 2^{jσ} (G_j)_{2^j}`. Then for every real `s`,
function `g` and point `x`,
`2^{j(s-σ)} |(K ⋆ g)(x)| ≤ C_{n,N} C_{A,0,N} M(2^{js} |g|)(x)`
(`Rd.IsUniformSchwartz.enorm_conv_dilate_le_maximal`, `Rd.enorm_two_pow_rpow`,
`Rd.dyadicWeight_mul_maximal`). -/
theorem dyadicWeight_mul_enorm_conv_le_maximal {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (hG : IsUniformSchwartz G A) {N : ℕ} (hN : finrank ℝ V < N) {j : ℕ} {K : 𝓢(V, ℂ)}
    (hK : K = ((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) •
      schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (G j))
    (s : ℝ) (g : V → ℂ) (x : V) :
    dyadicWeight (s - σ) j * ‖conv K g volume x‖ₑ ≤
      decayMaximalConst V N * familyDecayConst A 0 N *
        maximal (fun y => dyadicWeight s j * ‖g y‖ₑ) x := by
  rw [hK, FunLike.coe_smul, smul_conv, Pi.smul_apply, smul_eq_mul, eNorm_mul,
    enorm_two_pow_rpow j σ,
    coe_schwartzDilate, ← mul_assoc, ← ENNReal.dyadicWeight_add, sub_add_cancel,
    ← dyadicWeight_mul_maximal]
  calc dyadicWeight s j * ‖conv (dilate (2 ^ j) (G j : V → ℂ)) g volume x‖ₑ
      ≤ dyadicWeight s j * (decayMaximalConst V N * familyDecayConst A 0 N *
          maximal (fun y => ‖g y‖ₑ) x) := by
        gcongr
        exact hG.enorm_conv_dilate_le_maximal hN j g x
    _ = _ := by ring

/-! ### Fourier multipliers on `F^s_{p,q}` -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The multiplier bound for one family of blocks**: for a function `m` of temperate growth
with `m(D) ψTilde_j = 2^{jσ} (G_j)_{2^j}` and `(G_j)` uniformly Schwartz with bounds `A`, `1 < p
< ∞`,
`1 < q ≤ ∞` and `N > n`, if the blocks of `u` are `L_p` functions `g_j`, then
`‖m(D) u‖_{F^{s-σ}_{p,q}} ≤ C_{n,N} C_{A,0,N} C_{FS} ‖ x ↦ ‖(2^{js} |g_j(x)|)_j‖_{ℓ_q} ‖_p`
with the Fefferman–Stein constant `C_{FS} = Rd.feffermanSteinConst V p q`. The blocks of
`m(D) u` are the convolutions `(m(D) ψTilde_j) ⋆ g_j`
(`Rd.distribBlock_fourierMultiplierCLM_eq_convLp`), bounded at almost every point by
`Rd.dyadicWeight_mul_enorm_conv_le_maximal`, and `Rd.eLpNorm_le_of_le_lqNorm_maximal` applies. -/
theorem triebelLizorkinNormDistr_fourierMultiplier_le (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) (hm : m.HasTemperateGrowth) {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (hG : IsUniformSchwartz G A) (hK : ∀ j, SchwartzMap.fourierMultiplierCLM ℂ m (psiDualS j) =
      ((((2 : ℝ) ^ j) ^ σ : ℝ) : ℂ) • schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (G j))
    {N : ℕ} (hN : finrank ℝ V < N) (s : ℝ) {u : 𝓢'(V, ℂ)}
    {g : ℕ → Lp ℂ p (volume : Measure V)} (hg : ∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ))) :
    triebelLizorkinNormDistr p (s - σ) q (TemperedDistribution.fourierMultiplierCLM ℂ m u) ≤
      decayMaximalConst V N * familyDecayConst A 0 N * feffermanSteinConst V p q *
        eLpNorm (fun x => lqNorm q fun j => dyadicWeight s j * ‖g j x‖ₑ) p volume := by
  set K : ℕ → 𝓢(V, ℂ) := fun j => SchwartzMap.fourierMultiplierCLM ℂ m (psiDualS j) with hKdef
  refine (triebelLizorkinNormDistr_le (g := fun j => convLp hp (K j).integrable (g j))
    fun j => distribBlock_fourierMultiplierCLM_eq_convLp hp hm (hg j)).trans ?_
  refine eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (aemeasurable_lqNorm_dyadicWeight_Lp _ q _)
    (fun j => ((Lp.aestronglyMeasurable (g j)).eNorm.const_mul _)) ?_
  filter_upwards [ae_all_iff.2 fun j => convLp_apply_ae hp (K j).integrable (g j)] with x hx
  simp_rw [hx, ← ENNReal.lqNorm_const_mul]
  exact ENNReal.lqNorm_mono fun j =>
    dyadicWeight_mul_enorm_conv_le_maximal hG hN (hK j) s (g j) x

/-- **Fourier multipliers on `F^s_{p,q}` of tempered distributions**: for `1 < p < ∞`,
`1 < q ≤ ∞`, a symbol `m` of order `σ` and every real `s` there is a finite constant `C` with
`‖m(D) u‖_{F^{s-σ}_{p,q}} ≤ C ‖u‖_{F^s_{p,q}}` for every tempered distribution `u`; the constant is
existential. In particular `m(D)` maps `F^s_{p,q}` into `F^{s-σ}_{p,q}`. The uniform family of
`Rd.HasSymbolGrowth.exists_isUniformSchwartz_psiDualS` and
`Rd.triebelLizorkinNormDistr_fourierMultiplier_le` give the bound for every family of `L_p`
blocks of `u` (`Rd.le_mul_triebelLizorkinNormDistr`). -/
theorem exists_triebelLizorkinNormDistr_fourierMultiplier_le (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) (hm : HasSymbolGrowth σ m) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : 𝓢'(V, ℂ),
      triebelLizorkinNormDistr p (s - σ) q
          (TemperedDistribution.fourierMultiplierCLM ℂ m u) ≤
        C * triebelLizorkinNormDistr p s q u := by
  obtain ⟨G, A, hG, hK⟩ := hm.exists_isUniformSchwartz_psiDualS
  have hN : finrank ℝ V < finrank ℝ V + 1 := Nat.lt_succ_self _
  refine ⟨max 1 (decayMaximalConst V (finrank ℝ V + 1) * familyDecayConst A 0 (finrank ℝ V + 1) *
      feffermanSteinConst V p q), ?_, fun u => le_mul_triebelLizorkinNormDistr ?_ fun g hg => ?_⟩
  · exact max_ne_top ENNReal.one_ne_top (ENNReal.mul_ne_top
      (decayMaximalConst_mul_familyDecayConst_ne_top hN A) (feffermanSteinConst_ne_top hp1 hp hq1))
  · exact (zero_lt_one.trans_le (le_max_left _ _)).ne'
  · refine (triebelLizorkinNormDistr_fourierMultiplier_le hp1 hp hq1 hm.hasTemperateGrowth hG hK
      hN s hg).trans ?_
    gcongr
    exact le_max_right _ _

/-- **Fourier multipliers map `F^s_{p,q}` to `F^{s-σ}_{p,q}`**: for `1 < p < ∞`, `1 < q ≤ ∞`
and a symbol `m` of order `σ`, every tempered distribution `u ∈ F^s_{p,q}` has
`m(D) u ∈ F^{s-σ}_{p,q}` (`Rd.exists_triebelLizorkinNormDistr_fourierMultiplier_le`). -/
theorem MemTriebelLizorkinDistr.fourierMultiplierCLM (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) (hm : HasSymbolGrowth σ m) {s : ℝ} {u : 𝓢'(V, ℂ)}
    (hu : MemTriebelLizorkinDistr p s q u) :
    MemTriebelLizorkinDistr p (s - σ) q (TemperedDistribution.fourierMultiplierCLM ℂ m u) := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNormDistr_fourierMultiplier_le hp1 hp hq1 hm s
  exact (hCu u).trans_lt (ENNReal.mul_lt_top hC.lt_top hu)

/-- **Fourier multipliers on `F^s_{p,q}` of `L_p` functions**: for `1 < p < ∞`, `1 < q ≤ ∞`, a
symbol `m` of order `σ` and every real `s` there is a finite constant `C` with
`‖g‖_{F^{s-σ}_{p,q}} ≤ C ‖f‖_{F^s_{p,q}}` for all `f, g ∈ L_p(V)` with `g = m(D) f` as tempered
distributions; the constant is existential
(`Rd.exists_triebelLizorkinNormDistr_fourierMultiplier_le`,
`Rd.triebelLizorkinNormDistr_toTemperedDistribution`). -/
theorem exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) (hm : HasSymbolGrowth σ m) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f g : Lp ℂ p (volume : Measure V),
      (g : 𝓢'(V, ℂ)) = TemperedDistribution.fourierMultiplierCLM ℂ m (f : 𝓢'(V, ℂ)) →
        triebelLizorkinNorm (s - σ) q g ≤ C * triebelLizorkinNorm s q f := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNormDistr_fourierMultiplier_le (p := p) hp1 hp hq1
    hm s
  refine ⟨C, hC, fun f g hfg => ?_⟩
  have h := hCu (f : 𝓢'(V, ℂ))
  rwa [← hfg, triebelLizorkinNormDistr_toTemperedDistribution hp,
    triebelLizorkinNormDistr_toTemperedDistribution hp] at h

end Rd

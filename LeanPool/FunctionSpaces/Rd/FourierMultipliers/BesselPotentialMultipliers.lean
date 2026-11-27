/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.BesselPotentials.BesselPotentialDistributions
public import TauCeti.Analysis.Distribution.Sobolev

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Fourier multipliers on Bessel potential spaces

For `1 < p < ∞`, a symbol `m` of order `σ` (`Rd.HasSymbolGrowth σ m`) maps Mathlib's Bessel
potential space `H^{s,p}` into `H^{s-σ,p}`, for every real `s`
(`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_hasSymbolGrowth`): in dimension
`n ≥ 1` by `H^{s,p} = F^s_{p,2}` (`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`) and the
multiplier theorem on `F^s_{p,2}`, in dimension `0` since every symbol is constant there and
`J_s` is the identity (`Rd.besselPotential_of_subsingleton`).

* **Mapping properties**: `H^{s,p} ⊆ H^{s',p}` for `s' ≤ s`
  (`TemperedDistribution.MemSobolev.mono_of_one_lt`), so `L_p ⊆ H^{s,p}` for `s ≤ 0`
  (`Rd.memSobolev_bessel_of_nonpos`); derivatives map `H^{s,p}` into `H^{s-1,p}`
  (`TemperedDistribution.MemSobolev.lineDerivOp_of_one_lt`) and the Laplacian into `H^{s-2,p}`
  (`TemperedDistribution.MemSobolev.laplacian_of_one_lt`).
* **The derivative characterisation**: `J_2 = 1 - (2π)^{-2} Δ`
  (`TemperedDistribution.besselPotential_two_eq_sub_laplacian`), and `f ∈ H^{s+1,p}` iff
  `f ∈ H^{s,p}` and `∂_v f ∈ H^{s,p}` for every direction `v`
  (`TemperedDistribution.memSobolev_add_one_iff`).
* **The lifting property for every `q`**: for `g, J_σ g ∈ L_p` and `1 < q ≤ ∞`,
  `‖J_σ g‖_{F^{s-σ}_{p,q}}` and `‖g‖_{F^s_{p,q}}` are equivalent
  (`Rd.exists_triebelLizorkinNorm_besselPotential_le`,
  `Rd.exists_triebelLizorkinNorm_le_besselPotential`; Triebel 1983, Theorem 2.3.8).

The general Sobolev API and derivative characterizations are imported from Tau Ceti.
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal SchwartzMap Real Laplacian LineDeriv
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The Bessel potential in dimension `0`**: on a space with one point, `⟨ξ⟩^s = 1`, so `J_s`
is the identity (Mathlib's `TemperedDistribution.fourierMultiplierCLM_const`). -/
theorem besselPotential_of_subsingleton [Subsingleton V] (s : ℝ) (u : 𝓢'(V, ℂ)) :
    besselPotential V ℂ s u = u := by
  have h : (fun x : V => ((((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) : ℂ)) = fun _ => 1 := by
    funext x
    rw [Subsingleton.elim x 0, norm_zero]
    simp
  rw [TemperedDistribution.besselPotential, h, TemperedDistribution.fourierMultiplierCLM_const,
    one_smul, ContinuousLinearMap.id_apply]

/-- **Fourier multipliers on `H^{s,p}` in dimension `0`**: on a space with one point every
function `m` is constant, `m(D) u = m(0) u`, and `H^{s,p} = H^{t,p}` for all `s`, `t`
(`Rd.besselPotential_of_subsingleton`). -/
theorem memSobolev_fourierMultiplierCLM_of_subsingleton [Subsingleton V] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {s t : ℝ} (m : V → ℂ) {u : 𝓢'(V, ℂ)}
    (hu : TemperedDistribution.MemSobolev s p u) :
    TemperedDistribution.MemSobolev t p (TemperedDistribution.fourierMultiplierCLM ℂ m u) := by
  have hm : m = fun _ => m 0 := funext fun x => by rw [Subsingleton.elim x 0]
  obtain ⟨f, hf⟩ := hu
  rw [besselPotential_of_subsingleton] at hf
  refine ⟨m 0 • f, ?_⟩
  rw [besselPotential_of_subsingleton, hm, TemperedDistribution.fourierMultiplierCLM_const,
    smul_apply, ContinuousLinearMap.id_apply, hf,
    ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_smul]

end Rd

namespace TemperedDistribution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Fourier multipliers on Bessel potential spaces**: for `1 < p < ∞`, a symbol `m` of order
`σ` and every real `s`, `m(D)` maps Mathlib's Bessel potential space `H^{s,p}(V)` into
`H^{s-σ,p}(V)`. In dimension `n ≥ 1`, `H^{s,p} = F^s_{p,2}`
(`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`) and `m(D)` maps `F^s_{p,2}` into
`F^{s-σ}_{p,2}` (`Rd.MemTriebelLizorkinDistr.fourierMultiplierCLM`); dimension `0` is
`Rd.memSobolev_fourierMultiplierCLM_of_subsingleton`. -/
theorem MemSobolev.fourierMultiplierCLM_of_hasSymbolGrowth (hp1 : 1 < p) (hp : p ≠ ∞)
    {σ s : ℝ} {m : V → ℂ} (hm : Rd.HasSymbolGrowth σ m) {u : 𝓢'(V, ℂ)}
    (hu : MemSobolev s p u) : MemSobolev (s - σ) p (fourierMultiplierCLM ℂ m u) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Rd.memSobolev_fourierMultiplierCLM_of_subsingleton m hu
  rw [Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr hp1 hp] at hu ⊢
  exact hu.fourierMultiplierCLM hp1 hp ENNReal.one_lt_two hm

/-- **The Laplacian on Bessel potential spaces**: for `1 < p < ∞`, the Laplacian maps `H^{s,p}`
into `H^{s-2,p}`, since `Δ = -(2π)^2 ‖ξ‖^2(D)` (Mathlib's
`TemperedDistribution.laplacian_eq_fourierMultiplierCLM`) with the symbol `‖ξ‖^2` of order `2`
(`Rd.hasSymbolGrowth_norm_sq`). For `p = 2` this is Mathlib's
`TemperedDistribution.MemSobolev.laplacian`. -/
theorem MemSobolev.laplacian_of_one_lt (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ} {f : 𝓢'(V, ℂ)}
    (hf : MemSobolev s p f) : MemSobolev (s - 2) p (Δ f) := by
  rw [laplacian_eq_fourierMultiplierCLM]
  exact (hf.fourierMultiplierCLM_of_hasSymbolGrowth hp1 hp
    Rd.hasSymbolGrowth_norm_sq).smul_of_tower _

end TemperedDistribution

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`L_p ⊆ H^{s,p}` for `s ≤ 0`**: for `1 < p < ∞`, real `s ≤ 0` and `f ∈ L_p(V)`, the tempered
distribution of `f` lies in Mathlib's `H^{s,p}(V)`, since it lies in `H^{0,p}` (Mathlib's
`TemperedDistribution.memSobolev_zero_iff`) and `H^{0,p} ⊆ H^{s,p}`
(`TemperedDistribution.MemSobolev.mono_of_one_lt`). -/
theorem memSobolev_bessel_of_nonpos (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ} (hs : s ≤ 0)
    (f : Lp ℂ p (volume : Measure V)) : TemperedDistribution.MemSobolev s p (f : 𝓢'(V, ℂ)) :=
  (TemperedDistribution.memSobolev_zero_iff.2 ⟨f, rfl⟩).mono_of_one_lt hp1 hp hs

/-- **The lifting property for every `q`, first half**: for `1 < p < ∞`, `1 < q ≤ ∞` and all
reals `σ`, `s` there is a finite constant `C` such that
`‖h‖_{F^{s-σ}_{p,q}} ≤ C ‖g‖_{F^s_{p,q}}` for all `g, h ∈ L_p(V)` with `J_σ g = h`; the constant is
existential. `J_σ` is the Fourier multiplier with the symbol `⟨ξ⟩^σ` of order `σ`
(`Rd.hasSymbolGrowth_besselWeight`, `Rd.exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq`). -/
theorem exists_triebelLizorkinNorm_besselPotential_le (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) (σ s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g h : Lp ℂ p (volume : Measure V),
      besselPotential V ℂ σ (g : 𝓢'(V, ℂ)) = h →
        triebelLizorkinNorm (s - σ) q h ≤ C * triebelLizorkinNorm s q g := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq (V := V) hp1 hp hq1
    (hasSymbolGrowth_besselWeight σ) s
  exact ⟨C, hC, fun g h hgh => hCu g h hgh.symm⟩

/-- **The lifting property for every `q`, second half**: for `1 < p < ∞`, `1 < q ≤ ∞` and all
reals `σ`, `s` there is a finite constant `C` such that
`‖g‖_{F^s_{p,q}} ≤ C ‖h‖_{F^{s-σ}_{p,q}}` for all `g, h ∈ L_p(V)` with `J_σ g = h`; the constant is
existential. Here `g = J_{-σ} h` (Mathlib's
`TemperedDistribution.besselPotential_neg_apply_eq_iff`) with the symbol `⟨ξ⟩^{-σ}` of order
`-σ`. With `Rd.exists_triebelLizorkinNorm_besselPotential_le` this is Triebel's lifting property
(Triebel 1983, Theorem 2.3.8) for `1 < q ≤ ∞`. -/
theorem exists_triebelLizorkinNorm_le_besselPotential (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) (σ s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g h : Lp ℂ p (volume : Measure V),
      besselPotential V ℂ σ (g : 𝓢'(V, ℂ)) = h →
        triebelLizorkinNorm s q g ≤ C * triebelLizorkinNorm (s - σ) q h := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq (V := V) hp1 hp hq1
    (hasSymbolGrowth_besselWeight (-σ)) (s - σ)
  refine ⟨C, hC, fun g h hgh => ?_⟩
  have h' := hCu h g ((TemperedDistribution.besselPotential_neg_apply_eq_iff σ _ _).2 hgh).symm
  rwa [sub_neg_eq_add, sub_add_cancel] at h'

end Rd

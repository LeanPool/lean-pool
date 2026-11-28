/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.CriticalSobolevEmbedding
public import LeanPool.FunctionSpaces.Rd.BesselPotentials.BesselPotentialLifting

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Embeddings of Bessel potential spaces

Let `V` have dimension `n ≥ 1`, `1 < p < ∞`, `p ≤ r < ∞` and `s ≥ n(1/p - 1/r)`. Every element of
Mathlib's Bessel potential space `H^{s,p}(V)` is an `L_r` function: as a tempered distribution it
is a function `g ∈ L_r(V)` (`Rd.exists_memLp_eq_of_memSobolev_bessel`), and in the bundled space
`‖g‖_r ≤ C ‖F‖_{H^{s,p}}` with an existential constant
(`Rd.exists_enorm_le_of_besselPotentialSpace`). The proof uses `H^{s,p} = F^s_{p,2}` for
`s ≥ 0` (`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`) and the critical embedding
`F^α_{p,∞} ↪ L_r` (`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`); an `L_p` class and
an `L_r` class with almost everywhere equal representatives are the same tempered distribution
(`Rd.toTemperedDistribution_eq_of_ae_eq`).
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal SchwartzMap BesselPotentialSpace

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- **`H^{s,p} ↪ L_r`**: let `n ≥ 1`, `1 < p < ∞`, `p ≤ r < ∞` and `s ≥ n(1/p - 1/r)`. Every
tempered distribution `f` in Mathlib's Bessel potential space `H^{s,p}(V)` is a function
`g ∈ L_r(V)`. Since `s ≥ 0`, `f` is an `L_p` function `g₀ ∈ F^s_{p,2}`
(`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`), and `F^s_{p,2} ↪ L_r`
(`Rd.exists_memLp_ae_eq_of_memTriebelLizorkin_of_le`). The potential route through the
Hardy–Littlewood–Sobolev inequality is Stein's (1970, Chapter V). -/
theorem exists_memLp_eq_of_memSobolev_bessel [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hpr : p ≤ r) (hr : r ≠ ∞) {s : ℝ} (hs : nikolskiiExponent (finrank ℝ V) p r ≤ s)
    {f : 𝓢'(V, ℂ)} (hf : TemperedDistribution.MemSobolev s p f) :
    ∃ g : Lp ℂ r (volume : Measure V), (g : 𝓢'(V, ℂ)) = f := by
  have hs0 : 0 ≤ s := (nikolskiiExponent_nonneg (Nat.cast_nonneg _) Fact.out hpr).trans hs
  obtain ⟨h, hh⟩ := hf
  obtain ⟨C, -, hC⟩ := exists_memTriebelLizorkin_of_besselPotential_eq (V := V) hp1 hp hs0
  obtain ⟨g₀, hg₀, hmem, -⟩ := hC f h hh
  obtain ⟨g, hg⟩ := exists_memLp_ae_eq_of_memTriebelLizorkin_of_le hpr hr hs one_le_two hmem
  exact ⟨g, (toTemperedDistribution_eq_of_ae_eq hg).trans hg₀⟩

/-- **`H^{s,p} ↪ L_r` in Mathlib's bundled space**: let `n ≥ 1`, `1 < p < ∞`, `p ≤ r < ∞` and
`s ≥ n(1/p - 1/r)`. There is a finite constant `C` such that every element `F` of Mathlib's
`H^{s,p}(V)` is a function `g ∈ L_r(V)` with `‖g‖_r ≤ C ‖F‖_{H^{s,p}}`; the constant is
existential. For `r = p` it is `QTilde_{V,p} C₀`, from the lower square function bound
`‖g‖_p ≤ QTilde_{V,p} ‖g‖_{F^0_{p,2}}` (`Rd.enorm_le_triebelLizorkinNorm_zero_two`), and for `p < r`
it is `K_{V,p,r} C₀` (`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`), where `C₀` is the
constant of `H^{s,p} ⊆ F^s_{p,2}` (`Rd.exists_memTriebelLizorkin_toDistr`). -/
theorem exists_enorm_le_of_besselPotentialSpace [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hpr : p ≤ r) (hr : r ≠ ∞) {s : ℝ} (hs : nikolskiiExponent (finrank ℝ V) p r ≤ s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : H^{s, p}(V, ℂ), ∃ g : Lp ℂ r (volume : Measure V),
      (g : 𝓢'(V, ℂ)) = F.toDistr ∧ ‖g‖ₑ ≤ C * ‖F‖ₑ := by
  have hs0 : 0 ≤ s := (nikolskiiExponent_nonneg (Nat.cast_nonneg _) Fact.out hpr).trans hs
  obtain ⟨C₀, hC₀, hC⟩ := exists_memTriebelLizorkin_toDistr (V := V) hp1 hp hs0
  rcases hpr.eq_or_lt with rfl | hlt
  · refine ⟨squareSynthesisConst V p * C₀,
      ENNReal.mul_ne_top (squareSynthesisConst_ne_top hp1 hp) hC₀, fun F => ?_⟩
    obtain ⟨g₀, hg₀, -, hn⟩ := hC F
    refine ⟨g₀, hg₀, (enorm_le_triebelLizorkinNorm_zero_two hp1 hp g₀).trans ?_⟩
    rw [mul_assoc]
    exact mul_le_mul' le_rfl ((triebelLizorkinNorm_mono_smoothness hs0 2 g₀).trans hn)
  refine ⟨criticalEmbeddingConst V p r * C₀,
    ENNReal.mul_ne_top (criticalEmbeddingConst_ne_top hlt hr) hC₀, fun F => ?_⟩
  obtain ⟨g₀, hg₀, hmem, hn⟩ := hC F
  have hle : triebelLizorkinNorm (nikolskiiExponent (finrank ℝ V) p r) ∞ g₀ ≤ C₀ * ‖F‖ₑ :=
    ((triebelLizorkinNorm_mono_exponent one_le_two le_top g₀).trans
      (triebelLizorkinNorm_mono_smoothness hs 2 g₀)).trans hn
  obtain ⟨g, hg, hgn⟩ := exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top hlt hr rfl
    (hle.trans_lt (ENNReal.mul_lt_top hC₀.lt_top eNorm_lt_top))
  refine ⟨g, (toTemperedDistribution_eq_of_ae_eq hg).trans hg₀, hgn.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul' le_rfl hle

end Rd

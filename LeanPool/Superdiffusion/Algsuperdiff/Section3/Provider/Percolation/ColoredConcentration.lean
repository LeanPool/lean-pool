/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Coloring
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.IndepChain
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.PartitionAverages

/-!
# ColoredConcentration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The colouring corollary of the ABK26 concentration inequality

ABK26 states, immediately after Proposition `p.concentration`: if `{X_z}_{z ∈ 3^n
ℤ^d ∩ □_m}` are centered with `X_z = O_{Γ_σ}(1)` and `X_z, X_{z'}` are independent
whenever the corresponding subcubes do not touch, then

`∑_{z} X_z ≤ O_{Γ_σ}(C(σ) 3^{d(m-n)/2})`.

This module proves the corollary in the form the percolation lemma consumes:
sites of the lattice `ℤ^d`, independence supplied by the *two-set* finite-range
hypothesis of ABK26 at range `3 ^ L`, and the conclusion stated for the
**average** over a finite site set `S`.

The proof is the standard colouring argument.

1. Colour each site by its residue modulo `3 ^ L + 1` (`Coloring.lean`). Two
   distinct sites of one colour are separated at range `3 ^ L`.
2. Inside a colour class, the two-set hypothesis upgrades to mutual
   independence (`IndepChain.lean`) and CoarseGraining's concentration
   inequality applies, giving the class sum at scale `C(σ) √(#class) K`.
3. The classes are recombined with CoarseGraining's finite triangle inequality,
   at the Cauchy--Schwarz cost `∑_c √(#class c) ≤ √(colourCount) √(#S)` of
   `Coloring.sum_sqrt_card_colorClass_le`.

Because the colour count is taken to be `min ((3^L+1)^d) (#S)`, the estimate is
simultaneously the "independent" bound `√((3^L+1)^d / #S)` for `3 ^ L` small
compared with the diameter of `S` and the trivial triangle-inequality bound `1`
for `3 ^ L` large. Both regimes are needed by Step 1 of
`l.percolation.bound.general`, and using only the first would produce a
divergent scale sum.

## Main results

* `Algsuperdiff.Section3.Provider.Percolation.isBigO_gammaSigma_sum_of_pairwise_separated`
* `Algsuperdiff.Section3.Provider.Percolation.isBigO_gammaSigma_average_of_separatedIndep`

## References

* ABK26, Proposition `p.concentration` and its corollary.
* ABK26, Lemma `l.percolation.bound.general`, hypothesis (ii).
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Positivity of CoarseGraining's public constant for the centered independent-sum
`Γ_σ` concentration inequality.  CoarseGraining keeps this fact private, so it
is reproved here from CoarseGraining's public constants. -/
theorem gammaSigmaIndependentSumConst_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst σ := by
  dsimp [HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst]
  by_cases hσ_lt : σ < 1
  · simpa [hσ_lt, HCPolySupport.Book.Ch04.gammaSigmaHeavyTailEndpointConst,
      gammaSigmaHeavyTailEndpointConst] using
      mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
        (gammaSigmaHeavyTailConst_pos hσ)
  · by_cases hσ_eq : σ = 1
    · subst hσ_eq
      simpa [hσ_lt, HCPolySupport.Book.Ch04.gammaSigmaExpRegimeEndpointConst,
        gammaSigmaExpRegimeEndpointConst] using
        mul_pos (by norm_num : (0 : ℝ) < 2) gammaOneExpRegimeConst_pos
    · have hExpConst_pos : 0 < gammaSigmaExpRegimeConst σ := by
        dsimp [gammaSigmaExpRegimeConst]
        exact lt_of_lt_of_le (mul_pos (by positivity) (gammaMomentConst_pos hσ))
          (le_max_left _ _)
      simpa [hσ_lt, hσ_eq, HCPolySupport.Book.Ch04.gammaSigmaExpRegimeEndpointConst,
        gammaSigmaExpRegimeEndpointConst] using
        mul_pos (by norm_num : (0 : ℝ) < 2) hExpConst_pos

/-- **Concentration on a pairwise-separated site set.**

For centered random variables localised at pairwise-separated sites, the two-set
finite-range hypothesis of ABK26 upgrades to mutual independence and the
concentration inequality applies verbatim. -/
theorem isBigO_gammaSigma_sum_of_pairwise_separated [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {L : ℕ} {S : Finset (Fin d → ℤ)} {σ K : ℝ}
    (hindep : ∀ S₁ S₂ : Set (Fin d → ℤ), (∀ u ∈ S₁, ∀ v ∈ S₂, 3 ^ L < latDist u v) →
      Indep (siteSigma B S₁ L) (siteSigma B S₂ L) μ)
    (hsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → 3 ^ L < latDist u v)
    (hS : S.Nonempty) (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    {X : (Fin d → ℤ) → Ω → ℝ}
    (hX_loc : ∀ z ∈ S, Measurable[siteSigma B ({z} : Set (Fin d → ℤ)) L] (X z))
    (hX_meas : ∀ z, Measurable (X z))
    (hX : ∀ z ∈ S, IsBigO μ (gammaSigma σ) (X z) K)
    (h_mean : ∀ z ∈ S, ∫ ω, X z ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ z ∈ S, X z ω)
      (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst σ *
        Real.sqrt (S.card : ℝ) * K) := by
  classical
  have hne : Nonempty {x : Fin d → ℤ // x ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hindepFun :
      iIndepFun (fun i : {x : Fin d → ℤ // x ∈ S} => X i.val) μ :=
    iIndepFun_of_measurable_siteSigma (z := fun i : {x : Fin d → ℤ // x ∈ S} => i.val)
      hindep
      (fun i j hij => hsep i.val i.property j.val j.property fun h => hij (Subtype.ext h))
      fun i => hX_loc i.val i.property
  have hcard : (Finset.univ : Finset {x : Fin d → ℤ // x ∈ S}).card = S.card := by
    rw [Finset.card_univ, Fintype.card_coe]
  have hmain :=
    HCPolySupport.Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := μ) (X := fun i : {x : Fin d → ℤ // x ∈ S} => X i.val)
      (s := Finset.univ) (σ := σ) (K := K) hindepFun (fun i => hX_meas i.val)
      Finset.univ_nonempty hσ₀ hσ₂ hK (fun i _ => hX i.val i.property)
      fun i _ => h_mean i.val i.property
  rw [hcard] at hmain
  have hsum : (fun ω => ∑ i : {x : Fin d → ℤ // x ∈ S}, X i.val ω) =
      fun ω => ∑ z ∈ S, X z ω := by
    funext ω
    exact Finset.sum_coe_sort S fun z => X z ω
  rwa [hsum] at hmain

/-- **The colouring corollary, in averaged form.**

Under the ABK26 two-set finite-range hypothesis at range `3 ^ L`, the average
over a finite site set `S` of centered `O_{Γ_σ}(K)` variables localised at the
sites is `O_{Γ_σ}` at the scale
`C(σ) √(min ((3^L+1)^d) (#S)) · √(#S) / #S · K`.

The `min` in the colour count makes the estimate valid — and sharp in order —
in both the regime where `3 ^ L` is small compared with the diameter of `S`
(genuine concentration) and the regime where it is large (the deterministic
triangle inequality). -/
theorem isBigO_gammaSigma_average_of_separatedIndep [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {L : ℕ} {S : Finset (Fin d → ℤ)} {σ K : ℝ}
    (hindep : ∀ S₁ S₂ : Set (Fin d → ℤ), (∀ u ∈ S₁, ∀ v ∈ S₂, 3 ^ L < latDist u v) →
      Indep (siteSigma B S₁ L) (siteSigma B S₂ L) μ)
    (hS : S.Nonempty) (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    {X : (Fin d → ℤ) → Ω → ℝ}
    (hX_loc : ∀ z ∈ S, Measurable[siteSigma B ({z} : Set (Fin d → ℤ)) L] (X z))
    (hX_meas : ∀ z, Measurable (X z))
    (hX : ∀ z ∈ S, IsBigO μ (gammaSigma σ) (X z) K)
    (h_mean : ∀ z ∈ S, ∫ ω, X z ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => (S.card : ℝ)⁻¹ * ∑ z ∈ S, X z ω)
      (gammaTriangleConst σ * HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst σ *
        (Real.sqrt (min (((3 ^ L + 1) ^ d : ℕ) : ℝ) ((S.card : ℝ))) *
          (Real.sqrt (S.card : ℝ) / (S.card : ℝ))) * K) := by
  classical
  have hTotal : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hcolors : (S.image (siteColor L)).Nonempty := hS.image _
  have hClassCount : ∀ c ∈ S.image (siteColor L), (0 : ℝ) < ((colorClass L S c).card : ℝ) := by
    intro c hc
    exact_mod_cast (colorClass_nonempty hc).card_pos
  have hY : ∀ c ∈ S.image (siteColor L),
      IsBigO μ (gammaSigma σ) (fun ω => ∑ z ∈ colorClass L S c, X z ω)
        (HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst σ *
          Real.sqrt ((colorClass L S c).card : ℝ) * K) := by
    intro c hc
    refine isBigO_gammaSigma_sum_of_pairwise_separated hindep
      (fun u hu v hv huv => three_pow_lt_latDist_of_mem_colorClass hu hv huv)
      (colorClass_nonempty hc) hσ₀ hσ₂ hK
      (fun z hz => hX_loc z (colorClass_subset hz)) hX_meas
      (fun z hz => hX z (colorClass_subset hz))
      fun z hz => h_mean z (colorClass_subset hz)
  have hYmeas : ∀ c ∈ S.image (siteColor L),
      Measurable fun ω => ∑ z ∈ colorClass L S c, X z ω := fun c _ =>
    Finset.measurable_sum _ fun z _ => hX_meas z
  have haverage :=
    HCPolySupport.Book.Ch04.isBigO_finsetAverage_colorClassSums_gammaSigma
      (μ := μ) (colors := S.image (siteColor L))
      (Y := fun c ω => ∑ z ∈ colorClass L S c, X z ω)
      (classCount := fun c => ((colorClass L S c).card : ℝ))
      (colorCount := min (((3 ^ L + 1) ^ d : ℕ) : ℝ) ((S.card : ℝ)))
      (totalCount := (S.card : ℝ))
      (C := HCPolySupport.Book.Ch04.gammaSigmaIndependentSumConst σ) (K := K) (σ := σ)
      hσ₀ hcolors hClassCount hTotal (gammaSigmaIndependentSumConst_pos hσ₀) hK
      hY hYmeas (sum_sqrt_card_colorClass_le L S)
  have hsum : (fun ω => (S.card : ℝ)⁻¹ *
      ∑ c ∈ S.image (siteColor L), ∑ z ∈ colorClass L S c, X z ω) =
      fun ω => (S.card : ℝ)⁻¹ * ∑ z ∈ S, X z ω := by
    funext ω
    congr 1
    exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx)
      fun z => X z ω
  rwa [hsum] at haverage

end

end Algsuperdiff.Section3.Provider.Percolation

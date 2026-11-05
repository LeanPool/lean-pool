/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.PartitionAverages
public import Mathlib.Algebra.Order.Chebyshev

/-!
# ColoredAverage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Abstract coloured (finite-range) `Γ_σ` concentration

ABK26, the grid corollary stated immediately after Proposition
`p.concentration`: for centered `O_{Γ_σ}(1)` variables indexed by a `3ⁿ`-grid
inside `□_m`, independent whenever the corresponding subcubes do not touch
(finite range of dependence), the averaged sum obeys `∑_{z} X_z ≤
O_{Γ_σ}(C(σ)·3^{d(m−n)/2})`, i.e. the average gains `3^{−d(m−n)/2}`.

## What this module adds

CoarseGraining proves the *concrete* triadic instance of the corollary
(`Ch04.isBigO_gammaSigma_descendantAverage_of_unitRangeDependentLaw`), tied to
the specific triadic geometry and the *unit* range `r = 1`, and it exposes the
recombination step `Ch04.isBigO_finsetAverage_colorClassSums_gammaSigma`.  What
is missing everywhere — in CoarseGraining and in this repository, whose only
colourings are hard-wired to spatial sites `Fin d → ℤ` — is the **abstract,
index-set and palette generic** colouring wrapper: for an arbitrary finite
index set `s` and an arbitrary colouring `c : ι → κ` whose colour classes are
internally mutually independent, centered `O_{Γ_σ}(K)` summands give the
averaged `√card / card` gain.

That wrapper is `isBigO_gammaSigma_average_colored` below.  It is the reusable
core of the grid corollary at *any* range `r`: the caller supplies one
`iIndepFun` per used colour, which is exactly what a finite-range-`r` colouring
with `C(r,d)` colours delivers.  Instantiating `κ`, `c` at the triadic residue
colouring recovers CoarseGraining's concrete theorem; instantiating them at
`ZMod (r+1)` on a window of `ℤ` gives the `r`-dependent Cesàro engine.

The combinatorial `hSqrt` input is supplied here in the generality any
finite palette provides (`sum_sqrt_class_card_le`).

## Main results

* `Algsuperdiff.Probability.gammaSigmaIndependentSumConst_pos`
* `Algsuperdiff.Probability.sum_sqrt_class_card_le`
* `Algsuperdiff.Probability.isBigO_gammaSigma_average_colored`

## References

* ABK26, Proposition `p.concentration` and its grid corollary.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport.IndependentSums
open HCPolySupport.Book.Ch04 (gammaSigmaIndependentSumConst
  isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
  isBigO_finsetAverage_colorClassSums_gammaSigma)
open scoped BigOperators

noncomputable section

/-- Positivity of CoarseGraining's public constant for the centered independent-sum
`Γ_σ` concentration inequality.  CoarseGraining keeps this fact private, so it
is reproved here from CoarseGraining's public constants. -/
theorem gammaSigmaIndependentSumConst_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < gammaSigmaIndependentSumConst σ := by
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

/-- **Cauchy--Schwarz over the colour classes.** For any colouring `c : ι → κ`
of a finite set `s` by a finite palette `κ`, the sum of the square roots of the
colour-class cardinalities is at most `√(#κ) · √(#s)`.

This is the `hSqrt` hypothesis of `isBigO_gammaSigma_average_colored`, in the
form in which a residue colouring by a `Fintype` palette supplies it. -/
theorem sum_sqrt_class_card_le {ι κ : Type*} [DecidableEq κ] [Fintype κ]
    (s : Finset ι) (c : ι → κ) :
    ∑ b ∈ s.image c, Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ) ≤
      Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (s.card : ℝ) := by
  have hnn : (0 : ℝ) ≤
      ∑ b ∈ s.image c, Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  -- the colour classes partition `s`
  have hsum_card :
      ∑ b ∈ s.image c, ((s.filter (fun j => c j = b)).card : ℝ) = (s.card : ℝ) := by
    have h : s.card = ∑ b ∈ s.image c, (s.filter (fun j => c j = b)).card :=
      Finset.card_eq_sum_card_image c s
    exact_mod_cast h.symm
  have hsq :
      ∑ b ∈ s.image c, (Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ)) ^ 2
        = (s.card : ℝ) := by
    rw [← hsum_card]
    exact Finset.sum_congr rfl (fun _ _ => Real.sq_sqrt (Nat.cast_nonneg _))
  have hCheb := sq_sum_le_card_mul_sum_sq (s := s.image c)
    (f := fun b => Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ))
  rw [hsq] at hCheb
  have htcard : (((s.image c).card : ℕ) : ℝ) ≤ (Fintype.card κ : ℝ) := by
    have h := Finset.card_le_univ (s.image c)
    exact_mod_cast h
  have hkey :
      (∑ b ∈ s.image c, Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ)) ^ 2
        ≤ (Fintype.card κ : ℝ) * (s.card : ℝ) :=
    hCheb.trans (mul_le_mul_of_nonneg_right htcard (Nat.cast_nonneg _))
  calc ∑ b ∈ s.image c, Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ)
      = Real.sqrt
          ((∑ b ∈ s.image c, Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card κ : ℝ) * (s.card : ℝ)) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (s.card : ℝ) :=
        Real.sqrt_mul (Nat.cast_nonneg _) _

/-- **Coloured (finite-range) concentration.** Let `s` be a finite index set and
`c : ι → κ` a colouring whose colour classes `{i ∈ s | c i = b}` are internally
mutually independent (hypothesis `h_indep`, one `iIndepFun` per used colour —
this is precisely the finite-range-of-dependence colouring with `C(r,d)`
colours). If each summand is centered with `X i ≤ O_{Γ_σ}(K)`, and the
colour-class square roots obey the combinatorial bound `hSqrt` (with
`colorCount ≥ #colours`), then the average obeys

`(1/#s)∑_{i∈s} X_i ≤ O_{Γ_σ}(gammaTriangleConst σ · gammaSigmaIndependentSumConst σ ·
  (√colorCount · √#s / #s) · K)`.

Instantiating `s` at a triadic descendant set, `c` at the residue colouring and
`colorCount` at the residue-period power recovers the paper's `3^{−d(m−n)/2}`
grid corollary. -/
theorem isBigO_gammaSigma_average_colored
    {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [DecidableEq κ]
    (s : Finset ι) (c : ι → κ) {X : ι → Ω → ℝ} {σ K colorCount : ℝ}
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (h_indep : ∀ b ∈ s.image c,
      ProbabilityTheory.iIndepFun
        (fun (i : {i // i ∈ s.filter (fun j => c j = b)}) => X i.1) P)
    (h_meas : ∀ i ∈ s, Measurable (X i))
    (hX : ∀ i ∈ s, IsBigO P (gammaSigma σ) (X i) K)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂P = 0)
    (hSqrt :
      ∑ b ∈ s.image c, Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ) ≤
        Real.sqrt colorCount * Real.sqrt (s.card : ℝ)) :
    IsBigO P (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (gammaTriangleConst σ * gammaSigmaIndependentSumConst σ *
        (Real.sqrt colorCount * (Real.sqrt (s.card : ℝ) / (s.card : ℝ))) * K) := by
  by_cases hs : s.Nonempty
  · -- Per-colour-class concentration via the subtype/`attach` trick.
    have hY : ∀ b ∈ s.image c,
        IsBigO P (gammaSigma σ)
          (fun ω => ∑ i ∈ s.filter (fun j => c j = b), X i ω)
          (gammaSigmaIndependentSumConst σ *
            Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ) * K) := by
      intro b hb
      obtain ⟨i₀, hi₀, hci₀⟩ := Finset.mem_image.mp hb
      have hne : (s.filter (fun j => c j = b)).attach.Nonempty :=
        (Finset.attach_nonempty_iff).mpr ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hci₀⟩⟩
      have hsum :=
        isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
          (μ := P) (X := fun i : {i // i ∈ s.filter (fun j => c j = b)} => X i.1)
          (s := (s.filter (fun j => c j = b)).attach) (σ := σ) (K := K)
          (h_indep b hb)
          (fun i => h_meas i.1 (Finset.mem_of_mem_filter i.1 i.2))
          hne hσ₀ hσ₂ hK
          (fun i _ => hX i.1 (Finset.mem_of_mem_filter i.1 i.2))
          (fun i _ => h_mean i.1 (Finset.mem_of_mem_filter i.1 i.2))
      have hfun :
          (fun ω => ∑ x ∈ (s.filter (fun j => c j = b)).attach, X (↑x) ω)
            = (fun ω => ∑ i ∈ s.filter (fun j => c j = b), X i ω) := by
        funext ω
        exact Finset.sum_attach (s := s.filter (fun j => c j = b)) (f := fun i => X i ω)
      have hcard :
          Real.sqrt ((s.filter (fun j => c j = b)).attach.card : ℝ)
            = Real.sqrt ((s.filter (fun j => c j = b)).card : ℝ) := by
        rw [Finset.card_attach]
      rw [hfun, hcard] at hsum
      exact hsum
    have hYmeas : ∀ b ∈ s.image c,
        Measurable (fun ω => ∑ i ∈ s.filter (fun j => c j = b), X i ω) := by
      intro b _hb
      exact Finset.measurable_sum _
        (fun i hi => h_meas i (Finset.mem_of_mem_filter i hi))
    have hClassCount : ∀ b ∈ s.image c,
        0 < ((s.filter (fun j => c j = b)).card : ℝ) := by
      intro b hb
      obtain ⟨i₀, hi₀, hci₀⟩ := Finset.mem_image.mp hb
      have hne : (s.filter (fun j => c j = b)).Nonempty :=
        ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hci₀⟩⟩
      exact_mod_cast hne.card_pos
    -- Aggregate the colour-class estimates and divide by the total.
    have haverage :=
      isBigO_finsetAverage_colorClassSums_gammaSigma
        (μ := P) (colors := s.image c)
        (Y := fun b ω => ∑ i ∈ s.filter (fun j => c j = b), X i ω)
        (classCount := fun b => ((s.filter (fun j => c j = b)).card : ℝ))
        (colorCount := colorCount) (totalCount := (s.card : ℝ))
        (C := gammaSigmaIndependentSumConst σ) (K := K) (σ := σ)
        hσ₀ (hs.image c) hClassCount (by exact_mod_cast hs.card_pos)
        (gammaSigmaIndependentSumConst_pos hσ₀) hK hY hYmeas hSqrt
    -- `∑_b ∑_{i : c i = b} X_i = ∑_{i ∈ s} X_i` (partition into colour classes).
    have hfun_eq :
        (fun ω => ((s.card : ℝ)⁻¹) *
            ∑ b ∈ s.image c, ∑ i ∈ s.filter (fun j => c j = b), X i ω) =
          (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) := by
      funext ω
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem c hi) (fun i => X i ω)
    rw [← hfun_eq]
    exact haverage
  · -- Empty index set: the average and the scale both vanish.
    have hcard0 : (s.card : ℝ) = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hs]; simp
    rw [isBigO_gammaSigma_iff]
    intro t ht
    have hscale0 :
        gammaTriangleConst σ * gammaSigmaIndependentSumConst σ *
          (Real.sqrt colorCount * (Real.sqrt (s.card : ℝ) / (s.card : ℝ))) * K = 0 := by
      rw [hcard0]; simp
    rw [hscale0, zero_mul]
    have hempty :
        absTailEvent (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) (0 : ℝ)
          = (∅ : Set Ω) := by
      ext ω
      rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp [absTailEvent]
    rw [hempty]
    have h0 : P.real (∅ : Set Ω) = 0 := by simp
    rw [h0]
    exact (Real.exp_pos _).le

end

end Algsuperdiff.Probability

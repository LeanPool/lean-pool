/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormClause
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamGaugeCongruence
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxFreeCcg

/-!
# HomSpineSupFormMonotone

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The sup-form clause: the three transport lemmas of the datum instantiation

## What this file supplies

The producer route (`HomSpineDepthBandInput` → `HomSpineSupFormClauseAt`)
delivers `CoarseGrainingSupMultiscale` at ITS OWN slots: the produced constant
`√d·CA·C(p,d)`, the error order `s₁ = s/8`, and the pinned representative
`Fgrad = ∇u − ∇v`.  The lane's carrier
(`HomSeamSupClauseCcgFree.RecutCoreSupplyFluxSupClauseAt`) asks for the clause
at the slot triple `(CcgF M, s/4, ∀ G agreeing on the open cube)`.  Three
transports close the gap, each in the favorable direction:

* **`Ccg` monotonicity** (`mono_ccg`).  The clause constant occurs only inside
  `coarseGrainingFinitePRHS`, which is monotone UP in `Ccg` at the clause's own
  sign data (`HomSeamFluxFreeCcg.coarseGrainingFinitePRHS_mono_ccg`); the
  needed `0 ≤ S` is forced by the clause's own energy premise.  So the produced
  clause may be raised to `max (recutPinnedCcgFlux d p) (produced M)`.

* **The `s₁`-slot decoupling** (`mono_s1`).  `s₁` occurs in the clause ONLY
  through the weight `s − s₁` of `coarseGrainingEnergyPartial` (verified
  against the definition: neither `negBesovSupPartialNorm` nor
  `coarseGrainingFinitePRHS` mentions `s₁`).  The energy partial is ANTITONE in
  its weight (`coarseGrainingEnergyPartial_anti_weight`: the weights
  `3^{-(wp)i}` decrease in `w` on nonnegative cell data), and `s/8 ≤ s/4` means
  `s − s/8 ≥ s − s/4`; hence the clause at `s₁ = s/8` IMPLIES the clause at
  `s₁ = s/4`: any `S` dominating the `s/4`-weighted partials dominates the
  `s/8`-weighted ones.

* **The `Fgrad` congruence** (`congr_grad_of_eqOn`).  `negBesovSupPartialNorm`
  is a `Finset.sup'` of `negBesovLpDepthSeminorm`, and the
  `HomSeamGaugeCongruence.negBesovLpDepthSeminorm_congr_of_eqOn` makes each
  depth term blind to the representative on the open cube; `Finset.sup'_congr`
  lifts this to the sup, so the clause at the pinned representative serves the
  carrier's `∀ G` slot.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The energy partial: nonnegativity and weight antitonicity -/

/-- The printed energy partial is nonnegative on nonnegative cell data. -/
theorem coarseGrainingEnergyPartial_nonneg (Q : TriadicCube d) (p w : ℝ) (jn N : ℕ)
    {Gen : TriadicCube d → ℝ} (hGen0 : ∀ R, 0 ≤ Gen R) :
    0 ≤ coarseGrainingEnergyPartial Q p w jn N Gen := by
  rw [coarseGrainingEnergyPartial_def]
  exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (descendantsAverage_nonneg _ _ _ fun R _ => Real.rpow_nonneg (hGen0 R) _)) _

/-- **The energy partial is ANTITONE in its weight** on nonnegative cell data:
the depth weights `3^{-(wp)i}` decrease in `w`. -/
theorem coarseGrainingEnergyPartial_anti_weight (Q : TriadicCube d) {p w w' : ℝ}
    (hp : 0 ≤ p) (hww' : w ≤ w') (jn N : ℕ) {Gen : TriadicCube d → ℝ}
    (hGen0 : ∀ R, 0 ≤ Gen R) :
    coarseGrainingEnergyPartial Q p w' jn N Gen ≤
      coarseGrainingEnergyPartial Q p w jn N Gen := by
  rw [coarseGrainingEnergyPartial_def, coarseGrainingEnergyPartial_def]
  refine Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (descendantsAverage_nonneg _ _ _ fun R _ => Real.rpow_nonneg (hGen0 R) _))
    (Finset.sum_le_sum fun i _ => ?_) (one_div_nonneg.mpr hp)
  refine mul_le_mul_of_nonneg_right ?_
    (descendantsAverage_nonneg _ _ _ fun R _ => Real.rpow_nonneg (hGen0 R) _)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have h1 : w * p ≤ w' * p := mul_le_mul_of_nonneg_right hww' hp
  have h2 : -(w' * p) ≤ -(w * p) := neg_le_neg h1
  exact mul_le_mul_of_nonneg_right h2 hi

/-! ## 2. The `s₁`-slot decoupling -/

/-- **The sup-form clause moves UP in the `s₁` slot.**  `s₁` occurs only through
the weight `s − s₁`, and lowering the weight only strengthens the energy
premise; the conclusion never sees `s₁`. -/
theorem CoarseGrainingSupMultiscale.mono_s1 {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s1' s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d} (hp : 0 ≤ p) (hGen0 : ∀ R, 0 ≤ Gen R)
    (hs1 : s1 ≤ s1')
    (h : CoarseGrainingSupMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux) :
    CoarseGrainingSupMultiscale Q jn Ccg s s1' s2 p sigma E1 E2 Dg Gen Fgrad Fflux := by
  intro S hS N
  refine h S (fun N' => le_trans ?_ (hS N')) N
  exact coarseGrainingEnergyPartial_anti_weight Q hp
    (by linarith only [hs1] : s - s1' ≤ s - s1) jn N' hGen0

/-! ## 3. The `Ccg` monotonicity -/

/-- **The sup-form clause moves UP in the clause constant**, at the sign data
the lane's slots carry; the needed `0 ≤ S` is forced by the clause's own
energy premise. -/
theorem CoarseGrainingSupMultiscale.mono_ccg {Q : TriadicCube d} {jn : ℕ}
    {Ccg Ccg' s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d} (hCcg : Ccg ≤ Ccg') (hs : 0 < s) (hss2 : s < s2)
    (hE1 : 0 ≤ E1) (hDg : 0 ≤ Dg) (hGen0 : ∀ R, 0 ≤ Gen R)
    (h : CoarseGrainingSupMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux) :
    CoarseGrainingSupMultiscale Q jn Ccg' s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux := by
  intro S hS N
  have hS0 : (0 : ℝ) ≤ S := by
    have hge := hS 0
    have h0 : (0 : ℝ) ≤ coarseGrainingEnergyPartial Q p (s - s1) jn 0 Gen :=
      coarseGrainingEnergyPartial_nonneg Q p (s - s1) jn 0 hGen0
    linarith only [hge, h0]
  exact le_trans (h S hS N)
    (coarseGrainingFinitePRHS_mono_ccg (Q.scale - (jn : ℤ)) hCcg hs hss2 hE1 hDg hS0)

/-! ## 4. The `Fgrad` congruence -/

/-- **The sup-over-depths partial gauge is blind to the representative** on the
open cube: the `Finset.sup'` lift of the depth congruence. -/
theorem negBesovSupPartialNorm_congr_of_eqOn (Q : TriadicCube d) (s p : ℝ) (N : ℕ)
    {G G' : Vec d → Vec d} (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    negBesovSupPartialNorm Q s p N G = negBesovSupPartialNorm Q s p N G' := by
  rw [negBesovSupPartialNorm_def, negBesovSupPartialNorm_def]
  exact Finset.sup'_congr Finset.nonempty_range_add_one rfl fun j _ =>
    negBesovLpDepthSeminorm_congr_of_eqOn Q s p j hG

/-- **The sup-form clause transports along any representative** agreeing on the
open cube — the shape the carrier's `∀ G` slot asks for. -/
theorem CoarseGrainingSupMultiscale.congr_grad_of_eqOn {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {G G' Fflux : Vec d → Vec d}
    (h : CoarseGrainingSupMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen G Fflux)
    (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    CoarseGrainingSupMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen G' Fflux := by
  intro S hS N
  have hkey := h S hS N
  rwa [negBesovSupPartialNorm_congr_of_eqOn Q s p N hG] at hkey

end

end Algsuperdiff.Section4.Provider.Homogenization

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.CollarMass
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionKtotEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CollarLayerEnvelope

/-!
# ConclusionAssemblyFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The concluding assembly of `p.bfA.multiscalebound`

`ConclusionCompetitor.toReal_tsum_simplexPartition_cutoff_two_leg_le_payload`
is the Step-3 payload at the two cell functionals `goodCellForm`,
`collarCellForm`.  Four groups of binders were still the caller's when it
proved: the good leg (`hgood`), the collar leg (`hcol`), the four mass data
(`hmassgood`, `hmasscol`, `hMass`, `hBadMass`, `hBadDens`) and the parameter
window.  `ConclusionKtotEnvelope` supplies the local `hgood` antecedent.  This
module reduces `hcol` to the two explicit slope-envelope inputs below,
discharges the `F` input, instantiates the mass data using the proved local
`CollarMass` route, and runs the composition.  Its remaining `G` input is local
to this module's theorem and is discharged by the later
`ConclusionCompose`/`ConclusionRoot` route.

## 1. The collar leg

`ConclusionCompetitor.collarCellForm_le_stepOneLayerMajorant_ae` prices one
collar cell by `4 Cgrad² 3^{2b(k+h_k)}` times the Step-1 majorant `M`, and
`ConclusionKtot.stepOneLayerMajorant_le_ktotConst_mul` prices `M` by `ktotConst
. 3^{2γ(k+h_k)}`.  Composing them
(`collarCellForm_le_ktotConst_mul_layerScale_ae`) and feeding the layer
envelope of `ConclusionData` through `ConclusionKtotEnvelope`'s absorption
(`collarCellForm_le_collarEnvelopeConst_mul_layerQuantity_ae`) gives the
layer-free constant `collarEnvelopeConst` at the exponent

```
2b + 2γ + ε   (γ = M.gamma, ε the absorption exponent),
```

i.e. the collar leg's honest per-cell growth is `3^{(2b+2γ+ε)(k+h_k)}`, NOT
`3^{2b(k+h_k)}`.  This module's theorem still exposes `hGv`, the `G`-leg
envelope at `(∇·D̂_q)(𝔰)`, and applies it at `Gv := competitorDivergence` in
the downstream binder-drop composition.  Thus `hGv` is an explicit premise of
this local theorem, not a currently open project obligation and not evidence
that this module closes a source node.

## 2. Why the payload's `b` is not the geometry's `b`

The payload's `hcol` slot is `Ccol . 3^{2b . layerQuantity b hs k₀ n}`.
Section 1 produces `3^{(2b+2γ+ε)(k+h_k)}`.  The manuscript's own Step 3 also
multiplies `e.bounds.on.slopes.when.bad` by `e.good.simplex.consequence`, so
the extra `3^{γ(k+h_k)}` is genuinely there and is NOT an artefact of this
repository; `ConclusionAssembly.layerContrib` simply carries the collar leg at
the bare `3^{2b(k+h_k)}`, i.e. it expects the caller to have already absorbed
the Step-1 growth into its own `b`.

The absorption is legitimate because `toReal_tsum_simplexPartition_..._payload`
binds `hn` and `(b, hs, k₀)` independently: nothing there forces
`hn = whitneyScaleSeq b hs k₀`.  So the assembly runs at

```
hn := whitneyScale M m E b k₀ ω = whitneyScaleSeq b h_hat_sep k₀   (the geometry),
payload parameters := (β, h_hat_sep + k₀, kp)   with   2b + 2γ + ε ≤ 2β ,
```

and `layerQuantity_le_of_le` supplies `layerQuantity b h_hat_sep k₀ n ≤
layerQuantity β (h_hat_sep+k₀) kp n` (the ceiling `⌈b(1-b)^{-1}n⌉` is monotone in
`b`, and the offsets are ordered).  Both legs then fit their slots: the good leg
because its exponent `γ` is nonnegative and the layer quantity only grew; the
collar leg because `2b+2γ+ε ≤ 2β` and the layer quantity only grew.

## 3. The mass data

`hMass`/`hmassgood` are `LayerMass.sum_cubeMassRatio_whitneyLayer_le` at
`Cmass = 6d` (`assemblyMass`).  For the bad sequence the module takes the
feasible route `CollarMass` records:

```
Bad j := min ( collarMassCap ,  6d . 3^{-j} ) ,
collarMassCap := 9 . 99^d ( exp(-c(d) E^{-2} γ^{-1}) + 3^{-(h_hat_sep+k₀)/2} )
```

(`assemblyBad`).  The `min`'s right branch is `hBadMass` and is available
because `collarLayer ⊆ 𝒲(□_m,n)`; the left branch is
`CollarMass.sum_cubeMassRatio_collarLayer_le_layerQuantity` read at
`layerQuantity b h_hat_sep k₀ n ≥ h_hat_sep + k₀`
(`sum_cubeMassRatio_collarLayer_le_assemblyBad`).  `hBadDens` is then the T
`Bad j ≤ ε` at `ε := collarMassCap` --- the whole `3^{-(j+h_j)/2}` decay is
spent inside the constant, which is exactly what
`ConclusionAssembly.layerContrib_le` consumes anyway (its only use of
`hBadDens` is through `k₀ ≤ layerQuantity`, i.e. through the constant).  The
`(hs, k₀)` shift that `CollarMass` leaves to its consumer is therefore implemented here as
the *payload* offset `hs := h_hat_sep + k₀`, and the `9.99^d` dimensional factor is
paid once, inside `ε`, by the single arithmetic gate

```
9 . 99^d ( exp(-c(d) E^{-2} γ^{-1}) + 3^{-k₀/2} )  ≤  exp(-kp)          (GATE)
```

which is the binder `hcap` and is discharged in
`Provider/Multiscale/ConclusionFeasibility.lean`.

## 4. What this local assembly delivers

`toReal_tsum_simplexPartition_cutoff_two_leg_le_payload_assembled_ae` is, almost
surely and on the scale-separation event, the Step-3 payload

```
( ∑'_{𝔰 ∈ SW(□_m)} ofReal(|𝔰|/|□_m| g_good 𝔰) + ofReal(|𝔰|/|□_m| g_col 𝔰) )^{ℝ}
  ≤ layerSumConst β (2γ+ε) kp Ktot Ccol (6d)
      . 3^{(2γ+ε)(h_hat_sep+k₀)} ( 1 + 3^{2β(h_hat_sep+k₀)} exp(-kp/36) )
```

at the concrete competitor `(∇ℓ̂_p, G)` and the concrete loads `(σ_i^{-1/2}p,
σ_i^{1/2}q)`, with `Ktot`, `Ccol` explicit and layer-free.  The right-hand
side is the manuscript's own first Step-3 display, which is written there at
`3^{γ(h_hat_sep+k_0)}(1 + 3^{2b(h_hat_sep+k_0)}(...))` before the `k_0` collapse.

This module itself does not perform the following three downstream steps:

* discharge of its local `hGv` premise (now performed downstream using
  `CollarLayerEnvelopeG`);
* the eight affine A clauses of `ConclusionCompetitor.sum_of_a_decomp_cutoff`
  (`l.piecewise.affine.approx`), which are what turn this payload into a bound
  on `|(p,q).𝐀_L(□_m)(p,q)|` --- this module does NOT invoke
  `sum_of_a_decomp_cutoff` (the later superposed route supplies these clauses);
* the real-valued join of `sum_of_a_decomp_cutoff` with the payload, i.e. the
  finiteness of the intermediate `[0,∞]` sum (performed in `ConclusionRoot`).

## What is *not* proved

* **No local proof of the `G`-leg**: the theorem below keeps it as a hypothesis;
  the downstream repository supplies it as described above.
* **No affine A discharge, no glued competitor, no `H¹` statement.**
* **No claim that `Ccol` is the manuscript's `C`**: `collarEnvelopeConst` is the
  honest output of the route above (`4 Cgrad² ktotConst`), nothing is optimized.
* **No new probabilistic input**: the only measure-theoretic steps are
  `ae_all_iff` over the countable `h_hat_sep`-values and the a.e. statements
  already proved.

## Main definitions

* `Algsuperdiff.Section3.Provider.Multiscale.collarEnvelopeConst`
* `Algsuperdiff.Section3.Provider.Multiscale.collarMassCap`
* `Algsuperdiff.Section3.Provider.Multiscale.assemblyMass`
* `Algsuperdiff.Section3.Provider.Multiscale.assemblyBad`

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.layerQuantity_le_of_le`
* `Algsuperdiff.Section3.Provider.Multiscale.collarCellForm_le_ktotConst_mul_layerScale_ae`
* `Algsuperdiff.Section3.Provider.Multiscale.`
  `collarCellForm_le_collarEnvelopeConst_mul_layerQuantity_ae`
* `Algsuperdiff.Section3.Provider.Multiscale.sum_cubeMassRatio_collarLayer_le_assemblyBad`

## References

* ABK26, `p.bfA.multiscalebound` Step 3 (the payload display),
  `e.bounds.on.slopes.when.bad`, `e.sum-of-a-decomp`,
  `e.good.simplex.consequence`, `l.bad.cubes.density`, `e.hn.def`, `e.hn.gap`,
  `l.piecewise.affine.approx`, `r.gradient.bound.simplified`.
* `Provider/Multiscale/ConclusionCompetitor.lean` (the payload and the two cell
  functionals), `Provider/Multiscale/ConclusionKtotEnvelope.lean` (the good
  leg), `Provider/Multiscale/CollarMass.lean` (the collar mass),
  `Provider/Multiscale/LayerMass.lean` (the layer mass),
  `Provider/Affine/CollarLayerEnvelope.lean` (the `F`-leg envelope).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Affine

noncomputable section

variable {d : ℕ}

/-! ## The layer quantity is monotone in the parameter and in the offset -/

/-- **`e.hn.def` is monotone in `b` and in the offset `h_hat_sep + k₀`.**  The
scale profile is `h_n = ⌈b(1-b)^{-1} n⌉ + hs + k₀` and `b ↦ b(1-b)^{-1}` is
increasing on `[0,1)`, so a larger parameter and a larger offset give a larger
layer quantity `n + h_n`.  This is what lets the assembly run the geometry at
the manuscript's `b` while pricing the payload at a larger `β` (see the module
docstring, section 2). -/
theorem layerQuantity_le_of_le {b β : ℝ} (hbb : b ≤ β) (hb1 : β < 1)
    {hs k₀ hs' k₀' : ℕ} (hshift : hs + k₀ ≤ hs' + k₀') (n : ℕ) :
    layerQuantity b hs k₀ n ≤ layerQuantity β hs' k₀' n := by
  have hb1' : b < 1 := lt_of_le_of_lt hbb hb1
  have h1 : (0 : ℝ) < 1 - b := by linarith
  have h2 : (0 : ℝ) < 1 - β := by linarith
  have hne1 : (1 : ℝ) - b ≠ 0 := ne_of_gt h1
  have hne2 : (1 : ℝ) - β ≠ 0 := ne_of_gt h2
  have hslope : b * (1 - b)⁻¹ ≤ β * (1 - β)⁻¹ := by
    rw [← sub_nonneg]
    have hid : β * (1 - β)⁻¹ - b * (1 - b)⁻¹ = (β - b) * ((1 - β)⁻¹ * (1 - b)⁻¹) := by
      field_simp
      ring
    rw [hid]
    exact mul_nonneg (by linarith)
      (mul_nonneg (inv_nonneg.2 h2.le) (inv_nonneg.2 h1.le))
  have hceil : whitneyScaleSeq b hs k₀ n ≤ whitneyScaleSeq β hs' k₀' n := by
    have hmul : b * (1 - b)⁻¹ * (n : ℝ) ≤ β * (1 - β)⁻¹ * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg n)
    have := Nat.ceil_le_ceil hmul
    unfold whitneyScaleSeq
    omega
  have hcast : (whitneyScaleSeq b hs k₀ n : ℝ) ≤ (whitneyScaleSeq β hs' k₀' n : ℝ) := by
    exact_mod_cast hceil
  rw [layerQuantity, layerQuantity]
  linarith

/-! ## The collar leg, priced against a layer-dependent gauge bound -/

/-- **The collar twin of
`ConclusionKtotEnvelope.goodCellForm_le_ktotConst_mul_layerScale_ae`.**
`ConclusionCompetitor.collarCellForm_le_stepOneLayerMajorant_ae` composed with
`ConclusionKtot.stepOneLayerMajorant_le_ktotConst_mul`: on a bad cube the
indicator `1_{¬𝓑}` kills the term, and on a good cube the Step-1 majorant is
priced by the layer constant at the cube's own layer gauge bound `Sc n`. -/
theorem collarCellForm_le_ktotConst_mul_layerScale_ae (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) (hn : ℕ → ℕ)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0) {L : ℤ} (hmL : m ≤ L) (p q : Vec d)
    {b Cgrad : ℝ} (hCgrad : 1 ≤ Cgrad) (hb : 0 ≤ b)
    {Cw : ℝ} {Sc : ℕ → ℝ} (hSc0 : ∀ n : ℕ, 0 ≤ Sc n) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
          Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) ≤ Cw) →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
          cubeSupBound Q Q.scale L omega.1 ≤ Sc n) →
      ∀ Fv Gv : KuhnCell d → Vec d,
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
            ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
              vecNormSq (Fv T - p) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq p) →
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
            ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
              vecNormSq (Gv T - q) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq q) →
        ∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
            collarCellForm M m hn L omega
                (fun U => (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv U)
                (fun U => Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U) T ≤
              4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
                (ktotConst M m i Cw (max (oscThreshold M m) (Sc n)) p q *
                  (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (hn n : ℝ)))) := by
  classical
  filter_upwards [collarCellForm_le_stepOneLayerMajorant_ae hd M hS m hn hmi hi hCgrad hb]
    with omega hbase hCw hSwave Fv Gv hFv hGv n Q hQ T hT
  have hscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) := scale_eq_of_mem_whitneyLayer hQ
  have hQm : Q.scale ≤ m := by rw [hscale]; omega
  have hQL : Q.scale ≤ L := le_trans hQm hmL
  have hCw0 : (0 : ℝ) ≤ Cw :=
    le_trans (multiscaleDescendantWeight_nonneg Q (simplexScale m hn n) (1 / 4)) (hCw n Q hQ)
  have hSup0 : (0 : ℝ) ≤ max (oscThreshold M m) (Sc n) :=
    le_trans (hSc0 n) (le_max_right _ _)
  have hamp0 : (0 : ℝ) ≤ 4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  by_cases hbad : Q ∈ badFamily M m hn omega
  · have hcube : whitneyCubeOf m hn T = Q :=
      whitneyCubeOf_of_mem_whitneySimplexCells hQ hT
    have hzero : notBadIndicator M m hn omega T = 0 :=
      notBadIndicator_of_bad (by rw [hcube]; exact hbad)
    rw [collarCellForm, hzero, mul_zero, zero_mul]
    exact mul_nonneg hamp0
      (mul_nonneg (ktotConst_nonneg hd M m i hCw0 _ p q) (Real.rpow_nonneg (by norm_num) _))
  · have hnb : omega ∉ BadEvents.bad M Q := fun h => hbad ⟨⟨n, hQ⟩, h⟩
    have hosc : omega ∉ badOsc M Q := fun h => hnb (Or.inl h)
    have hw : (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ≤
        max (oscThreshold M m) (Sc n) :=
      le_trans (w1Infinity_incrementUnitCube₂_le_max_oscThreshold M Q hosc hQL)
        (max_le_max (oscThreshold_mono M hQm) (hSwave n Q hQ))
    refine le_trans
      (hbase n Q hQ L hQL T hT Fv Gv p q (hFv n Q hQ T hT) (hGv n Q hQ T hT)) ?_
    exact mul_le_mul_of_nonneg_left
      (stepOneLayerMajorant_le_ktotConst_mul hd M m hn n i L omega hQ p q (hCw n Q hQ)
        hSup0 hw) hamp0

/-! ## The collar leg at the layer envelope -/

/-- **The collar leg's layer-free constant**: the factor `4 Cgrad²` times the
layer-free `ktotConst` of `ConclusionKtotEnvelope`. -/
def collarEnvelopeConst (M : ABKModel d) (m i L : ℤ) (eps t Cgrad : ℝ) (p q : Vec d) : ℝ :=
  4 * Cgrad ^ 2 * ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q

theorem collarEnvelopeConst_nonneg (hd : 2 ≤ d) (M : ABKModel d) (m i L : ℤ)
    (eps t Cgrad : ℝ) (p q : Vec d) :
    0 ≤ collarEnvelopeConst M m i L eps t Cgrad p q :=
  mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (ktotConst_nonneg hd M m i (by norm_num) _ p q)

/-- **The collar leg's per-cell bound at the honest layer envelope.**  The collar
twin of
`ConclusionKtotEnvelope.goodCellForm_le_ktotEnvelopeConst_mul_layerQuantity_ae`:
under the same envelope antecedent and at the same descendant weight `Cw = 3`,
the collar cell functional is at most a layer-free constant times
`3^{(2b + 2γ + ε)(k+h_k)}`. -/
theorem collarCellForm_le_collarEnvelopeConst_mul_layerQuantity_ae (hd : 2 ≤ d)
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hs k₀ : ℕ) {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0)
    {L : ℤ} (hmL : m ≤ L) (p q : Vec d) {eps : ℝ} (heps : 0 < eps) {t : ℝ}
    (ht0 : 0 ≤ t) {Cgrad : ℝ} (hCgrad : 1 ≤ Cgrad) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
          cubeSupBound Q Q.scale L omega.1 ≤
            whitneyWaveLayerScale M m (whitneyScaleSeq b hs k₀) n L * t) →
      ∀ Fv Gv : KuhnCell d → Vec d,
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
            ∀ T ∈ whitneySimplexCells (d := d) m (whitneyScaleSeq b hs k₀) n Q,
              vecNormSq (Fv T - p) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (whitneyScaleSeq b hs k₀ n : ℝ)))) *
                  vecNormSq p) →
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
            ∀ T ∈ whitneySimplexCells (d := d) m (whitneyScaleSeq b hs k₀) n Q,
              vecNormSq (Gv T - q) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (whitneyScaleSeq b hs k₀ n : ℝ)))) *
                  vecNormSq q) →
        ∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScaleSeq b hs k₀) n,
          ∀ T ∈ whitneySimplexCells (d := d) m (whitneyScaleSeq b hs k₀) n Q,
            collarCellForm M m (whitneyScaleSeq b hs k₀) L omega
                (fun U => (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv U)
                (fun U => Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U)
                T ≤
              collarEnvelopeConst M m i L eps t Cgrad p q *
                (3 : ℝ) ^ ((2 * b + 2 * M.gamma + eps) * layerQuantity b hs k₀ n) := by
  have hSc0 : ∀ n : ℕ, 0 ≤ whitneyWaveLayerScale M m (whitneyScaleSeq b hs k₀) n L * t :=
    fun n => mul_nonneg
      (whitneyWaveLayerScale_nonneg hd M m (whitneyScaleSeq b hs k₀) n L) ht0
  filter_upwards [collarCellForm_le_ktotConst_mul_layerScale_ae hd M hS m
    (whitneyScaleSeq b hs k₀) hmi hi hmL p q hCgrad hb0.le (Cw := 3) hSc0]
    with omega hbase hSwave Fv Gv hFv hGv n Q hQ T hT
  have hstep := hbase (multiscaleDescendantWeight_whitneyScaleSeq_le_three hb0 hb hs k₀ m)
    hSwave Fv Gv hFv hGv n Q hQ T hT
  set Lq : ℝ := (n : ℝ) + ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ) with hLq
  have hkR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hhR : (0 : ℝ) ≤ ((whitneyScaleSeq b hs k₀ n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLq0 : (0 : ℝ) ≤ Lq := by rw [hLq]; linarith
  have hE : (1 : ℝ) ≤ (3 : ℝ) ^ (eps * Lq) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg heps.le hLq0)
  have hsq := sq_max_oscThreshold_whitneyWaveLayerScale_le M m (whitneyScaleSeq b hs k₀) n L
    (eps := eps) (t := t) heps
  have hconst := ktotConst_le_mul hd M m i (Cw := 3) (by norm_num) hE hsq p q
  have hamp0 : (0 : ℝ) ≤ 4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * Lq))) :=
    mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hZ : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * Lq) := Real.rpow_nonneg (by norm_num) _
  have hmerge : (3 : ℝ) ^ (2 * (b * Lq)) *
      ((3 : ℝ) ^ (eps * Lq) * (3 : ℝ) ^ (2 * M.gamma * Lq))
      = (3 : ℝ) ^ ((2 * b + 2 * M.gamma + eps) * layerQuantity b hs k₀ n) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num), layerQuantity, ← hLq]
    congr 1
    ring
  calc collarCellForm M m (whitneyScaleSeq b hs k₀) L omega
        (fun U => (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv U)
        (fun U => Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U) T
      ≤ 4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * Lq))) *
          (ktotConst M m i 3
              (max (oscThreshold M m)
                (whitneyWaveLayerScale M m (whitneyScaleSeq b hs k₀) n L * t)) p q *
            (3 : ℝ) ^ (2 * M.gamma * Lq)) := hstep
    _ ≤ 4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * Lq))) *
          (ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q * (3 : ℝ) ^ (eps * Lq) *
            (3 : ℝ) ^ (2 * M.gamma * Lq)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hconst hZ) hamp0
    _ = collarEnvelopeConst M m i L eps t Cgrad p q *
          ((3 : ℝ) ^ (2 * (b * Lq)) *
            ((3 : ℝ) ^ (eps * Lq) * (3 : ℝ) ^ (2 * M.gamma * Lq))) := by
        rw [collarEnvelopeConst]; ring
    _ = collarEnvelopeConst M m i L eps t Cgrad p q *
          (3 : ℝ) ^ ((2 * b + 2 * M.gamma + eps) * layerQuantity b hs k₀ n) := by rw [hmerge]

/-! ## The four mass data -/

/-- **The density cap of the collar mass**, at the constant `9 . 99^d` of
`CollarMass.sum_cubeMassRatio_collarLayer_le_layerQuantity` read at the bottom
layer `k + h_k ≥ h_hat_sep + k₀`.  It is the payload's `ε`. -/
def collarMassCap (M : ABKModel d) (Ev : ℝ) (hs k₀ : ℕ) : ℝ :=
  9 * (99 : ℝ) ^ d *
    (Real.exp (-(Percolation.siteRateBase d / 2 * (Ev⁻¹ ^ 2 * M.gamma⁻¹))) +
      (3 : ℝ) ^ (-(((hs : ℝ) + (k₀ : ℝ)) / 2)))

theorem collarMassCap_nonneg (M : ABKModel d) (Ev : ℝ) (hs k₀ : ℕ) :
    0 ≤ collarMassCap M Ev hs k₀ := by
  have h1 : (0 : ℝ) ≤ (99 : ℝ) ^ d := by positivity
  have h2 : (0 : ℝ) ≤ Real.exp (-(Percolation.siteRateBase d / 2 * (Ev⁻¹ ^ 2 * M.gamma⁻¹))) :=
    (Real.exp_pos _).le
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((hs : ℝ) + (k₀ : ℝ)) / 2)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [collarMassCap]
  have h4 : (0 : ℝ) ≤ 9 * (99 : ℝ) ^ d := by linarith
  exact mul_nonneg h4 (by linarith)

/-- **The layer mass sequence** of the payload, at `Cmass = 6 d`
(`LayerMass.sum_cubeMassRatio_whitneyLayer_le`). -/
def assemblyMass (d : ℕ) : ℕ → ℝ := fun n => 6 * (d : ℝ) * (3 : ℝ) ^ (-(n : ℝ))

/-- **The bad-mass sequence** of the payload at the feasible route: the minimum of
the density cap and the layer's own mass. -/
def assemblyBad (M : ABKModel d) (Ev : ℝ) (hs k₀ : ℕ) : ℕ → ℝ :=
  fun n => min (collarMassCap M Ev hs k₀) (6 * (d : ℝ) * (3 : ℝ) ^ (-(n : ℝ)))

theorem assemblyMass_nonneg (d : ℕ) (n : ℕ) : 0 ≤ assemblyMass d n := by
  rw [assemblyMass]
  positivity

theorem assemblyBad_nonneg (M : ABKModel d) (Ev : ℝ) (hs k₀ : ℕ) (n : ℕ) :
    0 ≤ assemblyBad M Ev hs k₀ n := by
  rw [assemblyBad]
  exact le_min (collarMassCap_nonneg M Ev hs k₀) (by positivity)

theorem assemblyMass_le (d : ℕ) (n : ℕ) :
    assemblyMass d n ≤ 6 * (d : ℝ) * (3 : ℝ) ^ (-(n : ℝ)) := le_of_eq rfl

theorem assemblyBad_le_mass (M : ABKModel d) (Ev : ℝ) (hs k₀ : ℕ) (n : ℕ) :
    assemblyBad M Ev hs k₀ n ≤ 6 * (d : ℝ) * (3 : ℝ) ^ (-(n : ℝ)) := min_le_right _ _

theorem assemblyBad_le_cap (M : ABKModel d) (Ev : ℝ) (hs k₀ : ℕ) (n : ℕ) :
    assemblyBad M Ev hs k₀ n ≤ collarMassCap M Ev hs k₀ := min_le_left _ _

/-- **`hmasscol`, discharged at `assemblyBad`.**  The left branch of the
minimum is `CollarMass.sum_cubeMassRatio_collarLayer_le_layerQuantity` read at
the bottom of the layer quantity; the right branch is
`collarLayer ⊆ 𝒲(□_m,n)` composed with
`LayerMass.sum_cubeMassRatio_whitneyLayer_le`. -/
theorem sum_cubeMassRatio_collarLayer_le_assemblyBad {M : ABKModel d} {m : ℤ} {Ev b : ℝ}
    {k₀ : ℕ} {omega : CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 1 ≤ k₀)
    (hne : (Percolation.hsepSet M m Ev b omega).Nonempty) (n : ℕ) :
    ∑ Q ∈ collarLayer M m (whitneyScale M m Ev b k₀ omega) n omega,
        cubeMassRatio (originCube d m) Q
      ≤ assemblyBad M Ev (Percolation.hsep M m Ev b omega) k₀ n := by
  classical
  refine le_min ?_ ?_
  · refine le_trans (sum_cubeMassRatio_collarLayer_le_layerQuantity hb0 hb hk₀ hne n) ?_
    have hlow : ((Percolation.hsep M m Ev b omega : ℕ) : ℝ) + (k₀ : ℝ) ≤
        layerQuantity b (Percolation.hsep M m Ev b omega) k₀ n := by
      have hnat : Percolation.hsep M m Ev b omega + k₀ ≤
          whitneyScaleSeq b (Percolation.hsep M m Ev b omega) k₀ n :=
        add_le_whitneyScaleSeq b _ _ n
      have hcast : ((Percolation.hsep M m Ev b omega + k₀ : ℕ) : ℝ) ≤
          ((whitneyScaleSeq b (Percolation.hsep M m Ev b omega) k₀ n : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at hcast
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [layerQuantity]
      linarith
    have hexp : -(layerQuantity b (Percolation.hsep M m Ev b omega) k₀ n / 2) ≤
        -((((Percolation.hsep M m Ev b omega : ℕ) : ℝ) + (k₀ : ℝ)) / 2) := by linarith
    have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hpow : (0 : ℝ) ≤ 9 * (99 : ℝ) ^ d := by positivity
    rw [collarMassCap]
    exact mul_le_mul_of_nonneg_left (by linarith) hpow
  · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (collarLayer_subset M m (whitneyScale M m Ev b k₀ omega) n omega)
      (fun Q _ _ => cubeMassRatio_nonneg _ Q)) ?_
    exact sum_cubeMassRatio_whitneyLayer_le m (whitneyScale M m Ev b k₀ omega) n

/-! ## The concluding assembly -/


end

end Algsuperdiff.Section3.Provider.Multiscale

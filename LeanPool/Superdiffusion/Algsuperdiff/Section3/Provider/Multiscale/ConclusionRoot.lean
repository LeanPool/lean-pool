/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionAssemblyFinal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CollarLayerEnvelopeG
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.GlobalSuperposition

/-!
# ConclusionRoot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `[0,∞]` root of the concluding assembly of `p.bfA.multiscalebound`

`ConclusionCompetitor` records the join of the two as *not performed*, because
a `toReal` bound is vacuous unless the intermediate `[0,∞]` sum is finite.
This module performs the join.

## 1. What the module delivers

```
tsum_..._le_ofReal_payload            the [0,∞] twin of ConclusionCompetitor's payload
tsum_..._le_ofReal_payload_assembled_ae   its assembled form, at a FREE competitor pair
abs_blockVecDot_..._le_payload_ae     the local join at the concrete competitor
ofReal_abs_blockVecDot_le_tsum_superposed_ae   the join's left half at the SUPERPOSED
                                               competitor, with EXACTLY hF/hG open
abs_blockVecDot_..._le_payload_superposed      its real-valued form
```

```
| (𝐀hom_i^{-1/2}(p,q)) . 𝐀_L(□_m) (𝐀hom_i^{-1/2}(p,q)) |
  ≤ layerSumConst β (2γ+ε) kp Ktot Ccol (6d)
      . 3^{(2γ+ε)(h_hat_sep+k₀)} ( 1 + 3^{2β(h_hat_sep+k₀)} exp(-kp/36) )
```

## 2. The two open legs, and why they are packaged

`sum_of_a_decomp_cutoff` carries eight affine A clauses.  `q + L²_sol,0(□_m)`.
Later files now prove the superposed potential and divergence trace statements;
the theorems below retain their original conditional interfaces.

At the concrete single-mesh competitor the four cell-constant clauses `hbadF`,
`hoffF`, `hbadG`, `hoffG` are theorems here
(`kuhnSlope_competitorVertexData_eq_zero…`, `…_eq_of_mem_simplexPartition` and
their `competitorDivergence` twins, all read off the proved
`CompetitorVertexData` / `CollarLayerEnvelopeG` clauses through
`mem_simplexPartition_iff`).  What is NOT available at that competitor is
`hFc`/`hGc`: there is no proved global field whose cell constants are
`kuhnSlope 𝔰 (competitorVertexData ℐ p)` on ALL of `SW(□_m)` — that is exactly
what the cross-scale gluing rules out for the single-assignment presentation.  `hF`
and `hFc` are therefore carried as ONE existential binder

```
∃ F, F − 𝐀hom^{-1/2}p ∈ L²_pot,0(□_m)  ∧  F = Fc on every open cell of SW(□_m),
```

which is precisely `e.hat.linear.1` for the concrete family, and likewise for
`hG`/`hGc`.  So the theorem has TWO open legs and they are the affine chain's
own two open legs.  Nothing else is assumed.

## 3. The superposition leg, and the finding that separates the two routes

`GlobalSuperposition.superposedCompetitor_decomp_clauses_badFamily` discharges
all six cell-constant clauses at the superposed competitor `ℓ̂_p = ℓ_p + Σ_𝒞 (ℓ̂_p^𝒞 −
ℓ_p)`, including `hFc`/`hGc`, because that competitor comes with a global
field.  `ofReal_abs_blockVecDot_le_tsum_superposed_ae` consumes it: at the
manuscript's own bad family and at any loads, with the window binder discharged
by `badComponents_window_badFamily`, the whole of `sum_of_a_decomp_cutoff`
reduces to `hF` and `hG`.

Off the collar and on bad cubes the two competitors agree (both are `p` resp.
`0`, by clauses 3 and 1 on each side).  On a good cube the superposed cell
slope is a sum of per-component corrections read on per-component meshes; this
historical module neither identifies it with the single-mesh slope nor prices
it.  The later `SuperposedEnvelope.lean` proves the summed active-component
estimate, including the dimension-only overlap bound, and the correct trace
providers land in `SuperposedPotentialClosure.lean` and
`SuperposedDivergencePotential.lean`.

## 4. Why `hgood` and `hmasscol` are not re-done here

This module re-runs that same wiring only because the `toReal` conclusion
cannot be converted to the `ofReal` one after the fact; the wiring is
transcribed, not re-derived, and it is generalized in exactly two places: the
collar constant `Cgrad` is free (with `1 ≤ Cgrad`) and the competitor pair
`(Fv, Gv)` is free (with the two collar-envelope binders).  The proved local
`F`-leg and `G`-leg envelopes then instantiate it, so the `G`-leg input that is
explicit in `ConclusionAssemblyFinal` is discharged here at `Gv:= ∇·D̂_q =
competitorDivergence`.

## What is *not* proved

* **This module closes no node.**  Its historical public theorems retain
  `hF`/`hG` or other payload data as conditional/A premises.  Later providers
  discharge those premises at the correct superposed objects; that downstream
  progress is not credited to this file.
* **No local gradient or trace identification.**  Those statements are not
  proved below; see `SuperposedPotentialClosure.lean` and
  `SuperposedDivergencePotential.lean` for the later route.
* **No local summed active-component estimate.**  See
  `SuperposedEnvelope.lean`; the theorem below continues to expose the older
  collar-data interface.
* **No new probabilistic input, and no new constant**: every constant below is
  the one the proved inputs produce; nothing is optimized, and the only
  measure-theoretic step is `filter_upwards` on already-proved a.e. statements.
* **No `Ktot` construction**: the good leg's layer constant is
  `ConclusionKtotEnvelope`'s, unchanged, and the `|b_L|` branch of Step 2 is
  untouched.

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.payload_nonneg`
* `Algsuperdiff.Section3.Provider.Multiscale.`
  `tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload`
* `Algsuperdiff.Section3.Provider.Multiscale.`
  `tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload_assembled_ae`

## References

* ABK26, `p.bfA.multiscalebound` Step 3 (the payload display),
  `e.sum-of-a-decomp`, `e.bounds.on.slopes.when.bad`,
  `l.piecewise.affine.approx` (clauses 1 and 3), the false disjointness,
  `e.hat.linear.1`, `e.hatdq`, `e.hat.D.bc`, `l.bad.cubes.density`, `e.hn.def`,
  the `b`-window with label, `e.SW.def`, the Step-1 majorant.
* `Provider/Multiscale/ConclusionCompetitor.lean` (`sum_of_a_decomp_cutoff` and
  the two concrete cell functionals), `Provider/Multiscale/ConclusionAssemblyFinal.lean`
  (the assembled payload this module transcribes into `[0,∞]`),
  `Provider/Multiscale/ConclusionFeasibility.lean` (the parameter window),
  `Provider/Multiscale/LayerMass.lean` (`tsum_simplexPartition_le_ofReal_payload`),
  `Provider/Affine/CollarLayerEnvelope.lean` and
  `Provider/Affine/CollarLayerEnvelopeG.lean` (the two proved local envelopes),
  `Provider/Affine/CompetitorVertexData.lean` (clauses 1 and 3),
  `Provider/Affine/GlobalSuperposition.lean` (the six clauses at the superposed
  competitor and the window discharge).
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

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The payload is nonnegative -/

theorem payload_nonneg {b γ Ktot Ccol Cmass : ℝ} {k₀ : ℕ} (hs : ℝ)
    (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hCmass : 0 ≤ Cmass) :
    0 ≤ layerSumConst b γ k₀ Ktot Ccol Cmass *
      ((3 : ℝ) ^ (γ * hs) *
        (1 + (3 : ℝ) ^ (2 * b * hs) * Real.exp (-((k₀ : ℝ) / 36)))) := by
  have h3 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hinv : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := inv_nonneg.2 (by linarith)
  have e1 : (0 : ℝ) ≤ Ktot * Cmass * (3 : ℝ) ^ (γ * ((k₀ : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg hK hCmass) (Real.rpow_nonneg (by norm_num) _)
  have e2 : (0 : ℝ) ≤ 2 * (Ccol * Real.sqrt Cmass) * (3 : ℝ) ^ (2 * b) :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hC (Real.sqrt_nonneg _)))
      (Real.rpow_nonneg (by norm_num) _)
  have hL : 0 ≤ layerSumConst b γ k₀ Ktot Ccol Cmass := by
    rw [layerSumConst]
    exact mul_nonneg hinv (by linarith)
  have hr : (0 : ℝ) ≤ (3 : ℝ) ^ (γ * hs) := Real.rpow_nonneg (by norm_num) _
  have hprod : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * b * hs) * Real.exp (-((k₀ : ℝ) / 36)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
  exact mul_nonneg hL (mul_nonneg hr (by linarith))

/-! ## The Step-3 payload in `[0,∞]` -/

theorem tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload (M : ABKModel d)
    {m : ℤ} {hn : ℕ → ℕ} {L : ℤ} {omega : CutoffSample d} {p q : Vec d}
    {Fc Gc : KuhnCell d → Vec d} {b γ ε Cmass Ktot Ccol : ℝ} {hs k₀ : ℕ}
    {Mass Bad : ℕ → ℝ}
    (hmono : Monotone hn) (hb0 : 0 < b) (hb9 : 9 * b ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ : 4 * γ ≤ 1 - b) (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hCmass : 0 ≤ Cmass)
    (hε0 : 0 ≤ ε) (hεk0 : ε ≤ Real.exp (-(k₀ : ℝ)))
    (hMass0 : ∀ j : ℕ, 0 ≤ Mass j) (hBad0 : ∀ j : ℕ, 0 ≤ Bad j)
    (hMass : ∀ j : ℕ, Mass j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadMass : ∀ j : ℕ, Bad j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadDens : ∀ j : ℕ, Bad j ≤ ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ j / 2)))
    (hgood : ∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m hn n,
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
        goodCellForm M m hn L omega p q T ≤ Ktot * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n))
    (hcol : ∀ (n : ℕ), ∀ Q ∈ collarLayer M m hn n omega,
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
        collarCellForm M m hn L omega Fc Gc T ≤
          Ccol * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n))
    (hmassgood : ∀ n : ℕ, ∑ Q ∈ whitneyLayer (d := d) m hn n,
      cubeMassRatio (originCube d m) Q ≤ Mass n)
    (hmasscol : ∀ n : ℕ, ∑ Q ∈ collarLayer M m hn n omega,
      cubeMassRatio (originCube d m) Q ≤ Bad n) :
    (∑' T : ↥(simplexPartition (d := d) m hn),
        (ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            goodCellForm M m hn L omega p q (T : KuhnCell d)) +
          ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            collarCellForm M m hn L omega Fc Gc (T : KuhnCell d))))
      ≤ ENNReal.ofReal (layerSumConst b γ k₀ Ktot Ccol Cmass *
          ((3 : ℝ) ^ (γ * (hs : ℝ)) *
            (1 + (3 : ℝ) ^ (2 * b * (hs : ℝ)) * Real.exp (-((k₀ : ℝ) / 36))))) :=
  tsum_simplexPartition_le_ofReal_payload hmono hb0 hb9 hγ0 hγ hK hC hCmass hε0 hεk0
    hMass0 hBad0 hMass hBadMass hBadDens
    (fun T => ENNReal.ofReal (cellWeight m T * goodCellForm M m hn L omega p q T) +
      ENNReal.ofReal (cellWeight m T * collarCellForm M m hn L omega Fc Gc T))
    (fun n => sum_sum_ofReal_two_leg_le_ofReal_layerContrib
      (Sgood := whitneyLayer (d := d) m hn n) (Scol := collarLayer M m hn n omega)
      subset_rfl (collarLayer_subset M m hn n omega) hK hC (hgood n)
      (fun _ hQ hQ' => absurd hQ hQ') (hcol n)
      (collarLayer_zero M m hn n L omega Fc Gc) (hmassgood n) (hmasscol n))

/-! ## The assembled Step-3 payload in `[0,∞]`, at a free competitor pair -/

theorem tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload_assembled_ae (hd : 2 ≤ d)
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {i : ℤ} (hmi : m - 1 ≤ i)
    (hi : i ≤ m0) {L : ℤ} (hmL : m ≤ L) (p q : Vec d) {eps : ℝ} (heps : 0 < eps)
    {t : ℝ} (ht0 : 0 ≤ t) {Cgrad : ℝ} (hCgrad : 1 ≤ Cgrad) {β : ℝ} (hβ0 : 0 < β)
    (hβ9 : 9 * β ≤ 1) (hβb : 2 * b + 2 * M.gamma + eps ≤ 2 * β)
    (hγwin : 4 * (2 * M.gamma + eps) ≤ 1 - β) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(Percolation.siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (Percolation.hsepSet M m (E : ℝ) b omega).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega) n,
          cubeSupBound Q Q.scale L omega.1 ≤
            whitneyWaveLayerScale M m (whitneyScale M m (E : ℝ) b k₀ omega) n L * t) →
      ∀ Fv Gv : KuhnCell d → Vec d,
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega) n,
            ∀ T ∈ whitneySimplexCells (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega) n Q,
              vecNormSq (Fv T - p) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
                  (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) * vecNormSq p) →
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega) n,
            ∀ T ∈ whitneySimplexCells (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega) n Q,
              vecNormSq (Gv T - q) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
                  (whitneyScale M m (E : ℝ) b k₀ omega n : ℝ)))) * vecNormSq q) →
        (∑' T : ↥(simplexPartition (d := d) m (whitneyScale M m (E : ℝ) b k₀ omega)),
            (ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
                goodCellForm M m (whitneyScale M m (E : ℝ) b k₀ omega) L omega
                  ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
                  (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
                  (T : KuhnCell d)) +
              ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
                collarCellForm M m (whitneyScale M m (E : ℝ) b k₀ omega) L omega
                  (fun U => (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ •
                    Fv U)
                  (fun U => Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U)
                  (T : KuhnCell d)))) ≤
          ENNReal.ofReal (layerSumConst β (2 * M.gamma + eps) kp
              (ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q)
              (collarEnvelopeConst M m i L eps t Cgrad p q) (6 * (d : ℝ)) *
            ((3 : ℝ) ^ ((2 * M.gamma + eps) *
                ((Percolation.hsep M m (E : ℝ) b omega + k₀ : ℕ) : ℝ)) *
              (1 + (3 : ℝ) ^ (2 * β * ((Percolation.hsep M m (E : ℝ) b omega + k₀ : ℕ) : ℝ)) *
                Real.exp (-((kp : ℝ) / 36))))) := by
  classical
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hβ1 : β < 1 := by linarith
  have hbβ : b ≤ β := by linarith
  have hγ0 : (0 : ℝ) ≤ 2 * M.gamma + eps := by linarith
  have hgoodall := (MeasureTheory.ae_all_iff (ι := ℕ)).2 (fun hs : ℕ =>
    goodCellForm_le_ktotEnvelopeConst_mul_layerQuantity_ae hd M hS m hb0 hb hs k₀ hmi hi
      hmL p q heps ht0)
  have hcolall := (MeasureTheory.ae_all_iff (ι := ℕ)).2 (fun hs : ℕ =>
    collarCellForm_le_collarEnvelopeConst_mul_layerQuantity_ae hd M hS m hb0 hb hs k₀ hmi hi
      hmL p q heps ht0 hCgrad)
  filter_upwards [hgoodall, hcolall] with omega hg hc hne henv Fv Gv hFv hGv
  set hs : ℕ := Percolation.hsep M m (E : ℝ) b omega with hhs
  have hLQ : ∀ n : ℕ, layerQuantity b hs k₀ n ≤ layerQuantity β (hs + k₀) kp n :=
    fun n => layerQuantity_le_of_le hbβ hβ1 (by omega) n
  have hLQ0 : ∀ n : ℕ, (0 : ℝ) ≤ layerQuantity b hs k₀ n := fun n => layerQuantity_nonneg _ _ _ _
  have hK : (0 : ℝ) ≤ ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q :=
    ktotConst_nonneg hd M m i (by norm_num) _ p q
  have hC : (0 : ℝ) ≤ collarEnvelopeConst M m i L eps t Cgrad p q :=
    collarEnvelopeConst_nonneg hd M m i L eps t Cgrad p q
  have hεk0 : collarMassCap M (E : ℝ) hs k₀ ≤ Real.exp (-(kp : ℝ)) := by
    refine le_trans ?_ hcap
    have hmono3 : (3 : ℝ) ^ (-(((hs : ℝ) + (k₀ : ℝ)) / 2)) ≤ (3 : ℝ) ^ (-((k₀ : ℝ) / 2)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hs0 : (0 : ℝ) ≤ (hs : ℝ) := Nat.cast_nonneg hs
      linarith
    have hpow : (0 : ℝ) ≤ 9 * (99 : ℝ) ^ d := by positivity
    rw [collarMassCap]
    exact mul_le_mul_of_nonneg_left (by linarith) hpow
  refine tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload M
    (b := β) (γ := 2 * M.gamma + eps) (ε := collarMassCap M (E : ℝ) hs k₀)
    (Cmass := 6 * (d : ℝ)) (hs := hs + k₀) (k₀ := kp)
    (Mass := assemblyMass d) (Bad := assemblyBad M (E : ℝ) hs k₀)
    (whitneyScaleSeq_mono hb0.le (by linarith) hs k₀) hβ0 hβ9 hγ0 hγwin hK hC
    (by positivity) (collarMassCap_nonneg M (E : ℝ) hs k₀) hεk0
    (fun j => assemblyMass_nonneg d j) (fun j => assemblyBad_nonneg M (E : ℝ) hs k₀ j)
    (fun j => assemblyMass_le d j) (fun j => assemblyBad_le_mass M (E : ℝ) hs k₀ j)
    (fun j => le_trans (assemblyBad_le_cap M (E : ℝ) hs k₀ j)
      (by have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(layerQuantity β (hs + k₀) kp j / 2)) :=
            Real.rpow_nonneg (by norm_num) _
          linarith))
    ?_ ?_ (fun n => sum_cubeMassRatio_whitneyLayer_le m _ n)
    (fun n => sum_cubeMassRatio_collarLayer_le_assemblyBad hb0 hb hk₀ hne n)
  · intro n Q hQ T hT
    refine le_trans (hg hs henv n Q hQ T hT) ?_
    refine mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hK
    exact mul_le_mul_of_nonneg_left (hLQ n) hγ0
  · intro n Q hQ T hT
    refine le_trans
      (hc hs henv Fv Gv hFv hGv n Q (collarLayer_subset M m _ n omega hQ) T hT) ?_
    refine mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hC
    have h1 : (2 * b + 2 * M.gamma + eps) * layerQuantity b hs k₀ n ≤
        2 * β * layerQuantity b hs k₀ n :=
      mul_le_mul_of_nonneg_right (by linarith) (hLQ0 n)
    have h2 : 2 * β * layerQuantity b hs k₀ n ≤ 2 * β * layerQuantity β (hs + k₀) kp n :=
      mul_le_mul_of_nonneg_left (hLQ n) (by linarith)
    linarith

/-! ## The four local cell-constant clauses at the concrete competitor -/


/-! ## The local top-level join at the concrete competitor -/


end

end Algsuperdiff.Section3.Provider.Multiscale

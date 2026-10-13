/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.Step3Seams

/-!
# LayerUniform

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The a.e.-uniform layer lift, and the collar leg of Step 3

`LayerMass.toReal_tsum_simplexPartition_le_payload` reduces Step 3 of
`p.bfA.multiscalebound` (ABK26) to the single hypothesis

```
hlayer : ∀ n : ℕ, ∑ □ ∈ 𝒲(□_m,n), ∑ 𝔰 ∈ S(□), f 𝔰
           ≤ ENNReal.ofReal (layerContrib b γ hs k₀ Ktot Ccol Mass Bad n) ,
```

a statement about **one** sample `ω`, quantified over **all** layers, all
Whitney cubes and all cells at once.  `Step3Seams` proves the three simplex
legs of Step 1 (`e.good.simplex.consequence` at the manuscript's own simplex
carrier) only *per cube*: each of them is an `∀ᵐ ω` statement whose null set
depends on the cube `Q` and on the two scales `k`, `i`.  This module supplies
the two things that stand between those legs and `hlayer`.

## What is proved

1. **The a.e.-uniform lift** (items (1) of the `#conclusion` remainder).
   `TriadicCube d` is countable (`Homogenization.instCountableTriadicCube`) and
   so is `ℤ`, so `MeasureTheory.ae_all_iff` -- applied three times, once per
   quantifier, which is what makes the iterated form over
   `TriadicCube d × ℤ × ℤ` legitimate -- turns the per-cube family into a single
   null set.  The two non-random ordering hypotheses `Q.scale ≤ i` and `i ≤ m0`
   are carried *inside* the a.e. statement as implications; guarding them is
   `ae_imp_of_imp_ae`, a two-line case split, and no measurability is used.  The
   three lifts are `responseJ_simplexDomain_normalized_flux_le_ae_uniform`,
   `responseJ_simplexDomain_normalized_slope_le_ae_uniform` and
   `blockVecDot_coarseBlockMatrix_simplexDomain_normalized_le_ae_uniform`; the
   third is specialized to the Whitney layer in
   `blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae`, which is the exact
   per-cell datum `Step3Seams.sum_sum_ofReal_cellWeight_le_ofReal_mul` consumes
   on the good leg.

   Note the binder economy of the lift: the proved legs carry `hm: Q.scale ≤
   m0` *and* `hji: Q.scale ≤ i` *and* `hi: i ≤ m0`; the first is implied by the
   other two, so the uniform statements carry only two.

2. From the *layer-envelope* reading of the collar gradient estimate --
   `|∇ℓ̂_p(𝔰) - p| ≤ Cgrad |p| 3^{b(k+h_k)}` on the cells of a layer-`k` collar
   cube, which is what leaves standing of the printed component-local display
   -- the normalized display

   ```
   |(∇·D̂_q)(𝔰)|²/|q|² + |∇ℓ̂_p(𝔰)|²/|p|² ≤ 8 Cgrad² 3^{2 b (k + h_k)}
   ```

   is `bounds_on_slopes_when_bad`.  The `8` is's own `2 × (2 + 2)`: the per-leg
   step `|∇ℓ̂_p|² ≤ 2(1 + ratio²)|p|² ≤ 4 Cgrad² 3^{2b(k+h_k)} |p|²`
   (`vecNormSq_le_four_mul_of_slope_error`, which uses `1 ≤ Cgrad` and `1 ≤
   3^{b(k+h_k)}` exactly as records) summed over the two legs.

3. **The collar leg made dischargeable.**  The per-cell term of the *second*
   sum of `Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean) is the
   `𝐀_L(𝔰)` quadratic form loaded at the competitor's cell constants
   `(Fc 𝔰, Gc 𝔰)`.  Since `e.good.simplex.consequence` is proved for an
   *arbitrary* load, it applies at that load verbatim, and item 2 then trades
   the competitor's slopes for the original ones:
   `blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae` bounds the
   collar cell term by `4 Cgrad² 3^{2b(k+h_k)}` times the good-leg majorant at
   `(p,q)`.  That is a uniform per-cell constant on each cube.  The declarations
   in this file still accept the layer-uniform majorants as interface data.
   Later conclusion providers, including `ConclusionKtotEnvelope.lean` and
   `ConclusionAssemblyFinal.lean`, produce and consume the concrete layer
   envelopes; that downstream discharge is not credited to this abstract file.

4. **The two legs assembled in the `hlayer` shape.**
   `sum_sum_ofReal_two_leg_le_ofReal_layerContrib` runs
   `sum_sum_ofReal_cellWeight_le_ofReal_mul` once per leg at the two constants
   `Ktot 3^{γ(k+h_k)}` and `Ccol 3^{2b(k+h_k)}` of
   `ConclusionAssembly.layerContrib` and adds them, and
   `toReal_tsum_simplexPartition_two_leg_le_payload` composes the result with
   `LayerMass.toReal_tsum_simplexPartition_le_payload` to reach the Step-3
   payload.  Its cell functional is
   `f 𝔰 = ofReal(|𝔰|/|□_m| . g_good 𝔰) + ofReal(|𝔰|/|□_m| . g_col 𝔰)`, the
   `[0,∞]` reading of the right-hand side of `e.sum-of-a-decomp`.

## What is not proved in this file, and what its A carries

* This file does not construct the **affine approximation**
  `l.piecewise.affine.approx`.  Its collar gradient conclusion enters only as
  the two hypotheses `vecNormSq (Fv - p) ≤ Cgrad² 3^{2b(k+h_k)} vecNormSq p`
  (and the `q`-twin) of item 2/3, in the source-shaped A style of
  `Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean)'s
  `hbadF`/`hbadG`/`hoffF`/`hoffG` (which carry clauses 1 and 3 of
  `e.hat.linear.properties`; this module carries the layer-envelope reading of
  clause 2, the one clause `SubadditiveDecomposition.lean` explicitly does
  *not* use).  Accordingly `hF`, `hG`, and `Cgrad` are explicit A obligations
  of the declarations here.  The later affine providers
  `SuperposedPotentialClosure.lean`, `SuperposedDivergencePotential.lean`, and
  `SuperposedEnvelope.lean` establish the concrete potential, solenoidal, and
  envelope legs used downstream; those theorems do not retroactively turn this
  abstract interface into a source-node export.
* At bad cells (`hbadF`/`hbadG`) the competitor constants *vanish*, so the
  collar term is `0` there --- the block pairing of a zero load is zero --- and
  the A antecedent is vacuous.  The collar leg's live cells are the good cells
  of `𝒩(ℐ)`, which is where the antecedent is read.
* The declarations here do not prove the **mass comparison** between the collar
  family `(𝒩(ℐ) ∩ 𝒲(□_m,k)) ∖ ℐ` and the bad family `ℐ_k`; they take `hmasscol
  : ∑_{□ ∈ S_col} |□|/|□_m| ≤ Bad n` as an explicit A obligation.
  `CollarMass.lean` now proves the concrete collar-vs-bad comparison used
  later.
* The declarations here also leave the cell functionals `g_good`, `g_col`, the
  subfamilies, and their pointwise bounds as abstract A data.
  `ConclusionCompetitor.lean` supplies the concrete coefficient-family and
  competitor instantiation.  This file therefore remains a conditional
  layer-pricing interface even though later providers discharge its inputs.

## Main results

* `blockVecDot_coarseBlockMatrix_simplexDomain_normalized_le_ae_uniform`:
  `e.good.simplex.consequence` at the simplex carrier, on ONE null set for all
  cubes, all cell scales and all frame scales.
* `blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae`: the same, read on a
  Whitney layer.
* `vecNormSq_le_four_mul_of_slope_error`, `quadratic_form_le_of_slope_bounds`:
  the two arithmetic steps behind `e.bounds.on.slopes.when.bad` --- a slope
  within `Cgrad 3^{b(k+h_k)}` of the load has square at most
  `4 Cgrad² 3^{2b(k+h_k)}` times the load's, and that trade passes to the
  cell's quadratic form.
* `blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae`: the collar
  leg's per-cell bound.
* `sum_sum_ofReal_two_leg_le_ofReal_layerContrib`: the `hlayer` shape, one
  Whitney layer priced by `layerContrib`.

## References

* ABK26, `e.sum-of-a-decomp`, `e.good.simplex.consequence`, Step 1, Step 3,
  `e.bounds.on.slopes.when.bad`, `l.piecewise.affine.approx`,
  `r.gradient.bound.simplified`, `e.SW.def`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Whitney

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Two countability primitives -/

/-- A **non-random** hypothesis can be pushed inside an `a.e.` statement: the
case split on the hypothesis is performed once, outside the measure.  No
measurability of anything is used. -/
private theorem ae_imp_of_imp_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P : Prop} {R : α → Prop} (h : P → ∀ᵐ a ∂μ, R a) : ∀ᵐ a ∂μ, P → R a := by
  by_cases hP : P
  · filter_upwards [h hP] with a ha
    exact fun _ => ha
  · exact Filter.Eventually.of_forall fun _ hPa => absurd hPa hP

/-- **One null set for all cubes and all pairs of scales.**  `TriadicCube d` is
countable (`Homogenization.instCountableTriadicCube`) and so is `ℤ`, so
`MeasureTheory.ae_all_iff` applies once per quantifier; the iterated form is
legitimate because each application is at a genuinely countable index type, and
the intermediate predicates are the `∀`-closures of the later ones. -/
private theorem ae_forall_cube_two_scales {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {R : α → TriadicCube d → ℤ → ℤ → Prop}
    (h : ∀ (Q : TriadicCube d) (k i : ℤ), ∀ᵐ a ∂μ, R a Q k i) :
    ∀ᵐ a ∂μ, ∀ (Q : TriadicCube d) (k i : ℤ), R a Q k i :=
  ae_all_iff.2 fun Q => ae_all_iff.2 fun k => ae_all_iff.2 fun i => h Q k i

/-! ## The three simplex legs of Step 1, a.e.-uniformly -/


/-- **`e.good.simplex.consequence` at the manuscript's own carrier,
a.e.-uniformly** (ABK26, assembled).  One null set serves every triadic cube
`Q`, every cell scale `k` and every frame scale `i` simultaneously -- which is
what a *layer* of `e.sum-of-a-decomp` needs, since a layer contains many cubes
and Step 3 sums over all layers. -/
theorem blockVecDot_coarseBlockMatrix_simplexDomain_normalized_le_ae_uniform
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (Q : TriadicCube d) (k i : ℤ), Q.scale ≤ i → i ≤ m0 →
        omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
          ∀ T : KuhnCell d, T.supportCube ∈ descendantsAtScale Q k →
            ∀ p q : Vec d,
              blockVecDot
                  ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                    Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
                  (blockMatVecMul
                    (Ch02.coarseBlockMatrix (simplexDomain T)
                      (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T))
                    ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                      Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)) ≤
                640 * simplexCrudeConst d (1 / 4) *
                    Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                    (1 + 8 * bigLambdaSensitivityConst d *
                        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
                        (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
                        (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) *
                    vecNormSq p +
                  320 * simplexCrudeConst d (1 / 4) *
                    Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                    (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q :=
  ae_forall_cube_two_scales fun Q k _ =>
    ae_imp_of_imp_ae fun hji => ae_imp_of_imp_ae fun hi =>
      blockVecDot_coarseBlockMatrix_simplexDomain_normalized_le_of_notMem_bad_ae hd M hS
        Q (hji.trans hi) k hji hi

/-! ## The uniform statement, read on one Whitney layer -/

/-- **`e.good.simplex.consequence` on a Whitney layer.**  Almost surely, for
every layer `n`, every layer-`n` Whitney cube `□` on which the bad event does not
occur, and every cell `𝔰` of the layer-`n` decomposition of `□`, the load-`(p,q)`
quadratic form of `𝐀_L(𝔰)` in the `𝐀hom_i^{-1/2}` frame obeys the Step-1 bound at
the cell scale `simplexScale m hn n = m - (n+1) - h_{n+1}` of `e.SW.def`.

`Q.scale ≤ i` is automatic: layer `0` is empty and a layer-`n` cube has scale
`m - n - h_n ≤ m - 1 ≤ i`. -/
theorem blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae (hd : 2 ≤ d)
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) (hn : ℕ → ℕ)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        omega ∉ BadEvents.bad M Q → ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, ∀ p q : Vec d,
            blockVecDot
                ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                  Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (simplexDomain T)
                    (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T))
                  ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                    Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)) ≤
              640 * simplexCrudeConst d (1 / 4) *
                  Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
                  (1 + 8 * bigLambdaSensitivityConst d *
                      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
                      (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
                      (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) *
                  vecNormSq p +
                320 * simplexCrudeConst d (1 / 4) *
                  Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
                  (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q := by
  filter_upwards
    [blockVecDot_coarseBlockMatrix_simplexDomain_normalized_le_ae_uniform hd M hS]
    with omega huniform n Q hQ hbad L hL T hT p q
  have hn1 : 1 ≤ n := (mem_whitneyLayer_iff.mp hQ).1
  have hscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) := scale_eq_of_mem_whitneyLayer hQ
  have hQi : Q.scale ≤ i := by omega
  have hosc : omega ∉ badOsc M Q := fun h => hbad (Set.mem_union_left _ h)
  have hloc : omega ∉ badLoc M Q := fun h => hbad (Set.mem_union_right _ h)
  exact huniform Q (simplexScale m hn n) i hQi hi hosc hloc L hL T
    (mem_whitneySimplexCells_iff.mp hT) p q

/-! ## `e.bounds.on.slopes.when.bad`'s constant -/

/-- **The per-leg step.**  If a field's slope on a cell differs from the load by at
most `Cgrad 3^{b(k+h_k)}` times the load, its square is at most `4 Cgrad²
3^{2b(k+h_k)}` times the load's square:

```
|F|² ≤ 2(|F - p|² + |p|²) ≤ 2(A + 1)|p|² ≤ 4 A |p|²      (A := Cgrad² 3^{2b(k+h_k)} ≥ 1) .
```

writes the middle quantity as `2(1 + ratio²)` and the last step is exactly its
"uses `1 ≤ 3^{b(k+h_k)}` and `1 ≤ Cgrad`".  Stated with the amplitude `t` as a
free real, so that no `rpow` enters the arithmetic. -/
theorem vecNormSq_le_four_mul_of_slope_error {Cgrad t : ℝ} {F p : Vec d}
    (hC : 1 ≤ Cgrad) (ht : 1 ≤ t)
    (hF : vecNormSq (F - p) ≤ Cgrad ^ 2 * t * vecNormSq p) :
    vecNormSq F ≤ 4 * (Cgrad ^ 2 * t) * vecNormSq p := by
  have hsplit : vecNormSq F ≤ 2 * (vecNormSq (F - p) + vecNormSq p) := by
    have h := vecNormSq_add_le (F - p) p
    rwa [sub_add_cancel] at h
  have hp0 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hC2 : (1 : ℝ) ≤ Cgrad ^ 2 := by nlinarith [hC]
  have hCt : (1 : ℝ) ≤ Cgrad ^ 2 * t := by nlinarith [hC2, ht]
  linarith [hsplit, hF, mul_nonneg hp0 (sub_nonneg.2 hCt)]


/-! ## The collar leg's per-cell bound -/

/-- **The trade of the competitor's slopes for the load**, as pure real
arithmetic.  `Φ` is the cell's quadratic form, `Kp`/`Kq` the two Step-1
coefficients, `nF`/`nG` the competitor's squared slopes and `np`/`nq` the load's.
This is the only step of the collar leg that is not Step 1. -/
theorem quadratic_form_le_of_slope_bounds {Φ Kp Kq A nF nG np nq : ℝ}
    (hform : Φ ≤ Kp * nF + Kq * nG) (hKp : 0 ≤ Kp) (hKq : 0 ≤ Kq)
    (hF : nF ≤ A * np) (hG : nG ≤ A * nq) : Φ ≤ A * (Kp * np + Kq * nq) := by
  linarith [hform, mul_le_mul_of_nonneg_left hF hKp, mul_le_mul_of_nonneg_left hG hKq]

/-- **The collar leg of `e.sum-of-a-decomp`, per cell** (ABK26).  Almost surely,
for every layer `n`, every good layer-`n` Whitney cube `□`, every cell `𝔰` of
`□` and every load `(p,q)` and competitor cell constants `(Fv, Gv)` satisfying
the collar A of `e.bounds.on.slopes.when.bad`, the competitor's own quadratic
form at `𝔰` is at most `4 Cgrad² 3^{2b(n + h_n)}` times the Step-1 majorant of
the load's form.

The route is the manuscript's: `e.good.simplex.consequence` is proved for an
*arbitrary* load, so it applies at the competitor's load verbatim; then
`vecNormSq_le_four_mul_of_slope_error` (the per-leg half) trades `|∇ℓ̂_p|²` for
`|p|²` and `|(∇·D̂_q)|²` for `|q|²`.  Because the frame `𝐀hom_i^{-1/2}` is
block diagonal with scalar blocks (`e.homs.defs.U.diag`), the framed competitor
`(σ_i^{-1/2} Fv, σ_i^{1/2} Gv)` is the frame applied to the unframed slopes
and no rescaling arithmetic is needed.

The right-hand side is a constant on the cells of one cube: it depends on `□`
only through `Q.scale` and the increment gauge, and on `𝔰` not at all.  Since
the increment gauge varies across a layer's cubes, a per-layer supremum is
still needed before this is the abstract `C` of
`Step3Seams.sum_sum_ofReal_cellWeight_le_ofReal_mul` on the collar leg; the
good leg absorbs the same step into its layer constant. -/
theorem blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae (hd : 2 ≤ d)
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) (hn : ℕ → ℕ)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0) {b Cgrad : ℝ}
    (hCgrad : 1 ≤ Cgrad) (hb : 0 ≤ b) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        omega ∉ BadEvents.bad M Q → ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, ∀ p q Fv Gv : Vec d,
            vecNormSq (Fv - p) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq p →
            vecNormSq (Gv - q) ≤ Cgrad ^ 2 *
                (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq q →
            blockVecDot
                ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv,
                  Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (simplexDomain T)
                    (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T))
                  ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv,
                    Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv)) ≤
              4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
                (640 * simplexCrudeConst d (1 / 4) *
                    Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
                    (1 + 8 * bigLambdaSensitivityConst d *
                        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
                        (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
                        (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) *
                    vecNormSq p +
                  320 * simplexCrudeConst d (1 / 4) *
                    Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
                    (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q) := by
  filter_upwards
    [blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae hd M hS m hn hmi hi]
    with omega hgood n Q hQ hbad L hL T hT p q Fv Gv hFv hGv
  have hSnn : (0 : ℝ) ≤ simplexCrudeConst d (1 / 4) :=
    simplexCrudeConst_nonneg d (by norm_num)
  have hW : (0 : ℝ) ≤ Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) :=
    multiscaleDescendantWeight_nonneg Q (simplexScale m hn n) (1 / 4)
  have hXi : (0 : ℝ) ≤ 8 * bigLambdaSensitivityConst d *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
      (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
      (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2 := by
    have h1 : (0 : ℝ) ≤ 8 * bigLambdaSensitivityConst d := by
      have := (bigLambdaSensitivityConst_pos hd).le
      linarith
    have h2 : (0 : ℝ) ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
      inv_nonneg.2 (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
    have h3 : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
    have h4 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) (sq_nonneg _)
  have hKp : (0 : ℝ) ≤ 640 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (1 + 8 * bigLambdaSensitivityConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
        (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSnn) hW) (by linarith)
  have hKq : (0 : ℝ) ≤ 320 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSnn) hW)
      (Real.rpow_nonneg (by norm_num) _)
  have ht : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) := by
    refine Real.one_le_rpow (by norm_num) ?_
    have hnn : (0 : ℝ) ≤ (n : ℝ) + (hn n : ℝ) := by positivity
    have := mul_nonneg hb hnn
    linarith
  exact quadratic_form_le_of_slope_bounds (hgood n Q hQ hbad L hL T hT Fv Gv) hKp hKq
    (vecNormSq_le_four_mul_of_slope_error hCgrad ht hFv)
    (vecNormSq_le_four_mul_of_slope_error hCgrad ht hGv)

/-! ## The two legs of `e.sum-of-a-decomp`, in the `hlayer` shape -/

/-- **One Whitney layer of `e.sum-of-a-decomp`, majorized by
`ConclusionAssembly.layerContrib`.**  The two sums of `e.sum-of-a-decomp` are
majorized separately by `Step3Seams.sum_sum_ofReal_cellWeight_le_ofReal_mul`, at
the two per-cell constants of `layerContrib`:

* good leg -- `S_good` the good part of the layer, `C = Ktot 3^{γ(k+h_k)}` (the
  layer reading of `e.good.simplex.consequence`);
* collar leg -- `S_col` the good part of the collar `𝒩(ℐ)` of the layer, `C =
  Ccol 3^{2b(k+h_k)}` (`e.bounds.on.slopes.when.bad`, at the constant of
  `blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae`).

`hmassgood` and `hmasscol` are the caller's mass obligations.  `hmassgood` is
discharged by `Finset.sum_le_sum_of_subset_of_nonneg` against
`LayerMass.sum_cubeMassRatio_whitneyLayer_le`.  `hmasscol` is the caller's
collar-vs-bad mass comparison; the bounded-overlap geometry behind it is NOW
proved locally (`Provider/Multiscale/CollarMass.lean`, at the concrete collar
carrier `collarLayer` --- a `filter`, not the set-difference form this note
once described;), with the feasible consumer instantiation recorded there.  The
binder remains abstract here so the assembly composes with any admissible
`Bad`. -/
theorem sum_sum_ofReal_two_leg_le_ofReal_layerContrib {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {b γ Ktot Ccol : ℝ} {hs k₀ : ℕ} {Mass Bad : ℕ → ℝ}
    {ggood gcol : KuhnCell d → ℝ} {Sgood Scol : Finset (TriadicCube d)}
    (hSgood : Sgood ⊆ whitneyLayer (d := d) m hn n)
    (hScol : Scol ⊆ whitneyLayer (d := d) m hn n)
    (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol)
    (hgood : ∀ Q ∈ Sgood, ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
      ggood T ≤ Ktot * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n))
    (hgoodz : ∀ Q ∈ whitneyLayer (d := d) m hn n, Q ∉ Sgood →
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, ggood T = 0)
    (hcol : ∀ Q ∈ Scol, ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
      gcol T ≤ Ccol * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n))
    (hcolz : ∀ Q ∈ whitneyLayer (d := d) m hn n, Q ∉ Scol →
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, gcol T = 0)
    (hmassgood : ∑ Q ∈ Sgood, cubeMassRatio (originCube d m) Q ≤ Mass n)
    (hmasscol : ∑ Q ∈ Scol, cubeMassRatio (originCube d m) Q ≤ Bad n) :
    ∑ Q ∈ whitneyLayer (d := d) m hn n,
        ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
          (ENNReal.ofReal (cellWeight m T * ggood T) +
            ENNReal.ofReal (cellWeight m T * gcol T))
      ≤ ENNReal.ofReal (layerContrib b γ hs k₀ Ktot Ccol Mass Bad n) := by
  classical
  have hgpow : (0 : ℝ) ≤ (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n) :=
    Real.rpow_nonneg (by norm_num) _
  have hcpow : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n) :=
    Real.rpow_nonneg (by norm_num) _
  have hCg : (0 : ℝ) ≤ Ktot * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n) :=
    mul_nonneg hK hgpow
  have hCc : (0 : ℝ) ≤ Ccol * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n) :=
    mul_nonneg hC hcpow
  have hmg0 : (0 : ℝ) ≤ ∑ Q ∈ Sgood, cubeMassRatio (originCube d m) Q :=
    Finset.sum_nonneg fun Q _ => cubeMassRatio_nonneg _ Q
  have hmc0 : (0 : ℝ) ≤ ∑ Q ∈ Scol, cubeMassRatio (originCube d m) Q :=
    Finset.sum_nonneg fun Q _ => cubeMassRatio_nonneg _ Q
  have h1 := sum_sum_ofReal_cellWeight_le_ofReal_mul hSgood hCg hgood hgoodz
  have h2 := sum_sum_ofReal_cellWeight_le_ofReal_mul hScol hCc hcol hcolz
  have hsplit : ∑ Q ∈ whitneyLayer (d := d) m hn n,
      ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        (ENNReal.ofReal (cellWeight m T * ggood T) +
          ENNReal.ofReal (cellWeight m T * gcol T))
      = (∑ Q ∈ whitneyLayer (d := d) m hn n,
          ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            ENNReal.ofReal (cellWeight m T * ggood T)) +
        ∑ Q ∈ whitneyLayer (d := d) m hn n,
          ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            ENNReal.ofReal (cellWeight m T * gcol T) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Q _ => Finset.sum_add_distrib
  rw [hsplit]
  refine le_trans (add_le_add h1 h2) ?_
  rw [← ENNReal.ofReal_add (mul_nonneg hCg hmg0) (mul_nonneg hCc hmc0)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hgle : Ktot * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n) *
      (∑ Q ∈ Sgood, cubeMassRatio (originCube d m) Q)
      ≤ Ktot * (Mass n * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n)) :=
    calc Ktot * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n) *
          (∑ Q ∈ Sgood, cubeMassRatio (originCube d m) Q)
        ≤ Ktot * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n) * Mass n :=
          mul_le_mul_of_nonneg_left hmassgood hCg
      _ = Ktot * (Mass n * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ n)) := by ring
  have hcle : Ccol * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n) *
      (∑ Q ∈ Scol, cubeMassRatio (originCube d m) Q)
      ≤ Ccol * ((3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n) * Bad n) :=
    calc Ccol * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n) *
          (∑ Q ∈ Scol, cubeMassRatio (originCube d m) Q)
        ≤ Ccol * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n) * Bad n :=
          mul_le_mul_of_nonneg_left hmasscol hCc
      _ = Ccol * ((3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ n) * Bad n) := by ring
  rw [layerContrib]
  linarith [hgle, hcle]


end

end Algsuperdiff.Section3.Provider.Multiscale

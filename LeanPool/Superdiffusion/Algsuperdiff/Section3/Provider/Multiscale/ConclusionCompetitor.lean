/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LayerUniform

/-!
# ConclusionCompetitor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.sum-of-a-decomp` at the Step-3 coefficient family and competitor

`Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean; ABK26) is stated
at an **abstract** cell coefficient family `aS` and an **abstract** competitor
pair `(F, G)`; `LayerUniform.sum_sum_ofReal_two_leg_le_ofReal_layerContrib` and
`LayerUniform.toReal_tsum_simplexPartition_two_leg_le_payload` are stated at
**abstract** cell functionals `g_good`, `g_col`.  This module performs the
local provider instantiation: it instantiates `aS` at the manuscript's own
coefficient family, reads off the two concrete per-cell functionals, and shows
they land exactly in the two-leg shape the layer theorems consume.

## The instantiation

The cell coefficient object is `cellCutoffCoeffOn M L omega 𝔰:= simplexCoeffOn
(coefficientCutoffTriadicCoeffFamily M L omega) 𝔰`, the same object at which
`Step3Seams` and `LayerUniform` prove Step 1.  Two facts make the instantiation
free:

* `SimplexDissection.simplexDomain 𝔰` and `SimplexDomains.kuhnCellDomain 𝔰` are
  the *same* `Ch02.Domain d` (same carrier, and their remaining fields are
  proofs), so `simplexCoeffOn`'s value is literally a
  `Ch02.CoeffOn (kuhnCellDomain 𝔰)`; `coarseBlockMatrix_cellCutoffCoeffOn`
  records the identification, by `rfl`.
* `sum_of_a_decomp`'s compatibility binder `haS: (aS 𝔰).toCoeffField =
  a.toCoeffField` holds by `rfl` at `a:= (coefficientCutoffTriadicCoeffFamily M
  L omega).coeffOn □_m`: `restrictCoeffOn` keeps the representative field, and
  `coefficientCutoffCoeffOn_toCoeffField` says the representative is
  `coefficientCutoff M.nu L omega` on *every* cube ("only its locally derived
  ellipticity witness changes with the cube").

So `sum_of_a_decomp_cutoff` carries **no** coefficient binder at all: `aS` and
`haS` are gone, and what is left is the eight-binder affine A of
`l.piecewise.affine.approx`, transported verbatim.

## The two concrete cell functionals

```
g_good 𝔰 = ((p,q) . 𝐀_L(𝔰) (p,q))                 1_{¬𝓑(𝔰)}
g_col  𝔰 = ((Fc 𝔰,Gc 𝔰) . 𝐀_L(𝔰) (Fc 𝔰,Gc 𝔰))     1_{¬𝓑(𝔰)} 1_{𝔰 ∈ 𝒩(ℐ)}
```

(`goodCellForm`, `collarCellForm`).

## The two sub-families, and what is discharged

The layer theorems take four data per leg (`hS…`, `h…`, `h…z`, `hmass…`).  At
the concrete functionals two of them are **theorems**, not data:

* the good leg's sub-family is the **whole** layer (`Sgood n = 𝒲(□_m,n)`): the
  indicator `1_{¬𝓑}` is already inside `g_good`, so the bad cubes contribute
  `0` and no restriction is needed.  `hSgood` is `subset_rfl` and `hgoodz` is
  vacuous.
* the collar leg's sub-family is `collarLayer = 𝒲(□_m,n) ∩ 𝒩(ℐ)`.  `hScol` is
  `Finset.filter_subset` and `hcolz` is `collarIndicator_of_notMem` composed
  with `whitneyCubeOf_of_mem_whitneySimplexCells` (`collarLayer_zero`).

`hgood`, `hcol`, `hmassgood`, `hmasscol` remain the caller's, in exactly the
interface style of `LayerUniform`; see below for which of them this repository
can and cannot supply.

## The per-cell bounds, and the one thing they are not

`goodCellForm_le_stepOneLayerMajorant_ae` and
`collarCellForm_le_stepOneLayerMajorant_ae` are the concrete readings of
`LayerUniform.blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae` and
`LayerUniform.blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae`:
almost surely, for *every* layer, *every* cube of the layer (bad ones included
--- there the indicator kills the term) and every cell,

```
g_good 𝔰  ≤  M(□, n, i, L, ω; p, q) ,
g_col  𝔰  ≤  4 Cgrad² 3^{2b(n+h_n)} . M(□, n, i, L, ω; p, q) ,
```

with `M = stepOneLayerMajorant` the Step-1 majorant.

`M` is **not** constant on a layer.  Every factor of it is (`□.scale = m - n -
h_n` is fixed on `𝒲(□_m,n)`, and `multiscaleDescendantWeight`,
`3^{-2γ□.scale}`, `3^{γ(i-□.scale)}` depend on `□` only through `□.scale`)
*except* the increment gauge `‖k_L - k_{□.scale}‖_{W^{1,∞}(□)}²`, which
genuinely varies over the layer.  Turning `M` into the layer constant `Ktot
3^{γ(n+h_n)}` that `layerContrib` wants is precisely the `|b_L|` branch ---
Step 2's business, not this module's --- and it is why `hgood` is left as the
caller's datum here.  Nothing below asserts that a deterministic `Ktot` exists.

## What is *not* proved, and what is carried as data

* The **affine A** associated with `l.piecewise.affine.approx`: its eight
  clauses are the binders `hF`, `hG`, `hFc`, `hGc`, `hbadF`, `hbadG`, `hoffF`,
  `hoffG` of `sum_of_a_decomp_cutoff`, transported binder for binder from
  `sum_of_a_decomp`; and its collar gradient conclusion in the layer-envelope
  reading leaves standing is the pair `hFv`, `hGv` carried *inside*
  `collarCellForm_le_stepOneLayerMajorant_ae`, exactly as `LayerUniform`
  carries it.  Nothing here constructs that source object or asserts it is
  satisfiable, and `Cgrad` is a free real.
* The **collar-vs-bad mass comparison** is `hmasscol`, an explicit A input as
  in `LayerUniform`.  Its twin `hmassgood` is now at the *whole* layer, i.e.
  `LayerMass.sum_cubeMassRatio_whitneyLayer_le` at `Mass n := 6d 3^{-n}`
  discharges it for any caller who pins `Mass` there; it is kept as a binder
  only because `Mass` is a parameter of `layerContrib`.
* The **layer-uniform good constant** `Ktot`: see above.
* The **real-valued join** of `sum_of_a_decomp_cutoff` with
  `ConclusionRoot.tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload` needs
  the finiteness of the intermediate `[0,∞]` sum; it is not performed here, and
  both halves are proved separately so that a consumer can perform it once the
  layer constants are pinned.

## Main results

* `sum_of_a_decomp_cutoff`: `e.sum-of-a-decomp` at the manuscript's own
  coefficient family, right-hand side in the exact two-leg cell shape.
* `goodCellForm_le_stepOneLayerMajorant_ae`,
  `collarCellForm_le_stepOneLayerMajorant_ae`: the two concrete per-cell
  bounds, a.e., uniformly over layers, cubes and cells.
* `collarLayer_zero`: the collar leg vanishes off the collar sub-family.

## References

* ABK26, `e.sum-of-a-decomp` (the display carrying the collar indicators);
  `e.good.simplex.consequence`; Step 1; Step 3;
  `e.bounds.on.slopes.when.bad`; `e.SW.def`; `l.piecewise.affine.approx`;
  `r.gradient.bound.simplified`; `e.homs.defs.U.diag`.
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

/-! ## The coefficient family at the cells of `SW(□_m)` -/

/-- **`aS` of `e.sum-of-a-decomp`, instantiated.**  The coefficient object of
the cutoff `a_L` on one cell of `SW(□_m)`: the restriction of the cell's
support-cube representative, i.e. the very object at which `Step3Seams` and
`LayerUniform` prove Step 1.  Its type is stated at `kuhnCellDomain` because
that is the carrier `sum_of_a_decomp` uses; `simplexDomain` is the same
`Ch02.Domain d`. -/
def cellCutoffCoeffOn (M : ABKModel d) (L : ℤ) (omega : CutoffSample d)
    (T : KuhnCell d) : Ch02.CoeffOn (kuhnCellDomain T) :=
  simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T

/-- The two carriers agree, so the two spellings of the cell's coarse block
matrix agree. -/
theorem coarseBlockMatrix_cellCutoffCoeffOn (M : ABKModel d) (L : ℤ)
    (omega : CutoffSample d) (T : KuhnCell d) :
    Ch02.coarseBlockMatrix (kuhnCellDomain T) (cellCutoffCoeffOn M L omega T) =
      Ch02.coarseBlockMatrix (simplexDomain T)
        (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T) :=
  rfl

/-- **`haS` of `e.sum-of-a-decomp`, discharged.**  Every cube of the cutoff
family carries the *same* representative field `coefficientCutoff M.nu L omega`
(`coefficientCutoffCoeffOn_toCoeffField`), and `restrictCoeffOn` keeps it, so
the cell object and the root-cube object have literally equal representatives.
-/
theorem haS_cellCutoffCoeffOn (M : ABKModel d) (m L : ℤ) (omega : CutoffSample d)
    (T : KuhnCell d) :
    (cellCutoffCoeffOn M L omega T).toCoeffField =
      ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d m)).toCoeffField :=
  rfl

/-! ## The two concrete cell functionals of `e.sum-of-a-decomp` -/

/-- **The good leg's cell functional**: the load's own `𝐀_L(𝔰)` quadratic form,
trimmed by `1_{¬𝓑(𝔰)}`. -/
def goodCellForm (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (L : ℤ)
    (omega : CutoffSample d) (p q : Vec d) (T : KuhnCell d) : ℝ :=
  blockVecDot (p, q)
      (blockMatVecMul
        (Ch02.coarseBlockMatrix (kuhnCellDomain T) (cellCutoffCoeffOn M L omega T)) (p, q)) *
    notBadIndicator M m hn omega T

/-- **The collar leg's cell functional**: the competitor's own `𝐀_L(𝔰)` quadratic
form at its cell constants, trimmed by `1_{¬𝓑(𝔰)}` and by `1_{𝔰 ∈ 𝒩(ℐ)}`. -/
def collarCellForm (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (L : ℤ)
    (omega : CutoffSample d) (Fc Gc : KuhnCell d → Vec d) (T : KuhnCell d) : ℝ :=
  blockVecDot (Fc T, Gc T)
      (blockMatVecMul
        (Ch02.coarseBlockMatrix (kuhnCellDomain T) (cellCutoffCoeffOn M L omega T))
        (Fc T, Gc T)) *
    notBadIndicator M m hn omega T * collarIndicator M m hn omega T

/-! ## `e.sum-of-a-decomp` at the cutoff family -/

/-- **`e.sum-of-a-decomp` at the manuscript's own coefficient family**, with the
right-hand side in the exact cell shape that
`LayerUniform.toReal_tsum_simplexPartition_two_leg_le_payload` consumes:

```
ofReal | (p,q) . 𝐀_L(□_m) (p,q) |
  ≤ ∑'_{𝔰 ∈ SW(□_m)} ( ofReal( (|𝔰|/|□_m|) g_good 𝔰 ) + ofReal( (|𝔰|/|□_m|) g_col 𝔰 ) ) .
```

The coefficient binders `aS`, `haS` of `sum_of_a_decomp` are gone; every
remaining hypothesis is a clause of `l.piecewise.affine.approx` /
`e.hat.linear.properties`, transported verbatim (see the module docstring). -/
theorem sum_of_a_decomp_cutoff [NeZero d] {m : ℤ} {hn : ℕ → ℕ}
    (hstep : ∀ n : ℕ, hn n ≤ hn (n + 1) + 1) (M : ABKModel d) (L : ℤ)
    (omega : CutoffSample d) (p q : Vec d) (F G : Vec d → Vec d)
    (Fc Gc : KuhnCell d → Vec d)
    (hF : Ch01.PotentialZeroTraceFieldOn (openCubeSet (originCube d m))
      fun x => F x - p)
    (hG : Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet (originCube d m))
      fun x => G x - q)
    (hFc : ∀ T ∈ simplexPartition (d := d) m hn, ∀ x ∈ T.openCarrier, F x = Fc T)
    (hGc : ∀ T ∈ simplexPartition (d := d) m hn, ∀ x ∈ T.openCarrier, G x = Gc T)
    (hbadF : ∀ T ∈ simplexPartition (d := d) m hn,
      whitneyCubeOf m hn T ∈ badFamily M m hn omega → Fc T = 0)
    (hbadG : ∀ T ∈ simplexPartition (d := d) m hn,
      whitneyCubeOf m hn T ∈ badFamily M m hn omega → Gc T = 0)
    (hoffF : ∀ T ∈ simplexPartition (d := d) m hn,
      whitneyCubeOf m hn T ∉ whitneyNeighborhood m hn (badFamily M m hn omega) → Fc T = p)
    (hoffG : ∀ T ∈ simplexPartition (d := d) m hn,
      whitneyCubeOf m hn T ∉ whitneyNeighborhood m hn (badFamily M m hn omega) → Gc T = q) :
    ENNReal.ofReal
        |blockVecDot (p, q)
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d m)))
            (p, q))| ≤
      ∑' T : ↥(simplexPartition (d := d) m hn),
        (ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            goodCellForm M m hn L omega p q (T : KuhnCell d)) +
          ENNReal.ofReal (cellWeight m (T : KuhnCell d) *
            collarCellForm M m hn L omega Fc Gc (T : KuhnCell d))) := by
  have hmain := sum_of_a_decomp hstep M omega
    ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d m))
    (fun T => cellCutoffCoeffOn M L omega (T : KuhnCell d))
    (fun T => haS_cellCutoffCoeffOn M m L omega (T : KuhnCell d))
    p q F G (fun T => Fc (T : KuhnCell d)) (fun T => Gc (T : KuhnCell d))
    hF hG (fun T => hFc (T : KuhnCell d) T.2) (fun T => hGc (T : KuhnCell d) T.2)
    (fun T => hbadF (T : KuhnCell d) T.2) (fun T => hbadG (T : KuhnCell d) T.2)
    (fun T => hoffF (T : KuhnCell d) T.2) (fun T => hoffG (T : KuhnCell d) T.2)
  refine hmain.trans (le_of_eq ?_)
  rw [ENNReal.tsum_add]
  refine congrArg₂ (· + ·) (tsum_congr fun T => ?_) (tsum_congr fun T => ?_)
  · exact congrArg ENNReal.ofReal (by simp only [goodCellForm]; ring)
  · exact congrArg ENNReal.ofReal (by simp only [collarCellForm]; ring)

/-! ## The Step-1 majorant, as a layer quantity -/

/-- **The Step-1 majorant at a cell of a Whitney layer**, read at the simplex
carrier.  This is the right-hand side of
`LayerUniform.blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae`, named
so that the two per-cell bounds below can be read.

Every factor depends on `□` only through `□.scale` --- which is constant on a
Whitney layer --- *except* the increment gauge
`‖k_L - k_{□.scale}‖_{W^{1,∞}(□)}²`; see the module docstring. -/
def stepOneLayerMajorant (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) (i L : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) (p q : Vec d) : ℝ :=
  640 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (1 + 8 * bigLambdaSensitivityConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
          (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) *
      vecNormSq p +
    320 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q

theorem stepOneLayerMajorant_nonneg (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ)
    (hn : ℕ → ℕ) (n : ℕ) (i L : ℤ) (omega : CutoffSample d) (Q : TriadicCube d)
    (p q : Vec d) : 0 ≤ stepOneLayerMajorant M m hn n i L omega Q p q := by
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
  have hp : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hq : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hleg1 : (0 : ℝ) ≤ 640 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (1 + 8 * bigLambdaSensitivityConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
        (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) * vecNormSq p :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSnn) hW)
      (by linarith)) hp
  have hleg2 : (0 : ℝ) ≤ 320 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSnn) hW)
      (Real.rpow_nonneg (by norm_num) _)) hq
  rw [stepOneLayerMajorant]
  linarith

/-! ## The two concrete per-cell bounds -/

/-- **The good leg's per-cell bound, concretely.**  Almost surely, for every
layer, every cube of the layer --- bad cubes included, where `1_{¬𝓑}` kills the
term --- and every cell of it, the concrete `g_good` at the framed load
`𝐀hom_i^{-1/2}(p,q)` is at most the Step-1 majorant.

This is `LayerUniform.blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae`
with the indicator put back in; the bad-cube case is the indicator's own
vanishing plus `stepOneLayerMajorant_nonneg`. -/
theorem goodCellForm_le_stepOneLayerMajorant_ae (hd : 2 ≤ d) (M : ABKModel d)
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) (hn : ℕ → ℕ)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, ∀ p q : Vec d,
            goodCellForm M m hn L omega
                ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
                (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) T ≤
              stepOneLayerMajorant M m hn n i L omega Q p q := by
  classical
  filter_upwards
    [blockVecDot_coarseBlockMatrix_whitneySimplexCells_le_ae hd M hS m hn hmi hi]
    with omega hgood n Q hQ L hL T hT p q
  have hcube : whitneyCubeOf m hn T = Q :=
    whitneyCubeOf_of_mem_whitneySimplexCells hQ hT
  by_cases hbad : Q ∈ badFamily M m hn omega
  · have hzero : notBadIndicator M m hn omega T = 0 :=
      notBadIndicator_of_bad (by rw [hcube]; exact hbad)
    rw [goodCellForm, hzero, mul_zero]
    exact stepOneLayerMajorant_nonneg hd M m hn n i L omega Q p q
  · have hnb : omega ∉ BadEvents.bad M Q := fun h => hbad ⟨⟨n, hQ⟩, h⟩
    have hone : notBadIndicator M m hn omega T = 1 :=
      notBadIndicator_of_not_bad (by rw [hcube]; exact hbad)
    rw [goodCellForm, hone, mul_one, coarseBlockMatrix_cellCutoffCoeffOn,
      stepOneLayerMajorant]
    exact hgood n Q hQ hnb L hL T hT p q

/-- Almost surely, for every layer, every cube of the layer, every cell of it,
every load and every competitor cell constants satisfying the collar A of
`e.bounds.on.slopes.when.bad`, the concrete `g_col` at the framed competitor
constants is at most `4 Cgrad² 3^{2b(n+h_n)}` times the Step-1 majorant at the
load `(p, q)` --- the competitor's slopes are traded for the load, so the
majorant argument is the load, not the competitor.

`LayerUniform.blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae`
with the two indicators put back in.  The hypotheses `hFv`, `hGv` are the
conditional A shape of clause 2 of `e.hat.linear.properties` in the reading
leaves standing; they are hypotheses, not theorems of this repository. -/
theorem collarCellForm_le_stepOneLayerMajorant_ae (hd : 2 ≤ d) (M : ABKModel d)
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) (hn : ℕ → ℕ)
    {i : ℤ} (hmi : m - 1 ≤ i) (hi : i ≤ m0) {b Cgrad : ℝ} (hCgrad : 1 ≤ Cgrad)
    (hb : 0 ≤ b) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (n : ℕ) (Q : TriadicCube d), Q ∈ whitneyLayer (d := d) m hn n →
        ∀ L : ℤ, Q.scale ≤ L →
          ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, ∀ Fv Gv : KuhnCell d → Vec d,
            ∀ p q : Vec d,
              vecNormSq (Fv T - p) ≤ Cgrad ^ 2 *
                  (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq p →
              vecNormSq (Gv T - q) ≤ Cgrad ^ 2 *
                  (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ)))) * vecNormSq q →
              collarCellForm M m hn L omega
                  (fun U => (Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • Fv U)
                  (fun U => Real.sqrt
                    ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • Gv U) T ≤
                4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
                  stepOneLayerMajorant M m hn n i L omega Q p q := by
  classical
  filter_upwards
    [blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae hd M hS m hn hmi hi
      hCgrad hb]
    with omega hcol n Q hQ L hL T hT Fv Gv p q hFv hGv
  have hcube : whitneyCubeOf m hn T = Q :=
    whitneyCubeOf_of_mem_whitneySimplexCells hQ hT
  have hpow : (0 : ℝ) ≤ 4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) :=
    mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hmaj : (0 : ℝ) ≤ 4 * (Cgrad ^ 2 * (3 : ℝ) ^ (2 * (b * ((n : ℝ) + (hn n : ℝ))))) *
      stepOneLayerMajorant M m hn n i L omega Q p q :=
    mul_nonneg hpow (stepOneLayerMajorant_nonneg hd M m hn n i L omega Q p q)
  by_cases hbad : Q ∈ badFamily M m hn omega
  · have hzero : notBadIndicator M m hn omega T = 0 :=
      notBadIndicator_of_bad (by rw [hcube]; exact hbad)
    rw [collarCellForm, hzero, mul_zero, zero_mul]
    exact hmaj
  · by_cases hnbhd : Q ∈ whitneyNeighborhood m hn (badFamily M m hn omega)
    · have hnb : omega ∉ BadEvents.bad M Q := fun h => hbad ⟨⟨n, hQ⟩, h⟩
      have hone : notBadIndicator M m hn omega T = 1 :=
        notBadIndicator_of_not_bad (by rw [hcube]; exact hbad)
      have hcolone : collarIndicator M m hn omega T = 1 :=
        collarIndicator_of_mem (by rw [hcube]; exact hnbhd)
      rw [collarCellForm, hone, hcolone, mul_one, mul_one,
        coarseBlockMatrix_cellCutoffCoeffOn, stepOneLayerMajorant]
      exact hcol n Q hQ hnb L hL T hT p q (Fv T) (Gv T) hFv hGv
    · have hcolzero : collarIndicator M m hn omega T = 0 :=
        collarIndicator_of_notMem (by rw [hcube]; exact hnbhd)
      rw [collarCellForm, hcolzero, mul_zero]
      exact hmaj

/-! ## The collar sub-family, and the vanishing of the collar leg off it -/

open Classical in
/-- **`(𝒩(ℐ) ∩ 𝒲(□_m,n))`**, the collar part of one Whitney layer: the sub-family
`S_col` that `LayerUniform.sum_sum_ofReal_two_leg_le_ofReal_layerContrib` takes
on its second leg.  The classification is by *meeting the collar*, which is
exactly what `collarIndicator` performs. -/
def collarLayer (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (omega : CutoffSample d) : Finset (TriadicCube d) :=
  (whitneyLayer (d := d) m hn n).filter
    (fun Q => Q ∈ whitneyNeighborhood m hn (badFamily M m hn omega))

theorem collarLayer_subset (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (omega : CutoffSample d) :
    collarLayer M m hn n omega ⊆ whitneyLayer (d := d) m hn n := by
  classical
  rw [collarLayer]
  exact Finset.filter_subset _ _

/-- **The collar leg vanishes off the collar sub-family** --- the `hcolz` datum
of the two-leg theorems, discharged at the concrete functional. -/
theorem collarLayer_zero (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) (L : ℤ)
    (omega : CutoffSample d) (Fc Gc : KuhnCell d → Vec d) :
    ∀ Q ∈ whitneyLayer (d := d) m hn n, Q ∉ collarLayer M m hn n omega →
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
        collarCellForm M m hn L omega Fc Gc T = 0 := by
  classical
  intro Q hQ hQc T hT
  have hnbhd : Q ∉ whitneyNeighborhood m hn (badFamily M m hn omega) := by
    intro h
    exact hQc (by rw [collarLayer]; exact Finset.mem_filter.2 ⟨hQ, h⟩)
  have hcube : whitneyCubeOf m hn T = Q :=
    whitneyCubeOf_of_mem_whitneySimplexCells hQ hT
  rw [collarCellForm, collarIndicator_of_notMem (by rw [hcube]; exact hnbhd), mul_zero]

/-! ## The Step-3 payload at the two concrete functionals -/


end

end Algsuperdiff.Section3.Provider.Multiscale

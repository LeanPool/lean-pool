/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam3Closure

/-!
# ConclusionSeam1PerCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Seam 1 of Step 3: the per-simplex fourth moment, regrouped onto the cubes

`Provider/Multiscale/ConclusionSeam2.lean` records, in its "What is *not*
proved" list, exactly one geometric gap of the `|b_L|` display of ABK26's
`p.bfA.multiscalebound` Step 3:

> The **first** printed inequality of the display, which converts the
> per-*simplex* fourth moment
> `⨍_{𝔰 ∈ SW(□_n) ∩ 𝒲(□_n,k)} |(k_L - k_{n-k-h_k})_𝔰|⁴` into the per-cube one.
> It needs the piecewise-constant reading of `k` on the cells of `SW(□_m)`,
> which is not proved.

`ConclusionSeam3Closure`'s own list of open items repeats it verbatim.  This
module proves that conversion, in the corrected reading.

## The step, exactly

`(h)_𝔰` is read as the manuscript reads it: the constant value that a
piecewise-affine field takes on the cell, i.e. its **cell mean** `⨍_𝔰 h`
(CoarseGraining's `volumeAverageMat T.openCarrier`).  With that reading the
step is Jensen on each cell followed by the exact tiling of a Whitney cube by
its cells:

```
∑_{𝔰 ∈ S(□)} (|𝔰|/|□_m|) |(k_L − k_j)_𝔰|⁴
      ≤ C(d) · (|□|/|□_m|) ⨍_□ |k_L − k_j|⁴ ,
```

`sum_cellWeight_mul_simplexIncrementFourth_le`, and its sum over the Whitney
layer `𝒲(□_m,k)` is `layerSimplexFourthMass_le`.  Under the square root and the
display's own prefactor `γ 3^{−2γℓ}` this is
`seamSimplexObject_le_mul_seamLayerObject`: the per-simplex object is bounded
by `√(C(d))` times `ConclusionSeam3.seamLayerObject`, the per-cube object that
seams 2 and 3 already price.

The weight `|𝔰|/|□_m|` is the proved `SubadditiveDecomposition.cellWeight`,
i.e. the weight the manuscript's own subadditive decomposition carries (
`e.sum-of-a-decomp`); the cube weight `|□|/|□_m|` is the proved
`cubeMassRatio`.

## The constant, disclosed

`simplexToCubeConst d = d⁴`.  It is a **dimension-only** constant and it sits
under the printed `C`.  Nothing else is lost: the two Jensen steps and the
regrouping are sharp.  A constant-free route would need `‖⨍_𝔰 h‖ ≤ ⨍_𝔰 ‖h‖` for
the Euclidean operator norm, which is not proved anywhere (CoarseGraining has
only the *finite-sum* form
`matrixOperatorNorm_descendantsAverageMat_le_descendantsAverage`), and is not
proved here.

## The average convention, stated plainly (NOT hidden)

The printed display writes `\avsum` --- the **cardinal** average `|A|⁻¹ ∑`, ---
over the simplices of the layer, and again over the cubes.  The corrected route
replaces the cube-side cardinal average by the **volume-weighted** sum `∑_□
(|□|/|□_m|)`, and that is the object `ConclusionSeam2PerCube` /
`ConclusionSeam3` carry.  This module therefore runs the simplex side in the
same volume-weighted normalization --- which is also the normalization of the
manuscript's *own* subadditive decomposition, where the simplex sum first
appears with the weights `|𝔰|/|□_n|`.  The two normalizations differ by the
layer's mass fraction `W_k = ∑_{□ ∈ 𝒲(□_m,k)} |□|/|□_m|`, and the identity `W_k
= ∑_{𝔰 ∈ layer} |𝔰|/|□_m|` **is** proved here
(`sum_cellWeight_whitneySimplexCells_eq`, summed over the layer).  See "What is
*not* proved".

## What is *not* proved

* **No cardinal-average form.**  Nothing below states the printed `⨍_{𝔰 ∈
  SW(□_n) ∩ 𝒲(□_n,k)}`; see the paragraph above.  The exact missing input is
  `volume (KuhnCell.openCarrier T) = cubeVolume T.supportCube / d !`
  (equivalently: any two cells of one cube have equal volume).
* **No `|b_L|` assembly.**  The display's first inequality also *produces* the
  per-simplex sum from `σ_{m-1}^{-1}|b_L(□_n)| − C`, through
  `e.sum-of-a-decomp`, `e.good.simplex.consequence`,
  `e.bounds.on.slopes.when.bad`, `l.bad.cubes.density` and Hölder.  None of
  that is here: this module proves only the per-simplex → per-cube conversion
  of the *fourth-moment factor*.
* **No per-layer weight and no `k`-sum.** records that the printed `C 3^{−3k/4}(1 +
  3^{2bh_hat_sep}e^{−cE⁻²γ⁻¹})` is not derivable in the corrected degree-2 reading;
  no sum over `k` is formed below and no per-layer weight is produced, used or
  approached.
* **The printed step is neither stated nor used.**'s false transition (→ 6468,
  `√(av X²) ≤ av X`) does not appear: the square root stays outside the
  volume-weighted fourth mass throughout.
* **No `e.bL.multiscale` headline**, no `k₀` tuning, no terminal
  `exp(−cE⁻²γ⁻¹)` absorption, no seam-3 `h_hat_sep` reconciliation (the composition
  theorems below inherit `ConclusionSeam3`'s own indices character for
  character).
* **No face-to-face or simplicial-complex property** of `SW(□_m)`, and no claim
  that the *closed* cells cover: the tiling used is the proved exact half-open
  one plus the proved null boundary.

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.matrixOperatorNorm_simplexIncrementValue_pow_four_le`
* `Algsuperdiff.Section3.Provider.Multiscale.sum_cellWeight_mul_volumeAverage_eq`
* `Algsuperdiff.Section3.Provider.Multiscale.sum_cellWeight_whitneySimplexCells_eq`
* `Algsuperdiff.Section3.Provider.Multiscale.sum_cellWeight_mul_simplexIncrementFourth_le`
* `Algsuperdiff.Section3.Provider.Multiscale.layerSimplexFourthMass_le`
* `Algsuperdiff.Section3.Provider.Multiscale.seamSimplexObject_le_mul_seamLayerObject`

## References

* ABK26, `p.bfA.multiscalebound` Step 3, the `|b_L|` branch (`align*`; first
  inequality); `\avsum`; `e.SW.def`; `e.simplex.def` and the simplex volume;
  `e.sum-of-a-decomp`; the cell value `(·)_𝔰`; `e.kmn.bounds`.
* `Provider/Whitney/SimplexPartition.lean` (`SW(□_m)` and its exact tiling),
  `Provider/Multiscale/SimplexDomains.lean` (the null cell boundary),
  `Provider/Multiscale/SubadditiveDecomposition.lean` (`cellWeight`),
  `Provider/Multiscale/Step3Seams.lean` (`cubeMassRatio_originCube_eq_div`),
  `Provider/Multiscale/ConclusionSeam3.lean` (`seamLayerObject`, the consumers),
  `Provider/Multiscale/ConclusionSeam2.lean` and
  `Provider/Multiscale/ConclusionSeam3Closure.lean` (the proved local `Γ₁`
  results consumed by the composition theorems; the single import of this
  module is the latter, which is already in the dependency cone of
  `Algsuperdiff/Section3.lean`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Elementary matrix-norm arithmetic

Both directions of the Frobenius comparison, in squared form.  These are
CoarseGraining's proved `matrixOperatorNorm_le_matrixFrobeniusNorm` and
`abs_entry_le_matrixOperatorNorm`, restated at the exponent the fourth moment
uses. -/

private theorem matrixOperatorNorm_sq_le_matrixFrobeniusNormSq (A : Mat d) :
    Book.Ch02.matrixOperatorNorm A ^ 2 ≤ Book.Ch02.matrixFrobeniusNormSq A := by
  have h := pow_le_pow_left₀ (Book.Ch02.matrixOperatorNorm_nonneg A)
    (Book.Ch02.matrixOperatorNorm_le_matrixFrobeniusNorm A) 2
  have hsq : Book.Ch02.matrixFrobeniusNorm A ^ 2 = Book.Ch02.matrixFrobeniusNormSq A := by
    simp only [Book.Ch02.matrixFrobeniusNorm]
    exact Real.sq_sqrt (Book.Ch02.matrixFrobeniusNormSq_nonneg A)
  rwa [hsq] at h

private theorem matrixFrobeniusNormSq_le_dim_sq_mul (A : Mat d) :
    Book.Ch02.matrixFrobeniusNormSq A ≤ (d : ℝ) ^ 2 * Book.Ch02.matrixOperatorNorm A ^ 2 := by
  have hentry : ∀ i j : Fin d, A i j ^ 2 ≤ Book.Ch02.matrixOperatorNorm A ^ 2 := by
    intro i j
    have h := pow_le_pow_left₀ (abs_nonneg (A i j))
      (Book.Ch02.abs_entry_le_matrixOperatorNorm A i j) 2
    rwa [sq_abs] at h
  calc Book.Ch02.matrixFrobeniusNormSq A = ∑ _i : Fin d, ∑ _j : Fin d, A _i _j ^ 2 := rfl
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, Book.Ch02.matrixOperatorNorm A ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (d : ℝ) ^ 2 * Book.Ch02.matrixOperatorNorm A ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## The cell as a set of positive finite volume -/

private theorem volume_openCarrier_ne_top (T : KuhnCell d) :
    volume T.openCarrier ≠ ⊤ :=
  (isBoundedDomain_openCarrier T).volume_lt_top.ne

private theorem toReal_volume_openCarrier_pos (T : KuhnCell d) :
    0 < (volume T.openCarrier).toReal :=
  ENNReal.toReal_pos
    ((isOpen_openCarrier T).measure_pos volume (openCarrier_nonempty T)).ne'
    (volume_openCarrier_ne_top T)

/-! ## Integrability on a cell

Every integrand below is continuous, and a cell is contained in the closed ball
around its support cube; this is the containment chain the proved
`integrableOn_cubeSet_streamIncrementLpDensity` already uses. -/

/-- The `L^p` density of a stream increment is integrable on a Kuhn cell. -/
theorem integrableOn_openCarrier_streamIncrementLpDensity {p : ℝ} (hp : 0 < p)
    (T : KuhnCell d) (n m : ℤ) (omega : ShellSeq d) :
    IntegrableOn (streamIncrementLpDensity p n m omega) T.openCarrier volume :=
  (integrableOn_cubeSet_streamIncrementLpDensity hp T.supportCube n m omega).mono_set
    (T.openCarrier_subset_carrier.trans T.carrier_subset_cubeSet)

private theorem streamIncrementLpDensity_ofNat (k : ℕ) (n m : ℤ) (omega : ShellSeq d)
    (x : Vec d) :
    streamIncrementLpDensity (k : ℝ) n m omega x =
      Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x) ^ k := by
  rw [streamIncrementLpDensity, Real.rpow_natCast]

private theorem integrableOn_openCarrier_entry (T : KuhnCell d) (n m : ℤ)
    (omega : ShellSeq d) (i j : Fin d) :
    IntegrableOn (fun x : Vec d => finiteShellIncrement omega n m x i j)
      T.openCarrier volume := by
  refine Integrable.mono'
    (integrableOn_openCarrier_streamIncrementLpDensity (p := 1) one_pos T n m omega)
    (continuous_finiteShellIncrement_entry omega n m i j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num,
    streamIncrementLpDensity_ofNat]
  simpa using Book.Ch02.abs_entry_le_matrixOperatorNorm (finiteShellIncrement omega n m x) i j

private theorem integrableOn_openCarrier_entry_sq (T : KuhnCell d) (n m : ℤ)
    (omega : ShellSeq d) (i j : Fin d) :
    IntegrableOn (fun x : Vec d => finiteShellIncrement omega n m x i j ^ 2)
      T.openCarrier volume := by
  refine Integrable.mono'
    (integrableOn_openCarrier_streamIncrementLpDensity (p := 2) two_pos T n m omega)
    (((continuous_finiteShellIncrement_entry omega n m i j).pow 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    streamIncrementLpDensity_ofNat, abs_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (abs_nonneg (finiteShellIncrement omega n m x i j))
    (Book.Ch02.abs_entry_le_matrixOperatorNorm (finiteShellIncrement omega n m x) i j) 2
  rwa [sq_abs] at h

private theorem continuous_matrixFrobeniusNormSq_finiteShellIncrement (n m : ℤ)
    (omega : ShellSeq d) :
    Continuous fun x : Vec d =>
      Book.Ch02.matrixFrobeniusNormSq (finiteShellIncrement omega n m x) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_finiteShellIncrement_entry omega n m i j).pow 2

private theorem integrableOn_openCarrier_frobeniusNormSq (T : KuhnCell d) (n m : ℤ)
    (omega : ShellSeq d) :
    IntegrableOn
      (fun x : Vec d => Book.Ch02.matrixFrobeniusNormSq (finiteShellIncrement omega n m x))
      T.openCarrier volume := by
  refine Integrable.mono'
    (((integrableOn_openCarrier_streamIncrementLpDensity (p := 2) two_pos T n m
      omega).const_mul ((d : ℝ) ^ 2)))
    (continuous_matrixFrobeniusNormSq_finiteShellIncrement n m omega).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Book.Ch02.matrixFrobeniusNormSq_nonneg _),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, streamIncrementLpDensity_ofNat]
  exact matrixFrobeniusNormSq_le_dim_sq_mul _

/-! ## Two elementary facts about the CoarseGraining volume average

The monotone form and the squared Jensen. -/

private theorem volumeAverage_mono {U : Set (Vec d)} (hU : MeasurableSet U)
    {f g : Vec d → ℝ} (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume)
    (hle : ∀ x ∈ U, f x ≤ g x) :
    volumeAverage U f ≤ volumeAverage U g := by
  have hnn : 0 ≤ volumeAverage U (g - f) :=
    volumeAverage_nonneg_of_nonneg_on hU fun x hx => by
      simpa [Pi.sub_apply] using sub_nonneg.2 (hle x hx)
  rw [volumeAverage_sub hg hf] at hnn
  linarith

private theorem sq_volumeAverage_le {U : Set (Vec d)} (hU : MeasurableSet U)
    (hvol : (volume U).toReal ≠ 0) {g : Vec d → ℝ}
    (hg : IntegrableOn g U volume) (hg2 : IntegrableOn (fun x => g x ^ 2) U volume) :
    volumeAverage U g ^ 2 ≤ volumeAverage U fun x => g x ^ 2 := by
  set a : ℝ := volumeAverage U g with ha
  have hfin : volume U ≠ ⊤ := (ENNReal.toReal_ne_zero.mp hvol).2
  have hconst : IntegrableOn (fun _ : Vec d => a ^ 2) U volume :=
    integrableOn_const hfin (by simp)
  have hsmul : IntegrableOn ((2 * a) • g) U volume := hg.smul (2 * a)
  have hdiff : IntegrableOn ((fun x => g x ^ 2) - (2 * a) • g) U volume := hg2.sub hsmul
  have hfun : (fun x => (g x - a) ^ 2)
      = ((fun x => g x ^ 2) - (2 * a) • g) + fun _ : Vec d => a ^ 2 := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnn : 0 ≤ volumeAverage U fun x => (g x - a) ^ 2 :=
    volumeAverage_nonneg_of_nonneg_on hU fun x _ => sq_nonneg _
  have hexp : (volumeAverage U fun x => (g x - a) ^ 2)
      = (volumeAverage U fun x => g x ^ 2) - a ^ 2 := by
    rw [hfun, volumeAverage_add hdiff hconst, volumeAverage_sub hg2 hsmul,
      volumeAverage_smul, volumeAverage_const hvol, ← ha]
    ring
  linarith [hnn, hexp.symm.le, hexp.le]

/-! ## The cell value of the stream increment, and the per-cell Jensen -/

/-- The dimension-only constant of the per-simplex to per-cube step, `d⁴`.  See the
module docstring: it is the price of scalarizing the Euclidean operator norm
through the Frobenius norm, and it sits under the printed `C`. -/
def simplexToCubeConst (d : ℕ) : ℝ := (d : ℝ) ^ 4


/-- **The manuscript's `(k_m − k_n)_𝔰`**: the constant value of the stream
increment on a cell of `SW(□_m)`, read as the cell mean. -/
def simplexIncrementValue (n m : ℤ) (omega : ShellSeq d) (T : KuhnCell d) : Mat d :=
  volumeAverageMat T.openCarrier (finiteShellIncrement omega n m)

/-- **The per-simplex fourth moment `|(k_m − k_n)_𝔰|⁴`**, in the exact Euclidean
matrix operator norm the whole `Stream` chain uses. -/
def simplexIncrementFourth (n m : ℤ) (omega : ShellSeq d) (T : KuhnCell d) : ℝ :=
  Book.Ch02.matrixOperatorNorm (simplexIncrementValue n m omega T) ^ 4

theorem simplexIncrementFourth_nonneg (n m : ℤ) (omega : ShellSeq d) (T : KuhnCell d) :
    0 ≤ simplexIncrementFourth n m omega T := by
  rw [simplexIncrementFourth]; positivity

/-- **The per-cell Jensen step.**  The fourth power of the cell value is dominated
by `d⁴` times the cell average of the fourth-power density.  Two squared Jensen
applications and CoarseGraining's Frobenius pair; no hypothesis at all. -/
theorem matrixOperatorNorm_simplexIncrementValue_pow_four_le (T : KuhnCell d) (n m : ℤ)
    (omega : ShellSeq d) :
    simplexIncrementFourth n m omega T
      ≤ simplexToCubeConst d *
        volumeAverage T.openCarrier (streamIncrementLpDensity 4 n m omega) := by
  classical
  have hU : MeasurableSet T.openCarrier := (isOpen_openCarrier T).measurableSet
  have hvol : (volume T.openCarrier).toReal ≠ 0 := (toReal_volume_openCarrier_pos T).ne'
  have hdens2 : IntegrableOn (streamIncrementLpDensity 2 n m omega) T.openCarrier volume :=
    integrableOn_openCarrier_streamIncrementLpDensity two_pos T n m omega
  have hdens4 : IntegrableOn (streamIncrementLpDensity 4 n m omega) T.openCarrier volume :=
    integrableOn_openCarrier_streamIncrementLpDensity (by norm_num) T n m omega
  -- The Frobenius square of the cell value is the double sum of the entry averages.
  have hfrob : Book.Ch02.matrixFrobeniusNormSq (simplexIncrementValue n m omega T)
      = ∑ i : Fin d, ∑ j : Fin d,
          (volumeAverage T.openCarrier
            fun x => finiteShellIncrement omega n m x i j) ^ 2 := rfl
  -- Entrywise Jensen.
  have hentry : ∀ i : Fin d, ∀ j : Fin d,
      (volumeAverage T.openCarrier fun x => finiteShellIncrement omega n m x i j) ^ 2
        ≤ volumeAverage T.openCarrier
            fun x => finiteShellIncrement omega n m x i j ^ 2 := fun i j =>
    sq_volumeAverage_le hU hvol (integrableOn_openCarrier_entry T n m omega i j)
      (integrableOn_openCarrier_entry_sq T n m omega i j)
  -- Linearity of the average over the double sum.
  have hsumj : ∀ i : Fin d,
      (∑ j : Fin d, volumeAverage T.openCarrier
          fun x => finiteShellIncrement omega n m x i j ^ 2)
        = volumeAverage T.openCarrier
            fun x => ∑ j : Fin d, finiteShellIncrement omega n m x i j ^ 2 := fun i =>
    (volumeAverage_sum (U := T.openCarrier) Finset.univ
      (fun j x => finiteShellIncrement omega n m x i j ^ 2)
      fun j _ => integrableOn_openCarrier_entry_sq T n m omega i j).symm
  have hsumi : (∑ i : Fin d, volumeAverage T.openCarrier
        fun x => ∑ j : Fin d, finiteShellIncrement omega n m x i j ^ 2)
      = volumeAverage T.openCarrier
          fun x => Book.Ch02.matrixFrobeniusNormSq (finiteShellIncrement omega n m x) :=
    (volumeAverage_sum (U := T.openCarrier) Finset.univ
      (fun i x => ∑ j : Fin d, finiteShellIncrement omega n m x i j ^ 2)
      fun i _ => by
        refine MeasureTheory.integrable_finsetSum _ fun j _ => ?_
        exact integrableOn_openCarrier_entry_sq T n m omega i j).symm
  -- The squared step.
  have hsq : Book.Ch02.matrixOperatorNorm (simplexIncrementValue n m omega T) ^ 2
      ≤ (d : ℝ) ^ 2 * volumeAverage T.openCarrier (streamIncrementLpDensity 2 n m omega) := by
    have h1 := matrixOperatorNorm_sq_le_matrixFrobeniusNormSq
      (simplexIncrementValue n m omega T)
    rw [hfrob] at h1
    have h2 : (∑ i : Fin d, ∑ j : Fin d,
        (volumeAverage T.openCarrier fun x => finiteShellIncrement omega n m x i j) ^ 2)
        ≤ ∑ i : Fin d, ∑ j : Fin d, volumeAverage T.openCarrier
            fun x => finiteShellIncrement omega n m x i j ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    have h3 : (∑ i : Fin d, ∑ j : Fin d, volumeAverage T.openCarrier
        fun x => finiteShellIncrement omega n m x i j ^ 2)
        = volumeAverage T.openCarrier
            fun x => Book.Ch02.matrixFrobeniusNormSq (finiteShellIncrement omega n m x) := by
      rw [← hsumi]
      exact Finset.sum_congr rfl fun i _ => hsumj i
    have h4 : (volumeAverage T.openCarrier
        fun x => Book.Ch02.matrixFrobeniusNormSq (finiteShellIncrement omega n m x))
        ≤ volumeAverage T.openCarrier
            fun x => (d : ℝ) ^ 2 * streamIncrementLpDensity 2 n m omega x := by
      refine volumeAverage_mono hU (integrableOn_openCarrier_frobeniusNormSq T n m omega)
        (hdens2.const_mul _) fun x _ => ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, streamIncrementLpDensity_ofNat]
      exact matrixFrobeniusNormSq_le_dim_sq_mul _
    have h5 : (volumeAverage T.openCarrier
        fun x => (d : ℝ) ^ 2 * streamIncrementLpDensity 2 n m omega x)
        = (d : ℝ) ^ 2 * volumeAverage T.openCarrier (streamIncrementLpDensity 2 n m omega) :=
      volumeAverage_smul T.openCarrier ((d : ℝ) ^ 2) _
    linarith [h1, h2, h3.le, h3.ge, h4, h5.le, h5.ge]
  -- The outer squared Jensen.
  have hout : (volumeAverage T.openCarrier (streamIncrementLpDensity 2 n m omega)) ^ 2
      ≤ volumeAverage T.openCarrier (streamIncrementLpDensity 4 n m omega) := by
    have h := sq_volumeAverage_le hU hvol hdens2
      (by
        have : (fun x : Vec d => streamIncrementLpDensity 2 n m omega x ^ 2)
            = streamIncrementLpDensity 4 n m omega := by
          funext x
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
            streamIncrementLpDensity_ofNat, streamIncrementLpDensity_ofNat, ← pow_mul]
        rw [this]
        exact hdens4)
    have heq : (volumeAverage T.openCarrier
        fun x => streamIncrementLpDensity 2 n m omega x ^ 2)
        = volumeAverage T.openCarrier (streamIncrementLpDensity 4 n m omega) := by
      congr 1
      funext x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        streamIncrementLpDensity_ofNat, streamIncrementLpDensity_ofNat, ← pow_mul]
    rwa [heq] at h
  have hnn : 0 ≤ volumeAverage T.openCarrier (streamIncrementLpDensity 2 n m omega) :=
    volumeAverage_nonneg_of_nonneg_on hU fun x _ => streamIncrementLpDensity_nonneg _ _ _ _ _
  have hfinal := pow_le_pow_left₀ (sq_nonneg
    (Book.Ch02.matrixOperatorNorm (simplexIncrementValue n m omega T))) hsq 2
  rw [simplexIncrementFourth, simplexToCubeConst]
  calc Book.Ch02.matrixOperatorNorm (simplexIncrementValue n m omega T) ^ 4
      = (Book.Ch02.matrixOperatorNorm (simplexIncrementValue n m omega T) ^ 2) ^ 2 := by
        ring
    _ ≤ ((d : ℝ) ^ 2 *
          volumeAverage T.openCarrier (streamIncrementLpDensity 2 n m omega)) ^ 2 := hfinal
    _ = (d : ℝ) ^ 4 *
          (volumeAverage T.openCarrier (streamIncrementLpDensity 2 n m omega)) ^ 2 := by ring
    _ ≤ (d : ℝ) ^ 4 *
          volumeAverage T.openCarrier (streamIncrementLpDensity 4 n m omega) := by
        exact mul_le_mul_of_nonneg_left hout (by positivity)

/-! ## Regrouping the cells of one Whitney cube

The cells of a layer-`k` Whitney cube tile it exactly in the half-open
realization, and each cell exceeds its open realization by a null set; so the
open cells exhaust the cube up to a null set, and the integral over the cube
splits as a finite sum over the cells. -/

private theorem iUnion_openCarrier_ae_eq_cubeSet {m : ℤ} {hn : ℕ → ℕ} {k : ℕ}
    (hstep : hn k ≤ hn (k + 1) + 1) {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn k) :
    (⋃ T ∈ (whitneySimplexCells (d := d) m hn k Q : Set (KuhnCell d)), T.openCarrier)
      =ᵐ[volume] cubeSet Q := by
  classical
  have htile : cubeSet Q
      = ⋃ T ∈ (whitneySimplexCells (d := d) m hn k Q : Set (KuhnCell d)), T.carrier :=
    cubeSet_eq_iUnion_whitneySimplexCells hstep hQ
  have hsub : (⋃ T ∈ (whitneySimplexCells (d := d) m hn k Q : Set (KuhnCell d)),
      T.openCarrier) ⊆ cubeSet Q := by
    rw [htile]
    exact Set.iUnion₂_mono fun T _ => T.openCarrier_subset_carrier
  refine MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩
  · rw [Set.sdiff_eq_empty.2 hsub]
    exact measure_empty
  · refine measure_mono_null ?_
      (measure_biUnion_null_iff (Set.to_countable
        ((whitneySimplexCells (d := d) m hn k Q : Set (KuhnCell d)))) |>.2
        fun T _ => volume_carrier_diff_openCarrier T)
    intro x hx
    have hxU : x ∈ ⋃ T ∈ (whitneySimplexCells (d := d) m hn k Q : Set (KuhnCell d)),
        T.carrier := by
      rw [← htile]
      exact hx.1
    obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hxU
    refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, hxT, ?_⟩⟩
    intro hxo
    exact hx.2 (Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, hxo⟩⟩)

/-- **The regrouping, as an exact identity.**  For an integrand integrable on a
layer-`k` Whitney cube `□`, the `e.sum-of-a-decomp` weighted sum of the cell
means over the cells of `□` is the `cubeMassRatio`-weighted cube mean.

No cell volume is evaluated: it cancels between the weight `|𝔰|/|□_m|` and the
normalization of the cell mean.  This is why the unproved simplex volume
`|△_n^π| = 3^{dn}/d!` is not needed. -/
theorem sum_cellWeight_mul_volumeAverage_eq {m : ℤ} {hn : ℕ → ℕ} {k : ℕ}
    (hstep : hn k ≤ hn (k + 1) + 1) {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn k)
    {f : Vec d → ℝ} (hf : IntegrableOn f (cubeSet Q) volume) :
    (∑ T ∈ whitneySimplexCells (d := d) m hn k Q,
        cellWeight m T * volumeAverage T.openCarrier f)
      = cubeMassRatio (originCube d m) Q * cubeAverage Q f := by
  classical
  have hroot : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  have hQvol : (0 : ℝ) < cubeVolume Q := cubeVolume_pos _
  have hcellsub : ∀ T ∈ whitneySimplexCells (d := d) m hn k Q,
      T.openCarrier ⊆ cubeSet Q := by
    intro T hT
    exact T.openCarrier_subset_carrier.trans
      (carrier_subset_cubeSet_of_mem_whitneySimplexCells hT)
  -- termwise: the cell volume cancels
  have hterm : ∀ T ∈ whitneySimplexCells (d := d) m hn k Q,
      cellWeight m T * volumeAverage T.openCarrier f
        = (cubeVolume (originCube d m))⁻¹ * ∫ x in T.openCarrier, f x := by
    intro T _
    have hTpos : (0 : ℝ) < (volume T.openCarrier).toReal := toReal_volume_openCarrier_pos T
    rw [cellWeight, volumeAverage, volume_openCubeSet_toReal]
    field_simp
  -- the finite additivity of the integral over the open cells
  have hint : ∀ T ∈ whitneySimplexCells (d := d) m hn k Q,
      IntegrableOn f T.openCarrier volume := fun T hT => hf.mono_set (hcellsub T hT)
  have hsplit : (∫ x in ⋃ T ∈ whitneySimplexCells (d := d) m hn k Q, T.openCarrier, f x)
      = ∑ T ∈ whitneySimplexCells (d := d) m hn k Q, ∫ x in T.openCarrier, f x :=
    MeasureTheory.integral_biUnion_finset _
      (fun T _ => (isOpen_openCarrier T).measurableSet)
      (triadicSimplexPartition_openCarrier_pairwiseDisjoint Q (simplexScale m hn k)) hint
  have hcube : (∫ x in ⋃ T ∈ whitneySimplexCells (d := d) m hn k Q, T.openCarrier, f x)
      = ∫ x in cubeSet Q, f x :=
    MeasureTheory.setIntegral_congr_set (iUnion_openCarrier_ae_eq_cubeSet hstep hQ)
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hsplit, hcube,
    cubeMassRatio_originCube_eq_div, cubeAverage]
  field_simp

/-- **The layer mass fraction, at the simplices.**  Taking `f = 1` in the
regrouping identity: the cells of a layer-`k` Whitney cube carry exactly the
cube's own mass.  This upgrades the proved inequality
`Step3Seams.sum_cellWeight_whitneySimplexCells_le` to an equality, and it is
half of the dictionary between the printed cardinal average and the
volume-weighted sum (the other half --- equal cell volumes --- is not proved;
see the module docstring). -/
theorem sum_cellWeight_whitneySimplexCells_eq {m : ℤ} {hn : ℕ → ℕ} {k : ℕ}
    (hstep : hn k ≤ hn (k + 1) + 1) {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn k) :
    (∑ T ∈ whitneySimplexCells (d := d) m hn k Q, cellWeight m T)
      = cubeMassRatio (originCube d m) Q := by
  classical
  have hone : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (cubeSet Q) volume :=
    integrableOn_const (volume_cubeSet_lt_top Q).ne (by simp)
  have h := sum_cellWeight_mul_volumeAverage_eq hstep hQ hone
  have hcell : ∀ T ∈ whitneySimplexCells (d := d) m hn k Q,
      cellWeight m T * volumeAverage T.openCarrier (fun _ : Vec d => (1 : ℝ))
        = cellWeight m T := by
    intro T _
    rw [volumeAverage_const (toReal_volume_openCarrier_pos T).ne', mul_one]
  have hQavg : cubeAverage Q (fun _ : Vec d => (1 : ℝ)) = 1 := by
    rw [cubeAverage, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      volume_cubeSet_toReal, smul_eq_mul, mul_one, inv_mul_cancel₀ (cubeVolume_pos Q).ne']
  rw [Finset.sum_congr rfl hcell] at h
  rw [h, hQavg, mul_one]

/-- **The per-simplex to per-cube step at one Whitney cube.**  Jensen on each
cell, then the exact regrouping. -/
theorem sum_cellWeight_mul_simplexIncrementFourth_le {m : ℤ} {hn : ℕ → ℕ} {k : ℕ}
    (hstep : hn k ≤ hn (k + 1) + 1) {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn k)
    (n1 n2 : ℤ) (omega : ShellSeq d) :
    (∑ T ∈ whitneySimplexCells (d := d) m hn k Q,
        cellWeight m T * simplexIncrementFourth n1 n2 omega T)
      ≤ simplexToCubeConst d *
        (cubeMassRatio (originCube d m) Q *
          cubeAverage Q (streamIncrementLpDensity 4 n1 n2 omega)) := by
  classical
  have hstepwise : (∑ T ∈ whitneySimplexCells (d := d) m hn k Q,
      cellWeight m T * simplexIncrementFourth n1 n2 omega T)
      ≤ ∑ T ∈ whitneySimplexCells (d := d) m hn k Q,
        simplexToCubeConst d *
          (cellWeight m T *
            volumeAverage T.openCarrier (streamIncrementLpDensity 4 n1 n2 omega)) := by
    refine Finset.sum_le_sum fun T _ => ?_
    have h := matrixOperatorNorm_simplexIncrementValue_pow_four_le T n1 n2 omega
    calc cellWeight m T * simplexIncrementFourth n1 n2 omega T
        ≤ cellWeight m T * (simplexToCubeConst d *
            volumeAverage T.openCarrier (streamIncrementLpDensity 4 n1 n2 omega)) :=
          mul_le_mul_of_nonneg_left h (cellWeight_nonneg m T)
      _ = simplexToCubeConst d * (cellWeight m T *
            volumeAverage T.openCarrier (streamIncrementLpDensity 4 n1 n2 omega)) := by ring
  rw [← Finset.mul_sum] at hstepwise
  rwa [sum_cellWeight_mul_volumeAverage_eq hstep hQ
    ((integrableOn_cubeSet_streamIncrementLpDensity (by norm_num) Q n1 n2 omega))]
    at hstepwise

/-! ## The Whitney layer, and the display -/

/-- **The per-simplex fourth mass of the Whitney layer `SW(□_m) ∩ 𝒲(□_m,k)`**, in
the volume-weighted normalization of `e.sum-of-a-decomp`.  The index set is the
layer's own cell family, written as the iterated sum over the layer's cubes and
their cells. -/
def layerSimplexFourthMass (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) (n1 n2 : ℤ)
    (omega : CutoffSample d) : ℝ :=
  ∑ Q ∈ whitneyLayer (d := d) m hn k, ∑ T ∈ whitneySimplexCells (d := d) m hn k Q,
    cellWeight m T * simplexIncrementFourth n1 n2 omega.1 T


/-- **The per-simplex to per-cube step, over the whole Whitney layer.**  This is
the fourth-moment content of the display's first printed inequality, in the
corrected reading: the right-hand side is the volume-weighted layer fourth mass
that `ConclusionSeam2PerCube` and `ConclusionSeam3` price. -/
theorem layerSimplexFourthMass_le {m : ℤ} {hn : ℕ → ℕ} {k : ℕ}
    (hstep : hn k ≤ hn (k + 1) + 1) (n1 n2 : ℤ) (omega : CutoffSample d) :
    layerSimplexFourthMass m hn k n1 n2 omega
      ≤ simplexToCubeConst d *
        ∑ Q ∈ whitneyLayer (d := d) m hn k, cubeMassRatio (originCube d m) Q *
          cubeAverage Q (streamIncrementLpDensity 4 n1 n2 omega.1) := by
  classical
  rw [layerSimplexFourthMass, Finset.mul_sum]
  exact Finset.sum_le_sum fun Q hQ =>
    sum_cellWeight_mul_simplexIncrementFourth_le hstep hQ n1 n2 omega.1

/-- **The display's per-simplex left-hand object** (with the prefactor pulled out
of the square root): `γ 3^{−2γℓ} (∑_{𝔰} (|𝔰|/|□_m|) |(k_L −
k_{ℓ−h})_𝔰|⁴)^{1/2}`. -/
def seamSimplexObject (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) (ell : ℤ) (h : ℕ)
    (L : ℤ) (omega : CutoffSample d) : ℝ :=
  M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) *
    Real.sqrt (layerSimplexFourthMass m hn k (ell - (h : ℤ)) L omega)


/-- **The step, at the display.**  The per-simplex object of the `b_L` display's first
printed inequality is bounded by `√(simplexToCubeConst d) = d²` times
`ConclusionSeam3.seamLayerObject`, the per-cube object that seams 2 and 3
already price.  Everything is pathwise and deterministic: no Orlicz index is
created or moved. -/
theorem seamSimplexObject_le_mul_seamLayerObject (M : ABKModel d) {m : ℤ} {hn : ℕ → ℕ}
    {k : ℕ} (hstep : hn k ≤ hn (k + 1) + 1) (ell : ℤ) (h : ℕ) (L : ℤ)
    (omega : CutoffSample d) :
    seamSimplexObject M m hn k ell h L omega
      ≤ (d : ℝ) ^ 2 * seamLayerObject M m hn k ell h L omega := by
  have hmass := layerSimplexFourthMass_le (m := m) (hn := hn) (k := k) hstep
    (ell - (h : ℤ)) L omega
  have hpref : 0 ≤ M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) :=
    mul_nonneg M.shellPrefix.gamma_pos.le (Real.rpow_nonneg (by norm_num) _)
  have hsum : 0 ≤ ∑ Q ∈ whitneyLayer (d := d) m hn k,
      cubeMassRatio (originCube d m) Q *
        cubeAverage Q (streamIncrementLpDensity 4 (ell - (h : ℤ)) L omega.1) :=
    Finset.sum_nonneg fun Q _ => mul_nonneg (cubeMassRatio_nonneg _ Q)
      (cubeAverage_nonneg_of_nonneg_on fun x _ =>
        streamIncrementLpDensity_nonneg 4 _ _ _ x)
  have hsqrt : Real.sqrt (layerSimplexFourthMass m hn k (ell - (h : ℤ)) L omega)
      ≤ (d : ℝ) ^ 2 * Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn k,
          cubeMassRatio (originCube d m) Q *
            cubeAverage Q (streamIncrementLpDensity 4 (ell - (h : ℤ)) L omega.1)) := by
    have h1 := Real.sqrt_le_sqrt hmass
    rw [simplexToCubeConst, Real.sqrt_mul (by positivity)] at h1
    have h2 : Real.sqrt ((d : ℝ) ^ 4) = (d : ℝ) ^ 2 := by
      rw [show ((d : ℝ) ^ 4) = ((d : ℝ) ^ 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rwa [h2] at h1
  rw [seamSimplexObject, seamLayerObject]
  calc M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) *
        Real.sqrt (layerSimplexFourthMass m hn k (ell - (h : ℤ)) L omega)
      ≤ M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) *
        ((d : ℝ) ^ 2 * Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn k,
          cubeMassRatio (originCube d m) Q *
            cubeAverage Q (streamIncrementLpDensity 4 (ell - (h : ℤ)) L omega.1))) :=
        mul_le_mul_of_nonneg_left hsqrt hpref
    _ = (d : ℝ) ^ 2 * (M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) *
        Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn k,
          cubeMassRatio (originCube d m) Q *
            cubeAverage Q (streamIncrementLpDensity 4 (ell - (h : ℤ)) L omega.1))) := by
        ring

/-! ## Composition with the proved local seam-2 / seam-3 results -/


end

end Algsuperdiff.Section3.Provider.Multiscale

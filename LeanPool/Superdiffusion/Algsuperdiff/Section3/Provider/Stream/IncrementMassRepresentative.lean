/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementConcentration
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.Differentiation
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.SliceMeasurability
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.RestrictionBridge
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeColoring

/-!
# IncrementMassRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A measurable local representative of the cube `L^p` mass

`Provider/Stream/IncrementConcentration.lean` reduced the concentration step of
`e.kl.bounds.large` (ABK26) to a single missing input: the measurability of
the cube observable `regFieldLpMass p U` for the canonical carrier σ-algebra of
`RegCoeffField d`.

* is measurable and local **by construction** (a limsup over triadic scales of a
  countable sum of scalar multiples of the linear entry-test generators
  `entryTestR i j (1_{cubeSet R})`), and
* **agrees with `regFieldLpMass` at every continuous field**, which is all the
  application needs: the stream increments `k_m - k_n` are continuous
  (`continuous_finiteShellIncrement_entry`), so the identification is a pointwise
  identity on the image of the increment law and no a.e. bookkeeping is needed.

## The shape of the representative

`regFieldLpMassRep p U a` is the `limsup` over `k : ℕ` of the scale-`(-k)`
*grid mass*

`(vol U)⁻¹ * ∑_{R : scale(R) = -k, cubeSet R ⊆ U} vol(cubeSet R) · |⨍_R a|^p`,

where `⨍_R a = avgMat (cubeSet R) a` is CoarseGraining's matrix of entry
averages.  The grid at a *nonpositive* scale is invariant under integer
translations, which is exactly what makes the resulting set-indexed observable
translation covariant in CoarseGraining's restriction-lane sense
(`Ch04.IsRestrictionTranslationCovariant`) for **every** observation set `U` —
the cube family itself is not, since the integer translate of a triadic cube of
positive scale is not a triadic cube.

## What is proved

* `gridMass_cubeSet_toReal_eq_descendantsAverage` — on a triadic cube the grid
  mass is CoarseGraining's `descendantsAverage` of the cube-average norms.
* `measurable_regFieldLpMassRep`, `isLocalRandomVariable_regFieldLpMassRep` —
  the two restriction-lane measurability hypotheses of the centered descendant
  average estimate.
* `isTranslationCovariantR_regFieldLpMassRep` — its `hX_cov` hypothesis.
* `regFieldLpMassRep_cubeSet_eq_regFieldLpMass_of_continuous` — **the
  identification**: on continuous fields the representative is the genuine
  volume-normalized `L^p` mass.  This is the Riemann-sum convergence of the
  triadic cube averages of a continuous field.
* `regFieldLpMassRep_cubeSet_smulReg_finiteShellIncrement` — its reading at a
  rescaled stream increment, the form the concentration step consumes.

## References

* ABK26, `e.kl.bounds.large`; `p.concentration`.
* `Provider/Stream/IncrementConcentration.lean`, "The remaining gap for
  `e.kl.bounds.large`", which specifies exactly this representative.
* CoarseGraining `Homogenization/Probability/RegCoeffField/Sigma.lean` (the
  carrier σ-algebra and its entry-test generators),
  `Homogenization/Probability/RegCoeffField/Differentiation.lean` (`avgMat`).
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory Filter
open scoped ENNReal
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Elementary triadic-cube geometry -/

/-- The centre of a triadic cube belongs to its half-open realization. -/
theorem cubeCenter_mem_cubeSet (Q : TriadicCube d) : cubeCenter Q ∈ cubeSet Q := by
  intro i
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  constructor
  · have : ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤
        (Q.index i : ℝ) * cubeScaleFactor Q := by nlinarith
    simpa [cubeCenter] using this
  · have : (Q.index i : ℝ) * cubeScaleFactor Q <
        ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by nlinarith
    simpa [cubeCenter] using this

/-- Every triadic cube is nonempty. -/
theorem cubeSet_nonempty (Q : TriadicCube d) : (cubeSet Q).Nonempty :=
  ⟨cubeCenter Q, cubeCenter_mem_cubeSet Q⟩

/-- Two points of a triadic cube are at distance strictly less than its side
length. -/
theorem dist_lt_cubeScaleFactor_of_mem_cubeSet {Q : TriadicCube d} {x y : Vec d}
    (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    dist x y < cubeScaleFactor Q := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  refine (dist_pi_lt_iff hs).2 fun i => ?_
  have hxi := hx i
  have hyi := hy i
  rw [Real.dist_eq, abs_lt]
  constructor <;> [nlinarith [hxi.1, hxi.2, hyi.1, hyi.2];
    nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]]

/-- **A same-scale subcube is a descendant.**  A triadic cube of scale
`Q.scale - j` contained in `Q` is one of the depth-`j` descendants of `Q`: it
meets the (unique) descendant containing any of its points, and distinct cubes
of the same scale are disjoint. -/
theorem mem_descendantsAtDepth_of_scale_eq_of_cubeSet_subset {Q R : TriadicCube d}
    {j : ℕ} (hscale : R.scale = Q.scale - (j : ℤ)) (hsub : cubeSet R ⊆ cubeSet Q) :
    R ∈ descendantsAtDepth Q j := by
  obtain ⟨x, hx⟩ := cubeSet_nonempty R
  obtain ⟨S, hS, hxS⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j (hsub hx)
  have hSscale : S.scale = Q.scale - (j : ℤ) :=
    scale_eq_sub_of_mem_descendantsAtDepth hS
  by_cases hRS : R = S
  · exact hRS ▸ hS
  · exact absurd hxS
      (Set.disjoint_left.mp
        (disjoint_cubeSet_of_scale_eq_of_ne (hscale.trans hSscale.symm) hRS) hx)

/-! ## The triadic grid at nonpositive scales -/

/-- The scale-`(-k)` triadic cubes contained in the observation set `U`.  For
`k : ℕ` this family is invariant under integer translations of `U`, which is
what makes the grid mass below translation covariant on *every* set. -/
def gridCubesIn (U : Set (Vec d)) (k : ℕ) : Set (TriadicCube d) :=
  {R : TriadicCube d | R.scale = -(k : ℤ) ∧ cubeSet R ⊆ U}

/-- On a triadic cube the grid family is exactly the corresponding family of
descendants. -/
theorem gridCubesIn_cubeSet_eq_descendantsAtDepth (Q : TriadicCube d) {k : ℕ}
    (hk : -(k : ℤ) ≤ Q.scale) :
    gridCubesIn (cubeSet Q) k =
      ↑(descendantsAtDepth Q (Q.scale + (k : ℤ)).toNat) := by
  have hdepth : Q.scale - ((Q.scale + (k : ℤ)).toNat : ℤ) = -(k : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  ext R
  simp only [gridCubesIn, Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · rintro ⟨hscale, hsub⟩
    exact mem_descendantsAtDepth_of_scale_eq_of_cubeSet_subset (by rw [hdepth, hscale]) hsub
  · intro hR
    refine ⟨?_, cubeSet_subset_of_mem_descendantsAtDepth hR⟩
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hdepth]

/-! ## Probes and averages on a triadic cube -/

/-- The constant-one indicator of a triadic cube is an enriched CoarseGraining
probe: it is bounded and measurable, and its support has compact closure
because the cube is contained in a closed ball. -/
theorem isProbeR_indicator_cubeSet (R : TriadicCube d) :
    IsProbeR (Set.indicator (cubeSet R) (fun _ : Vec d => (1 : ℝ))) := by
  refine ⟨measurable_const.indicator (measurableSet_cubeSet R), ⟨1, fun x => ?_⟩, ?_⟩
  · by_cases hx : x ∈ cubeSet R <;> simp [Set.indicator, hx]
  · have hsub : closure
        (Function.support (Set.indicator (cubeSet R) (fun _ : Vec d => (1 : ℝ)))) ⊆
        Metric.closedBall (cubeCenter R) (cubeRadius R) :=
      closure_minimal
        ((support_indicator_one_subset (cubeSet R)).trans (cubeSet_subset_closedBall R))
        Metric.isClosed_closedBall
    exact IsCompact.of_isClosed_subset (isCompact_closedBall _ _) isClosed_closure hsub

/-- **The cube average matrix is a local carrier observable.**  Each entry of
`avgMat (cubeSet R)` is a scalar multiple of the localized entry-test generator
against the cube indicator, hence `LocalSigmaR U`-measurable as soon as the cube
lies in `U`. -/
theorem measurable_avgMat_cubeSet_localSigmaR {U : Set (Vec d)} (R : TriadicCube d)
    (hRU : cubeSet R ⊆ U) :
    @Measurable (RegCoeffField d) (Mat d) (LocalSigmaR U) _ (avgMat (cubeSet R)) := by
  refine @measurable_matrix_of_entries d (RegCoeffField d) (LocalSigmaR U)
    (avgMat (cubeSet R)) ?_
  intro i j
  have hsupp :
      Function.support (Set.indicator (cubeSet R) (fun _ : Vec d => (1 : ℝ))) ⊆ U :=
    (support_indicator_one_subset (cubeSet R)).trans hRU
  have hgen : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
      (entryTestR i j (Set.indicator (cubeSet R) (fun _ : Vec d => (1 : ℝ)))) :=
    measurable_entryTestR_localSigmaR i j (isProbeR_indicator_cubeSet R) hsupp
  have heq : (fun a : RegCoeffField d => avgMat (cubeSet R) a i j) =
      fun a : RegCoeffField d => (volume (cubeSet R)).toReal⁻¹ •
        entryTestR i j (Set.indicator (cubeSet R) (fun _ : Vec d => (1 : ℝ))) a := by
    funext a
    exact avgMat_entry_eq_smul_entryTestR i j (cubeSet R) (measurableSet_cubeSet R) a
  rw [heq]
  exact hgen.const_smul ((volume (cubeSet R)).toReal⁻¹)

/-! ## The grid mass -/

/-- One term of the scale-`(-k)` grid mass of `a` on `U`. -/
def gridMassTerm (p : ℝ) (U : Set (Vec d)) (k : ℕ) (R : TriadicCube d)
    (a : RegCoeffField d) : ℝ≥0∞ :=
  Set.indicator (gridCubesIn U k)
    (fun S : TriadicCube d => volume (cubeSet S) *
      ENNReal.ofReal (Book.Ch02.matrixOperatorNorm (avgMat (cubeSet S) a) ^ p)) R

theorem gridMassTerm_of_mem {p : ℝ} {U : Set (Vec d)} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ gridCubesIn U k) (a : RegCoeffField d) :
    gridMassTerm p U k R a = volume (cubeSet R) *
      ENNReal.ofReal (Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p) :=
  Set.indicator_of_mem hR _

theorem gridMassTerm_of_notMem {p : ℝ} {U : Set (Vec d)} {k : ℕ} {R : TriadicCube d}
    (hR : R ∉ gridCubesIn U k) (a : RegCoeffField d) :
    gridMassTerm p U k R a = 0 :=
  Set.indicator_of_notMem hR _

/-- The scale-`(-k)` grid mass of `a` on `U`: the countable sum, over the
scale-`(-k)` triadic cubes contained in `U`, of the cube volume times the `p`-th
power of the operator norm of the cube average. -/
def gridMass (p : ℝ) (U : Set (Vec d)) (k : ℕ) (a : RegCoeffField d) : ℝ≥0∞ :=
  ∑' R : TriadicCube d, gridMassTerm p U k R a

/-- **The countably generated representative of the cube `L^p` mass.** -/
def regFieldLpMassRep (p : ℝ) (U : Set (Vec d)) (a : RegCoeffField d) : ℝ :=
  limsup (fun k : ℕ => (volume U).toReal⁻¹ * (gridMass p U k a).toReal) atTop

/-! ## Measurability and locality of the representative -/

theorem measurable_gridMassTerm_localSigmaR (p : ℝ) (U : Set (Vec d)) (k : ℕ)
    (R : TriadicCube d) :
    @Measurable (RegCoeffField d) ℝ≥0∞ (LocalSigmaR U) _ (gridMassTerm p U k R) := by
  by_cases hR : R ∈ gridCubesIn U k
  · have heq : gridMassTerm p U k R = fun a : RegCoeffField d =>
        volume (cubeSet R) *
          ENNReal.ofReal (Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p) := by
      funext a
      exact gridMassTerm_of_mem hR a
    rw [heq]
    have hnorm : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
        (fun a : RegCoeffField d =>
          Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p) :=
      (ShellField.continuous_matrixOperatorNorm.measurable.comp
        (measurable_avgMat_cubeSet_localSigmaR R hR.2)).pow_const p
    exact hnorm.ennreal_ofReal.const_mul _
  · have heq : gridMassTerm p U k R = fun _ : RegCoeffField d => (0 : ℝ≥0∞) := by
      funext a
      exact gridMassTerm_of_notMem hR a
    rw [heq]
    exact measurable_const

theorem measurable_gridMass_localSigmaR (p : ℝ) (U : Set (Vec d)) (k : ℕ) :
    @Measurable (RegCoeffField d) ℝ≥0∞ (LocalSigmaR U) _ (gridMass p U k) := by
  let : MeasurableSpace (RegCoeffField d) := LocalSigmaR U
  exact Measurable.tsum (L := SummationFilter.unconditional (TriadicCube d))
    fun R => measurable_gridMassTerm_localSigmaR p U k R

/-- **The representative is a local carrier observable.**  It is generated by
countably many entry tests against probes supported in `U`. -/
theorem measurable_regFieldLpMassRep_localSigmaR (p : ℝ) (U : Set (Vec d)) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _ (regFieldLpMassRep p U) :=
  Measurable.limsup fun k =>
    ((measurable_gridMass_localSigmaR p U k).ennreal_toReal).const_mul _

/-- **The representative is measurable for the canonical carrier σ-algebra.**
This is the `hX0_meas`/`hX_desc_meas` hypothesis of
the restriction-lane centered descendant average estimate. -/
theorem measurable_regFieldLpMassRep (p : ℝ) (U : Set (Vec d)) :
    Measurable (regFieldLpMassRep p U) :=
  (measurable_regFieldLpMassRep_localSigmaR p U).mono (LocalSigmaR_le U) le_rfl

/-- **CoarseGraining locality of the representative.** This is the `hX_local`
hypothesis of
`isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw`. -/
theorem isLocalRandomVariable_regFieldLpMassRep (p : ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    HCPolySupport.Book.Ch04.IsRestrictionLocalRandomVariable U hU
      (regFieldLpMassRep p U) :=
  measurable_restrictionSigmaR_of_measurable_localSigmaR hU
    (measurable_regFieldLpMassRep_localSigmaR p U)

/-! ## Translation covariance of the representative -/

/-- Index translation of triadic cubes is a bijection of the cube type. -/
def translateCubeEquiv (s : Fin d → ℤ) : TriadicCube d ≃ TriadicCube d where
  toFun := translateCube s
  invFun := translateCube fun i => -(s i)
  left_inv := by
    intro R
    cases R with
    | mk scale index =>
        change (⟨scale, fun i => index i + s i + -(s i)⟩ : TriadicCube d) = ⟨scale, index⟩
        congr 1
        funext i
        ring
  right_inv := by
    intro R
    cases R with
    | mk scale index =>
        change (⟨scale, fun i => index i + -(s i) + s i⟩ : TriadicCube d) = ⟨scale, index⟩
        congr 1
        funext i
        ring

@[simp] theorem translateCubeEquiv_apply (s : Fin d → ℤ) (R : TriadicCube d) :
    translateCubeEquiv s R = translateCube s R := rfl

@[simp] theorem scale_translateCube (s : Fin d → ℤ) (R : TriadicCube d) :
    (translateCube s R).scale = R.scale := rfl

/-- **The nonpositive triadic grid is integer-translation invariant.**  At scale
`-k` the index shift `3^k z` implements exactly the spatial translation by the
integer vector `z`. -/
theorem cubeSet_translateCube_descendantTranslationShift (z : Fin d → ℤ) (k : ℕ)
    {R : TriadicCube d} (hR : R.scale = -(k : ℤ)) :
    cubeSet (translateCube (descendantTranslationShift k z) R) =
      translateSet (intVecToRealVec z) (cubeSet R) := by
  have hvec : (fun i => ((descendantTranslationShift k z i : ℤ) : ℝ) * cubeScaleFactor R) =
      intVecToRealVec z := by
    funext i
    have h3 : ((3 : ℝ) ^ (k : ℕ)) ≠ 0 := pow_ne_zero k (by norm_num)
    simp only [descendantTranslationShift, cubeScaleFactor, hR, intVecToRealVec,
      Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [zpow_neg, zpow_natCast]
    field_simp
  ext x
  rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem, hvec]

/-- Translation transports set inclusion both ways. -/
theorem translateSet_subset_translateSet_iff (w : Vec d) (A B : Set (Vec d)) :
    translateSet w A ⊆ translateSet w B ↔ A ⊆ B := by
  constructor
  · intro h x hx
    have hx' : x + w ∈ translateSet w A := by
      rw [mem_translateSet_iff_sub_mem]
      simpa using hx
    have := h hx'
    rw [mem_translateSet_iff_sub_mem] at this
    simpa using this
  · intro h x hx
    rw [mem_translateSet_iff_sub_mem] at hx ⊢
    exact h hx

/-- **The cube-average matrix is translation covariant.**  Translating the
observation set is the same as translating the field. -/
theorem avgMat_translateSet (w : Vec d) (B : Set (Vec d)) (a : RegCoeffField d) :
    avgMat (translateSet w B) a = avgMat B (translateReg w a) := by
  funext i j
  rw [avgMat, avgMat, volume_translateSet_eq]
  refine congrArg (fun t : ℝ => (volume B).toReal⁻¹ • t) ?_
  rw [← setIntegral_comp_addRight_translateSet w B (fun y : Vec d => a y i j)]
  rfl

/-- The grid family transports along an integer translation. -/
theorem gridCubesIn_translateSet (U : Set (Vec d)) (k : ℕ) (z : Fin d → ℤ)
    {R : TriadicCube d} :
    translateCubeEquiv (descendantTranslationShift k z) R ∈
        gridCubesIn (translateSet (intVecToRealVec z) U) k ↔ R ∈ gridCubesIn U k := by
  simp only [gridCubesIn, Set.mem_ofPred_eq, translateCubeEquiv_apply, scale_translateCube]
  constructor
  · rintro ⟨hscale, hsub⟩
    rw [cubeSet_translateCube_descendantTranslationShift z k hscale,
      translateSet_subset_translateSet_iff] at hsub
    exact ⟨hscale, hsub⟩
  · rintro ⟨hscale, hsub⟩
    refine ⟨hscale, ?_⟩
    rw [cubeSet_translateCube_descendantTranslationShift z k hscale,
      translateSet_subset_translateSet_iff]
    exact hsub

theorem gridMassTerm_translateSet (p : ℝ) (U : Set (Vec d)) (k : ℕ) (z : Fin d → ℤ)
    (R : TriadicCube d) (a : RegCoeffField d) :
    gridMassTerm p (translateSet (intVecToRealVec z) U) k
        (translateCubeEquiv (descendantTranslationShift k z) R) a =
      gridMassTerm p U k R (translateReg (intVecToRealVec z) a) := by
  by_cases hR : R ∈ gridCubesIn U k
  · have hR' := (gridCubesIn_translateSet U k z (R := R)).2 hR
    rw [gridMassTerm_of_mem hR', gridMassTerm_of_mem hR, translateCubeEquiv_apply,
      cubeSet_translateCube_descendantTranslationShift z k hR.1,
      volume_translateSet_eq, avgMat_translateSet]
  · have hR' : translateCubeEquiv (descendantTranslationShift k z) R ∉
        gridCubesIn (translateSet (intVecToRealVec z) U) k := fun h =>
      hR ((gridCubesIn_translateSet U k z (R := R)).1 h)
    rw [gridMassTerm_of_notMem hR', gridMassTerm_of_notMem hR]

theorem gridMass_translateSet (p : ℝ) (U : Set (Vec d)) (k : ℕ) (z : Fin d → ℤ)
    (a : RegCoeffField d) :
    gridMass p (translateSet (intVecToRealVec z) U) k a =
      gridMass p U k (translateReg (intVecToRealVec z) a) := by
  rw [gridMass, gridMass,
    ← (translateCubeEquiv (descendantTranslationShift k z)).tsum_eq
      (fun R : TriadicCube d => gridMassTerm p (translateSet (intVecToRealVec z) U) k R a)]
  exact tsum_congr fun R => gridMassTerm_translateSet p U k z R a

/-- **CoarseGraining's exact translation-covariance predicate for the
representative.** This is the `hX_cov` hypothesis of the restriction-lane
centered descendant average estimate.  It holds for *every* observation set
because the grid used by the representative sits at nonpositive scales, where
integer translations act by index shifts. -/
theorem isTranslationCovariantR_regFieldLpMassRep (p : ℝ) :
    HCPolySupport.Book.Ch04.IsRestrictionTranslationCovariant
      (regFieldLpMassRep (d := d) p) := by
  intro U z a
  rw [regFieldLpMassRep, regFieldLpMassRep]
  refine congrArg (fun f : ℕ → ℝ => limsup f atTop) ?_
  funext k
  rw [gridMass_translateSet p U k z a, volume_translateSet_eq]

/-! ## The grid mass on a triadic cube -/

theorem volume_cubeSet_ne_top (R : TriadicCube d) : volume (cubeSet R) ≠ ⊤ :=
  (lt_of_le_of_lt (measure_mono (cubeSet_subset_closedBall R))
    measure_closedBall_lt_top).ne

/-- On a triadic cube of scale at least `-k` the grid mass is the finite sum over
the scale-`(-k)` descendants. -/
theorem gridMass_cubeSet (p : ℝ) (Q : TriadicCube d) {k : ℕ} (hk : -(k : ℤ) ≤ Q.scale)
    (a : RegCoeffField d) :
    gridMass p (cubeSet Q) k a =
      ∑ R ∈ descendantsAtDepth Q (Q.scale + (k : ℤ)).toNat,
        volume (cubeSet R) *
          ENNReal.ofReal (Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p) := by
  classical
  have hmem : ∀ R : TriadicCube d,
      R ∈ gridCubesIn (cubeSet Q) k ↔
        R ∈ descendantsAtDepth Q (Q.scale + (k : ℤ)).toNat := by
    intro R
    rw [gridCubesIn_cubeSet_eq_descendantsAtDepth Q hk]
    exact Finset.mem_coe
  have hzero : ∀ R ∉ descendantsAtDepth Q (Q.scale + (k : ℤ)).toNat,
      gridMassTerm p (cubeSet Q) k R a = 0 := fun R hR =>
    gridMassTerm_of_notMem (fun h => hR ((hmem R).1 h)) a
  rw [gridMass, tsum_eq_sum hzero]
  exact Finset.sum_congr rfl fun R hR => gridMassTerm_of_mem ((hmem R).2 hR) a

/-- **The grid mass on a triadic cube is CoarseGraining's descendant average of the
cube-average norms.** -/
theorem gridMass_cubeSet_toReal_eq_descendantsAverage (p : ℝ) (Q : TriadicCube d)
    {k : ℕ} (hk : -(k : ℤ) ≤ Q.scale) (a : RegCoeffField d) :
    (volume (cubeSet Q)).toReal⁻¹ * (gridMass p (cubeSet Q) k a).toReal =
      descendantsAverage Q (Q.scale + (k : ℤ)).toNat
        (fun R => Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p) := by
  classical
  obtain ⟨R₀, hR₀⟩ := descendantsAtDepth_nonempty Q (Q.scale + (k : ℤ)).toNat
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q (Q.scale + (k : ℤ)).toNat).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (descendantsAtDepth_nonempty Q (Q.scale + (k : ℤ)).toNat)
  have hv₀ : (0 : ℝ) < cubeVolume R₀ := cubeVolume_pos R₀
  have hnetop : ∀ R ∈ descendantsAtDepth Q (Q.scale + (k : ℤ)).toNat,
      volume (cubeSet R) *
        ENNReal.ofReal (Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p) ≠ ⊤ :=
    fun R _ => ENNReal.mul_ne_top (volume_cubeSet_ne_top R) ENNReal.ofReal_ne_top
  have hterm : ∀ R ∈ descendantsAtDepth Q (Q.scale + (k : ℤ)).toNat,
      (volume (cubeSet R) *
          ENNReal.ofReal (Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p)).toReal =
        cubeVolume R₀ * Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p := by
    intro R hR
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg (Book.Ch02.matrixOperatorNorm_nonneg _) p),
      volume_cubeSet_toReal, cubeVolume_eq_of_mem_descendantsAtDepth hR hR₀]
  rw [gridMass_cubeSet p Q hk a, ENNReal.toReal_sum hnetop,
    Finset.sum_congr rfl hterm, ← Finset.mul_sum, volume_cubeSet_toReal,
    cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR₀]
  dsimp only [descendantsAverage]
  field_simp

/-! ## Averaging estimates -/

/-- The cube average of a scalar function stays within a uniform bound of any
value it is uniformly close to on the cube. -/
theorem abs_cubeAverage_sub_le (R : TriadicCube d) {g : Vec d → ℝ} {c eps : ℝ}
    (hg : IntegrableOn g (cubeSet R) volume)
    (hb : ∀ x ∈ cubeSet R, |g x - c| ≤ eps) :
    |cubeAverage R g - c| ≤ eps := by
  have hvol : (0 : ℝ) < cubeVolume R := cubeVolume_pos R
  have hconst : IntegrableOn (fun _ : Vec d => c) (cubeSet R) volume :=
    integrableOn_const (volume_cubeSet_ne_top R) (by finiteness)
  have hsub : ∫ x in cubeSet R, (g x - c) =
      (∫ x in cubeSet R, g x) - cubeVolume R * c := by
    rw [integral_sub hg hconst, setIntegral_const, smul_eq_mul, measureReal_def,
      volume_cubeSet_toReal]
  have hbound : ‖∫ x in cubeSet R, (g x - c)‖ ≤
      eps * (volume : Measure (Vec d)).real (cubeSet R) := by
    refine norm_setIntegral_le_of_norm_le_const
      (lt_top_iff_ne_top.2 (volume_cubeSet_ne_top R)) (fun x hx => ?_)
    simpa [Real.norm_eq_abs] using hb x hx
  rw [Real.norm_eq_abs, hsub, measureReal_def, volume_cubeSet_toReal] at hbound
  have hrewrite : cubeAverage R g - c =
      (cubeVolume R)⁻¹ * ((∫ x in cubeSet R, g x) - cubeVolume R * c) := by
    rw [cubeAverage]
    field_simp
  rw [hrewrite, abs_mul, abs_of_nonneg (inv_nonneg.2 hvol.le)]
  calc (cubeVolume R)⁻¹ * |(∫ x in cubeSet R, g x) - cubeVolume R * c|
      ≤ (cubeVolume R)⁻¹ * (eps * cubeVolume R) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hvol.le)
    _ = eps := by field_simp

/-- Each entry of the cube-average matrix is the corresponding scalar cube
average. -/
theorem avgMat_cubeSet_entry_eq_cubeAverage (R : TriadicCube d) (a : RegCoeffField d)
    (i j : Fin d) :
    avgMat (cubeSet R) a i j = cubeAverage R (fun x : Vec d => a x i j) := by
  rw [avgMat, cubeAverage, volume_cubeSet_toReal, smul_eq_mul]

/-- The entries of a carrier field are integrable on every triadic cube. -/
theorem integrableOn_cubeSet_entry (R : TriadicCube d) (a : RegCoeffField d)
    (i j : Fin d) :
    IntegrableOn (fun x : Vec d => a x i j) (cubeSet R) volume :=
  ((a.entry_locInt i j).integrableOn_isCompact
    (isCompact_closedBall (cubeCenter R) (cubeRadius R))).mono_set
    (cubeSet_subset_closedBall R)

/-- A descendant average is within `eps` of another one when all its terms are. -/
theorem abs_descendantsAverage_sub_le {Q : TriadicCube d} {j : ℕ}
    {G H : TriadicCube d → ℝ} {eps : ℝ}
    (hGH : ∀ R ∈ descendantsAtDepth Q j, |G R - H R| ≤ eps) :
    |descendantsAverage Q j G - descendantsAverage Q j H| ≤ eps := by
  classical
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
  dsimp only [descendantsAverage]
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hcard.le)]
  have h1 : |∑ R ∈ descendantsAtDepth Q j, (G R - H R)| ≤
      ∑ R ∈ descendantsAtDepth Q j, |G R - H R| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ R ∈ descendantsAtDepth Q j, |G R - H R| ≤
      ∑ _R ∈ descendantsAtDepth Q j, eps := Finset.sum_le_sum hGH
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  calc ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        |∑ R ∈ descendantsAtDepth Q j, (G R - H R)|
      ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          (((descendantsAtDepth Q j).card : ℝ) * eps) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.2 hcard.le)
    _ = eps := by field_simp

/-! ## The identification at continuous fields -/

/-- **The representative computes the genuine cube `L^p` mass at every
continuous field.**  This is the Riemann-sum convergence of the triadic cube
averages: on the compact closure of the cube the field is uniformly continuous,
so each depth-`j` cube average is uniformly close to the field on that cube, and
the descendant average of the `p`-th powers converges to the cube average of the
density. -/
theorem regFieldLpMassRep_cubeSet_eq_regFieldLpMass_of_continuous {p : ℝ} (hp : 0 < p)
    (Q : TriadicCube d) {a : RegCoeffField d}
    (hcont : ∀ i j, Continuous fun x : Vec d => a x i j) :
    regFieldLpMassRep p (cubeSet Q) a = regFieldLpMass p (cubeSet Q) a := by
  classical
  have hamat : Continuous fun x : Vec d => (a x : Mat d) := continuous_matrix hcont
  have hfcont : Continuous fun x : Vec d => Book.Ch02.matrixOperatorNorm (a x) ^ p :=
    (Real.continuous_rpow_const hp.le).comp
      (ShellField.continuous_matrixOperatorNorm.comp hamat)
  have hFcont : Continuous fun (x : Vec d) (i j : Fin d) => a x i j :=
    continuous_pi fun i => continuous_pi fun j => hcont i j
  have hKcpt : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    isCompact_closedBall _ _
  have hQK : cubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q
  have hfint : IntegrableOn (fun x : Vec d => Book.Ch02.matrixOperatorNorm (a x) ^ p)
      (cubeSet Q) volume :=
    (hfcont.continuousOn.integrableOn_compact hKcpt).mono_set hQK
  have hmass : regFieldLpMass p (cubeSet Q) a =
      cubeAverage Q (fun x : Vec d => Book.Ch02.matrixOperatorNorm (a x) ^ p) := by
    rw [regFieldLpMass, cubeAverage, volume_cubeSet_toReal]
  rw [hmass, regFieldLpMassRep]
  refine Tendsto.limsup_eq (Metric.tendsto_atTop.2 ?_)
  intro eps heps
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn hFcont.continuousOn
  have hCnonneg : (0 : ℝ) ≤ C :=
    le_trans (norm_nonneg _) (hC (cubeCenter Q) (hQK (cubeCenter_mem_cubeSet Q)))
  have hentry : ∀ x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q),
      ∀ i j, |a x i j| ≤ C := by
    intro x hx i j
    have h1 := norm_le_pi_norm (fun (i : Fin d) (j : Fin d) => a x i j) i
    have h2 := norm_le_pi_norm (fun j : Fin d => a x i j) j
    have h3 := (h2.trans h1).trans (hC x hx)
    simpa [Real.norm_eq_abs] using h3
  have hnormle : ∀ A : Mat d, (∀ i j, |A i j| ≤ C) →
      Book.Ch02.matrixOperatorNorm A ≤ (d : ℝ) * (d : ℝ) * C := by
    intro A hA
    have h0 : Book.Ch02.matrixOperatorNorm A ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
      simpa using
        Book.Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries A 0
    refine h0.trans ?_
    calc ∑ i : Fin d, ∑ j : Fin d, |A i j|
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, C :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA i j
      _ = (d : ℝ) * (d : ℝ) * C := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  obtain ⟨eta, heta, hetaspec⟩ :=
    Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := (0 : ℝ)) (b := (d : ℝ) * (d : ℝ) * C)).uniformContinuousOn_of_continuous
        (f := fun t : ℝ => t ^ p) (Real.continuous_rpow_const hp.le).continuousOn)
      (eps / 2) (by linarith)
  have hetapos : (0 : ℝ) < eta / ((d : ℝ) * (d : ℝ) + 1) := by positivity
  obtain ⟨delta, hdelta, hdeltaspec⟩ :=
    Metric.uniformContinuousOn_iff.1
      (hKcpt.uniformContinuousOn_of_continuous hFcont.continuousOn)
      (eta / ((d : ℝ) * (d : ℝ) + 1)) hetapos
  have hev1 : ∀ᶠ k : ℕ in atTop, -(k : ℤ) ≤ Q.scale := by
    filter_upwards [eventually_ge_atTop (-Q.scale).toNat] with k hk
    omega
  have hev2 : ∀ᶠ k : ℕ in atTop, ((3 : ℝ) ^ (-(k : ℤ))) < delta := by
    have h13 : Tendsto (fun k : ℕ => ((1 : ℝ) / 3) ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    filter_upwards [h13.eventually_lt_const hdelta] with k hk
    have hpow : ((3 : ℝ) ^ (-(k : ℤ))) = ((1 : ℝ) / 3) ^ k := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rwa [hpow]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hk1, hk2⟩ := hN k hk
  rw [gridMass_cubeSet_toReal_eq_descendantsAverage p Q hk1 a,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q
      (Q.scale + (k : ℤ)).toNat _ hfint, Real.dist_eq]
  refine lt_of_le_of_lt (abs_descendantsAverage_sub_le (eps := eps / 2) ?_) (by linarith)
  intro R hR
  have hRscale : R.scale = -(k : ℤ) := by
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR,
      Int.toNat_of_nonneg (show (0 : ℤ) ≤ Q.scale + (k : ℤ) by omega)]
    ring
  have hRQ : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hRK : cubeSet R ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := hRQ.trans hQK
  have hRdist : ∀ x ∈ cubeSet R, ∀ y ∈ cubeSet R, dist x y < delta := by
    intro x hx y hy
    refine lt_of_lt_of_le (dist_lt_cubeScaleFactor_of_mem_cubeSet hx hy) ?_
    rw [cubeScaleFactor, hRscale]
    exact hk2.le
  have hclose : ∀ y ∈ cubeSet R, ∀ i j,
      |avgMat (cubeSet R) a i j - a y i j| ≤ eta / ((d : ℝ) * (d : ℝ) + 1) := by
    intro y hy i j
    rw [avgMat_cubeSet_entry_eq_cubeAverage]
    refine abs_cubeAverage_sub_le R (integrableOn_cubeSet_entry R a i j) ?_
    intro x hx
    have hd := hdeltaspec x (hRK hx) y (hRK hy) (hRdist x hx y hy)
    have h1 := dist_le_pi_dist (fun (i : Fin d) (j : Fin d) => a x i j)
      (fun (i : Fin d) (j : Fin d) => a y i j) i
    have h2 := dist_le_pi_dist (fun j : Fin d => a x i j) (fun j : Fin d => a y i j) j
    have h3 := ((h2.trans h1).trans_lt hd).le
    simpa [Real.dist_eq] using h3
  have hnormclose : ∀ y ∈ cubeSet R,
      |Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) -
        Book.Ch02.matrixOperatorNorm (a y)| < eta := by
    intro y hy
    have hS : ∑ i : Fin d, ∑ j : Fin d, |avgMat (cubeSet R) a i j - a y i j| ≤
        (d : ℝ) * (d : ℝ) * (eta / ((d : ℝ) * (d : ℝ) + 1)) := by
      calc ∑ i : Fin d, ∑ j : Fin d, |avgMat (cubeSet R) a i j - a y i j|
          ≤ ∑ _i : Fin d, ∑ _j : Fin d, (eta / ((d : ℝ) * (d : ℝ) + 1)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hclose y hy i j
        _ = (d : ℝ) * (d : ℝ) * (eta / ((d : ℝ) * (d : ℝ) + 1)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hSlt : ∑ i : Fin d, ∑ j : Fin d,
        |avgMat (cubeSet R) a i j - a y i j| < eta := by
      refine lt_of_le_of_lt hS ?_
      have hpos : (0 : ℝ) < (d : ℝ) * (d : ℝ) + 1 := by positivity
      rw [mul_div_assoc', div_lt_iff₀ hpos]
      nlinarith [heta]
    have h1 := Book.Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
      (avgMat (cubeSet R) a) (a y)
    have h2 := Book.Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
      (a y) (avgMat (cubeSet R) a)
    have hsymm : ∑ i : Fin d, ∑ j : Fin d, |a y i j - avgMat (cubeSet R) a i j| =
        ∑ i : Fin d, ∑ j : Fin d, |avgMat (cubeSet R) a i j - a y i j| :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => abs_sub_comm _ _
    rw [hsymm] at h2
    rw [abs_lt]
    constructor <;> linarith
  have hAvgC : ∀ i j, |avgMat (cubeSet R) a i j| ≤ C := by
    intro i j
    rw [avgMat_cubeSet_entry_eq_cubeAverage]
    have hz := abs_cubeAverage_sub_le R (c := 0) (eps := C)
      (integrableOn_cubeSet_entry R a i j)
      (fun x hx => by simpa using hentry x (hRK hx) i j)
    simpa using hz
  have hIcc : ∀ A : Mat d, (∀ i j, |A i j| ≤ C) →
      Book.Ch02.matrixOperatorNorm A ∈ Set.Icc (0 : ℝ) ((d : ℝ) * (d : ℝ) * C) :=
    fun A hA => ⟨Book.Ch02.matrixOperatorNorm_nonneg A, hnormle A hA⟩
  have hpointwise : ∀ y ∈ cubeSet R,
      |Book.Ch02.matrixOperatorNorm (avgMat (cubeSet R) a) ^ p -
        Book.Ch02.matrixOperatorNorm (a y) ^ p| < eps / 2 := by
    intro y hy
    have hgap := hetaspec _ (hIcc _ hAvgC) _
      (hIcc (a y) (fun i j => hentry y (hRK hy) i j))
      (by rw [Real.dist_eq]; exact hnormclose y hy)
    rwa [Real.dist_eq] at hgap
  rw [abs_sub_comm]
  refine abs_cubeAverage_sub_le R (hfint.mono_set hRQ) ?_
  intro y hy
  rw [abs_sub_comm]
  exact (hpointwise y hy).le

/-! ## Reading at a stream increment -/

/-- A spatial rescaling of a continuous field is continuous. -/
theorem continuous_smulReg_entry {r : ℝ} (hr : r ≠ 0) {a : RegCoeffField d}
    (hcont : ∀ i j, Continuous fun x : Vec d => a x i j) (i j : Fin d) :
    Continuous fun x : Vec d => smulReg r hr a x i j := by
  have hsmul : Continuous fun x : Vec d => r • x := continuous_const_smul r
  simpa using! (hcont i j).comp hsmul

/-- Every spatial rescaling of a finite stream increment is continuous. -/
theorem continuous_smulReg_finiteShellIncrement_entry (omega : ShellSeq d) (n m : ℤ)
    {r : ℝ} (hr : r ≠ 0) (i j : Fin d) :
    Continuous fun x : Vec d =>
      smulReg r hr (finiteShellIncrement omega n m) x i j :=
  continuous_smulReg_entry hr
    (fun i j => continuous_finiteShellIncrement_entry omega n m i j) i j

/-- **The representative computes the genuine cube `L^p` mass at every rescaled
stream increment.**  This is the pointwise identity on the image of the
(rescaled) increment law used by the concentration step: no a.e. bookkeeping
enters, because every increment field is continuous. -/
theorem regFieldLpMassRep_cubeSet_smulReg_finiteShellIncrement {p : ℝ} (hp : 0 < p)
    (R : TriadicCube d) (omega : ShellSeq d) (n m : ℤ) {r : ℝ} (hr : r ≠ 0) :
    regFieldLpMassRep p (cubeSet R) (smulReg r hr (finiteShellIncrement omega n m)) =
      regFieldLpMass p (cubeSet R) (smulReg r hr (finiteShellIncrement omega n m)) :=
  regFieldLpMassRep_cubeSet_eq_regFieldLpMass_of_continuous hp R
    (fun i j => continuous_smulReg_finiteShellIncrement_entry omega n m hr i j)

end

end Algsuperdiff.Section3.Provider.Stream

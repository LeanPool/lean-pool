/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementMassRepresentative

/-!
# IncrementLpGain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The partition-average gain for the stream-increment `L^p` mass

This module supplies the conditional large-window concentration kernel used
toward `e.kl.bounds.large` (ABK26): CoarseGraining's partition-average
fluctuation theorem
`Homogenization.Book.Ch04.isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw`
is applied to the per-subcube `L^p` mass of a finite stream increment, and its
conclusion is transported back to the shell-sequence sample space in exactly
the head-plus-tail shape that
`Provider/Stream/IncrementLp.streamIncrementLpNorm_head_tail_of_mass_head_tail`
consumes.

## The scale obstruction and the partition normalization

CoarseGraining's theorem carries `hn : 0 ≤ n` on its *subcube* scale, because
it reaches a descendant cube from the origin cube by an **integer**
translation.  Under it, the source's scale-`m` subcubes are replaced by the
slightly coarser scale-`(m+c)` subcubes, and the partition gain becomes

`3^{-(d/2)(l-m-c)} = 3^{(d/2)c} * 3^{-(d/2)(l-m)}`,

i.e. the printed gain with a dimensional constant `3^{(d/2)c}`.  This is the `l
>= m + c` regime; the complementary regime `l < m + c` is *not* treated here:
there the partition is empty and `e.kl.bounds.large` reduces to the proved
`l`-uniform `e.kmn.bounds` with a `C(d)`-enlarged amplitude, which belongs to
the assembly of `l.km.kn.Lp.estimates`.  The window binder `hsl : m + c <= l`
below is an implementation branch condition, not a premise of the source
theorem.  `IncrementLpLarge.lean` later combines this branch with the
complementary regime and discharges the centering input.

## What is proved

* `dilateCube`, `cubeSet_dilateCube`, `descendantsAtDepth_dilateCube`,
  `descendantsAtScale_originCube_eq_image_dilateCube` — the triadic dilation
  dictionary matching `smulReg` on the carrier.
* `regFieldLpMass_smulReg` — the cube `L^p` mass is dilation covariant.
* `descendantAverage_regFieldLpMassRep_eq_streamIncrementLpMass` — **the exact
  identification**: at a partition-rescaled increment field, CoarseGraining's
  descendant partition average of the measurable representative *is* the cube
  mass `streamIncrementLpMass p l n m omega`.
* `isBigOWith_comp_of_isBigO_map` — transport of a weak-Orlicz tail bound along
  a push-forward.
* `isBigOWith_gammaSigma_streamIncrementLpMass_sub_originMean` — **the deliverable**:
  the `Gamma_sigma` bound with the geometric partition gain for the centered cube
  mass, on the shell-sequence sample space.
* `streamIncrementLpMass_head_tail` — its packaging as `mass <= H + T` with
  `T >= 0` and `T` in `O_{Gamma_sigma}` of the gain, the exact input of
  `streamIncrementLpNorm_head_tail_of_mass_head_tail`.

## References

* ABK26, `e.kl.bounds.large`; `e.kmn.bounds`; `p.concentration`; the cutoff
  range.
* `Provider/Stream/IncrementLaw.lean` (`incrementPartitionScale`,
  `partitionStreamIncrementLaw` and its two structural assumptions),
  `Provider/Stream/IncrementConcentration.lean` (the deterministic descendant
  identity), `Provider/Stream/IncrementMassRepresentative.lean` (the measurable
  local representative).
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory Filter
open scoped ENNReal Pointwise
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Triadic dilation -/

/-- The triadic dilation of a cube by the factor `3^s`: the same index at a
scale shifted by `s`. -/
def dilateCube (s : ℤ) (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale + s
    index := Q.index }

@[simp] theorem dilateCube_scale (s : ℤ) (Q : TriadicCube d) :
    (dilateCube s Q).scale = Q.scale + s := rfl

@[simp] theorem dilateCube_index (s : ℤ) (Q : TriadicCube d) :
    (dilateCube s Q).index = Q.index := rfl

@[simp] theorem dilateCube_originCube (s k : ℤ) :
    dilateCube s (originCube d k) = originCube d (k + s) := rfl

theorem dilateCube_injective (s : ℤ) : Function.Injective (dilateCube (d := d) s) := by
  intro Q R h
  obtain ⟨s1, i1⟩ := Q
  obtain ⟨s2, i2⟩ := R
  simp only [dilateCube, TriadicCube.mk.injEq, add_left_inj] at h
  simp [h.1, h.2]

/-- **The dilation dictionary on cube realizations.** -/
theorem cubeSet_dilateCube (s : ℤ) (Q : TriadicCube d) :
    cubeSet (dilateCube s Q) = ((3 : ℝ) ^ s) • cubeSet Q := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ s := zpow_pos (by norm_num) s
  have hfac : cubeScaleFactor (dilateCube s Q) = cubeScaleFactor Q * (3 : ℝ) ^ s := by
    rw [cubeScaleFactor, cubeScaleFactor, dilateCube_scale,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  constructor
  · intro hx i
    have h := hx i
    rw [hfac, dilateCube_index] at h
    have hval : (((3 : ℝ) ^ s)⁻¹ • x) i = x i / (3 : ℝ) ^ s := by
      simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hval]
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hr]
      linarith [h.1]
    · rw [div_lt_iff₀ hr]
      linarith [h.2]
  · intro hx i
    have h := hx i
    have hval : (((3 : ℝ) ^ s)⁻¹ • x) i = x i / (3 : ℝ) ^ s := by
      simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hval, le_div_iff₀ hr, div_lt_iff₀ hr] at h
    rw [hfac, dilateCube_index]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem childCubes_dilateCube (s : ℤ) (Q : TriadicCube d) :
    childCubes (dilateCube s Q) = (childCubes Q).image (dilateCube s) := by
  classical
  ext R
  simp only [Finset.mem_image, mem_childCubes_iff]
  constructor
  · rintro ⟨digits, rfl⟩
    refine ⟨{ scale := Q.scale - 1
              index := fun i => 3 * Q.index i + ((digits i : ℕ) : ℤ) - 1 },
      ⟨digits, rfl⟩, ?_⟩
    simp only [dilateCube, TriadicCube.mk.injEq]
    exact ⟨by omega, trivial⟩
  · rintro ⟨S, ⟨digits, rfl⟩, rfl⟩
    refine ⟨digits, ?_⟩
    simp only [dilateCube, TriadicCube.mk.injEq]
    exact ⟨by omega, trivial⟩

theorem descendantsAtDepth_dilateCube (s : ℤ) (Q : TriadicCube d) :
    ∀ j : ℕ, descendantsAtDepth (dilateCube s Q) j =
      (descendantsAtDepth Q j).image (dilateCube s)
  | 0 => by simp [descendantsAtDepth]
  | j + 1 => by
      classical
      rw [descendantsAtDepth_succ, descendantsAtDepth_dilateCube s Q j,
        descendantsAtDepth_succ, Finset.image_biUnion, Finset.biUnion_image]
      refine Finset.biUnion_congr rfl fun R _ => ?_
      rw [childCubes_dilateCube]

/-- **The partition dictionary.**  The scale-`s` subcubes of the origin cube at
scale `l` are the triadic dilations by `3^s` of the scale-`0` subcubes of the
origin cube at scale `l - s`. -/
theorem descendantsAtScale_originCube_eq_image_dilateCube {l s : ℤ} (hsl : s ≤ l) :
    descendantsAtScale (originCube d l) s =
      (descendantsAtScale (originCube d (l - s)) 0).image (dilateCube s) := by
  classical
  have hzero : (0 : ℤ) ≤ (originCube d (l - s)).scale := by
    simpa [originCube] using sub_nonneg.2 hsl
  have hs : s ≤ (originCube d l).scale := by simpa [originCube] using hsl
  have hcube : dilateCube s (originCube d (l - s)) = originCube d l := by
    rw [dilateCube_originCube]
    congr 1
    ring
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d l) hs,
    descendantsAtScale_eq_descendantsAtDepth (originCube d (l - s)) hzero, ← hcube,
    descendantsAtDepth_dilateCube]
  congr 2
  simp [originCube]

/-! ## Dilation covariance of the cube `L^p` mass -/

theorem regFieldLpMass_eq_volumeAverage (p : ℝ) (U : Set (Vec d)) (a : RegCoeffField d) :
    regFieldLpMass p U a =
      volumeAverage U (fun x : Vec d => Book.Ch02.matrixOperatorNorm (a x) ^ p) := rfl

/-- **The cube `L^p` mass is dilation covariant**: rescaling the field is the
same as rescaling the observation set. -/
theorem regFieldLpMass_smulReg (p : ℝ) {r : ℝ} (hr : r ≠ 0) (hrpos : 0 < r)
    (U : Set (Vec d)) (a : RegCoeffField d) :
    regFieldLpMass p U (smulReg r hr a) = regFieldLpMass p (r • U) a := by
  rw [regFieldLpMass_eq_volumeAverage, regFieldLpMass_eq_volumeAverage,
    Book.Ch01.volumeAverage_smul_set_comp_smul_of_pos hrpos U
      (fun y : Vec d => Book.Ch02.matrixOperatorNorm (a y) ^ p)]
  rfl

theorem regFieldLpMass_cubeSet_smulReg (p : ℝ) (s : ℤ) {r : ℝ} (hr : r ≠ 0)
    (hrs : r = (3 : ℝ) ^ s) (R : TriadicCube d) (a : RegCoeffField d) :
    regFieldLpMass p (cubeSet R) (smulReg r hr a) =
      regFieldLpMass p (cubeSet (dilateCube s R)) a := by
  have hrpos : 0 < r := by rw [hrs]; exact zpow_pos (by norm_num) s
  rw [regFieldLpMass_smulReg p hr hrpos, cubeSet_dilateCube, hrs]

/-! ## The representative at a partition-rescaled increment -/

/-- At a triadically rescaled stream increment the measurable representative on a
cube is the cube average of the increment `L^p` density on the *dilated* cube. -/
theorem regFieldLpMassRep_cubeSet_smulReg_eq_cubeAverage {p : ℝ} (hp : 0 < p)
    (s : ℤ) {r : ℝ} (hr : r ≠ 0) (hrs : r = (3 : ℝ) ^ s) (R : TriadicCube d)
    (omega : ShellSeq d) (n m : ℤ) :
    regFieldLpMassRep p (cubeSet R) (smulReg r hr (finiteShellIncrement omega n m)) =
      cubeAverage (dilateCube s R) (streamIncrementLpDensity p n m omega) := by
  rw [regFieldLpMassRep_cubeSet_smulReg_finiteShellIncrement hp R omega n m hr,
    regFieldLpMass_cubeSet_smulReg p s hr hrs, cubeAverage_streamIncrementLpDensity]

/-- The cube mass of a stream increment is the cube average of its density. -/
theorem streamIncrementLpMass_eq_cubeAverage {p : ℝ} (hp : 0 < p) (l n m : ℤ)
    (omega : ShellSeq d) :
    streamIncrementLpMass p l n m omega =
      cubeAverage (originCube d l) (streamIncrementLpDensity p n m omega) := by
  have hs : descendantsAtScale (originCube d l) l = {originCube d l} :=
    descendantsAtScale_self (originCube d l)
  have h := streamIncrementLpMass_eq_descendantAverage_of_scale hp (le_refl l) n m omega
  rw [hs] at h
  simpa using h

/-- **The exact identification.**  At a partition-rescaled increment field
CoarseGraining's descendant partition average of the measurable representative
*is* the cube mass of the increment on `cu_l`. -/
theorem descendantAverage_regFieldLpMassRep_eq_streamIncrementLpMass {p : ℝ} (hp : 0 < p)
    {l s : ℤ} (hsl : s ≤ l) {r : ℝ} (hr : r ≠ 0) (hrs : r = (3 : ℝ) ^ s)
    (n m : ℤ) (omega : ShellSeq d) :
    Book.Ch04.restrictionDescendantAverage 0 (l - s) (regFieldLpMassRep p)
        (smulReg r hr (finiteShellIncrement omega n m)) =
      streamIncrementLpMass p l n m omega := by
  classical
  rw [streamIncrementLpMass_eq_descendantAverage_of_scale hp hsl n m omega,
    descendantsAtScale_originCube_eq_image_dilateCube (d := d) hsl,
    Finset.sum_image (fun _R _ _S _ h => dilateCube_injective s h),
    Finset.card_image_of_injective _ (dilateCube_injective s),
    Book.Ch04.restrictionDescendantAverage]
  congr 1
  exact Finset.sum_congr rfl fun R _ =>
    regFieldLpMassRep_cubeSet_smulReg_eq_cubeAverage hp s hr hrs R omega n m

/-! ## Transport of a weak-Orlicz tail bound along a push-forward -/

/-- A `Psi` tail bound for a measurable observable of a push-forward law is the
same bound for its composition with the (measurable) push-forward map. -/
theorem isBigOWith_comp_of_isBigO_map {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {F : Omega → RegCoeffField d} (hF : Measurable F)
    {g : RegCoeffField d → ℝ} (hg : Measurable g) {Psi : ℝ → ℝ} {A : ℝ}
    (h : IndependentSums.IsBigO (Measure.map F mu) Psi g A) :
    IndependentSums.IsBigOWith mu Psi (fun omega => |g (F omega)|) A := by
  intro t ht
  have hs : MeasurableSet
      (IndependentSums.upperTailEvent (fun x : RegCoeffField d => |g x|) (A * t)) :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hg)
  have hgoal :
      mu.real (IndependentSums.upperTailEvent
          (fun omega => |g (F omega)|) (A * t)) =
        (Measure.map F mu).real
          (IndependentSums.upperTailEvent (fun x : RegCoeffField d => |g x|) (A * t)) := by
    rw [Measure.real, Measure.real, Measure.map_apply hF hs]
    rfl
  rw [hgoal]
  exact h ht

/-! ## The partition-average gain on the shell-sequence sample space -/

theorem measurable_partitionIncrementField (n m : ℤ) :
    Measurable (fun omega : ShellSeq d =>
      smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
        (finiteShellIncrement omega n m)) :=
  (measurable_smulReg _ _).comp (measurable_finiteShellIncrement n m)

theorem partitionStreamIncrementLaw_eq_map (M : ABKModel d) (n m : ℤ) :
    partitionStreamIncrementLaw M n m =
      Measure.map (fun omega : ShellSeq d =>
        smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
          (finiteShellIncrement omega n m)) M.P.toMeasure :=
  rfl

/-- **The CoarseGraining partition-average fluctuation theorem, applied to the
increment mass.**  All three structural hypotheses (stationarity, unit-range
dependence) and all three regularity hypotheses (locality, translation
covariance, measurability) of the cube observable are discharged by the proved
`Provider/Stream/IncrementLaw.lean` and
`Provider/Stream/IncrementMassRepresentative.lean`. -/
theorem isBigO_gammaSigma_centeredDescendantAverage_regFieldLpMassRep
    (M : ABKModel d) (p : ℝ) {n m l : ℤ}
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) {sigma K : ℝ}
    (hsigma0 : 0 < sigma) (hsigma2 : sigma ≤ 2) (hK : 0 < K)
    (hX0 : Book.Ch04.IsBigO (partitionStreamIncrementLaw M n m)
      (Book.Ch04.gammaSigma sigma)
      (Book.Ch04.restrictionCenteredOriginObservable
        (partitionStreamIncrementLaw M n m) 0
        (regFieldLpMassRep p)) K) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M n m) (Book.Ch04.gammaSigma sigma)
      (Book.Ch04.restrictionCenteredDescendantAverage
        (partitionStreamIncrementLaw M n m) 0
        (l - (m + (incrementPartitionShift d : ℤ))) (regFieldLpMassRep p))
      (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 sigma *
        Book.Ch04.partitionCardinalityScale (d := d) 0
          (l - (m + (incrementPartitionShift d : ℤ))) * K) :=
  Book.Ch04.isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw
    (le_refl (0 : ℤ)) (by omega)
    (partitionStreamIncrementLaw_stationary M n m)
    (partitionStreamIncrementLaw_unitRangeDependent M n m) (regFieldLpMassRep p)
    (fun R _ => isLocalRandomVariable_regFieldLpMassRep p (measurableSet_cubeSet R))
    (isTranslationCovariantR_regFieldLpMassRep p)
    (measurable_regFieldLpMassRep p _) (fun R _ => measurable_regFieldLpMassRep p _)
    hsigma0 hsigma2 hK hX0

/-- The centered descendant average of the representative, read at a sample. -/
theorem centeredDescendantAverage_regFieldLpMassRep_apply (M : ABKModel d) {p : ℝ}
    (hp : 0 < p) {n m l : ℤ} (hsl : m + (incrementPartitionShift d : ℤ) ≤ l)
    (omega : ShellSeq d) :
    Book.Ch04.restrictionCenteredDescendantAverage
      (partitionStreamIncrementLaw M n m) 0
        (l - (m + (incrementPartitionShift d : ℤ))) (regFieldLpMassRep p)
        (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
          (finiteShellIncrement omega n m)) =
      streamIncrementLpMass p l n m omega -
        ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
          ∂(partitionStreamIncrementLaw M n m) := by
  have hQ : (0 : ℤ) ≤ (originCube d (l - (m + (incrementPartitionShift d : ℤ)))).scale := by
    simpa [originCube] using (by omega : (0 : ℤ) ≤ l - (m + (incrementPartitionShift d : ℤ)))
  have hsub :=
    Book.Ch04.centeredDescendantAverage_eq_descendantAverage_sub_originMean
    (P := partitionStreamIncrementLaw M n m)
    (Q := originCube d (l - (m + (incrementPartitionShift d : ℤ)))) (n := 0) hQ
    (regFieldLpMassRep p)
  have h1 : Book.Ch04.restrictionCenteredDescendantAverage
      (partitionStreamIncrementLaw M n m) 0
      (l - (m + (incrementPartitionShift d : ℤ))) (regFieldLpMassRep p)
      (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
        (finiteShellIncrement omega n m)) =
      Book.Ch04.restrictionDescendantAverage 0
          (l - (m + (incrementPartitionShift d : ℤ)))
          (regFieldLpMassRep p)
          (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
            (finiteShellIncrement omega n m)) -
        ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
          ∂(partitionStreamIncrementLaw M n m) :=
    congrFun hsub _
  rw [h1, descendantAverage_regFieldLpMassRep_eq_streamIncrementLpMass hp hsl
    (incrementPartitionScale_ne_zero d m) rfl n m omega]

/-- The origin-cube centering constant is the expected cube mass at the single
scale `m + c`. -/
theorem integral_regFieldLpMassRep_originCube_zero (M : ABKModel d) {p : ℝ} (hp : 0 < p)
    (n m : ℤ) :
    ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
        ∂(partitionStreamIncrementLaw M n m) =
      ∫ omega, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m omega
        ∂M.P.toMeasure := by
  rw [partitionStreamIncrementLaw_eq_map,
    integral_map (measurable_partitionIncrementField n m).aemeasurable
      (measurable_regFieldLpMassRep p (cubeSet (originCube d 0))).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  show regFieldLpMassRep p (cubeSet (originCube d 0))
      (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
        (finiteShellIncrement omega n m)) =
    streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m omega
  rw [regFieldLpMassRep_cubeSet_smulReg_eq_cubeAverage hp
      (m + (incrementPartitionShift d : ℤ)) (incrementPartitionScale_ne_zero d m) rfl
      (originCube d 0) omega n m,
    streamIncrementLpMass_eq_cubeAverage hp]
  congr 1
  simp

/-- **The deliverable.**  On the shell-sequence sample space the cube `L^p` mass
of the increment on `cu_l` is, up to the deterministic head
`E[⨍_{cu_{m+c}} |k_m - k_n|^p]`, of size `O_{Gamma_sigma}` of the partition gain
`3^{-(d/2)(l-m-c)}` times the origin-cube amplitude. -/
theorem isBigOWith_gammaSigma_streamIncrementLpMass_sub_originMean
    (M : ABKModel d) {p : ℝ} (hp : 0 < p) {n m l : ℤ}
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) {sigma K : ℝ}
    (hsigma0 : 0 < sigma) (hsigma2 : sigma ≤ 2) (hK : 0 < K)
    (hX0 : Book.Ch04.IsBigO (partitionStreamIncrementLaw M n m)
      (Book.Ch04.gammaSigma sigma)
      (Book.Ch04.restrictionCenteredOriginObservable
        (partitionStreamIncrementLaw M n m) 0
        (regFieldLpMassRep p)) K) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma sigma)
      (fun omega : ShellSeq d =>
        |streamIncrementLpMass p l n m omega -
          ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
            ∂M.P.toMeasure|)
      (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 sigma *
        Book.Ch04.partitionCardinalityScale (d := d) 0
          (l - (m + (incrementPartitionShift d : ℤ))) * K) := by
  classical
  have hmain := isBigO_gammaSigma_centeredDescendantAverage_regFieldLpMassRep M p hsl
    hsigma0 hsigma2 hK hX0
  have hg : Measurable (Book.Ch04.restrictionCenteredDescendantAverage
      (partitionStreamIncrementLaw M n m) 0
      (l - (m + (incrementPartitionShift d : ℤ))) (regFieldLpMassRep p)) := by
    unfold Book.Ch04.restrictionCenteredDescendantAverage
    exact (Finset.measurable_sum _ fun R _ =>
      (measurable_regFieldLpMassRep p (cubeSet R)).sub measurable_const).const_mul _
  have htrans := isBigOWith_comp_of_isBigO_map M.P.toMeasure
    (measurable_partitionIncrementField (d := d) n m) hg hmain
  have hfun : (fun omega : ShellSeq d =>
      |Book.Ch04.restrictionCenteredDescendantAverage
        (partitionStreamIncrementLaw M n m) 0
        (l - (m + (incrementPartitionShift d : ℤ))) (regFieldLpMassRep p)
        (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
          (finiteShellIncrement omega n m))|) =
      fun omega : ShellSeq d =>
        |streamIncrementLpMass p l n m omega -
          ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
            ∂M.P.toMeasure| := by
    funext omega
    rw [centeredDescendantAverage_regFieldLpMassRep_apply M hp hsl omega,
      integral_regFieldLpMassRep_originCube_zero M hp n m]
  rw [← hfun]
  exact htrans

/-- **The head-plus-tail packaging.**  These are four of the five inputs of
`streamIncrementLpNorm_head_tail_of_mass_head_tail` (a nonnegative
deterministic head, a nonnegative tail, the pointwise mass bound, and the
`Gamma_sigma` tail bound with the partition gain); the fifth, `hK : 0 ≤ K`, is
supplied at the call site. -/
theorem streamIncrementLpMass_head_tail (M : ABKModel d) {p : ℝ} (hp : 0 < p) {n m l : ℤ}
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) {sigma K : ℝ}
    (hsigma0 : 0 < sigma) (hsigma2 : sigma ≤ 2) (hK : 0 < K)
    (hX0 : Book.Ch04.IsBigO (partitionStreamIncrementLaw M n m)
      (Book.Ch04.gammaSigma sigma)
      (Book.Ch04.restrictionCenteredOriginObservable
        (partitionStreamIncrementLaw M n m) 0
        (regFieldLpMassRep p)) K) :
    (0 ≤ ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
        ∂M.P.toMeasure) ∧
      (∀ omega : ShellSeq d,
        0 ≤ |streamIncrementLpMass p l n m omega -
          ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
            ∂M.P.toMeasure|) ∧
      (∀ omega : ShellSeq d,
        streamIncrementLpMass p l n m omega ≤
          (∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
            ∂M.P.toMeasure) +
            |streamIncrementLpMass p l n m omega -
              ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
                ∂M.P.toMeasure|) ∧
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma sigma)
        (fun omega : ShellSeq d =>
          |streamIncrementLpMass p l n m omega -
            ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
              ∂M.P.toMeasure|)
        (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 sigma *
          Book.Ch04.partitionCardinalityScale (d := d) 0
            (l - (m + (incrementPartitionShift d : ℤ))) * K) := by
  refine ⟨integral_nonneg fun w => streamIncrementLpMass_nonneg p _ n m w,
    fun omega => abs_nonneg _, fun omega => ?_,
    isBigOWith_gammaSigma_streamIncrementLpMass_sub_originMean M hp hsl hsigma0 hsigma2
      hK hX0⟩
  have h := le_abs_self (streamIncrementLpMass p l n m omega -
    ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
      ∂M.P.toMeasure)
  linarith

end

end Algsuperdiff.Section3.Provider.Stream

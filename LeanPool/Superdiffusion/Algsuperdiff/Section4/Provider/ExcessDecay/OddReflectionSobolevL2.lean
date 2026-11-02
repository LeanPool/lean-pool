/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionMap
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionVolume
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeReflection.Reflections

/-!
# OddReflectionSobolevL2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The cellwise change of variables for the partial odd reflection

`OddReflectionMap` supplies the pointwise half (`abs_oddExtend: |oddExtend f| =
|f ∘ windowFold|`) and `OddReflectionVolume` the volume half
(`volume_reflectedWindow_le`); what is missing is the change of variables that
turns an integral over the *partially reflected* window into `2^{#S}` copies of
the integral over the window.

## The route

`windowFold` acts coordinatewise, and in each coordinate it is either the
identity or the reflection through the met face.  Hence for **every** point `y`
there is a subset `S ⊆ Fin d` with

```text
  windowFold y = cellMap S y ,   cellMap S y i = if i ∈ S then 2·pᵢ - yᵢ else yᵢ ,
```

`pᵢ` the met-face level of coordinate `i` (`foldPivot`).  Each `cellMap S` is an
involutive homeomorphism and — being a product of one-dimensional reflections
and identities — measure preserving (`volume_preserving_pi`).  Splitting the
reflected window along the `2^d` sets

```text
  B S = (reflectedWindow \ N) ∩ {y : windowFold y = cellMap S y} ,
```

`N` the (Lebesgue null) union of the interface hyperplanes `{yᵢ = pᵢ}`, and
using `windowFold_mem_truncatedWindow` off `N`, one gets
`cellMap S '' (B S) ⊆ truncatedWindow` and therefore

```text
  ∫⁻_{reflected V} g ∘ windowFold  ≤  2^d · ∫⁻_V g .
```

Only a *cover* by the `B S` is needed, never a partition, so no disjointness
bookkeeping appears.  The exact factor is `2^{#S}` for the met set; the stated
`2^d` is the two-sided form the analytic layer consumes (matching
`volume_reflectedWindow_le`).

## What is not done here

No harmonicity, no `H¹` statement: this module is pure measure theory.

## References

* CoarseGraining
  `Homogenization.Sobolev.Foundations.CubeReflection.Reflections`
  (`realFaceReflection`, `measurePreserving_realFaceReflection`).
* Mathlib `MeasureTheory.volume_preserving_pi`,
  `MeasureTheory.MeasurePreserving.lintegral_comp_emb`,
  `MeasureTheory.lintegral_iUnion_le`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The pivot of a coordinate and the cell maps -/

open Classical in
/-- The reflection level of coordinate `i`: the met face of `∂□_m`, or `0` if
that coordinate meets no face. -/
def foldPivot (x : Vec d) (m k : ℤ) (i : Fin d) : ℝ :=
  if MeetsUpperFace x m k i then (1 / 2 : ℝ) * (3 : ℝ) ^ m
  else if MeetsLowerFace x m k i then -(1 / 2 : ℝ) * (3 : ℝ) ^ m
  else 0

/-- The reflection of exactly the coordinates in `S` through their pivots. -/
def cellMap (x : Vec d) (m k : ℤ) (S : Finset (Fin d)) : Vec d → Vec d :=
  fun y i => if i ∈ S then realFaceReflection (foldPivot x m k i) (y i) else y i

@[simp] theorem cellMap_apply (x : Vec d) (m k : ℤ) (S : Finset (Fin d))
    (y : Vec d) (i : Fin d) :
    cellMap x m k S y i =
      if i ∈ S then realFaceReflection (foldPivot x m k i) (y i) else y i :=
  rfl

theorem cellMap_involutive (x : Vec d) (m k : ℤ) (S : Finset (Fin d)) (y : Vec d) :
    cellMap x m k S (cellMap x m k S y) = y := by
  funext i
  by_cases hi : i ∈ S
  · simp only [cellMap_apply, ite_eq_left hi, realFaceReflection]
    ring
  · simp only [cellMap_apply, ite_eq_right hi]

theorem cellMap_injective (x : Vec d) (m k : ℤ) (S : Finset (Fin d)) :
    Function.Injective (cellMap x m k S) := by
  intro y z hyz
  have h := congrArg (cellMap x m k S) hyz
  rwa [cellMap_involutive, cellMap_involutive] at h

theorem continuous_cellMap (x : Vec d) (m k : ℤ) (S : Finset (Fin d)) :
    Continuous (cellMap x m k S) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i ∈ S
  · simp only [cellMap_apply, ite_eq_left hi, realFaceReflection]
    exact continuous_const.sub (continuous_apply i)
  · simp only [cellMap_apply, ite_eq_right hi]
    exact continuous_apply i

theorem measurableEmbedding_cellMap (x : Vec d) (m k : ℤ) (S : Finset (Fin d)) :
    MeasurableEmbedding (cellMap x m k S) :=
  (continuous_cellMap x m k S).measurableEmbedding (cellMap_injective x m k S)

theorem measurePreserving_cellMap (x : Vec d) (m k : ℤ) (S : Finset (Fin d)) :
    MeasurePreserving (cellMap x m k S) := by
  classical
  set f : (i : Fin d) → ℝ → ℝ :=
    fun i => if i ∈ S then realFaceReflection (foldPivot x m k i) else id with hf
  have hfi : ∀ i : Fin d, MeasurePreserving (f i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa [hf, hi] using measurePreserving_realFaceReflection (foldPivot x m k i)
    · simpa [hf, hi] using MeasurePreserving.id (volume : Measure ℝ)
  have hpi : MeasurePreserving (fun y : Vec d => fun i : Fin d => f i (y i)) :=
    volume_preserving_pi hfi
  have hEq : (fun y : Vec d => fun i : Fin d => f i (y i)) = cellMap x m k S := by
    funext y i
    by_cases hi : i ∈ S <;> simp [hf, cellMap, hi]
  rwa [hEq] at hpi

/-! ## 2. The fold is a cell map at every point -/

theorem foldCoord_eq_or (x : Vec d) (m k : ℤ) (i : Fin d) (t : ℝ) :
    foldCoord x m k i t = t ∨
      foldCoord x m k i t = realFaceReflection (foldPivot x m k i) t := by
  by_cases hup : MeetsUpperFace x m k i
  · have hpiv : foldPivot x m k i = (1 / 2 : ℝ) * (3 : ℝ) ^ m := ite_eq_left hup
    rw [foldCoord_of_meetsUpperFace hup, hpiv, realFaceReflection]
    rcases min_choice t ((3 : ℝ) ^ m - t) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; ring)
  · by_cases hlow : MeetsLowerFace x m k i
    · have hpiv : foldPivot x m k i = -(1 / 2 : ℝ) * (3 : ℝ) ^ m := by
        rw [foldPivot, ite_eq_right hup, ite_eq_left hlow]
      rw [foldCoord_of_meetsLowerFace hup hlow, hpiv, realFaceReflection]
      rcases max_choice t (-(3 : ℝ) ^ m - t) with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; ring)
    · exact Or.inl (foldCoord_of_unmet hup hlow t)

theorem continuous_windowFold (x : Vec d) (m k : ℤ) :
    Continuous (windowFold x m k) := by
  refine continuous_pi fun i => ?_
  by_cases hup : MeetsUpperFace x m k i
  · simp only [windowFold_apply, foldCoord_of_meetsUpperFace hup]
    exact (continuous_apply i).min (continuous_const.sub (continuous_apply i))
  · by_cases hlow : MeetsLowerFace x m k i
    · simp only [windowFold_apply, foldCoord_of_meetsLowerFace hup hlow]
      exact (continuous_apply i).max (continuous_const.sub (continuous_apply i))
    · simp only [windowFold_apply, foldCoord_of_unmet hup hlow]
      exact continuous_apply i

/-- **Every point lies in some cell.**  The coordinatewise fold agrees, at each
point, with the reflection of the coordinates it actually moves. -/
theorem exists_cellMap_eq (x : Vec d) (m k : ℤ) (y : Vec d) :
    ∃ S : Finset (Fin d), windowFold x m k y = cellMap x m k S y := by
  classical
  refine ⟨Finset.univ.filter fun i => foldCoord x m k i (y i) ≠ y i, ?_⟩
  funext i
  have hmem : i ∈ Finset.univ.filter (fun j => foldCoord x m k j (y j) ≠ y j) ↔
      foldCoord x m k i (y i) ≠ y i := by simp
  rw [windowFold_apply, cellMap_apply]
  by_cases hi : i ∈ Finset.univ.filter fun j => foldCoord x m k j (y j) ≠ y j
  · rw [ite_eq_left hi]
    rcases foldCoord_eq_or x m k i (y i) with he | he
    · exact absurd he (hmem.mp hi)
    · exact he
  · rw [ite_eq_right hi]
    exact not_not.mp fun hne => hi (hmem.mpr hne)

/-! ## 3. The interface hyperplanes are null -/

theorem volume_coordLevel_eq_zero (i : Fin d) (c : ℝ) :
    volume {y : Vec d | y i = c} = 0 := by
  classical
  have hset : {y : Vec d | y i = c} =
      Set.pi Set.univ fun j => if j = i then ({c} : Set ℝ) else Set.univ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hy j
      by_cases hji : j = i
      · subst hji
        simp [hy]
      · simp [hji]
    · intro hy
      simpa using hy i
  rw [hset, volume_pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

/-- The union of the interface hyperplanes: the null set the change of
variables discards. -/
def foldInterface (x : Vec d) (m k : ℤ) : Set (Vec d) :=
  ⋃ i : Fin d, {y : Vec d | y i = foldPivot x m k i}

theorem volume_foldInterface_eq_zero (x : Vec d) (m k : ℤ) :
    volume (foldInterface x m k) = 0 :=
  measure_iUnion_null fun i => volume_coordLevel_eq_zero i (foldPivot x m k i)

theorem notMem_foldInterface_apply {x : Vec d} {m k : ℤ} {y : Vec d}
    (hy : y ∉ foldInterface x m k) (i : Fin d) : y i ≠ foldPivot x m k i := by
  intro h
  exact hy (Set.mem_iUnion.2 ⟨i, h⟩)

/-! ## 4. The cellwise change of variables -/

private theorem setLIntegral_comp_cellMap (x : Vec d) (m k : ℤ)
    (S : Finset (Fin d)) (g : Vec d → ℝ≥0∞) {B : Set (Vec d)}
    (hB : MeasurableSet B) :
    ∫⁻ y in B, g (cellMap x m k S y) = ∫⁻ z in cellMap x m k S '' B, g z := by
  classical
  set Φ : Vec d → Vec d := cellMap x m k S with hΦ
  have hinv : ∀ y, Φ (Φ y) = y := cellMap_involutive x m k S
  have himg : Φ '' B = Φ ⁻¹' B := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change Φ (Φ y) ∈ B
      rwa [hinv]
    · intro hz
      exact ⟨Φ z, hz, hinv z⟩
  have hmeasB : MeasurableSet (Φ ⁻¹' B) :=
    (measurableEmbedding_cellMap x m k S).measurable hB
  have hpt : ∀ y : Vec d,
      B.indicator (fun y => g (Φ y)) y = ((Φ ⁻¹' B).indicator g) (Φ y) := by
    intro y
    by_cases hy : y ∈ B
    · have hy' : Φ y ∈ Φ ⁻¹' B := by
        change Φ (Φ y) ∈ B
        rwa [hinv]
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy']
    · have hy' : Φ y ∉ Φ ⁻¹' B := by
        intro hmem
        exact hy (by simpa [hinv] using hmem)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
  calc ∫⁻ y in B, g (Φ y)
      = ∫⁻ y, B.indicator (fun y => g (Φ y)) y := (lintegral_indicator hB _).symm
    _ = ∫⁻ y, ((Φ ⁻¹' B).indicator g) (Φ y) := by
        exact lintegral_congr fun y => hpt y
    _ = ∫⁻ z, ((Φ ⁻¹' B).indicator g) z :=
        (measurePreserving_cellMap x m k S).lintegral_comp_emb
          (measurableEmbedding_cellMap x m k S) _
    _ = ∫⁻ z in Φ ⁻¹' B, g z := lintegral_indicator hmeasB _
    _ = ∫⁻ z in Φ '' B, g z := by rw [himg]

/-- **: the cellwise change of variables.**  Folding the partially reflected window
onto the window costs at most the factor `2^d` (the exact factor is `2^{#S}`
for the met set `S`). -/
theorem setLIntegral_comp_windowFold_le (x : Vec d) {m k : ℤ} (hkm : k < m)
    (g : Vec d → ℝ≥0∞) :
    ∫⁻ y in reflectedWindow x m k, g (windowFold x m k y) ≤
      2 ^ d * ∫⁻ y in truncatedWindow x m k, g y := by
  classical
  set A : Set (Vec d) := reflectedWindow x m k with hA
  set V : Set (Vec d) := truncatedWindow x m k with hV
  set N : Set (Vec d) := foldInterface x m k with hN
  set B : Finset (Fin d) → Set (Vec d) := fun S =>
    (A \ N) ∩ {y : Vec d | windowFold x m k y = cellMap x m k S y} with hB
  have hAmeas : MeasurableSet A := measurableSet_reflectedWindow x m k
  have hNmeas : MeasurableSet N := by
    rw [hN, foldInterface]
    exact MeasurableSet.iUnion fun i =>
      measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hBmeas : ∀ S, MeasurableSet (B S) := by
    intro S
    refine (hAmeas.diff hNmeas).inter ?_
    exact (isClosed_eq (continuous_windowFold x m k) (continuous_cellMap x m k S))
      |>.measurableSet
  -- (i) the interface is null
  have hae : A =ᵐ[(volume : Measure (Vec d))] A \ N := by
    have hNc : ∀ᵐ y ∂(volume : Measure (Vec d)), y ∉ N := by
      rw [MeasureTheory.ae_iff]
      simpa [hN] using volume_foldInterface_eq_zero x m k
    filter_upwards [hNc] with y hy
    exact propext ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
  have hstep0 : ∫⁻ y in A, g (windowFold x m k y) =
      ∫⁻ y in A \ N, g (windowFold x m k y) := setLIntegral_congr hae
  -- (ii) the cells cover
  have hcover : A \ N ⊆ ⋃ S : Finset (Fin d), B S := by
    intro y hy
    obtain ⟨S, hS⟩ := exists_cellMap_eq x m k y
    exact Set.mem_iUnion.2 ⟨S, ⟨hy, hS⟩⟩
  -- (iii) each cell maps into the window
  have hinto : ∀ S : Finset (Fin d), cellMap x m k S '' B S ⊆ V := by
    intro S z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyA : y ∈ A := hy.1.1
    have hyN : y ∉ N := hy.1.2
    have hfold : windowFold x m k y = cellMap x m k S y := hy.2
    have hup : ∀ i, MeetsUpperFace x m k i →
        y i ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
      intro i hi
      have hpiv : foldPivot x m k i = (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
        rw [foldPivot, ite_eq_left hi]
      have := notMem_foldInterface_apply (x := x) (m := m) (k := k) hyN i
      rwa [hpiv] at this
    have hlow : ∀ i, MeetsLowerFace x m k i →
        y i ≠ -(1 / 2 : ℝ) * (3 : ℝ) ^ m := by
      intro i hi
      have hnu : ¬ MeetsUpperFace x m k i := fun hu =>
        not_meetsLowerFace_of_meetsUpperFace hkm hu hi
      have hpiv : foldPivot x m k i = -(1 / 2 : ℝ) * (3 : ℝ) ^ m := by
        rw [foldPivot, ite_eq_right hnu, ite_eq_left hi]
      have := notMem_foldInterface_apply (x := x) (m := m) (k := k) hyN i
      rwa [hpiv] at this
    have := windowFold_mem_truncatedWindow hkm hyA hup hlow
    rwa [hfold] at this
  -- (iv) assemble
  calc ∫⁻ y in A, g (windowFold x m k y)
      = ∫⁻ y in A \ N, g (windowFold x m k y) := hstep0
    _ ≤ ∫⁻ y in ⋃ S : Finset (Fin d), B S, g (windowFold x m k y) :=
        lintegral_mono_set hcover
    _ ≤ ∑' S : Finset (Fin d), ∫⁻ y in B S, g (windowFold x m k y) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' _S : Finset (Fin d), ∫⁻ y in V, g y := by
        refine ENNReal.tsum_le_tsum fun S => ?_
        have hcongr : ∫⁻ y in B S, g (windowFold x m k y) =
            ∫⁻ y in B S, g (cellMap x m k S y) := by
          refine setLIntegral_congr_fun (hBmeas S) fun y hy => ?_
          rw [hy.2]
        rw [hcongr, setLIntegral_comp_cellMap x m k S g (hBmeas S)]
        exact lintegral_mono_set (hinto S)
    _ = 2 ^ d * ∫⁻ y in V, g y := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
          Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-! ## 5. The `L²` cost of the odd extension -/

theorem enorm_oddExtend (x : Vec d) (m k : ℤ) (f : Vec d → ℝ) (y : Vec d) :
    ‖oddExtend x m k f y‖ₑ = ‖f (windowFold x m k y)‖ₑ := by
  have hnorm : ‖oddExtend x m k f y‖ = ‖f (windowFold x m k y)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_oddExtend]
  rw [← ofReal_norm, ← ofReal_norm, hnorm]

/-- **, in the shape the `Lᵖ` layer consumes.** -/
theorem setLIntegral_enorm_rpow_oddExtend_le (x : Vec d) {m k : ℤ} (hkm : k < m)
    (f : Vec d → ℝ) (q : ℝ) :
    ∫⁻ y in reflectedWindow x m k, ‖oddExtend x m k f y‖ₑ ^ q ≤
      2 ^ d * ∫⁻ y in truncatedWindow x m k, ‖f y‖ₑ ^ q := by
  have hcongr : ∫⁻ y in reflectedWindow x m k, ‖oddExtend x m k f y‖ₑ ^ q =
      ∫⁻ y in reflectedWindow x m k, ‖f (windowFold x m k y)‖ₑ ^ q :=
    lintegral_congr fun y => by rw [enorm_oddExtend]
  rw [hcongr]
  exact setLIntegral_comp_windowFold_le x hkm (fun z => ‖f z‖ₑ ^ q)

private theorem measurable_foldSignCoord (x : Vec d) (m k : ℤ) (i : Fin d) :
    Measurable (foldSignCoord x m k i) :=
  Measurable.ite (MeasurableSet.const _)
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
    (Measurable.ite (MeasurableSet.const _)
      (Measurable.ite measurableSet_Iio measurable_const measurable_const) measurable_const)

private theorem measurable_windowFoldSign (x : Vec d) (m k : ℤ) :
    Measurable (windowFoldSign x m k) :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_foldSignCoord x m k i).comp (measurable_pi_apply i)

/-- The fold does not charge null sets of the window: it is quasi measure
preserving from the reflected window to the window. -/
private theorem quasiMeasurePreserving_windowFold (x : Vec d) {m k : ℤ} (hkm : k < m) :
    Measure.QuasiMeasurePreserving (windowFold x m k)
      (volume.restrict (reflectedWindow x m k))
      (volume.restrict (truncatedWindow x m k)) := by
  have hmeas : Measurable (windowFold x m k) := (continuous_windowFold x m k).measurable
  refine ⟨hmeas, Measure.AbsolutelyContinuous.mk ?_⟩
  intro T hT hT0
  rw [Measure.map_apply hmeas hT]
  have h := setLIntegral_comp_windowFold_le x hkm (T.indicator 1)
  rw [lintegral_indicator_one hT, hT0, mul_zero] at h
  have hpre : ∫⁻ y in reflectedWindow x m k, T.indicator 1 (windowFold x m k y) =
      volume.restrict (reflectedWindow x m k) (windowFold x m k ⁻¹' T) := by
    rw [← lintegral_indicator_one (hmeas hT)]
    rfl
  rw [← hpre]
  exact nonpos_iff_eq_zero.mp h

/-- **: the odd extension costs at most `C(d) = 2^d` in `L²`.** -/
theorem eLpNorm_oddExtend_le (x : Vec d) {m k : ℤ} (hkm : k < m) (f : Vec d → ℝ) :
    eLpNorm (oddExtend x m k f) 2 (volume.restrict (reflectedWindow x m k)) ≤
      2 ^ d * eLpNorm f 2 (volume.restrict (truncatedWindow x m k)) := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict (truncatedWindow x m k))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (pow_ne_zero d (by norm_num))]
    exact le_top
  have hodd : AEStronglyMeasurable (oddExtend x m k f)
      (volume.restrict (reflectedWindow x m k)) :=
    (measurable_windowFoldSign x m k).aestronglyMeasurable.mul
      (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_windowFold x hkm))
  have htoReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  have hA : eLpNorm (oddExtend x m k f) 2
      (volume.restrict (reflectedWindow x m k)) =
      (∫⁻ y in reflectedWindow x m k, ‖oddExtend x m k f y‖ₑ ^ (2 : ℝ)) ^
        ((1 : ℝ) / 2) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hodd,
      htoReal]
  have hV : eLpNorm f 2 (volume.restrict (truncatedWindow x m k)) =
      (∫⁻ y in truncatedWindow x m k, ‖f y‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
      htoReal]
  rw [hA, hV]
  have hle := setLIntegral_enorm_rpow_oddExtend_le x hkm f (2 : ℝ)
  have h1 : (∫⁻ y in reflectedWindow x m k, ‖oddExtend x m k f y‖ₑ ^ (2 : ℝ)) ^
      ((1 : ℝ) / 2) ≤
      ((2 : ℝ≥0∞) ^ d * ∫⁻ y in truncatedWindow x m k, ‖f y‖ₑ ^ (2 : ℝ)) ^
        ((1 : ℝ) / 2) :=
    ENNReal.rpow_le_rpow hle (by norm_num)
  have h2 : ((2 : ℝ≥0∞) ^ d * ∫⁻ y in truncatedWindow x m k, ‖f y‖ₑ ^ (2 : ℝ)) ^
      ((1 : ℝ) / 2) =
      ((2 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2) *
        (∫⁻ y in truncatedWindow x m k, ‖f y‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have h3 : ((2 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ≥0∞) ^ d := by
    have hone : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ d := one_le_pow₀ (by norm_num)
    calc ((2 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2)
        ≤ ((2 : ℝ≥0∞) ^ d) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le hone (by norm_num)
      _ = (2 : ℝ≥0∞) ^ d := ENNReal.rpow_one _
  calc (∫⁻ y in reflectedWindow x m k, ‖oddExtend x m k f y‖ₑ ^ (2 : ℝ)) ^
        ((1 : ℝ) / 2)
      ≤ ((2 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2) *
        (∫⁻ y in truncatedWindow x m k, ‖f y‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← h2]; exact h1
    _ ≤ (2 : ℝ≥0∞) ^ d *
        (∫⁻ y in truncatedWindow x m k, ‖f y‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        mul_le_mul' h3 (le_refl _)

end

end Algsuperdiff.Section4.Provider.ExcessDecay

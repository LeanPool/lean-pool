/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.TranslatedCubeGeometry
public import LeanPool.HighContrastHomogenization.Support.Besov.Positive
public import LeanPool.HighContrastHomogenization.Support.Besov.Localization
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.Definitions
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Definitions

/-!
# High-contrast homogenization: Provider.Regularity.CubeTranslationDualTest

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The displaced-cube test function

The difference of the indicator of a centered triadic cube and of its
displacement, normalized by the volume ratio to the parent cube, is a mean-zero
test whose pairing with a vector field reads exactly the difference between the
field's average over the cube and its average over the displaced cube.

Its positive Besov norm is small for two independent reasons, and the two
estimates are recorded separately.

* At every depth the oscillation is controlled by the volume of the set where
  the cube and its displacement disagree, which is proportional to the
  displacement relative to the cube side.
* Beyond the depth of the cube itself the test is close, in normalized `L²`, to
  a test built from a displacement adapted to the triadic grid at that depth,
  and an adapted test has no oscillation at that depth at all.  The error is
  proportional to the depth's own side length, so it decays geometrically.

Together the two make the Besov norm of the test proportional to the square root
of the relative displacement, which is the whole content of the translation
stability of cube averages.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The scaled difference of two indicator functions. -/
@[expose]
def cubeIndicatorDifference (c : ℝ) (S₁ S₂ : Set (Vec d)) : Vec d → ℝ :=
  fun x => c * ((S₁.indicator (fun _ => (1 : ℝ)) x) -
    (S₂.indicator (fun _ => (1 : ℝ)) x))

/-- The set on which two sets disagree. -/
@[expose]
def setDisagreement (S₁ S₂ : Set (Vec d)) : Set (Vec d) :=
  (S₁ \ S₂) ∪ (S₂ \ S₁)

theorem measurable_cubeIndicatorDifference {c : ℝ} {S₁ S₂ : Set (Vec d)}
    (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂) :
    Measurable (cubeIndicatorDifference c S₁ S₂) :=
  (measurable_const.mul
    ((measurable_const.indicator h₁).sub (measurable_const.indicator h₂)))

theorem abs_cubeIndicatorDifference_le {c : ℝ} (hc : 0 ≤ c)
    (S₁ S₂ : Set (Vec d)) (x : Vec d) :
    |cubeIndicatorDifference c S₁ S₂ x| ≤
      c * ((setDisagreement S₁ S₂).indicator (fun _ => (1 : ℝ)) x) := by
  unfold cubeIndicatorDifference setDisagreement
  by_cases h₁ : x ∈ S₁ <;> by_cases h₂ : x ∈ S₂ <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h₁, h₂,
      abs_of_nonneg hc]

theorem abs_cubeIndicatorDifference_le_const {c : ℝ} (hc : 0 ≤ c)
    (S₁ S₂ : Set (Vec d)) (x : Vec d) :
    |cubeIndicatorDifference c S₁ S₂ x| ≤ c := by
  refine (abs_cubeIndicatorDifference_le hc S₁ S₂ x).trans ?_
  by_cases hx : x ∈ setDisagreement S₁ S₂ <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hc]

theorem measurableSet_setDisagreement {S₁ S₂ : Set (Vec d)}
    (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂) :
    MeasurableSet (setDisagreement S₁ S₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

theorem memLp_cubeIndicatorDifference {c : ℝ} (hc : 0 ≤ c) {S₁ S₂ : Set (Vec d)}
    (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂) (Q : TriadicCube d)
    (p : ℝ≥0∞) :
    MemLp (cubeIndicatorDifference c S₁ S₂) p (normalizedCubeMeasure Q) := by
  refine MemLp.of_bound
    (measurable_cubeIndicatorDifference h₁ h₂).aestronglyMeasurable c ?_
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using abs_cubeIndicatorDifference_le_const hc S₁ S₂ x

/-! ## Normalized measure of a disagreement set -/

theorem normalizedCubeMeasure_real_le_volume_div (Q : TriadicCube d)
    {G : Set (Vec d)} (hG : volume G ≠ ⊤) :
    (normalizedCubeMeasure Q).real G ≤ (volume G).toReal / cubeVolume Q := by
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  have hle : normalizedCubeMeasure Q G ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) * volume G := by
    rw [normalizedCubeMeasure, Measure.smul_apply, smul_eq_mul, cubeMeasure,
      Measure.restrict_apply' (measurableSet_cubeSet Q)]
    gcongr
    exact Set.inter_subset_left
  have htop : ENNReal.ofReal ((cubeVolume Q)⁻¹) * volume G ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG
  have hreal := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [div_eq_inv_mul]
  exact hreal

theorem cubeLpNorm_two_cubeIndicatorDifference_le (Q : TriadicCube d) {c : ℝ}
    (hc : 0 ≤ c) {S₁ S₂ : Set (Vec d)} (h₁ : MeasurableSet S₁)
    (h₂ : MeasurableSet S₂) (htop : volume (setDisagreement S₁ S₂) ≠ ⊤) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeIndicatorDifference c S₁ S₂) ≤
      c * Real.sqrt ((volume (setDisagreement S₁ S₂)).toReal / cubeVolume Q) := by
  set G : Set (Vec d) := setDisagreement S₁ S₂ with hGdef
  have hGmeas : MeasurableSet G := measurableSet_setDisagreement h₁ h₂
  have hbound : ∀ᵐ x ∂ normalizedCubeMeasure Q,
      ‖cubeIndicatorDifference c S₁ S₂ x‖ ≤
        ‖G.indicator (fun _ => c) x‖ := by
    filter_upwards with x
    have hle := abs_cubeIndicatorDifference_le hc S₁ S₂ x
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx] at hle ⊢
      simpa only [Real.norm_eq_abs, mul_one, abs_of_nonneg hc] using hle
    · rw [Set.indicator_of_notMem hx] at hle ⊢
      simpa only [Real.norm_eq_abs, mul_zero, abs_zero, norm_zero] using hle
  have hmono : eLpNorm (cubeIndicatorDifference c S₁ S₂) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) ≤
        eLpNorm (G.indicator (fun _ => c)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
    eLpNorm_mono_ae (measurable_cubeIndicatorDifference h₁ h₂).aestronglyMeasurable hbound
  have hind : eLpNorm (G.indicator (fun _ => c)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) =
        (‖c‖ₑ) * (normalizedCubeMeasure Q G) ^ (1 / (2 : ℝ)) := by
    simpa using eLpNorm_indicator_const (μ := normalizedCubeMeasure Q)
      hGmeas.nullMeasurableSet
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hfin : normalizedCubeMeasure Q G ≠ ⊤ :=
    (measure_lt_top (normalizedCubeMeasure Q) G).ne
  have htoReal : (eLpNorm (G.indicator (fun _ => c)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)).toReal =
        c * Real.sqrt ((normalizedCubeMeasure Q).real G) := by
    rw [hind, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    rw [Real.sqrt_eq_rpow]
    simp [Measure.real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hrhsTop : eLpNorm (G.indicator (fun _ => c)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) ≠ ⊤ := by
    rw [hind]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin)
  have hreal := ENNReal.toReal_mono hrhsTop hmono
  rw [htoReal] at hreal
  refine hreal.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine Real.sqrt_le_sqrt ?_
  exact normalizedCubeMeasure_real_le_volume_div Q htop

/-! ## Oscillation against a normalized `L²` norm -/

theorem cubeBesovOscillation_two_le_two_mul_cubeLpNorm (Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) f ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by
  have hconst : MemLp (fun _ : Vec d => -cubeAverage Q f) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := memLp_const _
  have hfun : cubeFluctuation Q f =
      fun x => f x + (fun _ : Vec d => -cubeAverage Q f) x := by
    funext x
    simp [cubeFluctuation, sub_eq_add_neg]
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) f
        = cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => f x + (fun _ : Vec d => -cubeAverage Q f) x) := by
          rw [cubeBesovOscillation, hfun]
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) f +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage Q f) :=
          cubeLpNorm_add_le Q (2 : ℝ≥0∞) f _ hf hconst (by norm_num)
    _ = cubeLpNorm Q (2 : ℝ≥0∞) f + ‖cubeAverage Q f‖ := by
          rw [cubeLpNorm_const Q (2 : ℝ≥0∞) (-cubeAverage Q f) (by norm_num)]
          simp
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) f + cubeLpNorm Q (2 : ℝ≥0∞) f := by
          gcongr
          exact norm_cubeAverage_le_cubeLpNorm_two Q f hf
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by ring

/-- A function that is constant on a cube has no oscillation there. -/
theorem cubeBesovOscillation_eq_zero_of_eq_on_cubeSet (R : TriadicCube d)
    {f : Vec d → ℝ} {gamma : ℝ} (hf : ∀ x ∈ cubeSet R, f x = gamma) :
    cubeBesovOscillation R (2 : ℝ≥0∞) f = 0 := by
  have havg : cubeAverage R f = gamma := by
    rw [cubeAverage_congr_on_cubeSet hf, cubeAverage_const]
  have hzero : ∀ x ∈ cubeSet R, cubeFluctuation R f x = 0 := by
    intro x hx
    simp [cubeFluctuation, hf x hx, havg]
  have hcube : cubeFluctuation R f =ᵐ[cubeMeasure R] fun _ => (0 : ℝ) := by
    rw [cubeMeasure, Filter.EventuallyEq,
      MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet R)]
    exact Filter.Eventually.of_forall hzero
  have hae : cubeFluctuation R f =ᵐ[normalizedCubeMeasure R] fun _ => (0 : ℝ) := by
    rw [normalizedCubeMeasure]
    exact Measure.ae_smul_measure hcube (ENNReal.ofReal ((cubeVolume R)⁻¹))
  rw [cubeBesovOscillation, cubeLpNorm,
    eLpNorm_congr_ae (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure R) hae]
  simp

/-- Two functions that agree on a cube have the same oscillation there. -/
theorem cubeBesovOscillation_congr_on_cubeSet (R : TriadicCube d)
    {f g : Vec d → ℝ} (hfg : ∀ x ∈ cubeSet R, f x = g x) :
    cubeBesovOscillation R (2 : ℝ≥0∞) f = cubeBesovOscillation R (2 : ℝ≥0∞) g := by
  have havg : cubeAverage R f = cubeAverage R g :=
    cubeAverage_congr_on_cubeSet hfg
  have hcube : cubeFluctuation R f =ᵐ[cubeMeasure R] cubeFluctuation R g := by
    rw [cubeMeasure, Filter.EventuallyEq,
      MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet R)]
    refine Filter.Eventually.of_forall fun x hx => ?_
    simp [cubeFluctuation, hfg x hx, havg]
  have hae : cubeFluctuation R f =ᵐ[normalizedCubeMeasure R] cubeFluctuation R g := by
    rw [normalizedCubeMeasure]
    exact Measure.ae_smul_measure hcube (ENNReal.ofReal ((cubeVolume R)⁻¹))
  rw [cubeBesovOscillation, cubeBesovOscillation, cubeLpNorm, cubeLpNorm,
    eLpNorm_congr_ae hae]

/-! ## The displaced-cube test -/

/-- The mean-zero test that reads the difference between the average of a field
over a centered triadic cube and its average over a fixed displacement of that
cube. -/
@[expose]
def cubeTranslationTest (d : ℕ) (n : ℕ) (t : Vec d) : Vec d → ℝ :=
  cubeIndicatorDifference ((3 : ℝ) ^ d) (cubeSet (originCube d (n : ℤ)))
    (translatedCubeSet (originCube d (n : ℤ)) t)

theorem memLp_cubeTranslationTest (d n : ℕ) (t : Vec d) (Q : TriadicCube d)
    (p : ℝ≥0∞) :
    MemLp (cubeTranslationTest d n t) p (normalizedCubeMeasure Q) :=
  memLp_cubeIndicatorDifference (by positivity)
    (measurableSet_cubeSet _) (measurableSet_translatedCubeSet _ _) Q p

/-- A test built from two triadic-grid-compatible sets is constant on every
cube of the compatible scale. -/
private theorem exists_const_on_cubeSet_of_subset_or_disjoint {R : TriadicCube d}
    {c : ℝ} {S₁ S₂ : Set (Vec d)}
    (h₁ : cubeSet R ⊆ S₁ ∨ Disjoint (cubeSet R) S₁)
    (h₂ : cubeSet R ⊆ S₂ ∨ Disjoint (cubeSet R) S₂) :
    ∃ gamma : ℝ, ∀ x ∈ cubeSet R, cubeIndicatorDifference c S₁ S₂ x = gamma := by
  have hval : ∀ (S : Set (Vec d)),
      (cubeSet R ⊆ S ∨ Disjoint (cubeSet R) S) →
        ∃ a : ℝ, ∀ x ∈ cubeSet R, S.indicator (fun _ => (1 : ℝ)) x = a := by
    intro S hS
    rcases hS with hS | hS
    · exact ⟨1, fun x hx => Set.indicator_of_mem (hS hx) _⟩
    · refine ⟨0, fun x hx => Set.indicator_of_notMem ?_ _⟩
      exact Set.disjoint_left.mp hS hx
  obtain ⟨a, ha⟩ := hval S₁ h₁
  obtain ⟨b, hb⟩ := hval S₂ h₂
  refine ⟨c * (a - b), fun x hx => ?_⟩
  rw [cubeIndicatorDifference, ha x hx, hb x hx]

/-- Depth averages are controlled by any field whose normalized `L²` norm
dominates the oscillation on every cube of that depth. -/
private theorem depthAverage_le_of_forall_oscillation_le (Q : TriadicCube d)
    (j : ℕ) {g w : Vec d → ℝ}
    (hw : MemLp w (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hosc : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) g ≤ 2 * cubeLpNorm R (2 : ℝ≥0∞) w) :
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j ≤
      4 * (cubeLpNorm Q (2 : ℝ≥0∞) w) ^ 2 := by
  have htwo : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  calc
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j
        ≤ descendantsAverage Q j (fun R => 4 * (cubeLpNorm R (2 : ℝ≥0∞) w) ^ 2) := by
          refine descendantsAverage_le_descendantsAverage Q j ?_
          intro R hR
          have hle := hosc R hR
          have hnn : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) g :=
            cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) g
          have hsq : (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ (2 : ℕ) ≤
              (2 * cubeLpNorm R (2 : ℝ≥0∞) w) ^ (2 : ℕ) :=
            pow_le_pow_left₀ hnn hle 2
          rw [htwo, Real.rpow_natCast]
          calc
            (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ (2 : ℕ)
                ≤ (2 * cubeLpNorm R (2 : ℝ≥0∞) w) ^ (2 : ℕ) := hsq
            _ = 4 * (cubeLpNorm R (2 : ℝ≥0∞) w) ^ 2 := by ring
    _ = 4 * descendantsAverage Q j (fun R => (cubeLpNorm R (2 : ℝ≥0∞) w) ^ 2) :=
          descendantsAverage_mul_left Q j 4 _
    _ = 4 * (cubeLpNorm Q (2 : ℝ≥0∞) w) ^ 2 := by
          rw [show descendantsAverage Q j
              (fun R => (cubeLpNorm R (2 : ℝ≥0∞) w) ^ 2) =
            cubeL2ScalarDepthAverage Q w j from rfl,
            cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q w j hw]

/-! ## The two depth estimates -/

private theorem cubeVolume_originCube (m : ℕ) :
    cubeVolume (originCube d (m : ℤ)) = ((3 : ℝ) ^ m) ^ d := by
  rw [cubeVolume, cubeScaleFactor_originCube, zpow_natCast]

private theorem depthAverage_translationTest_le (d n : ℕ) (t : Vec d) (j : ℕ)
    {u : Vec d} {V : ℝ} (hV : 0 ≤ V) (hVle : V ≤ (3 : ℝ) ^ n)
    (huv : ∀ i, |u i - t i| ≤ V)
    (hosc : ∀ R ∈ descendantsAtDepth (originCube d ((n + 1 : ℕ) : ℤ)) j,
      cubeBesovOscillation R (2 : ℝ≥0∞) (cubeTranslationTest d n t) ≤
        2 * cubeLpNorm R (2 : ℝ≥0∞)
          (cubeIndicatorDifference ((3 : ℝ) ^ d)
            (translatedCubeSet (originCube d (n : ℤ)) u)
            (translatedCubeSet (originCube d (n : ℤ)) t))) :
    cubeBesovDepthAverage (originCube d ((n + 1 : ℕ) : ℤ)) (2 : ℝ≥0∞)
        (cubeTranslationTest d n t) j ≤
      8 * (d : ℝ) * (3 : ℝ) ^ d * (V / (3 : ℝ) ^ n) := by
  set A : TriadicCube d := originCube d (n : ℤ) with hA
  set Q : TriadicCube d := originCube d ((n + 1 : ℕ) : ℤ) with hQ
  set w : Vec d → ℝ :=
    cubeIndicatorDifference ((3 : ℝ) ^ d) (translatedCubeSet A u)
      (translatedCubeSet A t) with hw
  have hscaleA : cubeScaleFactor A = (3 : ℝ) ^ n := by
    rw [hA, cubeScaleFactor_originCube, zpow_natCast]
  have hgapEq : setDisagreement (translatedCubeSet A u) (translatedCubeSet A t) =
      cubeTranslationGap A u t := rfl
  have hgapSub : cubeTranslationGap A u t ⊆
      translatedCubeSet A u ∪ translatedCubeSet A t := by
    rintro x (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr hx.1
  have hunionTop : volume (translatedCubeSet A u ∪ translatedCubeSet A t) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    exact ENNReal.add_ne_top.2
      ⟨volume_translatedCubeSet_ne_top A u, volume_translatedCubeSet_ne_top A t⟩
  have hgapTop : volume (cubeTranslationGap A u t) ≠ ⊤ :=
    ne_top_of_le_ne_top hunionTop (measure_mono hgapSub)
  have hgapVol : (volume (cubeTranslationGap A u t)).toReal ≤
      2 * (d : ℝ) * (V / (3 : ℝ) ^ n) * ((3 : ℝ) ^ n) ^ d := by
    have := volume_cubeTranslationGap_toReal_le A u t hV (by rw [hscaleA]; exact hVle) huv
    rwa [hscaleA, show cubeVolume A = ((3 : ℝ) ^ n) ^ d from cubeVolume_originCube n] at this
  have hwmem : MemLp w (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeIndicatorDifference (by positivity)
      (measurableSet_translatedCubeSet A u) (measurableSet_translatedCubeSet A t) Q _
  have hwnorm : cubeLpNorm Q (2 : ℝ≥0∞) w ≤
      (3 : ℝ) ^ d *
        Real.sqrt ((volume (cubeTranslationGap A u t)).toReal / cubeVolume Q) := by
    have := cubeLpNorm_two_cubeIndicatorDifference_le Q (c := (3 : ℝ) ^ d)
      (by positivity) (measurableSet_translatedCubeSet A u)
      (measurableSet_translatedCubeSet A t) (by rw [hgapEq]; exact hgapTop)
    rwa [hgapEq] at this
  have hQvol : cubeVolume Q = ((3 : ℝ) ^ (n + 1)) ^ d := cubeVolume_originCube (n + 1)
  have hkey := depthAverage_le_of_forall_oscillation_le Q j hwmem hosc
  refine hkey.trans ?_
  have hsqrtnn : 0 ≤ Real.sqrt
      ((volume (cubeTranslationGap A u t)).toReal / cubeVolume Q) := Real.sqrt_nonneg _
  have hnorm_nonneg : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) w := cubeLpNorm_nonneg Q _ w
  have hsq : (cubeLpNorm Q (2 : ℝ≥0∞) w) ^ 2 ≤
      ((3 : ℝ) ^ d) ^ 2 *
        ((volume (cubeTranslationGap A u t)).toReal / cubeVolume Q) := by
    have hpow := pow_le_pow_left₀ hnorm_nonneg hwnorm 2
    refine hpow.trans (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt]
    exact div_nonneg ENNReal.toReal_nonneg (cubeVolume_nonneg Q)
  have hQpos : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  have hdiv : (volume (cubeTranslationGap A u t)).toReal / cubeVolume Q ≤
      2 * (d : ℝ) * (V / (3 : ℝ) ^ n) * (((3 : ℝ) ^ n) ^ d / cubeVolume Q) := by
    rw [div_le_iff₀ hQpos]
    have hrew : 2 * (d : ℝ) * (V / (3 : ℝ) ^ n) *
        (((3 : ℝ) ^ n) ^ d / cubeVolume Q) * cubeVolume Q =
        2 * (d : ℝ) * (V / (3 : ℝ) ^ n) * (((3 : ℝ) ^ n) ^ d) := by
      field_simp
    rw [hrew]
    exact hgapVol
  have hratio : ((3 : ℝ) ^ n) ^ d / cubeVolume Q = ((3 : ℝ) ^ d)⁻¹ := by
    rw [hQvol]
    rw [pow_succ, mul_pow]
    field_simp
  calc
    4 * (cubeLpNorm Q (2 : ℝ≥0∞) w) ^ 2
        ≤ 4 * (((3 : ℝ) ^ d) ^ 2 *
            ((volume (cubeTranslationGap A u t)).toReal / cubeVolume Q)) := by
          have h4 : (0 : ℝ) ≤ 4 := by norm_num
          exact mul_le_mul_of_nonneg_left hsq h4
    _ ≤ 4 * (((3 : ℝ) ^ d) ^ 2 *
            (2 * (d : ℝ) * (V / (3 : ℝ) ^ n) * (((3 : ℝ) ^ n) ^ d / cubeVolume Q))) := by
          have hpos : (0 : ℝ) ≤ 4 * ((3 : ℝ) ^ d) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hdiv hpos
          calc
            4 * (((3 : ℝ) ^ d) ^ 2 *
                ((volume (cubeTranslationGap A u t)).toReal / cubeVolume Q))
                = 4 * ((3 : ℝ) ^ d) ^ 2 *
                  ((volume (cubeTranslationGap A u t)).toReal / cubeVolume Q) := by ring
            _ ≤ 4 * ((3 : ℝ) ^ d) ^ 2 *
                  (2 * (d : ℝ) * (V / (3 : ℝ) ^ n) *
                    (((3 : ℝ) ^ n) ^ d / cubeVolume Q)) := this
            _ = 4 * (((3 : ℝ) ^ d) ^ 2 *
                  (2 * (d : ℝ) * (V / (3 : ℝ) ^ n) *
                    (((3 : ℝ) ^ n) ^ d / cubeVolume Q))) := by ring
    _ = 8 * (d : ℝ) * (3 : ℝ) ^ d * (V / (3 : ℝ) ^ n) := by
          rw [hratio]
          have h3 : ((3 : ℝ) ^ d) ≠ 0 := by positivity
          field_simp
          ring

/-! ## The crude and the adapted depth estimate -/

/-- Every depth average of the displaced-cube test is controlled by the relative
displacement. -/
theorem cubeTranslationTest_depthAverage_le_displacement (d n : ℕ) (t : Vec d)
    {W : ℝ} (hW : 0 ≤ W) (hWle : W ≤ (3 : ℝ) ^ n) (htW : ∀ i, |t i| ≤ W) (j : ℕ) :
    cubeBesovDepthAverage (originCube d ((n + 1 : ℕ) : ℤ)) (2 : ℝ≥0∞)
        (cubeTranslationTest d n t) j ≤
      8 * (d : ℝ) * (3 : ℝ) ^ d * (W / (3 : ℝ) ^ n) := by
  refine depthAverage_translationTest_le d n t j (u := 0) hW hWle
    (fun i => by simpa using htW i) ?_
  intro R _hR
  have hzero : cubeIndicatorDifference ((3 : ℝ) ^ d)
      (translatedCubeSet (originCube d (n : ℤ)) 0)
      (translatedCubeSet (originCube d (n : ℤ)) t) = cubeTranslationTest d n t := by
    rw [translatedCubeSet_zero, cubeTranslationTest]
  rw [hzero]
  exact cubeBesovOscillation_two_le_two_mul_cubeLpNorm R
    (memLp_cubeTranslationTest d n t R (2 : ℝ≥0∞))

/-- Beyond the depth of the cube itself the depth averages of the displaced-cube
test decay geometrically: the test is close to one whose displacement is adapted
to the triadic grid at that depth, and an adapted test has no oscillation
there. -/
theorem cubeTranslationTest_depthAverage_le_depth (d n : ℕ) (t : Vec d) (j : ℕ)
    (hj : 1 ≤ j) :
    cubeBesovDepthAverage (originCube d ((n + 1 : ℕ) : ℤ)) (2 : ℝ≥0∞)
        (cubeTranslationTest d n t) j ≤
      24 * (d : ℝ) * (3 : ℝ) ^ d * ((1 / 3 : ℝ)) ^ j := by
  set A : TriadicCube d := originCube d (n : ℤ) with hA
  set Q : TriadicCube d := originCube d ((n + 1 : ℕ) : ℤ) with hQ
  set rj : ℝ := (3 : ℝ) ^ (((n : ℤ) + 1) - (j : ℤ)) with hrj
  have hrjpos : 0 < rj := zpow_pos (by norm_num) _
  set u : Vec d := fun i => (⌊t i / rj⌋ : ℝ) * rj with hu
  have hclose : ∀ i, |u i - t i| ≤ rj := by
    intro i
    have hfract : t i / rj - (⌊t i / rj⌋ : ℝ) = Int.fract (t i / rj) := rfl
    have h0 : 0 ≤ Int.fract (t i / rj) := Int.fract_nonneg _
    have h1 : Int.fract (t i / rj) < 1 := Int.fract_lt_one _
    have hval : u i - t i = -(rj * Int.fract (t i / rj)) := by
      rw [hu, ← hfract]
      field_simp
      ring
    rw [hval, abs_neg, abs_of_nonneg (by positivity)]
    nlinarith only [h0, h1, hrjpos]
  have hrjle : rj ≤ (3 : ℝ) ^ n := by
    rw [hrj, show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast 3 n).symm]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hratio : rj / (3 : ℝ) ^ n = 3 * (1 / 3 : ℝ) ^ j := by
    rw [hrj, show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast 3 n).symm,
      ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    have hexp : ((n : ℤ) + 1 - (j : ℤ)) - (n : ℤ) = 1 - (j : ℤ) := by ring
    rw [hexp, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, zpow_natCast,
      one_div, inv_pow]
    ring
  have hmain := depthAverage_translationTest_le d n t j (u := u) hrjpos.le hrjle hclose ?_
  · calc
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) (cubeTranslationTest d n t) j
          ≤ 8 * (d : ℝ) * (3 : ℝ) ^ d * (rj / (3 : ℝ) ^ n) := hmain
      _ = 24 * (d : ℝ) * (3 : ℝ) ^ d * ((1 / 3 : ℝ)) ^ j := by rw [hratio]; ring
  · intro R hR
    have hRscale : R.scale = ((n : ℤ) + 1) - (j : ℤ) := by
      have hsc := scale_eq_sub_of_mem_descendantsAtDepth hR
      rw [hsc]
      show ((n + 1 : ℕ) : ℤ) - (j : ℤ) = ((n : ℤ) + 1) - (j : ℤ)
      push_cast
      ring
    have hRfac : cubeScaleFactor R = rj := by rw [cubeScaleFactor, hRscale, hrj]
    have hle : R.scale ≤ A.scale := by
      rw [hRscale, hA]
      show ((n : ℤ) + 1) - (j : ℤ) ≤ (n : ℤ)
      omega
    have hsubA : cubeSet R ⊆ cubeSet A ∨ Disjoint (cubeSet R) (cubeSet A) := by
      have h0 := cubeSet_subset_or_disjoint_translatedCubeSet (R := R) (A := A)
        (t := (0 : Vec d)) hle (fun i => ⟨0, by simp⟩)
      rwa [translatedCubeSet_zero] at h0
    have hsubU : cubeSet R ⊆ translatedCubeSet A u ∨
        Disjoint (cubeSet R) (translatedCubeSet A u) :=
      cubeSet_subset_or_disjoint_translatedCubeSet (R := R) (A := A) (t := u) hle
        (fun i => ⟨⌊t i / rj⌋, by rw [hRfac, hu]⟩)
    obtain ⟨gamma, hgamma⟩ :=
      exists_const_on_cubeSet_of_subset_or_disjoint (c := (3 : ℝ) ^ d) hsubA hsubU
    have hsub : cubeBesovOscillation R (2 : ℝ≥0∞)
        (fun x => cubeTranslationTest d n t x - gamma) =
        cubeBesovOscillation R (2 : ℝ≥0∞) (cubeTranslationTest d n t) := by
      rw [cubeBesovOscillation, cubeBesovOscillation,
        cubeFluctuation_sub_const_of_memLp_two R
          (memLp_cubeTranslationTest d n t R (2 : ℝ≥0∞)) gamma]
    have hcongr : cubeBesovOscillation R (2 : ℝ≥0∞)
        (fun x => cubeTranslationTest d n t x - gamma) =
        cubeBesovOscillation R (2 : ℝ≥0∞)
          (cubeIndicatorDifference ((3 : ℝ) ^ d) (translatedCubeSet A u)
            (translatedCubeSet A t)) := by
      refine cubeBesovOscillation_congr_on_cubeSet R ?_
      intro x hx
      rw [← hgamma x hx]
      simp only [cubeTranslationTest, cubeIndicatorDifference]
      ring
    rw [← hsub, hcongr]
    exact cubeBesovOscillation_two_le_two_mul_cubeLpNorm R
      (memLp_cubeIndicatorDifference (by positivity)
        (measurableSet_translatedCubeSet A u) (measurableSet_translatedCubeSet A t)
        R (2 : ℝ≥0∞))

/-! ## The test has zero average and small dual test norm -/

private theorem normalizedCubeMeasure_apply_of_subset (Q : TriadicCube d)
    {S : Set (Vec d)} (hsub : S ⊆ cubeSet Q) :
    normalizedCubeMeasure Q S = ENNReal.ofReal ((cubeVolume Q)⁻¹) * volume S := by
  rw [normalizedCubeMeasure, Measure.smul_apply, smul_eq_mul, cubeMeasure,
    Measure.restrict_apply' (measurableSet_cubeSet Q),
    Set.inter_eq_self_of_subset_left hsub]

theorem cubeAverage_cubeTranslationTest_eq_zero (d n : ℕ) (t : Vec d)
    (Q : TriadicCube d)
    (hsubA : cubeSet (originCube d (n : ℤ)) ⊆ cubeSet Q)
    (hsubT : translatedCubeSet (originCube d (n : ℤ)) t ⊆ cubeSet Q) :
    cubeAverage Q (cubeTranslationTest d n t) = 0 := by
  set A : TriadicCube d := originCube d (n : ℤ) with hA
  set mu : Measure (Vec d) := normalizedCubeMeasure Q with hmu
  have hi1 : Integrable ((cubeSet A).indicator (fun _ => (1 : ℝ))) mu :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_cubeSet A)
  have hi2 : Integrable ((translatedCubeSet A t).indicator (fun _ => (1 : ℝ))) mu :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_translatedCubeSet A t)
  have hval : ∀ S : Set (Vec d), MeasurableSet S →
      ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂mu = mu.real S := by
    intro S hS
    rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
  have hmeasA : mu.real (cubeSet A) = mu.real (translatedCubeSet A t) := by
    rw [hmu, Measure.real, Measure.real,
      normalizedCubeMeasure_apply_of_subset Q hsubA,
      normalizedCubeMeasure_apply_of_subset Q hsubT,
      volume_translatedCubeSet A t]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure, ← hmu]
  simp only [cubeTranslationTest, cubeIndicatorDifference]
  rw [integral_const_mul, integral_sub hi1 hi2, hval _ (measurableSet_cubeSet A),
    hval _ (measurableSet_translatedCubeSet A t), hmeasA, sub_self, mul_zero]

/-- The dual test norm of the displaced-cube test is bounded by the sum over
depths of the weighted square roots of its depth averages. -/
theorem cubeTranslationTest_dualTestNorm_le (d n : ℕ) (t : Vec d) (s : ℝ)
    (Q : TriadicCube d) (M : ℕ)
    (hsubA : cubeSet (originCube d (n : ℤ)) ⊆ cubeSet Q)
    (hsubT : translatedCubeSet (originCube d (n : ℤ)) t ⊆ cubeSet Q) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M (cubeTranslationTest d n t) ≤
      ∑ j ∈ Finset.range (M + 1),
        cubeBesovDepthWeight Q s j *
          Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞)
            (cubeTranslationTest d n t) j) := by
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hne : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by rw [hconj]; norm_num
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M _ hne,
    hconj, cubeBesovPartialNorm,
    cubeAverage_cubeTranslationTest_eq_zero d n t Q hsubA hsubT]
  simp only [norm_zero, mul_zero, add_zero]
  rw [cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq]
  refine (sqrt_sum_sq_le_sum (Finset.range (M + 1)) _
    (fun j _ => cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) _ j)).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [cubeBesovDepthSeminorm, show ((2 : ℝ≥0∞).toReal) = 2 by norm_num,
    ← Real.sqrt_eq_rpow]

/-! ## Containment in the parent cube -/

theorem cubeSet_originCube_subset_succ (d n : ℕ) :
    cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d ((n + 1 : ℕ) : ℤ)) := by
  intro x hx
  rw [mem_cubeSet_originCube_iff] at hx ⊢
  intro i
  have hxi := hx i
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  have hsucc : (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) = 3 * (3 : ℝ) ^ (n : ℤ) := by
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  rw [hsucc]
  constructor
  · linarith only [hxi.1, hpos]
  · linarith only [hxi.2, hpos]

theorem translatedCubeSet_originCube_subset_succ (d n : ℕ) (t : Vec d) {W : ℝ}
    (hWle : W ≤ (3 : ℝ) ^ n) (htW : ∀ i, |t i| ≤ W) :
    translatedCubeSet (originCube d (n : ℤ)) t ⊆
      cubeSet (originCube d ((n + 1 : ℕ) : ℤ)) := by
  intro x hx
  have hxi := mem_translatedCubeSet_iff.mp hx
  rw [mem_cubeSet_originCube_iff]
  intro i
  have hx' := hxi i
  have hti : |t i| ≤ (3 : ℝ) ^ n := (htW i).trans hWle
  have htlo : -((3 : ℝ) ^ n) ≤ t i := by
    have := neg_abs_le (t i); linarith only [this, hti]
  have hthi : t i ≤ (3 : ℝ) ^ n := (le_abs_self (t i)).trans hti
  have hn : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := zpow_natCast 3 n
  have hsucc : (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) = 3 * (3 : ℝ) ^ n := by
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, hn]
    ring
  rw [hsucc]
  have hidx : ((originCube d (n : ℤ)).index i : ℝ) = 0 := by
    rw [originCube]; norm_num
  rw [hidx, cubeScaleFactor_originCube, hn] at hx'
  constructor
  · linarith only [hx'.1, htlo]
  · linarith only [hx'.2, hthi]

/-! ## The explicit bound -/

private theorem cubeBesovDepthWeight_eq_scaleWeight_mul (Q : TriadicCube d)
    (s : ℝ) (j : ℕ) :
    cubeBesovDepthWeight Q s j = cubeBesovScaleWeight s Q * ((3 : ℝ) ^ s) ^ j := by
  have hL : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  have hpow : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [cubeBesovDepthWeight, cubeBesovScaleWeight, div_eq_mul_inv,
    Real.mul_rpow hL.le (by positivity), Real.inv_rpow (by positivity)]
  congr 1
  rw [Real.rpow_neg hpow.le, inv_inv,
    ← Real.rpow_natCast (3 : ℝ) j, ← Real.rpow_natCast ((3 : ℝ) ^ s) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf

private theorem geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m : ℕ) : ∑ k ∈ Finset.range m, r ^ k ≤ (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  have hpos : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hrm : (0 : ℝ) ≤ r ^ m := pow_nonneg hr0 m
  have hd1 : r - 1 ≠ 0 := by
    intro h
    exact hne (by linarith only [h])
  have heq : (r ^ m - 1) / (r - 1) = (1 - r ^ m) / (1 - r) := by
    rw [div_eq_div_iff hd1 (ne_of_gt hpos)]
    ring
  rw [geom_sum_eq hne, heq, inv_eq_one_div]
  gcongr
  linarith only [hrm]

/-- The explicit bound on the dual test norm of the displaced-cube test: a term
proportional to the square root of the relative displacement, and a geometric
tail in the depth at which the two are separated. -/
@[expose]
noncomputable def cubeTranslationTestBound (d n : ℕ) (s W : ℝ) (J : ℕ) : ℝ :=
  Real.sqrt (8 * (d : ℝ) * (3 : ℝ) ^ d * (W / (3 : ℝ) ^ n)) *
      (∑ j ∈ Finset.range J, ((3 : ℝ) ^ s) ^ j) +
    Real.sqrt (24 * (d : ℝ) * (3 : ℝ) ^ d) *
      (((3 : ℝ) ^ (s - 1 / 2)) ^ J / (1 - (3 : ℝ) ^ (s - 1 / 2)))

private theorem sqrt_pow_third (j : ℕ) :
    Real.sqrt ((1 / 3 : ℝ) ^ j) = (Real.sqrt (1 / 3)) ^ j := by
  rw [show ((1 / 3 : ℝ) ^ j) = ((Real.sqrt (1 / 3)) ^ j) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)],
    Real.sqrt_sq (by positivity)]

private theorem rpow_mul_sqrt_third {s : ℝ} :
    (3 : ℝ) ^ s * Real.sqrt (1 / 3) = (3 : ℝ) ^ (s - 1 / 2) := by
  have hsqrt : Real.sqrt (1 / 3 : ℝ) = (3 : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hsqrt, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), sub_eq_add_neg]

theorem cubeTranslationTestBound_pos (d : ℕ) [NeZero d] (n : ℕ) {s W : ℝ}
    (hs2 : s < 1 / 2) (J : ℕ) :
    0 < cubeTranslationTestBound d n s W J := by
  have hd : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast this
  have hrho0 : (0 : ℝ) < (3 : ℝ) ^ (s - 1 / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrho1 : (3 : ℝ) ^ (s - 1 / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs2])
  have hfirst : 0 ≤ Real.sqrt (8 * (d : ℝ) * (3 : ℝ) ^ d * (W / (3 : ℝ) ^ n)) *
      (∑ j ∈ Finset.range J, ((3 : ℝ) ^ s) ^ j) := by
    refine mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
    positivity
  have hsecond : 0 < Real.sqrt (24 * (d : ℝ) * (3 : ℝ) ^ d) *
      (((3 : ℝ) ^ (s - 1 / 2)) ^ J / (1 - (3 : ℝ) ^ (s - 1 / 2))) := by
    have hnum : (0 : ℝ) < ((3 : ℝ) ^ (s - 1 / 2)) ^ J := by positivity
    have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (s - 1 / 2) := by linarith only [hrho1]
    have hsqrt : 0 < Real.sqrt (24 * (d : ℝ) * (3 : ℝ) ^ d) := by
      refine Real.sqrt_pos.2 ?_
      positivity
    positivity
  rw [cubeTranslationTestBound]
  linarith only [hfirst, hsecond]

/-- The dual test norm of the displaced-cube test is at most the cube's scale
weight times the explicit bound. -/
theorem cubeTranslationTest_dualTestNorm_le_bound (d : ℕ) [NeZero d] (n : ℕ)
    (t : Vec d) {s : ℝ} (hs2 : s < 1 / 2) {W : ℝ} (hW : 0 ≤ W)
    (hWle : W ≤ (3 : ℝ) ^ n) (htW : ∀ i, |t i| ≤ W) {J : ℕ} (hJ : 1 ≤ J) (M : ℕ) :
    cubeBesovDualTestNorm (originCube d ((n + 1 : ℕ) : ℤ)) s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M
        (cubeTranslationTest d n t) ≤
      cubeBesovScaleWeight s (originCube d ((n + 1 : ℕ) : ℤ)) *
        cubeTranslationTestBound d n s W J := by
  set Q : TriadicCube d := originCube d ((n + 1 : ℕ) : ℤ) with hQ
  set g : Vec d → ℝ := cubeTranslationTest d n t with hg
  set w : ℝ := cubeBesovScaleWeight s Q with hwdef
  set a : ℝ := (3 : ℝ) ^ s with hadef
  set rho : ℝ := (3 : ℝ) ^ (s - 1 / 2) with hrhodef
  set cW : ℝ := Real.sqrt (8 * (d : ℝ) * (3 : ℝ) ^ d * (W / (3 : ℝ) ^ n)) with hcWdef
  set cD : ℝ := Real.sqrt (24 * (d : ℝ) * (3 : ℝ) ^ d) with hcDdef
  have hwpos : 0 < w := by
    rw [hwdef, cubeBesovScaleWeight]
    exact Real.rpow_pos_of_pos (zpow_pos (by norm_num) _) _
  have hapos : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hrho0 : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
  have hrho1 : rho < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs2])
  have hstart := cubeTranslationTest_dualTestNorm_le d n t s Q M
    (cubeSet_originCube_subset_succ d n)
    (translatedCubeSet_originCube_subset_succ d n t hWle htW)
  refine hstart.trans ?_
  have hterm : ∀ j ∈ Finset.range (M + 1),
      cubeBesovDepthWeight Q s j *
          Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j) ≤
        w * (if j < J then cW * a ^ j else cD * rho ^ j) := by
    intro j _hj
    rw [cubeBesovDepthWeight_eq_scaleWeight_mul Q s j, ← hwdef, ← hadef]
    by_cases hcase : j < J
    · rw [ite_eq_left hcase]
      have hd := cubeTranslationTest_depthAverage_le_displacement d n t hW hWle htW j
      have hsqrt : Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j) ≤ cW := by
        rw [hcWdef]
        exact Real.sqrt_le_sqrt (by
          simpa only [hQ, hg, mul_div_assoc] using hd)
      have hnn : 0 ≤ w * a ^ j := by positivity
      calc w * a ^ j * Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j)
          ≤ w * a ^ j * cW := by
            exact mul_le_mul_of_nonneg_left hsqrt hnn
        _ = w * (cW * a ^ j) := by ring
    · rw [ite_eq_right hcase]
      have hj1 : 1 ≤ j := by omega
      have hd := cubeTranslationTest_depthAverage_le_depth d n t j hj1
      have hsqrt : Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j) ≤
          cD * (Real.sqrt (1 / 3 : ℝ)) ^ j := by
        have hstep : Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j) ≤
            Real.sqrt (24 * (d : ℝ) * (3 : ℝ) ^ d * ((1 / 3 : ℝ)) ^ j) :=
          Real.sqrt_le_sqrt (by simpa only [hQ, hg] using hd)
        refine hstep.trans (le_of_eq ?_)
        rw [Real.sqrt_mul (by positivity), sqrt_pow_third, hcDdef]
      have hnn : 0 ≤ w * a ^ j := by positivity
      have hmul : a ^ j * (Real.sqrt (1 / 3 : ℝ)) ^ j = rho ^ j := by
        rw [← mul_pow, hadef, hrhodef, rpow_mul_sqrt_third]
      calc w * a ^ j * Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) g j)
          ≤ w * a ^ j * (cD * (Real.sqrt (1 / 3 : ℝ)) ^ j) :=
            mul_le_mul_of_nonneg_left hsqrt hnn
        _ = w * (cD * (a ^ j * (Real.sqrt (1 / 3 : ℝ)) ^ j)) := by ring
        _ = w * (cD * rho ^ j) := by rw [hmul]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hwpos.le
  rw [Finset.sum_ite]
  have hcWnn : 0 ≤ cW := Real.sqrt_nonneg _
  have hcDnn : 0 ≤ cD := Real.sqrt_nonneg _
  have hfirst : ∑ j ∈ (Finset.range (M + 1)).filter (fun j => j < J), cW * a ^ j ≤
      cW * ∑ j ∈ Finset.range J, a ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
    intro j hj
    exact Finset.mem_range.2 (Finset.mem_filter.mp hj).2
  have hIco : (Finset.range (M + 1)).filter (fun j => ¬ j < J) =
      Finset.Ico J (M + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]
    omega
  have hsecond : ∑ j ∈ (Finset.range (M + 1)).filter (fun j => ¬ j < J),
      cD * rho ^ j ≤ cD * (rho ^ J / (1 - rho)) := by
    rw [hIco, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hcDnn
    rw [Finset.sum_Ico_eq_sum_range]
    have hpow : ∀ k : ℕ, rho ^ (J + k) = rho ^ J * rho ^ k := fun k => pow_add rho J k
    calc ∑ k ∈ Finset.range (M + 1 - J), rho ^ (J + k)
        = rho ^ J * ∑ k ∈ Finset.range (M + 1 - J), rho ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => hpow k
      _ ≤ rho ^ J * (1 - rho)⁻¹ := by
          refine mul_le_mul_of_nonneg_left
            (geom_sum_le_inv_one_sub hrho0.le hrho1 _) (by positivity)
      _ = rho ^ J / (1 - rho) := by rw [div_eq_mul_inv]
  rw [cubeTranslationTestBound, ← hcWdef, ← hcDdef, ← hadef, ← hrhodef]
  linarith only [hfirst, hsecond]

end

end HighContrast
end HCPolySupport

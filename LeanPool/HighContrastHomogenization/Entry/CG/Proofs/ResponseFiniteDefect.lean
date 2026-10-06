/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Definitions
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientField
public import LeanPool.HighContrastHomogenization.Support.PDE.Harmonic
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# High-contrast homogenization: Entry.CG.Proofs.ResponseFiniteDefect

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite CG response defect

For a finite pairwise disjoint family of open pieces `U i` of an open set `W` of finite volume,
the response of a locally elliptic coefficient field over `W` is at most the volume-weighted sum
of the responses over the pieces, plus the relative volume of the uncovered remainder
`W \ ⋃ i, U i` times the plain pointwise upper bound
`lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)` on the response integrand. This finite
subadditivity of the response over a partition, with its uncovered-volume defect, is the
partition input to the coarse block comparisons of `p.successful.short.bridge` and to the
parent--child recurrence `p.fixed.geometry.parent.child.recurrence`.
-/

namespace HCPolySupport.HighContrast.CG

open MeasureTheory
open scoped BigOperators

private theorem volume_piece_ne_top_of_subset {d : ℕ} {W V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)] (hsub : V ⊆ W) :
    volume V ≠ ⊤ := by
  have hW : volume W ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_ne_top (volumeMeasureOn W) Set.univ)
  exact MeasureTheory.measure_ne_top_of_subset hsub hW

private theorem measurable_iUnion_finset {d : ℕ} {ι : Type*}
    (F : Finset ι) {U : ι → Set (Vec d)}
    (hmeas : ∀ i ∈ F, MeasurableSet (U i)) :
    MeasurableSet (⋃ i ∈ F, U i) := by
  exact Finset.measurableSet_biUnion F hmeas

private theorem iUnion_finset_subset {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    (hsub : ∀ i ∈ F, U i ⊆ W) :
    (⋃ i ∈ F, U i) ⊆ W := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hiF, hxU⟩
  exact hsub i hiF hxU

private theorem setIntegral_eq_sum_add_remainder_private {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    (hmeas : ∀ i ∈ F, MeasurableSet (U i))
    (hsub : ∀ i ∈ F, U i ⊆ W) (hdisj : (F : Set ι).PairwiseDisjoint U)
    {f : Vec d → ℝ} (hf : IntegrableOn f W) :
    (∫ x in W, f x) = (∑ i ∈ F, ∫ x in U i, f x) +
      ∫ x in W \ ⋃ i ∈ F, U i, f x := by
  classical
  let S : Set (Vec d) := ⋃ i ∈ F, U i
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact measurable_iUnion_finset F hmeas
  have hSsub : S ⊆ W := by
    dsimp [S]
    exact iUnion_finset_subset F hsub
  have hIntPieces : ∀ i ∈ F, IntegrableOn f (U i) := by
    intro i hi
    exact hf.mono_set (hsub i hi)
  have hSIntegral :
      (∫ x in S, f x) = ∑ i ∈ F, ∫ x in U i, f x := by
    dsimp [S]
    exact MeasureTheory.integral_biUnion_finset F hmeas hdisj hIntPieces
  have hdiff := MeasureTheory.setIntegral_sdiff (μ := volume) hSmeas hf hSsub
  calc
    (∫ x in W, f x)
        = (∫ x in S, f x) + ∫ x in W \ S, f x := by
          rw [hdiff]
          abel
    _ = (∑ i ∈ F, ∫ x in U i, f x) + ∫ x in W \ S, f x := by
          rw [hSIntegral]

private theorem scalarResponseIntegrand_eqOn_restrict {d : ℕ} {W V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)]
    (hWopen : IsOpen W) (hVopen : IsOpen V) (hsub : V ⊆ W)
    {a : CoeffField d} {lam Lam : ℝ} (hEllV : IsEllipticFieldOn lam Lam V a)
    (p q : Vec d) (u : AHarmonicFunction a W) :
    Set.EqOn (scalarResponseIntegrand W a p q u)
      (scalarResponseIntegrand V a p q
        (u.restrictOfIsEllipticFieldOn hWopen hVopen hsub hEllV)) V := by
  intro x _hx
  simp [scalarResponseIntegrand, H1Function.restrict]

theorem responseCompetitor_piece_le {d : ℕ} {W V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hVopen : IsOpen V) (hsub : V ⊆ W)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a)
    (p q : Vec d) (u : AHarmonicFunction a W) :
    (∫ x in V, scalarResponseIntegrand W a p q u x) ≤
      (volume V).toReal * ResponseJ V p q a := by
  classical
  have hVfin : volume V ≠ ⊤ :=
    volume_piece_ne_top_of_subset (W := W) (V := V) hsub
  by_cases hVvol : (volume V).toReal = 0
  · have hVnull : volume V = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (volume V)).mp hVvol with h | h
      · exact h
      · exact (hVfin h).elim
    rw [MeasureTheory.setIntegral_measure_zero
      (fun x => scalarResponseIntegrand W a p q u x) hVnull]
    simp [hVvol]
  · let : IsFiniteMeasure (volumeMeasureOn V) :=
      ⟨by simpa [volumeMeasureOn] using (lt_top_iff_ne_top.mpr hVfin)⟩
    have hEllV : IsEllipticFieldOn lam Lam V a :=
      hEll.mono hVopen.measurableSet hsub
    let uV : AHarmonicFunction a V :=
      u.restrictOfIsEllipticFieldOn hWopen hVopen hsub hEllV
    have hcongr :
        (∫ x in V, scalarResponseIntegrand W a p q u x) =
          ∫ x in V, scalarResponseIntegrand V a p q uV x := by
      refine MeasureTheory.setIntegral_congr_fun hVopen.measurableSet ?_
      intro x hx
      exact scalarResponseIntegrand_eqOn_restrict hWopen hVopen hsub hEllV p q u hx
    have hmem :
        volumeAverage V (scalarResponseIntegrand V a p q uV) ≤ ResponseJ V p q a :=
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hEllV hVvol p q
        (responseJValueSet_mem V p q a uV)
    have hint_eq :
        (∫ x in V, scalarResponseIntegrand V a p q uV x) =
          (volume V).toReal * volumeAverage V (scalarResponseIntegrand V a p q uV) := by
      unfold volumeAverage
      field_simp [hVvol]
    calc
      (∫ x in V, scalarResponseIntegrand W a p q u x)
          = ∫ x in V, scalarResponseIntegrand V a p q uV x := hcongr
      _ = (volume V).toReal * volumeAverage V (scalarResponseIntegrand V a p q uV) := hint_eq
      _ ≤ (volume V).toReal * ResponseJ V p q a :=
          mul_le_mul_of_nonneg_left hmem ENNReal.toReal_nonneg

theorem responseCompetitor_remainder_le {d : ℕ} {W R : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hR : MeasurableSet R) (hsub : R ⊆ W)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a)
    (p q : Vec d) (u : AHarmonicFunction a W) :
    (∫ x in R, scalarResponseIntegrand W a p q u x) ≤
      (volume R).toReal * (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) := by
  have hRfin : volume R ≠ ⊤ :=
    volume_piece_ne_top_of_subset (W := W) (V := R) hsub
  let : IsFiniteMeasure (volumeMeasureOn R) :=
    ⟨by simpa [volumeMeasureOn] using (lt_top_iff_ne_top.mpr hRfin)⟩
  have hfW : IntegrableOn (scalarResponseIntegrand W a p q u) W :=
    scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
  have hfR : IntegrableOn (scalarResponseIntegrand W a p q u) R :=
    hfW.mono_set hsub
  have hconst :
      IntegrableOn
        (fun _ : Vec d => lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) R :=
    integrable_const _
  calc
    (∫ x in R, scalarResponseIntegrand W a p q u x)
        ≤ ∫ _x in R, lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q) :=
          MeasureTheory.setIntegral_mono_on (μ := volume) (f := scalarResponseIntegrand W a p q u)
            (g := fun _ : Vec d => lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q))
            hfR hconst hR
            (fun x hx => scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn
              hEll p q u x (hsub hx))
    _ = (volume R).toReal * (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) := by
          rw [MeasureTheory.setIntegral_const, Measure.real, smul_eq_mul]

theorem responseCompetitor_finite_defect {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hWvol : (volume W).toReal ≠ 0)
    (hopen : ∀ i ∈ F, IsOpen (U i)) (hsub : ∀ i ∈ F, U i ⊆ W)
    (hdisj : (F : Set ι).PairwiseDisjoint U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a)
    (p q : Vec d) (u : AHarmonicFunction a W) :
    volumeAverage W (scalarResponseIntegrand W a p q u) ≤
      ∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a +
        (volume (W \ ⋃ i ∈ F, U i)).toReal / (volume W).toReal *
          (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) := by
  classical
  let f : Vec d → ℝ := scalarResponseIntegrand W a p q u
  let C : ℝ := lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)
  let R : Set (Vec d) := W \ ⋃ i ∈ F, U i
  have hWmeas : MeasurableSet W := hWopen.measurableSet
  have hmeas : ∀ i ∈ F, MeasurableSet (U i) :=
    fun i hi => (hopen i hi).measurableSet
  have hfW : IntegrableOn f W :=
    scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
  have hsplit :
      (∫ x in W, f x) = (∑ i ∈ F, ∫ x in U i, f x) + ∫ x in R, f x := by
    dsimp [R, f]
    exact setIntegral_eq_sum_add_remainder_private F hmeas hsub hdisj hfW
  have hpieces :
      ∑ i ∈ F, (∫ x in U i, f x) ≤
        ∑ i ∈ F, (volume (U i)).toReal * ResponseJ (U i) p q a := by
    refine Finset.sum_le_sum ?_
    intro i hi
    dsimp [f]
    exact responseCompetitor_piece_le hWopen (hopen i hi) (hsub i hi) hEll p q u
  have hRmeas : MeasurableSet R := by
    dsimp [R]
    exact hWmeas.diff (measurable_iUnion_finset F hmeas)
  have hRsub : R ⊆ W := by
    intro x hx
    exact hx.1
  have hrem :
      (∫ x in R, f x) ≤ (volume R).toReal * C := by
    dsimp [R, f, C]
    exact responseCompetitor_remainder_le hRmeas hRsub hEll p q u
  have hint_le :
      (∫ x in W, f x) ≤
        (∑ i ∈ F, (volume (U i)).toReal * ResponseJ (U i) p q a) +
          (volume R).toReal * C := by
    rw [hsplit]
    exact add_le_add hpieces hrem
  have hWinv_nonneg : 0 ≤ (volume W).toReal⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hint_le hWinv_nonneg
  unfold volumeAverage
  dsimp [f, C, R] at hscaled ⊢
  calc
    (volume W).toReal⁻¹ * ∫ x in W, scalarResponseIntegrand W a p q u x
        ≤ (volume W).toReal⁻¹ *
            ((∑ i ∈ F, (volume (U i)).toReal * ResponseJ (U i) p q a) +
              (volume (W \ ⋃ i ∈ F, U i)).toReal *
                (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q))) := hscaled
    _ = ∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a +
          (volume (W \ ⋃ i ∈ F, U i)).toReal / (volume W).toReal *
            (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [hWvol]
        · field_simp [hWvol]

theorem responseJ_le_sum_volumeRatio_mul_responseJ_add_defect_of_isEllipticFieldOn_provider {d : ℕ}
    {ι : Type*} (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hWvol : (volume W).toReal ≠ 0)
    (hopen : ∀ i ∈ F, IsOpen (U i)) (hsub : ∀ i ∈ F, U i ⊆ W)
    (hdisj : (F : Set ι).PairwiseDisjoint U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a) (p q : Vec d) :
    ResponseJ W p q a ≤
      ∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a +
        (volume (W \ ⋃ i ∈ F, U i)).toReal / (volume W).toReal *
          (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) := by
  unfold ResponseJ
  refine csSup_le (responseJValueSet_nonempty W p q a) ?_
  rintro m ⟨u, rfl⟩
  exact responseCompetitor_finite_defect F hWopen hWvol hopen hsub hdisj hEll p q u

end HCPolySupport.HighContrast.CG

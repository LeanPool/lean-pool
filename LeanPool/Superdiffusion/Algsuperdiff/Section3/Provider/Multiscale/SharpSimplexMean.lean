/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionKtot
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam1PerCube

/-!
# SharpSimplexMean

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}


private theorem probe_volume_openCarrier_ne_top (T : KuhnCell d) :
    volume T.openCarrier ≠ ⊤ :=
  (isBoundedDomain_openCarrier T).volume_lt_top.ne

private theorem probe_toReal_volume_openCarrier_pos (T : KuhnCell d) :
    0 < (volume T.openCarrier).toReal :=
  ENNReal.toReal_pos
    ((isOpen_openCarrier T).measure_pos volume (openCarrier_nonempty T)).ne'
    (probe_volume_openCarrier_ne_top T)

private theorem probe_integrableOn_openCarrier_entry (T : KuhnCell d) (n m : ℤ)
    (omega : ShellSeq d) (i j : Fin d) :
    IntegrableOn (fun x : Vec d => finiteShellIncrement omega n m x i j)
      T.openCarrier volume := by
  refine Integrable.mono'
    (integrableOn_openCarrier_streamIncrementLpDensity (p := 1) one_pos T n m omega)
    (continuous_finiteShellIncrement_entry omega n m i j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, streamIncrementLpDensity, Real.rpow_one]
  simpa using Book.Ch02.abs_entry_le_matrixOperatorNorm
    (finiteShellIncrement omega n m x) i j

private theorem probe_abs_apply_le_abs_volumeAverage_add_of_pointwise_oscillation
    (S : Set (Vec d)) (f : Vec d → ℝ) {x : Vec d} {B : ℝ}
    (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤)
    (hSpos : 0 < (volume S).toReal) (hf : IntegrableOn f S)
    (hOsc : ∀ y ∈ S, |f x - f y| ≤ B) :
    |f x| ≤ |volumeAverage S f| + B := by
  let : IsFiniteMeasure (volumeMeasureOn S) :=
    ⟨by simpa [volumeMeasureOn] using hSfin.lt_top⟩
  have hvol : (volume S).toReal ≠ 0 := ne_of_gt hSpos
  have hconst : IntegrableOn (fun _ : Vec d => f x) S :=
    integrableOn_const hSfin
  have hdiff : IntegrableOn (fun y => f x - f y) S := hconst.sub hf
  have hupper : volumeAverage S (fun y => f x - f y) ≤ B :=
    volumeAverage_le_of_le_on hS hdiff hvol fun y hy =>
      (le_abs_self _).trans (hOsc y hy)
  have hnegdiff : IntegrableOn (fun y => -(f x - f y)) S := hdiff.neg
  have hlower' : volumeAverage S (fun y => -(f x - f y)) ≤ B :=
    volumeAverage_le_of_le_on hS hnegdiff hvol fun y hy =>
      (neg_le_abs _).trans (hOsc y hy)
  have hlower : -B ≤ volumeAverage S (fun y => f x - f y) := by
    have hneg : volumeAverage S (fun y => -(f x - f y)) =
        -volumeAverage S (fun y => f x - f y) := by
      rw [show (fun y : Vec d => -(f x - f y)) =
          (-1 : ℝ) • (fun y => f x - f y) by funext y; simp]
      rw [volumeAverage_smul]
      ring
    rw [hneg] at hlower'
    linarith
  have habs : |volumeAverage S (fun y => f x - f y)| ≤ B :=
    abs_le.2 ⟨hlower, hupper⟩
  have hmean : volumeAverage S (fun _ : Vec d => f x) = f x :=
    volumeAverage_const hvol
  have hsplit : f x = volumeAverage S f + volumeAverage S (fun y => f x - f y) := by
    have hsub := volumeAverage_sub hconst hf
    have hsub' : volumeAverage S (fun y => f x - f y) =
        volumeAverage S (fun _ : Vec d => f x) - volumeAverage S f := by
      simpa only [Pi.sub_apply] using! hsub
    linarith [hmean, hsub']
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add_right habs _)

private theorem probe_segment_mem_openCubeSet_originCube {ell : ℤ}
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    y + t • (x - y) ∈ openCubeSet (originCube d ell) := by
  exact (convex_openCubeSet (originCube d ell)).add_smul_sub_mem hy hx ht

private theorem probe_vecNorm_le_sqrt_card_mul_norm (w : Vec d) :
    vecNorm w ≤ Real.sqrt (d : ℝ) * ‖w‖ := by
  classical
  have hsum : vecNormSq w ≤ (d : ℝ) * ‖w‖ ^ 2 := by
    have hrw : vecNormSq w = ∑ i : Fin d, (w i) ^ 2 := by
      simp [vecNormSq, vecDot, sq]
    rw [hrw]
    calc
      (∑ i : Fin d, (w i) ^ 2) ≤ ∑ _i : Fin d, ‖w‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : |w i| ≤ ‖w‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm w i
        nlinarith [abs_nonneg (w i), sq_abs (w i)]
      _ = (d : ℝ) * ‖w‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    vecNorm w = Real.sqrt (vecNormSq w) := by
      rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg w)]
    _ ≤ Real.sqrt ((d : ℝ) * ‖w‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ‖w‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg w)]

private theorem probe_abs_entry_shell_sub_le_localCubeDerivNorm_mul_vecNorm
    (j : ShellField d) (ell : ℤ) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) (i l : Fin d) :
    |j x i l - j y i l| ≤
      localCubeDerivNorm ell j * vecNorm (x - y) := by
  set f : ℝ → ℝ := fun t =>
    (matrixEntryCLM i l) (j (y + t • (x - y))) with hf
  set f' : ℝ → ℝ := fun t =>
    (matrixEntryCLM i l) ((ShellField.deriv j (y + t • (x - y))) (x - y)) with hf'
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' t) (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have hpath : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) t := by
      simpa using (hasDerivAt_id t).smul_const (x - y) |>.const_add y
    exact (((matrixEntryCLM i l).hasFDerivAt).comp_hasDerivAt t
      ((j.hasFDerivAt _).comp_hasDerivAt t hpath)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖f' t‖ ≤ localCubeDerivNorm ell j * vecNorm (x - y) := by
    intro t ht
    have hz : y + t • (x - y) ∈ openCubeSet (originCube d ell) :=
      probe_segment_mem_openCubeSet_originCube hx hy ⟨ht.1, ht.2.le⟩
    calc
      ‖f' t‖ = |(ShellField.deriv j (y + t • (x - y)) (x - y)) i l| := rfl
      _ ≤ matrixOperatorNorm
          ((ShellField.deriv j (y + t • (x - y))) (x - y)) :=
        Book.Ch02.abs_entry_le_matrixOperatorNorm _ _ _
      _ ≤ ShellField.matrixDerivativeNorm
          (ShellField.deriv j (y + t • (x - y))) * vecNorm (x - y) :=
        matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm _ _
      _ ≤ localCubeDerivNorm ell j * vecNorm (x - y) :=
        mul_le_mul_of_nonneg_right
          (matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell j hz)
          (vecNorm_nonneg _)
  have hkey := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have hf1 : f 1 = j x i l := by simp [hf]
  have hf0 : f 0 = j y i l := by simp [hf]
  rw [hf1, hf0] at hkey
  simpa only [Real.norm_eq_abs, sub_zero, mul_one] using hkey

private theorem probe_abs_entry_shell_sub_le_cubeOscGauge
    (Q : TriadicCube d) (j : ShellField d) {x y : Vec d}
    (hx : x ∈ openCubeSet Q) (hy : y ∈ openCubeSet Q) (i l : Fin d) :
    |j x i l - j y i l| ≤ Real.sqrt (d : ℝ) * cubeOscGauge Q j := by
  have hx' : x - cubeBasePoint Q ∈ openCubeSet (originCube d Q.scale) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
      mem_translateSet_iff_sub_mem, ← cubeBasePoint_eq_triadicCubeShift] at hx
    exact hx
  have hy' : y - cubeBasePoint Q ∈ openCubeSet (originCube d Q.scale) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
      mem_translateSet_iff_sub_mem, ← cubeBasePoint_eq_triadicCubeShift] at hy
    exact hy
  have hraw := probe_abs_entry_shell_sub_le_localCubeDerivNorm_mul_vecNorm
    (ShellField.translate (cubeBasePoint Q) j) Q.scale hx' hy' i l
  have hvalx : ShellField.translate (cubeBasePoint Q) j (x - cubeBasePoint Q) = j x := by
    rw [ShellField.translate_apply, sub_add_cancel]
  have hvaly : ShellField.translate (cubeBasePoint Q) j (y - cubeBasePoint Q) = j y := by
    rw [ShellField.translate_apply, sub_add_cancel]
  rw [hvalx, hvaly] at hraw
  have hdistSup : ‖(x - cubeBasePoint Q) - (y - cubeBasePoint Q)‖ ≤
      cubeScaleFactor Q := by
    have hxy := norm_sub_le_cubeScaleFactor_of_mem_cubeSet Q
      (openCubeSet_subset_cubeSet Q hx) (openCubeSet_subset_cubeSet Q hy)
    simpa [dist_eq_norm] using hxy
  have hdist : vecNorm ((x - cubeBasePoint Q) - (y - cubeBasePoint Q)) ≤
      Real.sqrt (d : ℝ) * cubeScaleFactor Q := by
    exact (probe_vecNorm_le_sqrt_card_mul_norm _).trans
      (mul_le_mul_of_nonneg_left hdistSup (Real.sqrt_nonneg _))
  have hlocal0 : 0 ≤ localCubeDerivNorm Q.scale
      (ShellField.translate (cubeBasePoint Q) j) := localCubeDerivNorm_nonneg _ _
  calc
    |j x i l - j y i l|
        ≤ localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) j) *
            vecNorm ((x - cubeBasePoint Q) - (y - cubeBasePoint Q)) := hraw
    _ ≤ localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) j) *
          (Real.sqrt (d : ℝ) * cubeScaleFactor Q) :=
      mul_le_mul_of_nonneg_left hdist hlocal0
    _ = Real.sqrt (d : ℝ) * ((3 : ℝ) ^ Q.scale *
          localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) j)) := by
      rw [cubeScaleFactor]
      ring
    _ ≤ Real.sqrt (d : ℝ) * cubeOscGauge Q j :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)

theorem probe_abs_entry_increment_le_simplexMean_add_cubeOscGauge
    (Q : TriadicCube d) (n L : ℤ) (omega : ShellSeq d) (T : KuhnCell d)
    (hTQ : T.openCarrier ⊆ openCubeSet Q) {x : Vec d} (hx : x ∈ openCubeSet Q)
    (i l : Fin d) :
    |finiteShellIncrement omega n L x i l| ≤
      |simplexIncrementValue n L omega T i l| +
        Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega n L) := by
  have hbase := probe_abs_apply_le_abs_volumeAverage_add_of_pointwise_oscillation
    T.openCarrier (fun y => finiteShellIncrement omega n L y i l)
      (x := x) (B := Real.sqrt (d : ℝ) *
        cubeOscGauge Q (shellIncrement omega n L))
      (isOpen_openCarrier T).measurableSet
      (probe_volume_openCarrier_ne_top T)
      (probe_toReal_volume_openCarrier_pos T)
      (probe_integrableOn_openCarrier_entry T n L omega i l)
      (fun y hy => by
        simpa only [shellIncrement_apply] using
          probe_abs_entry_shell_sub_le_cubeOscGauge Q
            (shellIncrement omega n L) hx (hTQ hy) i l)
  simpa [simplexIncrementValue, volumeAverageMat] using hbase

private theorem probe_matrixOperatorNorm_increment_le_simplexMean_add_cubeOscGauge
    (Q : TriadicCube d) (n L : ℤ) (omega : ShellSeq d) (T : KuhnCell d)
    (hTQ : T.openCarrier ⊆ openCubeSet Q) {x : Vec d} (hx : x ∈ openCubeSet Q) :
    matrixOperatorNorm (finiteShellIncrement omega n L x) ≤
      (d : ℝ) ^ 2 *
        (matrixOperatorNorm (simplexIncrementValue n L omega T) +
          Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega n L)) := by
  have hentry : ∀ i l : Fin d,
      |finiteShellIncrement omega n L x i l| ≤
        matrixOperatorNorm (simplexIncrementValue n L omega T) +
          Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega n L) := by
    intro i l
    exact (probe_abs_entry_increment_le_simplexMean_add_cubeOscGauge
      Q n L omega T hTQ hx i l).trans
        (add_le_add
          (Book.Ch02.abs_entry_le_matrixOperatorNorm
            (simplexIncrementValue n L omega T) i l) le_rfl)
  calc
    matrixOperatorNorm (finiteShellIncrement omega n L x)
        ≤ ∑ p : Fin d × Fin d,
            |finiteShellIncrement omega n L x p.1 p.2| :=
      matrixOperatorNorm_le_sum_univ_abs_entry _
    _ ≤ ∑ _p : Fin d × Fin d,
          (matrixOperatorNorm (simplexIncrementValue n L omega T) +
            Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega n L)) :=
      Finset.sum_le_sum fun p _ => hentry p.1 p.2
    _ = (d : ℝ) ^ 2 *
          (matrixOperatorNorm (simplexIncrementValue n L omega T) +
            Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega n L)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

private theorem probe_toReal_eLpNorm_le {f : Vec d → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ openCubeSet (originCube d 0), ‖f x‖ ≤ C) :
    (eLpNorm f ∞
      (volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal ≤ C := by
  by_cases hf : AEStronglyMeasurable f
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.toReal_top]
    exact hC
  rw [eLpNorm_exponent_top hf]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  exact eLpNormEssSup_le_of_ae_bound
    (ae_restrict_of_forall_mem
      (isOpen_openCubeSet (originCube d 0)).measurableSet hbound)

theorem probe_w1Infinity_incrementUnitCube₂_le_simplexMean_add_cubeOscGauge
    (Q : TriadicCube d) (n L : ℤ) (omega : CutoffSample d) (T : KuhnCell d)
    (hTQ : T.openCarrier ⊆ openCubeSet Q) :
    (incrementUnitCube₂ Q n L omega).w1Infinity ≤
      cubeOscGauge Q (shellIncrement omega.1 n L) +
        (d : ℝ) ^ 2 *
          (matrixOperatorNorm (simplexIncrementValue n L omega.1 T) +
            Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega.1 n L)) := by
  let G : ℝ := cubeOscGauge Q (shellIncrement omega.1 n L)
  let H : ℝ := matrixOperatorNorm (simplexIncrementValue n L omega.1 T)
  let V : ℝ := (d : ℝ) ^ 2 * (H + Real.sqrt (d : ℝ) * G)
  have hG : 0 ≤ G := cubeOscGauge_nonneg Q _
  have hH : 0 ≤ H := matrixOperatorNorm_nonneg _
  have hV : 0 ≤ V := by
    dsimp only [V]
    positivity
  rw [UnitCubeSkewW2Infinity.w1Infinity]
  refine max_le ?_ ?_
  · have hfirst :
        (eLpNorm (fun x => Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
            ((incrementUnitCube₂ Q n L omega).firstDeriv x)) ∞
          (volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal ≤
          (incrementUnitCube₂ Q n L omega).gradientW1Infinity := by
      rw [UnitCubeSkewW2Infinity.gradientW1Infinity]
      exact le_max_right _ _
    calc
      (eLpNorm (fun x => Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
            ((incrementUnitCube₂ Q n L omega).firstDeriv x)) ∞
          (volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal
          ≤ (incrementUnitCube₂ Q n L omega).gradientW1Infinity := hfirst
      _ ≤ G := gradientW1Infinity_incrementUnitCube₂_le Q n L omega
      _ ≤ G + V := le_add_of_nonneg_right hV
      _ = cubeOscGauge Q (shellIncrement omega.1 n L) +
          (d : ℝ) ^ 2 *
            (matrixOperatorNorm (simplexIncrementValue n L omega.1 T) +
              Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega.1 n L)) := rfl
  · have hvalue :
        (eLpNorm (fun y => matrixNorm
            ((incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn.1.1 y)) ∞
          (volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal ≤ V := by
      refine probe_toReal_eLpNorm_le hV ?_
      intro y hy
      have hxy := mem_openCubeSet_of_mem_unitOpenCube Q hy
      rw [Real.norm_eq_abs, abs_of_nonneg (matrixNorm_nonneg _),
        matrixNorm_eq_matrixOperatorNorm]
      change matrixOperatorNorm
          (shellIncrement omega.1 n L
            (((3 : ℝ) ^ Q.scale) • y + cubeBasePoint Q)) ≤ V
      rw [shellIncrement_apply]
      exact probe_matrixOperatorNorm_increment_le_simplexMean_add_cubeOscGauge
        Q n L omega.1 T hTQ hxy
    calc
      (eLpNorm (fun y => matrixNorm
            ((incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn.1.1 y)) ∞
          (volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal
          ≤ V := hvalue
      _ ≤ G + V := le_add_of_nonneg_left hG
      _ = cubeOscGauge Q (shellIncrement omega.1 n L) +
          (d : ℝ) ^ 2 *
            (matrixOperatorNorm (simplexIncrementValue n L omega.1 T) +
              Real.sqrt (d : ℝ) * cubeOscGauge Q (shellIncrement omega.1 n L)) := rfl

def probeSimplexW1Const (d : ℕ) : ℝ :=
  1 + (d : ℝ) ^ 2 * (1 + Real.sqrt (d : ℝ))

theorem probeSimplexW1Const_nonneg (d : ℕ) : 0 ≤ probeSimplexW1Const d := by
  rw [probeSimplexW1Const]
  positivity

theorem probe_w1Infinity_incrementUnitCube₂_sq_le_simplexMean_sq_add_cubeOscGauge_sq
    (Q : TriadicCube d) (n L : ℤ) (omega : CutoffSample d) (T : KuhnCell d)
    (hTQ : T.openCarrier ⊆ openCubeSet Q) :
    (incrementUnitCube₂ Q n L omega).w1Infinity ^ 2 ≤
      2 * probeSimplexW1Const d ^ 2 *
        (matrixOperatorNorm (simplexIncrementValue n L omega.1 T) ^ 2 +
          cubeOscGauge Q (shellIncrement omega.1 n L) ^ 2) := by
  let w : ℝ := (incrementUnitCube₂ Q n L omega).w1Infinity
  let H : ℝ := matrixOperatorNorm (simplexIncrementValue n L omega.1 T)
  let G : ℝ := cubeOscGauge Q (shellIncrement omega.1 n L)
  let a : ℝ := (d : ℝ) ^ 2
  let r : ℝ := Real.sqrt (d : ℝ)
  let C : ℝ := probeSimplexW1Const d
  have hw0 : 0 ≤ w :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.w1Infinity_nonneg _
  have hH0 : 0 ≤ H := matrixOperatorNorm_nonneg _
  have hG0 : 0 ≤ G := cubeOscGauge_nonneg Q _
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hC0 : 0 ≤ C := probeSimplexW1Const_nonneg d
  have hw : w ≤ G + a * (H + r * G) := by
    simpa only [w, H, G, a, r] using
      probe_w1Infinity_incrementUnitCube₂_le_simplexMean_add_cubeOscGauge
        Q n L omega T hTQ
  have hlin : G + a * (H + r * G) ≤ C * (H + G) := by
    have hC : C = 1 + a * (1 + r) := by rfl
    rw [hC]
    have harH : 0 ≤ (a * r) * H := mul_nonneg (mul_nonneg ha0 hr0) hH0
    have haG : 0 ≤ a * G := mul_nonneg ha0 hG0
    nlinarith
  have hwC : w ≤ C * (H + G) := hw.trans hlin
  have hHG0 : 0 ≤ H + G := add_nonneg hH0 hG0
  have hpow : w ^ 2 ≤ (C * (H + G)) ^ 2 :=
    pow_le_pow_left₀ hw0 hwC 2
  have hsumSq : (H + G) ^ 2 ≤ 2 * (H ^ 2 + G ^ 2) := by
    nlinarith [sq_nonneg (H - G)]
  calc
    w ^ 2 ≤ (C * (H + G)) ^ 2 := hpow
    _ = C ^ 2 * (H + G) ^ 2 := by ring
    _ ≤ C ^ 2 * (2 * (H ^ 2 + G ^ 2)) :=
      mul_le_mul_of_nonneg_left hsumSq (sq_nonneg C)
    _ = 2 * probeSimplexW1Const d ^ 2 *
          (matrixOperatorNorm (simplexIncrementValue n L omega.1 T) ^ 2 +
            cubeOscGauge Q (shellIncrement omega.1 n L) ^ 2) := by
      dsimp only [C, H, G]
      ring

theorem probe_w1Infinity_incrementUnitCube₂_sq_le_simplexMean_sq_add_oscThreshold_sq
    (M : ABKModel d) (Q : TriadicCube d) {L : ℤ} (hL : Q.scale ≤ L)
    {omega : CutoffSample d} (homega : omega ∉ badOsc M Q) (T : KuhnCell d)
    (hTQ : T.openCarrier ⊆ openCubeSet Q) :
    (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2 ≤
      2 * probeSimplexW1Const d ^ 2 *
        (matrixOperatorNorm (simplexIncrementValue Q.scale L omega.1 T) ^ 2 +
          oscThreshold M Q.scale ^ 2) := by
  have hbase :=
    probe_w1Infinity_incrementUnitCube₂_sq_le_simplexMean_sq_add_cubeOscGauge_sq
      Q Q.scale L omega T hTQ
  have hG0 : 0 ≤ cubeOscGauge Q (shellIncrement omega.1 Q.scale L) :=
    cubeOscGauge_nonneg Q _
  have hG : cubeOscGauge Q (shellIncrement omega.1 Q.scale L) ≤
      oscThreshold M Q.scale := by
    exact incrementOscGauge_le_oscThreshold M Q homega hL
  have hGsq : cubeOscGauge Q (shellIncrement omega.1 Q.scale L) ^ 2 ≤
      oscThreshold M Q.scale ^ 2 := pow_le_pow_left₀ hG0 hG 2
  have hcoef : 0 ≤ 2 * probeSimplexW1Const d ^ 2 := by positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hGsq) hcoef)

theorem probe_inv_cstar_mul_gamma_mul_rpow_mul_oscThreshold_sq
    (M : ABKModel d) (j : ℤ) :
    (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) * oscThreshold M j ^ 2 =
      deltaOsc d ^ 2 := by
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  calc
    (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) * oscThreshold M j ^ 2
        = (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
            ((3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) *
              oscThreshold M j ^ 2) := by ring
    _ = (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
          (deltaOsc d ^ 2 * Algsuperdiff.Section3.Disorder.cstar M / M.gamma) := by
      rw [rpow_mul_oscThreshold_sq]
    _ = deltaOsc d ^ 2 := by
      field_simp [ne_of_gt hc, ne_of_gt hg]

def probeSimplexMeanSensitivityConst (d : ℕ) : ℝ :=
  16 * bigLambdaSensitivityConst d * probeSimplexW1Const d ^ 2

theorem probeSimplexMeanSensitivityConst_nonneg (hd : 2 ≤ d) :
    0 ≤ probeSimplexMeanSensitivityConst d := by
  rw [probeSimplexMeanSensitivityConst]
  exact mul_nonneg
    (mul_nonneg (by norm_num) (bigLambdaSensitivityConst_pos hd).le)
    (sq_nonneg _)


/-! ## Weighted layer bridge for the simplex means -/

private theorem probe_sum_weight_mul_sq_le_sqrt_mul_sqrt {alpha : Type*}
    (s : Finset alpha) (w x : alpha → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    (∑ a ∈ s, w a * x a ^ 2) ≤
      Real.sqrt (∑ a ∈ s, w a) *
        Real.sqrt (∑ a ∈ s, w a * x a ^ 4) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a ^ 2)
  calc
    (∑ a ∈ s, w a * x a ^ 2) =
        ∑ a ∈ s, Real.sqrt (w a) * (Real.sqrt (w a) * x a ^ 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← mul_assoc, Real.mul_self_sqrt (hw a ha)]
    _ ≤ Real.sqrt (∑ a ∈ s, Real.sqrt (w a) ^ 2) *
          Real.sqrt (∑ a ∈ s, (Real.sqrt (w a) * x a ^ 2) ^ 2) := hcs
    _ = Real.sqrt (∑ a ∈ s, w a) *
          Real.sqrt (∑ a ∈ s, w a * x a ^ 4) := by
      congr 2 <;> apply Finset.sum_congr rfl
      · intro a ha
        exact Real.sq_sqrt (hw a ha)
      · intro a ha
        rw [mul_pow, Real.sq_sqrt (hw a ha)]
        ring

def probeLayerSimplexMeanSq (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (n1 n2 : ℤ) (omega : CutoffSample d) : ℝ :=
  ∑ Q ∈ whitneyLayer (d := d) m hn n,
    ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
      cellWeight m T *
        matrixOperatorNorm (simplexIncrementValue n1 n2 omega.1 T) ^ 2

theorem probeLayerSimplexMeanSq_le_sqrt_mass_mul_sqrt_fourth
    (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (hstep : hn n ≤ hn (n + 1) + 1) (n1 n2 : ℤ)
    (omega : CutoffSample d) :
    probeLayerSimplexMeanSq m hn n n1 n2 omega ≤
      Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn n,
        cubeMassRatio (originCube d m) Q) *
      Real.sqrt (layerSimplexFourthMass m hn n n1 n2 omega) := by
  classical
  rw [probeLayerSimplexMeanSq, layerSimplexFourthMass,
    ← Finset.sum_biUnion (pairwiseDisjoint_whitneySimplexCells m hn n),
    ← Finset.sum_biUnion (pairwiseDisjoint_whitneySimplexCells m hn n)]
  have hcs := probe_sum_weight_mul_sq_le_sqrt_mul_sqrt
    (layerCells (d := d) m hn n)
    (cellWeight m)
    (fun T => matrixOperatorNorm (simplexIncrementValue n1 n2 omega.1 T))
    (fun T _ => cellWeight_nonneg m T)
  have hmass :
      (∑ T ∈ layerCells (d := d) m hn n, cellWeight m T) =
        ∑ Q ∈ whitneyLayer (d := d) m hn n,
          cubeMassRatio (originCube d m) Q := by
    rw [layerCells,
      Finset.sum_biUnion (pairwiseDisjoint_whitneySimplexCells m hn n)]
    apply Finset.sum_congr rfl
    intro Q hQ
    exact sum_cellWeight_whitneySimplexCells_eq hstep hQ
  rw [hmass] at hcs
  simpa only [simplexIncrementFourth] using! hcs

/-! ## Refined collar carrier with the same simplex mean -/


/-! ## The actual weighted good-cell layer -/

def probeMeanGoodBaseConst (d : ℕ) : ℝ :=
  1920 * simplexCrudeConst d (1 / 4) *
    (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2)

def probeMeanGoodWaveConst (M : ABKModel d) : ℝ :=
  1920 * simplexCrudeConst d (1 / 4) *
    probeSimplexMeanSensitivityConst d *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹

theorem probeMeanGoodBaseConst_nonneg (hd : 2 ≤ d) :
    0 ≤ probeMeanGoodBaseConst d := by
  rw [probeMeanGoodBaseConst]
  have hS : 0 ≤ simplexCrudeConst d (1 / 4) :=
    simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)
  have hA : 0 ≤ probeSimplexMeanSensitivityConst d :=
    probeSimplexMeanSensitivityConst_nonneg hd
  positivity

theorem probeMeanGoodWaveConst_nonneg (hd : 2 ≤ d) (M : ABKModel d) :
    0 ≤ probeMeanGoodWaveConst M := by
  rw [probeMeanGoodWaveConst]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd))
    (inv_nonneg.2 (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le)


theorem probe_sum_collarLayer_meanSq_le_sqrt_mass_mul_sqrt_fourth
    (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (hstep : hn n ≤ hn (n + 1) + 1) (n1 n2 : ℤ)
    (omega : CutoffSample d) :
    (∑ Q ∈ collarLayer M m hn n omega,
      ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T *
          matrixOperatorNorm (simplexIncrementValue n1 n2 omega.1 T) ^ 2) ≤
      Real.sqrt (∑ Q ∈ collarLayer M m hn n omega,
        cubeMassRatio (originCube d m) Q) *
      Real.sqrt (layerSimplexFourthMass m hn n n1 n2 omega) := by
  classical
  let S := collarLayer M m hn n omega
  let F : TriadicCube d → ℝ := fun Q =>
    ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
      cellWeight m T * matrixOperatorNorm (simplexIncrementValue n1 n2 omega.1 T) ^ 4
  have hcell : ∀ Q ∈ S,
      (∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        cellWeight m T *
          matrixOperatorNorm (simplexIncrementValue n1 n2 omega.1 T) ^ 2) ≤
        Real.sqrt (cubeMassRatio (originCube d m) Q) * Real.sqrt (F Q) := by
    intro Q hQ
    have hQ' : Q ∈ whitneyLayer (d := d) m hn n :=
      collarLayer_subset M m hn n omega hQ
    have hcs := probe_sum_weight_mul_sq_le_sqrt_mul_sqrt
      (whitneySimplexCells (d := d) m hn n Q) (cellWeight m)
      (fun T => matrixOperatorNorm (simplexIncrementValue n1 n2 omega.1 T))
      (fun T _ => cellWeight_nonneg m T)
    rw [sum_cellWeight_whitneySimplexCells_eq hstep hQ'] at hcs
    simpa only [F] using hcs
  have hsum := Finset.sum_le_sum hcell
  have hcsQ := Real.sum_sqrt_mul_sqrt_le S
    (f := fun Q => cubeMassRatio (originCube d m) Q) (g := F)
    (fun Q => cubeMassRatio_nonneg _ Q)
    (fun Q => Finset.sum_nonneg fun T _ =>
      mul_nonneg (cellWeight_nonneg m T) (by positivity))
  have hfourth : (∑ Q ∈ S, F Q) ≤
      layerSimplexFourthMass m hn n n1 n2 omega := by
    rw [layerSimplexFourthMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (collarLayer_subset M m hn n omega)
      (fun Q _ _ => Finset.sum_nonneg fun T _ =>
        mul_nonneg (cellWeight_nonneg m T) (simplexIncrementFourth_nonneg _ _ _ _))
  calc
    _ ≤ ∑ Q ∈ S,
        Real.sqrt (cubeMassRatio (originCube d m) Q) * Real.sqrt (F Q) := by
      simpa only [S] using hsum
    _ ≤ Real.sqrt (∑ Q ∈ S, cubeMassRatio (originCube d m) Q) *
        Real.sqrt (∑ Q ∈ S, F Q) := hcsQ
    _ ≤ Real.sqrt (∑ Q ∈ S, cubeMassRatio (originCube d m) Q) *
        Real.sqrt (layerSimplexFourthMass m hn n n1 n2 omega) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfourth) (Real.sqrt_nonneg _)


end

end Algsuperdiff.Section3.Provider.Multiscale

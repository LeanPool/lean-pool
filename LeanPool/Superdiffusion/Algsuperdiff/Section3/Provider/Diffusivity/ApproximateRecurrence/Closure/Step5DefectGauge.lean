/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFiveDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationCorrectorRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationEighthMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationGridEighth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationFullMesh
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLinfty

/-!
# Step5DefectGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-5 cross defect at the cube's own base point, and the re-sited gauge

ABK26, `e.nablaw.oscillations` and `e.lower.bound.oscillations`, read inside
Step 5 of `l.approximate.recurrence.formula`.

`Closure.StepProducers` recorded an obstruction on the Step-5 binder `hdefect`:
the proved display sited the forcing gauge of `e.nablaw.oscillations` at
**one** window `z0`, whereas the per-cube geometric step needs the gauge on a
window containing the cube.  This module carries out the re-siting.

## What is proved

* `step5CrossDefect_le_meshOscillationCell` --- the manuscript's per-cube step,
  **proved**: for a cube `R` of scale at most `n`,
  ```
    step5CrossDefect R omega n m e u
      <= (d^2 sqrt d / 2) * ( ||u - (u)_R||_{L2bar(R)}
                              * 3^{R.scale} ||grad(k_m - k_n)||_{Linf(z_R + cu_n)} ) ,
  ```
  with `z_R = triadicCubeShift R` the cube's **own** base point.  The two steps
  are the manuscript's: the mean value inequality on `R` (through the proved
  `Provider.Stream.abs_entry_sum_sub_origin_le`, applied to the translated
  shell sequence) and Cauchy--Schwarz on `R`.  The constant
  `step5CrossDefectConst d = d^2 sqrt d / 2` is dimensional and absolute: `d^2`
  is the entrywise-`l1` comparison of the Euclidean operator norm, `sqrt d / 2`
  is the circumradius of the unit cube.
* `meshOscillationCell_eq_sqrt_cubeAverage` --- at its own scale the oscillation
  cell of `e.nablaw.oscillations` is the root cube average of the squared
  fluctuation, which is what Cauchy--Schwarz produces.
* `gridFourthMomentRoot_shellDerivNormSum_le_of_base_point` --- the grid is
  finite and the fourth-moment bound of `LocalizationOscillationTail` is uniform
  in the base point, so the **per-cube-sited** grid gauge root is dominated by
  the single-window root at a maximizing cube.
* `exists_gamma0_freshShellDirichlet_step5MeshOscillationResited_le_gamma_pow_fifteen`
  --- consequently `e.lower.bound.oscillations` holds in the re-sited shape,
  i.e. literally the `hosc` binder of
  `Closure.JunctionDischargeStepFiveDisplay.step5GaugeEndpoint_of_correctors_gauge`
  at the gauge family `fun R omega => 3^nmesh * shellDerivNormSum n (n+h)
  (triadicCubeShift R) omega`.  Nothing is weakened: the proved full-mesh
  producer is re-instantiated, not re-proved, and its own binders are carried
  verbatim.

## References

* ABK26, `e.nablaw.oscillations`; `e.lower.bound.oscillations`; Step 5.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 HCPolySupport.Book.Ch03
open MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L^1 <= L^2` on the normalized cube -/

private theorem holderConj22 : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

private theorem ofReal_two' : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  simp [ENNReal.ofReal_ofNat]

/-- Cauchy--Schwarz against the constant `1`: on a probability space the mean of
a nonnegative `L^2` function is at most the root of its second moment. -/
theorem integral_le_sqrt_integral_sq {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {f : Omega → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmem : MemLp f 2 mu) :
    ∫ x, f x ∂mu ≤ Real.sqrt (∫ x, f x ^ (2 : ℕ) ∂mu) := by
  have hf2 : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by rwa [ofReal_two']
  have hone : MemLp (fun _ : Omega => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg holderConj22
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall fun _ => zero_le_one)
    hf2 hone
  simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul] at hh
  have hnn : (0 : ℝ) ≤ ∫ x, f x ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun x => Real.rpow_nonneg (hf x) _
  have hpt : ∀ x : Omega, f x ^ (2 : ℝ) = f x ^ (2 : ℕ) := by
    intro x
    rw [← Real.rpow_natCast (f x) 2]
    norm_num
  simp only [hpt] at hh hnn
  rw [Real.sqrt_eq_rpow]
  simpa [one_div] using hh

/-! ## Transfer between the normalized cube measure and Lebesgue -/

theorem integrableOn_openCubeSet_of_integrable_normalized (R : TriadicCube d)
    {f : Vec d → ℝ} (hf : Integrable f (normalizedCubeMeasure R)) :
    IntegrableOn f (openCubeSet R) volume := by
  have hne : ENNReal.ofReal ((cubeVolume R)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos R))).ne'
  rw [normalizedCubeMeasure, cubeMeasure] at hf
  have h := (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hf
  show Integrable f (volume.restrict (openCubeSet R))
  rwa [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] at h

theorem memLp_two_coord (R : TriadicCube d) {u : Vec d → Vec d}
    (hu : MemLp u 2 (normalizedCubeMeasure R)) (j : Fin d) :
    MemLp (fun x => u x j) 2 (normalizedCubeMeasure R) := by
  refine hu.mono ((continuous_apply j).comp_aestronglyMeasurable hu.aestronglyMeasurable) ?_
  filter_upwards with x
  exact norm_le_pi_norm (u x) j

theorem ae_mem_openCubeSet_normalizedCubeMeasure (R : TriadicCube d) :
    ∀ᵐ x ∂(normalizedCubeMeasure R), x ∈ openCubeSet R := by
  have hbase : ∀ᵐ x ∂(volume.restrict (cubeSet R)), x ∈ openCubeSet R := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
    exact ae_restrict_mem (measurableSet_openCubeSet R)
  exact MeasureTheory.Measure.ae_smul_measure hbase _

/-! ## The oscillation cell as a root cube average -/

/-- **The oscillation cell of `e.nablaw.oscillations` at the cube's own scale.**
It is the root cube average of the squared fluctuation, which is exactly the
quantity Cauchy--Schwarz on the cube produces. -/
theorem meshOscillationCell_eq_sqrt_cubeAverage (R : TriadicCube d) (u : Vec d → Vec d)
    (hu : MemLp u 2 (normalizedCubeMeasure R)) :
    meshOscillationCell R.scale u R =
      Real.sqrt (cubeAverage R (fun x => vecNormSq (u x - cubeAverageVec R u))) := by
  classical
  let : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨by simp [normalizedCubeMeasure_apply_univ R]⟩
  have hwin : openCubeAtScale (triadicCubeShift R) R.scale = openCubeSet R :=
    openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have havg : volumeAverageVec (openCubeSet R) u = cubeAverageVec R u := by
    funext i
    exact volumeAverage_openCubeSet_eq_cubeAverage' R (fun x => u x i)
  have hint : ∀ k : Fin d,
      IntegrableOn (fun x => (u x k - cubeAverageVec R u k) ^ 2) (openCubeSet R) volume := by
    intro k
    refine integrableOn_openCubeSet_of_integrable_normalized R ?_
    have hk : MemLp (fun x => u x k - cubeAverageVec R u k) 2 (normalizedCubeMeasure R) :=
      (memLp_two_coord R hu k).sub (memLp_const _)
    simpa using hk.integrable_sq
  have hdev := Book.Ch01.meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub
    (V := openCubeSet R) (h := u) (c := cubeAverageVec R u) hint
  rw [meshOscillationCell, hwin]
  congr 1
  rw [show Book.Ch01.meanSquareOscillationVecOn (openCubeSet R) u
      = Book.Ch01.meanSquareDeviationVecOn (openCubeSet R) u
        (volumeAverageVec (openCubeSet R) u) from rfl, havg, hdev]
  exact volumeAverage_openCubeSet_eq_cubeAverage' R _

/-! ## The mean value step, at the cube's own base point -/

private theorem openCubeSet_originCube_mono' {s n : ℤ} (h : s ≤ n) :
    openCubeSet (originCube d s) ⊆ openCubeSet (originCube d n) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3 : (3 : ℝ) ^ s ≤ (3 : ℝ) ^ n := zpow_le_zpow_right₀ (by norm_num) h
  have hpos : (0 : ℝ) < (3 : ℝ) ^ s := zpow_pos (by norm_num) s
  exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩

/-- **The entrywise mean value inequality.**  On its own cube the fresh shell
deviates from its value at the cube's base point by at most the cube's
circumradius times the shell-derivative gauge *at that base point*. -/
theorem abs_finiteShellIncrement_entry_sub_center_le (R : TriadicCube d)
    (omega : ShellSeq d) (n m : ℤ) (hsc : R.scale ≤ n) {x : Vec d}
    (hx : x ∈ openCubeSet R) (i l : Fin d) :
    |finiteShellIncrement omega n m x i l -
        finiteShellIncrement omega n m (triadicCubeShift R) i l| ≤
      shellDerivNormSum n m (triadicCubeShift R) omega *
        (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2)) := by
  classical
  set z : Vec d := triadicCubeShift R with hz
  set G : ℝ := shellDerivNormSum n m z omega with hG
  have hG0 : 0 ≤ G := shellDerivNormSum_nonneg n m z omega
  have hy0 : x - z ∈ openCubeSet (originCube d R.scale) := by
    have hset := openCubeSet_eq_translateSet_originCube_of_triadicCube R
    rw [hset, mem_translateSet_iff_sub_mem] at hx
    exact hx
  have hy : x - z ∈ openCubeSet (originCube d n) := openCubeSet_originCube_mono' hsc hy0
  have hvec : vecNorm (x - z) ≤ Real.sqrt d * ((3 : ℝ) ^ R.scale / 2) :=
    Provider.Stream.vecNorm_le_of_mem_openCubeSet_originCube hy0
  set omega' : ShellSeq d := fun k => ShellField.translate z (omega k) with hom
  have hval : ∀ k : ℤ, (omega' k) (x - z) = (omega k) x := by
    intro k
    rw [hom]
    show (omega k) ((x - z) + z) = (omega k) x
    rw [sub_add_cancel]
  have hval0 : ∀ k : ℤ, (omega' k) 0 = (omega k) z := by
    intro k
    rw [hom]
    show (omega k) ((0 : Vec d) + z) = (omega k) z
    rw [zero_add]
  have hgauge : ∑ k ∈ Finset.Ioc n m, Provider.Stream.localCubeDerivNorm n (omega' k) = G :=
    rfl
  have hbase := Provider.Stream.abs_entry_sum_sub_origin_le omega' n m hy i l
  rw [hgauge] at hbase
  have hL : (∑ k ∈ Finset.Ioc n m, (omega' k) (x - z)) i l =
      finiteShellIncrement omega n m x i l := by
    rw [finiteShellIncrement_apply_entry, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ => congrFun (congrFun (hval k) i) l
  have hR0 : (∑ k ∈ Finset.Ioc n m, (omega' k) 0) i l =
      finiteShellIncrement omega n m z i l := by
    rw [finiteShellIncrement_apply_entry, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ => congrFun (congrFun (hval0 k) i) l
  rw [hL, hR0] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_left hvec hG0)

/-- **The operator-norm form of the mean value step.** -/
theorem matrixOperatorNorm_finiteShellIncrement_sub_center_le (R : TriadicCube d)
    (omega : ShellSeq d) (n m : ℤ) (hsc : R.scale ≤ n) {x : Vec d}
    (hx : x ∈ openCubeSet R) :
    matrixOperatorNorm (finiteShellIncrement omega n m x -
        finiteShellIncrement omega n m (triadicCubeShift R)) ≤
      (d : ℝ) ^ 2 * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2)) *
        shellDerivNormSum n m (triadicCubeShift R) omega := by
  classical
  set z : Vec d := triadicCubeShift R with hz
  set G : ℝ := shellDerivNormSum n m z omega with hG
  have hsum : ∑ i : Fin d, ∑ l : Fin d,
      |(finiteShellIncrement omega n m x - finiteShellIncrement omega n m z) i l -
        (0 : Mat d) i l| ≤
      (d : ℝ) ^ 2 * (G * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2))) := by
    calc ∑ i : Fin d, ∑ l : Fin d,
          |(finiteShellIncrement omega n m x - finiteShellIncrement omega n m z) i l -
            (0 : Mat d) i l|
        ≤ ∑ _i : Fin d, ∑ _l : Fin d, G * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => by
            rw [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
            exact abs_finiteShellIncrement_entry_sub_center_le R omega n m hsc hx i l
      _ = (d : ℝ) ^ 2 * (G * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2))) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
          ring
  have hstart := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
    (finiteShellIncrement omega n m x - finiteShellIncrement omega n m z) (0 : Mat d)
  rw [matrixOperatorNorm_zero, zero_add] at hstart
  refine hstart.trans (hsum.trans (le_of_eq ?_))
  ring

/-- The entries of a finite shell increment are continuous. -/
theorem continuous_finiteShellIncrement_entry (omega : ShellSeq d) (n m : ℤ)
    (i j : Fin d) : Continuous (fun x : Vec d => finiteShellIncrement omega n m x i j) := by
  classical
  have hfun : (fun x : Vec d => finiteShellIncrement omega n m x i j)
      = fun x : Vec d => ∑ k ∈ Finset.Ioc n m, (omega k) x i j := by
    funext x
    rw [finiteShellIncrement_apply_entry]
  rw [hfun]
  exact continuous_finsetSum _ fun k _ =>
    ((continuous_apply j).comp ((continuous_apply i).comp (omega k).1.1.continuous))

/-! ## The per-cube cross defect -/

/-- The dimensional constant of the per-cube step: the entrywise-`l1` comparison of
the Euclidean operator norm (`d^2`) times the circumradius of the unit cube
(`sqrt d / 2`). -/
def step5CrossDefectConst (d : ℕ) : ℝ := (d : ℝ) ^ 2 * Real.sqrt d / 2

theorem step5CrossDefectConst_nonneg (d : ℕ) : 0 ≤ step5CrossDefectConst d := by
  unfold step5CrossDefectConst
  positivity

private theorem integral_vecDot_matVecMul (nu : Measure (Vec d)) (e : Vec d)
    (A : Vec d → Mat d) (v : Vec d → Vec d)
    (h : ∀ i j, Integrable (fun x => A x i j * v x j) nu) :
    ∫ x, vecDot e (matVecMul (A x) (v x)) ∂nu
      = ∑ i, ∑ j, e i * ∫ x, A x i j * v x j ∂nu := by
  classical
  have hpt : (fun x : Vec d => vecDot e (matVecMul (A x) (v x)))
      = fun x : Vec d => ∑ i, ∑ j, e i * (A x i j * v x j) := by
    funext x
    show (∑ i, e i * (∑ j, A x i j * v x j)) = _
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [hpt, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (h i j).const_mul (e i)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (h i j).const_mul (e i))]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- **The per-cube step of `e.nablaw.oscillations`, proved.**

The Step-5 cross defect on a cube `R` of scale at most `n` is at most the
absolute dimensional constant times the oscillation cell of `grad w` on `R`
times the cube's side length times the shell-derivative gauge on the window
`triadicCubeShift R + cu_n` --- the window based at `R`'s **own** site.

The proof is the manuscript's: the defect equals
`fint_R e . (h(x) - h(z_R)) (u(x) - (u)_R)` (the two cross terms cancel against
the averages), the mean value inequality bounds `||h - h(z_R)||_{Linf(R)}`, and
Cauchy--Schwarz on `R` turns `fint_R |u - (u)_R|` into the oscillation cell.

only on `hsc` (the cube is at most the gauge scale), on the direction bound
`he` and on the `L^2` membership of `u` on the cube, which is the very object
the display is about. -/
theorem step5CrossDefect_le_meshOscillationCell (R : TriadicCube d) (omega : ShellSeq d)
    (n m : ℤ) (hsc : R.scale ≤ n) {e : Vec d} (he : vecNorm e ≤ 1) (u : Vec d → Vec d)
    (hu : MemLp u 2 (normalizedCubeMeasure R)) :
    step5CrossDefect R omega n m e u ≤
      step5CrossDefectConst d *
        (meshOscillationCell R.scale u R *
          ((3 : ℝ) ^ ((R.scale : ℤ) : ℝ) *
            shellDerivNormSum n m (triadicCubeShift R) omega)) := by
  classical
  let : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨by simp [normalizedCubeMeasure_apply_univ R]⟩
  set nu : Measure (Vec d) := normalizedCubeMeasure R with hnu
  set z : Vec d := triadicCubeShift R with hzdef
  set G : ℝ := shellDerivNormSum n m z omega with hGdef
  set A : Vec d → Mat d := fun x => finiteShellIncrement omega n m x with hAdef
  set C : Mat d := finiteShellIncrement omega n m z with hCdef
  set ubar : Vec d := cubeAverageVec R u with hubardef
  have hG0 : 0 ≤ G := shellDerivNormSum_nonneg n m z omega
  set Bpre : ℝ := (d : ℝ) ^ 2 * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2)) * G with hBpre
  have hBpre0 : 0 ≤ Bpre := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ R.scale := zpow_pos (by norm_num) _
    have hsq : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    rw [hBpre]
    positivity
  have hAmeas : ∀ i j : Fin d, AEStronglyMeasurable (fun x => A x i j) nu := fun i j =>
    (continuous_finiteShellIncrement_entry omega n m i j).aestronglyMeasurable
  have hbdd : ∀ i j : Fin d, ∀ᵐ x ∂nu,
      ‖A x i j‖ ≤ |C i j| + G * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2)) := by
    intro i j
    filter_upwards [ae_mem_openCubeSet_normalizedCubeMeasure R] with x hx
    have hb := abs_finiteShellIncrement_entry_sub_center_le R omega n m hsc hx i j
    have habs : |A x i j| ≤ |C i j| + |A x i j - C i j| := by
      have := abs_sub_abs_le_abs_sub (A x i j) (C i j)
      linarith [abs_nonneg (A x i j - C i j)]
    rw [Real.norm_eq_abs]
    linarith [habs, hb]
  have hAint : ∀ i j : Fin d, Integrable (fun x => A x i j) nu := by
    intro i j
    exact Integrable.mono' (integrable_const
      (|C i j| + G * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2)))) (hAmeas i j) (hbdd i j)
  have huint : ∀ j : Fin d, Integrable (fun x => u x j) nu := fun j =>
    (memLp_two_coord R hu j).integrable (by norm_num)
  have hAuint : ∀ i j : Fin d, Integrable (fun x => A x i j * u x j) nu := fun i j =>
    Integrable.bdd_mul (huint j) (hAmeas i j) (hbdd i j)
  have hbar : ∀ i j : Fin d, freshShellCubeAverage R omega n m i j = ∫ x, A x i j ∂nu := by
    intro i j
    rw [freshShellCubeAverage_apply, hnu, cubeAverage_eq_integral_normalizedCubeMeasure]
  have hubar : ∀ j : Fin d, ubar j = ∫ x, u x j ∂nu := fun j => by
    rw [hubardef, hnu]
    exact cubeAverage_eq_integral_normalizedCubeMeasure R (fun x => u x j)
  have hexp : ∀ i j : Fin d, (fun x : Vec d => (A x - C) i j * (u x - ubar) j)
      = fun x : Vec d => A x i j * u x j - ubar j * A x i j - C i j * u x j
          + C i j * ubar j := by
    intro i j
    funext x
    rw [Matrix.sub_apply, Pi.sub_apply]
    ring
  have hsubint : ∀ i j : Fin d,
      Integrable (fun x : Vec d => (A x - C) i j * (u x - ubar) j) nu := by
    intro i j
    rw [hexp i j]
    exact (((hAuint i j).sub ((hAint i j).const_mul (ubar j))).sub
      ((huint j).const_mul (C i j))).add (integrable_const _)
  have hper : ∀ i j : Fin d,
      (∫ x, (A x - C) i j * (u x - ubar) j ∂nu)
        = (∫ x, A x i j * u x j ∂nu) - (∫ x, A x i j ∂nu) * (∫ x, u x j ∂nu) := by
    intro i j
    have iAu : Integrable (fun x : Vec d => A x i j * u x j) nu := hAuint i j
    have iA : Integrable (fun x : Vec d => ubar j * A x i j) nu :=
      (hAint i j).const_mul (ubar j)
    have iu : Integrable (fun x : Vec d => C i j * u x j) nu :=
      (huint j).const_mul (C i j)
    have i1 : Integrable (fun x : Vec d => A x i j * u x j - ubar j * A x i j) nu :=
      iAu.sub iA
    have i2 : Integrable
        (fun x : Vec d => A x i j * u x j - ubar j * A x i j - C i j * u x j) nu :=
      i1.sub iu
    have ic : Integrable (fun _ : Vec d => C i j * ubar j) nu := integrable_const _
    rw [hexp i j, integral_add i2 ic, integral_sub i1 iu, integral_sub iAu iA,
      integral_const_mul, integral_const_mul, integral_const, hubar j]
    simp only [smul_eq_mul, probReal_univ, one_mul]
    ring
  have hid : step5CrossDefect R omega n m e u
      = ∫ x, vecDot e (matVecMul (A x - C) (u x - ubar)) ∂nu := by
    rw [integral_vecDot_matVecMul nu e (fun x => A x - C) (fun x => u x - ubar) hsubint]
    have hL : step5CrossDefect R omega n m e u
        = (∑ i, ∑ j, e i * ∫ x, A x i j * u x j ∂nu)
          - ∑ i, ∑ j, e i * ((∫ x, A x i j ∂nu) * (∫ x, u x j ∂nu)) := by
      rw [step5CrossDefect]
      congr 1
      · rw [hnu, cubeAverage_eq_integral_normalizedCubeMeasure]
        exact integral_vecDot_matVecMul nu e A u hAuint
      · show (∑ i, e i * (∑ j, freshShellCubeAverage R omega n m i j * ubar j)) = _
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hbar i j, hubar j]
    rw [hL, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_sub, hper i j]
  have hvnmem : MemLp (fun x => vecNorm (u x - ubar)) 2 nu :=
    memLp_vecNorm_eight_of_memLp_eight R (hu.sub (memLp_const _))
  have hvnint : Integrable (fun x => vecNorm (u x - ubar)) nu :=
    hvnmem.integrable (by norm_num)
  have hDint : Integrable (fun x => vecDot e (matVecMul (A x - C) (u x - ubar))) nu := by
    have hfun : (fun x : Vec d => vecDot e (matVecMul (A x - C) (u x - ubar)))
        = fun x : Vec d => ∑ i, ∑ j, e i * ((A x - C) i j * (u x - ubar) j) := by
      funext x
      show (∑ i, e i * (∑ j, (A x - C) i j * (u x - ubar) j)) = _
      exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    rw [hfun]
    exact integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hsubint i j).const_mul _
  have hptbd : ∀ᵐ x ∂nu, vecDot e (matVecMul (A x - C) (u x - ubar)) ≤
      Bpre * vecNorm (u x - ubar) := by
    filter_upwards [ae_mem_openCubeSet_normalizedCubeMeasure R] with x hx
    have h1 : vecDot e (matVecMul (A x - C) (u x - ubar)) ≤
        vecNorm e * vecNorm (matVecMul (A x - C) (u x - ubar)) :=
      le_trans (le_abs_self _) (abs_vecDot_le_vecNorm_mul_vecNorm _ _)
    have h2 : vecNorm (matVecMul (A x - C) (u x - ubar)) ≤
        matrixOperatorNorm (A x - C) * vecNorm (u x - ubar) :=
      vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _
    have h3 : matrixOperatorNorm (A x - C) ≤
        (d : ℝ) ^ 2 * (Real.sqrt d * ((3 : ℝ) ^ R.scale / 2)) * G :=
      matrixOperatorNorm_finiteShellIncrement_sub_center_le R omega n m hsc hx
    have hw0 : (0 : ℝ) ≤ vecNorm (u x - ubar) := vecNorm_nonneg _
    have hM0 : (0 : ℝ) ≤ vecNorm (matVecMul (A x - C) (u x - ubar)) := vecNorm_nonneg _
    calc vecDot e (matVecMul (A x - C) (u x - ubar))
        ≤ vecNorm e * vecNorm (matVecMul (A x - C) (u x - ubar)) := h1
      _ ≤ 1 * vecNorm (matVecMul (A x - C) (u x - ubar)) :=
          mul_le_mul_of_nonneg_right he hM0
      _ = vecNorm (matVecMul (A x - C) (u x - ubar)) := one_mul _
      _ ≤ matrixOperatorNorm (A x - C) * vecNorm (u x - ubar) := h2
      _ ≤ Bpre * vecNorm (u x - ubar) := mul_le_mul_of_nonneg_right h3 hw0
  have hosc : (∫ x, vecNorm (u x - ubar) ∂nu) ≤ meshOscillationCell R.scale u R := by
    have hstep := integral_le_sqrt_integral_sq nu
      (fun x => vecNorm_nonneg (u x - ubar)) hvnmem
    have hsq : ∀ x : Vec d, vecNorm (u x - ubar) ^ (2 : ℕ) = vecNormSq (u x - ubar) :=
      fun x => vecNorm_sq_eq_vecNormSq _
    simp only [hsq] at hstep
    rw [meshOscillationCell_eq_sqrt_cubeAverage R u hu, hnu,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    exact hstep
  calc step5CrossDefect R omega n m e u
      = ∫ x, vecDot e (matVecMul (A x - C) (u x - ubar)) ∂nu := hid
    _ ≤ ∫ x, Bpre * vecNorm (u x - ubar) ∂nu :=
        integral_mono_ae hDint (hvnint.const_mul _) hptbd
    _ = Bpre * ∫ x, vecNorm (u x - ubar) ∂nu := integral_const_mul _ _
    _ ≤ Bpre * meshOscillationCell R.scale u R :=
        mul_le_mul_of_nonneg_left hosc hBpre0
    _ = step5CrossDefectConst d *
          (meshOscillationCell R.scale u R *
            ((3 : ℝ) ^ ((R.scale : ℤ) : ℝ) * G)) := by
        rw [Real.rpow_intCast, hBpre, step5CrossDefectConst]
        ring

/-! ## The re-sited forcing gauge on the grid

The bound of
`LocalizationOscillationTail.integral_shellDerivNormSum_rpow_four_le` is
uniform in the base point, and the grid is finite; so the average of the
per-cube fourth moments is at most the largest one, which is realized at a
maximizing cube.  The proved full-mesh producer is quantified over the base
point, hence applies at that cube and delivers the re-sited display with **no**
loss. -/

theorem gridFourthMomentRoot_const_mul' {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (I : Finset (TriadicCube d)) {c : ℝ} (hc : 0 ≤ c)
    (F : TriadicCube d → Omega → ℝ) :
    gridFourthMomentRoot mu I (fun R omega => c * F R omega) =
      c * gridFourthMomentRoot mu I F := by
  unfold gridFourthMomentRoot
  rw [gridFourthMoment_const_mul,
    Real.mul_rpow (by positivity) (gridFourthMoment_nonneg mu I F),
    ← Real.rpow_natCast c 4, ← Real.rpow_mul hc]
  norm_num

/-- **The per-cube-sited grid gauge root is realized at one base point.**  The
grid being finite, the grid fourth-moment root of the base-point-sited forcing
gauge is at most its single-window root at a maximizing cube. -/
theorem gridFourthMomentRoot_shellDerivNormSum_le_of_base_point (M : ABKModel d)
    (lowScale highScale : ℤ) (I : Finset (TriadicCube d)) :
    ∃ z0 : Vec d,
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure I
          (fun (R : TriadicCube d) (omega : CutoffSample d) =>
            shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val) ≤
        (∫ omega : CutoffSample d,
          shellDerivNormSum lowScale highScale z0 omega.val ^ (4 : ℝ)
            ∂(cutoffSampleLaw M).toMeasure) ^ ((4 : ℝ)⁻¹) := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, ?_⟩
    have h0 : gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (∅ : Finset (TriadicCube d))
        (fun (R : TriadicCube d) (omega : CutoffSample d) =>
          shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val) = 0 := by
      unfold gridFourthMomentRoot gridFourthMoment cubeFamilyAverage
      simp
    rw [h0]
    exact Real.rpow_nonneg (integral_nonneg fun omega =>
      Real.rpow_nonneg (shellDerivNormSum_nonneg _ _ _ _) _) _
  obtain ⟨Rmax, _hRmax, hmax⟩ := I.exists_max_image
    (fun R => ∫ omega : CutoffSample d,
      shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val ^ (4 : ℝ)
        ∂(cutoffSampleLaw M).toMeasure) hne
  refine ⟨triadicCubeShift Rmax, ?_⟩
  refine Real.rpow_le_rpow (gridFourthMoment_nonneg _ _ _) ?_ (by norm_num)
  exact gridFourthMoment_le_of_forall_le _ I _
    (integral_nonneg fun omega => Real.rpow_nonneg (shellDerivNormSum_nonneg _ _ _ _) _)
    hmax

/-- **`e.lower.bound.oscillations` in the re-sited `hosc` shape.**

This is literally the `hosc` binder of
`Closure.JunctionDischargeStepFiveDisplay.step5GaugeEndpoint_of_correctors_gauge`
at the gauge family
`fun R omega => 3^nmesh * shellDerivNormSum n (n+h) (triadicCubeShift R) omega`,
i.e. with the forcing gauge of `e.nablaw.oscillations` read at each cube's own
base point, which is what the per-cube step
`step5CrossDefect_le_meshOscillationCell` produces.

The proved full-mesh producer is re-instantiated, not re-proved: its base point
is universally quantified and its bound is uniform in that point, so the
maximizing cube of the finite grid supplies the transfer.  Every binder is that
producer's own.

Inherited unchanged from
`ApproximateRecurrence.exists_gamma0_freshShellDirichlet_step5MeshOscillation_le_gamma_pow_fifteen`. -/
theorem exists_gamma0_freshShellDirichlet_step5MeshOscillationResited_le_gamma_pow_fifteen
    (d : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {Eb : ℝ // 1 ≤ Eb}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (n : ℤ) (h : ℕ) (K j : ℕ) (nmesh : ℤ), 0 < h → n ≤ m0 →
            (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
              ((K : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
            nmesh =
              recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) →
            (j : ℤ) = (K : ℤ) - nmesh →
            ∀ e : Vec d, vecNorm e ≤ 1 →
              ∀ wD : ShellSeq d → H10Function (openCubeSet (originCube d (K : ℤ))),
                  (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d (K : ℤ))) (wD omega)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e x)) →
                  (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
                    MemLp (fun omega : ShellSeq d =>
                      meshOscillationCell nmesh
                        (wD omega).toH1Function.grad R ^ (4 : ℝ)) 2 M.P.toMeasure) →
                  cubeFamilyAverage (descendantsAtDepth (originCube d (K : ℤ)) j)
                      (fun R => ∫ omega : ShellSeq d,
                        meshOscillationCell nmesh
                          (wD omega).toH1Function.grad R ^ (8 : ℝ) ∂M.P.toMeasure) ≤ E →
                  gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
                      (descendantsAtDepth (originCube d (K : ℤ)) j)
                      (fun R omega => meshOscillationCell nmesh
                        (fun x => (wD omega.val).toH1Function.grad x) R) +
                      ((Annealed.sigmaBar M n : ℝ))⁻¹ *
                        gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
                          (descendantsAtDepth (originCube d (K : ℤ)) j)
                          (fun (R : TriadicCube d) (omega : CutoffSample d) =>
                            (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
                              shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R)
                                omega.val) ≤
                    M.gamma ^ (15 : ℕ) := by
  classical
  obtain ⟨gamma0, hg0pos, hg0quarter, hmain⟩ :=
    exists_gamma0_freshShellDirichlet_step5MeshOscillation_le_gamma_pow_fifteen d hd E
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate n h K j nmesh hhpos hn0 hcstar hK hnmesh hj e he wD
    hsol hmem8 hEle
  obtain ⟨z0, hz0⟩ := gridFourthMomentRoot_shellDerivNormSum_le_of_base_point M n
    (n + (h : ℤ)) (descendantsAtDepth (originCube d (K : ℤ)) j)
  have hbase := hmain M hMgamma m0 Eind hstate n h K j nmesh hhpos hn0 hcstar hK hnmesh hj
    e he z0 wD hsol hmem8 hEle
  have hsig0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    (inv_pos.2 (Annealed.sigmaBar M n).2).le
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hpull : gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
      (descendantsAtDepth (originCube d (K : ℤ)) j)
      (fun (R : TriadicCube d) (omega : CutoffSample d) =>
        (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
          shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val) =
      (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
        gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
          (descendantsAtDepth (originCube d (K : ℤ)) j)
          (fun (R : TriadicCube d) (omega : CutoffSample d) =>
            shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val) :=
    gridFourthMomentRoot_const_mul' _ _ h3nn _
  have hgauge : gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
      (descendantsAtDepth (originCube d (K : ℤ)) j)
      (fun (R : TriadicCube d) (omega : CutoffSample d) =>
        (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
          shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val) ≤
      (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
        (∫ omega : CutoffSample d,
          shellDerivNormSum n (n + (h : ℤ)) z0 omega.val ^ (4 : ℝ)
            ∂(cutoffSampleLaw M).toMeasure) ^ ((4 : ℝ)⁻¹) := by
    rw [hpull]
    exact mul_le_mul_of_nonneg_left hz0 h3nn
  have hmul := mul_le_mul_of_nonneg_left hgauge hsig0
  linarith [hbase, hmul]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

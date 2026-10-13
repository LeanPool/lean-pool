/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowNormalized
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringVolume
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanControlReduction
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealDatumStep

/-!
# SealScalarBase

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Base infrastructure for the boundary lane's scalar composition

Four ingredients the scalar-control composition consumes, none of them specific
to the flush geometry:

* `h10FunctionOfSetEq` — the `H¹₀` transport across a set equality, with exact
  value and gradient preservation (the `H¹₀` sibling of the proved
  `h1FunctionOfSetEq`);
* `isWeaklyHarmonicOn_sub_h1` — weak `Δ`-harmonicity is closed under differences;
* `eLpNorm_sub_average_translatedCube_le_meanZeroPoincare` — the equal-sides
  mean-zero cube Poincaré at a **general** translated cube `c + □_j ⊆ □_m`
  (the `c`-and-scale-generic form of `BoundaryClauseSkeleton`'s covering-cube
  instance, by the same axis-cube realization);
* `toReal_eLpNorm_scaleN_cube_le_anchorWindow` — the `L²` transport of a
  scale-`n` cube inside the frozen window `W' = (z+□_{n+3}) ∩ □_m`, at the
  volume-ratio constant `√(27^d)`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `H¹₀` transport across a set equality -/

/-- Transport an `H¹₀` function across an equality of its carrier set. -/
def h10FunctionOfSetEq {U V : Set (Vec d)} (h : U = V) (u : H10Function U) :
    H10Function V := h ▸ u

@[simp] theorem h10FunctionOfSetEq_toFun {U V : Set (Vec d)} (h : U = V)
    (u : H10Function U) :
    (h10FunctionOfSetEq h u).toH1Function.toFun = u.toH1Function.toFun := by
  subst h
  rfl

@[simp] theorem h10FunctionOfSetEq_grad {U V : Set (Vec d)} (h : U = V)
    (u : H10Function U) :
    (h10FunctionOfSetEq h u).toH1Function.grad = u.toH1Function.grad := by
  subst h
  rfl

/-! ## 2. Weak harmonicity is closed under differences -/

private theorem holderTriple_two_two'' : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
  ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩

private theorem integrableOn_mul_of_memL2' {V : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict V)) (hv : MemLp v 2 (volume.restrict V)) :
    IntegrableOn (fun y => u y * v y) V volume := by
  have := holderTriple_two_two''
  exact hu.integrable_mul hv

private theorem integrableOn_vecDot_of_memL2' {V : Set (Vec d)}
    {F G : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (volume.restrict V))
    (hG : ∀ i, MemLp (fun y => G y i) 2 (volume.restrict V)) :
    IntegrableOn (fun y => vecDot (F y) (G y)) V volume := by
  classical
  have hterm : ∀ i : Fin d, IntegrableOn (fun y => F y i * G y i) V volume :=
    fun i => integrableOn_mul_of_memL2' (hF i) (hG i)
  have hsum : IntegrableOn (fun y => ∑ i : Fin d, F y i * G y i) V volume :=
    MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hterm i
  have hfun : (fun y => vecDot (F y) (G y)) =
      fun y => ∑ i : Fin d, F y i * G y i := by
    funext y
    rfl
  rw [hfun]
  exact hsum

private theorem vecDot_sub_left' (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  classical
  simp only [vecDot, Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Weak `Δ`-harmonicity is closed under differences. -/
theorem isWeaklyHarmonicOn_sub_h1 {V : Set (Vec d)} {v₁ v₂ : H1Function V}
    (h₁ : IsWeaklyHarmonicOn V v₁) (h₂ : IsWeaklyHarmonicOn V v₂) :
    IsWeaklyHarmonicOn V (v₁ - v₂) := by
  intro φ
  have hI1 : IntegrableOn
      (fun x => vecDot (v₁.grad x) (φ.toH1Function.grad x)) V volume :=
    integrableOn_vecDot_of_memL2' (fun i => v₁.gradMemL2 i)
      (fun i => φ.toH1Function.gradMemL2 i)
  have hI2 : IntegrableOn
      (fun x => vecDot (v₂.grad x) (φ.toH1Function.grad x)) V volume :=
    integrableOn_vecDot_of_memL2' (fun i => v₂.gradMemL2 i)
      (fun i => φ.toH1Function.gradMemL2 i)
  have hfun : (fun x => vecDot ((v₁ - v₂).grad x) (φ.toH1Function.grad x)) =
      fun x => vecDot (v₁.grad x) (φ.toH1Function.grad x) -
        vecDot (v₂.grad x) (φ.toH1Function.grad x) := by
    funext x
    have hg : (v₁ - v₂).grad x = v₁.grad x - v₂.grad x := by
      rw [H1Function.sub_grad]
    rw [hg, vecDot_sub_left']
  calc ∫ x in V, vecDot ((v₁ - v₂).grad x) (φ.toH1Function.grad x)
      = (∫ x in V, vecDot (v₁.grad x) (φ.toH1Function.grad x)) -
          ∫ x in V, vecDot (v₂.grad x) (φ.toH1Function.grad x) := by
        rw [hfun, integral_sub hI1 hI2]
    _ = 0 := by rw [h₁ φ, h₂ φ, sub_zero]

/-! ## 3. The mean-zero Poincaré at a general translated cube -/

/-- **The equal-sides mean-zero cube Poincaré on `c + □_j ⊆ □_m`.**

The `c`-and-scale-generic form of `BoundaryClauseSkeleton`'s covering-cube
instance: any translated origin cube inside `□_m` is an axis cube of side
`3^j`, and CoarseGraining's scale-uniform mean-zero Poincaré applies verbatim;
the normalization cancels because the same cube carries both sides. -/
theorem eLpNorm_sub_average_translatedCube_le_meanZeroPoincare {j m : ℤ}
    {c : Vec d}
    (hsub : (fun y' => c + y') '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m))
    (h : H1Function (openCubeSet (originCube d m))) :
    (eLpNorm (fun y => h.toFun y -
          volumeAverage ((fun y' => c + y') '' openCubeSet (originCube d j))
            h.toFun) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y' => c + y') '' openCubeSet (originCube d j)))).toReal ≤
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ j *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y' => c + y') '' openCubeSet (originCube d j)))).toReal := by
  classical
  set cc : Set (Vec d) :=
    (fun y' => c + y') '' openCubeSet (originCube d j) with hcc
  set Lc : ℝ := (3 : ℝ) ^ j with hLc
  set A : Vec d := fun i => c i - (1 / 2 : ℝ) * (3 : ℝ) ^ j with hA
  have hLpos : (0 : ℝ) < Lc := zpow_pos (by norm_num) _
  have hcube : cc = axisCube A Lc := by
    rw [hcc, hA, hLc]
    exact image_add_openCubeSet_eq_axisCube c j
  have hccsub : cc ⊆ openCubeSet (originCube d m) := by
    rw [hcc]
    exact hsub
  have hsubA : axisCube A Lc ⊆ openCubeSet (originCube d m) := by
    rw [← hcube]
    exact hccsub
  have hraw : (eLpNorm (fun y => h.toFun y - integralAverage cc h.toFun) 2
        (volumeMeasureOn cc)).toReal ≤
      unitMeanZeroPoincareConst d * Lc *
        ∑ i : Fin d,
          (eLpNorm (fun y => h.grad y i) 2 (volumeMeasureOn cc)).toReal := by
    rw [hcube]
    have hpo := scaled_meanZero_poincare A hLpos
      (h.restrict (isOpen_axisCube A Lc) hsubA)
    have hfun : ((h.restrict (isOpen_axisCube A Lc) hsubA).subAverage).toFun =
        fun y => h.toFun y - integralAverage (axisCube A Lc) h.toFun := by
      funext y
      exact H1Function.subAverage_apply _ y
    rwa [hfun] at hpo
  have hiv : integralAverage cc h.toFun = volumeAverage cc h.toFun := rfl
  rw [hiv] at hraw
  have hrestrict : volumeMeasureOn cc = volume.restrict cc := rfl
  rw [hrestrict] at hraw
  simp only [eLpNorm_normalizedVolumeMeasureOn_eq, ENNReal.toReal_mul]
  have hr : (0 : ℝ) ≤ (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal := ENNReal.toReal_nonneg
  calc (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
        (eLpNorm (fun y => h.toFun y - volumeAverage cc h.toFun) 2
          (volume.restrict cc)).toReal
      ≤ (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
          (unitMeanZeroPoincareConst d * Lc *
            ∑ i : Fin d,
              (eLpNorm (fun y => h.grad y i) 2 (volume.restrict cc)).toReal) :=
        mul_le_mul_of_nonneg_left hraw hr
    _ = unitMeanZeroPoincareConst d * Lc *
          ∑ i : Fin d,
            (((volume cc)⁻¹) ^ (1 / 2 : ℝ)).toReal *
              (eLpNorm (fun y => h.grad y i) 2 (volume.restrict cc)).toReal := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring

/-! ## 4. The scale-`n` window transport -/

/-- The frozen window's volume is at most `27^d` times a scale-`n` cube's. -/
theorem volume_anchorWindow_le_scaleN_cube (n m : ℤ) (z c' : Vec d) :
    volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) ≤
      ENNReal.ofReal ((27 : ℝ) ^ d) *
        volume ((fun y => c' + y) '' openCubeSet (originCube d n)) := by
  have h1 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≤
      volume ((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) :=
    measure_mono Set.inter_subset_left
  have h2 : volume ((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) =
      volume (openCubeSet (originCube d (n + 3))) := volume_image_add z _
  have h3 : volume ((fun y => c' + y) '' openCubeSet (originCube d n)) =
      volume (openCubeSet (originCube d n)) := volume_image_add c' _
  have h4 : volume (openCubeSet (originCube d (n + 3))) =
      ENNReal.ofReal (((3 : ℝ) ^ (n + 3)) ^ d) := by
    rw [← ENNReal.ofReal_toReal (volume_openCubeSet_originCube_ne_top d (n + 3)),
      volume_toReal_openCubeSet_originCube]
  have h5 : volume (openCubeSet (originCube d n)) =
      ENNReal.ofReal (((3 : ℝ) ^ n) ^ d) := by
    rw [← ENNReal.ofReal_toReal (volume_openCubeSet_originCube_ne_top d n),
      volume_toReal_openCubeSet_originCube]
  have h6 : ((3 : ℝ) ^ (n + 3)) ^ d = (27 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d := by
    have h7 : (3 : ℝ) ^ (n + 3) = 27 * (3 : ℝ) ^ n := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
      ring
    rw [h7, mul_pow]
  calc volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
      ≤ volume ((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) := h1
    _ = ENNReal.ofReal ((27 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d) := by rw [h2, h4, h6]
    _ = ENNReal.ofReal ((27 : ℝ) ^ d) * ENNReal.ofReal (((3 : ℝ) ^ n) ^ d) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((27 : ℝ) ^ d) *
          volume ((fun y => c' + y) '' openCubeSet (originCube d n)) := by
        rw [h3, h5]

/-- **The `L²` transport of a scale-`n` cube onto the frozen window**, at the
volume-ratio constant `√(27^d)`. -/
theorem toReal_eLpNorm_scaleN_cube_le_anchorWindow {n m : ℤ} {z c' : Vec d}
    (hsub : (fun y => c' + y) '' openCubeSet (originCube d n) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    {f : Vec d → ℝ}
    (hfin : eLpNorm f 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤) :
    (eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => c' + y) '' openCubeSet (originCube d n)))).toReal ≤
      Real.sqrt ((27 : ℝ) ^ d) *
        (eLpNorm f 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  have h27pos : (0 : ℝ) < (27 : ℝ) ^ d := by positivity
  have hbase := eLpNorm_le_of_volume_le (K := ENNReal.ofReal ((27 : ℝ) ^ d))
    hsub (ne_of_gt (ENNReal.ofReal_pos.mpr h27pos)) ENNReal.ofReal_ne_top
    (volume_anchorWindow_le_scaleN_cube n m z c') f
  have hhalf : (ENNReal.ofReal ((27 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt ((27 : ℝ) ^ d)) := by
    rw [ENNReal.ofReal_rpow_of_pos h27pos, Real.sqrt_eq_rpow]
  rw [hhalf] at hbase
  have hRne : ENNReal.ofReal (Real.sqrt ((27 : ℝ) ^ d)) *
      eLpNorm f 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hstep := ENNReal.toReal_mono hRne hbase
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hstep

/-! ## 5. Volume-ratio facts at the frozen window -/

theorem volume_toReal_anchorWindow_le (n m : ℤ) (z : Vec d) :
    (volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))).toReal ≤ ((3 : ℝ) ^ (n + 3)) ^ d := by
  have h1 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≤
      volume ((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) :=
    measure_mono Set.inter_subset_left
  have h2 := volume_image_add_openCubeSet_ne_top z (n + 3)
  have h3 := ENNReal.toReal_mono h2 h1
  rwa [volume_toReal_image_add_openCubeSet_originCube] at h3

theorem volume_toReal_anchorWindow_pos {n m : ℤ} {z c' : Vec d}
    (hsub : (fun y => c' + y) '' openCubeSet (originCube d n) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) :
    0 < (volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)))).toReal := by
  have h1 := measure_mono (μ := (volume : Measure (Vec d))) hsub
  have h2 := ENNReal.toReal_mono (volume_anchorWindow_ne_top (n + 3) m z) h1
  exact lt_of_lt_of_le (volume_toReal_image_add_openCubeSet_pos c' n) h2

theorem ratio_anchorWindow_coveringCube_le (n m : ℤ) (x z : Vec d) :
    (volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))).toReal /
      (volume ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))).toReal ≤ (3 : ℝ) ^ d := by
  have hpos := volume_toReal_image_add_openCubeSet_pos
    (wellPlacedCentre x m (n + 2)) (n + 2)
  rw [div_le_iff₀ hpos, volume_toReal_image_add_openCubeSet_originCube]
  have hup := volume_toReal_anchorWindow_le n m z
  have heq : ((3 : ℝ) ^ (n + 3)) ^ d = (3 : ℝ) ^ d * ((3 : ℝ) ^ (n + 2)) ^ d := by
    have h1 : (3 : ℝ) ^ (n + 3) = 3 * (3 : ℝ) ^ (n + 2) := by
      rw [show n + 3 = (n + 2) + 1 by ring,
        zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    rw [h1, mul_pow]
  calc (volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))).toReal
      ≤ ((3 : ℝ) ^ (n + 3)) ^ d := hup
    _ = (3 : ℝ) ^ d * ((3 : ℝ) ^ (n + 2)) ^ d := heq

theorem ratio_anchorWindow_scaleN_le (n m : ℤ) (z c' : Vec d) :
    (volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))).toReal /
      (volume ((fun y => c' + y) '' openCubeSet (originCube d n))).toReal ≤
      (27 : ℝ) ^ d := by
  have hpos := volume_toReal_image_add_openCubeSet_pos c' n
  rw [div_le_iff₀ hpos, volume_toReal_image_add_openCubeSet_originCube]
  have hup := volume_toReal_anchorWindow_le n m z
  have heq : ((3 : ℝ) ^ (n + 3)) ^ d = (27 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d := by
    have h1 : (3 : ℝ) ^ (n + 3) = 27 * (3 : ℝ) ^ n := by
      have h33 : (3 : ℝ) ^ (3 : ℤ) = 27 := by norm_num
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) n 3, h33]
      ring
    rw [h1, mul_pow]
  calc (volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))).toReal
      ≤ ((3 : ℝ) ^ (n + 3)) ^ d := hup
    _ = (27 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d := heq

/-! ## 6. The transfer of a cube mean to the window mean -/

theorem abs_avg_cube_sub_window_le {m : ℤ} {W A : Set (Vec d)} {R : ℝ}
    (hAm : MeasurableSet A) (hsub : A ⊆ W)
    (hWm : W ⊆ openCubeSet (originCube d m))
    (hWpos : 0 < (volume W).toReal) (hApos : 0 < (volume A).toReal)
    (hAtop : volume A ≠ ⊤) (hWtop : volume W ≠ ⊤)
    (hR : (volume W).toReal / (volume A).toReal ≤ R)
    (u : H1Function (openCubeSet (originCube d m))) :
    |volumeAverage A u.toFun - volumeAverage W u.toFun| ≤
      Real.sqrt R *
        normalizedL2On W (fun y => u.toFun y - volumeAverage W u.toFun) := by
  have hmemA := memLp_toFun_of_subset u (hsub.trans hWm)
  have hmemW := memLp_toFun_of_subset u hWm
  have h := abs_volumeAverage_sub_windowAverage_le (W := W) (V := A) hAm hsub
    hWpos hApos hAtop (integrableOn_of_memLp_two hAtop hmemA)
    (integrableOn_sub_const_sq hAtop hmemA (volumeAverage W u.toFun))
    (integrableOn_sub_const_sq hWtop hmemW (volumeAverage W u.toFun))
  refine h.trans ?_
  have hnl : 0 ≤ normalizedL2On W (fun y => u.toFun y - volumeAverage W u.toFun) :=
    normalizedL2On_nonneg _ _
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hR) hnl


end

end Algsuperdiff.Section4.Provider.ExcessDecay

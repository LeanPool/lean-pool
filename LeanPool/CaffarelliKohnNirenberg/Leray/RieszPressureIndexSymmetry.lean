/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2Symmetry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2Input
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation

/-!
# Symmetry of the double Riesz pressure components

The mixed second derivative realization identifies the two index orders.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem rieszPressureL2Extension_index_swap (i j : Fin 3)
    (u : Lp ℝ 2 (volume : Measure Vec3)) :
    CKN.Foundation.Euclidean.rieszSecondL2Extension
        (CKN.Foundation.Euclidean.rieszSecondL2Input i j) u =
      CKN.Foundation.Euclidean.rieszSecondL2Extension
        (CKN.Foundation.Euclidean.rieszSecondL2Input j i) u := by
  let Tij := CKN.Foundation.Euclidean.rieszSecondL2Extension
    (CKN.Foundation.Euclidean.rieszSecondL2Input i j)
  let Tji := CKN.Foundation.Euclidean.rieszSecondL2Extension
    (CKN.Foundation.Euclidean.rieszSecondL2Input j i)
  have hClosed : IsClosed {w : Lp ℝ 2 (volume : Measure Vec3) | Tij w = Tji w} := by
    exact isClosed_eq Tij.continuous Tji.continuous
  have hdense : DenseRange
      (fun z : {w : Lp ℝ 2 (volume : Measure Vec3) // ∃ f : Vec3 → ℝ,
        w =ᵐ[volume] f ∧ HasCompactSupport f ∧ ContDiff ℝ (⊤ : ℕ∞) f} =>
        (z : Lp ℝ 2 (volume : Measure Vec3))) :=
    (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure Vec3))
      (by norm_num)).denseRange_val
  have hEq : Tij u = Tji u := by
    apply isClosed_property hdense hClosed
    rintro ⟨w, hw⟩
    rcases hw with ⟨f, hwf, hfc, hf⟩
    change Tij w = Tji w
    have hmem : MemLp f 2 (volume : Measure Vec3) :=
      hf.continuous.memLp_of_hasCompactSupport hfc
    have hw' : w = hmem.toLp f := by
      apply Lp.ext
      exact hwf.trans hmem.coeFn_toLp.symm
    rw [hw']
    obtain ⟨hmemIJ, hIJ⟩ :=
      CKN.Foundation.Euclidean.rieszSecondL2Input_extension_smooth_hessian
        i j hf hfc
    obtain ⟨hmemJI, hJI⟩ :=
      CKN.Foundation.Euclidean.rieszSecondL2Input_extension_smooth_hessian
        j i hf hfc
    have hHessian :
        mixedSecond (CKN.pressureNewtonianPotential f) i j =
        mixedSecond (CKN.pressureNewtonianPotential f) j i := by
      funext x
      exact CKN.mixedSecond_swap
        (CKN.pressureNewtonianPotential_smooth hf hfc) i j x
    have hLp : hmemIJ.toLp
          (mixedSecond (CKN.pressureNewtonianPotential f) i j) =
        hmemJI.toLp
          (mixedSecond (CKN.pressureNewtonianPotential f) j i) := by
      apply Lp.ext
      filter_upwards [hmemIJ.coeFn_toLp, hmemJI.coeFn_toLp] with x hleft hright
      rw [hleft, hright]
      exact congrFun hHessian x
    calc
      Tij (hmem.toLp f) = hmemIJ.toLp
          (mixedSecond (CKN.pressureNewtonianPotential f) i j) := hIJ
      _ = hmemJI.toLp
          (mixedSecond (CKN.pressureNewtonianPotential f) j i) := hLp
      _ = Tji (hmem.toLp f) := hJI.symm
  exact hEq

/-- CKN's two all-exponent pressure components agree in their index order,
used by `lem:riesz-duality`. -/
theorem rieszPressureOperator_ae_eq_index_swap
    (r : ℝ) (hr : 1 < r) (i j : Fin 3) (g : Vec3 → ℝ)
    (hg : MemLp g (ENNReal.ofReal r) (volume : Measure Vec3))
    (hg2 : MemLp g 2 (volume : Measure Vec3)) :
    (fun x => rieszPressureOperator r hr i j (hg.toLp g) x) =ᵐ[volume]
      fun x => rieszPressureOperator r hr j i (hg.toLp g) x := by
  have hExt := rieszPressureL2Extension_index_swap i j (hg2.toLp g)
  have hRawI := CKN.Foundation.Euclidean.rieszSecondL2RawOperator_ae_eq
    (CKN.Foundation.Euclidean.rieszSecondL2Input i j) hg2
  have hMeasI := CKN.Foundation.Euclidean.rieszSecondL2MeasurableOperator_ae_eq_extension
    (CKN.Foundation.Euclidean.rieszSecondL2Input i j) (hg2.toLp g)
  have hRawJ := CKN.Foundation.Euclidean.rieszSecondL2RawOperator_ae_eq
    (CKN.Foundation.Euclidean.rieszSecondL2Input j i) hg2
  have hMeasJ := CKN.Foundation.Euclidean.rieszSecondL2MeasurableOperator_ae_eq_extension
    (CKN.Foundation.Euclidean.rieszSecondL2Input j i) (hg2.toLp g)
  have hRaw :
      CKN.Foundation.Euclidean.rieszSecondL2RawOperator
          (CKN.Foundation.Euclidean.rieszSecondL2Input i j) g =ᵐ[volume]
        CKN.Foundation.Euclidean.rieszSecondL2RawOperator
          (CKN.Foundation.Euclidean.rieszSecondL2Input j i) g := by
    have hExtAE :
        ((CKN.Foundation.Euclidean.rieszSecondL2Extension
          (CKN.Foundation.Euclidean.rieszSecondL2Input i j) (hg2.toLp g)) :
          Vec3 → ℝ) =ᵐ[volume]
        ((CKN.Foundation.Euclidean.rieszSecondL2Extension
          (CKN.Foundation.Euclidean.rieszSecondL2Input j i) (hg2.toLp g)) :
          Vec3 → ℝ) := by
      exact (Lp.ext_iff).1 hExt
    have hPath := hMeasI.trans (hExtAE.trans hMeasJ.symm)
    exact hRawI.trans (hPath.trans hRawJ.symm)
  have hI := rieszPressureOperator_ae_eq_negRaw r hr i j g hg hg2
  have hJ := rieszPressureOperator_ae_eq_negRaw r hr j i g hg hg2
  exact hI.trans (hRaw.neg.trans hJ.symm)

end CKN.Leray

end

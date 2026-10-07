/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDuality
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureIndexSymmetry

/-!
# Compact-core duality for the space-time pressure operators

The spatial CKN L² pairing yields duality first for compact space-time data.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem rieszPressureOperator_pairing_compact
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q) (i j : Fin 3)
    {f g : Vec3 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ x, rieszPressureOperator r hr i j
        ((hf.memLp_of_hasCompactSupport hfc).toLp f) x * g x =
      ∫ x, f x * rieszPressureOperator q hq j i
        ((hg.memLp_of_hasCompactSupport hgc).toLp g) x := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  have hfR : MemLp f (ENNReal.ofReal r) (volume : Measure Vec3) :=
    hf.memLp_of_hasCompactSupport hfc
  have hgQ : MemLp g (ENNReal.ofReal q) (volume : Measure Vec3) :=
    hg.memLp_of_hasCompactSupport hgc
  have hf2 : MemLp f 2 (volume : Measure Vec3) :=
    hf.memLp_of_hasCompactSupport hfc
  have hg2 : MemLp g 2 (volume : Measure Vec3) :=
    hg.memLp_of_hasCompactSupport hgc
  let raw (a b : Fin 3) (w : Vec3 → ℝ) : Vec3 → ℝ :=
    CKN.Foundation.Euclidean.rieszSecondL2RawOperator
      (CKN.Foundation.Euclidean.rieszSecondL2Input a b) w
  have hleft := rieszPressureOperator_ae_eq_negRaw r hr i j f hfR hf2
  have hright := rieszPressureOperator_ae_eq_negRaw q hq j i g hgQ hg2
  have hraw := CKN.Foundation.Euclidean.rieszSecondL2RawOperator_integral_mul_commute
    (CKN.Foundation.Euclidean.rieszSecondL2Input i j) hf2 hg2
  have hOpI := rieszPressureOperator_ae_eq_negRaw q hq i j g hgQ hg2
  have hOpJ := rieszPressureOperator_ae_eq_negRaw q hq j i g hgQ hg2
  have hOpSwap := rieszPressureOperator_ae_eq_index_swap q hq i j g hgQ hg2
  have hRawSwapNeg := hOpI.symm.trans (hOpSwap.trans hOpJ)
  have hRawSwap : raw i j g =ᵐ[volume] raw j i g := by
    filter_upwards [hRawSwapNeg] with x hx
    exact neg_injective hx
  calc
    ∫ x, rieszPressureOperator r hr i j (hfR.toLp f) x * g x =
        ∫ x, -raw i j f x * g x := by
          apply integral_congr_ae
          filter_upwards [hleft] with x hx
          exact congrArg (fun y : ℝ => y * g x) hx
    _ = -(∫ x, raw i j f x * g x) := by
          calc
            _ = ∫ x, -(raw i j f x * g x) := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
            _ = _ := by rw [integral_neg]
    _ = -(∫ x, f x * raw j i g x) := by
          rw [hraw]
          congr 1
          apply integral_congr_ae
          filter_upwards [hRawSwap] with x hx
          exact congrArg (fun y : ℝ => f x * y) hx
    _ = ∫ x, f x * (-raw j i g x) := by
          rw [← integral_neg]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    _ = ∫ x, f x * rieszPressureOperator q hq j i (hgQ.toLp g) x := by
          apply integral_congr_ae
          filter_upwards [hright] with x hx
          exact congrArg (fun y : ℝ => f x * y) hx.symm

/-- The joint compact representative obeys the adjoint identity, used by
`lem:riesz-duality`. -/
theorem rieszPressureComponentCompactClass_pairing
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q) (i j : Fin 3)
    {F G : Vec3 × ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    ∫ z, (rieszPressureComponentCompactClass r hr i j (F := F) hF hFc :
        Vec3 × ℝ → ℝ) z * G z =
      ∫ z, F z * (rieszPressureComponentCompactClass q hq j i (F := G) hG hGc :
        Vec3 × ℝ → ℝ) z := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  have : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q) :=
    Real.HolderConjugate.ennrealOfReal hHolder
  obtain ⟨P, hPm, hPmem, hPclass, hPslice⟩ :=
    exists_rieszPressureComponentCompactClass_representative r hr i j hF hFc
  obtain ⟨Q, hQm, hQmem, hQclass, hQslice⟩ :=
    exists_rieszPressureComponentCompactClass_representative q hq j i hG hGc
  have hGmem : MemLp G (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ)) :=
    hG.memLp_of_hasCompactSupport hGc
  have hFmem : MemLp F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    hF.memLp_of_hasCompactSupport hFc
  have hPG : Integrable (fun z : Vec3 × ℝ => P z * G z)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hPmem.integrable_mul hGmem
  have hFQ : Integrable (fun z : Vec3 × ℝ => F z * Q z)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hFmem.integrable_mul hQmem
  have hSections : ∀ᵐ t ∂(volume : Measure ℝ),
      ∫ x, P (x, t) * G (x, t) = ∫ x, F (x, t) * Q (x, t) := by
    filter_upwards [hPslice, hQslice] with t hPt hQt
    let f : Vec3 → ℝ := fun x => F (x, t)
    let g : Vec3 → ℝ := fun x => G (x, t)
    have hf : Continuous f := hF.comp (continuous_id.prodMk continuous_const)
    have hfc : HasCompactSupport f := continuous_spaceTimeSlice_hasCompactSupport hFc t
    have hg : Continuous g := hG.comp (continuous_id.prodMk continuous_const)
    have hgc : HasCompactSupport g := continuous_spaceTimeSlice_hasCompactSupport hGc t
    have hsp := rieszPressureOperator_pairing_compact r hr q hq i j hf hfc hg hgc
    calc
      ∫ x, P (x, t) * G (x, t) =
          ∫ x, rieszPressureOperator r hr i j
            ((hf.memLp_of_hasCompactSupport hfc).toLp f) x * g x := by
              apply integral_congr_ae
              filter_upwards [hPt] with x hx
              exact congrArg (fun y : ℝ => y * G (x, t)) hx
      _ = ∫ x, f x * rieszPressureOperator q hq j i
            ((hg.memLp_of_hasCompactSupport hgc).toLp g) x := hsp
      _ = ∫ x, F (x, t) * Q (x, t) := by
              apply integral_congr_ae
              filter_upwards [hQt] with x hx
              exact congrArg (fun y : ℝ => F (x, t) * y) hx.symm
  calc
    ∫ z, (rieszPressureComponentCompactClass r hr i j (F := F) hF hFc :
        Vec3 × ℝ → ℝ) z * G z = ∫ z, P z * G z := by
          apply integral_congr_ae
          filter_upwards [hPclass] with z hz
          exact congrArg (fun y : ℝ => y * G z) hz.symm
    _ = ∫ t, ∫ x, P (x, t) * G (x, t) := by
          rw [Measure.volume_eq_prod]
          exact integral_prod_symm _ hPG
    _ = ∫ t, ∫ x, F (x, t) * Q (x, t) := by
          apply integral_congr_ae
          exact hSections
    _ = ∫ z, F z * Q z := by
          symm
          rw [Measure.volume_eq_prod]
          exact integral_prod_symm _ hFQ
    _ = ∫ z, F z * (rieszPressureComponentCompactClass q hq j i (F := G)
          hG hGc : Vec3 × ℝ → ℝ) z := by
          apply integral_congr_ae
          filter_upwards [hQclass] with z hz
          exact congrArg (fun y : ℝ => F z * y) hz

end CKN.Leray

end

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

/- Cellwise Cauchy--Schwarz estimates over an enlarged-margin ruled carrier. -/

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledTriadicWhitneyCarrier
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledWhitneyRowCauchySchwarz

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast
open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The unnormalized volume-weighted square row associated with a nonnegative
cell quantity. -/
@[expose]
def rawWhitneyRowEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (X : system.CellIndex → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i : system.CellIndex, volume (system.cell i) * X i

/-- The volume-normalized square row associated with a nonnegative cell
quantity. -/
@[expose]
def normalizedWhitneyRowEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (X : system.CellIndex → ℝ≥0∞) : ℝ≥0∞ :=
  (volume U)⁻¹ * rawWhitneyRowEnergy system X

/-- Countable Cauchy--Schwarz for extended nonnegative rows. -/
theorem tsum_rpow_half_mul_rpow_half_le
    {ι : Type*} [Countable ι] (A B : ι → ℝ≥0∞) :
    (∑' i, A i ^ (1 / 2 : ℝ) * B i ^ (1 / 2 : ℝ)) ≤
      (∑' i, A i) ^ (1 / 2 : ℝ) *
        (∑' i, B i) ^ (1 / 2 : ℝ) := by
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hA : AEMeasurable A (Measure.count : Measure ι) :=
    (measurable_of_countable A).aemeasurable
  have hB : AEMeasurable B (Measure.count : Measure ι) :=
    (measurable_of_countable B).aemeasurable
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    (μ := (Measure.count : Measure ι)) (f := A) (g := B)
    hA hB (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa only [lintegral_count] using hholder

private theorem volume_mul_half_products
    (v N P : ℝ≥0∞) :
    v * (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) =
      (v * N) ^ (1 / 2 : ℝ) * (v * P) ^ (1 / 2 : ℝ) := by
  have hv : v ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ) = v := by
    rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
      (by norm_num) (by norm_num)]
    norm_num
  calc
    v * (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) =
        (v ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ)) *
          (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) :=
      congrArg (fun z => z *
        (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ))) hv.symm
    _ = (v ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) *
        (v ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) := by
      ac_rfl
    _ = (v * N) ^ (1 / 2 : ℝ) * (v * P) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]

private theorem volume_mul_ofReal_abs_volumeAverage
    (V : Set (Vec d)) (f : Vec d → ℝ)
    (hVzero : volume V ≠ 0) (hVtop : volume V ≠ ⊤) :
    volume V * ENNReal.ofReal |volumeAverage V f| =
      ENNReal.ofReal |∫ x in V, f x ∂volume| := by
  have hvol : 0 ≤ (volume V).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hvolNe : (volume V).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hVzero, hVtop⟩
  unfold volumeAverage
  rw [abs_mul, abs_of_nonneg hvol, ENNReal.ofReal_mul hvol]
  calc
    volume V *
          (ENNReal.ofReal (volume V).toReal⁻¹ *
            ENNReal.ofReal |∫ x in V, f x ∂volume|) =
        ENNReal.ofReal (volume V).toReal *
          (ENNReal.ofReal (volume V).toReal⁻¹ *
            ENNReal.ofReal |∫ x in V, f x ∂volume|) := by
      rw [ENNReal.ofReal_toReal hVtop]
    _ = ENNReal.ofReal
          ((volume V).toReal *
            ((volume V).toReal⁻¹ * |∫ x in V, f x ∂volume|)) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    _ = ENNReal.ofReal |∫ x in V, f x ∂volume| := by
      rw [← mul_assoc, mul_inv_cancel₀ hvolNe, one_mul]

private theorem volume_mul_ofReal_abs_volumeAverage_whitneyCell
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) (f : Vec d → ℝ) :
    volume (system.cell i) *
        ENNReal.ofReal |volumeAverage (system.cell i) f| =
      ENNReal.ofReal |∫ x in system.cell i, f x ∂volume| := by
  apply volume_mul_ofReal_abs_volumeAverage
  · have hreal : 0 < (volume (system.cell i)).toReal := by
      change 0 < (volume
        (openCubeSet
          (translateCube (system.index i) (originCube d (system.scale i))))).toReal
      rw [volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
      simp only [translateCube, originCube]
      positivity
    exact (ENNReal.toReal_pos_iff.mp hreal).1.ne'
  · exact
      (volume_openCubeSet_lt_top
        (translateCube (system.index i) (originCube d (system.scale i)))).ne

/-- If every normalized cell pairing is bounded by the product of a negative
and positive cell size, then the sum of raw cell pairings is bounded by the
product of the two volume-weighted square rows. -/
theorem whitneyCellIntegrals_le_row_cauchySchwarz
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {f : Vec d → ℝ} (N P : system.CellIndex → ℝ≥0∞)
    (hcell : ∀ i : system.CellIndex,
      ENNReal.ofReal |volumeAverage (system.cell i) f| ≤
        N i ^ (1 / 2 : ℝ) * P i ^ (1 / 2 : ℝ)) :
    (∑' i : system.CellIndex,
        ENNReal.ofReal |∫ x in system.cell i, f x ∂volume|) ≤
      (rawWhitneyRowEnergy system N) ^ (1 / 2 : ℝ) *
        (rawWhitneyRowEnergy system P) ^ (1 / 2 : ℝ) := by
  calc
    (∑' i : system.CellIndex,
        ENNReal.ofReal |∫ x in system.cell i, f x ∂volume|) ≤
        ∑' i : system.CellIndex,
          (volume (system.cell i) * N i) ^ (1 / 2 : ℝ) *
            (volume (system.cell i) * P i) ^ (1 / 2 : ℝ) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← volume_mul_ofReal_abs_volumeAverage_whitneyCell system i f,
        ← volume_mul_half_products]
      exact mul_le_mul_right (hcell i) _
    _ ≤ (∑' i : system.CellIndex, volume (system.cell i) * N i) ^
          (1 / 2 : ℝ) *
        (∑' i : system.CellIndex, volume (system.cell i) * P i) ^
          (1 / 2 : ℝ) :=
      tsum_rpow_half_mul_rpow_half_le
        (fun i : system.CellIndex => volume (system.cell i) * N i)
        (fun i : system.CellIndex => volume (system.cell i) * P i)
    _ = (rawWhitneyRowEnergy system N) ^ (1 / 2 : ℝ) *
        (rawWhitneyRowEnergy system P) ^ (1 / 2 : ℝ) := rfl

/-- The domain pairing is controlled by the two ruled Whitney square rows
once the local dual estimate is known on every cell. -/
theorem ofReal_abs_volumeAverage_le_whitneyRow_cauchySchwarz
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hd : 1 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    {f : Vec d → ℝ} (hf : IntegrableOn f U volume)
    (N P : system.CellIndex → ℝ≥0∞)
    (hcell : ∀ i : system.CellIndex,
      ENNReal.ofReal |volumeAverage (system.cell i) f| ≤
        N i ^ (1 / 2 : ℝ) * P i ^ (1 / 2 : ℝ)) :
    ENNReal.ofReal |volumeAverage U f| ≤
      ENNReal.ofReal (volume U).toReal⁻¹ *
        ((rawWhitneyRowEnergy system N) ^ (1 / 2 : ℝ) *
          (rawWhitneyRowEnergy system P) ^ (1 / 2 : ℝ)) := by
  let A : Set (Vec d) := ⋃ i : system.CellIndex, system.cell i
  have hAU : A ⊆ U := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact system.cell_subset i hxi
  have hiUnionRows : A =
      ⋃ a : ℤ, ⋃ w ∈ (system.rows a : Set (Fin d → ℤ)),
        standardCell d a w := by
    dsimp only [A]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i.1,
        Set.mem_iUnion₂.mpr ⟨i.2.1, i.2.2, hxi⟩⟩
    · intro hx
      obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      let i : system.CellIndex := ⟨a, ⟨w, hw⟩⟩
      exact Set.mem_iUnion.mpr ⟨i, hxw⟩
  have hAE : A =ᵐ[volume] U := by
    have hdiff : volume (U \ A) = 0 := by
      rw [hiUnionRows]
      exact system.ae_exhaustion hd hU
    exact _root_.Filter.EventuallyLE.antisymm (ae_of_all volume hAU)
      (ae_le_set.mpr hdiff)
  have hmeas : ∀ i : system.CellIndex,
      MeasurableSet (system.cell i) := by
    intro i
    exact (isOpen_openCubeSet
      (translateCube (system.index i)
        (originCube d (system.scale i)))).measurableSet
  have hdisjoint : Pairwise
      (Disjoint on fun i : system.CellIndex => system.cell i) := by
    intro i j hij
    exact system.pairwise_disjoint i j hij
  have hfA : IntegrableOn f A volume := hf.mono_set hAU
  have hsum : Summable
      (fun i : system.CellIndex => ∫ x in system.cell i, f x ∂volume) :=
    (hasSum_integral_iUnion hmeas hdisjoint hfA).summable
  have hintegral :
      ∫ x in U, f x ∂volume =
        ∑' i : system.CellIndex, ∫ x in system.cell i, f x ∂volume := by
    calc
      ∫ x in U, f x ∂volume = ∫ x in A, f x ∂volume := by
        rw [Measure.restrict_congr_set hAE]
      _ = ∑' i : system.CellIndex,
          ∫ x in system.cell i, f x ∂volume :=
        integral_iUnion hmeas hdisjoint hfA
  have habs :
      |∫ x in U, f x ∂volume| ≤
        ∑' i : system.CellIndex,
          |∫ x in system.cell i, f x ∂volume| := by
    rw [hintegral]
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
  have hvol : 0 ≤ (volume U).toReal⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have hbase : ENNReal.ofReal |volumeAverage U f| ≤
      ENNReal.ofReal (volume U).toReal⁻¹ *
        ∑' i : system.CellIndex,
          ENNReal.ofReal |∫ x in system.cell i, f x ∂volume| := by
    unfold volumeAverage
    rw [abs_mul, abs_of_nonneg hvol, ENNReal.ofReal_mul hvol]
    calc
      ENNReal.ofReal (volume U).toReal⁻¹ *
            ENNReal.ofReal |∫ x in U, f x ∂volume| ≤
          ENNReal.ofReal (volume U).toReal⁻¹ *
            ENNReal.ofReal
              (∑' i : system.CellIndex,
                |∫ x in system.cell i, f x ∂volume|) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal habs) _
      _ = ENNReal.ofReal (volume U).toReal⁻¹ *
            ∑' i : system.CellIndex,
              ENNReal.ofReal |∫ x in system.cell i, f x ∂volume| := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _)
          hsum.norm]
  exact hbase.trans
    (mul_le_mul_right
      (whitneyCellIntegrals_le_row_cauchySchwarz system N P hcell) _)

end

end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledWhitneyCellDuality
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.IntegrableBoundaryWeightedCenteredHardy
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryDistance

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledHardyPositiveRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A private byte-faithful copy of the inverse fractional scale weight from
`RuledWhitneyCellDuality`.  It is repeated here because that module keeps its
one-cell implementation adapters private. -/
@[expose]
public def ruledScaleWeight
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (i : system.CellIndex) : ℝ≥0∞ :=
  ENNReal.ofReal (((3 : ℝ) ^ system.scale i) ^ (-2 * s))

/-- The expanded positive fractional square shared by the ruled Hardy row
and its pairing consumer.  Its body is byte-faithful to the private one-cell
adapter in `RuledWhitneyCellDuality`. -/
@[expose]
def ruledPositiveWhitneyCellEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : Vec d → Vec d) (i : system.CellIndex) : ℝ≥0∞ :=
  (volume (system.cell i))⁻¹ *
    (ruledScaleWeight system s i *
        ∫⁻ x in system.cell i,
          ENNReal.ofReal (vecNormSq (F x)) ∂volume +
      ∫⁻ z in system.cell i ×ˢ system.cell i,
        whitneyRowFractionalKernel s F z ∂(volume.prod volume))

/-- The inverse-scale local `L²` contribution over the ruled Whitney cells. -/
@[expose]
def ruledPositiveRowL2Energy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  (volume U)⁻¹ *
    ∑' i : system.CellIndex, ruledScaleWeight system s i *
      ∫⁻ x in system.cell i, ENNReal.ofReal (vecNormSq (F x)) ∂volume

/-- The normalized same-cell Gagliardo contribution over the ruled cells. -/
@[expose]
def ruledPositiveRowGagliardoEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  (volume U)⁻¹ *
    ∑' i : system.CellIndex,
      ∫⁻ z in system.cell i ×ˢ system.cell i,
        whitneyRowFractionalKernel s F z ∂(volume.prod volume)

/-- The complete positive fractional energy over the ruled Whitney cells. -/
@[expose]
def ruledPositiveRowEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ruledPositiveRowL2Energy system s F +
    ruledPositiveRowGagliardoEnergy system s F

private theorem volume_whitneyCell_pos
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : 0 < volume (system.cell i) := by
  have hreal : 0 < (volume (system.cell i)).toReal := by
    change 0 < (volume
      (openCubeSet
        (translateCube (system.index i) (originCube d (system.scale i))))).toReal
    rw [volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
    simp only [translateCube, originCube]
    positivity
  exact (ENNReal.toReal_pos_iff.mp hreal).1

private theorem volume_whitneyCell_ne_top
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : volume (system.cell i) ≠ ⊤ :=
  (volume_openCubeSet_lt_top
    (translateCube (system.index i) (originCube d (system.scale i)))).ne

/-- Multiplying one expanded ruled-cell square by its volume recovers its
two raw positive-row contributions. -/
theorem volume_mul_positiveWhitneyCellEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : Vec d → Vec d) (i : system.CellIndex) :
    volume (system.cell i) * ruledPositiveWhitneyCellEnergy system s F i =
      ruledScaleWeight system s i *
          ∫⁻ x in system.cell i,
            ENNReal.ofReal (vecNormSq (F x)) ∂volume +
        ∫⁻ z in system.cell i ×ˢ system.cell i,
          whitneyRowFractionalKernel s F z ∂(volume.prod volume) := by
  unfold ruledPositiveWhitneyCellEnergy
  rw [← mul_assoc,
    ENNReal.mul_inv_cancel (volume_whitneyCell_pos system i).ne'
      (volume_whitneyCell_ne_top system i), one_mul]

/-- The raw row of expanded ruled-cell squares is the domain volume times
the normalized ruled positive-row energy. -/
theorem rawWhitneyRowEnergy_positive_eq_volume_mul_ruledPositiveRowEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤)
    (s : ℝ) (F : Vec d → Vec d) :
    rawWhitneyRowEnergy system (ruledPositiveWhitneyCellEnergy system s F) =
      volume U * ruledPositiveRowEnergy system s F := by
  let X : ℝ≥0∞ := ∑' i : system.CellIndex,
    ruledScaleWeight system s i *
      ∫⁻ x in system.cell i,
        ENNReal.ofReal (vecNormSq (F x)) ∂volume
  let Y : ℝ≥0∞ := ∑' i : system.CellIndex,
    ∫⁻ z in system.cell i ×ˢ system.cell i,
      whitneyRowFractionalKernel s F z ∂(volume.prod volume)
  have hcancel : volume U * (volume U)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hUpos.ne' hUtop
  calc
    rawWhitneyRowEnergy system (ruledPositiveWhitneyCellEnergy system s F) =
        ∑' i : system.CellIndex,
          (ruledScaleWeight system s i *
              ∫⁻ x in system.cell i,
                ENNReal.ofReal (vecNormSq (F x)) ∂volume +
            ∫⁻ z in system.cell i ×ˢ system.cell i,
              whitneyRowFractionalKernel s F z ∂(volume.prod volume)) := by
      apply tsum_congr
      intro i
      exact volume_mul_positiveWhitneyCellEnergy system s F i
    _ = X + Y := by rw [ENNReal.tsum_add]
    _ = volume U * ruledPositiveRowEnergy system s F := by
      unfold ruledPositiveRowEnergy ruledPositiveRowL2Energy
        ruledPositiveRowGagliardoEnergy
      change X + Y = volume U * ((volume U)⁻¹ * X + (volume U)⁻¹ * Y)
      calc
        X + Y = (volume U * (volume U)⁻¹) * X +
            (volume U * (volume U)⁻¹) * Y := by
          simp only [hcancel, one_mul]
        _ = volume U * ((volume U)⁻¹ * X + (volume U)⁻¹ * Y) := by
          rw [mul_add, mul_assoc, mul_assoc]

/-- The normalized row of expanded ruled-cell squares is exactly the ruled
positive-row energy. -/
theorem normalizedWhitneyRowEnergy_positive_eq_ruledPositiveRowEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤)
    (s : ℝ) (F : Vec d → Vec d) :
    normalizedWhitneyRowEnergy system
        (ruledPositiveWhitneyCellEnergy system s F) =
      ruledPositiveRowEnergy system s F := by
  unfold normalizedWhitneyRowEnergy
  rw [rawWhitneyRowEnergy_positive_eq_volume_mul_ruledPositiveRowEnergy
    system hUpos hUtop]
  rw [← mul_assoc,
    ENNReal.inv_mul_cancel hUpos.ne' hUtop, one_mul]

private theorem aemeasurable_whitneyRowFractionalKernel
    {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict U)) {s : ℝ} (hs : 0 ≤ s) :
    AEMeasurable (whitneyRowFractionalKernel s F)
      ((volume.prod volume).restrict (U ×ˢ U)) := by
  rw [← Measure.prod_restrict]
  have hsub : AEMeasurable (fun z : Vec d × Vec d => F z.1 - F z.2)
      ((volume.restrict U).prod (volume.restrict U)) :=
    hF.aestronglyMeasurable.aemeasurable.comp_fst.sub
      hF.aestronglyMeasurable.aemeasurable.comp_snd
  have hnum : AEMeasurable
      (fun z : Vec d × Vec d => vecNormSq (F z.1 - F z.2))
      ((volume.restrict U).prod (volume.restrict U)) :=
    continuous_vecNormSq.measurable.comp_aemeasurable hsub
  have hp : 0 ≤ (d : ℝ) + 2 * s := by
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  have hdist : Continuous
      (fun z : Vec d × Vec d =>
        Real.sqrt (vecNormSq (z.1 - z.2))) :=
    (continuous_vecNormSq.comp (continuous_fst.sub continuous_snd)).sqrt
  have hden : Measurable
      (fun z : Vec d × Vec d =>
        Real.sqrt (vecNormSq (z.1 - z.2)) ^ ((d : ℝ) + 2 * s)) :=
    (hdist.rpow_const fun _ => Or.inr hp).measurable
  exact (hnum.div hden.aemeasurable).ennreal_ofReal

/-- Exact disjointness bounds the ruled same-cell Gagliardo row by one
global fractional seminorm, with constant one. -/
theorem ruledPositiveRowGagliardoEnergy_le_fracSeminormSq
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤)
    {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U))
    {s : ℝ} (hs : 0 ≤ s) :
    ruledPositiveRowGagliardoEnergy system s F ≤ fracSeminormSq U s F := by
  have hdiag :
      (∑' i : system.CellIndex,
        ∫⁻ z in system.cell i ×ˢ system.cell i,
          whitneyRowFractionalKernel s F z ∂(volume.prod volume)) ≤
        ∫⁻ z in U ×ˢ U,
          whitneyRowFractionalKernel s F z ∂(volume.prod volume) := by
    exact tsum_setLIntegral_prod_self_le
      (ι := system.CellIndex) volume
      (A := fun i => system.cell i) (U := U)
      (fun i => (isOpen_openCubeSet
        (translateCube (system.index i)
          (originCube d (system.scale i)))).measurableSet)
      (fun _ _ hij => system.pairwise_disjoint _ _ hij)
      system.cell_subset
      (whitneyRowFractionalKernel s F)
  have hpair :
      (∫⁻ z in U ×ˢ U,
          whitneyRowFractionalKernel s F z ∂(volume.prod volume)) =
        ∫⁻ x in U, ∫⁻ y in U,
          whitneyRowFractionalKernel s F (x, y) ∂volume :=
    setLIntegral_prod _ (aemeasurable_whitneyRowFractionalKernel hF hs)
  have hraw :
      (∫⁻ x in U, ∫⁻ y in U,
          whitneyRowFractionalKernel s F (x, y) ∂volume) =
        volume U * fracSeminormSq U s F := by
    rw [fracSeminormSq, eVolumeAverage,
      ENNReal.mul_div_cancel hUpos.ne' hUtop]
    rfl
  unfold ruledPositiveRowGagliardoEnergy
  calc
    (volume U)⁻¹ *
        (∑' i : system.CellIndex,
          ∫⁻ z in system.cell i ×ˢ system.cell i,
            whitneyRowFractionalKernel s F z ∂(volume.prod volume)) ≤
        (volume U)⁻¹ *
          (∫⁻ z in U ×ˢ U,
            whitneyRowFractionalKernel s F z ∂(volume.prod volume)) :=
      mul_le_mul_right hdiag _
    _ = (volume U)⁻¹ *
        (volume U * fracSeminormSq U s F) := by rw [hpair, hraw]
    _ = fracSeminormSq U s F := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hUpos.ne' hUtop, one_mul]

/-- The new ruled buffer gives the factor-41 upper comparison between
Euclidean boundary distance and the selected cell scale. -/
theorem euclideanBoundaryDistance_lt_ruledScaleFactor [NeZero d]
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpen U) (i : system.CellIndex) {x : Vec d}
    (hx : x ∈ system.cell i) :
    euclideanBoundaryDistance U x <
      41 * Real.sqrt d * (3 : ℝ) ^ system.scale i := by
  obtain ⟨y, hyFrontier, hxy⟩ :=
    (system.boundaryDistance_compare hU i hx).2
  have hyU : y ∉ U := by
    intro hy
    have : y ∈ U ∩ frontier U := ⟨hy, hyFrontier⟩
    rw [hU.inter_frontier_eq] at this
    exact this
  exact (euclideanBoundaryDistance_le_of_not_mem hyU).trans_lt hxy

@[expose]
public def ruledBoundaryScaleFactor (d : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((41 * Real.sqrt d) ^ (2 * s))

private theorem ruledScaleWeight_le_boundaryWeight [NeZero d]
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U) {s : ℝ} (hs : 0 < s)
    (i : system.CellIndex) {x : Vec d} (hx : x ∈ system.cell i) :
    ruledScaleWeight system s i ≤
      ruledBoundaryScaleFactor d s * euclideanBoundaryWeight U (2 * s) x := by
  let ell : ℝ := (3 : ℝ) ^ system.scale i
  let q : ℝ := 41 * Real.sqrt d
  let delta : ℝ := euclideanBoundaryDistance U x
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hq : 0 < q := mul_pos (by norm_num) hsqrt
  have hell : 0 < ell := by
    dsimp only [ell]
    exact zpow_pos (by norm_num) _
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact euclideanBoundaryDistance_pos
      (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)) hU (system.cell_subset i hx)
  have hupper : delta < q * ell := by
    simpa only [delta, q, ell] using
      euclideanBoundaryDistance_lt_ruledScaleFactor system hU.1 i hx
  have hnegative : -2 * s ≤ 0 := by linarith only [hs]
  have hmono : (q * ell) ^ (-2 * s) ≤ delta ^ (-2 * s) :=
    Real.rpow_le_rpow_of_nonpos hdelta hupper.le hnegative
  have hqcancel : q ^ (2 * s) * q ^ (-2 * s) = 1 := by
    rw [← Real.rpow_add hq]
    ring_nf
    simp only [Real.rpow_zero]
  have hfactor : ell ^ (-2 * s) =
      q ^ (2 * s) * (q * ell) ^ (-2 * s) := by
    rw [Real.mul_rpow hq.le hell.le]
    calc
      ell ^ (-2 * s) = 1 * ell ^ (-2 * s) := by rw [one_mul]
      _ = (q ^ (2 * s) * q ^ (-2 * s)) * ell ^ (-2 * s) := by
        rw [hqcancel, one_mul]
      _ = q ^ (2 * s) * (q ^ (-2 * s) * ell ^ (-2 * s)) := by ring
  unfold ruledScaleWeight ruledBoundaryScaleFactor euclideanBoundaryWeight
  change ENNReal.ofReal (ell ^ (-2 * s)) ≤
    ENNReal.ofReal (q ^ (2 * s)) * ENNReal.ofReal (delta ^ (-(2 * s)))
  rw [hfactor]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _)]
  have hmul := mul_le_mul_right (ENNReal.ofReal_le_ofReal hmono)
    (ENNReal.ofReal (q ^ (2 * s)))
  convert hmul using 1
  ring_nf

private theorem ruledPositiveRowL2Energy_le_boundaryWeightedEnergy
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U) {s : ℝ} (hs : 0 < s)
    (F : Vec d → Vec d) :
    ruledPositiveRowL2Energy system s F ≤
      ruledBoundaryScaleFactor d s *
        euclideanBoundaryWeightedEnergy U (2 * s) F := by
  let f : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (vecNormSq (F x))
  let g : Vec d → ℝ≥0∞ := fun x =>
    euclideanBoundaryWeight U (2 * s) x * f x
  let K : ℝ≥0∞ := ruledBoundaryScaleFactor d s
  have hKtop : K ≠ ∞ := by
    dsimp only [K, ruledBoundaryScaleFactor]
    exact ENNReal.ofReal_ne_top
  have hcell : ∀ i : system.CellIndex,
      ruledScaleWeight system s i *
          ∫⁻ x in system.cell i, f x ∂volume ≤
        K * ∫⁻ x in system.cell i, g x ∂volume := by
    intro i
    have hcellMeas : MeasurableSet (system.cell i) :=
      (isOpen_openCubeSet
        (translateCube (system.index i)
          (originCube d (system.scale i)))).measurableSet
    have hweightTop : ruledScaleWeight system s i ≠ ∞ :=
      ENNReal.ofReal_ne_top
    calc
      ruledScaleWeight system s i *
          ∫⁻ x in system.cell i, f x ∂volume =
          ∫⁻ x in system.cell i,
            ruledScaleWeight system s i * f x ∂volume := by
        exact (lintegral_const_mul' _ _ hweightTop).symm
      _ ≤ ∫⁻ x in system.cell i, K * g x ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hcellMeas] with x hx
        have hw := ruledScaleWeight_le_boundaryWeight system hU hs i hx
        dsimp only [K, g]
        calc
          ruledScaleWeight system s i * f x ≤
              (ruledBoundaryScaleFactor d s *
                euclideanBoundaryWeight U (2 * s) x) * f x := by
            simpa only [mul_comm] using mul_le_mul_right hw (f x)
          _ = ruledBoundaryScaleFactor d s *
              (euclideanBoundaryWeight U (2 * s) x * f x) := by
            rw [mul_assoc]
      _ = K * ∫⁻ x in system.cell i, g x ∂volume := by
        rw [lintegral_const_mul' _ _ hKtop]
  have hsumCells :
      (∑' i : system.CellIndex, ∫⁻ x in system.cell i, g x ∂volume) ≤
        ∫⁻ x in U, g x ∂volume := by
    have hmeas : ∀ i : system.CellIndex, MeasurableSet (system.cell i) :=
      fun i => (isOpen_openCubeSet
        (translateCube (system.index i)
          (originCube d (system.scale i)))).measurableSet
    have hsub : (⋃ i : system.CellIndex, system.cell i) ⊆ U := by
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact system.cell_subset i hxi
    rw [← lintegral_iUnion hmeas system.pairwise_disjoint]
    exact lintegral_mono_set hsub
  unfold ruledPositiveRowL2Energy euclideanBoundaryWeightedEnergy
    eVolumeAverage
  change (volume U)⁻¹ *
      (∑' i : system.CellIndex,
        ruledScaleWeight system s i *
          ∫⁻ x in system.cell i, f x ∂volume) ≤
    K * ((∫⁻ x in U, g x ∂volume) / volume U)
  calc
    (volume U)⁻¹ *
        (∑' i : system.CellIndex,
          ruledScaleWeight system s i *
            ∫⁻ x in system.cell i, f x ∂volume) ≤
        (volume U)⁻¹ *
          (∑' i : system.CellIndex,
            K * ∫⁻ x in system.cell i, g x ∂volume) := by
      exact mul_le_mul_right (ENNReal.tsum_le_tsum hcell) _
    _ = (volume U)⁻¹ *
        (K * ∑' i : system.CellIndex,
          ∫⁻ x in system.cell i, g x ∂volume) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ (volume U)⁻¹ * (K * ∫⁻ x in U, g x ∂volume) := by
      exact mul_le_mul_right (mul_le_mul_right hsumCells K) _
    _ = K * ((∫⁻ x in U, g x ∂volume) / volume U) := by
      rw [div_eq_mul_inv]
      ac_rfl

/-- For fixed dimension, fractional order, and sandwich radii, one finite
coefficient controls the normalized expanded positive row of every ruled
Whitney system by the domain fractional norm square. -/
theorem exists_normalizedRuledPositiveWhitneyRowHsConstant
    (hd : 1 ≤ d) {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hs : 0 < s) (hsHalf : s < 1 / 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad →
        ∀ (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
          (G : Vec d → Vec d),
          Integrable G (volume.restrict U) →
            normalizedWhitneyRowEnergy system
                (ruledPositiveWhitneyCellEnergy system s G) ≤
              C * hsNormSq U s G := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨Ccenter, hCcenterTop, hcenter⟩ :=
    exists_euclideanBoundaryWeightedCenteredEnergy_le_fracSeminormSq_of_integrable
      hd hrho hRad ⟨hs, hsHalf⟩
  let K : ℝ≥0∞ := ruledBoundaryScaleFactor d s
  let M : ℝ≥0∞ :=
    ENNReal.ofReal (((d : ℝ) / rho) ^ (2 * s) / (1 - 2 * s))
  let D : ℝ≥0∞ := 2 * Ccenter + 2 * M
  let A : ℝ≥0∞ := convexHardyPositiveRowHsShapeFactor d Rad s
  let C : ℝ≥0∞ := (K * D + 1) * A
  have hKtop : K ≠ ∞ := by
    dsimp only [K, ruledBoundaryScaleFactor]
    exact ENNReal.ofReal_ne_top
  have hMtop : M ≠ ∞ := by
    dsimp only [M]
    exact ENNReal.ofReal_ne_top
  have hDtop : D ≠ ∞ := by
    dsimp only [D]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num) hCcenterTop,
        ENNReal.mul_ne_top (by norm_num) hMtop⟩
  have hAtop : A ≠ ∞ := by
    dsimp only [A]
    exact convexHardyPositiveRowHsShapeFactor_ne_top hd hs.le Rad
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    exact ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top hKtop hDtop, by norm_num⟩) hAtop
  · intro U hU hsand system G hG
    have hUne : U.Nonempty :=
      ⟨system.center, system.inner_ball
        (center_mem_euclideanBallAt system.center hrho)⟩
    have hUpos : 0 < volume U :=
      volume_pos_of_isOpenBoundedConvexDomain hU hUne
    have hUtop : volume U ≠ ∞ := hU.volume_lt_top.ne
    have hweighted := euclideanBoundaryWeightedEnergy_le_centered_add_explicitMean
      hd hU hsand ⟨hs, hsHalf⟩ hG
    have hcentered := hcenter U hU hsand G hG
    let mean : ℝ≥0∞ := ENNReal.ofReal (vecNormSq (volumeAverageVec U G))
    let frac : ℝ≥0∞ := fracSeminormSq U s G
    have hweightedMain :
        euclideanBoundaryWeightedEnergy U (2 * s) G ≤
          D * (mean + frac) := by
      calc
        euclideanBoundaryWeightedEnergy U (2 * s) G ≤
            2 * euclideanBoundaryWeightedCenteredEnergy U (2 * s) G +
              2 * mean * M := by
          simpa only [mean, M] using hweighted
        _ ≤ 2 * (Ccenter * frac) + 2 * mean * M := by
          exact add_le_add (mul_le_mul_right hcentered 2) le_rfl
        _ ≤ D * frac + D * mean := by
          apply add_le_add
          · have hcoef : 2 * Ccenter ≤ D := by
              dsimp only [D]
              exact le_add_right le_rfl
            calc
              2 * (Ccenter * frac) = (2 * Ccenter) * frac := by
                rw [mul_assoc]
              _ ≤ D * frac := by
                simpa only [mul_comm] using mul_le_mul_right hcoef frac
          · have hcoef : 2 * M ≤ D := by
              dsimp only [D]
              exact le_add_left le_rfl
            calc
              2 * mean * M = (2 * M) * mean := by ac_rfl
              _ ≤ D * mean := by
                simpa only [mul_comm] using mul_le_mul_right hcoef mean
        _ = D * (mean + frac) := by
          calc
            D * frac + D * mean = D * mean + D * frac := add_comm _ _
            _ = D * (mean + frac) := (mul_add _ _ _).symm
    have hL2 : ruledPositiveRowL2Energy system s G ≤
        K * (D * (mean + frac)) :=
      (ruledPositiveRowL2Energy_le_boundaryWeightedEnergy
        system hU hs G).trans (mul_le_mul_right hweightedMain K)
    have hGag : ruledPositiveRowGagliardoEnergy system s G ≤
        mean + frac :=
      (ruledPositiveRowGagliardoEnergy_le_fracSeminormSq
        hUpos hUtop system hG hs.le).trans (le_add_left le_rfl)
    have hrow : ruledPositiveRowEnergy system s G ≤
        (K * D + 1) * (mean + frac) := by
      unfold ruledPositiveRowEnergy
      calc
        ruledPositiveRowL2Energy system s G +
            ruledPositiveRowGagliardoEnergy system s G ≤
            K * (D * (mean + frac)) + (mean + frac) :=
          add_le_add hL2 hGag
        _ = (K * D + 1) * (mean + frac) := by ring
    let oldSystem : ConvexHardyWhitneySystem U rho Rad :=
      Classical.choice (exists_convexHardyWhitneySystem hd hU hsand)
    have habsorb : mean + frac ≤ A * hsNormSq U s G := by
      simpa only [mean, frac, A] using
        oldSystem.mean_add_fracSeminormSq_le_hsNormSq
          hd hRad hUpos hUtop hG hs
    rw [normalizedWhitneyRowEnergy_positive_eq_ruledPositiveRowEnergy
      system hUpos hUtop]
    calc
      ruledPositiveRowEnergy system s G ≤
          (K * D + 1) * (mean + frac) := hrow
      _ ≤ (K * D + 1) * (A * hsNormSq U s G) :=
        mul_le_mul_right habsorb _
      _ = C * hsNormSq U s G := by
        dsimp only [C]
        ac_rfl

end

end HighContrast
end HCPolySupport

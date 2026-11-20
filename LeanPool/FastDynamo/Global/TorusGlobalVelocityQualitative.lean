/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusFullVelocityConcrete
public import LeanPool.FastDynamo.Global.TorusCellAxialPlateauBridge
public import LeanPool.FastDynamo.Global.TorusIocFundamentalBox

/-!
# Qualitative properties of the concrete global velocity

`TorusFullVelocityConcrete` constructs the actual global Fourier-`W^{1,∞}`
graph element and proves reality, the weak derivative identities, transverse
incompressibility, and the literal one-cell formula.  This file records the
remaining elementary qualitative consequences which are visible directly
from the cell geometry.

The main point is nonvanishing.  Halfway from a cell centre to the edge of
its buffer, the local helical copy has already vanished, whereas the axial
cutoff is still identically one.  Thus a positive axial-separation parameter
gives an explicit point at which the full global velocity is exactly the
nonzero vector `a_n e₃`.  No nonvanishing property of the local spectral
seed is used.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Metric Set WithLp
open scoped ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

namespace FullVelocityConcrete

/-! ## The transverse accumulation point -/

/-- The unique transverse accumulation point of the placed cell centres in
the paper's Euclidean chart.  Its product with the axial circle is the
accumulation circle of the three-dimensional construction. -/
def accumulationPoint : ℝ × ℝ := (0, 1 / 2)

/-- The accumulation point `p_∞ = (0, 1/2)` has first coordinate `0` (§3.3). -/
@[simp] theorem accumulationPoint_fst : accumulationPoint.1 = 0 := rfl

/-- The accumulation point `p_∞ = (0, 1/2)` has second coordinate `1/2` (§3.3). -/
@[simp] theorem accumulationPoint_snd : accumulationPoint.2 = 1 / 2 := rfl

/-- The distance from a cell centre to the accumulation point is exactly its
positive first coordinate. -/
theorem dist_cellCenter_accumulationPoint
    (f : ScaleFamily r) (n : ℕ) :
    dist (f.cellCenter n) accumulationPoint = f.cellCenterCoordinate n := by
  rw [Prod.dist_eq]
  simp only [cellCenter_fst, accumulationPoint_fst, dist_zero_right, Real.norm_eq_abs,
    cellCenter_snd, one_div, accumulationPoint_snd, dist_self, abs_nonneg, sup_of_le_left,
    abs_eq_self]
  exact (f.cellCenterCoordinate_pos n).le

/-- The placed centres converge to the paper's accumulation point. -/
theorem tendsto_cellCenter_accumulationPoint (f : ScaleFamily r) :
    Tendsto f.cellCenter atTop (nhds accumulationPoint) := by
  change Tendsto
    (fun n : ℕ ↦ (f.cellCenterCoordinate n, (1 / 2 : ℝ)))
    atTop (nhds ((0 : ℝ), (1 / 2 : ℝ)))
  rw [nhds_prod_eq]
  exact f.tendsto_cellCenterCoordinate_zero.prodMk tendsto_const_nhds

/-- Every point of the `n`th open buffer remains more than `3 R_n` from the
accumulation point.  This is the sharp elementary estimate used in the
paper's quadratic-decay argument. -/
theorem three_mul_bufferRadius_lt_dist_accumulationPoint_of_mem_bufferDisk
    (f : ScaleFamily r) (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∈ f.bufferDisk n) :
    3 * f.bufferRadius n < dist x accumulationPoint := by
  have hxcenter : dist x (f.cellCenter n) < f.bufferRadius n := hx
  have htriangle := dist_triangle (f.cellCenter n) x accumulationPoint
  rw [dist_cellCenter_accumulationPoint, dist_comm (f.cellCenter n) x,
    f.cellCenterCoordinate_recursion n] at htriangle
  linarith [f.cellCenterCoordinate_pos (n + 1)]

/-! ## A canonical point in the axial-only part of each cell -/

/-- The point halfway along the positive first-coordinate radius of the
`n`th buffer.  The local-flow core has radius strictly below `R_n / 10`,
while this point has radius `R_n / 2`. -/
def axialAnnulusWitness
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) : ℝ × ℝ :=
  (P.scaleFamily.cellCenterCoordinate n +
      P.scaleFamily.bufferRadius n / 2,
    1 / 2)

/-- First coordinate of the annular witness: the cell centre's coordinate advanced by `R_n / 2`. -/
@[simp] theorem axialAnnulusWitness_fst
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    (axialAnnulusWitness P n).1 =
      P.scaleFamily.cellCenterCoordinate n +
        P.scaleFamily.bufferRadius n / 2 :=
  rfl

/-- Second coordinate of the annular witness: it lies on the same horizontal line `x_2 = 1/2` as
every cell centre. -/
@[simp] theorem axialAnnulusWitness_snd
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    (axialAnnulusWitness P n).2 = 1 / 2 :=
  rfl

/-- The witness is exactly at pair-distance `R_n / 2` from the cell centre. -/
theorem dist_axialAnnulusWitness_cellCenter
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    dist (axialAnnulusWitness P n) (P.scaleFamily.cellCenter n) =
      P.scaleFamily.bufferRadius n / 2 := by
  rw [Prod.dist_eq]
  change max
    (dist (P.scaleFamily.cellCenterCoordinate n +
      P.scaleFamily.bufferRadius n / 2)
      (P.scaleFamily.cellCenterCoordinate n))
    (dist (1 / 2 : ℝ) (1 / 2 : ℝ)) =
      P.scaleFamily.bufferRadius n / 2
  rw [dist_self, max_eq_left (dist_nonneg : 0 ≤
    dist (P.scaleFamily.cellCenterCoordinate n +
      P.scaleFamily.bufferRadius n / 2)
      (P.scaleFamily.cellCenterCoordinate n))]
  rw [Real.dist_eq]
  simp only [add_sub_cancel_left]
  exact abs_of_nonneg
    (div_nonneg (P.scaleFamily.bufferRadius_nonneg n) (by norm_num))

/-- The witness is at Euclidean distance exactly `R_n / 2` from the cell
centre: it sits on the same horizontal line `x₂ = 1 / 2` as every centre, so
there the Euclidean and product metrics agree. -/
theorem pairEuclideanDist_axialAnnulusWitness_cellCenter
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    pairEuclideanDist (axialAnnulusWitness P n) (P.scaleFamily.cellCenter n) =
      P.scaleFamily.bufferRadius n / 2 := by
  have hsnd : (axialAnnulusWitness P n).2 =
      (P.scaleFamily.cellCenter n).2 := by simp
  have hfst : (axialAnnulusWitness P n).1 - (P.scaleFamily.cellCenter n).1 =
      P.scaleFamily.bufferRadius n / 2 := by simp
  rw [pairEuclideanDist_eq_abs_of_snd_eq hsnd, hfst]
  exact abs_of_nonneg
    (div_nonneg (P.scaleFamily.bufferRadius_nonneg n) (by norm_num))

/-- The axial witness lies outside the much smaller local-flow core. -/
theorem axialAnnulusWitness_not_mem_localCoreDisk
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    axialAnnulusWitness P n ∉
      P.scaleFamily.localCoreDisk supportRadius n := by
  rw [ScaleFamily.localCoreDisk, mem_ball, not_lt,
    dist_axialAnnulusWitness_cellCenter]
  have hfit := P.supportFit n
  linarith [P.scaleFamily.bufferRadius_pos n]

/-- The witness still lies strictly inside the constant axial plateau. -/
theorem axialAnnulusWitness_mem_threeQuarterPlateau
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    pairEuclideanDist (axialAnnulusWitness P n) (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4 := by
  rw [pairEuclideanDist_axialAnnulusWitness_cellCenter]
  linarith [P.scaleFamily.bufferRadius_pos n]

/-- A small open neighbourhood of the annular witness.  The radius `R_n/20`
leaves quantitative room both to the local-flow core and to the edge of the
three-quarter plateau. -/
def axialAnnulusWitnessNeighborhood
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) : Set (ℝ × ℝ) :=
  ball (axialAnnulusWitness P n) (P.scaleFamily.bufferRadius n / 20)

/-- The witness neighbourhood is measurable, being an open ball. -/
theorem measurableSet_axialAnnulusWitnessNeighborhood
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    MeasurableSet (axialAnnulusWitnessNeighborhood P n) :=
  measurableSet_ball

/-- Every point in the witness neighbourhood remains on the axial plateau. -/
theorem pairEuclideanDist_le_three_quarters_of_mem_axialAnnulusWitnessNeighborhood
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {x : ℝ × ℝ} (hx : x ∈ axialAnnulusWitnessNeighborhood P n) :
    pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4 := by
  have htriangle := pairEuclideanDist_triangle x (axialAnnulusWitness P n)
    (P.scaleFamily.cellCenter n)
  have hxw : dist x (axialAnnulusWitness P n) <
      P.scaleFamily.bufferRadius n / 20 := by
    simpa only [axialAnnulusWitnessNeighborhood, mem_ball] using hx
  have hcmp := pairEuclideanDist_le_two_mul_dist x (axialAnnulusWitness P n)
  rw [pairEuclideanDist_axialAnnulusWitness_cellCenter] at htriangle
  linarith [P.scaleFamily.bufferRadius_pos n]

/-- Every point in the witness neighbourhood is outside the local-flow core. -/
theorem not_mem_localCoreDisk_of_mem_axialAnnulusWitnessNeighborhood
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {x : ℝ × ℝ} (hx : x ∈ axialAnnulusWitnessNeighborhood P n) :
    x ∉ P.scaleFamily.localCoreDisk supportRadius n := by
  intro hcore
  have htriangle := dist_triangle (axialAnnulusWitness P n) x
    (P.scaleFamily.cellCenter n)
  have hwx : dist (axialAnnulusWitness P n) x <
      P.scaleFamily.bufferRadius n / 20 := by
    simpa only [axialAnnulusWitnessNeighborhood, mem_ball, dist_comm] using hx
  have hxc : dist x (P.scaleFamily.cellCenter n) <
      supportRadius * P.scaleFamily.ell n := hcore
  rw [dist_axialAnnulusWitness_cellCenter] at htriangle
  have hfit := P.supportFit n
  linarith [P.scaleFamily.bufferRadius_pos n]

/-- The witness neighbourhood lies in the fixed placement chart. -/
theorem axialAnnulusWitnessNeighborhood_subset_placementChart
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    axialAnnulusWitnessNeighborhood P n ⊆ ScaleFamily.placementChart := by
  intro x hx
  exact P.mem_placementChart_of_dist_le_three_quarters n
    (pairEuclideanDist_le_three_quarters_of_mem_axialAnnulusWitnessNeighborhood
      P n hx)

/-- The witness neighbourhood is contained in the canonical half-open
fundamental square used by the measure-preserving torus representative. -/
theorem axialAnnulusWitnessNeighborhood_subset_pairIocFundamentalBox
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    axialAnnulusWitnessNeighborhood P n ⊆
      TorusIocFundamentalBox.pairIocFundamentalBox := by
  intro x hx
  have hchart :=
    axialAnnulusWitnessNeighborhood_subset_placementChart P n hx
  rcases hchart with ⟨⟨hxzero, hxquarter⟩, hyquarter, hythreequarter⟩
  exact ⟨⟨hxzero, by linarith⟩, by constructor <;> linarith⟩

/-- The corresponding positive-measure torus neighbourhood, expressed via
the canonical representative. -/
def torusAxialAnnulusWitnessNeighborhood
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    Set TransverseTorus :=
  transverseIocRepresentative ⁻¹' axialAnnulusWitnessNeighborhood P n

/-- Quotienting the witness neighbourhood into the torus preserves its
Euclidean area exactly. -/
theorem measure_torusAxialAnnulusWitnessNeighborhood
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    transverseMeasure (torusAxialAnnulusWitnessNeighborhood P n) =
      volume (axialAnnulusWitnessNeighborhood P n) := by
  have hmeasure :=
    TorusIocFundamentalBox.measurePreserving_transverseIocRepresentative
      |>.measure_preimage
        (measurableSet_axialAnnulusWitnessNeighborhood P n).nullMeasurableSet
  have hinter : axialAnnulusWitnessNeighborhood P n ∩
      TorusIocFundamentalBox.pairIocFundamentalBox =
        axialAnnulusWitnessNeighborhood P n :=
    Set.inter_eq_left.mpr
      (axialAnnulusWitnessNeighborhood_subset_pairIocFundamentalBox P n)
  rw [Measure.restrict_apply
      (measurableSet_axialAnnulusWitnessNeighborhood P n), hinter] at hmeasure
  exact hmeasure

/-- The torus witness neighbourhood has strictly positive measure. -/
theorem measure_torusAxialAnnulusWitnessNeighborhood_pos
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    0 < transverseMeasure (torusAxialAnnulusWitnessNeighborhood P n) := by
  rw [measure_torusAxialAnnulusWitnessNeighborhood P n]
  exact measure_ball_pos volume (axialAnnulusWitness P n)
    (div_pos (P.scaleFamily.bufferRadius_pos n) (by norm_num))

/-! ## Exact local-copy formulae -/

/-- The literal real representative of the full global velocity. -/
def parameterizedFullGlobalRealTorusSource
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (q : TransverseTorus) : R3 :=
  parameterizedHelicalGlobalRealTorusSource h P angularSpeed axialSpeed q +
    P.axialOffsetGlobalTorus tau q

/-- The value stored in the full global `W¹⁻∞` graph has the preceding
literal real representative almost everywhere. -/
theorem transverseW1InfValue_parameterizedFullGlobalW1Inf_eq_realSource_ae
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (htau : 0 ≤ tau) :
    (transverseW1InfValue (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau) : TransverseTorus → R3)
      =ᵐ[transverseMeasure]
        parameterizedFullGlobalRealTorusSource
          h P angularSpeed axialSpeed tau := by
  filter_upwards [
    transverseW1InfValue_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau] with q hq
  simpa only [parameterizedFullGlobalRealTorusSource] using hq

/-- On a local-flow core, the full global source is exactly the
paper's translated and rescaled reference profile (`eq:local-copy`) plus the constant axial shift.
This expands the certificate-valued statement in
`parameterizedFullGlobalTorusSource_eq_cell_add_axialShift_of_mem_core` to
the displayed formula `ell_n v((x-p_n)/ell_n) + a_n e₃`. -/
theorem parameterizedFullGlobalTorusSource_eq_rescaledLocalCopy_add_axialShift_of_mem_core
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint x) =
      P.scaleFamily.ell n •
          parameterizedSmoothedVelocity h angularSpeed axialSpeed
            (helicalCellCoordinate h P n x) +
        complexifyR3
          (P.scaleFamily.axialAmplitude tau n • axialUnitR3) := by
  have hxbuffer : x ∈ P.scaleFamily.bufferDisk n :=
    P.localCoreDisk_subset_bufferDisk n hx
  have hchart : x ∈ ScaleFamily.placementChart :=
    P.bufferDisk_subset_chart n hxbuffer
  have hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨hchart.1.1, by linarith [hchart.1.2]⟩
  have hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨by linarith [hchart.2.1], by linarith [hchart.2.2]⟩
  rw [parameterizedFullGlobalTorusSource_eq_cell_add_axialShift_of_mem_core
    h P angularSpeed axialSpeed tau n hx,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource_transverseTorusPoint_eq_source_of_mem_Ioc
        hxzero hxone]
  rfl

/-- On the local-flow core, each displayed transverse derivative of the full
global source is exactly the corresponding derivative of the rescaled local
copy.  The amplitude/dilation factors in the local copy have cancelled, and
the axial cutoff has zero derivative on its plateau. -/
theorem parameterizedFullGlobalTorusFirstDerivative_eq_rescaledLocalCopy_of_mem_core
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) (j : Fin 2)
    {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    parameterizedFullGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed tau j (transverseTorusPoint x) =
      parameterizedHelicalCellSourceDeriv
        h P angularSpeed axialSpeed n j x := by
  have hxbuffer : x ∈ P.scaleFamily.bufferDisk n :=
    P.localCoreDisk_subset_bufferDisk n hx
  have hqbuffer : transverseTorusPoint x ∈ P.torusBufferDisk n :=
    ⟨x, hxbuffer, rfl⟩
  have hplateau : pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4 := by
    have hcore : dist x (P.scaleFamily.cellCenter n) <
        (1 + (h : ℝ)) * P.scaleFamily.ell n := hx
    have hfit := P.supportFit n
    have hcmp :=
      pairEuclideanDist_le_two_mul_dist x (P.scaleFamily.cellCenter n)
    linarith [P.scaleFamily.bufferRadius_pos n]
  have hchart : x ∈ ScaleFamily.placementChart :=
    P.bufferDisk_subset_chart n hxbuffer
  have hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨hchart.1.1, by linarith [hchart.1.2]⟩
  have hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨by linarith [hchart.2.1], by linarith [hchart.2.2]⟩
  let certificate := parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed n
  have hderivative :=
    certificate.torusFirstDerivative_transverseTorusPoint_eq_firstDerivative_of_mem_Ioc
      j hxzero hxone
  rw [parameterizedFullGlobalTorusFirstDerivative,
    parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hqbuffer j,
    P.axialOffsetGlobalTorusDerivative_eq_cell_of_mem_buffer tau hqbuffer j, hderivative,
    P.axialOffsetTorusDerivative_eq_zero_of_dist_le_three_quarters tau n j hplateau,
    map_zero, add_zero]
  rfl

/-- Anywhere in the three-quarter axial plateau but outside the local-flow
core, the full global field is exactly the constant axial shift.  This is
the open region used in the paper's proof that the velocity is nonzero. -/
theorem parameterizedFullGlobalTorusSource_eq_axialShift_of_mem_plateau_of_not_mem_core
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) {x : ℝ × ℝ}
    (hplateau : pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4)
    (hcore : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint x) =
      complexifyR3
        (P.scaleFamily.axialAmplitude tau n • axialUnitR3) := by
  have hxbuffer : x ∈ P.scaleFamily.bufferDisk n :=
    P.mem_bufferDisk_of_dist_le_three_quarters n hplateau
  have hqbuffer : transverseTorusPoint x ∈ P.torusBufferDisk n :=
    ⟨x, hxbuffer, rfl⟩
  have hqcore : transverseTorusPoint x ∉ P.torusLocalCoreDisk n := by
    intro hmem
    obtain ⟨y, hycore, hyq⟩ := hmem
    have hybuffer : y ∈ P.scaleFamily.bufferDisk n :=
      P.localCoreDisk_subset_bufferDisk n hycore
    have hxy : y = x :=
      transverseTorusPoint_injectiveOn_placementChart
        (P.bufferDisk_subset_chart n hybuffer)
        (P.bufferDisk_subset_chart n hxbuffer) hyq
    exact hcore (hxy ▸ hycore)
  rw [parameterizedFullGlobalTorusSource,
    parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hqbuffer,
    P.axialOffsetGlobalTorus_eq_cell_of_mem_buffer tau hqbuffer,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
        hqcore,
    P.axialOffsetTorus_eq_axialAmplitude_of_core tau n hplateau,
    zero_add]

/-- Real-representative version of the preceding axial-only plateau formula. -/
theorem parameterizedFullGlobalRealTorusSource_eq_axialShift_of_mem_plateau_of_not_mem_core
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) {x : ℝ × ℝ}
    (hplateau : pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4)
    (hcore : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint x) =
      P.scaleFamily.axialAmplitude tau n • axialUnitR3 := by
  have hxbuffer : x ∈ P.scaleFamily.bufferDisk n :=
    P.mem_bufferDisk_of_dist_le_three_quarters n hplateau
  have hqbuffer : transverseTorusPoint x ∈ P.torusBufferDisk n :=
    ⟨x, hxbuffer, rfl⟩
  have hqcore : transverseTorusPoint x ∉ P.torusLocalCoreDisk n := by
    intro hmem
    obtain ⟨y, hycore, hyq⟩ := hmem
    have hybuffer : y ∈ P.scaleFamily.bufferDisk n :=
      P.localCoreDisk_subset_bufferDisk n hycore
    have hxy : y = x :=
      transverseTorusPoint_injectiveOn_placementChart
        (P.bufferDisk_subset_chart n hybuffer)
        (P.bufferDisk_subset_chart n hxbuffer) hyq
    exact hcore (hxy ▸ hycore)
  rw [parameterizedFullGlobalRealTorusSource,
    parameterizedHelicalGlobalRealTorusSource,
    parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hqbuffer,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
        hqcore,
    P.axialOffsetGlobalTorus_eq_cell_of_mem_buffer tau hqbuffer,
    P.axialOffsetTorus_eq_axialAmplitude_of_core tau n hplateau]
  apply PiLp.ext
  intro i
  simp [vecRe]

/-- The full real representative is constant and purely axial throughout
the positive-measure witness neighbourhood. -/
theorem parameterizedFullGlobalRealTorusSource_eq_axialShift_of_mem_witnessNeighborhood
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) {q : TransverseTorus}
    (hq : q ∈ torusAxialAnnulusWitnessNeighborhood P n) :
    parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau q =
      P.scaleFamily.axialAmplitude tau n • axialUnitR3 := by
  let x := transverseIocRepresentative q
  have hx : x ∈ axialAnnulusWitnessNeighborhood P n := hq
  rw [← transverseTorusPoint_transverseIocRepresentative q]
  exact
    parameterizedFullGlobalRealTorusSource_eq_axialShift_of_mem_plateau_of_not_mem_core
      h P angularSpeed axialSpeed tau n
        (pairEuclideanDist_le_three_quarters_of_mem_axialAnnulusWitnessNeighborhood
          P n hx)
        (not_mem_localCoreDisk_of_mem_axialAnnulusWitnessNeighborhood P n hx)

/-- At the canonical annular witness, the global field is exactly `a_n e₃`. -/
theorem parameterizedFullGlobalTorusSource_at_axialAnnulusWitness
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint (axialAnnulusWitness P n)) =
      complexifyR3
        (P.scaleFamily.axialAmplitude tau n • axialUnitR3) :=
  parameterizedFullGlobalTorusSource_eq_axialShift_of_mem_plateau_of_not_mem_core
    h P angularSpeed axialSpeed tau n
      (axialAnnulusWitness_mem_threeQuarterPlateau P n)
      (axialAnnulusWitness_not_mem_localCoreDisk P n)

/-! ## Nonvanishing -/

/-- For positive `tau`, the paper's constant axial shift in every cell
is a nonzero real vector. -/
theorem axialAmplitude_smul_axialUnitR3_ne_zero
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius)
    {tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    P.scaleFamily.axialAmplitude tau n • axialUnitR3 ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  have hamp : 0 < P.scaleFamily.axialAmplitude tau n :=
    P.scaleFamily.axialAmplitude_pos htau n
  rw [norm_smul, norm_axialUnitR3, mul_one, Real.norm_eq_abs,
    abs_of_pos hamp, norm_zero] at hnorm
  exact hamp.ne' hnorm

/-- A positive axial separation parameter makes the value at every canonical
annular witness nonzero. -/
theorem parameterizedFullGlobalTorusSource_at_axialAnnulusWitness_ne_zero
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) {tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint (axialAnnulusWitness P n)) ≠ 0 := by
  rw [parameterizedFullGlobalTorusSource_at_axialAnnulusWitness]
  intro hzero
  have hcoord := congrArg (fun z : C3 ↦ z (2 : Fin 3)) hzero
  have hamp : 0 < P.scaleFamily.axialAmplitude tau n :=
    P.scaleFamily.axialAmplitude_pos htau n
  have hampzero : P.scaleFamily.axialAmplitude tau n = 0 := by
    exact_mod_cast (by
      simpa [complexifyR3_apply, axialUnitR3] using hcoord)
  exact hamp.ne' hampzero

/-- Consequently the literal full global torus source is not the zero
function.  This is the pointwise nonvanishing clause of the paper's
global-velocity lemma. -/
theorem parameterizedFullGlobalTorusSource_ne_zero
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) {tau : ℝ} (htau : 0 < tau) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau ≠ 0 := by
  intro hzero
  have hat := congrFun hzero
    (transverseTorusPoint (axialAnnulusWitness P 0))
  exact parameterizedFullGlobalTorusSource_at_axialAnnulusWitness_ne_zero
    h P angularSpeed axialSpeed htau 0 hat

/-- The actual quotient `W¹⁻∞` global velocity is nonzero for every
positive axial-separation parameter.  Unlike point evaluation, this statement
about an `L∞` equivalence class needs a positive-measure region; the explicit
witness neighbourhood above supplies it. -/
theorem parameterizedFullGlobalW1Inf_ne_zero
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) {tau : ℝ} (htau : 0 < tau) :
    parameterizedFullGlobalW1Inf
      h P angularSpeed axialSpeed tau htau.le ≠ 0 := by
  intro hzero
  have hrepresentative :=
    transverseW1InfValue_parameterizedFullGlobalW1Inf_eq_realSource_ae
      h P angularSpeed axialSpeed tau htau.le
  rw [hzero] at hrepresentative
  have hsourceZero : ∀ᵐ q ∂transverseMeasure,
      parameterizedFullGlobalRealTorusSource
        h P angularSpeed axialSpeed tau q = 0 := by
    filter_upwards [hrepresentative] with q hq
    simpa using hq.symm
  have hsetNe : transverseMeasure
      (torusAxialAnnulusWitnessNeighborhood P 0) ≠ 0 :=
    ne_of_gt (measure_torusAxialAnnulusWitnessNeighborhood_pos P 0)
  obtain ⟨q, hqmem, hqzero⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hsetNe
      (ae_restrict_of_ae hsourceZero)
  rw [parameterizedFullGlobalRealTorusSource_eq_axialShift_of_mem_witnessNeighborhood
    h P angularSpeed axialSpeed tau 0 hqmem] at hqzero
  exact axialAmplitude_smul_axialUnitR3_ne_zero P htau 0 hqzero

/-! ## The Euclidean cell sum at the accumulation point -/

/-- One combined real cell before quotienting the placement chart. -/
def parameterizedFullEuclideanCellRealSource
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) (x : ℝ × ℝ) : R3 :=
  vecRe (parameterizedHelicalCellSource
      h P angularSpeed axialSpeed n x) +
    P.axialOffsetEuclidean tau n x

/-- A combined Euclidean cell vanishes off its buffer. -/
theorem parameterizedFullEuclideanCellRealSource_eq_zero_of_not_mem_bufferDisk
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.bufferDisk n) :
    parameterizedFullEuclideanCellRealSource
      h P angularSpeed axialSpeed tau n x = 0 := by
  have hcore : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n :=
    fun hmem ↦ hx (P.localCoreDisk_subset_bufferDisk n hmem)
  rw [parameterizedFullEuclideanCellRealSource,
    parameterizedHelicalCellSource_eq_zero_of_not_mem_localCoreDisk
      h P angularSpeed axialSpeed n hcore,
    P.axialOffsetEuclidean_eq_zero_of_not_mem_bufferDisk tau n hx]
  apply PiLp.ext
  intro i
  simp [vecRe]

/-- A combined cell is zero on every distinct buffer. -/
theorem parameterizedFullEuclideanCellRealSource_eq_zero_on_distinct_buffer
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) {m n : ℕ} (hmn : m ≠ n)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk n) :
    parameterizedFullEuclideanCellRealSource
      h P angularSpeed axialSpeed tau m x = 0 := by
  apply parameterizedFullEuclideanCellRealSource_eq_zero_of_not_mem_bufferDisk
  intro hm
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hlt)) hm hx
  · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hgt)) hx hm

/-- The paper's pointwise Euclidean cell sum.  This is the chart-side
representative whose cells accumulate at `accumulationPoint`. -/
def parameterizedFullGlobalEuclideanRealSource
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) (x : ℝ × ℝ) : R3 :=
  ∑' n : ℕ,
    parameterizedFullEuclideanCellRealSource
      h P angularSpeed axialSpeed tau n x

/-- Inside a buffer, the Euclidean global sum is exactly its unique cell. -/
theorem parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau x =
      parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n x := by
  unfold parameterizedFullGlobalEuclideanRealSource
  exact tsum_eq_single n fun m hmn ↦
    parameterizedFullEuclideanCellRealSource_eq_zero_on_distinct_buffer
      h P angularSpeed axialSpeed tau hmn hx

/-- Outside all buffers, the Euclidean global sum vanishes. -/
theorem parameterizedFullGlobalEuclideanRealSource_eq_zero_of_outside_buffers
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed tau : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) :
    parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau x = 0 := by
  unfold parameterizedFullGlobalEuclideanRealSource
  simp_rw [parameterizedFullEuclideanCellRealSource_eq_zero_of_not_mem_bufferDisk
    h P angularSpeed axialSpeed tau _ (hx _)]
  exact tsum_zero

/-- A single combined cell has the paper's `O(ell_n)` amplitude. -/
theorem norm_parameterizedFullEuclideanCellRealSource_le
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) {tau : ℝ} (htau : 0 ≤ tau)
    (n : ℕ) (x : ℝ × ℝ) :
    ‖parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n x‖ ≤
      (parameterizedHelicalValueBound h angularSpeed axialSpeed +
          tau / p.wavenumber) * P.scaleFamily.ell n := by
  calc
    ‖parameterizedFullEuclideanCellRealSource
        h P angularSpeed axialSpeed tau n x‖ ≤
        ‖vecRe (parameterizedHelicalCellSource
          h P angularSpeed axialSpeed n x)‖ +
          ‖P.axialOffsetEuclidean tau n x‖ := by
      exact norm_add_le _ _
    _ ≤ parameterizedHelicalValueBound h angularSpeed axialSpeed *
          P.scaleFamily.ell n +
        P.scaleFamily.axialAmplitude tau n :=
      add_le_add
        ((norm_vecRe_le _).trans
          (norm_parameterizedHelicalCellSource_le
            h P angularSpeed axialSpeed n x))
        (P.norm_axialOffsetEuclidean_le htau n x)
    _ = (parameterizedHelicalValueBound h angularSpeed axialSpeed +
          tau / p.wavenumber) * P.scaleFamily.ell n := by
      unfold ScaleFamily.axialAmplitude
      ring

/-- The Euclidean global source obeys the paper's quadratic decay at
the accumulation point.  The identity `ell_n = R_n²` and the separation
`dist(x,p_∞) > 3R_n` are the only geometric inputs. -/
theorem norm_parameterizedFullGlobalEuclideanRealSource_le_dist_sq
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) {tau : ℝ} (htau : 0 ≤ tau)
    (x : ℝ × ℝ) :
    ‖parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau x‖ ≤
      (parameterizedHelicalValueBound h angularSpeed axialSpeed +
          tau / p.wavenumber) * dist x accumulationPoint ^ 2 := by
  have hconstant : 0 ≤
      parameterizedHelicalValueBound h angularSpeed axialSpeed +
        tau / p.wavenumber :=
    add_nonneg
      (parameterizedHelicalValueBound_nonneg h angularSpeed axialSpeed)
      (div_nonneg htau p.wavenumber_pos.le)
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
      h P angularSpeed axialSpeed tau hn]
    have hsep :=
      three_mul_bufferRadius_lt_dist_accumulationPoint_of_mem_bufferDisk
        P.scaleFamily n hn
    have hRle : P.scaleFamily.bufferRadius n ≤
        dist x accumulationPoint := by
      nlinarith [P.scaleFamily.bufferRadius_pos n]
    have hsquare : P.scaleFamily.bufferRadius n ^ 2 ≤
        dist x accumulationPoint ^ 2 :=
      (sq_le_sq₀ (P.scaleFamily.bufferRadius_nonneg n)
        (dist_nonneg : 0 ≤ dist x accumulationPoint)).2 hRle
    calc
      ‖parameterizedFullEuclideanCellRealSource
          h P angularSpeed axialSpeed tau n x‖ ≤
          (parameterizedHelicalValueBound h angularSpeed axialSpeed +
            tau / p.wavenumber) * P.scaleFamily.ell n :=
        norm_parameterizedFullEuclideanCellRealSource_le
          h P angularSpeed axialSpeed htau n x
      _ = (parameterizedHelicalValueBound h angularSpeed axialSpeed +
            tau / p.wavenumber) * P.scaleFamily.bufferRadius n ^ 2 := by
        rw [P.scaleFamily.bufferRadius_sq n]
      _ ≤ (parameterizedHelicalValueBound h angularSpeed axialSpeed +
            tau / p.wavenumber) * dist x accumulationPoint ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hconstant
  · push Not at hbuffer
    rw [parameterizedFullGlobalEuclideanRealSource_eq_zero_of_outside_buffers
      h P angularSpeed axialSpeed tau hbuffer, norm_zero]
    exact mul_nonneg hconstant (sq_nonneg _)

/-- The Euclidean cell sum is Fréchet differentiable at the accumulation
point, with derivative zero.  This formalises the quadratic-decay step of
the paper's global-velocity lemma in the actual placement chart. -/
theorem parameterizedFullGlobalEuclideanRealSource_hasFDerivAt_accumulationPoint
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) {tau : ℝ} (htau : 0 ≤ tau) :
    HasFDerivAt
      (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau)
      (0 : (ℝ × ℝ) →L[ℝ] R3) accumulationPoint := by
  let C := parameterizedHelicalValueBound h angularSpeed axialSpeed +
    tau / p.wavenumber
  have hbigO :
      parameterizedFullGlobalEuclideanRealSource
          h P angularSpeed axialSpeed tau =O[nhds accumulationPoint]
        fun x : ℝ × ℝ ↦ ‖x - accumulationPoint‖ ^ 2 := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [] with x
    have hbound :=
      norm_parameterizedFullGlobalEuclideanRealSource_le_dist_sq
        h P angularSpeed axialSpeed htau x
    simpa only [C, dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖x - accumulationPoint‖)] using hbound
  exact hbigO.hasFDerivAt (by norm_num)

/-- In particular, the chart-side global field is differentiable at the
accumulation point. -/
theorem parameterizedFullGlobalEuclideanRealSource_differentiableAt_accumulationPoint
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) {tau : ℝ} (htau : 0 ≤ tau) :
    DifferentiableAt ℝ
      (parameterizedFullGlobalEuclideanRealSource
        h P angularSpeed axialSpeed tau) accumulationPoint :=
  (parameterizedFullGlobalEuclideanRealSource_hasFDerivAt_accumulationPoint
    h P angularSpeed axialSpeed htau).differentiableAt

end FullVelocityConcrete

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

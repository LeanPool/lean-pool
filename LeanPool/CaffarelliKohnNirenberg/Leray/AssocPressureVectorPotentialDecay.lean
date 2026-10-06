/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressurePotentialDecayBase
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressurePotentialDecayEstimates
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed

/-!
# Assoc Pressure Vector Potential Decay

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The componentwise time derivative of a vector test on product
space-time coordinates. -/
@[expose]
def associatedPressureVectorTimePartial
    (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 :=
  fun z i => CKN.timePartial (fun w : Vec3 × ℝ => φ w i) z

@[expose]
def associatedPressureCurlSourceTest
    (φ : Vec3 × ℝ → Vec3) (j : Fin 3) : Vec3 × ℝ → Vec3 :=
  fun z i =>
    if j = 0 then
      if i = 1 then -φ z 2 else if i = 2 then φ z 1 else 0
    else if j = 1 then
      if i = 0 then φ z 2 else if i = 2 then -φ z 0 else 0
    else
      if i = 0 then -φ z 1 else if i = 1 then φ z 0 else 0

private theorem associatedPressureVectorComponent_tsupport_subset
    (φ : Vec3 × ℝ → Vec3) (i : Fin 3) :
    tsupport (fun z : Vec3 × ℝ => φ z i) ⊆ tsupport φ := by
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro z hz
  by_contra hnot
  have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hnot
  exact hz (by simp [hzero])

/-- The time derivative of a compact space-time test field remains in the
same compact test class. -/
theorem associatedPressureVectorTimePartial_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    associatedPressureVectorTimePartial φ ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
  have hcomponent (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hφ i
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureVectorTimePartial φ) := by
    apply contDiff_pi.2
    intro i
    exact CKN.contDiff_timePartial (hcomponent i).1
  have hcompact : HasCompactSupport (associatedPressureVectorTimePartial φ) :=
    HasCompactSupport.of_support_subset_isCompact hφ.2.1.isCompact (by
      intro z hz
      by_contra hnot
      apply hz
      funext i
      have hnotComponent : z ∉ tsupport (fun w : Vec3 × ℝ => φ w i) := by
        intro hzComponent
        exact hnot (associatedPressureVectorComponent_tsupport_subset φ i hzComponent)
      exact CKN.timePartial_eq_zero_off_tsupport hnotComponent)
  have hsupport : Function.support (associatedPressureVectorTimePartial φ) ⊆
      tsupport φ := by
    intro z hz
    by_contra hnot
    apply hz
    funext i
    have hnotComponent : z ∉ tsupport (fun w : Vec3 × ℝ => φ w i) := by
      intro hzComponent
      exact hnot (associatedPressureVectorComponent_tsupport_subset φ i hzComponent)
    exact CKN.timePartial_eq_zero_off_tsupport hnotComponent
  have htsupport : tsupport (associatedPressureVectorTimePartial φ) ⊆ tsupport φ :=
    closure_minimal hsupport (isClosed_tsupport φ)
  exact ⟨hcont, hcompact, htsupport.trans hφ.2.2⟩

private theorem associatedPressureCurlSourceTest_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (j : Fin 3) :
    associatedPressureCurlSourceTest φ j ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
  have hcomponent (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hφ i
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (associatedPressureCurlSourceTest φ j) := by
    apply contDiff_pi.2
    intro i
    fin_cases j <;> fin_cases i <;>
      simp only [associatedPressureCurlSourceTest, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Fin.reduceFinMk] <;>
      first
      | exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : Vec3 × ℝ => (0 : ℝ)))
      | exact (hcomponent 0).1
      | exact (hcomponent 0).1.neg
      | exact (hcomponent 1).1
      | exact (hcomponent 1).1.neg
      | exact (hcomponent 2).1
      | exact (hcomponent 2).1.neg
  have hcompact : HasCompactSupport (associatedPressureCurlSourceTest φ j) :=
    HasCompactSupport.of_support_subset_isCompact hφ.2.1.isCompact (by
      intro z hz
      by_contra hnot
      apply hz
      have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hnot
      funext i
      simp [associatedPressureCurlSourceTest, hzero])
  have hsupport : Function.support (associatedPressureCurlSourceTest φ j) ⊆
      tsupport φ := by
    intro z hz
    by_contra hnot
    apply hz
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hnot
    funext i
    simp [associatedPressureCurlSourceTest, hzero]
  have htsupport : tsupport (associatedPressureCurlSourceTest φ j) ⊆ tsupport φ :=
    closure_minimal hsupport (isClosed_tsupport φ)
  exact ⟨hcont, hcompact, htsupport.trans hφ.2.2⟩

/-- Time differentiation commutes with the scalar Helmholtz potential. -/
theorem associatedPressureHelmholtzScalarPotential_timePartial
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (z : Vec3 × ℝ) :
    CKN.timePartial (associatedPressureHelmholtzScalarPotential φ) z =
      associatedPressureHelmholtzScalarPotential
        (associatedPressureVectorTimePartial φ) z := by
  have hdiv := associatedPressureTestDivergence_contDiff hφ
  have hdivc := associatedPressureTestDivergence_hasCompactSupport hφ
  have hdivTime :
      (fun q : Vec3 × ℝ =>
        CKN.timePartial (show ParabolicPoint → ℝ from
          associatedPressureTestDivergence φ) q) =
        associatedPressureTestDivergence (associatedPressureVectorTimePartial φ) := by
    funext q
    let f : Fin 3 → Vec3 × ℝ → ℝ := fun i w =>
      CKN.spatialPartialProd (fun y : Vec3 × ℝ => φ y i) i w
    have hsum := timePartial_finsetSum_at (Finset.univ : Finset (Fin 3)) f
      (z := q) (by
        intro i hi
        have hfi : ContDiff ℝ (⊤ : ℕ∞) (f i) := by
          have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => φ w i) :=
            (CKN.component_mem_spaceTimeTestFunction hφ i).1
          exact CKN.spatialPartial_contDiff hφi i
        exact (hfi.differentiable (by simp) q))
    have hsum' : CKN.timePartial (associatedPressureTestDivergence φ) q =
        ∑ i : Fin 3, CKN.timePartial (f i) q := by
      change CKN.timePartial
          (fun w : ParabolicPoint => ∑ i : Fin 3,
            CKN.spatialPartialProd (fun y : Vec3 × ℝ => φ y i) i w) q = _
      simpa only [f] using hsum
    rw [hsum']
    unfold associatedPressureTestDivergence
    apply Finset.sum_congr rfl
    intro i hi
    exact timePartial_spatialPartial_comm
      ((CKN.component_mem_spaceTimeTestFunction hφ i).1) q i
  rw [associatedPressureHelmholtzScalarPotential,
    associatedPressureHelmholtzScalarPotential,
    associatedPressureNewtonianPotential_timePartial hdiv hdivc z, hdivTime]

private theorem associatedPressureHelmholtzVectorComponent_eq_scalarPotential
    {φ : Vec3 × ℝ → Vec3}
    (j : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureHelmholtzVectorPotential φ z j =
      associatedPressureHelmholtzScalarPotential
        (associatedPressureCurlSourceTest φ j) z := by
  have hdiv : associatedPressureTestDivergence
      (associatedPressureCurlSourceTest φ j) =
        fun q => -associatedPressureTestCurlComponent φ j q := by
    funext q
    fin_cases j <;>
      simp [associatedPressureTestDivergence,
        associatedPressureTestCurlComponent,
        associatedPressureCurlSourceTest, Fin.sum_univ_three,
        CKN.spatialPartialProd, CKN.spatialPartial] <;> ring
  rw [associatedPressureHelmholtzScalarPotential, hdiv,
    associatedPressureNewtonianPotential_neg]
  rfl

/-- Each component of the Helmholtz vector potential and its time derivative
has the uniform decay required for spatial cutoff limits in
`thm:assoc-pressure`. -/
theorem associatedPressureHelmholtzVectorPotential_component_decay
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (j : Fin 3) :
    RieszPressurePotentialDecay (fun z => associatedPressureHelmholtzVectorPotential φ z j) ∧
    RieszPressurePotentialDecay (fun z =>
      CKN.timePartial
        (fun w : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ w j) z) := by
  let η := associatedPressureCurlSourceTest φ j
  have hη := associatedPressureCurlSourceTest_mem_spaceTimeTestFunction hφ j
  have hηt := associatedPressureVectorTimePartial_mem_spaceTimeTestFunction hη
  have hvec : (fun z => associatedPressureHelmholtzVectorPotential φ z j) =
      associatedPressureHelmholtzScalarPotential η := by
    funext z
    exact associatedPressureHelmholtzVectorComponent_eq_scalarPotential j z
  have htime : (fun z =>
      CKN.timePartial
        (fun w : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ w j) z) =
      associatedPressureHelmholtzScalarPotential
        (associatedPressureVectorTimePartial η) := by
    funext z
    have hvec' :
        (fun w : ParabolicPoint =>
          associatedPressureHelmholtzVectorPotential φ (show Vec3 × ℝ from w) j) =
        (fun w : ParabolicPoint =>
          associatedPressureHelmholtzScalarPotential η (show Vec3 × ℝ from w)) := by
      funext w
      exact congrFun hvec (show Vec3 × ℝ from w)
    change CKN.timePartial
      (fun w : ParabolicPoint =>
        associatedPressureHelmholtzVectorPotential φ (show Vec3 × ℝ from w) j) z = _
    calc
      _ = CKN.timePartial
          (fun w : ParabolicPoint =>
            associatedPressureHelmholtzScalarPotential η (show Vec3 × ℝ from w)) z :=
        congrArg (fun f : ParabolicPoint → ℝ => CKN.timePartial f z) hvec'
      _ = associatedPressureHelmholtzScalarPotential
          (associatedPressureVectorTimePartial η) z :=
        associatedPressureHelmholtzScalarPotential_timePartial hη z
  constructor
  · exact hvec ▸ associatedPressureHelmholtzScalarPotential_decay hη
  · exact htime ▸ associatedPressureHelmholtzScalarPotential_decay hηt

end CKN.Leray

end

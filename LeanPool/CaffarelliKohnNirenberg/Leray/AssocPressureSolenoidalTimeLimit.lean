/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalCore

/-!
# Solenoidal cutoff time limits

Time differentiation and convergence for the Helmholtz cutoff curl.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- The componentwise time derivative of the Helmholtz vector potential. -/
@[expose]
def associatedPressureHelmholtzVectorPotentialTimePartial
    (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 :=
  fun z i => CKN.timePartial
    (fun w : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ w i) z

private theorem associatedPressureHelmholtzCutoffPotential_timePartial
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.timePartial
      (fun w : Vec3 × ℝ =>
        associatedPressureHelmholtzCutoffVectorPotential φ n w i) z =
      rieszPressurePotentialCutoff n z.1 *
        associatedPressureHelmholtzVectorPotentialTimePartial φ z i := by
  let A : Vec3 × ℝ → ℝ := fun q => associatedPressureHelmholtzVectorPotential φ q i
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    exact (contDiff_apply ℝ ℝ i).comp
      (associatedPressureHelmholtzVectorPotential_contDiff hφ)
  have htimeA : DifferentiableAt ℝ (fun t : ℝ => A (z.1, t)) z.2 := by
    exact ((hA.differentiable (by simp)).differentiableAt).comp z.2 (by fun_prop)
  have hcut : (fun t : ℝ =>
      associatedPressureHelmholtzCutoffVectorPotential φ n (z.1, t) i) =
      (fun _ : ℝ => rieszPressurePotentialCutoff n z.1) *
        (fun t => A (z.1, t)) := by
    funext t
    simp [A, associatedPressureHelmholtzCutoffVectorPotential, smul_eq_mul]
  have hconst : DifferentiableAt ℝ
      (fun _ : ℝ => rieszPressurePotentialCutoff n z.1) z.2 :=
    differentiableAt_const _
  change (fderiv ℝ
      (fun t : ℝ => associatedPressureHelmholtzCutoffVectorPotential φ n
        (z.1, t) i) z.2) 1 = _
  rw [hcut, fderiv_mul hconst htimeA]
  simp [A, CKN.timePartial, associatedPressureHelmholtzVectorPotentialTimePartial]

/-- The time derivative of the cutoff curl is the curl of the cutoff time
derivative of the vector potential. -/
theorem associatedPressureHelmholtzCutoffCurl_timePartial_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestTimePartial
      (fun w => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) w i)
      z =
    associatedPressureTestCurl
      (fun q => rieszPressurePotentialCutoff n q.1 •
        associatedPressureHelmholtzVectorPotentialTimePartial φ q) z i := by
  have hcut := associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction
    hφ n
  have hcomm := associatedPressureTestCurl_timePartial hcut.1 i
    z
  have hcomponent (k : Fin 3) (q : Vec3 × ℝ) :=
    associatedPressureHelmholtzCutoffPotential_timePartial hφ n k q
  have hcomponent' (k : Fin 3) (q : Vec3 × ℝ) :
      associatedPressureTestTimePartial
        (fun y => associatedPressureHelmholtzCutoffVectorPotential φ n y k)
        q =
        rieszPressurePotentialCutoff n q.1 *
          associatedPressureHelmholtzVectorPotentialTimePartial φ q k := by
    simpa [associatedPressureTestTimePartial, CKN.timePartialProd] using hcomponent k q
  have hvec :
      (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
        (fun y => associatedPressureHelmholtzCutoffVectorPotential φ n y k)
        q) =
      (fun q => rieszPressurePotentialCutoff n q.1 •
        associatedPressureHelmholtzVectorPotentialTimePartial φ q) := by
    funext q k
    exact hcomponent' k q
  have hcommProd :
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) w i)
          (parabolicHomeomorph.symm z) =
        associatedPressureTestCurl
          (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
            (fun y => associatedPressureHelmholtzCutoffVectorPotential φ n y k)
            q) z i := by
    exact hcomm
  rw [hvec] at hcommProd
  simpa using hcommProd

/-- At each fixed point, the cutoff curl time derivative eventually agrees
with the full Helmholtz curl time derivative. -/
theorem associatedPressureHelmholtzCutoffCurl_timePartial_eventually_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) w i)
          z =
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) w i)
          z := by
  have hdecay (k : Fin 3) :=
    associatedPressureHelmholtzVectorPotential_component_decay hφ k
  have hAtSmooth (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) := by
    exact CKN.contDiff_timePartial
      ((contDiff_apply ℝ ℝ k).comp
        (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  have hdir (k l : Fin 3) : ∀ᶠ n : ℕ in atTop,
      rieszPressureJointDirection
        (rieszPressurePotentialCutoffTest
          (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) n) l z =
      rieszPressureJointDirection
        (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) l z :=
    associatedPressurePotentialCutoff_direction_eventually_eq (hAtSmooth k) l z
  have hpartial (k l : Fin 3) : ∀ᶠ n : ℕ in atTop,
      associatedPressureTestPartial
          (fun q => rieszPressurePotentialCutoff n q.1 *
            associatedPressureHelmholtzVectorPotentialTimePartial φ q k) l z =
        associatedPressureTestPartial
          (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) l z := by
    have hc := hdir k l
    filter_upwards [hc] with n hn
    have hcutSmooth := CKN.contDiff_timePartial
      ((contDiff_apply ℝ ℝ k).comp
        (associatedPressureHelmholtzVectorPotential_contDiff hφ))
    have hcutTest := rieszPressurePotentialCutoffTest_contDiff (hAtSmooth k) n
    have hleft := rieszPressure_sliceSpatialDeriv_eq_joint hcutTest l z
    have hright := rieszPressure_sliceSpatialDeriv_eq_joint (hAtSmooth k) l z
    have hleft' :
        associatedPressureTestPartial
            (fun q => rieszPressurePotentialCutoff n q.1 *
              associatedPressureHelmholtzVectorPotentialTimePartial φ q k) l z =
          rieszPressureJointDirection
            (rieszPressurePotentialCutoffTest
              (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) n)
            l z := by
      simpa [associatedPressureTestPartial, CKN.spatialPartial, CKN.spatialDeriv,
        rieszPressurePotentialCutoffTest] using hleft
    have hright' :
        associatedPressureTestPartial
            (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) l z =
          rieszPressureJointDirection
            (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) l z := by
      simpa [associatedPressureTestPartial, CKN.spatialPartial, CKN.spatialDeriv] using hright
    calc
      _ = rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest
            (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) n)
          l z := hleft'
      _ = rieszPressureJointDirection
          (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q k) l z := hn
      _ = _ := hright'.symm
  have htime := associatedPressureHelmholtzCutoffCurl_timePartial_eq hφ
  have hAtSmooth := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hbase := associatedPressureTestCurl_timePartial hAtSmooth i
    z
  have hbaseVec :
      (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
        (fun y => associatedPressureHelmholtzVectorPotential φ y k)
        q) =
      associatedPressureHelmholtzVectorPotentialTimePartial φ := by
    funext q k
    rfl
  have hbaseProd :
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) w i)
          z =
        associatedPressureTestCurl
          (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
            (fun y => associatedPressureHelmholtzVectorPotential φ y k)
            q) z i := by
    exact hbase
  rw [hbaseVec] at hbaseProd
  have hbase' :
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) w i)
          z =
        associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotentialTimePartial φ) z i := by
    simpa using hbaseProd
  fin_cases i
  · filter_upwards [hpartial 2 1, hpartial 1 2] with n h1 h2
    calc
      _ = associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 •
            associatedPressureHelmholtzVectorPotentialTimePartial φ q) z 0 := by
        simpa using htime n 0 z
      _ = associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotentialTimePartial φ) z 0 := by
        simp only [associatedPressureTestCurl_zero]
        dsimp
        rw [h1, h2]
      _ = _ := hbase'.symm
  · filter_upwards [hpartial 0 2, hpartial 2 0] with n h1 h2
    calc
      _ = associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 •
            associatedPressureHelmholtzVectorPotentialTimePartial φ q) z 1 := by
        simpa using htime n 1 z
      _ = associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotentialTimePartial φ) z 1 := by
        simp only [associatedPressureTestCurl_one]
        dsimp
        rw [h1, h2]
      _ = _ := hbase'.symm
  · filter_upwards [hpartial 1 0, hpartial 0 1] with n h1 h2
    calc
      _ = associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 •
            associatedPressureHelmholtzVectorPotentialTimePartial φ q) z 2 := by
        simpa using htime n 2 z
      _ = associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotentialTimePartial φ) z 2 := by
        simp only [associatedPressureTestCurl_two]
        dsimp
        rw [h1, h2]
      _ = _ := hbase'.symm

end CKN.Leray

end

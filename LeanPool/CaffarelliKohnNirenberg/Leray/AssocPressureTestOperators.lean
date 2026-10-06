/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureHelmholtz
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.PointwiseEnergy

/-!
# Assoc Pressure Test Operators

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatial coordinate derivative of a scalar field in product
space-time coordinates. -/
@[expose]
def associatedPressureTestPartial
    (f : Vec3 × ℝ → ℝ) (i : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  CKN.spatialPartial f i z

/-- The three-dimensional curl of a vector test field in product
space-time coordinates. -/
@[expose]
def associatedPressureTestCurl (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 :=
  fun z j => associatedPressureTestCurlComponent φ j z

@[simp]
theorem associatedPressureTestCurl_zero (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) :
    associatedPressureTestCurl φ z 0 =
      associatedPressureTestPartial (fun w => φ w 2) 1 z -
        associatedPressureTestPartial (fun w => φ w 1) 2 z := by
  rfl

@[simp]
theorem associatedPressureTestCurl_one (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) :
    associatedPressureTestCurl φ z 1 =
      associatedPressureTestPartial (fun w => φ w 0) 2 z -
        associatedPressureTestPartial (fun w => φ w 2) 0 z := by
  rfl

@[simp]
theorem associatedPressureTestCurl_two (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) :
    associatedPressureTestCurl φ z 2 =
      associatedPressureTestPartial (fun w => φ w 1) 0 z -
        associatedPressureTestPartial (fun w => φ w 0) 1 z := by
  rfl

theorem associatedPressureTestPartial_eq_spatialPartial
    (f : Vec3 × ℝ → ℝ) (i : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestPartial f i z = CKN.spatialPartial f i z := rfl

private theorem associatedPressureTestPartial_smooth
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => associatedPressureTestPartial f i z) := by
  simpa only [associatedPressureTestPartial] using CKN.spatialPartial_contDiff hf i

private theorem associatedPressureTestPartial_zero_off_tsupport
    {f : Vec3 × ℝ → ℝ} (z : Vec3 × ℝ)
    (hz : z ∉ tsupport f) (i : Fin 3) :
    associatedPressureTestPartial f i z = 0 := by
  rw [associatedPressureTestPartial_eq_spatialPartial]
  exact CKN.spatialPartial_eq_zero_off_tsupport hz i

/-- The curl of a compact smooth vector test remains in the same compact
test class. -/
theorem associatedPressureTestCurl_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) :
    associatedPressureTestCurl φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I := by
  rcases hφ with ⟨hφsmooth, hφcompact, hφsupport⟩
  have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z i) :=
    (contDiff_apply ℝ ℝ i).comp hφsmooth
  have hpartSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestPartial (fun w => φ w i) j z) :=
    associatedPressureTestPartial_smooth (hcomp i) j
  have hsmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestCurl φ z i) := by
    fin_cases i
    · exact (hpartSmooth 2 1).sub (hpartSmooth 1 2)
    · exact (hpartSmooth 0 2).sub (hpartSmooth 2 0)
    · exact (hpartSmooth 1 0).sub (hpartSmooth 0 1)
  have hzero (z : Vec3 × ℝ) (hz : z ∉ tsupport φ) :
      associatedPressureTestCurl φ z = 0 := by
    apply funext
    intro i
    have hc (j : Fin 3) : z ∉ tsupport (fun w : Vec3 × ℝ => φ w j) := by
      intro hmem
      have hsub : tsupport (fun w : Vec3 × ℝ => φ w j) ⊆ tsupport φ :=
        CKN.tsupport_component_subset (V := Vec3) (ι := Fin 3) φ j
          (by intro w hw; simp [hw])
      exact hz (hsub hmem)
    have hpartZero (j k : Fin 3) :
        associatedPressureTestPartial (fun w : Vec3 × ℝ => φ w j) k z = 0 :=
      associatedPressureTestPartial_zero_off_tsupport z (hc j) k
    fin_cases i
    · change associatedPressureTestCurl φ z 0 = 0
      rw [associatedPressureTestCurl_zero, hpartZero 2 1, hpartZero 1 2]
      ring
    · change associatedPressureTestCurl φ z 1 = 0
      rw [associatedPressureTestCurl_one, hpartZero 0 2, hpartZero 2 0]
      ring
    · change associatedPressureTestCurl φ z 2 = 0
      rw [associatedPressureTestCurl_two, hpartZero 1 0, hpartZero 0 1]
      ring
  have hfunSupport : Function.support (associatedPressureTestCurl φ) ⊆ tsupport φ := by
    intro z hz
    by_contra hnot
    exact hz (hzero z hnot)
  have htsupport : tsupport (associatedPressureTestCurl φ) ⊆ tsupport φ :=
    closure_minimal hfunSupport (isClosed_tsupport φ)
  refine ⟨contDiff_pi.2 hsmooth, ?_, htsupport.trans hφsupport⟩
  exact hφcompact.isCompact.of_isClosed_subset (isClosed_tsupport _)
    htsupport

/-- The curl of a smooth vector field is smooth. -/
theorem associatedPressureTestCurl_contDiff
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureTestCurl φ) := by
  have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hpartSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestPartial (fun w => φ w i) j z) :=
    associatedPressureTestPartial_smooth (hcomp i) j
  apply contDiff_pi.2
  intro i
  fin_cases i
  · exact (hpartSmooth 2 1).sub (hpartSmooth 1 2)
  · exact (hpartSmooth 0 2).sub (hpartSmooth 2 0)
  · exact (hpartSmooth 1 0).sub (hpartSmooth 0 1)

/-- Mixed spatial derivatives of a smooth scalar field commute in product
space-time coordinates. -/
theorem associatedPressureTestPartial_spatialPartial_commute
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestPartial
        (fun w => associatedPressureTestPartial f i w) j z =
      associatedPressureTestPartial
        (fun w => associatedPressureTestPartial f j w) i z := by
  let φ : Vec3 → ℝ := fun x => f (x, z.2)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  have hswap := CKN.mixedSecond_swap hφ i j z.1
  change CKN.mixedSecond φ j i z.1 = CKN.mixedSecond φ i j z.1
  exact hswap.symm

/-- Spatial differentiation distributes over subtraction of smooth scalar
fields. -/
theorem associatedPressureTestPartial_sub_smooth
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestPartial (fun w => f w - g w) i z =
      associatedPressureTestPartial f i z - associatedPressureTestPartial g i z := by
  let F : Vec3 → ℝ := fun x => f (x, z.2)
  let G : Vec3 → ℝ := fun x => g (x, z.2)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hf.comp (contDiff_id.prodMk contDiff_const)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := hg.comp (contDiff_id.prodMk contDiff_const)
  have hFd : DifferentiableAt ℝ F z.1 := (hF.differentiable (by simp)) z.1
  have hGd : DifferentiableAt ℝ G z.1 := (hG.differentiable (by simp)) z.1
  have hsub := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (fderiv_fun_sub hFd hGd)
  simpa [associatedPressureTestPartial, CKN.spatialPartial, F, G] using hsub

/-- The curl of a smooth test field has zero spatial divergence. -/
theorem associatedPressureTestCurl_divergence
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : Vec3 × ℝ) :
    ∑ i : Fin 3, associatedPressureTestPartial
      (fun w : Vec3 × ℝ => associatedPressureTestCurl φ w i) i z = 0 := by
  have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => φ w i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hpartSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => associatedPressureTestPartial (fun x => φ x i) j w) :=
    associatedPressureTestPartial_smooth (hcomp i) j
  rw [Fin.sum_univ_three]
  simp only [associatedPressureTestCurl_zero, associatedPressureTestCurl_one,
    associatedPressureTestCurl_two]
  rw [associatedPressureTestPartial_sub_smooth (hpartSmooth 2 1)
      (hpartSmooth 1 2) 0 z,
    associatedPressureTestPartial_sub_smooth (hpartSmooth 0 2)
      (hpartSmooth 2 0) 1 z,
    associatedPressureTestPartial_sub_smooth (hpartSmooth 1 0)
      (hpartSmooth 0 1) 2 z]
  rw [associatedPressureTestPartial_spatialPartial_commute (hcomp 2) 1 0 z,
    associatedPressureTestPartial_spatialPartial_commute (hcomp 1) 2 0 z,
    associatedPressureTestPartial_spatialPartial_commute (hcomp 0) 2 1 z]
  ring

/-- The componentwise time derivative of a scalar test in product
space-time coordinates. -/
@[expose]
def associatedPressureTestTimePartial (f : Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ :=
  CKN.timePartialProd f

theorem associatedPressureTestPartial_timePartial_commute
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestTimePartial
        (fun w => associatedPressureTestPartial f i w) z =
      associatedPressureTestPartial
        (fun w => associatedPressureTestTimePartial f w) i z := by
  change CKN.timePartial
      (fun w : ParabolicPoint => CKN.spatialPartial f i w) z =
    CKN.spatialPartial
      (fun w : ParabolicPoint => CKN.timePartial f w) i z
  exact CKN.timePartial_spatialPartial_comm hf z i

private theorem associatedPressureTestTimePartial_sub
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) :
    associatedPressureTestTimePartial (fun w => f w - g w) z =
      associatedPressureTestTimePartial f z - associatedPressureTestTimePartial g z := by
  change CKN.timePartial (fun w : ParabolicPoint => f w - g w) z = _
  exact CKN.timePartial_sub_at
    ((hf.differentiable (by simp)) z) ((hg.differentiable (by simp)) z)

/-- Time differentiation commutes with the curl on smooth product-space
tests. -/
theorem associatedPressureTestCurl_timePartial
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestTimePartial
        (fun w : Vec3 × ℝ => associatedPressureTestCurl φ w i) z =
      associatedPressureTestCurl
        (fun w : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
          (fun y => φ y k) w) z i := by
  have hcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => φ w k) :=
    (contDiff_apply ℝ ℝ k).comp hφ
  have hderiv (k l : Fin 3) (w : Vec3 × ℝ) :
      associatedPressureTestTimePartial
        (fun y => associatedPressureTestPartial (fun x => φ x k) l y) w =
      associatedPressureTestPartial
        (fun x => associatedPressureTestTimePartial
          (fun y => φ y k) x) l w := by
    exact associatedPressureTestPartial_timePartial_commute (hcomp k) l w
  fin_cases i
  · change associatedPressureTestTimePartial
        (fun y : Vec3 × ℝ => associatedPressureTestPartial (fun x => φ x 2) 1 y -
          associatedPressureTestPartial (fun x => φ x 1) 2 y) z =
      associatedPressureTestCurl
        (fun w => fun k => associatedPressureTestTimePartial (fun y => φ y k) w) z 0
    rw [associatedPressureTestCurl_zero]
    rw [associatedPressureTestTimePartial_sub
      (associatedPressureTestPartial_smooth (hcomp 2) 1)
      (associatedPressureTestPartial_smooth (hcomp 1) 2) z]
    rw [hderiv 2 1 z, hderiv 1 2 z]
  · change associatedPressureTestTimePartial
        (fun y : Vec3 × ℝ => associatedPressureTestPartial (fun x => φ x 0) 2 y -
          associatedPressureTestPartial (fun x => φ x 2) 0 y) z =
      associatedPressureTestCurl
        (fun w => fun k => associatedPressureTestTimePartial (fun y => φ y k) w) z 1
    rw [associatedPressureTestCurl_one]
    rw [associatedPressureTestTimePartial_sub
      (associatedPressureTestPartial_smooth (hcomp 0) 2)
      (associatedPressureTestPartial_smooth (hcomp 2) 0) z]
    rw [hderiv 0 2 z, hderiv 2 0 z]
  · change associatedPressureTestTimePartial
        (fun y : Vec3 × ℝ => associatedPressureTestPartial (fun x => φ x 1) 0 y -
          associatedPressureTestPartial (fun x => φ x 0) 1 y) z =
      associatedPressureTestCurl
        (fun w => fun k => associatedPressureTestTimePartial (fun y => φ y k) w) z 2
    rw [associatedPressureTestCurl_two]
    rw [associatedPressureTestTimePartial_sub
      (associatedPressureTestPartial_smooth (hcomp 1) 0)
      (associatedPressureTestPartial_smooth (hcomp 0) 1) z]
    rw [hderiv 1 0 z, hderiv 0 1 z]

end CKN.Leray

end

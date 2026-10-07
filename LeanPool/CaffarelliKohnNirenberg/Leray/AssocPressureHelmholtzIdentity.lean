/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureHelmholtz
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureTestOperators

/-!
# Assoc Pressure Helmholtz Identity

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Convolution
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- The product-space gradient of a scalar test field. -/
@[expose]
def associatedPressureTestGradient (h : Vec3 × ℝ → ℝ) : Vec3 × ℝ → Vec3 :=
  fun z i => CKN.spatialPartialProd h i z

private theorem associatedPressureTestSpatialPartial_smooth
    {h : Vec3 × ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialPartialProd h i) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun z : Vec3 × ℝ => CKN.spatialPartial h i z)
  exact CKN.spatialPartial_contDiff hh i

private theorem associatedPressureTestSpatialPartial_compact
    {h : Vec3 × ℝ → ℝ} (hc : HasCompactSupport h) (i : Fin 3) :
    HasCompactSupport (CKN.spatialPartialProd h i) := by
  change HasCompactSupport (fun z : Vec3 × ℝ => CKN.spatialPartial h i z)
  exact CKN.hasCompactSupport_spatialPartial hc i

private theorem associatedPressureTestSpatialPartial_sub
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (fun w => f w - g w) i z =
      CKN.spatialPartialProd f i z - CKN.spatialPartialProd g i z := by
  have hfSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => f (x, z.2)) :=
    hf.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have hgSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
    hg.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (fderiv_fun_sub (hfSlice.differentiable (by simp) z.1)
      (hgSlice.differentiable (by simp) z.1))
  simpa [CKN.spatialPartialProd, CKN.spatialPartial] using h

private theorem associatedPressureTestSpatialPartial_add
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (fun w => f w + g w) i z =
      CKN.spatialPartialProd f i z + CKN.spatialPartialProd g i z := by
  have hfSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => f (x, z.2)) :=
    hf.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have hgSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
    hg.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (fderiv_fun_add (hfSlice.differentiable (by simp) z.1)
      (hgSlice.differentiable (by simp) z.1))
  simpa [CKN.spatialPartialProd, CKN.spatialPartial] using h

private theorem associatedPressureTestSpatialPartial_commute
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (CKN.spatialPartialProd f j) i z =
      CKN.spatialPartialProd (CKN.spatialPartialProd f i) j z := by
  have hswap := CKN.mixedSecond_swap
    (hf.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)) i j z.1
  change CKN.mixedSecond (fun x : Vec3 => f (x, z.2)) i j z.1 =
    CKN.mixedSecond (fun x : Vec3 => f (x, z.2)) j i z.1
  exact hswap

private theorem associatedPressureTestSpatialPartial_neg
    {f : Vec3 × ℝ → ℝ} (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (fun w => -f w) i z =
      -CKN.spatialPartialProd f i z := by
  simp [CKN.spatialPartialProd, CKN.spatialPartial]

/-- Applying the Newtonian potential to a spatial Laplacian recovers a smooth
compactly supported function. -/
private theorem associatedPressureNewtonianPotential_of_laplacian
    {h : Vec3 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) (x : Vec3) :
    CKN.pressureNewtonianPotential (CKN.spatialLaplacian h) x = h x := by
  have hrep := CKN.Foundation.Heat.newtonian_representation_smooth hh hc x
  simpa [CKN.pressureNewtonianPotential, integral_neg] using hrep.symm

private theorem associatedPressureNewtonianPotential_sub
    {g h : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhc : HasCompactSupport h) (z : Vec3 × ℝ) :
    associatedPressureNewtonianPotential (g - h) z =
      associatedPressureNewtonianPotential g z -
        associatedPressureNewtonianPotential h z := by
  let gSlice : Vec3 → ℝ := fun x => g (x, z.2)
  let hSlice : Vec3 → ℝ := fun x => h (x, z.2)
  let Kg : Set Vec3 := (tsupport g).image (fun w : Vec3 × ℝ => w.1)
  let Kh : Set Vec3 := (tsupport h).image (fun w : Vec3 × ℝ => w.1)
  have hproj : Continuous (fun w : Vec3 × ℝ => w.1) := continuous_fst
  have hKg : IsCompact Kg := hgc.isCompact.image hproj
  have hKh : IsCompact Kh := hhc.isCompact.image hproj
  have hgSliceCompact : HasCompactSupport gSlice :=
    HasCompactSupport.of_support_subset_isCompact hKg (by
      intro x hx
      change g (x, z.2) ≠ 0 at hx
      exact ⟨(x, z.2), subset_tsupport g hx, rfl⟩)
  have hhSliceCompact : HasCompactSupport hSlice :=
    HasCompactSupport.of_support_subset_isCompact hKh (by
      intro x hx
      change h (x, z.2) ≠ 0 at hx
      exact ⟨(x, z.2), subset_tsupport h hx, rfl⟩)
  have hgSlice : ContDiff ℝ (⊤ : ℕ∞) gSlice := by
    exact hg.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have hhSlice : ContDiff ℝ (⊤ : ℕ∞) hSlice := by
    exact hh.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  have hKernel : LocallyIntegrable (-newtonianKernel) volume :=
    locallyIntegrable_newtonianKernel.neg
  have hgInt : Integrable (fun x : Vec3 =>
      (-newtonianKernel (z.1 - x)) * gSlice x) volume := by
    have hi := hgSliceCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hgSlice.continuous hKernel z.1
    simpa [ContinuousLinearMap.lsmul_apply, mul_comm] using hi.integrable
  have hhInt : Integrable (fun x : Vec3 =>
      (-newtonianKernel (z.1 - x)) * hSlice x) volume := by
    have hi := hhSliceCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hhSlice.continuous hKernel z.1
    simpa [ContinuousLinearMap.lsmul_apply, mul_comm] using hi.integrable
  rw [associatedPressureNewtonianPotential, associatedPressureNewtonianPotential,
    associatedPressureNewtonianPotential, CKN.pressureNewtonianPotential,
    CKN.pressureNewtonianPotential, CKN.pressureNewtonianPotential]
  change (∫ x : Vec3, (-newtonianKernel (z.1 - x)) * (gSlice x - hSlice x)) =
    (∫ x : Vec3, (-newtonianKernel (z.1 - x)) * gSlice x) -
      ∫ x : Vec3, (-newtonianKernel (z.1 - x)) * hSlice x
  have hintegrand :
      (fun x : Vec3 => (-newtonianKernel (z.1 - x)) * (gSlice x - hSlice x)) =
        (fun x => (-newtonianKernel (z.1 - x)) * gSlice x -
          (-newtonianKernel (z.1 - x)) * hSlice x) := by
    funext x
    ring
  rw [hintegrand, integral_sub hgInt hhInt]

private theorem associatedPressureTestCurlCurl_identity
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (j : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestCurl (associatedPressureTestCurl φ) z j =
      CKN.spatialPartialProd (associatedPressureTestDivergence φ) j z -
        ∑ k : Fin 3,
          CKN.spatialPartialProd (CKN.spatialPartialProd
            (fun w : Vec3 × ℝ => φ w j) k) k z := by
  let hφi (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hφ i
  have hmix (c i j : Fin 3) (w : Vec3 × ℝ) :
      CKN.spatialPartialProd (CKN.spatialPartialProd
        (fun y : Vec3 × ℝ => φ y c) j) i w =
      CKN.spatialPartialProd (CKN.spatialPartialProd
        (fun y : Vec3 × ℝ => φ y c) i) j w :=
    associatedPressureTestSpatialPartial_commute ((hφi c).1) i j w
  have hD (c i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun y : Vec3 × ℝ => φ y c) i) :=
    associatedPressureTestSpatialPartial_smooth (hφi c).1 i
  unfold associatedPressureTestDivergence
  fin_cases j
  · simp only [
      associatedPressureTestCurl, associatedPressureTestCurlComponent, Fin.zero_eta, Fin.isValue,
      ↓reduceIte, Fin.reduceEq, one_ne_zero, Fin.sum_univ_three]
    rw [associatedPressureTestSpatialPartial_sub (hD 1 0) (hD 0 1) 1 z,
      associatedPressureTestSpatialPartial_sub (hD 0 2) (hD 2 0) 2 z]
    rw [associatedPressureTestSpatialPartial_add ((hD 0 0).add (hD 1 1)) (hD 2 2) 0 z,
      associatedPressureTestSpatialPartial_add (hD 0 0) (hD 1 1) 0 z]
    rw [hmix 1 1 0 z, hmix 2 2 0 z]
    ring
  · simp only [
      associatedPressureTestCurl, associatedPressureTestCurlComponent, Fin.mk_one, Fin.isValue,
      one_ne_zero, ↓reduceIte, Fin.reduceEq, Fin.sum_univ_three]
    rw [associatedPressureTestSpatialPartial_sub (hD 2 1) (hD 1 2) 2 z,
      associatedPressureTestSpatialPartial_sub (hD 1 0) (hD 0 1) 0 z]
    rw [associatedPressureTestSpatialPartial_add ((hD 0 0).add (hD 1 1)) (hD 2 2) 1 z,
      associatedPressureTestSpatialPartial_add (hD 0 0) (hD 1 1) 1 z]
    rw [hmix 2 2 1 z, hmix 0 0 1 z]
    ring
  · simp only [
      associatedPressureTestCurl, associatedPressureTestCurlComponent, Fin.reduceFinMk,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, one_ne_zero, Fin.sum_univ_three]
    rw [associatedPressureTestSpatialPartial_sub (hD 0 2) (hD 2 0) 0 z,
      associatedPressureTestSpatialPartial_sub (hD 2 1) (hD 1 2) 1 z]
    rw [associatedPressureTestSpatialPartial_add ((hD 0 0).add (hD 1 1)) (hD 2 2) 2 z,
      associatedPressureTestSpatialPartial_add (hD 0 0) (hD 1 1) 2 z]
    rw [hmix 0 0 2 z, hmix 1 1 2 z]
    ring

/-- The componentwise spatial Laplacian of a vector-valued pressure test field. -/
@[expose]
def associatedPressureTestLaplacianComponent
    (φ : Vec3 × ℝ → Vec3) (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
  ∑ k : Fin 3, CKN.spatialPartialProd
    (CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) k) k z

private theorem associatedPressureTestLaplacianComponent_contDiff
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureTestLaplacianComponent φ i) := by
  have hφi := CKN.component_mem_spaceTimeTestFunction hφ i
  have hD (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) k) :=
    associatedPressureTestSpatialPartial_smooth hφi.1 k
  apply ContDiff.sum
  intro k hk
  exact associatedPressureTestSpatialPartial_smooth (hD k) k

private theorem associatedPressureTestLaplacianComponent_hasCompactSupport
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) :
    HasCompactSupport (associatedPressureTestLaplacianComponent φ i) := by
  have hφi := CKN.component_mem_spaceTimeTestFunction hφ i
  have hD (k : Fin 3) : HasCompactSupport
      (CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) k) :=
    associatedPressureTestSpatialPartial_compact hφi.2.1 k
  have hDD (k : Fin 3) : HasCompactSupport
      (CKN.spatialPartialProd
        (CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) k) k) :=
    associatedPressureTestSpatialPartial_compact (hD k) k
  have hsum := HasCompactSupport.finset_sum
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun k : Fin 3 => fun z : Vec3 × ℝ =>
      CKN.spatialPartialProd
        (CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) k) k z)
    (fun k _ => hDD k)
  change HasCompactSupport (fun z : Vec3 × ℝ => ∑ k : Fin 3,
    CKN.spatialPartialProd
      (CKN.spatialPartialProd (fun w : Vec3 × ℝ => φ w i) k) k z)
  convert hsum using 1
  funext z
  simp only [Finset.sum_apply]

private theorem associatedPressureNewtonianPotential_testLaplacian
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureNewtonianPotential
      (associatedPressureTestLaplacianComponent φ i) z = φ z i := by
  let fSlice : Vec3 → ℝ := fun x => φ (x, z.2) i
  have hφi := CKN.component_mem_spaceTimeTestFunction hφ i
  have hfSlice : ContDiff ℝ (⊤ : ℕ∞) fSlice := by
    exact hφi.1.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  let K : Set Vec3 := (tsupport (fun w : Vec3 × ℝ => φ w i)).image
    (fun w : Vec3 × ℝ => w.1)
  have hproj : Continuous (fun w : Vec3 × ℝ => w.1) := continuous_fst
  have hK : IsCompact K := hφi.2.1.isCompact.image hproj
  have hfSliceCompact : HasCompactSupport fSlice :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro x hx
      change φ (x, z.2) i ≠ 0 at hx
      exact ⟨(x, z.2), subset_tsupport (fun w : Vec3 × ℝ => φ w i) hx, rfl⟩)
  have hsource :
      (fun x : Vec3 => associatedPressureTestLaplacianComponent φ i (x, z.2)) =
        CKN.spatialLaplacian fSlice := by
    funext x
    rfl
  change CKN.pressureNewtonianPotential
      (fun x : Vec3 => associatedPressureTestLaplacianComponent φ i (x, z.2)) z.1 = _
  rw [hsource]
  simpa [fSlice, associatedPressureNewtonianPotential] using
    associatedPressureNewtonianPotential_of_laplacian hfSlice hfSliceCompact z.1

private theorem associatedPressureNewtonianPotential_neg_spatialPartial
    {h : Vec3 × ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) (i : Fin 3) (z : Vec3 × ℝ) :
  CKN.spatialPartialProd
        (fun w => -associatedPressureNewtonianPotential h w) i z =
      -associatedPressureNewtonianPotential (CKN.spatialPartialProd h i) z := by
  rw [associatedPressureTestSpatialPartial_neg i z]
  rw [associatedPressureNewtonianPotential_spatialPartial hh hc i z]

private theorem associatedPressureHelmholtzVectorPotential_curl
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (j : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ) z j =
      -associatedPressureNewtonianPotential
        (fun w => associatedPressureTestCurl (associatedPressureTestCurl φ) w j) z := by
  have hcurl (k : Fin 3) := associatedPressureTestCurlComponent_contDiff hφ k
  have hcurlc (k : Fin 3) := associatedPressureTestCurlComponent_hasCompactSupport hφ k
  have hD (k l : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ k) l) :=
    associatedPressureTestSpatialPartial_smooth (hcurl k) l
  have hDc (k l : Fin 3) : HasCompactSupport
      (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ k) l) :=
    associatedPressureTestSpatialPartial_compact (hcurlc k) l
  fin_cases j
  · simp only [
      associatedPressureTestCurl, associatedPressureTestCurlComponent, Fin.zero_eta, Fin.isValue,
      ↓reduceIte, associatedPressureHelmholtzVectorPotential, Fin.reduceEq, one_ne_zero]
    rw [associatedPressureNewtonianPotential_neg_spatialPartial
      (hcurl 2) (hcurlc 2) 1 z,
      associatedPressureNewtonianPotential_neg_spatialPartial
        (hcurl 1) (hcurlc 1) 2 z]
    calc
      _ = -(associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 2) 1) z -
          associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 1) 2) z) := by ring
      _ = -associatedPressureNewtonianPotential
          ((CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 2) 1) -
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 1) 2)) z := by
        rw [← associatedPressureNewtonianPotential_sub (hD 2 1) (hDc 2 1)
          (hD 1 2) (hDc 1 2) z]
      _ = -associatedPressureNewtonianPotential
          (fun w => associatedPressureTestCurl (associatedPressureTestCurl φ) w 0) z := by rfl
  · simp only [
      associatedPressureTestCurl, associatedPressureTestCurlComponent, Fin.mk_one, Fin.isValue,
      one_ne_zero, ↓reduceIte, associatedPressureHelmholtzVectorPotential, Fin.reduceEq]
    rw [associatedPressureNewtonianPotential_neg_spatialPartial
      (hcurl 0) (hcurlc 0) 2 z,
      associatedPressureNewtonianPotential_neg_spatialPartial
        (hcurl 2) (hcurlc 2) 0 z]
    calc
      _ = -(associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 0) 2) z -
          associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 2) 0) z) := by ring
      _ = -associatedPressureNewtonianPotential
          ((CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 0) 2) -
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 2) 0)) z := by
        rw [← associatedPressureNewtonianPotential_sub (hD 0 2) (hDc 0 2)
          (hD 2 0) (hDc 2 0) z]
      _ = -associatedPressureNewtonianPotential
          (fun w => associatedPressureTestCurl (associatedPressureTestCurl φ) w 1) z := by rfl
  · simp only [
      associatedPressureTestCurl, associatedPressureTestCurlComponent, Fin.reduceFinMk,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, associatedPressureHelmholtzVectorPotential,
      one_ne_zero]
    rw [associatedPressureNewtonianPotential_neg_spatialPartial
      (hcurl 1) (hcurlc 1) 0 z,
      associatedPressureNewtonianPotential_neg_spatialPartial
        (hcurl 0) (hcurlc 0) 1 z]
    calc
      _ = -(associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 1) 0) z -
          associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 0) 1) z) := by ring
      _ = -associatedPressureNewtonianPotential
          ((CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 1) 0) -
            (CKN.spatialPartialProd (associatedPressureTestCurlComponent φ 0) 1)) z := by
        rw [← associatedPressureNewtonianPotential_sub (hD 1 0) (hDc 1 0)
          (hD 0 1) (hDc 0 1) z]
      _ = -associatedPressureNewtonianPotential
          (fun w => associatedPressureTestCurl (associatedPressureTestCurl φ) w 2) z := by rfl

/-- The smooth spatial Helmholtz decomposition of a compactly supported test
field, as in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtz_identity
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (z : Vec3 × ℝ) :
    φ z = associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) z +
      associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotential φ) z := by
  funext j
  have hdiv := associatedPressureTestDivergence_contDiff hφ
  have hdivc := associatedPressureTestDivergence_hasCompactSupport hφ
  have hdivj := associatedPressureTestSpatialPartial_smooth hdiv j
  have hdivjc := associatedPressureTestSpatialPartial_compact hdivc j
  have hlap := associatedPressureTestLaplacianComponent_contDiff hφ j
  have hlapc := associatedPressureTestLaplacianComponent_hasCompactSupport hφ j
  have hgrad :
      associatedPressureTestGradient
          (associatedPressureHelmholtzScalarPotential φ) z j =
        associatedPressureNewtonianPotential
          (CKN.spatialPartialProd (associatedPressureTestDivergence φ) j) z := by
    exact associatedPressureNewtonianPotential_spatialPartial hdiv hdivc j z
  have hcurlcurl_source :
      (fun w => associatedPressureTestCurl (associatedPressureTestCurl φ) w j) =
        (CKN.spatialPartialProd (associatedPressureTestDivergence φ) j -
          associatedPressureTestLaplacianComponent φ j) := by
    funext w
    exact associatedPressureTestCurlCurl_identity hφ j w
  have hcurlcurl_potential :
      associatedPressureNewtonianPotential
          (fun w => associatedPressureTestCurl (associatedPressureTestCurl φ) w j) z =
        associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestDivergence φ) j) z - φ z j := by
    calc
      associatedPressureNewtonianPotential
          (fun w => associatedPressureTestCurl (associatedPressureTestCurl φ) w j) z =
        associatedPressureNewtonianPotential
          (CKN.spatialPartialProd (associatedPressureTestDivergence φ) j -
            associatedPressureTestLaplacianComponent φ j) z := by rw [hcurlcurl_source]
      _ = associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestDivergence φ) j) z -
          associatedPressureNewtonianPotential
            (associatedPressureTestLaplacianComponent φ j) z :=
          associatedPressureNewtonianPotential_sub hdivj hdivjc hlap hlapc z
      _ = associatedPressureNewtonianPotential
            (CKN.spatialPartialProd (associatedPressureTestDivergence φ) j) z - φ z j := by
          rw [associatedPressureNewtonianPotential_testLaplacian hφ j z]
  change φ z j = associatedPressureTestCurl
    (associatedPressureHelmholtzVectorPotential φ) z j +
      associatedPressureTestGradient (associatedPressureHelmholtzScalarPotential φ) z j
  rw [associatedPressureHelmholtzVectorPotential_curl hφ j z, hgrad,
    hcurlcurl_potential]
  ring

end CKN.Leray

end

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureHelmholtzIdentity
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotential
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrders
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Potential decay foundations

Newtonian-potential identities and component formulas for the Helmholtz potentials.
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

/-- A first spatial derivative is bounded by the first iterated derivative. -/
theorem associatedPressureFirstSpatialDerivative_le_iteratedFDeriv
    {f : Vec3 → ℝ} (i : Fin 3) (x : Vec3) :
    |CKN.spatialDeriv f i x| ≤ ‖iteratedFDeriv ℝ 1 f x‖ := by
  have hval : iteratedFDeriv ℝ 1 f x ![CKN.basisVec i] =
      CKN.spatialDeriv f i x := by
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [← hval]
  have hnorm := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ 1 f x) ![CKN.basisVec i]
  have hprod : ∏ k : Fin 1, ‖(![CKN.basisVec i] : Fin 1 → Vec3) k‖ = 1 := by
    simp [CKN.basisVec, Pi.norm_single]
  rw [← Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv ℝ 1 f x ![CKN.basisVec i]‖ ≤
        ‖iteratedFDeriv ℝ 1 f x‖ *
          ∏ k : Fin 1, ‖(![CKN.basisVec i] : Fin 1 → Vec3) k‖ := hnorm
    _ = ‖iteratedFDeriv ℝ 1 f x‖ := by rw [hprod, mul_one]

/-- A second spatial derivative is bounded by the second iterated derivative. -/
theorem associatedPressureSecondSpatialDerivative_le_iteratedFDeriv
    {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 3) (x : Vec3) :
    |CKN.spatialDeriv (CKN.spatialDeriv f j) i x| ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
  have hval :
      iteratedFDeriv ℝ 2 f x ![CKN.basisVec i, CKN.basisVec j] =
        CKN.spatialDeriv (CKN.spatialDeriv f j) i x := by
    rw [iteratedFDeriv_two_apply]
    change (fderiv ℝ (fderiv ℝ f) x) (CKN.basisVec i) (CKN.basisVec j) =
      (fderiv ℝ (fun y => (fderiv ℝ f y) (CKN.basisVec j)) x)
        (CKN.basisVec i)
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf.contDiffAt.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiableAt (by simp)
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  rw [← hval]
  have hnorm := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ 2 f x) ![CKN.basisVec i, CKN.basisVec j]
  have hprod :
      ∏ k : Fin 2, ‖(![CKN.basisVec i, CKN.basisVec j] : Fin 2 → Vec3) k‖ = 1 := by
    simp [Fin.prod_univ_two, CKN.basisVec, Pi.norm_single]
  rw [← Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv ℝ 2 f x ![CKN.basisVec i, CKN.basisVec j]‖ ≤
        ‖iteratedFDeriv ℝ 2 f x‖ *
          ∏ k : Fin 2, ‖(![CKN.basisVec i, CKN.basisVec j] : Fin 2 → Vec3) k‖ := hnorm
    _ = ‖iteratedFDeriv ℝ 2 f x‖ := by rw [hprod, mul_one]

/-- A third spatial derivative is bounded by the third iterated derivative. -/
theorem associatedPressureThirdSpatialDerivative_le_iteratedFDeriv
    {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j k : Fin 3) (x : Vec3) :
    |CKN.spatialDeriv (CKN.spatialDeriv (CKN.spatialDeriv f k) j) i x| ≤
      ‖iteratedFDeriv ℝ 3 f x‖ := by
  have hval :
      iteratedFDeriv ℝ 3 f x ![CKN.basisVec i, CKN.basisVec j, CKN.basisVec k] =
        CKN.spatialDeriv (CKN.spatialDeriv (CKN.spatialDeriv f k) j) i x := by
    have hfd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x :=
      (hf.contDiffAt.iteratedFDeriv_right (m := 1) (i := 2) (by norm_num)).differentiableAt
        (by simp)
    rw [hfd.iteratedFDeriv_succ_apply_left']
    have htail :
        Fin.tail (![CKN.basisVec i, CKN.basisVec j, CKN.basisVec k] : Fin 3 → Vec3) =
          ![CKN.basisVec j, CKN.basisVec k] := by
      ext l
      fin_cases l <;> rfl
    have hhead :
        (![CKN.basisVec i, CKN.basisVec j, CKN.basisVec k] : Fin 3 → Vec3) 0 =
          CKN.basisVec i := rfl
    rw [htail, hhead]
    have hfun : (fun y : Vec3 =>
        iteratedFDeriv ℝ 2 f y ![CKN.basisVec j, CKN.basisVec k]) =
        (fun y => CKN.spatialDeriv (CKN.spatialDeriv f k) j y) := by
      funext y
      rw [iteratedFDeriv_two_apply]
      change (fderiv ℝ (fderiv ℝ f) y) (CKN.basisVec j) (CKN.basisVec k) =
        (fderiv ℝ (fun w => (fderiv ℝ f w) (CKN.basisVec k)) y)
          (CKN.basisVec j)
      have hfd' : DifferentiableAt ℝ (fderiv ℝ f) y :=
        (hf.contDiffAt.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiableAt (by simp)
      rw [fderiv_clm_apply hfd' (differentiableAt_const _)]
      simp
    rw [hfun]
    change (fderiv ℝ (fun y =>
      CKN.spatialDeriv (CKN.spatialDeriv f k) j y) x) (CKN.basisVec i) = _
    rfl
  rw [← hval]
  have hnorm := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ 3 f x) ![CKN.basisVec i, CKN.basisVec j, CKN.basisVec k]
  have hprod :
      ∏ l : Fin 3,
        ‖(![CKN.basisVec i, CKN.basisVec j, CKN.basisVec k] : Fin 3 → Vec3) l‖ = 1 := by
    simp [Fin.prod_univ_three, CKN.basisVec, Pi.norm_single]
  rw [← Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv ℝ 3 f x ![CKN.basisVec i, CKN.basisVec j, CKN.basisVec k]‖ ≤
        ‖iteratedFDeriv ℝ 3 f x‖ *
          ∏ l : Fin 3,
            ‖(![CKN.basisVec i, CKN.basisVec j, CKN.basisVec k] : Fin 3 → Vec3) l‖ := hnorm
    _ = ‖iteratedFDeriv ℝ 3 f x‖ := by rw [hprod, mul_one]

/-- The Newtonian Helmholtz potentials vanish on every time slice outside
the compact time support of the test field. -/
theorem associatedPressureHelmholtzPotentials_zero_off_time_support
    {φ : Vec3 × ℝ → Vec3}
    {t : ℝ} (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :
    associatedPressureHelmholtzScalarPotential φ (x, t) = 0 ∧
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0 := by
  have hnot (y : Vec3) : (y, t) ∉ tsupport φ := by
    intro hy
    exact ht ⟨(y, t), hy, rfl⟩
  have hslice (i : Fin 3) : (fun y : Vec3 => φ (y, t) i) = 0 := by
    funext y
    exact congrArg (fun v : Vec3 => v i)
      (image_eq_zero_of_notMem_tsupport (hnot y))
  have hpartial (i j : Fin 3) (y : Vec3) :
      CKN.spatialPartialProd (fun z : Vec3 × ℝ => φ z i) j (y, t) = 0 := by
    change (fderiv ℝ (fun z : Vec3 => φ (z, t) i) y) (CKN.basisVec j) = 0
    rw [hslice i]
    simp
  have hdiv (y : Vec3) : associatedPressureTestDivergence φ (y, t) = 0 := by
    simp [associatedPressureTestDivergence, hpartial]
  have hcurl (j : Fin 3) (y : Vec3) :
      associatedPressureTestCurlComponent φ j (y, t) = 0 := by
    fin_cases j <;> simp [associatedPressureTestCurlComponent, hpartial]
  have hdivSlice :
      (fun y : Vec3 => associatedPressureTestDivergence φ (y, t)) = 0 := by
    funext y
    exact hdiv y
  have hcurlSlice (j : Fin 3) :
      (fun y : Vec3 => associatedPressureTestCurlComponent φ j (y, t)) = 0 := by
    funext y
    exact hcurl j y
  constructor
  · change associatedPressureNewtonianPotential
      (associatedPressureTestDivergence φ) (x, t) = 0
    rw [associatedPressureNewtonianPotential, hdivSlice]
    simp [CKN.pressureNewtonianPotential]
  · funext j
    change -associatedPressureNewtonianPotential
      (associatedPressureTestCurlComponent φ j) (x, t) = 0
    rw [associatedPressureNewtonianPotential, hcurlSlice j]
    simp [CKN.pressureNewtonianPotential]

/-- Both Helmholtz potentials have the compact time support required in
`lem:riesz-duality` and in the solenoidal cutoff argument. -/
theorem associatedPressureHelmholtzPotentials_compactTimeSupport
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧
      (∀ t ∉ K, ∀ x,
        associatedPressureHelmholtzScalarPotential φ (x, t) = 0 ∧
        associatedPressureHelmholtzVectorPotential φ (x, t) = 0) := by
  refine ⟨(tsupport φ).image Prod.snd, hφ.2.1.isCompact.image continuous_snd, ?_⟩
  intro t ht x
  exact associatedPressureHelmholtzPotentials_zero_off_time_support ht x

/-- A compact smooth source has a finite absolute integral on each time slice. -/
theorem associatedPressurePotentialSource_slice_integral_bound
    {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ C ≥ 0, ∀ t : ℝ, ∫ x : Vec3, |g (x, t)| ≤ C := by
  let K : Set Vec3 := (tsupport g).image Prod.fst
  have hproj : Continuous (fun z : Vec3 × ℝ => z.1) := continuous_fst
  have hK : IsCompact K := hgc.isCompact.image hproj
  obtain ⟨C₀, hC₀⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hC₀nonneg : 0 ≤ C₀ := le_trans (norm_nonneg (g (0, 0))) (hC₀ (0, 0))
  let C : ℝ := max C₀ 0 * (volume : Measure Vec3).real K
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (le_max_right _ _) (ENNReal.toReal_nonneg)
  refine ⟨C, hCnonneg, fun t => ?_⟩
  let gSlice : Vec3 → ℝ := fun x => g (x, t)
  have hgSlice : Continuous gSlice := hg.continuous.comp
    (continuous_id.prodMk continuous_const)
  have hKzero : ∀ x ∉ K, gSlice x = 0 := by
    intro x hx
    have hnot : (x, t) ∉ tsupport g := by
      intro hmem
      exact hx ⟨(x, t), hmem, rfl⟩
    change g (x, t) = 0
    exact image_eq_zero_of_notMem_tsupport (f := g) hnot
  have hgcSlice : HasCompactSupport gSlice :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro x hx
      exact ⟨(x, t), subset_tsupport (f := g)
        (Function.mem_support.mpr (by simpa [gSlice] using hx)), rfl⟩)
  have hInt : Integrable (fun x : Vec3 => |gSlice x|) volume :=
    hgSlice.abs.integrable_of_hasCompactSupport hgcSlice.abs
  have hsetNonneg : 0 ≤ ∫ x in K, |gSlice x| :=
    integral_nonneg fun _ => abs_nonneg _
  have hsetBound : ‖∫ x in K, |gSlice x|‖ ≤
      max C₀ 0 * (volume : Measure Vec3).real K := by
    apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
    intro x hx
    simp only [Real.norm_eq_abs, abs_abs]
    have hpoint : |g (x, t)| ≤ C₀ := by
      simpa only [Real.norm_eq_abs] using hC₀ (x, t)
    exact hpoint.trans (le_max_left _ _)
  have hsetLe : (∫ x in K, |gSlice x|) ≤ C := by
    dsimp [C]
    rw [Real.norm_eq_abs, abs_of_nonneg hsetNonneg] at hsetBound
    exact hsetBound
  have hKzeroAbs : ∀ x ∉ K, |gSlice x| = 0 := by
    intro x hx
    simp [hKzero x hx]
  have hglobal : ∫ x : Vec3, |gSlice x| = ∫ x in K, |gSlice x| := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hKzeroAbs
  rw [hglobal]
  exact hsetLe

private theorem associatedPressureNewtonianPotential_finset_sum
    {g : Fin 3 → Vec3 × ℝ → ℝ}
    (hcont : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i))
    (hcomp : ∀ i, HasCompactSupport (g i)) (z : Vec3 × ℝ) :
    associatedPressureNewtonianPotential (fun q => ∑ i : Fin 3, g i q) z =
      ∑ i : Fin 3, associatedPressureNewtonianPotential (g i) z := by
  let gSlice (i : Fin 3) : Vec3 → ℝ := fun y => g i (y, z.2)
  have hSliceCont (i : Fin 3) : Continuous (gSlice i) :=
    (hcont i).continuous.comp (continuous_id.prodMk continuous_const)
  have hproj : Continuous (fun q : Vec3 × ℝ => q.1) := continuous_fst
  have hK (i : Fin 3) : IsCompact ((tsupport (g i)).image Prod.fst) :=
    (hcomp i).isCompact.image hproj
  have hSliceComp (i : Fin 3) : HasCompactSupport (gSlice i) := by
    apply HasCompactSupport.of_support_subset_isCompact (hK i)
    intro y hy
    exact ⟨(y, z.2), subset_tsupport (f := g i)
      (Function.mem_support.mpr (by simpa [gSlice] using hy)), rfl⟩
  have hKernel : LocallyIntegrable (-newtonianKernel) volume :=
    locallyIntegrable_newtonianKernel.neg
  have hInt (i : Fin 3) : Integrable
      (fun y : Vec3 => (-newtonianKernel (z.1 - y)) * gSlice i y) volume := by
    have hi := (hSliceComp i).convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hSliceCont i) hKernel z.1
    simpa [ContinuousLinearMap.lsmul_apply, mul_comm] using hi.integrable
  change ∫ y : Vec3, (-newtonianKernel (z.1 - y)) *
      (∑ i : Fin 3, g i (y, z.2)) =
    ∑ i : Fin 3, ∫ y : Vec3,
      (-newtonianKernel (z.1 - y)) * g i (y, z.2)
  have hintegrand : (fun y : Vec3 => (-newtonianKernel (z.1 - y)) *
      (∑ i : Fin 3, g i (y, z.2))) =
      (fun y => ∑ i : Fin 3, (-newtonianKernel (z.1 - y)) * g i (y, z.2)) := by
    funext y
    rw [Finset.mul_sum]
  rw [hintegrand, integral_finsetSum Finset.univ (by
    intro i hi
    exact hInt i)]

/-- Negation commutes with the Newtonian potential in `lem:helmholtz-test`. -/
theorem associatedPressureNewtonianPotential_neg
    {g : Vec3 × ℝ → ℝ} (z : Vec3 × ℝ) :
    associatedPressureNewtonianPotential (fun q => -g q) z =
      -associatedPressureNewtonianPotential g z := by
  rw [associatedPressureNewtonianPotential, associatedPressureNewtonianPotential,
    CKN.pressureNewtonianPotential, CKN.pressureNewtonianPotential]
  simp only [mul_neg, integral_neg]

private theorem associatedPressureNewtonianPotential_add
    {g h : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (z : Vec3 × ℝ) :
    associatedPressureNewtonianPotential (fun q => g q + h q) z =
      associatedPressureNewtonianPotential g z + associatedPressureNewtonianPotential h z := by
  let f : Fin 3 → Vec3 × ℝ → ℝ := fun k q =>
    if k = 0 then g q else if k = 1 then h q else 0
  have hf (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (f k) := by
    fin_cases k
    · simpa [f] using hg
    · simpa [f] using hh
    · simpa [f] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : Vec3 × ℝ => (0 : ℝ)))
  have hfc (k : Fin 3) : HasCompactSupport (f k) := by
    fin_cases k
    · simpa [f] using hgc
    · simpa [f] using hhc
    · change HasCompactSupport (0 : Vec3 × ℝ → ℝ)
      exact HasCompactSupport.zero
  have hsum : (fun q : Vec3 × ℝ => g q + h q) = fun q => ∑ k : Fin 3, f k q := by
    funext q
    simp [f, Fin.sum_univ_three]
  rw [hsum, associatedPressureNewtonianPotential_finset_sum hf hfc z]
  simp [f, Fin.sum_univ_three, associatedPressureNewtonianPotential,
    CKN.pressureNewtonianPotential]

private theorem associatedPressureNewtonianPotential_sub
    {g h : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (z : Vec3 × ℝ) :
    associatedPressureNewtonianPotential (fun q => g q - h q) z =
      associatedPressureNewtonianPotential g z - associatedPressureNewtonianPotential h z := by
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun q => -h q) := hh.neg
  have hnegc : HasCompactSupport (fun q => -h q) := hhc.neg
  rw [show (fun q : Vec3 × ℝ => g q - h q) = (fun q => g q + -h q) by
    funext q
    ring]
  rw [associatedPressureNewtonianPotential_add hg hgc hneg hnegc z,
    associatedPressureNewtonianPotential_neg]
  ring

private theorem associatedPressureHelmholtzVectorPotential_component_zero
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (z : Vec3 × ℝ) :
    associatedPressureHelmholtzVectorPotential φ z 0 =
      CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (fun q => φ q 1)) 2 z -
        CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (fun q => φ q 2)) 1 z := by
  have hφ₁ := CKN.component_mem_spaceTimeTestFunction hφ 1
  have hφ₂ := CKN.component_mem_spaceTimeTestFunction hφ 2
  have hleft : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun q => φ q 2) 1) :=
    CKN.spatialPartial_contDiff hφ₂.1 1
  have hleftc : HasCompactSupport
      (CKN.spatialPartialProd (fun q => φ q 2) 1) := by
    change HasCompactSupport (fun q : Vec3 × ℝ => CKN.spatialPartial
      (show ParabolicPoint → ℝ from fun w : Vec3 × ℝ => φ w 2) 1 q)
    exact CKN.hasCompactSupport_spatialPartial hφ₂.2.1 1
  have hright : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun q => φ q 1) 2) :=
    CKN.spatialPartial_contDiff hφ₁.1 2
  have hrightc : HasCompactSupport
      (CKN.spatialPartialProd (fun q => φ q 1) 2) := by
    change HasCompactSupport (fun q : Vec3 × ℝ => CKN.spatialPartial
      (show ParabolicPoint → ℝ from fun w : Vec3 × ℝ => φ w 1) 2 q)
    exact CKN.hasCompactSupport_spatialPartial hφ₁.2.1 2
  change -associatedPressureNewtonianPotential
    (fun q => CKN.spatialPartialProd (fun w => φ w 2) 1 q -
      CKN.spatialPartialProd (fun w => φ w 1) 2 q) z = _
  rw [associatedPressureNewtonianPotential_sub hleft hleftc hright hrightc z]
  rw [← associatedPressureNewtonianPotential_spatialPartial hφ₂.1 hφ₂.2.1 1 z,
    ← associatedPressureNewtonianPotential_spatialPartial hφ₁.1 hφ₁.2.1 2 z]
  ring

private theorem associatedPressureHelmholtzVectorPotential_component_one
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (z : Vec3 × ℝ) :
    associatedPressureHelmholtzVectorPotential φ z 1 =
      CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (fun q => φ q 2)) 0 z -
        CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (fun q => φ q 0)) 2 z := by
  have hφ₀ := CKN.component_mem_spaceTimeTestFunction hφ 0
  have hφ₂ := CKN.component_mem_spaceTimeTestFunction hφ 2
  have hleft : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun q => φ q 0) 2) :=
    CKN.spatialPartial_contDiff hφ₀.1 2
  have hleftc : HasCompactSupport
      (CKN.spatialPartialProd (fun q => φ q 0) 2) := by
    change HasCompactSupport (fun q : Vec3 × ℝ => CKN.spatialPartial
      (show ParabolicPoint → ℝ from fun w : Vec3 × ℝ => φ w 0) 2 q)
    exact CKN.hasCompactSupport_spatialPartial hφ₀.2.1 2
  have hright : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun q => φ q 2) 0) :=
    CKN.spatialPartial_contDiff hφ₂.1 0
  have hrightc : HasCompactSupport
      (CKN.spatialPartialProd (fun q => φ q 2) 0) := by
    change HasCompactSupport (fun q : Vec3 × ℝ => CKN.spatialPartial
      (show ParabolicPoint → ℝ from fun w : Vec3 × ℝ => φ w 2) 0 q)
    exact CKN.hasCompactSupport_spatialPartial hφ₂.2.1 0
  change -associatedPressureNewtonianPotential
    (fun q => CKN.spatialPartialProd (fun w => φ w 0) 2 q -
      CKN.spatialPartialProd (fun w => φ w 2) 0 q) z = _
  rw [associatedPressureNewtonianPotential_sub hleft hleftc hright hrightc z]
  rw [← associatedPressureNewtonianPotential_spatialPartial hφ₀.1 hφ₀.2.1 2 z,
    ← associatedPressureNewtonianPotential_spatialPartial hφ₂.1 hφ₂.2.1 0 z]
  ring

private theorem associatedPressureHelmholtzVectorPotential_component_two
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (z : Vec3 × ℝ) :
    associatedPressureHelmholtzVectorPotential φ z 2 =
      CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (fun q => φ q 0)) 1 z -
        CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (fun q => φ q 1)) 0 z := by
  have hφ₀ := CKN.component_mem_spaceTimeTestFunction hφ 0
  have hφ₁ := CKN.component_mem_spaceTimeTestFunction hφ 1
  have hleft : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun q => φ q 1) 0) :=
    CKN.spatialPartial_contDiff hφ₁.1 0
  have hleftc : HasCompactSupport
      (CKN.spatialPartialProd (fun q => φ q 1) 0) := by
    change HasCompactSupport (fun q : Vec3 × ℝ => CKN.spatialPartial
      (show ParabolicPoint → ℝ from fun w : Vec3 × ℝ => φ w 1) 0 q)
    exact CKN.hasCompactSupport_spatialPartial hφ₁.2.1 0
  have hright : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (fun q => φ q 0) 1) :=
    CKN.spatialPartial_contDiff hφ₀.1 1
  have hrightc : HasCompactSupport
      (CKN.spatialPartialProd (fun q => φ q 0) 1) := by
    change HasCompactSupport (fun q : Vec3 × ℝ => CKN.spatialPartial
      (show ParabolicPoint → ℝ from fun w : Vec3 × ℝ => φ w 0) 1 q)
    exact CKN.hasCompactSupport_spatialPartial hφ₀.2.1 1
  change -associatedPressureNewtonianPotential
    (fun q => CKN.spatialPartialProd (fun w => φ w 1) 0 q -
      CKN.spatialPartialProd (fun w => φ w 0) 1 q) z = _
  rw [associatedPressureNewtonianPotential_sub hleft hleftc hright hrightc z]
  rw [← associatedPressureNewtonianPotential_spatialPartial hφ₁.1 hφ₁.2.1 0 z,
    ← associatedPressureNewtonianPotential_spatialPartial hφ₀.1 hφ₀.2.1 1 z]
  ring

/-- A spatial partial derivative distributes over a finite coordinate sum,
used to express the scalar and vector Helmholtz potentials componentwise. -/
theorem associatedPressureSpatialPartial_finset_sum
    (f : Fin 3 → Vec3 × ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (fun q => ∑ j : Fin 3, f j q) i z =
      ∑ j : Fin 3, CKN.spatialPartialProd (f j) i z := by
  let fSlice (j : Fin 3) : Vec3 → ℝ := fun x => f j (x, z.2)
  have hdiff (j : Fin 3) : DifferentiableAt ℝ (fSlice j) z.1 := by
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fSlice j) :=
      (hf j).comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
    exact (hsmooth.differentiable (by simp)) z.1
  change (fderiv ℝ (fun x : Vec3 => ∑ j : Fin 3, fSlice j x) z.1)
      (CKN.basisVec i) = _
  rw [fderiv_fun_sum (u := Finset.univ) (fun j hj => hdiff j)]
  simp [fSlice, CKN.spatialPartialProd, CKN.spatialPartial]

/-- The scalar Helmholtz potential is the sum of the differentiated Newtonian potentials. -/
theorem associatedPressureHelmholtzScalarPotential_eq_sum_spatialPartial
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (z : Vec3 × ℝ) :
    associatedPressureHelmholtzScalarPotential φ z =
      ∑ i : Fin 3, CKN.spatialPartialProd
        (associatedPressureNewtonianPotential (fun q => φ q i)) i z := by
  let source (i : Fin 3) : Vec3 × ℝ → ℝ := fun q =>
    CKN.spatialPartialProd (fun w => φ w i) i q
  have hsourceCont (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (source i) := by
    exact CKN.spatialPartial_contDiff
      (CKN.component_mem_spaceTimeTestFunction hφ i).1 i
  have hsourceComp (i : Fin 3) : HasCompactSupport (source i) := by
    exact CKN.hasCompactSupport_spatialPartial
      (CKN.component_mem_spaceTimeTestFunction hφ i).2.1 i
  have hcomponentCont (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => φ q i) :=
    (CKN.component_mem_spaceTimeTestFunction hφ i).1
  have hcomponentComp (i : Fin 3) : HasCompactSupport
      (fun q : Vec3 × ℝ => φ q i) :=
    (CKN.component_mem_spaceTimeTestFunction hφ i).2.1
  have hsum :
      associatedPressureNewtonianPotential
        (fun q => ∑ i : Fin 3, source i q) z =
        ∑ i : Fin 3, associatedPressureNewtonianPotential (source i) z :=
    associatedPressureNewtonianPotential_finset_sum hsourceCont hsourceComp z
  have hdiv : (fun q => ∑ i : Fin 3, source i q) =
      associatedPressureTestDivergence φ := by
    funext q
    rfl
  change associatedPressureNewtonianPotential
      (associatedPressureTestDivergence φ) z = _
  rw [← hdiv, hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (associatedPressureNewtonianPotential_spatialPartial
    (hcomponentCont i) (hcomponentComp i) i z).symm

/-- The scalar Helmholtz potential gradient is a sum of second derivatives. -/
theorem associatedPressureHelmholtzScalarPotential_direction_eq_sum
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) (z : Vec3 × ℝ) :
    rieszPressureJointDirection (associatedPressureHelmholtzScalarPotential φ) i z =
      ∑ k : Fin 3, CKN.spatialPartialProd
        (CKN.spatialPartialProd
          (associatedPressureNewtonianPotential (fun q => φ q k)) k) i z := by
  have hψsmooth := associatedPressureHelmholtzScalarPotential_contDiff hφ
  rw [← rieszPressure_sliceSpatialDeriv_eq_joint hψsmooth i z]
  have hψfun : associatedPressureHelmholtzScalarPotential φ =
      fun q => ∑ k : Fin 3, CKN.spatialPartialProd
        (associatedPressureNewtonianPotential (fun w => φ w k)) k q := by
    funext q
    exact associatedPressureHelmholtzScalarPotential_eq_sum_spatialPartial hφ q
  rw [hψfun]
  apply associatedPressureSpatialPartial_finset_sum
  intro k
  exact CKN.spatialPartial_contDiff
    (associatedPressureNewtonianPotential_contDiff
      (CKN.component_mem_spaceTimeTestFunction hφ k).1
      (CKN.component_mem_spaceTimeTestFunction hφ k).2.1) k

/-- The scalar Helmholtz potential Hessian is a sum of third derivatives. -/
theorem associatedPressureHelmholtzScalarPotential_hessian_eq_sum
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i j : Fin 3) (z : Vec3 × ℝ) :
    rieszPressureJointHessian (associatedPressureHelmholtzScalarPotential φ) i j z =
      ∑ k : Fin 3, CKN.spatialPartialProd
        (CKN.spatialPartialProd
          (CKN.spatialPartialProd
            (associatedPressureNewtonianPotential (fun q => φ q k)) k) j) i z := by
  let f (k : Fin 3) : Vec3 × ℝ → ℝ := fun q =>
    CKN.spatialPartialProd
      (associatedPressureNewtonianPotential (fun w => φ w k)) k q
  have hf (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (f k) := by
    exact CKN.spatialPartial_contDiff
      (associatedPressureNewtonianPotential_contDiff
        (CKN.component_mem_spaceTimeTestFunction hφ k).1
        (CKN.component_mem_spaceTimeTestFunction hφ k).2.1) k
  let df (k : Fin 3) : Vec3 × ℝ → ℝ := fun q =>
    CKN.spatialPartialProd (f k) j q
  have hdf (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (df k) :=
    CKN.spatialPartial_contDiff (hf k) j
  have hψsmooth := associatedPressureHelmholtzScalarPotential_contDiff hφ
  rw [← rieszPressure_sliceMixedSecond_eq_joint hψsmooth i j z]
  have hψfun : associatedPressureHelmholtzScalarPotential φ =
      fun q => ∑ k : Fin 3, f k q := by
    funext q
    exact associatedPressureHelmholtzScalarPotential_eq_sum_spatialPartial hφ q
  rw [hψfun]
  change CKN.spatialDeriv
      (CKN.spatialDeriv (fun x : Vec3 => ∑ k : Fin 3, f k (x, z.2)) j)
      i z.1 = _
  have hfirst : (fun q => CKN.spatialPartialProd
      (fun w => ∑ k : Fin 3, f k w) j q) = fun q => ∑ k : Fin 3, df k q := by
    funext q
    exact associatedPressureSpatialPartial_finset_sum f hf j q
  have hfirstSlice :
      CKN.spatialDeriv (fun x : Vec3 => ∑ k : Fin 3, f k (x, z.2)) j =
        fun x => ∑ k : Fin 3, df k (x, z.2) := by
    funext x
    have h := congrFun hfirst (x, z.2)
    simpa [CKN.spatialPartialProd, CKN.spatialPartial, CKN.spatialDeriv, df] using h
  rw [hfirstSlice]
  change CKN.spatialPartialProd (fun q => ∑ k : Fin 3, df k q) i z = _
  exact associatedPressureSpatialPartial_finset_sum df hdf i z

end CKN.Leray

end

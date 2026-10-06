/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Setting.PressureGaugeSlices
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.ProductH1
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistribution
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientProduct

/-!
# Weak vorticity equation

The slice weak-gradient data in suitability identify the explicit velocity
gradient used to define vorticity.
-/

public section


open MeasureTheory
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

/-- The spatial curl of a smooth vector test field. -/
@[expose] def spatialTestCurl (ψ : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  fun i => Fin.cases
    (CKN.spatialDeriv (fun y => ψ y 2) 1 x -
      CKN.spatialDeriv (fun y => ψ y 1) 2 x)
    (fun j => Fin.cases
      (CKN.spatialDeriv (fun y => ψ y 0) 2 x -
        CKN.spatialDeriv (fun y => ψ y 2) 0 x)
      (fun k => Fin.cases
        (CKN.spatialDeriv (fun y => ψ y 1) 0 x -
          CKN.spatialDeriv (fun y => ψ y 0) 1 x)
        (fun l => Fin.elim0 l) k) j) i

@[simp]
theorem spatialTestCurl_zero (ψ : Vec3 → Vec3) (x : Vec3) :
    spatialTestCurl ψ x 0 =
      CKN.spatialDeriv (fun y => ψ y 2) 1 x -
        CKN.spatialDeriv (fun y => ψ y 1) 2 x := rfl

@[simp]
theorem spatialTestCurl_one (ψ : Vec3 → Vec3) (x : Vec3) :
    spatialTestCurl ψ x 1 =
      CKN.spatialDeriv (fun y => ψ y 0) 2 x -
        CKN.spatialDeriv (fun y => ψ y 2) 0 x := rfl

@[simp]
theorem spatialTestCurl_two (ψ : Vec3 → Vec3) (x : Vec3) :
    spatialTestCurl ψ x 2 =
      CKN.spatialDeriv (fun y => ψ y 1) 0 x -
        CKN.spatialDeriv (fun y => ψ y 0) 1 x := rfl

/-- The classical cross product in the native three-component carrier. -/
@[expose] def spatialCross (u ω : Vec3) : Vec3 :=
  fun i => Fin.cases
    (u 1 * ω 2 - u 2 * ω 1)
    (fun j => Fin.cases
      (u 2 * ω 0 - u 0 * ω 2)
      (fun k => Fin.cases (u 0 * ω 1 - u 1 * ω 0)
        (fun l => Fin.elim0 l) k) j) i

@[simp]
theorem spatialCross_zero (u ω : Vec3) :
    spatialCross u ω 0 = u 1 * ω 2 - u 2 * ω 1 := rfl

@[simp]
theorem spatialCross_one (u ω : Vec3) :
    spatialCross u ω 1 = u 2 * ω 0 - u 0 * ω 2 := rfl

@[simp]
theorem spatialCross_two (u ω : Vec3) :
    spatialCross u ω 2 = u 0 * ω 1 - u 1 * ω 0 := rfl

/-- The curl determined by a spatial weak gradient. -/
@[expose] def spatialWeakVorticity (Du : Vec3 → Fin 3 → Vec3) (x : Vec3) : Vec3 :=
  fun i => Fin.cases
    (Du x 2 1 - Du x 1 2)
    (fun j => Fin.cases
      (Du x 0 2 - Du x 2 0)
      (fun k => Fin.cases (Du x 1 0 - Du x 0 1)
        (fun l => Fin.elim0 l) k) j) i

@[simp]
theorem spatialWeakVorticity_zero (Du : Vec3 → Fin 3 → Vec3) (x : Vec3) :
    spatialWeakVorticity Du x 0 = Du x 2 1 - Du x 1 2 := rfl

@[simp]
theorem spatialWeakVorticity_one (Du : Vec3 → Fin 3 → Vec3) (x : Vec3) :
    spatialWeakVorticity Du x 1 = Du x 0 2 - Du x 2 0 := rfl

@[simp]
theorem spatialWeakVorticity_two (Du : Vec3 → Fin 3 → Vec3) (x : Vec3) :
    spatialWeakVorticity Du x 2 = Du x 1 0 - Du x 0 1 := rfl

/-- The weak-gradient curl gives the usual convective-term identity in three
dimensions. -/
theorem spatialConvective_decomposition
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (x : Vec3) (i : Fin 3) :
    (∑ j : Fin 3, u x j * Du x i j) =
      (∑ j : Fin 3, u x j * Du x j i) -
        spatialCross (u x) (spatialWeakVorticity Du x) i := by
  fin_cases i
  · change (∑ j : Fin 3, u x j * Du x 0 j) =
      (∑ j : Fin 3, u x j * Du x j 0) -
        spatialCross (u x) (spatialWeakVorticity Du x) 0
    rw [spatialCross_zero, spatialWeakVorticity_one, spatialWeakVorticity_two]
    simp only [Fin.sum_univ_three]
    ring
  · change (∑ j : Fin 3, u x j * Du x 1 j) =
      (∑ j : Fin 3, u x j * Du x j 1) -
        spatialCross (u x) (spatialWeakVorticity Du x) 1
    rw [spatialCross_one, spatialWeakVorticity_zero, spatialWeakVorticity_two]
    simp only [Fin.sum_univ_three]
    ring
  · change (∑ j : Fin 3, u x j * Du x 2 j) =
      (∑ j : Fin 3, u x j * Du x j 2) -
        spatialCross (u x) (spatialWeakVorticity Du x) 2
    rw [spatialCross_two, spatialWeakVorticity_zero, spatialWeakVorticity_one]
    simp only [Fin.sum_univ_three]
    ring

private theorem vorticityIntegrableProductTest
    {U : Set Vec3} {a b φ : Vec3 → ℝ}
    (hUfinite : (volume.restrict U) Set.univ < ⊤)
    (ha : MemLp a 2 (volume.restrict U))
    (hb : MemLp b 2 (volume.restrict U))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    IntegrableOn (fun x => a x * b x * φ x) U volume := by
  let μ := volume.restrict U
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ENNReal.HolderConjugate.instTwoTwo
  let : IsFiniteMeasure μ := ⟨hUfinite⟩
  have hab : MemLp (fun x => a x * b x) 1 μ := ha.mul hb
  have hφtop : MemLp φ (⊤ : ℝ≥0∞) μ :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφc μ
  have hprod : MemLp (fun x => a x * b x * φ x) 1 μ := hab.mul hφtop
  exact hprod.integrable (by norm_num)

private theorem suitableWeakProductPartialPairing
    {U : Set Vec3} (hU : IsOpen U)
    (hUfinite : (volume.restrict U) Set.univ < ⊤)
    {a b : Vec3 → ℝ} {Da Db : Vec3 → Fin 3 → ℝ}
    (ha : MemLp a 2 (volume.restrict U)) (hb : MemLp b 2 (volume.restrict U))
    (hDa : ∀ i, MemLp (fun x => Da x i) 2 (volume.restrict U))
    (hDb : ∀ i, MemLp (fun x => Db x i) 2 (volume.restrict U))
    (hwa : CKN.HasWeakGradientOn U a Da) (hwb : CKN.HasWeakGradientOn U b Db)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (k : Fin 3) :
    (∫ x in U, a x * b x * CKN.spatialDeriv φ k x) =
      -∫ x in U, (Da x k * b x + a x * Db x k) * φ x := by
  have hprod : CKN.HasWeakGradientOn U (fun x => a x * b x)
      (fun x k => Da x k * b x + a x * Db x k) :=
    CKN.HasWeakGradientOn.mul_of_memLp_two hU ha hb hDa hDb hwa hwb
  have hφd : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv φ k) :=
    CKN.contDiff_spatialDeriv_smooth hφ k
  have hφdc : HasCompactSupport (CKN.spatialDeriv φ k) :=
    CKN.hasCompactSupport_spatialDeriv hφc k
  have hleft : IntegrableOn
      (fun x => a x * b x * CKN.spatialDeriv φ k x) U volume :=
    vorticityIntegrableProductTest hUfinite ha hb hφd hφdc
  have hright₁ : IntegrableOn (fun x => Da x k * b x * φ x) U volume :=
    vorticityIntegrableProductTest hUfinite (hDa k) hb hφ hφc
  have hright₂ : IntegrableOn (fun x => a x * Db x k * φ x) U volume :=
    vorticityIntegrableProductTest hUfinite ha (hDb k) hφ hφc
  have hright : IntegrableOn
      (fun x => (Da x k * b x + a x * Db x k) * φ x) U volume := by
    have heq : (fun x => (Da x k * b x + a x * Db x k) * φ x) =
        (fun x => Da x k * b x * φ x + a x * Db x k * φ x) := by
      funext x
      ring
    rw [heq]
    exact hright₁.add hright₂
  have h := hprod k φ hφ hφc hφU
  simpa only [CKN.spatialDeriv] using h

/-- A spatial product pairing for the convection tensor, obtained from the
slice weak-gradient identities (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakConvectionProductPairing
    {U : Set Vec3} (hU : IsOpen U)
    (hUfinite : (volume.restrict U) Set.univ < ⊤)
    {v : Vec3 → Vec3} {Dv : Vec3 → Fin 3 → Vec3}
    (hv : ∀ i : Fin 3, MemLp (fun x => v x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin 3, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => v x i) (fun x => Dv x i))
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (i : Fin 3) :
    (∫ x in U, ∑ j : Fin 3,
        v x i * v x j * CKN.spatialDeriv φ j x) =
      -∫ x in U, ∑ j : Fin 3,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x := by
  have hprod : ∀ j : Fin 3,
      CKN.HasWeakGradientOn U (fun x => v x i * v x j)
        (fun x k => Dv x i k * v x j + v x i * Dv x j k) := by
    intro j
    exact CKN.HasWeakGradientOn.mul_of_memLp_two hU (hv i) (hv j)
      (fun k => (memLp_pi_iff.mp (hDv i)) k)
      (fun k => (memLp_pi_iff.mp (hDv j)) k) (hweak i) (hweak j)
  have hφd (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv φ j) :=
    CKN.contDiff_spatialDeriv_smooth hφ j
  have hφdc (j : Fin 3) : HasCompactSupport (CKN.spatialDeriv φ j) :=
    CKN.hasCompactSupport_spatialDeriv hφc j
  have hleft (j : Fin 3) : IntegrableOn
      (fun x => v x i * v x j * CKN.spatialDeriv φ j x) U volume :=
    vorticityIntegrableProductTest hUfinite (hv i) (hv j) (hφd j) (hφdc j)
  have hright₁ (j : Fin 3) : IntegrableOn
      (fun x => Dv x i j * v x j * φ x) U volume :=
    vorticityIntegrableProductTest hUfinite ((memLp_pi_iff.mp (hDv i)) j) (hv j) hφ hφc
  have hright₂ (j : Fin 3) : IntegrableOn
      (fun x => v x i * Dv x j j * φ x) U volume :=
    vorticityIntegrableProductTest hUfinite (hv i) ((memLp_pi_iff.mp (hDv j)) j) hφ hφc
  have hright (j : Fin 3) : IntegrableOn
      (fun x => (Dv x i j * v x j + v x i * Dv x j j) * φ x) U volume := by
    have heq : (fun x => (Dv x i j * v x j + v x i * Dv x j j) * φ x) =
        (fun x => Dv x i j * v x j * φ x + v x i * Dv x j j * φ x) := by
      funext x
      ring
    rw [heq]
    exact (hright₁ j).add (hright₂ j)
  have hpair (j : Fin 3) :
      (∫ x in U, v x i * v x j * CKN.spatialDeriv φ j x) =
        -(∫ x in U, (Dv x i j * v x j + v x i * Dv x j j) * φ x) := by
    have h := hprod j j φ hφ hφc hφU
    simpa only [CKN.spatialDeriv] using h
  calc
    (∫ x in U, ∑ j : Fin 3,
        v x i * v x j * CKN.spatialDeriv φ j x) =
        ∑ j : Fin 3, ∫ x in U,
          v x i * v x j * CKN.spatialDeriv φ j x := by
            rw [integral_finsetSum _ (fun j _ => hleft j)]
    _ = ∑ j : Fin 3, -(∫ x in U,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hpair j
    _ = -(∑ j : Fin 3, ∫ x in U,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x) := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x in U, ∑ j : Fin 3,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x := by
          rw [integral_finsetSum _ (fun j _ => hright j)]

/-- The vector convection tensor paired against a compact smooth field reduces
to the weak-gradient product rule on suitable slices (manuscript
`lem:vorticity-weak-eq`). -/
theorem suitableWeakConvectionTensorPairing
    {U : Set Vec3} (hU : IsOpen U)
    (hUfinite : (volume.restrict U) Set.univ < ⊤)
    {v : Vec3 → Vec3} {Dv : Vec3 → Fin 3 → Vec3}
    (hv : ∀ i : Fin 3, MemLp (fun x => v x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin 3, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => v x i) (fun x => Dv x i))
    {φ : Vec3 → Vec3}
    (hφ : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x i))
    (hφc : ∀ i : Fin 3, HasCompactSupport (fun x => φ x i))
    (hφU : ∀ i : Fin 3, tsupport (fun x => φ x i) ⊆ U) :
    (∑ i : Fin 3, ∫ x in U, ∑ j : Fin 3,
        v x i * v x j * CKN.spatialDeriv (fun y => φ y i) j x) =
      -∑ i : Fin 3, ∫ x in U, ∑ j : Fin 3,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x i := by
  calc
    (∑ i : Fin 3, ∫ x in U, ∑ j : Fin 3,
        v x i * v x j * CKN.spatialDeriv (fun y => φ y i) j x) =
      ∑ i : Fin 3, -(∫ x in U, ∑ j : Fin 3,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact suitableWeakConvectionProductPairing hU hUfinite hv hDv hweak
            (hφ i) (hφc i) (hφU i) i
    _ = -∑ i : Fin 3, ∫ x in U, ∑ j : Fin 3,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x i := by
          rw [Finset.sum_neg_distrib]

/-- The gradient part of convection pairs to zero against a divergence-free
compact test field (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakGradientPairingZero
    {U : Set Vec3} (hU : IsOpen U)
    (hUfinite : (volume.restrict U) Set.univ < ⊤)
    {v : Vec3 → Vec3} {Dv : Vec3 → Fin 3 → Vec3}
    (hv : ∀ i : Fin 3, MemLp (fun x => v x i) 2 (volume.restrict U))
    (hDv : MemLp Dv 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => v x i) (fun x => Dv x i))
    {φ : Vec3 → Vec3}
    (hφ : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x i))
    (hφc : ∀ i : Fin 3, HasCompactSupport (fun x => φ x i))
    (hφU : ∀ i : Fin 3, tsupport (fun x => φ x i) ⊆ U)
    (hdivφ : ∀ x, ∑ i : Fin 3, CKN.spatialDeriv (fun y => φ y i) i x = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x in U, v x j * Dv x j i * φ x i) = 0 := by
  have hDvVec (j : Fin 3) : MemLp (fun x => Dv x j) 2 (volume.restrict U) :=
    (memLp_pi_iff.mp hDv) j
  have hDvCoord (j k : Fin 3) : MemLp (fun x => Dv x j k) 2
      (volume.restrict U) := (memLp_pi_iff.mp (hDvVec j)) k
  have hφd (i k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialDeriv (fun x => φ x i) k) :=
    CKN.contDiff_spatialDeriv_smooth (hφ i) k
  have hφdc (i k : Fin 3) : HasCompactSupport
      (CKN.spatialDeriv (fun x => φ x i) k) :=
    CKN.hasCompactSupport_spatialDeriv (hφc i) k
  have hφdkU (i k : Fin 3) :
      tsupport (CKN.spatialDeriv (fun x => φ x i) k) ⊆ U :=
    (CKN.tsupport_spatialDeriv_subset k).trans (hφU i)
  have hleftTerm (i j : Fin 3) : IntegrableOn
      (fun x => v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x)
      U volume :=
    vorticityIntegrableProductTest hUfinite (hv j) (hv j)
      (hφd i i) (hφdc i i)
  have hrightTerm (i j : Fin 3) : IntegrableOn
      (fun x => v x j * Dv x j i * φ x i) U volume :=
    vorticityIntegrableProductTest hUfinite (hv j) (hDvCoord j i)
      (hφ i) (hφc i)
  have hpair (i j : Fin 3) :
      (∫ x in U, v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) =
        -(2 * ∫ x in U, v x j * Dv x j i * φ x i) := by
    have hp := suitableWeakProductPartialPairing hU hUfinite (hv j) (hv j)
      (fun k => (memLp_pi_iff.mp (hDvVec j)) k)
      (fun k => (memLp_pi_iff.mp (hDvVec j)) k)
      (hweak j) (hweak j) (hφ i) (hφc i) (hφU i) i
    calc
      (∫ x in U, v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) =
          -∫ x in U, (Dv x j i * v x j + v x j * Dv x j i) * φ x i := hp
      _ = -(2 * ∫ x in U, v x j * Dv x j i * φ x i) := by
          congr 1
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
  have hleftSum (j : Fin 3) : IntegrableOn
      (fun x => ∑ i : Fin 3,
        v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) U volume :=
    integrable_finsetSum _ (fun i _ => hleftTerm i j)
  have hleftZero (j : Fin 3) :
      (∫ x in U, ∑ i : Fin 3,
        v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) = 0 := by
    have heq : (fun x => ∑ i : Fin 3,
        v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) =
        (fun x => v x j * v x j *
          ∑ i : Fin 3, CKN.spatialDeriv (fun y => φ y i) i x) := by
      funext x
      rw [Finset.mul_sum]
    have hzero : (fun x => v x j * v x j *
        ∑ i : Fin 3, CKN.spatialDeriv (fun y => φ y i) i x) =ᵐ[volume.restrict U] 0 := by
      filter_upwards [] with x
      calc
        v x j * v x j *
            ∑ i : Fin 3, CKN.spatialDeriv (fun y => φ y i) i x =
          v x j * v x j * 0 := by rw [hdivφ x]
        _ = 0 := by ring
    calc
      _ = ∫ x in U, v x j * v x j *
          ∑ i : Fin 3, CKN.spatialDeriv (fun y => φ y i) i x := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => congrFun heq x
      _ = 0 := by
          rw [integral_congr_ae hzero]
          simp
  have hpairSum :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U, v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) =
        -(2 * ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x in U, v x j * Dv x j i * φ x i) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          -(2 * ∫ x in U, v x j * Dv x j i * φ x i) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            exact hpair i j
      _ = _ := by simp [Finset.sum_neg_distrib, Finset.mul_sum]
  have hleftAll :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U, v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) = 0 := by
    rw [Finset.sum_comm]
    have hsum (j : Fin 3) :
        (∑ i : Fin 3, ∫ x in U,
          v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x) =
        ∫ x in U, ∑ i : Fin 3,
          v x j * v x j * CKN.spatialDeriv (fun y => φ y i) i x := by
      rw [integral_finsetSum _ (fun i _ => hleftTerm i j)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hsum j]
    exact hleftZero j
  have hGzero : ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x in U, v x j * Dv x j i * φ x i = 0 := by
    have heq := hpairSum
    rw [hleftAll] at heq
    have hmul : 2 * (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U, v x j * Dv x j i * φ x i) = 0 := by
      linarith only [heq]
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  exact hGzero

/-- The antisymmetric flux pairing is the cross-product pairing with the
spatial curl of the test field. -/
theorem vorticityFlux_spatialTestCurl_pairing
    (u ω : Vec3) (ψ : Vec3 → Vec3) (x : Vec3) :
    (∑ j : Fin 3, ∑ i : Fin 3,
        (u j * ω i - ω j * u i) * CKN.spatialDeriv (fun y => ψ y i) j x) =
      ∑ k : Fin 3, spatialCross u ω k * spatialTestCurl ψ x k := by
  simp only [Fin.sum_univ_three, spatialCross_zero, spatialCross_one,
    spatialCross_two, spatialTestCurl_zero, spatialTestCurl_one,
    spatialTestCurl_two]
  ring

/-- The CKN spatial partial derivative written on ordinary product
coordinates. -/
@[expose] def vorticityTestPartial (f : Vec3 × ℝ → ℝ) (i : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  (fderiv ℝ (fun x : Vec3 => f (x, z.2)) z.1) (CKN.basisVec i)

theorem vorticityTestPartial_eq_spatialPartial
    (f : Vec3 × ℝ → ℝ) (i : Fin 3) (z : Vec3 × ℝ) :
    vorticityTestPartial f i z = CKN.spatialPartial f i z := rfl

/-- The classical spatial curl of a smooth vector test field, using CKN's
factor-wise spatial partial derivatives (manuscript `lem:vorticity-weak-eq`). -/
@[expose] def vorticityTestCurl (ψ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : Vec3 :=
  fun i => Fin.cases
    (vorticityTestPartial (fun w => ψ w 2) 1 z -
      vorticityTestPartial (fun w => ψ w 1) 2 z)
    (fun j => Fin.cases
      (vorticityTestPartial (fun w => ψ w 0) 2 z -
        vorticityTestPartial (fun w => ψ w 2) 0 z)
      (fun k => Fin.cases
        (vorticityTestPartial (fun w => ψ w 1) 0 z -
          vorticityTestPartial (fun w => ψ w 0) 1 z)
        (fun l => Fin.elim0 l) k) j) i

@[simp]
theorem vorticityTestCurl_zero (ψ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) :
    vorticityTestCurl ψ z 0 =
      vorticityTestPartial (fun w => ψ w 2) 1 z -
        vorticityTestPartial (fun w => ψ w 1) 2 z := rfl

@[simp]
theorem vorticityTestCurl_one (ψ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) :
    vorticityTestCurl ψ z 1 =
      vorticityTestPartial (fun w => ψ w 0) 2 z -
        vorticityTestPartial (fun w => ψ w 2) 0 z := rfl

@[simp]
theorem vorticityTestCurl_two (ψ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) :
    vorticityTestCurl ψ z 2 =
      vorticityTestPartial (fun w => ψ w 1) 0 z -
        vorticityTestPartial (fun w => ψ w 0) 1 z := rfl

/-- Curl preserves the compact smooth test class and its support. -/
theorem vorticityTestCurl_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) :
    vorticityTestCurl ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I := by
  rcases hψ with ⟨hψsmooth, hψcompact, hψsupport⟩
  have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ψ z i) :=
    (contDiff_apply ℝ ℝ i).comp hψsmooth
  have hpartSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => vorticityTestPartial (fun w => ψ w i) j z) := by
    have h := CKN.spatialPartial_contDiff (hcomp i) j
    convert h using 1
    funext z
    exact vorticityTestPartial_eq_spatialPartial (fun w => ψ w i) j z
  have hsmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => vorticityTestCurl ψ z i) := by
    fin_cases i
    · exact (hpartSmooth 2 1).sub (hpartSmooth 1 2)
    · exact (hpartSmooth 0 2).sub (hpartSmooth 2 0)
    · exact (hpartSmooth 1 0).sub (hpartSmooth 0 1)
  have hzero (z : Vec3 × ℝ) (hz : z ∉ tsupport ψ) :
    vorticityTestCurl ψ z = 0 := by
    apply funext
    intro i
    have hc (j : Fin 3) : z ∉ tsupport (fun w : Vec3 × ℝ => ψ w j) := by
      intro hmem
      have hsub : tsupport (fun w : Vec3 × ℝ => ψ w j) ⊆ tsupport ψ :=
        CKN.tsupport_component_subset (V := Vec3) (ι := Fin 3) ψ j
          (by intro w hw; simp [hw])
      exact hz (hsub hmem)
    have hpartZero (j k : Fin 3) :
        vorticityTestPartial (fun w : Vec3 × ℝ => ψ w j) k z = 0 := by
      rw [vorticityTestPartial_eq_spatialPartial]
      exact CKN.spatialPartial_eq_zero_off_tsupport (hc j) k
    fin_cases i
    · change vorticityTestCurl ψ z 0 = 0
      rw [vorticityTestCurl_zero]
      rw [hpartZero 2 1, hpartZero 1 2]
      ring
    · change vorticityTestCurl ψ z 1 = 0
      rw [vorticityTestCurl_one]
      rw [hpartZero 0 2, hpartZero 2 0]
      ring
    · change vorticityTestCurl ψ z 2 = 0
      rw [vorticityTestCurl_two]
      rw [hpartZero 1 0, hpartZero 0 1]
      ring
  have hfunSupport : Function.support (vorticityTestCurl ψ) ⊆ tsupport ψ := by
    intro z hz
    by_contra hnot
    exact hz (hzero z hnot)
  have htsupport : tsupport (vorticityTestCurl ψ) ⊆ tsupport ψ :=
    closure_minimal hfunSupport (isClosed_tsupport ψ)
  refine ⟨contDiff_pi.2 hsmooth, ?_, htsupport.trans hψsupport⟩
  exact hψcompact.isCompact.of_isClosed_subset (isClosed_tsupport _)
    htsupport

/-- Mixed spatial derivatives of a smooth scalar test commute, expressed in
product coordinates (manuscript `lem:vorticity-weak-eq`). -/
theorem vorticityTestPartial_spatialPartial_commute
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    vorticityTestPartial (fun w => vorticityTestPartial ψ i w) j z =
      vorticityTestPartial (fun w => vorticityTestPartial ψ j w) i z := by
  let φ : Vec3 → ℝ := fun x => ψ (x, z.2)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.prodMk contDiff_const)
  have hswap := CKN.mixedSecond_swap hφ i j z.1
  change CKN.mixedSecond φ j i z.1 = CKN.mixedSecond φ i j z.1
  exact hswap.symm

/-- Spatial differentiation distributes over subtraction of smooth tests. -/
theorem vorticityTestPartial_sub_smooth
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (z : Vec3 × ℝ) :
    vorticityTestPartial (fun w => f w - g w) i z =
      vorticityTestPartial f i z - vorticityTestPartial g i z := by
  let F : Vec3 → ℝ := fun x => f (x, z.2)
  let G : Vec3 → ℝ := fun x => g (x, z.2)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hf.comp (contDiff_id.prodMk contDiff_const)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := hg.comp (contDiff_id.prodMk contDiff_const)
  have hFd : DifferentiableAt ℝ F z.1 := (hF.differentiable (by simp)) z.1
  have hGd : DifferentiableAt ℝ G z.1 := (hG.differentiable (by simp)) z.1
  have hsub := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (fderiv_fun_sub hFd hGd)
  simpa only [vorticityTestPartial, F, G, sub_apply] using hsub

/-- The curl test is divergence-free. -/
theorem vorticityTestCurl_divergence
    {ψ : Vec3 × ℝ → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : Vec3 × ℝ) :
    ∑ i : Fin 3, vorticityTestPartial
      (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) i z = 0 := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => ψ w 0) :=
    (contDiff_apply ℝ ℝ 0).comp hψ
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => ψ w 1) :=
    (contDiff_apply ℝ ℝ 1).comp hψ
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => ψ w 2) :=
    (contDiff_apply ℝ ℝ 2).comp hψ
  have hpartSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => vorticityTestPartial (fun x => ψ x i) j w) := by
    have h := CKN.spatialPartial_contDiff
      (show ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 × ℝ => ψ x i) from
        (contDiff_apply ℝ ℝ i).comp hψ) j
    convert h using 1
    funext w
    exact vorticityTestPartial_eq_spatialPartial (fun x => ψ x i) j w
  rw [Fin.sum_univ_three]
  change vorticityTestPartial (fun w : Vec3 × ℝ => vorticityTestCurl ψ w 0) 0 z +
      vorticityTestPartial (fun w : Vec3 × ℝ => vorticityTestCurl ψ w 1) 1 z +
      vorticityTestPartial (fun w : Vec3 × ℝ => vorticityTestCurl ψ w 2) 2 z = 0
  simp only [vorticityTestCurl_zero, vorticityTestCurl_one, vorticityTestCurl_two]
  rw [vorticityTestPartial_sub_smooth (hpartSmooth 2 1)
      (hpartSmooth 1 2) 0 z,
    vorticityTestPartial_sub_smooth (hpartSmooth 0 2)
      (hpartSmooth 2 0) 1 z,
    vorticityTestPartial_sub_smooth (hpartSmooth 1 0)
      (hpartSmooth 0 1) 2 z]
  rw [vorticityTestPartial_spatialPartial_commute h2 1 0 z,
    vorticityTestPartial_spatialPartial_commute h1 2 0 z,
    vorticityTestPartial_spatialPartial_commute h0 2 1 z]
  ring

/-- Suitable solutions carry the spatial weak-gradient identity on almost every
time slice of each local box (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakGradientOnSlices
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    (Ω' : Set Vec3) (J : Set ℝ) (hbox : CKN.localBox Ω I Ω' J)
    (i : Fin 3) :
    ∀ᵐ s ∂(volume.restrict J),
      CKN.HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) := by
  rcases h with ⟨_, _, _, _, _, hdata, _, _, _⟩
  exact (hdata Ω' J hbox).2.2.2.2.2.2.2.2 i

/-- The spatial weak-gradient trace vanishes on almost every local slice of a
suitable solution (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakGradientTraceZeroOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    (Ω' : Set Vec3) (J : Set ℝ) (hbox : CKN.localBox Ω I Ω' J) :
    ∀ᵐ s ∂(volume.restrict J),
      (fun x => ∑ i : Fin 3, Du (x, s) i i) =ᵐ[volume.restrict Ω'] 0 := by
  have hInt : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ => 0) :=
    CKN.isSuitableWeakSolution_iff_integrable.mp h
  have hmem := CKN.slice_memLp_ae_of_sws hInt hbox
  have hweak : ∀ᵐ s ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i) := by
    rw [ae_all_iff]
    exact suitableWeakGradientOnSlices h Ω' J hbox
  have hlocal : ∀ᵐ s ∂(volume.restrict J), ∀ i : Fin 3,
      LocallyIntegrableOn (fun x => u (x, s) i) Ω' volume := by
    filter_upwards [hmem] with s hs i
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (((memLp_pi_iff.mp hs.1) i).locallyIntegrable (by norm_num))
  have hdivTest : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω' →
      ∀ᵐ s ∂(volume.restrict J),
        ∫ x in Ω', ∑ i : Fin 3, u (x, s) i *
          (fderiv ℝ ψ x) (CKN.basisVec i) = 0 := by
    intro ψ hψ hψc hψΩ'
    have hψΩ : tsupport ψ ⊆ Ω :=
      hψΩ'.trans (subset_closure.trans hbox.2.2.1)
    have hJI : J ⊆ I := subset_closure.trans hbox.2.2.2.2.2
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI
      (CKN.divfree_slice_weak_of_suitable hInt ψ hψ hψc hψΩ)] with s hs
    have hzero (A : Set Vec3) (hA : tsupport ψ ⊆ A) :
        (∫ x in A, ∑ i : Fin 3, u (x, s) i *
          (fderiv ℝ ψ x) (CKN.basisVec i)) =
        ∫ x, ∑ i : Fin 3, u (x, s) i *
          (fderiv ℝ ψ x) (CKN.basisVec i) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hψx : x ∉ tsupport ψ := fun hmem => hx (hA hmem)
      have hD (i : Fin 3) :
          (fderiv ℝ ψ x) (CKN.basisVec i) = 0 := by
        have hnot : x ∉ tsupport (CKN.spatialDeriv ψ i) := by
          intro hi
          exact hψx (CKN.tsupport_spatialDeriv_subset i hi)
        have hz : CKN.spatialDeriv ψ i x = 0 :=
          image_eq_zero_of_notMem_tsupport hnot
        simpa only [CKN.spatialDeriv] using hz
      simp [hD]
    rw [hzero Ω' hψΩ', ← hzero Ω hψΩ]
    exact hs
  have hdiv := CKN.ae_slice_divergence_zero_of_forall_test hbox.1
    hlocal hdivTest
  filter_upwards [hmem, hweak, hdiv] with s hs hw hd
  exact CKN.Core.Step4.weak_gradient_trace_eq_zero_ae hbox.1
    (fun i => (memLp_pi_iff.mp hs.1) i)
    (fun i j => (memLp_pi_iff.mp ((memLp_pi_iff.mp hs.2) i)) j)
    hw hd

/-- Slice weak gradients integrate by parts against smooth space-time tests on
a local box (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakSpatialIntegrationByParts
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    (Ω' : Set Vec3) (J : Set ℝ) (hbox : CKN.localBox Ω I Ω' J)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψsupport : tsupport ψ ⊆ Ω' ×ˢ J)
    (i j : Fin 3) :
    (∫ t in J, ∫ x in Ω', Du (x, t) i j * ψ (x, t)) =
      -∫ t in J, ∫ x in Ω', u (x, t) i * CKN.spatialPartial ψ j (x, t) := by
  have hslice := suitableWeakGradientOnSlices h Ω' J hbox i
  have hpair : ∀ᵐ t ∂(volume.restrict J),
      (∫ x in Ω', Du (x, t) i j * ψ (x, t)) =
        -(∫ x in Ω', u (x, t) i * CKN.spatialPartial ψ j (x, t)) := by
    filter_upwards [hslice] with t ht
    have hs := CKN.slice_testFunction hψ hψc hψsupport t
    have hweak := ht j (fun x : Vec3 => ψ (x, t)) hs.1 hs.2.1 hs.2.2
    have hweak' :
        (∫ x in Ω', u (x, t) i * CKN.spatialPartial ψ j (x, t)) =
          -∫ x in Ω', Du (x, t) i j * ψ (x, t) := by
      simpa only [CKN.spatialPartial] using hweak
    simpa only [neg_neg] using (congrArg Neg.neg hweak').symm
  calc
    (∫ t in J, ∫ x in Ω', Du (x, t) i j * ψ (x, t)) =
        ∫ t in J, -(∫ x in Ω', u (x, t) i * CKN.spatialPartial ψ j (x, t)) :=
      integral_congr_ae hpair
    _ = -∫ t in J, ∫ x in Ω', u (x, t) i * CKN.spatialPartial ψ j (x, t) := by
      rw [integral_neg]

end

end ESS

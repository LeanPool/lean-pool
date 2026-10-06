/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyEquality
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyLimitAlgebra
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Constructor
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

local instance localEnergyLimitHolderTripleFourFourTwo :
    ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  have hreal : Real.HolderTriple 4 4 2 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitHolderTripleFourFourFourThirds :
    ENNReal.HolderTriple 2 4 (ENNReal.ofReal (4 / 3 : ℝ)) := by
  have hreal : Real.HolderTriple 2 4 (4 / 3) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitHolderTripleFourThirdsFourOne :
    ENNReal.HolderTriple (ENNReal.ofReal (4 / 3 : ℝ)) 4 1 := by
  have hreal : Real.HolderTriple (4 / 3) 4 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitHolderTripleThreeHalvesFourTwelveElevenths :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 4
      (ENNReal.ofReal (12 / 11 : ℝ)) := by
  have hreal : Real.HolderTriple (3 / 2) 4 (12 / 11) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitHolderTripleTwelveEleventhsTwelveOne :
    ENNReal.HolderTriple (ENNReal.ofReal (12 / 11 : ℝ)) 12 1 := by
  have hreal : Real.HolderTriple (12 / 11) 12 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitHolderTripleTwoTwoOne :
    ENNReal.HolderTriple 2 2 1 := by
  have hreal : Real.HolderTriple 2 2 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

/-- The zero-extended local energy density has zero integral for each smooth
test supported strictly inside the unit cylinder. -/
theorem localEnergy_mollifiedBase_integral_limit_zero
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ localEnergyUnitProductCylinder) :
    ∫ z, localEnergyLimitExpandedBaseIntegrand
      (fun z i => localEnergyVelocityZeroExtension u i z)
      (fun _ => 0)
      (fun z i j => localEnergyGradientZeroExtension Du i j z)
      (localEnergyPressureZeroExtension p) (show ParabolicPoint → ℝ from ψ) z
      ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
  let U : Set (Vec3 × ℝ) := localEnergyUnitProductCylinder
  let u0 : Vec3 × ℝ → Vec3 := fun z i => localEnergyVelocityZeroExtension u i z
  let g0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ :=
    fun z i j => localEnergyGradientZeroExtension Du i j z
  let p0 : Vec3 × ℝ → ℝ := localEnergyPressureZeroExtension p
  let ψP : ParabolicPoint → ℝ := show ParabolicPoint → ℝ from ψ
  let a : Vec3 × ℝ → ℝ := fun z =>
    timePartial ψP (parabolicHomeomorph.symm z) +
      ∑ i : Fin 3, spatialSecondPartial ψP i i (parabolicHomeomorph.symm z)
  let b : Fin 3 → Vec3 × ℝ → ℝ := fun i z =>
    spatialPartial ψP i (parabolicHomeomorph.symm z)
  have hCoeff := localEnergy_testCoefficients hψ hψc
  have hExt := localEnergy_zeroExtensionLp hu hDu henergy hpLp hL3 hgrad
  have hScales := localEnergy_exists_scales_for_test hψc hψU
  obtain ⟨ε, hε, δ, hδ, hδpos, hcover⟩ := hScales
  have hInputs := localEnergy_mollifiedInputs_tendsto hu hDu henergy hpLp hL3 hgrad
    hδ hδpos
  have hProducts := localEnergy_mollifiedProducts_tendsto hu hDu henergy hpLp hL3 hgrad
    hδ hδpos
  have ha : MemLp a 2 (volume : Measure (Vec3 × ℝ)) := by
    simpa [a] using hCoeff.1
  have hb4 (i : Fin 3) : MemLp (b i) 4 (volume : Measure (Vec3 × ℝ)) := by
    simpa [b] using hCoeff.2.1 i
  have hb12 (i : Fin 3) : MemLp (b i) 12 (volume : Measure (Vec3 × ℝ)) := by
    simpa [b] using hCoeff.2.2.1 i
  have hψInf : MemLp ψ ⊤ (volume : Measure (Vec3 × ℝ)) := hCoeff.2.2.2
  have haNeg : MemLp (fun z : Vec3 × ℝ => -a z) 2
      (volume : Measure (Vec3 × ℝ)) := ha.neg
  have hb4Neg (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => -b i z) 4
      (volume : Measure (Vec3 × ℝ)) := (hb4 i).neg
  have hb12Neg (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => (-2 : ℝ) * b i z) 12
      (volume : Measure (Vec3 × ℝ)) := (hb12 i).const_mul (-2)
  have hψTwo : MemLp (fun z : Vec3 × ℝ => (2 : ℝ) * ψ z) ⊤
      (volume : Measure (Vec3 × ℝ)) := hψInf.const_mul 2
  have huN (n : ℕ) (i : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) 4
      (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num) (hδpos n) (hExt.1 i)
  have hFN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j) 2
      (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num)
      (hδpos n) (hExt.2.1 i j)
  have hGN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j) 2
      (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num)
      (hδpos n) (hExt.2.2.1 i j)
  have hpN (n : ℕ) : MemLp (localEnergyMollifiedPressure p (δ n) (hδpos n))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact localEnergy_mollify_memLp
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num)
      (hδpos n) hExt.2.2.2
  have hU0 (i : Fin 3) : MemLp (fun z => u0 z i) 4
      (volume : Measure (Vec3 × ℝ)) := by
    simpa [u0, localEnergyVelocityZeroExtension, U,
      localEnergyUnitProductCylinder] using hExt.1 i
  have hG0 (i j : Fin 3) : MemLp (fun z => g0 z i j) 2
      (volume : Measure (Vec3 × ℝ)) := by
    simpa [g0, localEnergyGradientZeroExtension, U,
      localEnergyUnitProductCylinder] using hExt.2.2.1 i j
  have hp0 : MemLp p0 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    simpa [p0, localEnergyPressureZeroExtension, U,
      localEnergyUnitProductCylinder] using hExt.2.2.2
  have huLim (i : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i - u0 z i)
      4 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    simpa [u0, localEnergyMollifiedVelocity, localEnergyVelocityZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.1 i
  have hGLim (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j - g0 z i j)
      2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    simpa [g0, localEnergyMollifiedGradient, localEnergyGradientZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.2.2.1 i j
  have hSqN (n : ℕ) (i : Fin 3) : MemLp
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) 2
      (volume : Measure (Vec3 × ℝ)) :=
    (huN n i).mul (huN n i)
  have hSq0 (i : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => u0 z i * u0 z i) 2
      (volume : Measure (Vec3 × ℝ)) := (hU0 i).mul (hU0 i)
  have hSqConv (i : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i -
          u0 z i * u0 z i) 2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    simpa [u0] using hProducts.1 i
  have hCubicN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z j)
      (ENNReal.ofReal (4 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact (hSqN n i).mul (huN n j)
  have hCubic0 (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => u0 z i * u0 z i * u0 z j)
      (ENNReal.ofReal (4 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact (hSq0 i).mul (hU0 j)
  have hCubicConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z j -
          u0 z i * u0 z i * u0 z j)
      (ENNReal.ofReal (4 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    simpa [u0] using hProducts.2.1 i j
  have hPressureUN (n : ℕ) (i : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedPressure p (δ n) (hδpos n) z *
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i)
      (ENNReal.ofReal (12 / 11 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    (hpN n).mul (huN n i)
  have hPressureU0 (i : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => p0 z * u0 z i)
      (ENNReal.ofReal (12 / 11 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    hp0.mul (hU0 i)
  have hPressureUConv (i : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => localEnergyMollifiedPressure p (δ n) (hδpos n) z *
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i - p0 z * u0 z i)
      (ENNReal.ofReal (12 / 11 : ℝ)) (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    simpa [u0, p0] using hProducts.2.2.1 i
  have hStressN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z j) 2
      (volume : Measure (Vec3 × ℝ)) :=
    (hFN n i j).sub ((huN n i).mul (huN n j))
  have hStressLim (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z j) 2
      (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    exact hProducts.2.2.2.1 i j
  have hGradSqN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j *
          localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j) 1
      (volume : Measure (Vec3 × ℝ)) := (hGN n i j).mul (hGN n i j)
  have hGradSq0 (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => g0 z i j * g0 z i j) 1
      (volume : Measure (Vec3 × ℝ)) := (hG0 i j).mul (hG0 i j)
  have hGradSqConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j *
            localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j -
          g0 z i j * g0 z i j) 1 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    simpa [g0] using hProducts.2.2.2.2 i j
  have hUBConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z - u0 z i * b j z)
      2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) :=
    localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 4) (q := 4) (r := 2) (by norm_num)
      (hU0 i) (hb4 j) (fun n => huN n i) (huLim i)
  have hGψConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j * ψ z -
          g0 z i j * ψ z) 2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) :=
    localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 2) (q := ⊤) (r := 2) (by norm_num)
      (hG0 i j) hψInf (fun n => hGN n i j) (hGLim i j)
  have hKBaseN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ =>
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z +
          ψ z * localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j)
      2 (volume : Measure (Vec3 × ℝ)) := by
    have hleft : MemLp
        (fun z : Vec3 × ℝ => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z)
        2 (volume : Measure (Vec3 × ℝ)) :=
      MeasureTheory.MemLp.mul (p := 4) (q := 4) (r := 2) (huN n i) (hb4 j)
    have hright : MemLp
        (fun z : Vec3 × ℝ => ψ z *
          localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j)
        2 (volume : Measure (Vec3 × ℝ)) :=
      MeasureTheory.MemLp.mul (p := ⊤) (q := 2) (r := 2) hψInf (hGN n i j)
    exact hleft.add (by simpa [mul_comm] using hright)
  have hKBase0 (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => u0 z i * b j z + ψ z * g0 z i j)
      2 (volume : Measure (Vec3 × ℝ)) := by
    have hleft : MemLp (fun z : Vec3 × ℝ => u0 z i * b j z) 2
        (volume : Measure (Vec3 × ℝ)) :=
      MeasureTheory.MemLp.mul (p := 4) (q := 4) (r := 2) (hU0 i) (hb4 j)
    have hright : MemLp (fun z : Vec3 × ℝ => ψ z * g0 z i j) 2
        (volume : Measure (Vec3 × ℝ)) :=
      MeasureTheory.MemLp.mul (p := ⊤) (q := 2) (r := 2) hψInf (hG0 i j)
    exact hleft.add (by simpa [mul_comm] using hright)
  have hKBaseConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z +
          ψ z * localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j) -
        (u0 z i * b j z + ψ z * g0 z i j)) 2 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_add_sub
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hUBConv i j) (by
        simpa [mul_comm] using hGψConv i j)
  have hKBaseScaledN (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => (-2 : ℝ) *
        (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z +
          ψ z * localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j))
      2 (volume : Measure (Vec3 × ℝ)) := (hKBaseN n i j).const_mul (-2)
  have hKBaseScaled0 (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => (-2 : ℝ) * (u0 z i * b j z + ψ z * g0 z i j))
      2 (volume : Measure (Vec3 × ℝ)) := (hKBase0 i j).const_mul (-2)
  have hKBaseScaledConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => (-2 : ℝ) *
        (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z +
          ψ z * localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j) -
        (-2 : ℝ) * (u0 z i * b j z + ψ z * g0 z i j))
      2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) :=
    localEnergy_tendsto_eLpNorm_const_smul_sub (-2) (hKBaseConv i j)
  have hStressTermConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ =>
        (localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z j) *
          ((-2 : ℝ) *
            (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z +
              ψ z * localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j)))
      1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    have hzero : MemLp (fun _ : Vec3 × ℝ => (0 : ℝ)) 2
        (volume : Measure (Vec3 × ℝ)) := by simp
    have h := localEnergy_tendsto_eLpNorm_mul_sub
      (p := 2) (q := 2) (r := 1) (by norm_num)
      hzero (hKBaseScaled0 i j) (fun n => hStressN n i j)
      (fun n => hKBaseScaledN n i j)
      (by simpa using hStressLim i j)
      (hKBaseScaledConv i j)
    simpa using h
  let squareTerm : ℕ → Fin 3 → Vec3 × ℝ → ℝ := fun n i z =>
    (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
      localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) * (-a z)
  let squareTerm0 : Fin 3 → Vec3 × ℝ → ℝ := fun i z =>
    (u0 z i * u0 z i) * (-a z)
  let cubicTerm : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun n i j z =>
    (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
      localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
      localEnergyMollifiedVelocity u (δ n) (hδpos n) z j) * (-b j z)
  let cubicTerm0 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z =>
    (u0 z i * u0 z i * u0 z j) * (-b j z)
  let pressureTerm : ℕ → Fin 3 → Vec3 × ℝ → ℝ := fun n i z =>
    (localEnergyMollifiedPressure p (δ n) (hδpos n) z *
      localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) * ((-2 : ℝ) * b i z)
  let pressureTerm0 : Fin 3 → Vec3 × ℝ → ℝ := fun i z =>
    (p0 z * u0 z i) * ((-2 : ℝ) * b i z)
  let stressTerm : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun n i j z =>
    (localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
      localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z j) *
      ((-2 : ℝ) *
        (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z +
          ψ z * localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j))
  let gradientTerm : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun n i j z =>
    (localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j *
      localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j) * ((2 : ℝ) * ψ z)
  let gradientTerm0 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z =>
    (g0 z i j * g0 z i j) * ((2 : ℝ) * ψ z)

  have hSquareTermConv (i : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ => squareTerm n i z - squareTerm0 i z)
        1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 2) (q := 2) (r := 1) (by norm_num)
      (hSq0 i) haNeg (fun n => hSqN n i) (by simpa [squareTerm, squareTerm0] using hSqConv i)
  have hCubicTermConv (i j : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ => cubicTerm n i j z - cubicTerm0 i j z)
        1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := ENNReal.ofReal (4 / 3 : ℝ)) (q := 4) (r := 1) (by norm_num)
      (hCubic0 i j) (hb4Neg j) (fun n => hCubicN n i j)
      (by simpa [cubicTerm, cubicTerm0] using hCubicConv i j)
  have hPressureTermConv (i : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ => pressureTerm n i z - pressureTerm0 i z)
        1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := ENNReal.ofReal (12 / 11 : ℝ)) (q := 12) (r := 1) (by norm_num)
      (hPressureU0 i) (hb12Neg i) (fun n => hPressureUN n i)
      (by simpa [pressureTerm, pressureTerm0] using hPressureUConv i)
  have hStressExpandedConv (i j : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ => stressTerm n i j z) 1
        (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    simpa [stressTerm] using hStressTermConv i j
  have hGradientTermConv (i j : Fin 3) : Tendsto
      (fun n => eLpNorm (fun z : Vec3 × ℝ => gradientTerm n i j z - gradientTerm0 i j z)
        1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 1) (q := ⊤) (r := 1) (by norm_num)
      (hGradSq0 i j) hψTwo (fun n => hGradSqN n i j)
      (by simpa [gradientTerm, gradientTerm0] using hGradSqConv i j)

  let squareSum : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    ∑ i : Fin 3, squareTerm n i z
  let squareSum0 : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3, squareTerm0 i z
  let cubicSum : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm n i j z
  let cubicSum0 : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm0 i j z
  let pressureSum : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    ∑ i : Fin 3, pressureTerm n i z
  let pressureSum0 : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3, pressureTerm0 i z
  let stressSum : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    ∑ i : Fin 3, ∑ j : Fin 3, stressTerm n i j z
  let gradientSum : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm n i j z
  let gradientSum0 : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm0 i j z
  let energyN : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    (squareSum n z + cubicSum n z) +
      ((pressureSum n z + stressSum n z) + gradientSum n z)
  let energy0 : Vec3 × ℝ → ℝ := fun z =>
    (squareSum0 z + cubicSum0 z) + (pressureSum0 z + gradientSum0 z)

  have hSquareSumConv : Tendsto
      (fun n => eLpNorm (squareSum n - squareSum0) 1 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_finset_sum_sub (by norm_num) Finset.univ
      (fun n i z => squareTerm n i z) (fun i z => squareTerm0 i z)
      (by intro i hi; exact hSquareTermConv i)
  have hCubicSumConv : Tendsto
      (fun n => eLpNorm (cubicSum n - cubicSum0) 1 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_double_sum_sub (by norm_num)
      (fun i j => hCubicTermConv i j)
  have hPressureSumConv : Tendsto
      (fun n => eLpNorm (pressureSum n - pressureSum0) 1 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_finset_sum_sub (by norm_num) Finset.univ
      (fun n i z => pressureTerm n i z) (fun i z => pressureTerm0 i z)
      (by intro i hi; exact hPressureTermConv i)
  have hStressSumConv : Tendsto
      (fun n => eLpNorm (stressSum n) 1 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    have hdouble : Tendsto
        (fun n => eLpNorm
          (fun z : Vec3 × ℝ =>
            (∑ i : Fin 3, ∑ j : Fin 3, stressTerm n i j z) -
              ∑ i : Fin 3, ∑ j : Fin 3, (0 : ℝ))
          1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
      refine localEnergy_tendsto_eLpNorm_double_sum_sub
        (α := Vec3 × ℝ) (ι := Fin 3) (κ := Fin 3)
        (μ := (volume : Measure (Vec3 × ℝ))) (p := 1) (by norm_num) ?_
      intro i j
      simpa using hStressExpandedConv i j
    simpa [stressSum] using hdouble
  have hGradientSumConv : Tendsto
      (fun n => eLpNorm (gradientSum n - gradientSum0) 1 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_double_sum_sub (by norm_num)
      (fun i j => hGradientTermConv i j)
  have hEnergyConv : Tendsto
      (fun n => eLpNorm (energyN n - energy0) 1 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    have hLeft : Tendsto
        (fun n => eLpNorm
          (fun z : Vec3 × ℝ => squareSum n z + cubicSum n z -
            (squareSum0 z + cubicSum0 z))
          1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
      exact localEnergy_tendsto_eLpNorm_add_sub
        (α := Vec3 × ℝ) (μ := (volume : Measure (Vec3 × ℝ))) (p := 1)
        (f := squareSum0) (g := cubicSum0)
        (fn := squareSum) (gn := cubicSum) (by norm_num)
        hSquareSumConv hCubicSumConv
    have hRight : Tendsto
        (fun n => eLpNorm
          (fun z : Vec3 × ℝ => pressureSum n z + stressSum n z -
            (pressureSum0 z + 0))
          1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
      exact localEnergy_tendsto_eLpNorm_add_sub
        (α := Vec3 × ℝ) (μ := (volume : Measure (Vec3 × ℝ))) (p := 1)
        (f := pressureSum0) (g := fun _ : Vec3 × ℝ => (0 : ℝ))
        (fn := pressureSum) (gn := stressSum) (by norm_num)
        hPressureSumConv (by simpa using hStressSumConv)
    have hRight' : Tendsto
        (fun n => eLpNorm
          (fun z : Vec3 × ℝ =>
            (pressureSum n z + stressSum n z) + gradientSum n z -
              ((pressureSum0 z + 0) + gradientSum0 z))
          1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
      exact localEnergy_tendsto_eLpNorm_add_sub
        (α := Vec3 × ℝ) (μ := (volume : Measure (Vec3 × ℝ))) (p := 1)
        (f := fun z : Vec3 × ℝ => pressureSum0 z + 0)
        (g := gradientSum0)
        (fn := fun n z => pressureSum n z + stressSum n z)
        (gn := gradientSum) (by norm_num) hRight hGradientSumConv
    have hCombined : Tendsto
        (fun n => eLpNorm
          (fun z : Vec3 × ℝ =>
            (squareSum n z + cubicSum n z) +
              ((pressureSum n z + stressSum n z) + gradientSum n z) -
                ((squareSum0 z + cubicSum0 z) +
                  ((pressureSum0 z + 0) + gradientSum0 z)))
          1 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
      exact localEnergy_tendsto_eLpNorm_add_sub
        (α := Vec3 × ℝ) (μ := (volume : Measure (Vec3 × ℝ))) (p := 1)
        (f := fun z : Vec3 × ℝ => squareSum0 z + cubicSum0 z)
        (g := fun z : Vec3 × ℝ => (pressureSum0 z + 0) + gradientSum0 z)
        (fn := fun n z => squareSum n z + cubicSum n z)
        (gn := fun n z => (pressureSum n z + stressSum n z) + gradientSum n z)
        (by norm_num) hLeft hRight'
    have hfun (n : ℕ) : eLpNorm (energyN n - energy0) 1
        (volume : Measure (Vec3 × ℝ)) = eLpNorm
          (fun z : Vec3 × ℝ =>
            (squareSum n z + cubicSum n z) +
              ((pressureSum n z + stressSum n z) + gradientSum n z) -
                ((squareSum0 z + cubicSum0 z) +
                  ((pressureSum0 z + 0) + gradientSum0 z)))
          1 (volume : Measure (Vec3 × ℝ)) := by
      congr 1
      funext z
      simp [energyN, energy0]
    exact hCombined.congr fun n => (hfun n).symm

  have hSquareTermN (n : ℕ) (i : Fin 3) : MemLp (squareTerm n i) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := 2) (q := 2) (r := 1)
      (hSqN n i) haNeg
  have hSquareTerm0 (i : Fin 3) : MemLp (squareTerm0 i) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := 2) (q := 2) (r := 1) (hSq0 i) haNeg
  have hCubicTermN (n : ℕ) (i j : Fin 3) : MemLp (cubicTerm n i j) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (4 / 3 : ℝ)) (q := 4) (r := 1)
      (hCubicN n i j) (hb4Neg j)
  have hCubicTerm0 (i j : Fin 3) : MemLp (cubicTerm0 i j) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (4 / 3 : ℝ)) (q := 4) (r := 1)
      (hCubic0 i j) (hb4Neg j)
  have hPressureTermN (n : ℕ) (i : Fin 3) : MemLp (pressureTerm n i) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (12 / 11 : ℝ)) (q := 12) (r := 1)
      (hPressureUN n i) (hb12Neg i)
  have hPressureTerm0 (i : Fin 3) : MemLp (pressureTerm0 i) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (12 / 11 : ℝ)) (q := 12) (r := 1)
      (hPressureU0 i) (hb12Neg i)
  have hStressTermN (n : ℕ) (i j : Fin 3) : MemLp (stressTerm n i j) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := 2) (q := 2) (r := 1)
      (hStressN n i j) (hKBaseScaledN n i j)
  have hStressTerm0 (i j : Fin 3) : MemLp (fun _ : Vec3 × ℝ => (0 : ℝ)) 1
      (volume : Measure (Vec3 × ℝ)) := by simp
  have hGradientTermN (n : ℕ) (i j : Fin 3) : MemLp (gradientTerm n i j) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := 1) (q := ⊤) (r := 1)
      (hGradSqN n i j) hψTwo
  have hGradientTerm0 (i j : Fin 3) : MemLp (gradientTerm0 i j) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact MeasureTheory.MemLp.mul (p := 1) (q := ⊤) (r := 1)
      (hGradSq0 i j) hψTwo

  have hSquareSumN (n : ℕ) : MemLp (squareSum n) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact memLp_finsetSum Finset.univ (by intro i hi; exact hSquareTermN n i)
  have hSquareSum0 : MemLp squareSum0 1 (volume : Measure (Vec3 × ℝ)) := by
    exact memLp_finsetSum Finset.univ (by intro i hi; exact hSquareTerm0 i)
  have hCubicSumN (n : ℕ) : MemLp (cubicSum n) 1
      (volume : Measure (Vec3 × ℝ)) :=
    localEnergy_memLp_double_sum (fun i j => hCubicTermN n i j)
  have hCubicSum0 : MemLp cubicSum0 1 (volume : Measure (Vec3 × ℝ)) :=
    localEnergy_memLp_double_sum (fun i j => hCubicTerm0 i j)
  have hPressureSumN (n : ℕ) : MemLp (pressureSum n) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact memLp_finsetSum Finset.univ (by intro i hi; exact hPressureTermN n i)
  have hPressureSum0 : MemLp pressureSum0 1 (volume : Measure (Vec3 × ℝ)) := by
    exact memLp_finsetSum Finset.univ (by intro i hi; exact hPressureTerm0 i)
  have hStressSumN (n : ℕ) : MemLp (stressSum n) 1
      (volume : Measure (Vec3 × ℝ)) :=
    localEnergy_memLp_double_sum (fun i j => hStressTermN n i j)
  have hGradientSumN (n : ℕ) : MemLp (gradientSum n) 1
      (volume : Measure (Vec3 × ℝ)) :=
    localEnergy_memLp_double_sum (fun i j => hGradientTermN n i j)
  have hGradientSum0 : MemLp gradientSum0 1 (volume : Measure (Vec3 × ℝ)) :=
    localEnergy_memLp_double_sum (fun i j => hGradientTerm0 i j)
  have hEnergyN (n : ℕ) : MemLp (energyN n) 1
      (volume : Measure (Vec3 × ℝ)) := by
    exact ((hSquareSumN n).add (hCubicSumN n)).add
      (((hPressureSumN n).add (hStressSumN n)).add (hGradientSumN n))
  have hEnergy0 : MemLp energy0 1 (volume : Measure (Vec3 × ℝ)) := by
    exact (hSquareSum0.add hCubicSum0).add (hPressureSum0.add hGradientSum0)

  have hEnergyN_eq_expanded (n : ℕ) : energyN n =
      localEnergyLimitExpandedBaseIntegrand
        (localEnergyMollifiedVelocity u (δ n) (hδpos n))
        (fun z i j => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z j)
        (localEnergyMollifiedGradient Du (δ n) (hδpos n))
        (localEnergyMollifiedPressure p (δ n) (hδpos n)) ψP := by
    funext z
    have hfirst :
        -(∑ i : Fin 3,
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) * a z =
          ∑ i : Fin 3, squareTerm n i z := by
      calc
        _ = -((∑ i : Fin 3,
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) * a z) := by ring
        _ = -(∑ i : Fin 3,
          (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) * a z) := by
              rw [Finset.sum_mul]
        _ = ∑ i : Fin 3, squareTerm n i z := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              simp [squareTerm]
    have hcubic :
        -(∑ i : Fin 3, ∑ j : Fin 3,
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z j * b j z) =
          ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm n i j z := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp [cubicTerm]
    have hpressure :
        -(∑ i : Fin 3,
          localEnergyMollifiedPressure p (δ n) (hδpos n) z *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * (2 * b i z)) =
          ∑ i : Fin 3, pressureTerm n i z := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp [pressureTerm]
    have hstress :
        -(∑ i : Fin 3, ∑ j : Fin 3,
          (localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
              localEnergyMollifiedVelocity u (δ n) (hδpos n) z j) *
            (2 * (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i * b j z +
              ψ z * localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j))) =
          ∑ i : Fin 3, ∑ j : Fin 3, stressTerm n i j z := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp [stressTerm]
    simp only [a, b] at hfirst hcubic hpressure hstress
    have hψEval (x : Vec3 × ℝ) : ψP (parabolicHomeomorph.symm x) = ψ x := by
      simp [ψP]
    rw [← hψEval z] at hstress
    simp only [sub_eq_add_neg] at hstress
    change
      (∑ i : Fin 3, squareTerm n i z + ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm n i j z) +
        ((∑ i : Fin 3, pressureTerm n i z +
          ∑ i : Fin 3, ∑ j : Fin 3, stressTerm n i j z) +
          ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm n i j z) =
      -(∑ i : Fin 3,
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) *
        (timePartial ψP (parabolicHomeomorph.symm z) +
          ∑ i : Fin 3, spatialSecondPartial ψP i i (parabolicHomeomorph.symm z))
      - ∑ i : Fin 3, ∑ j : Fin 3,
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z j *
              spatialPartial ψP j (parabolicHomeomorph.symm z)
      - ∑ i : Fin 3,
          localEnergyMollifiedPressure p (δ n) (hδpos n) z *
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
              (2 * spatialPartial ψP i (parabolicHomeomorph.symm z))
      - ∑ i : Fin 3, ∑ j : Fin 3,
          (localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
            localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
              localEnergyMollifiedVelocity u (δ n) (hδpos n) z j) *
            (2 * (localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
              spatialPartial ψP j (parabolicHomeomorph.symm z) +
              ψP (parabolicHomeomorph.symm z) *
                localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j))
      + ∑ i : Fin 3, ∑ j : Fin 3,
          localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j *
            localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j *
              (2 * ψP (parabolicHomeomorph.symm z))
    simp only [sub_eq_add_neg]
    rw [hfirst, hcubic, hpressure, hstress]
    simp only [squareTerm, cubicTerm, pressureTerm, stressTerm, gradientTerm]
    rw [hψEval z]
    ring

  have hEnergy0_eq_expanded : energy0 =
      localEnergyLimitExpandedBaseIntegrand u0 (fun _ _ _ => 0) g0 p0 ψP := by
    funext z
    have hfirst :
        -(∑ i : Fin 3, u0 z i * u0 z i) * a z = ∑ i : Fin 3, squareTerm0 i z := by
      calc
        _ = -((∑ i : Fin 3, u0 z i * u0 z i) * a z) := by ring
        _ = -(∑ i : Fin 3, (u0 z i * u0 z i) * a z) := by rw [Finset.sum_mul]
        _ = ∑ i : Fin 3, squareTerm0 i z := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          simp [squareTerm0]
    have hcubic0 :
        -(∑ i : Fin 3, ∑ j : Fin 3, u0 z i * u0 z i * u0 z j * b j z) =
          ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm0 i j z := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp [cubicTerm0]
    have hpressure0 :
        -(∑ i : Fin 3, p0 z * u0 z i * (2 * b i z)) =
          ∑ i : Fin 3, pressureTerm0 i z := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp [pressureTerm0]
    simp only [a, b] at hfirst hcubic0 hpressure0
    change
      (∑ i : Fin 3, squareTerm0 i z +
        ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm0 i j z) +
        (∑ i : Fin 3, pressureTerm0 i z +
          ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm0 i j z) =
      -(∑ i : Fin 3, u0 z i * u0 z i) *
        (timePartial ψP (parabolicHomeomorph.symm z) +
          ∑ i : Fin 3, spatialSecondPartial ψP i i (parabolicHomeomorph.symm z))
      - ∑ i : Fin 3, ∑ j : Fin 3,
          u0 z i * u0 z i * u0 z j * spatialPartial ψP j (parabolicHomeomorph.symm z)
      - ∑ i : Fin 3, p0 z * u0 z i *
          (2 * spatialPartial ψP i (parabolicHomeomorph.symm z))
      - ∑ i : Fin 3, ∑ j : Fin 3,
          (0 : ℝ) * (2 * (u0 z i * spatialPartial ψP j (parabolicHomeomorph.symm z) +
            ψP (parabolicHomeomorph.symm z) * g0 z i j))
      + ∑ i : Fin 3, ∑ j : Fin 3,
          g0 z i j * g0 z i j * (2 * ψP (parabolicHomeomorph.symm z))
    simp only [sub_eq_add_neg]
    rw [hfirst, hcubic0, hpressure0]
    have hψEval (x : Vec3 × ℝ) : ψP (parabolicHomeomorph.symm x) = ψ x := by
      simp [ψP]
    rw [hψEval z]
    simp [squareTerm0, cubicTerm0, pressureTerm0, zero_mul,
      Finset.sum_const_zero]
    ring

  have hMollifiedZero (n : ℕ) : ∫ z, energyN n z
      ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    rw [hEnergyN_eq_expanded n]
    rw [← localEnergy_smoothBase_eq_expanded (hψ := hψ)]
    have hzero := localEnergy_mollified_base_integral_zero
      hu hDu henergy hpLp hL3 hgrad hS2 hS3 hψ hψc (hδpos n) (hcover n)
    change ∫ z, smoothEnergyBaseIntegrand
      (fun y i => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i)) (δ n) (hδpos n) y)
      (fun y i j => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i * u q j)) (δ n) (hδpos n) y -
          spaceTimeMollify
            ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
              (fun q : Vec3 × ℝ => u q i)) (δ n) (hδpos n) y *
            spaceTimeMollify
              ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
                (fun q : Vec3 × ℝ => u q j)) (δ n) (hδpos n) y)
      (fun y i j => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => Du q i j)) (δ n) (hδpos n) y)
      (spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p) (δ n) (hδpos n))
      ψ z = 0
    exact hzero

  have hIntegralConv := localEnergy_integral_tendsto_of_L1
    (μ := (volume : Measure (Vec3 × ℝ))) (f := energy0)
    (fn := energyN) hEnergyN hEnergyConv
  have hZeroLimit : Tendsto
      (fun n : ℕ => ∫ z, energyN n z ∂(volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0) := by
    have heq : (fun n : ℕ => ∫ z, energyN n z ∂(volume : Measure (Vec3 × ℝ))) =
        fun _ => 0 := by
      funext n
      exact hMollifiedZero n
    rw [heq]
    exact tendsto_const_nhds
  have hIntegralZero : ∫ z, energy0 z ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    have huniq := tendsto_nhds_unique hZeroLimit hIntegralConv
    simpa using huniq.symm
  rw [hEnergy0_eq_expanded] at hIntegralZero
  change ∫ z, localEnergyLimitExpandedBaseIntegrand
    (fun z i => localEnergyVelocityZeroExtension u i z)
    (fun z i j => (0 : ℝ))
    (fun z i j => localEnergyGradientZeroExtension Du i j z)
    (localEnergyPressureZeroExtension p) ψP z = 0
  exact hIntegralZero

end ESS

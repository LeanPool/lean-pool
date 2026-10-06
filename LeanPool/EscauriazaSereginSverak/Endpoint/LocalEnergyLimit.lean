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

/-!
# Local Energy Limit

Local energy identities and limit passages for the endpoint regularity proof.
-/

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

private theorem localEnergy_finiteEnergySums_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (square : ℕ → Fin 3 → α → ℝ) (square₀ : Fin 3 → α → ℝ)
    (cubic : ℕ → Fin 3 → Fin 3 → α → ℝ) (cubic₀ : Fin 3 → Fin 3 → α → ℝ)
    (pressure : ℕ → Fin 3 → α → ℝ) (pressure₀ : Fin 3 → α → ℝ)
    (stress : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (hSquare : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => square n i x - square₀ i x) 1 μ) atTop (nhds 0))
    (hCubic : ∀ i j, Tendsto (fun n => eLpNorm
      (fun x => cubic n i j x - cubic₀ i j x) 1 μ) atTop (nhds 0))
    (hPressure : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => pressure n i x - pressure₀ i x) 1 μ) atTop (nhds 0))
    (hStress : ∀ i j, Tendsto (fun n => eLpNorm (stress n i j) 1 μ)
      atTop (nhds 0))
    (hGradient : ∀ i j, Tendsto (fun n => eLpNorm
      (fun x => gradient n i j x - gradient₀ i j x) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => (∑ i : Fin 3, square n i x) - ∑ i : Fin 3, square₀ i x)
      1 μ) atTop (nhds 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => (∑ i : Fin 3, ∑ j : Fin 3, cubic n i j x) -
        ∑ i : Fin 3, ∑ j : Fin 3, cubic₀ i j x) 1 μ) atTop (nhds 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => (∑ i : Fin 3, pressure n i x) - ∑ i : Fin 3, pressure₀ i x)
      1 μ) atTop (nhds 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3, stress n i j x)
      1 μ) atTop (nhds 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => (∑ i : Fin 3, ∑ j : Fin 3, gradient n i j x) -
        ∑ i : Fin 3, ∑ j : Fin 3, gradient₀ i j x) 1 μ) atTop (nhds 0) := by
  have hSquareSum := localEnergy_tendsto_eLpNorm_finset_sum_sub
    (α := α) (μ := μ) (p := 1) (by norm_num) Finset.univ
    (fun n i x => square n i x) (fun i x => square₀ i x)
    (by intro i hi; exact hSquare i)
  have hCubicSum := localEnergy_tendsto_eLpNorm_double_sum_sub
    (α := α) (μ := μ) (p := 1) (by norm_num) hCubic
  have hPressureSum := localEnergy_tendsto_eLpNorm_finset_sum_sub
    (α := α) (μ := μ) (p := 1) (by norm_num) Finset.univ
    (fun n i x => pressure n i x) (fun i x => pressure₀ i x)
    (by intro i hi; exact hPressure i)
  have hStressSum := localEnergy_tendsto_eLpNorm_double_sum_sub
    (α := α) (μ := μ) (p := 1) (by norm_num)
    (fun i j => by simpa using hStress i j)
  have hGradientSum := localEnergy_tendsto_eLpNorm_double_sum_sub
    (α := α) (μ := μ) (p := 1) (by norm_num) hGradient
  exact ⟨hSquareSum, hCubicSum, hPressureSum, hStressSum, hGradientSum⟩

private theorem localEnergy_energySums_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (squareSum : ℕ → α → ℝ) (squareSum₀ : α → ℝ)
    (cubicSum : ℕ → α → ℝ) (cubicSum₀ : α → ℝ)
    (pressureSum : ℕ → α → ℝ) (pressureSum₀ : α → ℝ)
    (stressSum : ℕ → α → ℝ)
    (gradientSum : ℕ → α → ℝ) (gradientSum₀ : α → ℝ)
    (hSquare : Tendsto (fun n => eLpNorm (squareSum n - squareSum₀) 1 μ)
      atTop (nhds 0))
    (hCubic : Tendsto (fun n => eLpNorm (cubicSum n - cubicSum₀) 1 μ)
      atTop (nhds 0))
    (hPressure : Tendsto (fun n => eLpNorm (pressureSum n - pressureSum₀) 1 μ)
      atTop (nhds 0))
    (hStress : Tendsto (fun n => eLpNorm (stressSum n) 1 μ)
      atTop (nhds 0))
    (hGradient : Tendsto (fun n => eLpNorm (gradientSum n - gradientSum₀) 1 μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (((squareSum n + cubicSum n) + (pressureSum n + stressSum n) +
        gradientSum n) -
        ((squareSum₀ + cubicSum₀) + (pressureSum₀ + gradientSum₀))) 1 μ)
      atTop (nhds 0) := by
  have hLeft := localEnergy_tendsto_eLpNorm_add_sub
    (α := α) (μ := μ) (p := 1) (by norm_num)
    hSquare hCubic
  have hPressureStress := localEnergy_tendsto_eLpNorm_add_sub
    (α := α) (μ := μ) (p := 1) (by norm_num)
    hPressure (by simpa using hStress)
  have hRight := localEnergy_tendsto_eLpNorm_add_sub
    (α := α) (μ := μ) (p := 1) (by norm_num)
    hPressureStress hGradient
  have hCombined := localEnergy_tendsto_eLpNorm_add_sub
    (α := α) (μ := μ) (p := 1) (by norm_num) hLeft hRight
  have hfun (n : ℕ) : eLpNorm
      (((squareSum n + cubicSum n) + (pressureSum n + stressSum n) +
        gradientSum n) -
        ((squareSum₀ + cubicSum₀) + (pressureSum₀ + gradientSum₀))) 1 μ =
      eLpNorm
        ((squareSum n + cubicSum n) +
          ((pressureSum n + stressSum n) + gradientSum n) -
          ((squareSum₀ + cubicSum₀) +
            ((pressureSum₀ + 0) + gradientSum₀))) 1 μ := by
    congr 1
    funext x
    simp [add_assoc]
  exact hCombined.congr fun n => (hfun n).symm

private theorem localEnergy_energyDensity_memLp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (square : ℕ → Fin 3 → α → ℝ) (square₀ : Fin 3 → α → ℝ)
    (cubic : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (cubic₀ : Fin 3 → Fin 3 → α → ℝ)
    (pressure : ℕ → Fin 3 → α → ℝ) (pressure₀ : Fin 3 → α → ℝ)
    (stress : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (hSquare : ∀ n i, MemLp (square n i) 1 μ)
    (hSquare₀ : ∀ i, MemLp (square₀ i) 1 μ)
    (hCubic : ∀ n i j, MemLp (cubic n i j) 1 μ)
    (hCubic₀ : ∀ i j, MemLp (cubic₀ i j) 1 μ)
    (hPressure : ∀ n i, MemLp (pressure n i) 1 μ)
    (hPressure₀ : ∀ i, MemLp (pressure₀ i) 1 μ)
    (hStress : ∀ n i j, MemLp (stress n i j) 1 μ)
    (hGradient : ∀ n i j, MemLp (gradient n i j) 1 μ)
    (hGradient₀ : ∀ i j, MemLp (gradient₀ i j) 1 μ) :
    (∀ n, MemLp (fun x =>
      (∑ i : Fin 3, square n i x) + (∑ i : Fin 3, ∑ j : Fin 3, cubic n i j x) +
        (((∑ i : Fin 3, pressure n i x) +
          (∑ i : Fin 3, ∑ j : Fin 3, stress n i j x)) +
            ∑ i : Fin 3, ∑ j : Fin 3, gradient n i j x)) 1 μ) ∧
    MemLp (fun x =>
      (∑ i : Fin 3, square₀ i x) + (∑ i : Fin 3, ∑ j : Fin 3, cubic₀ i j x) +
        ((∑ i : Fin 3, pressure₀ i x) +
          ∑ i : Fin 3, ∑ j : Fin 3, gradient₀ i j x)) 1 μ := by
  have hSquareSum (n : ℕ) : MemLp (fun x => ∑ i : Fin 3, square n i x) 1 μ :=
    memLp_finsetSum Finset.univ (by intro i hi; exact hSquare n i)
  have hSquareSum₀ : MemLp (fun x => ∑ i : Fin 3, square₀ i x) 1 μ :=
    memLp_finsetSum Finset.univ (by intro i hi; exact hSquare₀ i)
  have hCubicSum (n : ℕ) : MemLp (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      cubic n i j x) 1 μ := localEnergy_memLp_double_sum (fun i j => hCubic n i j)
  have hCubicSum₀ : MemLp (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      cubic₀ i j x) 1 μ := localEnergy_memLp_double_sum (fun i j => hCubic₀ i j)
  have hPressureSum (n : ℕ) : MemLp (fun x => ∑ i : Fin 3, pressure n i x) 1 μ :=
    memLp_finsetSum Finset.univ (by intro i hi; exact hPressure n i)
  have hPressureSum₀ : MemLp (fun x => ∑ i : Fin 3, pressure₀ i x) 1 μ :=
    memLp_finsetSum Finset.univ (by intro i hi; exact hPressure₀ i)
  have hStressSum (n : ℕ) : MemLp (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      stress n i j x) 1 μ := localEnergy_memLp_double_sum (fun i j => hStress n i j)
  have hGradientSum (n : ℕ) : MemLp (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      gradient n i j x) 1 μ := localEnergy_memLp_double_sum (fun i j => hGradient n i j)
  have hGradientSum₀ : MemLp (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      gradient₀ i j x) 1 μ := localEnergy_memLp_double_sum (fun i j => hGradient₀ i j)
  constructor
  · intro n
    exact ((hSquareSum n).add (hCubicSum n)).add
      ((hPressureSum n).add (hStressSum n).add (hGradientSum n))
  · exact (hSquareSum₀.add hCubicSum₀).add (hPressureSum₀.add hGradientSum₀)

private theorem localEnergy_finiteEnergyDensityLimit
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (square : ℕ → Fin 3 → α → ℝ) (square₀ : Fin 3 → α → ℝ)
    (cubic : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (cubic₀ : Fin 3 → Fin 3 → α → ℝ)
    (pressure : ℕ → Fin 3 → α → ℝ) (pressure₀ : Fin 3 → α → ℝ)
    (stress : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (squareSum : ℕ → α → ℝ) (squareSum₀ : α → ℝ)
    (cubicSum : ℕ → α → ℝ) (cubicSum₀ : α → ℝ)
    (pressureSum : ℕ → α → ℝ) (pressureSum₀ : α → ℝ)
    (stressSum : ℕ → α → ℝ)
    (gradientSum : ℕ → α → ℝ) (gradientSum₀ : α → ℝ)
    (hSquareLp : ∀ n i, MemLp (square n i) 1 μ)
    (hSquare₀Lp : ∀ i, MemLp (square₀ i) 1 μ)
    (hCubicLp : ∀ n i j, MemLp (cubic n i j) 1 μ)
    (hCubic₀Lp : ∀ i j, MemLp (cubic₀ i j) 1 μ)
    (hPressureLp : ∀ n i, MemLp (pressure n i) 1 μ)
    (hPressure₀Lp : ∀ i, MemLp (pressure₀ i) 1 μ)
    (hStressLp : ∀ n i j, MemLp (stress n i j) 1 μ)
    (hGradientLp : ∀ n i j, MemLp (gradient n i j) 1 μ)
    (hGradient₀Lp : ∀ i j, MemLp (gradient₀ i j) 1 μ)
    (hSquareConv : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => square n i x - square₀ i x) 1 μ) atTop (nhds 0))
    (hCubicConv : ∀ i j, Tendsto (fun n => eLpNorm
      (fun x => cubic n i j x - cubic₀ i j x) 1 μ) atTop (nhds 0))
    (hPressureConv : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => pressure n i x - pressure₀ i x) 1 μ) atTop (nhds 0))
    (hStressConv : ∀ i j, Tendsto (fun n => eLpNorm (stress n i j) 1 μ)
      atTop (nhds 0))
    (hGradientConv : ∀ i j, Tendsto (fun n => eLpNorm
      (fun x => gradient n i j x - gradient₀ i j x) 1 μ) atTop (nhds 0)) :
    (∀ n, MemLp (fun x =>
      (squareSum n x + cubicSum n x) + ((pressureSum n x + stressSum n x) +
        gradientSum n x)) 1 μ) ∧
    MemLp (fun x => (squareSum₀ x + cubicSum₀ x) +
      (pressureSum₀ x + gradientSum₀ x)) 1 μ ∧
    Tendsto (fun n => eLpNorm
      ((squareSum n + cubicSum n) + ((pressureSum n + stressSum n) + gradientSum n) -
        ((squareSum₀ + cubicSum₀) + (pressureSum₀ + gradientSum₀))) 1 μ)
      atTop (nhds 0) := by
  have hLp := localEnergy_energyDensity_memLp μ square square₀ cubic cubic₀
    pressure pressure₀ stress gradient gradient₀ hSquareLp hSquare₀Lp
    hCubicLp hCubic₀Lp hPressureLp hPressure₀Lp hStressLp hGradientLp hGradient₀Lp
  have hTerms := localEnergy_finiteEnergySums_tendsto μ square square₀ cubic cubic₀
    pressure pressure₀ stress gradient gradient₀ hSquareConv hCubicConv
    hPressureConv hStressConv hGradientConv
  have hEnergyConv := localEnergy_energySums_tendsto μ
    squareSum squareSum₀ cubicSum cubicSum₀ pressureSum pressureSum₀
    stressSum gradientSum gradientSum₀ hTerms.1 hTerms.2.1 hTerms.2.2.1
    hTerms.2.2.2.1 hTerms.2.2.2.2
  exact ⟨hLp.1, hLp.2, hEnergyConv⟩

private structure LocalEnergyEnergySequenceFacts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (squareTerm : ℕ → Fin 3 → α → ℝ) (squareTerm0 : Fin 3 → α → ℝ)
    (cubicTerm : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (cubicTerm0 : Fin 3 → Fin 3 → α → ℝ)
    (pressureTerm : ℕ → Fin 3 → α → ℝ) (pressureTerm0 : Fin 3 → α → ℝ)
    (stressTerm : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradientTerm : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradientTerm0 : Fin 3 → Fin 3 → α → ℝ) where
  energyN : ℕ → α → ℝ
  energy0 : α → ℝ
  energyN_memLp : ∀ n, MemLp (energyN n) 1 μ
  energy0_memLp : MemLp energy0 1 μ
  energy_tendsto : Tendsto (fun n => eLpNorm (energyN n - energy0) 1 μ)
    atTop (nhds 0)
  energyN_terms : ∀ n, energyN n = fun x =>
    ((∑ i : Fin 3, squareTerm n i x) + (∑ i : Fin 3, ∑ j : Fin 3, cubicTerm n i j x)) +
      (((∑ i : Fin 3, pressureTerm n i x) +
        (∑ i : Fin 3, ∑ j : Fin 3, stressTerm n i j x)) +
          ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm n i j x)
  energy0_terms : energy0 = fun x =>
    ((∑ i : Fin 3, squareTerm0 i x) + (∑ i : Fin 3, ∑ j : Fin 3, cubicTerm0 i j x)) +
      ((∑ i : Fin 3, pressureTerm0 i x) + ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm0 i j x)

private theorem localEnergy_energySequenceFacts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (squareTerm : ℕ → Fin 3 → α → ℝ) (squareTerm0 : Fin 3 → α → ℝ)
    (cubicTerm : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (cubicTerm0 : Fin 3 → Fin 3 → α → ℝ)
    (pressureTerm : ℕ → Fin 3 → α → ℝ) (pressureTerm0 : Fin 3 → α → ℝ)
    (stressTerm : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradientTerm : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradientTerm0 : Fin 3 → Fin 3 → α → ℝ)
    (hSquareN : ∀ n i, MemLp (squareTerm n i) 1 μ)
    (hSquare0 : ∀ i, MemLp (squareTerm0 i) 1 μ)
    (hCubicN : ∀ n i j, MemLp (cubicTerm n i j) 1 μ)
    (hCubic0 : ∀ i j, MemLp (cubicTerm0 i j) 1 μ)
    (hPressureN : ∀ n i, MemLp (pressureTerm n i) 1 μ)
    (hPressure0 : ∀ i, MemLp (pressureTerm0 i) 1 μ)
    (hStressN : ∀ n i j, MemLp (stressTerm n i j) 1 μ)
    (hGradientN : ∀ n i j, MemLp (gradientTerm n i j) 1 μ)
    (hGradient0 : ∀ i j, MemLp (gradientTerm0 i j) 1 μ)
    (hSquareConv : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => squareTerm n i x - squareTerm0 i x) 1 μ) atTop (nhds 0))
    (hCubicConv : ∀ i j, Tendsto (fun n => eLpNorm
      (fun x => cubicTerm n i j x - cubicTerm0 i j x) 1 μ) atTop (nhds 0))
    (hPressureConv : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => pressureTerm n i x - pressureTerm0 i x) 1 μ) atTop (nhds 0))
    (hStressConv : ∀ i j, Tendsto (fun n => eLpNorm (stressTerm n i j) 1 μ)
      atTop (nhds 0))
    (hGradientConv : ∀ i j, Tendsto (fun n => eLpNorm
      (fun x => gradientTerm n i j x - gradientTerm0 i j x) 1 μ) atTop (nhds 0)) :
    LocalEnergyEnergySequenceFacts μ squareTerm squareTerm0 cubicTerm cubicTerm0
      pressureTerm pressureTerm0 stressTerm gradientTerm gradientTerm0 := by
  let squareSum : ℕ → α → ℝ := fun n x => ∑ i : Fin 3, squareTerm n i x
  let squareSum0 : α → ℝ := fun x => ∑ i : Fin 3, squareTerm0 i x
  let cubicSum : ℕ → α → ℝ := fun n x => ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm n i j x
  let cubicSum0 : α → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm0 i j x
  let pressureSum : ℕ → α → ℝ := fun n x => ∑ i : Fin 3, pressureTerm n i x
  let pressureSum0 : α → ℝ := fun x => ∑ i : Fin 3, pressureTerm0 i x
  let stressSum : ℕ → α → ℝ := fun n x => ∑ i : Fin 3, ∑ j : Fin 3, stressTerm n i j x
  let gradientSum : ℕ → α → ℝ := fun n x => ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm n i j x
  let gradientSum0 : α → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm0 i j x
  let energyN : ℕ → α → ℝ := fun n x =>
    (squareSum n x + cubicSum n x) + ((pressureSum n x + stressSum n x) + gradientSum n x)
  let energy0 : α → ℝ := fun x =>
    (squareSum0 x + cubicSum0 x) + (pressureSum0 x + gradientSum0 x)
  have hFacts := localEnergy_finiteEnergyDensityLimit μ
    (fun n i x => squareTerm n i x) squareTerm0 cubicTerm cubicTerm0
    (fun n i x => pressureTerm n i x) pressureTerm0 stressTerm gradientTerm gradientTerm0
    squareSum squareSum0 cubicSum cubicSum0 pressureSum pressureSum0 stressSum
    gradientSum gradientSum0
    (by intro n i; exact hSquareN n i) (by intro i; exact hSquare0 i)
    hCubicN hCubic0 (by intro n i; exact hPressureN n i)
    (by intro i; exact hPressure0 i) hStressN hGradientN hGradient0
    hSquareConv hCubicConv hPressureConv hStressConv hGradientConv
  have hEnergyN (n : ℕ) : MemLp (energyN n) 1 μ := by
    simpa [energyN, squareSum, cubicSum, pressureSum, stressSum, gradientSum] using hFacts.1 n
  have hEnergy0 : MemLp energy0 1 μ := by
    simpa [energy0, squareSum0, cubicSum0, pressureSum0, gradientSum0] using hFacts.2.1
  have hEnergyConv : Tendsto (fun n => eLpNorm (energyN n - energy0) 1 μ)
      atTop (nhds 0) := by
    simpa [energyN, energy0, squareSum, squareSum0, cubicSum, cubicSum0,
      pressureSum, pressureSum0, stressSum, gradientSum, gradientSum0] using hFacts.2.2
  refine ⟨energyN, energy0, hEnergyN, hEnergy0, hEnergyConv, ?_, ?_⟩
  · intro n
    rfl
  · rfl

private theorem localEnergy_energySequence_eq_of_sum_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {squareTerm : ℕ → Fin 3 → α → ℝ} {squareTerm0 : Fin 3 → α → ℝ}
    {cubicTerm : ℕ → Fin 3 → Fin 3 → α → ℝ}
    {cubicTerm0 : Fin 3 → Fin 3 → α → ℝ}
    {pressureTerm : ℕ → Fin 3 → α → ℝ} {pressureTerm0 : Fin 3 → α → ℝ}
    {stressTerm : ℕ → Fin 3 → Fin 3 → α → ℝ}
    {gradientTerm : ℕ → Fin 3 → Fin 3 → α → ℝ}
    {gradientTerm0 : Fin 3 → Fin 3 → α → ℝ}
    (facts : LocalEnergyEnergySequenceFacts μ squareTerm squareTerm0 cubicTerm cubicTerm0
      pressureTerm pressureTerm0 stressTerm gradientTerm gradientTerm0)
    (targetN : ℕ → α → ℝ) (target0 : α → ℝ)
    (hN : ∀ n, (fun x =>
      ((∑ i : Fin 3, squareTerm n i x) +
        (∑ i : Fin 3, ∑ j : Fin 3, cubicTerm n i j x)) +
        (((∑ i : Fin 3, pressureTerm n i x) +
          (∑ i : Fin 3, ∑ j : Fin 3, stressTerm n i j x)) +
          ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm n i j x)) = targetN n)
    (h0 : (fun x =>
      ((∑ i : Fin 3, squareTerm0 i x) +
        (∑ i : Fin 3, ∑ j : Fin 3, cubicTerm0 i j x)) +
        ((∑ i : Fin 3, pressureTerm0 i x) +
          ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm0 i j x)) = target0) :
    (∀ n, facts.energyN n = targetN n) ∧ facts.energy0 = target0 := by
  constructor
  · intro n
    rw [facts.energyN_terms n]
    simpa [add_assoc] using hN n
  · rw [facts.energy0_terms]
    exact h0

private theorem localEnergy_integral_zero_of_L1_limit
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (fn : ℕ → α → ℝ)
    (hfn : ∀ n, MemLp (fn n) 1 μ)
    (hconv : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (nhds 0))
    (hzero : ∀ n, ∫ x, fn n x ∂μ = 0) : ∫ x, f x ∂μ = 0 := by
  have hIntegralConv := localEnergy_integral_tendsto_of_L1
    (μ := μ) (f := f) (fn := fn) hfn hconv
  have hZeroLimit : Tendsto (fun n : ℕ => ∫ x, fn n x ∂μ)
      atTop (nhds 0) := by
    have heq : (fun n : ℕ => ∫ x, fn n x ∂μ) = fun _ => 0 := by
      funext n
      exact hzero n
    rw [heq]
    exact tendsto_const_nhds
  have huniq := tendsto_nhds_unique hZeroLimit hIntegralConv
  simpa using huniq.symm

private def localEnergySeparatedBase
    (u : Vec3 × ℝ → Fin 3 → ℝ) (R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p ψ : Vec3 × ℝ → ℝ) (a : Vec3 × ℝ → ℝ)
    (b : Fin 3 → Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ := fun z =>
  ((∑ i : Fin 3, (u z i * u z i) * (-a z)) +
    (∑ i : Fin 3, ∑ j : Fin 3, (u z i * u z i * u z j) * (-b j z))) +
    (((∑ i : Fin 3, (p z * u z i) * ((-2 : ℝ) * b i z)) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        R z i j * ((-2 : ℝ) * (u z i * b j z + ψ z * G z i j)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, (G z i j * G z i j) * ((2 : ℝ) * ψ z)))

private theorem localEnergy_separatedBase_eq_expanded
    (u : Vec3 × ℝ → Fin 3 → ℝ) (R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p ψ₀ : Vec3 × ℝ → ℝ) (ψ : ParabolicPoint → ℝ)
    (a : Vec3 × ℝ → ℝ) (b : Fin 3 → Vec3 × ℝ → ℝ)
    (ha : ∀ z, a z = timePartial ψ (parabolicHomeomorph.symm z) +
      ∑ i : Fin 3, spatialSecondPartial ψ i i (parabolicHomeomorph.symm z))
    (hb : ∀ i z, b i z = spatialPartial ψ i (parabolicHomeomorph.symm z))
    (hψ : ∀ z, ψ (parabolicHomeomorph.symm z) = ψ₀ z) :
    localEnergySeparatedBase u R G p ψ₀ a b =
      localEnergyLimitExpandedBaseIntegrand u R G p ψ ψ := by
  funext z
  let squareTerm (i : Fin 3) := (u z i * u z i) * (-a z)
  let cubicTerm (i j : Fin 3) := (u z i * u z i * u z j) * (-b j z)
  let pressureTerm (i : Fin 3) := (p z * u z i) * ((-2 : ℝ) * b i z)
  let stressTerm (i j : Fin 3) := R z i j * ((-2 : ℝ) *
    (u z i * b j z + ψ₀ z * G z i j))
  let gradientTerm (i j : Fin 3) := (G z i j * G z i j) * ((2 : ℝ) * ψ₀ z)
  have hfirst : -(∑ i : Fin 3, u z i * u z i) * a z =
      ∑ i : Fin 3, squareTerm i := by
    calc
      _ = -((∑ i : Fin 3, u z i * u z i) * a z) := by ring
      _ = -(∑ i : Fin 3, (u z i * u z i) * a z) := by rw [Finset.sum_mul]
      _ = ∑ i : Fin 3, squareTerm i := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp [squareTerm]
  have hcubic : -(∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z i * u z j * b j z) =
        ∑ i : Fin 3, ∑ j : Fin 3, cubicTerm i j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [cubicTerm]
  have hpressure : -(∑ i : Fin 3, p z * u z i * (2 * b i z)) =
      ∑ i : Fin 3, pressureTerm i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [pressureTerm]
  have hstress : -(∑ i : Fin 3, ∑ j : Fin 3,
      R z i j * (2 * (u z i * b j z + ψ₀ z * G z i j))) =
        ∑ i : Fin 3, ∑ j : Fin 3, stressTerm i j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [stressTerm]
  change ((∑ i : Fin 3, squareTerm i) +
      (∑ i : Fin 3, ∑ j : Fin 3, cubicTerm i j)) +
      (((∑ i : Fin 3, pressureTerm i) +
        (∑ i : Fin 3, ∑ j : Fin 3, stressTerm i j)) +
        ∑ i : Fin 3, ∑ j : Fin 3, gradientTerm i j) = _
  rw [← ha z, ← hb, ← hψ z]
  simp only [localEnergyLimitExpandedBaseIntegrand, sub_eq_add_neg]
  rw [hfirst, hcubic, hpressure, hstress]
  simp only [squareTerm, cubicTerm, pressureTerm, stressTerm, gradientTerm]
  ring

private theorem localEnergy_mollifiedEnergySums_eq_expanded
    {α : Type*} (u : ℕ → α → Fin 3 → ℝ)
    (R G : ℕ → α → Fin 3 → Fin 3 → ℝ) (p : ℕ → α → ℝ)
    (u₀ : α → Fin 3 → ℝ) (R₀ G₀ : α → Fin 3 → Fin 3 → ℝ)
    (p₀ ψ₀ : α → ℝ) (ψ : ParabolicPoint → ℝ)
    (a : α → ℝ) (b : Fin 3 → α → ℝ)
    (square : ℕ → Fin 3 → α → ℝ) (square₀ : Fin 3 → α → ℝ)
    (cubic : ℕ → Fin 3 → Fin 3 → α → ℝ) (cubic₀ : Fin 3 → Fin 3 → α → ℝ)
    (pressure : ℕ → Fin 3 → α → ℝ) (pressure₀ : Fin 3 → α → ℝ)
    (stress : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (ha : ∀ z, a z = timePartial ψ (parabolicHomeomorph.symm z) +
      ∑ i : Fin 3, spatialSecondPartial ψ i i (parabolicHomeomorph.symm z))
    (hb : ∀ i z, b i z = spatialPartial ψ i (parabolicHomeomorph.symm z))
    (hψ : ∀ z, ψ (parabolicHomeomorph.symm z) = ψ₀ z) :
    (∀ n, (fun x =>
      ((∑ i : Fin 3, square n i x) + (∑ i : Fin 3, ∑ j : Fin 3, cubic n i j x)) +
        (((∑ i : Fin 3, pressure n i x) +
          (∑ i : Fin 3, ∑ j : Fin 3, stress n i j x)) +
            ∑ i : Fin 3, ∑ j : Fin 3, gradient n i j x)) =
      localEnergyLimitExpandedBaseIntegrand (u n) (R n) (G n) (p n) ψ x) ∧
    (fun x =>
      ((∑ i : Fin 3, square₀ i x) + (∑ i : Fin 3, ∑ j : Fin 3, cubic₀ i j x)) +
        ((∑ i : Fin 3, pressure₀ i x) +
          ∑ i : Fin 3, ∑ j : Fin 3, gradient₀ i j x)) =
      localEnergyLimitExpandedBaseIntegrand u₀ R₀ G₀ p₀ ψ := by
  constructor
  · intro n
    have hExpanded := localEnergy_separatedBase_eq_expanded
      (u n) (R n) (G n) (p n) ψ₀ ψ a b ha hb hψ
    funext x
    simpa [Finset.sum_const_zero] using congrFun hExpanded x
  · have hExpanded := localEnergy_separatedBase_eq_expanded
      u₀ R₀ G₀ p₀ ψ₀ ψ a b ha hb hψ
    funext x
    simpa [Finset.sum_const_zero] using congrFun hExpanded x

private theorem localEnergy_stressProduct_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (g : ℕ → Fin 3 → Fin 3 → α → ℝ) (g₀ : Fin 3 → Fin 3 → α → ℝ)
    (F : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (b : Fin 3 → α → ℝ) (ψ : α → ℝ)
    (hv₀ : ∀ i, MemLp (v₀ i) 4 μ) (hb₄ : ∀ j, MemLp (b j) 4 μ)
    (hv : ∀ n i, MemLp (v n i) 4 μ)
    (hvlim : ∀ i, Tendsto (fun n => eLpNorm (v n i - v₀ i) 4 μ) atTop (nhds 0))
    (hg₀ : ∀ i j, MemLp (g₀ i j) 2 μ) (hψ∞ : MemLp ψ ⊤ μ)
    (hg : ∀ n i j, MemLp (g n i j) 2 μ)
    (hglim : ∀ i j, Tendsto (fun n => eLpNorm (g n i j - g₀ i j) 2 μ)
      atTop (nhds 0))
    (hF : ∀ n i j, MemLp (F n i j) 2 μ)
    (hFlim : ∀ i j, Tendsto (fun n => eLpNorm (F n i j) 2 μ) atTop (nhds 0)) :
    ∀ i j, Tendsto (fun n => eLpNorm
      (fun x => F n i j x * ((-2 : ℝ) *
        (v n i x * b j x + ψ x * g n i j x))) 1 μ) atTop (nhds 0) := by
  have hUBConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun x => v n i x * b j x - v₀ i x * b j x) 2 μ) atTop (nhds 0) :=
    localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 4) (q := 4) (r := 2) (by norm_num)
      (hv₀ i) (hb₄ j) (fun n => hv n i) (hvlim i)
  have hGψConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun x => g n i j x * ψ x - g₀ i j x * ψ x) 2 μ) atTop (nhds 0) :=
    localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 2) (q := ⊤) (r := 2) (by norm_num)
      (hg₀ i j) hψ∞ (fun n => hg n i j) (hglim i j)
  have hKBaseN (n : ℕ) (i j : Fin 3) : MemLp
      (fun x => v n i x * b j x + ψ x * g n i j x) 2 μ := by
    have hleft : MemLp (fun x => v n i x * b j x) 2 μ :=
      MeasureTheory.MemLp.mul (p := 4) (q := 4) (r := 2) (hv n i) (hb₄ j)
    have hright : MemLp (fun x => ψ x * g n i j x) 2 μ :=
      MeasureTheory.MemLp.mul (p := ⊤) (q := 2) (r := 2) hψ∞ (hg n i j)
    exact hleft.add (by simpa [mul_comm] using hright)
  have hKBase₀ (i j : Fin 3) : MemLp
      (fun x => v₀ i x * b j x + ψ x * g₀ i j x) 2 μ := by
    have hleft : MemLp (fun x => v₀ i x * b j x) 2 μ :=
      MeasureTheory.MemLp.mul (p := 4) (q := 4) (r := 2) (hv₀ i) (hb₄ j)
    have hright : MemLp (fun x => ψ x * g₀ i j x) 2 μ :=
      MeasureTheory.MemLp.mul (p := ⊤) (q := 2) (r := 2) hψ∞ (hg₀ i j)
    exact hleft.add (by simpa [mul_comm] using hright)
  have hKBaseConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun x => (v n i x * b j x + ψ x * g n i j x) -
        (v₀ i x * b j x + ψ x * g₀ i j x)) 2 μ) atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_add_sub
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hUBConv i j) (by
        simpa [mul_comm] using hGψConv i j)
  have hKBaseScaledN (n : ℕ) (i j : Fin 3) : MemLp
      (fun x => (-2 : ℝ) * (v n i x * b j x + ψ x * g n i j x)) 2 μ :=
    (hKBaseN n i j).const_mul (-2)
  have hKBaseScaled₀ (i j : Fin 3) : MemLp
      (fun x => (-2 : ℝ) * (v₀ i x * b j x + ψ x * g₀ i j x)) 2 μ :=
    (hKBase₀ i j).const_mul (-2)
  have hKBaseScaledConv (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun x => (-2 : ℝ) * (v n i x * b j x + ψ x * g n i j x) -
        (-2 : ℝ) * (v₀ i x * b j x + ψ x * g₀ i j x)) 2 μ) atTop (nhds 0) :=
    localEnergy_tendsto_eLpNorm_const_smul_sub (-2) (hKBaseConv i j)
  intro i j
  have hzero : MemLp (fun _ : α => (0 : ℝ)) 2 μ := by simp
  have h := localEnergy_tendsto_eLpNorm_mul_sub
    (p := 2) (q := 2) (r := 1) (by norm_num)
    hzero (hKBaseScaled₀ i j) (fun n => hF n i j) (fun n => hKBaseScaledN n i j)
    (by simpa using hFlim i j) (hKBaseScaledConv i j)
  simpa using h

private theorem localEnergy_mollifiedFieldFacts
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
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (nhds 0))
    (hδpos : ∀ n, 0 < δ n) :
    (∀ n i, MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i) 4
      (volume : Measure (Vec3 × ℝ))) ∧
    (∀ n i j, MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j) 2
      (volume : Measure (Vec3 × ℝ))) ∧
    (∀ n i j, MemLp
      (fun z : Vec3 × ℝ => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j) 2
      (volume : Measure (Vec3 × ℝ))) ∧
    (∀ n, MemLp (localEnergyMollifiedPressure p (δ n) (hδpos n))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))) ∧
    (∀ i, MemLp (fun z => localEnergyVelocityZeroExtension u i z) 4
      (volume : Measure (Vec3 × ℝ))) ∧
    (∀ i j, MemLp (fun z => localEnergyGradientZeroExtension Du i j z) 2
      (volume : Measure (Vec3 × ℝ))) ∧
    MemLp (localEnergyPressureZeroExtension p) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) ∧
    (∀ i, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i -
        localEnergyVelocityZeroExtension u i z) 4 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0)) ∧
    (∀ i j, Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j -
        localEnergyGradientZeroExtension Du i j z) 2 (volume : Measure (Vec3 × ℝ)))
      atTop (nhds 0)) := by
  have hExt := localEnergy_zeroExtensionLp hu hDu henergy hpLp hL3 hgrad
  have hInputs := localEnergy_mollifiedInputs_tendsto
    hu hDu henergy hpLp hL3 hgrad hδ hδpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num) (hδpos n)
      (hExt.1 i)
  · intro n i j
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num) (hδpos n)
      (hExt.2.1 i j)
  · intro n i j
    exact localEnergy_mollify_memLp (by norm_num) (by norm_num) (hδpos n)
      (hExt.2.2.1 i j)
  · intro n
    exact localEnergy_mollify_memLp
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num)
      (hδpos n) hExt.2.2.2
  · intro i
    simpa [localEnergyVelocityZeroExtension, localEnergyUnitProductCylinder] using hExt.1 i
  · intro i j
    simpa [localEnergyGradientZeroExtension, localEnergyUnitProductCylinder] using hExt.2.2.1 i j
  · simpa [localEnergyPressureZeroExtension, localEnergyUnitProductCylinder] using hExt.2.2.2
  · intro i
    simpa [localEnergyMollifiedVelocity, localEnergyVelocityZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.1 i
  · intro i j
    simpa [localEnergyMollifiedGradient, localEnergyGradientZeroExtension,
      localEnergyUnitProductCylinder] using hInputs.2.2.1 i j

private structure LocalEnergyMollifiedProductLpFacts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ) : Prop where
  squareN : ∀ n i, MemLp (fun x => v n i x * v n i x) 2 μ
  square0 : ∀ i, MemLp (fun x => v₀ i x * v₀ i x) 2 μ
  cubicN : ∀ n i j, MemLp (fun x => v n i x * v n i x * v n j x)
    (ENNReal.ofReal (4 / 3 : ℝ)) μ
  cubic0 : ∀ i j, MemLp (fun x => v₀ i x * v₀ i x * v₀ j x)
    (ENNReal.ofReal (4 / 3 : ℝ)) μ
  pressureN : ∀ n i, MemLp (fun x => pressure n x * v n i x)
    (ENNReal.ofReal (12 / 11 : ℝ)) μ
  pressure0 : ∀ i, MemLp (fun x => pressure₀ x * v₀ i x)
    (ENNReal.ofReal (12 / 11 : ℝ)) μ
  gradientN : ∀ n i j, MemLp (fun x => gradient n i j x * gradient n i j x) 1 μ
  gradient0 : ∀ i j, MemLp (fun x => gradient₀ i j x * gradient₀ i j x) 1 μ

private structure LocalEnergyWeightedTermLpFacts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (F : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (b : Fin 3 → α → ℝ) (ψ : α → ℝ) (aNeg : α → ℝ) : Prop where
  squareN : ∀ n i, MemLp (fun x => (v n i x * v n i x) * aNeg x) 1 μ
  square0 : ∀ i, MemLp (fun x => (v₀ i x * v₀ i x) * aNeg x) 1 μ
  cubicN : ∀ n i j, MemLp
    (fun x => (v n i x * v n i x * v n j x) * (-b j x)) 1 μ
  cubic0 : ∀ i j, MemLp
    (fun x => (v₀ i x * v₀ i x * v₀ j x) * (-b j x)) 1 μ
  pressureN : ∀ n i, MemLp
    (fun x => (pressure n x * v n i x) * ((-2 : ℝ) * b i x)) 1 μ
  pressure0 : ∀ i, MemLp
    (fun x => (pressure₀ x * v₀ i x) * ((-2 : ℝ) * b i x)) 1 μ
  stressN : ∀ n i j, MemLp
    (fun x => F n i j x * ((-2 : ℝ) *
      (v n i x * b j x + ψ x * gradient n i j x))) 1 μ
  stress0 : ∀ i j, MemLp (fun _ : α => (0 : ℝ)) 1 μ
  gradientN : ∀ n i j, MemLp
    (fun x => (gradient n i j x * gradient n i j x) * ((2 : ℝ) * ψ x)) 1 μ
  gradient0 : ∀ i j, MemLp
    (fun x => (gradient₀ i j x * gradient₀ i j x) * ((2 : ℝ) * ψ x)) 1 μ

private theorem localEnergy_weightedTermLpFacts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (F : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (b : Fin 3 → α → ℝ) (ψ : α → ℝ) (aNeg : α → ℝ)
    (hProducts : LocalEnergyMollifiedProductLpFacts
      μ v v₀ pressure pressure₀ gradient gradient₀)
    (hF : ∀ n i j, MemLp (F n i j) 2 μ)
    (hK : ∀ n i j, MemLp
      (fun x => (-2 : ℝ) * (v n i x * b j x + ψ x * gradient n i j x)) 2 μ)
    (hb4Neg : ∀ j, MemLp (fun x => -b j x) 4 μ)
    (hb12Neg : ∀ i, MemLp (fun x => (-2 : ℝ) * b i x) 12 μ)
    (haNeg : MemLp aNeg 2 μ) (hψTwo : MemLp (fun x => (2 : ℝ) * ψ x) ⊤ μ) :
    LocalEnergyWeightedTermLpFacts μ v v₀ pressure pressure₀ F gradient gradient₀
      b ψ aNeg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · intro n i
    exact MeasureTheory.MemLp.mul (p := 2) (q := 2) (r := 1)
      (hProducts.squareN n i) haNeg
  · intro i
    exact MeasureTheory.MemLp.mul (p := 2) (q := 2) (r := 1)
      (hProducts.square0 i) haNeg
  · intro n i j
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (4 / 3 : ℝ)) (q := 4) (r := 1)
      (hProducts.cubicN n i j) (hb4Neg j)
  · intro i j
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (4 / 3 : ℝ)) (q := 4) (r := 1)
      (hProducts.cubic0 i j) (hb4Neg j)
  · intro n i
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (12 / 11 : ℝ)) (q := 12) (r := 1)
      (hProducts.pressureN n i) (hb12Neg i)
  · intro i
    exact MeasureTheory.MemLp.mul (p := ENNReal.ofReal (12 / 11 : ℝ)) (q := 12) (r := 1)
      (hProducts.pressure0 i) (hb12Neg i)
  · intro n i j
    exact MeasureTheory.MemLp.mul (p := 2) (q := 2) (r := 1)
      (hF n i j) (hK n i j)
  · intro n i j
    exact MeasureTheory.MemLp.mul (p := 1) (q := ⊤) (r := 1)
      (hProducts.gradientN n i j) hψTwo
  · intro i j
    exact MeasureTheory.MemLp.mul (p := 1) (q := ⊤) (r := 1)
      (hProducts.gradient0 i j) hψTwo

private theorem localEnergy_mollifiedProductLpFacts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (hv : ∀ n i, MemLp (v n i) 4 μ) (hv₀ : ∀ i, MemLp (v₀ i) 4 μ)
    (hp : ∀ n, MemLp (pressure n) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hp₀ : MemLp pressure₀ (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hg : ∀ n i j, MemLp (gradient n i j) 2 μ)
    (hg₀ : ∀ i j, MemLp (gradient₀ i j) 2 μ) :
    LocalEnergyMollifiedProductLpFacts μ v v₀ pressure pressure₀ gradient gradient₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i
    exact (hv n i).mul (hv n i)
  · intro i
    exact (hv₀ i).mul (hv₀ i)
  · intro n i j
    exact ((hv n i).mul (hv n i)).mul (hv n j)
  · intro i j
    exact ((hv₀ i).mul (hv₀ i)).mul (hv₀ j)
  · intro n i
    exact (hp n).mul (hv n i)
  · intro i
    exact hp₀.mul (hv₀ i)
  · intro n i j
    exact (hg n i j).mul (hg n i j)
  · intro i j
    exact (hg₀ i j).mul (hg₀ i j)

private structure LocalEnergyMollifiedProductLimits
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (F : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ) : Prop where
  square : ∀ i, Tendsto (fun n => eLpNorm
    (fun x => v n i x * v n i x - v₀ i x * v₀ i x) 2 μ) atTop (nhds 0)
  cubic : ∀ i j, Tendsto (fun n => eLpNorm
    (fun x => v n i x * v n i x * v n j x - v₀ i x * v₀ i x * v₀ j x)
    (ENNReal.ofReal (4 / 3 : ℝ)) μ) atTop (nhds 0)
  pressure : ∀ i, Tendsto (fun n => eLpNorm
    (fun x => pressure n x * v n i x - pressure₀ x * v₀ i x)
    (ENNReal.ofReal (12 / 11 : ℝ)) μ) atTop (nhds 0)
  residual : ∀ i j, Tendsto (fun n => eLpNorm (F n i j) 2 μ) atTop (nhds 0)
  gradient : ∀ i j, Tendsto (fun n => eLpNorm
    (fun x => gradient n i j x * gradient n i j x - gradient₀ i j x * gradient₀ i j x)
    1 μ) atTop (nhds 0)

private theorem localEnergy_weightedEnergyTermLimits
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (F : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (b : Fin 3 → α → ℝ) (ψ : α → ℝ) (aNeg : α → ℝ)
    (hLP : LocalEnergyMollifiedProductLpFacts μ v v₀ pressure pressure₀ gradient gradient₀)
    (hLimits : LocalEnergyMollifiedProductLimits μ v v₀ pressure pressure₀ F gradient gradient₀)
    (hF : ∀ n i j, MemLp (F n i j) 2 μ)
    (hv : ∀ n i, MemLp (v n i) 4 μ) (hv₀ : ∀ i, MemLp (v₀ i) 4 μ)
    (hg : ∀ n i j, MemLp (gradient n i j) 2 μ)
    (hg₀ : ∀ i j, MemLp (gradient₀ i j) 2 μ)
    (hb4 : ∀ j, MemLp (b j) 4 μ) (hb12 : ∀ i, MemLp (b i) 12 μ)
    (hψInf : MemLp ψ ⊤ μ) (haNeg : MemLp aNeg 2 μ)
    (hvLim : ∀ i, Tendsto (fun n => eLpNorm (v n i - v₀ i) 4 μ)
      atTop (nhds 0))
    (hgLim : ∀ i j, Tendsto (fun n => eLpNorm (gradient n i j - gradient₀ i j) 2 μ)
      atTop (nhds 0)) :
    (∀ i, Tendsto (fun n => eLpNorm
      (fun x => v n i x * v n i x * aNeg x - v₀ i x * v₀ i x * aNeg x) 1 μ)
      atTop (nhds 0)) ∧
    (∀ i j, Tendsto (fun n => eLpNorm
      (fun x => v n i x * v n i x * v n j x * (-b j x) -
        v₀ i x * v₀ i x * v₀ j x * (-b j x)) 1 μ) atTop (nhds 0)) ∧
    (∀ i, Tendsto (fun n => eLpNorm
      (fun x => pressure n x * v n i x * ((-2 : ℝ) * b i x) -
        pressure₀ x * v₀ i x * ((-2 : ℝ) * b i x)) 1 μ) atTop (nhds 0)) ∧
    (∀ i j, Tendsto (fun n => eLpNorm
      (fun x => F n i j x * ((-2 : ℝ) *
        (v n i x * b j x + ψ x * gradient n i j x))) 1 μ) atTop (nhds 0)) ∧
    (∀ i j, Tendsto (fun n => eLpNorm
      (fun x => gradient n i j x * gradient n i j x * ((2 : ℝ) * ψ x) -
        gradient₀ i j x * gradient₀ i j x * ((2 : ℝ) * ψ x)) 1 μ) atTop (nhds 0)) := by
  have hStress := localEnergy_stressProduct_tendsto μ v v₀ gradient gradient₀ F b ψ
    hv₀ hb4 hv hvLim hg₀ hψInf hg hgLim hF hLimits.residual
  have hb4Neg (j : Fin 3) : MemLp (fun x => -b j x) 4 μ := (hb4 j).neg
  have hb12Neg (i : Fin 3) : MemLp (fun x => (-2 : ℝ) * b i x) 12 μ :=
    (hb12 i).const_mul (-2)
  have hψTwo : MemLp (fun x => (2 : ℝ) * ψ x) ⊤ μ := hψInf.const_mul 2
  refine ⟨?_, ?_, ?_, hStress, ?_⟩
  · intro i
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 2) (q := 2) (r := 1) (by norm_num)
      (hLP.square0 i) haNeg (fun n => hLP.squareN n i) (hLimits.square i)
  · intro i j
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := ENNReal.ofReal (4 / 3 : ℝ)) (q := 4) (r := 1) (by norm_num)
      (hLP.cubic0 i j) (hb4Neg j) (fun n => hLP.cubicN n i j) (hLimits.cubic i j)
  · intro i
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := ENNReal.ofReal (12 / 11 : ℝ)) (q := 12) (r := 1) (by norm_num)
      (hLP.pressure0 i) (hb12Neg i) (fun n => hLP.pressureN n i) (hLimits.pressure i)
  · intro i j
    exact localEnergy_tendsto_eLpNorm_mul_fixed
      (p := 1) (q := ⊤) (r := 1) (by norm_num)
      (hLP.gradient0 i j) hψTwo (fun n => hLP.gradientN n i j) (hLimits.gradient i j)

private structure LocalEnergyWeightedTermLimitFacts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (F : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (b : Fin 3 → α → ℝ) (ψ : α → ℝ) (aNeg : α → ℝ) : Prop where
  square : ∀ i, Tendsto (fun n => eLpNorm
    (fun x => v n i x * v n i x * aNeg x - v₀ i x * v₀ i x * aNeg x) 1 μ)
    atTop (nhds 0)
  cubic : ∀ i j, Tendsto (fun n => eLpNorm
    (fun x => v n i x * v n i x * v n j x * (-b j x) -
      v₀ i x * v₀ i x * v₀ j x * (-b j x)) 1 μ) atTop (nhds 0)
  pressure : ∀ i, Tendsto (fun n => eLpNorm
    (fun x => pressure n x * v n i x * ((-2 : ℝ) * b i x) -
      pressure₀ x * v₀ i x * ((-2 : ℝ) * b i x)) 1 μ) atTop (nhds 0)
  stress : ∀ i j, Tendsto (fun n => eLpNorm
    (fun x => F n i j x * ((-2 : ℝ) *
      (v n i x * b j x + ψ x * gradient n i j x))) 1 μ) atTop (nhds 0)
  gradient : ∀ i j, Tendsto (fun n => eLpNorm
    (fun x => gradient n i j x * gradient n i j x * ((2 : ℝ) * ψ x) -
      gradient₀ i j x * gradient₀ i j x * ((2 : ℝ) * ψ x)) 1 μ) atTop (nhds 0)

private theorem localEnergy_weightedTermAnalysis
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → Fin 3 → α → ℝ) (v₀ : Fin 3 → α → ℝ)
    (pressure : ℕ → α → ℝ) (pressure₀ : α → ℝ)
    (F : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient : ℕ → Fin 3 → Fin 3 → α → ℝ)
    (gradient₀ : Fin 3 → Fin 3 → α → ℝ)
    (b : Fin 3 → α → ℝ) (ψ : α → ℝ) (aNeg : α → ℝ)
    (hLP : LocalEnergyMollifiedProductLpFacts μ v v₀ pressure pressure₀ gradient gradient₀)
    (hProducts : LocalEnergyMollifiedProductLimits μ v v₀ pressure pressure₀ F gradient gradient₀)
    (hF : ∀ n i j, MemLp (F n i j) 2 μ)
    (hv : ∀ n i, MemLp (v n i) 4 μ) (hv₀ : ∀ i, MemLp (v₀ i) 4 μ)
    (hg : ∀ n i j, MemLp (gradient n i j) 2 μ)
    (hg₀ : ∀ i j, MemLp (gradient₀ i j) 2 μ)
    (hb4 : ∀ j, MemLp (b j) 4 μ) (hb12 : ∀ i, MemLp (b i) 12 μ)
    (hψInf : MemLp ψ ⊤ μ) (haNeg : MemLp aNeg 2 μ)
    (hvLim : ∀ i, Tendsto (fun n => eLpNorm (v n i - v₀ i) 4 μ) atTop (nhds 0))
    (hgLim : ∀ i j, Tendsto (fun n => eLpNorm
      (gradient n i j - gradient₀ i j) 2 μ) atTop (nhds 0)) :
    LocalEnergyWeightedTermLpFacts μ v v₀ pressure pressure₀ F gradient gradient₀ b ψ aNeg ∧
      LocalEnergyWeightedTermLimitFacts μ v v₀ pressure pressure₀ F gradient gradient₀
        b ψ aNeg := by
  have hb4Neg (j : Fin 3) : MemLp (fun x => -b j x) 4 μ := (hb4 j).neg
  have hb12Neg (i : Fin 3) : MemLp (fun x => (-2 : ℝ) * b i x) 12 μ :=
    (hb12 i).const_mul (-2)
  have hψTwo : MemLp (fun x => (2 : ℝ) * ψ x) ⊤ μ := hψInf.const_mul 2
  have hK (n : ℕ) (i j : Fin 3) : MemLp
      (fun x => (-2 : ℝ) * (v n i x * b j x + ψ x * gradient n i j x)) 2 μ := by
    have hleft : MemLp (fun x => v n i x * b j x) 2 μ :=
      MeasureTheory.MemLp.mul (p := 4) (q := 4) (r := 2) (hv n i) (hb4 j)
    have hright : MemLp (fun x => ψ x * gradient n i j x) 2 μ :=
      MeasureTheory.MemLp.mul (p := ⊤) (q := 2) (r := 2) hψInf (hg n i j)
    exact (hleft.add (by simpa [mul_comm] using hright)).const_mul (-2)
  have hTermLp := localEnergy_weightedTermLpFacts μ v v₀ pressure pressure₀ F
    gradient gradient₀ b ψ aNeg hLP hF hK hb4Neg hb12Neg haNeg hψTwo
  have hLimits := localEnergy_weightedEnergyTermLimits μ v v₀ pressure pressure₀ F
    gradient gradient₀ b ψ aNeg hLP hProducts hF hv hv₀ hg hg₀ hb4 hb12 hψInf
    haNeg hvLim hgLim
  exact ⟨hTermLp, ⟨hLimits.1, hLimits.2.1, hLimits.2.2.1,
    hLimits.2.2.2.1, hLimits.2.2.2.2⟩⟩

private theorem localEnergy_mollifiedExpandedBaseIntegral_zero
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (ψ : ParabolicPoint → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hzero : ∫ z, smoothEnergyBaseIntegrand
      (fun y i => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i)) δ hδ y)
      (fun y i j => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => u q i * u q j)) δ hδ y -
          spaceTimeMollify
            ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
              (fun q : Vec3 × ℝ => u q i)) δ hδ y *
            spaceTimeMollify
              ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
                (fun q : Vec3 × ℝ => u q j)) δ hδ y)
      (fun y i j => spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
          (fun q : Vec3 × ℝ => Du q i j)) δ hδ y)
      (spaceTimeMollify
        ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p) δ hδ)
      ψ z ∂(volume : Measure (Vec3 × ℝ)) = 0) :
    ∫ z, localEnergyLimitExpandedBaseIntegrand
      (localEnergyMollifiedVelocity u δ hδ)
      (fun z i j => localEnergyMollifiedTensor u δ hδ z i j -
        localEnergyMollifiedVelocity u δ hδ z i * localEnergyMollifiedVelocity u δ hδ z j)
      (localEnergyMollifiedGradient Du δ hδ) (localEnergyMollifiedPressure p δ hδ)
      (show ParabolicPoint → ℝ from ψ) z ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
  rw [← localEnergy_smoothBase_eq_expanded (hψ := hψ)]
  change ∫ z, smoothEnergyBaseIntegrand
    (fun y i => spaceTimeMollify
      ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun q : Vec3 × ℝ => u q i)) δ hδ y)
    (fun y i j => spaceTimeMollify
      ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun q : Vec3 × ℝ => u q i * u q j)) δ hδ y -
        spaceTimeMollify
          ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
            (fun q : Vec3 × ℝ => u q i)) δ hδ y *
          spaceTimeMollify
            ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
              (fun q : Vec3 × ℝ => u q j)) δ hδ y)
    (fun y i j => spaceTimeMollify
      ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
        (fun q : Vec3 × ℝ => Du q i j)) δ hδ y)
    (spaceTimeMollify
      ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p) δ hδ)
    ψ z = 0
  exact hzero

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
  have hScales := localEnergy_exists_scales_for_test hψc hψU
  obtain ⟨ε, hε, δ, hδ, hδpos, hcover⟩ := hScales
  have hProducts := localEnergy_mollifiedProducts_tendsto hu hDu henergy hpLp hL3 hgrad
    hδ hδpos
  have hProductLimits : LocalEnergyMollifiedProductLimits
      (volume : Measure (Vec3 × ℝ))
      (fun n i z => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i)
      (fun i z => u0 z i)
      (fun n z => localEnergyMollifiedPressure p (δ n) (hδpos n) z) p0
      (fun n i j z => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z j)
      (fun n i j z => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j)
      (fun i j z => g0 z i j) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa [u0] using hProducts.1 i
    · intro i j
      simpa [u0] using hProducts.2.1 i j
    · intro i
      simpa [u0, p0] using hProducts.2.2.1 i
    · intro i j
      exact hProducts.2.2.2.1 i j
    · intro i j
      simpa [g0] using hProducts.2.2.2.2 i j
  have ha : MemLp a 2 (volume : Measure (Vec3 × ℝ)) := by
    simpa [a] using hCoeff.1
  have hb4 (i : Fin 3) : MemLp (b i) 4 (volume : Measure (Vec3 × ℝ)) := by
    simpa [b] using hCoeff.2.1 i
  have hb12 (i : Fin 3) : MemLp (b i) 12 (volume : Measure (Vec3 × ℝ)) := by
    simpa [b] using hCoeff.2.2.1 i
  have hψInf : MemLp ψ ⊤ (volume : Measure (Vec3 × ℝ)) := hCoeff.2.2.2
  have hFieldFacts := localEnergy_mollifiedFieldFacts
    hu hDu henergy hpLp hL3 hgrad hδ hδpos
  have huN := hFieldFacts.1
  have hGN := hFieldFacts.2.2.1
  have hpN := hFieldFacts.2.2.2.1
  have hU0 (i : Fin 3) : MemLp (fun z => u0 z i) 4
      (volume : Measure (Vec3 × ℝ)) := by simpa [u0] using hFieldFacts.2.2.2.2.1 i
  have hG0 (i j : Fin 3) : MemLp (fun z => g0 z i j) 2
      (volume : Measure (Vec3 × ℝ)) := by simpa [g0] using hFieldFacts.2.2.2.2.2.1 i j
  have hp0 : MemLp p0 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by simpa [p0] using hFieldFacts.2.2.2.2.2.2.1
  have huLim (i : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i - u0 z i)
      4 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    simpa [u0] using hFieldFacts.2.2.2.2.2.2.2.1 i
  have hGLim (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j - g0 z i j)
      2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
    simpa [g0] using hFieldFacts.2.2.2.2.2.2.2.2 i j
  have hProductLpFacts := localEnergy_mollifiedProductLpFacts
    (volume : Measure (Vec3 × ℝ))
    (fun n i z => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i)
    (fun i z => u0 z i)
    (fun n z => localEnergyMollifiedPressure p (δ n) (hδpos n) z) p0
    (fun n i j z => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j)
    (fun i j z => g0 z i j) huN hU0 hpN hp0 hGN hG0
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

  have hTermAnalysis := localEnergy_weightedTermAnalysis
    (volume : Measure (Vec3 × ℝ))
    (fun n i z => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i)
    (fun i z => u0 z i)
    (fun n z => localEnergyMollifiedPressure p (δ n) (hδpos n) z) p0
    (fun n i j z => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
      localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z j)
    (fun n i j z => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j)
    (fun i j z => g0 z i j) b ψ (fun z => -a z)
    hProductLpFacts hProductLimits
    (fun n i j => (hFieldFacts.2.1 n i j).sub ((huN n i).mul (huN n j)))
    huN hU0 hGN hG0 hb4 hb12 hψInf ha.neg huLim hGLim
  have hTermLp := hTermAnalysis.1
  have hSquareTermConv := hTermAnalysis.2.square
  have hCubicTermConv := hTermAnalysis.2.cubic
  have hPressureTermConv := hTermAnalysis.2.pressure
  have hStressExpandedConv := hTermAnalysis.2.stress
  have hGradientTermConv := hTermAnalysis.2.gradient
  have hSquareTermN := hTermLp.squareN
  have hSquareTerm0 := hTermLp.square0
  have hCubicTermN := hTermLp.cubicN
  have hCubicTerm0 := hTermLp.cubic0
  have hPressureTermN := hTermLp.pressureN
  have hPressureTerm0 := hTermLp.pressure0
  have hStressTermN := hTermLp.stressN
  have hStressTerm0 := hTermLp.stress0
  have hGradientTermN := hTermLp.gradientN
  have hGradientTerm0 := hTermLp.gradient0

  have hEnergySequence := localEnergy_energySequenceFacts
    (volume : Measure (Vec3 × ℝ)) squareTerm squareTerm0 cubicTerm cubicTerm0
    pressureTerm pressureTerm0 stressTerm gradientTerm gradientTerm0
    hSquareTermN hSquareTerm0 hCubicTermN hCubicTerm0 hPressureTermN hPressureTerm0
    hStressTermN hGradientTermN hGradientTerm0
    hSquareTermConv hCubicTermConv hPressureTermConv hStressExpandedConv
    hGradientTermConv
  let energyN := hEnergySequence.energyN
  let energy0 := hEnergySequence.energy0

  have hEnergySumsExpanded := localEnergy_mollifiedEnergySums_eq_expanded
    (fun n z i => localEnergyMollifiedVelocity u (δ n) (hδpos n) z i)
    (fun n z i j => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
      localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z j)
    (fun n z i j => localEnergyMollifiedGradient Du (δ n) (hδpos n) z i j)
    (fun n z => localEnergyMollifiedPressure p (δ n) (hδpos n) z)
    u0 (fun _ _ _ => 0) g0 p0 ψ ψP a b
    squareTerm squareTerm0 cubicTerm cubicTerm0 pressureTerm pressureTerm0
    stressTerm gradientTerm gradientTerm0 (fun z => rfl) (fun i z => rfl)
    (fun z => by simp [ψP])
  have hEnergyExpanded := localEnergy_energySequence_eq_of_sum_eq hEnergySequence
    (fun n => localEnergyLimitExpandedBaseIntegrand
      (localEnergyMollifiedVelocity u (δ n) (hδpos n))
      (fun z i j => localEnergyMollifiedTensor u (δ n) (hδpos n) z i j -
        localEnergyMollifiedVelocity u (δ n) (hδpos n) z i *
          localEnergyMollifiedVelocity u (δ n) (hδpos n) z j)
      (localEnergyMollifiedGradient Du (δ n) (hδpos n))
      (localEnergyMollifiedPressure p (δ n) (hδpos n)) ψP)
    (localEnergyLimitExpandedBaseIntegrand u0 (fun _ _ _ => 0) g0 p0 ψP)
    hEnergySumsExpanded.1 hEnergySumsExpanded.2
  have hEnergyN_eq_expanded := hEnergyExpanded.1
  have hEnergy0_eq_expanded := hEnergyExpanded.2

  have hMollifiedZero (n : ℕ) : ∫ z, energyN n z
      ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    rw [hEnergyN_eq_expanded n]
    have hzero := localEnergy_mollified_base_integral_zero
      hu hDu henergy hpLp hL3 hgrad hS2 hS3 hψ hψc (hδpos n) (hcover n)
    exact localEnergy_mollifiedExpandedBaseIntegral_zero
      (hδpos n) ψP hψ hzero

  have hIntegralZero := localEnergy_integral_zero_of_L1_limit
    (volume : Measure (Vec3 × ℝ)) energy0 energyN hEnergySequence.energyN_memLp
    hEnergySequence.energy_tendsto hMollifiedZero
  rw [hEnergy0_eq_expanded] at hIntegralZero
  change ∫ z, localEnergyLimitExpandedBaseIntegrand
    (fun z i => localEnergyVelocityZeroExtension u i z)
    (fun z i j => (0 : ℝ))
    (fun z i j => localEnergyGradientZeroExtension Du i j z)
    (localEnergyPressureZeroExtension p) ψP z = 0
  exact hIntegralZero

end ESS

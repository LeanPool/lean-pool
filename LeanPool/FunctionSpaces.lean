/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces
public import LeanPool.FunctionSpaces.Domains.Cube.IsoCoincidence
public import LeanPool.FunctionSpaces.Domains.Extension.HigherSobolevExtension
public import LeanPool.FunctionSpaces.Domains.Interval.SplinePeriodicJackson
public import LeanPool.FunctionSpaces.Domains.Manifolds.BoundaryTrace
public import LeanPool.FunctionSpaces.Domains.Spectral.ManifoldSpectralBesov
public import LeanPool.FunctionSpaces.Domains.Traces.BoundaryGagliardo
public import LeanPool.FunctionSpaces.Domains.Traces.TraceKernel
public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Interpolation
public import LeanPool.FunctionSpaces.Rd.BesselPotentials.BesselPotentialEmbedding
public import LeanPool.FunctionSpaces.Rd.FourierMultipliers.BesselPotentialMultipliers
public import LeanPool.FunctionSpaces.Rd.FourierMultipliers.MihlinMultipliers
public import LeanPool.FunctionSpaces.Rd.Interpolation.BesovInterpolation
public import LeanPool.FunctionSpaces.Rd.Interpolation.SobolevInterpolation
public import LeanPool.FunctionSpaces.Rd.MixedSmoothness.HyperbolicCross
public import LeanPool.FunctionSpaces.Rd.Sobolev.GagliardoNirenbergSobolev
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.LittlewoodPaleyFamilies
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinAtoms
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinDifferences
public import LeanPool.FunctionSpaces.Torus.BesovInterpolation
public import LeanPool.FunctionSpaces.Torus.BesovModuli
public import LeanPool.FunctionSpaces.Torus.FourierSpectralBasis
public import LeanPool.FunctionSpaces.Torus.NTermFourier
public import LeanPool.FunctionSpaces.Torus.PeriodicDistributions
public import LeanPool.FunctionSpaces.Torus.SobolevEmbedding
public import LeanPool.FunctionSpaces.Torus.TraceContinuous
public import LeanPool.FunctionSpaces.Torus.TriebelLizorkinInterpolation
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.D4Besov
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.OrderThree
public import LeanPool.FunctionSpaces.Wavelets.Examples.DyadicStepsQuasiBanach

/-
Modified for Lean Pool by adapting the module names and reducing direct imports.
-/

/-!
# Characterizations of Besov, Triebel–Lizorkin and Sobolev spaces

Source: url:https://github.com/mario-ullrich/Lean-FunctionSpaces/blob/d8b2b349567adb7ad049d517dec50bff4165e606/README.md
Authors: Mario Ullrich
Status: verified
Main declarations: `Rd.LocalMeansBump.besov_iff_atomic`, `Rd.memTriebelLizorkin_iff_atomic`,
  `Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`, `Daubechies.besov_iff_coeff_d4`,
  `Haar.memEMethod_stepCouple_iff_modulus`, `ApproximationScheme.memKMethod_reiteration`
Tags: approximation-theory, functional-analysis, harmonic-analysis, real-interpolation, wavelets
MSC: 46E35, 46B70, 42C40
-/

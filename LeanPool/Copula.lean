/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel, Gaëtan Serré, Rémy Degenne
-/

module

public import LeanPool.Copula.Classical.Characterization
public import LeanPool.Copula.Sklar.General
public import LeanPool.Copula.CDF.Bounds

/-!
# Finite-dimensional copulas and Sklar's theorem

Source: url:https://github.com/Corrram/copula/tree/fe53ea2f3e6af41da8541e7d0aa2edc38ed0dcc8
Authors: Marcus Rockel, Gaëtan Serré, Rémy Degenne
Status: verified
Main declarations: `ProbabilityTheory.Copula.exists_sklarCopula`
Tags: copulas, sklar-theorem, probability-measures, disintegration, quantiles
MSC: 60E05, 60B05
-/

/-!
## Mathematical scope

The completed core of Marcus Rockel's copula library, from
https://github.com/Corrram/copula/tree/fe53ea2f3e6af41da8541e7d0aa2edc38ed0dcc8.
It includes arbitrary real marginals, continuous-marginal uniqueness, the classical
CDF characterization in every finite dimension, and reusable randomized lifting.
-/

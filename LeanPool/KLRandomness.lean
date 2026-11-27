/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BaseInvariance
public import LeanPool.KLRandomness.Separation

/-!
# Kolmogorov–Loveland and Martin–Löf randomness

Source: arxiv:2611.31004v1, url:https://github.com/bjoernkjoshanssen/klr/tree/81f5fef2de3142aad714624033a5aa4f12031a6b
Authors: Bjørn Kjos-Hanssen
Status: verified
Main declarations: `Klr.martinLofRandom_ssubset_kolmogorovLovelandRandom`,
  `Klr.exists_not_martinLofRandom_no_partial_rational_success`,
  `Klr.binary_random_ssubset_baseFour_random`
Tags: algorithmic randomness, computability, martingales, effective measure theory
MSC: 03D32, 03B35
-/

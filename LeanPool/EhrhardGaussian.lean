/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EhrhardGaussian.Results.EhrhardInequality
public import LeanPool.EhrhardGaussian.Results.EhrhardTypeCharacterization
public import LeanPool.EhrhardGaussian.Results.GaussianConvexity

/-!
# Ehrhard's inequality and Gaussian log-MGF convexity

Source: arxiv:2311.08351, url:https://github.com/scottnarmstrong/Critical2DKPZ/tree/f1c98dacb2a83737096bd976019dfa2c5986ee5a
Authors: Scott Armstrong, Ahmed Bou-Rabee
Status: verified
Main declarations: `EhrhardGaussian.ehrhard_inequality`, `EhrhardGaussian.gaussian_convexity`,
  `EhrhardGaussian.Provider.ehrhardType_representation`,
  `EhrhardGaussian.Provider.ehrhardType_weakClosure`,
  `EhrhardGaussian.Provider.ehrhardType_momentBounds`
Tags: gaussian-measures, convexity, ehrhard-inequality, moment-generating-functions
MSC: 60D05, 60E15, 52A40
-/

/-! # Ehrhard's inequality and Gaussian convexity

Probability-theory dependency closure from Scott Armstrong's `Critical2DKPZ`,
commit `f1c98dacb2a83737096bd976019dfa2c5986ee5a` (Apache-2.0).
The proofs were written by AI agents under Armstrong's supervision.

The log-MGF theorem is Wei-Kuo Chen's Theorem 1 (arXiv:2311.08351v2).
The representation and moment arguments adapt Fernandez-Unzueta, Melbourne and
Palafox-Castillo, *On Convex Functions of Gaussian Variables*
(arXiv:2510.06676v1). The selected scope is the non-strict convex branch with
finite moments, including the value at zero and constant Gaussian images.
-/

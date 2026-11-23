/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

module

public import LeanPool.CutoffRigidity.ConvexInteractionTheorem
public import LeanPool.CutoffRigidity.EuclideanGaussianSplitting
public import LeanPool.CutoffRigidity.GaussianTransport.RiemannianLowerBound
public import LeanPool.CutoffRigidity.RiemannianSplitting.Extra.SplitPotential

/-!
# Gaussian splitting and convex interaction for rigid diffusions

Source: arxiv:2412.15969v5, url:https://github.com/djalilchafai/cutoff-rigidity-diffusions/tree/f3bf3663cfe743aaf74cd76bb2a7076c816a176f
Authors: Djalil Chafaï
Status: verified
Main declarations: `CutoffRigidity.normalized_convexInteraction_theorem`,
  `CutoffRigidity.euclidean_gaussian_splitting`,
  `CutoffRigidity.Paper.riemannian_gaussian_splitting`,
  `CutoffRigidity.Riemann.SplitData.lower_of_moments`,
  `CutoffRigidity.Paper.riemannian_transport_lower_of_moments`
Tags: curvature, spectral-gap, gaussian-factorization, gibbs-measures
MSC: 60J60, 47D07, 53C21
-/

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Defs
public import LeanPool.Cutfast.Radial
public import LeanPool.Cutfast.Moments
public import LeanPool.Cutfast.Barenblatt
public import LeanPool.Cutfast.Wasserstein
public import LeanPool.Cutfast.Elliptic
public import LeanPool.Cutfast.GaussianDensity
public import LeanPool.Cutfast.Distances
public import LeanPool.Cutfast.PDE
public import LeanPool.Cutfast.Asymptotics
public import LeanPool.Cutfast.Cutoff
public import LeanPool.Cutfast.FDE
public import LeanPool.Cutfast.HeavyTail
public import LeanPool.Cutfast.Entropy
public import LeanPool.Cutfast.DiffusionLimit
public import LeanPool.Cutfast.CutoffRadius
public import LeanPool.Cutfast.Student
public import LeanPool.Cutfast.Sphere

/-!
# Cutoff for fast diffusion and porous medium equations

Source: arxiv:2503.11770v2, url:https://github.com/djalilchafai/cutoff-fastdiff/tree/6621bf2a7779c7fb7cbda04bb7c860d853c5c516
Authors: Djalil Chafaï
Status: verified
Main declarations: `Cutfast.cutoff_wassersteinSq`, `Cutfast.cutoff_relEntropy`,
  `Cutfast.cutoff_fisherInfo`, `Cutfast.cutoff_fixedExponent_wassersteinSq`,
  `Cutfast.cutoff_fixedExponent_relEntropy`, `Cutfast.cutoff_fixedExponent_fisherInfo`
Tags: barenblatt-profiles, cutoff-phenomenon, optimal-transport, porous-medium-equation
MSC: 35K55, 35B40, 49Q22, 60J60
-/

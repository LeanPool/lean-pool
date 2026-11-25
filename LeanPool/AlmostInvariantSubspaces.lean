/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

module

public import LeanPool.AlmostInvariantSubspaces.FinalS2
public import LeanPool.AlmostInvariantSubspaces.SingleOrbit
public import LeanPool.AlmostInvariantSubspaces.VectorSpace
public import LeanPool.AlmostInvariantSubspaces.Question
public import LeanPool.AlmostInvariantSubspaces.OneSided
public import LeanPool.AlmostInvariantSubspaces.AllGroups

/-!
# Almost invariant subspaces and quantitative Kazhdan–Polishchuk bounds

Source: arxiv:2107.08085, url:https://github.com/jackryan225/almost-invariant-subspaces/tree/d199b316dbcd1a78043a7b43902028084a50d38e
Authors: Jack Ryan
Status: verified
Main declarations: `KPFullFinal.kp_family_finite_form_sharp`, `KPFullFinal.kp_family_canonical`,
  `KPFullFinal.kp_family_finite_form_lattice`, `AlmostInvariant.question_negative_complex`
Tags: invariant-subspaces, module-length, modular-lattices
MSC: 15A03, 06C05
-/

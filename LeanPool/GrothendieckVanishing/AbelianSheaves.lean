/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# The abelian category of abelian sheaves on a topological space
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

noncomputable section

instance sheafAbelianAddCommGrp (X : TopCat.{u}) :
    Abelian (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

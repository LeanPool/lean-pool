/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreDefs

/-!
# Ordinary product calculus on space-time

The Carleman calculations use the ordinary normed product structure on
space-time. These explicit structures keep that choice consistent across
the linear estimates.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The ordinary product normed additive group on space-time. -/
abbrev carlemanProductNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The product normed additive group structure on the spatial-time carrier. -/
local instance carlemanCoreProductNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

/-- The ordinary product normed real vector space on space-time. -/
abbrev carlemanProductNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

end CKN

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.AssemblyFinal

/-!
# Coarse-graining support: Support.Book.Ch05.Theorems.Section53.WeakNormsMaximizer

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch05
namespace Section53

/-!
# Deterministic weak-norm bounds for the maximizer

Top-level module for the second manuscript lemma in Section 5.3,
`l.weak.norms.maximizer.homogenization.scale`.  The apex theorem and its
paired gradient/flux constituents are proved in
`Section53/WeakNormsMaximizer/Assembly.lean` inside `namespace
WeakNormsMaximizer` and re-exported here at the `Section53` namespace level
so downstream callers can use the short manuscript-shaped name.
-/

export WeakNormsMaximizer
  (weakNormsMaximizer_homogenizationScale
   weakNormsMaximizerGradient_homogenizationScale
   weakNormsMaximizerFlux_homogenizationScale)

end Section53
end Ch05
end Book
end HCPolySupport

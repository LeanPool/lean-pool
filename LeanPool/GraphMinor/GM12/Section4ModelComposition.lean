/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
import LeanPool.GraphMinor.Minor.Basic

/-!
# Composing the branch sets of minor models

The omitted proof of XII (4.2), page 249, merges branches along the
contractions of the target minor. This file makes that operation explicit
for models of graph minors. Its branch sets are unions of old branch sets,
which is also the inclusion needed to preserve tangle control.
-/

public section

namespace GraphMinor.GM12

open Set

variable {α β α' β' α'' β'' : Type*}

/-- Compose branch sets and joining edges as in the omitted proof of XII (4.2),
page 249. The new branch is the union of the old branches selected by the
first model, joined by its internal edges. -/
theorem minorModel_comp {H : Graph α'' β''} {K : Graph α' β'} {G : Graph α β}
    {ηv : α'' → Set α'} {ηe : β'' → β'} {ηv' : α' → Set α} {ηe' : β' → β}
    (h₁ : IsMinorModel H K ηv ηe) (h₂ : IsMinorModel K G ηv' ηe') :
    IsMinorModel H G (fun v ↦ ⋃ v' ∈ ηv v, ηv' v') (ηe' ∘ ηe) :=
  GraphMinor.isMinorModel_comp h₁ h₂

end GraphMinor.GM12

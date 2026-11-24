/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AnalyticGermDecomposition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties

/-!
# Local parametrization of an irreducible analytic germ: the output interface

Blueprint `lag:parametrization-sets`, `lag:parametrization-regular`,
`lag:parametrization-dense`, and the algebraic step of `lag:thin-subgerm` (Demailly,
*Complex analytic and differential geometry*, II.4.19).

For an irreducible analytic germ `A` at `0 ∈ ℂⁿ`, `LocalParametrization A` records what the
local parametrization theorem provides and what the local statement consumes:

* a linear map `π : ℂⁿ → ℂᵈ` (the Noether normalization projection after a linear change
  of coordinates) and an open neighbourhood `Ω` of `0`;
* a subset `good ⊆ A ∩ Ω` (the part of `A` over the complement of the discriminant locus)
  consisting of regular points of `A ∩ Ω` of dimension `d`, dense in `A ∩ Ω`, on which `π`
  is open (it is locally a graph over `ℂᵈ`);
* for every analytic germ `B` not containing `A`, a holomorphic germ `h` on `ℂᵈ`, not
  identically zero, with `h ∘ π = 0` on `A ∩ B` near `0` (the constant term of a minimal
  integral equation over `𝒪_d` of an element of `I(A ∩ B) \ I(A)`).

The theorem that every irreducible germ carries this data is
`exists_localParametrization` (`GermParametrizationProof`).
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrization

open FirstPass AnalyticGermDecomposition

variable {n : ℕ}

/-- **Local parametrization data** of an irreducible analytic germ at `0 ∈ ℂⁿ`. -/
structure LocalParametrization (A : Set (ComplexModel n)) where
  /-- The dimension of the germ. -/
  dim : ℕ
  /-- The parametrizing projection. -/
  proj : ComplexModel n →L[ℂ] ComplexModel dim
  /-- The neighbourhood of `0` on which the parametrization is described. -/
  nbhd : Set (ComplexModel n)
  isOpen_nbhd : IsOpen nbhd
  zero_mem_nbhd : (0 : ComplexModel n) ∈ nbhd
  /-- The regular part lying over the complement of the discriminant locus. -/
  good : Set (ComplexModel n)
  good_subset : good ⊆ A ∩ nbhd
  regularAtDim_of_mem_good : ∀ y ∈ good,
    RegularAtDim (n := n) (M := ComplexModel n) (A ∩ nbhd) y dim
  isOpen_image_inter_good : ∀ O : Set (ComplexModel n), IsOpen O → IsOpen (proj '' (O ∩ good))
  subset_closure_good : A ∩ nbhd ⊆ closure good
  exists_eqn_of_not_le : ∀ B : Set (ComplexModel n), IsAnalyticGerm B → ¬ A ≤ᶠ[𝓝 0] B →
    ∃ h : ComplexModel dim → ℂ, (∀ᶠ w in 𝓝 0, DifferentiableAt ℂ h w) ∧
      ¬ (∀ᶠ w in 𝓝 0, h w = 0) ∧ ∀ᶠ z in 𝓝 0, z ∈ A → z ∈ B → h (proj z) = 0

end SGPT.Foundations.Analysis.Pending.GermParametrization

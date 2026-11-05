/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Dimensions of images of linear maps

## Main results

* `LinearMap.finrank_map_add_finrank_inf_ker`: rank–nullity for the restriction of a linear map
  to a finite-dimensional subspace `V`: `finrank (V.map φ) + finrank (V ⊓ ker φ) = finrank V`.
* `LinearMap.finrank_span_range_le`: extending the scalars of the span of the image of a
  `K`-linear map `g : V → A` to a field `L` cannot increase its dimension beyond `finrank K V`.
* `LinearMap.finrank_span_range_le_of_ker_le`: the same bound by the rank of any linear map whose
  kernel is contained in the kernel of `g`.
-/

@[expose] public section

namespace LinearMap

variable {K M W : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] [AddCommGroup W]
  [Module K W]

/-- Rank–nullity for the restriction of a linear map to a finite-dimensional subspace. -/
theorem finrank_map_add_finrank_inf_ker (φ : M →ₗ[K] W) (V : Submodule K M)
    [FiniteDimensional K V] :
    Module.finrank K (V.map φ) + Module.finrank K ↥(V ⊓ ker φ) = Module.finrank K V := by
  have h := (φ.domRestrict V).finrank_range_add_finrank_ker
  rwa [range_domRestrict, ker_domRestrict, ← Submodule.finrank_map_subtype_eq V,
    Submodule.map_comap_subtype] at h

end LinearMap

namespace LinearMap

/-- Extending the scalars of the span of a linear image cannot increase its dimension beyond
the dimension of its source. -/
theorem finrank_span_range_le {K L V A : Type*} [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup A] [Module K A] [Module L A] [IsScalarTower K L A]
    (g : V →ₗ[K] A) :
    Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K V := by
  classical
  let b := Module.finBasis K V
  let W := Submodule.span L (Set.range (fun i => g (b i)))
  have hg (v : V) : g v ∈ W := by
    rw [← b.sum_repr v, map_sum]
    apply W.sum_mem
    intro i _
    rw [map_smul, ← algebraMap_smul L (b.repr v i) (g (b i))]
    exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have he : Submodule.span L (Set.range g) = W := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨v, rfl⟩; exact hg v)
    · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨b i, rfl⟩)
  rw [he]
  have h := finrank_range_le_card (R := L) (fun i => g (b i))
  change Module.finrank L W ≤ Fintype.card (Fin (Module.finrank K V)) at h
  simpa only [Fintype.card_fin] using h

/-- A factorization through a K-linear image bounds the dimension after
extending the span to L. -/
theorem finrank_span_range_le_of_ker_le {K L V W A : Type*} [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup A] [Module K A] [Module L A] [IsScalarTower K L A]
    (f : V →ₗ[K] W) (g : V →ₗ[K] A) (h : f.ker ≤ g.ker) :
    Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K f.range := by
  let g' := f.ker.liftQ g h
  have he : Set.range g' = Set.range g := by
    rw [← LinearMap.coe_range, ← LinearMap.coe_range]
    exact congrArg (fun S : Submodule K A => (S : Set A)) (Submodule.range_liftQ _ _ _)
  rw [← he]
  exact (finrank_span_range_le g').trans_eq f.quotKerEquivRange.finrank_eq

end LinearMap

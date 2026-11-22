/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Counting
public import LeanPool.ExtriangulatedRealization.CD.Structure
public import LeanPool.ExtriangulatedRealization.Criterion.Necessity
public import LeanPool.ExtriangulatedRealization.Realization.Subcategory
public import LeanPool.ExtriangulatedRealization.InverseSystems.Aronszajn
public import LeanPool.ExtriangulatedRealization.InverseSystems.Linearization

/-!
# Theorem A (= Theorem 4.5)

Let `D_i = k^(T_i)` be the linearization of the Aronszajn system of Construction 4.3, indexed by
the countable ordinals. Its transition maps are surjective and `lim D = 0` while `D_0 = k`
(Lemma 4.1), so `C(D)` has no triangulated embedding by Theorem B. Countable families of objects
lie in some `C_{[0, m]}`, which has an algebraic realization by Corollary 2.4, since countable
sets of countable ordinals are bounded. The remaining properties come from Proposition 4.4 and
from `dim D_i = |T_i| ≤ ℵ₀`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Opposite Statement Cardinal

universe u

variable (k : Type u) [Field k]

/-- The inverse system `D_i = k^(T_i)` of Construction 4.3. -/
noncomputable abbrev treeSystem : (Omega1.{u})ᵒᵖ ⥤ ModuleCat.{u} k :=
  linearize Aronszajn.system k

lemma treeSystem_hasSurjectiveTransitions : HasSurjectiveTransitions (treeSystem k) :=
  linearize_hasSurjectiveTransitions _ k fun h => Aronszajn.system_map_surjective h

/-- The limit projections for the system in Construction 4.3 fail to be surjective.
The argument of Lemma 4.1 gives a zero limit, while the space at the first index is nonzero. -/
lemma treeSystem_not_projectionsSurjective : ¬ ProjectionsSurjective (treeSystem k) :=
  linearize_not_projectionsSurjective _ k (fun _ hT => Omega1.bddAbove_of_countable hT)
    Aronszajn.system_no_branch _ ⟨0, Aronszajn.zero_mem_tree_bot⟩

/-- The dimension bound in Construction 4.3 follows from `dim D_i = |T_i|`. -/
lemma rank_treeSystem_le (i : Omega1.{u}) : Module.rank k ((treeSystem k).obj (op i)) ≤ ℵ₀ := by
  change Module.rank k (Aronszajn.system.obj (op i) →₀ k) ≤ ℵ₀
  rw [rank_finsupp_self']
  have := Aronszajn.countable_system_obj i
  exact Cardinal.mk_le_aleph0

/-- **Theorem A (= Theorem 4.5).** The witness is `C(D)` for the system `D` of Construction 4.3;
with `theoremB_necessity` it has no triangulated embedding in any universes. -/
theorem theoremA : TheoremA.{u} := by
  intro k _
  let D := treeSystem k
  have hD : HasSurjectiveTransitions D := treeSystem_hasSurjectiveTransitions k
  refine ⟨Omega1.{u}, inferInstance, inferInstance, inferInstance, D, hD,
    treeSystem_not_projectionsSurjective k, cdData_isExtriangulated D hD, essentiallySmall_CD D,
    fun h => treeSystem_not_projectionsSurjective k
      (theoremB_necessity.{u, u, max 1 u} k _ D h), ?_,
    cdData_isHereditary D, isKrullSchmidt_CD D, cd_hasEnoughInjectives D hD,
    mk_indecomposableClasses D Omega1.mk_eq,
    fun X hX f => existsUnique_smul_of_isIndecomposable D hX f,
    fun A C hA hC => rank_ext_le_one_of_isIndecomposable D hA hC,
    rank_hom_le_aleph0 D (rank_treeSystem_le k)⟩
  intro S hS
  obtain ⟨m, hm⟩ := exists_labelsIn_Iic_of_countable D
    (fun _ hT => Omega1.bddAbove_of_countable hT) hS
  obtain ⟨hclosed, hext, -, hreal⟩ := (corollary_2_4 k _ D hD).2.2 (Set.Iic m)
  refine ⟨subcatJ D (Set.Iic m), hclosed, fun X hX => ?_, hext,
    hreal ⟨m, Set.mem_Iic.mpr le_rfl, fun _ hi => hi⟩⟩
  exact hm X hX

end ExtriangulatedRealization

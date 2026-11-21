/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PosetHomotopy.FiniteSpace.Core
public import LeanPool.PosetHomotopy.OrderComplex.Prism
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# The posets `S_p(G)` and `A_p(G)` (roadmap 4.1, 4.3, 4.4)

Brown's poset `S_p(G)` of nontrivial `p`-subgroups (`PSubgroupPoset`) and Quillen's poset
`A_p(G)` of nontrivial elementary abelian `p`-subgroups (`ElemAbelianPoset`), ordered by
inclusion (D. Quillen, « Homotopy properties of the poset of nontrivial p-subgroups of a group »,
Adv. Math. 28 (1978), 101–128, §2). The group acts on both by conjugation, through `ConjAct G`
and the pointwise action on subgroups.

* `contractibleSpace_of_normal` (roadmap 4.3; Quillen 1978, Proposition 2.4): if `G`, finite or
  not, has a nontrivial normal `p`-subgroup `N`, the realization of `S_p(G)` is contractible,
  since `Q ≤ QN ≥ N` makes the poset conical.
* `contractibleSpace_withUpperSet_iff` (roadmap 4.4; R. E. Stong, « Group actions on finite
  spaces », Discrete Math. 49 (1984), 95–100, as stated in E. G. Minian, K. I. Piterman, « The
  homotopy types of the posets of p-subgroups of a finite group », Adv. Math. 328 (2018),
  1217–1233, Proposition 2.1): for a finite group, `S_p(G)` with its upper-set topology is a
  contractible finite space exactly when `G` has a nontrivial normal `p`-subgroup. One direction
  is the fence `id ≤ (Q ↦ QN) ≥ N` of roadmap 1.2; the other is the fixed point of the conjugation
  action given by roadmap 1.5.
-/

@[expose] public section

open Topology Pointwise

namespace LeanPool.PosetHomotopy

universe u

section Posets

variable (G : Type u) [Group G] (p : ℕ)

/-- **Roadmap 4.1.** Brown's poset `S_p(G)` of nontrivial `p`-subgroups of `G`, ordered by
inclusion. -/
abbrev PSubgroupPoset : Type u :=
  {H : Subgroup G // H ≠ ⊥ ∧ IsPGroup p H}

/-- **Roadmap 4.1.** Quillen's poset `A_p(G)` of nontrivial elementary abelian `p`-subgroups of
`G`: nontrivial abelian subgroups of exponent dividing `p`, ordered by inclusion. -/
abbrev ElemAbelianPoset : Type u :=
  {H : Subgroup G // H ≠ ⊥ ∧ (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ ∀ x ∈ H, x ^ p = 1}

/-- **Roadmap 4.1.** The inclusion `A_p(G) ⊆ S_p(G)`: a subgroup of exponent dividing `p` is a
`p`-group. -/
def elemAbelianToPSubgroup : ElemAbelianPoset G p →o PSubgroupPoset G p where
  toFun H := ⟨H.1, H.2.1, fun g => ⟨1, Subtype.ext (by simpa using H.2.2.2 g.1 g.2)⟩⟩
  monotone' _ _ h := h

variable {G p}

theorem smul_ne_bot {H : Subgroup G} (hH : H ≠ ⊥) (g : ConjAct G) : g • H ≠ ⊥ := by
  intro h
  apply hH
  rw [← inv_smul_smul g H, h, Subgroup.smul_bot]

theorem isPGroup_smul {H : Subgroup G} (hH : IsPGroup p H) (g : ConjAct G) :
    IsPGroup p (g • H : Subgroup G) := by
  rw [Subgroup.pointwise_smul_def]
  exact hH.map _

/-- **Roadmap 4.1.** `G` acts on `S_p(G)` by conjugation. -/
instance : MulAction (ConjAct G) (PSubgroupPoset G p) where
  smul g H := ⟨g • H.1, smul_ne_bot H.2.1 g, isPGroup_smul H.2.2 g⟩
  one_smul H := Subtype.ext (one_smul _ H.1)
  mul_smul g h H := Subtype.ext (mul_smul g h H.1)

@[simp]
theorem coe_smul_pSubgroupPoset (g : ConjAct G) (H : PSubgroupPoset G p) :
    ((g • H : PSubgroupPoset G p) : Subgroup G) = g • (H : Subgroup G) := rfl

theorem smul_mono_subgroup {H K : Subgroup G} (h : H ≤ K) (g : ConjAct G) : g • H ≤ g • K := by
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
  exact Subgroup.map_mono h

/-- A subgroup fixed by conjugation is normal. -/
theorem normal_of_forall_smul_eq {H : Subgroup G} (h : ∀ g : ConjAct G, g • H = H) :
    H.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have := Subgroup.smul_mem_pointwise_smul n (ConjAct.toConjAct g) H hn
  rwa [h, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at this

end Posets

section Normal

variable {G : Type u} [Group G] {p : ℕ}

/-- The conical map `Q ↦ QN` of `S_p(G)` for a normal `p`-subgroup `N`. -/
def supNormal (N : Subgroup G) [N.Normal] (hNp : IsPGroup p N) :
    PSubgroupPoset G p →o PSubgroupPoset G p where
  toFun Q := ⟨Q.1 ⊔ N, fun h => Q.2.1 (eq_bot_iff.2 (le_sup_left.trans h.le)),
    Q.2.2.to_sup_of_normal_right hNp⟩
  monotone' _ _ h := sup_le_sup_right h N

/-- **Roadmap 4.3.** If a group `G`, finite or not, has a nontrivial normal `p`-subgroup, then
`S_p(G)` has a contractible realization. -/
theorem contractibleSpace_of_normal (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (hNp : IsPGroup p N) :
    ContractibleSpace
      (AbstractSimplicialComplex.Realization
        (TauCeti.AbstractSimplicialComplex.orderComplex (PSubgroupPoset G p))) :=
  contractibleSpace_of_conical ⟨N, hN, hNp⟩ (supNormal N hNp)
    (fun Q => (le_sup_left : Q.1 ≤ Q.1 ⊔ N)) fun Q => (le_sup_right : N ≤ Q.1 ⊔ N)

end Normal

section Stong

variable {G : Type u} [Group G] {p : ℕ}

instance : T0Space (WithUpperSet (PSubgroupPoset G p)) :=
  t0Space_iff_inseparable _ |>.2 fun a b h => by
    rw [inseparable_iff_specializes_and, Topology.IsUpperSet.specializes_iff_le,
      Topology.IsUpperSet.specializes_iff_le] at h
    exact le_antisymm (α := PSubgroupPoset G p) h.2 h.1

instance [Finite G] : Finite (PSubgroupPoset G p) :=
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  inferInstance

instance [Finite G] : Finite (WithUpperSet (PSubgroupPoset G p)) :=
  inferInstanceAs (Finite (PSubgroupPoset G p))

/-- The conjugation action on `S_p(G)` with its upper-set topology. -/
instance : MulAction (ConjAct G) (WithUpperSet (PSubgroupPoset G p)) where
  smul g H := WithUpperSet.toUpperSet (g • WithUpperSet.ofUpperSet H)
  one_smul H := by
    change WithUpperSet.toUpperSet ((1 : ConjAct G) • WithUpperSet.ofUpperSet H) = H
    rw [one_smul]; rfl
  mul_smul g h H := by
    change WithUpperSet.toUpperSet ((g * h) • WithUpperSet.ofUpperSet H) =
      WithUpperSet.toUpperSet (g • h • WithUpperSet.ofUpperSet H)
    rw [mul_smul]

instance : ContinuousConstSMul (ConjAct G) (WithUpperSet (PSubgroupPoset G p)) :=
  ⟨fun g => continuous_of_specializes fun a b hab => by
    rw [Topology.IsUpperSet.specializes_iff_le] at hab ⊢
    exact smul_mono_subgroup (G := G) hab g⟩

/-- A monotone self-map of `S_p(G)`, read on the upper-set topology. -/
def upperSetMap (f : PSubgroupPoset G p →o PSubgroupPoset G p) :
    C(WithUpperSet (PSubgroupPoset G p), WithUpperSet (PSubgroupPoset G p)) :=
  ⟨fun H => WithUpperSet.toUpperSet (f (WithUpperSet.ofUpperSet H)),
    continuous_of_specializes fun a b hab => by
      rw [Topology.IsUpperSet.specializes_iff_le] at hab ⊢
      exact f.monotone hab⟩

/-- **Roadmap 4.4.** Stong's theorem: for a finite group `G`, `S_p(G)`, as a finite space with its
upper-set topology, is contractible exactly when `G` has a nontrivial normal `p`-subgroup. -/
theorem contractibleSpace_withUpperSet_iff [Finite G] [Fact p.Prime] :
    ContractibleSpace (WithUpperSet (PSubgroupPoset G p)) ↔
      ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ IsPGroup p N := by
  constructor
  · intro
    obtain ⟨H, hH⟩ := exists_fixedPoint_of_contractibleSpace
      (G := ConjAct G) (X := WithUpperSet (PSubgroupPoset G p))
    refine ⟨(WithUpperSet.ofUpperSet H).1, normal_of_forall_smul_eq fun g => ?_,
      (WithUpperSet.ofUpperSet H).2.1, (WithUpperSet.ofUpperSet H).2.2⟩
    exact congrArg (fun K : WithUpperSet (PSubgroupPoset G p) => (WithUpperSet.ofUpperSet K).1)
      (hH g)
  · rintro ⟨N, hN, hN', hNp⟩
    let F := upperSetMap (supNormal N hNp)
    have h₁ : (ContinuousMap.id _).Homotopic F :=
      (homotopic_of_specializes F (ContinuousMap.id _) fun H => by
        rw [Topology.IsUpperSet.specializes_iff_le]
        exact le_sup_left (a := (WithUpperSet.ofUpperSet H).1)).symm
    have h₂ : F.Homotopic (ContinuousMap.const _ (WithUpperSet.toUpperSet ⟨N, hN', hNp⟩)) :=
      homotopic_of_specializes F _ fun H => by
        rw [Topology.IsUpperSet.specializes_iff_le]
        exact le_sup_right (a := (WithUpperSet.ofUpperSet H).1)
    exact (contractible_iff_id_nullhomotopic _).2 ⟨_, h₁.trans h₂⟩

end Stong

end LeanPool.PosetHomotopy

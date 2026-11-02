/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Closure
public import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Chains of closed sets, layers and traces

For a graph on an uncountable vertex type `V`, a chain is a continuous increasing family
`N ξ` of vertex sets indexed by ordinals, starting from `∅`, each successor closed over
its predecessor, each set of size below `#V` while `ξ < (#V).ord`, and covering `V` by
then. It replaces the chain of elementary submodels of the proof, with the first model
empty and with length `(#V).ord` in place of the cofinality of `#V`.

The layer of a vertex `v` is the ordinal `ξ` with `v ∈ N (ξ + 1) \ N ξ`, and its trace
is the set of its neighbours in `N ξ`, which contains every neighbour in an earlier layer.
-/

@[expose] public section

open Cardinal Order

universe u

namespace Erdos111

variable {V : Type u}

/-- A continuous chain of closed sets covering `V`, each of size below `#V` before
`(#V).ord`. -/
structure Chain (G : SimpleGraph V) where
  /-- The sets of the chain. -/
  N : Ordinal.{u} → Set V
  zero : N 0 = ∅
  mono : Monotone N
  succ : ∀ ξ, ClosedOver G (N ξ) (N (ξ + 1))
  limit : ∀ o, IsSuccLimit o → N o = ⋃ ζ < o, N ζ
  card_lt : ∀ ξ < (#V).ord, #(N ξ) < #V
  cover : ∀ v, ∃ ξ < (#V).ord, v ∈ N (ξ + 1)

namespace Chain

/-- A nonempty type is enumerated by the ordinals below `(#V).ord`. -/
theorem exists_enum [Nonempty V] :
    ∃ e : Ordinal.{u} → V, ∀ v, ∃ ξ < (#V).ord, e ξ = v := by
  classical
  obtain ⟨eqv⟩ : Nonempty ((#V).ord.ToType ≃ V) := Cardinal.eq.1 (mk_ord_toType _)
  refine ⟨fun ξ => if h : ξ < (#V).ord then eqv (Ordinal.ToType.mk ⟨ξ, h⟩)
    else Classical.arbitrary V, fun v => ?_⟩
  have h := (Ordinal.ToType.mk.symm (eqv.symm v)).2
  refine ⟨(Ordinal.ToType.mk.symm (eqv.symm v)).1, h, ?_⟩
  rw [Set.mem_Iio] at h
  simp only [h, dite_true]
  exact (congrArg eqv (Ordinal.ToType.mk.apply_symm_apply (eqv.symm v))).trans
    (eqv.apply_symm_apply v)

/-- A closure of `S ∪ {x}` over `S`. -/
noncomputable def closure (G : SimpleGraph V) (S : Set V) (x : V) : Set V :=
  (exists_closedOver G S {x}).choose

/-- The closure contains `S ∪ {x}`. -/
theorem subset_closure (G : SimpleGraph V) (S : Set V) (x : V) :
    S ∪ {x} ⊆ closure G S x :=
  (exists_closedOver G S {x}).choose_spec.1

/-- The closure is closed over `S`. -/
theorem closedOver_closure (G : SimpleGraph V) (S : Set V) (x : V) :
    ClosedOver G S (closure G S x) :=
  (exists_closedOver G S {x}).choose_spec.2.1

/-- The closure is small. -/
theorem mk_closure_le (G : SimpleGraph V) (S : Set V) (x : V) :
    #(closure G S x) ≤ max (#S + 1) ℵ₀ :=
  (exists_closedOver G S {x}).choose_spec.2.2.trans_eq (by rw [mk_singleton])

/-- The chain adding the vertices of an enumeration `e` one at a time. -/
noncomputable def build (G : SimpleGraph V) (e : Ordinal.{u} → V) (o : Ordinal.{u}) : Set V :=
  Ordinal.limitRecOn o ∅ (fun ξ S => closure G S (e ξ)) fun o _ IH =>
    ⋃ ζ, ⋃ h : ζ < o, IH ζ h

/-- The chain starts from `∅`. -/
theorem build_zero (G : SimpleGraph V) (e : Ordinal.{u} → V) : build G e 0 = ∅ := by
  simp [build]

/-- A successor set closes its predecessor with the next vertex. -/
theorem build_add_one (G : SimpleGraph V) (e : Ordinal.{u} → V) (ξ : Ordinal.{u}) :
    build G e (ξ + 1) = closure G (build G e ξ) (e ξ) := by
  simp [build]

/-- A limit set is the union of the earlier sets. -/
theorem build_limit (G : SimpleGraph V) (e : Ordinal.{u} → V) {o : Ordinal.{u}}
    (ho : IsSuccLimit o) : build G e o = ⋃ ζ < o, build G e ζ := by
  rw [build, Ordinal.limitRecOn_limit _ _ _ _ ho]
  rfl

/-- The chain is increasing. -/
theorem build_subset_build (G : SimpleGraph V) (e : Ordinal.{u} → V) (η : Ordinal.{u}) :
    ∀ ξ ≤ η, build G e ξ ⊆ build G e η := by
  induction η using Ordinal.limitRecOn with
  | zero =>
    intro ξ h
    rw [nonpos_iff_eq_zero.1 h]
  | add_one η ih =>
    intro ξ h
    rcases h.lt_or_eq with h | rfl
    · rw [build_add_one]
      exact Set.Subset.trans (ih ξ (Order.lt_add_one_iff.1 h))
        (Set.subset_union_left.trans (subset_closure G _ _))
    · exact Set.Subset.rfl
  | limit o ho ih =>
    intro ξ h
    rcases h.lt_or_eq with h | rfl
    · rw [build_limit G e ho]
      exact Set.subset_iUnion₂ (s := fun ζ _ => build G e ζ) ξ h
    · exact Set.Subset.rfl

/-- The chain is monotone. -/
theorem build_mono (G : SimpleGraph V) (e : Ordinal.{u} → V) : Monotone (build G e) :=
  fun ξ η h => build_subset_build G e η ξ h

/-- The `ξ`-th set has at most `max ξ.card ℵ₀` vertices. -/
theorem mk_build_le (G : SimpleGraph V) (e : Ordinal.{u} → V) (ξ : Ordinal.{u}) :
    #(build G e ξ) ≤ max ξ.card ℵ₀ := by
  induction ξ using Ordinal.limitRecOn with
  | zero => simp [build_zero]
  | add_one ξ ih =>
    rw [build_add_one]
    refine (mk_closure_le G _ _).trans (max_le ?_ (le_max_right _ _))
    refine (add_le_add_left ih 1).trans ?_
    rw [add_one_of_aleph0_le (le_max_right _ _)]
    exact max_le_max (Ordinal.card_le_card (Order.lt_add_one_iff.2 le_rfl).le) le_rfl
  | limit o ho ih =>
    rw [build_limit G e ho]
    exact mk_biUnion_le_of_le (le_max_left _ _) (le_max_right _ _) _ fun j hj =>
      (ih j hj).trans (max_le_max (Ordinal.card_le_card hj.le) le_rfl)

end Chain

/-- Every graph on an uncountable vertex type has a chain. -/
theorem exists_chain (G : SimpleGraph V) (hV : ℵ₀ < #V) : Nonempty (Chain G) := by
  have : Nonempty V := mk_ne_zero_iff.1 (aleph0_pos.trans hV).ne'
  obtain ⟨e, he⟩ := Chain.exists_enum (V := V)
  refine ⟨{
    N := Chain.build G e
    zero := Chain.build_zero G e
    mono := Chain.build_mono G e
    succ := fun ξ => by
      rw [Chain.build_add_one]
      exact Chain.closedOver_closure G _ _
    limit := fun o ho => Chain.build_limit G e ho
    card_lt := fun ξ hξ => (Chain.mk_build_le G e ξ).trans_lt (max_lt (lt_ord.1 hξ) hV)
    cover := fun v => ?_ }⟩
  obtain ⟨ξ, hξ, rfl⟩ := he v
  refine ⟨ξ, hξ, ?_⟩
  rw [Chain.build_add_one]
  exact Chain.subset_closure G _ _ (Or.inr rfl)

namespace Chain

variable {G : SimpleGraph V} (c : Chain G)

/-- The layer of `v`: the ordinal `ξ` with `v ∈ N (ξ + 1) \ N ξ`. -/
noncomputable def layer (v : V) : Ordinal.{u} :=
  sInf {ξ | v ∈ c.N (ξ + 1)}

/-- The trace of `v`: its neighbours in the set preceding its layer. -/
def trace (v : V) : Set V :=
  {u | G.Adj v u ∧ u ∈ c.N (c.layer v)}

/-- A vertex lies in `N ξ` exactly when its layer is below `ξ`. -/
theorem mem_N_iff {v : V} {ξ : Ordinal.{u}} : v ∈ c.N ξ ↔ c.layer v < ξ := by
  constructor
  · intro hv
    induction ξ using Ordinal.limitRecOn with
    | zero => simp [c.zero] at hv
    | add_one ξ ih =>
      exact Order.lt_add_one_iff.2 (csInf_le' (s := {ξ | v ∈ c.N (ξ + 1)}) hv)
    | limit o ho ih =>
      rw [c.limit o ho, Set.mem_iUnion₂] at hv
      obtain ⟨ζ, hζ, hv⟩ := hv
      exact (ih ζ hζ hv).trans hζ
  · intro h
    obtain ⟨ξ', -, hv⟩ := c.cover v
    exact c.mono (Order.add_one_le_of_lt h)
      (csInf_mem (s := {ξ | v ∈ c.N (ξ + 1)}) ⟨ξ', hv⟩)

/-- Every layer is below `(#V).ord`. -/
theorem layer_lt_ord (v : V) : c.layer v < (#V).ord := by
  obtain ⟨ξ, hξ, hv⟩ := c.cover v
  exact (csInf_le' (s := {ξ | v ∈ c.N (ξ + 1)}) hv).trans_lt hξ

/-- Every layer has fewer than `#V` vertices, when `V` is infinite. -/
theorem card_layer_lt (hV : ℵ₀ ≤ #V) (ξ : Ordinal.{u}) :
    #{v // c.layer v = ξ} < #V := by
  by_cases hξ : ξ < (#V).ord
  · refine (mk_subtype_le_of_subset fun v hv => c.mem_N_iff.2 ?_).trans_lt
      (c.card_lt _ ((isSuccLimit_ord hV).add_one_lt hξ))
    rw [hv]
    exact Order.lt_add_one_iff.2 le_rfl
  · have : IsEmpty {v // c.layer v = ξ} := ⟨fun v => hξ (v.2 ▸ c.layer_lt_ord v.1)⟩
    rw [mk_eq_zero]
    exact aleph0_pos.trans_le hV

/-- A neighbour in an earlier layer lies in the trace. -/
theorem mem_trace_of_layer_lt {u v : V} (h : G.Adj v u) (hl : c.layer u < c.layer v) :
    u ∈ c.trace v :=
  ⟨h, c.mem_N_iff.2 hl⟩

end Chain

end Erdos111

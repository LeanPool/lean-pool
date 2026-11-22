/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Criterion.TheoremB

/-!
# The two realization criteria of Proposition 4.6

If the ordinal `I` has a countable cofinal subset, a recursive lift along a cofinal sequence
extends every `u ∈ D_i` to a compatible family. If every `D_i` is finite-dimensional, extending
evaluation at `u` to the direct limit of the dual spaces gives such a family. In both cases
Theorem B gives an algebraic realization.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- The transition map `π_{ba} : D_b → D_a` for `a ≤ b`. -/
abbrev trans {a b : I} (h : a ≤ b) : D.obj (op b) →ₗ[k] D.obj (op a) :=
  (D.map (homOfLE h).op).hom

lemma trans_trans {a b c : I} (hab : a ≤ b) (hbc : b ≤ c) (v : D.obj (op c)) :
    trans D hab (trans D hbc v) = trans D (hab.trans hbc) v := by
  change (D.map (homOfLE hbc).op ≫ D.map (homOfLE hab).op).hom v = _
  rw [← D.map_comp]
  rfl

lemma trans_refl {a : I} (v : D.obj (op a)) : trans D (le_refl a) v = v := by
  change (D.map (𝟙 (op a))).hom v = v
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The lifting argument of Proposition 4.6 (1) extends to arbitrary linearly ordered
indices with surjective transition maps. The paper assumes a nonempty ordinal. -/
lemma projectionsSurjective_of_countable_cofinal (hD : HasSurjectiveTransitions D) (S : Set I)
    (hS : S.Countable) (hcof : ∀ i, ∃ j ∈ S, i ≤ j) : ProjectionsSurjective D := by
  intro i u
  have hSne : S.Nonempty := let ⟨j, hj, _⟩ := hcof i; ⟨j, hj⟩
  obtain ⟨e, he⟩ := hS.exists_eq_range hSne
  let s : ℕ → I := fun n =>
    (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr n.succ_pos⟩ (fun m => i ⊔ e m)
  have hs_mono : Monotone s := fun n n' h =>
    Finset.sup'_mono _ (Finset.range_subset_range.mpr (Nat.succ_le_succ h)) _
  have hs_succ : ∀ n, s n ≤ s (n + 1) := fun n => hs_mono n.le_succ
  have hs_e : ∀ n, e n ≤ s n := fun n =>
    le_sup_right.trans (Finset.le_sup' (fun m => i ⊔ e m) (Finset.mem_range.mpr n.lt_succ_self))
  have hs_i : i ≤ s 0 :=
    le_sup_left.trans (Finset.le_sup' (fun m => i ⊔ e m) (Finset.mem_range.mpr Nat.zero_lt_one))
  have hcof' : ∀ j, ∃ n, j ≤ s n := by
    intro j
    obtain ⟨j', hj', hjj'⟩ := hcof j
    rw [he] at hj'
    obtain ⟨n, rfl⟩ := hj'
    exact ⟨n, hjj'.trans (hs_e n)⟩
  have hlift : ∀ (a b : I) (h : a ≤ b) (v : D.obj (op a)), ∃ w, trans D h w = v :=
    fun _ _ h v => hD h v
  choose lift hlift using hlift
  let y : ∀ n, D.obj (op (s n)) := fun n =>
    @Nat.rec (fun n => D.obj (op (s n))) (lift _ _ hs_i u)
      (fun n yn => lift _ _ (hs_succ n) yn) n
  have hy_succ : ∀ n, trans D (hs_succ n) (y (n + 1)) = y n := fun n => hlift _ _ _ _
  have hy : ∀ n n' (h : n ≤ n'), trans D (hs_mono h) (y n') = y n := by
    intro n n' h
    induction h with
    | refl => exact trans_refl D _
    | step h ih =>
      rw [← ih, ← hy_succ, trans_trans]
  classical
  let N : I → ℕ := fun j => Nat.find (hcof' j)
  have hN : ∀ j, j ≤ s (N j) := fun j => Nat.find_spec (hcof' j)
  let z : ∀ j, D.obj (op j) := fun j => trans D (hN j) (y (N j))
  have hz : ∀ j n (h : j ≤ s n), z j = trans D h (y n) := by
    intro j n h
    have hn : N j ≤ n := Nat.find_min' (hcof' j) h
    change trans D (hN j) (y (N j)) = _
    rw [← hy _ _ hn, trans_trans]
  refine ⟨z, fun {j j'} hjj' => ?_, ?_⟩
  · rw [hz j' (N j') (hN j'), trans_trans, hz j (N j') (hjj'.trans (hN j'))]
  · rw [hz i 0 hs_i]
    exact hlift _ _ _ _

/-- The dual spaces `D_j^*`. -/
abbrev dualObj (j : I) : Type u := Module.Dual k (D.obj (op j))

/-- The dual transition maps `π_{ba}^* : D_a^* → D_b^*`. -/
noncomputable def dualTrans (a b : I) (h : a ≤ b) : dualObj D a →ₗ[k] dualObj D b :=
  (trans D h).dualMap

instance : DirectedSystem (dualObj D) fun a b h => dualTrans D a b h where
  map_self j α := by
    ext v
    change α (trans D (le_refl j) v) = α v
    rw [trans_refl]
  map_map {a b c} hab hbc α := by
    ext v
    change α (trans D hab (trans D hbc v)) = α (trans D (hab.trans hbc) v)
    rw [trans_trans]

omit [LinearOrder I] in
lemma directLimit_exists_extend [Preorder I] [IsDirectedOrder I] [DecidableEq I]
    (G : I → Type u) [∀ i, AddCommGroup (G i)]
    [∀ i, Module k (G i)] (f : ∀ a b : I, a ≤ b → G a →ₗ[k] G b)
    [DirectedSystem G fun a b h => f a b h] (hf : ∀ a b (h : a ≤ b), Function.Injective (f a b h))
    (i : I) (ψ : Module.Dual k (G i)) :
    ∃ φ : Module.Dual k (Module.DirectLimit G f), φ.comp (Module.DirectLimit.of k I G f i) = ψ := by
  have hinj : Function.Injective (Module.DirectLimit.of k I G f i) := by
    intro α β h
    obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_eq_of_of_eq h
    exact hf _ _ hij hj
  obtain ⟨g, hg⟩ := (Module.DirectLimit.of k I G f i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  exact ⟨ψ.comp g, by rw [LinearMap.comp_assoc, hg, LinearMap.comp_id]⟩

/-- The duality argument of Proposition 4.6 (2) extends to arbitrary linearly ordered
indices with surjective transition maps. The paper assumes a nonempty ordinal. -/
lemma projectionsSurjective_of_finiteDimensional (hD : HasSurjectiveTransitions D)
    (hfin : ∀ i, FiniteDimensional k (D.obj (op i))) : ProjectionsSurjective D := by
  intro i u
  have hf : ∀ a b (h : a ≤ b), Function.Injective (dualTrans D a b h) := by
    intro a b h α β hαβ
    ext v
    obtain ⟨w, rfl⟩ := hD h v
    exact LinearMap.congr_fun hαβ w
  obtain ⟨φ, hφ⟩ := directLimit_exists_extend (dualObj D) (dualTrans D) hf i
    (Module.Dual.eval k (D.obj (op i)) u)
  let z : ∀ j, D.obj (op j) := fun j =>
    (Module.evalEquiv k (D.obj (op j))).symm
      (φ.comp (Module.DirectLimit.of k I (dualObj D) (dualTrans D) j))
  have hz : ∀ j (α : dualObj D j),
      α (z j) = φ (Module.DirectLimit.of k I (dualObj D) (dualTrans D) j α) := fun j α =>
    Module.apply_evalEquiv_symm_apply k _ α _
  have hsep : ∀ j (v w : D.obj (op j)), (∀ α : dualObj D j, α v = α w) → v = w :=
    fun j v w h => (Module.evalEquiv k (D.obj (op j))).injective (by ext α; exact h α)
  refine ⟨z, fun {j j'} hjj' => ?_, ?_⟩
  · apply hsep
    intro α
    change (dualTrans D j j' hjj' α) (z j') = α (z j)
    rw [hz, hz]
    exact congrArg φ (Module.DirectLimit.of_f (hij := hjj'))
  · apply hsep
    intro α
    rw [hz]
    exact LinearMap.congr_fun hφ α

variable [WellFoundedLT I] [Nonempty I]

/-- The two sufficient conditions of Proposition 4.6 for algebraic realizability. -/
theorem proposition_4_6 : Proposition46.{u} := by
  intro k _ I _ _ _ D hD
  exact ⟨fun ⟨S, hS, hcof⟩ => hasAlgebraicRealization_of_projectionsSurjective D
      (projectionsSurjective_of_countable_cofinal D hD S hS hcof),
    fun hfin => hasAlgebraicRealization_of_projectionsSurjective D
      (projectionsSurjective_of_finiteDimensional D hD hfin)⟩

end ExtriangulatedRealization

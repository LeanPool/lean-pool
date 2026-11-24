/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Higman
public import LeanPool.GraphMinor.GM04.Patchwork.Stars
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Well-quasi-ordering star-decompositions of patchworks (Graph Minors IV, (8.4))

This file formalizes Graph Minors IV, (8.4) (pages 249–251):

* `higman83_universal`, `higman83_on_infinite_set`, and `higman83_partitioned`: helpers applying
  `Higman83Statement` on infinite subsets of `ℕ` and across finitely many tag classes.
* `lemma_8_4_claim_1`–`lemma_8_4_claim_8`: claims (1)–(8) of the proof of (8.4).
* `theorem_8_4`: Graph Minors IV, (8.4), showing that if `(Sᵢ, σᵢ)` is a star-decomposition of a
  removable `Ω`-patchwork `Pᵢ` with `|V(σᵢ(o(Sᵢ)))| ≤ n` and the tips `{Pᵢ | σᵢ(s)}` are
  well-quasi-ordered by simulation, then `Pᵢ` is simulated in `P_{i'}` for some `i < i'`.

Instead of mutating the vertex type of each `Pᵢ` in claim (3) ("By replacing each $P_i$ by an ...
$\Omega$-patchwork, we may therefore assume, to simplify notation, that for some set $V_0$ and march
$\pi_0$ in $V_0$, (3) *$V(\sigma_i(o(S_i))) = V_0$ and $\pi(G_i) = \pi_0$ for all $i \in I_2$.*"),
we fix a coordinate bijection `γᵢ : Fin m → V(σᵢ(o(Sᵢ)))` with inverse
`γ_invᵢ` for each `i ∈ I₂`, pull back the root marches to `Fin m` to pass to an infinite subset
where the pulled-back root march is constant (`π₀`), and use the composite bijection
`v ↦ γ_{i'}(γ_invᵢ(v))` between `V(σᵢ(o(Sᵢ)))` and `V(σ_{i'}(o(S_{i'})))`.
-/

public section

namespace GraphMinor.GM04

open SimpleGraph _root_.GraphMinor.Hypergraph

universe u v w u₁ u₂

variable {Ω : Type w} [Preorder Ω] {α β ι : Type*}

/-! ### Universe-polymorphic and partitioned Higman (8.3) helpers -/

open Classical in
/-- A wrapper equipping `Σ i : ℕ, Fin (X i).card` with the pullback preorder of `ℓ`. -/
private structure HigmanIdx {κ : Type*} {Ω' : Type*} (X : ℕ → Finset κ) (_ℓ : ℕ → κ → Ω') where
  i : ℕ
  j : Fin (X i).card

open Classical in
private instance {κ : Type*} {Ω' : Type*} [Preorder Ω'] (X : ℕ → Finset κ) (ℓ : ℕ → κ → Ω') :
    Preorder (ULift.{u₂} (HigmanIdx X ℓ)) where
  le a b := ℓ a.down.i ((X a.down.i).equivFin.symm a.down.j).1 ≤
    ℓ b.down.i ((X b.down.i).equivFin.symm b.down.j).1
  le_refl _ := le_rfl
  le_trans _ _ _ hab hbc := le_trans hab hbc

open Classical in
private theorem higmanIdx_wqo {κ : Type*} {Ω' : Type*} [Preorder Ω']
    (hΩ' : WellQuasiOrderedLE Ω') (X : ℕ → Finset κ) (ℓ : ℕ → κ → Ω') :
    WellQuasiOrderedLE (ULift.{u₂} (HigmanIdx X ℓ)) := by
  refine ⟨fun f ↦ ?_⟩
  obtain ⟨m, n, hlt, hle⟩ :=
    hΩ'.wqo fun k ↦ ℓ (f k).down.i ((X (f k).down.i).equivFin.symm (f k).down.j).1
  exact ⟨m, n, hlt, hle⟩

open Classical in
/-- `Higman83Statement` at any universe pair `{u₁, u₂}` implies `Higman83Statement` for any type
`κ` and any well-quasi-ordered type `Ω'`. -/
theorem higman83_universal (hH : Higman83Statement.{u₁, u₂})
    {κ : Type*} {Ω' : Type*} [Preorder Ω'] (hΩ' : WellQuasiOrderedLE Ω')
    (X : ℕ → Finset κ) (ℓ : ℕ → κ → Ω') :
    ∃ I : Set ℕ, I.Infinite ∧ ∀ i ∈ I, ∀ i' ∈ I, i < i' →
      ∃ g : κ → κ, Set.InjOn g (X i) ∧ Set.MapsTo g (X i) (X i') ∧
        ∀ x ∈ X i, ℓ i x ≤ ℓ i' (g x) := by
  have hwqo : WellQuasiOrderedLE (ULift.{u₂} (HigmanIdx X ℓ)) := higmanIdx_wqo hΩ' X ℓ
  let toIdx (i : ℕ) (x : {x // x ∈ X i}) : ULift.{u₁} (HigmanIdx X ℓ) :=
    ULift.up ⟨i, (X i).equivFin x⟩
  let X₀ (i : ℕ) : Finset (ULift.{u₁} (HigmanIdx X ℓ)) :=
    (Finset.univ : Finset (Fin (X i).card)).image fun j ↦ ULift.up ⟨i, j⟩
  let ℓ₀ : ℕ → ULift.{u₁} (HigmanIdx X ℓ) → ULift.{u₂} (HigmanIdx X ℓ) :=
    fun _ p ↦ ULift.up p.down
  obtain ⟨I, hI_inf, hI⟩ := hH hwqo X₀ ℓ₀
  refine ⟨I, hI_inf, fun i hi i' hi' hlt ↦ ?_⟩
  obtain ⟨g₀, hg₀_inj, hg₀_maps, hg₀_le⟩ := hI i hi i' hi' hlt
  have hmem_X₀ : ∀ x : {x // x ∈ X i}, toIdx i x ∈ X₀ i := by
    intro x
    exact Finset.mem_image.mpr ⟨(X i).equivFin x, Finset.mem_univ _, rfl⟩
  have hg₀_mem : ∀ x : {x // x ∈ X i},
      ∃ j' : Fin (X i').card, g₀ (toIdx i x) = ULift.up ⟨i', j'⟩ := by
    intro x
    have hm := hg₀_maps (hmem_X₀ x)
    obtain ⟨j', _, hEq⟩ := Finset.mem_image.mp hm
    exact ⟨j', hEq.symm⟩
  let g (x : κ) : κ :=
    if hx : x ∈ (X i : Set κ) then
      ((X i').equivFin.symm (hg₀_mem ⟨x, hx⟩).choose).1
    else x
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ hEq
    dsimp only [g] at hEq
    rw [dite_eq_left_of_eq_true (eq_true hx₁), dite_eq_left_of_eq_true (eq_true hx₂)] at hEq
    have hsub_eq : (X i').equivFin.symm (hg₀_mem ⟨x₁, hx₁⟩).choose =
        (X i').equivFin.symm (hg₀_mem ⟨x₂, hx₂⟩).choose := Subtype.ext hEq
    have hj'_eq : (hg₀_mem ⟨x₁, hx₁⟩).choose = (hg₀_mem ⟨x₂, hx₂⟩).choose :=
      (X i').equivFin.symm.injective hsub_eq
    have hg₀_eq : g₀ (toIdx i ⟨x₁, hx₁⟩) = g₀ (toIdx i ⟨x₂, hx₂⟩) := by
      rw [(hg₀_mem ⟨x₁, hx₁⟩).choose_spec, (hg₀_mem ⟨x₂, hx₂⟩).choose_spec, hj'_eq]
    have htoIdx_eq := hg₀_inj (hmem_X₀ ⟨x₁, hx₁⟩) (hmem_X₀ ⟨x₂, hx₂⟩) hg₀_eq
    have hj_eq : (X i).equivFin ⟨x₁, hx₁⟩ = (X i).equivFin ⟨x₂, hx₂⟩ := by
      have hdown := congrArg ULift.down htoIdx_eq
      injection hdown with h_i h_j
    exact congrArg Subtype.val ((X i).equivFin.injective hj_eq)
  · intro x hx
    dsimp only [g]
    rw [dite_eq_left_of_eq_true (eq_true hx)]
    exact ((X i').equivFin.symm (hg₀_mem ⟨x, hx⟩).choose).2
  · intro x hx
    have hx' : x ∈ (X i : Set κ) := hx
    dsimp only [g]
    rw [dite_eq_left_of_eq_true (eq_true hx')]
    have hle := hg₀_le (toIdx i ⟨x, hx⟩) (hmem_X₀ ⟨x, hx⟩)
    have hspec := (hg₀_mem ⟨x, hx⟩).choose_spec
    change ℓ (toIdx i ⟨x, hx⟩).down.i
        ((X (toIdx i ⟨x, hx⟩).down.i).equivFin.symm (toIdx i ⟨x, hx⟩).down.j).1 ≤
      ℓ (g₀ (toIdx i ⟨x, hx⟩)).down.i
        ((X (g₀ (toIdx i ⟨x, hx⟩)).down.i).equivFin.symm (g₀ (toIdx i ⟨x, hx⟩)).down.j).1 at hle
    rw [hspec] at hle
    simpa [toIdx] using hle

open Classical in
/-- Applying `Higman83Statement` within a given infinite subset `I ⊆ ℕ`. -/
theorem higman83_on_infinite_set (hH : Higman83Statement.{u₁, u₂})
    {κ : Type*} {Ω' : Type*} [Preorder Ω'] (hΩ' : WellQuasiOrderedLE Ω')
    {I : Set ℕ} (hI : I.Infinite) (X : ℕ → Finset κ) (ℓ : ℕ → κ → Ω') :
    ∃ I' ⊆ I, I'.Infinite ∧ ∀ i ∈ I', ∀ i' ∈ I', i < i' →
      ∃ g : κ → κ, Set.InjOn g (X i) ∧ Set.MapsTo g (X i) (X i') ∧
        ∀ x ∈ X i, ℓ i x ≤ ℓ i' (g x) := by
  let φ : ℕ → ℕ := Nat.nth (· ∈ I)
  have hφ_mono : StrictMono φ := Nat.nth_strictMono hI
  have hφ_mem : ∀ k, φ k ∈ I := Nat.nth_mem_of_infinite hI
  obtain ⟨J, hJ_inf, hJ⟩ := higman83_universal hH hΩ' (fun k ↦ X (φ k)) (fun k ↦ ℓ (φ k))
  refine ⟨φ '' J, ?_, hJ_inf.image hφ_mono.injective.injOn, ?_⟩
  · rintro _ ⟨k, _, rfl⟩
    exact hφ_mem k
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩ hlt
    exact hJ k hk k' hk' (hφ_mono.lt_iff_lt.mp hlt)

open Classical in
/-- Pigeonhole principle for an infinite set `I ⊆ ℕ` mapped into a finite set `s : Set τ`. -/
theorem exists_infinite_fiber {τ : Type*} {I : Set ℕ} (hI : I.Infinite)
    {s : Set τ} (hs : s.Finite) {f : ℕ → τ} (hf : ∀ i ∈ I, f i ∈ s) :
    ∃ c ∈ s, {i ∈ I | f i = c}.Infinite := by
  by_contra! hnot
  have hEq : I = ⋃ c ∈ s, {i ∈ I | f i = c} := by
    ext i
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun hi ↦ ⟨f i, hf i hi, hi, rfl⟩, fun ⟨_, _, hi, _⟩ ↦ hi⟩
  have hfin : I.Finite := by
    rw [hEq]
    exact hs.biUnion fun c hc ↦ hnot c hc
  exact hI hfin

open Classical in
/-- Iterating `higman83_on_infinite_set` over a finite set `A : Finset τ` of tags. -/
theorem higman83_partitioned_finset (hH : Higman83Statement.{u₁, u₂})
    {κ τ : Type*} {Ω' : Type*} [Preorder Ω'] (hΩ' : WellQuasiOrderedLE Ω')
    {I₀ : Set ℕ} (hI₀ : I₀.Infinite) (E : ℕ → Finset κ) (tag : ℕ → κ → τ) (ℓ : ℕ → κ → Ω')
    (A : Finset τ) :
    ∃ I ⊆ I₀, I.Infinite ∧ ∀ t ∈ A, ∀ i ∈ I, ∀ i' ∈ I, i < i' →
      ∃ g : κ → κ,
        Set.InjOn g {x ∈ (E i : Set κ) | tag i x = t} ∧
        Set.MapsTo g {x ∈ (E i : Set κ) | tag i x = t} {x ∈ (E i' : Set κ) | tag i' x = t} ∧
        ∀ x ∈ {x ∈ (E i : Set κ) | tag i x = t}, ℓ i x ≤ ℓ i' (g x) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨I₀, subset_rfl, hI₀, fun _ h ↦ False.elim (Finset.notMem_empty _ h)⟩
  | @insert t₀ A _ ih =>
    obtain ⟨I₁, hI₁_sub, hI₁_inf, hI₁⟩ := ih
    obtain ⟨I₂, hI₂_sub, hI₂_inf, hI₂⟩ :=
      higman83_on_infinite_set hH hΩ' hI₁_inf (fun i ↦ (E i).filter fun x ↦ tag i x = t₀) ℓ
    refine ⟨I₂, hI₂_sub.trans hI₁_sub, hI₂_inf, fun t ht i hi i' hi' hlt ↦ ?_⟩
    rcases Finset.mem_insert.mp ht with rfl | htA
    · obtain ⟨g, hg_inj, hg_maps, hg_le⟩ := hI₂ i hi i' hi' hlt
      simp only [Finset.coe_filter] at hg_inj hg_maps
      refine ⟨g, hg_inj, hg_maps, fun x hx ↦ hg_le x (Finset.mem_filter.mpr hx)⟩
    · exact hI₁ t htA i (hI₂_sub hi) i' (hI₂_sub hi') hlt

open Classical in
/-- Piecing together fiber injections over all `t : τ`. -/
theorem piece_fiber_injections {κ τ : Type*} {Ω' : Type*} [Preorder Ω']
    {E₁ E₂ : Set κ} {tag₁ tag₂ : κ → τ} {ℓ₁ ℓ₂ : κ → Ω'}
    (hfib : ∀ t : τ, ∃ g : κ → κ,
      Set.InjOn g {x ∈ E₁ | tag₁ x = t} ∧
      Set.MapsTo g {x ∈ E₁ | tag₁ x = t} {x ∈ E₂ | tag₂ x = t} ∧
      ∀ x ∈ {x ∈ E₁ | tag₁ x = t}, ℓ₁ x ≤ ℓ₂ (g x)) :
    ∃ g : κ → κ, Set.InjOn g E₁ ∧ Set.MapsTo g E₁ E₂ ∧
      (∀ x ∈ E₁, tag₂ (g x) = tag₁ x) ∧ (∀ x ∈ E₁, ℓ₁ x ≤ ℓ₂ (g x)) := by
  let g (x : κ) : κ := (hfib (tag₁ x)).choose x
  have hmem_fib : ∀ x ∈ E₁, x ∈ {y ∈ E₁ | tag₁ y = tag₁ x} := fun x hx ↦ ⟨hx, rfl⟩
  have hg_mem : ∀ x ∈ E₁, g x ∈ E₂ ∧ tag₂ (g x) = tag₁ x :=
    fun x hx ↦ (hfib (tag₁ x)).choose_spec.2.1 (hmem_fib x hx)
  refine ⟨g, ?_, fun x hx ↦ (hg_mem x hx).1, fun x hx ↦ (hg_mem x hx).2, fun x hx ↦ ?_⟩
  · intro x₁ hx₁ x₂ hx₂ hEq
    have htag_eq : tag₁ x₁ = tag₁ x₂ := by
      rw [← (hg_mem x₁ hx₁).2, ← (hg_mem x₂ hx₂).2, hEq]
    have hx₂_fib : x₂ ∈ {y ∈ E₁ | tag₁ y = tag₁ x₁} := ⟨hx₂, htag_eq.symm⟩
    have hEq' : (hfib (tag₁ x₁)).choose x₁ = (hfib (tag₁ x₁)).choose x₂ := by
      dsimp only [g] at hEq
      rwa [← htag_eq] at hEq
    exact (hfib (tag₁ x₁)).choose_spec.1 (hmem_fib x₁ hx₁) hx₂_fib hEq'
  · exact (hfib (tag₁ x)).choose_spec.2.2 x (hmem_fib x hx)

/-! ### Finite types of marches and subgraphs on `Fin m`, and coordinate pullbacks -/

open Classical in
/-- A march (nodup list) in `Fin m`. -/
abbrev MarchIn (m : ℕ) := {ρ : List (Fin m) // ρ.Nodup}

open Classical in
instance (m : ℕ) : Finite ((⊤ : SimpleGraph (Fin m)).Subgraph) :=
  Finite.of_injective (fun H ↦ (H.verts, H.Adj)) fun _ _ h ↦
    Subgraph.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

open Classical in
instance (m : ℕ) : Finite (MarchIn m) := by
  refine Finite.of_injective (fun (ρ : MarchIn m) (i : Fin m) ↦ ρ.1[i.1]?) ?_
  intro ρ₁ ρ₂ h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < m
  · exact congrFun h ⟨i, hi⟩
  · have hlen : ∀ ρ : MarchIn m, ρ.1.length ≤ m := by
      intro ρ
      rw [← List.toFinset_card_of_nodup ρ.2]
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)
    have h₁ : ρ₁.1[i]? = none := List.getElem?_eq_none ((hlen ρ₁).trans (Nat.le_of_not_lt hi))
    have h₂ : ρ₂.1[i]? = none := List.getElem?_eq_none ((hlen ρ₂).trans (Nat.le_of_not_lt hi))
    rw [h₁, h₂]

open Classical in
/-- The inclusion `Fin m → α` from an equivalence `c : Fin m ≃ V`. -/
def toVal {V : Set α} {m : ℕ} (c : Fin m ≃ V) (x : Fin m) : α := (c x).1

open Classical in
theorem toVal_mem {V : Set α} {m : ℕ} (c : Fin m ≃ V) (x : Fin m) : toVal c x ∈ V := (c x).2

open Classical in
theorem toVal_injective {V : Set α} {m : ℕ} (c : Fin m ≃ V) : Function.Injective (toVal c) :=
  fun _ _ h ↦ c.injective (Subtype.ext h)

open Classical in
/-- The bijection `V → V'` induced by two coordinate equivalences `c : Fin m ≃ V` and
`c' : Fin m ≃ V'`, extended by the identity outside `V`. -/
noncomputable def coordMap {V V' : Set α} {m : ℕ} (c : Fin m ≃ V) (c' : Fin m ≃ V') (v : α) : α :=
  if hv : v ∈ V then (c' (c.symm ⟨v, hv⟩)).1 else v

open Classical in
@[simp]
theorem coordMap_toVal {V V' : Set α} {m : ℕ} (c : Fin m ≃ V) (c' : Fin m ≃ V') (x : Fin m) :
    coordMap c c' (toVal c x) = toVal c' x := by
  have hx : (c x).1 ∈ V := (c x).2
  change (if hv : (c x).1 ∈ V then (c' (c.symm ⟨(c x).1, hv⟩)).1 else (c x).1) = (c' x).1
  rw [dite_eq_left_of_eq_true (eq_true hx)]
  simp

open Classical in
theorem coordMap_bijOn {V V' : Set α} {m : ℕ} (c : Fin m ≃ V) (c' : Fin m ≃ V') :
    Set.BijOn (coordMap c c') V V' := by
  refine ⟨fun v hv ↦ ?_, fun v₁ hv₁ v₂ hv₂ hEq ↦ ?_, fun v' hv' ↦ ?_⟩
  · dsimp only [coordMap]
    rw [dite_eq_left_of_eq_true (eq_true hv)]
    exact (c' (c.symm ⟨v, hv⟩)).2
  · dsimp only [coordMap] at hEq
    rw [dite_eq_left_of_eq_true (eq_true hv₁), dite_eq_left_of_eq_true (eq_true hv₂)] at hEq
    have hEq' : c.symm ⟨v₁, hv₁⟩ = c.symm ⟨v₂, hv₂⟩ := c'.injective (Subtype.ext hEq)
    exact congrArg Subtype.val (c.symm.injective hEq')
  · let x := c'.symm ⟨v', hv'⟩
    refine ⟨toVal c x, toVal_mem c x, ?_⟩
    rw [coordMap_toVal]
    exact congrArg Subtype.val (c'.apply_symm_apply ⟨v', hv'⟩)

open Classical in
theorem toVal_image_preimage {V : Set α} {m : ℕ} (c : Fin m ≃ V) {S : Set α} (hS : S ⊆ V) :
    toVal c '' (toVal c ⁻¹' S) = S := by
  refine Set.Subset.antisymm (Set.image_preimage_subset _ _) fun v hv ↦ ?_
  let x := c.symm ⟨v, hS hv⟩
  have hx : toVal c x = v := congrArg Subtype.val (c.apply_symm_apply ⟨v, hS hv⟩)
  exact ⟨x, show toVal c x ∈ S from hx.symm ▸ hv, hx⟩

open Classical in
theorem image_coordMap_eq_of_preimage_eq {V V' : Set α} {m : ℕ} (c : Fin m ≃ V) (c' : Fin m ≃ V')
    {S S' : Set α} (hS : S ⊆ V) (hS' : S' ⊆ V') (hEq : toVal c ⁻¹' S = toVal c' ⁻¹' S') :
    coordMap c c' '' S = S' := by
  rw [← toVal_image_preimage c hS, ← Set.image_comp]
  have hcomp : coordMap c c' ∘ toVal c = toVal c' := funext (coordMap_toVal c c')
  rw [hcomp, hEq, toVal_image_preimage c' hS']

open Classical in
/-- Pulling back a list `π : List α` with vertices in `V` along `c : Fin m ≃ V`. -/
noncomputable def pullList {V : Set α} {m : ℕ} (c : Fin m ≃ V) (π : List α) : List (Fin m) :=
  π.filterMap fun v ↦ if hv : v ∈ V then some (c.symm ⟨v, hv⟩) else none

open Classical in
theorem map_toVal_pullList {V : Set α} {m : ℕ} (c : Fin m ≃ V) {π : List α}
    (hπ : ∀ v ∈ π, v ∈ V) : (pullList c π).map (toVal c) = π := by
  induction π with
  | nil => rfl
  | cons v l ih =>
    have hv : v ∈ V := hπ v List.mem_cons_self
    have hl : ∀ w ∈ l, w ∈ V := fun w hw ↦ hπ w (List.mem_cons_of_mem v hw)
    dsimp only [pullList, List.filterMap_cons]
    rw [dite_eq_left_of_eq_true (eq_true hv)]
    simp only [List.map_cons]
    congr 1
    · exact congrArg Subtype.val (c.apply_symm_apply ⟨v, hv⟩)
    · exact ih hl

open Classical in
theorem pullList_nodup {V : Set α} {m : ℕ} (c : Fin m ≃ V) {π : List α}
    (hnd : π.Nodup) (hπ : ∀ v ∈ π, v ∈ V) : (pullList c π).Nodup := by
  have hmap : ((pullList c π).map (toVal c)).Nodup := by
    rw [map_toVal_pullList c hπ]
    exact hnd
  exact hmap.of_map (toVal c)

open Classical in
theorem map_coordMap_eq_of_pullList_eq {V V' : Set α} {m : ℕ} (c : Fin m ≃ V) (c' : Fin m ≃ V')
    {π π' : List α} (hπ : ∀ v ∈ π, v ∈ V) (hπ' : ∀ v' ∈ π', v' ∈ V')
    (hEq : pullList c π = pullList c' π') :
    π.map (coordMap c c') = π' := by
  conv_lhs => rw [← map_toVal_pullList c hπ]
  rw [List.map_map]
  have hcomp : coordMap c c' ∘ toVal c = toVal c' := funext (coordMap_toVal c c')
  rw [hcomp, hEq, map_toVal_pullList c' hπ']

/-! ### Graph Minors IV, (8.4), claims (1)–(3) -/

open Classical in
/-- Graph Minors IV, (8.4), claim (1) (page 250):
"Since there are only $n + 1$ possibilities for each $|V(\sigma_i(o(S_i)))|$ we may choose an
infinite subset $I_1 \subseteq \{1, 2, \dots\}$ and $m \ge 0$ such that
(1) For all $i \in I_1$, $|V(\sigma_i(o(S_i)))| = m$." -/
theorem lemma_8_4_claim_1 {n : ℕ} {S : ℕ → RootedTree ι} {σ : ℕ → ι → RootedHypergraph α β}
    (hcard : ∀ i, (σ i (S i).root).vertexSet.ncard ≤ n) :
    ∃ (I₁ : Set ℕ) (m : ℕ), I₁.Infinite ∧ m ≤ n ∧
      ∀ i ∈ I₁, (σ i (S i).root).vertexSet.ncard = m := by
  obtain ⟨m, hm, hI₁⟩ := exists_infinite_fiber Set.infinite_univ (Set.finite_Iic n)
    (f := fun i ↦ (σ i (S i).root).vertexSet.ncard) (fun i _ ↦ hcard i)
  exact ⟨{i ∈ Set.univ | (σ i (S i).root).vertexSet.ncard = m}, m, hI₁, hm, fun _ hi ↦ hi.2⟩

omit [Preorder Ω] in
open Classical in
/-- Graph Minors IV, (8.4), claim (2) (page 250):
"Similarly, we may choose an infinite $I_2 \subseteq I_1$ and $k \ge 0$ such that
(2) For all $i \in I_2$, $|\bar{\pi}(G_i)| = k$." -/
theorem lemma_8_4_claim_2 {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {I₁ : Set ℕ} (hI₁ : I₁.Infinite)
    (hm : ∀ i ∈ I₁, (σ i (S i).root).vertexSet.ncard = m) :
    ∃ (I₂ : Set ℕ) (k : ℕ), I₂ ⊆ I₁ ∧ I₂.Infinite ∧ k ≤ m ∧
      ∀ i ∈ I₂, (P i).G.roots.length = k := by
  have hlen_le : ∀ i ∈ I₁, (P i).G.roots.length ≤ m := by
    intro i hi
    have hset : ((P i).G.roots.toFinset : Set α) ⊆ (σ i (S i).root).vertexSet := by
      intro v hv
      rw [Finset.mem_coe, List.mem_toFinset, ← (htd i).roots_root] at hv
      exact (σ i (S i).root).roots_subset v hv
    have hncard : ((P i).G.roots.toFinset : Set α).ncard = (P i).G.roots.length := by
      rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup (P i).G.roots_nodup]
    rw [← hm i hi, ← hncard]
    exact Set.ncard_le_ncard hset (σ i (S i).root).vertexSet_finite
  obtain ⟨k, hk, hI₂⟩ := exists_infinite_fiber hI₁ (Set.finite_Iic m)
    (f := fun i ↦ (P i).G.roots.length) hlen_le
  exact ⟨{i ∈ I₁ | (P i).G.roots.length = k}, k, fun _ hi ↦ hi.1, hI₂, hk, fun _ hi ↦ hi.2⟩

open Classical in
/-- Canonical coordinate equivalence `Fin m ≃ V` for a finite set `V` with `V.ncard = m`. -/
noncomputable def coordEquiv {V : Set α} (hfin : V.Finite) {m : ℕ} (hm : V.ncard = m) :
    Fin m ≃ V := by
  let _ : Fintype V := hfin.fintype
  have hcard : Fintype.card V = m := by
    rw [← hm, Set.ncard_eq_toFinset_card V hfin, Set.Finite.card_toFinset]
  exact (Fintype.equivFinOfCardEq hcard).symm

open Classical in
/-- Canonical coordinate equivalence `Fin m ≃ V(σᵢ(o(Sᵢ)))` when `|V(σᵢ(o(Sᵢ)))| = m`. -/
noncomputable def rootCoord (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (i : ℕ) {m : ℕ} (hm : (σ i (S i).root).vertexSet.ncard = m) :
    Fin m ≃ (σ i (S i).root).vertexSet :=
  coordEquiv (σ i (S i).root).vertexSet_finite hm

open Classical in
/-- Total pulled-back list in `Fin m` along `rootCoord S σ i hm` (empty if `|V| ≠ m`). -/
noncomputable def rootPullList (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (m i : ℕ) (π : List α) : List (Fin m) :=
  if hm : (σ i (S i).root).vertexSet.ncard = m then
    pullList (rootCoord S σ i hm) π
  else []

open Classical in
theorem rootPullList_eq (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    {m i : ℕ} (hm : (σ i (S i).root).vertexSet.ncard = m) (π : List α) :
    rootPullList S σ m i π = pullList (rootCoord S σ i hm) π :=
  dite_eq_left_of_eq_true (eq_true hm)

omit [Preorder Ω] in
open Classical in
/-- Graph Minors IV, (8.4), claim (3) (page 250):
Coordinate version of "By replacing each $P_i$ by an ...isomorphic... $\Omega$-patchwork, we may
therefore assume,
to simplify notation, that for some set $V_0$ and march $\pi_0$ in $V_0$, (3)
*$V(\sigma_i(o(S_i))) = V_0$ and $\pi(G_i) = \pi_0$ for all $i \in I_2$":
there is an infinite `I₂' ⊆ I₂` and a march `π₀` in `Fin m` such that
`rootPullList S σ m i (P i).G.roots = π₀.1` for all `i ∈ I₂'`. -/
theorem lemma_8_4_claim_3 {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {I₂ : Set ℕ} (hI₂ : I₂.Infinite)
    (hm : ∀ i ∈ I₂, (σ i (S i).root).vertexSet.ncard = m) :
    ∃ (I₂' : Set ℕ) (π₀ : MarchIn m),
      I₂' ⊆ I₂ ∧ I₂'.Infinite ∧
      ∀ i ∈ I₂', rootPullList S σ m i (P i).G.roots = π₀.1 := by
  have hroots_sub : ∀ i, ∀ v ∈ (P i).G.roots, v ∈ (σ i (S i).root).vertexSet := by
    intro i v hv
    rw [← (htd i).roots_root] at hv
    exact (σ i (S i).root).roots_subset v hv
  let f (i : ℕ) : MarchIn m :=
    if hnd : (rootPullList S σ m i (P i).G.roots).Nodup then
      ⟨rootPullList S σ m i (P i).G.roots, hnd⟩
    else ⟨[], List.nodup_nil⟩
  obtain ⟨π₀, _, hI₂'⟩ :=
    exists_infinite_fiber hI₂ Set.finite_univ (f := f) (fun _ _ ↦ Set.mem_univ _)
  refine ⟨{i ∈ I₂ | f i = π₀}, π₀, fun _ hi ↦ hi.1, hI₂', fun i hi' ↦ ?_⟩
  have hmi : (σ i (S i).root).vertexSet.ncard = m := hm i hi'.1
  have hnd : (rootPullList S σ m i (P i).G.roots).Nodup := by
    rw [rootPullList_eq S σ hmi]
    exact pullList_nodup _ (P i).G.roots_nodup (hroots_sub i)
  have hEq := congrArg Subtype.val hi'.2
  dsimp only [f] at hEq
  rwa [dite_eq_left_of_eq_true (eq_true hnd)] at hEq

/-! ### Pulled-back edge invariants and Graph Minors IV, (8.4), claims (4)–(8) -/

open Classical in
/-- Pulled-back march `μᵢ(e)` in `Fin m` along `rootCoord S σ i hm`. -/
noncomputable def μPull (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (P : ℕ → Patchwork Ω α β) (m i : ℕ) (e : β) : List (Fin m) :=
  rootPullList S σ m i ((P i).μ e)

open Classical in
/-- Pulled-back patch `Δᵢ(e)` on `Fin m` along `marchMapSubgraph ((P i).μ e) (μPull ...)`. -/
noncomputable def ΔPull (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (P : ℕ → Patchwork Ω α β) (m i : ℕ) (e : β) :
    Set ((⊤ : SimpleGraph (Fin m)).Subgraph) :=
  marchMapSubgraph ((P i).μ e) (μPull S σ P m i e) '' ((P i).Δ e).groupings

open Classical in
/-- Pulled-back end set `V_{Gᵢ}(e)` in `Fin m` along `rootCoord S σ i hm`. -/
noncomputable def endsPull (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (P : ℕ → Patchwork Ω α β) (m i : ℕ) (e : β) : Set (Fin m) :=
  if hm : (σ i (S i).root).vertexSet.ncard = m then
    toVal (rootCoord S σ i hm) ⁻¹' (P i).G.ends e
  else ∅

omit [Preorder Ω] in
open Classical in
theorem endsPull_eq (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (P : ℕ → Patchwork Ω α β) {m i : ℕ} (hm : (σ i (S i).root).vertexSet.ncard = m) (e : β) :
    endsPull S σ P m i e = toVal (rootCoord S σ i hm) ⁻¹' (P i).G.ends e :=
  dite_eq_left_of_eq_true (eq_true hm)

omit [Preorder Ω] in
open Classical in
theorem ends_subset_root_vertexSet {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {i : ℕ} {e : β} (he : e ∈ (σ i (S i).root).edgeSet) :
    (P i).G.ends e ⊆ (σ i (S i).root).vertexSet := by
  rw [((htd i).le (S i).root (S i).root_mem).ends_eq e he]
  exact fun _ hv ↦ (σ i (S i).root).vertex_mem_of_inc hv

omit [Preorder Ω] in
open Classical in
theorem μ_subset_root_vertexSet {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {i : ℕ} {e : β} (he : e ∈ (σ i (S i).root).edgeSet) (hd : e ∈ (P i).dom) :
    ∀ v ∈ (P i).μ e, v ∈ (σ i (S i).root).vertexSet := by
  intro v hv
  have hv_ends : v ∈ (P i).G.ends e := by
    rw [← (P i).μ_set e hd]
    exact hv
  exact ends_subset_root_vertexSet htd he hv_ends

omit [Preorder Ω] in
open Classical in
theorem μPull_nodup {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {i : ℕ} (hmi : (σ i (S i).root).vertexSet.ncard = m)
    {e : β} (he : e ∈ (σ i (S i).root).edgeSet) (hd : e ∈ (P i).dom) :
    (μPull S σ P m i e).Nodup := by
  dsimp only [μPull]
  rw [rootPullList_eq S σ hmi]
  exact pullList_nodup _ ((P i).μ_nodup e hd) (μ_subset_root_vertexSet htd he hd)

omit [Preorder Ω] in
open Classical in
theorem μPull_ΔPull_imp {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {i i' : ℕ} (hmi : (σ i (S i).root).vertexSet.ncard = m)
    (hmi' : (σ i' (S i').root).vertexSet.ncard = m)
    {e e' : β} (he : e ∈ (σ i (S i).root).edgeSet) (hd : e ∈ (P i).dom)
    (he' : e' ∈ (σ i' (S i').root).edgeSet) (hd' : e' ∈ (P i').dom)
    (hμ : μPull S σ P m i e = μPull S σ P m i' e')
    (hΔ : ΔPull S σ P m i e = ΔPull S σ P m i' e') :
    (P i').μ e' = ((P i).μ e).map (coordMap (rootCoord S σ i hmi) (rootCoord S σ i' hmi')) ∧
      Set.MapsTo (marchMapSubgraph ((P i).μ e) ((P i').μ e'))
        ((P i).Δ e).groupings ((P i').Δ e').groupings := by
  have hsub : ∀ v ∈ (P i).μ e, v ∈ (σ i (S i).root).vertexSet :=
    μ_subset_root_vertexSet htd he hd
  have hsub' : ∀ v ∈ (P i').μ e', v ∈ (σ i' (S i').root).vertexSet :=
    μ_subset_root_vertexSet htd he' hd'
  have hμ_pull : pullList (rootCoord S σ i hmi) ((P i).μ e) =
      pullList (rootCoord S σ i' hmi') ((P i').μ e') := by
    rw [← rootPullList_eq S σ hmi, ← rootPullList_eq S σ hmi']
    exact hμ
  refine ⟨(map_coordMap_eq_of_pullList_eq _ _ hsub hsub' hμ_pull).symm, fun δ hδ ↦ ?_⟩
  let ρ := μPull S σ P m i e
  have hρ_nodup : ρ.Nodup := μPull_nodup htd hmi he hd
  have hlen : ((P i).μ e).length = ρ.length := by
    have hmap := congrArg List.length (map_toVal_pullList (rootCoord S σ i hmi) hsub)
    rw [List.length_map, ← rootPullList_eq S σ hmi] at hmap
    exact hmap.symm
  have hlen' : ((P i').μ e').length = ρ.length := by
    have hmap := congrArg List.length (map_toVal_pullList (rootCoord S σ i' hmi') hsub')
    rw [List.length_map, ← rootPullList_eq S σ hmi'] at hmap
    change (μPull S σ P m i' e').length = ((P i').μ e').length at hmap
    rw [← hmap, ← hμ]
  have hmem : marchMapSubgraph ((P i).μ e) ρ δ ∈ ΔPull S σ P m i' e' := by
    rw [← hΔ]
    exact ⟨δ, hδ, rfl⟩
  dsimp only [ΔPull] at hmem
  rw [← hμ] at hmem
  obtain ⟨δ', hδ', hEq⟩ := hmem
  have hcomp₁ := marchMapSubgraph_comp hρ_nodup hlen δ (π₃ := (P i').μ e')
  have hcomp₂ := marchMapSubgraph_comp hρ_nodup hlen' δ' (π₃ := (P i').μ e')
  have hverts' : δ'.verts ⊆ {v | v ∈ (P i').μ e'} := by
    rw [(((P i').Δ e').verts_eq δ' hδ').trans ((P i').Δ_verts e' ((P i').dom_subset hd')),
      (P i').μ_set e' hd']
  have hid := marchMapSubgraph_id hverts'
  have hEq2 := congrArg (marchMapSubgraph ρ ((P i').μ e')) hEq.symm
  rw [hcomp₁, hcomp₂, hid] at hEq2
  exact hEq2 ▸ hδ'

omit [Preorder Ω] in
open Classical in
theorem endsPull_imp {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {i i' : ℕ} (hmi : (σ i (S i).root).vertexSet.ncard = m)
    (hmi' : (σ i' (S i').root).vertexSet.ncard = m)
    {e e' : β} (he : e ∈ (σ i (S i).root).edgeSet) (he' : e' ∈ (σ i' (S i').root).edgeSet)
    (hends : endsPull S σ P m i e = endsPull S σ P m i' e') :
    coordMap (rootCoord S σ i hmi) (rootCoord S σ i' hmi') '' (P i).G.ends e =
      (P i').G.ends e' := by
  rw [endsPull_eq S σ P hmi, endsPull_eq S σ P hmi'] at hends
  exact image_coordMap_eq_of_preimage_eq _ _
    (ends_subset_root_vertexSet htd he) (ends_subset_root_vertexSet htd he') hends

open Classical in
/-- Set of root edges in `dom(μᵢ)` with pulled-back march `ρ`. -/
noncomputable def domRootEdges (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (P : ℕ → Patchwork Ω α β) (m : ℕ) (ρ : List (Fin m)) (i : ℕ) : Set β :=
  {e ∈ (σ i (S i).root).edgeSet | e ∈ (P i).dom ∧ μPull S σ P m i e = ρ}

open Classical in
/-- Graph Minors IV, (8.4), claim (4) (page 250):
"Since $\Omega$ is well-quasi-ordered and there are only finitely many different patches with
a given vertex set, we may choose by (8.3) an infinite $I_3 \subseteq I_2$ such that (4)
*For all $i$, $i' \in I_3$ with $i' > i$ there is an injection $\alpha$ from $\{e \in
\operatorname{dom}(\mu_i) \cap E(\sigma_i(o(S_i))) \colon \mu_i(e) = \rho\}$ into $\{e' \in
\operatorname{dom}(\mu_{i'}) \cap E(\sigma_{i'}(o(S_{i'}))) \colon \mu_{i'}(e') = \rho\}$,
such that for each $e$, $\phi_i(e) \le \phi_{i'}(\alpha(e))$ and $\Delta_i(e) =
\Delta_{i'}(\alpha(e))$ ... ." -/
theorem lemma_8_4_claim_4 (hH : Higman83Statement.{u₁, u₂}) (hΩ : WellQuasiOrderedLE Ω)
    {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β}
    {I₂' : Set ℕ} (hI₂' : I₂'.Infinite) :
    ∃ I₃ ⊆ I₂', I₃.Infinite ∧
      ∀ (ρ : MarchIn m), ∀ i ∈ I₃, ∀ i' ∈ I₃, i < i' →
        ∃ α : β → β,
          Set.InjOn α (domRootEdges S σ P m ρ.1 i) ∧
          Set.MapsTo α (domRootEdges S σ P m ρ.1 i) (domRootEdges S σ P m ρ.1 i') ∧
          ∀ e ∈ domRootEdges S σ P m ρ.1 i,
            (P i).φ e ≤ (P i').φ (α e) ∧
            ΔPull S σ P m i e = ΔPull S σ P m i' (α e) := by
  let Tag := MarchIn m × Set ((⊤ : SimpleGraph (Fin m)).Subgraph)
  let A_Tag : Finset Tag := (Set.finite_univ : (Set.univ : Set Tag).Finite).toFinset
  let E_dom (i : ℕ) : Finset β :=
    (σ i (S i).root).edgeSet_finite.toFinset.filter fun e ↦
      e ∈ (P i).dom ∧ (μPull S σ P m i e).Nodup
  let tag (i : ℕ) (e : β) : Tag :=
    if hnd : (μPull S σ P m i e).Nodup then
      (⟨μPull S σ P m i e, hnd⟩, ΔPull S σ P m i e)
    else (⟨[], List.nodup_nil⟩, ∅)
  obtain ⟨I₃, hI₃_sub, hI₃_inf, hI₃⟩ :=
    higman83_partitioned_finset hH hΩ hI₂' E_dom tag (fun i e ↦ (P i).φ e) A_Tag
  refine ⟨I₃, hI₃_sub, hI₃_inf, fun ρ i hi₃ i' hi₃' hlt ↦ ?_⟩
  have hset_eq : ∀ (j : ℕ) (D : Set ((⊤ : SimpleGraph (Fin m)).Subgraph)),
      {e ∈ domRootEdges S σ P m ρ.1 j | ΔPull S σ P m j e = D} =
        {e ∈ (E_dom j : Set β) | tag j e = (ρ, D)} := by
    intro j D
    ext e
    simp only [domRootEdges, E_dom, tag, Set.mem_sep_iff, Finset.mem_coe, Finset.mem_filter,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨heE, hd, hμ⟩, hD⟩
      have hnd : (μPull S σ P m j e).Nodup := hμ ▸ ρ.2
      refine ⟨⟨heE, hd, hnd⟩, ?_⟩
      rw [dite_eq_left_of_eq_true (eq_true hnd)]
      exact Prod.ext (Subtype.ext hμ) hD
    · rintro ⟨⟨heE, hd, hnd⟩, htag⟩
      rw [dite_eq_left_of_eq_true (eq_true hnd)] at htag
      exact ⟨⟨heE, hd, congrArg Subtype.val (congrArg Prod.fst htag)⟩, congrArg Prod.snd htag⟩
  have hfib : ∀ D : Set ((⊤ : SimpleGraph (Fin m)).Subgraph),
      ∃ g : β → β,
        Set.InjOn g {e ∈ domRootEdges S σ P m ρ.1 i | ΔPull S σ P m i e = D} ∧
        Set.MapsTo g {e ∈ domRootEdges S σ P m ρ.1 i | ΔPull S σ P m i e = D}
          {e ∈ domRootEdges S σ P m ρ.1 i' | ΔPull S σ P m i' e = D} ∧
        ∀ e ∈ {e ∈ domRootEdges S σ P m ρ.1 i | ΔPull S σ P m i e = D},
          (P i).φ e ≤ (P i').φ (g e) := by
    intro D
    rw [hset_eq i D, hset_eq i' D]
    have hmemA : (ρ, D) ∈ A_Tag := (Set.Finite.mem_toFinset _).mpr (Set.mem_univ _)
    exact hI₃ (ρ, D) hmemA i hi₃ i' hi₃' hlt
  obtain ⟨α, hα_inj, hα_maps, hα_tag, hα_le⟩ := piece_fiber_injections hfib
  exact ⟨α, hα_inj, hα_maps, fun e he ↦ ⟨hα_le e he, (hα_tag e he).symm⟩⟩

open Classical in
/-- Set of root edges outside `dom(μᵢ)` with pulled-back end set `Y`. -/
noncomputable def nondomRootEdges (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (P : ℕ → Patchwork Ω α β) (m : ℕ) (Y : Set (Fin m)) (i : ℕ) : Set β :=
  {e ∈ (σ i (S i).root).edgeSet | e ∉ (P i).dom ∧ endsPull S σ P m i e = Y}

open Classical in
/-- Graph Minors IV, (8.4), claim (5) (page 250):
"We may similarly choose an infinite subset $I_4 \subseteq I_3$ such that for all subsets $Y$
of $V_0$, (5) *For all $i, i' \in I_4$ with $i' > i$ there is an injection $\alpha$ from
$\{e \in E(\sigma_i(o(S_i))) - \operatorname{dom}(\mu_i) \colon V_{G_i}(e) = Y\}$ into $\{e'
\in E(\sigma_{i'}(o(S_{i'}))) - \operatorname{dom}(\mu_{i'}) \colon V_{G_{i'}}(e') = Y\}$,
such that $\phi_i(e) \le \phi_{i'}(\alpha(e))$ for each $e$." -/
theorem lemma_8_4_claim_5 (hH : Higman83Statement.{u₁, u₂}) (hΩ : WellQuasiOrderedLE Ω)
    {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β}
    {I₃ : Set ℕ} (hI₃ : I₃.Infinite) :
    ∃ I₄ ⊆ I₃, I₄.Infinite ∧
      ∀ (Y : Set (Fin m)), ∀ i ∈ I₄, ∀ i' ∈ I₄, i < i' →
        ∃ α : β → β,
          Set.InjOn α (nondomRootEdges S σ P m Y i) ∧
          Set.MapsTo α (nondomRootEdges S σ P m Y i) (nondomRootEdges S σ P m Y i') ∧
          ∀ e ∈ nondomRootEdges S σ P m Y i, (P i).φ e ≤ (P i').φ (α e) := by
  let A_Y : Finset (Set (Fin m)) := (Set.finite_univ : (Set.univ : Set (Set
    (Fin m))).Finite).toFinset
  let E_nondom (i : ℕ) : Finset β :=
    (σ i (S i).root).edgeSet_finite.toFinset.filter fun e ↦ e ∉ (P i).dom
  let tag (i : ℕ) (e : β) : Set (Fin m) := endsPull S σ P m i e
  obtain ⟨I₄, hI₄_sub, hI₄_inf, hI₄⟩ :=
    higman83_partitioned_finset hH hΩ hI₃ E_nondom tag (fun i e ↦ (P i).φ e) A_Y
  refine ⟨I₄, hI₄_sub, hI₄_inf, fun Y i hi₄ i' hi₄' hlt ↦ ?_⟩
  have hset_eq : ∀ j : ℕ,
      nondomRootEdges S σ P m Y j = {e ∈ (E_nondom j : Set β) | tag j e = Y} := by
    intro j
    ext e
    simp [nondomRootEdges, E_nondom, tag, and_assoc]
  rw [hset_eq i, hset_eq i']
  have hmemA : Y ∈ A_Y := (Set.Finite.mem_toFinset _).mpr (Set.mem_univ _)
  exact hI₄ Y hmemA i hi₄ i' hi₄' hlt

open Classical in
/-- Graph Minors IV, (8.4), claim (6) (page 250):
"By piecing together the injections of (4) and (5), we deduce (6) For all $i$, $i' \in I_4$ with
$i' > i$ there is an injection $\alpha \colon E(\sigma_i(o(S_i))) \to E(\sigma_{i'}(o(S_{i'})))$
such that for each $e \in E(\sigma_i(o(S_i)))$
(i) $\alpha(e) \in \operatorname{dom}(\mu_{i'})$ if and only if $e \in \operatorname{dom}(\mu_i)$
(ii) if $e \in \operatorname{dom}(\mu_i)$ then $\mu_i(e) = \mu_{i'}(\alpha(e))$ and
$\Delta_i(e) = \Delta_{i'}(\alpha(e))$
(iii) if $e \notin \operatorname{dom}(\mu_i)$ then $V_{G_i}(e) = V_{G_{i'}}(\alpha(e))$
(iv) $\phi_i(e) \le \phi_{i'}(\alpha(e))$." -/
theorem lemma_8_4_claim_6 {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {I₂ I₃ I₄ : Set ℕ} (hm : ∀ i ∈ I₂, (σ i (S i).root).vertexSet.ncard = m)
    (hI₃_sub : I₃ ⊆ I₂) (hI₄_sub : I₄ ⊆ I₃)
    (h4 : ∀ (ρ : MarchIn m), ∀ i ∈ I₃, ∀ i' ∈ I₃, i < i' →
      ∃ α : β → β,
        Set.InjOn α (domRootEdges S σ P m ρ.1 i) ∧
        Set.MapsTo α (domRootEdges S σ P m ρ.1 i) (domRootEdges S σ P m ρ.1 i') ∧
        ∀ e ∈ domRootEdges S σ P m ρ.1 i,
          (P i).φ e ≤ (P i').φ (α e) ∧
          ΔPull S σ P m i e = ΔPull S σ P m i' (α e))
    (h5 : ∀ (Y : Set (Fin m)), ∀ i ∈ I₄, ∀ i' ∈ I₄, i < i' →
      ∃ α : β → β,
        Set.InjOn α (nondomRootEdges S σ P m Y i) ∧
        Set.MapsTo α (nondomRootEdges S σ P m Y i) (nondomRootEdges S σ P m Y i') ∧
        ∀ e ∈ nondomRootEdges S σ P m Y i, (P i).φ e ≤ (P i').φ (α e))
    {i i' : ℕ} (hi₄ : i ∈ I₄) (hi₄' : i' ∈ I₄) (hlt : i < i') :
    let hmi := hm i (hI₃_sub (hI₄_sub hi₄))
    let hmi' := hm i' (hI₃_sub (hI₄_sub hi₄'))
    let γ := coordMap (rootCoord S σ i hmi) (rootCoord S σ i' hmi')
    ∃ αe : β → β,
      Set.MapsTo αe (σ i (S i).root).edgeSet (σ i' (S i').root).edgeSet ∧
      Set.InjOn αe (σ i (S i).root).edgeSet ∧
      (∀ e ∈ (σ i (S i).root).edgeSet, αe e ∈ (P i').dom ↔ e ∈ (P i).dom) ∧
      (∀ e ∈ (σ i (S i).root).edgeSet, e ∈ (P i).dom →
        (P i').μ (αe e) = ((P i).μ e).map γ ∧
          Set.MapsTo (marchMapSubgraph ((P i).μ e) ((P i').μ (αe e)))
            ((P i).Δ e).groupings ((P i').Δ (αe e)).groupings) ∧
      (∀ e ∈ (σ i (S i).root).edgeSet, e ∉ (P i).dom →
        γ '' (P i).G.ends e = (P i').G.ends (αe e)) ∧
      (∀ e ∈ (σ i (S i).root).edgeSet, (P i).φ e ≤ (P i').φ (αe e)) := by
  intro hmi hmi' γ
  have hi₃ : i ∈ I₃ := hI₄_sub hi₄
  have hi₃' : i' ∈ I₃ := hI₄_sub hi₄'
  let α_dom (ρ : MarchIn m) : β → β := (h4 ρ i hi₃ i' hi₃' hlt).choose
  let α_nondom (Y : Set (Fin m)) : β → β := (h5 Y i hi₄ i' hi₄' hlt).choose
  let αe (e : β) : β :=
    if hnd : e ∈ (P i).dom ∧ (μPull S σ P m i e).Nodup then
      α_dom ⟨μPull S σ P m i e, hnd.2⟩ e
    else
      α_nondom (endsPull S σ P m i e) e
  have hmem_dom : ∀ e ∈ (σ i (S i).root).edgeSet, ∀ (hd : e ∈ (P i).dom),
      (μPull S σ P m i e).Nodup ∧
        e ∈ domRootEdges S σ P m (μPull S σ P m i e) i :=
    fun e he hd ↦ ⟨μPull_nodup htd hmi he hd, ⟨he, hd, rfl⟩⟩
  have hmem_nondom : ∀ e ∈ (σ i (S i).root).edgeSet, e ∉ (P i).dom →
      e ∈ nondomRootEdges S σ P m (endsPull S σ P m i e) i :=
    fun e he hnd ↦ ⟨he, hnd, rfl⟩
  have hαe_dom_spec : ∀ e (he : e ∈ (σ i (S i).root).edgeSet) (hd : e ∈ (P i).dom),
      let hnd := (hmem_dom e he hd).1
      αe e = α_dom ⟨μPull S σ P m i e, hnd⟩ e ∧
      αe e ∈ (σ i' (S i').root).edgeSet ∧
      αe e ∈ (P i').dom ∧
      μPull S σ P m i' (αe e) = μPull S σ P m i e ∧
      (P i).φ e ≤ (P i').φ (αe e) ∧
      ΔPull S σ P m i e = ΔPull S σ P m i' (αe e) := by
    intro e he hd
    obtain ⟨hnd, hmem⟩ := hmem_dom e he hd
    have hEq : αe e = α_dom ⟨μPull S σ P m i e, hnd⟩ e := by
      dsimp only [αe]
      exact dite_eq_left_of_eq_true (eq_true ⟨hd, hnd⟩)
    have hspec := (h4 ⟨μPull S σ P m i e, hnd⟩ i hi₃ i' hi₃' hlt).choose_spec
    have hm' : αe e ∈ domRootEdges S σ P m (μPull S σ P m i e) i' :=
      hEq.symm ▸ hspec.2.1 hmem
    have hφΔ : (P i).φ e ≤ (P i').φ (αe e) ∧ ΔPull S σ P m i e = ΔPull S σ P m i' (αe e) :=
      hEq.symm ▸ hspec.2.2 e hmem
    exact ⟨hEq, hm'.1, hm'.2.1, hm'.2.2, hφΔ.1, hφΔ.2⟩
  have hαe_nondom_spec : ∀ e ∈ (σ i (S i).root).edgeSet, ∀ (hnd : e ∉ (P i).dom),
      αe e = α_nondom (endsPull S σ P m i e) e ∧
      αe e ∈ (σ i' (S i').root).edgeSet ∧
      αe e ∉ (P i').dom ∧
      endsPull S σ P m i' (αe e) = endsPull S σ P m i e ∧
      (P i).φ e ≤ (P i').φ (αe e) := by
    intro e he hnd
    have hmem := hmem_nondom e he hnd
    have hnot : ¬(e ∈ (P i).dom ∧ (μPull S σ P m i e).Nodup) := fun h ↦ hnd h.1
    have hEq : αe e = α_nondom (endsPull S σ P m i e) e := by
      dsimp only [αe]
      exact dite_eq_right_of_eq_false (eq_false hnot)
    have hspec := (h5 (endsPull S σ P m i e) i hi₄ i' hi₄' hlt).choose_spec
    have hm' : αe e ∈ nondomRootEdges S σ P m (endsPull S σ P m i e) i' :=
      hEq.symm ▸ hspec.2.1 hmem
    have hφ : (P i).φ e ≤ (P i').φ (αe e) :=
      hEq.symm ▸ hspec.2.2 e hmem
    exact ⟨hEq, hm'.1, hm'.2.1, hm'.2.2, hφ⟩
  refine ⟨αe, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    by_cases hd : e ∈ (P i).dom
    · exact (hαe_dom_spec e he hd).2.1
    · exact (hαe_nondom_spec e he hd).2.1
  · intro e₁ he₁ e₂ he₂ hEq
    by_cases hd₁ : e₁ ∈ (P i).dom <;> by_cases hd₂ : e₂ ∈ (P i).dom
    · obtain ⟨hEq₁, _, _, hμ₁, _, _⟩ := hαe_dom_spec e₁ he₁ hd₁
      obtain ⟨hEq₂, _, _, hμ₂, _, _⟩ := hαe_dom_spec e₂ he₂ hd₂
      have hμ_eq : μPull S σ P m i e₁ = μPull S σ P m i e₂ :=
        hμ₁.symm.trans (by rw [hEq, hμ₂])
      have hρ_eq : (⟨μPull S σ P m i e₁, (hmem_dom e₁ he₁ hd₁).1⟩ : MarchIn m) =
          ⟨μPull S σ P m i e₂, (hmem_dom e₂ he₂ hd₂).1⟩ :=
        Subtype.ext hμ_eq
      have hα_eq : α_dom ⟨μPull S σ P m i e₁, (hmem_dom e₁ he₁ hd₁).1⟩ e₁ =
          α_dom ⟨μPull S σ P m i e₁, (hmem_dom e₁ he₁ hd₁).1⟩ e₂ := by
        rw [← hEq₁, hEq, hEq₂, hρ_eq]
      have hm₂ : e₂ ∈ domRootEdges S σ P m (μPull S σ P m i e₁) i := by
        rw [hμ_eq]
        exact (hmem_dom e₂ he₂ hd₂).2
      exact (h4 ⟨μPull S σ P m i e₁, (hmem_dom e₁ he₁ hd₁).1⟩ i hi₃ i' hi₃' hlt).choose_spec.1
        (hmem_dom e₁ he₁ hd₁).2 hm₂ hα_eq
    · exact False.elim ((hαe_nondom_spec e₂ he₂ hd₂).2.2.1 (hEq ▸ (hαe_dom_spec e₁ he₁ hd₁).2.2.1))
    · exact False.elim ((hαe_nondom_spec e₁ he₁ hd₁).2.2.1 (hEq.symm ▸
      (hαe_dom_spec e₂ he₂ hd₂).2.2.1))
    · obtain ⟨hEq₁, _, _, hends₁, _⟩ := hαe_nondom_spec e₁ he₁ hd₁
      obtain ⟨hEq₂, _, _, hends₂, _⟩ := hαe_nondom_spec e₂ he₂ hd₂
      have hY_eq : endsPull S σ P m i e₁ = endsPull S σ P m i e₂ :=
        hends₁.symm.trans (by rw [hEq, hends₂])
      have hα_eq : α_nondom (endsPull S σ P m i e₁) e₁ =
          α_nondom (endsPull S σ P m i e₁) e₂ := by
        rw [← hEq₁, hEq, hEq₂, hY_eq]
      have hm₂ : e₂ ∈ nondomRootEdges S σ P m (endsPull S σ P m i e₁) i := by
        rw [hY_eq]
        exact hmem_nondom e₂ he₂ hd₂
      exact (h5 (endsPull S σ P m i e₁) i hi₄ i' hi₄' hlt).choose_spec.1
        (hmem_nondom e₁ he₁ hd₁) hm₂ hα_eq
  · intro e he
    by_cases hd : e ∈ (P i).dom
    · exact ⟨fun _ ↦ hd, fun _ ↦ (hαe_dom_spec e he hd).2.2.1⟩
    · exact ⟨fun hd' ↦ False.elim ((hαe_nondom_spec e he hd).2.2.1 hd'),
        fun hd' ↦ False.elim (hd hd')⟩
  · intro e he hd
    obtain ⟨_, he', hd', hμ, _, hΔ⟩ := hαe_dom_spec e he hd
    exact μPull_ΔPull_imp htd hmi hmi' he hd he' hd' hμ.symm hΔ
  · intro e he hnd
    obtain ⟨_, he', _, hends, _⟩ := hαe_nondom_spec e he hnd
    exact endsPull_imp htd hmi hmi' he he' hends.symm
  · intro e he
    by_cases hd : e ∈ (P i).dom
    · exact (hαe_dom_spec e he hd).2.2.2.2.1
    · exact (hαe_nondom_spec e he hd).2.2.2.2

open Classical in
/-- Wrapper equipping `ℕ × ι` with the tip-simulation preorder. -/
private structure TipPair (P : ℕ → Patchwork Ω α β) (S : ℕ → RootedTree ι)
    (σ : ℕ → ι → RootedHypergraph α β) where
  i : ℕ
  s : ι

open Classical in
private instance (P : ℕ → Patchwork Ω α β) (S : ℕ → RootedTree ι)
    (σ : ℕ → ι → RootedHypergraph α β) : Preorder (TipPair P S σ) where
  le a b := a.s ∈ (S a.i).edges →
    b.s ∈ (S b.i).edges ∧ Simulated ((P a.i).restrict (σ a.i a.s)) ((P b.i).restrict (σ b.i b.s))
  le_refl a := fun hs ↦ ⟨hs, Simulated.refl _⟩
  le_trans a b c hab hbc := fun hsa ↦
    ⟨(hbc (hab hsa).1).1, (hab hsa).2.trans (hbc (hab hsa).1).2⟩

open Classical in
private theorem tipPair_wqo {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β}
    (hwqo : ∀ Q : ℕ → Patchwork Ω α β,
      (∀ k, ∃ i, ∃ s ∈ (S i).edges, Q k = (P i).restrict (σ i s)) →
      ∃ j j', j < j' ∧ Simulated (Q j) (Q j')) :
    WellQuasiOrderedLE (TipPair P S σ) := by
  refine ⟨fun f ↦ ?_⟩
  by_cases hall : ∀ k, (f k).s ∈ (S (f k).i).edges
  · obtain ⟨j, j', hlt, hsim⟩ := hwqo (fun k ↦ (P (f k).i).restrict (σ (f k).i (f k).s))
      (fun k ↦ ⟨(f k).i, (f k).s, hall k, rfl⟩)
    exact ⟨j, j', hlt, fun _ ↦ ⟨hall j', hsim⟩⟩
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    exact ⟨k, k + 1, Nat.lt_succ_self k, fun h ↦ False.elim (hk h)⟩

open Classical in
/-- Pulled-back root march `π(σᵢ(s))` in `Fin m` for a tip `s` of `Sᵢ`. -/
noncomputable def tipRootsPull (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (m i : ℕ) (s : ι) : List (Fin m) :=
  rootPullList S σ m i (σ i s).roots

omit [Preorder Ω] in
open Classical in
theorem tip_roots_subset_root_vertexSet {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (hstar : ∀ i, (S i).IsStar)
    (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {i : ℕ} {s : ι} (hs : s ∈ (S i).edges) :
    ∀ v ∈ (σ i s).roots, v ∈ (σ i (S i).root).vertexSet := by
  intro v hv
  have hmem : v ∈ (σ i s).rootSet := hv
  rw [(htd i).rootSet_edge s hs, hstar i s hs] at hmem
  exact hmem.2

omit [Preorder Ω] in
open Classical in
theorem tipRootsPull_nodup {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (hstar : ∀ i, (S i).IsStar)
    (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {i : ℕ} (hmi : (σ i (S i).root).vertexSet.ncard = m)
    {s : ι} (hs : s ∈ (S i).edges) :
    (tipRootsPull S σ m i s).Nodup := by
  dsimp only [tipRootsPull]
  rw [rootPullList_eq S σ hmi]
  exact pullList_nodup _ (σ i s).roots_nodup (tip_roots_subset_root_vertexSet hstar htd hs)

open Classical in
/-- Set of tips `s ∈ U(Sᵢ)` with pulled-back root march `ρ`. -/
noncomputable def tipsWithMarch (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (m : ℕ) (ρ : List (Fin m)) (i : ℕ) : Set ι :=
  {s ∈ ((S i).edges : Set ι) | tipRootsPull S σ m i s = ρ}

open Classical in
/-- Graph Minors IV, (8.4), claim (7) (page 250) and claim (8) (page 251):
"Let $\rho$ be a march in $V_0$. Since $\{P_i | \sigma_i(s) \colon i \ge 1, s \in U(S_i)\}$ is
well-quasi-ordered by simulation we may choose by (8.3) an infinite $I_5 \subseteq I_4$ such that
(7) For all $i$, $i' \in I_5$ with $i' > i$ there is an injection $\beta$ from
$\{s \in U(S_i) \colon \pi(\sigma_i(s)) = \rho\}$ into
$\{s' \in U(S_{i'}) \colon \pi(\sigma_{i'}(s')) = \rho\}$, such that $P_i | \sigma_i(s)$ is
simulated in $P_{i'} | \sigma_{i'}(\beta(s))$ for each $s$."
"By repeating this for each $\rho$ and piecing together the resulting injections $\beta$, we deduce
that there is an infinite $I_6 \subseteq I_4$ such that (8) For all $i, i' \in I_6$ with $i' > i$
there is an injection $\beta \colon U(S_i) \to U(S_{i'})$ such that for each $s \in U(S_i)$,
(i) $\pi(\sigma_i(s)) = \pi(\sigma_{i'}(\beta(s)))$
(ii) there is a realizable expansion of $P_i \mid \sigma_i(s)$ in
$P_{i'} \mid \sigma_{i'}(\beta(s))$." -/
theorem lemma_8_4_claim_7 (hH : Higman83Statement.{u₁, u₂})
    {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β}
    (hwqo : ∀ Q : ℕ → Patchwork Ω α β,
      (∀ k, ∃ i, ∃ s ∈ (S i).edges, Q k = (P i).restrict (σ i s)) →
      ∃ j j', j < j' ∧ Simulated (Q j) (Q j'))
    {I₄ : Set ℕ} (hI₄ : I₄.Infinite) :
    ∃ I₆ ⊆ I₄, I₆.Infinite ∧
      ∀ (ρ : MarchIn m), ∀ i ∈ I₆, ∀ i' ∈ I₆, i < i' →
        ∃ βf : ι → ι,
          Set.InjOn βf (tipsWithMarch S σ m ρ.1 i) ∧
          Set.MapsTo βf (tipsWithMarch S σ m ρ.1 i) (tipsWithMarch S σ m ρ.1 i') ∧
          ∀ s ∈ tipsWithMarch S σ m ρ.1 i,
            Simulated ((P i).restrict (σ i s)) ((P i').restrict (σ i' (βf s))) := by
  let A_March : Finset (MarchIn m) := (Set.finite_univ : (Set.univ : Set
    (MarchIn m)).Finite).toFinset
  have hTipWQO : WellQuasiOrderedLE (TipPair P S σ) := tipPair_wqo hwqo
  let E_tips (i : ℕ) : Finset ι :=
    (S i).edges.filter fun s ↦ (tipRootsPull S σ m i s).Nodup
  let tag (i : ℕ) (s : ι) : MarchIn m :=
    if hnd : (tipRootsPull S σ m i s).Nodup then
      ⟨tipRootsPull S σ m i s, hnd⟩
    else ⟨[], List.nodup_nil⟩
  let ℓ (i : ℕ) (s : ι) : TipPair P S σ := ⟨i, s⟩
  obtain ⟨I₆, hI₆_sub, hI₆_inf, hI₆⟩ :=
    higman83_partitioned_finset hH hTipWQO hI₄ E_tips tag ℓ A_March
  refine ⟨I₆, hI₆_sub, hI₆_inf, fun ρ i hi₆ i' hi₆' hlt ↦ ?_⟩
  have hset_eq : ∀ j : ℕ,
      tipsWithMarch S σ m ρ.1 j = {s ∈ (E_tips j : Set ι) | tag j s = ρ} := by
    intro j
    ext s
    simp only [tipsWithMarch, E_tips, tag, Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨hs, hEq⟩
      have hnd : (tipRootsPull S σ m j s).Nodup := hEq ▸ ρ.2
      refine ⟨⟨hs, hnd⟩, ?_⟩
      rw [dite_eq_left_of_eq_true (eq_true hnd)]
      exact Subtype.ext hEq
    · rintro ⟨⟨hs, hnd⟩, htag⟩
      rw [dite_eq_left_of_eq_true (eq_true hnd)] at htag
      exact ⟨hs, congrArg Subtype.val htag⟩
  rw [hset_eq i, hset_eq i']
  have hmemA : ρ ∈ A_March := (Set.Finite.mem_toFinset _).mpr (Set.mem_univ _)
  obtain ⟨βf, hβ_inj, hβ_maps, hβ_le⟩ := hI₆ ρ hmemA i hi₆ i' hi₆' hlt
  refine ⟨βf, hβ_inj, hβ_maps, fun s hs ↦ ?_⟩
  have hs_edges : s ∈ (S i).edges := by
    rw [← hset_eq i] at hs
    exact hs.1
  exact (hβ_le s hs hs_edges).2

open Classical in
/-- Graph Minors IV, (8.4), claim (8) (page 251). -/
theorem lemma_8_4_claim_8 {m : ℕ} {P : ℕ → Patchwork Ω α β} {S : ℕ → RootedTree ι}
    {σ : ℕ → ι → RootedHypergraph α β} (hstar : ∀ i, (S i).IsStar)
    (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    {I₂ I₆ : Set ℕ} (hm : ∀ i ∈ I₂, (σ i (S i).root).vertexSet.ncard = m)
    (hI₆_sub : I₆ ⊆ I₂)
    (h7 : ∀ (ρ : MarchIn m), ∀ i ∈ I₆, ∀ i' ∈ I₆, i < i' →
      ∃ βf : ι → ι,
        Set.InjOn βf (tipsWithMarch S σ m ρ.1 i) ∧
        Set.MapsTo βf (tipsWithMarch S σ m ρ.1 i) (tipsWithMarch S σ m ρ.1 i') ∧
        ∀ s ∈ tipsWithMarch S σ m ρ.1 i,
          Simulated ((P i).restrict (σ i s)) ((P i').restrict (σ i' (βf s))))
    {i i' : ℕ} (hi₆ : i ∈ I₆) (hi₆' : i' ∈ I₆) (hlt : i < i') :
    let hmi := hm i (hI₆_sub hi₆)
    let hmi' := hm i' (hI₆_sub hi₆')
    let γ := coordMap (rootCoord S σ i hmi) (rootCoord S σ i' hmi')
    ∃ βf : ι → ι,
      Set.MapsTo βf (S i).edges (S i').edges ∧
      Set.InjOn βf (S i).edges ∧
      (∀ s ∈ (S i).edges, (σ i' (βf s)).roots = (σ i s).roots.map γ) ∧
      (∀ s ∈ (S i).edges, Simulated ((P i).restrict (σ i s)) ((P i').restrict (σ i' (βf s)))) := by
  intro hmi hmi' γ
  have hi₂ : i ∈ I₂ := hI₆_sub hi₆
  have hi₂' : i' ∈ I₂ := hI₆_sub hi₆'
  let tag (j : ℕ) (hj : j ∈ I₂) (s : ι) : MarchIn m :=
    if hs : s ∈ (S j).edges then
      ⟨tipRootsPull S σ m j s, tipRootsPull_nodup hstar htd (hm j hj) hs⟩
    else ⟨[], List.nodup_nil⟩
  have hset_eq : ∀ (j : ℕ) (hj : j ∈ I₂) (ρ : MarchIn m),
      {s ∈ ((S j).edges : Set ι) | tag j hj s = ρ} = tipsWithMarch S σ m ρ.1 j := by
    intro j hj ρ
    ext s
    simp only [tipsWithMarch, Finset.mem_coe]
    refine ⟨fun ⟨hs, hEq⟩ ↦ ⟨hs, ?_⟩, fun ⟨hs, hEq⟩ ↦ ⟨hs, ?_⟩⟩
    · dsimp only [tag] at hEq
      rw [dite_eq_left_of_eq_true (eq_true hs)] at hEq
      exact congrArg Subtype.val hEq
    · dsimp only [tag]
      rw [dite_eq_left_of_eq_true (eq_true hs)]
      exact Subtype.ext hEq
  let ℓ (j : ℕ) (s : ι) : TipPair P S σ := ⟨j, s⟩
  have hfib : ∀ ρ : MarchIn m, ∃ βf : ι → ι,
      Set.InjOn βf {s ∈ ((S i).edges : Set ι) | tag i hi₂ s = ρ} ∧
      Set.MapsTo βf {s ∈ ((S i).edges : Set ι) | tag i hi₂ s = ρ}
        {s ∈ ((S i').edges : Set ι) | tag i' hi₂' s = ρ} ∧
      ∀ s ∈ {s ∈ ((S i).edges : Set ι) | tag i hi₂ s = ρ}, ℓ i s ≤ ℓ i' (βf s) := by
    intro ρ
    rw [hset_eq i hi₂ ρ, hset_eq i' hi₂' ρ]
    obtain ⟨βf, hβ_inj, hβ_maps, hβ_sim⟩ := h7 ρ i hi₆ i' hi₆' hlt
    refine ⟨βf, hβ_inj, hβ_maps, fun s hs _ ↦ ?_⟩
    exact ⟨(hβ_maps hs).1, hβ_sim s hs⟩
  obtain ⟨βf, hβ_inj, hβ_maps, hβ_tag, hβ_le⟩ := piece_fiber_injections hfib
  refine ⟨βf, hβ_maps, hβ_inj, fun s hs ↦ ?_, fun s hs ↦ (hβ_le s hs hs).2⟩
  have hs' : βf s ∈ (S i').edges := hβ_maps hs
  have hEq_tag := congrArg Subtype.val (hβ_tag s hs)
  dsimp only [tag] at hEq_tag
  rw [dite_eq_left_of_eq_true (eq_true hs'), dite_eq_left_of_eq_true (eq_true hs)] at hEq_tag
  have hpull_eq : pullList (rootCoord S σ i hmi) (σ i s).roots =
      pullList (rootCoord S σ i' hmi') (σ i' (βf s)).roots := by
    rw [← rootPullList_eq S σ hmi, ← rootPullList_eq S σ hmi']
    exact hEq_tag.symm
  exact (map_coordMap_eq_of_pullList_eq _ _
    (tip_roots_subset_root_vertexSet hstar htd hs)
    (tip_roots_subset_root_vertexSet hstar htd hs') hpull_eq).symm

open Classical in
/-- **Graph Minors IV, (8.4)** (pages 249–250):
"Let $n \ge 0$, let $\Omega$ be a well-quasi-order, and let $P_i = (G_i, \mu_i, \Delta_i,
\phi_i)$ ($i = 1, 2, \dots$) be a countable sequence of removable $\Omega$-patchworks. For
each $i \ge 1$ let $(S_i, \sigma_i)$ be a star-decomposition of $G_i$ with
$|V(\sigma_i(o(S_i)))| \le n$." "*Suppose that $\{P_i | \sigma_i(s) \colon i \ge 1, s \in
U(S_i)\}$ is well-quasi-ordered by simulation. Then there exist $i' > i \ge 1$ such that
$P_i$ is simulated in $P_{i'}$." -/
theorem theorem_8_4_proof (hH : Higman83Statement.{u₁, u₂}) (hΩ : WellQuasiOrderedLE Ω)
    (n : ℕ) (P : ℕ → Patchwork Ω α β) (hrem : ∀ i, (P i).IsRemovable)
    (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (hstar : ∀ i, (S i).IsStar)
    (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    (hcard : ∀ i, (σ i (S i).root).vertexSet.ncard ≤ n)
    (hwqo : ∀ Q : ℕ → Patchwork Ω α β,
      (∀ k, ∃ i, ∃ s ∈ (S i).edges, Q k = (P i).restrict (σ i s)) →
      ∃ j j', j < j' ∧ Simulated (Q j) (Q j')) :
    ∃ i i', i < i' ∧ Simulated (P i) (P i') := by
  obtain ⟨I₁, m, hI₁_inf, _, hm₁⟩ := lemma_8_4_claim_1 hcard
  obtain ⟨I₂, _, hI₂_sub, hI₂_inf, _, _⟩ := lemma_8_4_claim_2 htd hI₁_inf hm₁
  have hm : ∀ i ∈ I₂, (σ i (S i).root).vertexSet.ncard = m := fun i hi ↦ hm₁ i (hI₂_sub hi)
  obtain ⟨I₂', π₀, hI₂'_sub, hI₂'_inf, h3⟩ := lemma_8_4_claim_3 htd hI₂_inf hm
  obtain ⟨I₃, hI₃_sub, hI₃_inf, h4⟩ := lemma_8_4_claim_4 hH hΩ hI₂'_inf
  have hI₃_sub₂ : I₃ ⊆ I₂ := hI₃_sub.trans hI₂'_sub
  obtain ⟨I₄, hI₄_sub, hI₄_inf, h5⟩ := lemma_8_4_claim_5 hH hΩ hI₃_inf
  have hI₄_sub₂ : I₄ ⊆ I₂ := hI₄_sub.trans hI₃_sub₂
  obtain ⟨I₆, hI₆_sub, hI₆_inf, h7⟩ := lemma_8_4_claim_7 hH hwqo hI₄_inf
  let i := Nat.nth (· ∈ I₆) 0
  let i' := Nat.nth (· ∈ I₆) 1
  have hi₆ : i ∈ I₆ := Nat.nth_mem_of_infinite hI₆_inf 0
  have hi₆' : i' ∈ I₆ := Nat.nth_mem_of_infinite hI₆_inf 1
  have hlt : i < i' := Nat.nth_strictMono hI₆_inf Nat.zero_lt_one
  have hi₄ : i ∈ I₄ := hI₆_sub hi₆
  have hi₄' : i' ∈ I₄ := hI₆_sub hi₆'
  have hi₂' : i ∈ I₂' := hI₃_sub (hI₄_sub hi₄)
  have hi'₂' : i' ∈ I₂' := hI₃_sub (hI₄_sub hi₄')
  have hi₂ : i ∈ I₂ := hI₂'_sub hi₂'
  have hi'₂ : i' ∈ I₂ := hI₂'_sub hi'₂'
  let hmi := hm i hi₂
  let hmi' := hm i' hi'₂
  let γ := coordMap (rootCoord S σ i hmi) (rootCoord S σ i' hmi')
  have hγ_bij : Set.BijOn γ (σ i (S i).root).vertexSet (σ i' (S i').root).vertexSet :=
    coordMap_bijOn (rootCoord S σ i hmi) (rootCoord S σ i' hmi')
  have hroots_sub : ∀ j, ∀ v ∈ (P j).G.roots, v ∈ (σ j (S j).root).vertexSet := by
    intro j v hv
    rw [← (htd j).roots_root] at hv
    exact (σ j (S j).root).roots_subset v hv
  have hroots_pull : pullList (rootCoord S σ i hmi) (P i).G.roots =
      pullList (rootCoord S σ i' hmi') (P i').G.roots := by
    rw [← rootPullList_eq S σ hmi, ← rootPullList_eq S σ hmi', h3 i hi₂', h3 i' hi'₂']
  have hγ_roots : (P i').G.roots = (P i).G.roots.map γ :=
    (map_coordMap_eq_of_pullList_eq _ _ (hroots_sub i) (hroots_sub i') hroots_pull).symm
  obtain ⟨αe, hα_maps, hα_inj, hα_dom, hα_μ, hα_ends, hα_φ⟩ :=
    lemma_8_4_claim_6 htd hm hI₃_sub₂ hI₄_sub h4 h5 hi₄ hi₄' hlt
  obtain ⟨βf, hβ_maps, hβ_inj, hβ_roots, hβ_sim⟩ :=
    lemma_8_4_claim_8 hstar htd hm (hI₆_sub.trans hI₄_sub₂) h7 hi₆ hi₆' hlt
  have hα_ends' : ∀ e ∈ (σ i (S i).root).edgeSet, e ∉ (P i).dom →
      ∀ v ∈ (P i).G.ends e, γ v ∈ (P i').G.ends (αe e) := by
    intro e he hnd v hv
    rw [← hα_ends e he hnd]
    exact ⟨v, hv, rfl⟩
  obtain ⟨ζv, ζe, hζ, _⟩ :=
    theorem_8_2_subset (hrem i') (hstar i) (htd i) (hstar i') (htd i')
      hγ_bij.mapsTo hγ_bij.injOn hγ_roots hα_maps hα_inj hα_dom hα_μ hα_ends' hα_φ
      hβ_maps hβ_inj hβ_roots hβ_sim (S i).edges subset_rfl
  rw [cross_edges_of_isTreeDecomposition (htd i)] at hζ
  have hAgrees_rfl : ∀ Q : Patchwork Ω α β, Q.Agrees Q :=
    fun _ ↦ ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hsim₁ : Simulated (P i)
      ((P i').restrict (cross (σ i') ((S i).edges.image βf) (S i').root)) :=
    ⟨ζv, ζe, hζ.congr (Patchwork.agrees_restrict_self (P i)) (hAgrees_rfl _)⟩
  have hsub' : (S i).edges.image βf ⊆ (S i').edges := by
    intro s' hs'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hs'
    exact hβ_maps hs
  have hle' : (cross (σ i') ((S i).edges.image βf) (S i').root).toHypergraph ≤
      (P i').G.toHypergraph :=
    cross_le_of_isTreeDecomposition (htd i') hsub'
  have hroots' : (cross (σ i') ((S i).edges.image βf) (S i').root).roots = (P i').G.roots :=
    (htd i').roots_root
  have hsim₂ : Simulated
      ((P i').restrict (cross (σ i') ((S i).edges.image βf) (S i').root)) (P i') :=
    (hrem i').simulated_restrict_of_roots_eq hle' hroots'
  exact ⟨i, i', hlt, hsim₁.trans hsim₂⟩

end GraphMinor.GM04

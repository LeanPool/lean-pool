/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/

-- Modified for Lean Pool: Lean 4.36 module and import port with style and linter fixes.

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Hom.Basic

import Mathlib.Tactic.Choose

/-!
# Core Definitions for the Classical Permutation Pattern Poset

Faithful Lean 4 formalization of:
- `Perm`: finite permutations `(len : ℕ, perm : Equiv.Perm (Fin len))`.
- `Contains` (`≤`): classical permutation pattern containment via order-preserving
  embeddings `Fin σ.len ↪o Fin τ.len` preserving pairwise value comparisons.
- `PartialOrder Perm`: reflexivity, transitivity, antisymmetry.
- `IsAntichain`, `IsChain`, `RankLevel`, `largestRank`, `width`, `IsSperner`.
- Fundamental chain-cover upper bound (`antichain_card_le_of_indexed_chain_cover`,
  `width_le_of_chain_cover`, `width_le_of_indexed_chain_cover`).
- `HasValley` and upward monotonicity (`hasValley_mono`).
- Genuine principal downset `Downset τ` (`π ∈ Downset τ ↔ π ≤ τ`) and
  interval `Interval σ τ` (`π ∈ Interval σ τ ↔ σ ≤ π ∧ π ≤ τ`).
- Faithful list representation `toList` and list standardization `standardizeList`.
-/

@[expose] public section

namespace PatternPoset

/-- A finite permutation of `{0, …, len - 1}` (0-indexed representation of `S_len`). -/
structure Perm where
  /-- Length of the permutation. -/
  len : ℕ
  /-- Underlying bijection on `Fin len`. -/
  perm : Equiv.Perm (Fin len)

instance : DecidableEq Perm := fun σ τ => by
  cases σ with
  | mk n p =>
    cases τ with
    | mk m q =>
      by_cases h : n = m
      · subst h
        by_cases hp : p = q
        · exact isTrue (by subst hp; rfl)
        · exact isFalse (fun heq => hp (by cases heq; rfl))
      · exact isFalse (fun heq => h (by cases heq; rfl))

/-- Extensionality for `Perm` via length equality and entry values. -/
theorem Perm.ext_val {σ τ : Perm} (hlen : σ.len = τ.len)
    (hval : ∀ i : Fin σ.len, (σ.perm i).val = (τ.perm (Fin.cast hlen i)).val) :
    σ = τ := by
  cases σ with
  | mk n p =>
    cases τ with
    | mk m q =>
      dsimp at hlen
      subst hlen
      congr 1
      ext i
      exact hval i

/-- Any strictly monotone function `Fin n → Fin n` is the identity. -/
theorem strictMono_fin_eq_id {n : ℕ} {f : Fin n → Fin n} (hf : StrictMono f) :
    ∀ i : Fin n, f i = i := by
  have hge : ∀ (k : ℕ) (hk : k < n), k ≤ (f ⟨k, hk⟩).val := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have h1 : k ≤ (f ⟨k, hk'⟩).val := ih hk'
      have h2 : (f ⟨k, hk'⟩).val < (f ⟨k + 1, hk⟩).val :=
        hf (show (⟨k, hk'⟩ : Fin n) < ⟨k + 1, hk⟩ by exact Nat.lt_succ_self k)
      omega
  have hle : ∀ (d : ℕ) (i : Fin n), n - 1 - i.val = d → (f i).val ≤ i.val := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h1 : (f i).val < n := (f i).isLt
      omega
    | succ d ih =>
      intro i hi
      have hi1 : i.val + 1 < n := by omega
      have hnext : (f ⟨i.val + 1, hi1⟩).val ≤ i.val + 1 :=
        ih ⟨i.val + 1, hi1⟩ (by dsimp; omega)
      have hlt : (f i).val < (f ⟨i.val + 1, hi1⟩).val :=
        hf (show i < ⟨i.val + 1, hi1⟩ by exact Nat.lt_succ_self i.val)
      omega
  intro i
  ext
  have h1 : i.val ≤ (f i).val := hge i.val i.isLt
  have h2 : (f i).val ≤ i.val := hle (n - 1 - i.val) i rfl
  omega

/-- Classical permutation pattern containment: `σ` occurs as a pattern in `τ` if there is
a strictly increasing map `f : Fin σ.len ↪o Fin τ.len` such that the values `τ.perm (f i)`
have the same relative order as `σ.perm i`. -/
def Contains (σ τ : Perm) : Prop :=
  ∃ f : Fin σ.len ↪o Fin τ.len,
    ∀ i j : Fin σ.len, σ.perm i < σ.perm j ↔ τ.perm (f i) < τ.perm (f j)

/-- Containment implies length inequality. -/
theorem contains_len_le {σ τ : Perm} (h : Contains σ τ) : σ.len ≤ τ.len := by
  rcases h with ⟨f, _⟩
  simpa using Fintype.card_le_of_injective f f.injective

/-- Two permutations of equal length with `Contains σ τ` are equal. -/
theorem contains_eq_of_len_eq {σ τ : Perm} (h : Contains σ τ) (hlen : σ.len = τ.len) :
    σ = τ := by
  rcases h with ⟨f, hf⟩
  cases σ with
  | mk n p =>
    cases τ with
    | mk m q =>
      dsimp at hlen
      subst hlen
      have hf_id : ∀ i : Fin n, f i = i := strictMono_fin_eq_id f.strictMono
      have hqp : StrictMono (fun a : Fin n => q (p.symm a)) := by
        intro a b hab
        have h1 : p (p.symm a) < p (p.symm b) := by simpa using hab
        have h2 : q (f (p.symm a)) < q (f (p.symm b)) := (hf _ _).mp h1
        simpa [hf_id] using h2
      have hqp_id : ∀ a : Fin n, q (p.symm a) = a := strictMono_fin_eq_id hqp
      congr 1
      refine Equiv.ext fun i => ?_
      have := hqp_id (p i)
      simpa using this.symm

/-- Uniqueness from relative order: if `σ` and `τ` have the same length and the same
pairwise value comparisons, then `σ = τ`. -/
theorem Perm.eq_of_lt_iff {σ τ : Perm} (hlen : σ.len = τ.len)
    (hlt : ∀ i j : Fin σ.len,
      σ.perm i < σ.perm j ↔ τ.perm (Fin.cast hlen i) < τ.perm (Fin.cast hlen j)) :
    σ = τ := by
  apply contains_eq_of_len_eq _ hlen
  refine ⟨⟨⟨Fin.cast hlen, (Fin.castOrderIso hlen).injective⟩, ?_⟩, hlt⟩
  intro a b
  exact (Fin.castOrderIso hlen).le_iff_le

instance : PartialOrder Perm where
  le := Contains
  le_refl σ := ⟨OrderEmbedding.ofStrictMono id strictMono_id, fun _ _ => Iff.rfl⟩
  le_trans _ _ _ h₁ h₂ := by
    rcases h₁ with ⟨f, hf⟩
    rcases h₂ with ⟨g, hg⟩
    exact ⟨f.trans g, fun i j => (hf i j).trans (hg (f i) (f j))⟩
  le_antisymm _ _ h₁ h₂ :=
    contains_eq_of_len_eq h₁ (le_antisymm (contains_len_le h₁) (contains_len_le h₂))

/-- Definitional bridge between `≤` on `Perm` and `Contains`. -/
theorem le_iff_contains {σ τ : Perm} : σ ≤ τ ↔ Contains σ τ := Iff.rfl

/-- Helper: `σ ≤ τ` implies `σ.len ≤ τ.len`. -/
theorem le_len_le {σ τ : Perm} (h : σ ≤ τ) : σ.len ≤ τ.len :=
  contains_len_le h

/-- Helper: `σ ≤ τ` with `σ.len = τ.len` implies `σ = τ`. -/
theorem eq_of_le_of_len_eq {σ τ : Perm} (h : σ ≤ τ) (hlen : σ.len = τ.len) : σ = τ :=
  contains_eq_of_len_eq h hlen

/-- An antichain in `Perm`: no two distinct elements are comparable. -/
def IsAntichain (A : Finset Perm) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y

/-- A chain in `Perm`: every pair of elements is comparable. -/
def IsChain (C : Finset Perm) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x

/-- The rank-`r` level of a finite set `S` of permutations: all elements of length `r`. -/
def RankLevel (S : Finset Perm) (r : ℕ) : Finset Perm :=
  S.filter (fun π => π.len = r)

/-- Every rank level is an antichain. -/
theorem rankLevel_isAntichain (S : Finset Perm) (r : ℕ) : IsAntichain (RankLevel S r) := by
  intro x hx y hy hxy
  rw [RankLevel, Finset.mem_filter] at hx hy
  exact eq_of_le_of_len_eq hxy (hx.2.trans hy.2.symm)

/-- The largest rank size (maximum cardinality of any rank level) of `S`. -/
def largestRank (S : Finset Perm) : ℕ :=
  (S.image Perm.len).sup (fun r => (RankLevel S r).card)

theorem rankLevel_card_le_largestRank (S : Finset Perm) (r : ℕ) :
    (RankLevel S r).card ≤ largestRank S := by
  by_cases hne : (RankLevel S r).Nonempty
  · rcases hne with ⟨π, hπ⟩
    rw [RankLevel, Finset.mem_filter] at hπ
    have hr : r ∈ S.image Perm.len := Finset.mem_image.mpr ⟨π, hπ.1, hπ.2⟩
    exact Finset.le_sup (f := fun r => (RankLevel S r).card) hr
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

theorem largestRank_le_iff {S : Finset Perm} {m : ℕ} :
    largestRank S ≤ m ↔ ∀ r : ℕ, (RankLevel S r).card ≤ m := by
  constructor
  · intro h r
    exact (rankLevel_card_le_largestRank S r).trans h
  · intro h
    unfold largestRank
    exact Finset.sup_le fun r _ => h r

theorem largestRank_eq_of_bounds {S : Finset Perm} {m r : ℕ}
    (hupper : ∀ r' : ℕ, (RankLevel S r').card ≤ m)
    (hlower : m ≤ (RankLevel S r).card) :
    largestRank S = m :=
  le_antisymm (largestRank_le_iff.mpr hupper) (hlower.trans (rankLevel_card_le_largestRank S r))

/-- The width of a finite set `S` of permutations: maximum cardinality of an antichain `A ⊆ S`. -/
noncomputable def width (S : Finset Perm) : ℕ :=
  letI := Classical.decPred IsAntichain
  (S.powerset.filter IsAntichain).sup Finset.card

theorem card_le_width_of_antichain {S A : Finset Perm}
    (hsub : A ⊆ S) (hanti : IsAntichain A) : A.card ≤ width S := by
  unfold width
  let _ := Classical.decPred IsAntichain
  have hmem : A ∈ S.powerset.filter IsAntichain := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, hanti⟩
  exact Finset.le_sup (f := Finset.card) hmem

theorem width_le_of_forall_antichain {S : Finset Perm} {m : ℕ}
    (h : ∀ A : Finset Perm, A ⊆ S → IsAntichain A → A.card ≤ m) :
    width S ≤ m := by
  unfold width
  let _ := Classical.decPred IsAntichain
  apply Finset.sup_le
  intro A hA
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact h A hA.1 hA.2

/-- Every finite poset `S` satisfies `largestRank S ≤ width S`. -/
theorem largestRank_le_width (S : Finset Perm) : largestRank S ≤ width S := by
  rw [largestRank_le_iff]
  intro r
  exact card_le_width_of_antichain (Finset.filter_subset _ _) (rankLevel_isAntichain S r)

/-- A finite subset `S` of the permutation pattern poset is **Sperner** if its width equals
its largest rank size. -/
def IsSperner (S : Finset Perm) : Prop :=
  width S = largestRank S

/-- Fundamental chain-cover upper bound (indexed form): if a finite family of chains
`{C i | i ∈ I}` covers `S`, then every antichain `A ⊆ S` has `A.card ≤ I.card`. -/
theorem antichain_card_le_of_indexed_chain_cover {ι : Type*}
    {S A : Finset Perm} {I : Finset ι} {C : ι → Finset Perm}
    (hsub : A ⊆ S) (hanti : IsAntichain A)
    (hchains : ∀ i ∈ I, IsChain (C i))
    (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ C i) :
    A.card ≤ I.card := by
  have hex : ∀ x : Perm, x ∈ A → ∃ i ∈ I, x ∈ C i := fun x hx => hcover x (hsub hx)
  classical
  choose f hfI hfC using fun (x : { x // x ∈ A }) => hex x.1 x.2
  by_cases hA : A.Nonempty
  · have hI_ne : Nonempty ι := by
      rcases hA with ⟨a, ha⟩
      exact ⟨f ⟨a, ha⟩⟩
    let g' : Perm → ι := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else Classical.choice hI_ne
    refine Finset.card_le_card_of_injOn g' ?_ ?_
    · intro x hx
      have hx' : x ∈ A := Finset.mem_coe.mp hx
      change g' x ∈ (I : Set ι)
      simp only [g', hx', dite_true]
      exact hfI ⟨x, hx'⟩
    · intro x hx y hy hxy
      have hx' : x ∈ A := Finset.mem_coe.mp hx
      have hy' : y ∈ A := Finset.mem_coe.mp hy
      have hxy' : f ⟨x, hx'⟩ = f ⟨y, hy'⟩ := by
        simpa only [g', hx', hy', dite_true] using hxy
      have hxC : x ∈ C (f ⟨x, hx'⟩) := hfC ⟨x, hx'⟩
      have hyC : y ∈ C (f ⟨x, hx'⟩) := hxy' ▸ hfC ⟨y, hy'⟩
      rcases hchains (f ⟨x, hx'⟩) (hfI ⟨x, hx'⟩) x hxC y hyC with hle | hle
      · exact hanti x hx' y hy' hle
      · exact (hanti y hy' x hx' hle).symm
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA, Finset.card_empty]
    exact Nat.zero_le _

/-- Indexed chain-cover upper bound on `width S`. -/
theorem width_le_of_indexed_chain_cover {ι : Type*}
    {S : Finset Perm} {I : Finset ι} {C : ι → Finset Perm}
    (hchains : ∀ i ∈ I, IsChain (C i))
    (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ C i) :
    width S ≤ I.card :=
  width_le_of_forall_antichain fun _ hsub hanti =>
    antichain_card_le_of_indexed_chain_cover hsub hanti hchains hcover

/-- Unindexed chain-cover upper bound on `width S`. -/
theorem width_le_of_chain_cover {S : Finset Perm} {𝒞 : Finset (Finset Perm)}
    (hchains : ∀ C ∈ 𝒞, IsChain C)
    (hcover : ∀ x ∈ S, ∃ C ∈ 𝒞, x ∈ C) :
    width S ≤ 𝒞.card :=
  width_le_of_indexed_chain_cover (I := 𝒞) (C := id) hchains hcover

/-- A permutation has a **valley** if some entry is strictly smaller than an earlier entry
and a later entry (i.e., contains `213` or `312`). -/
def HasValley (π : Perm) : Prop :=
  ∃ i j k : Fin π.len, i < j ∧ j < k ∧ π.perm j < π.perm i ∧ π.perm j < π.perm k

/-- Having a valley is inherited upward under pattern containment. -/
theorem hasValley_mono {σ τ : Perm} (hv : HasValley σ) (hle : σ ≤ τ) : HasValley τ := by
  rcases hv with ⟨i, j, k, hij, hjk, hji, hjk'⟩
  rcases le_iff_contains.mp hle with ⟨f, hf⟩
  exact ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk, (hf j i).mp hji, (hf j k).mp hjk'⟩

/-! ### Principal Downsets and Intervals -/

/-- The standardized pattern of `τ` obtained by restricting to the positions in
`S : Finset (Fin τ.len)`. -/
def subseqPerm (τ : Perm) (S : Finset (Fin τ.len)) : Perm where
  len := S.card
  perm :=
    let ePos : Fin S.card ≃o S := S.orderIsoOfFin rfl
    let V : Finset (Fin τ.len) := S.image τ.perm
    have hV : V.card = S.card := Finset.card_image_of_injective S τ.perm.injective
    let eVal : Fin S.card ≃o V := V.orderIsoOfFin hV
    let eRestrict : S ≃ V :=
      { toFun := fun x => ⟨τ.perm x.1, Finset.mem_image_of_mem τ.perm x.2⟩
        invFun := fun y =>
          ⟨τ.perm.symm y.1, by
            rcases Finset.mem_image.mp y.2 with ⟨x, hx, hxy⟩
            have : τ.perm.symm y.1 = x := by rw [← hxy]; exact τ.perm.symm_apply_apply x
            exact this ▸ hx⟩
        left_inv := fun x => Subtype.ext (τ.perm.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (τ.perm.apply_symm_apply y.1) }
    (ePos.toEquiv.trans eRestrict).trans eVal.toEquiv.symm

/-- Every subsequence pattern `subseqPerm τ S` is contained in `τ`. -/
theorem subseqPerm_le (τ : Perm) (S : Finset (Fin τ.len)) : subseqPerm τ S ≤ τ := by
  rw [le_iff_contains]
  let ePos : Fin S.card ≃o S := S.orderIsoOfFin rfl
  let V : Finset (Fin τ.len) := S.image τ.perm
  have hV : V.card = S.card := Finset.card_image_of_injective S τ.perm.injective
  let eVal : Fin S.card ≃o V := V.orderIsoOfFin hV
  refine ⟨ePos.toOrderEmbedding.trans (OrderEmbedding.subtype _), ?_⟩
  intro i j
  change (eVal.symm ⟨τ.perm (ePos i).1, _⟩) < (eVal.symm ⟨τ.perm (ePos j).1, _⟩) ↔
    τ.perm (ePos i).1 < τ.perm (ePos j).1
  exact eVal.symm.lt_iff_lt

/-- If `σ ≤ τ` via `f`, then `σ = subseqPerm τ (Finset.univ.image f)`. -/
theorem eq_subseqPerm_of_le {σ τ : Perm} (f : Fin σ.len ↪o Fin τ.len)
    (hf : ∀ i j : Fin σ.len, σ.perm i < σ.perm j ↔ τ.perm (f i) < τ.perm (f j)) :
    σ = subseqPerm τ (Finset.univ.image f) := by
  set S : Finset (Fin τ.len) := Finset.univ.image f
  have hcard : σ.len = (subseqPerm τ S).len := by
    change σ.len = S.card
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
  let ePos : Fin S.card ≃o S := S.orderIsoOfFin rfl
  let V : Finset (Fin τ.len) := S.image τ.perm
  have hV : V.card = S.card := Finset.card_image_of_injective S τ.perm.injective
  let eVal : Fin S.card ≃o V := V.orderIsoOfFin hV
  have hpos_eq : ∀ i : Fin σ.len, (ePos (Fin.cast hcard i)).1 = f i := by
    have hsm : StrictMono (fun i : Fin σ.len =>
        Fin.cast hcard.symm
          (ePos.symm ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩)) := by
      intro a b hab
      change (ePos.symm ⟨f a, _⟩).val < (ePos.symm ⟨f b, _⟩).val
      exact ePos.symm.lt_iff_lt.mpr (f.strictMono hab)
    have hid := strictMono_fin_eq_id hsm
    intro i
    have hi := hid i
    have h1 :
        ePos.symm ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩ = Fin.cast hcard i := by
      apply Fin.ext
      have hval :
          (ePos.symm ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩).val = i.val :=
        congrArg Fin.val hi
      exact hval
    have h2 := congrArg ePos h1
    simp only [OrderIso.apply_symm_apply] at h2
    exact congrArg Subtype.val h2.symm
  apply Perm.eq_of_lt_iff hcard
  intro i j
  rw [hf i j]
  change τ.perm (f i) < τ.perm (f j) ↔
    eVal.symm ⟨τ.perm (ePos (Fin.cast hcard i)).1, _⟩ <
    eVal.symm ⟨τ.perm (ePos (Fin.cast hcard j)).1, _⟩
  rw [eVal.symm.lt_iff_lt]
  change τ.perm (f i) < τ.perm (f j) ↔
    τ.perm (ePos (Fin.cast hcard i)).1 < τ.perm (ePos (Fin.cast hcard j)).1
  rw [hpos_eq i, hpos_eq j]

/-- The principal downset `[∅, τ]` of `τ` in the permutation pattern poset:
the genuine `Finset` of all patterns contained in `τ`. -/
def Downset (τ : Perm) : Finset Perm :=
  ((Finset.univ : Finset (Fin τ.len)).powerset).image (subseqPerm τ)

/-- Exact characterization of `Downset τ`: `π ∈ Downset τ ↔ π ≤ τ`. -/
theorem mem_downset_iff {π τ : Perm} : π ∈ Downset τ ↔ π ≤ τ := by
  unfold Downset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨S, _, rfl⟩
    exact subseqPerm_le τ S
  · intro hle
    rcases le_iff_contains.mp hle with ⟨f, hf⟩
    exact ⟨Finset.univ.image f, Finset.mem_powerset.mpr (Finset.subset_univ _),
      (eq_subseqPerm_of_le f hf).symm⟩

instance decidableContains : DecidableRel Contains :=
  fun σ τ => decidable_of_iff (σ ∈ Downset τ) (mem_downset_iff.trans le_iff_contains)

instance decidableLEPerm : DecidableRel (· ≤ · : Perm → Perm → Prop) :=
  fun σ τ => decidable_of_iff (σ ∈ Downset τ) mem_downset_iff

/-- The closed interval `[σ, τ]` in the permutation pattern poset:
all permutations `π` with `σ ≤ π` and `π ≤ τ`. -/
def Interval (σ τ : Perm) : Finset Perm :=
  (Downset τ).filter (fun π => σ ≤ π)

/-- Exact characterization of `Interval σ τ`:
`π ∈ Interval σ τ ↔ σ ≤ π ∧ π ≤ τ`. -/
theorem mem_interval_iff {σ τ π : Perm} : π ∈ Interval σ τ ↔ σ ≤ π ∧ π ≤ τ := by
  unfold Interval
  rw [Finset.mem_filter, mem_downset_iff]
  exact and_comm

/-! ### List Representation and Standardization -/

/-- List of 0-indexed values of a permutation `π`. -/
def Perm.toList (π : Perm) : List ℕ :=
  List.ofFn (fun i : Fin π.len => (π.perm i).val)

theorem Perm.toList_length (π : Perm) : π.toList.length = π.len := by
  simp [Perm.toList]

/-- `Perm.toList` is injective. -/
theorem Perm.toList_injective : Function.Injective Perm.toList := by
  intro σ τ h
  have hlen : σ.len = τ.len := by
    have := congrArg List.length h
    simpa [Perm.toList_length] using this
  apply Perm.ext_val hlen
  intro i
  have hget := congrArg (fun l => l[i.val]?) h
  simp only [Perm.toList, List.getElem?_ofFn, i.isLt, dite_true,
    show i.val < τ.len from hlen ▸ i.isLt] at hget
  exact Option.some.inj hget

/-- Standardize a list of distinct natural numbers to `{0, …, l.length - 1}` by
replacing each entry `v` with the count of entries strictly smaller than `v`. -/
def standardizeList (l : List ℕ) : List ℕ :=
  l.map (fun v => (l.filter (· < v)).length)

/-- Count of indices `j : Fin n` with `p j < p i` equals `(p i).val`. -/
theorem card_lt_perm_val {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (Finset.univ.filter (fun j : Fin n => p j < p i)).card = (p i).val := by
  have hbij :
      (Finset.univ.filter (fun j : Fin n => p j < p i)).card =
      (Finset.univ.filter (fun v : Fin n => v < p i)).card := by
    refine Finset.card_bij (fun j _ => p j) ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, hj.2⟩
    · intro j₁ _ j₂ _ h
      exact p.injective h
    · intro v hv
      rw [Finset.mem_filter] at hv
      refine ⟨p.symm v, ?_, p.apply_symm_apply v⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using hv.2⟩
  rw [hbij]
  have hbij2 :
      (Finset.univ.filter (fun v : Fin n => v < p i)).card =
      (Finset.range (p i).val).card := by
    refine Finset.card_bij (fun v _ => v.val) ?_ ?_ ?_
    · intro v hv
      rw [Finset.mem_filter] at hv
      exact Finset.mem_range.mpr hv.2
    · intro v₁ _ v₂ _ h
      exact Fin.ext h
    · intro k hk
      rw [Finset.mem_range] at hk
      refine ⟨⟨k, lt_trans hk (p i).isLt⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hk⟩
  rw [hbij2, Finset.card_range]

/-- If `σ ≤ τ` via `f`, then `σ.toList` equals `standardizeList` of the selected
values of `τ`. -/
theorem toList_eq_standardizeList_of_le {σ τ : Perm} (f : Fin σ.len ↪o Fin τ.len)
    (hf : ∀ i j : Fin σ.len, σ.perm i < σ.perm j ↔ τ.perm (f i) < τ.perm (f j)) :
    σ.toList = standardizeList (List.ofFn (fun i : Fin σ.len => (τ.perm (f i)).val)) := by
  set L := List.ofFn (fun i : Fin σ.len => (τ.perm (f i)).val)
  apply List.ext_getElem
  · simp [Perm.toList, standardizeList, L]
  · intro idx h1 h2
    simp only [Perm.toList, standardizeList, L, List.getElem_map, List.getElem_ofFn]
    have hfilt :
        ((List.ofFn (fun j : Fin σ.len => (τ.perm (f j)).val)).filter
          (· < (τ.perm (f ⟨idx, by simpa [Perm.toList] using h1⟩)).val)).length =
        (Finset.univ.filter (fun j : Fin σ.len =>
          σ.perm j < σ.perm ⟨idx, by simpa [Perm.toList] using h1⟩)).card := by
      have hlist :
          (List.ofFn (fun j : Fin σ.len => (τ.perm (f j)).val)).filter
            (· < (τ.perm (f ⟨idx, by simpa [Perm.toList] using h1⟩)).val) =
          ((List.finRange σ.len).filter (fun j : Fin σ.len =>
            decide (σ.perm j < σ.perm ⟨idx, by simpa [Perm.toList] using h1⟩))).map
            (fun j => (τ.perm (f j)).val) := by
        rw [List.ofFn_eq_map, List.filter_map]
        congr 1
        apply List.filter_congr
        intro j _
        simp only [Function.comp_apply, decide_eq_decide]
        exact (hf j ⟨idx, by simpa [Perm.toList] using h1⟩).symm
      rw [hlist, List.length_map]
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange σ.len).filter _)]
      congr 1
      ext j
      simp
    rw [hfilt, card_lt_perm_val]

end PatternPoset

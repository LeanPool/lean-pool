/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.HajnalSzemeredi.CountDefinitions
public import LeanPool.HajnalSzemeredi.Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Estructura de una coloración casi equitativa con clase grande inaccesible

Contexto (`Ctx`): `c` es casi equitativa en `S` con paleta `P` (`|P| = r + 1`), grado máximo
`≤ r`, y la clase grande `hi` no es accesible. Sea `𝒜 = acc` la familia de clases accesibles y
`ℬ = P \ 𝒜`.

* `h21`: todo `y ∈ B` tiene un vecino en cada clase de `𝒜` (desigualdad (2.1));
* `card_B`, `card_A`: `|B| = |ℬ| s + 1`, `|A| + 1 = |𝒜| s`;
* `two_le_card_acc`: `|𝒜| ≥ 2`;
* clases terminales y la familia `𝒜' = T_U` (`exists_TU`), con la propiedad (2.2);
* `countHyp`: las hipótesis de la parte de conteo.
-/

@[expose] public section

noncomputable section

open Finset Relation

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

open Classical in
/-- Contexto del lema principal. -/
structure Ctx (G : SimpleGraph V) (S : Finset V) (P : Finset ℕ) (c : V → ℕ)
    (r s lo hi : ℕ) : Prop where
  near : IsNear G S P c s lo hi
  deg : DegLe G S r
  card_P : P.card = r + 1
  hi_not : hi ∉ acc G S P c lo

open Classical in
/-- Arcos de `H - W`. -/
def avoid (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (W : ℕ) (a b : ℕ) : Prop :=
  Mov G S c a b ∧ a ≠ W ∧ b ≠ W

open Classical in
/-- `T_W`: clases accesibles distintas de `W` que no alcanzan `lo` en `H - W`. -/
def T (G : SimpleGraph V) (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (lo W : ℕ) : Finset ℕ :=
  ((acc G S P c lo).erase W).filter fun X => ¬ ReflTransGen (avoid G S c W) X lo

open Classical in
lemma card_part (S : Finset V) (c : V → ℕ) (Q : Finset ℕ) :
    (part S c Q).card = ∑ i ∈ Q, (cls S c i).card := by
  rw [← card_biUnion]
  · congr 1
    ext v
    simp [part, mem_cls, and_comm]
  · intro i _ j _ hij
    exact cls_disjoint hij

open Classical in
/-- `x ∈ T` y `x` alcanza un objetivo: si el camino pasa por `x'`, o lo evita o `x'` alcanza. -/
theorem split_avoid {α : Type*} {R : α → α → Prop} {x z : α} :
    ∀ {a}, ReflTransGen R a z → a ≠ x →
      ReflTransGen (fun u v => R u v ∧ u ≠ x ∧ v ≠ x) a z ∨ ReflTransGen R x z := by
  intro a h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact fun _ => Or.inl ReflTransGen.refl
  | head hab hbz ih =>
    rename_i a b
    intro hax
    by_cases hbx : b = x
    · subst hbx; exact Or.inr hbz
    · rcases ih hbx with h | h
      · exact Or.inl (ReflTransGen.head ⟨hab, hax, hbx⟩ h)
      · exact Or.inr h

open Classical in
/-- Transport reachability along inclusion of relations. -/
theorem rtgMono {α : Type*} {R R' : α → α → Prop} {a b : α} (h : ReflTransGen R a b)
    (hR : ∀ x y, R x y → R' x y) : ReflTransGen R' a b :=
  ReflTransGen.mono hR a b h

namespace Ctx

variable {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}

open Classical in
lemma acc_subset : acc G S P c lo ⊆ P := filter_subset _ _

open Classical in
lemma lo_mem_acc (h : Ctx G S P c r s lo hi) : lo ∈ acc G S P c lo :=
  mem_filter.mpr ⟨h.near.lo_mem, ReflTransGen.refl⟩

open Classical in
lemma mem_acc_of_mov (h : Ctx G S P c r s lo hi) {a b : ℕ} (hab : Mov G S c a b)
    (hb : b ∈ acc G S P c lo) : a ∈ acc G S P c lo := by
  obtain ⟨v, hv, -⟩ := id hab
  rw [mem_cls] at hv
  exact mem_filter.mpr ⟨hv.2 ▸ h.near.into v hv.1, ReflTransGen.head hab (mem_filter.mp hb).2⟩

open Classical in
lemma hi_mem_B (h : Ctx G S P c r s lo hi) : hi ∈ P \ acc G S P c lo :=
  mem_sdiff.mpr ⟨h.near.hi_mem, h.hi_not⟩

open Classical in
lemma cover (h : Ctx G S P c r s lo hi) :
    ∀ v ∈ S, c v ∈ acc G S P c lo ∪ (P \ acc G S P c lo) := by
  intro v hv
  rw [union_sdiff_of_subset acc_subset]
  exact h.near.into v hv

open Classical in
lemma card_r (h : Ctx G S P c r s lo hi) :
    r + 1 = (acc G S P c lo).card + (P \ acc G S P c lo).card := by
  have h1 := card_sdiff_of_subset (acc_subset (G := G) (S := S) (P := P) (c := c) (lo := lo))
  have h2 := card_le_card (acc_subset (G := G) (S := S) (P := P) (c := c) (lo := lo))
  have h3 := h.card_P
  omega

open Classical in
/-- (2.1): todo vértice de `B` tiene un vecino en cada clase accesible. -/
lemma h21 (h : Ctx G S P c r s lo hi) {y : V} (hy : y ∈ part S c (P \ acc G S P c lo))
    {X : ℕ} (hX : X ∈ acc G S P c lo) : (nIn G S c y X).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hy' := mem_filter.mp hy
  have hmov : Mov G S c (c y) X := by
    refine ⟨y, mem_cls.mpr ⟨hy'.1, rfl⟩, fun w hw hadj => ?_⟩
    have : w ∈ nIn G S c y X := mem_inter.mpr ⟨mem_nbr.mpr ⟨(mem_cls.mp hw).1, hadj⟩, hw⟩
    rw [hne] at this
    exact notMem_empty _ this
  exact (mem_sdiff.mp hy'.2).2 (h.mem_acc_of_mov hmov hX)

open Classical in
lemma card_B (h : Ctx G S P c r s lo hi) :
    (part S c (P \ acc G S P c lo)).card = (P \ acc G S P c lo).card * s + 1 := by
  rw [card_part, ← add_sum_erase _ _ h.hi_mem_B]
  have hsum : ∑ i ∈ (P \ acc G S P c lo).erase hi, (cls S c i).card =
      ∑ _i ∈ (P \ acc G S P c lo).erase hi, s := by
    refine sum_congr rfl fun i hi' => ?_
    obtain ⟨hih, hiB⟩ := mem_erase.mp hi'
    obtain ⟨hiP, hiA⟩ := mem_sdiff.mp hiB
    refine h.near.card i hiP ?_ hih
    rintro rfl
    exact hiA h.lo_mem_acc
  rw [hsum, sum_const, smul_eq_mul, card_erase_of_mem h.hi_mem_B, h.near.card_hi]
  have : 1 ≤ (P \ acc G S P c lo).card := card_pos.mpr ⟨hi, h.hi_mem_B⟩
  obtain ⟨k, hk⟩ : ∃ k, (P \ acc G S P c lo).card = k + 1 := ⟨_, (Nat.sub_add_cancel this).symm⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  ring

open Classical in
lemma card_A (h : Ctx G S P c r s lo hi) :
    (part S c (acc G S P c lo)).card + 1 = (acc G S P c lo).card * s := by
  rw [card_part, ← add_sum_erase _ _ h.lo_mem_acc]
  have hsum : ∑ i ∈ (acc G S P c lo).erase lo, (cls S c i).card =
      ∑ _i ∈ (acc G S P c lo).erase lo, s := by
    refine sum_congr rfl fun i hi' => ?_
    obtain ⟨hil, hiA⟩ := mem_erase.mp hi'
    refine h.near.card i (acc_subset hiA) hil ?_
    rintro rfl
    exact h.hi_not hiA
  rw [hsum, sum_const, smul_eq_mul, card_erase_of_mem h.lo_mem_acc]
  have hlo := h.near.card_lo
  have : 1 ≤ (acc G S P c lo).card := card_pos.mpr ⟨lo, h.lo_mem_acc⟩
  obtain ⟨k, hk⟩ : ∃ k, (acc G S P c lo).card = k + 1 := ⟨_, (Nat.sub_add_cancel this).symm⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  rw [← hlo]
  ring

open Classical in
/-- `|𝒜| ≥ 2`. -/
lemma two_le_card_acc (h : Ctx G S P c r s lo hi) : 2 ≤ (acc G S P c lo).card := by
  by_contra hlt
  push Not at hlt
  have hA : acc G S P c lo = {lo} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨h.lo_mem_acc, fun x hx => ?_⟩
    by_contra hne
    have : ({x, lo} : Finset ℕ) ⊆ acc G S P c lo := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact hx
      · rw [mem_singleton.mp hy]; exact h.lo_mem_acc
    have := card_le_card this
    rw [card_pair hne] at this
    omega
  set B := part S c (P \ acc G S P c lo)
  have hrB : (P \ acc G S P c lo).card = r := by
    have h1 := h.card_r
    have h2 : (acc G S P c lo).card = 1 := by rw [hA, card_singleton]
    omega
  -- doble conteo de aristas entre `B` y la clase `lo`
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := cls S c lo)
    (r := fun y x => G.Adj y x)
  have hleft : B.card ≤ ∑ y ∈ B, ((cls S c lo).bipartiteAbove (fun y x => G.Adj y x) y).card := by
    rw [card_eq_sum_ones]
    refine sum_le_sum fun y hy => ?_
    obtain ⟨w, hw⟩ := h.h21 hy h.lo_mem_acc
    rw [nIn, mem_inter, mem_nbr] at hw
    exact card_pos.mpr ⟨w, mem_filter.mpr ⟨hw.2, hw.1.2⟩⟩
  have hright : ∑ x ∈ cls S c lo, (B.bipartiteBelow (fun y x => G.Adj y x) x).card ≤
      ∑ _x ∈ cls S c lo, r := by
    refine sum_le_sum fun x hx => ?_
    refine le_trans (card_le_card fun y hy => ?_) (h.deg x (mem_cls.mp hx).1)
    obtain ⟨hyB, hadj⟩ := mem_filter.mp hy
    exact mem_nbr.mpr ⟨(mem_filter.mp hyB).1, hadj.symm⟩
  rw [sum_const, smul_eq_mul] at hright
  have hB : B.card = r * s + 1 := by
    have := h.card_B
    rw [hrB] at this
    exact this
  have hlo := h.near.card_lo
  have hmul : (cls S c lo).card * r ≤ s * r := Nat.mul_le_mul_right r (by omega)
  have hcomm : r * s = s * r := Nat.mul_comm r s
  have e1 : B.card ≤ (cls S c lo).card * r := by
    calc B.card ≤ _ := hleft
      _ = _ := hdc
      _ ≤ _ := hright
  omega

open Classical in
/-- `lo` no está en ningún `T_W`. -/
lemma lo_notMem_T (W : ℕ) : lo ∉ T G S P c lo W := by
  intro hmem
  exact (mem_filter.mp hmem).2 ReflTransGen.refl

open Classical in
lemma T_lo_nonempty (h : Ctx G S P c r s lo hi) : (T G S P c lo lo).Nonempty := by
  have h2 := h.two_le_card_acc
  have : 1 < ((acc G S P c lo).erase lo).card + 1 := by
    rw [card_erase_add_one h.lo_mem_acc]; omega
  obtain ⟨X, hX⟩ := card_pos.mp (by omega : 0 < ((acc G S P c lo).erase lo).card)
  refine ⟨X, mem_filter.mpr ⟨hX, fun hpath => ?_⟩⟩
  have hXlo := (mem_erase.mp hX).1
  rcases hpath.cases_tail with h' | ⟨b, -, hb⟩
  · exact hXlo h'.symm
  · exact hb.2.2 rfl

open Classical in
/-- Elección de `U` y de la familia `𝒜' = T_U`. -/
theorem exists_TU (h : Ctx G S P c r s lo hi) :
    ∃ U ∈ acc G S P c lo, (T G S P c lo U).Nonempty ∧
      (∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
        ReflTransGen (avoid G S c W) X lo) ∧
      (∀ X ∈ T G S P c lo U, ∀ Y ∈ acc G S P c lo, Y ∉ T G S P c lo U → Y ≠ U →
        ¬ Mov G S c X Y) := by
  set NT := (acc G S P c lo).filter fun W => (T G S P c lo W).Nonempty
  have hNT : NT.Nonempty := ⟨lo, mem_filter.mpr ⟨h.lo_mem_acc, h.T_lo_nonempty⟩⟩
  obtain ⟨U, hU, hmin⟩ := exists_min_image NT (fun W => (T G S P c lo W).card) hNT
  obtain ⟨hUacc, hUne⟩ := mem_filter.mp hU
  refine ⟨U, hUacc, hUne, ?_, ?_⟩
  · -- toda clase de `T_U` es terminal
    intro W hW X hX
    obtain ⟨hWU', hWnot⟩ := mem_filter.mp hW
    obtain ⟨hWU, hWacc⟩ := mem_erase.mp hWU'
    have hsub : T G S P c lo W ⊆ (T G S P c lo U).erase W := by
      intro Y hY
      obtain ⟨hYW', hYnot⟩ := mem_filter.mp hY
      obtain ⟨hYW, hYacc⟩ := mem_erase.mp hYW'
      refine mem_erase.mpr ⟨hYW, ?_⟩
      have hYU : Y ≠ U := by
        rintro rfl
        have hUlo : Y ≠ lo := by rintro rfl; exact hYnot ReflTransGen.refl
        obtain ⟨j, hj, hjU, hjpath⟩ := exists_step_avoid (mem_filter.mp hYacc).2 hUlo
        have hjW : j ≠ W := by rintro rfl; exact hWnot hjpath
        rcases split_avoid (x := W) hjpath hjW with hp | hp
        · exact hYnot (ReflTransGen.head ⟨hj, hWU.symm, hjW⟩
            (rtgMono hp (fun a b hab => ⟨hab.1.1, hab.2.1, hab.2.2⟩)))
        · exact hWnot hp
      refine mem_filter.mpr ⟨mem_erase.mpr ⟨hYU, hYacc⟩, fun hp => ?_⟩
      rcases split_avoid (x := W) hp hYW with hp' | hp'
      · exact hYnot (rtgMono hp' (fun a b hab => ⟨hab.1.1, hab.2.1, hab.2.2⟩))
      · exact hWnot hp'
    have hTW : T G S P c lo W = ∅ := by
      by_contra hne
      have hWNT : W ∈ NT := mem_filter.mpr ⟨hWacc, nonempty_iff_ne_empty.mpr hne⟩
      exact absurd (hmin W hWNT)
        (not_le.mpr (lt_of_le_of_lt (card_le_card hsub) (card_erase_lt_of_mem hW)))
    by_contra hnot
    have : X ∈ T G S P c lo W := mem_filter.mpr ⟨hX, hnot⟩
    rw [hTW] at this
    exact notMem_empty _ this
  · -- ninguna clase de `T_U` es movible a una clase de `(𝒜 \ 𝒜') \ {U}`
    intro X hX Y hY hYT hYU hmov
    obtain ⟨hXU', hXnot⟩ := mem_filter.mp hX
    have hXU := (mem_erase.mp hXU').1
    have hYreach : ReflTransGen (avoid G S c U) Y lo := by
      by_contra hn
      exact hYT (mem_filter.mpr ⟨mem_erase.mpr ⟨hYU, hY⟩, hn⟩)
    exact hXnot (ReflTransGen.head ⟨hmov, hXU, hYU⟩ hYreach)

open Classical in
lemma T_subset (U : ℕ) : T G S P c lo U ⊆ (acc G S P c lo).erase U := filter_subset _ _

open Classical in
/-- Las hipótesis de conteo valen para `𝒜' = T_U`. -/
theorem countHyp (h : Ctx G S P c r s lo hi) {U : ℕ} (hU : U ∈ acc G S P c lo)
    (hne : (T G S P c lo U).Nonempty)
    (hP2 : ∀ X ∈ T G S P c lo U, ∀ Y ∈ acc G S P c lo, Y ∉ T G S P c lo U → Y ≠ U →
      ¬ Mov G S c X Y) :
    CountHyp G S c (acc G S P c lo) (P \ acc G S P c lo) (T G S P c lo U) r s := by
  refine ⟨disjoint_sdiff, h.cover, fun W hW => (mem_erase.mp (T_subset U hW)).2, hne,
    h.card_r, h.deg, ?_, h.card_B, fun y hy X hX => h.h21 hy hX, ?_⟩
  · intro W hW
    have hWacc := (mem_erase.mp (T_subset U hW)).2
    refine h.near.card W (acc_subset hWacc) ?_ ?_
    · rintro rfl; exact lo_notMem_T _ hW
    · rintro rfl; exact h.hi_not hWacc
  · intro x hx hxT
    set Q := (acc G S P c lo \ T G S P c lo U).erase U
    have hQ : Q ⊆ (nbr G (part S c (acc G S P c lo)) x).image c := by
      intro Y hY
      obtain ⟨hYU, hY'⟩ := mem_erase.mp hY
      obtain ⟨hYacc, hYT⟩ := mem_sdiff.mp hY'
      have hnm := hP2 (c x) hxT Y hYacc hYT hYU
      have : ¬ Movable G S c x Y := fun hmov => hnm ⟨x, mem_cls.mpr ⟨hx, rfl⟩, hmov⟩
      simp only [Movable, not_forall, not_not] at this
      obtain ⟨w, hw, hadj⟩ := this
      rw [mem_cls] at hw
      refine mem_image.mpr ⟨w, mem_nbr.mpr ⟨mem_filter.mpr ⟨hw.1, hw.2 ▸ hYacc⟩, hadj⟩, hw.2⟩
    have h1 := le_trans (card_le_card hQ) card_image_le
    have hUmem : U ∈ acc G S P c lo \ T G S P c lo U :=
      mem_sdiff.mpr ⟨hU, fun hUT => (mem_erase.mp (T_subset U hUT)).1 rfl⟩
    have h2 : Q.card + 1 = _ := card_erase_add_one hUmem
    have h3 : (acc G S P c lo \ T G S P c lo U).card + (T G S P c lo U).card =
        (acc G S P c lo).card := by
      rw [card_sdiff_add_card_eq_card]
      exact fun W hW => (mem_erase.mp (T_subset U hW)).2
    omega

end Ctx

end HajnalSzemeredi

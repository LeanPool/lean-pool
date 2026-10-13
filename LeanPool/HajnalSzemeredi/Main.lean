/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.HajnalSzemeredi.Cases
public import LeanPool.HajnalSzemeredi.Count

/-!
Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.

# Teorema 2.4 de Kierstead–Kostochka (forma divisible)

`core`: si `|S| = s (r + 1)`, `|P| = r + 1` y `G[S]` tiene grado máximo `≤ r`, existe una
coloración propia de `S` con paleta `P` cuyas clases tienen todas tamaño `s`.

Inducción primaria en el número de aristas de `G[S]`; inducción secundaria (`main_lemma`) en el
número `q` de clases inaccesibles de una coloración casi equitativa.
-/

@[expose] public section

noncomputable section

open Finset Relation

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

open Classical in
/-- Hechos sobre `B⁻ = B \ {y₁}` necesarios para aplicar la hipótesis de inducción primaria. -/
lemma bminus {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ} {TU : Finset ℕ}
    (h : Ctx G S P c r s lo hi)
    (hch : CountHyp G S c (acc G S P c lo) (P \ acc G S P c lo) TU r s) {y₁ : V}
    (hy₁ : y₁ ∈ part S c (P \ acc G S P c lo)) :
    (part S c (P \ acc G S P c lo)).erase y₁ ⊆ S ∧
    edgeCount G ((part S c (P \ acc G S P c lo)).erase y₁) < edgeCount G S ∧
    ((part S c (P \ acc G S P c lo)).erase y₁).card =
      s * ((P \ acc G S P c lo).card - 1 + 1) ∧
    DegLe G ((part S c (P \ acc G S P c lo)).erase y₁) ((P \ acc G S P c lo).card - 1) := by
  set PB := P \ acc G S P c lo
  set B := part S c PB
  have hBS : B.erase y₁ ⊆ S := (erase_subset _ _).trans (filter_subset _ _)
  have hPB : 1 ≤ PB.card := card_pos.mpr ⟨hi, h.hi_mem_B⟩
  have hs : 1 ≤ s := by have := h.near.card_lo; omega
  have hcard : (B.erase y₁).card = s * (PB.card - 1 + 1) := by
    have hB : B.card = PB.card * s + 1 := h.card_B
    rw [card_erase_of_mem hy₁, hB, Nat.sub_add_cancel hPB, Nat.add_sub_cancel, Nat.mul_comm]
  refine ⟨hBS, ?_, hcard, ?_⟩
  · -- hay una arista entre `B⁻` y la clase `lo`
    obtain ⟨y, hy⟩ : (B.erase y₁).Nonempty := by
      rw [← card_pos, hcard]; exact Nat.mul_pos hs (Nat.succ_pos _)
    have hyB := (mem_erase.mp hy).2
    obtain ⟨w, hw⟩ := h.h21 hyB h.lo_mem_acc
    rw [nIn, mem_inter, mem_nbr, mem_cls] at hw
    have hwB : w ∉ B.erase y₁ := by
      intro hwB
      have := (mem_filter.mp (mem_erase.mp hwB).2).2
      rw [hw.2.2] at this
      exact (mem_sdiff.mp this).2 h.lo_mem_acc
    apply card_lt_card
    refine ⟨fun p hp => ?_, fun hsub => ?_⟩
    · obtain ⟨hp, hadj⟩ := mem_filter.mp hp
      obtain ⟨h1, h2, h3⟩ := mem_offDiag.mp hp
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hBS h1, hBS h2, h3⟩, hadj⟩
    · have hyw : (y, w) ∈ (S.offDiag.filter fun p => G.Adj p.1 p.2) :=
        mem_filter.mpr ⟨mem_offDiag.mpr ⟨hBS hy, hw.1.1, hw.1.2.ne⟩, hw.1.2⟩
      exact hwB (mem_offDiag.mp (mem_filter.mp (hsub hyw)).1).2.1
  · intro y hy
    have hyB := (mem_erase.mp hy).2
    have h1 : (nbr G B y).card + 1 ≤ PB.card := hch.deg_B hyB
    have h2 : (nbr G (B.erase y₁) y).card ≤ (nbr G B y).card :=
      card_le_card fun w hw => mem_nbr.mpr ⟨(mem_erase.mp (mem_nbr.mp hw).1).2, (mem_nbr.mp hw).2⟩
    omega

open Classical in
/-- Lema principal (inducción secundaria en el número de clases inaccesibles). -/
theorem main_lemma {S : Finset V} {P : Finset ℕ} {r s lo : ℕ}
    (IH : ∀ S' ⊆ S, edgeCount G S' < edgeCount G S → ∀ (P' : Finset ℕ) (r' : ℕ),
      P'.card = r' + 1 → S'.card = s * (r' + 1) → DegLe G S' r' → ∃ c, IsEq G S' P' c s)
    (hdeg : DegLe G S r) (hP : P.card = r + 1) :
    ∀ (c : V → ℕ) (hi : ℕ), IsNear G S P c s lo hi → ∃ c', IsEq G S P c' s := by
  intro c hi hc
  induction hk : P.card - (acc G S P c lo).card using Nat.strong_induction_on
    generalizing c hi with
  | _ k ih =>
  by_cases hacc : hi ∈ acc G S P c lo
  · exact shift_of_acc hc (mem_filter.mp hacc).2
  have h : Ctx G S P c r s lo hi := ⟨hc, hdeg, hP, hacc⟩
  obtain ⟨U, hU, hne, hterm, hP2⟩ := h.exists_TU
  have hch := h.countHyp hU hne hP2
  obtain ⟨z, hzS, hzT, ⟨y₀, hy₀⟩, hcase⟩ := hch.lemma_2_3
  -- la coloración `g` de `B \ {y}` por la hipótesis de inducción primaria
  have getg : ∀ y ∈ part S c (P \ acc G S P c lo), ∃ g, IsEq G
      ((part S c (P \ acc G S P c lo)).erase y) (P \ acc G S P c lo) g s := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := bminus h hch hy
    exact IH _ h1 h2 _ _ (Nat.succ_pred_eq_of_pos (card_pos.mpr ⟨hi, h.hi_mem_B⟩)).symm h3 h4
  have memB : ∀ y ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z,
      y ∈ part S c (P \ acc G S P c lo) := fun y hy => (mem_filter.mp hy).1
  by_cases hmov : ∃ X ∈ acc G S P c lo, X ≠ c z ∧ Movable G S c z X
  · obtain ⟨g, hg⟩ := getg y₀ (memB y₀ hy₀)
    exact case1 h hterm hzS hzT hy₀ hmov hg
  · rcases hcase with hX | ⟨y₁, hy₁, y₂, hy₂, hne12, hnadj⟩
    · exact absurd hX hmov
    · push Not at hmov
      obtain ⟨g, hg⟩ := getg y₁ (memB y₁ hy₁)
      obtain ⟨c', hi', hnear, hlt⟩ :=
        case2 h hterm hzS hzT (fun X hX hXz => hmov X hX hXz) hy₁ hy₂ hne12 hnadj hg
      have hle : (acc G S P c' lo).card ≤ P.card := card_le_card (filter_subset _ _)
      exact ih _ (by omega) c' hi' hnear rfl

open Classical in
/-- Existencia de una partición de `S` en clases de tamaño `s` indexadas por `P`. -/
theorem exists_equipartition (P : Finset ℕ) (s : ℕ) :
    ∀ S : Finset V, S.card = s * P.card → ∃ c : V → ℕ, Into S c P ∧
      ∀ i ∈ P, (cls S c i).card = s := by
  induction P using Finset.induction_on with
  | empty =>
    intro S hS
    refine ⟨fun _ => 0, fun v hv => ?_, fun i hi => absurd hi (notMem_empty i)⟩
    simp only [card_empty, mul_zero, card_eq_zero] at hS
    subst hS
    simp only [notMem_empty] at hv
  | insert a P ha ih =>
    intro S hS
    rw [card_insert_of_notMem ha, Nat.mul_succ] at hS
    obtain ⟨Tₐ, hTS, hTcard⟩ := exists_subset_card_eq (s := S) (n := s) (by omega)
    obtain ⟨c, hc, hcard⟩ := ih (S \ Tₐ) (by rw [card_sdiff_of_subset hTS]; omega)
    refine ⟨fun v => if v ∈ Tₐ then a else c v, fun v hv => ?_, fun i hi => ?_⟩
    · by_cases hvT : v ∈ Tₐ
      · simp [hvT]
      · simp only [hvT, ite_false]
        exact mem_insert_of_mem (hc v (mem_sdiff.mpr ⟨hv, hvT⟩))
    · rcases mem_insert.mp hi with rfl | hi
      · rw [← hTcard]
        congr 1
        ext v
        simp only [mem_cls]
        constructor
        · rintro ⟨hv, hva⟩
          by_contra hvT
          simp only [hvT, ite_false] at hva
          exact ha (hva ▸ hc v (mem_sdiff.mpr ⟨hv, hvT⟩))
        · intro hvT
          exact ⟨hTS hvT, by simp [hvT]⟩
      · rw [← hcard i hi]
        congr 1
        ext v
        simp only [mem_cls, mem_sdiff]
        constructor
        · rintro ⟨hv, hvi⟩
          have hvT : v ∉ Tₐ := by
            intro hvT
            simp only [hvT, ite_true] at hvi
            exact ha (hvi ▸ hi)
          simp only [hvT, ite_false] at hvi
          exact ⟨⟨hv, hvT⟩, hvi⟩
        · rintro ⟨⟨hv, hvT⟩, hvi⟩
          exact ⟨hv, by simp [hvT, hvi]⟩

open Classical in
/-- **Teorema 2.4** (forma divisible). -/
theorem core (n : ℕ) : ∀ (G : SimpleGraph V) (S : Finset V) (P : Finset ℕ) (r s : ℕ),
    edgeCount G S = n → P.card = r + 1 → S.card = s * (r + 1) → DegLe G S r →
    ∃ c, IsEq G S P c s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G S P r s hn hP hS hdeg
  by_cases h0 : n = 0
  · -- sin aristas: cualquier equipartición sirve
    obtain ⟨c, hc, hcard⟩ := exists_equipartition P s S (by rw [hS, hP])
    refine ⟨c, fun v hv w hw hadj => ?_, hc, hcard⟩
    exfalso
    have : (v, w) ∈ S.offDiag.filter fun p => G.Adj p.1 p.2 :=
      mem_filter.mpr ⟨mem_offDiag.mpr ⟨hv, hw, hadj.ne⟩, hadj⟩
    rw [edgeCount, h0] at hn
    rw [card_eq_zero.mp hn] at this
    exact notMem_empty _ this
  -- hay una arista `xy`
  obtain ⟨⟨x, y⟩, hxy⟩ : (S.offDiag.filter fun p => G.Adj p.1 p.2).Nonempty := by
    rw [← card_pos]; unfold edgeCount at hn; omega
  obtain ⟨hxyS, hadj⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy, -⟩ := mem_offDiag.mp hxyS
  obtain ⟨G', hG'⟩ : ∃ G' : SimpleGraph V, ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ s(a, b) ≠ s(x, y) :=
    ⟨{ Adj := fun a b => G.Adj a b ∧ s(a, b) ≠ s(x, y)
       symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
       loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }, fun _ _ => Iff.rfl⟩
  have hG'le : ∀ a b, G'.Adj a b → G.Adj a b := fun a b h => ((hG' a b).mp h).1
  have hG'adj : ∀ a b, G.Adj a b → s(a, b) ≠ s(x, y) → G'.Adj a b :=
    fun a b hab hne => (hG' a b).mpr ⟨hab, hne⟩
  -- menos aristas en `G'`
  have hlt : edgeCount G' S < edgeCount G S := by
    apply card_lt_card
    refine ⟨fun p hp => ?_, fun hsub => ?_⟩
    · obtain ⟨hp, hpadj⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hp, hG'le _ _ hpadj⟩
    · have := (mem_filter.mp (hsub hxy)).2
      exact ((hG' x y).mp this).2 rfl
  have hdeg' : DegLe G' S r := fun v hv =>
    le_trans (card_le_card fun w hw =>
      mem_nbr.mpr ⟨(mem_nbr.mp hw).1, hG'le _ _ (mem_nbr.mp hw).2⟩) (hdeg v hv)
  obtain ⟨f₀, hf₀⟩ := ih _ (hn ▸ hlt) G' S P r s rfl hP hS hdeg'
  -- hipótesis de inducción para subconjuntos (mismo grafo `G`)
  have IH : ∀ S' ⊆ S, edgeCount G S' < edgeCount G S → ∀ (P' : Finset ℕ) (r' : ℕ),
      P'.card = r' + 1 → S'.card = s * (r' + 1) → DegLe G S' r' → ∃ c, IsEq G S' P' c s :=
    fun S' _ hS' P' r' hP' hcard hdeg'' => ih _ (hn ▸ hS') G S' P' r' s rfl hP' hcard hdeg''
  by_cases hcol : f₀ x = f₀ y
  · -- `x` e `y` en la misma clase: mover `x` a una clase sin vecinos de `x`
    -- vecinos de `x` en colores distintos de `f₀ x`: a lo más `r - 1`
    set N := (nbr G S x).filter fun w => f₀ w ≠ f₀ x
    have hN : N.card + 1 ≤ r := by
      have hsub : insert y N ⊆ nbr G S x := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact mem_nbr.mpr ⟨hy, hadj⟩
        · exact (mem_filter.mp hw).1
      have hyN : y ∉ N := fun h => (mem_filter.mp h).2 hcol.symm
      have := card_le_card hsub
      rw [card_insert_of_notMem hyN] at this
      exact le_trans this (hdeg x hx)
    have hfree : ∃ j ∈ P.erase (f₀ x), ∀ w ∈ N, f₀ w ≠ j := by
      by_contra hno
      push Not at hno
      have hsub : P.erase (f₀ x) ⊆ N.image f₀ := by
        intro j hj
        obtain ⟨w, hw, hwj⟩ := hno j hj
        exact mem_image.mpr ⟨w, hw, hwj⟩
      have h1 := le_trans (card_le_card hsub) card_image_le
      rw [card_erase_of_mem (hf₀.into x hx), hP] at h1
      omega
    obtain ⟨j, hjP, hjfree⟩ := hfree
    obtain ⟨hjx, hjP⟩ := mem_erase.mp hjP
    have hmov : Movable G S f₀ x j := by
      intro w hw hxw
      rw [mem_cls] at hw
      exact hjfree w (mem_filter.mpr ⟨mem_nbr.mpr ⟨hw.1, hxw⟩, hw.2 ▸ hjx⟩) hw.2
    have hcx : f₀ x ≠ j := Ne.symm hjx
    have hproper : Proper G S (Function.update f₀ x j) := by
      have hp' : Proper G' S (Function.update f₀ x j) :=
        proper_update hf₀.proper fun w hw hxw => hmov w hw (hG'le _ _ hxw)
      intro a ha b hb hab
      by_cases he : s(a, b) = s(x, y)
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hab' : a ≠ b := hab.ne
          simp only [Function.update_self, Function.update_of_ne hab'.symm]
          rw [← hcol]; exact Ne.symm hcx
        · have hab' : a ≠ b := hab.ne
          simp only [Function.update_self, Function.update_of_ne hab']
          rw [← hcol]; exact hcx
      · exact hp' a ha b hb (hG'adj a b hab he)
    have hs1 : (cls S f₀ (f₀ x)).card = s := hf₀.card _ (hf₀.into x hx)
    have hnear : IsNear G S P (Function.update f₀ x j) s (f₀ x) j := by
      refine ⟨hproper, into_update hf₀.into hjP, hf₀.into x hx, hjP, hcx, ?_, ?_, ?_⟩
      · have h1 : (cls S (Function.update f₀ x j) (f₀ x)).card + 1 = (cls S f₀ (f₀ x)).card :=
          card_cls_update_old hx hcx
        omega
      · rw [card_cls_update_self hx hcx, hf₀.card j hjP]
      · intro i hi hix hij
        rw [cls_update_other hij hix, hf₀.card i hi]
    exact main_lemma IH hdeg hP _ j hnear
  · -- `f₀` ya es propia para `G`
    refine ⟨f₀, fun a ha b hb hab => ?_, hf₀.into, hf₀.card⟩
    by_cases he : s(a, b) = s(x, y)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcol
      · exact Ne.symm hcol
    · exact hf₀.proper a ha b hb (hG'adj a b hab he)

end HajnalSzemeredi

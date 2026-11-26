/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3b
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM09.Section5b
public import LeanPool.GraphMinor.GM09.Section6
public import LeanPool.GraphMinor.GM09.Section6b
import LeanPool.GraphMinor.GM09.Section7
import LeanPool.GraphMinor.GM09.Section10e
import Mathlib.Data.Set.Card

/-!
# The inductive step of (6.1) of Graph Minors IX

The proof of (6.1) shrinks a large transaction twice, each time getting rid of one peripheral
separating member. This file carries out that step (page 58): we list the paths in order starting
from a peripheral separating path `P₁`. If one of the next `p + 4` paths is non-separating we keep
it. Otherwise we use (5.5) to find a new non-separating path.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor

universe u v

variable {α : Type u} {β : Type v}

namespace Society

variable {S : Society α β}

theorem IsFenceFor.mono {F F' : Set (Graph α β)} {A B : Set α} (h : S.IsFenceFor F A B)
    (hsub : F' ⊆ F) : S.IsFenceFor F' A B :=
  ⟨⟨fun R hR => h.1.1 R (hsub hR), fun _ hR₁ _ hR₂ hne => h.1.2 (hsub hR₁) (hsub hR₂) hne⟩,
    h.2.1, fun R hR => h.2.2 R (hsub hR)⟩

theorem IsFenceFor.symm {F : Set (Graph α β)} {A B : Set α} (h : S.IsFenceFor F A B) :
    S.IsFenceFor F B A := by
  refine ⟨h.1, h.2.1.symm, fun R hR => ?_⟩
  obtain ⟨a, ha, b, hb, e⟩ := h.2.2 R hR
  exact ⟨b, hb, a, ha, IsOmegaPathWithEnds.symm S e⟩

/-- If a separating path `R` is peripheral in a set `next`, and an end of `next` lies in `Ω(a, b)`,
and every path of `F` not in `next` has an end in `Ω(a, b)`, then `R` is peripheral in `F`. The
reason is that a path of `F` with an end in `Ω(b, a)` and an end in `Ω(a, b)` would cross `R`. -/
theorem isPeripheralIn_of_next {F next : Set (Graph α β)} {R : Graph α β} {a b z : α}
    (hRF : R ∈ F) (hRn : R ∈ next) (hsep : S.IsSeparatingOmegaPath R)
    (hF : S.IsDisjointOmegaPathSet F) (hR : S.IsOmegaPathWithEnds R a b)
    (hz : z ∈ S.Ω.interval a b) (hzn : z ∈ S.transactionEnds next)
    (hoth : ∀ Q ∈ F, Q ∉ next → ∃ y ∈ S.Ω.interval a b, ∃ w, S.IsOmegaPathWithEnds Q y w)
    (hper : S.IsPeripheralIn next R) : S.IsPeripheralIn F R := by
  rcases (IsOmegaPathWithEnds.isPeripheralIn_iff S hRn hR).mp hper with h | h
  · exact (disjoint_left.mp h hz hzn).elim
  · refine (IsOmegaPathWithEnds.isPeripheralIn_iff S hRF hR).mpr (Or.inr ?_)
    rw [disjoint_left]
    rintro x hx ⟨Q, hQ, y, hQe⟩
    by_cases hQn : Q ∈ next
    · exact disjoint_left.mp h hx ⟨Q, hQn, y, hQe⟩
    obtain ⟨y', hy', w, hw⟩ := hoth Q hQ hQn
    have hne : Q ≠ R := fun h => hQn (h ▸ hRn)
    rcases IsOmegaPathWithEnds.ends_eq S hw hQe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact disjoint_left.mp (S.Ω.disjoint_interval_swap a b) hy' hx
    · refine hsep.2 ⟨Q, hF.2 hQ hRF hne, _, _, _, _, hw, hR, ?_⟩
      exact (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hy', hx⟩)).symm

/-- Inside the arc from `s` to `t`, with `w` outside it and `u` before `v`, the cut at `w` and `v`
is a fence with `u` and everything from `w` to `s` on one side, and `v` and everything from `t` to
`w` on the other. -/
theorem _root_.GraphMinor.GM09.CyclicPerm.exists_fence_of_arc {Ω : CyclicPerm α} {s t w u v : α}
    (hw : w ∈ Ω.interval t s) (hv : v = t ∨ v ∈ Ω.interval s t) (hu : u = s ∨ u ∈ Ω.interval s v)
    (hvbar : v ∈ Ω.bar) :
    Ω.IsFence (Ω.interval w v) ({w, v} ∪ Ω.interval v w) ∧ u ∈ Ω.interval w v ∧
      Ω.interval w s ⊆ Ω.interval w v ∧ Ω.interval t w ⊆ Ω.interval v w := by
  have ht : t ∈ Ω.interval s w := Ω.mem_interval_rotate_right hw
  have hv' : v ∈ Ω.interval s w := by
    rcases hv with rfl | hv
    · exact ht
    · exact Ω.interval_subset_interval_left ht hv
  have hs : s ∈ Ω.interval w v := Ω.mem_interval_rotate_right hv'
  have hne : w ≠ v := fun h => Ω.not_mem_interval_right s w (h ▸ hv')
  refine ⟨?_, ?_, Ω.interval_subset_interval_left hs, ?_⟩
  · have := (Ω.isFence_interval_compl hvbar hw.1.1 hne.symm).symm
    rwa [pair_comm] at this
  · rcases hu with rfl | hu
    · exact hs
    · exact Ω.interval_subset_interval_right hs hu
  · rcases hv with rfl | hv
    · exact Subset.rfl
    · have h4 : Ω.IsClockwise4 s v t w := Ω.isClockwise4_iff_interval.mpr ⟨hv, hw⟩
      exact Ω.interval_subset_interval_right
        (Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate h4)).1

/-- Two distinct points of the closed arc from `s` to `t`, listed so that the first comes before the
second. -/
theorem _root_.GraphMinor.GM09.CyclicPerm.exists_ordered_of_mem_arc {Ω : CyclicPerm α} {s t x y : α}
    (hx : x = s ∨ x = t ∨ x ∈ Ω.interval s t) (hy : y = s ∨ y = t ∨ y ∈ Ω.interval s t)
    (hst : s ≠ t) (hsbar : s ∈ Ω.bar) (hxy : x ≠ y) :
    ((x = s ∨ x ∈ Ω.interval s y) ∧ (y = t ∨ y ∈ Ω.interval s t)) ∨
      ((y = s ∨ y ∈ Ω.interval s x) ∧ (x = t ∨ x ∈ Ω.interval s t)) := by
  rcases hx with rfl | rfl | hx
  · rcases hy with rfl | rfl | hy
    · exact (hxy rfl).elim
    · exact Or.inl ⟨Or.inl rfl, Or.inl rfl⟩
    · exact Or.inl ⟨Or.inl rfl, Or.inr hy⟩
  · rcases hy with rfl | rfl | hy
    · exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
    · exact (hxy rfl).elim
    · exact Or.inr ⟨Or.inr hy, Or.inl rfl⟩
  · rcases hy with rfl | rfl | hy
    · exact Or.inr ⟨Or.inl rfl, Or.inr hx⟩
    · exact Or.inl ⟨Or.inr hx, Or.inl rfl⟩
    · have hne₁ : x ≠ s := hx.1.2 ∘ fun h => by simp [h]
      have hne₂ : y ≠ s := hy.1.2 ∘ fun h => by simp [h]
      rcases Ω.mem_interval_or_interval_swap hsbar hy.1.1 hx.1.1 hne₂.symm hne₁ hxy with h | h
      · exact Or.inl ⟨Or.inr h, Or.inr hy⟩
      · exact Or.inr ⟨Or.inr (Ω.mem_interval_rotate_right h), Or.inr hx⟩

theorem ncard_image_fin_ge {γ : Type*} {k : ℕ} {f : Fin k → γ} (hf : Injective f) (m : ℕ) :
    (f '' {i | m ≤ i.1}).ncard = k - m := by
  rw [ncard_image_of_injective _ hf]
  have h : {i : Fin k | m ≤ i.1} =
      range (fun i : Fin (k - m) => (⟨m + i.1, by have := i.2; omega⟩ : Fin k)) := by
    ext i
    simp only [mem_ofPred_eq, mem_range, Fin.ext_iff]
    constructor
    · intro hi
      exact ⟨⟨i.1 - m, by have := i.2; omega⟩, by simp; omega⟩
    · rintro ⟨j, hj⟩
      omega
  rw [h, ← image_univ, ncard_image_of_injective, ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  intro i j hij
  simp only [Fin.mk.injEq] at hij
  exact Fin.ext (by omega)

/-- A bijection of `Fin k` for which each of the first `n` points goes below everything after it
is the identity on those points. -/
theorem eq_self_of_lt_of_forall {k n : ℕ} {φ : Fin k → Fin k} (hinj : Injective φ)
    (hsurj : Surjective φ) (hlt : ∀ i j : Fin k, i.1 < n → i < j → φ i < φ j) :
    ∀ i : Fin k, i.1 < n → φ i = i := by
  have key : ∀ m (i : Fin k), i.1 = m → i.1 < n → φ i = i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi hin
      obtain ⟨j, hj⟩ := hsurj i
      rcases lt_trichotomy j i with hji | rfl | hij
      · have := ih j.1 (by rw [← hi]; exact hji) j rfl (lt_trans (show j.1 < i.1 from hji) hin)
        rw [this] at hj
        exact (hji.ne hj).elim
      · exact hj
      · have h₁ : φ i < i := hj ▸ hlt i j hin hij
        have h₂ := ih (φ i).1 (by rw [← hi]; exact h₁) (φ i) rfl (lt_trans h₁ hin)
        exact (h₁.ne (hinj h₂)).elim
  exact fun i hi => key i.1 i rfl hi

variable (S) in
/-- The paths of a transaction `F` of size `k`, listed in clockwise order of their ends: the first
ends in `L` are those on one side of a fence, with the path `R i` starting at the end number
`k - 1 - i`, and the second ends in the same list at `k`, `k + 1`, .... -/
structure IsEndEnumeration (F : Set (Graph α β)) {k : ℕ} (L : List α) (R : Fin k → Graph α β)
    (φ : Fin k → Fin k) : Prop where
  len : L.length = 2 * k
  cw : S.Ω.IsClockwiseSeq L
  ends_eq : {v | v ∈ L} = S.transactionEnds F
  inj : Injective R
  range_eq : range R = F
  φ_inj : Injective φ
  φ_surj : Surjective φ
  ends : ∀ i : Fin k, S.IsOmegaPathWithEnds (R i)
    (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega))

namespace IsEndEnumeration

variable {F : Set (Graph α β)} {k : ℕ} {L : List α} {R : Fin k → Graph α β} {φ : Fin k → Fin k}

/-- The first end at index `i`. -/
def endA (E : S.IsEndEnumeration F L R φ) (i : Fin k) : α :=
  L[k - 1 - i.1]'(by have := E.len; omega)

/-- The second end at index `i`. -/
def endB (E : S.IsEndEnumeration F L R φ) (i : Fin k) : α :=
  L[k + i.1]'(by have := E.len; omega)

theorem ends' (E : S.IsEndEnumeration F L R φ) (i : Fin k) :
    S.IsOmegaPathWithEnds (R i) (E.endA i) (E.endB (φ i)) := E.ends i

theorem mem (E : S.IsEndEnumeration F L R φ) (i : Fin k) : R i ∈ F :=
  E.range_eq ▸ ⟨i, rfl⟩

theorem exists_eq (E : S.IsEndEnumeration F L R φ) {Q : Graph α β} (hQ : Q ∈ F) :
    ∃ i, R i = Q := by
  have : Q ∈ range R := E.range_eq ▸ hQ
  exact this

theorem endA_mem (E : S.IsEndEnumeration F L R φ) {x i : Fin k} (hx : x < i) (c : Fin k) :
    E.endA x ∈ S.Ω.interval (E.endA i) (E.endB c) := by
  have := E.len
  exact S.Ω.mem_interval_of_lt E.cw (i₁ := k - 1 - i.1) (i₂ := k - 1 - x.1) (i₃ := k + c.1)
    (by have : x.1 < i.1 := hx; omega) (by omega) (by omega)

theorem endB_mem (E : S.IsEndEnumeration F L R φ) {c d : Fin k} (hcd : c < d) (i : Fin k) :
    E.endB c ∈ S.Ω.interval (E.endA i) (E.endB d) := by
  have := E.len
  exact S.Ω.mem_interval_of_lt E.cw (i₁ := k - 1 - i.1) (i₂ := k + c.1) (i₃ := k + d.1)
    (by omega) (by have : c.1 < d.1 := hcd; omega) (by omega)

theorem endB_mem_endB (E : S.IsEndEnumeration F L R φ) {c d e : Fin k} (hcd : c < d) (hde : d < e) :
    E.endB d ∈ S.Ω.interval (E.endB c) (E.endB e) := by
  have := E.len
  exact S.Ω.mem_interval_of_lt E.cw (i₁ := k + c.1) (i₂ := k + d.1) (i₃ := k + e.1)
    (by have : c.1 < d.1 := hcd; omega) (by have : d.1 < e.1 := hde; omega) (by omega)

/-- A separating path does not cross a path listed after it, so the second ends come in the same
order. -/
theorem φ_lt_of_separating (E : S.IsEndEnumeration F L R φ) (hF : S.IsDisjointOmegaPathSet F)
    {i j : Fin k} (hij : i < j) (hsep : S.IsSeparatingOmegaPath (R i)) : φ i < φ j := by
  by_contra hlt
  have hne : φ j ≠ φ i := fun h => hij.ne (E.φ_inj h).symm
  have hji : φ j < φ i := lt_of_le_of_ne (not_lt.mp hlt) hne
  have h₁ : E.endB (φ j) ∈ S.Ω.interval (E.endA i) (E.endB (φ i)) := E.endB_mem hji i
  have h₂ : E.endA i ∈ S.Ω.interval (E.endA j) (E.endB (φ i)) := E.endA_mem hij _
  have h₃ : E.endA j ∈ S.Ω.interval (E.endB (φ i)) (E.endA i) := S.Ω.mem_interval_rotate_right h₂
  have hcr := S.Ω.crosses_iff_interval.mpr (Or.inr ⟨h₁, h₃⟩)
  exact hsep.2 ⟨R j, hF.2 (E.mem j) (E.mem i) (fun h => hij.ne (E.inj h).symm), _, _, _, _,
    E.ends' j, E.ends' i, hcr.symm⟩

end IsEndEnumeration

/-- List a transaction in order, starting with a path `P₁` whose ends `a₁`, `b₁` are consecutive
among the ends of the transaction. -/
theorem exists_isEndEnumeration {F : Set (Graph α β)} {P₁ : Graph α β} {a₁ b₁ : α} {k : ℕ}
    (htrans : S.IsTransaction F) (hk : F.ncard = k) (hk₁ : 1 ≤ k) (hP₁ : P₁ ∈ F)
    (hends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (hgap : Disjoint (S.Ω.interval a₁ b₁) (S.transactionEnds F)) :
    ∃ (A B : Set α) (L : List α) (R : Fin k → Graph α β) (φ : Fin k → Fin k)
      (E : S.IsEndEnumeration F L R φ), S.IsFenceFor F A B ∧
        R ⟨0, by omega⟩ = P₁ ∧ φ ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
        E.endA ⟨0, by omega⟩ = a₁ ∧ E.endB ⟨0, by omega⟩ = b₁ := by
  classical
  obtain ⟨A, B, hF, haA, hbB⟩ : ∃ A B, S.IsFenceFor F A B ∧ a₁ ∈ A ∧ b₁ ∈ B := by
    obtain ⟨A, B, hF⟩ := htrans
    obtain ⟨a, ha, b, hb, e⟩ := hF.2.2 P₁ hP₁
    rcases IsOmegaPathWithEnds.ends_eq S hends e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨A, B, hF, ha, hb⟩
    · exact ⟨B, A, IsFenceFor.symm hF, hb, ha⟩
  obtain ⟨L, hlen, R, φ, hcw, hset, hinj, hsub, hφi, hφs, hRe, hLA, hLB, -⟩ :=
    S.exists_clockwise_enumeration hF hk hk₁
  have hrange : range R = F := by
    refine eq_of_subset_of_ncard_le hsub ?_ (hF.1.finite S)
    rw [← image_univ, ncard_image_of_injective _ hinj, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, hk]
  have E : S.IsEndEnumeration F L R φ :=
    ⟨hlen, hcw, hset, hinj, hrange, hφi, hφs, hRe⟩
  have hdisjAB := hF.2.1.2.2.1
  have ha_end : a₁ ∈ S.transactionEnds F := hends.mem_transactionEnds_left S hP₁
  have hb_end : b₁ ∈ S.transactionEnds F := hends.mem_transactionEnds_right S hP₁
  rw [← hset] at ha_end hb_end
  obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem ha_end
  obtain ⟨v, hv, rfl⟩ := List.getElem_of_mem hb_end
  have huk : u < k := by
    by_contra h
    exact disjoint_left.mp hdisjAB haA (hLB u hu (by omega))
  have hvk : k ≤ v := by
    by_contra h
    exact disjoint_left.mp hdisjAB (hLA v hv (by omega)) hbB
  have hmem : ∀ n (hn : n < L.length), L[n] ∈ S.transactionEnds F := fun n hn => by
    rw [← hset]
    exact List.getElem_mem hn
  have hu' : u = k - 1 := by
    by_contra hne
    have := S.Ω.mem_interval_of_lt hcw (i₁ := u) (i₂ := u + 1) (i₃ := v) (by omega) (by omega) hv
    exact disjoint_left.mp hgap this (hmem _ _)
  have hv' : v = k := by
    by_contra hne
    have := S.Ω.mem_interval_of_lt hcw (i₁ := u) (i₂ := k) (i₃ := v) (by omega) (by omega) hv
    exact disjoint_left.mp hgap this (hmem _ _)
  subst hv'
  have h0 := hRe ⟨0, by omega⟩
  have hR0 : R ⟨0, by omega⟩ = P₁ := by
    by_contra hne
    have hd := hF.1.2 (E.mem ⟨0, by omega⟩) hP₁ hne
    refine disjoint_left.mp hd h0.1.left_mem ?_
    have : L[v - 1 - (0 : ℕ)]'(by omega) = L[u] := by
      congr 1
      omega
    rw [this]
    exact hends.1.left_mem
  have he₁ : L[v - 1 - (0 : ℕ)]'(by omega) = L[u] := by
    congr 1
    omega
  refine ⟨A, B, L, R, φ, E, hF, hR0, ?_, he₁, rfl⟩
  rw [hR0, he₁] at h0
  rcases IsOmegaPathWithEnds.ends_eq S hends h0 with ⟨-, h⟩ | ⟨h, -⟩
  · have := (List.Nodup.getElem_inj_iff hcw.1).mp h
    exact Fin.ext (by simp; omega)
  · exact (hends.2.1 (by
      have h' := (List.Nodup.getElem_inj_iff hcw.1).mp h
      omega)).elim

/-- A path with non-adjacent ends in a loopless graph has another vertex. -/
theorem exists_inner_vertex {G P : Graph α β} {a b : α} (hP : IsGraphPathWithEnds G P a b)
    (hab : a ≠ b) (hloop : ∀ e x y, G.IsLink e x y → x ≠ y) (hno : ∀ e, ¬ G.IsLink e a b) :
    ∃ r ∈ V(P), r ≠ a ∧ r ≠ b := by
  obtain ⟨hle, W, -⟩ := hP
  cases W with
  | nil hv => exact (hab rfl).elim
  | cons hl rest =>
    rename_i x e
    have hxa : x ≠ a := (hloop _ _ _ (hl.mono hle)).symm
    refine ⟨x, hl.right_mem, hxa, ?_⟩
    rintro rfl
    exact hno _ (hl.mono hle)

/-- The first case of the step of (6.1): one of `P₂, …, P_{p+5}` is non-separating, and we keep it
together with `P_{p+6}, …`. -/
theorem statementSt_succ_case_nonSeparating {p t k : ℕ} {P_set P_t : Set (Graph α β)}
    {A B : Set α} {L : List α} {R : Fin k → Graph α β} {φ : Fin k → Fin k}
    (ht : t < 2) (E : S.IsEndEnumeration P_t L R φ) (hF : S.IsFenceFor P_t A B)
    (hcard_t : 3 * p + 8 - t * (p + 4) ≤ k) (hk : p + 5 ≤ k) {i₀ : Fin k} (hi₀ : i₀.1 = 0)
    (hper₀ : S.IsPeripheralIn P_t (R i₀)) (hsep₀ : S.IsSeparatingOmegaPath (R i₀))
    (hper_card :
      {P ∈ P_t | S.IsPeripheralIn P_t P ∧ S.IsSeparatingOmegaPath P}.ncard ≤ 2 - t)
    (hsep_mem : ∀ P ∈ P_t, S.IsSeparatingOmegaPath P → P ∈ P_set)
    (hper_sep : ∀ P ∈ P_t, S.IsPeripheralIn P_t P → S.IsSeparatingOmegaPath P →
      S.IsPeripheralIn P_set P)
    {j : Fin k} (hj₀ : j.1 ≠ 0) (hjp : j.1 < p + 5) (hj : S.IsNonSeparatingOmegaPath (R j)) :
    S.StatementSt p P_set (t + 1) := by
  have hrest_sub : R '' {i | p + 5 ≤ i.1} ⊆ P_t := by
    rintro _ ⟨i, -, rfl⟩
    exact E.mem i
  have hj_rest : R j ∉ R '' {i | p + 5 ≤ i.1} := by
    rintro ⟨i, hi, h⟩
    have : i = j := E.inj h
    have hi' : p + 5 ≤ i.1 := hi
    rw [this] at hi'
    omega
  have hsub_next : insert (R j) (R '' {i | p + 5 ≤ i.1}) ⊆ P_t :=
    insert_subset (E.mem j) hrest_sub
  have hfin : (R '' {i | p + 5 ≤ i.1}).Finite := (hF.1.finite S).subset hrest_sub
  refine S.statementSt_succ_of_nonSeparating_member ht ⟨A, B, hF⟩ (E.mem i₀) hper₀ hsep₀ hper_card
    hsep_mem hper_sep hsub_next ?_ (mem_insert _ _) hj ⟨A, B, IsFenceFor.mono hF hsub_next⟩ ?_ ?_
  · rintro (h | ⟨i, hi, h⟩)
    · exact hj₀ (by rw [← E.inj h]; exact hi₀)
    · have hi' : p + 5 ≤ i.1 := hi
      rw [E.inj h] at hi'
      omega
  · rw [ncard_insert_of_notMem hj_rest hfin, ncard_image_fin_ge E.inj,
      show (t + 1) * (p + 4) = t * (p + 4) + (p + 4) by ring]
    generalize t * (p + 4) = x at hcard_t ⊢
    omega
  · rintro Q (rfl | ⟨i, hi, rfl⟩) hper hsep
    · exact Or.inl rfl
    · have hi' : p + 5 ≤ i.1 := hi
      refine Or.inr (isPeripheralIn_of_next (E.mem i) (Or.inr ⟨i, hi, rfl⟩) hsep hF.1 (E.ends' i)
        (E.endA_mem (x := j) (Fin.lt_def.mpr (by omega)) _)
        ((E.ends' j).mem_transactionEnds_left S (mem_insert _ _)) ?_ hper)
      intro Q hQ hQn
      obtain ⟨m, rfl⟩ := E.exists_eq hQ
      have hm : m.1 < p + 5 := by
        by_contra hge
        exact hQn (Or.inr ⟨m, not_lt.mp hge, rfl⟩)
      exact ⟨_, E.endA_mem (Fin.lt_def.mpr (by omega)) _, _, E.ends' m⟩

private theorem pairedPrefixEnds (L : List α) {k m : ℕ} (hlen : L.length = 2 * k)
    (hm : m ≤ k) :
    (List.ofFn fun i : Fin m => L[k - 1 - i.1]'(by have := i.2; omega)).reverse ++
      (List.ofFn fun i : Fin m => L[k + i.1]'(by have := i.2; omega)) =
      (L.drop (k - m)).take (2 * m) := by
  apply List.ext_getElem
  · simp
    omega
  · intro n h₁ h₂
    rw [List.getElem_take, List.getElem_drop, List.getElem_append]
    split
    · rename_i hn
      simp only [List.length_reverse, List.length_ofFn] at hn
      rw [List.getElem_reverse, List.getElem_ofFn]
      simp only [List.length_ofFn]
      congr 1
      omega
    · rename_i hn
      simp only [List.length_reverse, List.length_ofFn] at hn
      rw [List.getElem_ofFn]
      simp only [List.length_reverse, List.length_ofFn]
      congr 1
      omega

/-- The second case of the step of (6.1): all of `P₁, …, P_{p+5}` are separating, and (5.5) gives a
non-separating path on the far side of `P_{p+5}`, which we add to `P_{p+6}, …`. -/
theorem statementSt_succ_case_replacement {p t k : ℕ} {P_set P_t : Set (Graph α β)}
    {A B : Set α} {L : List α} {R : Fin k → Graph α β} {φ : Fin k → Fin k}
    (hconn : S.IsInternallyKConnected 4) (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (ht : t < 2) (E : S.IsEndEnumeration P_t L R φ) (hF : S.IsFenceFor P_t A B)
    (hcard_t : 3 * p + 8 - t * (p + 4) ≤ k) (hk : p + 6 ≤ k) {i₀ : Fin k} (hi₀ : i₀.1 = 0)
    (hper₀ : S.IsPeripheralIn P_t (R i₀)) (hsep₀ : S.IsSeparatingOmegaPath (R i₀))
    (hper_card :
      {P ∈ P_t | S.IsPeripheralIn P_t P ∧ S.IsSeparatingOmegaPath P}.ncard ≤ 2 - t)
    (hsep_mem : ∀ P ∈ P_t, S.IsSeparatingOmegaPath P → P ∈ P_set)
    (hper_sep : ∀ P ∈ P_t, S.IsPeripheralIn P_t P → S.IsSeparatingOmegaPath P →
      S.IsPeripheralIn P_set P)
    (hall : ∀ i : Fin k, i.1 < p + 5 → S.IsSeparatingOmegaPath (R i))
    (hno_int : ∀ Q ∈ P_set, Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hempty : S.Ω.interval (E.endA i₀) (E.endB i₀) = ∅)
    (_hφ₀ : φ i₀ = i₀)
    (hind : S.G.induce V(R i₀) = R i₀)
    (hcatch : Catches (S.Ω.interval (E.endB i₀) (E.endA i₀)) (deleteVertices S.G V(R i₀)))
    (hloop : ∀ e x y, S.G.IsLink e x y → x ≠ y)
    (hno_gap : ∀ e, ¬ S.G.IsLink e (E.endA i₀) (E.endB i₀))
    (hext : ∀ (S₀ : Society α β) (r : α), S₀.G = S.G → r ∉ S.Ω.bar →
      S₀.Ω.bar = S.Ω.bar ∪ {r} → S₀.Ω.IsRestriction S.Ω.bar S.Ω →
      ∃ P₀ : Set (Graph α β), S₀.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    (hno_cr : ∀ P_c : Set (Graph α β), S.IsCrookedTransaction P_c → P_c.ncard ≠ p) :
    S.StatementSt p P_set (t + 1) := by
  classical
  have hφ : ∀ i : Fin k, i.1 < p + 5 → φ i = i := eq_self_of_lt_of_forall E.φ_inj E.φ_surj
    fun i j hi hij => E.φ_lt_of_separating hF.1 hij (hall i hi)
  have hφge : ∀ i : Fin k, p + 5 ≤ i.1 → p + 5 ≤ (φ i).1 := by
    intro i hi
    by_contra hlt
    have h := hφ (φ i) (by omega)
    rw [E.φ_inj h] at hlt
    omega
  have hends₀ : ∀ i : Fin k, i.1 < p + 5 → S.IsOmegaPathWithEnds (R i) (E.endA i) (E.endB i) := by
    intro i hi
    have := E.ends' i
    rwa [hφ i hi] at this
  have hint : ∀ i : Fin k, i.1 < p + 5 → Disjoint (pathInternalVerts S.G (R i)) S.Ω.bar :=
    fun i hi => hno_int _ (hsep_mem _ (E.mem i) (hall i hi))
  let m : Fin k := ⟨p + 4, by omega⟩
  have hm : m.1 < p + 5 := by simp [m]
  obtain ⟨G₁, G₂, _, hsep, hinter, hle₁, hab₁, hba₂, -⟩ :=
    S.exists_minimal_separation_of_separating (hends₀ m hm) (hall m hm) (hint m hm)
  -- The objects needed for (5.5).
  let ι : Fin (p + 5) → Fin k := fun i => ⟨i.1, by omega⟩
  have hι : Injective ι := fun i j h => Fin.ext (by simpa [ι] using h)
  have hi0 : ι 0 = i₀ := Fin.ext (by simp [ι, hi₀])
  have hιm : ι ⟨p + 4, by omega⟩ = m := rfl
  have hιlt : ∀ i, (ι i).1 < p + 5 := fun i => i.2
  have hr : ∃ r ∈ V(R i₀), r ≠ E.endA i₀ ∧ r ≠ E.endB i₀ :=
    exists_inner_vertex (hends₀ i₀ (by omega)).1 (hends₀ i₀ (by omega)).2.1 hloop hno_gap
  obtain ⟨r, hrV, hra, hrb⟩ := hr
  have hrbar : r ∉ S.Ω.bar := by
    intro h
    have hin : r ∈ V(R i₀) ∩ S.Ω.bar := ⟨hrV, h⟩
    rw [(hends₀ i₀ (by omega)).vertexSet_inter_bar_eq S (hint i₀ (by omega))] at hin
    rcases hin with h | h
    · exact hra h
    · exact hrb h
  have ha₀ : E.endA i₀ ∈ S.Ω.bar := (hends₀ i₀ (by omega)).2.2.1
  have hb₀ : E.endB i₀ ∈ S.Ω.bar := (hends₀ i₀ (by omega)).2.2.2
  obtain ⟨S₀, hG₀, hbar₀, hres₀, hcw₀⟩ := S.exists_extension ha₀ hb₀ (hends₀ i₀ (by omega)).2.1
    ((hends₀ i₀ (by omega)).1.1.vertexSet_mono hrV) hrbar hempty
  have hlist : (List.ofFn fun i => E.endA (ι i)).reverse ++ (List.ofFn fun i => E.endB (ι i)) =
      (L.drop (k - (p + 5))).take (2 * (p + 5)) := by
    simpa only [IsEndEnumeration.endA, IsEndEnumeration.endB, ι] using
      pairedPrefixEnds L E.len (m := p + 5) (by omega)
  have hcw : S.Ω.IsClockwiseSeq
      ((List.ofFn fun i => E.endA (ι i)).reverse ++ (List.ofFn fun i => E.endB (ι i))) := by
    rw [hlist]
    exact E.cw.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  have htr_Q : S.IsTransaction (range fun i => R (ι i)) := by
    refine ⟨A, B, IsFenceFor.mono hF ?_⟩
    rintro _ ⟨i, rfl⟩
    exact E.mem _
  have hcatches : Catches (S.Ω.bar \ {E.endA i₀, E.endB i₀}) (deleteVertices S.G V(R i₀)) := by
    have heq : S.Ω.bar \ {E.endA i₀, E.endB i₀} = S.Ω.interval (E.endB i₀) (E.endA i₀) := by
      ext x
      constructor
      · rintro ⟨hx, hne⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
        rcases S.Ω.mem_interval_or_interval_swap ha₀ hb₀ hx (hends₀ i₀ (by omega)).2.1 hne.1
          hne.2 with h | h
        · rw [hempty] at h
          exact h.elim
        · exact h
      · intro hx
        refine ⟨hx.1.1, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun h => S.Ω.not_mem_interval_right _ _ (h ▸ hx),
          fun h => S.Ω.not_mem_interval_left _ _ (h ▸ hx)⟩
    rw [heq]
    exact hcatch
  obtain ⟨-, P', hP'_nonsep, hP'_le⟩ := S.theorem_5_5_proof (S₀ := S₀) (p := p)
    (Q := fun i => R (ι i)) (a := fun i => E.endA (ι i)) (b := fun i => E.endB (ι i)) (r := r)
    hconn hp2 hp3 (E.inj.comp hι) htr_Q (fun i => hall _ (hιlt i)) (fun i => hint _ (hιlt i))
    (fun i => hends₀ _ (hιlt i)) hcw (by rw [hi0]; exact hempty)
    (by rw [hi0]; exact ⟨hrV, by simp [hra, hrb]⟩) hsep hinter hle₁ hab₁ hba₂ hG₀ hbar₀ hres₀
    (by rw [hi0]; exact hcw₀) (by rw [hi0]; exact hind) (by rw [hi0]; exact hcatches)
    (hext S₀ r hG₀ hrbar hbar₀ hres₀) hno_cr
  -- The paths after `P_{p+5}` lie on the second side.
  have hdisj : ∀ i : Fin k, p + 5 ≤ i.1 → Disjoint V(P') V(R i) := by
    intro i hi
    have hne : R i ≠ R m := fun h => by
      have := E.inj h
      rw [this] at hi
      simp [m] at hi
    have hav : Disjoint V(R i) (V(G₁) ∩ V(G₂)) := by
      rw [hinter]
      exact hF.1.2 (E.mem i) (E.mem m) hne
    have ha_in : E.endA i ∈ S.Ω.interval (E.endB m) (E.endA m) :=
      S.Ω.mem_interval_rotate_right (E.endA_mem (Fin.lt_def.mpr (by simp [m]; omega)) m)
    have hsubV : V(R i) ⊆ V(G₂) \ V(G₁) :=
      connected_subset_right_of_avoids_inter hsep (E.ends' i).1.1
        (E.ends' i).1.isGraphConnected hav ⟨E.endA i, (E.ends' i).1.left_mem, hba₂ ha_in⟩
    rw [disjoint_right]
    exact fun z hz hz' => (hsubV hz).2 (hP'_le.vertexSet_mono hz')
  obtain ⟨u, v, hPuv⟩ := hP'_nonsep.1
  have hm_ends := hends₀ m hm
  have harc : ∀ x, x ∈ V(G₁) → x ∈ S.Ω.bar →
      x = E.endA m ∨ x = E.endB m ∨ x ∈ S.Ω.interval (E.endA m) (E.endB m) := by
    intro x hx₁ hxb
    by_contra hcon
    simp only [not_or] at hcon
    rcases S.Ω.mem_interval_or_interval_swap hm_ends.2.2.1 hm_ends.2.2.2 hxb hm_ends.2.1 hcon.1
      hcon.2.1 with h | h
    · exact hcon.2.2 h
    · have hin : x ∈ V(R m) ∩ S.Ω.bar := ⟨hinter ▸ ⟨hx₁, hba₂ h⟩, hxb⟩
      rw [hm_ends.vertexSet_inter_bar_eq S (hint m hm)] at hin
      rcases hin with h' | h'
      · exact hcon.1 h'
      · exact hcon.2.1 h'
  have hord := CyclicPerm.exists_ordered_of_mem_arc
    (harc u (hP'_le.vertexSet_mono hPuv.1.left_mem) hPuv.2.2.1)
    (harc v (hP'_le.vertexSet_mono hPuv.1.right_mem) hPuv.2.2.2) hm_ends.2.1 hm_ends.2.2.1 hPuv.2.1
  obtain ⟨u', v', hPe, hu', hv'⟩ : ∃ u' v', S.IsOmegaPathWithEnds P' u' v' ∧
      (u' = E.endA m ∨ u' ∈ S.Ω.interval (E.endA m) v') ∧
      (v' = E.endB m ∨ v' ∈ S.Ω.interval (E.endA m) (E.endB m)) := by
    rcases hord with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨u, v, hPuv, h₁, h₂⟩
    · exact ⟨v, u, IsOmegaPathWithEnds.symm S hPuv, h₁, h₂⟩
  let last : Fin k := ⟨k - 1, by omega⟩
  have hmlast : m < last := Fin.lt_def.mpr (by simp [m, last]; omega)
  have hw : E.endB last ∈ S.Ω.interval (E.endB m) (E.endA m) :=
    S.Ω.mem_interval_rotate_left (E.endB_mem hmlast m)
  obtain ⟨hfence, huw, hA_sub, hB_sub⟩ := CyclicPerm.exists_fence_of_arc hw hv' hu' hPe.2.2.2
  have hrest_sub : R '' {i | p + 5 ≤ i.1} ⊆ P_t := by
    rintro _ ⟨i, -, rfl⟩
    exact E.mem i
  have hF' : S.IsFenceFor (insert P' (R '' {i | p + 5 ≤ i.1})) (S.Ω.interval (E.endB last) v')
      ({E.endB last, v'} ∪ S.Ω.interval v' (E.endB last)) := by
    refine ⟨⟨?_, ?_⟩, hfence, ?_⟩
    · rintro Q (rfl | ⟨i, -, rfl⟩)
      · exact ⟨_, _, hPe⟩
      · exact ⟨_, _, E.ends' i⟩
    · rintro Q₁ (rfl | ⟨i, hi, rfl⟩) Q₂ (rfl | ⟨j, hj, rfl⟩) hne
      · exact (hne rfl).elim
      · exact hdisj j hj
      · exact (hdisj i hi).symm
      · exact hF.1.2 (E.mem i) (E.mem j) hne
    · rintro Q (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨u', huw, v', Or.inl (Or.inr rfl), hPe⟩
      · have hi' : p + 5 ≤ i.1 := hi
        refine ⟨E.endA i, hA_sub (S.Ω.mem_interval_rotate_right
          (E.endA_mem (Fin.lt_def.mpr (by simp [m]; omega)) last)), E.endB (φ i), ?_, E.ends' i⟩
        have hφi := hφge i hi'
        by_cases hl : φ i = last
        · rw [hl]
          exact Or.inl (Or.inl rfl)
        · have hlt : φ i < last := by
            refine lt_of_le_of_ne ?_ hl
            exact Fin.le_def.mpr (by simp [last]; have := (φ i).2; omega)
          exact Or.inr (hB_sub (E.endB_mem_endB (Fin.lt_def.mpr (by simp [m]; omega)) hlt))
  have hP'_rest : P' ∉ R '' {i | p + 5 ≤ i.1} := by
    rintro ⟨i, hi, rfl⟩
    exact disjoint_left.mp (hdisj i hi) (E.ends' i).1.left_mem (E.ends' i).1.left_mem
  have hfin : (R '' {i | p + 5 ≤ i.1}).Finite := (hF.1.finite S).subset hrest_sub
  have hrest_diff : R '' {i | p + 5 ≤ i.1} ⊆ P_t \ {R i₀} := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨E.mem i, fun h => ?_⟩
    have hi' : p + 5 ≤ i.1 := hi
    rw [E.inj h] at hi'
    omega
  refine S.statementSt_succ_of_replacement_nonSeparating ht ⟨A, B, hF⟩ (E.mem i₀) hper₀ hsep₀
    hper_card hsep_mem hper_sep hrest_diff hP'_nonsep ⟨_, _, hF'⟩ ?_ ?_
  · rw [ncard_insert_of_notMem hP'_rest hfin, ncard_image_fin_ge E.inj,
      show (t + 1) * (p + 4) = t * (p + 4) + (p + 4) by ring]
    generalize t * (p + 4) = x at hcard_t ⊢
    omega
  · rintro Q (rfl | ⟨i, hi, rfl⟩) hper hsep
    · exact Or.inl rfl
    · have hi' : p + 5 ≤ i.1 := hi
      have hmi : m < i := Fin.lt_def.mpr (by simp [m]; omega)
      have hs_in : E.endA m ∈ S.Ω.interval (E.endA i) (E.endB (φ i)) := E.endA_mem hmi _
      have ht_in : E.endB m ∈ S.Ω.interval (E.endA i) (E.endB (φ i)) :=
        E.endB_mem (Fin.lt_def.mpr (by have := hφge i hi'; simp [m]; omega)) i
      have hu_in : u' ∈ S.Ω.interval (E.endA i) (E.endB (φ i)) := by
        have hsub : S.Ω.interval (E.endA m) (E.endB m) ⊆
            S.Ω.interval (E.endA i) (E.endB (φ i)) := fun z hz =>
          S.Ω.interval_subset_interval_left ht_in
            (S.Ω.interval_subset_interval_right (E.endA_mem hmi m) hz)
        rcases hu' with rfl | hu'
        · exact hs_in
        · rcases hv' with rfl | hv'
          · exact hsub hu'
          · exact hsub (S.Ω.interval_subset_interval_left hv' hu')
      refine Or.inr (isPeripheralIn_of_next (E.mem i) (Or.inr ⟨i, hi, rfl⟩) hsep hF.1 (E.ends' i)
        hu_in (hPe.mem_transactionEnds_left S (mem_insert _ _)) ?_ hper)
      intro Q hQ hQn
      obtain ⟨n, rfl⟩ := E.exists_eq hQ
      have hn : n.1 < p + 5 := by
        by_contra hge
        exact hQn (Or.inr ⟨n, not_lt.mp hge, rfl⟩)
      exact ⟨_, E.endA_mem (Fin.lt_def.mpr (by omega)) _, _, E.ends' n⟩

/-- The step `S_t → S_{t+1}` of (6.1) (page 58). The hypothesis `hc9` is (9) of that proof for the
transaction `P_set`, and `hext` says that adding one vertex to `Ω` gives a crooked transaction of
size `p`. -/
theorem statementSt_step {p t : ℕ} {P_set : Set (Graph α β)} (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hconn : S.IsInternallyKConnected 4) (ht : t < 2)
    (hloop : ∀ e x y, S.G.IsLink e x y → x ≠ y)
    (hbd : ∀ e a b, S.G.IsLink e a b → a ∈ S.Ω.bar → b ∈ S.Ω.bar → a ≠ b →
      S.Ω.interval a b ≠ ∅)
    (hno_int : ∀ Q ∈ P_set, Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hc9 : ∀ P ∈ P_set, S.IsSeparatingOmegaPath P → ∀ a b, S.IsOmegaPathWithEnds P a b →
      Disjoint (S.Ω.interval a b) (S.transactionEnds P_set) →
      S.Ω.interval a b = ∅ ∧ P = S.G.induce V(P) ∧
        Catches (S.Ω.interval b a) (deleteVertices S.G V(P)))
    (hext : ∀ (S₀ : Society α β) (r : α), S₀.G = S.G → r ∉ S.Ω.bar →
      S₀.Ω.bar = S.Ω.bar ∪ {r} → S₀.Ω.IsRestriction S.Ω.bar S.Ω →
      ∃ P₀ : Set (Graph α β), S₀.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    (hno_cr : ∀ P_c : Set (Graph α β), S.IsCrookedTransaction P_c → P_c.ncard ≠ p)
    (hSt : S.StatementSt p P_set t) : S.StatementSt p P_set (t + 1) := by
  refine S.statementSt_succ ht hSt fun P_t htrans hcard_t hper_card hsep_mem hper_sep hex => ?_
  obtain ⟨P₁, hin, hper, hsep⟩ := hex
  have hP₁ := hsep_mem P₁ hin hsep
  obtain ⟨a₁, b₁, hends, hgap⟩ : ∃ a₁ b₁, S.IsOmegaPathWithEnds P₁ a₁ b₁ ∧
      Disjoint (S.Ω.interval a₁ b₁) (S.transactionEnds P_set) := by
    obtain ⟨-, a, b, e, hd | hd⟩ := hper_sep P₁ hin hper hsep
    · exact ⟨a, b, e, hd⟩
    · exact ⟨b, a, IsOmegaPathWithEnds.symm S e, hd⟩
  obtain ⟨hemp, hind, hcatch⟩ := hc9 P₁ hP₁ hsep a₁ b₁ hends hgap
  have hk : 2 * p + 4 ≤ P_t.ncard := by
    interval_cases t <;> omega
  obtain ⟨A, B, L, R, φ, E, hF, hR0, hφ0, hA0, hB0⟩ :=
    S.exists_isEndEnumeration htrans rfl (by omega) hin hends (by rw [hemp]; exact empty_disjoint _)
  by_cases hall : ∀ i : Fin P_t.ncard, i.1 < p + 5 → S.IsSeparatingOmegaPath (R i)
  · refine S.statementSt_succ_case_replacement hconn hp2 hp3 ht E hF hcard_t (by omega)
      (i₀ := ⟨0, by omega⟩) rfl (hR0 ▸ hper) (hR0 ▸ hsep) hper_card hsep_mem hper_sep hall hno_int
      (by rw [hA0, hB0]; exact hemp) hφ0 ?_ ?_ hloop ?_ hext hno_cr
    · rw [hR0]
      exact hind.symm
    · rw [hA0, hB0, hR0]
      exact hcatch
    · rw [hA0, hB0]
      exact fun e hl => hbd e _ _ hl hends.2.2.1 hends.2.2.2 hends.2.1 hemp
  · push Not at hall
    obtain ⟨j, hjp, hjn⟩ := hall
    have hj₀ : j.1 ≠ 0 := by
      intro h
      have : j = ⟨0, by omega⟩ := Fin.ext h
      rw [this, hR0] at hjn
      exact hjn hsep
    have hω : S.IsOmegaPath (R j) := hF.1.1 _ (E.mem j)
    have hnon : S.IsNonSeparatingOmegaPath (R j) := by
      refine ⟨hω, ?_⟩
      by_contra hcr
      exact hjn ⟨hω, hcr⟩
    exact S.statementSt_succ_case_nonSeparating ht E hF hcard_t (by omega) (i₀ := ⟨0, by omega⟩) rfl
      (hR0 ▸ hper) (hR0 ▸ hsep) hper_card hsep_mem hper_sep hj₀ hjp hnon

/-- The quantity that drops in the proof of (6.1): deleting an edge or a vertex of `ΩBar` lowers its
first part, and adding a vertex to `Ω` lowers its second part. -/
noncomputable def sixOneMeasure (S : Society α β) : ℕ :=
  2 * (V(S.G).ncard + E(S.G).ncard) + (V(S.G) \ S.Ω.bar).ncard

theorem sixOneMeasure_deleteEdge {e : β} (he : e ∈ E(S.G)) :
    sixOneMeasure (S.deleteEdge e) < sixOneMeasure S := by
  have h := ncard_deleteEdge (S := S) he
  have hV : V((S.deleteEdge e).G) \ (S.deleteEdge e).Ω.bar = V(S.G) \ S.Ω.bar := by
    rw [vertexSet_deleteEdge]
    rfl
  unfold sixOneMeasure
  rw [hV]
  omega

theorem sixOneMeasure_deleteBarVertex {v : α} (hv : v ∈ S.Ω.bar)
    (hno : ∀ e x, ¬ S.G.IsLink e v x) :
    sixOneMeasure (S.deleteBarVertex v) < sixOneMeasure S := by
  have h := ncard_deleteBarVertex hv hno
  have hV : V((S.deleteBarVertex v).G) \ (S.deleteBarVertex v).Ω.bar = V(S.G) \ S.Ω.bar := by
    rw [vertexSet_deleteBarVertex]
    change _ \ (S.Ω.restrict (S.Ω.bar \ {v}) sdiff_subset).bar = _
    rw [S.Ω.restrict_bar]
    ext x
    simp only [mem_sdiff, mem_singleton_iff, not_and, not_not]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨h₁, fun hx => h₂ (h₃ hx)⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨h₁, fun hx => h₂ (hx ▸ hv)⟩, fun hx => (h₂ hx).elim⟩
  unfold sixOneMeasure
  rw [hV]
  omega

theorem sixOneMeasure_extension {S₀ : Society α β} {r : α} (hG : S₀.G = S.G) (hr : r ∉ S.Ω.bar)
    (hbar : S₀.Ω.bar = S.Ω.bar ∪ {r}) : sixOneMeasure S₀ < sixOneMeasure S := by
  have hrV : r ∈ V(S.G) := hG ▸ S₀.bar_subset (hbar ▸ Or.inr rfl)
  have hsub : V(S.G) \ S₀.Ω.bar ⊂ V(S.G) \ S.Ω.bar := by
    refine ⟨fun x hx => ⟨hx.1, fun h => hx.2 (hbar ▸ Or.inl h)⟩, fun h => ?_⟩
    exact (h ⟨hrV, hr⟩).2 (hbar ▸ Or.inr rfl)
  have := ncard_lt_ncard hsub (S.finite_V.subset sdiff_subset)
  unfold sixOneMeasure
  rw [hG]
  omega

/-- **Graph Minors IX, (6.1)** (page 55): the sophistication bound as a statement about
`HasSophisticationLE`, by induction on `sixOneMeasure`. -/
theorem hasSophisticationLE_of_no_crooked {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p ≠ 3) :
    ∀ (n : ℕ) (S : Society α β), sixOneMeasure S = n → S.IsKConnected 3 →
      S.IsInternallyKConnected 4 →
      (∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) →
      S.HasSophisticationLE (3 * p + 7) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hconn3 hconn4 hno_cr
    subst hn
    by_contra hns
    -- Deleting an edge which leaves the connectivity alone would finish the proof.
    have hdel : ∀ {e : β} {u w : α}, S.G.IsLink e u w →
        (∀ G₁ G₂, (S.deleteEdge e).IsSocietySeparation G₁ G₂ →
          (u ∈ V(G₁) ∧ w ∈ V(G₁)) ∨ (u ∈ V(G₂) ∧ w ∈ V(G₂))) →
        (S.deleteEdge e).HasSophisticationLE (3 * p + 7) := by
      intro e u w hl hside
      obtain ⟨h₁, h₂⟩ := connected_deleteEdge hl hconn3 hconn4 hside
      exact ih _ (sixOneMeasure_deleteEdge hl.edge_mem) _ rfl h₁ h₂
        fun P hP => hno_cr P hP.of_deleteEdge
    -- (1): the graph is simple.
    have hloop : ∀ e x y, S.G.IsLink e x y → x ≠ y := by
      rintro e x y hl rfl
      exact hns (hasSophisticationLE_of_deleteEdge_loop hl
        (hdel hl fun _ _ hs => side_of_redundant hl (Or.inl rfl) hs))
    have hpar : ∀ e f x y, S.G.IsLink e x y → S.G.IsLink f x y → e = f := by
      intro e f x y he hf
      by_contra hne
      have hne' : f ≠ e := Ne.symm hne
      exact hns (hasSophisticationLE_of_deleteEdge_parallel he hne' hf (hloop _ _ _ he)
        (hdel he fun _ _ hs => side_of_redundant he (Or.inr ⟨f, hne', hf⟩) hs))
    have hsimple : IsSimpleGraph S.G :=
      ⟨fun e _ x hl => hloop e x x hl rfl, fun e he f hf x y h₁ h₂ => hpar e f x y h₁ h₂⟩
    -- (2): every vertex of `ΩBar` has a neighbour.
    have hno_iso : ∀ v ∈ S.Ω.bar, ∃ u : α, S.G.Adj v u := by
      intro v hv
      by_contra hcon
      have hno : ∀ e x, ¬ S.G.IsLink e v x := fun e x hl => hcon ⟨x, e, hl⟩
      obtain ⟨h₁, h₂⟩ := connected_deleteBarVertex hv hno hconn3 hconn4
      exact hns (hasSophisticationLE_of_deleteBarVertex hv hno
        (ih _ (sixOneMeasure_deleteBarVertex hv hno) _ rfl h₁ h₂
          fun P hP => hno_cr P hP.of_deleteBarVertex))
    -- (4): no edge joins two consecutive vertices of `Ω`.
    have hbd : ∀ e a b, S.G.IsLink e a b → a ∈ S.Ω.bar → b ∈ S.Ω.bar → a ≠ b →
        S.Ω.interval a b ≠ ∅ := by
      intro e a b hl ha hb hab hgap
      exact hns (hasSophisticationLE_of_deleteEdge_boundary hl ha hb hab hgap
        (hdel hl fun _ _ hs => Or.inr ⟨hs.2 ha, hs.2 hb⟩))
    -- A transaction of size `3p + 8` exists.
    have hex : ∃ P₀ : Set (Graph α β), S.IsTransaction P₀ ∧ P₀.ncard = 3 * p + 8 := by
      by_contra hcon
      refine hns (hasSophisticationLE_of_forall_le S fun F hF => ?_)
      by_contra hlt
      obtain ⟨F', hF', hc⟩ := Set.exists_subset_card_eq (s := F) (n := 3 * p + 8) (by omega)
      obtain ⟨A, B, hf⟩ := hF
      exact hcon ⟨F', ⟨A, B, IsFenceFor.mono hf hF'⟩, hc⟩
    obtain ⟨P_set, htrans, hcard, hno_int, hmax⟩ :=
      S.exists_transaction_with_max_coveredComponentUnion hex
    have hc9 : ∀ P ∈ P_set, S.IsSeparatingOmegaPath P → ∀ a b, S.IsOmegaPathWithEnds P a b →
        Disjoint (S.Ω.interval a b) (S.transactionEnds P_set) →
        S.Ω.interval a b = ∅ ∧ P = S.G.induce V(P) ∧
          Catches (S.Ω.interval b a) (deleteVertices S.G V(P)) :=
      fun P hP hsep a b hab hd => S.lemma_6_1_claim_9 hp2 hconn3 hno_cr hsimple hno_iso
        htrans hcard hno_int hmax hP hsep hab hd
    -- Adding a vertex to `Ω` gives a society to which the induction applies.
    have hext : ∀ (S₀ : Society α β) (r : α), S₀.G = S.G → r ∉ S.Ω.bar →
        S₀.Ω.bar = S.Ω.bar ∪ {r} → S₀.Ω.IsRestriction S.Ω.bar S.Ω →
        ∃ P₀ : Set (Graph α β), S₀.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard := by
      intro S₀ r hG hr hbar hres
      by_contra hcon
      have hsub : S.Ω.bar ⊆ S₀.Ω.bar := hbar ▸ subset_union_left
      obtain ⟨h₁, h₂⟩ := connected_of_extension hG hsub hconn3 hconn4
      refine hns (HasSophisticationLE.of_extension hG hsub hres
        (ih _ (sixOneMeasure_extension hG hr hbar) _ rfl h₁ h₂ fun P hP hc => ?_))
      exact hcon ⟨P, hP, hc.ge⟩
    have hS₂ : S.StatementSt p P_set 2 :=
      S.statementSt_two htrans hcard fun t ht h =>
        statementSt_step hp2 hp3 hconn4 ht hloop hbd hno_int hc9 hext hno_cr h
    obtain ⟨P_set', hcr', hcard'⟩ := S.exists_crooked_of_statementSt_two hp2 hp3 hS₂
    exact hno_cr P_set' hcr' hcard'

/-- **Graph Minors IX, (6.1)** (page 55):
"Let $p \ge 2$ be an integer with $p \ne 3$, and let $(G, \Omega)$ be a 3-connected,
internally 4-connected society, in which there is no crooked transaction of cardinality $p$.
Then the sophistication of $(G, \Omega)$ is at most $3p + 7$." -/
theorem theorem_6_1_proof {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hconn3 : S.IsKConnected 3)
    (hconn4 : S.IsInternallyKConnected 4)
    (hno_crooked : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) :
    S.HasSophisticationLE (3 * p + 7) ∧ S.sophistication ≤ 3 * p + 7 := by
  have h := hasSophisticationLE_of_no_crooked hp2 hp3 _ S rfl hconn3 hconn4 hno_crooked
  exact ⟨h, Nat.sInf_le h⟩

end Society

export Society (theorem_6_1_proof)

end GraphMinor.GM09

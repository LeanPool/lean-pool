/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordSurface
public import LeanPool.GraphMinor.Surface.Dihedral

/-!
# Cutting a word

Let `W` be a word and `L` a set of labels. The word `cutW W L` gives each side with a label in `L` a
label of its own, so
these sides are no longer pasted. It presents the surface cut along the sides with labels in `L`.

To see what happens at a corner, we use the *ends of sides* `SE W`. Crossing a corner of a polygon
(`twn`) and crossing a
pasted side (`prtL`) are involutions of the ends of sides, and the first one has no fixed point. So
the results of
`Dihedral.lean` apply, and `corner_cut` tells which corners stay pasted.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

variable {W : ℕ → List Letter} {L : Set ℕ}

open Classical in
/-- The letter at the position `p` of the word `i` after cutting. -/
noncomputable def cutL (L : Set ℕ) (i p : ℕ) (l : Letter) : Letter :=
  if l.1 ∈ L then (2 * Nat.pair i p + 1, l.2) else (2 * l.1, l.2)

/-- The cut word. -/
noncomputable def cutW (W : ℕ → List Letter) (L : Set ℕ) (i : ℕ) : List Letter := (W i).mapIdx
  (cutL L i)

theorem cutW_length (i : ℕ) : (cutW W L i).length = (W i).length := List.length_mapIdx ..

theorem cutW_get (i p : ℕ) : (cutW W L i)[p]? = ((W i)[p]?).map (cutL L i p) := by
  simp [cutW, List.getElem?_mapIdx]

theorem spt_cut (i p : ℕ) (u : ℝ) : spt (cutW W L) i p u = spt W i p u := by
  simp [spt, cutW_length]

theorem cutW_eq_nil (i : ℕ) : cutW W L i = [] ↔ W i = [] := by
  rw [← List.length_eq_zero_iff, cutW_length, List.length_eq_zero_iff]

theorem dsk_cut : Dsk (cutW W L) = Dsk W := by
  ext a
  simp [Dsk, cutW_eq_nil]

theorem finW_cut (h : FinW W) : FinW (cutW W L) := by
  refine Set.Finite.subset h fun i hi => ?_
  exact fun he => hi ((cutW_eq_nil i).mpr he)

theorem cut_get_iff {i p k' : ℕ} {e : Bool} : (cutW W L i)[p]? = some (k', e) ↔
    ∃ k, (W i)[p]? = some (k, e) ∧ ((k ∈ L ∧ k' = 2 * Nat.pair i p + 1) ∨ (k ∉ L ∧ k' = 2 * k))
      := by
  classical
  rw [cutW_get, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨k, e'⟩, h1, h2⟩
    by_cases hk : k ∈ L
    · simp only [cutL, hk, ite_true, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨k, h1, .inl ⟨hk, rfl⟩⟩
    · simp only [cutL, hk, ite_false, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨k, h1, .inr ⟨hk, rfl⟩⟩
  · rintro ⟨k, h1, ⟨hk, rfl⟩ | ⟨hk, rfl⟩⟩
    · exact ⟨_, h1, by simp [cutL, hk]⟩
    · exact ⟨_, h1, by simp [cutL, hk]⟩

theorem isPaired_cut (hP : IsPaired W) : IsPaired (cutW W L) := by
  intro k'
  rcases Nat.even_or_odd' k' with ⟨m, rfl | rfl⟩
  · refine (encard_le_encard ?_).trans (hP m)
    rintro s ⟨e, he⟩
    obtain ⟨k, h1, ⟨-, h2⟩ | ⟨-, h2⟩⟩ := cut_get_iff.mp he
    · omega
    · have : k = m := by omega
      subst this
      exact ⟨e, h1⟩
  · have hsub : {s : ℕ × ℕ | ∃ e, (cutW W L s.1)[s.2]? = some (2 * m + 1, e)} ⊆ {Nat.unpair m} := by
      rintro ⟨i, p⟩ ⟨e, he⟩
      simp only at he
      obtain ⟨k, h1, ⟨-, h2⟩ | ⟨-, h2⟩⟩ := cut_get_iff.mp he
      · have h3 : Nat.pair i p = m := by omega
        rw [mem_singleton_iff, ← h3, Nat.unpair_pair]
      · omega
    refine (encard_le_encard hsub).trans ?_
    rw [encard_singleton]
    norm_num

/-- A step of the cut word is a step of the word along a side that is not cut. -/
theorem stp_of_cut {a b : ℕ × ℂ} (h : Stp (cutW W L) a b) : ∃ (i j p q k : ℕ) (e e' : Bool) (u : ℝ),
    (W i)[p]? = some (k, e) ∧ (W j)[q]? = some (k, e') ∧ (i, p) ≠ (j, q) ∧ u ∈ Icc (0 : ℝ) 1
      ∧ k ∉ L ∧
      a = spt W i p u ∧ b = spt W j q (flp e e' u) := by
  obtain ⟨i, j, p, q, k', e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp h
  obtain ⟨k, h4, h5⟩ := cut_get_iff.mp h1
  obtain ⟨l, h6, h7⟩ := cut_get_iff.mp h2
  rw [spt_cut, spt_cut]
  rcases h5 with ⟨-, h5⟩ | ⟨h8, h5⟩ <;> rcases h7 with ⟨-, h7⟩ | ⟨h9, h7⟩
  · have h9 : Nat.pair i p = Nat.pair j q := by omega
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp h9
    exact absurd rfl h3
  · omega
  · omega
  · have : k = l := by omega
    subst this
    exact ⟨i, j, p, q, k, e, e', u, h4, h6, h3, hu, h8, rfl, rfl⟩

theorem stp_to_cut {i j p q k : ℕ} {e e' : Bool} {u : ℝ} (h1 : (W i)[p]? = some (k, e)) (h2 :
  (W j)[q]? = some (k, e'))
    (h3 : (i, p) ≠ (j, q)) (hu : u ∈ Icc (0 : ℝ) 1) (hk : k ∉ L) :
    Stp (cutW W L) (spt W i p u) (spt W j q (flp e e' u)) := by
  rw [← spt_cut (L := L), ← spt_cut (L := L) j]
  exact stp_iff.mpr ⟨i, j, p, q, 2 * k, e, e', u, cut_get_iff.mpr ⟨k, h1, .inr ⟨hk, rfl⟩⟩,
    cut_get_iff.mpr ⟨k, h2, .inr ⟨hk, rfl⟩⟩, h3, hu, rfl, rfl⟩

theorem stp_of_stp_cut {a b : ℕ × ℂ} (h : Stp (cutW W L) a b) : Stp W a b := by
  obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, -, rfl, rfl⟩ := stp_of_cut h
  exact stp_iff.mpr ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩

theorem prel_of_prel_cut {a b : ℕ × ℂ} (h : PRel (cutW W L) a b) : PRel W a b := by
  induction h with
  | rel _ _ h => exact .rel _ _ (stp_of_stp_cut h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2

theorem prel_cut_empty {a b : ℕ × ℂ} (h : PRel W a b) : PRel (cutW W ∅) a b := by
  induction h with
  | rel _ _ h =>
    obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp h
    exact .rel _ _ (stp_to_cut h1 h2 h3 hu (notMem_empty k))
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2

/-- A side with a label in `L` is free after cutting. -/
theorem freeSide_cut {i p k : ℕ} {e : Bool} (h : (W i)[p]? = some (k, e)) (hk : k ∈ L) : FreeSide
  (cutW W L) i p := by
  intro j q k' e₁ e₂ h1 h2
  obtain ⟨l, h3, h4⟩ := cut_get_iff.mp h1
  obtain ⟨l', h5, h6⟩ := cut_get_iff.mp h2
  have : l = k := by
    rw [h] at h3
    simpa using (congrArg (Option.map Prod.fst) h3).symm
  subst this
  rcases h4 with ⟨-, h4⟩ | ⟨h7, -⟩
  · rcases h6 with ⟨-, h6⟩ | ⟨-, h6⟩
    · have h9 : Nat.pair i p = Nat.pair j q := by omega
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp h9
      rfl
    · omega
  · exact absurd hk h7

theorem freeSide_of_cut {i p : ℕ} (h : FreeSide W i p) : FreeSide (cutW W L) i p := by
  intro j q k' e₁ e₂ h1 h2
  obtain ⟨l, h3, h4⟩ := cut_get_iff.mp h1
  obtain ⟨l', h5, h6⟩ := cut_get_iff.mp h2
  rcases h4 with ⟨-, h4⟩ | ⟨-, h4⟩ <;> rcases h6 with ⟨-, h6⟩ | ⟨-, h6⟩
  · have h9 : Nat.pair i p = Nat.pair j q := by omega
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp h9
    rfl
  · omega
  · omega
  · have : l = l' := by omega
    subst this
    exact h j q l _ _ h3 h5

/-! ## Ends of sides -/

/-- An end of a side: `true` is the end with offset one. -/
abbrev SE (W : ℕ → List Letter) : Type := {g : ℕ × ℕ × Bool // g.2.1 < (W g.1).length}

theorem finite_se (hW : FinW W) : Finite (SE W) := by
  have h := finite_sides hW
  have : Finite {x : ℕ × ℕ | ∃ l, (W x.1)[x.2]? = some l} := h
  refine Finite.of_injective (β := {x : ℕ × ℕ | ∃ l, (W x.1)[x.2]? = some l} × Bool)
    (fun g => (⟨(g.1.1, g.1.2.1), _, List.getElem?_eq_getElem g.2⟩, g.1.2.2)) ?_
  rintro ⟨⟨i, p, b⟩, h1⟩ ⟨⟨i', p', b'⟩, h2⟩ he
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
  rfl

/-- The offset of an end. -/
noncomputable def eo (b : Bool) : ℝ := if b then 1 else 0

theorem eo_mem (b : Bool) : eo b ∈ Icc (0 : ℝ) 1 := by
  cases b <;> simp [eo]

/-- The point of an end. -/
noncomputable def spe (W : ℕ → List Letter) (g : SE W) : ℕ × ℂ := spt W g.1.1 g.1.2.1 (eo g.1.2.2)

/-- The next position. -/
def nxt (n p : ℕ) : ℕ := if p + 1 = n then 0 else p + 1

/-- The position before. -/
def prv (n p : ℕ) : ℕ := if p = 0 then n - 1 else p - 1

/-- Crossing the corner at an end. -/
def twn (W : ℕ → List Letter) (g : SE W) : SE W :=
  ⟨(g.1.1, if g.1.2.2 then nxt (W g.1.1).length g.1.2.1 else prv (W g.1.1).length g.1.2.1,
    !g.1.2.2), by
    obtain ⟨⟨i, p, b⟩, h⟩ := g
    simp only at h ⊢
    cases b <;> simp only [nxt, prv, ite_true, Bool.false_eq_true, ite_false] <;> split_ifs
      <;> omega⟩

theorem twn_ne (g : SE W) : twn W g ≠ g := by
  obtain ⟨⟨i, p, b⟩, h⟩ := g
  intro he
  have := congrArg (fun x : SE W => x.1.2.2) he
  cases b <;> simp [twn] at this

theorem twn_invol : Function.Involutive (twn W) := by
  rintro ⟨⟨i, p, b⟩, h⟩
  replace h : p < (W i).length := h
  apply Subtype.ext
  have h1 : nxt (W i).length (prv (W i).length p) = p := by
    by_cases hp : p = 0
    · subst hp
      simp only [nxt, prv, ite_true]
      rw [ite_eq_left (by omega)]
    · simp only [nxt, prv, ite_eq_right hp]
      rw [ite_eq_right (by omega)]
      omega
  have h2 : prv (W i).length (nxt (W i).length p) = p := by
    by_cases hp : p + 1 = (W i).length
    · simp only [nxt, prv, ite_eq_left hp, ite_true]
      omega
    · simp only [nxt, prv, ite_eq_right hp, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
  cases b
  · change (i, nxt (W i).length (prv (W i).length p), false) = (i, p, false)
    rw [h1]
  · change (i, prv (W i).length (nxt (W i).length p), true) = (i, p, true)
    rw [h2]

theorem per_card (n : ℕ) (hn : 0 < n) : per n n = per n 0 := by
  have := per_add_self (m := n) hn.ne' 0
  simpa using this

theorem spe_twn (g : SE W) : spe W (twn W g) = spe W g := by
  obtain ⟨⟨i, p, b⟩, h⟩ := g
  simp only at h
  have hn : 0 < (W i).length := by omega
  cases b
  · simp only [spe, twn, spt, eo, Bool.not_false, ite_true, Bool.false_eq_true, ite_false, prv,
    Prod.mk.injEq, true_and]
    split_ifs with h1
    · subst h1
      have : ((W i).length - 1 : ℕ) + (1 : ℝ) = (W i).length := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [this, per_card _ hn]
      simp
    · have : ((p - 1 : ℕ) : ℝ) + 1 = p := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [this]
      simp
  · simp only [spe, twn, spt, eo, Bool.not_true, ite_true, Bool.false_eq_true, ite_false, nxt,
    Prod.mk.injEq, true_and]
    split_ifs with h1
    · have : (p : ℝ) + 1 = (W i).length := by exact_mod_cast h1
      rw [this, per_card _ hn]
      simp
    · push_cast
      simp

/-- Two ends at the same point are equal or are the two ends of a corner. -/
theorem same_corner {g h : SE W} (he : spe W g = spe W h) : h = g ∨ h = twn W g := by
  obtain ⟨⟨i, p, b⟩, hp⟩ := g
  obtain ⟨⟨j, q, b'⟩, hq⟩ := h
  simp only at hp hq
  have hij : i = j := congrArg Prod.fst he
  subst hij
  have h2 : per (W i).length (p + eo b) = per (W i).length (q + eo b') := congrArg Prod.snd he
  have hn : 0 < (W i).length := by omega
  obtain ⟨m, hm⟩ := per_eq hn h2
  set n := (W i).length with hndef
  have hbd : ∀ x : ℤ, -n ≤ x → x ≤ n → x = m * n → x = 0 ∨ x = n ∨ x = -n := by
    intro x h1 h3 h4
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have h5 : m = 0 ∨ m = 1 ∨ m = -1 := by
      have h6 : m < 2 := by
        by_contra hc
        have : 2 * (n : ℤ) ≤ m * n := by nlinarith
        omega
      have h7 : -2 < m := by
        by_contra hc
        have : m * (n : ℤ) ≤ -2 * n := by nlinarith
        omega
      omega
    rcases h5 with rfl | rfl | rfl
    · left
      simpa using h4
    · right
      left
      simpa using h4
    · right
      right
      simpa using h4
  have hsub : ∀ (x y : ℤ), ((x : ℝ) = y + m * n) → x - y = m * n := by
    intro x y h
    have : (x : ℝ) - y = m * n := by linarith
    exact_mod_cast this
  cases b <;> cases b' <;> simp only [eo, ite_true, Bool.false_eq_true, ite_false, add_zero] at hm
  · have h3 := hsub p q (by exact_mod_cast hm)
    have := hbd _ (by omega) (by omega) h3
    left
    have hpq : p = q := by omega
    subst hpq
    rfl
  · have h3 := hsub p (q + 1) (by push_cast; exact_mod_cast hm)
    have := hbd _ (by omega) (by omega) h3
    right
    apply Subtype.ext
    simp only [twn, Bool.false_eq_true, ite_false, prv, Bool.not_false, Prod.mk.injEq, and_true,
      true_and]
    split_ifs <;> omega
  · have h3 := hsub (p + 1) q (by push_cast; exact_mod_cast hm)
    have := hbd _ (by omega) (by omega) h3
    right
    apply Subtype.ext
    simp only [twn, ite_true, nxt, Bool.not_true, Prod.mk.injEq, and_true, true_and]
    split_ifs <;> omega
  · have h3 := hsub p q (by
      have : (p : ℝ) = q + m * n := by linarith
      exact_mod_cast this)
    have := hbd _ (by omega) (by omega) h3
    left
    have hpq : p = q := by omega
    subst hpq
    rfl

/-- `g'` is the end of the other side with the same label not in `L`, at the same point after
pasting. -/
def MateL (W : ℕ → List Letter) (L : Set ℕ) (g g' : SE W) : Prop :=
  ∃ k e e', (W g.1.1)[g.1.2.1]? = some (k, e) ∧ (W g'.1.1)[g'.1.2.1]? = some (k, e') ∧
    (g.1.1, g.1.2.1) ≠ (g'.1.1, g'.1.2.1) ∧ k ∉ L ∧ g'.1.2.2 = (if e = e' then g.1.2.2 else
      !g.1.2.2)

theorem MateL.symm {g g' : SE W} (h : MateL W L g g') : MateL W L g' g := by
  obtain ⟨k, e, e', h1, h2, h3, h4, h5⟩ := h
  refine ⟨k, e', e, h2, h1, h3.symm, h4, ?_⟩
  rw [h5]
  by_cases he : e = e'
  · simp [he]
  · simp [he, Ne.symm he]

theorem MateL.unique (hP : IsPaired W) {g g' g'' : SE W} (h : MateL W L g g')
  (h' : MateL W L g g'') : g' = g'' := by
  obtain ⟨k, e, e', h1, h2, h3, h4, h5⟩ := h
  obtain ⟨k₂, e₂, e₂', h1', h2', h3', h4', h5'⟩ := h'
  have hk : (k, e) = (k₂, e₂) := by
    rw [h1] at h1'
    exact Option.some.inj h1'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
  rcases hP.third h1 h2 h2' h3 with h6 | h6
  · exact absurd h6.symm h3'
  · obtain ⟨⟨j, q, b⟩, h7⟩ := g'
    obtain ⟨⟨j', q', b'⟩, h8⟩ := g''
    simp only [Prod.mk.injEq] at h6
    obtain ⟨rfl, rfl⟩ := h6
    have he : e' = e₂' := by
      simp only at h2 h2'
      rw [h2] at h2'
      simpa using h2'
    subst he
    apply Subtype.ext
    simp only at h5 h5'
    simp only [Prod.mk.injEq, true_and]
    rw [h5, h5']

open Classical in
/-- Crossing the side at an end, if this side is pasted and is not cut. -/
noncomputable def prtL (W : ℕ → List Letter) (L : Set ℕ) (g : SE W) : SE W :=
  if h : ∃ g', MateL W L g g' then h.choose else g

theorem prtL_of_mate (hP : IsPaired W) {g g' : SE W} (h : MateL W L g g') : prtL W L g = g' := by
  have hex : ∃ g', MateL W L g g' := ⟨g', h⟩
  rw [prtL, dite_eq_left hex]
  exact MateL.unique hP hex.choose_spec h

theorem prtL_of_not {g : SE W} (h : ¬ ∃ g', MateL W L g g') : prtL W L g = g := by
  rw [prtL, dite_eq_right h]

theorem prtL_invol (hP : IsPaired W) : Function.Involutive (prtL W L) := by
  intro g
  by_cases h : ∃ g', MateL W L g g'
  · obtain ⟨g', hg⟩ := h
    rw [prtL_of_mate hP hg, prtL_of_mate hP hg.symm]
  · rw [prtL_of_not h, prtL_of_not h]

theorem eo_flp (e e' b : Bool) : eo (if e = e' then b else !b) = flp e e' (eo b) := by
  by_cases h : e = e' <;> cases b <;> simp [flp, eo, h]

theorem MateL.stp {g g' : SE W} (h : MateL W L g g') : Stp (cutW W L) (spe W g) (spe W g') := by
  obtain ⟨k, e, e', h1, h2, h3, h4, h5⟩ := h
  have := stp_to_cut (L := L) h1 h2 h3 (eo_mem g.1.2.2) h4
  rw [← eo_flp, ← h5] at this
  exact this

theorem MateL.of_le {L' : Set ℕ} {g g' : SE W} (h : MateL W L g g') (hs : L' ⊆ L) : MateL W L' g g'
  := by
  obtain ⟨k, e, e', h1, h2, h3, h4, h5⟩ := h
  exact ⟨k, e, e', h1, h2, h3, fun h' => h4 (hs h'), h5⟩

theorem prtL_cases (hP : IsPaired W) (g : SE W) : prtL W L g = g ∨ prtL W L g = prtL W ∅ g := by
  by_cases h : ∃ g', MateL W L g g'
  · obtain ⟨g', hg⟩ := h
    right
    rw [prtL_of_mate hP hg, prtL_of_mate hP (hg.of_le (empty_subset L))]
  · exact .inl (prtL_of_not h)

/-- The orbit of an end. -/
abbrev Orb (W : ℕ → List Letter) (L : Set ℕ) : SE W → SE W → Prop := TwoOrb (twn W) (prtL W L)

theorem prel_of_orb (hP : IsPaired W) {g g' : SE W} (h : Orb W L g g') : PRel (cutW W L) (spe W g)
  (spe W g') := by
  induction h with
  | rel a b h =>
    rcases h with rfl | rfl
    · rw [spe_twn]
      exact .refl _
    · by_cases hm : ∃ g', MateL W L a g'
      · obtain ⟨g', hg⟩ := hm
        rw [prtL_of_mate hP hg]
        exact .rel _ _ hg.stp
      · rw [prtL_of_not hm]
        exact .refl _
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2

theorem orb_of_stp (hP : IsPaired W) (g : SE W) {b : ℕ × ℂ} (h : Stp (cutW W L) (spe W g) b) :
    ∃ g', spe W g' = b ∧ Orb W L g g' := by
  classical
  obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, hk, ha, rfl⟩ := stp_of_cut h
  have hp := lt_length h1
  have hq := lt_length h2
  obtain ⟨⟨i₀, p₀, b₀⟩, hg⟩ := g
  replace hg : p₀ < (W i₀).length := hg
  have hi : i₀ = i := congrArg Prod.fst ha
  subst hi
  have hper : per (W i₀).length (p₀ + eo b₀) = per (W i₀).length (p + u) := congrArg Prod.snd ha
  have hend : u = 0 ∨ u = 1 := by
    by_contra hc
    push Not at hc
    have h4 : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hc.1), lt_of_le_of_ne hu.2 hc.2⟩
    obtain ⟨-, h5⟩ := side_unique hp hg h4 (eo_mem b₀) hper.symm
    cases b₀ <;> simp [eo] at h5 <;> simp [h5] at hc
  let x : Bool := decide (u = 1)
  have hx : eo x = u := by
    rcases hend with rfl | rfl <;> simp [eo, x]
  let h₁ : SE W := ⟨(i₀, p, x), hp⟩
  have hs1 : spe W h₁ = spt W i₀ p u := by simp only [spe, h₁, hx]
  have hor : Orb W L ⟨(i₀, p₀, b₀), hg⟩ h₁ := by
    rcases same_corner (g := ⟨(i₀, p₀, b₀), hg⟩) (h := h₁) (ha.trans hs1.symm) with h5 | h5
    · rw [h5]
      exact .refl _
    · rw [h5]
      exact TwoOrb.left _ _ _
  let h₂ : SE W := ⟨(j, q, if e = e' then x else !x), hq⟩
  have hm : MateL W L h₁ h₂ := ⟨k, e, e', h1, h2, h3, hk, rfl⟩
  refine ⟨h₂, ?_, .trans _ _ _ hor ?_⟩
  · simp only [spe, h₂, eo_flp, hx]
  · rw [← prtL_of_mate hP hm]
    exact TwoOrb.right _ _ _

theorem orb_of_prel (hP : IsPaired W) (g : SE W) {b : ℕ × ℂ} (h : PRel (cutW W L) (spe W g) b) :
    ∃ g', spe W g' = b ∧ Orb W L g g' := by
  have key : ∀ x y, PRel (cutW W L) x y → ((∃ g', spe W g' = x ∧ Orb W L g g') ↔ ∃ g', spe W g' = y
    ∧ Orb W L g g') := by
    have hstep : ∀ x y, Stp (cutW W L) x y → (∃ g', spe W g' = x ∧ Orb W L g g') → ∃ g', spe W g'
      = y ∧ Orb W L g g' := by
      rintro _ y hs ⟨g', rfl, hg⟩
      obtain ⟨g'', h1, h2⟩ := orb_of_stp hP g' hs
      exact ⟨g'', h1, .trans _ _ _ hg h2⟩
    intro x y hxy
    induction hxy with
    | rel x y hs => exact ⟨hstep x y hs, hstep y x hs.symm⟩
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  exact (key _ _ h).mp ⟨g, rfl, .refl _⟩

theorem orb_of_spe (hP : IsPaired W) {g g' : SE W} (h : PRel (cutW W L) (spe W g)
  (spe W g')) : Orb W L g g' := by
  obtain ⟨g'', h1, h2⟩ := orb_of_prel hP g h
  rcases same_corner h1 with h3 | h3
  · rw [h3]
    exact h2
  · rw [h3]
    exact .trans _ _ _ h2 (TwoOrb.left _ _ _)

theorem orb_empty (hP : IsPaired W) {g g' : SE W} (h : PRel W (spe W g) (spe W g')) : Orb W ∅ g g'
  :=
  orb_of_spe hP (prel_cut_empty h)

/-- What cutting does at a corner. -/
theorem corner_cut (hW : FinW W) (hP : IsPaired W) {c c' d d' : SE W} (hcc : prtL W ∅ c = c')
  (hc1 : prtL W L c = c)
    (hc2 : prtL W L c' = c') (hd1 : prtL W L d = d) (hd2 : prtL W L d' = d') (hne : c ≠ c')
      (hne1 : d ≠ c) (hne2 : d ≠ c')
    (hne3 : d' ≠ c) (hne4 : d' ≠ c') (hne5 : d ≠ d') (hod : PRel W (spe W c) (spe W d))
      (hod' : PRel W (spe W c) (spe W d'))
    (hπd : prtL W ∅ d = d ∨ prtL W ∅ d = d') (hπd' : prtL W ∅ d' = d ∨ prtL W ∅ d' = d')
    (hfix : ∀ g, PRel W (spe W c) (spe W g) → prtL W L g = g → g = c ∨ g = c' ∨ g = d ∨ g = d') :
    ¬ PRel (cutW W L) (spe W c) (spe W c') ∧ ∀ g, PRel W (spe W c) (spe W g) →
      PRel (cutW W L) (spe W c) (spe W g) ∨ PRel (cutW W L) (spe W c') (spe W g) := by
  have := finite_se hW
  obtain ⟨h1, h2⟩ := cut_classes (twn_invol (W := W)) (prtL_invol hP) (prtL_invol hP) twn_ne
    (prtL_cases hP) hcc hc1 hc2 hd1
    hd2 hne hne1 hne2 hne3 hne4 hne5 (orb_empty hP hod) (orb_empty hP hod') hπd hπd'
    (fun g hg hf => hfix g (prel_of_prel_cut (prel_of_orb hP hg)) hf)
  refine ⟨fun h => h1 (orb_of_spe hP h), fun g hg => ?_⟩
  rcases h2 g (orb_empty hP hg) with h | h
  · exact .inl (prel_of_orb hP h)
  · exact .inr (prel_of_orb hP h)

/-- A free end at a corner has one other free end at this corner. -/
theorem exists_free_end (hW : FinW W) (hP : IsPaired W) {g : SE W} (hg : prtL W ∅ g = g) :
    ∃ g', g' ≠ g ∧ prtL W ∅ g' = g' ∧ PRel W (spe W g) (spe W g') ∧
      ∀ z, PRel W (spe W g) (spe W z) → prtL W ∅ z = z → z = g ∨ z = g' := by
  have := finite_se hW
  obtain ⟨y, h1, h2, h3, h4⟩ := exists_other_end (twn_invol (W := W)) (prtL_invol hP) twn_ne hg
  exact ⟨y, h1, h2, prel_of_prel_cut (prel_of_orb hP h3), fun z hz hf => h4 z (orb_empty hP hz) hf⟩

theorem prtL_eq_iff (hP : IsPaired W) (g : SE W) {k : ℕ} {e : Bool} (h : (W g.1.1)[g.1.2.1]? = some
  (k, e)) :
    prtL W L g = g ↔ k ∈ L ∨ FreeSide W g.1.1 g.1.2.1 := by
  classical
  constructor
  · intro hf
    by_cases hk : k ∈ L
    · exact .inl hk
    right
    intro j q k₂ e₁ e₂ h1 h2
    by_contra hne
    have hk2 : (k₂, e₁) = (k, e) := by
      rw [h] at h1
      exact (Option.some.inj h1).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk2
    have hm : MateL W L g ⟨(j, q, if e₁ = e₂ then g.1.2.2 else !g.1.2.2), lt_length h2⟩
      := ⟨k₂, e₁, e₂, h, h2, hne, hk, rfl⟩
    have h3 := (prtL_of_mate hP hm).symm.trans hf
    exact hne (by rw [← h3])
  · intro hf
    refine prtL_of_not ?_
    rintro ⟨g', k₂, e₁, e₂, h1, h2, h3, h4, -⟩
    have hk2 : (k₂, e₁) = (k, e) := by
      rw [h] at h1
      exact (Option.some.inj h1).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk2
    rcases hf with hf | hf
    · exact h4 hf
    · exact h3 (hf _ _ _ _ _ h1 h2)

end GraphMinor.Surface

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L8c

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 8, part (d): the move

`move8`: in an optimal colouring with all `n_T ≤ 2`, if `g_{a,d} > g_{b,d}` there is an
`{a, b}`-recolouring that keeps `g_{e,·}` for `e ≠ a, b` and `g_{a,·} + g_{b,·}`, and changes
`D = g_a - g_b` by `-2` at `d` and, in addition, either nowhere, or by `-2` at some `d₁` where
`D ≥ 1` (`D ≥ 2` if `d₁ = d`), or by `+2` at some `d₁ ≠ d` where `D ≤ -1`.

Proof: a `J'`-free vertex `u` of an `a`-side pair at `d` (`#AV > #BV`); swap its `J ∪ J' ∪ K`
component; the touched pairs are those of the `J`-unmatched vertices of the component, the
`J'`-matched ones cancel in pairs, and the other free end `u'` decides the case.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L8

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {Sm Sp : Finset (Fin k)} {c : PEC G (Fin k)} {a b : Fin k}

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Rec.mono {R R' : Finset (Fin k)} {c c' : PEC G (Fin k)} (h : Rec R c c') (hR : R ⊆ R') :
    Rec R' c c' := by
  classical
  obtain ⟨ho, π, ⟨h1, h2⟩, e⟩ := h
  exact ⟨ho, π, ⟨h1, fun T x hx => h2 T x (fun h => hx (hR h))⟩, e⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem pcnt_pos {P : Finset V} {T : Finset (Fin k)} :
    0 < pcnt c P T ↔ ∃ w ∈ P, colSet c w = T := by
  classical
  unfold pcnt
  rw [card_pos]
  constructor
  · rintro ⟨w, hw⟩; exact ⟨w, (mem_filter.1 hw).1, (mem_filter.1 hw).2⟩
  · rintro ⟨w, hw, he⟩; exact ⟨w, mem_filter.2 ⟨hw, he⟩⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Touched pairs are counted by the `J`-unmatched vertices of `P`. -/
theorem touched_count (hn2 : ∀ T, cnt c T ≤ 2) {P : Finset V} (hP : ∀ w ∈ P, ¬ JMatched c a b w)
    (d : ℕ) :
    #(univ.filter fun T => InA Sm Sp c a b d T ∧
        (0 < pcnt c P T ∨ 0 < pcnt c P (swapSet a b T))) =
      #(P.filter (AV Sm Sp c a b d)) := by
  classical
  symm
  refine card_bij (fun w _ => Tof c a b w) (fun w hw => ?_) (fun w hw w' hw' h => ?_)
    (fun T hT => ?_)
  · obtain ⟨hwP, -, T, hT, hc⟩ := mem_filter.1 hw
    rw [Tof_eq hT hc]
    refine mem_filter.2 ⟨mem_univ _, hT, ?_⟩
    rcases hc with e | e
    · exact Or.inl (pcnt_pos.2 ⟨w, hwP, e⟩)
    · exact Or.inr (pcnt_pos.2 ⟨w, hwP, e⟩)
  · obtain ⟨-, hu, T, hT, hc⟩ := mem_filter.1 hw
    obtain ⟨-, hu', T', hT', hc'⟩ := mem_filter.1 hw'
    rw [Tof_eq hT hc, Tof_eq hT' hc'] at h
    subst h
    exact unm_unique hn2 hT hu hu' hc hc'
  · obtain ⟨hT, ht⟩ := (mem_filter.1 hT).2
    have : ∃ w ∈ P, colSet c w = T ∨ colSet c w = swapSet a b T := by
      rcases ht with h | h
      · obtain ⟨w, hw, e⟩ := pcnt_pos.1 h; exact ⟨w, hw, Or.inl e⟩
      · obtain ⟨w, hw, e⟩ := pcnt_pos.1 h; exact ⟨w, hw, Or.inr e⟩
    obtain ⟨w, hw, hc⟩ := this
    exact ⟨w, mem_filter.2 ⟨hw, hP w hw, T, hT, hc⟩, Tof_eq hT hc⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem BV_iff {d : ℕ} {w : V} : BV Sm Sp c a b d w ↔ AV Sm Sp c b a d w := by
  classical
  simp only [BV, AV, JMatched, swapSet_comm b a]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem g_preserved_outside_pair {c c' : PEC G (Fin k)} {a b e : Fin k}
    (ha : a ∈ Sp) (hb : b ∈ Sp) (haS : a ∉ Sm) (hbS : b ∉ Sm)
    (hrec : Rec {a, b} c c') (hea : e ≠ a) (heb : e ≠ b) (d' : ℕ) :
    g Sm Sp c' e d' = g Sm Sp c e d' := by
  classical
  have := hrec.card_filter (fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ e ∈ T ∧ #T = d') (fun T T' hcT h => by
    have hSm : ∀ z ∈ Sm, z ∉ ({a, b} : Finset (Fin k)) := fun z hz h' => by
      rcases mem_insert.1 h' with rfl | h'
      · exact haS hz
      · rw [mem_singleton.1 h'] at hz; exact hbS hz
    have hSp : ∀ z, z ∉ Sp → z ∉ ({a, b} : Finset (Fin k)) := fun z hz h' => by
      rcases mem_insert.1 h' with rfl | h'
      · exact hz ha
      · rw [mem_singleton.1 h'] at hz; exact hz hb
    have he : e ∉ ({a, b} : Finset (Fin k)) := by
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨hea, heb⟩
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun z hz => (h z (hSm z hz)).1 (h1 hz), fun z hz => ?_, (h e he).1 h3, hcT ▸ h4⟩
      by_contra hzp; exact hzp (h2 ((h z (hSp z hzp)).2 hz))
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun z hz => (h z (hSm z hz)).2 (h1 hz), fun z hz => ?_, (h e he).2 h3, hcT ▸ h4⟩
      by_contra hzp; exact hzp (h2 ((h z (hSp z hzp)).1 hz))) 1
  unfold g
  convert this using 2 <;> ext T <;> simp only [mem_filter, mem_univ, true_and] <;> tauto

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem matching_filter_card {c : PEC G (Fin k)} {a b : Fin k}
    (Jx : V → V → Prop) (hJ : XMatch c a b Jx) (M : Finset V) (A B : V → Prop)
    (hside : ∀ u v, A u → Jx u v → B v)
    (hside' : ∀ u v, B u → Jx u v → A v)
    (hMx : ∀ w ∈ M, ∃ v, Jx w v ∧ v ∈ M) : #(M.filter A) = #(M.filter B) := by
  classical
  choose! f hf hfM using hMx
  refine card_bij (fun w _ => f w) (fun w hw => ?_) (fun w hw w' hw' h => ?_) (fun v hv => ?_)
  · obtain ⟨hwM, hwA⟩ := mem_filter.1 hw
    exact mem_filter.2 ⟨hfM w hwM, hside w _ hwA (hf w hwM)⟩
  · exact hJ.uniq _ _ _ (hJ.symm _ _ (hf w (mem_filter.1 hw).1))
      (h ▸ hJ.symm _ _ (hf w' (mem_filter.1 hw').1))
  · obtain ⟨hvM, hvB⟩ := mem_filter.1 hv
    refine ⟨f v, mem_filter.2 ⟨hfM v hvM, hside' v _ hvB (hf v hvM)⟩, ?_⟩
    exact hJ.uniq _ _ _ (hf (f v) (hfM v hvM)) (hJ.symm _ _ (hf v hvM))

open Classical in
omit [Fintype V] in
private theorem card_filter_erase_two {P : Finset V} {u u' : V}
    (huP : u ∈ P) (hu'P : u' ∈ P) (hne : u' ≠ u) (Pr : V → Prop) :
    #(P.filter Pr) = #(((P.erase u).erase u').filter Pr) +
      (if Pr u' then 1 else 0) + (if Pr u then 1 else 0) := by
  classical
  let M := (P.erase u).erase u'
  change #(P.filter Pr) = #(M.filter Pr) +
    (if Pr u' then 1 else 0) + (if Pr u then 1 else 0)
  have h1 : P = insert u (insert u' M) := by
    ext w
    simp only [M, mem_insert, mem_erase]
    constructor
    · intro hw; by_cases e1 : w = u
      · left; exact e1
      · by_cases e2 : w = u'
        · right; left; exact e2
        · right; right; exact ⟨e2, e1, hw⟩
    · rintro (rfl | rfl | ⟨-, -, hw⟩)
      · exact huP
      · exact hu'P
      · exact hw
  have hu'M : u' ∉ M := fun h => (ne_of_mem_erase h) rfl
  have huM : u ∉ insert u' M := by
    rw [mem_insert]; rintro (h | h)
    · exact hne h.symm
    · exact (ne_of_mem_erase (mem_of_mem_erase h)) rfl
  rw [h1, card_filter, card_filter, sum_insert huM, sum_insert hu'M]
  ring

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The move of Lemma 8.** -/
theorem move8 (hopt : IsOptimal c) (hn2 : ∀ T, cnt c T ≤ 2) (ha : a ∈ Sp) (hb : b ∈ Sp)
    (haS : a ∉ Sm) (hbS : b ∉ Sm) (hab : a ≠ b) {d : ℕ}
    (hD : g Sm Sp c b d < g Sm Sp c a d) :
    ∃ c', Rec {a, b} c c' ∧
      (∀ e, e ≠ a → e ≠ b → ∀ d', g Sm Sp c' e d' = g Sm Sp c e d') ∧
      (∀ d', g Sm Sp c' a d' + g Sm Sp c' b d' = g Sm Sp c a d' + g Sm Sp c b d') ∧
      ((∀ d', (g Sm Sp c' a d' : ℤ) - g Sm Sp c' b d' =
          (g Sm Sp c a d' : ℤ) - g Sm Sp c b d' - (if d' = d then 2 else 0)) ∨
        (∃ d₁, (if d₁ = d then (2 : ℤ) else 1) ≤ (g Sm Sp c a d₁ : ℤ) - g Sm Sp c b d₁ ∧
          ∀ d', (g Sm Sp c' a d' : ℤ) - g Sm Sp c' b d' = (g Sm Sp c a d' : ℤ) - g Sm Sp c b d' -
            (if d' = d then 2 else 0) - (if d' = d₁ then 2 else 0)) ∨
        (∃ d₁, d₁ ≠ d ∧ (g Sm Sp c a d₁ : ℤ) - g Sm Sp c b d₁ ≤ -1 ∧
          ∀ d', (g Sm Sp c' a d' : ℤ) - g Sm Sp c' b d' = (g Sm Sp c a d' : ℤ) - g Sm Sp c b d' -
            (if d' = d then 2 else 0) + (if d' = d₁ then 2 else 0))) := by
  classical
  obtain ⟨Jx, hJ, hpair, hmaxA, hmaxB⟩ := exists_xmatch (Sm := Sm) (Sp := Sp) (c := c) (a := a)
    (b := b)
  have hgd := fun d' => gdiff_eq (Sm := Sm) (Sp := Sp) hn2 ha hb haS hbS hab d'
  -- the partner of a matched vertex has the other side and the same degree
  have hside : ∀ d' u v, AV Sm Sp c a b d' u → Jx u v → BV Sm Sp c a b d' v := by
    intro d' u v hu huv
    obtain ⟨d'', h | h⟩ := hpair u v huv
    · have : d'' = d' := (AV_card h.1).symm.trans (AV_card hu)
      rw [← this]; exact h.2
    · exact absurd h.1 (fun h' => AV_BV_excl hu h')
  have hside' : ∀ d' u v, BV Sm Sp c a b d' u → Jx u v → AV Sm Sp c a b d' v := by
    intro d' u v hu huv
    obtain ⟨d'', h | h⟩ := hpair u v huv
    · exact absurd hu (fun h' => AV_BV_excl h.1 h')
    · have : d'' = d' := (BV_card h.1).symm.trans (BV_card hu)
      rw [← this]; exact h.2
  -- counting: the matched vertices of one side inject into the other side
  have hinjA : ∀ d', #((univ.filter (AV Sm Sp c a b d')).filter fun u => ∃ v, Jx u v) ≤
      #(univ.filter (BV Sm Sp c a b d')) := by
    intro d'
    choose! f hf using fun u (h : u ∈ (univ.filter (AV Sm Sp c a b d')).filter
      fun u => ∃ v, Jx u v) => (mem_filter.1 h).2
    refine card_le_card_of_injOn f (fun u hu => mem_filter.2 ⟨mem_univ _,
      hside d' u _ (mem_filter.1 (mem_filter.1 hu).1).2 (hf u hu)⟩) ?_
    intro u hu u' hu' h
    exact hJ.uniq _ _ _ (hJ.symm _ _ (hf u hu)) (h ▸ hJ.symm _ _ (hf u' hu'))
  have hinjB : ∀ d', #(univ.filter (BV Sm Sp c a b d')) ≤ #(univ.filter (AV Sm Sp c a b d')) →
      #(univ.filter (BV Sm Sp c a b d')) ≤
        #((univ.filter (AV Sm Sp c a b d')).filter fun u => ∃ v, Jx u v) := by
    intro d' hle
    have hall := hmaxB d' hle
    choose! f hf using fun u (h : u ∈ univ.filter (BV Sm Sp c a b d')) =>
      hall u (mem_filter.1 h).2
    refine card_le_card_of_injOn f (fun u hu => mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _,
      hside' d' u _ (mem_filter.1 hu).2 (hf u hu)⟩, ⟨u, hJ.symm _ _ (hf u hu)⟩⟩) ?_
    intro u hu u' hu' h
    exact hJ.uniq _ _ _ (hJ.symm _ _ (hf u hu)) (h ▸ hJ.symm _ _ (hf u' hu'))
  have hAB : #(univ.filter (BV Sm Sp c a b d)) < #(univ.filter (AV Sm Sp c a b d)) := by
    have := hgd d
    have : (g Sm Sp c b d : ℤ) < g Sm Sp c a d := by exact_mod_cast hD
    omega
  -- a free `a`-side vertex at `d`
  obtain ⟨u, hAu, hfu⟩ : ∃ u, AV Sm Sp c a b d u ∧ ¬ ∃ v, Jx u v := by
    by_contra hne
    push Not at hne
    have := hinjA d
    have e : (univ.filter (AV Sm Sp c a b d)).filter (fun u => ∃ v, Jx u v) =
        univ.filter (AV Sm Sp c a b d) :=
      filter_true_of_mem fun u hu => hne u (mem_filter.1 hu).2
    rw [e] at this
    omega
  have hue := AV_end hAu
  have hFu : FreeX c a b Jx u := ⟨hAu.1, hfu⟩
  obtain ⟨u', hne, hr, hue', hFu', huniq⟩ := exists_unique_other_endX (hJ := hJ) hab hue hFu
  obtain ⟨c', hopt', hc'⟩ := swap_component (Jx := Jx) (hJ := hJ) hopt hab hue
  set Q := mComp c a b Jx hJ u
  set P := Q.filter fun v => ¬ JMatched c a b v with hPdef
  set tc : Finset (Fin k) → Prop := fun T => 0 < pcnt c P T ∨ 0 < pcnt c P (swapSet a b T)
    with htcdef
  have htc : ∀ T, tc (swapSet a b T) ↔ tc T := by
    intro T; simp only [htcdef, swapSet_swapSet]; tauto
  have hc'' : ∀ T, cnt c' T = cnt c (if tc T then swapSet a b T else T) := hc'
  -- the recolouring
  have hinv : Function.Involutive fun T => if tc T then swapSet a b T else T := by
    intro T
    by_cases h : tc T
    · simp only [ite_eq_left h, ite_eq_left ((htc T).2 h), swapSet_swapSet]
    · simp only [ite_eq_right h]
  have hrec : Rec {a, b} c c' := by
    refine ⟨hopt', hinv.toPerm _, RPerm.of_cases (mem_insert_self _ _)
      (mem_insert_of_mem (mem_singleton_self _)) fun T => ?_, fun T => hc'' T⟩
    simp only [Function.Involutive.coe_toPerm]
    split_ifs
    · right; rfl
    · left; rfl
  -- the `a`- and `b`-counts
  have hgA := fun d' => g_after (Sm := Sm) (Sp := Sp) (c := c) (c' := c') ha hb haS hbS tc htc
      hc'' d'
  have hc''' : ∀ T, cnt c' T = cnt c (if tc T then swapSet b a T else T) := by
    intro T
    rw [hc'' T]
    by_cases h : tc T
    · rw [ite_eq_left h, ite_eq_left h, swapSet_comm]
    · rw [ite_eq_right h, ite_eq_right h]
  have htc' : ∀ T, tc (swapSet b a T) ↔ tc T := by intro T; rw [swapSet_comm]; exact htc T
  have hgB := fun d' => g_after (Sm := Sm) (Sp := Sp) (c := c) (c' := c') hb ha hbS haS tc htc'
    hc''' d'
  refine ⟨c', hrec, ?_, ?_, ?_⟩
  · intro e hea heb d'
    exact g_preserved_outside_pair ha hb haS hbS hrec hea heb d'
  · intro d'
    have h1 := hgA d'; have h2 := hgB d'
    have : (g Sm Sp c' a d' : ℤ) + g Sm Sp c' b d' = g Sm Sp c a d' + g Sm Sp c b d' := by linarith
    exact_mod_cast this
  -- touched pairs through `P`
  have hPu : ∀ w ∈ P, ¬ JMatched c a b w := fun w hw => (mem_filter.1 hw).2
  have htA : ∀ d', #(univ.filter fun T => InA Sm Sp c a b d' T ∧ tc T) =
      #(P.filter (AV Sm Sp c a b d')) := fun d' => touched_count hn2 hPu d'
  have htB : ∀ d', #(univ.filter fun T => InA Sm Sp c b a d' T ∧ tc T) =
      #(P.filter (BV Sm Sp c a b d')) := by
    intro d'
    have hPu' : ∀ w ∈ P, ¬ JMatched c b a w := fun w hw => by
      have := hPu w hw; simp only [JMatched, swapSet_comm b a] at this ⊢; exact this
    have := touched_count (Sm := Sm) (Sp := Sp) (a := b) (b := a) hn2 hPu' d'
    rw [show (univ.filter fun T => InA Sm Sp c b a d' T ∧ tc T) =
      univ.filter fun T => InA Sm Sp c b a d' T ∧
        (0 < pcnt c P T ∨ 0 < pcnt c P (swapSet b a T)) by
      congr 1; ext T; simp only [htcdef, swapSet_comm b a], this]
    congr 1
    ext w; simp only [mem_filter, BV_iff]
  have hDiff : ∀ d', (g Sm Sp c' a d' : ℤ) - g Sm Sp c' b d' = (g Sm Sp c a d' : ℤ) -
      g Sm Sp c b d' - 2 * #(P.filter (AV Sm Sp c a b d')) +
        2 * #(P.filter (BV Sm Sp c a b d')) := by
    intro d'
    have h1 := hgA d'; have h2 := hgB d'
    rw [htA, htB] at h1 h2
    linarith
  -- the `J'`-matched vertices of `P` cancel
  have huP : u ∈ P := mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, Reachable.refl _⟩, hFu.1⟩
  have hu'P : u' ∈ P := mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hr⟩, hFu'.1⟩
  set M := (P.erase u).erase u'
  have hMx : ∀ w ∈ M, ∃ v, Jx w v ∧ v ∈ M := by
    intro w hw
    have hwu' := ne_of_mem_erase hw
    have hwu := ne_of_mem_erase (mem_of_mem_erase hw)
    have hwP := mem_of_mem_erase (mem_of_mem_erase hw)
    obtain ⟨hwQ, hwm⟩ := mem_filter.1 hwP
    have hrw : (mGraph c a b Jx hJ).Reachable u w := (mem_filter.1 hwQ).2
    have : ∃ v, Jx w v := by
      by_contra hno
      exact hwu' (huniq w hwu hrw ⟨hwm, hno⟩)
    obtain ⟨v, hv⟩ := this
    obtain ⟨hwe, -, hwv⟩ := hJ.ends w v hv
    obtain ⟨hve, hvm, -⟩ := hJ.ends v w (hJ.symm _ _ hv)
    have hvQ : v ∈ Q := mComp_closed hwQ ⟨hwv, hwe, hve, Or.inr (Or.inr hv)⟩
    refine ⟨v, hv, mem_erase.2 ⟨fun e => hFu'.2 ⟨w, e ▸ hJ.symm _ _ hv⟩,
      mem_erase.2 ⟨fun e => hFu.2 ⟨w, e ▸ hJ.symm _ _ hv⟩, mem_filter.2 ⟨hvQ, hvm⟩⟩⟩⟩
  have hMcancel : ∀ d', #(M.filter (AV Sm Sp c a b d')) =
      #(M.filter (BV Sm Sp c a b d')) := fun d' =>
    matching_filter_card Jx hJ M _ _ (hside d') (hside' d') hMx
  have hsplitP : ∀ (Pr : V → Prop), #(P.filter Pr) = #(M.filter Pr) +
      (if Pr u' then 1 else 0) + (if Pr u then 1 else 0) :=
    fun Pr => card_filter_erase_two huP hu'P hne Pr
  have hBu : ∀ d', ¬ BV Sm Sp c a b d' u := fun d' h => AV_BV_excl hAu h
  have hAu' : ∀ d', AV Sm Sp c a b d' u ↔ d' = d := fun d' =>
    ⟨fun h => (AV_card h).symm.trans (AV_card hAu), fun h => h ▸ hAu⟩
  have hD' : ∀ d', (g Sm Sp c' a d' : ℤ) - g Sm Sp c' b d' = (g Sm Sp c a d' : ℤ) -
      g Sm Sp c b d' - (if d' = d then 2 else 0) - (if AV Sm Sp c a b d' u' then 2 else 0) +
        (if BV Sm Sp c a b d' u' then 2 else 0) := by
    intro d'
    rw [hDiff, hsplitP, hsplitP, hMcancel]
    simp only [hAu', hBu, ite_false]
    split_ifs <;> push_cast <;> ring
  -- the other end
  by_cases hA' : ∃ d₁, AV Sm Sp c a b d₁ u'
  · obtain ⟨d₁, hd₁⟩ := hA'
    have hAd : ∀ d', AV Sm Sp c a b d' u' ↔ d' = d₁ := fun d' =>
      ⟨fun h => (AV_card h).symm.trans (AV_card hd₁), fun h => h ▸ hd₁⟩
    have hBd : ∀ d', ¬ BV Sm Sp c a b d' u' := fun d' h => AV_BV_excl hd₁ h
    right; left
    refine ⟨d₁, ?_, fun d' => by rw [hD' d']; simp only [hAd, hBd, ite_false]; ring⟩
    have hg1 := hgd d₁
    split_ifs with hdd
    · subst hdd
      -- two free `a`-side vertices at `d`
      have hle := hinjB d₁ (le_of_lt hAB)
      have hsub : insert u (insert u' ((univ.filter (AV Sm Sp c a b d₁)).filter
          fun u => ∃ v, Jx u v)) ⊆ univ.filter (AV Sm Sp c a b d₁) := by
        intro w hw
        rcases mem_insert.1 hw with rfl | hw
        · exact mem_filter.2 ⟨mem_univ _, hAu⟩
        rcases mem_insert.1 hw with rfl | hw
        · exact mem_filter.2 ⟨mem_univ _, hd₁⟩
        · exact (mem_filter.1 hw).1
      have hc := card_le_card hsub
      rw [card_insert_of_notMem, card_insert_of_notMem] at hc
      · omega
      · intro h; exact hFu'.2 (mem_filter.1 h).2
      · rw [mem_insert]; rintro (h | h)
        · exact hne h.symm
        · exact hFu.2 (mem_filter.1 h).2
    · have : ¬ #(univ.filter (AV Sm Sp c a b d₁)) ≤ #(univ.filter (BV Sm Sp c a b d₁)) :=
        fun hle => hFu'.2 (hmaxA d₁ hle u' hd₁)
      omega
  · push Not at hA'
    by_cases hB' : ∃ d₁, BV Sm Sp c a b d₁ u'
    · obtain ⟨d₁, hd₁⟩ := hB'
      have hBd : ∀ d', BV Sm Sp c a b d' u' ↔ d' = d₁ := fun d' =>
        ⟨fun h => (BV_card h).symm.trans (BV_card hd₁), fun h => h ▸ hd₁⟩
      have hlt : ¬ #(univ.filter (BV Sm Sp c a b d₁)) ≤ #(univ.filter (AV Sm Sp c a b d₁)) :=
        fun hle => hFu'.2 (hmaxB d₁ hle u' hd₁)
      right; right
      refine ⟨d₁, fun e => hlt (e ▸ le_of_lt hAB), ?_, fun d' => by
        rw [hD' d']; simp only [hA', hBd, ite_false]; ring⟩
      have := hgd d₁
      omega
    · push Not at hB'
      left
      intro d'
      rw [hD' d']
      simp only [hA', hB', ite_false]
      ring
end Bkls.L8

end LeanPool.BalancedEdgeColourings

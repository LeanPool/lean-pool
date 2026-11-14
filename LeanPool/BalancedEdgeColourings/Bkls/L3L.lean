/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Comp
public import LeanPool.BalancedEdgeColourings.Bkls.Lemma3
public import LeanPool.BalancedEdgeColourings.Bkls.CycleAdj

/-!
# Lemma 3 in line-graph form, with paths

`L` is a graph of maximum degree `2` whose vertices are to be coloured with three colours,
properly; the colour set of an edge `ab` of `L` is `{g a, g b}`. `μ` matches some edges of `L` to
other edges (possibly adjacent). If every odd cycle of `L` has an unmatched edge and no
`6`-cycle has all its
opposite edges matched, a colouring separating the colour sets of matched edges exists
(`lemma3L`). Paths of `L` (ends free) are coloured with `exists_path_colouring`, cycles with
`Cyc.cycle_colouring`, one component at a time.

In Corollary 4 the vertices of `L` are the edges of the two-coloured graph, and the edges of `L`
are its vertices of degree two (and the identified pairs of matched ends).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L3L

open Finset LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {E : Type*} [Fintype E] [DecidableEq E] {L : SimpleGraph E}

/-- The colour set of an edge. -/
def cs (g : E → Fin 3) (e : Sym2 E) : Finset (Fin 3) :=
  Sym2.lift ⟨fun a b => ({g a, g b} : Finset (Fin 3)), fun _ _ => Finset.pair_comm _ _⟩ e

omit [DecidableEq E] [Fintype E] in
theorem cs_mk (g : E → Fin 3) (a b : E) : cs g s(a, b) = {g a, g b} := by
  classical
  exact rfl

/-- `g` is good on `T`: proper there, and separating the matched edges inside `T`. -/
def Good (L : SimpleGraph E) (μ : Sym2 E → Option (Sym2 E)) (T : E → Prop) (g : E → Fin 3) :
    Prop :=
  (∀ a b, T a → L.Adj a b → g a ≠ g b) ∧
    ∀ e e', μ e = some e' → (∀ v ∈ e, T v) → (∀ v ∈ e', T v) → cs g e ≠ cs g e'

omit [DecidableEq E] [Fintype E] in
theorem cs_congr [Finite E] {g g' : E → Fin 3} {e : Sym2 E} (h : ∀ v ∈ e, g' v = g v) : cs g'
    e = cs g e := by
  classical
  let : Fintype E := Fintype.ofFinite E
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [cs_mk, cs_mk, h a (Sym2.mem_mk_left a b), h b (Sym2.mem_mk_right a b)]

omit [DecidableEq E] [Fintype E] in
theorem card_cs [Finite E] {g : E → Fin 3} {a b : E} (h : g a ≠ g b) : (cs g s(a, b)).card = 2 := by
  classical
  let : Fintype E := Fintype.ofFinite E
  rw [cs_mk]; exact card_pair h

omit [Fintype E] in
private theorem colour_cycle_component [Finite E]
    {μ : Sym2 E → Option (Sym2 E)}
    (hμ : ∀ e e', μ e = some e' →
      μ e' = some e ∧ e ∈ L.edgeSet ∧ e' ∈ L.edgeSet ∧ e ≠ e')
    {n : ℕ} {p : ℕ → E} (hp : IsPathFn L n p)
    {C D : Finset E} {idx : E → ℕ} {g : E → Fin 3}
    (hmemC : ∀ w, w ∈ C ↔ ∃ i ≤ n, p i = w)
    (hcl : ∀ j ≤ n, ∀ y, L.Adj (p j) y → ∃ k ≤ n, p k = y)
    (hadj : ∀ i j, i < j → j ≤ n → L.Adj (p i) (p j) →
      j = i + 1 ∨ (i = 0 ∧ j = n))
    (hg1 : ∀ a b, a ∈ D \ C → L.Adj a b → g a ≠ g b)
    (hidx : ∀ i ≤ n, idx (p i) = i)
    (hextend : ∀ c : ℕ → Fin 3,
      (∀ a b, a ∈ C → L.Adj a b → c (idx a) ≠ c (idx b)) →
      (∀ e e', μ e = some e' → (∀ v ∈ e, v ∈ C) →
        (∀ v ∈ e', v ∈ C) → cs (fun w => c (idx w)) e ≠ cs (fun w => c (idx w)) e') →
      (∀ e e', μ e = some e' → (∀ v ∈ e, v ∈ C) → (∀ v ∈ e', v ∈ D \ C) →
        cs (fun w => c (idx w)) e ≠ cs g e') →
      ∃ g', Good L μ (· ∈ D) g')
    (hodd : ∀ n p, IsPathFn L n p → 2 ≤ n → L.Adj (p 0) (p n) → Odd (n + 1) →
      μ s(p n, p 0) = none ∨ ∃ i < n, μ s(p i, p (i + 1)) = none)
    (h6 : ∀ p, IsPathFn L 5 p → L.Adj (p 0) (p 5) →
      ¬ ∀ k : ZMod 6, μ s(p (k - 1).val, p k.val) = some s(p (k + 2).val, p (k + 3).val))
    (hcyc : (2 ≤ n ∧ L.Adj (p 0) (p n))) :
    ∃ g', Good L μ (· ∈ D) g' := by
  classical
  obtain ⟨hn2, hend⟩ := hcyc
  set r := n + 1 with hr
  have : NeZero r := ⟨by omega⟩
  let ι : ZMod r → E := fun k => p k.val
  have hιlt : ∀ k : ZMod r, k.val ≤ n := fun k => by have := ZMod.val_lt k; omega
  have hιinj : ∀ a b : ZMod r, ι a = ι b → a = b := fun a b h =>
    ZMod.val_injective r (hp.1 _ _ (hιlt a) (hιlt b) h)
  have hιnat : ∀ i ≤ n, ι (i : ZMod r) = p i := fun i hi => by
    change p ((i : ZMod r).val) = p i
    rw [Cyc.val_cast_of_lt (by omega)]
  have hιsucc : ∀ k : ZMod r, L.Adj (ι k) (ι (k + 1)) := by
    intro k
    change L.Adj (p k.val) (p (k + 1).val)
    rw [Cyc.val_add_one' k]
    rcases Nat.lt_or_ge k.val n with h | h
    · rw [Nat.mod_eq_of_lt (by omega)]; exact hp.2 _ h
    · have hk : k.val = n := le_antisymm (hιlt k) h
      rw [hk, show n + 1 = r from rfl, Nat.mod_self]
      exact hend.symm
  let ed : ZMod r → Sym2 E := fun k => s(ι (k - 1), ι k)
  have keyA : ∀ i < n, s(p i, p (i + 1)) = ed ((i + 1 : ℕ) : ZMod r) := by
    intro i hi
    change s(p i, p (i + 1)) = s(p (((i + 1 : ℕ) : ZMod r) - 1).val, p ((i + 1 : ℕ) : ZMod
        r).val)
    rw [show ((i + 1 : ℕ) : ZMod r) - 1 = (i : ZMod r) by push_cast; ring,
      Cyc.val_cast_of_lt (by omega), Cyc.val_cast_of_lt (by omega)]
  have keyB : s(p n, p 0) = ed 0 := by
    have hv : ((0 : ZMod r) - 1).val = n := by
      rw [Cyc.val_sub_one', ZMod.val_zero, ite_eq_left rfl]; omega
    change s(p n, p 0) = s(p ((0 : ZMod r) - 1).val, p (0 : ZMod r).val)
    rw [hv, ZMod.val_zero]
  have hed : ∀ e, e ∈ L.edgeSet → (∀ v ∈ e, v ∈ C) → ∃ k, e = ed k := by
    intro e he hC'
    induction e using Sym2.inductionOn with
    | hf a b =>
      obtain ⟨i, hi, rfl⟩ := (hmemC a).1 (hC' a (Sym2.mem_mk_left a b))
      obtain ⟨j, hj, rfl⟩ := (hmemC b).1 (hC' b (Sym2.mem_mk_right _ b))
      rw [SimpleGraph.mem_edgeSet] at he
      rcases lt_trichotomy i j with hij | hij | hij
      · rcases hadj i j hij hj he with h | h
        · exact ⟨((i + 1 : ℕ) : ZMod r), by rw [h]; exact keyA i (by omega)⟩
        · exact ⟨0, by rw [h.1, h.2, Sym2.eq_swap]; exact keyB⟩
      · subst hij; exact absurd he (L.loopless.irrefl _)
      · rcases hadj j i hij hi he.symm with h | h
        · exact ⟨((j + 1 : ℕ) : ZMod r), by rw [h, Sym2.eq_swap]; exact keyA j (by omega)⟩
        · exact ⟨0, by rw [h.1, h.2]; exact keyB⟩
  have hedC : ∀ k, ∀ v ∈ ed k, v ∈ C := fun k v hv => by
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact (hmemC _).2 ⟨_, hιlt _, rfl⟩
    · exact (hmemC _).2 ⟨_, hιlt _, rfl⟩
  have hedinj : ∀ a b, ed a = ed b → a = b := by
    intro a b h
    rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact hιinj _ _ h2
    · have e1 : a - 1 = b := hιinj _ _ h1
      have e2 : a = b - 1 := hιinj _ _ h2
      have hb : b = a + 1 := by rw [e2]; ring
      rw [hb] at e1
      have h3 : (2 : ZMod r) = 0 := by
        calc (2 : ZMod r) = (a + 1) - (a - 1) := by ring
          _ = 0 := by rw [e1]; simp
      have h4 : ((2 : ℕ) : ZMod r) = 0 := by rw [Nat.cast_ofNat]; exact h3
      rw [ZMod.natCast_eq_zero_iff] at h4
      have := Nat.le_of_dvd (by omega) h4
      omega
  -- the states
  let stOf : Option (Sym2 E) → Cyc.VState r := fun o =>
    match o with
    | none => .free
    | some e' =>
      if h' : ∃ j, ed j = e' then .int h'.choose
      else if ∀ v ∈ e', v ∈ (D \ C) then .ext (cs g e') else .free
  let st : ZMod r → Cyc.VState r := fun k => stOf (μ (ed k))
  have hst_int : ∀ k j, st k = .int j → μ (ed k) = some (ed j) := by
    intro k j h
    cases hmu : μ (ed k) with
    | none => simp [st, stOf, hmu] at h
    | some e' =>
      simp only [st, stOf, hmu] at h
      split_ifs at h with h1 h2
      · rw [← Cyc.VState.int.inj h, h1.choose_spec]
  have hst_in : ∀ k j, μ (ed k) = some (ed j) → st k = .int j := by
    intro k j hmu
    have hex : ∃ j', ed j' = ed j := ⟨j, rfl⟩
    simp only [st, stOf, hmu, dite_eq_left hex]
    rw [hedinj _ _ hex.choose_spec]
  have hst_ext : ∀ k e', μ (ed k) = some e' → (∀ v ∈ e', v ∈ (D \ C)) →
      st k = .ext (cs g e') := by
    intro k e' hmu he'
    have hnex : ¬ ∃ j, ed j = e' := by
      rintro ⟨j, rfl⟩
      have := he' _ (Sym2.mem_mk_right _ _)
      exact (mem_sdiff.1 this).2 (hedC j _ (Sym2.mem_mk_right _ _))
    simp only [st, stOf, hmu, dite_eq_right hnex, ite_eq_left he']
  have hst_free : ∀ k, μ (ed k) = none → st k = .free := fun k hmu => by
    simp only [st, stOf, hmu]
  obtain ⟨f, hf1, hf2, hf3⟩ := Cyc.cycle_colouring_adj r (by omega) st
    (fun k F h => by
      cases hmu : μ (ed k) with
      | none => simp [st, stOf, hmu] at h
      | some e' =>
        simp only [st, stOf, hmu] at h
        split_ifs at h with h1 h2
        · rw [← Cyc.VState.ext.inj h]
          obtain ⟨-, -, he'L, -⟩ := hμ _ _ hmu
          induction e' using Sym2.inductionOn with
          | hf a b =>
            exact card_cs (hg1 a b (h2 a (Sym2.mem_mk_left a b)) he'L))
    (fun k j h => by
      have hmu := hst_int k j h
      obtain ⟨hmu', -, -, hne⟩ := hμ _ _ hmu
      exact ⟨hst_in j k hmu', fun e => hne (by rw [e])⟩)
    (fun hodd' => by
      rcases hodd n p hp hn2 hend hodd' with h | ⟨i, hi, h⟩
      · exact ⟨0, hst_free 0 (by rw [← keyB]; exact h)⟩
      · exact ⟨((i + 1 : ℕ) : ZMod r), hst_free _ (by rw [← keyA i hi]; exact h)⟩)
    (fun ⟨h6r, hall⟩ => by
      have hn5 : n = 5 := by omega
      subst hn5
      apply h6 p hp hend
      intro k
      have := hst_int k (k + 3) (hall k)
      simp only [ed, ι] at this
      rw [show k + 3 - 1 = k + 2 by ring] at this
      exact this)
  -- the colouring of `C`
  have hcsS : ∀ k, cs (fun w => f ((idx w : ℕ) : ZMod r)) (ed k) = Cyc.S f k := by
    intro k
    change cs (fun w => f ((idx w : ℕ) : ZMod r)) s(p (k - 1).val, p k.val) = Cyc.S f k
    simp only [cs_mk]
    rw [hidx _ (hιlt (k - 1)), hidx _ (hιlt k), ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    rfl
  refine hextend (fun i => f (i : ZMod r)) (fun a b ha hab => ?_) (fun e e' he h1 h2 => ?_)
    (fun e e' he h1 h2 => ?_)
  · obtain ⟨i, hi, rfl⟩ := (hmemC a).1 ha
    obtain ⟨j, hj, rfl⟩ := hcl i hi b hab
    show f ((idx (p i) : ℕ) : ZMod r) ≠ f ((idx (p j) : ℕ) : ZMod r)
    rw [hidx i hi, hidx j hj]
    obtain ⟨k, hk⟩ := hed s(p i, p j) hab (fun v hv => by
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact (hmemC _).2 ⟨i, hi, rfl⟩
      · exact (hmemC _).2 ⟨j, hj, rfl⟩)
    have hfk := hf1 (k - 1)
    rw [sub_add_cancel] at hfk
    rcases Sym2.eq_iff.1 hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : (i : ZMod r) = k - 1 := hιinj _ _ (by rw [hιnat i hi]; exact h1)
      have e2 : (j : ZMod r) = k := hιinj _ _ (by rw [hιnat j hj]; exact h2)
      rw [e1, e2]; exact hfk
    · have e1 : (i : ZMod r) = k := hιinj _ _ (by rw [hιnat i hi]; exact h1)
      have e2 : (j : ZMod r) = k - 1 := hιinj _ _ (by rw [hιnat j hj]; exact h2)
      rw [e1, e2]; exact hfk.symm
  · obtain ⟨-, heL, he'L, -⟩ := hμ e e' he
    obtain ⟨k, rfl⟩ := hed e heL h1
    obtain ⟨k', rfl⟩ := hed e' he'L h2
    rw [hcsS, hcsS]
    exact hf3 k k' (hst_in k k' he)
  · obtain ⟨-, heL, -, -⟩ := hμ e e' he
    obtain ⟨k, rfl⟩ := hed e heL h1
    rw [hcsS]
    exact hf2 k _ (hst_ext k e' he h2)

omit [Fintype E] in
private theorem colour_path_component
    {μ : Sym2 E → Option (Sym2 E)}
    (hμ : ∀ e e', μ e = some e' →
      μ e' = some e ∧ e ∈ L.edgeSet ∧ e' ∈ L.edgeSet ∧ e ≠ e')
    {n : ℕ} {p : ℕ → E} (hp : IsPathFn L n p)
    {C D : Finset E} {idx : E → ℕ} {g : E → Fin 3}
    (hmemC : ∀ w, w ∈ C ↔ ∃ i ≤ n, p i = w)
    (hcl : ∀ j ≤ n, ∀ y, L.Adj (p j) y → ∃ k ≤ n, p k = y)
    (hadj : ∀ i j, i < j → j ≤ n → L.Adj (p i) (p j) →
      j = i + 1 ∨ (i = 0 ∧ j = n))
    (hidx : ∀ i ≤ n, idx (p i) = i)
    (hextend : ∀ c : ℕ → Fin 3,
      (∀ a b, a ∈ C → L.Adj a b → c (idx a) ≠ c (idx b)) →
      (∀ e e', μ e = some e' → (∀ v ∈ e, v ∈ C) →
        (∀ v ∈ e', v ∈ C) → cs (fun w => c (idx w)) e ≠ cs (fun w => c (idx w)) e') →
      (∀ e e', μ e = some e' → (∀ v ∈ e, v ∈ C) → (∀ v ∈ e', v ∈ D \ C) →
        cs (fun w => c (idx w)) e ≠ cs g e') →
      ∃ g', Good L μ (· ∈ D) g')
    (hcyc : ¬ (2 ≤ n ∧ L.Adj (p 0) (p n))) :
    ∃ g', Good L μ (· ∈ D) g' := by
  classical
  have hcons : ∀ i j, i ≤ n → j ≤ n → L.Adj (p i) (p j) → j = i + 1 ∨ i = j + 1 := by
    intro i j hi hj h
    rcases lt_trichotomy i j with hij | rfl | hij
    · rcases hadj i j hij hj h with h' | h'
      · exact Or.inl h'
      · by_cases hn2 : 2 ≤ n
        · exact absurd ⟨hn2, by rw [← h'.1, ← h'.2]; exact h⟩ hcyc
        · left; omega
    · exact absurd h (L.loopless.irrefl _)
    · rcases hadj j i hij hi h.symm with h' | h'
      · exact Or.inr h'
      · by_cases hn2 : 2 ≤ n
        · exact absurd ⟨hn2, by rw [← h'.1, ← h'.2]; exact h.symm⟩ hcyc
        · right; omega
  -- the path edges
  have hpe : ∀ e, e ∈ L.edgeSet → (∀ v ∈ e, v ∈ C) →
      ∃ k, 1 ≤ k ∧ k ≤ n ∧ e = s(p (k - 1), p k) := by
    intro e he hC'
    induction e using Sym2.inductionOn with
    | hf a b =>
      obtain ⟨i, hi, rfl⟩ := (hmemC a).1 (hC' a (Sym2.mem_mk_left a b))
      obtain ⟨j, hj, rfl⟩ := (hmemC b).1 (hC' b (Sym2.mem_mk_right _ b))
      rcases hcons i j hi hj he with h | h
      · exact ⟨j, by omega, hj, by rw [show j - 1 = i by omega]⟩
      · exact ⟨i, by omega, hi, by rw [show i - 1 = j by omega, Sym2.eq_swap]⟩
  have hpeinj : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      s(p (i - 1), p i) = s(p (j - 1), p j) → i = j := by
    intro i j hi1 hin hj1 hjn h
    rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact hp.1 _ _ hin hjn h2
    · have a := hp.1 _ _ (by omega) hjn h1
      have b := hp.1 _ _ hin (by omega) h2
      omega
  have hpeC : ∀ i, 1 ≤ i → i ≤ n → ∀ v ∈ s(p (i - 1), p i), v ∈ C := fun i hi1 hin v hv => by
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact (hmemC _).2 ⟨i - 1, by omega, rfl⟩
    · exact (hmemC _).2 ⟨i, hin, rfl⟩
  -- the states
  let stOf : Option (Sym2 E) → PState := fun o =>
    match o with
    | none => .free
    | some e' =>
      if h' : ∃ j, 1 ≤ j ∧ j ≤ n ∧ s(p (j - 1), p j) = e' then .int h'.choose
      else if ∀ v ∈ e', v ∈ (D \ C) then .ext (cs g e') else .free
  let st : ℕ → PState := fun i =>
    if 1 ≤ i ∧ i ≤ n then stOf (μ s(p (i - 1), p i)) else .free
  have hst_int : ∀ i j, st i = .int j →
      1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n ∧ μ s(p (i - 1), p i) = some s(p (j - 1), p j) := by
    intro i j h
    simp only [st] at h
    split_ifs at h with hi
    · cases hmu : μ s(p (i - 1), p i) with
      | none => simp [stOf, hmu] at h
      | some e' =>
        simp only [stOf, hmu] at h
        split_ifs at h with h1 h2
        · have hj := PState.int.inj h
          obtain ⟨hj1, hjn, hje⟩ := h1.choose_spec
          rw [hj] at hj1 hjn hje
          exact ⟨hi.1, hi.2, hj1, hjn, by rw [hje]⟩
  have hst_in : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      μ s(p (i - 1), p i) = some s(p (j - 1), p j) → st i = .int j := by
    intro i j hi1 hin hj1 hjn hmu
    have hex : ∃ j', 1 ≤ j' ∧ j' ≤ n ∧ s(p (j' - 1), p j') = s(p (j - 1), p j) :=
      ⟨j, hj1, hjn, rfl⟩
    simp only [st, ite_eq_left (show 1 ≤ i ∧ i ≤ n from ⟨hi1, hin⟩), stOf, hmu,
        dite_eq_left hex]
    obtain ⟨a1, a2, a3⟩ := hex.choose_spec
    rw [hpeinj _ _ a1 a2 hj1 hjn a3]
  have hst_ext : ∀ i e', 1 ≤ i → i ≤ n → μ s(p (i - 1), p i) = some e' →
      (∀ v ∈ e', v ∈ (D \ C)) → st i = .ext (cs g e') := by
    intro i e' hi1 hin hmu he'
    have hnex : ¬ ∃ j, 1 ≤ j ∧ j ≤ n ∧ s(p (j - 1), p j) = e' := by
      rintro ⟨j, hj1, hjn, rfl⟩
      have := he' (p j) (Sym2.mem_mk_right _ _)
      exact (mem_sdiff.1 this).2 ((hmemC _).2 ⟨j, hjn, rfl⟩)
    simp only [st, ite_eq_left (show 1 ≤ i ∧ i ≤ n from ⟨hi1, hin⟩), stOf, hmu,
        dite_eq_right hnex,
      ite_eq_left he']
  obtain ⟨f, hprop, hsat⟩ := exists_path_colouring (n + 1) st
    (by simp [st]) (by simp [st])
    (fun i j h => by
      obtain ⟨hi1, hin, hj1, hjn, hmu⟩ := hst_int i j h
      obtain ⟨hmu', -, -, hne⟩ := hμ _ _ hmu
      exact ⟨hst_in j i hj1 hjn hi1 hin hmu', fun e => hne (by rw [e]), by omega⟩)
    (fun i hi => by simp only [st, ite_eq_right (show ¬ (1 ≤ i ∧ i ≤ n) by omega)])
  have hcs : ∀ k, 1 ≤ k → k ≤ n →
      cs (fun w => f (idx w)) s(p (k - 1), p k) = pathSet (n + 1) f k := by
    intro k hk1 hkn
    rw [cs_mk, hidx _ (by omega), hidx _ hkn, pathSet_mid f (by omega) (by omega)]
  refine hextend f (fun a b ha hab => ?_) (fun e e' he h1 h2 => ?_) (fun e e' he h1 h2 => ?_)
  · obtain ⟨i, hi, rfl⟩ := (hmemC a).1 ha
    obtain ⟨j, hj, rfl⟩ := hcl i hi b hab
    rw [hidx i hi, hidx j hj]
    rcases hcons i j hi hj hab with h | h
    · subst h; exact hprop i (by omega)
    · subst h; exact (hprop j (by omega)).symm
  · obtain ⟨-, heL, he'L, -⟩ := hμ e e' he
    obtain ⟨k, hk1, hkn, rfl⟩ := hpe e heL h1
    obtain ⟨k', hk1', hkn', rfl⟩ := hpe e' he'L h2
    have h := hsat k (by omega)
    simp only [PSat, hst_in k k' hk1 hkn hk1' hkn' he] at h
    rw [hcs k hk1 hkn, hcs k' hk1' hkn']
    exact h
  · obtain ⟨-, heL, -, -⟩ := hμ e e' he
    obtain ⟨k, hk1, hkn, rfl⟩ := hpe e heL h1
    have h := hsat k (by omega)
    simp only [PSat, hst_ext k e' hk1 hkn he h2] at h
    rw [hcs k hk1 hkn]
    exact h

omit [DecidableEq E] in
/-- **Lemma 3, line-graph form.** -/
theorem lemma3L [DecidableRel L.Adj] (hdeg : ∀ v, L.degree v ≤ 2)
    (μ : Sym2 E → Option (Sym2 E))
    (hμ : ∀ e e', μ e = some e' →
      μ e' = some e ∧ e ∈ L.edgeSet ∧ e' ∈ L.edgeSet ∧ e ≠ e')
    (hodd : ∀ n p, IsPathFn L n p → 2 ≤ n → L.Adj (p 0) (p n) → Odd (n + 1) →
      μ s(p n, p 0) = none ∨ ∃ i < n, μ s(p i, p (i + 1)) = none)
    (h6 : ∀ p, IsPathFn L 5 p → L.Adj (p 0) (p 5) →
      ¬ ∀ k : ZMod 6, μ s(p (k - 1).val, p k.val) = some s(p (k + 2).val, p (k + 3).val)) :
    ∃ g : E → Fin 3, (∀ a b, L.Adj a b → g a ≠ g b) ∧ ∀ e e', μ e = some e' → cs g e ≠ cs g e' := by
  classical
  -- closed sets
  let Cl : Finset E → Prop := fun D => ∀ a b, L.Adj a b → (a ∈ D ↔ b ∈ D)
  suffices key : ∀ m, ∀ D : Finset E, #D ≤ m → Cl D → ∃ g, Good L μ (· ∈ D) g by
    obtain ⟨g, hg1, hg2⟩ := key _ univ le_rfl (fun a b _ => by simp)
    exact ⟨g, fun a b h => hg1 a b (mem_univ _) h,
      fun e e' h => hg2 e e' h (fun v _ => mem_univ v) (fun v _ => mem_univ v)⟩
  intro m
  induction m with
  | zero =>
    intro D hDc _
    have : D = ∅ := card_eq_zero.1 (by omega)
    subst this
    refine ⟨fun _ => 0, fun a b ha => absurd ha (notMem_empty a), fun e e' _ he => ?_⟩
    induction e using Sym2.inductionOn with
    | hf a b => exact absurd (he a (Sym2.mem_mk_left a b)) (notMem_empty a)
  | succ m ih =>
    intro D hDc hD
    rcases D.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · refine ⟨fun _ => 0, fun a b ha => absurd ha (notMem_empty a), fun e e' _ he => ?_⟩
      induction e using Sym2.inductionOn with
      | hf a b => exact absurd (he a (Sym2.mem_mk_left a b)) (notMem_empty a)
    obtain ⟨n, p, hp, hpx, hmax⟩ := exists_maxPath L x
    have hcl : ∀ j ≤ n, ∀ y, L.Adj (p j) y → ∃ k ≤ n, p k = y := fun j hj y hy =>
      maxPath_closed hdeg hp hpx hmax hj hy
    have hadj : ∀ i j, i < j → j ≤ n → L.Adj (p i) (p j) → j = i + 1 ∨ (i = 0 ∧ j = n) :=
      fun i j hij hjn h => maxPath_adj hdeg hp hij hjn h
    -- the component `C` lies in `D`
    set C := (range (n + 1)).image p with hC
    have hmemC : ∀ w, w ∈ C ↔ ∃ i ≤ n, p i = w := fun w => by
      simp only [hC, mem_image, mem_range]
      exact ⟨fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩, fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩⟩
    have hpD0 : ∀ i ≤ n, (p i ∈ D ↔ p 0 ∈ D) := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ihi => rw [← ihi (by omega), hD _ _ (hp.2 i (by omega))]
    have hCD : C ⊆ D := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := (hmemC w).1 hw
      obtain ⟨i0, hi0, hx0⟩ := hpx
      rw [hpD0 i hi, ← hpD0 i0 hi0, hx0]; exact hx
    -- the rest
    set D' := D \ C with hD'
    have hCcl : ∀ a b, L.Adj a b → (a ∈ C ↔ b ∈ C) := by
      intro a b hab
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := (hmemC a).1 ha
        obtain ⟨k, hk, rfl⟩ := hcl i hi b hab
        exact (hmemC _).2 ⟨k, hk, rfl⟩
      · intro hb
        obtain ⟨i, hi, rfl⟩ := (hmemC b).1 hb
        obtain ⟨k, hk, rfl⟩ := hcl i hi a hab.symm
        exact (hmemC _).2 ⟨k, hk, rfl⟩
    have hD'c : Cl D' := fun a b hab => by
      simp only [hD', mem_sdiff]
      rw [hD a b hab, hCcl a b hab]
    have hcardD' : #D' ≤ m := by
      have h1 := card_sdiff_add_card_eq_card hCD
      have h2 : 0 < #C := card_pos.2 ⟨p 0, (hmemC _).2 ⟨0, by omega, rfl⟩⟩
      rw [hD']; omega
    obtain ⟨g, hg1, hg2⟩ := ih D' hcardD' hD'c
    -- the index of a vertex of `C`
    let idx : E → ℕ := fun w => if h : ∃ i ≤ n, p i = w then h.choose else 0
    have hidx : ∀ i ≤ n, idx (p i) = i := fun i hi => by
      have h : ∃ i' ≤ n, p i' = p i := ⟨i, hi, rfl⟩
      simp only [idx, dite_eq_left h]
      exact hp.1 _ _ h.choose_spec.1 hi h.choose_spec.2
    have hpidx : ∀ w ∈ C, idx w ≤ n ∧ p (idx w) = w := fun w hw => by
      obtain ⟨i, hi, rfl⟩ := (hmemC w).1 hw
      rw [hidx i hi]; exact ⟨hi, rfl⟩
    -- every edge meets `C` in both ends or in none
    have hedgeC : ∀ e, e ∈ L.edgeSet → (∃ v ∈ e, v ∈ C) → ∀ v ∈ e, v ∈ C := by
      intro e he ⟨v, hve, hvC⟩ w hwe
      induction e using Sym2.inductionOn with
      | hf a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        rcases Sym2.mem_iff.1 hve with rfl | rfl <;> rcases Sym2.mem_iff.1 hwe with rfl | rfl
        · exact hvC
        · exact (hCcl _ _ he).1 hvC
        · exact (hCcl _ _ he).2 hvC
        · exact hvC
    have hedgeD : ∀ e, e ∈ L.edgeSet → (∃ v ∈ e, v ∈ D') → ∀ v ∈ e, v ∈ D' := by
      intro e he ⟨v, hve, hvD⟩ w hwe
      induction e using Sym2.inductionOn with
      | hf a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        rcases Sym2.mem_iff.1 hve with rfl | rfl <;> rcases Sym2.mem_iff.1 hwe with rfl | rfl
        · exact hvD
        · exact (hD'c _ _ he).1 hvD
        · exact (hD'c _ _ he).2 hvD
        · exact hvD
    -- an edge inside `C` joins consecutive vertices (or the ends)
    have hinC : ∀ a b, a ∈ C → L.Adj a b → ∃ i j, i ≤ n ∧ j ≤ n ∧ p i = a ∧ p j = b ∧
        (j = i + 1 ∨ i = j + 1 ∨ (i = 0 ∧ j = n) ∨ (i = n ∧ j = 0)) := by
      intro a b ha hab
      obtain ⟨i, hi, rfl⟩ := (hmemC a).1 ha
      obtain ⟨j, hj, rfl⟩ := hcl i hi b hab
      refine ⟨i, j, hi, hj, rfl, rfl, ?_⟩
      rcases lt_trichotomy i j with h | rfl | h
      · rcases hadj i j h hj hab with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inl h'))
      · exact absurd hab (L.loopless.irrefl _)
      · rcases hadj j i h hi hab.symm with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr ⟨h'.2, h'.1⟩))
    -- the colouring of `C`, by cases
    have hextend : ∀ c : ℕ → Fin 3,
        (∀ a b, a ∈ C → L.Adj a b → c (idx a) ≠ c (idx b)) →
        (∀ e e', μ e = some e' → (∀ v ∈ e, v ∈ C) →
          (∀ v ∈ e', v ∈ C) → cs (fun w => c (idx w)) e ≠ cs (fun w => c (idx w)) e') →
        (∀ e e', μ e = some e' → (∀ v ∈ e, v ∈ C) → (∀ v ∈ e', v ∈ D') →
          cs (fun w => c (idx w)) e ≠ cs g e') →
        ∃ g', Good L μ (· ∈ D) g' := by
      intro c hc1 hc2 hc3
      let g' : E → Fin 3 := fun w => if w ∈ C then c (idx w) else g w
      have hgC : ∀ w ∈ C, g' w = c (idx w) := fun w hw => by simp only [g', ite_eq_left hw]
      have hgD : ∀ w, w ∉ C → g' w = g w := fun w hw => by simp only [g', ite_eq_right hw]
      refine ⟨g', fun a b ha hab => ?_, fun e e' he hev he'v => ?_⟩
      · by_cases haC : a ∈ C
        · have hbC := (hCcl a b hab).1 haC
          rw [hgC a haC, hgC b hbC]; exact hc1 a b haC hab
        · have hbC : b ∉ C := fun h => haC ((hCcl a b hab).2 h)
          rw [hgD a haC, hgD b hbC]
          exact hg1 a b (mem_sdiff.2 ⟨ha, haC⟩) hab
      · obtain ⟨-, heL, he'L, -⟩ := hμ e e' he
        have hsplit : ∀ f, f ∈ L.edgeSet → (∀ v ∈ f, v ∈ D) →
            (∀ v ∈ f, v ∈ C) ∨ (∀ v ∈ f, v ∈ D') := by
          intro f hf hfD
          induction f using Sym2.inductionOn with
          | hf a b =>
            by_cases haC : a ∈ C
            · exact Or.inl (hedgeC _ hf ⟨a, Sym2.mem_mk_left a b, haC⟩)
            · exact Or.inr (hedgeD _ hf ⟨a, Sym2.mem_mk_left a b,
                mem_sdiff.2 ⟨hfD a (Sym2.mem_mk_left a b), haC⟩⟩)
        have hcsC : ∀ f, (∀ v ∈ f, v ∈ C) → cs g' f = cs (fun w => c (idx w)) f :=
          fun f hf => cs_congr fun v hv => hgC v (hf v hv)
        have hcsD : ∀ f, (∀ v ∈ f, v ∈ D') → cs g' f = cs g f :=
          fun f hf => cs_congr fun v hv => hgD v (mem_sdiff.1 (hf v hv)).2
        rcases hsplit e heL hev with h1 | h1 <;> rcases hsplit e' he'L he'v with h2 | h2
        · rw [hcsC e h1, hcsC e' h2]; exact hc2 e e' he h1 h2
        · rw [hcsC e h1, hcsD e' h2]; exact hc3 e e' he h1 h2
        · rw [hcsD e h1, hcsC e' h2]
          exact fun h => hc3 e' e (hμ e e' he).1 h2 h1 h.symm
        · rw [hcsD e h1, hcsD e' h2]; exact hg2 e e' he h1 h2
    -- the restriction of a matched edge to a state
    by_cases hcyc : 2 ≤ n ∧ L.Adj (p 0) (p n)
    · exact colour_cycle_component hμ hp hmemC hcl hadj hg1 hidx hextend hodd h6 hcyc
    · exact colour_path_component hμ hp hmemC hcl hadj hidx hextend hcyc

end Bkls.L3L

end LeanPool.BalancedEdgeColourings

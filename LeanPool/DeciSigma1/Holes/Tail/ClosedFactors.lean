/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Tail.Rays

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Closed factors free of suffix occurrences

Two cuts `c < c'` of a word `x` bound a *closed* factor for a dictionary if they have the same
suffix node: the same longest suffix in the dictionary and the same state of the run before it
(`NodeClosedAt`). Repeating the factor `x[c, c')` then changes neither the states nor the suffix
nodes, up to the period `c' - c`. The bound on rejected tails repeats closed factors to build
periodic continuations, and the repetition must not create new comparisons with the suffixes of
target words; the dictionary is the suffix dictionary of the targets (`suffixDictionary`).

Among any `suffixLengthBound m N Ss bs` consecutive cuts there is a factor closed for the suffix
dictionary of at most `m` targets, at some window `B` between `bs` and
`suffixLengthEnvelope m N Ss bs`, longer than `B` and of length at most `factorLengthBound m N B`,
such that no occurrence of the suffix of length `B` of any target ends inside it, provided the
suffix chains of the targets that start at a length at least `bs` have at most the budgets `Ss`
(`exists_closed_factor_free_of_suffix_occurrences`). The base case is a pigeonhole on the suffix
nodes of cuts spaced `B + 1` apart (`exists_nodeClosedAt_of_spaced_cuts`), so
`suffixLengthBound m N [] b = factorLengthBound m N b + 1` is a polynomial in `b`. The proof is an
induction on the list of targets. For one target it follows a suffix chain while the distance to
the previous occurrence of the suffix stays below the length of the closed factor
(`Words.chain_stop_from`); the remaining targets are handled at a window at least `bs`, so their
chains from `bs` on suffice.

## Main declarations

- `suffixLengthBound`, `suffixLengthEnvelope`: the length of the search interval and the
  largest window.
- `exists_closed_factor_free_of_suffix_occurrences`: closed factors free of suffix occurrences
  of the targets.
- `exists_closed_factor_replicate`: the same for at most `m` targets with a common chain budget.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Words

variable {α S : Type} {k : ℕ}

/-! ## The recursion -/

/-- The number of consecutive cuts that contain a closed factor free of suffix occurrences of the
targets, for a dictionary of `m` targets, `N` states, the chain budgets `Ss` (one for each
target, the head for the outermost one) and the initial window `b`. -/
def suffixLengthBound (m N : ℕ) : List ℕ → ℕ → ℕ
  | [] => fun b => factorLengthBound m N b + 1
  | S :: Ss => fun b =>
      2 * suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b) +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
          suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) + 2

/-- The largest window at which such a closed factor is found. -/
def suffixLengthEnvelope (m N : ℕ) : List ℕ → ℕ → ℕ
  | [] => fun b => b
  | S :: Ss => fun b =>
      suffixLengthEnvelope m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b))

@[simp] theorem suffixLengthBound_nil (m N b : ℕ) :
    suffixLengthBound m N [] b = factorLengthBound m N b + 1 := rfl

@[simp] theorem suffixLengthEnvelope_nil (m N b : ℕ) : suffixLengthEnvelope m N [] b = b := rfl

theorem suffixLengthBound_cons (m N S : ℕ) (Ss : List ℕ) (b : ℕ) :
    suffixLengthBound m N (S :: Ss) b =
      2 * suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b) +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
          suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) + 2 := rfl

theorem suffixLengthEnvelope_cons (m N S : ℕ) (Ss : List ℕ) (b : ℕ) :
    suffixLengthEnvelope m N (S :: Ss) b =
      suffixLengthEnvelope m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) := rfl

/-! ## Iterates of inflationary monotone maps -/

theorem le_iterate_of_le_self {f : ℕ → ℕ} (hf : ∀ b, b ≤ f b) (n b : ℕ) : b ≤ f^[n] b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply]; exact (hf b).trans (ih _)

/-! ## Monotonicity -/

theorem suffixLengthBound_mono (m N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthBound m N Ss)
  | [] => fun b b' h => by simp only [suffixLengthBound_nil];
                           exact Nat.add_le_add_right (factorLengthBound_mono m N h) 1
  | S :: Ss => fun b b' h => by
    have hg := suffixLengthBound_mono m N Ss
    have hG : Monotone (fun b => b + suffixLengthBound m N Ss b) :=
        fun a a' h => Nat.add_le_add h (hg h)
    have h1 := hG.iterate S h
    rw [suffixLengthBound_cons, suffixLengthBound_cons]
    have h2 := hg h1
    have h3 := hg (Nat.add_le_add h1 h2)
    omega

theorem suffixLengthEnvelope_mono (m N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthEnvelope m N Ss)
  | [] => fun b b' h => h
  | S :: Ss => fun b b' h => by
    have hg := suffixLengthBound_mono m N Ss
    have hG : Monotone (fun b => b + suffixLengthBound m N Ss b) :=
        fun a a' h => Nat.add_le_add h (hg h)
    have h1 := hG.iterate S h
    rw [suffixLengthEnvelope_cons, suffixLengthEnvelope_cons]
    exact suffixLengthEnvelope_mono m N Ss (Nat.add_le_add h1 (hg h1))

theorem le_suffixLengthEnvelope (m N : ℕ) :
    ∀ (Ss : List ℕ) (b : ℕ), b ≤ suffixLengthEnvelope m N Ss b
  | [] , b => le_rfl
  | S :: Ss, b => by
    rw [suffixLengthEnvelope_cons]
    have :=
        le_iterate_of_le_self (f := fun b => b + suffixLengthBound m N Ss b)
            (fun b => Nat.le_add_right _ _)
      S b
    exact (this.trans (Nat.le_add_right _ _)).trans (le_suffixLengthEnvelope m N Ss _)

/-! ## Closed factors -/

/-- The empty word has every chain budget. -/
theorem chainBound_nil [DecidableEq α] (S : ℕ) : ChainBound ([] : List α) S :=
  fun bs h => (chainBound_len ([] : List α) bs h).trans (by simp)

section ClosedFactors

variable [DecidableEq α] [Fintype S]

/-- An occurrence of `v_{b+h}(t)` ending `h` letters after an occurrence of `v_b(t)`, with `h` at
most the window gap, gives `suffixReturnGap t b ≤ h`. -/
theorem suffixReturnGap_le_of_two_occ {x t : List α} {b g e e' : ℕ}
    (he : e ∈ occurrences x t (b + g))
    (he' : e' ∈ occurrences x t b) (hlt : e' < e) (hgap : e - e' ≤ g) :
    ∃ h, suffixReturnGap t b = some h ∧ h ≤ e - e' := by
  rw [mem_occurrences] at he he'
  obtain ⟨hex, hbt, hocc⟩ := he
  obtain ⟨hex', hbt', hocc'⟩ := he'
  have hl1 : (suffixOfLength t (b + g)).length = b + g := by simp [hbt]
  have hl2 : (suffixOfLength t b).length = b := by simp [hbt']
  rw [suffix_take_iff hex, hl1] at hocc
  rw [suffix_take_iff hex', hl2] at hocc'
  obtain ⟨hbe, hocc⟩ := hocc
  obtain ⟨hbe', hocc'⟩ := hocc'
  apply suffixReturnGap_le_of_occ hbt' (by omega) (by omega)
  rw [suffix_take_iff (by omega), hl2]
  refine ⟨by omega, fun j hj => ?_⟩
  have e1 := hocc (b + g - (e - e') - b + j) (by omega)
  have e2 := hocc' j hj
  rw [getElem?_suffixOfLength] at e1 e2 ⊢
  rw [← e2, show t.length - (e - e') - b + j = t.length - (b + g) + (b + g - (e - e') - b + j) by
    omega, ← e1]
  congr 1; omega

variable (T : Readers.Table α S k) (q0 : S) (x : List α)

/-- Let `ds` be a list of at most `m` words. If the chains of the targets `ts` that start at a
length at least `b₀` have at most the budgets `Ss`, then for every `bs ≥ b₀` any
`suffixLengthBound m N Ss bs` consecutive cuts `u, u + 1, …` of `x` contain cuts `c < c'` that are
closed for the suffix dictionary of `ds` at a window `B` with
`bs ≤ B ≤ suffixLengthEnvelope m N Ss bs`, such that no occurrence of the suffix of length `B` of
any target ends in `(c, c']`, and `B < c' - c ≤ factorLengthBound m N B`. -/
theorem exists_closed_factor_free_of_suffix_occurrences (ds : List (List α)) {m : ℕ}
    (hm : ds.length ≤ m) (b₀ : ℕ) :
    ∀ (ts : List (List α)) (Ss : List ℕ), List.Forall₂ (fun t S => ChainBoundFrom t b₀ S) ts Ss →
    ∀ bs u, b₀ ≤ bs → u + suffixLengthBound m (Fintype.card S) Ss bs ≤ x.length + 1 →
      ∃ B c c', bs ≤ B ∧ B ≤ suffixLengthEnvelope m (Fintype.card S) Ss bs ∧ u ≤ c ∧
        c' < u + suffixLengthBound m (Fintype.card S) Ss bs ∧
            NodeClosedAt T q0 (suffixDictionary ds B) x c c' ∧
        (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧ B < c' - c ∧
          c' - c ≤ factorLengthBound m (Fintype.card S) B := by
  intro ts Ss hS
  induction hS with
  | nil =>
    intro bs u _ hu
    simp only [suffixLengthBound_nil] at hu ⊢
    have hcard : (suffixDictionary ds bs).card * Fintype.card S ≤
        suffixNodeBound m (Fintype.card S) bs := by
      rw [suffixNodeBound, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ ((card_suffixDictionary_le ds bs).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) 1))
    have hV : (bs + 1) * ((suffixDictionary ds bs).card * Fintype.card S) ≤
        factorLengthBound m (Fintype.card S) bs := Nat.mul_le_mul_left _ hcard
    obtain ⟨c, c', hc, hc', hsp, hcl⟩ := exists_nodeClosedAt_of_spaced_cuts T q0
      (D := suffixDictionary ds bs) nil_mem_suffixDictionary x (s := bs + 1) (u := u) (by omega)
      (by omega)
    exact ⟨bs, c, c', le_rfl, le_rfl, hc, by omega, hcl, by simp, by omega, by omega⟩
  | @cons t Sb ts Ss hSt hrest ih =>
    intro bs u hb₀ hu
    set N := Fintype.card S
    set g := suffixLengthBound m N Ss with hg
    have hgm : Monotone g := suffixLengthBound_mono m N Ss
    set bstar := (fun b => b + g b)^[Sb] bs with hbstar
    have hL : suffixLengthBound m N (Sb :: Ss) bs = 2 * g bstar + g (bstar + g bstar) + 2 :=
        suffixLengthBound_cons m N Sb Ss bs
    have hF : suffixLengthEnvelope m N (Sb :: Ss) bs =
        suffixLengthEnvelope m N Ss (bstar + g bstar) := suffixLengthEnvelope_cons m N Sb Ss bs
    rw [hL] at hu ⊢
    rw [hF]
    obtain ⟨b, hbs, hbb, hstop⟩ := chain_stop_from hSt g hgm hb₀
    have hgb : g b ≤ g bstar := hgm hbb
    have hgb' : g (b + g b) ≤ g (bstar + g bstar) := hgm (Nat.add_le_add hbb hgb)
    have hFb : ∀ b', b' ≤ bstar + g bstar → suffixLengthEnvelope m N Ss b' ≤
        suffixLengthEnvelope m N Ss (bstar + g bstar) :=
      fun b' h => suffixLengthEnvelope_mono m N Ss h
    by_cases hcase : ∃ u', u ≤ u' ∧ u' + g b ≤ u + (2 * g bstar + g (bstar + g bstar) + 2) ∧
        ∀ e ∈ occurrences x t b, e < u' ∨ u' + g b ≤ e
    · -- case 1: `g b` consecutive cuts outside `occurrences x t b`
      obtain ⟨u', hu1, hu2, hfree⟩ := hcase
      obtain ⟨B, c, c', hB1, hB2, hc, hc', hcl, hts, hgap⟩ := ih b u' (by omega) (by omega)
      refine ⟨B, c, c', hbs.trans hB1, hB2.trans (hFb b (by omega)), by omega, by omega, hcl,
        ?_, hgap⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · refine NoSuffixOccurrenceEndsBetween.mono (fun e he => ?_) hB1
        rcases hfree e he with h | h <;> omega
      · exact hts t' ht'
    · -- case 2: the first occurrence is early and later ones are dense
      push Not at hcase
      obtain ⟨e0, he0, h01, h02⟩ := hcase u le_rfl (by omega)
      have hne : ((occurrences x t b).filter (fun e => u ≤ e)).Nonempty :=
        ⟨e0, Finset.mem_filter.mpr ⟨he0, h01⟩⟩
      set e1 := ((occurrences x t b).filter (fun e => u ≤ e)).min' hne with he1
      have he1mem := Finset.min'_mem _ hne
      rw [← he1, Finset.mem_filter] at he1mem
      have he1min : ∀ e ∈ occurrences x t b, u ≤ e → e1 ≤ e := fun e he hue =>
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨he, hue⟩)
      have he1u : e1 < u + g b := (he1min e0 he0 h01).trans_lt h02
      -- no end of `v_{b + g b}` after `e1`
      have hnone : ∀ e, e1 < e → e < u + (2 * g bstar + g (bstar + g bstar) + 2) →
          e ∉ occurrences x t (b + g b) := by
        intro e he1e heu he
        have heb : e ∈ occurrences x t b := occurrences_antitone (Nat.le_add_right _ _) he
        have hne' : ((occurrences x t b).filter (fun y => y < e)).Nonempty :=
          ⟨e1, Finset.mem_filter.mpr ⟨he1mem.1, he1e⟩⟩
        set e' := ((occurrences x t b).filter (fun y => y < e)).max' hne' with he'
        have he'mem := Finset.max'_mem _ hne'
        rw [← he', Finset.mem_filter] at he'mem
        have he'max : ∀ y ∈ occurrences x t b, y < e → y ≤ e' := fun y hy hye =>
          Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hy, hye⟩)
        have he1e' : e1 ≤ e' := he'max e1 he1mem.1 he1e
        have hgap : e - e' ≤ g b := by
          by_contra hgt
          obtain ⟨y, hy, h1, h2⟩ := hcase (e' + 1) (by omega) (by omega)
          have := he'max y hy (by omega)
          omega
        obtain ⟨h0, hD, hle⟩ := suffixReturnGap_le_of_two_occ he he'mem.1 he'mem.2 hgap
        have := hstop h0 hD
        omega
      obtain ⟨B, c, c', hB1, hB2, hc, hc', hcl, hts, hgapB⟩ :=
        ih (b + g b) (e1 + 1) (by omega) (by omega)
      refine ⟨B, c, c', by omega, hB2.trans (hFb _ (by omega)), by omega, by omega, hcl, ?_,
        hgapB⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · refine NoSuffixOccurrenceEndsBetween.mono (fun e he => ?_) hB1
        by_contra hcon
        push Not at hcon
        exact hnone e (by omega) (by omega) he
      · exact hts t' ht'

/-- At most `m` targets, each with chain budget `S` from `b₀`, can be handled with the budget
list `replicate m S`, by adding empty targets. -/
theorem suffixLengthBound_pad (ts : List (List α)) {m S b₀ : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBoundFrom t b₀ S) :
    ∃ ts' : List (List α), (∀ t ∈ ts, t ∈ ts') ∧
        List.Forall₂ (fun t S => ChainBoundFrom t b₀ S) ts' (List.replicate m S) := by
  induction m generalizing ts with
  | zero =>
    obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by simp, .nil⟩
  | succ m ih =>
    cases ts with
    | nil =>
      obtain ⟨ts', _, h⟩ := ih [] (by simp) (by simp)
      exact ⟨[] :: ts', by simp, .cons ((chainBound_nil S).chainBoundFrom b₀) h⟩
    | cons t ts =>
      obtain ⟨ts', h1, h2⟩ := ih ts (by simp at hm; omega)
        (fun t' ht' => hS t' (List.mem_cons_of_mem _ ht'))
      refine ⟨t :: ts', fun t' ht' => ?_, .cons (hS t List.mem_cons_self) h2⟩
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h1 t' ht')

/-- Closed factors free of suffix occurrences of at most `m` targets with a common chain budget
for the chains that start at the initial window `bs` or later, closed for the suffix dictionary
of the targets. -/
theorem exists_closed_factor_replicate (ts : List (List α)) {m Sb bs : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBoundFrom t bs Sb) {u : ℕ}
    (hseg : u + suffixLengthBound m (Fintype.card S) (List.replicate m Sb) bs ≤ x.length) :
    ∃ B c c', bs ≤ B ∧ B ≤ suffixLengthEnvelope m (Fintype.card S) (List.replicate m Sb) bs ∧
      u ≤ c ∧ c' ≤ u + suffixLengthBound m (Fintype.card S) (List.replicate m Sb) bs ∧
      NodeClosedAt T q0 (suffixDictionary ts B) x c c' ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧ B < c' - c ∧
      c' - c ≤ factorLengthBound m (Fintype.card S) B := by
  obtain ⟨ts', hsub, hF⟩ := suffixLengthBound_pad ts hm hS
  obtain ⟨B, c, c', h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_closed_factor_free_of_suffix_occurrences T q0 x ts hm bs ts' (List.replicate m Sb) hF
      bs u le_rfl (by omega)
  exact ⟨B, c, c', h1, h2, h3, h4.le, h5, fun t ht => h6 t (hsub t ht), h7⟩

end ClosedFactors

end DeciSigma1.Holes.Tail

/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Tail.Levels
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Suffix chains from long windows

A word with the level cover property at level `m` has suffix chains of at most
`chainLengthBound m + N` members (`levelCoverProperty_chainBound`), a number that grows with the
level. From a long window on, the number of members is bounded independently of the level.

Let `U` be the suffix of length `b` of a word `w` whose rejected tail `[J, |w|)` has a periodic
cover by at most `P` factors of period at most `E`, with at most `T` uncovered positions, and
whose longest suffix with period at most `E` is shorter than `Y`. If
`b ≥ 1 + T + P (Y + T + 2 E P + 1)`, at most `P` occurrences of `U` start in the rejected tail
(`card_tailOccurrences_le`). Some factor of the cover meets `U` in more than
`r = Y + T + 2 E P + 1` positions; its period `p` breaks at a position `o` inside `U`, since `U`
is not a long periodic suffix. Every occurrence of `U` in the tail repeats the interval of period
`p` before `o` and the break at its copy of `o`. Among the last `r` positions before the copy of
the break, some factor of the cover has more than `2 E`; by Fine–Wilf it inherits the period
`p`, so it ends at or before the copy of the break, and it cannot serve a later occurrence,
whose interval of period `p` would cover the earlier break. Distinct occurrences in the tail are
therefore charged to distinct factors.

Along a suffix chain `b₀ < b₁ < ⋯` with `b ≤ b₀`, the member `bᵢ` gives an occurrence of `U`
ending at `|w| - bᵢ + b₀` (`suffixChain_mem_occurrences`), which starts in the tail when the
suffix of length `bᵢ` does. The members whose suffixes start at or before the first rejected
cut carry distinct live states. So every chain from a window at least
`(Q + 2) (chainLengthBound m + 1)` has at most `Q + N` steps, where `Q = pieceCountBase`
(`levelCoverProperty_chainBoundFrom`).

## Main declarations

- `exists_factor_inter_gt`: a factor of a cover meets a long interval of the tail in many
  positions.
- `card_tailOccurrences_le`: few occurrences of a long suffix start in a covered tail.
- `suffixChain_mem_occurrences`: the members of a chain give occurrences of a short suffix.
- `levelCoverProperty_chainBoundFrom`: chains from long windows have at most
  `pieceCountBase + N` steps.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Readers DeciSigma1.Words

variable {α S : Type} {k : ℕ}

/-- If all but `T` positions of the rejected tail `[J, |w|)` lie in the factors `fs`, and the
interval `[x, y)` of the tail has more than `T + |fs| · r` positions, some factor meets it in
more than `r` positions. -/
theorem exists_factor_inter_gt {w : List α} {fs : List PeriodicFactor} {J T r x y : ℕ}
    (hunc : (uncoveredPositions fs J w.length).card ≤ T) (hJx : J ≤ x) (hy : y ≤ w.length)
    (hlen : T + fs.length * r < y - x) : ∃ f ∈ fs, r < min f.stop y - max f.start x := by
  by_contra hno
  push Not at hno
  set X := Finset.Ico x y with hX
  have hsplit := Finset.card_filter_add_card_filter_not (s := X) (p := Covers fs)
  have h1 : (X.filter (fun z => ¬ Covers fs z)).card ≤ T := by
    refine le_trans (Finset.card_le_card ?_) hunc
    intro z hz
    simp only [X, uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hz ⊢
    exact ⟨⟨by omega, by omega⟩, hz.2⟩
  have h2 : (X.filter (Covers fs)).card ≤ fs.length * r := by
    refine (card_filter_covers_le X fs).trans ?_
    have := List.sum_le_length_nsmul
      (fs.map (fun f => (X.filter (fun z => f.start ≤ z ∧ z < f.stop)).card)) r (by
        intro c hc
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
        calc (X.filter (fun z => f.start ≤ z ∧ z < f.stop)).card
            ≤ (Finset.Ico (max f.start x) (min f.stop y)).card :=
              Finset.card_le_card (fun z hz => by
                simp only [X, Finset.mem_filter, Finset.mem_Ico] at hz ⊢; omega)
          _ = min f.stop y - max f.start x := Nat.card_Ico _ _
          _ ≤ r := hno f hf)
    simpa using this
  have h4 : X.card = y - x := Nat.card_Ico _ _
  omega

section Occurrences

variable [DecidableEq α]

/-- If the rejected tail `[J, |w|)` of `w` has a periodic cover by at most `P` factors of period
at most `E` with at most `T` uncovered positions, the longest suffix of `w` with period at most
`E` is shorter than `Y`, and `b ≥ 1 + T + P (Y + T + 2 E P + 1)`, then at most `P` occurrences of
the suffix of length `b` of `w` start at or after `J`. -/
theorem card_tailOccurrences_le {w : List α} {J P E T Y b : ℕ} (hcov : PeriodicCover w J P E T)
    (hY : longestPeriodicSuffixLength E w < Y) (hb : 1 + T + P * (Y + T + 2 * E * P + 1) ≤ b) :
    ((occurrences w w b).filter (fun e => J + b ≤ e)).card ≤ P := by
  classical
  obtain ⟨fs, hfl, hfv, hunc⟩ := hcov
  set O := (occurrences w w b).filter (fun e => J + b ≤ e) with hO
  set n := w.length with hn
  -- an occurrence ending at `e` copies the last `b` letters, shifted by `n - e`
  have hcopy : ∀ e ∈ O, J + b ≤ e ∧ e ≤ n ∧
      ∀ z, n - b ≤ z → z < n → w[z - (n - e)]? = w[z]? := by
    intro e he
    rw [hO, Finset.mem_filter, mem_occurrences] at he
    obtain ⟨⟨hen, hbn, hocc⟩, hJe⟩ := he
    have hl : (suffixOfLength w b).length = b := by simp [hbn]
    rw [suffix_take_iff hen, hl] at hocc
    refine ⟨hJe, hen, fun z hz hzn => ?_⟩
    have := hocc.2 (z - (n - b)) (by omega)
    rw [getElem?_suffixOfLength, show e - b + (z - (n - b)) = z - (n - e) by omega,
      show w.length - b + (z - (n - b)) = z by omega] at this
    exact this
  rcases O.eq_empty_or_nonempty with hO0 | ⟨e₀, he₀⟩
  · rw [hO0]; simp
  obtain ⟨hJe₀, he₀n, -⟩ := hcopy e₀ he₀
  set r := Y + T + 2 * E * P + 1 with hr
  -- a factor `f` meets the suffix `[n - b, n)` in more than `r` positions
  obtain ⟨f, hf, hfr⟩ := exists_factor_inter_gt (r := r) hunc (x := n - b) (y := n) (by omega)
    le_rfl (by have : fs.length * r ≤ P * r := Nat.mul_le_mul_right _ hfl; omega)
  obtain ⟨hp, hpE, hfn, hfper⟩ := hfv f hf
  set p := f.period with hpdef
  have hP1 : 1 ≤ P := (List.length_pos_of_mem hf).trans_le hfl
  have hEP : 2 * E ≤ 2 * E * P := Nat.le_mul_of_pos_right _ hP1
  set a1 := max f.start (n - b) with ha1
  have hfr' : r < f.stop - a1 := by rw [min_eq_left hfn] at hfr; exact hfr
  -- the first break of the period `p` at or after `f.stop`
  have hex : ∃ j, f.stop + j = n ∨ w[f.stop + j]? ≠ w[f.stop + j - p]? :=
    ⟨n - f.stop, .inl (by omega)⟩
  set o := f.stop + Nat.find hex with ho
  have hmin : ∀ j < Nat.find hex, f.stop + j ≠ n ∧ w[f.stop + j]? = w[f.stop + j - p]? :=
    fun j hj => by simpa using Nat.find_min hex hj
  have hon : o ≤ n := by
    by_contra hlt
    exact (hmin (n - f.stop) (by omega)).1 (by omega)
  have hper : PeriodicOn w p a1 o := by
    intro q hq hqo
    by_cases hqf : q + p < f.stop
    · exact hfper q ((le_max_left _ _).trans hq) hqf
    · have h2 := (hmin (q + p - f.stop) (by omega)).2
      rw [show f.stop + (q + p - f.stop) = q + p by omega, show q + p - p = q by omega] at h2
      exact h2.symm
  have hon' : o < n := by
    rcases lt_or_eq_of_le hon with h | h
    · exact h
    · exfalso
      rw [h] at hper
      have := le_longestPeriodicSuffixLength hp hpE (by omega) hper
      omega
  have hbrk : w[o]? ≠ w[o - p]? := by
    rcases Nat.find_spec hex with h | h
    · omega
    · exact h
  -- each occurrence repeats the periodic interval `[a1, o)` and its break at `o`
  have hC1 : ∀ e ∈ O, PeriodicOn w p (a1 - (n - e)) (o - (n - e)) := by
    intro e he q hq hqo
    obtain ⟨-, -, hc⟩ := hcopy e he
    have e1 := hc (q + (n - e)) (by omega) (by omega)
    have e2 := hc (q + p + (n - e)) (by omega) (by omega)
    rw [show q + (n - e) - (n - e) = q by omega] at e1
    rw [show q + p + (n - e) - (n - e) = q + p by omega] at e2
    rw [e1, e2, show q + p + (n - e) = q + (n - e) + p by omega]
    exact hper _ (by omega) (by omega)
  have hC2 : ∀ e ∈ O, w[o - (n - e)]? ≠ w[o - (n - e) - p]? := by
    intro e he
    obtain ⟨-, -, hc⟩ := hcopy e he
    rw [hc o (by omega) hon', show o - (n - e) - p = o - p - (n - e) by omega,
      hc (o - p) (by omega) (by omega)]
    exact hbrk
  -- a factor of the cover meets the last `r` positions before the repeated break
  have hF : ∀ e, ∃ F : PeriodicFactor, e ∈ O →
      F ∈ fs ∧ 2 * E < min F.stop (o - (n - e)) - max F.start (o - (n - e) - r) := by
    intro e
    by_cases he : e ∈ O
    · obtain ⟨hJe, hen, -⟩ := hcopy e he
      have hl : fs.length * (2 * E) ≤ 2 * E * P := by
        calc fs.length * (2 * E) ≤ P * (2 * E) := Nat.mul_le_mul_right _ hfl
          _ = 2 * E * P := Nat.mul_comm _ _
      obtain ⟨F, hF1, hF2⟩ := exists_factor_inter_gt (r := 2 * E) hunc
        (x := o - (n - e) - r) (y := o - (n - e)) (by omega) (by omega) (by omega)
      exact ⟨F, fun _ => ⟨hF1, hF2⟩⟩
    · exact ⟨⟨0, 0, 0⟩, fun h => absurd h he⟩
  choose F hF using hF
  -- that factor ends at or before the repeated break
  have hstop : ∀ e ∈ O, (F e).stop ≤ o - (n - e) := by
    intro e he
    obtain ⟨hF1, hF2⟩ := hF e he
    obtain ⟨hp', hp'E, hF'n, hF'per⟩ := hfv _ hF1
    obtain ⟨hJe, hen, -⟩ := hcopy e he
    by_contra hlt
    push Not at hlt
    set oe := o - (n - e)
    set c1 := max (F e).start (oe - r)
    have hc1 : oe - c1 > 2 * E := by rw [min_eq_right hlt.le] at hF2; exact hF2
    have h1 : PeriodicOn w p c1 oe := (hC1 e he).mono (by omega) le_rfl
    have h2 : PeriodicOn w (F e).period c1 oe := hF'per.mono (le_max_left _ _) hlt.le
    have hgle : p.gcd (F e).period ≤ (F e).period := Nat.gcd_le_right _ hp'
    have hg := period_extend_gcd (by omega) (by omega) h1 h2 (by omega)
    have hFg := periodicOn_of_window hF'per hg (le_max_left _ _) hlt.le (by omega) hp'
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_left p (F e).period
    have := hFg.eq_of_le_add (p := oe - p) (by omega) c (by
      rw [Nat.mul_comm, ← hc]; omega)
    rw [Nat.mul_comm, ← hc, show oe - p + p = oe by omega] at this
    exact hC2 e he this.symm
  -- distinct occurrences are charged to distinct factors
  have hinj : Set.InjOn F O := by
    intro e he e' he' heq
    by_contra hne
    have key : ∀ e ∈ O, ∀ e' ∈ O, e < e' → F e = F e' → False := by
      intro e he e' he' hlt heq
      have hs := hstop e he
      obtain ⟨-, hF2⟩ := hF e' he'
      obtain ⟨hJe', hen', -⟩ := hcopy e' he'
      obtain ⟨hJe, hen, -⟩ := hcopy e he
      rw [← heq] at hF2
      have := (hC1 e' he') (o - (n - e) - p) (by omega) (by omega)
      rw [show o - (n - e) - p + p = o - (n - e) by omega] at this
      exact hC2 e he this.symm
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key e he e' he' h heq
    · exact key e' he' e he h heq.symm
  calc O.card ≤ fs.toFinset.card :=
        Finset.card_le_card_of_injOn F (fun e he => List.mem_toFinset.mpr (hF e he).1) hinj
    _ ≤ fs.length := List.toFinset_card_le fs
    _ ≤ P := hfl

/-- In a suffix chain of `t` with first member `b`, the suffix of length `b` is a prefix of the
suffix of length `b'` for every member `b' ≤ |t|`. -/
theorem suffixChain_getElem?_eq_of_mem {t : List α} {b b' : ℕ} {bs : List ℕ}
    (h : SuffixChain t (b :: bs)) (hb' : b' ∈ b :: bs) (hle : b' ≤ t.length) :
    b ≤ b' ∧ ∀ j < b, t[t.length - b' + j]? = t[t.length - b + j]? := by
  rcases List.mem_cons.mp hb' with rfl | hmem
  · exact ⟨le_rfl, fun _ _ => rfl⟩
  obtain ⟨hlt, -, hpre⟩ := (List.pairwise_cons.mp h.pairwise).1 b' hmem
  unfold suffixOfLength at hpre
  rw [prefix_drop_iff (Nat.sub_le _ _)] at hpre
  refine ⟨hlt.le, fun j hj => ?_⟩
  rw [hpre.2 j (by simp; omega), List.getElem?_drop]

/-- Along a suffix chain of `t` with first member `b₀ ≥ b`, the member `b' ≤ |t|` gives an
occurrence of the suffix of length `b` ending at `|t| - b' + b₀`. -/
theorem suffixChain_mem_occurrences {t : List α} {b b₀ b' : ℕ} {bs : List ℕ}
    (h : SuffixChain t (b₀ :: bs)) (hb : b ≤ b₀) (hb' : b' ∈ b₀ :: bs) (hle : b' ≤ t.length) :
    t.length - b' + b₀ ∈ occurrences t t b := by
  obtain ⟨hbb, htext⟩ := suffixChain_getElem?_eq_of_mem h hb' hle
  rw [mem_occurrences]
  refine ⟨by omega, by omega, ?_⟩
  have hl : (suffixOfLength t b).length = b := by simp; omega
  rw [suffix_take_iff (by omega), hl]
  refine ⟨by omega, fun j hj => ?_⟩
  rw [getElem?_suffixOfLength, show t.length - b' + b₀ - b + j = t.length - b' + (b₀ - b + j) by
    omega, htext _ (by omega)]
  congr 1; omega

end Occurrences

section Chains

variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- A word with the level cover property at level `m` has suffix chains of at most
`pieceCountBase + N` steps from every window at least
`(pieceCountBase + 2) (chainLengthBound m + 1)`. -/
theorem levelCoverProperty_chainBoundFrom (C : LevelBounds σ k (Fintype.card S))
    {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k} {m : ℕ} (h : M.Eligible W i)
    (hK : LevelCoverProperty C m M W i) {b₀ : ℕ}
    (hb : (C.pieceCountBase + 2) * (C.chainLengthBound m + 1) ≤ b₀) :
    ChainBoundFrom (W i) b₀ (C.pieceCountBase + Fintype.card S) := by
  classical
  intro b bs hbb hbs
  have hX := C.chainLengthBound_ge_cover m
  set Q := C.pieceCountBase
  set X := C.chainLengthBound m
  set E := C.periodBound m
  set n := (W i).length with hn
  set J := M.firstRejection W i with hJ
  set B := (Q + 2) * (X + 1) with hB
  -- at most `Q + 1` occurrences of the suffix of length `B` start in the rejected tail
  have hB' : 1 + C.uncoveredBound m + (Q + 1) * (C.terminalLengthBound m + C.uncoveredBound m +
      2 * E * (Q + 1) + 1) ≤ B := by
    have e1 : 2 * E * (Q + 1) = (Q + 1) * (2 * E) := by ring
    have e2 : (Q + 1) * (C.terminalLengthBound m + C.uncoveredBound m +
        2 * E * (Q + 1) + 1) ≤ (Q + 1) * (X + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : B = (Q + 1) * (X + 1) + (X + 1) := by rw [hB]; ring
    omega
  have hocc := card_tailOccurrences_le hK.1 hK.2 hB'
  by_cases hne : bs = []
  · simp [hne]
  have hle : ∀ b' ∈ b :: bs, b' ≤ n :=
    hbs.le_length (by have := List.length_pos_of_ne_nil hne; simp; omega)
  set A := (b :: bs).toFinset with hA
  have hcard : A.card = bs.length + 1 := by
    rw [hA, List.toFinset_card_of_nodup hbs.nodup, List.length_cons]
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (p := fun b' => n - b' ≤ J)
  -- members whose suffixes start at or before the first rejected cut carry distinct live states
  have hH : (A.filter (fun b' => n - b' ≤ J)).card ≤ Fintype.card S - 1 := by
    apply card_le_card_sub_one_of_injOn _ (fun b' => n - b')
      (fun x hx y hy he => by
        rw [Finset.mem_coe, Finset.mem_filter, hA, List.mem_toFinset] at hx hy
        have := hle x hx.1; have := hle y hy.1; simp only at he; omega)
      (fun b' => M.runPrefix W i (n - b')) M.dead
    · intro x hx y hy hxy
      rw [Finset.mem_filter, hA, List.mem_toFinset] at hx hy
      have hyx : y < x := by have := hle x hx.1; have := hle y hy.1; omega
      have hpre : suffixOfLength (W i) y <+: suffixOfLength (W i) x :=
        hbs.prefix_of_lt hy.1 hx.1 hyx
      exact StructuralReader.runPrefix_ne_of_le_firstRejection h hxy hy.2 hpre
    · intro x _; exact h.runPrefix_ne _
  -- the others give distinct occurrences of the suffix of length `B` in the rejected tail
  have hT : (A.filter (fun b' => ¬ n - b' ≤ J)).card ≤ Q + 1 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun b' => n - b' + b) (fun x hx => ?_)
      (fun x hx y hy he => ?_)) hocc
    · rw [Finset.mem_coe, Finset.mem_filter, hA, List.mem_toFinset] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨suffixChain_mem_occurrences hbs (hb.trans hbb) hx.1 (hle x hx.1), ?_⟩
      dsimp only
      have := hb.trans hbb
      omega
    · rw [Finset.mem_coe, Finset.mem_filter, hA, List.mem_toFinset] at hx hy
      have := hle x hx.1; have := hle y hy.1; simp only at he; omega
  omega

end Chains

end DeciSigma1.Holes.Tail

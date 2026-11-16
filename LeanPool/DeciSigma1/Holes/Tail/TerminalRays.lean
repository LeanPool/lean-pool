/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Arithmetic.FinitePaths
public import LeanPool.DeciSigma1.Holes.Tail.Levels
import Mathlib.Tactic.Ring.RingNF

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Terminal rays

A coordinate whose word ends with a long suffix of small period is continued by a ray of that
period. If the longest suffix of `w` with period at most `periodBound m` has at least
`terminalLengthBound m` letters, its last `p · N!` letters form a closed factor after the first
rejected cut, and no occurrence of a suffix of a target ends inside it (`exists_terminal_ray`).
The ray of this factor contains the whole word, so its comparisons with itself and with other
such rays are comparisons of the original words (`terminalRay_no_selfAdmission`,
`terminalRay_admission_edge`).

## Main declarations

- `RayAgrees`, `rayState_eq_runPrefix`: rays that agree with a word on a prefix, and their
  states.
- `runPrefix_period_stable`: runs on a periodic interval of a word are periodic.
- `exists_terminal_ray`: the ray of a long periodic suffix.
- `terminalRay_no_selfAdmission`, `terminalRay_admission_edge`: comparisons of terminal rays are
  comparisons of the original words.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table

variable {α S : Type} {k : ℕ}

/-! ## Rays that agree with a word -/

/-- The ray `Ω` agrees with the word `x` on its first `E ≤ |x|` letters. -/
def RayAgrees (Ω : Ray α) (x : List α) (E : ℕ) : Prop :=
  E ≤ x.length ∧ streamPrefix Ω.stream E = x.take E

theorem RayAgrees.streamPrefix_eq {Ω : Ray α} {x : List α} {E a : ℕ} (h : RayAgrees Ω x E)
    (ha : a ≤ E) : streamPrefix Ω.stream a = x.take a := by
  have := congrArg (List.take a) h.2
  rw [take_streamPrefix, List.take_take, min_eq_left ha] at this
  exact this

theorem RayAgrees.getElem? {Ω : Ray α} {x : List α} {E t : ℕ} (h : RayAgrees Ω x E)
    (ht : t < E) : x[t]? = some (Ω.stream t) := by
  have h1 : (x.take E)[t]? = x[t]? := List.getElem?_take_of_lt ht
  rw [← h1, ← h.2, List.getElem?_eq_getElem (by simpa using ht), getElem_streamPrefix _ _ _ ht]

/-- Two rays that agree with the same word agree with each other below both ends. -/
theorem RayAgrees.stream_eq {Ω Ω' : Ray α} {x : List α} {E E' t : ℕ} (h : RayAgrees Ω x E)
    (h' : RayAgrees Ω' x E') (ht : t < E) (ht' : t < E') : Ω.stream t = Ω'.stream t :=
  Option.some.inj ((h.getElem? ht).symm.trans (h'.getElem? ht'))

/-- Two rays that agree with the same word are equal if both ends lie at least the sum of the two
periods beyond both onsets. -/
theorem RayAgrees.stream_eq_of_le [DecidableEq α] {Ω Ω' : Ray α} {x : List α} {E E' : ℕ}
    (h : RayAgrees Ω x E) (h' : RayAgrees Ω' x E')
    (hE : max Ω.onset Ω'.onset + Ω.period + Ω'.period ≤ min E E')
    (t : ℕ) : Ω.stream t = Ω'.stream t := by
  simpa using Ray.stream_suffix_eq_of_prefix_eq Ω Ω' 0 0
    (fun t ht => by simpa using h.stream_eq h' (t := t) (by omega) (by omega)) t

/-- States along a ray that agrees with the word of coordinate `i` are the original states. -/
theorem rayState_eq_runPrefix (M : StructuralReader α S k) {W : Fin k → List α} {i : Fin k}
    {Ω : Ray α}
    {E a : ℕ} (h : RayAgrees Ω (W i) E) (ha : a ≤ E) :
    rayState M (M.start i) Ω a = M.runPrefix W i a := by
  simp only [rayState, Table.runPrefix, h.streamPrefix_eq ha]

/-- The ray of a factor agrees with the original word up to the end of the factor. -/
theorem repeatFactorRay_agrees {x : List α} {c c' : ℕ} (hcc : c < c') (hc' : c' ≤ x.length) :
    RayAgrees (repeatFactorRay x c c' hcc hc') x c' := by
  refine ⟨hc', ?_⟩
  have h1 := streamPrefix_repeatFactorRay hcc hc' (c' - c)
  rw [show c + (c' - c) = c' by omega] at h1
  rw [h1]
  have h2 := pumpFactor_take (L := c' - c) hcc hc' le_rfl (p := c') le_rfl
  rwa [List.take_of_length_le (by rw [length_pumpFactor hcc hc']; omega)] at h2

/-! ## Runs on a periodic interval -/

/-- On an interval `[s, e)` of period `p`, the states at cuts `x ≥ s + N · p` repeat after
`p · N!` letters. -/
theorem runPrefix_period_stable [Fintype S] (T : Table α S k) (W : Fin k → List α) (i : Fin k)
    {p s e x : ℕ} (hp : 0 < p) (hper : PeriodicOn (W i) p s e) (he : e ≤ (W i).length)
    (hx : s + Fintype.card S * p ≤ x) (hxe : x + p * (Fintype.card S).factorial ≤ e) :
    T.runPrefix W i (x + p * (Fintype.card S).factorial) = T.runPrefix W i x := by
  set u := ((W i).drop s).take (e - s) with hu
  have hulen : u.length = e - s := by simp only [hu, List.length_take, List.length_drop]; omega
  have hperu : PeriodicOn u p 0 u.length := by
    intro j _ hj
    rw [hulen] at hj
    simp only [hu, List.getElem?_take, List.getElem?_drop]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), show s + (j + p) = (s + j) + p by ring]
    exact hper (s + j) (by omega) (by omega)
  have hutake : ∀ t ≤ e - s, ((W i).drop s).take t = u.take t := by
    intro t ht; rw [hu, List.take_take, min_eq_left ht]
  have key :=
      Arithmetic.runFrom_take_periodic T (T.runPrefix W i s) hp hperu (o := x - s) (by omega) 1
    (by rw [hulen]; omega)
  rw [show x + p * (Fintype.card S).factorial =
      s + (x - s + 1 * (p * (Fintype.card S).factorial)) by omega,
    Table.runPrefix_add, hutake _ (by omega), key, ← hutake _ (by omega), ← Table.runPrefix_add,
    show s + (x - s) = x by omega]

theorem iterate_add_const (h b0 : ℕ) : ∀ n, (fun b => b + h)^[n] b0 = b0 + n * h
  | 0 => by simp
  | n + 1 => by rw [Function.iterate_succ_apply', iterate_add_const h b0 n]; ring

/-! ## Terminal rays -/

section TerminalRay

variable {σ : ℕ} [DecidableEq α] [Fintype S]

/-- If the longest suffix of `w` with period at most `periodBound m` has at least
`terminalLengthBound m` letters, the last `h = p · N!` letters of `w`, for the period `p` of that
suffix, form a factor closed at a window `B'` after the first rejected cut; the interval
`[c - B', |w|)` has period `p`, and no occurrence of the suffix of length `B'` of a target with
chain budget `fixedChainBudget (m + 1)` ends inside the factor. -/
theorem exists_terminal_ray (C : LevelBounds σ k (Fintype.card S)) {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) {m : ℕ}
    (hT : C.terminalLengthBound m ≤ longestPeriodicSuffixLength (C.periodBound m) (W i)) :
    ∃ B c p, ClosedAt M.toTable (M.start i) (W i) B c (W i).length ∧ M.firstRejection W i ≤ c ∧
      0 < p ∧ p ≤ C.periodBound m ∧ (W i).length - c = p * (Fintype.card S).factorial ∧
      PeriodicOn (W i) p (c - B) (W i).length ∧
      ∀ t : List α, ChainBound t (C.fixedChainBudget (m + 1)) →
          NoSuffixOccurrenceEndsBetween (W i) t B c (W i).length := by
  have hbud := C.terminalLengthBound_ge_periodBudget m
  have hY : 0 < C.terminalLengthBound m := by omega
  obtain ⟨s, p, hp, hpE, hs, hper, hYs⟩ := exists_of_le_longestPeriodicSuffixLength hY hT
  have hfac : 0 < (Fintype.card S).factorial := Nat.factorial_pos _
  have hh0 : 0 < p * (Fintype.card S).factorial := Nat.mul_pos hp hfac
  have hh0le : p * (Fintype.card S).factorial ≤ C.periodBound m * (Fintype.card S).factorial :=
    Nat.mul_le_mul_right _ hpE
  have hSl : C.fixedChainBudget (m + 1) * (p * (Fintype.card S).factorial) ≤
      C.fixedChainBudget (m + 1) * (C.periodBound m * (Fintype.card S).factorial) :=
          Nat.mul_le_mul_left _ hh0le
  have hNp : Fintype.card S * p ≤ Fintype.card S * C.periodBound m := Nat.mul_le_mul_left _ hpE
  have hcomm : (Fintype.card S).factorial * p = p * (Fintype.card S).factorial := Nat.mul_comm _ _
  set h0 := p * (Fintype.card S).factorial with hh0def
  set B0 := 1 + C.fixedChainBudget (m + 1) * h0 with hB0
  set n := (W i).length with hn
  have hlong : s + (B0 + h0) + h0 + Fintype.card S * p ≤ n := by omega
  have hcl : ClosedAt M.toTable (M.start i) (W i) (B0 + h0) (n - h0) n := by
    refine ⟨by omega, by omega, le_rfl, ?_⟩
    have hst : M.runPrefix W i (n - h0 - (B0 + h0) + h0) = M.runPrefix W i (n - h0 - (B0 + h0)) :=
      runPrefix_period_stable M.toTable W i hp hper le_rfl (by omega) (by omega)
    rw [show n - h0 - (B0 + h0) + h0 = n - (B0 + h0) by omega] at hst
    simp only [windowState]
    refine Prod.ext hst.symm ?_
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_drop, List.getElem?_take]
    by_cases hj : j < B0 + h0
    · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      have := hper.eq_of_le_add (p := n - h0 - (B0 + h0) + j) (by omega)
        (Fintype.card S).factorial (by omega)
      rw [this]; congr 1; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  refine ⟨B0 + h0, n - h0, p, hcl, ?_, hp, hpE, by omega, hper.mono (by omega) le_rfl, ?_⟩
  · by_cases hsJ : M.firstRejection W i ≤ s
    · omega
    · have := firstRejection_sub_lt_word h hp hper (by omega) (StructuralReader.firstRejection_le h)
      omega
  · intro t ht
    obtain ⟨b, hb1, hb2, hstop⟩ := chain_stop ht (fun _ => h0) (fun _ _ _ => le_rfl) 1
    have hb2' : b ≤ B0 := by
      have := iterate_add_const h0 1 (C.fixedChainBudget (m + 1))
      rw [this] at hb2
      omega
    apply noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt hcl (B := B0) (by omega)
    intro h' hD'
    obtain ⟨h'', hD'', hle⟩ := suffixReturnGap_mono hb2' hD'
    have := hstop h'' hD''
    omega

end TerminalRay

/-! ## Comparisons on rays that contain the original word -/

section Original

variable [DecidableEq α] [DecidableEq S]

/-- A comparison of a terminal ray with itself is a comparison of the original word: in a
comparison of a word with itself the host cut is at most the target cut, so restricting it to
the original target suffix gives a comparison of the original word. -/
theorem terminalRay_no_selfAdmission {M : StructuralReader α S k} {W : Fin k → List α}
    (hW : M.IsHole W) {i : Fin k}
    {Ω : Ray α} (hΩ : RayAgrees Ω (W i) (W i).length) :
    ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
      M.admitted (rayState M (M.start i) Ω a) (rayState M (M.start i) Ω b) = true →
      ¬ ∀ t, Ω.stream (a + t) = Ω.stream (b + t) := by
  intro a b hb hab hadm heq
  have hJ := StructuralReader.firstRejection_le (hW.1 i)
  rw [rayState_eq_runPrefix M hΩ (by omega), rayState_eq_runPrefix M hΩ (by omega)] at hadm
  have hpre : (W i).drop b <+: (W i).drop a := by
    rw [prefix_drop_iff (by omega)]
    refine ⟨by simp; omega, fun j hj => ?_⟩
    simp only [List.length_drop] at hj
    rw [List.getElem?_drop, hΩ.getElem? (by omega), hΩ.getElem? (by omega), heq j]
  have h2 := hW.2 i i _ (pair_mem_channel (by omega) (by omega) hpre)
  rw [h2] at hadm
  exact absurd hadm (by decide)

/-- A constraint of the ray system between two rays that contain their whole original words
holds at the lengths of the original words. -/
theorem terminalRay_admission_edge {M : StructuralReader α S k} {W : Fin k → List α}
    (hW : M.IsHole W) {i j : Fin k}
    {Ωi Ωj : Ray α} (hi : RayAgrees Ωi (W i) (W i).length)
    (hj : RayAgrees Ωj (W j) (W j).length) {a b : ℕ} (hb : b ≤ M.firstRejection W j)
    (hadm : M.admitted (rayState M (M.start i) Ωi a) (rayState M (M.start j) Ωj b) = true)
    (heq : ∀ t, Ωi.stream (a + t) = Ωj.stream (b + t)) :
    ((W i).length : ℤ) + ((b : ℤ) - a + 1) ≤ (W j).length := by
  by_contra hlt
  push Not at hlt
  have hJ := StructuralReader.firstRejection_le (hW.1 j)
  have ha : a ≤ (W i).length := by omega
  rw [rayState_eq_runPrefix M hi ha, rayState_eq_runPrefix M hj (by omega)] at hadm
  have hpre : (W j).drop b <+: (W i).drop a := by
    rw [prefix_drop_iff ha]
    refine ⟨by simp; omega, fun t ht => ?_⟩
    simp only [List.length_drop] at ht
    rw [List.getElem?_drop, hi.getElem? (by omega), hj.getElem? (by omega), heq t]
  have h2 := hW.2 i j _ (pair_mem_channel ha (by omega) hpre)
  rw [h2] at hadm
  exact absurd hadm (by decide)

end Original

end DeciSigma1.Holes.Tail

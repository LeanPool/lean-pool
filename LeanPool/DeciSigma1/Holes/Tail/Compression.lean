/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Periodic.Bound
public import LeanPool.DeciSigma1.Holes.Periodic.Transport
public import LeanPool.DeciSigma1.Holes.Tail.RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Compression of runs and the bound on rejected tails

A hole whose immortal rejected tails are covered by designated runs is shortened one period class
at a time. A pass takes a designated run of largest period and applies an admissible deletion to
its class. The resulting hole has the same endpoints, its first rejected cuts are the images of
the original ones, and the other designated runs survive.

Pieces ending at or before first rejection, or in mortal words, form the heads. Every comparable
set of heads has at most `k * (N - 1)` members, by distinct live states. All remaining pieces are
tails; there are at most two per designated run plus the uncovered positions. The resulting
`OccurrenceSplit` gives a cap affine in the number of uncovered positions. Processed runs become
uncovered positions for the next pass. After all runs are processed, the immortal rejected tails
are bounded by `compressionLengthBound`. Combining this with `exists_hole_with_run_cover` gives
`tailLengthBound`.

## Main declarations

- `occurrenceSplit`: head height and total tail count for a class in a hole with a run cover.
- `exists_hole_compressed_step`: one pass of compression.
- `compressionLengthBound`, `exists_hole_tail_le_compressionLengthBound`: the bound after all
  passes.
- `tailLengthBound`, `exists_hole_rejectedTailLength_le`: the bound on rejected tails.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words

variable {α S : Type} {k : ℕ}

/-! ## The retained-cut map -/

section Keep

variable {D : Finset ℕ}

/-- Every position of the edited word is the image of a retained original position. -/
theorem retainedCount_surj {a p' : ℕ} (h : p' < retainedCount D a) :
    ∃ p < a, p ∉ D ∧ retainedCount D p = p' := by
  induction a with
  | zero => simp at h
  | succ a ih =>
    rw [retainedCount_succ] at h
    by_cases ha : a ∈ D
    · rw [ite_eq_left ha] at h
      obtain ⟨p, hp, h1, h2⟩ := ih (by omega)
      exact ⟨p, by omega, h1, h2⟩
    · rw [ite_eq_right ha] at h
      by_cases hp' : p' < retainedCount D a
      · obtain ⟨p, hp, h1, h2⟩ := ih hp'
        exact ⟨p, by omega, h1, h2⟩
      · exact ⟨a, by omega, ha, by omega⟩

/-- The retained positions of `[s, e)` count `retainedCount e - retainedCount s`. -/
theorem retainedCount_eq_add_card {s e : ℕ} (h : s ≤ e) :
    retainedCount D e = retainedCount D s + ((Finset.Ico s e).filter (· ∉ D)).card := by
  unfold retainedCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    by_cases hp : p ∈ D
    · simp [hp]
    · simp only [hp, not_false_eq_true, and_true]; omega
  · rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hp hp'
    omega

end Keep

/-- If no position of a piece is deleted, and neither are the letters just before and after it,
the retained interval is a piece of the edited word with the same period, at the images of the
original cuts. -/
theorem isPeriodicPiece_deletePositions {U U' : Fin k → List α} {l : Fin k}
    {Dl : Finset ℕ}
    (hU' : U' l = deletePositions (U l) Dl) {d s e : ℕ} (hc : IsPeriodicPiece U d l s e)
    (hin : ∀ p, s ≤ p → p < e → p ∉ Dl) (hleft : s ≠ 0 → s - 1 ∉ Dl)
    (hright : e < (U l).length → e ∉ Dl) :
    IsPeriodicPiece U' d l (retainedCount Dl s) (retainedCount Dl e) ∧ retainedCount Dl e =
        retainedCount Dl s + (e - s) := by
  obtain ⟨hpiece, hlength, -⟩ :=
    isPeriodicPiece_deletePositions_with_root hU' hc hin hleft hright
  exact ⟨hpiece, hlength⟩

/-! ## Counting lemmas -/

/-- A set of natural numbers in `(a, a + 2d)` with pairwise gaps greater than `d` has at most two
elements. -/
theorem card_le_two_of_gaps (A : Finset ℕ) {a d : ℕ} (hA : ∀ x ∈ A, a < x ∧ x < a + 2 * d)
    (hgap : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → d < x - y ∨ d < y - x) : A.card ≤ 2 := by
  by_contra h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp (show 2 < A.card by omega)
  have := hA x hx; have := hA y hy; have := hA z hz
  have := hgap x hx y hy hxy; have := hgap x hx z hz hxz; have := hgap y hy z hz hyz
  omega

/-- A set of natural numbers that are `c` or lie in `(a, a + d)`, with pairwise gaps greater than
`d`, has at most two elements. -/
theorem card_le_two_of_gaps_with_exception (A : Finset ℕ) {a c d : ℕ}
    (hA : ∀ x ∈ A, x = c ∨ (a < x ∧ x < a + d))
    (hgap : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → d < x - y ∨ d < y - x) : A.card ≤ 2 := by
  by_contra h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp (show 2 < A.card by omega)
  have := hA x hx; have := hA y hy; have := hA z hz
  have := hgap x hx y hy hxy; have := hgap x hx z hz hxz; have := hgap y hy z hz hyz
  omega

section Count

variable [DecidableEq α] {U : Fin k → List α} {d : ℕ}

omit [DecidableEq α] in
/-- Distinct pieces of one word have ends more than `d` apart. -/
theorem piece_end_gap {P Q : Piece U d} (hl : P.coordinate = Q.coordinate) (hne : P ≠ Q) :
    d < P.stop - Q.stop ∨ d < Q.stop - P.stop := by
  have := piece_ends_sep hne hl
  omega

omit [DecidableEq α] in
theorem piece_end_injOn (A : Finset (Piece U d)) {i : Fin k} (hA : ∀ P ∈ A, P.coordinate = i) :
    Set.InjOn Piece.stop (A : Set (Piece U d)) := by
  intro P hP Q hQ he
  by_contra hne
  have := piece_end_gap ((hA P hP).trans (hA Q hQ).symm) hne
  omega

omit [DecidableEq α] in
/-- Comparable followers in one word: the later end's suffix is a prefix of the earlier one's. -/
theorem followerEdge_drop {P Q : Piece U d} (hl : P.coordinate = Q.coordinate)
    (hlt : P.stop < Q.stop) (hG : FollowerEdge P Q) :
    (U P.coordinate).drop Q.stop <+: (U P.coordinate).drop P.stop := by
  rcases hG with h | h
  · simp only [Piece.follower] at h
    rw [hl] at h
    have := h.length_le
    simp only [List.length_drop] at this
    have := Q.stop_le_length
    omega
  · simpa only [Piece.follower, hl] using h

variable [DecidableEq S]

omit [DecidableEq α] in
omit [DecidableEq S] in
/-- Pieces of one word with pairwise comparable followers, whose states at their ends are distinct
and live, number at most `N - 1`. -/
theorem card_chain_le [Fintype S] (M : StructuralReader α S k) (A : Finset (Piece U d)) {i : Fin k}
    (hA : ∀ P ∈ A, P.coordinate = i)
    (hdist : ∀ P ∈ A, ∀ Q ∈ A, P.stop < Q.stop → M.runPrefix U i P.stop ≠ M.runPrefix U i Q.stop)
    (hlive : ∀ P ∈ A, M.runPrefix U i P.stop ≠ M.dead) : A.card ≤ Fintype.card S - 1 := by
  classical
  exact
    card_le_card_sub_one_of_injOn A Piece.stop (piece_end_injOn A hA)
      (fun P => M.runPrefix U i P.stop) M.dead hdist hlive

omit [DecidableEq S] in
/-- The pieces of the class of `ρ` in word `i` that end after the first rejected cut number at
most two for each designated run of the word plus the uncovered positions of its rejected
tail. -/
theorem card_tail_le (M : StructuralReader α S k) {ρ : List α} (runs : Finset (RunSpec k))
    (hruns : ∀ r ∈ runs,
        IsPeriodicPiece U r.period r.coordinate r.start r.stop ∧ r.period ≤ ρ.length) {i : Fin k}
    (B : Finset (Piece U ρ.length))
    (hB : ∀ P ∈ B, P ∈ piecesOf U ρ ∧ P.coordinate = i ∧ M.firstRejection U i < P.stop) :
    B.card ≤ 2 * (runs.filter (fun r => r.coordinate = i)).card +
        (uncoveredTailPositions M U runs i).card := by
  classical
  have hsub : B ⊆ (runs.filter (fun r => r.coordinate = i)).biUnion
      (fun r => B.filter (fun P => r.start ≤ P.stop - 1 ∧ P.stop - 1 < r.stop)) ∪
        B.filter (fun P => P.stop - 1 ∈ uncoveredTailPositions M U runs i) := by
    intro P hP
    obtain ⟨-, hPl, hPJ⟩ := hB P hP
    by_cases hu : P.stop - 1 ∈ uncoveredTailPositions M U runs i
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP, hu⟩)
    · apply Finset.mem_union_left
      simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico, not_and, not_not] at hu
      have hle := P.stop_le_length
      rw [hPl] at hle
      obtain ⟨r, hr, hrl, h1, h2⟩ := hu ⟨by omega, by omega⟩
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hrl⟩,
        Finset.mem_filter.mpr ⟨hP, h1, h2⟩⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
  · refine (Finset.card_biUnion_le_card_mul _ _ 2 fun r hr => ?_).trans_eq (Nat.mul_comm _ _)
    obtain ⟨hr, hrl⟩ := Finset.mem_filter.mp hr
    obtain ⟨hpc, hdr⟩ := hruns r hr
    set Br := B.filter (fun P => r.start ≤ P.stop - 1 ∧ P.stop - 1 < r.stop)
    have hBr : ∀ P ∈ Br, P ∈ piecesOf U ρ ∧ P.coordinate = i ∧ r.start < P.stop ∧ P.stop ≤
        r.stop := by
      intro P hP
      obtain ⟨hP, h1, h2⟩ := Finset.mem_filter.mp hP
      have := P.long; have := P.period_pos
      exact ⟨(hB P hP).1, (hB P hP).2.1, by omega, by omega⟩
    have hinj := piece_end_injOn Br (fun P hP => (hBr P hP).2.1)
    rw [← Finset.card_image_of_injOn hinj]
    have hgap : ∀ x ∈ Br.image Piece.stop, ∀ y ∈ Br.image Piece.stop, x ≠ y →
        ρ.length < x - y ∨ ρ.length < y - x := by
      intro x hx y hy hxy
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hy
      exact piece_end_gap ((hBr P hP).2.1.trans (hBr Q hQ).2.1.symm) (fun h => hxy (h ▸ rfl))
    let R : Piece U r.period := Piece.ofIsPeriodicPiece hpc
    by_cases hcls : IsConjugate R.root ρ
    · -- a run of the same class: its own end, and at most one end in `(R.start, R.start + d)`
      have hdeq : r.period = ρ.length := by
        have := hcls.length_eq; rw [R.root_length] at this; exact this.symm
      have hpc' : IsPeriodicPiece U ρ.length r.coordinate r.start r.stop := hdeq ▸ hpc
      let R' : Piece U ρ.length := Piece.ofIsPeriodicPiece hpc'
      apply card_le_two_of_gaps_with_exception _ (a := r.start) (c := r.stop) _ hgap
      intro x hx
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨-, hPl, h1, h2⟩ := hBr P hP
      have hR's : R'.start = r.start := rfl
      have hR'e : R'.stop = r.stop := rfl
      by_cases hPR : P = R'
      · left; rw [hPR]; exact hR'e
      · right
        have hl : P.coordinate = R'.coordinate := by rw [hPl]; exact hrl.symm
        have := P.long
        rcases le_total P.start R'.start with hs | hs
        · have := Piece.sep hPR hl hs
          omega
        · have := Piece.sep (Ne.symm hPR) hl.symm hs
          omega
    · -- a run of another class: ends in `(R.start, R.start + 2d)` (Fine–Wilf)
      apply card_le_two_of_gaps _ (a := r.start) _ hgap
      intro x hx
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hPc, hPl, h1, h2⟩ := hBr P hP
      have hdiff : ¬ IsConjugate P.root R.root := fun h =>
        hcls (h.symm.trans ((mem_piecesOf U).mp hPc))
      have hfw := fw_overlap P R hdiff hdr (by rw [hPl]; exact hrl.symm)
      have := P.long
      change min P.stop r.stop - max P.start r.start < ρ.length + r.period at hfw
      refine ⟨h1, ?_⟩
      rcases le_total P.start r.start with hs | hs
      · rw [min_eq_left h2, max_eq_right hs] at hfw; omega
      · rw [min_eq_left h2, max_eq_left hs] at hfw; omega
  · apply Finset.card_le_card_of_injOn (fun P => P.stop - 1)
    · intro P hP
      exact (Finset.mem_filter.mp hP).2
    · intro P hP Q hQ he
      have hPB := (Finset.mem_filter.mp hP).1
      have hQB := (Finset.mem_filter.mp hQ).1
      have := (hB P hPB).2.2; have := (hB Q hQB).2.2
      apply piece_end_injOn B (fun P hP => (hB P hP).2.1) hPB hQB
      simp only at he
      omega

open Classical in
/-- Pieces ending at or before first rejection, and pieces of mortal words, have bounded comparable
height. The remaining pieces are counted by designated runs and uncovered tail positions. -/
noncomputable def occurrenceSplit [Fintype S] (M : StructuralReader α S k)
    (hU : M.IsHole U) (ρ : List α) (runs : Finset (RunSpec k))
    (hruns : ∀ r ∈ runs,
      IsPeriodicPiece U r.period r.coordinate r.start r.stop ∧ r.period ≤ ρ.length)
    {t : ℕ} (ht : 2 * runs.card + ∑ i, (if M.Immortal (M.endState U i) then
      (uncoveredTailPositions M U runs i).card else 0) ≤ t) :
    OccurrenceSplit U ρ (k * (Fintype.card S - 1)) t := by
  classical
  refine ⟨(fun P => ¬ M.Immortal (M.endState U P.coordinate) ∨
    P.stop ≤ M.firstRejection U P.coordinate), ?_, ?_⟩
  · intro c _ hhead hchain
    have hword : ∀ i, (c.filter (fun P => P.coordinate = i)).card ≤ Fintype.card S - 1 := by
      intro i
      set ci := c.filter (fun P => P.coordinate = i)
      have hci : ∀ P ∈ ci, P ∈ c ∧ P.coordinate = i := fun P hP => Finset.mem_filter.mp hP
      have hdrop : ∀ P ∈ ci, ∀ Q ∈ ci, P.stop < Q.stop →
          (U i).drop Q.stop <+: (U i).drop P.stop := by
        intro P hP Q hQ hlt
        have h := followerEdge_drop ((hci P hP).2.trans (hci Q hQ).2.symm) hlt
          (hchain P (hci P hP).1 Q (hci Q hQ).1)
        rwa [(hci P hP).2] at h
      apply card_chain_le M ci (fun P hP => (hci P hP).2)
      · intro P hP Q hQ hlt
        by_cases him : M.Immortal (M.endState U i)
        · have hQJ := hhead Q (hci Q hQ).1
          rw [(hci Q hQ).2] at hQJ
          exact StructuralReader.runPrefix_ne_of_le_firstRejection (hU.1 i) hlt
            (hQJ.resolve_left (not_not.mpr him)) (hdrop P hP Q hQ hlt)
        · have hlen := Q.stop_le_length
          rw [(hci Q hQ).2] at hlen
          exact StructuralReader.runPrefix_ne_of_mortal (hU.1 i) him hlt hlen
            (hdrop P hP Q hQ hlt)
      · intro P _; exact (hU.1 i).runPrefix_ne _
    calc c.card = ∑ i, (c.filter (fun P => P.coordinate = i)).card :=
          Finset.card_eq_sum_card_fiberwise (fun P _ => Finset.mem_univ P.coordinate)
      _ ≤ ∑ _ : Fin k, (Fintype.card S - 1) := Finset.sum_le_sum fun i _ => hword i
      _ = k * (Fintype.card S - 1) := by simp
  · intro c hcsub htail
    have hword : ∀ i, (c.filter (fun P => P.coordinate = i)).card ≤
        2 * (runs.filter (fun r => r.coordinate = i)).card +
          (if M.Immortal (M.endState U i) then
            (uncoveredTailPositions M U runs i).card else 0) := by
      intro i
      by_cases him : M.Immortal (M.endState U i)
      · rw [ite_eq_left him]
        apply card_tail_le M runs hruns
        intro P hP
        obtain ⟨hP, hPi⟩ := Finset.mem_filter.mp hP
        have hPJ := htail P hP
        rw [hPi] at hPJ
        exact ⟨hcsub hP, hPi, by omega⟩
      · have he : c.filter (fun P => P.coordinate = i) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro P hP
          obtain ⟨hP, hPi⟩ := Finset.mem_filter.mp hP
          exact htail P hP (Or.inl (by rwa [hPi]))
        rw [he, Finset.card_empty]
        exact Nat.zero_le _
    refine le_trans ?_ ht
    calc c.card = ∑ i, (c.filter (fun P => P.coordinate = i)).card :=
          Finset.card_eq_sum_card_fiberwise (fun P _ => Finset.mem_univ P.coordinate)
      _ ≤ ∑ i, (2 * (runs.filter (fun r => r.coordinate = i)).card +
          (if M.Immortal (M.endState U i) then
            (uncoveredTailPositions M U runs i).card else 0)) :=
        Finset.sum_le_sum fun i _ => hword i
      _ = 2 * runs.card + ∑ i, (if M.Immortal (M.endState U i) then
          (uncoveredTailPositions M U runs i).card else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (RunSpec.coordinate r))]

end Count

/-! ## One pass -/

/-- The split cap is monotone in the period. -/
theorem pieceLengthBound_mono {N d d' h t : ℕ} (hd : d ≤ d') :
    pieceLengthBound N d h t ≤ pieceLengthBound N d' h t := by
  unfold pieceLengthBound fixedMargin comparisonGap boundaryMargin stateTransientLength
    statePeriodModulus
  have h2 := Nat.mul_le_mul_right N.factorial hd
  have h3 := Nat.mul_le_mul_left N hd
  have h4 := Nat.mul_le_mul_left ((t + 1) * 2 ^ h - 1)
    (show 2 * (N * d + d * N.factorial) + d * N.factorial + d * N.factorial ≤
      2 * (N * d' + d' * N.factorial) + d' * N.factorial + d' * N.factorial by omega)
  omega

section Pass

variable [DecidableEq α] [Fintype S] [DecidableEq S]

open Classical in
/-- One pass of compression: shorten the class of a designated run of largest period. The other
designated runs survive at their retained cuts, and the processed runs become uncovered
positions, at most `pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E)` each. -/
theorem exists_hole_compressed_step (M : StructuralReader α S k) {U : Fin k → List α}
    (hU : M.IsHole U) {n D E : ℕ}
    (runs : Finset (RunSpec k)) (hcard : runs.card ≤ n + 1) (hruns : ∀ r ∈ runs, IsBoundedRun U D r)
    (hE : ∑ i,
        (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0) ≤ E)
    (hne : runs.Nonempty) :
    ∃ U', M.IsHole U' ∧
      HasBoundedRunCover M U' n D (E + (n + 1) * Periodic.pieceLengthBound (Fintype.card S) D
        (k * (Fintype.card S - 1)) (2 * (n + 1) + E)) := by
  classical
  set N := Fintype.card S with hNdef
  set H := k * (N - 1)
  set T := 2 * (n + 1) + E
  obtain ⟨r0, hr0, hmax⟩ := Finset.exists_max_image runs RunSpec.period hne
  let P0 : Piece U r0.period := Piece.ofIsPeriodicPiece (hruns r0 hr0).1
  have hρ : IsPrimitive P0.root := P0.primitive
  have hρlen : P0.root.length = r0.period := P0.root_length
  set ρ := P0.root with hρdef
  have hρD : ρ.length ≤ D := hρlen ▸ (hruns r0 hr0).2.1
  have hle : ∀ r ∈ runs, r.period ≤ ρ.length := fun r hr => hρlen ▸ hmax r hr
  have hsplit : OccurrenceSplit U ρ H T :=
    occurrenceSplit M hU ρ runs (fun r hr => ⟨(hruns r hr).1, hle r hr⟩) (by
      dsimp [T]; omega)
  obtain ⟨x, hx, hcap⟩ := cap_exists N hρ hsplit
  have hdom := editedTuple_dominates M.toTable hx
  obtain ⟨hU', hends⟩ := StructuralReader.IsHole.of_dominates hU hdom
  have hJ' : ∀ l, M.firstRejection (editedTuple U ρ N x) l =
      keepCut U ρ N x l (M.firstRejection U l) :=
    editedTuple_firstRejection M hU hx
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨M.dead⟩
  -- the class of a designated run
  let same : RunSpec k → Prop :=
      fun r => IsConjugate (((U r.coordinate).drop r.start).take r.period) ρ
  have hsame0 : same r0 := IsConjugate.refl _
  let img : RunSpec k → RunSpec k := fun r =>
    ⟨r.coordinate, keepCut U ρ N x r.coordinate r.start, keepCut U ρ N x r.coordinate r.stop,
        r.period⟩
  let runs' := (runs.filter (fun r => ¬ same r)).image img
  refine ⟨editedTuple U ρ N x, hU', runs', ?_, ?_, ?_⟩
  · -- at least one run fewer
    have : (runs.filter (fun r => ¬ same r)).card < runs.card :=
      Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨r0, hr0, fun h => h hsame0⟩)
    exact Finset.card_image_le.trans (by omega)
  · -- the runs of the other classes survive at their retained cuts
    intro r' hr'
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hr'
    obtain ⟨hr, hns⟩ := Finset.mem_filter.mp hr
    obtain ⟨hpc, hdD, hlong⟩ := hruns r hr
    let R : Piece U r.period := Piece.ofIsPeriodicPiece hpc
    obtain ⟨hin, hleft, hright, -⟩ :=
        exists_preserved_piece_of_nonconjugate_root hx hN R hns (hle r hr)
      (by change ρ.length + r.period ≤ r.stop - r.start; omega)
    obtain ⟨hpc', hke⟩ := isPeriodicPiece_deletePositions (U' := editedTuple U ρ N x)
      (Dl := deletedPositions U ρ N x r.coordinate) rfl hpc hin hleft hright
    refine ⟨hpc', hdD, ?_⟩
    change 2 * D ≤ retainedCount (deletedPositions U ρ N x r.coordinate) r.stop -
        retainedCount (deletedPositions U ρ N x r.coordinate) r.start
    omega
  · -- the letters: original letters and the retained letters of the processed runs
    have hcapD : Periodic.pieceLengthBound N ρ.length H T ≤
        Periodic.pieceLengthBound N D H T :=
        pieceLengthBound_mono hρD
    have hword : ∀ i, (uncoveredTailPositions M (editedTuple U ρ N x) runs' i).card ≤
        (uncoveredTailPositions M U runs i).card +
          Periodic.pieceLengthBound N D H T *
              (runs.filter (fun r => r.coordinate = i ∧ same r)).card := by
      intro i
      have hsub : uncoveredTailPositions M (editedTuple U ρ N x) runs' i ⊆
          ((uncoveredTailPositions M U runs i) ∪
          (runs.filter (fun r => r.coordinate = i ∧ same r)).biUnion
            (fun r => (Finset.Ico r.start r.stop).filter (· ∉ deletedPositions U ρ N x i))).image
              (retainedCount (deletedPositions U ρ N x i)) := by
        intro p' hp'
        simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico] at hp'
        obtain ⟨⟨hJp, hpl⟩, hnc⟩ := hp'
        have hlen' : (editedTuple U ρ N x i).length =
            retainedCount (deletedPositions U ρ N x i) (U i).length := by
          rw [editedTuple, length_deletePositions]
        rw [hlen'] at hpl
        obtain ⟨p, hp, hpD, rfl⟩ := retainedCount_surj hpl
        rw [hJ' i] at hJp
        change retainedCount (deletedPositions U ρ N x i) (M.firstRejection U i) ≤
            retainedCount (deletedPositions U ρ N x i) p at hJp
        have hJp' : M.firstRejection U i ≤ p := by
          by_contra hcon
          have := retainedCount_lt_of_not_mem hpD (show p < M.firstRejection U i by omega)
          omega
        apply Finset.mem_image_of_mem
        by_cases hcov : RunCovers runs i p
        · obtain ⟨r, hr, hrl, h1, h2⟩ := hcov
          by_cases hs : same r
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,
              Finset.mem_filter.mpr ⟨hr, hrl, hs⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h1, h2⟩, hpD⟩⟩)
          · exfalso
            apply hnc
            refine ⟨img r, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hr, hs⟩), hrl,
              ?_, ?_⟩
            · change retainedCount (deletedPositions U ρ N x r.coordinate) r.start ≤
                retainedCount (deletedPositions U ρ N x i) p
              rw [hrl]; exact retainedCount_mono h1
            · change retainedCount (deletedPositions U ρ N x i) p <
                retainedCount (deletedPositions U ρ N x r.coordinate) r.stop
              rw [hrl]; exact retainedCount_lt_of_not_mem hpD h2
        · exact Finset.mem_union_left _ (by
            simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico]
            exact ⟨⟨hJp', hp⟩, hcov⟩)
      refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
          ((Finset.card_biUnion_le_card_mul _ _ _ fun r hr => ?_).trans_eq (Nat.mul_comm _ _)) _)))
      obtain ⟨hr, hrl, hs⟩ := Finset.mem_filter.mp hr
      obtain ⟨hpc, -, -⟩ := hruns r hr
      have hrd : (((U r.coordinate).drop r.start).take r.period).length = r.period := by
        have := hpc.1; have := hpc.2.1; simp; omega
      have hdeq : r.period = ρ.length := by
        have := hs.length_eq; rw [hrd] at this; exact this.symm
      have hpc' : IsPeriodicPiece U ρ.length r.coordinate r.start r.stop := hdeq ▸ hpc
      let R : Piece U ρ.length := Piece.ofIsPeriodicPiece hpc'
      have hRmem : R ∈ piecesOf U ρ := by
        rw [mem_piecesOf]
        change IsConjugate (((U r.coordinate).drop r.start).take ρ.length) ρ
        rw [← hdeq]; exact hs
      have hend := hx.retainedCount_piece_end R
      have hc := hcap R hRmem
      change retainedCount (deletedPositions U ρ N x r.coordinate) r.stop =
          retainedCount (deletedPositions U ρ N x r.coordinate) r.start +
        (r.stop - r.start - Periodic.statePeriodModulus N ρ.length * x R) at hend
      change r.stop - r.start - Periodic.statePeriodModulus N ρ.length * x R ≤
          Periodic.pieceLengthBound N ρ.length H T at hc
      rw [← hrl]
      have hkc :=
          retainedCount_eq_add_card (D := deletedPositions U ρ N x r.coordinate)
              (show r.start ≤ r.stop by
        have := hpc.1; omega)
      omega
    calc ∑ i, (if M.Immortal (M.endState (editedTuple U ρ N x) i) then
            (uncoveredTailPositions M (editedTuple U ρ N x) runs' i).card else 0)
        ≤ ∑ i,
            ((if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0) +
            Periodic.pieceLengthBound N D H T *
              (runs.filter (fun r => r.coordinate = i)).card) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hends i]
          have hf : (runs.filter (fun r => r.coordinate = i ∧ same r)).card ≤
              (runs.filter (fun r => r.coordinate = i)).card :=
            Finset.card_le_card (fun r hr => by
              simp only [Finset.mem_filter] at hr ⊢; exact ⟨hr.1, hr.2.1⟩)
          have := Nat.mul_le_mul_left (Periodic.pieceLengthBound N D H T) hf
          split_ifs
          · have := hword i; omega
          · omega
      _ = (∑ i,
          (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0)) +
            Periodic.pieceLengthBound N D H T * runs.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (RunSpec.coordinate r))]
      _ ≤ E + (n + 1) * Periodic.pieceLengthBound N D H T := by
          have := Nat.mul_le_mul_left (Periodic.pieceLengthBound N D H T) hcard
          rw [Nat.mul_comm (n + 1)]
          omega

end Pass

open Classical in
/-- The tail bound when no designated run is left: every immortal tail is uncovered. -/
theorem tail_le_of_empty (M : StructuralReader α S k) {U : Fin k → List α} {E : ℕ}
    (hE : ∑ i,
        (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U ∅ i).card else 0) ≤ E)
    (i : Fin k) (hi : M.Immortal (M.endState U i)) : M.rejectedTailLength U i ≤ E := by
  have h1 : M.rejectedTailLength U i = (uncoveredTailPositions M U ∅ i).card := by
    simp [uncoveredTailPositions, RunCovers, StructuralReader.rejectedTailLength]
  have h2 := Finset.single_le_sum (f := fun j => if M.Immortal (M.endState U j) then
    (uncoveredTailPositions M U ∅ j).card else 0) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  simp only [ite_eq_left hi] at h2
  omega

/-- The bound after the passes, for `n` remaining designated runs and `E` uncovered positions; a
pass adds the split cap for each of at most `n + 1` processed runs. The head height is
`k * (N - 1)` and the tail count is at most `2 * (n + 1) + E`, so each pass is affine in `E`. -/
def compressionLengthBoundIter (k N D : ℕ) : ℕ → ℕ → ℕ
  | 0, E => E
  | n + 1, E => compressionLengthBoundIter k N D n
      (E + (n + 1) * Periodic.pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E))

theorem le_compressionLengthBoundIter (k N D : ℕ) : ∀ n E, E ≤ compressionLengthBoundIter k N D n E
  | 0, _ => le_rfl
  | n + 1, E => (Nat.le_add_right E _).trans (le_compressionLengthBoundIter k N D n _)

/-- The bound on rejected tails after compressing `k · R` designated runs of period at most `D`
with `E` uncovered positions. -/
def compressionLengthBound (k N R D E : ℕ) : ℕ := compressionLengthBoundIter k N D (k * R) E

section Passes

variable [DecidableEq α] [Fintype S] [DecidableEq S]

/-- At most `n` passes bound every immortal rejected tail by
`compressionLengthBoundIter k N D n E`. -/
theorem exists_hole_tail_le_compressionLengthBoundIter (M : StructuralReader α S k) (D : ℕ)
    (n : ℕ) : ∀ (U : Fin k → List α) (E : ℕ),
    M.IsHole U → HasBoundedRunCover M U n D E →
    ∃ U', M.IsHole U' ∧ ∀ i, M.Immortal (M.endState U' i) → M.rejectedTailLength U' i ≤
      compressionLengthBoundIter k (Fintype.card S) D n E := by
  induction n with
  | zero =>
    rintro U E hU ⟨runs, hcard, -, hE⟩
    have : runs = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    exact ⟨U, hU, fun i hi => tail_le_of_empty M hE i hi⟩
  | succ n ih =>
    rintro U E hU ⟨runs, hcard, hruns, hE⟩
    by_cases hne : runs.Nonempty
    · obtain ⟨U', hU', hcov⟩ := exists_hole_compressed_step M hU runs hcard hruns hE hne
      exact ih U' _ hU' hcov
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      exact ⟨U, hU, fun i hi =>
        (tail_le_of_empty M hE i hi).trans (le_compressionLengthBoundIter _ _ _ _ _)⟩

/-- A hole with a run cover has a hole whose immortal rejected tails have at most
`compressionLengthBound k N R D E` letters. -/
theorem exists_hole_tail_le_compressionLengthBound (M : StructuralReader α S k) {W : Fin k → List α}
    (hW : M.IsHole W) {R D E : ℕ} (hcov : HasScaledRunCover M W R D E) :
    ∃ W', M.IsHole W' ∧ ∀ i, M.Immortal (M.endState W' i) → M.rejectedTailLength W' i ≤
      compressionLengthBound k (Fintype.card S) R D E :=
  exists_hole_tail_le_compressionLengthBoundIter M D (k * R) W E hW hcov

end Passes

/-! ## The bound on rejected tails -/

/-- The bound on rejected tails for an alphabet of size `σ`, `k` coordinates and `N` states. -/
def tailLengthBound (σ k N : ℕ) : ℕ :=
  compressionLengthBound k N ((levelBounds σ k N).pieceCountBase + 3)
      ((levelBounds σ k N).periodBound (levelCount k))
    (uncoveredLengthBound (levelBounds σ k N))

variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]

/-- The bound on rejected tails: a structural reader with `k` starts and `N` states over an
alphabet of size `σ` that has a hole has a hole whose immortal coordinates have rejected tails
of at most `tailLengthBound σ k N` letters. -/
theorem exists_hole_rejectedTailLength_le (M : StructuralReader α S k) {W : Fin k → List α}
    (hW : M.IsHole W) :
    ∃ W', M.IsHole W' ∧ ∀ i, M.Immortal (M.endState W' i) →
      M.rejectedTailLength W' i ≤ tailLengthBound (Fintype.card α) k (Fintype.card S) := by
  obtain ⟨W', hW', hcov⟩ :=
    exists_hole_with_run_cover (levelBounds (Fintype.card α) k (Fintype.card S)) hW
  exact exists_hole_tail_le_compressionLengthBound M hW' hcov

end DeciSigma1.Holes.Tail

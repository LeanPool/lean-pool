/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Tail.RayFamilies
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Holes with run covers

A ray family is turned into a hole. The lengths of the ray prefixes are a natural-number
solution of the ray system above the required lower bounds
(`Arithmetic.DifferenceSystem.exists_long_solution`). Replacing each ray coordinate by its
prefix of that length gives a hole: comparisons between rays carry no admitted pair
(`ray_prefix_hole`), comparisons of a ray with a fixed word are comparisons of original words
(`comparison_of_pumpFactor`), and admitted targets lie at or before the first rejected cut.
The resulting hole has the same first rejected cuts, and the rejected tails of its immortal
coordinates are covered by few designated runs, that is, pieces of bounded period, up to
`uncoveredLengthBound` letters (`exists_hole_with_run_cover`).

## Main declarations

- `RunSpec`, `IsBoundedRun`: designated runs.
- `uncoveredTailPositions`, `HasBoundedRunCover`, `HasScaledRunCover`: covers of rejected tails
  by designated runs.
- `uncoveredLengthBound`: the bound on uncovered positions.
- `exists_hole_with_run_cover`: every hole has a hole with a run cover.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table

variable {α S : Type} {k : ℕ}

/-! ## Designated runs and uncovered tail positions -/

/-- A designated run: the positions `[start, stop)` of the word of `coordinate`, with period
`period`. -/
structure RunSpec (k : ℕ) where
  /-- Coordinate whose word contains the run. -/
  coordinate : Fin k
  /-- First position of the run. -/
  start : ℕ
  /-- Position immediately after the run. -/
  stop : ℕ
  /-- Period assigned to the run. -/
  period : ℕ
  deriving DecidableEq

section Runs

variable [DecidableEq α]

/-- `r` is a designated run of `U`: a piece of period `≤ D` and length `≥ 2D`. -/
def IsBoundedRun (U : Fin k → List α) (D : ℕ) (r : RunSpec k) : Prop :=
  IsPeriodicPiece U r.period r.coordinate r.start r.stop ∧ r.period ≤ D ∧ 2 * D ≤ r.stop - r.start

/-- Position `p` of word `i` lies in a designated run. -/
def RunCovers (runs : Finset (RunSpec k)) (i : Fin k) (p : ℕ) : Prop :=
  ∃ r ∈ runs, r.coordinate = i ∧ r.start ≤ p ∧ p < r.stop

instance (runs : Finset (RunSpec k)) (i : Fin k) (p : ℕ) : Decidable (RunCovers runs i p) :=
  inferInstanceAs (Decidable (∃ r ∈ runs, _))

theorem RunCovers.mono {rs runs : Finset (RunSpec k)} {i : Fin k} {p : ℕ} (h : RunCovers rs i p)
    (hsub : rs ⊆ runs) : RunCovers runs i p :=
  let ⟨r, hr, h1⟩ := h; ⟨r, hsub hr, h1⟩

/-- The tail positions `[J, |U i|)` of word `i` in no designated run. -/
def uncoveredTailPositions (M : StructuralReader α S k) (U : Fin k → List α)
    (runs : Finset (RunSpec k)) (i : Fin k) :
    Finset ℕ :=
  (Finset.Ico (M.firstRejection U i) (U i).length).filter (fun p => ¬ RunCovers runs i p)

/-- At most `n` designated runs of period `≤ D` and length `≥ 2D`, and at most `E` uncovered
tail positions in the immortal words. -/
def HasBoundedRunCover [Fintype α] [Fintype S] [DecidableEq S] (M : StructuralReader α S k)
    (U : Fin k → List α)
    (n D E : ℕ) : Prop :=
  ∃ runs : Finset (RunSpec k), runs.card ≤ n ∧ (∀ r ∈ runs, IsBoundedRun U D r) ∧
    ∑ i, (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0) ≤ E

/-- A run cover with at most `k · R` designated runs, at most `R` for each word. -/
def HasScaledRunCover [Fintype α] [Fintype S] [DecidableEq S] (M : StructuralReader α S k)
    (U : Fin k → List α) (R D E : ℕ) : Prop :=
  HasBoundedRunCover M U (k * R) D E

omit [DecidableEq α] in
/-- Periodic factors to designated runs: a factor of length `≥ 2D` lies in a maximal piece of
period dividing its period; a shorter one is charged by its length. -/
theorem exists_runs_of_cover (U : Fin k → List α) (i : Fin k) {D : ℕ} :
    ∀ fs : List PeriodicFactor, (∀ f ∈ fs, f.Valid (U i) D) →
    ∃ rs : Finset (RunSpec k), rs.card ≤ fs.length ∧
        (∀ r ∈ rs, r.coordinate = i ∧ IsBoundedRun U D r) ∧
      ∃ X : Finset ℕ, X.card ≤ fs.length * (2 * D) ∧
        ∀ p, Covers fs p → RunCovers rs i p ∨ p ∈ X
  | [], _ => by
    classical
    exact ⟨∅, by simp, by simp, ∅, by simp, fun p h => by simp [Covers] at h⟩
  | f :: fs, hfs => by
    classical
    obtain ⟨rs, hrs1, hrs2, X, hX1, hX2⟩ :=
      exists_runs_of_cover U i fs (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
    obtain ⟨hp, hpD, hfe, hper⟩ := hfs f List.mem_cons_self
    by_cases hlong : 2 * D ≤ f.stop - f.start
    · obtain ⟨P, hPl, hPs, hPe, hdvd⟩ := long_factor_in_piece U i hp hfe
        (by have := Nat.mul_le_mul_left 2 hpD; omega) hper
      let r : RunSpec k :=
          ⟨i, P.start, P.stop, leastPeriod (((U i).drop f.start).take (f.stop - f.start))⟩
      have hd : leastPeriod (((U i).drop f.start).take (f.stop - f.start)) ≤ D :=
        (Nat.le_of_dvd hp hdvd).trans hpD
      refine ⟨insert r rs, (Finset.card_insert_le _ _).trans (by simp; omega), ?_, X,
        hX1.trans (Nat.mul_le_mul_right _ (by simp)), ?_⟩
      · intro r' hr'
        rcases Finset.mem_insert.mp hr' with rfl | hr'
        · refine ⟨rfl, ?_, hd, by simp only [r]; omega⟩
          have := P.isPeriodicPiece; rw [hPl] at this; exact this
        · exact hrs2 r' hr'
      · intro p hcov
        rcases covers_cons.mp hcov with hf | hcov
        · exact Or.inl ⟨r, Finset.mem_insert_self _ _, rfl, by simp only [r]; omega,
            by simp only [r]; omega⟩
        · rcases hX2 p hcov with h | h
          · exact Or.inl (h.mono (Finset.subset_insert _ _))
          · exact Or.inr h
    · refine ⟨rs, hrs1.trans (by simp), hrs2, Finset.Ico f.start f.stop ∪ X, ?_, ?_⟩
      · calc (Finset.Ico f.start f.stop ∪ X).card ≤ (Finset.Ico f.start f.stop).card + X.card :=
              Finset.card_union_le _ _
          _ ≤ 2 * D + fs.length * (2 * D) := by simp only [Nat.card_Ico]; omega
          _ = (f :: fs).length * (2 * D) := by simp only [List.length_cons]; ring
      · intro p hcov
        rcases covers_cons.mp hcov with hf | hcov
        · exact Or.inr (Finset.mem_union_left _ (Finset.mem_Ico.mpr hf))
        · rcases hX2 p hcov with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_union_right _ h)

omit [DecidableEq α] in
omit [DecidableEq α] in
/-- Uncovered tail positions after the conversion: uncovered by the factors, or charged. -/
theorem card_uncoveredTailPositions_le (M : StructuralReader α S k) (U : Fin k → List α)
    {runs rs : Finset (RunSpec k)}
    (hsub : rs ⊆ runs) (i : Fin k) {fs : List PeriodicFactor} {X : Finset ℕ}
    (hX : ∀ p, Covers fs p → RunCovers rs i p ∨ p ∈ X) :
    (uncoveredTailPositions M U runs i).card ≤
        (uncoveredPositions fs (M.firstRejection U i) (U i).length).card + X.card := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro p hp
  simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico] at hp
  by_cases hc : Covers fs p
  · rcases hX p hc with h | h
    · exact absurd (h.mono hsub) hp.2
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp [uncoveredPositions, hp.1, hc])

/-- A cover of every immortal tail by `≤ P` factors of period `≤ D` and `≤ T` letters gives
`HasBoundedRunCover` with `k·P` runs and `k (T + P·2D)` letters. -/
theorem hasBoundedRunCover_of_covers [Fintype α] [Fintype S] [DecidableEq S]
    (M : StructuralReader α S k)
    (U : Fin k → List α) {P D T : ℕ}
    (h : ∀ i, M.Immortal (M.endState U i) → PeriodicCover (U i) (M.firstRejection U i) P D T) :
    HasBoundedRunCover M U (k * P) D (k * (T + P * (2 * D))) := by
  classical
  have h2 : ∀ i, ∃ rs : Finset (RunSpec k), rs.card ≤ P ∧
      (∀ r ∈ rs, r.coordinate = i ∧ IsBoundedRun U D r) ∧
      (M.Immortal (M.endState U i) → ∀ runs : Finset (RunSpec k), rs ⊆ runs →
        (uncoveredTailPositions M U runs i).card ≤ T + P * (2 * D)) := by
    intro i
    by_cases him : M.Immortal (M.endState U i)
    · obtain ⟨fs, hfs1, hfs2, hfs3⟩ := h i him
      obtain ⟨rs, hrs1, hrs2, X, hX1, hX2⟩ := exists_runs_of_cover U i fs hfs2
      refine ⟨rs, hrs1.trans hfs1, hrs2, fun _ runs hsub => ?_⟩
      have := card_uncoveredTailPositions_le M U hsub i hX2
      have := Nat.mul_le_mul_right (2 * D) hfs1
      omega
    · exact ⟨∅, by simp, by simp, fun h => absurd h him⟩
  choose rs hrs1 hrs2 hrs3 using h2
  refine ⟨Finset.univ.biUnion rs, ?_, ?_, ?_⟩
  · calc (Finset.univ.biUnion rs).card ≤ ∑ i, (rs i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin k, P := Finset.sum_le_sum fun i _ => hrs1 i
      _ = k * P := by simp
  · intro r hr
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hr
    exact (hrs2 i r hi).2
  · calc ∑ i, (if M.Immortal (M.endState U i) then
            (uncoveredTailPositions M U (Finset.univ.biUnion rs) i).card else 0)
        ≤ ∑ _i : Fin k, (T + P * (2 * D)) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs with him
          · exact hrs3 i him _ (Finset.subset_biUnion_of_mem rs (Finset.mem_univ i))
          · exact Nat.zero_le _
      _ = k * (T + P * (2 * D)) := by simp

end Runs

/-! ## The assembly -/

/-- The bound on the uncovered positions of the rejected tails in `exists_hole_with_run_cover`. -/
def uncoveredLengthBound {σ N : ℕ} (C : LevelBounds σ k N) : ℕ :=
  k * (C.uncoveredBound (levelCount k) + (C.pieceCountBase + 3) * (3 * C.escapeLengthBound
      (levelCount k) + 3) + (C.pieceCountBase + 3) * (2 * C.periodBound (levelCount k)))

section Assembly

variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]

/-- Every hole has a hole whose immortal rejected tails are covered by `pieceCountBase + 3`
designated runs per word, of period at most `D = periodBound (levelCount k)` and length at least
`2D`, up to `uncoveredLengthBound C` positions. -/
theorem exists_hole_with_run_cover (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} (hW : M.IsHole W) :
    ∃ W', M.IsHole W' ∧
      HasScaledRunCover M W' (C.pieceCountBase + 3) (C.periodBound (levelCount k))
          (uncoveredLengthBound C) := by
  classical
  obtain ⟨F⟩ := exists_rayFamily C hW
  have heD : ∀ l, l ≤ F.level → C.periodBound l ≤ C.periodBound (levelCount k) :=
      fun l hl => C.periodBound_mono (hl.trans F.le_top)
  -- the ray lengths: a solution of the ray system above the required lower bounds
  let st : {i // i ∈ F.rays} → S := fun i => M.start i.1
  let J : {i // i ∈ F.rays} → ℕ := fun i => M.firstRejection W i.1
  obtain ⟨L, hsat, hlow⟩ := Arithmetic.DifferenceSystem.exists_long_solution _ F.no_positive_cycle
    (fun i : {i // i ∈ F.rays} => F.endCut i.1 + J i + maxOnset F.ray + 2 * maxPeriod F.ray +
        totalLength W + 1)
  let W' : Fin k → List α := fun i =>
    if h : i ∈ F.rays then streamPrefix (F.ray ⟨i, h⟩).stream (L ⟨i, h⟩) else W i
  have hWr : ∀ i (h : i ∈ F.rays), W' i = streamPrefix (F.ray ⟨i, h⟩).stream (L ⟨i, h⟩) :=
    fun i h => dite_eq_left h
  have hWf : ∀ i, i ∉ F.rays → W' i = W i := fun i h => dite_eq_right h
  have hLc : ∀ i (h : i ∈ F.rays), F.endCut i + M.firstRejection W i + totalLength W <
      L ⟨i, h⟩ := by
    intro i h; have := hlow ⟨i, h⟩; simp only [J] at this; omega
  have hlenr : ∀ i (h : i ∈ F.rays), (W' i).length = L ⟨i, h⟩ := by
    intro i h; rw [hWr i h, length_streamPrefix]
  have hstay : ∀ i (h : i ∈ F.rays),
      W' i = pumpFactor (W i) (F.startCut i) (F.endCut i) (L ⟨i, h⟩ - F.startCut i) := by
    intro i h
    have hcl := F.closed i h
    have := hLc i h
    have := hcl.1
    rw [hWr i h, F.ray_eq i h, ← streamPrefix_repeatFactorRay hcl.1 hcl.2.1]
    congr 1; omega
  have hray : ∀ i (h : i ∈ F.rays), M.Eligible W' i ∧ M.Immortal (M.endState W' i) ∧
      M.firstRejection W' i = M.firstRejection W i := by
    intro i h
    have hcl := F.closed i h
    have := hLc i h
    exact pumpFactor_eligible M (hW.1 i) hcl (F.firstRejection_le_startCut i h) (by omega)
        (hstay i h)
  have helig : ∀ i, M.Eligible W' i := fun i => if h : i ∈ F.rays then (hray i h).1
    else (StructuralReader.eligible_congr (hWf i h)).mpr (hW.1 i)
  have hJ : ∀ i, M.firstRejection W' i = M.firstRejection W i := fun i =>
    if h : i ∈ F.rays then (hray i h).2.2 else StructuralReader.firstRejection_congr (hWf i h)
  -- on the rays, admitted targets lie at or before the first rejected cut
  have hK : ∀ (j : {i // i ∈ F.rays}) b p, b ≤ L j →
      M.admitted p (rayState M (st j) (F.ray j) b) = true → b ≤ J j := by
    intro j b p hb hadm
    have hq : rayState M (st j) (F.ray j) b = M.runPrefix W' j.1 b := by
      simp only [rayState, Table.runPrefix, hWr j.1 j.2, take_streamPrefix, min_eq_left hb, st]
    rw [hq] at hadm
    have :=
        StructuralReader.admitted_target_le_firstRejection (helig j.1)
            (by rw [hlenr j.1 j.2]; exact hb) hadm
    rw [hJ] at this
    exact this
  have hchan : ∀ i j, ∀ pq ∈ M.channel W' i j, M.admitted pq.1 pq.2 = false := by
    intro i j pq hpq
    by_cases hi : i ∈ F.rays <;> by_cases hj : j ∈ F.rays
    · -- ray host, ray target
      have key := ray_prefix_hole (M := M) st F.ray J L hK
        (fun j => by have := hlow j; simp only [J] at this ⊢; omega)
        (fun i a b => F.no_self_admission i.1 i.2 a b) hsat ⟨i, hi⟩ ⟨j, hj⟩ pq
      apply key
      simp only [Table.channel] at hpq
      rw [hWr i hi, hWr j hj] at hpq
      exact hpq
    · -- ray host, fixed target: comparisons of the original words
      have hcl := F.closed i hi
      have := hLc i hi
      have hsub := comparison_of_pumpFactor (T := M.toTable) (qt := M.start j) hcl
        (F.mem_targets j hj) (F.free i hi j hj) (L := L ⟨i, hi⟩ - F.startCut i) (by omega)
      simp only [Table.channel] at hpq
      rw [hstay i hi, hWf j hj] at hpq
      exact hW.2 i j pq (hsub hpq)
    · -- fixed host, ray target: admitted targets and length
      by_contra hadm
      rw [Bool.not_eq_false] at hadm
      obtain ⟨a, ha, b, hb, hpre, rfl⟩ := mem_channel.mp hpq
      have hbJ := StructuralReader.admitted_target_le_firstRejection (helig j) hb hadm
      rw [hJ] at hbJ
      have hl := hpre.length_le
      simp only [List.length_drop, hlenr j hj, hWf i hi] at hl
      have := hLc j hj
      have := length_le_totalLength W i
      omega
    · -- fixed / fixed: unchanged
      rw [Table.channel_congr (hWf i hi) (hWf j hj)] at hpq
      exact hW.2 i j pq hpq
  have hhole : M.IsHole W' := ⟨helig, hchan⟩
  have hend : ∀ i, i ∉ F.rays → M.endState W' i = M.endState W i :=
    fun i h => Table.endState_congr (hWf i h)
  refine ⟨W', hhole, ?_⟩
  -- the run cover
  apply hasBoundedRunCover_of_covers M W'
    (T := C.uncoveredBound (levelCount k) + (C.pieceCountBase + 3) * (3 * C.escapeLengthBound
        (levelCount k) + 3))
  intro i himm
  rw [hJ i]
  have hTt : ∀ l, l ≤ F.level → C.uncoveredBound l ≤ C.uncoveredBound (levelCount k) :=
      fun l hl => C.uncoveredBound_mono (hl.trans F.le_top)
  by_cases h : i ∈ F.rays
  · have hcl := F.closed i h
    have hLi := hLc i h
    have hcc := hcl.1
    have hc' := hcl.2.1
    -- the pumped factor `[c, L)`, with the period of the ray
    let sf : PeriodicFactor := ⟨F.startCut i, L ⟨i, h⟩, (F.ray ⟨i, h⟩).period⟩
    have hsf : sf.Valid (W' i) (C.periodBound (levelCount k)) := by
      refine ⟨Ray.period_pos, (F.period_le_bound i h).trans (heD _ le_rfl), (hlenr i h).ge, ?_⟩
      have hag : RayAgrees (F.ray ⟨i, h⟩) (W' i) (L ⟨i, h⟩) :=
        ⟨(hlenr i h).ge, by rw [hWr i h, List.take_of_length_le (by rw [length_streamPrefix])]⟩
      exact (periodicOn_of_rayAgrees hag).mono
        (by rw [F.ray_eq i h]; exact onset_repeatFactorRay_le hcc hc') le_rfl
    -- letters of the edited word below `c'` are original letters
    have hlet : ∀ q < F.endCut i, (W' i)[q]? = (W i)[q]? := by
      intro q hq
      rw [hstay i h]
      exact getElem?_pumpFactor_of_lt hcc hc' (by omega) hq
    rcases F.cover i h with ⟨hc'eq, hcov⟩ | hcov
    · -- terminal ray: its cover of `[J, |w|)` and the pumped factor
      refine (((hcov.mono le_rfl (heD _ (by omega)) le_rfl).cons_of_agree hsf
        (show F.startCut i ≤ _ by omega) (hlenr i h).symm
        (by rw [hlenr i h]; omega) fun q hq => hlet q (by omega)).mono (by omega) le_rfl ?_)
      exact (hTt _ (by omega)).trans (Nat.le_add_right _ _)
    · -- other ray: its cover of `[J, c)` and the pumped factor
      have hlc : ((W i).take (F.startCut i)).length = F.startCut i := by simp; omega
      refine (((hcov.mono le_rfl (heD _ le_rfl) le_rfl).cons_of_agree hsf
        hlc.ge (hlenr i h).symm
        (by rw [hlc, hlenr i h]; omega) fun q hq => ?_).mono (by omega) le_rfl ?_)
      · rw [hlc] at hq
        rw [hlet q (by omega), List.getElem?_take_of_lt hq]
      · have := Nat.mul_le_mul_left (C.pieceCountBase + 3) (Nat.add_le_add_right
          (Nat.mul_le_mul_left 3 (C.escapeLengthBound_mono F.le_top)) 3)
        omega
  · -- fixed immortal word: its cover at level `l - 2`
    rcases F.fixed i h with hm | hKp
    · exact absurd (by rwa [← hend i h]) hm
    rw [hWf i h]
    exact hKp.1.mono (by omega) (heD _ (by omega)) ((hTt _ (by omega)).trans (Nat.le_add_right _ _))

end Assembly

end DeciSigma1.Holes.Tail

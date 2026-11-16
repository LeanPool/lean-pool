/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Tail.Candidates
public import LeanPool.DeciSigma1.Holes.Tail.WindowChains

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Families of rays

At a stable level `l` (`exists_stable_level`), the coordinates of a hole split into fixed ones,
which have a mortal endpoint or the level cover property at level `l - 2`, and coordinates that
are continued by rays. A coordinate with a long periodic suffix gets a terminal ray
(`exists_terminal_ray`); the others are processed in turn (`exists_greedy_choice`), each taking
a candidate without forbidden overlaps with the rays chosen before
(`exists_compatible_rayCandidate`). Every ray is the ray of a factor after the first rejected
cut that is closed for the suffix dictionary of the fixed words (a terminal ray is closed at a
window, which suffices by `ClosedAt.nodeClosedAt`) and free of the suffixes of the fixed words,
and the resulting ray system has no positive cycle (`exists_rayFamily`).

## Main declarations

- `exists_greedy_choice`: values chosen one coordinate at a time, compatible with each other.
- `RayFamily`: a family of rays with the properties used to assemble a hole.
- `exists_rayFamily`: every hole has a ray family at a stable level.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

/-! ## Greedy choice -/

/-- Greedy choice of values for the coordinates of `P`, given the values `Ω₀` on a disjoint set
`U₀`. Suppose that for each `v ∈ P` and any admissible values (`Adm`) on a set `U` of other
coordinates, some good value (`Good`) for `v` is compatible (`Compat`) with all of them, that
good values are admissible, and that compatibility between good values is symmetric. Then some
values, equal to `Ω₀` on `U₀` and good on `P`, make the value of each `v ∈ P` compatible with
the value of every other coordinate of `U₀ ∪ P`. -/
theorem exists_greedy_choice {ι ρ : Type*} [DecidableEq ι] {U₀ P : Finset ι}
    (hdisj : Disjoint U₀ P) (Ω₀ : ι → ρ) (Adm Good : ι → ρ → Prop)
    (Compat : ι → ρ → ι → ρ → Prop) (hU₀ : ∀ u ∈ U₀, Adm u (Ω₀ u))
    (hAdm : ∀ v ∈ P, ∀ x, Good v x → Adm v x)
    (hsymm : ∀ v ∈ P, ∀ w ∈ P, ∀ x y, Good v x → Good w y → Compat v x w y → Compat w y v x)
    (hstep : ∀ v ∈ P, ∀ (U : Finset ι) (Ω : ι → ρ), v ∉ U → (∀ u ∈ U, Adm u (Ω u)) →
      ∃ x, Good v x ∧ ∀ u ∈ U, Compat v x u (Ω u)) :
    ∃ Ω : ι → ρ, (∀ u ∈ U₀, Ω u = Ω₀ u) ∧ (∀ v ∈ P, Good v (Ω v)) ∧
      ∀ v ∈ P, ∀ u ∈ U₀ ∪ P, u ≠ v → Compat v (Ω v) u (Ω u) := by
  suffices h : ∀ Q ⊆ P, ∃ Ω : ι → ρ, (∀ u ∈ U₀, Ω u = Ω₀ u) ∧ (∀ v ∈ Q, Good v (Ω v)) ∧
      ∀ v ∈ Q, ∀ u ∈ U₀ ∪ Q, u ≠ v → Compat v (Ω v) u (Ω u) from h P subset_rfl
  intro Q
  induction Q using Finset.induction_on with
  | empty => exact fun _ => ⟨Ω₀, fun _ _ => rfl, by simp, by simp⟩
  | insert v Q hvQ ih =>
    intro hsub
    have hvP := hsub (Finset.mem_insert_self v Q)
    have hQP : Q ⊆ P := (Finset.subset_insert v Q).trans hsub
    obtain ⟨Ω, hΩ₀, hgood, hcompat⟩ := ih hQP
    have hvU : v ∉ U₀ ∪ Q := by
      simp [Finset.disjoint_right.mp hdisj hvP, hvQ]
    obtain ⟨x, hx, hxc⟩ := hstep v hvP (U₀ ∪ Q) Ω hvU fun u hu => by
      rcases Finset.mem_union.mp hu with hu | hu
      · rw [hΩ₀ u hu]; exact hU₀ u hu
      · exact hAdm u (hQP hu) _ (hgood u hu)
    have hne : ∀ u ∈ U₀ ∪ Q, u ≠ v := by rintro u hu rfl; exact hvU hu
    have hupd : ∀ u ∈ U₀ ∪ Q, Function.update Ω v x u = Ω u :=
      fun u hu => Function.update_of_ne (hne u hu) _ _
    refine ⟨Function.update Ω v x, fun u hu => ?_, fun w hw => ?_, fun w hw u hu huw => ?_⟩
    · rw [hupd u (Finset.mem_union_left _ hu), hΩ₀ u hu]
    · rcases Finset.mem_insert.mp hw with rfl | hwQ
      · rwa [Function.update_self]
      · rw [hupd w (Finset.mem_union_right _ hwQ)]; exact hgood w hwQ
    have hu' : u = v ∨ u ∈ U₀ ∪ Q := by
      simp only [Finset.mem_union, Finset.mem_insert] at hu ⊢; tauto
    rcases Finset.mem_insert.mp hw with rfl | hwQ
    · rcases hu' with rfl | huU
      · exact absurd rfl huw
      · rw [Function.update_self, hupd u huU]; exact hxc u huU
    · rw [hupd w (Finset.mem_union_right _ hwQ)]
      rcases hu' with rfl | huU
      · rw [Function.update_self]
        exact hsymm _ hvP _ (hQP hwQ) _ _ hx (hgood w hwQ) (hxc w (Finset.mem_union_right _ hwQ))
      · rw [hupd u huU]; exact hcompat w hwQ u huU huw

/-! ## Ray families -/

/-- A family of rays for a hole at a stable level `l`. The coordinates split into fixed ones,
with a mortal endpoint or the level cover property at level `l - 2`, and rays. Each ray is the
ray of a factor after the first rejected cut that is closed for the suffix dictionary of a list
of targets containing every fixed word, free of the suffixes of every fixed word, and has period
at most `periodBound l`. A ray of a coordinate with a long periodic suffix keeps
the whole original word and its periodic cover at level `l - 1`; any other ray carries a cover
of the tail before its factor. The rays make no new comparison with themselves, and their
difference system has no positive cycle. -/
structure RayFamily [DecidableEq α] [Fintype S] {σ : ℕ}
    (C : LevelBounds σ k (Fintype.card S)) (M : StructuralReader α S k) (W : Fin k → List α) where
  /-- Common hierarchy level of the family. -/
  level : ℕ
  le_top : level ≤ levelCount k
  /-- Coordinates represented by infinite rays. -/
  rays : Finset (Fin k)
  /-- Suffix-window length for each ray coordinate. -/
  windowLength : Fin k → ℕ
  /-- Initial ray cut for each coordinate. -/
  startCut : Fin k → ℕ
  /-- Final ray cut for each coordinate. -/
  endCut : Fin k → ℕ
  /-- Infinite periodic continuation assigned to each ray coordinate. -/
  ray : {i // i ∈ rays} → Ray α
  /-- Finite target words used in the suffix dictionary. -/
  targets : List (List α)
  fixed : ∀ j, j ∉ rays → ¬ M.Immortal (M.endState W j) ∨ LevelCoverProperty C (level - 2) M W j
  mem_targets : ∀ j, j ∉ rays → W j ∈ targets
  closed : ∀ i ∈ rays, NodeClosedAt M.toTable (M.start i)
    (suffixDictionary targets (windowLength i)) (W i) (startCut i) (endCut i)
  ray_eq : ∀ i (hi : i ∈ rays),
    ray ⟨i, hi⟩ = repeatFactorRay (W i) (startCut i) (endCut i) (closed i hi).1 (closed i hi).2.1
  firstRejection_le_startCut : ∀ i ∈ rays, M.firstRejection W i ≤ startCut i
  free : ∀ i ∈ rays, ∀ j, j ∉ rays →
      NoSuffixOccurrenceEndsBetween (W i) (W j) (windowLength i) (startCut i) (endCut i)
  period_le_bound : ∀ i (hi : i ∈ rays), (ray ⟨i, hi⟩).period ≤ C.periodBound level
  cover : ∀ i ∈ rays, (endCut i = (W i).length ∧ CoordinateCover C (level - 1) M W i) ∨
    PeriodicCover ((W i).take (startCut i)) (M.firstRejection W i) (C.pieceCountBase + 2)
        (C.periodBound level) ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound level + 3))
  no_self_admission : ∀ i (hi : i ∈ rays), ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
    M.admitted (rayState M (M.start i) (ray ⟨i, hi⟩) a) (rayState M (M.start i) (ray ⟨i, hi⟩) b) =
        true →
    ¬ ∀ t, (ray ⟨i, hi⟩).stream (a + t) = (ray ⟨i, hi⟩).stream (b + t)
  no_positive_cycle : ¬ (raySystem M (fun i : {i // i ∈ rays} => M.start i.1) ray
    (fun i => M.firstRejection W i.1)).HasPositiveCycle

/-- The cuts of a factor `[startCut, endCut)` of a word, with a window of `windowLength` letters
before it. -/
structure FactorCuts where
  /-- Suffix-window length used by the periodic factor. -/
  windowLength : ℕ
  /-- Cut immediately before the factor. -/
  startCut : ℕ
  /-- Cut immediately after the factor. -/
  endCut : ℕ

/-- A total version of `repeatFactorRay` (a default ray when the factor is empty). -/
def mkRay (dflt : Ray α) (x : List α) (c c' : ℕ) : Ray α :=
  if h : c < c' ∧ c' ≤ x.length then repeatFactorRay x c c' h.1 h.2 else dflt

theorem mkRay_eq {dflt : Ray α} {x : List α} {c c' : ℕ} (h : c < c' ∧ c' ≤ x.length) :
    mkRay dflt x c c' = repeatFactorRay x c c' h.1 h.2 := dite_eq_left h

section Family

variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]

/-- Every hole has a ray family at a stable level. Terminal rays come from
`exists_terminal_ray` at level `l - 1`; the other rays are chosen in turn
(`exists_greedy_choice`), each a candidate without forbidden overlaps with the rays chosen
before (`exists_compatible_rayCandidate`). Compatibility is symmetric (`compatible_symm`), so
`rays_no_positiveCycle` applies. -/
theorem exists_rayFamily (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k} {W : Fin k → List α} (hW : M.IsHole W) : Nonempty
        (RayFamily C M W) := by
  classical
  obtain ⟨l, hl2, hlt, hst⟩ := exists_stable_level C M W hW.1
  -- the coordinates continued by rays: immortal, without the level cover property at `l - 2`
  let IsRay : Fin k → Prop := fun i =>
    M.Immortal (M.endState W i) ∧ ¬ LevelCoverProperty C (l - 2) M W i
  have hfixed : ∀ j, ¬ IsRay j →
      ¬ M.Immortal (M.endState W j) ∨ LevelCoverProperty C (l - 2) M W j := fun j hj => by
    by_cases h : M.Immortal (M.endState W j)
    · exact .inr (by_contra fun h' => hj ⟨h, h'⟩)
    · exact .inl h
  -- without letters every coordinate is mortal, and the family has no rays
  by_cases hα : IsEmpty α
  · have hmort : ∀ j, ¬ M.Immortal (M.endState W j) := fun j h => by
      obtain ⟨u, hu, -⟩ := h 1
      exact hα.false (u.head (List.ne_nil_of_length_pos (by omega)))
    exact ⟨{
      level := l, le_top := hlt, rays := ∅, windowLength := 0, startCut := 0,
      endCut := 0, ray := fun i => absurd i.2 (Finset.notMem_empty _), targets := List.ofFn W,
      fixed := fun j _ => .inl (hmort j), mem_targets := fun j _ => List.mem_ofFn.mpr ⟨j, rfl⟩,
      no_positive_cycle := by rintro ⟨i, -⟩; exact absurd i.2 (Finset.notMem_empty _),
      closed := by simp, ray_eq := by simp,
      firstRejection_le_startCut := by simp, free := by simp, period_le_bound := by simp,
      cover := by simp, no_self_admission := by simp }⟩
  obtain ⟨a0⟩ := not_isEmpty_iff.mp hα
  let mk : Fin k → FactorCuts → Ray α := fun i f =>
    mkRay ⟨[], [a0], List.cons_ne_nil _ _⟩ (W i) f.startCut f.endCut
  have hmk : ∀ i f (h : f.startCut < f.endCut ∧ f.endCut ≤ (W i).length),
      mk i f = repeatFactorRay (W i) f.startCut f.endCut h.1 h.2 :=
    fun i f h => mkRay_eq h
  -- the rays chosen earlier must agree with their words (`exists_compatible_rayCandidate`);
  -- this holds for the ray of a closed factor after the first rejected cut
  let Adm : Fin k → FactorCuts → Prop := fun u f =>
    RayAgrees (mk u f) (W u) f.endCut ∧ (mk u f).onset ≤ f.endCut ∧
      M.firstRejection W u ≤ f.endCut ∧
      ((mk u f).onset ≤ M.firstRejection W u → (mk u f).period ≤ C.periodBound (l - 1))
  have hadm : ∀ u f (h : f.startCut < f.endCut ∧ f.endCut ≤ (W u).length),
      M.firstRejection W u ≤ f.startCut →
      ((mk u f).onset ≤ M.firstRejection W u → (mk u f).period ≤ C.periodBound (l - 1)) →
      Adm u f := by
    intro u f h hJ hper
    refine ⟨?_, ?_, by have := h.1; omega, hper⟩ <;> rw [hmk u f h]
    · exact repeatFactorRay_agrees _ _
    · have := onset_repeatFactorRay_le h.1 h.2; have := h.1; omega
  -- terminal rays (coordinates with a cover at level `l - 1`) and the other rays
  let Tset := Finset.univ.filter fun i => IsRay i ∧ CoordinateCover C (l - 1) M W i
  let Mset := Finset.univ.filter fun i => IsRay i ∧ ¬ CoordinateCover C (l - 1) M W i
  have hdisj : Disjoint Tset Mset := Finset.disjoint_filter.mpr fun _ _ h h' => h'.2 h.2
  have hmem : ∀ i, i ∈ Tset ∪ Mset ↔ IsRay i := fun i => by
    by_cases h : CoordinateCover C (l - 1) M W i <;> simp [Tset, Mset, h]
  -- the fixed words, as targets; all their chains have at most `fixedChainBudget l` steps
  let ts : List (List α) := ((Finset.univ.filter fun j => ¬ IsRay j).toList).map W
  have hts : ts.length ≤ k := by
    simpa [ts] using (Finset.card_filter_le Finset.univ _).trans_eq (Finset.card_fin k)
  have hfixCB : ∀ j, ¬ IsRay j → ChainBound (W j) (C.fixedChainBudget l) := by
    intro j hj
    rcases hfixed j hj with hm | hK
    · exact (chainBound_mortal (hW.1 j) hm).mono
        (by have := C.stateCount_le_fixedChainBudget l; omega)
    · have hSl := C.fixedChainBudget_ge_chainLength (l - 2)
      rw [show l - 2 + 2 = l by omega] at hSl
      exact (levelCoverProperty_chainBound C (hW.1 j) hK).mono hSl
  -- from the initial window of the level on, their chains have at most `Q + N` steps
  have hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S) := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    rcases hfixed j (by simpa using hj) with hm | hK
    · exact ((chainBound_mortal (hW.1 j) hm).chainBoundFrom _).mono le_rfl (by omega)
    · have hb := C.chainWindow_le_startWindow (l - 2)
      rw [show l - 2 + 2 = l by omega] at hb
      exact levelCoverProperty_chainBoundFrom C (hW.1 j) hK hb
  -- the terminal ray of each coordinate of `Tset`, from `exists_terminal_ray` at level `l - 1`
  have hterm : ∀ i, ∃ f : FactorCuts, i ∈ Tset →
      ClosedAt M.toTable (M.start i) (W i) f.windowLength f.startCut f.endCut ∧
      f.endCut = (W i).length ∧ M.firstRejection W i ≤ f.startCut ∧
      (mk i f).period ≤ C.periodBound (l - 1) ∧ ∀ t, ChainBound t (C.fixedChainBudget l) →
        NoSuffixOccurrenceEndsBetween (W i) t f.windowLength f.startCut f.endCut := by
    intro i
    by_cases hi : i ∈ Tset
    · obtain ⟨hray, hcov⟩ := (Finset.mem_filter.mp hi).2
      have hlong : C.terminalLengthBound (l - 1) ≤
          longestPeriodicSuffixLength (C.periodBound (l - 1)) (W i) := by
        by_contra h; exact hray.2 ((hst i).2.mpr ⟨hcov, by omega⟩)
      obtain ⟨B, c, p, hcl, hJc, hp, hpl, hlen, hper, hfree⟩ :=
        exists_terminal_ray C (hW.1 i) hlong
      rw [show l - 1 + 1 = l by omega] at hfree
      refine ⟨⟨B, c, (W i).length⟩, fun _ => ⟨hcl, rfl, hJc, ?_, hfree⟩⟩
      rw [hmk i _ ⟨hcl.2.1, hcl.2.2.1⟩]
      exact (Ray.period_le_of_periodicFrom hp
        (repeatFactorRay_periodicFrom hcl hp (Dvd.intro _ hlen.symm) hper)).trans hpl
    · exact ⟨⟨0, 0, 0⟩, fun h => absurd h hi⟩
  choose Ω₀ hΩ₀ using hterm
  -- the other rays, one coordinate at a time, each a good candidate
  let Good : Fin k → FactorCuts → Prop := fun v f =>
    NodeClosedAt M.toTable (M.start v) (suffixDictionary ts f.windowLength) (W v) f.startCut
      f.endCut ∧
      M.firstRejection W v ≤ f.startCut ∧ f.endCut - f.startCut ≤ C.periodBound l ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween (W v) t f.windowLength f.startCut f.endCut) ∧
      M.firstRejection W v < (mk v f).onset ∧
      PeriodicCover ((W v).take f.startCut) (M.firstRejection W v) (C.pieceCountBase + 2)
        (C.periodBound l) ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3))
  obtain ⟨Ω, hΩT, hΩM, hΩc⟩ := exists_greedy_choice hdisj Ω₀ Adm Good
    (fun v f u g => NoForbiddenRayOverlap (mk v f) (mk u g) (M.firstRejection W v)
      (M.firstRejection W u))
    (fun u hu => let h := hΩ₀ u hu; hadm u _ ⟨h.1.2.1, h.1.2.2.1⟩ h.2.2.1 fun _ => h.2.2.2.1)
    (fun v _ f hf => hadm v f ⟨hf.1.1, hf.1.2.1⟩ hf.2.1 fun h =>
      absurd h (not_le.mpr hf.2.2.2.2.1))
    (fun _ _ _ _ _ _ hf hg h => compatible_symm hf.2.2.2.2.1 hg.2.2.2.2.1 h)
    (fun v hv U Ω' hvU hU => by
      obtain ⟨x, -, hx2, hx3, hx4, hx5, hx6, hx7⟩ := exists_compatible_rayCandidate C hW
        (by omega : 1 ≤ l) (fun h => (Finset.mem_filter.mp hv).2.2 ((hst v).1.mpr h)) ts hts hS
        U hvU (fun u => mk u (Ω' u)) (fun u => (Ω' u).endCut) hU
      have hx : mk v ⟨x.windowLength, x.startCut, x.endCut⟩ = x.ray :=
        hmk v _ ⟨x.closed.1, x.closed.2.1⟩
      refine ⟨⟨x.windowLength, x.startCut, x.endCut⟩, ⟨x.closed, hx2, hx3, hx4, ?_, hx6⟩,
        fun u hu => ?_⟩
      · rw [hx]; exact hx5
      · show NoForbiddenRayOverlap (mk v _) _ _ _
        rw [hx]; exact hx7 u hu)
  -- the family
  have hclosed : ∀ i ∈ Tset ∪ Mset,
      NodeClosedAt M.toTable (M.start i) (suffixDictionary ts (Ω i).windowLength) (W i)
        (Ω i).startCut (Ω i).endCut := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]
      exact (hΩ₀ i h).1.nodeClosedAt nil_mem_suffixDictionary
        fun _ hr => length_le_of_mem_suffixDictionary hr
    · exact (hΩM i h).1
  have hagT : ∀ i ∈ Tset, RayAgrees (mk i (Ω i)) (W i) (W i).length := fun i h => by
    rw [hΩT i h, ← (hΩ₀ i h).2.1]
    exact (hadm i _ ⟨(hΩ₀ i h).1.2.1, (hΩ₀ i h).1.2.2.1⟩ (hΩ₀ i h).2.2.1
      fun _ => (hΩ₀ i h).2.2.2.1).1
  refine ⟨{
    level := l, le_top := hlt, rays := Tset ∪ Mset,
    windowLength := fun i => (Ω i).windowLength, startCut := fun i => (Ω i).startCut,
    endCut := fun i => (Ω i).endCut, ray := fun i => mk i.1 (Ω i.1), targets := ts,
    fixed := fun j hj => hfixed j fun h => hj ((hmem j).mpr h),
    mem_targets := fun j hj => List.mem_map.mpr ⟨j, by
      simpa using fun h => hj ((hmem j).mpr h), rfl⟩, closed := hclosed,
    ray_eq := fun i hi => hmk i _ ⟨(hclosed i hi).1, (hclosed i hi).2.1⟩,
    firstRejection_le_startCut := fun i hi => ?_, free := fun i hi j hj => ?_,
    period_le_bound := fun i hi => ?_, cover := fun i hi => ?_,
    no_self_admission := fun i hi => ?_, no_positive_cycle := ?_ }⟩
  · rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact (hΩ₀ i h).2.2.1
    · exact (hΩM i h).2.1
  · have hj' : ¬ IsRay j := fun h => hj ((hmem j).mpr h)
    rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact (hΩ₀ i h).2.2.2.2 (W j) (hfixCB j hj')
    · exact (hΩM i h).2.2.2.1 (W j) (List.mem_map.mpr ⟨j, by simpa using hj', rfl⟩)
  · rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact (hΩ₀ i h).2.2.2.1.trans (C.periodBound_mono (by omega))
    · rw [hmk i _ ⟨(hΩM i h).1.1, (hΩM i h).1.2.1⟩]
      exact (period_repeatFactorRay_le _ _).trans (hΩM i h).2.2.1
  · rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact .inl ⟨(hΩ₀ i h).2.1, (Finset.mem_filter.mp h).2.2⟩
    · exact .inr (hΩM i h).2.2.2.2.2
  · rcases Finset.mem_union.mp hi with h | h
    · exact terminalRay_no_selfAdmission hW (hagT i h)
    · have hg := hΩM i h
      exact rayCandidate_no_selfAdmission hW
        (hadm i _ ⟨hg.1.1, hg.1.2.1⟩ hg.2.1 fun h => absurd h (not_le.mpr hg.2.2.2.2.1)).1
        (by have := hg.1.1; omega) hg.2.2.2.2.1
  · apply rays_no_positiveCycle M _ _ _ (fun i => ((W i.1).length : ℤ)) (fun i => i.1 ∈ Mset)
    · exact fun v hv => ⟨(hΩM v.1 hv).2.2.2.2.1,
        fun u huv => hΩc v.1 hv u.1 u.2 fun h => huv (Subtype.ext h)⟩
    · intro i j hi hj _ a b hb hadm heq
      exact terminalRay_admission_edge hW (hagT i.1 ((Finset.mem_union.mp i.2).resolve_right hi))
        (hagT j.1 ((Finset.mem_union.mp j.2).resolve_right hj)) hb hadm heq

end Family

end DeciSigma1.Holes.Tail

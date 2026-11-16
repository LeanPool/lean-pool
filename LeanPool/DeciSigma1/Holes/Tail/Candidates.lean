/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Tail.RayCompatibility
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Candidate rays

A coordinate whose rejected tail has no periodic cover at a level is continued by the ray of a
closed factor found in its tail. A `RayCandidate` of a word is a factor closed for the suffix
dictionary of the targets at a window, and longer than that window; its ray repeats the factor
forever. Since the window is larger than `N + 1` periods of the earlier levels, the ray agrees with
the word on a long run after its onset. If the tail has no periodic cover at level `l`, every
segment of `escapeLengthBound l` cuts after the first rejected cut contains a closed factor free of
the suffixes of the targets (`Holes.Tail.ClosedFactors`), and many of these candidates have distinct
onsets after the first rejected cut (`exists_many_rayCandidates`). Each ray chosen earlier excludes
few candidates (`Holes.Tail.RayCompatibility`), so a candidate without forbidden overlaps with all
of them exists (`exists_compatible_rayCandidate`).

The rays of candidates make no new comparisons with themselves
(`rayCandidate_no_selfAdmission`), and the ray system of compatible rays has no positive cycle
(`rays_no_positiveCycle`).

## Main declarations

- `RayCandidate`, `RayCandidate.ray`: candidates and their rays.
- `exists_many_rayCandidates`: many candidates with distinct onsets.
- `exists_compatible_rayCandidate`: a candidate compatible with the rays chosen before.
- `rayCandidate_no_selfAdmission`, `rays_no_positiveCycle`: the ray system of compatible rays is
  feasible.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

/-! ## Candidates -/

/-- A candidate of word `v` for the targets `ts`: a factor `[startCut, endCut)` longer than
`windowLength` and closed for the suffix dictionary of `ts` at window `windowLength`. -/
structure RayCandidate [DecidableEq α] (M : StructuralReader α S k) (W : Fin k → List α)
    (ts : List (List α)) (v : Fin k) where
  /-- Maximum suffix length in the ray's dictionary. -/
  windowLength : ℕ
  /-- Cut where the ray segment starts. -/
  startCut : ℕ
  /-- Cut where the ray segment ends. -/
  endCut : ℕ
  closed : NodeClosedAt M.toTable (M.start v) (suffixDictionary ts windowLength) (W v) startCut
    endCut
  windowLength_lt : windowLength < endCut - startCut

namespace RayCandidate

variable [DecidableEq α] {M : StructuralReader α S k} {W : Fin k → List α} {ts : List (List α)}
  {v : Fin k}

/-- The ray of a candidate: the word up to the factor, followed by the factor repeated
forever. -/
def ray (x : RayCandidate M W ts v) :
    Ray α := repeatFactorRay (W v) x.startCut x.endCut x.closed.1 x.closed.2.1

theorem agrees (x : RayCandidate M W ts v) :
    RayAgrees x.ray (W v) x.endCut := repeatFactorRay_agrees _ _

theorem onset_le (x : RayCandidate M W ts v) : x.ray.onset ≤ x.startCut :=
  onset_repeatFactorRay_le _ _

theorem period_le (x : RayCandidate M W ts v) : x.ray.period ≤ x.endCut - x.startCut :=
  period_repeatFactorRay_le _ _

end RayCandidate

/-! ## Counting tools -/

/-- If `f` takes at least `K` values on `Fin n`, some initial segment `{i | i < m}` has exactly
`K` values, and they are taken injectively on a set `R` of `K` indices of the segment. -/
theorem exists_initialSegment_transversal {β : Type*} [DecidableEq β] {n K : ℕ} (f : Fin n → β)
    (hK : K ≤ (Finset.univ.image f).card) :
    ∃ (m : ℕ) (R : Finset (Fin n)), (∀ i ∈ R, i.val < m) ∧ Set.InjOn f R ∧ R.card = K ∧
      ((Finset.univ.filter fun i : Fin n => i.val < m).image f).card = K := by
  classical
  set pre : ℕ → Finset (Fin n) := fun m => Finset.univ.filter fun i => i.val < m
  -- the number of values on `pre m` grows by at most one with `m`
  have hstep : ∀ m, ((pre (m + 1)).image f).card ≤ ((pre m).image f).card + 1 := by
    intro m
    have : pre (m + 1) = pre m ∪ Finset.univ.filter fun i => i.val = m := by
      ext i; simp only [pre, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [this, Finset.image_union]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le.trans ?_) _)
    exact Finset.card_le_one.mpr fun i hi j hj => Fin.ext (by simp at hi hj; omega)
  have hvalue : ∀ m, K ≤ ((pre m).image f).card → ∃ m', ((pre m').image f).card = K := by
    intro m
    induction m with
    | zero => intro h; exact ⟨0, by simp [pre] at h ⊢; omega⟩
    | succ m ih =>
      intro h
      by_cases h' : K ≤ ((pre m).image f).card
      · exact ih h'
      · exact ⟨m + 1, by have := hstep m; omega⟩
  obtain ⟨m, hm⟩ := hvalue n (by simp only [pre]; rwa [Finset.filter_true_of_mem fun i _ => i.isLt])
  obtain ⟨R, hRm, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (↑(pre m))
    ((pre m).image f) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨m, R, fun i hi => (Finset.mem_filter.mp (hRm hi)).2, hinj, ?_, hm⟩
  rw [← Finset.card_image_of_injOn hinj, himg, hm]

/-- Rays that agree with `x` up to their ends `E i`, with periods at most `P`, give one periodic
factor of `x` for each onset: it runs from the onset to the furthest end among the rays with that
onset, cut at `cap ≤ |x|`. Every position below `cap` from the onset to the end of one of the
rays is covered. -/
theorem exists_periodicFactors_of_rays [DecidableEq α] {ι : Type*} (s : Finset ι)
    (Ω : ι → Ray α) (E : ι → ℕ) {x : List α} {P cap : ℕ}
    (hag : ∀ i ∈ s, RayAgrees (Ω i) x (E i)) (hP : ∀ i ∈ s, (Ω i).period ≤ P)
    (hcap : cap ≤ x.length) :
    ∃ fs : List PeriodicFactor, fs.length = (s.image fun i => (Ω i).onset).card ∧
      (∀ f ∈ fs, f.Valid x P ∧ f.stop ≤ cap) ∧
      ∀ i ∈ s, ∀ y, (Ω i).onset ≤ y → y < E i → y < cap → Covers fs y := by
  classical
  -- for each onset, the end and the period of a ray with that onset reaching furthest
  have hbest : ∀ a, ∃ e p : ℕ, a ∈ s.image (fun i => (Ω i).onset) → ∃ i ∈ s,
      (Ω i).onset = a ∧ E i = e ∧ (Ω i).period = p ∧ ∀ j ∈ s, (Ω j).onset = a → E j ≤ e := by
    intro a
    by_cases ha : a ∈ s.image fun i => (Ω i).onset
    · obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨i, hi, hmax⟩ := (s.filter fun j => (Ω j).onset = (Ω i0).onset).exists_max_image E
        ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩
      rw [Finset.mem_filter] at hi
      exact ⟨E i, (Ω i).period, fun _ => ⟨i, hi.1, hi.2, rfl, rfl,
        fun j hj hja => hmax j (Finset.mem_filter.mpr ⟨hj, hja⟩)⟩⟩
    · exact ⟨0, 0, fun h => absurd h ha⟩
  choose e p hep using hbest
  refine ⟨(s.image fun i => (Ω i).onset).toList.map fun a => ⟨a, min (e a) cap, p a⟩,
    by simp, fun f hf => ?_, fun i hi y hy hyE hycap => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
    obtain ⟨i, hi, rfl, hie, hip, -⟩ := hep a (Finset.mem_toList.mp ha)
    rw [← hie, ← hip]
    exact ⟨⟨Ray.period_pos, hP i hi, (min_le_right _ _).trans hcap,
      (periodicOn_of_rayAgrees (hag i hi)).mono le_rfl (min_le_left _ _)⟩, min_le_right _ _⟩
  · have ha : (Ω i).onset ∈ s.image fun i => (Ω i).onset := Finset.mem_image_of_mem _ hi
    obtain ⟨-, -, -, -, -, hmax⟩ := hep _ ha
    exact ⟨_, List.mem_map.mpr ⟨_, Finset.mem_toList.mpr ha, rfl⟩, hy,
      lt_min (hyE.trans_le (hmax i hi rfl)) hycap⟩

section Selection

variable [DecidableEq α] [Fintype α] [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- A word whose rejected tail has no periodic cover at level `l` has candidates, one closed
factor in each segment of `escapeLengthBound l` cuts after the first rejected cut, free of the
suffixes of every target whose chains from `startWindow l` on have at most `Q + N` steps, where
`Q = pieceCountBase`. At least `Q - 1` of the candidates have pairwise distinct onsets after the
first rejected cut. All of them are among the first `Q + 2` distinct onsets, so for each the
tail before its factor is covered by at most `Q + 2` factors of period at most `periodBound l`
and at most `(Q + 3) (3 · escapeLengthBound l + 3)` other letters. -/
theorem exists_many_rayCandidates (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} {v : Fin k} (hv : M.Eligible W v) {l : ℕ}
        (hM : ¬ CoordinateCover C l M W v)
    (ts : List (List α)) (hts : ts.length ≤ k)
        (hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S)) :
    ∃ (n : ℕ) (cand : Fin n → RayCandidate M W ts v) (R : Finset (Fin n)),
      (∀ r, C.startWindow l ≤ (cand r).windowLength ∧ M.firstRejection W v ≤ (cand r).startCut ∧
        (cand r).endCut - (cand r).startCut ≤ C.periodBound l ∧ ∀ t ∈ ts,
            NoSuffixOccurrenceEndsBetween (W v) t (cand r).windowLength (cand r).startCut
                (cand r).endCut) ∧
      Set.InjOn (fun r => (cand r).ray.onset) R ∧
          (∀ r ∈ R, M.firstRejection W v < (cand r).ray.onset) ∧
      C.pieceCountBase - 1 ≤ R.card ∧
      ∀ r ∈
          R, PeriodicCover ((W v).take (cand r).startCut) (M.firstRejection W v)
              (C.pieceCountBase + 2) (C.periodBound l)
        ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3)) := by
  classical
  set J := M.firstRejection W v with hJ
  set T := C.escapeLengthBound l with hTl
  have hPT : C.periodBound l < T :=
    C.periodBound_lt_escapeLengthBound (Fintype.card_pos_iff.mpr ⟨M.dead⟩) l
  have hJw : J ≤ (W v).length := StructuralReader.firstRejection_le hv
  set n := ((W v).length - J) / T with hn_def
  have hn : (W v).length < J + n * T + T := by
    have := Nat.lt_div_mul_add (a := (W v).length - J) (show 0 < T by omega)
    rw [← hn_def] at this; omega
  have hnT : n * T ≤ (W v).length - J := Nat.div_mul_le_self _ _
  -- one candidate in each segment `[J + m T, J + m T + T)`, `m < n`
  have hseg : ∀ m : Fin n, ∃ x : RayCandidate M W ts v, J + m * T ≤ x.startCut ∧
      x.endCut ≤ J + m * T + T ∧ C.startWindow l ≤ x.windowLength ∧
      x.endCut - x.startCut ≤ C.periodBound l ∧
      ∀ t ∈ ts, NoSuffixOccurrenceEndsBetween (W v) t x.windowLength x.startCut x.endCut := by
    intro m
    have : m * T + T ≤ n * T := by rw [← add_one_mul]; exact Nat.mul_le_mul_right _ m.isLt
    obtain ⟨B, c, c', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      exists_closed_factor_replicate M.toTable (M.start v) (W v) ts hts hS (u := J + m * T)
        (bs := C.startWindow l) (by rw [← C.escapeLengthBound_eq]; omega)
    rw [← C.escapeLengthBound_eq] at h4
    rw [← C.comparisonWindow_eq] at h2
    exact ⟨⟨B, c, c', h5, h7⟩, h3, h4, h1,
      h8.trans ((factorLengthBound_mono _ _ h2).trans (C.factorLengthBound_le_periodBound l)), h6⟩
  choose cand hcand using hseg
  have hlt : ∀ m, (cand m).startCut < (cand m).endCut := fun m => (cand m).closed.1
  have hle : ∀ m, (cand m).endCut ≤ (W v).length := fun m => (cand m).closed.2.1
  have hper : ∀ m, (cand m).ray.period ≤ C.periodBound l := fun m =>
    (cand m).period_le.trans (hcand m).2.2.2.1
  -- the factors of the candidates of index `< m0` cover a position of each segment `m < r`
  -- below `cap`, so they leave at most `(|fs| + 1) · 2T` positions of `[J, cap)` uncovered
  have hcover : ∀ m0 r cap, r ≤ n → r ≤ m0 → cap ≤ (W v).length → cap ≤ J + r * T + T →
      (∀ m : Fin n, m.val < r → (cand m).startCut < cap) →
      ∃ fs : List PeriodicFactor,
        fs.length = ((Finset.univ.filter fun m : Fin n => m.val < m0).image
          fun m => (cand m).ray.onset).card ∧
        (∀ f ∈ fs, f.Valid (W v) (C.periodBound l) ∧ f.stop ≤ cap) ∧
        (uncoveredPositions fs J cap).card ≤ (fs.length + 1) * (2 * T) := by
    intro m0 r cap hrn hrm hcap hcapT hstart
    obtain ⟨fs, hlen, hval, hcov⟩ := exists_periodicFactors_of_rays _ (fun m => (cand m).ray)
      (fun m => (cand m).endCut) (fun m _ => (cand m).agrees) (fun m _ => hper m) hcap
    refine ⟨fs, hlen, hval, uncoveredPositions_card_le fs (by omega) hcapT fun m hm => ?_⟩
    have hmn : m < n := by omega
    have h1 : J + m * T ≤ (cand ⟨m, hmn⟩).startCut := (hcand ⟨m, hmn⟩).1
    have h2 : (cand ⟨m, hmn⟩).endCut ≤ J + m * T + T := (hcand ⟨m, hmn⟩).2.1
    refine ⟨_, h1, ?_, hstart _ hm, hcov _ ?_ _ ?_ (hlt _) (hstart _ hm)⟩
    · have := hlt ⟨m, hmn⟩; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · exact (cand _).onset_le
  -- with at most `Q + 1` distinct onsets the tail would have a periodic cover at level `l`
  have hmany : C.pieceCountBase + 2 ≤ (Finset.univ.image fun m => (cand m).ray.onset).card := by
    by_contra hfew
    obtain ⟨fs, hlen, hval, hunc⟩ := hcover n n (W v).length le_rfl le_rfl le_rfl hn.le
      fun m _ => (hlt m).trans_le (hle m)
    rw [Finset.filter_true_of_mem fun m _ => m.isLt] at hlen
    refine hM ⟨fs, by omega, fun f hf => (hval f hf).1, hunc.trans ?_⟩
    calc (fs.length + 1) * (2 * T) ≤ (C.pieceCountBase + 2) * (3 * T + 3) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ C.uncoveredBound l := C.uncoveredBound_ge_candidateBound l
  -- the first `Q + 2` distinct onsets
  obtain ⟨m0, R, hRm0, hinj, hRcard, hm0⟩ :=
    exists_initialSegment_transversal (fun m => (cand m).ray.onset) hmany
  -- at most three of them are at most `J`: those of index `0` and `1`, and one more, since two
  -- candidates of index at least `2` with onsets at most `J` are equal
  have hlow : (R.filter fun r => ¬ J < (cand r).ray.onset).card ≤ 3 := by
    have hsub : R.filter (fun r => ¬ J < (cand r).ray.onset) ⊆
        Finset.univ.filter (fun r : Fin n => r.val ≤ 1) ∪
          R.filter (fun r => 2 ≤ r.val ∧ (cand r).ray.onset ≤ J) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : r.val ≤ 1
      · exact Or.inl ⟨Finset.mem_univ _, h⟩
      · exact Or.inr ⟨hr.1, by omega, by omega⟩
    have h1 : (Finset.univ.filter fun r : Fin n => r.val ≤ 1).card ≤ 2 :=
      (Finset.card_le_card_of_injOn Fin.val (t := Finset.range 2)
        (fun r hr => by simp at hr ⊢; omega) Fin.val_injective.injOn).trans (by simp)
    have h2 : (R.filter fun r => 2 ≤ r.val ∧ (cand r).ray.onset ≤ J).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun r1 hr1 r2 hr2 => ?_
      rw [Finset.mem_filter] at hr1 hr2
      refine hinj hr1.1 hr2.1 (Ray.onset_eq_of_stream_eq
        ((cand r1).agrees.stream_eq_of_le (cand r2).agrees ?_))
      have : 2 * T ≤ r1.val * T := Nat.mul_le_mul_right _ hr1.2.1
      have : 2 * T ≤ r2.val * T := Nat.mul_le_mul_right _ hr2.2.1
      have := (hcand r1).1; have := (hcand r2).1; have := hlt r1; have := hlt r2
      have := hper r1; have := hper r2
      omega
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 3 := by omega
  refine ⟨n, cand, R.filter fun r => J < (cand r).ray.onset,
    fun r => ⟨(hcand r).2.2.1, by have := (hcand r).1; omega, (hcand r).2.2.2⟩,
    hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)),
    fun r hr => (Finset.mem_filter.mp hr).2, ?_, fun r hr => ?_⟩
  · have := Finset.card_filter_add_card_filter_not (s := R) (p := fun r => J < (cand r).ray.onset)
    omega
  -- the tail before the factor of `r` is covered by the factors of the first `Q + 2` onsets
  have hr := hRm0 r (Finset.mem_filter.mp hr).1
  have hrw : (cand r).startCut ≤ (W v).length := (hlt r).le.trans (hle r)
  obtain ⟨fs, hlen, hval, hunc⟩ := hcover m0 r.val (cand r).startCut r.isLt.le hr.le hrw
    (by have := (hcand r).2.1; have := hlt r; omega) fun m hm => by
      have : m.val * T + T ≤ r.val * T := by
        rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hm
      have := (hcand m).2.1; have := (hcand r).1; have := hlt m
      omega
  refine ⟨fs, by omega, fun f hf => ?_, ?_⟩
  · obtain ⟨⟨h1, h2, -, h4⟩, h5⟩ := hval f hf
    exact ⟨h1, h2, by rw [List.length_take]; omega, periodicOn_take h4 h5⟩
  · rw [List.length_take, min_eq_left hrw]
    exact hunc.trans (Nat.mul_le_mul (by omega) (by omega))

/-- Given the rays `U` chosen before the word `v`, each agreeing with its original word and with
a bounded period if it is periodic at its first rejected cut, some candidate of `v` with onset
after the first rejected cut has no forbidden overlap with any of them: each earlier ray
excludes at most `2 (N - 1)` candidates, and there are at least `Q - 1 > 2 (k - 1) (N - 1)`
candidates, where `Q = pieceCountBase`. -/
theorem exists_compatible_rayCandidate (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} (hW : M.IsHole W) {v : Fin k} {l : ℕ} (hl : 1 ≤ l)
    (hM : ¬ CoordinateCover C l M W v) (ts : List (List α)) (hts : ts.length ≤ k)
    (hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S))
    (U : Finset (Fin k)) (hvU : v ∉ U)
    (Ωu : Fin k → Ray α) (Eu : Fin k → ℕ)
    (hU : ∀ u ∈ U, RayAgrees (Ωu u) (W u) (Eu u) ∧ (Ωu u).onset ≤ Eu u ∧
      M.firstRejection W u ≤ Eu u ∧ ((Ωu u).onset ≤ M.firstRejection W u →
          (Ωu u).period ≤ C.periodBound (l - 1))) :
    ∃ x : RayCandidate M W ts v, C.startWindow l ≤ x.windowLength ∧
        M.firstRejection W v ≤ x.startCut ∧
        x.endCut - x.startCut ≤ C.periodBound l ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween (W v) t x.windowLength x.startCut x.endCut) ∧
          M.firstRejection W v <
          x.ray.onset ∧
      PeriodicCover ((W v).take x.startCut) (M.firstRejection W v) (C.pieceCountBase + 2)
          (C.periodBound l)
        ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3)) ∧
      ∀ u ∈
          U, NoForbiddenRayOverlap x.ray (Ωu u) (M.firstRejection W v) (M.firstRejection W u) := by
  classical
  obtain ⟨n, cand, R, hc, hinj, hJc, hR, hcov⟩ := exists_many_rayCandidates C (hW.1 v) hM ts hts hS
  have hagc : ∀ r ∈ R, RayAgrees (cand r).ray (W v) (cand r).endCut := fun r _ => (cand r).agrees
  have hAc : ∀ r ∈ R, (cand r).ray.onset ≤ (cand r).endCut := fun r _ => by
    have := (cand r).onset_le; have := (cand r).closed.1; omega
  have hbad : ∀ u ∈
      U, (R.filter (fun r => ¬ NoForbiddenRayOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
      (M.firstRejection W u))).card ≤ 2 * (Fintype.card S - 1) := by
    intro u hu
    obtain ⟨hag, hAu, hJu, hpu⟩ := hU u hu
    have hsub : R.filter
        (fun r => ¬ NoForbiddenRayOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
            (M.firstRejection W u)) ⊆
        R.filter
            (fun r => PrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
                (M.firstRejection W u)) ∪
        R.filter
            (fun r => PeriodicTailOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
                (M.firstRejection W u)) ∪
        R.filter
            (fun r => ReversePrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
                (M.firstRejection W u)) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      simp only [Finset.mem_union, Finset.mem_filter]
      unfold NoForbiddenRayOverlap at hr
      by_cases h1 : PrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v) (M.firstRejection W u)
      · exact Or.inl (Or.inl ⟨hr.1, h1⟩)
      by_cases h2 : PeriodicTailOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
          (M.firstRejection W u)
      · exact Or.inl (Or.inr ⟨hr.1, h2⟩)
      by_cases h3 : ReversePrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
          (M.firstRejection W u)
      · exact Or.inr ⟨hr.1, h3⟩
      exact absurd ⟨h1, h2, h3⟩ hr.2
    have h1 :=
        card_prefixOverlap_le R (fun r => (cand r).ray) (fun r => (cand r).endCut) (hW.1 u) hag hAu
      hagc hAc hinj
    have h2 := card_reversePrefixOverlap_le (u := u) (Ωu := Ωu u) R (fun r => (cand r).ray)
      (fun r => (cand r).endCut) (hW.1 v) hagc hAc hJc hinj
    have hcu := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    by_cases hAJ : (Ωu u).onset ≤ M.firstRejection W u
    · have hrun : ∀ r ∈ R, (cand r).ray.onset + (Fintype.card S + 1) * (Ωu u).period ≤
          (cand r).endCut := by
        intro r hr
        have h1 := (cand r).onset_le
        have h2 := (hc r).1
        have h3 := C.startWindow_gt (l - 1)
        rw [show l - 1 + 1 = l by omega] at h3
        have h4 : (Fintype.card S + 1) * (Ωu u).period ≤ (Fintype.card S + 1) *
            C.periodBound (l - 1) :=
          Nat.mul_le_mul_left _ (hpu hAJ)
        have h5 := (cand r).windowLength_lt
        have h6 := (cand r).closed.1
        omega
      have h3 :=
          card_periodicTailOverlap_le R (fun r => (cand r).ray) (fun r => (cand r).endCut)
              (hW.1 u) hag hJu
        hagc hrun hJc hinj
      have h0 : R.filter
          (fun r => PrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
              (M.firstRejection W u)) = ∅ :=
        Finset.filter_false_of_mem (fun r _ h => by have := h.1; omega)
      rw [h0, Finset.card_empty] at hcu
      omega
    · have h0 : R.filter
        (fun r => PeriodicTailOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
            (M.firstRejection W u)) = ∅ :=
        Finset.filter_false_of_mem (fun r _ h => hAJ h.1)
      rw [h0, Finset.card_empty] at hcu
      omega
  have hU1 : U.card ≤ k - 1 := by
    have hsub : U ⊆ Finset.univ.erase v :=
      fun u hu => Finset.mem_erase.mpr ⟨fun h => hvU (h ▸ hu), Finset.mem_univ _⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  -- `|U| · 2 (N - 1) ≤ 2 (k - 1) (N - 1) < Q - 1 ≤ |R|`
  obtain ⟨r, hr, hrc⟩ := exists_forall_of_card_filter_not_le _ hbad (by
    have hQ := C.pieceCountBase_eq
    have e1 : U.card * (2 * (Fintype.card S - 1)) ≤ (k - 1) * (2 * (Fintype.card S - 1)) :=
      Nat.mul_le_mul_right _ hU1
    have e2 : (k - 1) * (2 * (Fintype.card S - 1)) = 2 * (k - 1) * (Fintype.card S - 1) := by ring
    omega)
  exact ⟨cand r, (hc r).1, (hc r).2.1, (hc r).2.2.1, (hc r).2.2.2, hJc r hr, hcov r hr, hrc⟩

end Selection

/-! ## Comparisons of a ray with itself and positive cycles -/

/-- The ray of a candidate has no admitted comparison with itself beyond those of the original
word: a comparison with `a ≤ b ≤ J` and equal infinite suffixes forces `a = b`, and the pair at
equal cuts is a pair of the original hole. -/
theorem rayCandidate_no_selfAdmission [DecidableEq α] [DecidableEq S] {M : StructuralReader α S k}
    {W : Fin k → List α}
    (hW : M.IsHole W) {i : Fin k} {Ω : Ray α} {E : ℕ} (hag : RayAgrees Ω (W i) E)
    (hJE : M.firstRejection W i ≤ E) (hJA : M.firstRejection W i < Ω.onset) :
    ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
      M.admitted (rayState M (M.start i) Ω a) (rayState M (M.start i) Ω b) = true →
      ¬ ∀ t, Ω.stream (a + t) = Ω.stream (b + t) := by
  intro a b hb hab hadm heq
  rcases Ray.suffix_eq_cases heq with ⟨_, h2⟩ | ⟨h1, h2⟩
  · omega
  · have hab' : a = b := by omega
    subst hab'
    have hJl := StructuralReader.firstRejection_le (hW.1 i)
    rw [rayState_eq_runPrefix M hag (by omega)] at hadm
    have h := hW.2 i i _ (pair_mem_channel (W := W) (a := a) (b := a) (by omega) (by omega)
      (List.prefix_refl _))
    rw [h] at hadm
    exact absurd hadm (by decide)

/-- If every ray that is not periodic at its first rejected cut has no forbidden overlap with
any other ray, closed walks of the ray system avoid these rays; if moreover a potential `L`
satisfies every constraint between two of the other rays, the ray system has no positive
cycle. -/
theorem rays_no_positiveCycle [DecidableEq α] [Fintype S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) (L : ι → ℤ)
        (isM : ι → Prop)
    (hM : ∀ v, isM v → J v < (Ω v).onset ∧ ∀ u,
        u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u))
    (hT : ∀ i j, ¬ isM i → ¬ isM j → i ≠ j → ∀ a b, b ≤ J j →
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st j) (Ω j) b) = true →
      (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → L i + ((b : ℤ) - a + 1) ≤ L j) :
    ¬ (raySystem M st Ω J).HasPositiveCycle := by
  classical
  rintro ⟨i, p, hw, hpos⟩
  by_cases hex : ∃ v ∈ i :: p, isM v
  · obtain ⟨v, hv, hMv⟩ := hex
    exact not_mem_closed_walk_of_noForbiddenRayOverlap (M := M) (st := st) (Ω := Ω) (J := J)
        (hM v hMv).1 (hM v hMv).2 hw hv
  push Not at hex
  have hP : ∀ u v c, ¬ isM u → ¬ isM v → (raySystem M st Ω J).edgeWeight u v = some c → L u + c ≤
      L v := by
    intro u v c hu hv hc
    have hmem := Finset.mem_of_max hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_filter] at he
    obtain ⟨he, hi, hj⟩ := he
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    obtain ⟨i', j', he⟩ := he
    split_ifs at he with hij
    · simp at he
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hab, hadm, heq⟩ := Finset.mem_filter.mp hab
      obtain ⟨-, hb⟩ := Finset.mem_product.mp hab
      simp only at hi hj ⊢
      subst hi hj
      exact hT i' j' hu hv hij a b (by have := Finset.mem_range.mp hb; omega) hadm heq
  have hw' : (raySystem M st Ω J).IsWalk (i :: (p ++ [i])) := by simpa using hw
  have h1 :=
      DifferenceSystem.weight_le_local (D := raySystem M st Ω J) (x := L) (fun z => ¬ isM z) hP i
    (p ++ [i]) hw' (by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hex z List.mem_cons_self
      · rcases List.mem_append.mp hz with hz | hz
        · exact hex z (List.mem_cons_of_mem _ hz)
        · rw [List.mem_singleton] at hz; subst hz; exact hex z List.mem_cons_self)
  have h2 : (i :: (p ++ [i])).getLast (List.cons_ne_nil _ _) = i := by simp
  rw [h2] at h1
  have : (raySystem M st Ω J).weight (i :: p ++ [i]) =
      (raySystem M st Ω J).weight (i :: (p ++ [i])) :=
      rfl
  linarith

end DeciSigma1.Holes.Tail

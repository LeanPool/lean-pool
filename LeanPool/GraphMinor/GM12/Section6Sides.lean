/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section6Order
public import LeanPool.GraphMinor.GM12.Section2ArcComponents
import LeanPool.GraphMinor.GM12.Section2DiscChordSplit
public import LeanPool.GraphMinor.GM11.RadialBasics
public import LeanPool.GraphMinor.GM11.RadialChord
public import LeanPool.GraphMinor.GM14.DiscSlope
public import LeanPool.GraphMinor.Surface.ArcInPath
public import LeanPool.GraphMinor.Surface.TriPath
public import LeanPool.GraphMinor.Surface.DiscArcs
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Isometry
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.Fan

/-!
# Graph Minors XII, Section 6: the discs `D_0, …, D_k`

The proof of (6.1) starts: "The lines $U(P_1), \dots, U(P_{\theta/2})$ divide $\Delta - F$ into
$\theta/2 + 1$ open discs".
Each chord cuts `Δ` into two closed discs (`exists_side`), with the earlier chords on one side and
the
later chords on the other. Cutting the far side of one chord by the next chord gives the open disc
between them (`exists_pieces`).

The paper then says that the regions `r_i ⊇ D_i` are distinct "since `Γ₁` is 2-cell". This is
`no_bypass`. A path from one side of a chord to the other that misses the chord must leave `Δ`.
Closing
it up through `Δ` gives an `O`-arc inside a region of `Γ₁`, so it bounds a closed disc in this
region.
Then one end of the chord lies in that disc, and it cannot, as it is a vertex of `Γ₁`.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Two points of the boundary of a closed disc are joined by a line through the interior. -/
theorem chord_in_disc {Δ : Set S} (hΔ : IsClosedDisc Δ) {a b : S} (ha : a ∈ discBd Δ)
    (hb : b ∈ discBd Δ) (hab : a ≠ b) :
    ∃ L, IsLineWithEnds L a b ∧ L ⊆ Δ ∧ L ∩ discBd Δ = {a, b} :=
  Surface.exists_chord hΔ ha hb hab

omit [T2Space S] in
/-- A preconnected set in the union of two closed sets that misses their meet lies in one of them.
-/
theorem subset_side {X Y Z : Set S} (hX : IsClosed X) (hY : IsClosed Y) (hZ : IsPreconnected Z)
    (hsub : Z ⊆ X ∪ Y) (hd : Disjoint Z (X ∩ Y)) : Z ⊆ X ∨ Z ⊆ Y := by
  by_contra hc
  rw [not_or, Set.not_subset, Set.not_subset] at hc
  obtain ⟨⟨x, hx, hxX⟩, ⟨y, hy, hyY⟩⟩ := hc
  have hxY : x ∈ Y := (hsub hx).resolve_left hxX
  have hyX : y ∈ X := (hsub hy).resolve_right hyY
  obtain ⟨w, hw, hw'⟩ := isPreconnected_closed_iff.mp hZ X Y hX hY hsub ⟨y, hy, hyX⟩ ⟨x, hx, hxY⟩
  exact Set.disjoint_left.mp hd hw hw'

omit [T2Space S] in
/-- A line is connected. -/
theorem line_conn {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected h

omit [T2Space S] in
/-- A line with ends `a, b` has a point other than its ends. -/
theorem line_mid {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : (L \ {a, b}).Nonempty :=
  Surface.IsLineWithEnds.nonempty_sdiff h

/-- A line through a closed disc, meeting the boundary in its two ends, cuts the disc in two. -/
theorem split_with_arcs {D L A B : Set S} {a b : S} (hD : IsClosedDisc D)
    (hL : IsLineWithEnds L a b) (hA : IsLineWithEnds A a b) (hB : IsLineWithEnds B a b)
    (hAB : A ∩ B = {a, b}) (hLA : L ∩ A = {a, b}) (hLB : L ∩ B = {a, b})
    (hbd : discBd D = A ∪ B) (hLD : L ⊆ D) (hab : a ≠ b) :
    ∃ E₁ E₂ : Set S, IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧ E₁ ∪ E₂ = D ∧ E₁ ∩ E₂ = L ∧
      discBd E₁ = A ∪ L ∧ discBd E₂ = B ∪ L :=
  GM12.disc_split_with_boundary_arcs_inter hD hL hA hB hAB hLA hLB hbd hLD hab

/-- A line through a closed disc, meeting the boundary in its two ends, cuts the disc in two, and
the boundary into two lines. -/
theorem split_disc {D L : Set S} {a b : S} (hD : IsClosedDisc D) (hLD : L ⊆ D) (hab : a ≠ b)
    (hL : IsLineWithEnds L a b) (hc : L ∩ discBd D = {a, b}) :
    ∃ E₁ E₂ A B, IsLineWithEnds A a b ∧ IsLineWithEnds B a b ∧ A ∪ B = discBd D ∧ A ∩ B = {a, b} ∧
      IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧ E₁ ∪ E₂ = D ∧ E₁ ∩ E₂ = L ∧ discBd E₁ = A ∪ L ∧
      discBd E₂ = B ∪ L := by
  have hs : a ∈ discBd D := (hc ▸ (mem_insert a {b}) : a ∈ L ∩ discBd D).2
  have ht : b ∈ discBd D := (hc ▸ (Or.inr rfl : b ∈ ({a, b} : Set S)) : b ∈ L ∩ discBd D).2
  obtain ⟨x, y, hxy, hx0, hx1, hr⟩ := hD.isOArc_discBd.exists_arcs hs ht hab
  have la : IsLineWithEnds (range x) a b := hx0 ▸ hx1 ▸ hxy.arc_left.isLineWithEnds
  have lb : IsLineWithEnds (range y) a b := by
    have := hxy.arc_right.isLineWithEnds
    rwa [hxy.zero, hxy.one, hx0, hx1] at this
  have hmeet : range x ∩ range y = {a, b} := by
    ext z
    constructor
    · rintro ⟨⟨r, rfl⟩, ⟨r', e⟩⟩
      rcases hxy.meet r r' e.symm with ⟨h0, -⟩ | ⟨h1, -⟩
      · exact .inl (by rw [h0, hx0])
      · exact .inr (by rw [h1, hx1]; rfl)
    · rintro (rfl | rfl)
      · exact ⟨la.left_mem, lb.left_mem⟩
      · exact ⟨la.right_mem, lb.right_mem⟩
  have hcA : ∀ {G : Set S}, G ⊆ discBd D → a ∈ G → b ∈ G → L ∩ G = {a, b} := fun {G} hG ha hb => by
    refine subset_antisymm (fun z hz => hc ▸ ⟨hz.1, hG hz.2⟩) ?_
    rintro _ (rfl | rfl)
    · exact ⟨hL.left_mem, ha⟩
    · exact ⟨hL.right_mem, hb⟩
  obtain ⟨E₁, E₂, h1, h2, h3, h4, h5, h6⟩ := split_with_arcs hD hL la lb hmeet
    (hcA (hr ▸ subset_union_left) la.left_mem la.right_mem)
    (hcA (hr ▸ subset_union_right) lb.left_mem lb.right_mem) hr.symm hLD hab
  exact ⟨E₁, E₂, _, _, la, lb, hr, hmeet, h1, h2, h3, h4, h5, h6⟩

/-- The hypotheses on the chords of `Δ` in (6.1). -/
structure Chords (F Δ : Set S) (k : ℕ) (a b : Fin k → S) (R : Fin k → Set S) : Prop where
  /-- `Δ` is a closed disc. -/
  disc : IsClosedDisc Δ
  /-- `Δ` is bounded by `F`. -/
  bd : discBd Δ = F
  /-- Each `R i` is a line from `a i` to `b i`. -/
  line : ∀ i, IsLineWithEnds (R i) (a i) (b i)
  /-- Each `R i` lies in `Δ`. -/
  sub : ∀ i, R i ⊆ Δ
  /-- Each `R i` meets `F` only in its ends. -/
  meet : ∀ i, R i ∩ F = {a i, b i}
  /-- The lines are disjoint. -/
  disj : ∀ i j, i ≠ j → Disjoint (R i) (R j)
  /-- The ends of `R i` differ. -/
  ne : ∀ i, a i ≠ b i
  /-- The two arcs of `F` at `R i`. -/
  arcs : ∀ i, ∃ M N : Set S, IsLineWithEnds M (a i) (b i) ∧ IsLineWithEnds N (a i) (b i) ∧
    M ∪ N = F ∧ M ∩ N = {a i, b i} ∧ (∀ j, i < j → a j ∈ M ∧ b j ∈ M) ∧
    (∀ j, j < i → a j ∈ N ∧ b j ∈ N)

/-- The two closed discs on the two sides of the chord `R i`. -/
structure IsSide (F Δ R : Set S) {k : ℕ} (a b : Fin k → S) (i : Fin k)
  (X Y A B : Set S) : Prop where
  discX : IsClosedDisc X
  discY : IsClosedDisc Y
  union : X ∪ Y = Δ
  inter : X ∩ Y = R
  lineA : IsLineWithEnds A (a i) (b i)
  lineB : IsLineWithEnds B (a i) (b i)
  bdX : discBd X = A ∪ R
  bdY : discBd Y = B ∪ R
  arcs : A ∪ B = F
  arcs_inter : A ∩ B = {a i, b i}
  before : ∀ j, j < i → a j ∈ A ∧ b j ∈ A
  after : ∀ j, i < j → a j ∈ B ∧ b j ∈ B

variable {F Δ : Set S} {k : ℕ} {a b : Fin k → S} {R : Fin k → Set S}

/-- Each chord cuts `Δ` into two closed discs, with the earlier chords on the first side. -/
theorem Chords.exists_side (h : Chords F Δ k a b R) (i : Fin k) :
    ∃ X Y A B, IsSide F Δ (R i) a b i X Y A B := by
  obtain ⟨M, N, hM, hN, hu, hc, hb, ha⟩ := h.arcs i
  have hcA : ∀ {G : Set S}, G ⊆ F → a i ∈ G → b i ∈ G → R i ∩ G = {a i, b i} := fun {G} hG h1 h2
    => by
    refine subset_antisymm (fun z hz => h.meet i ▸ ⟨hz.1, hG hz.2⟩) ?_
    rintro _ (rfl | rfl)
    · exact ⟨(h.line i).left_mem, h1⟩
    · exact ⟨(h.line i).right_mem, h2⟩
  obtain ⟨X, Y, hX, hY, hun, hin, hbX, hbY⟩ := split_with_arcs h.disc (h.line i) hN hM
    (by rw [inter_comm]; exact hc)
    (hcA (hu ▸ subset_union_right) hN.left_mem hN.right_mem)
    (hcA (hu ▸ subset_union_left) hM.left_mem hM.right_mem)
    (by rw [h.bd, union_comm, hu]) (h.sub i) (h.ne i)
  exact ⟨X, Y, N, M, ⟨hX, hY, hun, hin, hN, hM, hbX, hbY, by rw [union_comm]; exact hu,
    by rw [inter_comm]; exact hc, ha, hb⟩⟩

section Sides

variable {X Y A B : Fin k → Set S} (h : Chords F Δ k a b R)
  (hs : ∀ i, IsSide F Δ (R i) a b i (X i) (Y i) (A i) (B i))

include hs

omit [T2Space S] in
theorem IsSide.R_sub_X (i : Fin k) : R i ⊆ X i := by
  rw [← (hs i).inter]
  exact inter_subset_left

omit [T2Space S] in
theorem IsSide.R_sub_Y (i : Fin k) : R i ⊆ Y i := by
  rw [← (hs i).inter]
  exact inter_subset_right

include h

/-- An earlier chord lies on the first side of a later one. -/
theorem R_before {i j : Fin k} (hj : j < i) : R j ⊆ X i := by
  have hij : j ≠ i := hj.ne
  have hd : Disjoint (R j) (X i ∩ Y i) := by
    rw [(hs i).inter]
    exact h.disj j i hij
  rcases subset_side (hs i).discX.isClosed (hs i).discY.isClosed
    (line_conn (h.line j)) (by rw [(hs i).union]; exact h.sub j) hd with h1 | h1
  · exact h1
  · have hA : a j ∈ X i := by
      have : a j ∈ discBd (X i) := by
        rw [(hs i).bdX]
        exact .inl ((hs i).before j hj).1
      exact GraphMinor.Surface.discBd_subset _ this
    exact (Set.disjoint_left.mp hd (h.line j).left_mem ⟨hA, h1 (h.line j).left_mem⟩).elim

/-- A later chord lies on the second side of an earlier one. -/
theorem R_after {i j : Fin k} (hj : i < j) : R j ⊆ Y i := by
  have hij : j ≠ i := hj.ne'
  have hd : Disjoint (R j) (X i ∩ Y i) := by
    rw [(hs i).inter]
    exact h.disj j i hij
  rcases subset_side (hs i).discX.isClosed (hs i).discY.isClosed
    (line_conn (h.line j)) (by rw [(hs i).union]; exact h.sub j) hd with h1 | h1
  · have hA : a j ∈ Y i := by
      have : a j ∈ discBd (Y i) := by
        rw [(hs i).bdY]
        exact .inl ((hs i).after j hj).1
      exact GraphMinor.Surface.discBd_subset _ this
    exact (Set.disjoint_left.mp hd (h.line j).left_mem ⟨h1 (h.line j).left_mem, hA⟩).elim
  · exact h1

/-- The piece of `Y p` next to `R p`, cut off by the next chord `R q`. -/
theorem mid_piece {p q : Fin k} (hpq : p < q) {E E' A₁ A₂ : Set S} (hE : IsClosedDisc E)
    (hu : E ∪ E' = Y p) (hi : E ∩ E' = R q) (hbE : discBd E = A₁ ∪ R q)
    (hbE' : discBd E' = A₂ ∪ R q) (hA : A₁ ∪ A₂ = discBd (Y p)) (hRp : R p ⊆ E) :
    R q ⊆ closure (discInt E) ∧ Disjoint (discInt E) (R q) ∧ R p ⊆ closure (discInt E) ∧
      Disjoint (discInt E) (R p) ∧ discInt E ⊆ Y p ∧ discInt E ⊆ X q := by
  have hsubE : discInt E ⊆ E := sdiff_subset
  have hcl := hE.subset_closure_discInt
  have hYΔ : Y p ⊆ Δ := by
    rw [← (hs p).union]
    exact subset_union_right
  have hRq : R q ⊆ discBd E := by rw [hbE]; exact subset_union_right
  have hRE : R q ⊆ E := hRq.trans (GraphMinor.Surface.discBd_subset E)
  have hEY : E ⊆ Y p := by rw [← hu]; exact subset_union_left
  have hd : Disjoint (discInt E) (R q) := disjoint_sdiff_left.mono_right hRq
  have hdp : Disjoint (discInt E) (R p) := by
    refine disjoint_sdiff_left.mono_right fun x hx => ?_
    have hxb : x ∈ discBd (Y p) := by
      rw [(hs p).bdY]
      exact .inr hx
    rw [← hA] at hxb
    rcases hxb with h1 | h2
    · rw [hbE]
      exact .inl h1
    · have hxE' : x ∈ E' := GraphMinor.Surface.discBd_subset E' (by rw [hbE']; exact .inl h2)
      have : x ∈ R q := hi ▸ ⟨hRp hx, hxE'⟩
      exact (Set.disjoint_left.mp (h.disj p q hpq.ne) hx this).elim
  refine ⟨hRE.trans hcl, hd, hRp.trans hcl, hdp, hsubE.trans hEY, ?_⟩
  have hdq : Disjoint (discInt E) (X q ∩ Y q) := by rw [(hs q).inter]; exact hd
  rcases subset_side (hs q).discX.isClosed (hs q).discY.isClosed hE.isPreconnected_discInt
    (by rw [(hs q).union]; exact hsubE.trans (hEY.trans hYΔ)) hdq with h1 | h1
  · exact h1
  · exfalso
    have hcY : closure (discInt E) ⊆ Y q := closure_minimal h1 (hs q).discY.isClosed
    have hx := (h.line p).left_mem
    have h2 : a p ∈ X q ∩ Y q := ⟨R_before h hs hpq hx, hcY (hRp.trans hcl hx)⟩
    rw [(hs q).inter] at h2
    exact Set.disjoint_left.mp (h.disj p q hpq.ne) hx h2

/-- The piece of `Δ` number `m`. It is `D_m` of the paper, with the numbering from `0`. -/
theorem exists_chord_piece (m : ℕ) (hm : m ≤ k) (hk : 0 < k) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ Δ ∧
      (∀ i : Fin k, i.1 = m → R i ⊆ discBd E ∧ discInt E ⊆ X i) ∧
      (∀ i : Fin k, i.1 + 1 = m → R i ⊆ discBd E ∧ discInt E ⊆ Y i) := by
  by_cases h0 : m = 0
  · subst h0
    let i₀ : Fin k := ⟨0, hk⟩
    have hsub : discInt (X i₀) ⊆ X i₀ := sdiff_subset
    have hXΔ : X i₀ ⊆ Δ := by rw [← (hs i₀).union]; exact subset_union_left
    have hRb : R i₀ ⊆ discBd (X i₀) := by rw [(hs i₀).bdX]; exact subset_union_right
    refine ⟨X i₀, (hs i₀).discX, hXΔ, ?_, fun i hi => by omega⟩
    intro i hi
    have hii : i = i₀ := Fin.ext hi
    rw [hii]
    exact ⟨hRb, hsub⟩
  by_cases hk' : m = k
  · subst hk'
    let i₀ : Fin m := ⟨m - 1, by omega⟩
    have hsub : discInt (Y i₀) ⊆ Y i₀ := sdiff_subset
    have hYΔ : Y i₀ ⊆ Δ := by rw [← (hs i₀).union]; exact subset_union_right
    have hRb : R i₀ ⊆ discBd (Y i₀) := by rw [(hs i₀).bdY]; exact subset_union_right
    refine ⟨Y i₀, (hs i₀).discY, hYΔ, fun i hi => by have := i.2; omega, ?_⟩
    intro i hi
    have hii : i = i₀ := Fin.ext (by simp only [i₀]; omega)
    rw [hii]
    exact ⟨hRb, hsub⟩
  let p : Fin k := ⟨m - 1, by omega⟩
  let q : Fin k := ⟨m, by omega⟩
  have hpq : p < q := by
    change m - 1 < m
    omega
  have hRq : R q ⊆ Y p := R_after h hs hpq
  have hmeet : R q ∩ discBd (Y p) = {a q, b q} := by
    rw [(hs p).bdY]
    ext x
    constructor
    · rintro ⟨hx, h1 | h1⟩
      · have : x ∈ R q ∩ F := ⟨hx, (hs p).arcs ▸ Or.inr h1⟩
        rwa [h.meet q] at this
      · exact (Set.disjoint_left.mp (h.disj q p hpq.ne') hx h1).elim
    · rintro (rfl | rfl)
      · exact ⟨(h.line q).left_mem, .inl ((hs p).after q hpq).1⟩
      · exact ⟨(h.line q).right_mem, .inl ((hs p).after q hpq).2⟩
  obtain ⟨E₁, E₂, A₁, A₂, -, -, hAu, -, hE₁, hE₂, hun, hin, hb₁, hb₂⟩ :=
    split_disc (hs p).discY hRq (h.ne q) (h.line q) hmeet
  have hdp : Disjoint (R p) (E₁ ∩ E₂) := by rw [hin]; exact h.disj p q hpq.ne
  have hRpY : R p ⊆ E₁ ∪ E₂ := by rw [hun]; exact IsSide.R_sub_Y hs p
  have build : ∀ {E E' A₁ A₂ : Set S}, IsClosedDisc E → IsClosedDisc E' → E ∪ E' = Y p →
      E ∩ E' = R q → discBd E = A₁ ∪ R q → discBd E' = A₂ ∪ R q → A₁ ∪ A₂ = discBd (Y p) → R p ⊆ E →
      ∃ E : Set S, IsClosedDisc E ∧ E ⊆ Δ ∧
      (∀ i : Fin k, i.1 = m → R i ⊆ discBd E ∧ discInt E ⊆ X i) ∧
      (∀ i : Fin k, i.1 + 1 = m → R i ⊆ discBd E ∧ discInt E ⊆ Y i) := by
    intro E E' A₁ A₂ hE hE' hu hi hbE hbE' hA hRp
    obtain ⟨-, -, -, h4, h5, h6⟩ := mid_piece h hs hpq hE hu hi hbE hbE' hA hRp
    have hYΔ : Y p ⊆ Δ := by rw [← (hs p).union]; exact subset_union_right
    have hEY : E ⊆ Y p := by rw [← hu]; exact subset_union_left
    refine ⟨E, hE, hEY.trans hYΔ, ?_, ?_⟩
    · intro i hi
      have hii : i = q := Fin.ext hi
      rw [hii]
      exact ⟨by rw [hbE]; exact subset_union_right, h6⟩
    · intro i hi
      have hii : i = p := Fin.ext (by simp only [p]; omega)
      rw [hii]
      refine ⟨fun x hx => ?_, h5⟩
      by_contra hn
      exact Set.disjoint_left.mp h4 ⟨hRp hx, hn⟩ hx
  rcases subset_side hE₁.isClosed hE₂.isClosed (line_conn (h.line p)) hRpY hdp with h1 | h1
  · exact build hE₁ hE₂ hun hin hb₁ hb₂ hAu h1
  · exact build hE₂ hE₁ (by rw [union_comm]; exact hun) (by rw [inter_comm]; exact hin) hb₂ hb₁
      (by rw [union_comm]; exact hAu) h1

/-- The pieces of `Δ`: `W m` lies before the chords from `m` on, after the chords before `m`, it
misses all chords, and the two chords next to it are in its closure. -/
theorem exists_pieces (hk : 0 < k) :
    ∃ E W : Fin (k + 1) → Set S, (∀ m, IsClosedDisc (E m) ∧ E m ⊆ Δ ∧ W m = discInt (E m)) ∧
      (∀ i : Fin k, R i ⊆ discBd (E i.castSucc) ∧ R i ⊆ discBd (E i.succ)) ∧
      (∀ m, IsPreconnected (W m) ∧ (W m).Nonempty ∧ W m ⊆ Δ) ∧
      (∀ m i, Disjoint (W m) (R i)) ∧
      (∀ m i, m.1 ≤ i.1 → W m ⊆ X i) ∧ (∀ m i, i.1 < m.1 → W m ⊆ Y i) ∧
      (∀ i : Fin k, R i ⊆ closure (W i.castSucc) ∧ R i ⊆ closure (W i.succ)) := by
  have hc' := fun m : Fin (k + 1) => exists_chord_piece h hs m.1 (by have := m.2; omega) hk
  choose E hE hEΔ hEX hEY using hc'
  let W : Fin (k + 1) → Set S := fun m => discInt (E m)
  have h1 : ∀ m, IsPreconnected (W m) := fun m => (hE m).isPreconnected_discInt
  have h2 : ∀ m, (W m).Nonempty := fun m => (hE m).nonempty_discInt
  have h3 : ∀ m, W m ⊆ Δ := fun m => sdiff_subset.trans (hEΔ m)
  have hpiece : ∀ m (i : Fin k), R i ⊆ discBd (E m) → R i ⊆ closure (W m) ∧ Disjoint (W m) (R i) :=
    fun m i hR => ⟨(hR.trans (GraphMinor.Surface.discBd_subset _)).trans
      (hE m).subset_closure_discInt, disjoint_sdiff_left.mono_right hR⟩
  have h4 : ∀ m (i : Fin k), i.1 = m.1 → R i ⊆ closure (W m) ∧ Disjoint (W m) (R i) ∧ W m ⊆ X i :=
    fun m i he => ⟨(hpiece m i (hEX m i he).1).1, (hpiece m i (hEX m i he).1).2, (hEX m i he).2⟩
  have h5 : ∀ m (i : Fin k), i.1 + 1 = m.1 →
      R i ⊆ closure (W m) ∧ Disjoint (W m) (R i) ∧ W m ⊆ Y i :=
    fun m i he => ⟨(hpiece m i (hEY m i he).1).1, (hpiece m i (hEY m i he).1).2, (hEY m i he).2⟩
  have hle : ∀ m i, m.1 ≤ i.1 → W m ⊆ X i ∧ Disjoint (W m) (R i) := by
    intro m i hmi
    by_cases he : i.1 = m.1
    · exact ⟨(h4 m i he).2.2, (h4 m i he).2.1⟩
    let q : Fin k := ⟨m.1, by have := i.2; omega⟩
    have hqi : q < i := by
      change m.1 < i.1
      omega
    obtain ⟨h6, h7, h8⟩ := h4 m q rfl
    have hd : Disjoint (W m) (R i) := by
      refine Set.disjoint_left.mpr fun x hx hxi => ?_
      have : x ∈ R q := (hs q).inter ▸ ⟨h8 hx, R_after h hs hqi hxi⟩
      exact Set.disjoint_left.mp h7 hx this
    refine ⟨?_, hd⟩
    have hdc : Disjoint (W m) (X i ∩ Y i) := by rw [(hs i).inter]; exact hd
    rcases subset_side (hs i).discX.isClosed (hs i).discY.isClosed (h1 m)
      (by rw [(hs i).union]; exact h3 m) hdc with h9 | h9
    · exact h9
    · exfalso
      have hcY : closure (W m) ⊆ Y i := closure_minimal h9 (hs i).discY.isClosed
      have hx := (h.line q).left_mem
      have : a q ∈ X i ∩ Y i := ⟨R_before h hs hqi hx, hcY (h6 hx)⟩
      rw [(hs i).inter] at this
      exact Set.disjoint_left.mp (h.disj q i hqi.ne) hx this
  have hlt : ∀ m i, i.1 < m.1 → W m ⊆ Y i ∧ Disjoint (W m) (R i) := by
    intro m i hmi
    by_cases he : i.1 + 1 = m.1
    · exact ⟨(h5 m i he).2.2, (h5 m i he).2.1⟩
    have hm0 := m.2
    let p : Fin k := ⟨m.1 - 1, by omega⟩
    have hip : i < p := by
      change i.1 < m.1 - 1
      omega
    obtain ⟨h6, h7, h8⟩ := h5 m p (by simp only [p]; omega)
    have hd : Disjoint (W m) (R i) := by
      refine Set.disjoint_left.mpr fun x hx hxi => ?_
      have : x ∈ R p := (hs p).inter ▸ ⟨R_before h hs hip hxi, h8 hx⟩
      exact Set.disjoint_left.mp h7 hx this
    refine ⟨?_, hd⟩
    have hdc : Disjoint (W m) (X i ∩ Y i) := by rw [(hs i).inter]; exact hd
    rcases subset_side (hs i).discX.isClosed (hs i).discY.isClosed (h1 m)
      (by rw [(hs i).union]; exact h3 m) hdc with h9 | h9
    · exfalso
      have hcX : closure (W m) ⊆ X i := closure_minimal h9 (hs i).discX.isClosed
      have hx := (h.line p).left_mem
      have : a p ∈ X i ∩ Y i := ⟨hcX (h6 hx), R_after h hs hip hx⟩
      rw [(hs i).inter] at this
      exact Set.disjoint_left.mp (h.disj p i hip.ne') hx this
    · exact h9
  refine ⟨E, W, fun m => ⟨hE m, hEΔ m, rfl⟩, fun i => ⟨(hEX _ i rfl).1, (hEY _ i rfl).1⟩,
    fun m => ⟨h1 m, h2 m, h3 m⟩, ?_, fun m i hi => (hle m i hi).1, fun m i hi => (hlt m i hi).1,
    fun i => ⟨(h4 i.castSucc i rfl).1, (h5 i.succ i rfl).1⟩⟩
  intro m i
  by_cases hi : m.1 ≤ i.1
  · exact (hle m i hi).2
  · exact (hlt m i (by omega)).2

end Sides

end GraphMinor.GM12

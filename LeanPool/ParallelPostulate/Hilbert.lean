/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
module
public import LeanPool.ParallelPostulate.Geometry

/-!
# Hilbert planes, and the independence of the parallel postulate

`HilbertPlane P L` is a plane with points `P` and lines `L`, a betweenness, and congruence of
segments and of angles, that meets Hilbert's axioms of incidence (I1 to I3), of order (B1 to
B4) and of congruence (C1 to C6). Playfair's axiom, `HilbertPlane.Playfair`, is not among them.
The axioms of continuity are `HilbertPlane.Archimedes` and `HilbertPlane.Dedekind`.

`model κ` makes a Hilbert plane of the plane of `HyperbolicPlane` under a bound `κ` that
is not positive: its points and its lines, its `Between`, `apart` for segments and `kleinAngle`
for angles. `euclidPlane` is the bound 0 and `kleinPlane` the bound `-1`. Playfair's axiom
holds in the first and fails in the second, so it is independent of the axioms of a Hilbert
plane: `playfair_independent`. Both planes meet Archimedes' axiom and Dedekind's axiom, so it
is independent of these axioms too: `playfair_independent_continuous`.

Everything is in the namespace `Hilbert`.

## What is assumed, and what is not formalised

* **The axioms of a Hilbert plane**, as Hartshorne calls it, are those of incidence, order and
  congruence. The axioms of continuity are stated apart, as `Archimedes` and `Dedekind`, and
  both planes meet them.
* **Dedekind's axiom stands for Hilbert's axiom of completeness.** Hilbert's axiom V.2 says that
  the points of a line cannot be extended while the other axioms still hold. It is a statement
  about all the models, not an axiom inside one plane. Dedekind's axiom is the usual axiom in
  its place. That the two are equivalent, given Archimedes' axiom, is not formalised.
* **B4 is Pasch's axiom**, as Hilbert states it. Hartshorne takes plane separation instead.
  Given the other axioms the two are equivalent. That is not formalised.
* **A segment is a pair of points, and an angle is a triple with its vertex in the middle.**
  The fields `seg_swap`, `ang_swap` and `ang_rays` say that congruence does not see the order
  of the ends of a segment, the order of the two rays of an angle, or the points chosen on the
  rays.
* **Not in the style of Mathlib.** In Mathlib the plane would be built on `EuclideanSpace`,
  betweenness would be `Sbtw`, and Klein's distance would be `riemannianEDist`.
-/

public section

/-!
# The axioms of a Hilbert plane

`HilbertPlane P L` is a plane with points `P` and lines `L`, a betweenness, and congruence of
segments and of angles, that meets Hilbert's axioms of incidence (I1 to I3), of order (B1 to
B4, with Pasch's axiom as B4) and of congruence (C1 to C6). Playfair's axiom,
`HilbertPlane.Playfair`, is not among them. The axioms of continuity are
`HilbertPlane.Archimedes` and `HilbertPlane.Dedekind`.

The statement of `Hilbert.playfair_independent_continuous` uses only these synthetic definitions;
its proof constructs the models using the geometry module.

## Contents

* the axioms: `HilbertPlane`, `Collinear`, `OnRay`, `SameSide`
* Playfair's axiom: `HilbertPlane.Parallel`, `HilbertPlane.Playfair`
* the axioms of continuity: `HilbertPlane.Archimedes`, `HilbertPlane.Dedekind`
-/

namespace ParallelPostulate

namespace Hilbert

variable {P L : Type*}

/-- Three points on one line. -/
@[expose] def Collinear (lies : P → L → Prop) (A B C : P) : Prop :=
  ∃ l, lies A l ∧ lies B l ∧ lies C l

/-- `C` is on the ray from `A` through `B`, and is not `A`. -/
@[expose] def OnRay (btw : P → P → P → Prop) (A B C : P) : Prop :=
  C = B ∨ btw A C B ∨ btw A B C

/-- `A` and `B` are on the same side of `l`: neither is on `l`, and no point of `l` is between
them. -/
@[expose] def SameSide (lies : P → L → Prop) (btw : P → P → P → Prop) (l : L) (A B : P) : Prop :=
  ¬ lies A l ∧ ¬ lies B l ∧ ¬ ∃ C, lies C l ∧ btw A C B

/-- **A Hilbert plane**: Hilbert's axioms of incidence, order and congruence. A segment is a
pair of points and an angle `ABC` is a triple with its vertex `B` in the middle; the fields
`seg_swap`, `ang_swap` and `ang_rays` say that congruence does not see the order of the ends of a
segment, the order of the two rays of an angle, or the points chosen on the rays. -/
structure HilbertPlane (P L : Type*) where
  /-- The point lies on the line. -/
  lies : P → L → Prop
  /-- `btw A B C`: `B` is between `A` and `C`. -/
  btw : P → P → P → Prop
  /-- `segCong A B C D`: the segment `AB` is congruent to the segment `CD`. -/
  segCong : P → P → P → P → Prop
  /-- `angCong A B C D E F`: the angle `ABC`, at `B`, is congruent to the angle `DEF`, at `E`. -/
  angCong : P → P → P → P → P → P → Prop
  I1 : ∀ A B : P, A ≠ B → ∃! l, lies A l ∧ lies B l
  I2 : ∀ l : L, ∃ A B : P, A ≠ B ∧ lies A l ∧ lies B l
  I3 : ∃ A B C : P, ¬ Collinear lies A B C
  B1 : ∀ A B C : P, btw A B C → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear lies A B C ∧ btw C B A
  B2 : ∀ A B : P, A ≠ B → ∃ C, btw A B C
  B3 : ∀ A B C : P, A ≠ B → B ≠ C → A ≠ C → Collinear lies A B C →
    (btw A B C ∨ btw B A C ∨ btw A C B) ∧ ¬ (btw A B C ∧ btw B A C) ∧
      ¬ (btw A B C ∧ btw A C B) ∧ ¬ (btw B A C ∧ btw A C B)
  B4 : ∀ (A B C : P) (l : L), ¬ Collinear lies A B C → ¬ lies A l → ¬ lies B l → ¬ lies C l →
    (∃ D, lies D l ∧ btw A D B) → ∃ E, lies E l ∧ (btw A E C ∨ btw B E C)
  seg_swap : ∀ A B : P, segCong A B B A
  ang_swap : ∀ A B C : P, angCong A B C C B A
  ang_rays : ∀ A B C A' C' : P, OnRay btw B A A' → OnRay btw B C C' → angCong A B C A' B C'
  C1 : ∀ A B C R : P, A ≠ B → C ≠ R → ∃! D, OnRay btw C R D ∧ segCong A B C D
  C2 : ∀ A B C D E F : P, segCong A B C D → segCong A B E F → segCong C D E F
  C2_refl : ∀ A B : P, segCong A B A B
  C3 : ∀ A B C D E F : P, btw A B C → btw D E F → segCong A B D E → segCong B C E F →
    segCong A C D F
  C4 : ∀ (A B C D F G : P) (l : L), ¬ Collinear lies A B C → D ≠ F → lies D l → lies F l →
    ¬ lies G l →
    (∃ E, SameSide lies btw l E G ∧ angCong A B C E D F) ∧
    ∀ E E', SameSide lies btw l E G → angCong A B C E D F → SameSide lies btw l E' G →
      angCong A B C E' D F → OnRay btw D E E'
  C5 : ∀ A B C D E F G H I : P, angCong A B C D E F → angCong A B C G H I → angCong D E F G H I
  C5_refl : ∀ A B C : P, angCong A B C A B C
  C6 : ∀ A B C D E F : P, ¬ Collinear lies A B C → ¬ Collinear lies D E F →
    segCong A B D E → segCong A C D F → angCong B A C E D F →
    segCong B C E F ∧ angCong A B C D E F ∧ angCong A C B D F E

namespace HilbertPlane

variable (H : HilbertPlane P L)

/-- Two lines are parallel when they have no point in common. -/
@[expose] def Parallel (l m : L) : Prop := ¬ ∃ A, H.lies A l ∧ H.lies A m

/-- **Playfair's axiom**: through a point that is not on a line there is at most one line
parallel to it. -/
@[expose] def Playfair : Prop :=
  ∀ (l : L) (A : P), ¬ H.lies A l → ∀ m m' : L, H.lies A m → H.Parallel m l →
    H.lies A m' → H.Parallel m' l → m = m'

/-- **Archimedes' axiom.** Laid off one after the other along the ray from `A` through `B`,
starting at `A`, enough copies of a segment `CD` reach `B` or pass it. -/
@[expose] def Archimedes : Prop :=
  ∀ A B C D : P, A ≠ B → C ≠ D → ∃ (n : ℕ) (X : ℕ → P), X 0 = A ∧
    (∀ i < n, H.segCong C D (X i) (X (i + 1))) ∧ (∀ i < n, OnRay H.btw A B (X (i + 1))) ∧
    (∀ i, i + 2 ≤ n → H.btw (X i) (X (i + 1)) (X (i + 2))) ∧ (H.btw A B (X n) ∨ X n = B)

/-- **Dedekind's axiom.** Split the points of a line into two parts, neither empty, so that no
point of either part is between two points of the other. Then there is one point, and only
one, that is between every point of the one part and every point of the other, unless it is
one of them. -/
@[expose] def Dedekind : Prop :=
  ∀ (l : L) (S T : Set P), (∀ X, H.lies X l ↔ X ∈ S ∨ X ∈ T) → (∀ X ∈ S, X ∉ T) →
    S.Nonempty → T.Nonempty → (∀ X ∈ S, ∀ Y ∈ T, ∀ Z ∈ T, ¬ H.btw Y X Z) →
    (∀ X ∈ T, ∀ Y ∈ S, ∀ Z ∈ S, ¬ H.btw Y X Z) →
    ∃! Q, H.lies Q l ∧ ∀ A ∈ S, ∀ B ∈ T, A ≠ Q → B ≠ Q → H.btw A Q B

end HilbertPlane

end Hilbert

end ParallelPostulate

/-!
# The plane of a bound as a Hilbert plane

`model κ` makes a Hilbert plane of the plane of a bound `κ` that is not positive: its points and
its lines, its `Between`, `apart` for segments and `kleinAngle` for angles.

## Contents

* the model: `Pt`, `Ln`, `mlies`, `mbtw`, `msegCong`, `mangCong`, `lineThrough`, `model_I1` to
  `model_I3`, `model_B1` to `model_B4`, `model_onRay`, `model_onRay_of`, `model_C1`,
  `model_side_ne_zero`, `model_sameSide_iff`, `model_C4`, `model_C6`, `model`
-/

namespace ParallelPostulate

namespace Hilbert

open Pairs HyperbolicPlane

open Real

/-! ## The plane of a bound as a Hilbert plane -/

/-- The points of the plane of the bound `κ`. -/
abbrev Pt (κ : ℝ) := {p : ℝ × ℝ // p ∈ plane κ}

/-- The lines of the plane of the bound `κ`. -/
abbrev Ln (κ : ℝ) := {S : Set (ℝ × ℝ) // IsLine (plane κ) S}

/-- A point lies on a line. -/
@[expose] def mlies (κ : ℝ) (p : Pt κ) (l : Ln κ) : Prop := p.1 ∈ l.1

/-- Betweenness is the file's `Between`. -/
@[expose] def mbtw (κ : ℝ) (A B C : Pt κ) : Prop := Between A.1 B.1 C.1

/-- Two segments are congruent when `apart` is the same for both. -/
@[expose] def msegCong (κ : ℝ) (A B C D : Pt κ) : Prop := apart κ A.1 B.1 = apart κ C.1 D.1

/-- The angle `ABC` is congruent to `DEF` when `kleinAngle` is the same at `B` and at `E`. -/
@[expose] def mangCong (κ : ℝ) (A B C D E F : Pt κ) : Prop :=
  kleinAngle κ B.1 A.1 C.1 = kleinAngle κ E.1 D.1 F.1

/-- The line through two different points of the plane. -/
@[expose] def lineThrough {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) : Ln κ :=
  ⟨(Dim.mk A.1 B.1).points ∩ plane κ, ⟨Dim.mk A.1 B.1, h, rfl, A.1, (Dim.mk _ _).zero_mem, A.2⟩⟩

theorem lies_lineThrough_left {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) :
    mlies κ A (lineThrough A B h) := ⟨(Dim.mk _ _).zero_mem, A.2⟩

theorem lies_lineThrough_right {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) :
    mlies κ B (lineThrough A B h) := ⟨(Dim.mk _ _).one_mem, B.2⟩

theorem model_I1 (κ : ℝ) : ∀ A B : Pt κ, A ≠ B → ∃! l, mlies κ A l ∧ mlies κ B l := by
  intro A B hAB
  obtain ⟨S, ⟨hS, hA, hB⟩, huniq⟩ :=
    line_through (plane κ) A.2 B.2 (fun h => hAB (Subtype.ext h))
  exact ⟨⟨S, hS⟩, ⟨hA, hB⟩, fun l hl => Subtype.ext (huniq l.1 ⟨l.2, hl.1, hl.2⟩)⟩

theorem model_I2 (κ : ℝ) : ∀ l : Ln κ, ∃ A B : Pt κ, A ≠ B ∧ mlies κ A l ∧ mlies κ B l := by
  intro l
  obtain ⟨A, B, hAB, hA, hB⟩ := l.2.two_points (plane_openAlong κ)
  exact ⟨⟨A, l.2.subset_plane hA⟩, ⟨B, l.2.subset_plane hB⟩,
    fun h => hAB (congrArg Subtype.val h), hA, hB⟩

theorem model_I3 (κ : ℝ) : ∃ A B C : Pt κ, ¬ Collinear (mlies κ) A B C := by
  obtain ⟨A, B, C, hA, hB, hC, h⟩ := exists_three_points κ
  exact ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, fun ⟨l, h1, h2, h3⟩ => h l.1 l.2 ⟨h1, h2, h3⟩⟩

theorem model_B1 (κ : ℝ) : ∀ A B C : Pt κ, mbtw κ A B C →
    A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear (mlies κ) A B C ∧ mbtw κ C B A := by
  intro A B C h
  obtain ⟨h1, h2, h3⟩ := Between.ne h
  exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e),
    fun e => h3 (congrArg Subtype.val e),
    ⟨lineThrough A C h3, lies_lineThrough_left A C h3, ⟨Between.mem h, B.2⟩,
      lies_lineThrough_right A C h3⟩, Between.symm h⟩

theorem model_B2 (κ : ℝ) : ∀ A B : Pt κ, A ≠ B → ∃ C, mbtw κ A B C := by
  intro A B hAB
  obtain ⟨C, hC, h⟩ := exists_beyond κ (fun e => hAB (Subtype.ext e)) B.2
  exact ⟨⟨C, hC⟩, h⟩

theorem model_B3 (κ : ℝ) : ∀ A B C : Pt κ, A ≠ B → B ≠ C → A ≠ C → Collinear (mlies κ) A B C →
    (mbtw κ A B C ∨ mbtw κ B A C ∨ mbtw κ A C B) ∧ ¬ (mbtw κ A B C ∧ mbtw κ B A C) ∧
      ¬ (mbtw κ A B C ∧ mbtw κ A C B) ∧ ¬ (mbtw κ B A C ∧ mbtw κ A C B) := by
  intro A B C hAB hBC hAC ⟨l, hA, hB, hC⟩
  have hAC' : A.1 ≠ C.1 := fun e => hAC (Subtype.ext e)
  have hBm : B.1 ∈ (Dim.mk A.1 C.1).points := by
    have h : B.1 ∈ l.1 := hB
    rw [IsLine.eq_through l.2 hA hC hAC'] at h
    exact h.1
  exact ⟨between_trichotomy (fun e => hAB (Subtype.ext e)) (fun e => hBC (Subtype.ext e)) hAC'
      hBm, fun ⟨h1, h2⟩ => Between.not_left h1 h2, fun ⟨h1, h2⟩ => Between.not_right h1 h2,
    fun ⟨h1, h2⟩ => Between.not_right h1 (Between.symm h2)⟩

theorem model_B4 (κ : ℝ) : ∀ (A B C : Pt κ) (l : Ln κ), ¬ Collinear (mlies κ) A B C →
    ¬ mlies κ A l → ¬ mlies κ B l → ¬ mlies κ C l →
    (∃ D, mlies κ D l ∧ mbtw κ A D B) → ∃ E, mlies κ E l ∧ (mbtw κ A E C ∨ mbtw κ B E C) := by
  intro A B C l _ hA hB hC ⟨D, hD, hAD⟩
  obtain ⟨M, hM, hl, -⟩ := l.2
  have hnot : ∀ X : Pt κ, ¬ mlies κ X l → X.1 ∉ M.points := fun X hX hm =>
    hX (by change X.1 ∈ l.1; rw [hl]; exact ⟨hm, X.2⟩)
  have hDm : D.1 ∈ M.points := by
    have h : D.1 ∈ l.1 := hD
    rw [hl] at h
    exact h.1
  obtain ⟨Y, hYM, hY, hYb⟩ :=
    pasch κ A.2 B.2 C.2 M hM (hnot A hA) (hnot B hB) (hnot C hC) hDm hAD
  exact ⟨⟨Y, hY⟩, by change Y ∈ l.1; rw [hl]; exact ⟨hYM, hY⟩, hYb⟩

/-- A point on a ray, as Hilbert has it, in the plane of a bound. -/
theorem model_onRay {κ : ℝ} {O A X : Pt κ} (h : Hilbert.OnRay (mbtw κ) O A X) :
    HyperbolicPlane.OnRay O.1 A.1 X.1 :=
  onRay_of_between (h.imp (congrArg Subtype.val) id)

theorem model_onRay_of {κ : ℝ} {O A X : Pt κ} (hOA : O.1 ≠ A.1)
    (h : HyperbolicPlane.OnRay O.1 A.1 X.1) : Hilbert.OnRay (mbtw κ) O A X :=
  (between_of_onRay hOA h).imp Subtype.ext id

theorem model_C1 (κ : ℝ) (hκ : κ ≤ 0) : ∀ A B C R : Pt κ, A ≠ B → C ≠ R →
    ∃! D, Hilbert.OnRay (mbtw κ) C R D ∧ msegCong κ A B C D := by
  intro A B C R hAB hCR
  have hCR' : C.1 ≠ R.1 := fun e => hCR (Subtype.ext e)
  obtain ⟨X, ⟨hX, hray, hap⟩, huniq⟩ :=
    segment_construction_apart hκ A.2 B.2 C.2 (fun e => hAB (Subtype.ext e)) hCR'
  refine ⟨⟨X, hX⟩, ⟨model_onRay_of hCR' hray, hap⟩, ?_⟩
  rintro D ⟨hD, hapD⟩
  exact Subtype.ext (huniq D.1 ⟨D.2, model_onRay hD, hapD⟩)

/-- Three points of the plane that are not on one line give a side that is not 0. -/
theorem model_side_ne_zero {κ : ℝ} {A B C : Pt κ} (h : ¬ Collinear (mlies κ) A B C) :
    (Dim.mk B.1 A.1).side C.1 ≠ 0 := by
  intro hs
  apply h
  by_cases hBA : B.1 = A.1
  · by_cases hAC : A.1 = C.1
    · have hne : A.1 ≠ (A.1.1 + 1, A.1.2) := by
        intro e
        have := congrArg Prod.fst e
        simp at this
      refine ⟨⟨(Dim.mk A.1 (A.1.1 + 1, A.1.2)).points ∩ plane κ,
        ⟨_, hne, rfl, A.1, (Dim.mk _ _).zero_mem, A.2⟩⟩, ⟨(Dim.mk _ _).zero_mem, A.2⟩, ?_, ?_⟩
      · change B.1 ∈ _
        rw [hBA]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
      · change C.1 ∈ _
        rw [← hAC]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
    · refine ⟨lineThrough A C hAC, lies_lineThrough_left A C hAC, ?_,
        lies_lineThrough_right A C hAC⟩
      change B.1 ∈ _
      rw [hBA]
      exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
  · exact ⟨lineThrough B A hBA, lies_lineThrough_right B A hBA, lies_lineThrough_left B A hBA,
      ⟨Dim.mem_points_of_side_eq_zero _ hBA C.1 hs, C.2⟩⟩

/-- Hilbert's sides of a line, in the plane of a bound, are the signs of `side`. -/
theorem model_sameSide_iff {κ : ℝ} {D F : Pt κ} {l : Ln κ} (hD : mlies κ D l) (hF : mlies κ F l)
    (hDF : D.1 ≠ F.1) (E G : Pt κ) :
    Hilbert.SameSide (mlies κ) (mbtw κ) l E G ↔ HyperbolicPlane.SameSide D.1 F.1 E.1 G.1 := by
  have hl := IsLine.eq_through l.2 hD hF hDF
  have hmem : ∀ X : Pt κ, mlies κ X l ↔ (Dim.mk D.1 F.1).side X.1 = 0 := by
    intro X
    change X.1 ∈ l.1 ↔ _
    rw [hl]
    constructor
    · rintro ⟨h, -⟩
      exact Dim.side_eq_zero_of_mem _ h
    · intro h
      exact ⟨Dim.mem_points_of_side_eq_zero _ hDF X.1 h, X.2⟩
  constructor
  · rintro ⟨hE, hG, hno⟩
    have hE' : (Dim.mk D.1 F.1).side E.1 ≠ 0 := fun h => hE ((hmem E).mpr h)
    have hG' : (Dim.mk D.1 F.1).side G.1 ≠ 0 := fun h => hG ((hmem G).mpr h)
    change 0 < _ * _
    rcases lt_trichotomy ((Dim.mk D.1 F.1).side E.1 * (Dim.mk D.1 F.1).side G.1) 0 with h | h | h
    · obtain ⟨Y, hYM, hY, hYb⟩ := crosses κ (Dim.mk D.1 F.1) hDF E.2 G.2 h
      exact absurd ⟨⟨Y, hY⟩, (hmem ⟨Y, hY⟩).mpr (Dim.side_eq_zero_of_mem _ hYM), hYb⟩ hno
    · exact absurd h (mul_ne_zero hE' hG')
    · exact h
  · intro h
    have h' : 0 < (Dim.mk D.1 F.1).side E.1 * (Dim.mk D.1 F.1).side G.1 := h
    have hE' : (Dim.mk D.1 F.1).side E.1 ≠ 0 := by
      intro e
      rw [e, zero_mul] at h'
      exact lt_irrefl 0 h'
    have hG' : (Dim.mk D.1 F.1).side G.1 ≠ 0 := by
      intro e
      rw [e, mul_zero] at h'
      exact lt_irrefl 0 h'
    refine ⟨fun hm => hE' ((hmem E).mp hm), fun hm => hG' ((hmem G).mp hm), ?_⟩
    rintro ⟨C, hCl, ⟨-, u, hu0, hu1, hC⟩⟩
    have h0 := (hmem C).mp hCl
    rw [← hC, Dim.side_through] at h0
    have h1 := congrArg (· * (Dim.mk D.1 F.1).side E.1) h0
    simp only [zero_mul] at h1
    have h2 : 0 < (1 - u) * (Dim.mk D.1 F.1).side E.1 ^ 2 :=
      mul_pos (sub_pos.mpr hu1) (by positivity)
    have h3 := mul_pos hu0 h'
    nlinarith

theorem model_C4 (κ : ℝ) : ∀ (A B C D F G : Pt κ) (l : Ln κ), ¬ Collinear (mlies κ) A B C →
    D ≠ F → mlies κ D l → mlies κ F l → ¬ mlies κ G l →
    (∃ E, Hilbert.SameSide (mlies κ) (mbtw κ) l E G ∧ mangCong κ A B C E D F) ∧
    ∀ E E', Hilbert.SameSide (mlies κ) (mbtw κ) l E G → mangCong κ A B C E D F →
      Hilbert.SameSide (mlies κ) (mbtw κ) l E' G → mangCong κ A B C E' D F →
      Hilbert.OnRay (mbtw κ) D E E' := by
  intro A B C D F G l hABC hDF hD hF hG
  have hDF' : D.1 ≠ F.1 := fun e => hDF (Subtype.ext e)
  have hl := IsLine.eq_through l.2 hD hF hDF'
  have hGs : (Dim.mk D.1 F.1).side G.1 ≠ 0 := by
    intro h
    apply hG
    change G.1 ∈ l.1
    rw [hl]
    exact ⟨Dim.mem_points_of_side_eq_zero _ hDF' G.1 h, G.2⟩
  obtain ⟨hex, huniq⟩ := angle_construction B.2 D.2 (model_side_ne_zero hABC) hDF' hGs
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE, hs, ha⟩ := hex
    refine ⟨⟨E, hE⟩, (model_sameSide_iff hD hF hDF' ⟨E, hE⟩ G).mpr hs, ?_⟩
    change kleinAngle κ B.1 A.1 C.1 = kleinAngle κ D.1 E F.1
    rw [kleinAngle_comm κ D.1 E F.1, ha]
  · intro E E' hs ha hs' ha'
    have hDE : D.1 ≠ E.1 := by
      intro e
      apply hs.1
      rw [show E = D from (Subtype.ext e).symm]
      exact hD
    unfold mangCong at ha ha'
    have hr := huniq E.1 E'.1 E.2 ((model_sameSide_iff hD hF hDF' E G).mp hs)
      (by rw [kleinAngle_comm]; exact ha.symm) E'.2 ((model_sameSide_iff hD hF hDF' E' G).mp hs')
      (by rw [kleinAngle_comm]; exact ha'.symm)
    exact model_onRay_of hDE hr

theorem model_C6 (κ : ℝ) (hκ : κ ≤ 0) : ∀ A B C D E F : Pt κ, ¬ Collinear (mlies κ) A B C →
    ¬ Collinear (mlies κ) D E F → msegCong κ A B D E → msegCong κ A C D F →
    mangCong κ B A C E D F →
    msegCong κ B C E F ∧ mangCong κ A B C D E F ∧ mangCong κ A C B D F E := by
  intro A B C D E F h1 h2 e1 e2 e3
  obtain ⟨hBA, hCB, hCA⟩ := ne_of_side_ne_zero (model_side_ne_zero h1)
  obtain ⟨hED, hFE, hFD⟩ := ne_of_side_ne_zero (model_side_ne_zero h2)
  exact sas_apart hκ A.2 B.2 C.2 D.2 E.2 F.2 hBA.symm hCA.symm hCB.symm hED.symm hFD.symm
    hFE.symm e1 e2 e3

/-- **The plane of a bound that is not positive is a Hilbert plane.** -/
@[expose] noncomputable def model (κ : ℝ) (hκ : κ ≤ 0) : HilbertPlane (Pt κ) (Ln κ) where
  lies := mlies κ
  btw := mbtw κ
  segCong := msegCong κ
  angCong := mangCong κ
  I1 := model_I1 κ
  I2 := model_I2 κ
  I3 := model_I3 κ
  B1 := model_B1 κ
  B2 := model_B2 κ
  B3 := model_B3 κ
  B4 := model_B4 κ
  seg_swap := fun A B => apart_comm κ A.1 B.1
  ang_swap := fun A B C => kleinAngle_comm κ B.1 A.1 C.1
  ang_rays := fun _ _ _ _ _ hA hC => (kleinAngle_onRay (model_onRay hA) (model_onRay hC)).symm
  C1 := model_C1 κ hκ
  C2 := fun _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
  C2_refl := fun _ _ => rfl
  C3 := fun A _ C D _ F h1 h2 h3 h4 => segment_addition_apart hκ A.2 C.2 D.2 F.2 h1 h2 h3 h4
  C4 := model_C4 κ
  C5 := fun _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
  C5_refl := fun _ _ _ => rfl
  C6 := model_C6 κ hκ

end Hilbert

end ParallelPostulate

/-!
# The axioms of continuity in the plane of a bound

The plane of every bound that is not positive meets Dedekind's axiom and Archimedes' axiom. A
line is an interval of numbers, so Dedekind's axiom is the least upper bound of the real
numbers. Archimedes' axiom follows from a length of segments that adds along a segment: Klein's
distance under a negative bound, and the square root of `apart` under the bound 0.

## Contents

* a cut of an interval of real numbers: `cut_point_ordered`, `cut_point`
* Dedekind's axiom in the plane of a bound: `model_dedekind`
* Archimedes' axiom in the plane of a bound: `archimedes_of_length`, `model_archimedes`
-/

namespace ParallelPostulate

namespace Hilbert

open Pairs HyperbolicPlane

/-! ## A cut of an interval of real numbers -/

/-- A cut of an interval, with the first part below the second, has one cut point. -/
theorem cut_point_ordered {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hsep : ∀ s ∈ S, ∀ t ∈ T, s < t) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨t0, ht0⟩ := hTne
  have hbdd : BddAbove S := ⟨t0, fun s hs => (hsep s hs t0 ht0).le⟩
  have hle : ∀ s ∈ S, s ≤ sSup S := fun s hs => le_csSup hbdd hs
  have hge : ∀ t ∈ T, sSup S ≤ t := fun t ht => csSup_le ⟨s0, hs0⟩ fun s hs => (hsep s hs t ht).le
  have hcI : sSup S ∈ I :=
    hI s0 ((hST s0).mpr (Or.inl hs0)) t0 ((hST t0).mpr (Or.inr ht0)) _ (hle s0 hs0) (hge t0 ht0)
  refine ⟨sSup S, ⟨hcI, fun a ha b hb hac hbc =>
    Or.inl ⟨lt_of_le_of_ne (hle a ha) hac, lt_of_le_of_ne (hge b hb) hbc.symm⟩⟩, ?_⟩
  rintro c' ⟨hc'I, hc'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨s, hs, hcs⟩ := exists_lt_of_lt_csSup ⟨s0, hs0⟩ hlt
    have ht0c : c' < t0 := lt_of_lt_of_le hlt (hge t0 ht0)
    rcases hc' s hs t0 ht0 hcs.ne' ht0c.ne' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
  · set m := (sSup S + c') / 2 with hm
    have hm1 : sSup S < m := by linarith
    have hm2 : m < c' := by linarith
    have hmI : m ∈ I := hI _ hcI _ hc'I m hm1.le hm2.le
    have hmT : m ∈ T := by
      rcases (hST m).mp hmI with h | h
      · exact absurd (hle m h) (not_le.mpr hm1)
      · exact h
    have hs0c : s0 < c' := lt_of_le_of_lt (hle s0 hs0) hgt
    rcases hc' s0 hs0 m hmT hs0c.ne hm2.ne with ⟨-, h2⟩ | ⟨-, h2⟩ <;> linarith

/-- **A cut of an interval of real numbers has one cut point.** -/
theorem cut_point {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hdisj : ∀ t ∈ S, t ∉ T) (hSne : S.Nonempty)
    (hTne : T.Nonempty) (hS : ∀ x ∈ S, ∀ y ∈ T, ∀ z ∈ T, ¬ StrictBetween y x z)
    (hT : ∀ x ∈ T, ∀ y ∈ S, ∀ z ∈ S, ¬ StrictBetween y x z) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨t0, ht0⟩ := hTne
  have hst0 : s0 ≠ t0 := fun e => hdisj s0 hs0 (e ▸ ht0)
  rcases lt_or_gt_of_ne hst0 with hlt | hgt
  · apply cut_point_ordered hI hST ⟨s0, hs0⟩ ⟨t0, ht0⟩
    intro s hs t ht
    by_contra hts
    have hts' : t < s := lt_of_le_of_ne (not_lt.mp hts) (fun e => hdisj s hs (e ▸ ht))
    have hts0 : t ≠ s0 := fun e => hdisj s0 hs0 (e ▸ ht)
    rcases lt_or_gt_of_ne hts0 with h | h
    · exact hS s0 hs0 t ht t0 ht0 (Or.inl ⟨h, hlt⟩)
    · exact hT t ht s0 hs0 s hs (Or.inl ⟨h, hts'⟩)
  · have hST' : ∀ t, t ∈ I ↔ t ∈ T ∨ t ∈ S := fun t => (hST t).trans or_comm
    have hsep : ∀ t ∈ T, ∀ s ∈ S, t < s := by
      intro t ht s hs
      by_contra hst
      have hst' : s < t := lt_of_le_of_ne (not_lt.mp hst) (fun e => hdisj s hs (e ▸ ht))
      have hts0 : t ≠ s0 := fun e => hdisj s0 hs0 (e ▸ ht)
      rcases lt_or_gt_of_ne hts0 with h | h
      · exact hT t ht s hs s0 hs0 (Or.inl ⟨hst', h⟩)
      · exact hS s0 hs0 t0 ht0 t ht (Or.inl ⟨hgt, h⟩)
    obtain ⟨c, ⟨hcI, hc⟩, huniq⟩ := cut_point_ordered hI hST' ⟨t0, ht0⟩ ⟨s0, hs0⟩ hsep
    have hsymm : ∀ a c b : ℝ, StrictBetween a c b ↔ StrictBetween b c a :=
      fun _ _ _ => or_comm
    refine ⟨c, ⟨hcI, fun a ha b hb hac hbc => (hsymm _ _ _).mpr (hc b hb a ha hbc hac)⟩, ?_⟩
    rintro c' ⟨hc'I, hc'⟩
    exact huniq c' ⟨hc'I, fun b hb a ha hbc hac => (hsymm _ _ _).mpr (hc' a ha b hb hac hbc)⟩

/-! ## Dedekind's axiom in the plane of a bound -/

/-- **Dedekind's axiom holds in the plane of a bound that is not positive.** -/
theorem model_dedekind (κ : ℝ) (hκ : κ ≤ 0) : (model κ hκ).Dedekind := by
  intro l S T hST hdisj hSne hTne hS hT
  obtain ⟨M, hM, hl, -⟩ := l.2
  have hlies : ∀ X : Pt κ, (model κ hκ).lies X l ↔ X.1 ∈ M.points := by
    intro X
    change X.1 ∈ l.1 ↔ _
    rw [hl]
    exact ⟨fun h => h.1, fun h => ⟨h, X.2⟩⟩
  let I : Set ℝ := {t | M.pt t ∈ plane κ}
  let S' : Set ℝ := {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ S}
  let T' : Set ℝ := {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ T}
  have hpar : ∀ X : Pt κ, (model κ hκ).lies X l → ∃ t, ∃ h : M.pt t ∈ plane κ,
      X = ⟨M.pt t, h⟩ := by
    intro X hX
    obtain ⟨t, ht⟩ := (hlies X).mp hX
    exact ⟨t, ht ▸ X.2, Subtype.ext ht.symm⟩
  have hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I :=
    fun a ha b hb c hac hcb => pt_mem_plane_of_le M ha hb hac hcb
  have hST' : ∀ t, t ∈ I ↔ t ∈ S' ∨ t ∈ T' := by
    intro t
    constructor
    · intro h
      rcases (hST ⟨M.pt t, h⟩).mp ((hlies _).mpr ⟨t, rfl⟩) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj' : ∀ t ∈ S', t ∉ T' := fun t ⟨h, hs⟩ ⟨_, ht⟩ => hdisj _ hs ht
  have hne' : ∀ {U : Set (Pt κ)} {U' : Set ℝ}, (∀ X ∈ U, (model κ hκ).lies X l) →
      U' = {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ U} → U.Nonempty →
      U'.Nonempty := by
    rintro U U' hU rfl ⟨X, hX⟩
    obtain ⟨t, h, rfl⟩ := hpar X (hU X hX)
    exact ⟨t, h, hX⟩
  have hSl : ∀ X ∈ S, (model κ hκ).lies X l := fun X hX => (hST X).mpr (Or.inl hX)
  have hTl : ∀ X ∈ T, (model κ hκ).lies X l := fun X hX => (hST X).mpr (Or.inr hX)
  have hS' : ∀ x ∈ S', ∀ y ∈ T', ∀ z ∈ T', ¬ StrictBetween y x z :=
    fun x ⟨hx, hxS⟩ y ⟨hy, hyT⟩ z ⟨hz, hzT⟩ h =>
      hS _ hxS _ hyT _ hzT (between_pt_of_strictBetween M hM h)
  have hT' : ∀ x ∈ T', ∀ y ∈ S', ∀ z ∈ S', ¬ StrictBetween y x z :=
    fun x ⟨hx, hxT⟩ y ⟨hy, hyS⟩ z ⟨hz, hzS⟩ h =>
      hT _ hxT _ hyS _ hzS (between_pt_of_strictBetween M hM h)
  obtain ⟨c, ⟨hcI, hc⟩, huniq⟩ := cut_point hI hST' hdisj' (hne' hSl rfl hSne)
    (hne' hTl rfl hTne) hS' hT'
  refine ⟨⟨M.pt c, hcI⟩, ⟨(hlies _).mpr ⟨c, rfl⟩, ?_⟩, ?_⟩
  · intro A hA B hB hAQ hBQ
    obtain ⟨a, ha, rfl⟩ := hpar A (hSl A hA)
    obtain ⟨b, hb, rfl⟩ := hpar B (hTl B hB)
    exact between_pt_of_strictBetween M hM (hc a ⟨ha, hA⟩ b ⟨hb, hB⟩
      (fun e => hAQ (by subst e; rfl)) (fun e => hBQ (by subst e; rfl)))
  · rintro Q ⟨hQl, hQ⟩
    obtain ⟨c', hc', rfl⟩ := hpar Q hQl
    have := huniq c' ⟨hc', fun a ⟨ha, hA⟩ b ⟨hb, hB⟩ hac hbc =>
      strictBetween_of_between_pt M hM (hQ _ hA _ hB
        (fun e => hac (M.pt_injective hM (congrArg Subtype.val e)))
        (fun e => hbc (M.pt_injective hM (congrArg Subtype.val e))))⟩
    subst this
    rfl

/-! ## Archimedes' axiom in the plane of a bound -/

/-- **Archimedes' axiom, from a length.** Suppose a length of segments of the plane is 0 for
a point and positive for two different points, adds along a segment, is equal for two segments
exactly when `apart` is, and takes every positive value on every ray. Then the plane meets
Archimedes' axiom. -/
theorem archimedes_of_length {κ : ℝ} (hκ : κ ≤ 0) (len : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hcong : ∀ {P Q R S : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → R ∈ plane κ → S ∈ plane κ →
      (apart κ P Q = apart κ R S ↔ len P Q = len R S))
    (hadd : ∀ {A B C : ℝ × ℝ}, A ∈ plane κ → C ∈ plane κ → Between A B C →
      len A C = len A B + len B C)
    (hpos : ∀ {P Q : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → P ≠ Q → 0 < len P Q)
    (hzero : ∀ {P : ℝ × ℝ}, P ∈ plane κ → len P P = 0)
    (hexist : ∀ {O D : ℝ × ℝ}, O ∈ plane κ → O ≠ D → ∀ d, 0 < d →
      ∃ t, 0 < t ∧ (Dim.mk O D).pt t ∈ plane κ ∧ len O ((Dim.mk O D).pt t) = d) :
    (model κ hκ).Archimedes := by
  intro A B C D hAB hCD
  have hAB' : A.1 ≠ B.1 := fun e => hAB (Subtype.ext e)
  have hM : (Dim.mk A.1 B.1).zero ≠ (Dim.mk A.1 B.1).one := hAB'
  have hpt0 : (Dim.mk A.1 B.1).pt 0 = A.1 := Dim.pt_zero _
  have hpt1 : (Dim.mk A.1 B.1).pt 1 = B.1 := Dim.pt_one _
  have hδ : 0 < len C.1 D.1 := hpos C.2 D.2 (fun e => hCD (Subtype.ext e))
  have hch : ∀ i : ℕ, ∃ t, 0 < t ∧ (Dim.mk A.1 B.1).pt t ∈ plane κ ∧
      len A.1 ((Dim.mk A.1 B.1).pt t) = ((i : ℝ) + 1) * len C.1 D.1 :=
    fun i => hexist A.2 hAB' _ (by positivity)
  choose u hu0 hum hul using hch
  let σ : ℕ → ℝ := fun i => match i with
    | 0 => 0
    | i + 1 => u i
  have hσm : ∀ i, (Dim.mk A.1 B.1).pt (σ i) ∈ plane κ := by
    rintro (_ | i)
    · change (Dim.mk A.1 B.1).pt 0 ∈ plane κ
      rw [hpt0]
      exact A.2
    · exact hum i
  have hσl : ∀ i : ℕ, len A.1 ((Dim.mk A.1 B.1).pt (σ i)) = (i : ℝ) * len C.1 D.1 := by
    rintro (_ | i)
    · change len A.1 ((Dim.mk A.1 B.1).pt 0) = _
      rw [hpt0, hzero A.2]
      simp
    · change len A.1 ((Dim.mk A.1 B.1).pt (u i)) = _
      rw [hul i]
      push_cast
      ring
  have hσ0 : ∀ i, 0 ≤ σ i := by
    rintro (_ | i)
    · exact le_rfl
    · exact (hu0 i).le
  have hmono : ∀ s t : ℝ, 0 ≤ t → (Dim.mk A.1 B.1).pt s ∈ plane κ →
      (Dim.mk A.1 B.1).pt t ∈ plane κ →
      len A.1 ((Dim.mk A.1 B.1).pt s) < len A.1 ((Dim.mk A.1 B.1).pt t) → s < t := by
    intro s t ht hsm htm hlt
    by_contra hts
    rcases (not_lt.mp hts).eq_or_lt with e | e
    · rw [e] at hlt
      exact lt_irrefl _ hlt
    · rcases ht.eq_or_lt with e0 | e0
      · rw [← e0, hpt0, hzero A.2] at hlt
        rw [← e0] at e
        have hne : A.1 ≠ (Dim.mk A.1 B.1).pt s :=
          fun h => e.ne (Dim.pt_injective _ hM (hpt0.trans h))
        linarith [hpos A.2 hsm hne]
      · have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM (Or.inl ⟨e0, e⟩)
        rw [hpt0] at hb
        have hsum := hadd A.2 hsm hb
        have hne : (Dim.mk A.1 B.1).pt t ≠ (Dim.mk A.1 B.1).pt s :=
          fun h => e.ne (Dim.pt_injective _ hM h)
        linarith [hpos htm hsm hne]
  have hσlt : ∀ i j : ℕ, i < j → σ i < σ j := by
    intro i j hij
    apply hmono _ _ (hσ0 j) (hσm i) (hσm j)
    rw [hσl, hσl]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hδ
  let X : ℕ → Pt κ := fun i => ⟨(Dim.mk A.1 B.1).pt (σ i), hσm i⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (len A.1 B.1 / len C.1 D.1)
  refine ⟨n, X, Subtype.ext hpt0, ?_, ?_, ?_, ?_⟩
  · intro i _
    change apart κ C.1 D.1 = apart κ ((Dim.mk A.1 B.1).pt (σ i)) ((Dim.mk A.1 B.1).pt (σ (i + 1)))
    rw [hcong C.2 D.2 (hσm i) (hσm (i + 1))]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h1 := hσl 1
      change len C.1 D.1 = len ((Dim.mk A.1 B.1).pt 0) ((Dim.mk A.1 B.1).pt (σ 1))
      rw [hpt0, h1]
      simp
    · have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM
        (Or.inl ⟨(hσlt 0 i hi : 0 < σ i), hσlt i (i + 1) (by omega)⟩)
      rw [hpt0] at hb
      have hsum := hadd A.2 (hσm (i + 1)) hb
      rw [hσl i, hσl (i + 1)] at hsum
      push_cast at hsum
      linarith
  · intro i _
    exact model_onRay_of hAB' ⟨σ (i + 1), hσlt 0 (i + 1) (by omega), rfl⟩
  · intro i _
    exact between_pt_of_strictBetween (Dim.mk A.1 B.1) hM
      (Or.inl ⟨hσlt i (i + 1) (by omega), hσlt (i + 1) (i + 2) (by omega)⟩)
  · left
    have hB1 : (Dim.mk A.1 B.1).pt 1 ∈ plane κ := by
      rw [hpt1]
      exact B.2
    have h1 : 1 < σ n := by
      apply hmono 1 (σ n) (hσ0 n) hB1 (hσm n)
      rw [hpt1, hσl]
      rwa [div_lt_iff₀ hδ] at hn
    have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM (Or.inl ⟨zero_lt_one, h1⟩)
    rw [hpt0, hpt1] at hb
    exact hb

/-- **Archimedes' axiom holds in the plane of a bound that is not positive.** Under a negative
bound the length is Klein's distance; under the bound 0 it is the square root of `apart`. -/
theorem model_archimedes (κ : ℝ) (hκ : κ ≤ 0) : (model κ hκ).Archimedes := by
  rcases hκ.lt_or_eq with h | rfl
  · have hk : 0 < √(-κ) := Real.sqrt_pos.mpr (neg_pos.mpr h)
    apply archimedes_of_length hκ (kleinDist κ)
    · intro P Q R S hP hQ hR hS
      exact apart_eq_iff_kleinDist_eq h hP hQ hR hS
    · intro A B C hA hC hABC
      exact (kleinDist_add_of_between h hA hC hABC).2
    · intro P Q hP hQ hPQ
      exact kleinDist_pos h hP hQ hPQ
    · intro P hP
      rw [kleinDist_eq_arsinh h hP hP, apart_self]
      simp
    · intro O D hO hOD d hd
      have hsinh : 0 < Real.sinh (√(-κ) * d) := Real.sinh_pos_iff.mpr (mul_pos hk hd)
      obtain ⟨t, ht, hX, hap⟩ := exists_onRay_apart h hO hOD
        (α := Real.sinh (√(-κ) * d) ^ 2 / (-κ)) (div_pos (by positivity) (neg_pos.mpr h))
      refine ⟨t, ht, hX, ?_⟩
      have e : -κ * (Real.sinh (√(-κ) * d) ^ 2 / (-κ)) = Real.sinh (√(-κ) * d) ^ 2 := by
        field_simp [h.ne]
      rw [kleinDist_eq_arsinh h hO hX, hap, e, Real.sqrt_sq hsinh.le, Real.arsinh_sinh]
      field_simp
  · apply archimedes_of_length hκ (fun P Q => √(apart 0 P Q))
    · intro P Q R S _ _ _ _
      exact (Real.sqrt_inj (apart_zero_nonneg _ _) (apart_zero_nonneg _ _)).symm
    · intro A B C _ _ hABC
      exact euclid_sqrt_apart_add hABC
    · intro P Q hP hQ hPQ
      exact Real.sqrt_pos.mpr (apart_pos hP hQ hPQ)
    · intro P _
      simp [apart_self]
    · intro O D _ hOD d hd
      have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
        have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
          intro e
          apply hOD
          have h1 := congrArg Prod.fst e
          have h2 := congrArg Prod.snd e
          simp only [] at h1 h2
          exact Prod.ext (by linarith) (by linarith)
        exact sq_add_sq_pos hne
      have hsV := Real.sqrt_pos.mpr hV
      refine ⟨d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2), div_pos hd hsV, mem_plane_zero _, ?_⟩
      have e : apart 0 O ((Dim.mk O D).pt (d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)))
          = (d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2
            * ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := by
        rw [apart_zero_bound]
        simp only [Dim.pt]
        ring
      change √(apart 0 O _) = d
      rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_pos hd hsV).le]
      field_simp

end Hilbert

end ParallelPostulate

/-!
# The independence of the parallel postulate

`euclidPlane`, the plane of the bound 0, and `kleinPlane`, the plane of the bound `-1`, are
Hilbert planes that meet the axioms of continuity. Playfair's axiom holds in the first and fails
in the second, so it is independent of Hilbert's axioms, with continuity or without it.

## Contents

* the two planes: `euclidPlane`, `kleinPlane`, `euclidPlane_playfair`, `kleinPlane_not_playfair`
* the independence: `playfair_independent`, `playfair_not_consequence`,
  `not_playfair_not_consequence`, `playfair_independent_continuous`
-/

namespace ParallelPostulate

namespace Hilbert

open Pairs HyperbolicPlane

/-- **Euclid's plane**: the plane of the bound 0. -/
noncomputable abbrev euclidPlane : HilbertPlane (Pt 0) (Ln 0) := model 0 le_rfl

/-- **Klein's plane**: the plane of the bound `-1`. -/
noncomputable abbrev kleinPlane : HilbertPlane (Pt (-1)) (Ln (-1)) :=
  model (-1) (by norm_num)

/-- **Playfair's axiom holds in Euclid's plane.** -/
theorem euclidPlane_playfair : euclidPlane.Playfair := by
  intro l A hA m m' hm hml hm' hm'l
  have key : ∀ n : Ln 0, euclidPlane.lies A n → euclidPlane.Parallel n l → n.1 ∩ l.1 = ∅ := by
    intro n _ hnl
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hxn, hxl⟩
    exact hnl ⟨⟨x, n.2.subset_plane hxn⟩, hxn, hxl⟩
  obtain ⟨M, -, huniq⟩ := euclid_one_parallel le_rfl l.2 hA
  have e1 := huniq m.1 ⟨m.2, hm, key m hm hml⟩
  have e2 := huniq m'.1 ⟨m'.2, hm', key m' hm' hm'l⟩
  exact Subtype.ext (e1.trans e2.symm)

/-- **Playfair's axiom fails in Klein's plane.** -/
theorem kleinPlane_not_playfair : ¬ kleinPlane.Playfair := by
  intro h
  obtain ⟨S, P, hS, hP, hPS⟩ := plane_exists_line_and_point (-1 : ℝ)
  obtain ⟨M₁, M₂, hne, ⟨h₁, hP₁, e₁⟩, ⟨h₂, hP₂, e₂⟩⟩ :=
    hyperbolic_two_parallels (by norm_num : (-1 : ℝ) < 0) hS hP hPS
  have par : ∀ {M : Set (ℝ × ℝ)} (hM : IsLine (plane (-1)) M), M ∩ S = ∅ →
      kleinPlane.Parallel ⟨M, hM⟩ ⟨S, hS⟩ := by
    intro M hM hMS ⟨A, hAM, hAS⟩
    have hA : A.1 ∈ M ∩ S := ⟨hAM, hAS⟩
    rw [hMS] at hA
    exact hA
  have := h ⟨S, hS⟩ ⟨P, hP⟩ hPS ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ hP₁ (par h₁ e₁) hP₂ (par h₂ e₂)
  exact hne (congrArg Subtype.val this)

/-- **The parallel postulate is independent of the axioms of a Hilbert plane.** There is a
Hilbert plane in which Playfair's axiom holds, and one in which it fails. -/
theorem playfair_independent :
    (∃ (P L : Type) (H : HilbertPlane P L), H.Playfair) ∧
      ∃ (P L : Type) (H : HilbertPlane P L), ¬ H.Playfair :=
  ⟨⟨_, _, euclidPlane, euclidPlane_playfair⟩, ⟨_, _, kleinPlane, kleinPlane_not_playfair⟩⟩

/-- Playfair's axiom does not follow from the axioms of a Hilbert plane. -/
theorem playfair_not_consequence : ¬ ∀ (P L : Type) (H : HilbertPlane P L), H.Playfair :=
  fun h => kleinPlane_not_playfair (h _ _ kleinPlane)

/-- Nor does its negation. -/
theorem not_playfair_not_consequence : ¬ ∀ (P L : Type) (H : HilbertPlane P L), ¬ H.Playfair :=
  fun h => h _ _ euclidPlane euclidPlane_playfair

/-! ## The independence, with continuity -/

/-- **The parallel postulate is independent of Hilbert's axioms, with continuity.** Both planes
meet Archimedes' axiom and Dedekind's axiom; Playfair's axiom holds in the one and fails in
the other. -/
theorem playfair_independent_continuous :
    (∃ (P L : Type) (H : HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ H.Playfair) ∧
      ∃ (P L : Type) (H : HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ ¬ H.Playfair :=
  ⟨⟨_, _, euclidPlane, model_archimedes 0 le_rfl, model_dedekind 0 le_rfl, euclidPlane_playfair⟩,
    ⟨_, _, kleinPlane, model_archimedes (-1) (by norm_num), model_dedekind (-1) (by norm_num),
      kleinPlane_not_playfair⟩⟩

end Hilbert

end ParallelPostulate

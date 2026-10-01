/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
module
public import Mathlib.Data.Set.Basic

/-!
# The axioms of a Hilbert plane

`HilbertPlane P L` is a plane with points `P` and lines `L`, a betweenness, and congruence of
segments and of angles, that meets Hilbert's axioms of incidence (I1 to I3), of order (B1 to
B4, with Pasch's axiom as B4) and of congruence (C1 to C6). Playfair's axiom,
`HilbertPlane.Playfair`, is not among them. The axioms of continuity are
`HilbertPlane.Archimedes` and `HilbertPlane.Dedekind`.

Apart from Mathlib, this file is all that the statement of the main theorem,
`Hilbert.playfair_independent_continuous`, depends on.

## Contents

* the axioms: `HilbertPlane`, `Collinear`, `OnRay`, `SameSide`
* Playfair's axiom: `HilbertPlane.Parallel`, `HilbertPlane.Playfair`
* the axioms of continuity: `HilbertPlane.Archimedes`, `HilbertPlane.Dedekind`
-/

public section

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

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.BandUnmodifiedCoreCertificate
public import LeanPool.ApollonianSuperharmonic.FootprintDeletionRetention
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance

-- [TABLET NODE: BandModifiedPeriodicComplex]

/-!
# BandModifiedPeriodicComplex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ModifiedPeriodicComplexProof

private theorem tile_ext :
    ∀ (A : ProtoTile), ∀ (B : ProtoTile), (A.cells = B.cells) → ((A.anchor = B.anchor) → (A = B))
        := by
  classical
  intro A B hc ha
  cases A; cases B; cases hc; cases ha; rfl

private theorem trans_comp :
    (∀ (A : ProtoTile), ∀ (B : ProtoTile), (A.cells = B.cells) → ((A.anchor = B.anchor) → (A =
        B))) → (∀ (A : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
        (TileTranslation A x) y = TileTranslation A (x + y)) := by
  classical
  intro tile_ext A x y
  apply tile_ext
  · change (A.cells.image (GaussianTranslation x)).image (GaussianTranslation y) =
      A.cells.image (GaussianTranslation (x + y))
    rw [Finset.image_image]
    congr 1
    funext z
    exact add_assoc z x y
  · exact add_assoc A.anchor x y

private theorem trans_zero :
    (∀ (A : ProtoTile), ∀ (B : ProtoTile), (A.cells = B.cells) → ((A.anchor = B.anchor) → (A =
        B))) → (∀ (A : ProtoTile), TileTranslation A 0 = A) := by
  classical
  intro tile_ext A
  apply tile_ext
  · change A.cells.image (GaussianTranslation 0) = A.cells
    have hz : GaussianTranslation 0 = id := by funext z; exact add_zero z
    rw [hz, Finset.image_id]
  · exact add_zero A.anchor

private theorem face_row :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L), ∀ (w :
        K.core.lattice), ∀ (f : PeriodicSubtileFaceIndex), ∀ (i : Fin 3), K.core.shift w
        (SixSubtileFaceVertices f i) =
        SixSubtileFaceVertices
          ⟨f.label, f.first + (K.latticeCoordinates w).1, f.second + (K.latticeCoordinates w).2⟩
              i := by
  classical
  intro P u v L K w f i
  have h := K.core.face_vertices_periodic w (K.faceEquiv.symm f) i
  rw [K.face_vertices, K.face_vertices, K.face_shift] at h
  simpa using h.symm

private theorem shift_eq :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L), (∀ (w :
        K.core.lattice), ∀ (f : PeriodicSubtileFaceIndex), ∀ (i : Fin 3), K.core.shift w
        (SixSubtileFaceVertices f i) = SixSubtileFaceVertices ⟨f.label, f.first +
        (K.latticeCoordinates w).1, f.second + (K.latticeCoordinates w).2⟩ i) → (∀ (w :
        K.core.lattice), ∀ (a : PeriodicSubtileIndex), K.core.shift w a =
        ⟨a.label, a.first + (K.latticeCoordinates w).1, a.second + (K.latticeCoordinates w).2⟩)
            := by
  classical
  intro P u v L K face_row w a
  rcases a with ⟨l, m, n⟩
  cases l with
  | A => exact face_row w ⟨.I1, m, n⟩ 0
  | B => exact face_row w ⟨.I1, m, n⟩ 1
  | C => exact face_row w ⟨.I1, m, n⟩ 2
  | D => exact face_row w ⟨.I2, m, n⟩ 2
  | E => exact face_row w ⟨.I4, m, n⟩ 2
  | F => exact face_row w ⟨.I3, m, n⟩ 2

private theorem t_shift :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    ∀ (w : K.core.lattice), ∀ (m : Int), ∀ (n : Int), t (m + (K.latticeCoordinates w).1) (n +
        (K.latticeCoordinates w).2) =
        t m n + (w : GaussianInt) := by
  classical
  intro P u v L K t w m n
  dsimp [t]
  rw [Int.cast_add, Int.cast_add, add_mul, add_mul,
    ← K.latticeCoordinates_spec w]
  abel

private theorem tile_periodic :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (L : AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v
        L),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    (∀ (A : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
        (TileTranslation A x) y = TileTranslation A (x + y)) → ((∀ (w : K.core.lattice), ∀ (a :
        PeriodicSubtileIndex), K.core.shift w a = ⟨a.label, a.first +
        (K.latticeCoordinates w).1, a.second + (K.latticeCoordinates w).2⟩) → ((∀ (w :
        K.core.lattice), ∀ (m : Int), ∀ (n : Int), t (m + (K.latticeCoordinates w).1) (n +
        (K.latticeCoordinates w).2) = t m n + (w : GaussianInt)) → (∀ (w : K.core.lattice), ∀ (a
        : PeriodicSubtileIndex), T (K.core.shift w a) = TileTranslation (T a) w))) := by
  classical
  intro P O u v L K T t trans_comp shift_eq t_shift w a
  rw [shift_eq]
  rcases a with ⟨l, m, n⟩
  cases l <;> change TileTranslation _ (t (m + _) (n + _)) =
    TileTranslation (TileTranslation _ (t m n)) w <;>
    rw [trans_comp, t_shift]

private theorem unchanged :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let S := SubtileOccurrenceInterpretation P u v
    ∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (T a = S a) := by
  classical
  intro P O u v T S a ha
  rcases a with ⟨l, m, n⟩
  cases l <;> simp_all [T, S, ModifiedSubtileOccurrenceInterpretation,
    SubtileOccurrenceInterpretation]

private theorem modified_a :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let S := SubtileOccurrenceInterpretation P u v
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    ∀ (m : Int), ∀ (n : Int), T ⟨.A, m, n⟩ =
      TileCellComplement (S ⟨.A, m, n⟩) (TileTranslation O (t m n)) := by
  classical
  intro P O u v T S t m n
  exact (TileCellComplementCovariance (P 0 true) O (t m n)).1

private theorem cells_nonempty :
    ∀ (A : ProtoTile), (LatticeTile A) → (A.cells.Nonempty) := by
  classical
  intro A hA
  rcases hA with ⟨e⟩
  have hp := (e ⟨0, by simp⟩).property
  simp only [TileRealization, Set.mem_iUnion] at hp
  obtain ⟨x, hx, _⟩ := hp
  exact ⟨x, hx⟩

private theorem original_nonempty :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), (BandUnmodifiedCoreCertificate P u v L) → (
    let S := SubtileOccurrenceInterpretation P u v
    (∀ (A : ProtoTile), (LatticeTile A) → (A.cells.Nonempty)) → (∀ (a : PeriodicSubtileIndex), (S
        a).cells.Nonempty)) := by
  classical
  intro P u v L K S cells_nonempty a
  change (SubtileOccurrenceInterpretation P u v a).cells.Nonempty
  rw [← K.tile_eq]
  exact cells_nonempty _ (K.core.tiles_are_disks a)

private theorem modified_nonempty :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), (forall o : PeriodicSubtileIndex, LatticeTile
        (ModifiedSubtileOccurrenceInterpretation P O u v o)) → (
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    (∀ (A : ProtoTile), (LatticeTile A) → (A.cells.Nonempty)) → (∀ (a : PeriodicSubtileIndex), (T
        a).cells.Nonempty)) := by
  classical
  intro P O u v hdisks T cells_nonempty a
  exact cells_nonempty _ (hdisks a)

private theorem separation :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), (∀ x : LatticeCell, ∃! o : PeriodicSubtileIndex, x ∈
        (ModifiedSubtileOccurrenceInterpretation P O u v o).cells) → ((O.cells ⊆ (P 0
        true).cells) → ((O.cells ⊆ (P 0 false).cells) → (∀ (a : PeriodicSubtileIndex), ∀ (b :
        PeriodicSubtileIndex), a ≠ b →
    ¬((a.label = SixSubtileLabel.A ∧ b.label = SixSubtileLabel.B ∨
            a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
          a.first = b.first ∧ a.second = b.second) →
      Disjoint (SubtileOccurrenceInterpretation P u v a).cells (SubtileOccurrenceInterpretation P
          u v b).cells))) := by
  classical
  intro P O u v hpartition hOA hOB
  exact (BandOriginalPairSeparation P O u v hOA hOB hpartition).2

private theorem retention :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), (O.cells ⊆ (P 0 true).cells) → ((∀ m n : Int, ∀ x ∈ FootprintVertices
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ a : GaussianInt, x
        ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) -> a ∈ (SubtileOccurrenceInterpretation P u v
        ⟨.A, m, n⟩).cells ∨ a ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let S := SubtileOccurrenceInterpretation P u v
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    (∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (T a = S a)) → ((∀ (m : Int), ∀ (n : Int), T
        ⟨.A, m, n⟩ = TileCellComplement (S ⟨.A, m, n⟩) (TileTranslation O (t m n))) → ((∀ (a :
        PeriodicSubtileIndex), (S a).cells.Nonempty) → ((∀ (a : PeriodicSubtileIndex), (T
        a).cells.Nonempty) → ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b
        → ¬((a.label = SixSubtileLabel.A ∧ b.label = SixSubtileLabel.B ∨ a.label =
        SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧ a.first = b.first ∧ a.second =
        b.second) → Disjoint (SubtileOccurrenceInterpretation P u v a).cells
        (SubtileOccurrenceInterpretation P u v b).cells) → (∀ (m : Int), ∀ (n : Int), ∀ (b :
        PeriodicSubtileIndex), (b.label ≠ .A) → ((b ≠ ⟨.B, m, n⟩) → (FootprintEdges (T ⟨.A, m,
        n⟩) ∩ FootprintEdges (T b) =
          FootprintEdges (S ⟨.A, m, n⟩) ∩ FootprintEdges (S b) ∧
      FootprintVertices (T ⟨.A, m, n⟩) ∩ FootprintVertices (T b) =
          FootprintVertices (S ⟨.A, m, n⟩) ∩ FootprintVertices (S b)))))))))) := by
  classical
  intro P O u v hOA hisolated T S t unchanged modified_a original_nonempty modified_nonempty
      separation m n b hbA hb
  have hsepA : Disjoint (S b).cells (S ⟨.A, m, n⟩).cells := by
    apply separation
    · intro h; exact hbA (congrArg PeriodicSubtileIndex.label h)
    · rcases b with ⟨l, r, s⟩
      simp only [
        ] at *
      intro h
      rcases h with ⟨h, hr, hs⟩
      rcases h with h | h
      · cases h.2
      · exact hb (by cases h.1; cases hr; cases hs; rfl)
  have hsepB : Disjoint (S b).cells (S ⟨.B, m, n⟩).cells := by
    apply separation b _ hb
    simp [hbA]
  have hO : (TileTranslation O (t m n)).cells ⊆ (S ⟨.A, m, n⟩).cells := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr ⟨z, hOA hz, rfl⟩
  have hi : ∀ x ∈ CellSupportedFootprintVertices (TileTranslation O (t m n)),
      ∀ a : GaussianInt, x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) →
        a ∈ (S ⟨.A, m, n⟩).cells ∨ a ∈ (S ⟨.B, m, n⟩).cells := by
    intro x hx a ha
    apply hisolated m n x _ a ha
    rcases hx with ⟨z, hz, hzx⟩
    have hn : (TileTranslation O (t m n)).cells.Nonempty := ⟨z, hz⟩
    change x ∈ FootprintVertices (TileTranslation O (t m n))
    simpa [FootprintVertices, hn, CellSupportedFootprintVertices] using
      (show x ∈ CellSupportedFootprintVertices (TileTranslation O (t m n)) from
        ⟨z, hz, hzx⟩)
  have hr := FootprintDeletionRetention (S ⟨.A, m, n⟩)
    (S ⟨.B, m, n⟩) (TileTranslation O (t m n)) (S b) hO hi hsepA hsepB
  rw [modified_a, unchanged b hbA]
  exact ⟨hr.2.1, hr.2.2 (Or.inr
    ⟨by rw [← modified_a]; exact modified_nonempty _, original_nonempty b⟩)⟩

private theorem no_AA :
    ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b) →
        (¬ (a.label = .A ∧ b.label = .A)) := by
  classical
  intro a b h
  induction h <;> try (simp; done)
  rename_i a' b' h ih
  exact fun hh => ih ⟨hh.2, hh.1⟩

private theorem ordinary_retention :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let S := SubtileOccurrenceInterpretation P u v
    (∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (T a = S a)) → ((∀ (m : Int), ∀ (n : Int), ∀
        (b : PeriodicSubtileIndex), (b.label ≠ .A) → ((b ≠ ⟨.B, m, n⟩) → (FootprintEdges (T ⟨.A,
        m, n⟩) ∩ FootprintEdges (T b) = FootprintEdges (S ⟨.A, m, n⟩) ∩ FootprintEdges (S b) ∧
        FootprintVertices (T ⟨.A, m, n⟩) ∩ FootprintVertices (T b) = FootprintVertices (S ⟨.A, m,
        n⟩) ∩ FootprintVertices (S b)))) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
        PeriodicSubtileIndex), (AllowedSubtileIncidence a b) → (¬ (a.label = .A ∧ b.label = .A)))
        → (
    let exceptional : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop := fun a b =>
      ((a.label = .A ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧
        a.first = b.first ∧ a.second = b.second)
    ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b) →
        ((¬ exceptional a b) → (FootprintEdges (T a) ∩ FootprintEdges (T b) =
          FootprintEdges (S a) ∩ FootprintEdges (S b) ∧
      FootprintVertices (T a) ∩ FootprintVertices (T b) =
          FootprintVertices (S a) ∩ FootprintVertices (S b)))))) := by
  classical
  intro P O u v T S unchanged retention no_AA exceptional a b h he
  by_cases ha : a.label = .A
  · have hb : b.label ≠ .A := fun hb => no_AA a b h ⟨ha, hb⟩
    rcases a with ⟨l, m, n⟩
    cases ha
    apply retention m n b hb
    intro hB
    subst b
    exact he (by simp [exceptional])
  · by_cases hb : b.label = .A
    · rcases b with ⟨l, m, n⟩
      cases hb
      have hr := retention m n a ha (by
        intro hA
        subst a
        exact he (by simp [exceptional]))
      simpa only [Set.inter_comm] using hr
    · rw [unchanged a ha, unchanged b hb]
      exact ⟨rfl, rfl⟩

private theorem rho_common :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (L : AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v
        L),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let S := SubtileOccurrenceInterpretation P u v
    (∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (T a = S a)) → ((∀ (m : Int), ∀ (n : Int), ∀
        (b : PeriodicSubtileIndex), (b.label ≠ .A) → ((b ≠ ⟨.B, m, n⟩) → (FootprintEdges (T ⟨.A,
        m, n⟩) ∩ FootprintEdges (T b) = FootprintEdges (S ⟨.A, m, n⟩) ∩ FootprintEdges (S b) ∧
        FootprintVertices (T ⟨.A, m, n⟩) ∩ FootprintVertices (T b) = FootprintVertices (S ⟨.A, m,
        n⟩) ∩ FootprintVertices (S b)))) → (∀ (f : K.core.plane.Face), ∀ (i : Fin 3), K.core.rho
        f ∈ FootprintVertices (T (K.core.plane.faceVertex f i)))) := by
  classical
  intro P O u v L K T S unchanged retention f i
  have old (j : Fin 3) :
      K.core.rho f ∈ FootprintVertices (S (K.core.plane.faceVertex f j)) := by
    change K.core.rho f ∈ FootprintVertices
      (SubtileOccurrenceInterpretation P u v (K.core.plane.faceVertex f j))
    rw [← K.tile_eq]
    exact K.core.rho_common f j
  by_cases ha : (K.core.plane.faceVertex f i).label = .A
  · let b := K.core.plane.faceVertex f 2
    have hbA : b.label ≠ .A := by
      dsimp [b]
      rw [K.face_vertices]
      cases h : (K.faceEquiv f).label <;> simp [SixSubtileFaceVertices, h]
    have hbB : b.label ≠ .B := by
      dsimp [b]
      rw [K.face_vertices]
      cases h : (K.faceEquiv f).label <;> simp [SixSubtileFaceVertices, h]
    generalize hidx : K.core.plane.faceVertex f i = a at ha ⊢
    rcases a with ⟨l, m, n⟩
    cases ha
    have hr := (retention m n b hbA (by
      intro h; exact hbB (congrArg PeriodicSubtileIndex.label h))).2
    have hx : K.core.rho f ∈ FootprintVertices (S ⟨.A, m, n⟩) ∩
        FootprintVertices (S b) := ⟨hidx ▸ old i, old 2⟩
    rw [← hr] at hx
    exact hx.1
  · rw [unchanged _ ha]
    exact old i

private theorem walk_reverse :
    let Walk := fun (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt) =>
      q.head? = some r ∧ q.getLast? = some s ∧
      (∀ x ∈ q, x ∈ FootprintVertices A ∩ FootprintVertices B) ∧
      ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        q = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B
    ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (r : GaussianInt), ∀ (s : GaussianInt), ∀ (q : List
        GaussianInt), (Walk A B r s q) → (Walk A B s r q.reverse) := by
  classical
  intro Walk A B r s q hq
  refine ⟨by simpa using hq.2.1, by simpa using hq.1, ?_, ?_⟩
  · intro x hx
    exact hq.2.2.1 x (List.mem_reverse.mp hx)
  · intro x y l1 l2 he
    have hr := congrArg List.reverse he
    have hp : q = l2.reverse ++ y :: x :: l1.reverse := by
      simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using hr
    simpa [Finset.pair_comm] using hq.2.2.2 y x _ _ hp

private theorem walk_swap :
    let Walk := fun (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt) =>
      q.head? = some r ∧ q.getLast? = some s ∧
      (∀ x ∈ q, x ∈ FootprintVertices A ∩ FootprintVertices B) ∧
      ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        q = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B
    ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (r : GaussianInt), ∀ (s : GaussianInt), ∀ (q : List
        GaussianInt), (Walk A B r s q) → (Walk B A r s q) := by
  classical
  intro Walk A B r s q hq
  refine ⟨hq.1, hq.2.1, ?_, ?_⟩
  · intro x hx
    exact ⟨(hq.2.2.1 x hx).2, (hq.2.2.1 x hx).1⟩
  · intro x y l1 l2 he
    exact ⟨(hq.2.2.2 x y l1 l2 he).2, (hq.2.2.2 x y l1 l2 he).1⟩

private theorem walk_map :
    let Walk := fun (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt) =>
      q.head? = some r ∧ q.getLast? = some s ∧
      (∀ x ∈ q, x ∈ FootprintVertices A ∩ FootprintVertices B) ∧
      ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        q = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B
    ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (r : GaussianInt), ∀ (s : GaussianInt), ∀ (w :
        GaussianInt), ∀ (q : List GaussianInt), (Walk A B r s q) → (Walk (TileTranslation A w)
        (TileTranslation B w) (r + w) (s + w)
        (q.map (fun x => x + w))) := by
  classical
  intro Walk A B r s w q hq
  have hv (C : ProtoTile) : FootprintVertices (TileTranslation C w) =
      GaussianTranslation w '' FootprintVertices C :=
    (TileTranslationFormulas C w).2.2.2.2.2.1
  have he (C : ProtoTile) : FootprintEdges (TileTranslation C w) =
      (fun e : Finset GaussianInt => e.image (GaussianTranslation w)) ''
        FootprintEdges C := (TileTranslationFormulas C w).2.2.2.2.2.2.1
  refine ⟨by simp [hq.1], by simp [hq.2.1], ?_, ?_⟩
  · intro x hx
    rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
    rcases hq.2.2.1 z hz with ⟨ha, hb⟩
    rw [hv, hv]
    exact ⟨⟨z, ha, rfl⟩, ⟨z, hb, rfl⟩⟩
  · intro x y l1 l2 hxy
    have hinv := congrArg (List.map (fun z : GaussianInt => z - w)) hxy
    have hp : q = l1.map (fun z => z - w) ++
        (x - w) :: (y - w) :: l2.map (fun z => z - w) := by
      simpa [List.map_map, Function.comp_def] using hinv
    rcases hq.2.2.2 (x - w) (y - w) _ _ hp with ⟨ha, hb⟩
    have image_pair : ({x - w, y - w} : Finset GaussianInt).image
        (GaussianTranslation w) = {x, y} := by
      simp [GaussianTranslation]
    rw [he, he]
    exact ⟨⟨_, ha, image_pair⟩, ⟨_, hb, image_pair⟩⟩

private theorem rho_index :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    ∀ (f : PeriodicSubtileFaceIndex), K.core.rho (K.faceEquiv.symm f) =
        K.core.rho (K.faceEquiv.symm ⟨f.label, 0, 0⟩) + t f.first f.second := by
  classical
  intro P u v L K t f
  rcases K.core.face_orbit_representatives (K.faceEquiv.symm f) with
    ⟨r, hr, w, hf⟩
  rcases (K.face_reps r).mp hr with ⟨hr1, hr2⟩
  have hi := congrArg K.faceEquiv hf
  rw [K.face_shift] at hi
  simp only [Equiv.apply_symm_apply] at hi
  have hl := congrArg PeriodicSubtileFaceIndex.label hi
  have hm := congrArg PeriodicSubtileFaceIndex.first hi
  have hn := congrArg PeriodicSubtileFaceIndex.second hi
  simp only [hr1, zero_add] at hm
  simp only [hr2, zero_add] at hn
  have hre : K.faceEquiv r = ⟨f.label, 0, 0⟩ := by
    rcases hfr : K.faceEquiv r with ⟨l, m, n⟩
    simp only [hfr,
      ] at hl hr1 hr2 ⊢
    rw [← hl, hr1, hr2]
  have hw : (w : GaussianInt) = t f.first f.second := by
    change (w : GaussianInt) = (f.first : GaussianInt) * u +
      (f.second : GaussianInt) * v
    rw [hm, hn]
    exact (K.latticeCoordinates_spec w).symm
  rw [hf, K.core.rho_periodic, hw]
  congr 1
  exact congrArg K.core.rho ((K.faceEquiv.eq_symm_apply).mpr hre)

private theorem pm_spec :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (L : AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v
        L),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    let Walk := fun (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt) =>
      q.head? = some r ∧ q.getLast? = some s ∧
      (∀ x ∈ q, x ∈ FootprintVertices A ∩ FootprintVertices B) ∧
      ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        q = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B
    (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (r : GaussianInt), ∀ (s : GaussianInt), ∀ (w :
        GaussianInt), ∀ (q : List GaussianInt), (Walk A B r s q) → (Walk (TileTranslation A w)
        (TileTranslation B w) (r + w) (s + w) (q.map (fun x => x + w)))) → ((∀ (f :
        PeriodicSubtileFaceIndex), K.core.rho (K.faceEquiv.symm f) = K.core.rho (K.faceEquiv.symm
        ⟨f.label, 0, 0⟩) + t f.first f.second) → (∀ (p : List GaussianInt), (p.head? = some
        (K.core.rho ((K.faceEquiv.symm : PeriodicSubtileFaceIndex → K.core.plane.Face)
        ⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩)) ∧ p.getLast? = some (K.core.rho
        ((K.faceEquiv.symm : PeriodicSubtileFaceIndex → K.core.plane.Face)
        ⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩)) ∧ (∀ x ∈ p, x ∈ FootprintVertices
        (TileCellComplement (P (0 : Fin (3 : ℕ)) true) O) ∩ FootprintVertices (P (0 : Fin (3 :
        ℕ)) false)) ∧ ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (l1 : List GaussianInt), ∀ (l2
        : List GaussianInt), p = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges (TileCellComplement
        (P (0 : Fin (3 : ℕ)) true) O) ∩ FootprintEdges (P (0 : Fin (3 : ℕ)) false)) → (
    let pm : Int → Int → List GaussianInt := fun m n => p.map (fun x => x + t m n)
    ∀ (m : Int), ∀ (n : Int), Walk (T ⟨.A, m, n⟩) (T ⟨.B, m, n⟩)
      (K.core.rho (K.faceEquiv.symm ⟨.I1, m, n⟩))
      (K.core.rho (K.faceEquiv.symm ⟨.I2, m, n⟩)) (pm m n)))) := by
  classical
  intro P O u v L K T t Walk walk_map rho_index p hp pm m n
  rw [rho_index ⟨.I1, m, n⟩, rho_index ⟨.I2, m, n⟩]
  exact walk_map _ _ _ _ (t m n) p hp

private theorem E_asymm :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    ∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), (E f g) → (¬ E g f) := by
  classical
  intro P u v L K E f g h h'
  have hc : SixSubtileFaceLabel.I1 = .I2 := h.1.symm.trans h'.2.1
  cases hc

private theorem E_shift :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    ∀ (w : K.core.lattice), ∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), E
        (K.core.faceShift w f) (K.core.faceShift w g) ↔ E f g := by
  classical
  intro P u v L K E w f g
  simp [E, K.face_shift]

private theorem path_reverse :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    ∀ (p : List GaussianInt),
    let pm : Int → Int → List GaussianInt := fun m n => p.map (fun x => x + t m n)
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    let path : K.core.plane.Face → K.core.plane.Face → List GaussianInt := fun f g =>
      if E f g then pm (K.faceEquiv f).first (K.faceEquiv f).second
      else if E g f then (pm (K.faceEquiv g).first (K.faceEquiv g).second).reverse
      else K.core.facePath f g
    (∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), (E f g) → (¬ E g f)) → (∀ (f :
        K.core.plane.Face), ∀ (g : K.core.plane.Face), path g f = (path f g).reverse) := by
  classical
  intro P u v L K t p pm E path E_asymm f g
  by_cases h : E f g
  · simp [path, h, E_asymm f g h]
  · by_cases h' : E g f
    · simp [path, h, h']
    · simpa [path, h, h'] using K.core.facePath_reverse f g

private theorem pm_shift :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    (∀ (w : K.core.lattice), ∀ (m : Int), ∀ (n : Int), t (m + (K.latticeCoordinates w).1) (n +
        (K.latticeCoordinates w).2) = t m n + (w : GaussianInt)) → (∀ (p : List GaussianInt),
    let pm : Int → Int → List GaussianInt := fun m n => p.map (fun x => x + t m n)
    ∀ (w : K.core.lattice), ∀ (m : Int), ∀ (n : Int), pm (m + (K.latticeCoordinates w).1) (n +
        (K.latticeCoordinates w).2) =
        (pm m n).map (fun x => x + (w : GaussianInt))) := by
  classical
  intro P u v L K t t_shift p pm w m n
  simp [pm, t_shift, List.map_map, Function.comp_def, add_assoc]

private theorem path_periodic :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    ∀ (p : List GaussianInt),
    let pm : Int → Int → List GaussianInt := fun m n => p.map (fun x => x + t m n)
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    let path : K.core.plane.Face → K.core.plane.Face → List GaussianInt := fun f g =>
      if E f g then pm (K.faceEquiv f).first (K.faceEquiv f).second
      else if E g f then (pm (K.faceEquiv g).first (K.faceEquiv g).second).reverse
      else K.core.facePath f g
    (∀ (w : K.core.lattice), ∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), E
        (K.core.faceShift w f) (K.core.faceShift w g) ↔ E f g) → ((∀ (w : K.core.lattice), ∀ (m :
        Int), ∀ (n : Int), pm (m + (K.latticeCoordinates w).1) (n + (K.latticeCoordinates w).2) =
        (pm m n).map (fun x => x + (w : GaussianInt))) → (∀ (w : K.core.lattice), ∀ (f :
        K.core.plane.Face), ∀ (g : K.core.plane.Face), path (K.core.faceShift w f)
        (K.core.faceShift w g) =
        (path f g).map (fun x => x + (w : GaussianInt)))) := by
  classical
  intro P u v L K t p pm E path E_shift pm_shift w f g
  by_cases h : E f g
  · simp only [path, ite_eq_left h, ite_eq_left ((E_shift w f g).mpr h)]
    simp only [K.face_shift,
      ]
    exact pm_shift w _ _
  · by_cases h' : E g f
    · simp only [path, ite_eq_right h, ite_eq_right (mt (E_shift w f g).mp h),
        ite_eq_left h', ite_eq_left ((E_shift w g f).mpr h')]
      simp only [K.face_shift,
        pm_shift, List.map_reverse]
    · simp only [path, ite_eq_right h, ite_eq_right h', ite_eq_right (mt (E_shift w f g).mp h),
        ite_eq_right (mt (E_shift w g f).mp h')]
      exact K.core.facePath_periodic w f g

private theorem E_indices :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    ∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), (E f g) → (K.faceEquiv f = ⟨.I1,
        (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧
      K.faceEquiv g = ⟨.I2, (K.faceEquiv f).first, (K.faceEquiv f).second⟩) := by
  classical
  intro P u v L K E f g h
  rcases h with ⟨hlf, hlg, hm, hn⟩
  constructor
  · rcases hf : K.faceEquiv f with ⟨lf, m, n⟩
    simp only [hf,
      ] at hlf ⊢
    rw [hlf]
  · rcases hg : K.faceEquiv g with ⟨lg, r, s⟩
    simp only [hg,
      ] at hlg hm hn ⊢
    rw [hlg, ← hm, ← hn]

private theorem common_I :
    ∀ (m : Int), ∀ (n : Int), ∀ (a : PeriodicSubtileIndex), (∃ i, SixSubtileFaceVertices ⟨.I1, m,
        n⟩ i = a) → ((∃ i, SixSubtileFaceVertices ⟨.I2, m, n⟩ i = a) → (a = ⟨.A, m, n⟩ ∨ a = ⟨.B,
        m, n⟩)) := by
  classical
  intro m n a h1 h2
  rcases h1 with ⟨i, hi⟩
  fin_cases i
  · exact Or.inl hi.symm
  · exact Or.inr hi.symm
  · have ha : a = ⟨.C, m, n⟩ := hi.symm
    subst a
    rcases h2 with ⟨j, hj⟩
    fin_cases j <;> simp [SixSubtileFaceVertices] at hj

private theorem E_pair :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    (∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), (E f g) → (K.faceEquiv f = ⟨.I1,
        (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧ K.faceEquiv g = ⟨.I2, (K.faceEquiv
        f).first, (K.faceEquiv f).second⟩)) → ((∀ (m : Int), ∀ (n : Int), ∀ (a :
        PeriodicSubtileIndex), (∃ i, SixSubtileFaceVertices ⟨.I1, m, n⟩ i = a) → ((∃ i,
        SixSubtileFaceVertices ⟨.I2, m, n⟩ i = a) → (a = ⟨.A, m, n⟩ ∨ a = ⟨.B, m, n⟩))) → (∀ (a :
        PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (f : K.core.plane.Face), ∀ (g :
        K.core.plane.Face), (K.core.plane.adjacent a b) → ((E f g) → ((∃ i,
        K.core.plane.faceVertex f i = a) → ((∃ i, K.core.plane.faceVertex f i = b) → ((∃ i,
        K.core.plane.faceVertex g i = a) → ((∃ i, K.core.plane.faceVertex g i = b) → ((a = ⟨.A,
        (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧
       b = ⟨.B, (K.faceEquiv f).first, (K.faceEquiv f).second⟩) ∨
      (a = ⟨.B, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧
       b = ⟨.A, (K.faceEquiv f).first, (K.faceEquiv f).second⟩))))))))) := by
  classical
  intro P u v L K E E_indices common_I a b f g hab hE hfa hfb hga hgb
  rcases E_indices f g hE with ⟨hf, hg⟩
  rcases hfa with ⟨ia, hia⟩
  rcases hfb with ⟨ib, hib⟩
  rcases hga with ⟨ja, hja⟩
  rcases hgb with ⟨jb, hjb⟩
  rw [K.face_vertices, hf] at hia hib
  rw [K.face_vertices, hg] at hja hjb
  have ha := common_I _ _ a ⟨ia, hia⟩ ⟨ja, hja⟩
  have hb := common_I _ _ b ⟨ib, hib⟩ ⟨jb, hjb⟩
  have hne : a ≠ b := by
    intro he
    apply K.core.plane.adjacent_irreflexive a
    simpa only [← he] using hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hne (ha.trans hb.symm))
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact False.elim (hne (ha.trans hb.symm))

private theorem E_walk :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (L : AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v
        L),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    let Walk := fun (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt) =>
      q.head? = some r ∧ q.getLast? = some s ∧
      (∀ x ∈ q, x ∈ FootprintVertices A ∩ FootprintVertices B) ∧
      ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        q = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B
    ∀ (p : List GaussianInt),
    let pm : Int → Int → List GaussianInt := fun m n => p.map (fun x => x + t m n)
    (∀ (m : Int), ∀ (n : Int), Walk (T ⟨.A, m, n⟩) (T ⟨.B, m, n⟩) (K.core.rho (K.faceEquiv.symm
        ⟨.I1, m, n⟩)) (K.core.rho (K.faceEquiv.symm ⟨.I2, m, n⟩)) (pm m n)) → (
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    let path : K.core.plane.Face → K.core.plane.Face → List GaussianInt := fun f g =>
      if E f g then pm (K.faceEquiv f).first (K.faceEquiv f).second
      else if E g f then (pm (K.faceEquiv g).first (K.faceEquiv g).second).reverse
      else K.core.facePath f g
    (∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), (E f g) → (K.faceEquiv f = ⟨.I1,
        (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧ K.faceEquiv g = ⟨.I2, (K.faceEquiv
        f).first, (K.faceEquiv f).second⟩)) → (∀ (f : K.core.plane.Face), ∀ (g :
        K.core.plane.Face), (E f g) → (Walk (T ⟨.A, (K.faceEquiv f).first, (K.faceEquiv f).second⟩)
        (T ⟨.B, (K.faceEquiv f).first, (K.faceEquiv f).second⟩)
        (K.core.rho f) (K.core.rho g) (path f g)))) := by
  classical
  intro P O u v L K T t Walk p pm pm_spec E path E_indices f g hE
  rcases E_indices f g hE with ⟨hf, hg⟩
  have ff : f = K.faceEquiv.symm
      ⟨.I1, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ :=
    (K.faceEquiv.eq_symm_apply).mpr hf
  have gg : g = K.faceEquiv.symm
      ⟨.I2, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ :=
    (K.faceEquiv.eq_symm_apply).mpr hg
  simp only [path, ite_eq_left hE]
  rw [ff, gg]
  simp only [Equiv.apply_symm_apply]
  exact pm_spec _ _

private theorem AB_faces :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L), ∀ (m : Int), ∀
        (n : Int), ∀ (f : K.core.plane.Face), (∃ i, K.core.plane.faceVertex f i = ⟨.A, m, n⟩) →
        ((∃ i, K.core.plane.faceVertex f i = ⟨.B, m, n⟩) → (K.faceEquiv f = ⟨.I1, m, n⟩ ∨
        K.faceEquiv f = ⟨.I2, m, n⟩)) := by
  classical
  intro P u v L K m n f ha hb
  let F := K.faceEquiv.symm (PeriodicSubtileFaceIndex.mk .I1 m n)
  let G := K.faceEquiv.symm (PeriodicSubtileFaceIndex.mk .I2 m n)
  have hF : (∃ i, K.core.plane.faceVertex F i = ⟨.A, m, n⟩) ∧
      (∃ i, K.core.plane.faceVertex F i = ⟨.B, m, n⟩) := by
    constructor
    · exact ⟨0, by simp [F, K.face_vertices, SixSubtileFaceVertices]⟩
    · exact ⟨1, by simp [F, K.face_vertices, SixSubtileFaceVertices]⟩
  have hG : (∃ i, K.core.plane.faceVertex G i = ⟨.A, m, n⟩) ∧
      (∃ i, K.core.plane.faceVertex G i = ⟨.B, m, n⟩) := by
    constructor
    · exact ⟨0, by simp [G, K.face_vertices, SixSubtileFaceVertices]⟩
    · exact ⟨1, by simp [G, K.face_vertices, SixSubtileFaceVertices]⟩
  have hFG : F ≠ G := by
    intro h
    have hh := congrArg K.faceEquiv h
    simp [F, G] at hh
  have hab := (K.adjacent_iff _ _).mpr (AllowedSubtileIncidence.AB m n)
  rcases K.core.plane.every_edge_two_faces _ _ hab with
    ⟨f0, g0, _, _, _, hall⟩
  have hFF := hall F hF
  have hGG := hall G hG
  have hff := hall f ⟨ha, hb⟩
  have hf : f = F ∨ f = G := by
    rcases hFF with hFF | hFF <;> rcases hGG with hGG | hGG
    · exact False.elim (hFG (hFF.trans hGG.symm))
    · rcases hff with hff | hff
      · exact Or.inl (hff.trans hFF.symm)
      · exact Or.inr (hff.trans hGG.symm)
    · rcases hff with hff | hff
      · exact Or.inr (hff.trans hGG.symm)
      · exact Or.inl (hff.trans hFF.symm)
    · exact False.elim (hFG (hFF.trans hGG.symm))
  rcases hf with rfl | rfl
  · exact Or.inl (K.faceEquiv.apply_symm_apply _)
  · exact Or.inr (K.faceEquiv.apply_symm_apply _)

private theorem path_spec :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (L : AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v
        L),
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let S := SubtileOccurrenceInterpretation P u v
    let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
    let exceptional : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop := fun a b =>
      ((a.label = .A ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧
        a.first = b.first ∧ a.second = b.second)
    (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b) →
        ((¬ exceptional a b) → (FootprintEdges (T a) ∩ FootprintEdges (T b) = FootprintEdges (S
        a) ∩ FootprintEdges (S b) ∧ FootprintVertices (T a) ∩ FootprintVertices (T b) =
        FootprintVertices (S a) ∩ FootprintVertices (S b)))) → (
    let Walk := fun (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt) =>
      q.head? = some r ∧ q.getLast? = some s ∧
      (∀ x ∈ q, x ∈ FootprintVertices A ∩ FootprintVertices B) ∧
      ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        q = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B
    (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (r : GaussianInt), ∀ (s : GaussianInt), ∀ (q : List
        GaussianInt), (Walk A B r s q) → (Walk A B s r q.reverse)) → ((∀ (A : ProtoTile), ∀ (B :
        ProtoTile), ∀ (r : GaussianInt), ∀ (s : GaussianInt), ∀ (q : List GaussianInt), (Walk A B
        r s q) → (Walk B A r s q)) → (∀ (p : List GaussianInt),
    let pm : Int → Int → List GaussianInt := fun m n => p.map (fun x => x + t m n)
    let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
      (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
        (K.faceEquiv f).first = (K.faceEquiv g).first ∧
        (K.faceEquiv f).second = (K.faceEquiv g).second
    let path : K.core.plane.Face → K.core.plane.Face → List GaussianInt := fun f g =>
      if E f g then pm (K.faceEquiv f).first (K.faceEquiv f).second
      else if E g f then (pm (K.faceEquiv g).first (K.faceEquiv g).second).reverse
      else K.core.facePath f g
    (∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), path g f = (path f g).reverse) → ((∀
        (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (f : K.core.plane.Face), ∀ (g
        : K.core.plane.Face), (K.core.plane.adjacent a b) → ((E f g) → ((∃ i,
        K.core.plane.faceVertex f i = a) → ((∃ i, K.core.plane.faceVertex f i = b) → ((∃ i,
        K.core.plane.faceVertex g i = a) → ((∃ i, K.core.plane.faceVertex g i = b) → ((a = ⟨.A,
        (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧ b = ⟨.B, (K.faceEquiv f).first,
        (K.faceEquiv f).second⟩) ∨ (a = ⟨.B, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧ b =
        ⟨.A, (K.faceEquiv f).first, (K.faceEquiv f).second⟩)))))))) → ((∀ (f :
        K.core.plane.Face), ∀ (g : K.core.plane.Face), (E f g) → (Walk (T ⟨.A, (K.faceEquiv
        f).first, (K.faceEquiv f).second⟩) (T ⟨.B, (K.faceEquiv f).first, (K.faceEquiv
        f).second⟩) (K.core.rho f) (K.core.rho g) (path f g))) → ((∀ (m : Int), ∀ (n : Int), ∀ (f
        : K.core.plane.Face), (∃ i, K.core.plane.faceVertex f i = ⟨.A, m, n⟩) → ((∃ i,
        K.core.plane.faceVertex f i = ⟨.B, m, n⟩) → (K.faceEquiv f = ⟨.I1, m, n⟩ ∨ K.faceEquiv f
        = ⟨.I2, m, n⟩))) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
        (K.core.plane.adjacent a b) → (∀ (f : K.core.plane.Face), ∀ (g : K.core.plane.Face), (f ≠
        g) → ((∃ i, K.core.plane.faceVertex f i = a) → ((∃ i, K.core.plane.faceVertex f i = b) →
        ((∃ i, K.core.plane.faceVertex g i = a) → ((∃ i, K.core.plane.faceVertex g i = b) → (Walk
        (T a) (T b) (K.core.rho f) (K.core.rho g) (path f g)))))))))))))) := by
  classical
  intro P O u v L K T S t exceptional ordinary_retention Walk walk_reverse walk_swap p pm E path
      path_reverse E_pair E_walk AB_faces a b hab f g hfg hfa hfb hga hgb
  by_cases hE : E f g
  · have hw := E_walk f g hE
    rcases E_pair a b f g hab hE hfa hfb hga hgb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hw
    · exact walk_swap _ _ _ _ _ hw
  · by_cases hE' : E g f
    · have hw := walk_reverse _ _ _ _ _ (E_walk g f hE')
      rw [← path_reverse g f] at hw
      rcases E_pair a b g f hab hE' hga hgb hfa hfb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hw
      · exact walk_swap _ _ _ _ _ hw
    · have he : ¬ exceptional a b := by
        intro he
        rcases a with ⟨la, m, n⟩
        rcases b with ⟨lb, r, s⟩
        rcases he with ⟨hh, hmr, hns⟩
        dsimp at hmr hns
        subst r; subst s
        rcases hh with ⟨hla, hlb⟩ | ⟨hla, hlb⟩ <;> dsimp at hla hlb <;>
          cases hla <;> cases hlb
        all_goals
          have hf := AB_faces m n f (by assumption) (by assumption)
          have hg := AB_faces m n g (by assumption) (by assumption)
          rcases hf with hf | hf <;> rcases hg with hg | hg
          · exact hfg (K.faceEquiv.injective (hf.trans hg.symm))
          · exact hE (by simp [E, hf, hg])
          · exact hE' (by simp [E, hf, hg])
          · exact hfg (K.faceEquiv.injective (hf.trans hg.symm))
      have hr := ordinary_retention a b ((K.adjacent_iff a b).mp hab) he
      have hw := K.core.facePath_spec a b hab f g hfg hfa hfb hga hgb
      simp only [K.tile_eq] at hw
      simp only [path, ite_eq_right hE, ite_eq_right hE']
      refine ⟨hw.1, hw.2.1, ?_, ?_⟩
      · intro x hx
        rw [hr.2]
        exact hw.2.2.1 x hx
      · intro x y l1 l2 heq
        rw [hr.1]
        exact hw.2.2.2 x y l1 l2 heq

private theorem edge_AB :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ((FootprintEdges (TileCellComplement (P 0 true) O) ∩ FootprintEdges (P 0
        false)).Nonempty) → (
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    ∀ (m : Int), ∀ (n : Int), (FootprintEdges (T ⟨.A, m, n⟩) ∩ FootprintEdges (T ⟨.B, m,
        n⟩)).Nonempty) := by
  classical
  intro P O u v hABedge T m n
  let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
  rcases hABedge with ⟨e, ha, hb⟩
  refine ⟨e.image (GaussianTranslation (t m n)), ?_, ?_⟩
  · change _ ∈ FootprintEdges (TileTranslation (TileCellComplement (P 0 true) O) (t m n))
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.2.1]
    exact ⟨e, ha, rfl⟩
  · change _ ∈ FootprintEdges (TileTranslation (P 0 false) (t m n))
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.2.1]
    exact ⟨e, hb, rfl⟩

private theorem common_edge :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (L : AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v
        L), (∀ a b : PeriodicSubtileIndex, AllowedSubtileIncidence a b -> ¬ ((a.label = .A ∧
        b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second = b.second) ->
        (FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩ FootprintEdges
        (SubtileOccurrenceInterpretation P u v b)).Nonempty) → (
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    let S := SubtileOccurrenceInterpretation P u v
    let exceptional : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop := fun a b =>
      ((a.label = .A ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧
        a.first = b.first ∧ a.second = b.second)
    (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b) →
        ((¬ exceptional a b) → (FootprintEdges (T a) ∩ FootprintEdges (T b) = FootprintEdges (S
        a) ∩ FootprintEdges (S b) ∧ FootprintVertices (T a) ∩ FootprintVertices (T b) =
        FootprintVertices (S a) ∩ FootprintVertices (S b)))) → ((∀ (m : Int), ∀ (n : Int),
        (FootprintEdges (T ⟨.A, m, n⟩) ∩ FootprintEdges (T ⟨.B, m, n⟩)).Nonempty) → (∀ (a :
        PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (K.core.plane.adjacent a b) →
        ((FootprintEdges (T a) ∩ FootprintEdges (T b)).Nonempty)))) := by
  classical
  intro P O u v L K hordinaryEdge T S exceptional ordinary_retention edge_AB a b hab
  by_cases he : exceptional a b
  · rcases a with ⟨la, m, n⟩
    rcases b with ⟨lb, r, s⟩
    rcases he with ⟨hh, hmr, hns⟩
    dsimp at hmr hns
    subst r; subst s
    rcases hh with ⟨hla, hlb⟩ | ⟨hla, hlb⟩ <;> dsimp at hla hlb <;>
      cases hla <;> cases hlb
    · exact edge_AB m n
    · simpa only [Set.inter_comm] using edge_AB m n
  · have ha := (K.adjacent_iff a b).mp hab
    rw [(ordinary_retention a b ha he).1]
    exact hordinaryEdge a b ha he

private theorem reps :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (L :
        AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v L),
        K.core.vertexOrbitReps =
      {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
       ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩} := by
  classical
  intro P u v L K
  ext a
  rw [K.vertex_reps]
  rcases a with ⟨l, m, n⟩
  cases l <;> simp

private theorem area_balance :
    ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (L : AddSubgroup GaussianInt), ∀ (K : BandUnmodifiedCoreCertificate P u v
        L), (TileArea (TileCellComplement (P 0 true) O) + TileArea (P 0 false) + TileArea (P 1
        true) + TileArea (P 1 false) + TileArea (P 2 true) + TileArea (P 2 false) =
        K.core.latticeReps.card) → (
    let T := ModifiedSubtileOccurrenceInterpretation P O u v
    (∀ (A : ProtoTile), TileTranslation A 0 = A) → ((K.core.vertexOrbitReps = {⟨.A, 0, 0⟩, ⟨.B,
        0, 0⟩, ⟨.C, 0, 0⟩, ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩}) → ((∑ a ∈ K.core.vertexOrbitReps,
        TileArea (T a)) =
      K.core.latticeReps.card))) := by
  classical
  intro P O u v L K harea T trans_zero reps
  simpa [reps, T, ModifiedSubtileOccurrenceInterpretation, trans_zero, add_assoc]
    using harea

end ModifiedPeriodicComplexProof

theorem BandModifiedPeriodicComplex
    (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile)
    (u v : GaussianInt) (L : AddSubgroup GaussianInt)
    (K : BandUnmodifiedCoreCertificate P u v L)
    (hdisks : forall o : PeriodicSubtileIndex,
      LatticeTile (ModifiedSubtileOccurrenceInterpretation P O u v o))
    (hpartition : ∀ x : LatticeCell, ∃! o : PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells)
    (hOA : O.cells ⊆ (P 0 true).cells)
    (hOB : O.cells ⊆ (P 0 false).cells)
    (harea : TileArea (TileCellComplement (P 0 true) O) +
        TileArea (P 0 false) + TileArea (P 1 true) +
        TileArea (P 1 false) + TileArea (P 2 true) +
        TileArea (P 2 false) = K.core.latticeReps.card)
    (hisolated : ∀ m n : Int,
      ∀ x ∈ FootprintVertices
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)),
        ∀ a : GaussianInt,
          x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) ->
          a ∈ (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨
          a ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells)
    (hordinaryEdge : ∀ a b : PeriodicSubtileIndex,
      AllowedSubtileIncidence a b ->
      ¬ ((a.label = .A ∧ b.label = .B ∨
            a.label = .B ∧ b.label = .A) ∧
          a.first = b.first ∧ a.second = b.second) ->
      (FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
        FootprintEdges
          (SubtileOccurrenceInterpretation P u v b)).Nonempty)
    (hABedge :
      (FootprintEdges (TileCellComplement (P 0 true) O) ∩
        FootprintEdges (P 0 false)).Nonempty)
    (hABpath :
      ∃ p : List GaussianInt,
        p.head? = some
            (K.core.rho (K.faceEquiv.symm ⟨.I1, 0, 0⟩)) ∧
        p.getLast? = some
            (K.core.rho (K.faceEquiv.symm ⟨.I2, 0, 0⟩)) ∧
        (∀ x ∈ p,
          x ∈ FootprintVertices (TileCellComplement (P 0 true) O) ∩
            FootprintVertices (P 0 false)) ∧
        (∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
          p = l1 ++ x :: y :: l2 ->
            {x, y} ∈ FootprintEdges (TileCellComplement (P 0 true) O) ∩
              FootprintEdges (P 0 false))) :
    ∃ M : PeriodicTileComplex PeriodicSubtileIndex,
      M.lattice = L ∧
      (∀ o, M.tile o = ModifiedSubtileOccurrenceInterpretation P O u v o) ∧
      (∀ a b, M.plane.adjacent a b <-> AllowedSubtileIncidence a b) ∧
      ∃ e : M.plane.Face ≃ PeriodicSubtileFaceIndex,
        (∀ f : PeriodicSubtileFaceIndex,
          M.rho (e.symm f) = K.core.rho (K.faceEquiv.symm f)) ∧
        (∀ f i, M.plane.faceVertex f i = SixSubtileFaceVertices (e f) i) ∧
        (∀ f, f ∈ M.faceOrbitReps <->
          (e f).first = 0 ∧ (e f).second = 0) := by
-- BODY
  classical
  let T := ModifiedSubtileOccurrenceInterpretation P O u v
  let S := SubtileOccurrenceInterpretation P u v
  let t : Int → Int → GaussianInt := fun m n => (m : GaussianInt) * u + (n : GaussianInt) * v
  have tile_ext (A B : ProtoTile) (hc : A.cells = B.cells) (ha : A.anchor = B.anchor) :
      A = B := ModifiedPeriodicComplexProof.tile_ext A B hc ha
  have trans_comp (A : ProtoTile) (x y : GaussianInt) :
      TileTranslation (TileTranslation A x) y = TileTranslation A (x + y) :=
          ModifiedPeriodicComplexProof.trans_comp tile_ext A x y
  have trans_zero (A : ProtoTile) : TileTranslation A 0 = A :=
      ModifiedPeriodicComplexProof.trans_zero tile_ext A
  -- The face rows determine the inherited action on all six labels.
  have face_row (w : K.core.lattice) (f : PeriodicSubtileFaceIndex) (i : Fin 3) :
      K.core.shift w (SixSubtileFaceVertices f i) =
        SixSubtileFaceVertices
          ⟨f.label, f.first + (K.latticeCoordinates w).1, f.second + (K.latticeCoordinates w).2⟩
              i :=
                       ModifiedPeriodicComplexProof.face_row P u v L K w f i
  have shift_eq (w : K.core.lattice) (a : PeriodicSubtileIndex) :
      K.core.shift w a =
        ⟨a.label, a.first + (K.latticeCoordinates w).1, a.second + (K.latticeCoordinates w).2⟩ :=
                     ModifiedPeriodicComplexProof.shift_eq P u v L K face_row w a
  have t_shift (w : K.core.lattice) (m n : Int) :
      t (m + (K.latticeCoordinates w).1) (n + (K.latticeCoordinates w).2) =
        t m n + (w : GaussianInt) := ModifiedPeriodicComplexProof.t_shift P u v L K w m n
  have tile_periodic (w : K.core.lattice) (a : PeriodicSubtileIndex) :
      T (K.core.shift w a) = TileTranslation (T a) w :=
          ModifiedPeriodicComplexProof.tile_periodic P O u v L K trans_comp shift_eq t_shift w a
  have unchanged (a : PeriodicSubtileIndex) (ha : a.label ≠ .A) : T a = S a :=
      ModifiedPeriodicComplexProof.unchanged P O u v a ha
  have modified_a (m n : Int) : T ⟨.A, m, n⟩ =
      TileCellComplement (S ⟨.A, m, n⟩) (TileTranslation O (t m n)) :=
          ModifiedPeriodicComplexProof.modified_a P O u v m n
  have cells_nonempty (A : ProtoTile) (hA : LatticeTile A) : A.cells.Nonempty :=
      ModifiedPeriodicComplexProof.cells_nonempty A hA
  have original_nonempty (a : PeriodicSubtileIndex) : (S a).cells.Nonempty :=
      ModifiedPeriodicComplexProof.original_nonempty P u v L K cells_nonempty a
  have modified_nonempty (a : PeriodicSubtileIndex) : (T a).cells.Nonempty :=
      ModifiedPeriodicComplexProof.modified_nonempty P O u v hdisks cells_nonempty a
  have separation := ModifiedPeriodicComplexProof.separation P O u v hpartition hOA hOB
  -- Ordinary partners retain both footprint vertices and footprint edges.
  have retention (m n : Int) (b : PeriodicSubtileIndex)
      (hbA : b.label ≠ .A) (hb : b ≠ ⟨.B, m, n⟩) :
      FootprintEdges (T ⟨.A, m, n⟩) ∩ FootprintEdges (T b) =
          FootprintEdges (S ⟨.A, m, n⟩) ∩ FootprintEdges (S b) ∧
      FootprintVertices (T ⟨.A, m, n⟩) ∩ FootprintVertices (T b) =
          FootprintVertices (S ⟨.A, m, n⟩) ∩ FootprintVertices (S b) :=
              ModifiedPeriodicComplexProof.retention P O u v hOA hisolated unchanged modified_a
              original_nonempty modified_nonempty separation m n b hbA hb
  have no_AA (a b : PeriodicSubtileIndex) (h : AllowedSubtileIncidence a b) :
      ¬ (a.label = .A ∧ b.label = .A) := ModifiedPeriodicComplexProof.no_AA a b h
  let exceptional : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop := fun a b =>
    ((a.label = .A ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧
      a.first = b.first ∧ a.second = b.second)
  have ordinary_retention (a b : PeriodicSubtileIndex)
      (h : AllowedSubtileIncidence a b) (he : ¬ exceptional a b) :
      FootprintEdges (T a) ∩ FootprintEdges (T b) =
          FootprintEdges (S a) ∩ FootprintEdges (S b) ∧
      FootprintVertices (T a) ∩ FootprintVertices (T b) =
          FootprintVertices (S a) ∩ FootprintVertices (S b) :=
              ModifiedPeriodicComplexProof.ordinary_retention P O u v unchanged retention no_AA a
              b h he
  have rho_common (f : K.core.plane.Face) (i : Fin 3) :
      K.core.rho f ∈ FootprintVertices (T (K.core.plane.faceVertex f i)) :=
          ModifiedPeriodicComplexProof.rho_common P O u v L K unchanged retention f i
  let Walk := fun (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt) =>
    q.head? = some r ∧ q.getLast? = some s ∧
    (∀ x ∈ q, x ∈ FootprintVertices A ∩ FootprintVertices B) ∧
    ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
      q = l1 ++ x :: y :: l2 → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B
  have walk_reverse (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt)
      (hq : Walk A B r s q) : Walk A B s r q.reverse := ModifiedPeriodicComplexProof.walk_reverse
          A B r s q hq
  have walk_swap (A B : ProtoTile) (r s : GaussianInt) (q : List GaussianInt)
      (hq : Walk A B r s q) : Walk B A r s q := ModifiedPeriodicComplexProof.walk_swap A B r s q hq
  have walk_map (A B : ProtoTile) (r s w : GaussianInt) (q : List GaussianInt)
      (hq : Walk A B r s q) :
      Walk (TileTranslation A w) (TileTranslation B w) (r + w) (s + w)
        (q.map (fun x => x + w)) := ModifiedPeriodicComplexProof.walk_map A B r s w q hq
  have rho_index (f : PeriodicSubtileFaceIndex) :
      K.core.rho (K.faceEquiv.symm f) =
        K.core.rho (K.faceEquiv.symm ⟨f.label, 0, 0⟩) + t f.first f.second :=
            ModifiedPeriodicComplexProof.rho_index P u v L K f
  rcases hABpath with ⟨p, hp⟩
  let pm : Int → Int → List GaussianInt := fun m n => p.map (fun x => x + t m n)
  have pm_spec (m n : Int) : Walk (T ⟨.A, m, n⟩) (T ⟨.B, m, n⟩)
      (K.core.rho (K.faceEquiv.symm ⟨.I1, m, n⟩))
      (K.core.rho (K.faceEquiv.symm ⟨.I2, m, n⟩)) (pm m n) :=
          ModifiedPeriodicComplexProof.pm_spec P O u v L K walk_map rho_index p hp m n
  -- Define the exceptional replacement on every ordered face pair.
  let E : K.core.plane.Face → K.core.plane.Face → Prop := fun f g =>
    (K.faceEquiv f).label = .I1 ∧ (K.faceEquiv g).label = .I2 ∧
      (K.faceEquiv f).first = (K.faceEquiv g).first ∧
      (K.faceEquiv f).second = (K.faceEquiv g).second
  let path : K.core.plane.Face → K.core.plane.Face → List GaussianInt := fun f g =>
    if E f g then pm (K.faceEquiv f).first (K.faceEquiv f).second
    else if E g f then (pm (K.faceEquiv g).first (K.faceEquiv g).second).reverse
    else K.core.facePath f g
  have E_asymm (f g : K.core.plane.Face) (h : E f g) : ¬ E g f :=
      ModifiedPeriodicComplexProof.E_asymm P u v L K f g h
  have E_shift (w : K.core.lattice) (f g : K.core.plane.Face) :
      E (K.core.faceShift w f) (K.core.faceShift w g) ↔ E f g :=
          ModifiedPeriodicComplexProof.E_shift P u v L K w f g
  have path_reverse (f g : K.core.plane.Face) : path g f = (path f g).reverse :=
      ModifiedPeriodicComplexProof.path_reverse P u v L K p E_asymm f g
  have pm_shift (w : K.core.lattice) (m n : Int) :
      pm (m + (K.latticeCoordinates w).1) (n + (K.latticeCoordinates w).2) =
        (pm m n).map (fun x => x + (w : GaussianInt)) := ModifiedPeriodicComplexProof.pm_shift P
            u v L K t_shift p w m n
  have path_periodic (w : K.core.lattice) (f g : K.core.plane.Face) :
      path (K.core.faceShift w f) (K.core.faceShift w g) =
        (path f g).map (fun x => x + (w : GaussianInt)) :=
            ModifiedPeriodicComplexProof.path_periodic P u v L K p E_shift pm_shift w f g
  have E_indices (f g : K.core.plane.Face) (h : E f g) :
      K.faceEquiv f = ⟨.I1, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧
      K.faceEquiv g = ⟨.I2, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ :=
          ModifiedPeriodicComplexProof.E_indices P u v L K f g h
  have common_I (m n : Int) (a : PeriodicSubtileIndex)
      (h1 : ∃ i, SixSubtileFaceVertices ⟨.I1, m, n⟩ i = a)
      (h2 : ∃ i, SixSubtileFaceVertices ⟨.I2, m, n⟩ i = a) :
      a = ⟨.A, m, n⟩ ∨ a = ⟨.B, m, n⟩ := ModifiedPeriodicComplexProof.common_I m n a h1 h2
  have E_pair (a b : PeriodicSubtileIndex) (f g : K.core.plane.Face)
      (hab : K.core.plane.adjacent a b) (hE : E f g)
      (hfa : ∃ i, K.core.plane.faceVertex f i = a)
      (hfb : ∃ i, K.core.plane.faceVertex f i = b)
      (hga : ∃ i, K.core.plane.faceVertex g i = a)
      (hgb : ∃ i, K.core.plane.faceVertex g i = b) :
      (a = ⟨.A, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧
       b = ⟨.B, (K.faceEquiv f).first, (K.faceEquiv f).second⟩) ∨
      (a = ⟨.B, (K.faceEquiv f).first, (K.faceEquiv f).second⟩ ∧
       b = ⟨.A, (K.faceEquiv f).first, (K.faceEquiv f).second⟩) :=
           ModifiedPeriodicComplexProof.E_pair P u v L K E_indices common_I a b f g hab hE hfa
           hfb hga hgb
  have E_walk (f g : K.core.plane.Face) (hE : E f g) :
      Walk (T ⟨.A, (K.faceEquiv f).first, (K.faceEquiv f).second⟩)
        (T ⟨.B, (K.faceEquiv f).first, (K.faceEquiv f).second⟩)
        (K.core.rho f) (K.core.rho g) (path f g) := ModifiedPeriodicComplexProof.E_walk P O u v L
            K p pm_spec E_indices f g hE
  have AB_faces (m n : Int) (f : K.core.plane.Face)
      (ha : ∃ i, K.core.plane.faceVertex f i = ⟨.A, m, n⟩)
      (hb : ∃ i, K.core.plane.faceVertex f i = ⟨.B, m, n⟩) :
      K.faceEquiv f = ⟨.I1, m, n⟩ ∨ K.faceEquiv f = ⟨.I2, m, n⟩ :=
          ModifiedPeriodicComplexProof.AB_faces P u v L K m n f ha hb
  have path_spec (a b : PeriodicSubtileIndex) (hab : K.core.plane.adjacent a b)
      (f g : K.core.plane.Face) (hfg : f ≠ g)
      (hfa : ∃ i, K.core.plane.faceVertex f i = a)
      (hfb : ∃ i, K.core.plane.faceVertex f i = b)
      (hga : ∃ i, K.core.plane.faceVertex g i = a)
      (hgb : ∃ i, K.core.plane.faceVertex g i = b) :
      Walk (T a) (T b) (K.core.rho f) (K.core.rho g) (path f g) :=
          ModifiedPeriodicComplexProof.path_spec P O u v L K ordinary_retention walk_reverse
          walk_swap p path_reverse E_pair E_walk AB_faces a b hab f g hfg hfa hfb hga hgb
  have edge_AB (m n : Int) :
      (FootprintEdges (T ⟨.A, m, n⟩) ∩ FootprintEdges (T ⟨.B, m, n⟩)).Nonempty :=
          ModifiedPeriodicComplexProof.edge_AB P O u v hABedge m n
  have common_edge (a b : PeriodicSubtileIndex) (hab : K.core.plane.adjacent a b) :
      (FootprintEdges (T a) ∩ FootprintEdges (T b)).Nonempty :=
          ModifiedPeriodicComplexProof.common_edge P O u v L K hordinaryEdge ordinary_retention
          edge_AB a b hab
  have reps : K.core.vertexOrbitReps =
      {⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.C, 0, 0⟩,
       ⟨.D, 0, 0⟩, ⟨.E, 0, 0⟩, ⟨.F, 0, 0⟩} := ModifiedPeriodicComplexProof.reps P u v L K
  have area_balance : (∑ a ∈ K.core.vertexOrbitReps, TileArea (T a)) =
      K.core.latticeReps.card := ModifiedPeriodicComplexProof.area_balance P O u v L K harea
          trans_zero reps
  let M : PeriodicTileComplex PeriodicSubtileIndex :=
    { toPeriodicTileCore :=
        { K.core with
          tile := T
          tiles_are_disks := hdisks
          tile_periodic := tile_periodic
          rho_common := rho_common
          facePath := path
          facePath_reverse := path_reverse
          facePath_periodic := path_periodic
          facePath_spec := path_spec }
      area_balance := area_balance
      adjacent_has_common_edge := common_edge }
  refine ⟨M, K.lattice_eq, (fun _ => rfl), K.adjacent_iff, K.faceEquiv,
    (fun _ => rfl), K.face_vertices, K.face_reps⟩

end ApollonianSuperharmonic

end

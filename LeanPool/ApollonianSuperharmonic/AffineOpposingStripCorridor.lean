/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineTriangularCorridorStep
public import LeanPool.ApollonianSuperharmonic.TriangularStripSegmentOrderInterval
public import Mathlib.Data.List.Range

-- [TABLET NODE: AffineOpposingStripCorridor]

/-!
# AffineOpposingStripCorridor

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OpposingStripProof

private theorem ppseg :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (
        let h : Int → Int := fun k => (B*k+A-1)/A
        (∀ (k : Int), 0 ≤ A*h k-B*k ∧ A*h k-B*k < A) → ((∀ (k : Int), h (k+1) = h k ∨ h (k+1) = h
        k+1) → ((TriangularMaxIncrement (0,0) (A,B) = A) → ((TriangularMaxIncrement (A,B) (0,0) =
        A) → (
        let N := A.toNat
        ((N : Int) = A) → (
        let p : Nat → Int × Int := fun k => (k, h k)
        let PP := (List.range (N+1)).map p
        (Function.Injective p) → ((PP.head? = some (0,0)) → ((PP.getLast? = some (A,B)) →
        (TriangularStripSegment (0,0) (A,B) PP))))))))) ) := by
  classical
  intro A B hA h hh hnext hmax hrmax N hN p PP pinj phead plast
  rw [TriangularStripSegment, ite_eq_right (by
    intro he
    have := congrArg Prod.fst he
    simp at this
    omega)]
  refine ⟨phead, plast, List.nodup_range.map pinj, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
    simpa [TriangularBoundaryStrip, TriangularSignedHeight, hmax, p] using hh k
  · apply (List.isChain_map p).mpr
    apply (List.isChain_range_succ _ N).mpr
    intro k hk
    rcases hnext k with he | he <;>
      simp [TriangularLatticeAdjacent, p, Nat.cast_add, Prod.sub_def, he]

private theorem qqseg :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (
        let l : Int → Int := fun k => (B*k)/A
        (∀ (k : Int), 0 ≤ B*k-A*l k ∧ B*k-A*l k < A) → ((∀ (k : Int), l (k+1) = l k ∨ l (k+1) = l
        k+1) → ((TriangularMaxIncrement (0,0) (A,B) = A) → ((TriangularMaxIncrement (A,B) (0,0) =
        A) → (
        let N := A.toNat
        ((N : Int) = A) → (
        let q : Nat → Int × Int := fun k => (k, l k)
        let QQ := ((List.range (N+1)).map q).reverse
        (Function.Injective q) → ((((List.range (N+1)).map q).head? = some (0,0)) → ((((List.range
        (N+1)).map q).getLast? = some (A,B)) → (TriangularStripSegment (A,B) (0,0) QQ))))))))) )
            := by
  classical
  intro A B hA l hl lnext hmax hrmax N hN q QQ qinj qhead qlast
  rw [TriangularStripSegment, ite_eq_right (by
    intro he
    have := congrArg Prod.fst he
    simp at this
    omega)]
  refine ⟨?_, ?_, List.nodup_reverse.mpr (List.nodup_range.map qinj), ?_, ?_⟩
  · simpa [QQ] using qlast
  · simpa [QQ] using qhead
  · intro z hz
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hz)
    have he : TriangularSignedHeight (A,B) (0,0) (q k) = B*k-A*l k := by
      dsimp [TriangularSignedHeight, q]
      ring
    simpa [TriangularBoundaryStrip, hrmax, he] using hl k
  · apply List.isChain_reverse.mpr
    apply (List.isChain_map q).mpr
    apply (List.isChain_range_succ _ N).mpr
    intro k hk
    rcases lnext k with he | he <;>
      simp [TriangularLatticeAdjacent, q, Nat.cast_add, Prod.sub_def, he]

private theorem interior :
    (by
      classical
      exact
        ∀ (path : List (ℤ × ℤ)), ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), ∀ (z : ℤ × ℤ), path.head? = some a →
        path.getLast? = some b → z ∈ path → z ≠ a → z ≠ b → z ∈ (List.drop (1 : ℕ) path).dropLast
            ) := by
  classical
  intro path a b z ha hb hz hza hzb
  cases path with
  | nil => simp at hz
  | cons c t =>
    have hc : c = a := by simpa using ha
    have hzt : z ∈ t := by simpa [hc, hza] using hz
    have ht : t ≠ [] := List.ne_nil_of_mem hzt
    have hbt : t.getLast? = some b := by simpa [List.getLast?_cons_of_ne_nil ht] using hb
    apply List.mem_dropLast_of_mem_of_ne_getLast? hzt
    simpa [hbt] using hzb

private theorem bvertices :
    (by
      classical
      exact
        ∀ (P : List (ℤ × ℤ)), ∀ (Q : List (ℤ × ℤ)), ∀ (A : ℤ), ∀ (B : ℤ),
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        let N := A.toNat
        let p : Nat → Int × Int := fun k => (k, h k)
        let q : Nat → Int × Int := fun k => (k, l k)
        (∀ (k : Nat), (0 < k ∧ k < N) → (p k ∈ (P.drop 1).dropLast)) → ((∀ (k : Nat), (0 < k ∧ k
            < N)
        → (q k ∈ (Q.drop 1).dropLast)) → ((∀ (k : Int), h k = l k ∨ h k = l k+1) → (
        let block : Nat → List AffineTriangularFace := fun k =>
        if h k = l k then
        [.down (k,l k), .up (k,l k+1), .down ((k : Int)+1,l k), .up (k,h k)]
        else [.down (k,l k), .up (k,h k)]
        ∀ (k : ℕ), (0 : ℕ) < k ∧ k < N → ∀ f ∈ block k, (∃ a ∈ (List.drop (1 : ℕ) P).dropLast, a ∈
        AffineTriangularFaceVertices f) ∧ ∃ b ∈ (List.drop (1 : ℕ) Q).dropLast, b ∈
        AffineTriangularFaceVertices f))) ) := by
  classical
  intro P Q A B l h N p q pmem qmem gap block k hk f hf
  have hp := pmem k hk
  have hq := qmem k hk
  dsimp [block] at hf
  split at hf
  · rename_i he
    refine ⟨⟨p k,hp,?_⟩,⟨q k,hq,?_⟩⟩
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        simp [AffineTriangularFaceVertices, p,q,he,Prod.add_def,Prod.sub_def]
  · rename_i he
    have hg : h k = l k+1 := (gap k).resolve_left he
    refine ⟨⟨p k,hp,?_⟩,⟨q k,hq,?_⟩⟩
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;>
        simp [AffineTriangularFaceVertices,p,q,hg,Prod.add_def,Prod.sub_def]

private theorem bchain :
    (by
      classical
      exact
        ∀ (P : List (ℤ × ℤ)), ∀ (Q : List (ℤ × ℤ)), ∀ (A : ℤ), ∀ (B : ℤ),
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        let N := A.toNat
        let p : Nat → Int × Int := fun k => (k, h k)
        let q : Nat → Int × Int := fun k => (k, l k)
        (∀ (k : Nat), (0 < k ∧ k < N) → (p k ∈ (P.drop 1).dropLast)) → ((∀ (k : Nat), (0 < k ∧ k
            < N)
        → (q k ∈ (Q.drop 1).dropLast)) → ((∀ (k : Int), h k = l k ∨ h k = l k+1) → (
        let block : Nat → List AffineTriangularFace := fun k =>
        if h k = l k then
        [.down (k,l k), .up (k,l k+1), .down ((k : Int)+1,l k), .up (k,h k)]
        else [.down (k,l k), .up (k,h k)]
        (∀ (f : AffineTriangularFace), ∀ (g : AffineTriangularFace), ∀ (u : Int × Int), ∀ (v : Int ×
        Int), (f ≠ g) → ((u ≠ v) → ((TriangularLatticeAdjacent u v) → ((u ∈
        AffineTriangularFaceVertices f) → ((v ∈ AffineTriangularFaceVertices f) → ((u ∈
        AffineTriangularFaceVertices g) → ((v ∈ AffineTriangularFaceVertices g) → (((u ∈ (P.drop
        1).dropLast ∧ v ∈ (Q.drop 1).dropLast) ∨ (u ∈ (P.drop 1).dropLast ∧ u ∈ (Q.drop
        1).dropLast)) → (AffineTriangularCorridorStep P Q f g))))))))) → (∀ (k : ℕ), (0 : ℕ) < k
        ∧ k < N → List.IsChain (AffineTriangularCorridorStep P Q) (block k))))) ) := by
  classical
  intro P Q A B l h N p q pmem qmem gap block mkstep k hk
  have hp := pmem k hk
  have hq := qmem k hk
  dsimp [block]
  split
  · rename_i he
    have pq : p k = q k := by simp [p,q,he]
    have hm : p k ∈ (P.drop 1).dropLast ∧ p k ∈ (Q.drop 1).dropLast :=
      ⟨hp, pq ▸ hq⟩
    have s1 : AffineTriangularCorridorStep P Q (.down (k,l k)) (.up (k,l k+1)) := by
      apply mkstep _ _ (p k) ((k : Int),l k+1)
      · simp
      · simp [p,he]
      · simp [TriangularLatticeAdjacent,p,he,Prod.sub_def]
      · simp [AffineTriangularFaceVertices,p,he]
      · simp [AffineTriangularFaceVertices,Prod.add_def]
      · simp [AffineTriangularFaceVertices,p,he,Prod.sub_def]
      · simp [AffineTriangularFaceVertices]
      · exact Or.inr hm
    have s2 : AffineTriangularCorridorStep P Q (.up (k,l k+1)) (.down ((k : Int)+1,l k)) := by
      apply mkstep _ _ (p k) ((k : Int)+1,l k+1)
      · simp
      · simp [p,he]
      · simp [TriangularLatticeAdjacent,p,he,Prod.sub_def]
      · simp [AffineTriangularFaceVertices,p,he,Prod.sub_def]
      · simp [AffineTriangularFaceVertices,Prod.add_def]
      · simp [AffineTriangularFaceVertices,p,he,Prod.sub_def]
      · simp [AffineTriangularFaceVertices,Prod.add_def]
      · exact Or.inr hm
    have s3 : AffineTriangularCorridorStep P Q (.down ((k : Int)+1,l k)) (.up (k,h k)) := by
      apply mkstep _ _ (p k) ((k : Int)+1,l k)
      · simp
      · simp [p,he]
      · simp [TriangularLatticeAdjacent,p,he,Prod.sub_def]
      · simp [AffineTriangularFaceVertices,p,he,Prod.sub_def]
      · simp [AffineTriangularFaceVertices]
      · simp [AffineTriangularFaceVertices,p]
      · simp [AffineTriangularFaceVertices,he,Prod.add_def]
      · exact Or.inr hm
    simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using ⟨s1,s2,s3⟩
  · rename_i he
    have hg : h k = l k+1 := (gap k).resolve_left he
    have ss : AffineTriangularCorridorStep P Q (.down (k,l k)) (.up (k,h k)) := by
      apply mkstep _ _ (p k) (q k)
      · simp
      · simp [p,q,hg]
      · simp [TriangularLatticeAdjacent,p,q,hg,Prod.sub_def]
      · simp [AffineTriangularFaceVertices,p,hg,Prod.add_def]
      · simp [AffineTriangularFaceVertices,q]
      · simp [AffineTriangularFaceVertices,p]
      · simp [AffineTriangularFaceVertices,q,hg,Prod.sub_def]
      · exact Or.inl ⟨hp,hq⟩
    simpa using ss

private theorem joinstep :
    (by
      classical
      exact
        ∀ (P : List (ℤ × ℤ)), ∀ (Q : List (ℤ × ℤ)), ∀ (A : ℤ), ∀ (B : ℤ),
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        let N := A.toNat
        let p : Nat → Int × Int := fun k => (k, h k)
        let q : Nat → Int × Int := fun k => (k, l k)
        (∀ (k : Nat), (0 < k ∧ k < N) → (p k ∈ (P.drop 1).dropLast)) → ((∀ (k : Nat), (0 < k ∧ k
            < N)
        → (q k ∈ (Q.drop 1).dropLast)) → ((∀ (k : Int), l (k+1) = h k ∨ l (k+1) = h k-1) → ((∀ (k
            : Int), (l (k+1) = h k-1) → (h k = l k+1 ∧ h (k+1) = h k)) → ((∀ (f :
            AffineTriangularFace), ∀ (g : AffineTriangularFace), ∀ (u : Int × Int), ∀ (v : Int ×
        Int), (f ≠ g) → ((u ≠ v) → ((TriangularLatticeAdjacent u v) → ((u ∈
        AffineTriangularFaceVertices f) → ((v ∈ AffineTriangularFaceVertices f) → ((u ∈
        AffineTriangularFaceVertices g) → ((v ∈ AffineTriangularFaceVertices g) → (((u ∈ (P.drop
        1).dropLast ∧ v ∈ (Q.drop 1).dropLast) ∨ (u ∈ (P.drop 1).dropLast ∧ u ∈ (Q.drop
        1).dropLast)) → (AffineTriangularCorridorStep P Q f g))))))))) → (∀ (k : ℕ), (0 : ℕ) < k
        ∧ k + (1 : ℕ) < N → AffineTriangularCorridorStep P Q (AffineTriangularFace.up ((↑k : ℤ),
        h (↑k : ℤ))) (AffineTriangularFace.down ((↑k : ℤ) + (1 : ℤ), l ((↑k : ℤ) + (1 :
        ℤ))))))))) ) := by
  classical
  intro P Q A B l h N p q pmem qmem between below mkstep k hk
  rcases between k with he | he
  · apply mkstep _ _ (p k) (q (k+1))
    · simp
    · simp [p,q]
    · simp [TriangularLatticeAdjacent,p,q,Nat.cast_add,he,Prod.sub_def]
    · simp [AffineTriangularFaceVertices,p]
    · simp [AffineTriangularFaceVertices,q,Nat.cast_add,he,Prod.add_def]
    · simp [AffineTriangularFaceVertices,p,he,Prod.sub_def]
    · simp [AffineTriangularFaceVertices,q]
    · exact Or.inl ⟨pmem k (by omega), qmem (k+1) (by omega)⟩
  · obtain ⟨he1,he2⟩ := below k he
    apply mkstep _ _ (p (k+1)) (q k)
    · simp
    · simp [p,q]
    · simp [TriangularLatticeAdjacent,p,q,Nat.cast_add,he1,he2,Prod.sub_def]
    · simp [AffineTriangularFaceVertices,p,Nat.cast_add,he2,Prod.add_def]
    · simp [AffineTriangularFaceVertices,q,he1,Prod.sub_def]
    · simp [AffineTriangularFaceVertices,p,Nat.cast_add,he,he2,Prod.add_def]
    · simp [AffineTriangularFaceVertices,q,he,he1,Prod.sub_def]
    · exact Or.inl ⟨pmem (k+1) (by omega), qmem k (by omega)⟩

private theorem fsproperties :
    (by
      classical
      exact
        ∀ (P : List (ℤ × ℤ)), ∀ (Q : List (ℤ × ℤ)), ∀ (A : ℤ), ∀ (B : ℤ),
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        let N := A.toNat
        let block : Nat → List AffineTriangularFace := fun k =>
        if h k = l k then
        [.down (k,l k), .up (k,l k+1), .down ((k : Int)+1,l k), .up (k,h k)]
        else [.down (k,l k), .up (k,h k)]
        (∀ (k : Nat), (block k).head? = some (.down (k,l k))) → ((∀ (k : Nat), (block k).getLast? =
        some (.up (k,h k))) → ((∀ (k : Nat), block k ≠ []) → ((∀ (k : Nat), (0 < k ∧ k < N) → (∀
        f ∈ block k, (∃ a ∈ (P.drop 1).dropLast, a ∈ AffineTriangularFaceVertices f) ∧ (∃ b ∈
        (Q.drop 1).dropLast, b ∈ AffineTriangularFaceVertices f))) → ((∀ (k : Nat), (0 < k ∧ k <
        N) → ((block k).IsChain (AffineTriangularCorridorStep P Q))) → ((∀ (k : Nat), (0 < k ∧
        k+1 < N) → (AffineTriangularCorridorStep P Q (.up (k,h k)) (.down (k+1,l (k+1))))) → (
        let fs : Nat → List AffineTriangularFace := fun n =>
        (List.range n).flatMap (fun i => block (i+1))
        ∀ (n : ℕ), (0 : ℕ) < n ∧ n < N → fs n ≠ [] ∧ (fs n).head? = some (AffineTriangularFace.down
        ((1 : ℤ), l (1 : ℤ))) ∧ (fs n).getLast? = some (AffineTriangularFace.up ((↑n : ℤ), h (↑n
        : ℤ))) ∧ (∀ f ∈ fs n, (∃ a ∈ (List.drop (1 : ℕ) P).dropLast, a ∈
        AffineTriangularFaceVertices f) ∧ ∃ b ∈ (List.drop (1 : ℕ) Q).dropLast, b ∈
        AffineTriangularFaceVertices f) ∧ List.IsChain (AffineTriangularCorridorStep P Q) (fs
        n))))))) ) := by
  classical
  intro P Q A B l h N block bhead blast bne bvertices bchain joinstep fs n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      have he : fs 1 = block 1 := by simp [fs]
      rw [he]
      exact ⟨bne 1,bhead 1,blast 1,bvertices 1 hn,bchain 1 hn⟩
    · obtain ⟨hne,hhead,hlast,hvertices,hchain⟩ := ih (by omega)
      have he : fs (n+1) = fs n ++ block (n+1) := by
        simp [fs,List.range_succ,List.flatMap_append]
      rw [he]
      refine ⟨by simp [hne],?_,?_,?_,?_⟩
      · simp [List.head?_append, hhead]
      · simp [List.getLast?_append, blast (n + 1)]
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hvertices f hf
        · exact bvertices (n+1) (by omega) f hf
      · apply hchain.append (bchain (n+1) (by omega))
        intro f hf g hg
        have hf' : f = .up (n,h n) := by simpa [hlast] using hf.symm
        have hg' : g = .down (n+1,l (n+1)) := by simpa [bhead] using hg.symm
        subst f; subst g
        exact joinstep n (by omega)

private theorem pullback :
    (by
      classical
      exact
        let corridor (x y : Int × Int) (P Q : List (Int × Int)) : Prop :=
        ∃ faces : List AffineTriangularFace,
        faces ≠ [] ∧
        (∃ f, faces.head? = some f ∧ x ∈ AffineTriangularFaceVertices f) ∧
        (∃ f, faces.getLast? = some f ∧ y ∈ AffineTriangularFaceVertices f) ∧
        (∀ f ∈ faces,
        (∃ a ∈ (P.drop 1).dropLast, a ∈ AffineTriangularFaceVertices f) ∧
        (∃ b ∈ (Q.drop 1).dropLast, b ∈ AffineTriangularFaceVertices f)) ∧
        faces.IsChain (AffineTriangularCorridorStep P Q)
        ∀ (E : ℤ × ℤ ≃ ℤ × ℤ), ∀ (F : AffineTriangularFace ≃ AffineTriangularFace), (∀ (u : ℤ ×
            ℤ), ∀ (v : ℤ × ℤ), TriangularLatticeAdjacent ((E : ℤ × ℤ → ℤ × ℤ) u) ((E : ℤ × ℤ → ℤ
            × ℤ) v) ↔
        TriangularLatticeAdjacent u v) → (∀ (z : ℤ × ℤ), ∀ (f : AffineTriangularFace), (E : ℤ × ℤ
        → ℤ × ℤ) z ∈ AffineTriangularFaceVertices ((F : AffineTriangularFace →
        AffineTriangularFace) f) ↔ z ∈ AffineTriangularFaceVertices f) → ∀ (x : ℤ × ℤ), ∀ (y : ℤ
        × ℤ), ∀ (P : List (ℤ × ℤ)), ∀ (Q : List (ℤ × ℤ)), corridor ((E : ℤ × ℤ → ℤ × ℤ) x) ((E :
        ℤ × ℤ → ℤ × ℤ) y) (List.map (⇑E : ℤ × ℤ → ℤ × ℤ) P) (List.map (⇑E : ℤ × ℤ → ℤ × ℤ) Q) →
        corridor x y P Q ) := by
  classical
  intro corridor E F hAdj hInc x y P Q hcorr
  classical
  obtain ⟨fs,hne,⟨f0,hhead,hx⟩,⟨f1,hlast,hy⟩,hv,hc⟩ := hcorr
  have inc (z : Int × Int) (f : AffineTriangularFace)
      (hz : z ∈ AffineTriangularFaceVertices f) :
      E.symm z ∈ AffineTriangularFaceVertices (F.symm f) := by
    apply (hInc (E.symm z) (F.symm f)).mp
    simpa using hz
  have inner (p : List (Int × Int)) (z : Int × Int)
      (hz : z ∈ ((p.map E).drop 1).dropLast) : E.symm z ∈ (p.drop 1).dropLast := by
    rw [← List.map_drop, ← List.map_dropLast] at hz
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
    simpa using hu
  have step (f g : AffineTriangularFace) (hs : AffineTriangularCorridorStep (P.map E) (Q.map E) f
      g) :
      AffineTriangularCorridorStep P Q (F.symm f) (F.symm g) := by
    obtain ⟨hfg,u,v,huv,hadj,huf,hvf,hug,hvg,hm⟩ := hs
    refine ⟨fun he => hfg (F.symm.injective he), E.symm u,E.symm v,
      fun he => huv (E.symm.injective he),?_,inc u f huf,inc v f hvf,inc u g hug,inc v g hvg,?_⟩
    · apply (hAdj (E.symm u) (E.symm v)).mp
      simpa using hadj
    · rcases hm with ⟨hp,hq⟩ | ⟨hp,hq⟩
      · exact Or.inl ⟨inner P u hp,inner Q v hq⟩
      · exact Or.inr ⟨inner P u hp,inner Q u hq⟩
  refine ⟨fs.map F.symm,by simpa using hne,
    ⟨F.symm f0,?_,?_⟩,⟨F.symm f1,?_,?_⟩,?_,?_⟩
  · simp [hhead]
  · simpa using inc (E x) f0 hx
  · simp [hlast]
  · simpa using inc (E y) f1 hy
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    obtain ⟨⟨a,ha,haf⟩,⟨b,hb,hbf⟩⟩ := hv g hg
    exact ⟨⟨E.symm a,inner P a ha,inc a g haf⟩,
      ⟨E.symm b,inner Q b hb,inc b g hbf⟩⟩
  · apply (List.isChain_map F.symm).mpr
    exact hc.imp step

private theorem segmentMap :
    (by
      classical
      exact
        ∀ (E : ℤ × ℤ ≃ ℤ × ℤ), (∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), ∀ (z : ℤ × ℤ), TriangularSignedHeight
        ((E : ℤ × ℤ → ℤ × ℤ) x) ((E : ℤ × ℤ → ℤ × ℤ) y) ((E : ℤ × ℤ → ℤ × ℤ) z) =
        TriangularSignedHeight x y z) → (∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), TriangularMaxIncrement ((E
        : ℤ × ℤ → ℤ × ℤ) x) ((E : ℤ × ℤ → ℤ × ℤ) y) = TriangularMaxIncrement x y) → (∀ (u : ℤ ×
        ℤ), ∀ (v : ℤ × ℤ), TriangularLatticeAdjacent ((E : ℤ × ℤ → ℤ × ℤ) u) ((E : ℤ × ℤ → ℤ × ℤ)
        v) ↔ TriangularLatticeAdjacent u v) → ∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), x ≠ y → ∀ (P : List
        (ℤ × ℤ)), TriangularStripSegment x y P → TriangularStripSegment ((E : ℤ × ℤ → ℤ × ℤ) x)
        ((E : ℤ × ℤ → ℤ × ℤ) y) (List.map (⇑E : ℤ × ℤ → ℤ × ℤ) P) ) := by
  classical
  intro E hH hM hAdj x y hxy P hP
  have hexy : E x ≠ E y := fun he => hxy (E.injective he)
  simp only [TriangularStripSegment,ite_eq_right hxy] at hP
  simp only [TriangularStripSegment,ite_eq_right hexy]
  refine ⟨by simp [hP.1],by simp [hP.2.1],hP.2.2.1.map E.injective,?_,?_⟩
  · intro z hz
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
    simpa [TriangularBoundaryStrip,hH,hM] using hP.2.2.2.1 u hu
  · apply (List.isChain_map E).mpr
    exact hP.2.2.2.2.imp (fun u v h => (hAdj u v).mpr h)

private theorem chamber :
    (by
      classical
      exact
        ∀ (x : Int × Int), ∀ (y : Int × Int),
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
        (y.1-x.1 ≠ 0 ∨ y.2-x.2 ≠ 0) → (∃ n : Nat, 0 < (E n y).1 ∧ 0 ≤ (E n y).2 ∧ (E n y).2 < (E n
        y).1) ) := by
  classical
  intro x y R T E hnonzero
  by_cases ha : 0 ≤ y.1-x.1
  · by_cases hb : 0 ≤ y.2-x.2
    · by_cases hba : y.2-x.2 < y.1-x.1
      · refine ⟨0,?_⟩
        simp [E,T]
        omega
      · by_cases ha0 : y.1-x.1 = 0
        · refine ⟨4,?_⟩
          norm_num [E,T,R,pow_succ,Equiv.Perm.mul_apply]
          omega
        · refine ⟨5,?_⟩
          norm_num [E,T,R,pow_succ,Equiv.Perm.mul_apply]
          omega
    · refine ⟨1,?_⟩
      norm_num [E,T,R,pow_succ,Equiv.Perm.mul_apply]
      omega
  · by_cases hb : 0 ≤ y.2-x.2
    · by_cases hb0 : y.2-x.2 = 0
      · refine ⟨3,?_⟩
        norm_num [E,T,R,pow_succ,Equiv.Perm.mul_apply]
        omega
      · refine ⟨4,?_⟩
        norm_num [E,T,R,pow_succ,Equiv.Perm.mul_apply]
        omega
    · by_cases hba : y.2-x.2 ≤ y.1-x.1
      · refine ⟨2,?_⟩
        norm_num [E,T,R,pow_succ,Equiv.Perm.mul_apply]
        omega
      · refine ⟨3,?_⟩
        norm_num [E,T,R,pow_succ,Equiv.Perm.mul_apply]
        omega

end OpposingStripProof

namespace OpposingStripDetails

private theorem hl :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (
        let l : Int → Int := fun k => (B*k)/A
        ∀ (k : ℤ), (0 : ℤ) ≤ B * k - A * l k ∧ B * k - A * l k < A) ) := by
  classical
  intro A B hA l k
  have h0 := Int.emod_nonneg (B*k) (by omega : A ≠ 0)
  have h1 := Int.emod_lt_of_pos (B*k) (by omega : 0 < A)
  have h2 := Int.emod_add_mul_ediv (B*k) A
  dsimp [l]
  omega

private theorem hh :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (
        let h : Int → Int := fun k => (B*k+A-1)/A
        ∀ (k : ℤ), (0 : ℤ) ≤ A * h k - B * k ∧ A * h k - B * k < A) ) := by
  classical
  intro A B hA h k
  have h0 := Int.emod_nonneg (B*k+A-1) (by omega : A ≠ 0)
  have h1 := Int.emod_lt_of_pos (B*k+A-1) (by omega : 0 < A)
  have h2 := Int.emod_add_mul_ediv (B*k+A-1) A
  dsimp [h]
  omega

private theorem hluniq :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (
        let l : Int → Int := fun k => (B*k)/A
        (∀ (k : Int), 0 ≤ B*k-A*l k ∧ B*k-A*l k < A) → (∀ (k : ℤ), ∀ (s : ℤ), (0 : ℤ) ≤ B * k - A
            * s ∧ B * k - A * s < A → s = l k)) ) := by
  classical
  intro A B hA l hl k s hs
  have := hl k
  have : -1 < s-l k ∧ s-l k < 1 := by constructor <;> nlinarith
  omega

private theorem hhuniq :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (
        let h : Int → Int := fun k => (B*k+A-1)/A
        (∀ (k : Int), 0 ≤ A*h k-B*k ∧ A*h k-B*k < A) → (∀ (k : ℤ), ∀ (s : ℤ), (0 : ℤ) ≤ A * s - B
            * k ∧ A * s - B * k < A → s = h k)) ) := by
  classical
  intro A B hA h hh k s hs
  have := hh k
  have : -1 < s-h k ∧ s-h k < 1 := by constructor <;> nlinarith
  omega

private theorem lnext :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (((0 : ℤ) ≤ B) → ((B < A) → (
        let l : Int → Int := fun k => (B*k)/A
        (∀ (k : Int), 0 ≤ B*k-A*l k ∧ B*k-A*l k < A) → (∀ (k : ℤ), l (k + (1 : ℤ)) = l k ∨ l (k +
            (1 : ℤ)) = l k + (1 : ℤ))))) ) := by
  classical
  intro A B hA hB hBA l hl k
  have := hl k
  have := hl (k+1)
  have : -1 < l (k+1)-l k ∧ l (k+1)-l k < 2 := by constructor <;> nlinarith
  omega

private theorem hnext :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (((0 : ℤ) ≤ B) → ((B < A) → (
        let h : Int → Int := fun k => (B*k+A-1)/A
        (∀ (k : Int), 0 ≤ A*h k-B*k ∧ A*h k-B*k < A) → (∀ (k : ℤ), h (k + (1 : ℤ)) = h k ∨ h (k +
            (1 : ℤ)) = h k + (1 : ℤ))))) ) := by
  classical
  intro A B hA hB hBA h hh k
  have := hh k
  have := hh (k+1)
  have : -1 < h (k+1)-h k ∧ h (k+1)-h k < 2 := by constructor <;> nlinarith
  omega

private theorem hmax :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (((0 : ℤ) ≤ B) → ((B < A) → (
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        (l A = B) → ((h A = B) → (TriangularMaxIncrement (0,0) (A,B) = A))))) ) := by
  classical
  intro A B hA hB hBA l h hlA hhA
  simp only [TriangularMaxIncrement, sub_zero]
  rw [abs_of_nonneg (by omega : 0 ≤ A), abs_of_nonneg hB,
    abs_of_nonneg (by omega : 0 ≤ A-B)]
  omega

private theorem hrmax :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (((0 : ℤ) ≤ B) → ((B < A) → (
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        (l A = B) → ((h A = B) → ((TriangularMaxIncrement (0,0) (A,B) = A) →
            (TriangularMaxIncrement (A,B) (0,0) = A)))))) ) := by
  classical
  intro A B hA hB hBA l h hlA hhA hmax
  simp only [TriangularMaxIncrement, zero_sub, abs_neg]
  have he : -A - -B = -(A-B) := by ring
  rw [he, abs_neg, abs_of_nonneg (by omega : 0 ≤ A), abs_of_nonneg hB,
    abs_of_nonneg (by omega : 0 ≤ A-B)]
  omega

private theorem pinj :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ),
        let h : Int → Int := fun k => (B*k+A-1)/A
        let p : Nat → Int × Int := fun k => (k, h k)
        Function.Injective p ) := by
  classical
  intro A B h p i j he
  have := congrArg Prod.fst he
  simpa [p] using this

private theorem qinj :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ),
        let l : Int → Int := fun k => (B*k)/A
        let q : Nat → Int × Int := fun k => (k, l k)
        Function.Injective q ) := by
  classical
  intro A B l q i j he
  have := congrArg Prod.fst he
  simpa [q] using this

private theorem pmem :
    (by
      classical
      exact
        ∀ (P : List (ℤ × ℤ)), ∀ (A : ℤ), ∀ (B : ℤ),
        let h : Int → Int := fun k => (B*k+A-1)/A
        (TriangularMaxIncrement (0,0) (A,B) = A) → ((TriangularMaxIncrement (A,B) (0,0) = A) → (
        let N := A.toNat
        ((N : Int) = A) → (
        let p : Nat → Int × Int := fun k => (k, h k)
        let PP := (List.range (N+1)).map p
        (PP.head? = some (0,0)) → ((PP.getLast? = some (A,B)) → ((P = PP) → ((∀ (path : List (Int
            × Int)), ∀ (a : Int × Int), ∀ (b : Int × Int), ∀ (z : Int × Int), (path.head? = some
            a) → ((path.getLast? = some b) → ((z ∈ path) → ((z ≠ a) → ((z ≠ b) → (z ∈ (path.drop
            1).dropLast)))))) → (∀ (k : ℕ), (0 : ℕ) < k ∧ k < N → p k ∈ (List.drop (1 : ℕ)
            P).dropLast))))))) ) := by
  classical
  intro P A B h hmax hrmax N hN p PP phead plast Peq interior k hk
  rw [Peq]
  apply interior PP (0,0) (A,B) (p k) phead plast
  · apply List.mem_map.mpr
    exact ⟨k, List.mem_range.mpr (by omega), rfl⟩
  · intro he; have := congrArg Prod.fst he; dsimp [p] at this; omega
  · intro he; have := congrArg Prod.fst he; dsimp [p] at this; omega

private theorem qmem :
    (by
      classical
      exact
        ∀ (Q : List (ℤ × ℤ)), ∀ (A : ℤ), ∀ (B : ℤ),
        let l : Int → Int := fun k => (B*k)/A
        (TriangularMaxIncrement (0,0) (A,B) = A) → ((TriangularMaxIncrement (A,B) (0,0) = A) → (
        let N := A.toNat
        ((N : Int) = A) → (
        let q : Nat → Int × Int := fun k => (k, l k)
        let QQ := ((List.range (N+1)).map q).reverse
        (((List.range (N+1)).map q).head? = some (0,0)) → ((((List.range (N+1)).map q).getLast? =
            some (A,B)) → ((Q = QQ) → ((∀ (path : List (Int × Int)), ∀ (a : Int × Int), ∀ (b :
            Int × Int), ∀ (z : Int × Int), (path.head? = some a) → ((path.getLast? = some b) →
            ((z ∈ path) → ((z ≠ a) → ((z ≠ b) → (z ∈ (path.drop 1).dropLast)))))) → (∀ (k : ℕ),
            (0 : ℕ) < k ∧ k < N → q k ∈ (List.drop (1 : ℕ) Q).dropLast))))))) ) := by
  classical
  intro Q A B l hmax hrmax N hN q QQ qhead qlast Qeq interior k hk
  rw [Qeq]
  apply interior QQ (A,B) (0,0) (q k)
  · simpa [QQ] using qlast
  · simpa [QQ] using qhead
  · apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
  · intro he; have := congrArg Prod.fst he; dsimp [q] at this; omega
  · intro he; have := congrArg Prod.fst he; dsimp [q] at this; omega

private theorem gap :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        (∀ (k : Int), 0 ≤ B*k-A*l k ∧ B*k-A*l k < A) → ((∀ (k : Int), 0 ≤ A*h k-B*k ∧ A*h k-B*k <
            A) → (∀ (k : ℤ), h k = l k ∨ h k = l k + (1 : ℤ)))) ) := by
  classical
  intro A B hA l h hl hh k
  have := hl k
  have := hh k
  have : -1 < h k-l k ∧ h k-l k < 2 := by constructor <;> nlinarith
  omega

private theorem between :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ), ((2 : ℤ) ≤ A) → (((0 : ℤ) ≤ B) → ((B < A) → (
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        (∀ (k : Int), 0 ≤ B*k-A*l k ∧ B*k-A*l k < A) → ((∀ (k : Int), 0 ≤ A*h k-B*k ∧ A*h k-B*k <
            A) → (∀ (k : ℤ), l (k + (1 : ℤ)) = h k ∨ l (k + (1 : ℤ)) = h k - (1 : ℤ)))))) ) := by
  classical
  intro A B hA hB hBA l h hl hh k
  have := hl (k+1)
  have := hh k
  have : -2 < l (k+1)-h k ∧ l (k+1)-h k < 1 := by constructor <;> nlinarith
  omega

private theorem below :
    (by
      classical
      exact
        ∀ (A : ℤ), ∀ (B : ℤ),
        let l : Int → Int := fun k => (B*k)/A
        let h : Int → Int := fun k => (B*k+A-1)/A
        (∀ (k : Int), l (k+1) = l k ∨ l (k+1) = l k+1) → ((∀ (k : Int), h (k+1) = h k ∨ h (k+1) =
            h k+1) → ((∀ (k : Int), h k = l k ∨ h k = l k+1) → (∀ (k : ℤ), l (k + (1 : ℤ)) = h k
            - (1 : ℤ) → h k = l k + (1 : ℤ) ∧ h (k + (1 : ℤ)) = h k))) ) := by
  classical
  intro A B l h lnext hnext gap k he
  have hg := gap k
  have hg' := gap (k+1)
  have hn := lnext k
  have hn' := hnext k
  omega

private theorem rH :
    (by
      classical
      exact
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), ∀ (z : ℤ × ℤ), TriangularSignedHeight ((R : ℤ × ℤ → ℤ × ℤ)
            a) ((R : ℤ × ℤ → ℤ × ℤ) b) ((R : ℤ × ℤ → ℤ × ℤ) z) = TriangularSignedHeight a b z )
            := by
  classical
  intro R a b z
  simp only [TriangularSignedHeight,R,Equiv.coe_fn_mk]
  ring

private theorem rM :
    (by
      classical
      exact
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), TriangularMaxIncrement ((R : ℤ × ℤ → ℤ × ℤ) a) ((R : ℤ × ℤ
            → ℤ × ℤ) b) = TriangularMaxIncrement a b ) := by
  classical
  intro R a b
  have h1 : b.1-b.2-(a.1-a.2) = (b.1-a.1)-(b.2-a.2) := by ring
  have h2 : (b.1-a.1)-(b.2-a.2)-(b.1-a.1) = -(b.2-a.2) := by ring
  simp only [TriangularMaxIncrement,R,Equiv.coe_fn_mk,h1,h2,abs_neg]
  simp only [max_comm,max_left_comm]

private theorem rAdj :
    (by
      classical
      exact
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), TriangularLatticeAdjacent ((R : ℤ × ℤ → ℤ × ℤ) a) ((R : ℤ ×
            ℤ → ℤ × ℤ) b) ↔ TriangularLatticeAdjacent a b ) := by
  classical
  intro R a b
  simp only [TriangularLatticeAdjacent,R,Equiv.coe_fn_mk,Prod.sub_def,Prod.mk.injEq]
  omega

private theorem rInc :
    (by
      classical
      exact
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        let S : AffineTriangularFace ≃ AffineTriangularFace :=
          { toFun := fun f => match f with
              | .up z => .down (R z+(1,0))
              | .down z => .up (R z-(1,0))
            invFun := fun f => match f with
              | .up z => .down (R.symm (z+(1,0)))
              | .down z => .up (R.symm (z-(1,0)))
            left_inv := by intro f; cases f <;> simp
            right_inv := by intro f; cases f <;> simp }
        ∀ (z : ℤ × ℤ), ∀ (f : AffineTriangularFace), (R : ℤ × ℤ → ℤ × ℤ) z ∈
            AffineTriangularFaceVertices ((S : AffineTriangularFace → AffineTriangularFace) f) ↔
            z ∈ AffineTriangularFaceVertices f ) := by
  classical
  intro R S z f
  cases f <;>
    simp only [S,Equiv.coe_fn_mk,AffineTriangularFaceVertices,Finset.mem_insert,
      Finset.mem_singleton,R,Prod.add_def,Prod.sub_def,Prod.ext_iff] <;> omega

private theorem tH :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), ∀ (z : ℤ × ℤ), TriangularSignedHeight ((T : ℤ × ℤ → ℤ × ℤ)
            a) ((T : ℤ × ℤ → ℤ × ℤ) b) ((T : ℤ × ℤ → ℤ × ℤ) z) = TriangularSignedHeight a b z )
            := by
  classical
  intro x T a b z
  simp [T,TriangularSignedHeight,Prod.sub_def]

private theorem tAdj :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), TriangularLatticeAdjacent ((T : ℤ × ℤ → ℤ × ℤ) a) ((T : ℤ ×
            ℤ → ℤ × ℤ) b) ↔ TriangularLatticeAdjacent a b ) := by
  classical
  intro x T a b
  simp only [TriangularLatticeAdjacent,T,Equiv.coe_fn_mk]
  rw [sub_sub_sub_cancel_right]

private theorem tInc :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        let U : AffineTriangularFace ≃ AffineTriangularFace :=
          { toFun := fun f => match f with
              | .up z => .up (z-x)
              | .down z => .down (z-x)
            invFun := fun f => match f with
              | .up z => .up (z+x)
              | .down z => .down (z+x)
            left_inv := by intro f; cases f <;> simp
            right_inv := by intro f; cases f <;> simp }
        ∀ (z : ℤ × ℤ), ∀ (f : AffineTriangularFace), (T : ℤ × ℤ → ℤ × ℤ) z ∈
            AffineTriangularFaceVertices ((U : AffineTriangularFace → AffineTriangularFace) f) ↔
            z ∈ AffineTriangularFaceVertices f ) := by
  classical
  intro x T U z f
  cases f <;>
    simp only [U,T,Equiv.coe_fn_mk,AffineTriangularFaceVertices,Finset.mem_insert,
      Finset.mem_singleton,Prod.add_def,Prod.sub_def,Prod.ext_iff] <;> omega

private theorem eH :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        (∀ (a : Int × Int), ∀ (b : Int × Int), ∀ (z : Int × Int), TriangularSignedHeight
            (R a) (R b) (R z) = TriangularSignedHeight a b z) → (
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        (∀ (a : Int × Int), ∀ (b : Int × Int), ∀ (z : Int × Int), TriangularSignedHeight (T a) (T
            b) (T z) = TriangularSignedHeight a b z) → (
        let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
        ∀ (n : ℕ), ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), ∀ (z : ℤ × ℤ), TriangularSignedHeight ((E n : ℤ
            × ℤ → ℤ × ℤ) a) ((E n : ℤ × ℤ → ℤ × ℤ) b) ((E n : ℤ × ℤ → ℤ × ℤ) z) =
            TriangularSignedHeight a b z))) := by
  classical
  intro x R rH T tH E n a b z
  induction n with
  | zero => simpa [E] using tH a b z
  | succ n ih =>
    simpa [E,pow_succ',Equiv.Perm.mul_apply] using (rH (E n a) (E n b) (E n z)).trans ih

private theorem eM :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        (∀ (a : Int × Int), ∀ (b : Int × Int), TriangularMaxIncrement (R a) (R b) =
            TriangularMaxIncrement a b) → (
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        (∀ (a : Int × Int), ∀ (b : Int × Int), TriangularMaxIncrement (T a) (T b) =
            TriangularMaxIncrement a b) → (
        let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
        ∀ (n : ℕ), ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), TriangularMaxIncrement ((E n : ℤ × ℤ → ℤ × ℤ) a)
            ((E n : ℤ × ℤ → ℤ × ℤ) b) = TriangularMaxIncrement a b))) := by
  classical
  intro x R rM T tM E n a b
  induction n with
  | zero => simpa [E] using tM a b
  | succ n ih =>
    simpa [E,pow_succ',Equiv.Perm.mul_apply] using (rM (E n a) (E n b)).trans ih

private theorem eAdj :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        (∀ (a : Int × Int), ∀ (b : Int × Int), TriangularLatticeAdjacent (R a) (R b) ↔
            TriangularLatticeAdjacent a b) → (
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        (∀ (a : Int × Int), ∀ (b : Int × Int), TriangularLatticeAdjacent (T a) (T b) ↔
            TriangularLatticeAdjacent a b) → (
        let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
        ∀ (n : ℕ), ∀ (a : ℤ × ℤ), ∀ (b : ℤ × ℤ), TriangularLatticeAdjacent ((E n : ℤ × ℤ → ℤ × ℤ)
            a) ((E n : ℤ × ℤ → ℤ × ℤ) b) ↔ TriangularLatticeAdjacent a b))) := by
  classical
  intro x R rAdj T tAdj E n a b
  induction n with
  | zero => simpa [E] using tAdj a b
  | succ n ih =>
    simpa [E,pow_succ',Equiv.Perm.mul_apply] using (rAdj (E n a) (E n b)).trans ih

private theorem eInc :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        let S : AffineTriangularFace ≃ AffineTriangularFace :=
          { toFun := fun f => match f with
              | .up z => .down (R z+(1,0))
              | .down z => .up (R z-(1,0))
            invFun := fun f => match f with
              | .up z => .down (R.symm (z+(1,0)))
              | .down z => .up (R.symm (z-(1,0)))
            left_inv := by intro f; cases f <;> simp
            right_inv := by intro f; cases f <;> simp }
        (∀ (z : Int × Int), ∀ (f : AffineTriangularFace), R z ∈
            AffineTriangularFaceVertices (S f) ↔ z ∈ AffineTriangularFaceVertices f) → (
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        let U : AffineTriangularFace ≃ AffineTriangularFace :=
          { toFun := fun f => match f with
              | .up z => .up (z-x)
              | .down z => .down (z-x)
            invFun := fun f => match f with
              | .up z => .up (z+x)
              | .down z => .down (z+x)
            left_inv := by intro f; cases f <;> simp
            right_inv := by intro f; cases f <;> simp }
        (∀ (z : Int × Int), ∀ (f : AffineTriangularFace), T z ∈ AffineTriangularFaceVertices (U
            f) ↔ z ∈ AffineTriangularFaceVertices f) → (
        let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
        let F : Nat → AffineTriangularFace ≃ AffineTriangularFace := fun n => U.trans (S^n)
        ∀ (n : ℕ), ∀ (z : ℤ × ℤ), ∀ (f : AffineTriangularFace), (E n : ℤ × ℤ → ℤ × ℤ) z ∈
            AffineTriangularFaceVertices ((F n : AffineTriangularFace → AffineTriangularFace) f)
            ↔ z ∈ AffineTriangularFaceVertices f))) := by
  classical
  intro x R S rInc T U tInc E F n z f
  induction n with
  | zero => simpa [E,F] using tInc z f
  | succ n ih =>
    simpa [E,F,pow_succ',Equiv.Perm.mul_apply] using (rInc (E n z) (F n f)).trans ih

private theorem e0 :
    (by
      classical
      exact
        ∀ (x : Int × Int),
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
        ∀ (n : ℕ), (E n : ℤ × ℤ → ℤ × ℤ) x = ((0 : ℤ), (0 : ℤ)) ) := by
  classical
  intro x R T E n
  induction n with
  | zero => ext <;> simp [E,T,Prod.sub_def]
  | succ n ih => simpa [E,pow_succ',Equiv.Perm.mul_apply,R] using congrArg R ih

private theorem hnonzero :
    (by
      classical
      exact
        ∀ (x : Int × Int), ∀ (y : Int × Int), (x ≠ y) → (y.1-x.1 ≠ 0 ∨ y.2-x.2 ≠ 0) ) := by
  classical
  intro x y hxy
  by_contra hn
  simp only [not_or,not_not] at hn
  apply hxy
  ext <;> omega

private theorem hA2 :
    (by
      classical
      exact
        ∀ (x : Int × Int), ∀ (y : Int × Int),
        let R : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => (z.1-z.2,z.1)
            invFun := fun z => (z.2,z.2-z.1)
            left_inv := fun z => by ext <;> simp
            right_inv := fun z => by ext <;> simp }
        let T : (Int × Int) ≃ (Int × Int) :=
          { toFun := fun z => z-x
            invFun := fun z => z+x
            left_inv := fun z => by simp
            right_inv := fun z => by simp }
        let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
        (∀ (n : Nat), E n x = (0,0)) → (∀ (n : ℕ), ((0 : ℤ) < ((E n : ℤ × ℤ → ℤ × ℤ) y).1) → (((0
            : ℤ) ≤ ((E n : ℤ × ℤ → ℤ × ℤ) y).2) → ((((E n : ℤ × ℤ → ℤ × ℤ) y).2 < ((E n : ℤ × ℤ →
            ℤ × ℤ) y).1) → ((¬ TriangularLatticeAdjacent (E n x) (E n y)) → (2 ≤ (E n y).1))))) )
            := by
  classical
  intro x y R T E e0 n hA hB hBA hn
  by_contra hh
  have ha1 : (E n y).1 = 1 := by omega
  have hb0 : (E n y).2 = 0 := by omega
  apply hn
  rw [e0]
  simp [TriangularLatticeAdjacent,Prod.sub_def,ha1,hb0]

end OpposingStripDetails

theorem AffineOpposingStripCorridor
    (x y : Int × Int) (hxy : x ≠ y)
    (hnadj : ¬ TriangularLatticeAdjacent x y)
    (forward reverse : List (Int × Int))
    (hforward : TriangularStripSegment x y forward)
    (hreverse : TriangularStripSegment y x reverse) :
    ∃ faces : List AffineTriangularFace,
      faces ≠ [] ∧
      (∃ f, faces.head? = some f ∧
        x ∈ AffineTriangularFaceVertices f) ∧
      (∃ f, faces.getLast? = some f ∧
        y ∈ AffineTriangularFaceVertices f) ∧
      (∀ f ∈ faces,
        (∃ a ∈ (forward.drop 1).dropLast,
          a ∈ AffineTriangularFaceVertices f) ∧
        (∃ b ∈ (reverse.drop 1).dropLast,
          b ∈ AffineTriangularFaceVertices f)) ∧
      faces.IsChain (AffineTriangularCorridorStep forward reverse) := by
-- BODY
  classical
  let P := forward
  let Q := reverse
  have hP : TriangularStripSegment x y P := hforward
  have hQ : TriangularStripSegment y x Q := hreverse
  let corridor (x y : Int × Int) (P Q : List (Int × Int)) : Prop :=
    ∃ faces : List AffineTriangularFace,
      faces ≠ [] ∧
      (∃ f, faces.head? = some f ∧ x ∈ AffineTriangularFaceVertices f) ∧
      (∃ f, faces.getLast? = some f ∧ y ∈ AffineTriangularFaceVertices f) ∧
      (∀ f ∈ faces,
        (∃ a ∈ (P.drop 1).dropLast, a ∈ AffineTriangularFaceVertices f) ∧
        (∃ b ∈ (Q.drop 1).dropLast, b ∈ AffineTriangularFaceVertices f)) ∧
      faces.IsChain (AffineTriangularCorridorStep P Q)
  -- Reconstruct the strips and concatenate the interior-column face blocks.
  have normalized (A B : Int) (hA : 2 ≤ A) (hB : 0 ≤ B) (hBA : B < A)
      (P Q : List (Int × Int))
      (hP : TriangularStripSegment (0,0) (A,B) P)
      (hQ : TriangularStripSegment (A,B) (0,0) Q) :
      corridor (0,0) (A,B) P Q := by
    classical
    let l : Int → Int := fun k => (B*k)/A
    let h : Int → Int := fun k => (B*k+A-1)/A
    have hl (k : Int) := OpposingStripDetails.hl A B hA k
    have hh (k : Int) := OpposingStripDetails.hh A B hA k
    have hluniq (k s : Int) (hs : 0 ≤ B*k-A*s ∧ B*k-A*s < A) := OpposingStripDetails.hluniq A B
        hA hl k s hs
    have hhuniq (k s : Int) (hs : 0 ≤ A*s-B*k ∧ A*s-B*k < A) := OpposingStripDetails.hhuniq A B
        hA hh k s hs
    have hl0 : l 0 = 0 := (hluniq 0 0 (by constructor <;> nlinarith)).symm
    have hh0 : h 0 = 0 := (hhuniq 0 0 (by constructor <;> nlinarith)).symm
    have hlA : l A = B := (hluniq A B (by constructor <;> nlinarith)).symm
    have hhA : h A = B := (hhuniq A B (by constructor <;> nlinarith)).symm
    have lnext (k : Int) := OpposingStripDetails.lnext A B hA
        hB hBA hl k
    have hnext (k : Int) := OpposingStripDetails.hnext A B hA
        hB hBA hh k
    have hmax := OpposingStripDetails.hmax A B hA hB hBA
        hlA hhA
    have hrmax := OpposingStripDetails.hrmax A B hA hB
        hBA hlA hhA hmax
    let N := A.toNat
    have hN : (N : Int) = A := by dsimp [N]; omega
    let p : Nat → Int × Int := fun k => (k, h k)
    let q : Nat → Int × Int := fun k => (k, l k)
    let PP := (List.range (N+1)).map p
    let QQ := ((List.range (N+1)).map q).reverse
    have p0 : p 0 = (0,0) := by simp [p, hh0]
    have q0 : q 0 = (0,0) := by simp [q, hl0]
    have pN : p N = (A,B) := by simp [p, hN, hhA]
    have qN : q N = (A,B) := by simp [q, hN, hlA]
    have pinj := OpposingStripDetails.pinj A B
    have qinj := OpposingStripDetails.qinj A B
    have phead : PP.head? = some (0,0) := by
      simp [PP, List.range_succ_eq_map, p0]
    have qhead : ((List.range (N+1)).map q).head? = some (0,0) := by
      simp [List.range_succ_eq_map, q0]
    have plast : PP.getLast? = some (A,B) := by
      simp [PP, List.range_succ, pN]
    have qlast : ((List.range (N+1)).map q).getLast? = some (A,B) := by
      simp [List.range_succ, qN]
    have ppseg := OpposingStripProof.ppseg A B hA hh
        hnext hmax hrmax hN pinj phead plast
    have qqseg := OpposingStripProof.qqseg A B hA hl
        lnext hmax hrmax hN qinj qhead qlast
    have Peq : P = PP := (AffineTriangularStrip.1 (0,0) (A,B)).unique hP ppseg
    have Qeq : Q = QQ := (AffineTriangularStrip.1 (A,B) (0,0)).unique hQ qqseg
    have interior (path : List (Int × Int)) (a b z : Int × Int)
        (ha : path.head? = some a) (hb : path.getLast? = some b)
        (hz : z ∈ path) (hza : z ≠ a) (hzb : z ≠ b) := OpposingStripProof.interior path a b z ha
            hb hz hza hzb
    have pmem (k : Nat) (hk : 0 < k ∧ k < N) := OpposingStripDetails.pmem P A B hmax hrmax hN
        phead plast Peq interior k hk
    have qmem (k : Nat) (hk : 0 < k ∧ k < N) := OpposingStripDetails.qmem Q A B hmax hrmax hN
        qhead qlast Qeq interior k hk
    have gap (k : Int) := OpposingStripDetails.gap A B hA hl hh k
    have between (k : Int) := OpposingStripDetails.between A B
        hA hB hBA hl hh k
    have below (k : Int) (he : l (k+1) = h k-1) := OpposingStripDetails.below A B lnext hnext gap
        k he
    -- A height-zero vertex requires the four-face fan instead of a two-face block.
    let block : Nat → List AffineTriangularFace := fun k =>
      if h k = l k then
        [.down (k,l k), .up (k,l k+1), .down ((k : Int)+1,l k), .up (k,h k)]
      else [.down (k,l k), .up (k,h k)]
    have bhead (k : Nat) : (block k).head? = some (.down (k,l k)) := by
      dsimp [block]; split <;> rfl
    have blast (k : Nat) : (block k).getLast? = some (.up (k,h k)) := by
      dsimp [block]; split <;> rfl
    have bne (k : Nat) : block k ≠ [] := by
      dsimp [block]; split <;> simp
    have mkstep (f g : AffineTriangularFace) (u v : Int × Int)
        (hfg : f ≠ g) (huv : u ≠ v) (hadj : TriangularLatticeAdjacent u v)
        (huf : u ∈ AffineTriangularFaceVertices f) (hvf : v ∈ AffineTriangularFaceVertices f)
        (hug : u ∈ AffineTriangularFaceVertices g) (hvg : v ∈ AffineTriangularFaceVertices g)
        (hmem : (u ∈ (P.drop 1).dropLast ∧ v ∈ (Q.drop 1).dropLast) ∨
          (u ∈ (P.drop 1).dropLast ∧ u ∈ (Q.drop 1).dropLast)) :
        AffineTriangularCorridorStep P Q f g :=
      ⟨hfg,u,v,huv,hadj,huf,hvf,hug,hvg,hmem⟩
    have bvertices (k : Nat) (hk : 0 < k ∧ k < N) := OpposingStripProof.bvertices P Q A B pmem
        qmem gap k hk
    have bchain (k : Nat) (hk : 0 < k ∧ k < N) := OpposingStripProof.bchain P Q A B
            pmem qmem gap mkstep k hk
    have joinstep (k : Nat) (hk : 0 < k ∧ k+1 < N) := OpposingStripProof.joinstep P Q A B pmem
        qmem between below mkstep k hk
    let fs : Nat → List AffineTriangularFace := fun n =>
      (List.range n).flatMap (fun i => block (i+1))
    have fsproperties (n : Nat) (hn : 0 < n ∧ n < N) := OpposingStripProof.fsproperties P Q
            A B bhead blast bne bvertices bchain joinstep n hn
    obtain ⟨hne,hhead,hlast,hvertices,hchain⟩ := fsproperties (N-1) (by omega)
    have firstlower : l 1 = 0 := (hluniq 1 0 (by constructor <;> nlinarith)).symm
    have lasthigher : h (A-1) = B :=
      (hhuniq (A-1) B (by constructor <;> nlinarith)).symm
    refine ⟨fs (N-1),hne,⟨.down (1,l 1),hhead,?_⟩,
      ⟨.up (((N-1 : Nat) : Int),h ((N-1 : Nat) : Int)),hlast,?_⟩,hvertices,hchain⟩
    · simp [AffineTriangularFaceVertices,firstlower]
    · have hn1 : ((N-1 : Nat) : Int) = A-1 := by omega
      simp [AffineTriangularFaceVertices,hn1,lasthigher,Prod.add_def]
  -- Pull back every corridor field, including endpoint-deleted memberships.
  have pullback (E : (Int × Int) ≃ (Int × Int))
      (F : AffineTriangularFace ≃ AffineTriangularFace)
      (hAdj : ∀ u v, TriangularLatticeAdjacent (E u) (E v) ↔ TriangularLatticeAdjacent u v)
      (hInc : ∀ z f, E z ∈ AffineTriangularFaceVertices (F f) ↔ z ∈ AffineTriangularFaceVertices f)
      (x y : Int × Int) (P Q : List (Int × Int))
      (hcorr : corridor (E x) (E y) (P.map E) (Q.map E)) := OpposingStripProof.pullback E F hAdj
          hInc x y P Q hcorr
  have segmentMap (E : (Int × Int) ≃ (Int × Int))
      (hH : ∀ x y z, TriangularSignedHeight (E x) (E y) (E z) = TriangularSignedHeight x y z)
      (hM : ∀ x y, TriangularMaxIncrement (E x) (E y) = TriangularMaxIncrement x y)
      (hAdj : ∀ u v, TriangularLatticeAdjacent (E u) (E v) ↔ TriangularLatticeAdjacent u v)
      (x y : Int × Int) (hxy : x ≠ y) (P : List (Int × Int))
      (hP : TriangularStripSegment x y P) := OpposingStripProof.segmentMap E hH hM hAdj x y hxy P hP
  change corridor x y P Q
  -- Translation and the six powers of the determinant-one lattice rotation.
  let R : (Int × Int) ≃ (Int × Int) :=
    { toFun := fun z => (z.1-z.2,z.1)
      invFun := fun z => (z.2,z.2-z.1)
      left_inv := fun z => by ext <;> simp
      right_inv := fun z => by ext <;> simp }
  let S : AffineTriangularFace ≃ AffineTriangularFace :=
    { toFun := fun f => match f with
        | .up z => .down (R z+(1,0))
        | .down z => .up (R z-(1,0))
      invFun := fun f => match f with
        | .up z => .down (R.symm (z+(1,0)))
        | .down z => .up (R.symm (z-(1,0)))
      left_inv := by intro f; cases f <;> simp
      right_inv := by intro f; cases f <;> simp }
  have rH (a b z : Int × Int) := OpposingStripDetails.rH a b z
  have rM (a b : Int × Int) := OpposingStripDetails.rM a b
  have rAdj (a b : Int × Int) := OpposingStripDetails.rAdj a b
  have rInc (z : Int × Int) (f : AffineTriangularFace) := OpposingStripDetails.rInc z f
  let T : (Int × Int) ≃ (Int × Int) :=
    { toFun := fun z => z-x
      invFun := fun z => z+x
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
  let U : AffineTriangularFace ≃ AffineTriangularFace :=
    { toFun := fun f => match f with
        | .up z => .up (z-x)
        | .down z => .down (z-x)
      invFun := fun f => match f with
        | .up z => .up (z+x)
        | .down z => .down (z+x)
      left_inv := by intro f; cases f <;> simp
      right_inv := by intro f; cases f <;> simp }
  have tH (a b z : Int × Int) := OpposingStripDetails.tH x a b z
  have tM (a b : Int × Int) : TriangularMaxIncrement (T a) (T b) = TriangularMaxIncrement a b := by
    simp [T,TriangularMaxIncrement,Prod.sub_def]
  have tAdj (a b : Int × Int) := OpposingStripDetails.tAdj x a b
  have tInc (z : Int × Int) (f : AffineTriangularFace) := OpposingStripDetails.tInc x z f
  let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R^n)
  let F : Nat → AffineTriangularFace ≃ AffineTriangularFace := fun n => U.trans (S^n)
  have eH (n : Nat) (a b z : Int × Int) := OpposingStripDetails.eH x rH tH n a b z
  have eM (n : Nat) (a b : Int × Int) := OpposingStripDetails.eM x rM tM n a b
  have eAdj (n : Nat) (a b : Int × Int) := OpposingStripDetails.eAdj x rAdj tAdj n a b
  have eInc (n : Nat) (z : Int × Int) (f : AffineTriangularFace) := OpposingStripDetails.eInc x
      rInc tInc n z f
  have e0 (n : Nat) := OpposingStripDetails.e0 x n
  have hnonzero := OpposingStripDetails.hnonzero x y hxy
  have chamber := OpposingStripProof.chamber x y hnonzero
  obtain ⟨n,hA,hB,hBA⟩ := chamber
  have hn : ¬ TriangularLatticeAdjacent (E n x) (E n y) :=
    fun hh => hnadj ((eAdj n x y).mp hh)
  have hA2 := OpposingStripDetails.hA2 x y e0 n hA hB hBA hn
  have hp := segmentMap (E n) (eH n) (eM n) (eAdj n) x y hxy P hP
  have hq := segmentMap (E n) (eH n) (eM n) (eAdj n) y x (Ne.symm hxy) Q hQ
  apply pullback (E n) (F n) (eAdj n) (eInc n) x y P Q
  have he : E n y = ((E n y).1,(E n y).2) := rfl
  rw [e0,he] at hp hq ⊢
  exact normalized _ _ hA2 hB hBA _ _ hp hq

end ApollonianSuperharmonic

end

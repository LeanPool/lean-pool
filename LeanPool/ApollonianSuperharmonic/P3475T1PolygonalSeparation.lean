/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3475T1TriangleTree
public import LeanPool.ApollonianSuperharmonic.P3381T1PiecewiseAffinePolygonModel

-- [TABLET NODE: P3475T1PolygonalSeparation]

/-!
# P3475T1PolygonalSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PolygonalSeparationProof

private theorem hintpath :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), (P3475T1TriangleTree p X K) → (∀ (h : (↑X : Type) ≃ₜ (↑K : Type)),
            (∀ x : X, ((x : Real × Real) ∈ interior X) ↔ ((h x : Real × Real) ∈ interior K)) →
            (IsPathConnected (interior X)))
    ) := by
  classical
  intro n p X K t h hiff
  let S : Set X := {x | (x : Real × Real) ∈ interior X}
  let T : Set K := {y | (y : Real × Real) ∈ interior K}
  let H : S ≃ₜ T := h.subtype hiff
  have hKconv : Convex Real (interior K) := t.target_convex.interior
  have hKne : (interior K).Nonempty := t.target_interior
  have himageT : (Subtype.val '' T) = interior K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, interior_subset hy⟩, hy, rfl⟩
  have hTp : IsPathConnected T := by
    apply (Topology.IsInducing.isPathConnected_iff (f := Subtype.val)
      (hf := Topology.IsInducing.subtypeVal) (F := T)).mpr
    rw [himageT]
    exact hKconv.isPathConnected hKne
  have hSp : IsPathConnected S := by
    have hTspace : PathConnectedSpace T := isPathConnected_iff_pathConnectedSpace.mp hTp
    have hunivT : IsPathConnected (Set.univ : Set T) := pathConnectedSpace_iff_univ.mp hTspace
    have hunivS : IsPathConnected (Set.univ : Set S) := by
      simpa [Set.image_univ, H.symm.surjective.range_eq] using
        H.symm.isPathConnected_image.mpr hunivT
    have hSspace : PathConnectedSpace S := pathConnectedSpace_iff_univ.mpr hunivS
    exact isPathConnected_iff_pathConnectedSpace.mpr hSspace
  have himg : (Subtype.val '' S) = interior X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩
  rw [← himg]
  exact (Topology.IsInducing.isPathConnected_iff (f := Subtype.val)
    (hf := Topology.IsInducing.subtypeVal) (F := S)).mp hSp

private theorem bcombo :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3475T1TriangleTree p X K), ∀ (b : Fin t.count → ℝ × ℝ → Fin
            (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j = (1 :
            ℝ)) → ((∀ (k : Fin t.count), ∀ (z : ℝ × ℝ), ∑ j : Fin (3 : ℕ), b k z j • p.vertex
            (t.face k j) = z) → ((∀ (k : Fin t.count), ∀ (w : Fin (3 : ℕ) → ℝ), ∑ j : Fin (3 :
            ℕ), w j = (1 : ℝ) → b k (∑ j : Fin (3 : ℕ), w j • p.vertex (t.face k j)) = w) → (∀
            {ι : Type}, ∀ [inst : Fintype ι], ∀ (k : Fin t.count), ∀ (w : ι → ℝ), ∀ (f : ι → ℝ ×
            ℝ), ∑ r : ι, w r = (1 : ℝ) → ∀ (j : Fin (3 : ℕ)), b k (∑ r : ι, w r • f r) j = ∑ r :
            ι, w r * b k (f r) j)))
    ) := by
  classical
  intro n p X K t b bsum breconstruct bunique ι typeclassInstance0 k w f hw j
  let W : Fin 3 → Real := fun j => ∑ r, w r * b k (f r) j
  have hW : (∑ j, W j) = 1 := by
    simp only [W]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, bsum, mul_one]
    exact hw
  have hWz : (∑ j, W j • p.vertex (t.face k j)) = ∑ r, w r • f r := by
    simp only [W, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp_rw [mul_smul, ← Finset.smul_sum, breconstruct]
  have h := bunique k W hW
  rw [hWz] at h
  exact congrFun h j

private theorem contains :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3475T1TriangleTree p X K), ∀ (i : Fin (n + (3 : ℕ))), ∀ (u
            : ℝ), (0 < u) → ((u < 1) → (∀ (b : Fin t.count → ℝ × ℝ → Fin (3 : ℕ) → ℝ), (∀ (k :
            Fin t.count), ∀ (l : Fin t.count), ∀ z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
            (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))), ∀ (j : Fin (3 : ℕ)),
            t.face k j ∉ Set.range (t.face l) → b k z j = (0 : ℝ)) → (
        let D (k : Fin t.count) :=
          convexHull Real (Set.range (p.vertex ∘ t.face k))
        let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧
          i + 1 ∈ Set.range (t.face k)}
        ∀ (k : Fin t.count), ∀ (a : Fin (3 : ℕ)), (t.face k a = i) → (∀ (d : Fin (3 : ℕ)),
            (t.face k d = i + (1 : Fin (n + (3 : ℕ)))) → (
        let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex (i + 1)
        (b k z a = 1 - u) → ((b k z d = u) → ((z ∈ D k) → (∀ (l : Fin t.count), z ∈ D l → l ∈
            I))))))))
    ) := by
  classical
  intro n p X K t i u hu0' hu1' b bcommon D I k a ha d hd z hza hzd hzDk l hzl
  have hcommon : z ∈ convexHull Real
      (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))) := by
    rw [← t.source_intersection]
    exact ⟨hzDk, hzl⟩
  constructor
  · by_contra hi
    have hz0 := bcommon k l z hcommon a (by
      intro hface
      obtain ⟨m, hm⟩ := hface
      exact hi ⟨m, hm.trans ha⟩)
    rw [hza] at hz0
    linarith
  · by_contra hj
    have hz0 := bcommon k l z hcommon d (by
      intro hface
      obtain ⟨m, hm⟩ := hface
      exact hj ⟨m, hm.trans hd⟩)
    rw [hzd] at hz0
    linarith

private theorem hlocalchar :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3475T1TriangleTree p X K), ∀ (i : Fin (n + (3 : ℕ))), ∀ (u
            : ℝ), ∀ (b : Fin t.count → ℝ × ℝ → Fin (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (z : ℝ ×
            ℝ), z ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range (p.vertex ∘ t.face k))
            ↔ ∀ (j : Fin (3 : ℕ)), (0 : ℝ) ≤ b k z j) → (
        let D (k : Fin t.count) :=
          convexHull Real (Set.range (p.vertex ∘ t.face k))
        (∀ (a : Fin 3), ∀ (d : Fin 3), ∀ (c : Fin 3), (a ≠ d) → ((a ≠ c) → ((d ≠ c) → (∀ (j : Fin
            3), j = a ∨ j = d ∨ j = c)))) → (∀ (k : Fin t.count), ∀ (a : Fin (3 : ℕ)), (t.face k
            a = i) → (∀ (d : Fin (3 : ℕ)), (t.face k d = i + (1 : Fin (n + (3 : ℕ)))) → ((a ≠ d)
            → (∀ (c : Fin (3 : ℕ)), (a ≠ c) → ((d ≠ c) → ((p.vertex i = p.vertex (t.face k a)) →
            ((p.vertex (i + 1) = p.vertex (t.face k d)) → (((1 - u) • p.vertex i + u • p.vertex
            (i + 1) = (1 - u) • p.vertex (t.face k a) + u • p.vertex (t.face k d)) → ((b k ((1 -
            u) • p.vertex i + u • p.vertex (i + 1)) a = 1 - u) → ((b k ((1 - u) • p.vertex i + u
            • p.vertex (i + 1)) d = u) → ((b k ((1 - u) • p.vertex i + u • p.vertex (i + 1)) c =
            0) → (
        let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex (i + 1)
        (b k z a = 1 - u) → ((b k z d = u) → ((b k z c = 0) → (
        let N : Set (Real × Real) := ⋂ l,
          if l = k then Set.univ else (D l)ᶜ
        let Q : Set (Real × Real) := N ∩ {y | 0 < b k y a ∧ 0 < b k y d}
        (IsOpen Q) → ((z ∈ Q) → (∀ (r : ℝ), (Metric.ball z r ⊆ Q) → (∀ y ∈ Metric.ball z r, y ∈ X
            ↔ (0 : ℝ) ≤ b k y c)))))))))))))))))))
    ) := by
  classical
  intro n p X K t i u b bhull D indices k a ha d hd had c hac hdc hvA hvD hpoint hzcoordA
      hzcoordD hzcoordC z hza hzd hzc N Q hQopen hzQ r hball y hy
  have hyQ := hball hy
  constructor
  · intro hyX
    rw [t.source_cover] at hyX
    obtain ⟨l, hyl⟩ := Set.mem_iUnion.mp hyX
    have hlk : l = k := by
      by_contra hl
      have hnot := (Set.mem_iInter.mp hyQ.1) l
      simp only [hl, ite_false] at hnot
      exact hnot hyl
    have hyk : y ∈ D k := by simpa [D, hlk] using hyl
    exact (bhull k y).mp hyk c
  · intro hyc
    rw [t.source_cover]
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    apply (bhull k y).mpr
    intro j
    have hpos := hyQ.2
    rcases indices a d c had hac hdc j with rfl | rfl | rfl
    · exact hpos.1.le
    · exact hpos.2.le
    · exact hyc

private theorem hhalf :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3475T1TriangleTree p X K), ∀ (u : ℝ), (0 < u) → ((u < 1) →
            (∀ (b : Fin t.count → ℝ × ℝ → Fin (3 : ℕ) → ℝ), (∀ (k : Fin t.count), ∀ (x : Real ×
            Real), ∀ (y : Real × Real), ∀ (a : Real), ∀ (d : Real), (a + d = 1) → (∀ (j : Fin 3),
            b k (a • x + d • y) j = a * b k x j + d * b k y j)) → (∀ (k : Fin t.count), ∀ (c :
            Fin (3 : ℕ)), Convex Real {y : Real × Real | b k y c < 0})))
    ) := by
  classical
  intro n p X K t u hu0' hu1' b blinear k c x hx y hy a' d' ha' hd' had'
  change b k (a' • x + d' • y) c < 0
  rw [blinear k x y a' d' had' c]
  by_contra hnot
  have hnonneg : 0 ≤ a' * b k x c + d' * b k y c := le_of_not_gt hnot
  by_cases ha0 : a' = 0
  · have hdpos : 0 < d' := by rw [ha0, zero_add] at had'; linarith
    have hterm : d' * b k y c < 0 := mul_neg_of_pos_of_neg hdpos hy
    simp [ha0] at hnonneg
    linarith
  · have hapos : 0 < a' := lt_of_le_of_ne ha' (Ne.symm ha0)
    have hterm : a' * b k x c < 0 := mul_neg_of_pos_of_neg hapos hx
    have hother : d' * b k y c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd' hy.le
    linarith

private theorem hCpre :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
        IsPreconnected C
    ) := by
  classical
  intro n p C
  let edge : Fin (n + 3) → Set (Real × Real) := fun i =>
    segment Real (p.vertex i) (p.vertex (i + 1))
  have hedges : (⋃ i, edge i) = C := by rfl
  have hpre : ∀ i, IsPreconnected (edge i) := by
    intro i
    exact (convex_segment (p.vertex i) (p.vertex (i + 1))).isPreconnected
  let R : Fin (n + 3) → Fin (n + 3) → Prop := fun i j => (edge i ∩ edge j).Nonempty
  have hstep : ∀ i, R i (i + 1) := by
    intro i
    refine ⟨p.vertex (i + 1), ?_, ?_⟩
    · change p.vertex (i + 1) ∈ segment Real (p.vertex i) (p.vertex (i + 1))
      exact right_mem_segment Real (p.vertex i) (p.vertex (i + 1))
    · change p.vertex (i + 1) ∈ segment Real (p.vertex (i + 1)) (p.vertex ((i + 1) + 1))
      exact left_mem_segment Real (p.vertex (i + 1)) (p.vertex ((i + 1) + 1))
  have hRsymm : ∀ i j, R i j → R j i := by
    intro i j h
    obtain ⟨x, hxi, hxj⟩ := h
    exact ⟨x, hxj, hxi⟩
  have hreachSymm : ∀ i j, Relation.ReflTransGen R i j →
      Relation.ReflTransGen R j i := by
    intro i j hij
    induction hij with
    | refl => exact Relation.ReflTransGen.refl
    | @tail k l hkl hstep ih =>
        exact (Relation.ReflTransGen.single (hRsymm k l hstep)).trans ih
  have hreach : ∀ k : Nat, ∀ hk : k < n + 3,
      Relation.ReflTransGen R (0 : Fin (n + 3)) ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact Relation.ReflTransGen.refl
    | succ k ih =>
        intro hk
        have hk' : k < n + 3 := Nat.lt_trans (Nat.lt_succ_self k) hk
        let i : Fin (n + 3) := ⟨k, hk'⟩
        let j : Fin (n + 3) := ⟨k + 1, hk⟩
        have hij : i + 1 = j := by
          apply Fin.ext
          change (k + 1) % (n + 3) = k + 1
          exact Nat.mod_eq_of_lt hk
        have hr := ih hk'
        have hrel : R i j := hij ▸ hstep i
        simpa [i, j] using hr.tail hrel
  have hconn : ∀ i j : Fin (n + 3), Relation.ReflTransGen R i j := by
    intro i j
    have hi := hreach i.val i.isLt
    have hj := hreach j.val j.isLt
    have hi' : Relation.ReflTransGen R (0 : Fin (n + 3)) i := by simpa using hi
    have hj' : Relation.ReflTransGen R (0 : Fin (n + 3)) j := by simpa using hj
    exact (hreachSymm _ _ hi').trans hj'
  rw [← hedges]
  exact IsPreconnected.iUnion_of_reflTransGen hpre hconn

private theorem hVpre :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)),
        let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
        (frontier X = C) → ((IsOpen Xᶜ) → ((∀ x, x ∈ frontier X → ∃ N : Set (Real × Real), IsOpen
            N ∧ x ∈ N ∧ IsPreconnected (N \ X)) → ((IsPreconnected C) → (IsPreconnected Xᶜ))))
    ) := by
  classical
  intro n p X C hfrontierC hopenV hlocalAll hCpre
  apply isPreconnected_iff_subset_of_disjoint.mpr
  intro u v hu hv hcoverUV hdisjUV
  by_contra hnot
  simp only [not_or, Set.not_subset] at hnot
  obtain ⟨⟨x, hx, hxnot⟩, ⟨y, hy, hynot⟩⟩ := hnot
  have hxv : x ∈ v := (hcoverUV hx).resolve_left hxnot
  have hyu : y ∈ u := (hcoverUV hy).resolve_right hynot
  let U := Xᶜ ∩ u
  let V := Xᶜ ∩ v
  have hcov : U ∪ V = Xᶜ := by
    apply Set.Subset.antisymm
    · rintro z (hz | hz) <;> exact hz.1
    · intro z hz
      rcases hcoverUV hz with hzu | hzv
      · exact Or.inl ⟨hz, hzu⟩
      · exact Or.inr ⟨hz, hzv⟩
  have hd : Disjoint U V := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hz, hzu⟩ ⟨_, hzv⟩
    have hmem : z ∈ Xᶜ ∩ (u ∩ v) := ⟨hz, hzu, hzv⟩
    rw [hdisjUV] at hmem
    exact hmem
  have hU : IsOpen U := hopenV.inter hu
  have hV : IsOpen V := hopenV.inter hv
  have hneU : U.Nonempty := ⟨y, hy, hyu⟩
  have hneV : V.Nonempty := ⟨x, hx, hxv⟩
  have hsubU : U ⊆ Xᶜ := fun _ hz => hz.1
  have hsubV : V ⊆ Xᶜ := fun _ hz => hz.1
  have hclU : closure U ⊆ Vᶜ :=
    closure_minimal (Set.disjoint_left.mp hd) hV.isClosed_compl
  have hclV : closure V ⊆ Uᶜ :=
    closure_minimal (Set.disjoint_left.mp hd.symm) hU.isClosed_compl
  have hseparate : frontier X ∩ (closure U ∩ closure V) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hzU, hzV⟩
    obtain ⟨N, hN, hzN, hcN⟩ := hlocalAll z hz
    have hNc : N \ X ⊆ U ∪ V := by
      intro q hq
      rw [hcov]
      exact hq.2
    have hNd : (N \ X) ∩ (U ∩ V) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro q ⟨_, hqU, hqV⟩
      exact (Set.disjoint_left.mp hd) hqU hqV
    rcases isPreconnected_iff_subset_of_disjoint.mp hcN U V hU hV hNc hNd with h | h
    · obtain ⟨q, hqN, hqV⟩ := mem_closure_iff.mp hzV N hN hzN
      exact (Set.disjoint_left.mp hd) (h ⟨hqN, hsubV hqV⟩) hqV
    · obtain ⟨q, hqN, hqU⟩ := mem_closure_iff.mp hzU N hN hzN
      exact (Set.disjoint_left.mp hd) hqU (h ⟨hqN, hsubU hqU⟩)
  have hfrontcover : frontier X ⊆ closure U ∪ closure V := by
    rw [← closure_union, hcov, ← frontier_compl]
    exact frontier_subset_closure
  have hfrontUsub : frontier U ⊆ frontier X := by
    intro z hz
    have hzcl : z ∈ closure Xᶜ := closure_mono hsubU (frontier_subset_closure hz)
    have hznot : z ∉ Xᶜ := by
      intro he
      have he' : z ∈ U ∪ V := by rw [hcov]; exact he
      rcases he' with hzu | hzv
      · exact hz.2 (hU.interior_eq.symm ▸ hzu)
      · exact hclU (frontier_subset_closure hz) hzv
    rw [← frontier_compl, frontier, hopenV.interior_eq]
    exact ⟨hzcl, hznot⟩
  have hfrontVsub : frontier V ⊆ frontier X := by
    intro z hz
    have hzcl : z ∈ closure Xᶜ := closure_mono hsubV (frontier_subset_closure hz)
    have hznot : z ∉ Xᶜ := by
      intro he
      have he' : z ∈ U ∪ V := by rw [hcov]; exact he
      rcases he' with hzu | hzv
      · exact hclV (frontier_subset_closure hz) hzu
      · exact hz.2 (hV.interior_eq.symm ▸ hzv)
    rw [← frontier_compl, frontier, hopenV.interior_eq]
    exact ⟨hzcl, hznot⟩
  have hnotU : U ≠ Set.univ := by
    intro he
    obtain ⟨z, hz⟩ := hneV
    exact (Set.disjoint_left.mp hd) (he.symm ▸ Set.mem_univ z) hz
  have hnotV : V ≠ Set.univ := by
    intro he
    obtain ⟨z, hz⟩ := hneU
    exact (Set.disjoint_left.mp hd) hz (he.symm ▸ Set.mem_univ z)
  have hfrontcoverC : C ⊆ closure U ∪ closure V := by
    simpa only [hfrontierC] using hfrontcover
  have hseparateC : C ∩ (closure U ∩ closure V) = ∅ := by
    simpa only [hfrontierC] using hseparate
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hCpre
      (closure U) (closure V) isClosed_closure isClosed_closure
      hfrontcoverC hseparateC with h | h
  · obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨hneV, hnotV⟩
    have hzX := hfrontVsub hz
    have hzC : z ∈ C := by rw [← hfrontierC]; exact hzX
    have hbad : z ∈ C ∩ (closure U ∩ closure V) :=
      ⟨hzC, h hzC, frontier_subset_closure hz⟩
    rw [hseparateC] at hbad
    exact hbad
  · obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨hneU, hnotU⟩
    have hzX := hfrontUsub hz
    have hzC : z ∈ C := by rw [← hfrontierC]; exact hzX
    have hbad : z ∈ C ∩ (closure U ∩ closure V) :=
      ⟨hzC, frontier_subset_closure hz, h hzC⟩
    rw [hseparateC] at hbad
    exact hbad

private theorem hfrontU :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), (P3475T1TriangleTree p X K) → (
        let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
        (frontier X = C) → (∀ [IsClosed X], ∀ (h : (↑X : Type) ≃ₜ (↑K : Type)), (∀ x :
            X, ((x : Real × Real) ∈ interior X) ↔ ((h x : Real × Real) ∈ interior K)) → (frontier
            (interior X) = C)))
    ) := by
  classical
  intro n p X K t C hfrontierC hclosed h hiff
  have himageS :
      (h '' {x : X | (x : Real × Real) ∈ interior X}) =
        {y : K | (y : Real × Real) ∈ interior K} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hiff x).mp hx
    · intro hy
      refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
      exact (hiff (h.symm y)).mpr (by simpa using hy)
  let S : Set X := {x | (x : Real × Real) ∈ interior X}
  let T : Set K := {y | (y : Real × Real) ∈ interior K}
  have himageT : (Subtype.val '' T) = interior K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, interior_subset hy⟩, hy, rfl⟩
  have hKreg : closure (interior K) = K := by
    rw [t.target_convex.closure_interior_eq_closure_of_nonempty_interior t.target_interior,
      t.target_closed.closure_eq]
  have hTdense : closure T = Set.univ := by
    ext y
    rw [closure_subtype, himageT, hKreg]
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact y.property
  have hSdense : closure S = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : h x ∈ h '' closure S := by
      rw [h.image_closure S, himageS, hTdense]
      exact Set.mem_univ _
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := h.injective hyx
    simpa [this] using hy
  have himageSval : (Subtype.val '' S) = interior X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩
  have hXdense : X ⊆ closure (interior X) := by
    intro x hx
    have hxS : (⟨x, hx⟩ : X) ∈ closure S := by rw [hSdense]; exact Set.mem_univ _
    rw [closure_subtype, himageSval] at hxS
    exact hxS
  have hreg : closure (interior X) = X := by
    apply Set.Subset.antisymm
    · exact closure_minimal interior_subset hclosed
    · exact hXdense
  simpa [frontier, hreg, interior_interior, hclosed.closure_eq] using hfrontierC

private theorem hX :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)),
        let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
        (frontier X = C) → (∀ [IsClosed X], X = interior X ∪ C)
    ) := by
  classical
  intro n p X C hfrontierC hclosed
  ext z
  rw [← hfrontierC]
  constructor
  · intro hzX
    by_cases hzI : z ∈ interior X
    · exact Or.inl hzI
    · exact Or.inr ⟨by rw [hclosed.closure_eq]; exact hzX, hzI⟩
  · rintro (hzI | hzF)
    · exact interior_subset hzI
    · exact hclosed.frontier_subset hzF

end PolygonalSeparationProof

namespace PolygonalSeparationDetails

private theorem hiff :
    (by
      classical
      exact
        ∀ (X : Set (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (h : (↑X : Type) ≃ₜ (↑K : Type)),
            (∀ (x : (↑X : Type)), (↑x : ℝ × ℝ) ∈ frontier X ↔ (↑((h : (↑X : Type) → (↑K : Type))
            x) : ℝ × ℝ) ∈ frontier K) → (∀ x : X, ((x : Real × Real) ∈ interior X) ↔ ((h x : Real
            × Real) ∈ interior K)) ) := by
  classical
  intro X K h hboundary x
  rw [mem_interior_iff_notMem_frontier x.property,
      mem_interior_iff_notMem_frontier (h x).property]
  exact not_congr (hboundary x)

private theorem hlocalAll :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3475T1TriangleTree p X K),
        let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
        (∀ (i : Fin (n + (3 : ℕ))), ∃ (r : ℝ), (0 : ℝ) < r ∧ (∀ z ∈ Metric.ball (p.vertex i) r, z
            ∈ X ↔ ∃ (k : Fin t.count), i ∈ Set.range (t.face k) ∧ ∃ (w : Fin (3 : ℕ) → ℝ), (∀ (j
            : Fin (3 : ℕ)), (0 : ℝ) ≤ w j) ∧ z = p.vertex i + ∑ j : Fin (3 : ℕ), w j • (p.vertex
            (t.face k j) - p.vertex i)) ∧ IsPathConnected (Metric.ball (p.vertex i) r ∩ interior
            X) ∧ IsPathConnected (Metric.ball (p.vertex i) r \ X)) → ((frontier X = C) → (∀ x, x
            ∈ frontier X → ∃ N : Set (Real × Real), IsOpen N ∧ x ∈ N ∧ IsPreconnected (N \ X))) )
            := by
  classical
  intro n p X K t C hlocal hfrontierC
  obtain ⟨coordinates, vertex_incidence⟩ :=
    P5662T1TriangulationBarycentricCoordinates p X K t.toP3381T1PairedTriangulation
  intro z hz
  rw [hfrontierC] at hz
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
  rw [segment_eq_image] at hzi
  obtain ⟨u, hu, rfl⟩ := hzi
  by_cases hu0 : u = 0
  · subst u
    simp only [zero_smul, one_smul, sub_zero, add_zero]
    obtain ⟨r, hr, _, _, hexterior⟩ := hlocal i
    refine ⟨Metric.ball (p.vertex i) r, Metric.isOpen_ball,
      (by simpa only [zero_add] using Metric.mem_ball_self (x := p.vertex i) hr), ?_⟩
    exact hexterior.isConnected.isPreconnected
  · by_cases hu1 : u = 1
    · subst u
      simp only [one_smul, sub_self, zero_smul, zero_add]
      obtain ⟨r, hr, _, _, hexterior⟩ := hlocal (i + 1)
      refine ⟨Metric.ball (p.vertex (i + 1)) r, Metric.isOpen_ball,
        (by simpa only [zero_add] using
          Metric.mem_ball_self (x := p.vertex (i + 1)) hr), ?_⟩
      exact hexterior.isConnected.isPreconnected
    · have hu0' : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hu1' : u < 1 := lt_of_le_of_ne hu.2 hu1
      have hij : i ≠ i + 1 := by
        intro hi
        have hzero : (0 : Fin (n + 3)) = 1 :=
          add_left_cancel (show i + 0 = i + 1 by simp at hi)
        exact Fin.zero_ne_one hzero
      obtain ⟨b, bsum, breconstruct, bunique, bcontinuous, bhull, bvertex, bcommon⟩ :=
        coordinates
      let D (k : Fin t.count) :=
        convexHull Real (Set.range (p.vertex ∘ t.face k))
      have closedD (k : Fin t.count) : IsClosed (D k) :=
        ((Set.finite_range (p.vertex ∘ t.face k)).isCompact_convexHull Real).isClosed
      have third (a d : Fin 3) (had : a ≠ d) : ∃ c : Fin 3, a ≠ c ∧ d ≠ c := by
        fin_cases a <;> fin_cases d
        all_goals first | exact (had rfl).elim | decide
      have indices (a d c : Fin 3) (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c)
          (j : Fin 3) : j = a ∨ j = d ∨ j = c := by
        fin_cases a <;> fin_cases d <;> fin_cases c <;> fin_cases j
        all_goals first
          | exact (had rfl).elim
          | exact (hac rfl).elim
          | exact (hdc rfl).elim
          | decide
      have bcombo {ι : Type} [Fintype ι] (k : Fin t.count)
          (w : ι → Real) (f : ι → Real × Real) (hw : (∑ r, w r) = 1)
          (j : Fin 3) :
          b k (∑ r, w r • f r) j = ∑ r, w r * b k (f r) j := PolygonalSeparationProof.bcombo n
              p X K t b bsum breconstruct bunique (ι := ι) k w f hw j
      have blinear (k : Fin t.count) (x y : Real × Real) (a d : Real)
          (had : a + d = 1) (j : Fin 3) :
          b k (a • x + d • y) j = a * b k x j + d * b k y j := by
        let w : Fin 2 → Real := ![a, d]
        let f : Fin 2 → Real × Real := ![x, y]
        have hw : (∑ r, w r) = 1 := by simpa [Fin.sum_univ_two, w] using had
        simpa [Fin.sum_univ_two, w, f] using bcombo (ι := Fin 2) k w f hw j
      let I : Set (Fin t.count) := {k | i ∈ Set.range (t.face k) ∧
        i + 1 ∈ Set.range (t.face k)}
      have hcount := t.edge_count i (i + 1) hij
      have hcount1 : I.ncard = 1 := by
        dsimp [I]
        simpa using hcount
      obtain ⟨k, hIeq⟩ := Set.ncard_eq_one.mp hcount1
      have hkI : k ∈ I := by rw [hIeq]; simp
      obtain ⟨a, ha⟩ := hkI.1
      obtain ⟨d, hd⟩ := hkI.2
      have had : a ≠ d := by
        intro he
        apply hij
        calc
          i = t.face k a := ha.symm
          _ = t.face k d := congrArg (t.face k) he
          _ = i + 1 := hd
      obtain ⟨c, hac, hdc⟩ := third a d had
      have hvA : p.vertex i = p.vertex (t.face k a) := congrArg p.vertex ha.symm
      have hvD : p.vertex (i + 1) = p.vertex (t.face k d) := congrArg p.vertex hd.symm
      have hpoint :
          (1 - u) • p.vertex i + u • p.vertex (i + 1) =
            (1 - u) • p.vertex (t.face k a) + u • p.vertex (t.face k d) := by
        calc
          _ = (1 - u) • p.vertex (t.face k a) + u • p.vertex (i + 1) :=
            congrArg (fun q => (1 - u) • q + u • p.vertex (i + 1)) hvA
          _ = _ := congrArg (fun q => (1 - u) • p.vertex (t.face k a) + u • q) hvD
      have hzcoordA : b k ((1 - u) • p.vertex i + u • p.vertex (i + 1)) a = 1 - u := by
        rw [hpoint, blinear k _ _ _ _ (by ring), bvertex, bvertex]
        simp [had]
      have hzcoordD : b k ((1 - u) • p.vertex i + u • p.vertex (i + 1)) d = u := by
        rw [hpoint, blinear k _ _ _ _ (by ring), bvertex, bvertex]
        simp [Ne.symm had]
      have hzcoordC : b k ((1 - u) • p.vertex i + u • p.vertex (i + 1)) c = 0 := by
        rw [hpoint, blinear k _ _ _ _ (by ring), bvertex, bvertex]
        simp [Ne.symm hac, Ne.symm hdc]
      let z : Real × Real := (1 - u) • p.vertex i + u • p.vertex (i + 1)
      have hza : b k z a = 1 - u := hzcoordA
      have hzd : b k z d = u := hzcoordD
      have hzc : b k z c = 0 := hzcoordC
      have hzDk : z ∈ D k := by
        apply (bhull k z).mpr
        intro j
        rcases indices a d c had hac hdc j with rfl | rfl | rfl
        · rw [hza]
          exact sub_nonneg.mpr hu1'.le
        · rw [hzd]
          exact hu0'.le
        · rw [hzc]
      have contains (l : Fin t.count) (hzl : z ∈ D l) : l ∈ I :=
          PolygonalSeparationProof.contains n p X K t i u hu0' hu1' b bcommon k a ha d hd hza
          hzd hzDk l hzl
      let N : Set (Real × Real) := ⋂ l,
        if l = k then Set.univ else (D l)ᶜ
      have hNopen : IsOpen N := by
        apply isOpen_iInter_of_finite
        intro l
        split_ifs
        · exact isOpen_univ
        · exact (closedD l).isOpen_compl
      have hzN : z ∈ N := by
        apply Set.mem_iInter.mpr
        intro l
        split_ifs with hl
        · trivial
        · intro hzl
          have hlI := contains l hzl
          rw [hIeq] at hlI
          exact hl hlI
      let Q : Set (Real × Real) := N ∩ {y | 0 < b k y a ∧ 0 < b k y d}
      have hQopen : IsOpen Q := hNopen.inter
        ((isOpen_lt continuous_const (bcontinuous k a)).inter
          (isOpen_lt continuous_const (bcontinuous k d)))
      have hzQ : z ∈ Q := by
        refine ⟨hzN, ?_⟩
        change 0 < b k z a ∧ 0 < b k z d
        rw [hza, hzd]
        exact ⟨sub_pos.mpr hu1', hu0'⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hQopen z hzQ
      have hlocalchar (y : Real × Real) (hy : y ∈ Metric.ball z r) :
          y ∈ X ↔ 0 ≤ b k y c := PolygonalSeparationProof.hlocalchar n p X K t i u b bhull
              indices k a ha d hd had c hac hdc hvA hvD hpoint hzcoordA hzcoordD hzcoordC hza
              hzd hzc hQopen hzQ r hball y hy
      have hhalf : Convex Real {y : Real × Real | b k y c < 0} :=
          PolygonalSeparationProof.hhalf n p X K t u hu0' hu1' b blinear k c
      have hlocalEq : Metric.ball z r \ X =
          Metric.ball z r ∩ {y : Real × Real | b k y c < 0} := by
        ext y
        by_cases hy : y ∈ Metric.ball z r
        · have hchar := hlocalchar y hy
          simp [hy, hchar, not_le]
        · simp [hy]
      refine ⟨Metric.ball z r, Metric.isOpen_ball,
        Metric.mem_ball_self (x := z) hr, ?_⟩
      rw [hlocalEq]
      exact (convex_ball z r).inter hhalf |>.isPreconnected

private theorem hnonemptyV :
    (by
      classical
      exact
        ∀ (X : Set (Real × Real)), (IsCompact X) → ((Xᶜ).Nonempty) ) := by
  classical
  intro X hcompact
  by_contra hn
  have hce : Xᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  have hXeq : X = Set.univ := by simpa using congrArg (fun A : Set (Real × Real) => Aᶜ) hce
  rw [hXeq] at hcompact
  exact (NormedSpace.unbounded_univ Real (Real × Real)) hcompact.isBounded

private theorem hboundedV :
    (by
      classical
      exact
        ∀ (X : Set (Real × Real)), (IsCompact X) → (¬ Bornology.IsBounded (Xᶜ)) ) := by
  classical
  intro X hcompact hVb
  have hU : Bornology.IsBounded (X ∪ Xᶜ) := hcompact.isBounded.union hVb
  have hUniv : Bornology.IsBounded (Set.univ : Set (Real × Real)) := by
    simpa using hU
  exact (NormedSpace.unbounded_univ Real (Real × Real)) hUniv

private theorem hdisj :
    (by
      classical
      exact
        ∀ (X : Set (Real × Real)), Disjoint (interior X) Xᶜ ) := by
  classical
  intro X
  apply Set.disjoint_left.mpr
  intro x hxI hxC
  exact hxC (interior_subset hxI)

private theorem hcover :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)),
        let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
        (frontier X = C) → (∀ [IsClosed X], interior X ∪ Xᶜ = Cᶜ) ) := by
  classical
  intro n p X C hfrontierC hclosed
  ext z
  rw [← hfrontierC]
  simp [frontier]; tauto

end PolygonalSeparationDetails

theorem P3475T1PolygonalSeparation {n : Nat}
    (p : P3381T1PolygonBoundary n) (X K : Set (Real × Real))
    (t : P3475T1TriangleTree p X K) :
    let C := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
    ∃ U V : Set (Real × Real),
      IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
      IsOpen V ∧ IsConnected V ∧ ¬ Bornology.IsBounded V ∧
      Disjoint U V ∧ U ∪ V = Cᶜ ∧
      frontier U = C ∧ frontier V = C ∧ X = U ∪ C := by
-- BODY
  classical
  dsimp
  let C : Set (Real × Real) := ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))
  obtain ⟨hcompact, hinterior, hfrontier, hlocal⟩ :=
    P3381T1TriangulationBoundary p X K t.toP3381T1PairedTriangulation
  have hfrontierC : frontier X = C := by simpa [C] using hfrontier
  have hclosed : IsClosed X := hcompact.isClosed
  have hopenV : IsOpen Xᶜ := hclosed.isOpen_compl
  let M := P3381T1PiecewiseAffinePolygonModel p X K t.toP3381T1PairedTriangulation
  obtain ⟨h, hboundary, _⟩ := M
  have hiff : ∀ x : X, ((x : Real × Real) ∈ interior X) ↔
      ((h x : Real × Real) ∈ interior K) := PolygonalSeparationDetails.hiff X K h hboundary
  have hintpath : IsPathConnected (interior X) := PolygonalSeparationProof.hintpath n p X K t h hiff
  have hlocalAll : ∀ x, x ∈ frontier X →
      ∃ N : Set (Real × Real), IsOpen N ∧ x ∈ N ∧ IsPreconnected (N \ X) :=
          PolygonalSeparationDetails.hlocalAll n p X K t hlocal hfrontierC
  have hCpre : IsPreconnected C := PolygonalSeparationProof.hCpre n p
  have hVpre : IsPreconnected Xᶜ := PolygonalSeparationProof.hVpre n p X hfrontierC hopenV
      hlocalAll hCpre
  have hnonemptyV : (Xᶜ).Nonempty := PolygonalSeparationDetails.hnonemptyV X hcompact
  have hboundedU : Bornology.IsBounded (interior X) := hcompact.isBounded.subset interior_subset
  have hboundedV : ¬ Bornology.IsBounded (Xᶜ) := PolygonalSeparationDetails.hboundedV X hcompact
  have hdisj : Disjoint (interior X) Xᶜ := PolygonalSeparationDetails.hdisj X
  have hcover : interior X ∪ Xᶜ = Cᶜ := PolygonalSeparationDetails.hcover n p X hfrontierC
  have hfrontU : frontier (interior X) = C := PolygonalSeparationProof.hfrontU n p X K t
      hfrontierC  h hiff
  have hfrontV : frontier Xᶜ = C := by
    rw [frontier_compl, hfrontierC]
  have hX : X = interior X ∪ C := PolygonalSeparationProof.hX n p X hfrontierC
  refine ⟨interior X, Xᶜ, isOpen_interior, ?_, hboundedU, hopenV, ?_, hboundedV,
    hdisj, hcover, hfrontU, hfrontV, hX⟩
  · let : PathConnectedSpace (interior X) := isPathConnected_iff_pathConnectedSpace.mp hintpath
    exact ⟨hinterior, isPreconnected_iff_preconnectedSpace.mpr inferInstance⟩
  · exact ⟨hnonemptyV, hVpre⟩

end ApollonianSuperharmonic

end

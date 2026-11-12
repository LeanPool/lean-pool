/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3776T1StarWeightsExist
public import LeanPool.ApollonianSuperharmonic.P3776T1TileContractionsExist
public import LeanPool.ApollonianSuperharmonic.P3776T1DualEdgesExist
public import LeanPool.ApollonianSuperharmonic.P3776T1SectorMapsExist

-- [TABLET NODE: P3776T1PlaneMapExists]

/-!
# P3776T1PlaneMapExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PlaneMapConstruction

private theorem faceCoords_continuous :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P),
        let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
            W.face_simplex g x.1 x.2⟩
        ∀ (g : P.plane.Face), Continuous (faceCoords g) ) := by
  classical
  intro ι P W faceCoords g
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  exact (W.continuous (P.plane.faceVertex g i)).comp continuous_subtype_val

private theorem hEdgeFormula :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P), ∀ (H :
            P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (M :
            P3776T1SectorMaps P H E),
        let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
            W.face_simplex g x.1 x.2⟩
        let faceValue (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            Real × Real := M.faceMap g (faceCoords g x)
        ∀ (g : P.plane.Face), ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), ∀ (x : ℝ × ℝ), ∀ (hg : x
            ∈ closure (P.plane.faceRegion g)), x ∈ P.plane.edgeArc (P.plane.faceVertex g i)
            (P.plane.faceVertex g j) → i ≠ j → faceValue g ⟨x, hg⟩ = if W.weight
            (P.plane.faceVertex g i) x ≤ (1 / 2 : ℝ) then H.homotopy (P.plane.faceVertex g j) ((2
            : ℝ) * W.weight (P.plane.faceVertex g i) x) (E.port (P.plane.faceVertex g i)
            (P.plane.faceVertex g j)) else H.homotopy (P.plane.faceVertex g i) ((2 : ℝ) * ((1 :
            ℝ) - W.weight (P.plane.faceVertex g i) x)) (E.port (P.plane.faceVertex g i)
            (P.plane.faceVertex g j)) ) := by
  classical
  intro ι P W H E M faceCoords faceValue g i j x hg hx hij
  let s := faceCoords g ⟨x, hg⟩
  have hadj := P.plane.face_edges g i j hij
  have hzero : ∀ k, k ≠ i → k ≠ j → s.1 k = 0 := by
    intro k hki hkj
    apply W.edge_support _ _ hadj x hx (P.plane.faceVertex g k)
    · intro he
      exact hki (P.plane.face_vertices_distinct g he)
    · intro he
      exact hkj (P.plane.face_vertices_distinct g he)
  have hrange : (s.1 i : Real) ∈ Set.Icc 0 1 :=
    ⟨s.2.1 i, by
      have h := Finset.single_le_sum (fun j _ => s.2.1 j) (Finset.mem_univ i)
      simpa only [s.2.2] using h⟩
  have hsum : s.1 j = 1 - s.1 i := by
    have hsum' : (∑ k : Fin 3, s.1 k) = s.1 i + s.1 j := by
      calc
        (∑ k : Fin 3, s.1 k) = ∑ k ∈ ({i, j} : Finset (Fin 3)), s.1 k :=
          (Finset.sum_subset (by simp) (by
            intro k hk hknot
            have hki : k ≠ i := by
              intro he
              subst k
              simp at hknot
            have hkj : k ≠ j := by
              intro he
              subst k
              simp at hknot
            exact hzero k hki hkj)).symm
        _ = s.1 i + s.1 j := by simp [Finset.sum_insert, hij]
    have hs : (∑ k : Fin 3, s.1 k) = 1 := by
      exact s.2.2
    rw [hsum'] at hs
    linarith
  have hvec : ∀ k, s.1 k = if k = i then (s.1 i : Real)
      else if k = j then 1 - (s.1 i : Real) else 0 := by
    intro k
    by_cases hki : k = i
    · simp [hki]
    · by_cases hkj : k = j
      · simp [hkj, hsum, hij.symm]
      · simp [hki, hkj, hzero k hki hkj]
  have hformula := M.edge g i j hij ⟨s.1 i, hrange⟩ s hvec
  simpa [faceValue, faceCoords, s] using hformula

private theorem hBoundaryArc :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (g : P.plane.Face), ∀ x ∈ frontier
            (P.plane.faceRegion g), ∃ (i : Fin (3 : ℕ)) (j : Fin (3 : ℕ)), i ≠ j ∧ x ∈
            P.plane.edgeArc (P.plane.faceVertex g i) (P.plane.faceVertex g j) ) := by
  classical
  intro ι P g x hx
  rw [P.plane.face_boundary] at hx
  rcases hx with (hx | hx) | hx
  · exact ⟨0, 1, by decide, hx⟩
  · exact ⟨1, 2, by decide, hx⟩
  · exact ⟨2, 0, by decide, hx⟩

private theorem hEdgeWeightSum :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P),
        ∀ (g : P.plane.Face), ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), ∀ x ∈ closure
            (P.plane.faceRegion g), x ∈ P.plane.edgeArc (P.plane.faceVertex g i)
            (P.plane.faceVertex g j) → i ≠ j → W.weight (P.plane.faceVertex g i) x + W.weight
            (P.plane.faceVertex g j) x = (1 : ℝ) ) := by
  classical
  intro ι P W g i j x hg hx hij
  let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
      StandardSimplex (Fin 3) :=
    ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
      W.face_simplex g x.1 x.2⟩
  let s := faceCoords g ⟨x, hg⟩
  have hzero : ∀ k, k ≠ i → k ≠ j → s.1 k = 0 := by
    intro k hki hkj
    apply W.edge_support _ _ (P.plane.face_edges g i j hij) x hx
      (P.plane.faceVertex g k)
    · intro he
      exact hki (P.plane.face_vertices_distinct g he)
    · intro he
      exact hkj (P.plane.face_vertices_distinct g he)
  have hsum' : (∑ k : Fin 3, s.1 k) = s.1 i + s.1 j := by
    calc
      (∑ k : Fin 3, s.1 k) = ∑ k ∈ ({i, j} : Finset (Fin 3)), s.1 k :=
        (Finset.sum_subset (by simp) (by
          intro k hk hknot
          have hki : k ≠ i := by intro he; subst k; simp at hknot
          have hkj : k ≠ j := by intro he; subst k; simp at hknot
          exact hzero k hki hkj)).symm
      _ = s.1 i + s.1 j := by simp [Finset.sum_insert, hij]
  have hs : (∑ k : Fin 3, s.1 k) = 1 :=
    s.2.2
  have hresult : s.1 i + s.1 j = 1 := by rw [← hsum']; exact hs
  simpa [s, faceCoords] using hresult

private theorem hVertexValue :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P), ∀ (H :
            P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (M :
            P3776T1SectorMaps P H E),
        let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
            W.face_simplex g x.1 x.2⟩
        let faceValue (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            Real × Real := M.faceMap g (faceCoords g x)
        ∀ (g : P.plane.Face), ∀ (x : ℝ × ℝ), ∀ (hg : x ∈ closure (P.plane.faceRegion g)), ∀ (v :
            ι), ∀ (i : Fin (3 : ℕ)), P.plane.faceVertex g i = v → x = P.plane.position v →
            faceValue g ⟨x, hg⟩ = H.center v ) := by
  classical
  intro ι P W H E M faceCoords faceValue g x hg v i hvi hx
  subst x
  have hcoord : ∀ k : Fin 3,
      W.weight (P.plane.faceVertex g k) (P.plane.position v) =
        if k = i then 1 else 0 := by
    intro k
    have hk : P.plane.faceVertex g k = v ↔ k = i := by
      constructor
      · intro h
        exact P.plane.face_vertices_distinct g (h.trans hvi.symm)
      · rintro rfl
        exact hvi
    simp [W.vertex_value, hk]
  have hsimplex : ∀ k : Fin 3, (faceCoords g ⟨P.plane.position v, hg⟩).1 k =
      if k = i then 1 else 0 := by
    intro k
    exact hcoord k
  change M.faceMap g (faceCoords g ⟨P.plane.position v, hg⟩) = H.center v
  simpa [hvi] using M.vertex g i (faceCoords g ⟨P.plane.position v, hg⟩) hsimplex

private theorem hAgree :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P), ∀ (H :
            P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (M :
            P3776T1SectorMaps P H E),
        let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
            W.face_simplex g x.1 x.2⟩
        let faceValue (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            Real × Real := M.faceMap g (faceCoords g x)
        (∀ (g : P.plane.Face), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (x : Real × Real), ∀ (hg : x ∈
            closure (P.plane.faceRegion g)), (x ∈ P.plane.edgeArc (P.plane.faceVertex g i)
            (P.plane.faceVertex g j)) → ((i ≠ j) → (faceValue g ⟨x, hg⟩ = if W.weight
            (P.plane.faceVertex g i) x ≤ 1 / 2 then H.homotopy (P.plane.faceVertex g j) (2 *
            W.weight (P.plane.faceVertex g i) x) (E.port (P.plane.faceVertex g i)
            (P.plane.faceVertex g j)) else H.homotopy (P.plane.faceVertex g i) (2 * (1 - W.weight
            (P.plane.faceVertex g i) x)) (E.port (P.plane.faceVertex g i) (P.plane.faceVertex g
            j))))) → ((∀ (g : P.plane.Face), ∀ (x : Real × Real), (x ∈ frontier
            (P.plane.faceRegion g)) → (∃ i j : Fin 3, i ≠ j ∧ x ∈ P.plane.edgeArc
            (P.plane.faceVertex g i) (P.plane.faceVertex g j))) → ((∀ (g : P.plane.Face), ∀ (i :
            Fin 3), ∀ (j : Fin 3), ∀ (x : Real × Real), (x ∈ closure (P.plane.faceRegion g)) →
            ((x ∈ P.plane.edgeArc (P.plane.faceVertex g i) (P.plane.faceVertex g j)) → ((i ≠ j) →
            (W.weight (P.plane.faceVertex g i) x + W.weight (P.plane.faceVertex g j) x = 1)))) →
            ((∀ (g : P.plane.Face), ∀ (x : Real × Real), ∀ (hg : x ∈ closure (P.plane.faceRegion
            g)), ∀ (v : ι), ∀ (i : Fin 3), (P.plane.faceVertex g i = v) → ((x = P.plane.position
            v) → (faceValue g ⟨x, hg⟩ = H.center v))) → (∀ g, ∀ h, ∀ x, ∀ (hg : x ∈ closure
            (P.plane.faceRegion g)), ∀ (hh : x ∈ closure (P.plane.faceRegion h)), faceValue g ⟨x,
            hg⟩ = faceValue h ⟨x, hh⟩)))) ) := by
  classical
  intro ι P W H E M faceCoords faceValue hEdgeFormula hBoundaryArc hEdgeWeightSum hVertexValue g
      h x hg hh
  by_cases hgh : g = h
  · subst h
    rfl
  · have hxg : x ∉ P.plane.faceRegion g := by
      intro hx
      have : g = h := by
        by_contra hn
        exact Set.disjoint_left.mp ((P.plane.region_disjoint hn).closure_right
          (P.plane.region_open g)) hx hh
      exact hgh this
    have hxh : x ∉ P.plane.faceRegion h := by
      intro hx
      have : h = g := by
        by_contra hn
        exact Set.disjoint_left.mp ((P.plane.region_disjoint hn).closure_right
          (P.plane.region_open h)) hx hg
      exact hgh this.symm
    have hfg : x ∈ frontier (P.plane.faceRegion g) := by
      simpa [frontier, (P.plane.region_open g).interior_eq] using ⟨hg, hxg⟩
    have hfh : x ∈ frontier (P.plane.faceRegion h) := by
      simpa [frontier, (P.plane.region_open h).interior_eq] using ⟨hh, hxh⟩
    obtain ⟨i, j, hij, hxij⟩ := hBoundaryArc g x hfg
    obtain ⟨k, l, hkl, hxkl⟩ := hBoundaryArc h x hfh
    let a := P.plane.faceVertex g i
    let b := P.plane.faceVertex g j
    let c := P.plane.faceVertex h k
    let d := P.plane.faceVertex h l
    have hab : a ≠ b := by
      intro he
      exact hij (P.plane.face_vertices_distinct g he)
    have hcd : c ≠ d := by
      intro he
      exact hkl (P.plane.face_vertices_distinct h he)
    have hadj := P.plane.face_edges g i j hij
    by_cases hsame : ({a, b} : Set ι) = {c, d}
    · have ha : a = c ∨ a = d := by
        have hm : a ∈ ({c, d} : Set ι) := by rw [← hsame]; simp
        simpa using hm
      have hb : b = c ∨ b = d := by
        have hm : b ∈ ({c, d} : Set ι) := by rw [← hsame]; simp
        simpa using hm
      rcases ha with hac | had
      · rcases hb with hbc | hbd
        · exact (hab (hac.trans hbc.symm)).elim
        · have hfirst := hEdgeFormula g i j x hg hxij hij
          have hsecond := hEdgeFormula h k l x hh hxkl hkl
          have hki : P.plane.faceVertex h k = P.plane.faceVertex g i := hac.symm
          have hlj : P.plane.faceVertex h l = P.plane.faceVertex g j := hbd.symm
          rw [hki, hlj] at hsecond
          rw [hfirst, hsecond]
      · rcases hb with hbc | hbd
        · have hfirst := hEdgeFormula g i j x hg hxij hij
          have hsecond := hEdgeFormula h k l x hh hxkl hkl
          have hki : P.plane.faceVertex h k = P.plane.faceVertex g j := hbc.symm
          have hlj : P.plane.faceVertex h l = P.plane.faceVertex g i := had.symm
          rw [hki, hlj] at hsecond
          have hsum := hEdgeWeightSum g i j x hg hxij hij
          change W.weight a x + W.weight b x = 1 at hsum
          have hs : W.weight b x = 1 - W.weight a x := by linarith
          have hport := E.port_symmetric a b hadj
          by_cases hr : W.weight a x < 1 / 2
          · have hrle : W.weight a x ≤ 1 / 2 := le_of_lt hr
            have hsGreater : 1 / 2 < W.weight b x := by rw [hs]; linarith
            have hsnot : ¬ W.weight b x ≤ 1 / 2 := not_le_of_gt hsGreater
            rw [hfirst, hsecond]
            rw [ite_eq_left hrle, ite_eq_right hsnot]
            rw [hs, hport]
            congr 1; ring
          · have hge : 1 / 2 ≤ W.weight a x := le_of_not_gt hr
            by_cases hre : W.weight a x = 1 / 2
            · have hsval : W.weight b x = 1 / 2 := by rw [hs, hre]; norm_num
              have hre' : W.weight (P.plane.faceVertex g i) x = 1 / 2 := hre
              have hs' : W.weight (P.plane.faceVertex g j) x = 1 / 2 := hsval
              have hportmem := E.port_support a b hadj
              have hrev : P.plane.adjacent b a :=
                (P.plane.adjacent_symmetric a b).mp hadj
              have hportmem' := E.port_support b a hrev
              calc
                faceValue g ⟨x, hg⟩ = H.homotopy b 1 (E.port a b) := by
                  rw [hfirst]
                  have hi : W.weight (P.plane.faceVertex g i) x ≤ 1 / 2 := by
                    rw [hre']
                  rw [ite_eq_left hi]
                  rw [hre']
                  simp [a, b]
                _ = E.port a b := H.one b _ hportmem.2
                _ = E.port b a := hport
                _ = H.homotopy a 1 (E.port b a) := (H.one a _ hportmem'.2).symm
                _ = faceValue h ⟨x, hh⟩ := by
                  rw [hsecond]
                  have hj : W.weight (P.plane.faceVertex g j) x ≤ 1 / 2 := by
                    rw [hs']
                  rw [ite_eq_left hj]
                  rw [hs']
                  simp [a, b]
            · have hrgt : 1 / 2 < W.weight a x := lt_of_le_of_ne hge (Ne.symm hre)
              have hslt : W.weight b x < 1 / 2 := by rw [hs]; linarith
              rw [hfirst, hsecond]
              rw [ite_eq_right (not_le_of_gt hrgt), ite_eq_left (le_of_lt hslt)]
              rw [hs, hport]
        · exact (hab (had.trans hbd.symm)).elim
    · have hadj' := P.plane.face_edges h k l hkl
      have hxintersection : x ∈ P.plane.edgeArc a b ∩ P.plane.edgeArc c d :=
        ⟨hxij, hxkl⟩
      rw [P.plane.arc_intersections a b c d hadj hadj' hsame] at hxintersection
      obtain ⟨v, hv, hvx⟩ := hxintersection
      have hva : v = a ∨ v = b := by simpa using hv.1
      have hvc : v = c ∨ v = d := by simpa using hv.2
      rcases hva with hva | hvb <;> rcases hvc with hvc | hvd
      · have hleft := hVertexValue g x hg v i (rfl.trans hva.symm) hvx.symm
        have hright := hVertexValue h x hh v k (rfl.trans hvc.symm) hvx.symm
        exact hleft.trans hright.symm
      · have hleft := hVertexValue g x hg v i (rfl.trans hva.symm) hvx.symm
        have hright := hVertexValue h x hh v l (rfl.trans hvd.symm) hvx.symm
        exact hleft.trans hright.symm
      · have hleft := hVertexValue g x hg v j (rfl.trans hvb.symm) hvx.symm
        have hright := hVertexValue h x hh v k (rfl.trans hvc.symm) hvx.symm
        exact hleft.trans hright.symm
      · have hleft := hVertexValue g x hg v j (rfl.trans hvb.symm) hvx.symm
        have hright := hVertexValue h x hh v l (rfl.trans hvd.symm) hvx.symm
        exact hleft.trans hright.symm

private theorem hLoc :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), LocallyFinite (fun g : P.plane.Face => closure
            (P.plane.faceRegion g)) ) := by
  classical
  intro ι P x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x (by norm_num), ?_⟩
  have hfin := (P3776T1FixedGeometry P).2.2.1
    (Metric.closedBall x 1) (isCompact_closedBall x 1)
  exact hfin.subset (by
    intro g hg
    rcases hg with ⟨y, hyball, hyg⟩
    exact ⟨y, hyg, hyball⟩)

private theorem hcoverUnion :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (∀ x : Real × Real, ∃ g, x ∈ closure
            (P.plane.faceRegion g)) → ((⋃ g : P.plane.Face, closure (P.plane.faceRegion g)) =
            Set.univ) ) := by
  classical
  intro ι P hcover
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact hcover x

private theorem heq :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P), ∀ (H :
            P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (M :
            P3776T1SectorMaps P H E), ∀ (hcover : ∀ x : Real × Real, ∃ g, x ∈ closure
            (P.plane.faceRegion g)),
        let pick (x : Real × Real) : P.plane.Face := Classical.choose (hcover x)
        ∀ (hpick : ∀ (x : Real × Real), x ∈ closure (P.plane.faceRegion (pick x))),
        let coordinates (x : Real × Real) : StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex (pick x) i) x,
            W.face_simplex (pick x) x (hpick x)⟩
        let f (x : Real × Real) : Real × Real := M.faceMap (pick x) (coordinates x)
        let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
            W.face_simplex g x.1 x.2⟩
        let faceValue (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            Real × Real := M.faceMap g (faceCoords g x)
        (∀ g, ∀ h, ∀ x, ∀ (hg : x ∈ closure (P.plane.faceRegion g)), ∀ (hh : x ∈ closure
            (P.plane.faceRegion h)), faceValue g ⟨x, hg⟩ = faceValue h ⟨x, hh⟩) → (∀ (g :
            P.plane.Face), ∀ x : ↥(closure (P.plane.faceRegion g)), f x.1 = faceValue g x) ) := by
  classical
  intro ι P W H E M hcover pick hpick coordinates f faceCoords faceValue hAgree g x
  simpa [f, coordinates, faceValue, faceCoords] using
    (hAgree (pick x.1) g x.1 (hpick x.1) x.2)

private theorem hcont :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P), ∀ (H :
            P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (M :
            P3776T1SectorMaps P H E), ∀ (hcover : ∀ x : Real × Real, ∃ g, x ∈ closure
            (P.plane.faceRegion g)),
        let pick (x : Real × Real) : P.plane.Face := Classical.choose (hcover x)
        ∀ (hpick : ∀ (x : Real × Real), x ∈ closure (P.plane.faceRegion (pick x))),
        let coordinates (x : Real × Real) : StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex (pick x) i) x,
            W.face_simplex (pick x) x (hpick x)⟩
        let f (x : Real × Real) : Real × Real := M.faceMap (pick x) (coordinates x)
        let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
            W.face_simplex g x.1 x.2⟩
        let faceValue (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            Real × Real := M.faceMap g (faceCoords g x)
        (∀ (g : P.plane.Face), Continuous (faceValue g)) → (∀ (g : P.plane.Face), (∀ x :
            ↥(closure (P.plane.faceRegion g)), f x.1 = faceValue g x) → (Continuous (fun x :
            ↥(closure (P.plane.faceRegion g)) => f x.1))) ) := by
  classical
  intro ι P W H E M hcover pick hpick coordinates f faceCoords faceValue faceValue_continuous g heq
  have heqFun : (fun x : ↥(closure (P.plane.faceRegion g)) => f x.1) =
      faceValue g := funext heq
  rw [heqFun]
  exact faceValue_continuous g

private theorem htranslated :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (hcover : ∀ x : Real × Real, ∃ g, x ∈ closure
            (P.plane.faceRegion g)),
        let pick (x : Real × Real) : P.plane.Face := Classical.choose (hcover x)
        ∀ (u : ↥P.lattice), ∀ (x : ℝ × ℝ),
        let g := pick x
        (x ∈ closure (P.plane.faceRegion g)) → (x + GaussianRealPoint u ∈ closure
            (P.plane.faceRegion (P.faceShift u g))) ) := by
  classical
  intro ι P hcover pick u x g hg
  rw [P.faceRegion_periodic]
  have hcl : closure ((fun p => p + GaussianRealPoint u) ''
      P.plane.faceRegion g) =
      (fun p => p + GaussianRealPoint u) '' closure (P.plane.faceRegion g) :=
    (Homeomorph.addRight (GaussianRealPoint u)).image_closure _ |>.symm
  rw [hcl]
  exact ⟨x, hg, rfl⟩

private theorem hleft' :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (W : P3776T1StarWeights P), ∀ (H :
            P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (M :
            P3776T1SectorMaps P H E), ∀ (hcover : ∀ x : Real × Real, ∃ g, x ∈ closure
            (P.plane.faceRegion g)),
        let pick (x : Real × Real) : P.plane.Face := Classical.choose (hcover x)
        ∀ (hpick : ∀ (x : Real × Real), x ∈ closure (P.plane.faceRegion (pick x))),
        let coordinates (x : Real × Real) : StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex (pick x) i) x,
            W.face_simplex (pick x) x (hpick x)⟩
        let f (x : Real × Real) : Real × Real := M.faceMap (pick x) (coordinates x)
        let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            StandardSimplex (Fin 3) :=
          ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
            W.face_simplex g x.1 x.2⟩
        let faceValue (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
            Real × Real := M.faceMap g (faceCoords g x)
        ∀ (u : ↥P.lattice), ∀ (x : ℝ × ℝ),
        let g := pick x
        ∀ (htranslated : x + GaussianRealPoint u ∈ closure (P.plane.faceRegion (P.faceShift u
            g))), (faceValue (pick (x + GaussianRealPoint (↑u : GaussianInt))) ⟨x +
            GaussianRealPoint (↑u : GaussianInt), hpick (x + GaussianRealPoint u)⟩ = faceValue
                (P.faceShift u g) ⟨x +
            GaussianRealPoint (↑u : GaussianInt), htranslated⟩) → (f (x + GaussianRealPoint u) =
            faceValue (P.faceShift u g) ⟨x + GaussianRealPoint u, htranslated⟩) ) := by
  classical
  intro ι P W H E M hcover pick hpick coordinates f faceCoords faceValue u x g htranslated hleft
  simpa [f, coordinates, faceValue, faceCoords] using hleft

end PlaneMapConstruction

theorem P3776T1PlaneMapExists {ι : Type} (P : PeriodicTileCore ι) :
    ∃ f : (Real × Real) → (Real × Real), Continuous f ∧
      (∀ u : P.lattice, ∀ x, f (x + GaussianRealPoint u) = f x + GaussianRealPoint u) ∧
      ∀ x, ∃ a, f x ∈ TileRealization (P.tile a) := by
-- BODY
  classical
  obtain ⟨W⟩ := P3776T1StarWeightsExist P
  obtain ⟨H⟩ := P3776T1TileContractionsExist P
  obtain ⟨E⟩ := P3776T1DualEdgesExist P
  obtain ⟨M⟩ := P3776T1SectorMapsExist P H E
  have hcover : ∀ x : Real × Real, ∃ g, x ∈ closure (P.plane.faceRegion g) :=
    (P3776T1FixedGeometry P).2.2.2.1
  let pick (x : Real × Real) : P.plane.Face := Classical.choose (hcover x)
  have hpick (x : Real × Real) : x ∈ closure (P.plane.faceRegion (pick x)) :=
    Classical.choose_spec (hcover x)
  let coordinates (x : Real × Real) : StandardSimplex (Fin 3) :=
    ⟨fun i => W.weight (P.plane.faceVertex (pick x) i) x,
      W.face_simplex (pick x) x (hpick x)⟩
  let f (x : Real × Real) : Real × Real := M.faceMap (pick x) (coordinates x)
  let faceCoords (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
      StandardSimplex (Fin 3) :=
    ⟨fun i => W.weight (P.plane.faceVertex g i) x.1,
      W.face_simplex g x.1 x.2⟩
  let faceValue (g : P.plane.Face) (x : ↥(closure (P.plane.faceRegion g))) :
      Real × Real := M.faceMap g (faceCoords g x)
  have faceCoords_continuous (g : P.plane.Face) := PlaneMapConstruction.faceCoords_continuous ι P
      W g
  have faceValue_continuous (g : P.plane.Face) : Continuous (faceValue g) := by
    exact (M.faceMap g).continuous.comp (faceCoords_continuous g)
  have hEdgeFormula (g : P.plane.Face) (i j : Fin 3) (x : Real × Real)
      (hg : x ∈ closure (P.plane.faceRegion g))
      (hx : x ∈ P.plane.edgeArc (P.plane.faceVertex g i) (P.plane.faceVertex g j))
      (hij : i ≠ j) := PlaneMapConstruction.hEdgeFormula ι P W H E M g i j x hg hx hij
  have hBoundaryArc (g : P.plane.Face) (x : Real × Real)
      (hx : x ∈ frontier (P.plane.faceRegion g)) := PlaneMapConstruction.hBoundaryArc ι P g x hx
  have hEdgeWeightSum (g : P.plane.Face) (i j : Fin 3) (x : Real × Real)
      (hg : x ∈ closure (P.plane.faceRegion g))
      (hx : x ∈ P.plane.edgeArc (P.plane.faceVertex g i) (P.plane.faceVertex g j))
      (hij : i ≠ j) := PlaneMapConstruction.hEdgeWeightSum ι P W g i j x hg hx hij
  have hVertexValue (g : P.plane.Face) (x : Real × Real)
      (hg : x ∈ closure (P.plane.faceRegion g)) (v : ι) (i : Fin 3)
      (hvi : P.plane.faceVertex g i = v) (hx : x = P.plane.position v) :=
          PlaneMapConstruction.hVertexValue ι P W H E M g x hg v i hvi hx
  have hAgree := PlaneMapConstruction.hAgree ι P W H E M hEdgeFormula hBoundaryArc hEdgeWeightSum
      hVertexValue
  refine ⟨f, ?_, ?_, ?_⟩
  · have hLoc : LocallyFinite (fun g : P.plane.Face => closure (P.plane.faceRegion g)) :=
      PlaneMapConstruction.hLoc ι P
    have hcoverUnion := PlaneMapConstruction.hcoverUnion ι P hcover
    apply hLoc.continuous hcoverUnion
      (fun g => isClosed_closure)
      (fun g => ?_)
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : ↥(closure (P.plane.faceRegion g)) => f x.1)
    have heq := PlaneMapConstruction.heq ι P W H E M hcover hpick hAgree g
    have hcont := PlaneMapConstruction.hcont ι P W H E M hcover hpick faceValue_continuous g heq
    exact hcont
  · intro u x
    let g := pick x
    have hg : x ∈ closure (P.plane.faceRegion g) := hpick x
    have htranslated : x + GaussianRealPoint u ∈
        closure (P.plane.faceRegion (P.faceShift u g)) := PlaneMapConstruction.htranslated ι P
            hcover u x hg
    have hleft := hAgree (pick (x + GaussianRealPoint u)) (P.faceShift u g)
      (x + GaussianRealPoint u) (hpick _) htranslated
    have hright := hAgree (pick x) g x (hpick x) hg
    have hleft' : f (x + GaussianRealPoint u) =
        faceValue (P.faceShift u g) ⟨x + GaussianRealPoint u, htranslated⟩ :=
            PlaneMapConstruction.hleft' ι P W H E M hcover hpick u x htranslated hleft
    have hright' : f x = faceValue g ⟨x, hg⟩ := by
      simpa [f, coordinates, faceValue, faceCoords] using hright.symm
    rw [hleft', hright']
    change M.faceMap (P.faceShift u g)
        (faceCoords (P.faceShift u g) ⟨x + GaussianRealPoint u, htranslated⟩) =
      M.faceMap g (faceCoords g ⟨x, hg⟩) + GaussianRealPoint u
    rw [M.periodic]
    rw [add_right_cancel_iff]
    apply congrArg (M.faceMap g)
    apply Subtype.ext
    funext i
    change W.weight (P.plane.faceVertex (P.faceShift u g) i)
        (x + GaussianRealPoint u) = W.weight (P.plane.faceVertex g i) x
    rw [P.face_vertices_periodic, W.periodic]
  · intro x
    obtain ⟨i, _, hi⟩ := M.support (pick x) (coordinates x)
    exact ⟨P.plane.faceVertex (pick x) i, hi⟩

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTouchingDisjoint

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.P3996T1AdjacentParentPlacement
public import LeanPool.ApollonianSuperharmonic.P4590T1JunctionRefinement
public import LeanPool.ApollonianSuperharmonic.P4616T1OriginalMixedPaths
public import LeanPool.ApollonianSuperharmonic.P4616T1MixedCoarseSectors
public import LeanPool.ApollonianSuperharmonic.P4616T1PeriodicEndpointExclusion
public import LeanPool.ApollonianSuperharmonic.P4616T1FirstPredecessorCentroids
public import LeanPool.ApollonianSuperharmonic.P4616T1NestedCompanionFootprints

-- [TABLET NODE: P4590T1MixedCompanionMarks]

/-!
# P4590T1MixedCompanionMarks

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MixedCompanionMarksGeometry

private theorem endpointMem :
    (by
      classical
      exact
        ∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {a : GaussianInt}, ∀
            {b : GaussianInt}, (SimpleGridPathBetween V E a b) → (a ∈ V ∧ b ∈ V) ) := by
  classical
  intro V E a b hp
  obtain ⟨xs, _, hlen, hh, ht, hv, _, _⟩ := hp
  have hne : xs ≠ [] := by intro he; simp [he] at hlen
  have hhead : xs.head hne = a := by
    simpa [List.head?_eq_some_head hne] using hh
  have hlast : xs.getLast hne = b := by
    simpa [List.getLast?_eq_some_getLast hne] using ht
  rw [hv]
  constructor
  · change a ∈ xs.toFinset
    exact List.mem_toFinset.mpr (hhead ▸ List.head_mem hne)
  · change b ∈ xs.toFinset
    exact List.mem_toFinset.mpr (hlast ▸ List.getLast_mem hne)

private theorem pairDisjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
          cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
        let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
          cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
        (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), (i, s) ≠ (j, t) →
            ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ))) → Disjoint (cert.P i s).cells
            (cert.P j t).cells) → (∀ (k : Fin 6), Disjoint (U k).cells (W k).cells) ) := by
  classical
  intro q cfg C T cert U W separate k
  fin_cases k <;> dsimp [U, W] <;>
    exact separate _ _ _ _ (by decide) (by decide)

private theorem exclude :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
          cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
        let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
          cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
        let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
          cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
        let H : Fin 6 → ProtoTile := ![
          TileTranslation (cert.P 0 false) (cert.u + cert.v),
          TileTranslation (cert.P 0 false) cert.v,
          TileTranslation (cert.P 0 true) (-cert.u - cert.v),
          TileTranslation (cert.P 0 true) (-cert.v),
          TileTranslation (cert.P 1 false) (-cert.u),
          TileTranslation (cert.P 1 true) cert.u]
        let rho := fun f : PeriodicSubtileFaceIndex =>
          cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f)
        let p : Fin 6 → GaussianInt := ![rho ⟨.I2, 0, 0⟩, rho ⟨.I3, 0, 0⟩,
          rho ⟨.I1, 0, 0⟩, rho ⟨.I4, 0, 0⟩, rho ⟨.I3, 0, 0⟩, rho ⟨.I4, 0, 0⟩]
        let l : Fin 6 → GaussianInt := ![rho ⟨.J4, 0, 0⟩, rho ⟨.J2, 0, 0⟩,
          rho ⟨.J3, -1, -1⟩, rho ⟨.J1, 0, -1⟩, rho ⟨.J8, 0, 0⟩,
          rho ⟨.J7, 1, 0⟩]
        (∀ (k : Fin (6 : ℕ)), SimpleGridPathBetween (FootprintVertices (U k) ∩ FootprintVertices
            (W k)) (FootprintEdges (U k) ∩ FootprintEdges (W k)) (p k) (l k) ∧ p k ∈
            FootprintVertices (K k) ∧ l k ∈ FootprintVertices (H k)) → ((∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ T.cells) → (∀ (k : Fin 6), x ≠ l k)) ) := by
  classical
  intro q cfg C T cert x U W K H rho p l paths rootstar k
  let S : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 0 false,
    cert.P 0 true, cert.P 0 true, cert.P 1 false, cert.P 1 true]
  let m : Fin 6 → Int := ![1, 0, -1, 0, -1, 1]
  let n : Fin 6 → Int := ![1, 1, -1, -1, 0, 0]
  have hS : (S k).cells.Nonempty := by
    fin_cases k <;> exact (LatticeTileGridStructure _ (cert.parent_lattice _ _)).1.1
  have hST : (S k).cells ⊆ T.cells := by
    intro a ha
    apply (cert.outer_union a).mpr
    fin_cases k <;> exact ⟨_, _, ha⟩
  have hmn : (m k, n k) ≠ (0, 0) := by fin_cases k <;> decide
  apply P4616T1PeriodicEndpointExclusion q cfg C T cert
    (S k) hS hST (m k) (n k) hmn x (l k) rootstar
  have hh := (paths k).2.2
  fin_cases k <;> simpa [S, m, n, H, sub_eq_add_neg] using hh

private theorem coarse :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
          cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
        let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
          cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
        let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
          cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
        let H : Fin 6 → ProtoTile := ![
          TileTranslation (cert.P 0 false) (cert.u + cert.v),
          TileTranslation (cert.P 0 false) cert.v,
          TileTranslation (cert.P 0 true) (-cert.u - cert.v),
          TileTranslation (cert.P 0 true) (-cert.v),
          TileTranslation (cert.P 1 false) (-cert.u),
          TileTranslation (cert.P 1 true) cert.u]
        let rho := fun f : PeriodicSubtileFaceIndex =>
          cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f)
        let p : Fin 6 → GaussianInt := ![rho ⟨.I2, 0, 0⟩, rho ⟨.I3, 0, 0⟩,
          rho ⟨.I1, 0, 0⟩, rho ⟨.I4, 0, 0⟩, rho ⟨.I3, 0, 0⟩, rho ⟨.I4, 0, 0⟩]
        let l : Fin 6 → GaussianInt := ![rho ⟨.J4, 0, 0⟩, rho ⟨.J2, 0, 0⟩,
          rho ⟨.J3, -1, -1⟩, rho ⟨.J1, 0, -1⟩, rho ⟨.J8, 0, 0⟩,
          rho ⟨.J7, 1, 0⟩]
        (∀ (k : Fin (6 : ℕ)), SimpleGridPathBetween (FootprintVertices (U k) ∩ FootprintVertices
            (W k)) (FootprintEdges (U k) ∩ FootprintEdges (W k)) (p k) (l k) ∧ p k ∈
            FootprintVertices (K k) ∧ l k ∈ FootprintVertices (H k)) → ((∀ (k : Fin 6), Disjoint
            (U k).cells (W k).cells) → ((∀ (k : Fin 6), LatticeTile (U k)) → ((∀ (k : Fin 6),
            LatticeTile (W k)) → ((∀ (k : Fin 6), x ≠ l k) → ((∀ (k : Fin (6 : ℕ)), ∀ z ∈
            FootprintVertices (U k), z ∈ FootprintVertices (W k) → z ∈ FootprintVertices (K k) →
            ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell z j ∈ (K k).cells ∧
            LatticeVertexIncidentCell z j ∉ (U k).cells ∧ LatticeVertexIncidentCell z j ∉ (W
            k).cells) → (∀ (k : Fin 6), (x ∈ FootprintVertices (U k)) → ((x ∈ FootprintVertices
            (W k)) → (x ∈ FootprintVertices (K k) ↔ x = p k)))))))) ) := by
  classical
  intro q cfg C T cert x U W K H rho p l paths pairDisjoint diskU diskW exclude sectors k hu hw
  constructor
  · intro hk
    exact (P4616T1ThirdOwnerPathEndpoint (U k) (W k) (K k)
      (p k) (l k) x _ (diskU k) (diskW k) (pairDisjoint k)
      (paths k).1 ⟨hu, hw⟩ (sectors k x hu hw hk)).resolve_right (exclude k)
  · intro he
    simpa only [he] using (paths k).2.1

private theorem pos2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let r := cfg.firstPredecessor
        0 < (r 2).1 ) := by
  classical
  intro q cfg r
  dsimp [r]
  rw [cfg.firstParentTwo]
  have hh := cfg.secondLarge
  omega

private theorem pos3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let r := cfg.firstPredecessor
        0 < (r 3).1 ) := by
  classical
  intro q cfg r
  dsimp [r]
  rw [cfg.firstParentThree]
  have hh := (ProperBandCurvatureStructure q cfg.proper).2.1 2
  have hn := cfg.noLine 3
  change 0 ≤ (q 3).1 at hh
  omega

private theorem firstFour :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
          cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
        let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
          cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
        let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
          cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
        let H : Fin 6 → ProtoTile := ![
          TileTranslation (cert.P 0 false) (cert.u + cert.v),
          TileTranslation (cert.P 0 false) cert.v,
          TileTranslation (cert.P 0 true) (-cert.u - cert.v),
          TileTranslation (cert.P 0 true) (-cert.v),
          TileTranslation (cert.P 1 false) (-cert.u),
          TileTranslation (cert.P 1 true) cert.u]
        let rho := fun f : PeriodicSubtileFaceIndex =>
          cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f)
        let p : Fin 6 → GaussianInt := ![rho ⟨.I2, 0, 0⟩, rho ⟨.I3, 0, 0⟩,
          rho ⟨.I1, 0, 0⟩, rho ⟨.I4, 0, 0⟩, rho ⟨.I3, 0, 0⟩, rho ⟨.I4, 0, 0⟩]
        let l : Fin 6 → GaussianInt := ![rho ⟨.J4, 0, 0⟩, rho ⟨.J2, 0, 0⟩,
          rho ⟨.J3, -1, -1⟩, rho ⟨.J1, 0, -1⟩, rho ⟨.J8, 0, 0⟩,
          rho ⟨.J7, 1, 0⟩]
        (∀ (k : Fin (6 : ℕ)), SimpleGridPathBetween (FootprintVertices (U k) ∩
            FootprintVertices (W k)) (FootprintEdges (U k) ∩ FootprintEdges (W k)) (p k) (l k) ∧
            p k ∈ FootprintVertices (K k) ∧ l k ∈ FootprintVertices (H k)) → ((∀
                {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {a : GaussianInt}, ∀
                {b : GaussianInt}, (SimpleGridPathBetween V E a b) → (a ∈ V ∧ b ∈ V)) → (
        let r := cfg.firstPredecessor
        let j : Fin 4 → Fin 3 := ![1, 2, 1, 2]
        let s : Fin 4 → Fin 4 := ![3, 0, 1, 2]
        let e : Fin 4 → Fin 6 := fun k => ⟨k.val, by omega⟩
        (0 < (r 2).1) → ((0 < (r 3).1) → (∀ (k : Fin 4), (x ∈ FootprintVertices (U (e k))) → ((x
            ∈ FootprintVertices (W (e k))) → (x ∈ FootprintVertices (TileTranslation (U (e k))
            ((⟨0, 1⟩ : GaussianInt) ^ (s k).val * (if Even (s k).val then BandVectors.1 (r 0) (r
            (j k).succ) else BandVectors.1 (r (j k).succ) (r 0)))) ↔ x = p (e k)))))))) := by
  classical
  intro q cfg C T cert x U W K H rho p l paths endpointMem r j s e pos2 pos3 k hu hw
  have hbU : BandPrototile (r 0) (U (e k)) := by
    fin_cases k <;> first
      | simpa [r, cfg.firstChild, U, e] using (cert.outer_occurrence 0 true).1
      | simpa [r, cfg.firstChild, U, e] using (cert.outer_occurrence 0 false).1
  have hbW : BandPrototile (r (j k).succ) (W (e k)) := by
    fin_cases k <;> simp only [j]
    all_goals first
      | simpa [r, cfg.firstParentTwo, W, e] using (cert.outer_occurrence 1 false).1
      | simpa [r, cfg.firstParentTwo, W, e] using (cert.outer_occurrence 1 true).1
      | simpa [r, cfg.firstParentThree, W, e] using (cert.outer_occurrence 2 false).1
      | simpa [r, cfg.firstParentThree, W, e] using (cert.outer_occurrence 2 true).1
  have hposW : 0 < (r (j k).succ).1 := by
    fin_cases k <;> first | exact pos2 | exact pos3
  have hposZ : 0 < (r ((if Even (s k).val then j k - 1 else j k + 1).succ)).1 := by
    fin_cases k <;> norm_num [j, s, show Even (0 : Nat) from by decide,
      show ¬Even (1 : Nat) from by decide,
      show Even (2 : Nat) from by decide,
      show ¬Even (3 : Nat) from by decide] <;> first | exact pos2 | exact pos3
  obtain ⟨Z, hbZ, hcZ⟩ := P3996T1AdjacentParentPlacement r cfg.firstProper
    (j k) (s k) (U (e k)) hbU
  have algebra := P4616T1FirstPredecessorCentroids q cfg C T cert k
  have hcW : TileCentroid (W (e k)) - TileCentroid (U (e k)) =
      (1 / 2 : Real) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ (s k).val *
          (BandVectors.1 (r (j k).succ) (r 0) + BandVectors.1 (r 0) (r (j k).succ))) := by
    fin_cases k <;> simpa [U, W, e, j, s, r] using algebra.1
  obtain ⟨R, I, _, hne, _, hlink, _, _⟩ :=
    BandOrientedChildParentEndpoints r cfg.firstProper (j k) (s k)
      (U (e k)) (W (e k)) Z hbU hbW hbZ
      (ProperBandCurvatureStructure r cfg.firstProper).1 hposW hposZ hcW hcZ
  have hbH : BandPrototile (r 0) (H (e k)) := by
    fin_cases k <;> dsimp [H, e] <;> apply BandPrototileTranslation
    all_goals first
      | simpa [r, cfg.firstChild] using (cert.outer_occurrence 0 false).1
      | simpa [r, cfg.firstChild] using (cert.outer_occurrence 0 true).1
  have hcH : TileCentroid (TileTranslation (U (e k))
      ((⟨0, 1⟩ : GaussianInt) ^ (s k).val *
        (if Even (s k).val then BandVectors.1 (r (j k).succ) (r 0)
          else BandVectors.1 (r 0) (r (j k).succ)))) = TileCentroid (H (e k)) := by
    fin_cases k <;> simpa [U, H, e, j, s, r] using algebra.2
  obtain ⟨hcell, hanchor⟩ := BandPrototileCentroidUnique _ _ _
    (BandPrototileTranslation _ _ _ hbU) hbH hcH
  have hfoot := (ProtoTileObservableExtensionality _ _ hcell hanchor).1
  have hl := (endpointMem (paths (e k)).1).2
  have hi : I.point = l (e k) := by
    apply Eq.symm
    apply (I.unique_common _).mp
    exact ⟨⟨hl.1, hfoot.symm ▸ (paths (e k)).2.2⟩, hl.2⟩
  have hpR : SimpleGridPathBetween
      (FootprintVertices (U (e k)) ∩ FootprintVertices (W (e k)))
      (FootprintEdges (U (e k)) ∩ FootprintEdges (W (e k))) R.point I.point := by
    simpa only [Set.inter_comm, hlink] using R.pathCA
  have he := SimpleGridPathEndpointPairUnique (paths (e k)).1 hpR
  have hr : R.point = p (e k) := by
    have hm : R.point ∈ ({p (e k), l (e k)} : Finset GaussianInt) := by
      rw [he]
      simp
    rcases (show R.point = p (e k) ∨ R.point = l (e k) by simpa using hm) with hr | hr
    · exact hr
    · exact (hne (hr.trans hi.symm)).elim
  constructor
  · intro h
    exact ((R.unique_common x).mp ⟨⟨hu, h⟩, hw⟩).trans hr
  · intro h
    exact ((R.unique_common x).mpr (h.trans hr.symm)).1.2

private theorem incident :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (N : ProtoTile), (N.cells.Nonempty) → ((x ∈ FootprintVertices N) →
            (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ N.cells)) ) := by
  classical
  intro x N hne hn
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hn
  rcases hn with ⟨a, ha, h | h | h | h⟩
  · exact ⟨0, by simpa [LatticeVertexIncidentCell] using h ▸ ha⟩
  · refine ⟨1, ?_⟩; rw [h]; simpa [LatticeVertexIncidentCell] using ha
  · refine ⟨3, ?_⟩; rw [h]; simpa [LatticeVertexIncidentCell] using ha
  · refine ⟨2, ?_⟩
    change x - 1 - ⟨0, 1⟩ ∈ N.cells
    rw [h]
    convert ha using 1
    ext <;> simp

private abbrev touchDisjoint := ApollonianSuperharmonic.TileTouchingDisjoint.cells

private theorem nested :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
          cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
        let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
          cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
        let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
          cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
        let H : Fin 6 → ProtoTile := ![
          TileTranslation (cert.P 0 false) (cert.u + cert.v),
          TileTranslation (cert.P 0 false) cert.v,
          TileTranslation (cert.P 0 true) (-cert.u - cert.v),
          TileTranslation (cert.P 0 true) (-cert.v),
          TileTranslation (cert.P 1 false) (-cert.u),
          TileTranslation (cert.P 1 true) cert.u]
        let rho := fun f : PeriodicSubtileFaceIndex =>
          cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f)
        let p : Fin 6 → GaussianInt := ![rho ⟨.I2, 0, 0⟩, rho ⟨.I3, 0, 0⟩,
          rho ⟨.I1, 0, 0⟩, rho ⟨.I4, 0, 0⟩, rho ⟨.I3, 0, 0⟩, rho ⟨.I4, 0, 0⟩]
        let l : Fin 6 → GaussianInt := ![rho ⟨.J4, 0, 0⟩, rho ⟨.J2, 0, 0⟩,
          rho ⟨.J3, -1, -1⟩, rho ⟨.J1, 0, -1⟩, rho ⟨.J8, 0, 0⟩,
          rho ⟨.J7, 1, 0⟩]
        (∀ (k : Fin (6 : ℕ)), SimpleGridPathBetween (FootprintVertices (U k) ∩ FootprintVertices
            (W k)) (FootprintEdges (U k) ∩ FootprintEdges (W k)) (p k) (l k) ∧ p k ∈
            FootprintVertices (K k) ∧ l k ∈ FootprintVertices (H k)) → ((∀ (k : Fin 6), Disjoint
            (U k).cells (W k).cells) → ((∀ (k : Fin 6), LatticeTile (U k)) → ((∀ (k : Fin 6),
            LatticeTile (W k)) → ((∀ (k : Fin 6), x ≠ l k) → ((∀ (N : ProtoTile),
            (N.cells.Nonempty) → ((x ∈ FootprintVertices N) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ N.cells))) → (∀ (k : Fin 6), ∀ (N : ProtoTile),
            (N.cells.Nonempty) → ((Disjoint N.cells (U k).cells) → ((Disjoint N.cells (W
            k).cells) → ((x = p k → x ∈ FootprintVertices N) → ((x ∈ FootprintVertices (U k)) →
            ((x ∈ FootprintVertices (W k)) → (x ∈ FootprintVertices N ↔ x = p k)))))))))))) ) := by
  classical
  intro q cfg C T cert x U W K H rho p l paths pairDisjoint diskU diskW exclude incident k N hne
      hNU hNW hpresent hu hw
  refine ⟨?_, hpresent⟩
  intro hn
  obtain ⟨j, hj⟩ := incident N hne hn
  apply (P4616T1ThirdOwnerPathEndpoint (U k) (W k) N (p k) (l k) x _
    (diskU k) (diskW k) (pairDisjoint k) (paths k).1 ⟨hu, hw⟩ ?_).resolve_right (exclude k)
  exact ⟨j, hj, fun h => Finset.disjoint_left.mp hNU hj h,
    fun h => Finset.disjoint_left.mp hNW hj h⟩

end MixedCompanionMarksGeometry

theorem P4590T1MixedCompanionMarks
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hT : LatticeTile T) (x : GaussianInt)
    (hx : x ∈ FootprintVertices T) (hxb : x ∉ BoundaryFootprintVertices T) :
    (x ∈ FootprintVertices (cert.P 0 true) → x ∈ FootprintVertices (cert.P 1 false) →
      (x ∈ FootprintVertices (TileTranslation (cert.P 0 true)
        ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
          (if Even (3 : Nat) then
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)
          else BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0)))) ↔
        x ∈ FootprintVertices (cert.P 0 false))) ∧
    (x ∈ FootprintVertices (cert.P 0 true) → x ∈ FootprintVertices (cert.P 2 false) →
      (x ∈ FootprintVertices (TileTranslation (cert.P 0 true)
        ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) *
          (if Even (0 : Nat) then
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)
          else BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)))) ↔
        x ∈ FootprintVertices (cert.P 1 true))) ∧
    (x ∈ FootprintVertices (cert.P 1 true) → x ∈ FootprintVertices (cert.P 0 false) →
      (x ∈ FootprintVertices (TileTranslation (cert.P 0 false)
        ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
          (if Even (1 : Nat) then
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)
          else BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0)))) ↔
        x ∈ FootprintVertices (cert.P 0 true))) ∧
    (x ∈ FootprintVertices (cert.P 2 true) → x ∈ FootprintVertices (cert.P 0 false) →
      (x ∈ FootprintVertices (TileTranslation (cert.P 0 false)
        ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
          (if Even (2 : Nat) then
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)
          else BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)))) ↔
        x ∈ FootprintVertices (cert.P 1 false))) ∧
    (x ∈ FootprintVertices (cert.P 1 true) → x ∈ FootprintVertices (cert.P 2 false) →
      (x ∈ FootprintVertices (TileTranslation (cert.P 1 true)
        ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
          (if Even (3 : Nat) then
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)
          else BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))) ↔
        x ∈ FootprintVertices (cert.P 0 true))) ∧
    (x ∈ FootprintVertices (cert.P 2 true) → x ∈ FootprintVertices (cert.P 1 false) →
      (x ∈ FootprintVertices (TileTranslation (cert.P 1 false)
        ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
          (if Even (1 : Nat) then
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)
          else BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))) ↔
        x ∈ FootprintVertices (cert.P 0 false))) := by
-- BODY
  classical
  let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
    cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
  let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
    cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
  let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
    cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
  let H : Fin 6 → ProtoTile := ![
    TileTranslation (cert.P 0 false) (cert.u + cert.v),
    TileTranslation (cert.P 0 false) cert.v,
    TileTranslation (cert.P 0 true) (-cert.u - cert.v),
    TileTranslation (cert.P 0 true) (-cert.v),
    TileTranslation (cert.P 1 false) (-cert.u),
    TileTranslation (cert.P 1 true) cert.u]
  let rho := fun f : PeriodicSubtileFaceIndex =>
    cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f)
  let p : Fin 6 → GaussianInt := ![rho ⟨.I2, 0, 0⟩, rho ⟨.I3, 0, 0⟩,
    rho ⟨.I1, 0, 0⟩, rho ⟨.I4, 0, 0⟩, rho ⟨.I3, 0, 0⟩, rho ⟨.I4, 0, 0⟩]
  let l : Fin 6 → GaussianInt := ![rho ⟨.J4, 0, 0⟩, rho ⟨.J2, 0, 0⟩,
    rho ⟨.J3, -1, -1⟩, rho ⟨.J1, 0, -1⟩, rho ⟨.J8, 0, 0⟩,
    rho ⟨.J7, 1, 0⟩]
  have paths := P4616T1OriginalMixedPaths q cfg C T cert
  change ∀ k, SimpleGridPathBetween
      (FootprintVertices (U k) ∩ FootprintVertices (W k))
      (FootprintEdges (U k) ∩ FootprintEdges (W k)) (p k) (l k) ∧
    p k ∈ FootprintVertices (K k) ∧ l k ∈ FootprintVertices (H k) at paths
  have endpointMem {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {a b : GaussianInt} (hp : SimpleGridPathBetween V E a b) : a ∈ V ∧ b ∈ V :=
          MixedCompanionMarksGeometry.endpointMem (V := V) (E := E) (a := a) (b := b) hp
  obtain ⟨_, _, _, _, _, _, _, separate⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  have pairDisjoint (k : Fin 6) : Disjoint (U k).cells (W k).cells :=
      MixedCompanionMarksGeometry.pairDisjoint q cfg C T cert separate k
  have diskU (k : Fin 6) : LatticeTile (U k) := by
    fin_cases k <;> exact cert.parent_lattice _ _
  have diskW (k : Fin 6) : LatticeTile (W k) := by
    fin_cases k <;> exact cert.parent_lattice _ _
  have rootstar := (P4456T2VertexInterior T
    (LatticeTileGridStructure T hT).1.1 x hx).2.mp hxb
  have exclude (k : Fin 6) : x ≠ l k := MixedCompanionMarksGeometry.exclude q cfg C T cert x
      paths rootstar k
  have sectors := P4616T1MixedCoarseSectors q cfg C T cert
  change ∀ k z, z ∈ FootprintVertices (U k) → z ∈ FootprintVertices (W k) →
    z ∈ FootprintVertices (K k) → ∃ j : Fin 4,
      LatticeVertexIncidentCell z j ∈ (K k).cells ∧
      LatticeVertexIncidentCell z j ∉ (U k).cells ∧
      LatticeVertexIncidentCell z j ∉ (W k).cells at sectors
  have coarse (k : Fin 6) (hu : x ∈ FootprintVertices (U k))
      (hw : x ∈ FootprintVertices (W k)) :
      x ∈ FootprintVertices (K k) ↔ x = p k := MixedCompanionMarksGeometry.coarse q cfg C T cert
          x paths pairDisjoint diskU diskW exclude sectors k hu hw
  let r := cfg.firstPredecessor
  let j : Fin 4 → Fin 3 := ![1, 2, 1, 2]
  let s : Fin 4 → Fin 4 := ![3, 0, 1, 2]
  let e : Fin 4 → Fin 6 := fun k => ⟨k.val, by omega⟩
  have pos2 : 0 < (r 2).1 := MixedCompanionMarksGeometry.pos2 q cfg
  have pos3 : 0 < (r 3).1 := MixedCompanionMarksGeometry.pos3 q cfg
  have firstFour (k : Fin 4) (hu : x ∈ FootprintVertices (U (e k)))
      (hw : x ∈ FootprintVertices (W (e k))) :
      x ∈ FootprintVertices (TileTranslation (U (e k))
        ((⟨0, 1⟩ : GaussianInt) ^ (s k).val *
          (if Even (s k).val then BandVectors.1 (r 0) (r (j k).succ)
            else BandVectors.1 (r (j k).succ) (r 0)))) ↔ x = p (e k) :=
                MixedCompanionMarksGeometry.firstFour q cfg C T cert x paths endpointMem pos2
                pos3 k hu hw
  have incident (N : ProtoTile) (hne : N.cells.Nonempty)
      (hn : x ∈ FootprintVertices N) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ N.cells :=
          MixedCompanionMarksGeometry.incident x N hne hn
  have touchDisjoint (M N : ProtoTile) (hm : M.cells.Nonempty)
      (hn : N.cells.Nonempty) (ht : TileTouching M N) : Disjoint M.cells N.cells :=
          MixedCompanionMarksGeometry.touchDisjoint M N hm hn ht
  have nested (k : Fin 6) (N : ProtoTile) (hne : N.cells.Nonempty)
      (hNU : Disjoint N.cells (U k).cells) (hNW : Disjoint N.cells (W k).cells)
      (hpresent : x = p k → x ∈ FootprintVertices N)
      (hu : x ∈ FootprintVertices (U k)) (hw : x ∈ FootprintVertices (W k)) :
      x ∈ FootprintVertices N ↔ x = p k := MixedCompanionMarksGeometry.nested q cfg C T cert x
          paths pairDisjoint diskU diskW exclude incident k N hne hNU hNW hpresent hu hw
  have hQdisk := P4590T1PositivePrototileDisk _ _
    (cert.plus_occurrence 1 true).1 pos2
  have hSdisk := P4590T1PositivePrototileDisk _ _
    (cert.minus_occurrence 1 false).1 pos2
  have hQne := (LatticeTileGridStructure _ hQdisk).1.1
  have hSne := (LatticeTileGridStructure _ hSdisk).1.1
  have hf := P4616T1NestedCompanionFootprints q cfg C T cert
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ha hd
    exact (firstFour 0 ha hd).trans (coarse 0 ha hd).symm
  · intro ha hf
    exact (firstFour 1 ha hf).trans (coarse 1 ha hf).symm
  · intro hc hb
    exact (firstFour 2 hb hc).trans (coarse 2 hb hc).symm
  · intro he hb
    exact (firstFour 3 hb he).trans (coarse 3 hb he).symm
  · intro hc hF
    have hn := nested 4 (cert.Q 1 true) hQne
      (touchDisjoint _ _ hQne (LatticeTileGridStructure _ (diskU 4)).1.1 cert.double_third.1)
      (touchDisjoint _ _ (LatticeTileGridStructure _ (diskW 4)).1.1 hQne
        cert.double_third.2.2.1).symm
      (fun h => by simpa [h, p, rho] using cert.inner_third.1) hc hF
    have ht := hn.trans (coarse 4 hc hF).symm
    simpa [show ¬Even (3 : Nat) from by decide, hf.1, K] using ht
  · intro he hd
    have hn := nested 5 (cert.S 1 false) hSne
      (touchDisjoint _ _ hSne (LatticeTileGridStructure _ (diskU 5)).1.1 cert.double_fourth.1)
      (touchDisjoint _ _ (LatticeTileGridStructure _ (diskW 5)).1.1 hSne
        cert.double_fourth.2.2.1).symm
      (fun h => (P4590T1JunctionRefinement q cfg C T cert hT x hx hxb).2.2.2
        ⟨(coarse 5 hd he).mpr h, hd, he⟩ |>.1.1) hd he
    have ht := hn.trans (coarse 5 hd he).symm
    simpa [show ¬Even (1 : Nat) from by decide, hf.2, K] using ht

end ApollonianSuperharmonic

end

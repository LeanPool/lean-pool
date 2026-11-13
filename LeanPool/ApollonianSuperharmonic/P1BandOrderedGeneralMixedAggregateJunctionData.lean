/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.GaussianRealPointProperties

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.FinitePatchTopology
public import LeanPool.ApollonianSuperharmonic.LatticeTileComplementGridConnected
public import LeanPool.ApollonianSuperharmonic.PeriodicTileMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P1BandOrderedGeneralMixedAggregateJunctionData]

/-!
# P1BandOrderedGeneralMixedAggregateJunctionData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MixedAggregateGeometry

private def incomingCertificateTrees : List (List (Nat × Nat)) :=
  [
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145)],
    [(187, 186), (188, 186), (189, 186), (191, 186), (190, 187)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145), (188, 147), (191, 147),
      (186, 188), (187, 188), (189, 186), (190, 187)],
    [],
    [(145, 144), (193, 144), (146, 144), (147, 144), (149, 144), (148, 145)],
    [(187, 186), (193, 186), (188, 186), (189, 186), (191, 186), (190, 187)],
    [(145, 144), (193, 144), (146, 144), (147, 144), (149, 144), (148, 145), (186, 193),
      (191, 193), (188, 147), (187, 186), (189, 186), (190, 187)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145)],
    [(151, 150), (152, 150), (153, 150), (155, 150), (154, 151)],
    [(145, 144), (151, 144), (146, 144), (147, 144), (154, 144), (149, 144), (148, 145),
      (150, 151), (152, 151), (153, 151), (155, 150)],
    [],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145), (105, 146)],
    [(151, 150), (152, 150), (153, 150), (155, 150), (105, 151), (154, 151)],
    [(145, 144), (151, 144), (146, 144), (147, 144), (154, 144), (149, 144), (148, 145),
      (150, 151), (152, 151), (105, 151), (153, 151), (155, 150)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145)],
    [(97, 96), (98, 96), (99, 96), (101, 96), (100, 97)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (96, 145), (99, 145), (148, 145),
      (97, 96), (98, 96), (101, 96), (100, 99)],
    [],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145), (143, 145)],
    [(97, 96), (98, 96), (99, 96), (101, 96), (100, 97), (143, 99)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (96, 145), (99, 145), (148, 145),
      (143, 145), (97, 96), (98, 96), (101, 96), (100, 99)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145)],
    [],
    [(145, 144), (146, 144), (147, 144), (149, 144), (138, 145), (148, 145)],
    [],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145), (188, 147)],
    [(188, 138)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (138, 145), (148, 145), (188, 147)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145)],
    [],
    [(145, 144), (146, 144), (194, 144), (147, 144), (149, 144), (148, 145)],
    [],
    [(145, 144), (146, 144), (147, 144), (154, 144), (149, 144), (148, 145)],
    [(154, 194)],
    [(145, 144), (146, 144), (194, 144), (147, 144), (154, 144), (149, 144), (148, 145)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145)],
    [],
    [(145, 144), (146, 144), (147, 144), (149, 144), (148, 145), (106, 146)],
    [],
    [(145, 144), (146, 144), (147, 144), (149, 144), (96, 145), (148, 145)],
    [(96, 106)],
    [(145, 144), (146, 144), (147, 144), (149, 144), (96, 145), (148, 145), (106, 146)]
  ]

private def outgoingCertificateTrees : List (List (Nat × Nat)) :=
  [
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193),
      (188, 138)],
    [(103, 102), (151, 102), (96, 103), (144, 151), (145, 96), (193, 144), (147, 144),
      (138, 145), (148, 145), (195, 193), (196, 193), (141, 138), (236, 195), (182, 141),
      (185, 141), (235, 236), (180, 182), (233, 235), (230, 180)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (150, 151), (153, 151),
      (154, 151), (97, 96), (99, 96), (199, 150), (194, 153), (90, 97), (140, 99), (143, 99),
      (192, 199), (193, 194), (139, 90), (138, 140), (241, 192), (195, 192), (196, 193),
      (132, 139), (141, 139), (234, 241), (236, 195), (181, 132), (185, 141), (235, 234),
      (180, 181), (233, 235), (230, 180)],
    [(151, 102), (150, 151), (144, 151), (199, 150), (194, 144), (147, 144), (192, 199),
      (188, 147), (191, 147), (195, 192), (186, 188), (196, 195)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (150, 151), (153, 151),
      (154, 151), (99, 96), (199, 150), (194, 153), (140, 99), (143, 99), (192, 199),
      (138, 140), (195, 192), (187, 138), (188, 138), (196, 195), (186, 187), (191, 188)],
    [(103, 102), (151, 102), (96, 103), (150, 151), (144, 151), (145, 96), (199, 150),
      (194, 144), (147, 144), (138, 145), (148, 145), (192, 199), (141, 138), (241, 192),
      (195, 192), (182, 141), (185, 141), (234, 241), (236, 195), (196, 195), (180, 182),
      (235, 234), (230, 180), (233, 235)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (150, 151), (153, 151),
      (154, 151), (97, 96), (99, 96), (199, 150), (194, 153), (90, 97), (140, 99), (143, 99),
      (192, 199), (139, 90), (138, 140), (241, 192), (195, 192), (132, 139), (141, 139),
      (234, 241), (236, 195), (196, 195), (181, 132), (185, 141), (235, 234), (180, 181),
      (233, 235), (230, 180)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193),
      (188, 138)],
    [(109, 102), (105, 102), (112, 102), (108, 109), (111, 109), (146, 105), (149, 105),
      (157, 108), (144, 146), (159, 157), (160, 157), (194, 144), (200, 159), (197, 194),
      (199, 200)],
    [(103, 102), (109, 102), (105, 102), (112, 102), (96, 103), (106, 103), (108, 109),
      (111, 109), (99, 96), (157, 108), (140, 99), (143, 99), (159, 157), (160, 157),
      (138, 140), (200, 159), (187, 138), (188, 138), (199, 200), (186, 187), (191, 188),
      (192, 199), (197, 199), (193, 186), (194, 192)],
    [(103, 102), (151, 102), (96, 103), (106, 103), (149, 151), (146, 96)],
    [(103, 102), (151, 102), (96, 103), (106, 103), (153, 151), (154, 151), (99, 96),
      (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193), (188, 138)],
    [(103, 102), (109, 102), (112, 102), (96, 103), (106, 103), (108, 109), (111, 109),
      (145, 96), (146, 96), (157, 108), (144, 145), (149, 146), (159, 157), (160, 157),
      (194, 144), (200, 159), (197, 194), (199, 200)],
    [(103, 102), (109, 102), (112, 102), (96, 103), (106, 103), (108, 109), (111, 109),
      (99, 96), (157, 108), (140, 99), (143, 99), (159, 157), (160, 157), (138, 140),
      (200, 159), (187, 138), (188, 138), (199, 200), (186, 187), (191, 188), (192, 199),
      (197, 199), (193, 186), (194, 192)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193),
      (188, 138)],
    [(103, 102), (151, 102), (105, 102), (54, 103), (57, 103), (106, 103), (144, 151),
      (146, 105), (55, 54), (58, 57), (145, 144), (48, 55), (138, 145), (143, 145), (51, 48),
      (139, 138), (140, 138), (95, 51), (90, 139)],
    [(103, 102), (151, 102), (105, 102), (54, 103), (57, 103), (106, 103), (153, 151),
      (154, 151), (55, 54), (58, 57), (194, 153), (48, 55), (193, 194), (51, 48), (186, 193),
      (191, 193), (92, 51), (95, 51), (187, 186), (188, 186), (90, 92), (138, 187),
      (140, 90), (143, 138)],
    [(103, 102), (96, 103), (145, 96), (99, 96), (138, 145), (140, 99)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (193, 194), (138, 140), (191, 193), (188, 138)],
    [(103, 102), (151, 102), (105, 102), (54, 103), (57, 103), (106, 103), (144, 151),
      (146, 105), (55, 54), (58, 57), (145, 144), (48, 55), (138, 145), (51, 48), (139, 138),
      (140, 138), (95, 51), (90, 139)],
    [(103, 102), (151, 102), (105, 102), (54, 103), (57, 103), (106, 103), (153, 151),
      (154, 151), (55, 54), (58, 57), (194, 153), (48, 55), (193, 194), (51, 48), (186, 193),
      (191, 193), (92, 51), (95, 51), (187, 186), (188, 186), (90, 92), (138, 187), (140, 90)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193),
      (188, 138)],
    [(103, 102), (151, 102), (96, 103), (144, 151), (97, 96), (145, 96), (99, 96),
      (193, 144), (147, 144), (90, 97), (148, 145), (143, 145), (140, 99), (186, 193),
      (188, 147), (139, 90), (187, 186), (141, 139)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (97, 96), (99, 96), (194, 153), (90, 97), (140, 99), (143, 99), (193, 194), (139, 90),
      (186, 193), (191, 193), (141, 139), (187, 186), (188, 186)],
    [(103, 102), (151, 102), (96, 103), (144, 151), (145, 96), (193, 144), (147, 144),
      (138, 145), (148, 145), (186, 193), (191, 193), (187, 138)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (186, 193),
      (191, 193), (187, 138)],
    [(103, 102), (151, 102), (96, 103), (144, 151), (97, 96), (145, 96), (99, 96),
      (193, 144), (147, 144), (90, 97), (148, 145), (143, 145), (140, 99), (186, 193),
      (191, 193), (139, 90), (187, 186), (141, 139)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (97, 96), (99, 96), (194, 153), (90, 97), (140, 99), (143, 99), (193, 194), (139, 90),
      (186, 193), (191, 193), (141, 139), (187, 186)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193),
      (188, 138)],
    [(151, 102), (150, 151), (144, 151), (153, 151), (154, 151), (199, 150), (193, 144),
      (197, 153), (192, 199)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (150, 151), (153, 151),
      (154, 151), (99, 96), (199, 150), (197, 153), (140, 99), (143, 99), (192, 199),
      (138, 140), (193, 192), (188, 138), (191, 193)],
    [(151, 102), (144, 151), (153, 151), (194, 144)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (99, 96),
      (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193), (188, 138)],
    [(151, 102), (150, 151), (144, 151), (153, 151), (199, 150), (193, 144), (197, 153),
      (192, 199)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (150, 151), (153, 151),
      (99, 96), (199, 150), (197, 153), (140, 99), (143, 99), (192, 199), (138, 140),
      (193, 192), (188, 138), (191, 193)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (106, 103), (153, 151), (154, 151),
      (99, 96), (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193),
      (188, 138)],
    [(103, 102), (105, 102), (96, 103), (146, 105)],
    [(103, 102), (151, 102), (105, 102), (96, 103), (153, 151), (154, 151), (99, 96),
      (194, 153), (140, 99), (143, 99), (193, 194), (138, 140), (191, 193), (188, 138)],
    [(103, 102), (151, 102), (105, 102), (57, 103), (106, 103), (101, 103), (144, 151),
      (146, 105), (98, 57), (145, 144), (97, 98), (99, 145)],
    [(103, 102), (151, 102), (105, 102), (57, 103), (106, 103), (101, 103), (153, 151),
      (154, 151), (98, 57), (194, 153), (97, 98), (193, 194), (90, 97), (99, 97), (186, 193),
      (191, 193), (139, 90), (143, 99), (188, 186), (138, 139)],
    [(103, 102), (151, 102), (105, 102), (57, 103), (101, 103), (144, 151), (146, 105),
      (98, 57), (145, 144), (97, 98), (99, 145)],
    [(103, 102), (151, 102), (105, 102), (57, 103), (101, 103), (153, 151), (154, 151),
      (98, 57), (194, 153), (97, 98), (193, 194), (90, 97), (99, 97), (186, 193), (191, 193),
      (139, 90), (143, 99), (188, 186), (138, 139)]
  ]


private theorem mixedNeighbors_symmetric :
    (by
      classical
      exact
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        ∀ {a : PeriodicSubtileIndex}, ∀ {b : PeriodicSubtileIndex}, (b ∈ mixedNeighbors a) → (a ∈
            mixedNeighbors b) ) := by
  classical
  intro mixedNeighbors a b h
  rcases a with ⟨l,m,n⟩
  cases l
  all_goals simp only [mixedNeighbors, Finset.mem_insert, Finset.mem_singleton] at h
  case A =>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (by simp only [])
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (by simp only []))
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (by simp only [])))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (by simp only [])
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (by simp only []))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (by simp only [])
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (by simp only [])
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (by simp only [])
  case B =>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (by simp only [])
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (by simp only []))
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (by simp only [])))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (by simp only [])))
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (by simp only []))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (by simp only [])))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (by simp only []))
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (by simp only []))
  case C =>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simp only []))))
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [])))))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simp only []))))
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simp only []))))
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (by simp only [])))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (by simp only [])))
  case D =>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only []))))))
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [])))))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only []))))))
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simp only []))))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr ((by simp only []))))
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr ((by simp only []))))
  case E =>
    rcases h with rfl | rfl | rfl | rfl
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only
          [])))))))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only
          [])))))))
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only
          [])))))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only
          [])))))
  case F =>
    rcases h with rfl | rfl | rfl | rfl
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by simp only
          []))))))))
    · simp only [mixedNeighbors, add_sub_cancel_right,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by simp only
          []))))))))
    · simp only [mixedNeighbors,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by simp only
          []))))))
    · simp only [mixedNeighbors, sub_add_cancel,
        Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by simp only
          []))))))

private theorem mixedNeighbors_iff :
    (by
      classical
      exact
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        (∀ {a : PeriodicSubtileIndex}, ∀ {b : PeriodicSubtileIndex}, (b ∈ mixedNeighbors a) → (a
            ∈ mixedNeighbors b)) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
            AllowedSubtileIncidence a b ↔ b ∈ mixedNeighbors a) ) := by
  classical
  intro mixedNeighbors mixedNeighbors_symmetric a b
  constructor
  · intro h
    induction h with
    | symm h ih => exact mixedNeighbors_symmetric ih
    | _ => simp only [mixedNeighbors,Finset.mem_insert,Finset.mem_singleton,
        ]; tauto
  · rcases a with ⟨l,m,n⟩
    cases l
    all_goals simp only [mixedNeighbors, Finset.mem_insert, Finset.mem_singleton]; intro h
    case A =>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AB m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AB01 m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AB11 m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AC m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AC11 m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AD m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AE01 m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.AF m n
    case B =>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AB m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AB01 m
          (n-1)).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AB11
          (m-1) (n-1)).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.BC m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.BDm1m1 m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.BD m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.BE m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.BF0m1 m n
    case C =>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AC m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AC11
          (m-1) (n-1)).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.BC m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.CDm10 m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.CEm10 m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.CF m n
    case D =>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AD m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.BDm1m1
          (m+1) (n+1)).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.BD m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.CDm10
          (m+1) n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.DE m n
      · simpa only [sub_add_cancel,add_sub_cancel_right] using AllowedSubtileIncidence.DF10 m n
    case E =>
      rcases h with rfl | rfl | rfl | rfl
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AE01 m
          (n-1)).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.BE m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.CEm10
          (m+1) n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.DE m
          n).symm
    case F =>
      rcases h with rfl | rfl | rfl | rfl
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.AF m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.BF0m1 m
          (n+1)).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.CF m
          n).symm
      · simpa only [sub_add_cancel,add_sub_cancel_right] using (AllowedSubtileIncidence.DF10
          (m-1) n).symm

private theorem mixed_walk_reach :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ (r : α → α → Prop), ∀ (S : α → Prop), ∀ (p : List α), ∀ (a : α), ∀ (b :
            α), (p.head? = some a) → ((p.getLast? = some b) → ((∀ x ∈ p, S x) → ((p.IsChain r) →
            (Relation.ReflTransGen (fun x y => r x y ∧ S x ∧ S y) a b)))) ) := by
  classical
  intro α r S p a b ha hb hm hc
  have hn : p ≠ [] := by intro h; subst p; simp at ha
  have hc' : p.IsChain (fun x y => r x y ∧ S x ∧ S y) :=
    hc.imp_of_mem_imp (fun x y hx hy hxy => ⟨hxy, hm x hx, hm y hy⟩)
  have h := List.relationReflTransGen_of_exists_isChain p hc' hn
  have heada : p.head hn = a := by simpa [List.head?_eq_some_head hn] using ha
  have lastb : p.getLast hn = b := by simpa [List.getLast?_eq_some_getLast hn] using hb
  simpa [heada, lastb] using h

private theorem mixed_reach_walk :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ (r : α → α → Prop), ∀ (S : α → Prop), ∀ (a : α), ∀ (b : α), (S a) →
            ((Relation.ReflTransGen (fun x y => r x y ∧ S x ∧ S y) a b) → (∃ p : List α, p.head?
            = some a ∧ p.getLast? = some b ∧ (∀ x ∈ p, S x) ∧ p.IsChain r)) ) := by
  classical
  intro α r S a b ha h
  obtain ⟨l,hc,hl⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  refine ⟨a::l, rfl, ?_, ?_, hc.imp (fun _ _ h => h.1)⟩
  · simpa [List.getLast?_eq_some_getLast (List.cons_ne_nil a l)] using congrArg some hl
  · have go : ∀ (u : α) (p : List α), S u →
        (u::p).IsChain (fun x y => r x y ∧ S x ∧ S y) →
        ∀ x ∈ u::p, S x := by
      intro u p
      induction p generalizing u with
      | nil => simp_all
      | cons v p ih =>
        intro hu hc x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact hx.symm ▸ hu
        · exact ih v hc.rel.2.2 hc.tail x (by simpa only [List.mem_cons] using hx)
    exact go a l ha hc

private theorem mixed_boundary_detour :
    (by
      classical
      exact
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        (∀ {α : Type}, ∀ (r : α → α → Prop), ∀ (S : α → Prop), ∀ (p : List α), ∀ (a : α), ∀ (b :
            α), (p.head? = some a) → ((p.getLast? = some b) → ((∀ x ∈ p, S x) → ((p.IsChain r) →
            (Relation.ReflTransGen (fun x y => r x y ∧ S x ∧ S y) a b))))) → (∀ (G :
            PlaneTriangulation PeriodicSubtileIndex), (∀ a, ∀ b, G.adjacent a b ↔ b ∈
            mixedNeighbors a) → (∀ (D : Finset PeriodicSubtileIndex), ∀ (hub :
            PeriodicSubtileIndex), (∀ a ∈ D, ∀ b ∈ mixedNeighbors a, b ∉ D →
            Relation.ReflTransGen (fun x y => G.adjacent x y ∧ x ∉ D ∧ y ∉ D) b hub) → (∀ a ∉ D,
                ∀ b ∉ D, Relation.ReflTransGen (fun x y => G.adjacent x y ∧ x ∉ D ∧ y ∉ D) a b)))
                ) := by
  classical
  intro mixedNeighbors mixed_walk_reach G hadj D hub hboundary
  classical
  intro a ha b hb
  obtain ⟨p,hp,hq,hm,hc⟩ := G.three_connected ∅ (by simp) a (by simp) b (by simp)
  have hpath := mixed_walk_reach G.adjacent (fun _ => True) p a b hp hq
    (by simp) ((List.isChain_iff_forall_rel_of_append_cons_cons).2 hc)
  let f : PeriodicSubtileIndex → PeriodicSubtileIndex := fun x => if x ∈ D then hub else x
  have liftStep : ∀ x y, (G.adjacent x y ∧ True ∧ True) →
      Relation.ReflTransGen (fun x y => G.adjacent x y ∧ x ∉ D ∧ y ∉ D) (f x) (f y) := by
    intro x y h
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
    · simp only [f, ite_eq_left hx, ite_eq_left hy]
      exact .refl
    · simp only [f, ite_eq_left hx, ite_eq_right hy]
      have hs : ∀ {u v},
          Relation.ReflTransGen (fun x y => G.adjacent x y ∧ x ∉ D ∧ y ∉ D) u v →
          Relation.ReflTransGen (fun x y => G.adjacent x y ∧ x ∉ D ∧ y ∉ D) v u := by
        intro u v hh
        induction hh with
        | refl => exact .refl
        | tail hh hs ih =>
          exact (Relation.ReflTransGen.single
            ⟨(G.adjacent_symmetric _ _).1 hs.1, hs.2.2, hs.2.1⟩).trans ih
      exact hs (hboundary x hx y ((hadj x y).1 h.1) hy)
    · simp only [f, ite_eq_right hx, ite_eq_left hy]
      exact hboundary y hy x ((hadj y x).1 ((G.adjacent_symmetric x y).1 h.1)) hx
    · simp only [f, ite_eq_right hx, ite_eq_right hy]
      exact .single ⟨h.1,hx,hy⟩
  simpa [Function.onFun,f,ha,hb] using hpath.lift' f liftStep

private theorem mixedTree_sound :
    (by
      classical
      exact
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        let mixedDecode (k : Nat) : PeriodicSubtileIndex :=
          ⟨match k % 6 with | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F,
            (k / 6 / 7 : Int) - 3, (k / 6 % 7 : Int) - 3⟩
        let mixedTreeVertices (tree : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) :
            Finset PeriodicSubtileIndex :=
          tree.foldl (fun S e => insert (mixedDecode e.1) S) S
        let mixedTreeCheck (D : Finset PeriodicSubtileIndex) (inside : Bool)
            (es : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) : Bool :=
          es.foldr (fun (a,b) next S =>
            decide ((if inside then mixedDecode a ∈ D else mixedDecode a ∉ D) ∧
              mixedDecode b ∈ S ∧ mixedDecode b ∈ mixedNeighbors (mixedDecode a)) &&
            next (insert (mixedDecode a) S)) (fun _ => true) S
        ∀ (G : PlaneTriangulation PeriodicSubtileIndex), (∀ a, ∀ b, G.adjacent a b ↔ b ∈
            mixedNeighbors a) → (∀ (D : Finset PeriodicSubtileIndex), ∀ (inside : Bool), ∀ (hub :
            PeriodicSubtileIndex), ∀ (es : List (Nat × Nat)), ∀ (S : Finset
            PeriodicSubtileIndex), (∀ a ∈ S, Relation.ReflTransGen (fun x y => G.adjacent x y ∧
            (if inside then x ∈ D else x ∉ D) ∧
            (if inside then y ∈ D else y ∉ D)) a hub) → ((∀ a ∈ S, if inside then a ∈ D else a ∉
                D) → ((mixedTreeCheck D inside es S = true) → (∀ a ∈ mixedTreeVertices es S,
                Relation.ReflTransGen (fun x y => G.adjacent x y ∧ (if inside then x ∈ D else x ∉
                D) ∧ (if inside then y ∈ D else y ∉ D)) a hub)))) ) := by
  classical
  intro mixedNeighbors mixedDecode mixedTreeVertices mixedTreeCheck G hadj D inside hub es S hS
      hmem h
  induction es generalizing S with
  | nil => exact hS
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    simp only [mixedTreeCheck, List.foldr, Bool.and_eq_true, decide_eq_true_eq] at h
    apply ih (insert (mixedDecode a) S) _ _ h.2
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact (Relation.ReflTransGen.single
          ⟨(hadj _ _).2 h.1.2.2, h.1.1, hmem _ h.1.2.1⟩).trans
          (hS _ h.1.2.1)
      · exact hS x hx
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact h.1.1
      · exact hmem x hx

private theorem mixed_certificates :
    (by
      classical
      exact
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        let mixedDecode (k : Nat) : PeriodicSubtileIndex :=
          ⟨match k % 6 with | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F,
            (k / 6 / 7 : Int) - 3, (k / 6 % 7 : Int) - 3⟩
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let mixedSelection (j : Fin 42) : Finset PeriodicSubtileIndex :=
          let c := mixedComponents (j.val / 7)
          let k := j.val % 7 + 1
          (if k % 2 = 1 then c.1 else ∅) ∪
            (if k / 2 % 2 = 1 then c.2.1 else ∅) ∪
            (if k / 4 % 2 = 1 then c.2.2 else ∅)
        let mixedTreeVertices (tree : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) :
            Finset PeriodicSubtileIndex :=
          tree.foldl (fun S e => insert (mixedDecode e.1) S) S
        let mixedTreeCheck (D : Finset PeriodicSubtileIndex) (inside : Bool)
            (es : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) : Bool :=
          es.foldr (fun (a,b) next S =>
            decide ((if inside then mixedDecode a ∈ D else mixedDecode a ∉ D) ∧
              mixedDecode b ∈ S ∧ mixedDecode b ∈ mixedNeighbors (mixedDecode a)) &&
            next (insert (mixedDecode a) S)) (fun _ => true) S
        let mixedInTrees : List (List (Nat × Nat)) :=
            MixedAggregateGeometry.incomingCertificateTrees
        let mixedOutTrees : List (List (Nat × Nat)) :=
            MixedAggregateGeometry.outgoingCertificateTrees
        let mixedInHubs : List Nat :=
            [144, 186, 144, 193, 144, 186, 144, 144, 150, 144, 105, 144, 150, 144, 144, 96,
              144, 143, 144, 96, 144, 144, 138, 144, 188, 144, 138, 144, 144, 194, 144, 154,
              144, 194, 144, 144, 106, 144, 96, 144, 106, 144]
        ∀ (j : Fin 42),
        let D := mixedSelection j
        let it := mixedInTrees.getD j.val []
        let ih := mixedDecode (mixedInHubs.getD j.val 0)
        let ot := mixedOutTrees.getD j.val []
        let oh := mixedDecode 102
        ih ∈ D ∧ oh ∉ D ∧
          mixedTreeCheck D true it {ih} = true ∧
          D ⊆ mixedTreeVertices it {ih} ∧
          mixedTreeCheck D false ot {oh} = true ∧
          D.biUnion mixedNeighbors \ D ⊆ mixedTreeVertices ot {oh} ) := by
  classical
  intro mixedNeighbors mixedDecode mixedBlock mixedComponents mixedSelection mixedTreeVertices
      mixedTreeCheck mixedInTrees mixedOutTrees mixedInHubs j
  revert j
  decide +kernel

private theorem mixed_patches :
    (by
      classical
      exact
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), AllowedSubtileIncidence a b
            ↔ b ∈ mixedNeighbors a) → ((∀ {α : Type}, ∀ (r : α → α → Prop), ∀ (S : α → Prop), ∀
            (a : α), ∀ (b : α), (S a) → ((Relation.ReflTransGen (fun x y => r x y ∧ S x ∧ S y) a
            b) → (∃ p : List α, p.head? = some a ∧ p.getLast? = some b ∧ (∀ x ∈ p, S x) ∧
            p.IsChain r))) → ((∀ (G : PlaneTriangulation PeriodicSubtileIndex), (∀ a, ∀ b,
            G.adjacent a b ↔ b ∈ mixedNeighbors a) → (∀ (D : Finset PeriodicSubtileIndex), ∀ (hub
            : PeriodicSubtileIndex), (∀ a ∈ D, ∀ b ∈ mixedNeighbors a, b ∉ D →
            Relation.ReflTransGen (fun x y => G.adjacent x y ∧ x ∉ D ∧ y ∉ D) b hub) → (∀ a ∉ D,
            ∀ b ∉ D, Relation.ReflTransGen (fun x y => G.adjacent x y ∧ x ∉ D ∧ y ∉ D) a b))) → (
        let mixedDecode (k : Nat) : PeriodicSubtileIndex :=
          ⟨match k % 6 with | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F,
            (k / 6 / 7 : Int) - 3, (k / 6 % 7 : Int) - 3⟩
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let mixedSelection (j : Fin 42) : Finset PeriodicSubtileIndex :=
          let c := mixedComponents (j.val / 7)
          let k := j.val % 7 + 1
          (if k % 2 = 1 then c.1 else ∅) ∪
            (if k / 2 % 2 = 1 then c.2.1 else ∅) ∪
            (if k / 4 % 2 = 1 then c.2.2 else ∅)
        let mixedTreeVertices (tree : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) :
            Finset PeriodicSubtileIndex :=
          tree.foldl (fun S e => insert (mixedDecode e.1) S) S
        let mixedTreeCheck (D : Finset PeriodicSubtileIndex) (inside : Bool)
            (es : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) : Bool :=
          es.foldr (fun (a,b) next S =>
            decide ((if inside then mixedDecode a ∈ D else mixedDecode a ∉ D) ∧
              mixedDecode b ∈ S ∧ mixedDecode b ∈ mixedNeighbors (mixedDecode a)) &&
            next (insert (mixedDecode a) S)) (fun _ => true) S
        (∀ (G : PlaneTriangulation PeriodicSubtileIndex), (∀ a, ∀ b, G.adjacent a b ↔ b ∈
            mixedNeighbors a) → (∀ (D : Finset PeriodicSubtileIndex), ∀ (inside : Bool), ∀ (hub :
            PeriodicSubtileIndex), ∀ (es : List (Nat × Nat)), ∀ (S : Finset
            PeriodicSubtileIndex), (∀ a ∈ S, Relation.ReflTransGen (fun x y => G.adjacent x y ∧
            (if inside then x ∈ D else x ∉ D) ∧ (if inside then y ∈ D else y ∉ D)) a hub) → ((∀ a
            ∈ S, if inside then a ∈ D else a ∉ D) → ((mixedTreeCheck D inside es S = true) → (∀ a
            ∈ mixedTreeVertices es S, Relation.ReflTransGen (fun x y => G.adjacent x y ∧ (if
            inside then x ∈ D else x ∉ D) ∧ (if inside then y ∈ D else y ∉ D)) a hub))))) → (
        let mixedInTrees : List (List (Nat × Nat)) :=
            MixedAggregateGeometry.incomingCertificateTrees
        let mixedOutTrees : List (List (Nat × Nat)) :=
            MixedAggregateGeometry.outgoingCertificateTrees
        let mixedInHubs : List Nat :=
            [144, 186, 144, 193, 144, 186, 144, 144, 150, 144, 105, 144, 150, 144, 144, 96,
              144, 143, 144, 96, 144, 144, 138, 144, 188, 144, 138, 144, 144, 194, 144, 154,
              144, 194, 144, 144, 106, 144, 96, 144, 106, 144]
        (∀ (j : Fin 42),
        let D := mixedSelection j
        let it := mixedInTrees.getD j.val []
        let ih := mixedDecode (mixedInHubs.getD j.val 0)
        let ot := mixedOutTrees.getD j.val []
        let oh := mixedDecode 102
        ih ∈ D ∧ oh ∉ D ∧
          mixedTreeCheck D true it {ih} = true ∧
          D ⊆ mixedTreeVertices it {ih} ∧
          mixedTreeCheck D false ot {oh} = true ∧
          D.biUnion mixedNeighbors \ D ⊆ mixedTreeVertices ot {oh}) → (∀ (q : Fin 4 →
              CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
              BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
              C₀ T), ∀ j : Fin 42, ∃ patch : FiniteInducedTilePatch cert.modified.plane
              cert.modified.tile, patch.indices = mixedSelection j ∧ LatticeTile
              patch.unionTile))))) ) := by
  classical
  intro mixedNeighbors mixedNeighbors_iff mixed_reach_walk mixed_boundary_detour mixedDecode
      mixedBlock mixedComponents mixedSelection mixedTreeVertices mixedTreeCheck mixedTree_sound
      mixedInTrees mixedOutTrees mixedInHubs mixed_certificates q cfg C₀ T cert j
  let D := mixedSelection j
  let it := mixedInTrees.getD j.val []
  let ih := mixedDecode (mixedInHubs.getD j.val 0)
  let ot := mixedOutTrees.getD j.val []
  let oh := mixedDecode 102
  obtain ⟨hi,ho,hit,his,hot,hos⟩ := mixed_certificates j
  have hadj : ∀ a b, cert.modified.plane.adjacent a b ↔ b ∈ mixedNeighbors a := by
    intro a b
    exact (cert.modified_adjacency a b).trans (mixedNeighbors_iff a b)
  have symreach (S : PeriodicSubtileIndex → Prop) {a b : PeriodicSubtileIndex}
      (h : Relation.ReflTransGen (fun x y => cert.modified.plane.adjacent x y ∧ S x ∧ S y) a b) :
      Relation.ReflTransGen (fun x y => cert.modified.plane.adjacent x y ∧ S x ∧ S y) b a := by
    induction h with
    | refl => exact .refl
    | tail h hs ih => exact (Relation.ReflTransGen.single
        ⟨(cert.modified.plane.adjacent_symmetric _ _).1 hs.1, hs.2.2, hs.2.1⟩).trans ih
  have ir : ∀ a ∈ D,
      Relation.ReflTransGen (fun x y => cert.modified.plane.adjacent x y ∧ x ∈ D ∧ y ∈ D) a ih
          := by
    intro a ha
    exact mixedTree_sound cert.modified.plane hadj D true ih it {ih}
      (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; exact .refl)
      (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; exact hi) hit a (his ha)
  have obr : ∀ a ∈ D, ∀ b ∈ mixedNeighbors a, b ∉ D →
      Relation.ReflTransGen (fun x y => cert.modified.plane.adjacent x y ∧ x ∉ D ∧ y ∉ D) b oh
          := by
    intro a ha b hb hbd
    have hbin : b ∈ D.biUnion mixedNeighbors \ D := by
      simp only [Finset.mem_sdiff, Finset.mem_biUnion]
      exact ⟨⟨a,ha,hb⟩,hbd⟩
    exact mixedTree_sound cert.modified.plane hadj D false oh ot {oh}
      (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; exact .refl)
      (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; exact ho) hot b (hos hbin)
  have oconn := mixed_boundary_detour cert.modified.plane hadj D oh obr
  let W : ProtoTile := ⟨D.biUnion (fun a => (cert.modified.tile a).cells), 0⟩
  let patch : FiniteInducedTilePatch cert.modified.plane cert.modified.tile := {
    indices := D
    unionTile := W
    nonempty := ⟨ih,hi⟩
    tile_injective := by
      intro a ha b hb heq
      obtain ⟨x,hx⟩ := (LatticeTileGridStructure _ (cert.modified.tiles_are_disks a)).1.1
      have hx' : x ∈ (cert.modified.tile a).cells := hx
      have hbx : x ∈ (cert.modified.tile b).cells := by rw [← heq]; exact hx'
      obtain ⟨c,hc,hunique⟩ := PeriodicTileIndexedMultiplicityOne cert.modified x
      exact (hunique a hx').trans (hunique b hbx).symm
    exact_union := by intro x; simp [W]
    induced_connected := by
      intro a ha b hb
      obtain ⟨p,hp,hq,hm,hc⟩ := mixed_reach_walk cert.modified.plane.adjacent
        (fun x => x ∈ D) a b ha ((ir a ha).trans (symreach _ (ir b hb)))
      exact ⟨p,hp,hq,hm,(List.isChain_iff_forall_rel_of_append_cons_cons).1 hc⟩
    complement_connected := by
      intro a ha b hb
      obtain ⟨p,hp,hq,hm,hc⟩ := mixed_reach_walk cert.modified.plane.adjacent
        (fun x => x ∉ D) a b ha (oconn a ha b hb)
      exact ⟨p,hp,hq,hm,(List.isChain_iff_forall_rel_of_append_cons_cons).1 hc⟩ }
  refine ⟨patch,rfl,?_⟩
  exact FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b _ h => cert.modified.adjacent_has_common_edge a b h) patch

private theorem restore_mixed :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (O : ProtoTile), ∀ (W : ProtoTile), ∀ (R :
            ProtoTile), (LatticeTile A) → ((LatticeTile (TileCellComplement A O)) → ((LatticeTile
            (TileCellComplement B O)) → ((LatticeTile W) → ((O.cells ⊆ A.cells) →
            (((TileCellComplement A O).cells ⊆ W.cells) → ((Disjoint B.cells W.cells) → ((R.cells
            = W.cells ∪ O.cells) → ((∀ x ∈ O.cells, ∀ y, FourNeighborAdjacent x y →
            y ∈ A.cells ∨ y ∈ B.cells) → (LatticeTile R))))))))) ) := by
  classical
  intro A B O W R hA hAm hBm hW hOA hAmW hBW hR hiso
  classical
  let reach (S : Set LatticeCell) := Relation.ReflTransGen
    (fun x y => FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S)
  have symadj {a b : LatticeCell} (h : FourNeighborAdjacent a b) :
      FourNeighborAdjacent b a := by
    rcases h with h | h | h | h <;> subst b <;>
      simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
  have symreach (S : Set LatticeCell) {a b : LatticeCell} (h : reach S a b) : reach S b a := by
    induction h with
    | refl => exact .refl
    | tail h hs ih => exact (Relation.ReflTransGen.single ⟨symadj hs.1,hs.2.2,hs.2.1⟩).trans ih
  have walk_reach : ∀ (S : Set LatticeCell) (p : List LatticeCell) (a b : LatticeCell),
      p.head? = some a → p.getLast? = some b →
      (∀ x ∈ p, x ∈ S) → p.IsChain FourNeighborAdjacent → reach S a b := by
    intro S p a b ha hb hm hc
    have hn : p ≠ [] := by intro h; subst p; simp at ha
    have hc' : p.IsChain (fun x y => FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S) :=
      hc.imp_of_mem_imp (fun x y hx hy hxy => ⟨hxy, hm x hx, hm y hy⟩)
    have h := List.relationReflTransGen_of_exists_isChain p hc' hn
    have heada : p.head hn = a := by simpa [List.head?_eq_some_head hn] using ha
    have lastb : p.getLast hn = b := by simpa [List.getLast?_eq_some_getLast hn] using hb
    simpa [heada,lastb] using h
  have connected_reach : ∀ (S : Set LatticeCell), FourNeighborConnected S →
      ∀ a ∈ S, ∀ b ∈ S, reach S a b := by
    intro S hc a ha b hb
    obtain ⟨p,hp,hq,hm,hchain⟩ := hc.2 a ha b hb
    exact walk_reach S p a b hp hq hm
      ((List.isChain_iff_forall_rel_of_append_cons_cons).2 hchain)
  have reach_walk : ∀ (S : Set LatticeCell) (a b : LatticeCell), a ∈ S → reach S a b →
      ∃ p : List LatticeCell, p.head? = some a ∧ p.getLast? = some b ∧
        (∀ x ∈ p, x ∈ S) ∧ p.IsChain FourNeighborAdjacent := by
    intro S a b ha h
    obtain ⟨l,hc,hl⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    refine ⟨a::l,rfl,?_,?_,hc.imp (fun _ _ h => h.1)⟩
    · simpa [List.getLast?_eq_some_getLast (List.cons_ne_nil a l)] using congrArg some hl
    · have go : ∀ (u : LatticeCell) (p : List LatticeCell), u ∈ S →
          (u::p).IsChain (fun x y => FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S) →
          ∀ x ∈ u::p, x ∈ S := by
        intro u p
        induction p generalizing u with
        | nil =>
          intro hu hc x hx
          have hxu : x = u := List.mem_singleton.mp hx
          exact hxu ▸ hu
        | cons v p ih =>
          intro hu hc x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact ih v hc.rel.2.2 hc.tail x (by simpa only [List.mem_cons] using hx)
      exact go a l ha hc
  have hAR : A.cells ⊆ R.cells := by
    intro x hx
    rw [hR]
    by_cases ho : x ∈ O.cells
    · exact Finset.mem_union_right _ ho
    · exact Finset.mem_union_left _ (hAmW (Finset.mem_sdiff.mpr ⟨hx,ho⟩))
  have hWR : W.cells ⊆ R.cells := by rw [hR]; exact Finset.subset_union_left
  have hBmR : ∀ x ∈ (TileCellComplement B O).cells, x ∉ R.cells := by
    intro x hx
    simp only [TileCellComplement, Finset.mem_sdiff] at hx
    rw [hR]
    simp only [Finset.mem_union, not_or]
    exact ⟨fun hw => Finset.disjoint_left.mp hBW hx.1 hw,hx.2⟩
  have mono_reach : ∀ (S U : Set LatticeCell), S ⊆ U →
      ∀ {a b}, reach S a b → reach U a b := by
    intro S U hsub a b h
    exact Relation.ReflTransGen.mono
      (fun x y hxy => ⟨hxy.1,hsub hxy.2.1,hsub hxy.2.2⟩) _ _ h
  have cw := (LatticeTileGridStructure W hW).1
  have ca := (LatticeTileGridStructure A hA).1
  have cm := (LatticeTileGridStructure (TileCellComplement A O) hAm).1
  have cb := (LatticeTileGridStructure (TileCellComplement B O) hBm).1
  obtain ⟨base,hbase⟩ := cm.1
  have hbaseA : base ∈ A.cells := (Finset.mem_sdiff.mp hbase).1
  have hbaseW : base ∈ W.cells := hAmW hbase
  have inbase : ∀ x ∈ R.cells, reach (R.cells : Set LatticeCell) x base := by
    intro x hx
    rw [hR, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact mono_reach _ _ hWR (connected_reach _ cw x hx base hbaseW)
    · exact mono_reach _ _ hAR (connected_reach _ ca x (hOA hx) base hbaseA)
  have inside : FourNeighborConnected (R.cells : Set LatticeCell) := by
    refine ⟨⟨base,hWR hbaseW⟩,?_⟩
    intro x hx y hy
    obtain ⟨p,hp,hq,hm,hc⟩ := reach_walk _ x y hx
      ((inbase x hx).trans (symreach _ (inbase y hy)))
    exact ⟨p,hp,hq,hm,(List.isChain_iff_forall_rel_of_append_cons_cons).1 hc⟩
  obtain ⟨outbase,houtbase⟩ := cb.1
  have cout := LatticeTileComplementGridConnected W hW
  have bconnect : ∀ x ∈ (TileCellComplement B O).cells,
      reach ((R.cells : Set LatticeCell)ᶜ) x outbase := by
    intro x hx
    exact mono_reach _ _ hBmR (connected_reach _ cb x hx outbase houtbase)
  have outside : FourNeighborConnected ((R.cells : Set LatticeCell)ᶜ) := by
    refine ⟨⟨outbase,hBmR outbase houtbase⟩,?_⟩
    intro x hx y hy
    have hxW : x ∉ W.cells := fun h => hx (hWR h)
    have hyW : y ∉ W.cells := fun h => hy (hWR h)
    have hxO : x ∉ O.cells := fun h => hx (hAR (hOA h))
    have hyO : y ∉ O.cells := fun h => hy (hAR (hOA h))
    let f : LatticeCell → LatticeCell := fun z => if z ∈ O.cells then outbase else z
    have cross : ∀ a ∈ O.cells, ∀ b, b ∉ W.cells → b ∉ O.cells →
        FourNeighborAdjacent a b → b ∈ (TileCellComplement B O).cells := by
      intro a ha b hb ho hab
      rcases hiso a ha b hab with hba | hbb
      · exact False.elim (hb (hAmW (Finset.mem_sdiff.mpr ⟨hba,ho⟩)))
      · exact Finset.mem_sdiff.mpr ⟨hbb,ho⟩
    have liftStep : ∀ a b,
        (FourNeighborAdjacent a b ∧ a ∉ W.cells ∧ b ∉ W.cells) →
        reach ((R.cells : Set LatticeCell)ᶜ) (f a) (f b) := by
      intro a b hab
      by_cases ha : a ∈ O.cells <;> by_cases hb : b ∈ O.cells
      · simp only [f,ite_eq_left ha,ite_eq_left hb]; exact .refl
      · simp only [f,ite_eq_left ha,ite_eq_right hb]
        exact symreach _ (bconnect b (cross a ha b hab.2.2 hb hab.1))
      · simp only [f,ite_eq_right ha,ite_eq_left hb]
        exact bconnect a (cross b hb a hab.2.1 ha (symadj hab.1))
      · simp only [f,ite_eq_right ha,ite_eq_right hb]
        exact .single ⟨hab.1,by simpa [hR] using And.intro hab.2.1 ha,
          by simpa [hR] using And.intro hab.2.2 hb⟩
    have hxy := (connected_reach _ cout x hxW y hyW).lift' f liftStep
    have hxy' : reach ((R.cells : Set LatticeCell)ᶜ) x y := by
      simpa [reach,Function.onFun,f,hxO,hyO] using hxy
    obtain ⟨p,hp,hq,hm,hc⟩ := reach_walk _ x y hx hxy'
    exact ⟨p,hp,hq,hm,(List.isChain_iff_forall_rel_of_append_cons_cons).1 hc⟩
  exact FinitePolyominoDiskCriterion R inside outside
    (FiniteConnectedCellSetNoCheckerboard R.cells inside outside)

private theorem cellDisk :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells = Y.cells) → (LatticeTile X ↔ LatticeTile
            Y) ) := by
  classical
  intro X Y hc
  unfold LatticeTile TileRealization
  rw [hc]

private theorem translation_complement :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), TileTranslation
            (TileCellComplement X O) u = TileCellComplement (TileTranslation X u)
            (TileTranslation O u) ) := by
  classical
  intro X O u
  unfold TileTranslation TileCellComplement
  rw [Finset.image_sdiff X.cells O.cells
    (show Function.Injective (GaussianTranslation u) from
      fun _ _ h => add_right_cancel h)]

private theorem hOA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), cert.O.cells ⊆ (cert.P 0 true).cells ) := by
  classical
  intro q cfg C₀ T cert x hx
  rw [cert.precursor_eq] at hx
  exact (cert.plus_union x).2 ⟨0,false,hx⟩

private theorem hOB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), cert.O.cells ⊆ (cert.P 0 false).cells ) := by
  classical
  intro q cfg C₀ T cert x hx
  rw [cert.precursor_cells] at hx
  exact (cert.minus_union x).2 ⟨0,true,hx⟩

private theorem original_lattice :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        ∀ (a : PeriodicSubtileIndex), LatticeTile (original a) ) := by
  classical
  intro q cfg C₀ T cert original a
  rcases a with ⟨l,m,n⟩
  cases l <;> exact (TileDiskAreaCovariance _ _).1.mp (cert.parent_lattice _ _)

private theorem mod_nonA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        ∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (cert.modified.tile a = original a) ) := by
  classical
  intro q cfg C₀ T cert original a h
  rw [cert.modified_tile]
  rcases a with ⟨l,m,n⟩
  cases l
  · exact False.elim (h rfl)
  all_goals rfl

private theorem mod_A :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let offset (a : PeriodicSubtileIndex) : GaussianInt :=
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let precursor (a : PeriodicSubtileIndex) := TileTranslation cert.O (offset a)
        (∀ (X : ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), TileTranslation
            (TileCellComplement X O) u = TileCellComplement (TileTranslation X u)
            (TileTranslation O u)) → (∀ (a : PeriodicSubtileIndex), (a.label = .A) →
            (cert.modified.tile a = TileCellComplement (original a) (precursor a))) ) := by
  classical
  intro q cfg C₀ T cert original offset precursor translation_complement a h
  rw [cert.modified_tile]
  rcases a with ⟨l,m,n⟩
  cases h
  exact translation_complement _ _ _

private theorem precursor_subset_A :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let offset (a : PeriodicSubtileIndex) : GaussianInt :=
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let precursor (a : PeriodicSubtileIndex) := TileTranslation cert.O (offset a)
        (cert.O.cells ⊆ (cert.P 0 true).cells) → (∀ (a : PeriodicSubtileIndex), (a.label = .A) →
            ((precursor a).cells ⊆ (original a).cells)) ) := by
  classical
  intro q cfg C₀ T cert original offset precursor hOA a h
  rcases a with ⟨l,m,n⟩
  cases h
  exact Finset.image_mono _ hOA

private theorem precursor_subset_B :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let offset (a : PeriodicSubtileIndex) : GaussianInt :=
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let precursor (a : PeriodicSubtileIndex) := TileTranslation cert.O (offset a)
        let paired (a : PeriodicSubtileIndex) : PeriodicSubtileIndex := ⟨.B,a.first,a.second⟩
        (cert.O.cells ⊆ (cert.P 0 false).cells) → (∀ (a : PeriodicSubtileIndex), (precursor
            a).cells ⊆ (original (paired a)).cells) ) := by
  classical
  intro q cfg C₀ T cert original offset precursor paired hOB a
  exact Finset.image_mono _ hOB

private theorem mod_subset :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let offset (a : PeriodicSubtileIndex) : GaussianInt :=
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let precursor (a : PeriodicSubtileIndex) := TileTranslation cert.O (offset a)
        (∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (cert.modified.tile a = original a)) →
            ((∀ (a : PeriodicSubtileIndex), (a.label = .A) → (cert.modified.tile a =
            TileCellComplement (original a) (precursor a))) → (∀ (a : PeriodicSubtileIndex),
            (cert.modified.tile a).cells ⊆ (original a).cells)) ) := by
  classical
  intro q cfg C₀ T cert original offset precursor mod_nonA mod_A a
  by_cases h : a.label = .A
  · rw [mod_A a h]
    exact Finset.sdiff_subset
  · rw [mod_nonA a h]

private theorem exception_certificate :
    (by
      classical
      exact
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let mixedSelection (j : Fin 42) : Finset PeriodicSubtileIndex :=
          let c := mixedComponents (j.val / 7)
          let k := j.val % 7 + 1
          (if k % 2 = 1 then c.1 else ∅) ∪
            (if k / 2 % 2 = 1 then c.2.1 else ∅) ∪
            (if k / 4 % 2 = 1 then c.2.2 else ∅)
        let paired (a : PeriodicSubtileIndex) : PeriodicSubtileIndex := ⟨.B,a.first,a.second⟩
        let exception (j : Fin 42) : Option PeriodicSubtileIndex :=
          if j.val / 7 = 3 ∧ (j.val % 7 + 1) / 2 % 2 = 1 then some ⟨.A,0,-1⟩ else
          if j.val / 7 = 5 ∧ (j.val % 7 + 1) / 4 % 2 = 1 then some ⟨.A,-1,-1⟩ else none
        ∀ (j : Fin 42), (∀ a ∈ mixedSelection j, a.label = .A → paired a ∈ mixedSelection j ∨
            exception j = some a) ∧ (match exception j with
              | none => True
              | some a => a ∈ mixedSelection j ∧ a.label = .A ∧
                  paired a ∉ mixedSelection j) ) := by
  classical
  intro mixedBlock mixedComponents mixedSelection paired exception j
  let validException (j : Fin 42) : Bool := match exception j with
    | none => true
    | some a => decide (a ∈ mixedSelection j ∧ a.label = .A ∧ paired a ∉ mixedSelection j)
  have finiteCheck : ∀ j : Fin 42,
      (mixedSelection j).filter (fun a => ¬ (a.label = .A →
        paired a ∈ mixedSelection j ∨ exception j = some a)) = ∅ ∧
      validException j = true := by
    decide +kernel
  obtain ⟨h₁,h₂⟩ := finiteCheck j
  constructor
  · simpa only [Finset.filter_eq_empty_iff, not_not] using h₁
  · cases he : exception j with
    | none => trivial
    | some a =>
      apply of_decide_eq_true
      simpa only [validException, he] using h₂

private theorem shared_vertex :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (x : LatticeCell), (x ∈ O.cells) → (∀ (y : LatticeCell),
            (FourNeighborAdjacent x y) → (∃ v, v ∈ FootprintVertices O ∧ v ∈ FootprintVertices
            (⟨{y},y⟩ : ProtoTile))) ) := by
  classical
  intro O x hx y hxy
  have hn : O.cells.Nonempty := ⟨x,hx⟩
  rcases hxy with rfl | rfl | rfl | rfl
  · refine ⟨x+1, ?_, ?_⟩
    · simp only [FootprintVertices,ite_eq_left hn,Set.mem_ofPred_eq]
      exact ⟨x,hx,Or.inr (Or.inl rfl)⟩
    · simp [FootprintVertices]
  · refine ⟨x, ?_, ?_⟩
    · simp only [FootprintVertices,ite_eq_left hn,Set.mem_ofPred_eq]
      exact ⟨x,hx,Or.inl rfl⟩
    · simp [FootprintVertices]
  · refine ⟨x+⟨0,1⟩, ?_, ?_⟩
    · simp only [FootprintVertices,ite_eq_left hn,Set.mem_ofPred_eq]
      exact ⟨x,hx,Or.inr (Or.inr (Or.inl rfl))⟩
    · simp [FootprintVertices]
  · refine ⟨x, ?_, ?_⟩
    · simp only [FootprintVertices,ite_eq_left hn,Set.mem_ofPred_eq]
      exact ⟨x,hx,Or.inl rfl⟩
    · simp [FootprintVertices]

private theorem original_patches :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let mixedSelection (j : Fin 42) : Finset PeriodicSubtileIndex :=
          let c := mixedComponents (j.val / 7)
          let k := j.val % 7 + 1
          (if k % 2 = 1 then c.1 else ∅) ∪
            (if k / 2 % 2 = 1 then c.2.1 else ∅) ∪
            (if k / 4 % 2 = 1 then c.2.2 else ∅)
        (∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ j : Fin 42, ∃ patch : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile, patch.indices = mixedSelection j ∧ LatticeTile patch.unionTile) →
            ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (O : ProtoTile), ∀ (W : ProtoTile), ∀ (R :
            ProtoTile), (LatticeTile A) → ((LatticeTile (TileCellComplement A O)) → ((LatticeTile
            (TileCellComplement B O)) → ((LatticeTile W) → ((O.cells ⊆ A.cells) →
            (((TileCellComplement A O).cells ⊆ W.cells) → ((Disjoint B.cells W.cells) → ((R.cells
            = W.cells ∪ O.cells) → ((∀ x ∈ O.cells, ∀ y, FourNeighborAdjacent x y → y ∈ A.cells ∨
            y ∈ B.cells) → (LatticeTile R)))))))))) → (
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let offset (a : PeriodicSubtileIndex) : GaussianInt :=
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let precursor (a : PeriodicSubtileIndex) := TileTranslation cert.O (offset a)
        let paired (a : PeriodicSubtileIndex) : PeriodicSubtileIndex := ⟨.B,a.first,a.second⟩
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells = Y.cells) → (LatticeTile X ↔ LatticeTile
            Y)) → ((∀ (X : ProtoTile), ∀ (O : ProtoTile), ∀ (u : GaussianInt), TileTranslation
            (TileCellComplement X O) u = TileCellComplement (TileTranslation X u)
            (TileTranslation O u)) → ((∀ (a : PeriodicSubtileIndex), LatticeTile (original a)) →
            ((∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (cert.modified.tile a = original a))
            → ((∀ (a : PeriodicSubtileIndex), (a.label = .A) → (cert.modified.tile a =
            TileCellComplement (original a) (precursor a))) → ((∀ (a : PeriodicSubtileIndex),
            (a.label = .A) → ((precursor a).cells ⊆ (original a).cells)) → ((∀ (a :
            PeriodicSubtileIndex), (precursor a).cells ⊆ (original (paired a)).cells) → ((∀ (a :
            PeriodicSubtileIndex), (cert.modified.tile a).cells ⊆ (original a).cells) → (
        let exception (j : Fin 42) : Option PeriodicSubtileIndex :=
          if j.val / 7 = 3 ∧ (j.val % 7 + 1) / 2 % 2 = 1 then some ⟨.A,0,-1⟩ else
          if j.val / 7 = 5 ∧ (j.val % 7 + 1) / 4 % 2 = 1 then some ⟨.A,-1,-1⟩ else none
        (∀ (j : Fin 42), (∀ a ∈ mixedSelection j, a.label = .A → paired a ∈ mixedSelection j ∨
            exception j = some a) ∧ (match exception j with
              | none => True
              | some a => a ∈ mixedSelection j ∧ a.label = .A ∧
                  paired a ∉ mixedSelection j)) → ((∀ (O :
            ProtoTile), ∀ (x : LatticeCell), (x ∈ O.cells) → (∀ (y : LatticeCell),
            (FourNeighborAdjacent x y) → (∃ v, v ∈ FootprintVertices O ∧ v ∈ FootprintVertices
            (⟨{y},y⟩ : ProtoTile)))) → (∀ j : Fin 42, LatticeTile (⟨(mixedSelection j).biUnion
            (fun a => (original a).cells),0⟩ : ProtoTile))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock mixedComponents mixedSelection mixed_patches restore_mixed
      original offset precursor paired cellDisk translation_complement original_lattice mod_nonA
      mod_A precursor_subset_A precursor_subset_B mod_subset exception exception_certificate
      shared_vertex j
  let D := mixedSelection j
  let R : ProtoTile := ⟨D.biUnion (fun a => (original a).cells),0⟩
  obtain ⟨W,hWD,hW⟩ := mixed_patches q cfg C₀ T cert j
  have exactW (x : LatticeCell) : x ∈ W.unionTile.cells ↔
      ∃ a ∈ D, x ∈ (cert.modified.tile a).cells := by
    simpa [hWD] using W.exact_union x
  have exactR (x : LatticeCell) : x ∈ R.cells ↔
      ∃ a ∈ D, x ∈ (original a).cells := by simp [R]
  obtain ⟨hpaired,hexc⟩ := exception_certificate j
  have hWR : W.unionTile.cells ⊆ R.cells := by
    intro x hx
    obtain ⟨a,ha,hx⟩ := (exactW x).1 hx
    exact (exactR x).2 ⟨a,ha,mod_subset a hx⟩
  have split_cell (a : PeriodicSubtileIndex) (ha : a ∈ D) (x : LatticeCell)
      (hx : x ∈ (original a).cells) :
      x ∈ W.unionTile.cells ∨
        (exception j = some a ∧ x ∈ (precursor a).cells) := by
    by_cases hl : a.label = .A
    · by_cases ho : x ∈ (precursor a).cells
      · rcases hpaired a ha hl with hb | he
        · left
          apply (exactW x).2
          refine ⟨paired a,hb,?_⟩
          rw [mod_nonA (paired a) (by simp [paired])]
          exact precursor_subset_B a ho
        · exact Or.inr ⟨he,ho⟩
      · left
        apply (exactW x).2
        refine ⟨a,ha,?_⟩
        rw [mod_A a hl]
        exact Finset.mem_sdiff.mpr ⟨hx,ho⟩
    · left
      exact (exactW x).2 ⟨a,ha,by rw [mod_nonA a hl]; exact hx⟩
  cases he : exception j with
  | none =>
    have hc : R.cells = W.unionTile.cells := by
      apply Finset.Subset.antisymm _ hWR
      intro x hx
      obtain ⟨a,ha,hx⟩ := (exactR x).1 hx
      rcases split_cell a ha x hx with hx | ⟨he',hx⟩
      · exact hx
      · simp [he] at he'
    exact (cellDisk R W.unionTile hc).2 hW
  | some a =>
    rw [he] at hexc
    obtain ⟨ha,hl,hbn⟩ := hexc
    have hc : R.cells = W.unionTile.cells ∪ (precursor a).cells := by
      ext x
      constructor
      · intro hx
        obtain ⟨b,hb,hx⟩ := (exactR x).1 hx
        rcases split_cell b hb x hx with hx | ⟨he',hx⟩
        · exact Finset.mem_union_left _ hx
        · have hab : a = b := Option.some.inj (he.symm.trans he')
          subst b
          exact Finset.mem_union_right _ hx
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hWR hx
        · exact (exactR x).2 ⟨a,ha,precursor_subset_A a hl hx⟩
    have hBW : Disjoint (original (paired a)).cells W.unionTile.cells := by
      apply Finset.disjoint_left.mpr
      intro x hxB hxW
      obtain ⟨b,hb,hxb⟩ := (exactW x).1 hxW
      have hxBa : x ∈ (cert.modified.tile (paired a)).cells := by
        rw [mod_nonA (paired a) (by simp [paired])]
        exact hxB
      obtain ⟨c,hc,hunique⟩ := PeriodicTileIndexedMultiplicityOne cert.modified x
      have hba : b = paired a := (hunique b hxb).trans (hunique _ hxBa).symm
      exact hbn (hba ▸ hb)
    have hBm : LatticeTile (TileCellComplement (original (paired a)) (precursor a)) := by
      have hb := (TileDiskAreaCovariance _ (offset a)).1.mp cert.precursor_complement_lattice.2
      rw [translation_complement] at hb
      exact hb
    refine restore_mixed (original a) (original (paired a)) (precursor a) W.unionTile R
      (original_lattice a)
      ((mod_A a hl) ▸ cert.modified.tiles_are_disks a)
      hBm hW (precursor_subset_A a hl) ?_ hBW hc ?_
    · intro x hx
      apply (exactW x).2
      exact ⟨a,ha,(mod_A a hl).symm ▸ hx⟩
    · intro x hx y hxy
      obtain ⟨v,hv,hvy⟩ := shared_vertex (precursor a) x hx y hxy
      have hi := cert.precursor_isolated a.first a.second v hv y hvy
      rcases a with ⟨l,m,n⟩
      cases hl
      exact hi

private theorem selection_certificate :
    (by
      classical
      exact
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let mixedSelection (j : Fin 42) : Finset PeriodicSubtileIndex :=
          let c := mixedComponents (j.val / 7)
          let k := j.val % 7 + 1
          (if k % 2 = 1 then c.1 else ∅) ∪
            (if k / 2 % 2 = 1 then c.2.1 else ∅) ∪
            (if k / 4 % 2 = 1 then c.2.2 else ∅)
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let selectionIndex (r : Fin 6) (s : Fin 7) : Fin 42 := ⟨r.val * 7 + s.val,by omega⟩
        ∀ (r : Fin 6), mixedSelection (selectionIndex r 0) = componentIndices r 0 ∧
            mixedSelection (selectionIndex r 1) = componentIndices r 1 ∧ mixedSelection
            (selectionIndex r 3) = componentIndices r 2 ∧ mixedSelection (selectionIndex r 2) =
            componentIndices r 0 ∪ componentIndices r 1 ∧ mixedSelection (selectionIndex r 5) =
            componentIndices r 1 ∪ componentIndices r 2 ∧ mixedSelection (selectionIndex r 4) =
            componentIndices r 2 ∪ componentIndices r 0 ∧ mixedSelection (selectionIndex r 6) =
            componentIndices r 0 ∪ componentIndices r 1 ∪ componentIndices r 2 ) := by
  classical
  intro mixedBlock mixedComponents mixedSelection componentIndices selectionIndex r
  revert r
  decide +kernel

private theorem owner_certificate :
    (by
      classical
      exact
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let paired (a : PeriodicSubtileIndex) : PeriodicSubtileIndex := ⟨.B,a.first,a.second⟩
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let owners (D : Finset PeriodicSubtileIndex) :=
          D ∪ (D.filter (fun a => a.label = .A)).image paired
        ∀ (r : Fin 6), ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) → (Disjoint (owners
            (componentIndices r s)) (owners (componentIndices r t))) ) := by
  classical
  intro mixedBlock mixedComponents paired componentIndices owners r s t hst
  have hc : ∀ (r : Fin 6) (s t : Fin 3), s ≠ t →
      Disjoint (owners (componentIndices r s)) (owners (componentIndices r t)) := by
    decide +kernel
  exact hc r s t hst

private theorem edge_certificate :
    (by
      classical
      exact
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        ∀ (r : Fin 6), ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) → (((componentIndices r s).biUnion
            mixedNeighbors ∩ componentIndices r t).Nonempty) ) := by
  classical
  intro mixedNeighbors mixedBlock mixedComponents componentIndices r s t hst
  have hc : ∀ (r : Fin 6) (s t : Fin 3), s ≠ t →
      ((componentIndices r s).biUnion mixedNeighbors ∩ componentIndices r t).Nonempty := by
    decide +kernel
  exact hc r s t hst

private theorem original_owner :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let offset (a : PeriodicSubtileIndex) : GaussianInt :=
          (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
        let precursor (a : PeriodicSubtileIndex) := TileTranslation cert.O (offset a)
        let paired (a : PeriodicSubtileIndex) : PeriodicSubtileIndex := ⟨.B,a.first,a.second⟩
        (∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (cert.modified.tile a = original a)) →
            ((∀ (a : PeriodicSubtileIndex), (a.label = .A) → (cert.modified.tile a =
            TileCellComplement (original a) (precursor a))) → ((∀ (a : PeriodicSubtileIndex),
            (precursor a).cells ⊆ (original (paired a)).cells) → (
        let owners (D : Finset PeriodicSubtileIndex) :=
          D ∪ (D.filter (fun a => a.label = .A)).image paired
        ∀ (a : PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈ (original a).cells) → (∃ b ∈
            owners {a}, x ∈ (cert.modified.tile b).cells)))) ) := by
  classical
  intro q cfg C₀ T cert original offset precursor paired mod_nonA mod_A precursor_subset_B owners
      a x hx
  by_cases hl : a.label = .A
  · by_cases ho : x ∈ (precursor a).cells
    · refine ⟨paired a, ?_, ?_⟩
      · simp [owners,hl]
      · rw [mod_nonA (paired a) (by simp [paired])]
        exact precursor_subset_B a ho
    · refine ⟨a,by simp [owners],?_⟩
      rw [mod_A a hl]
      exact Finset.mem_sdiff.mpr ⟨hx,ho⟩
  · exact ⟨a,by simp [owners],by rw [mod_nonA a hl]; exact hx⟩

private theorem component_disjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let paired (a : PeriodicSubtileIndex) : PeriodicSubtileIndex := ⟨.B,a.first,a.second⟩
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let owners (D : Finset PeriodicSubtileIndex) :=
          D ∪ (D.filter (fun a => a.label = .A)).image paired
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        let component (r : Fin 6) (s : Fin 3) := unionOf (componentIndices r s)
        (∀ (r : Fin 6), ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) → (Disjoint (owners
            (componentIndices r s)) (owners (componentIndices r t)))) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈ (original a).cells) → (∃ b ∈ owners
            {a}, x ∈ (cert.modified.tile b).cells)) → ((∀ {D : Finset PeriodicSubtileIndex}, ∀
            {E : Finset PeriodicSubtileIndex}, (D ⊆ E) → (owners D ⊆ owners E)) → (∀ (r : Fin 6),
            ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) → (Disjoint (component r s).cells (component r
            t).cells)))) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock mixedComponents original paired componentIndices owners
      unionOf component owner_certificate original_owner owners_mono r s t hst
  apply Finset.disjoint_left.mpr
  intro x hs ht
  obtain ⟨a,ha,hxa⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨b,hb,hxb⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨u,hu,hxu⟩ := original_owner a x hxa
  obtain ⟨v,hv,hxv⟩ := original_owner b x hxb
  have hu' := owners_mono (Finset.singleton_subset_iff.mpr ha) hu
  have hv' := owners_mono (Finset.singleton_subset_iff.mpr hb) hv
  obtain ⟨c,hc,hunique⟩ := PeriodicTileIndexedMultiplicityOne cert.modified x
  have huv : u = v := (hunique u hxu).trans (hunique v hxv).symm
  exact Finset.disjoint_left.mp (owner_certificate r s t hst) hu' (huv.symm ▸ hv')

private theorem edges_mono :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆ Y.cells) → (FootprintEdges X ⊆
            FootprintEdges Y) ) := by
  classical
  intro X Y h e he
  obtain ⟨x,hx,hshape⟩ := he
  exact ⟨x,h hx,hshape⟩

private theorem component_edges :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
          let m := a.first
          let n := a.second
          match a.label with
          | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
              ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
          | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
              ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
          | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
              ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
          | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
              ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
          | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
          | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), AllowedSubtileIncidence a b
            ↔ b ∈ mixedNeighbors a) → (
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (∀ (a : PeriodicSubtileIndex), (cert.modified.tile a).cells ⊆ (original a).cells) → (
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        let component (r : Fin 6) (s : Fin 3) := unionOf (componentIndices r s)
        (∀ (r : Fin 6), ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) → (((componentIndices r s).biUnion
            mixedNeighbors ∩ componentIndices r t).Nonempty)) → ((∀ (X : ProtoTile), ∀ (Y :
            ProtoTile), (X.cells ⊆ Y.cells) → (FootprintEdges X ⊆ FootprintEdges Y)) → (∀ (r :
            Fin 6), ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) → ((FootprintEdges (component r s) ∩
            FootprintEdges (component r t)).Nonempty))))) ) := by
  classical
  intro q cfg C₀ T cert mixedNeighbors mixedNeighbors_iff mixedBlock mixedComponents original
      mod_subset componentIndices unionOf component edge_certificate edges_mono r s t hst
  obtain ⟨b,hb⟩ := edge_certificate r s t hst
  obtain ⟨hb,hbt⟩ := Finset.mem_inter.mp hb
  obtain ⟨a,ha,hab⟩ := Finset.mem_biUnion.mp hb
  have hadj := (cert.modified_adjacency a b).2 ((mixedNeighbors_iff a b).2 hab)
  obtain ⟨e,hea,heb⟩ := cert.modified.adjacent_has_common_edge a b hadj
  refine ⟨e,edges_mono _ _ ?_ hea,edges_mono _ _ ?_ heb⟩
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨a,ha,mod_subset a hx⟩
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨b,hbt,mod_subset b hx⟩

private theorem literal_junctions :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let mixedSelection (j : Fin 42) : Finset PeriodicSubtileIndex :=
          let c := mixedComponents (j.val / 7)
          let k := j.val % 7 + 1
          (if k % 2 = 1 then c.1 else ∅) ∪
            (if k / 2 % 2 = 1 then c.2.1 else ∅) ∪
            (if k / 4 % 2 = 1 then c.2.2 else ∅)
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        ∀ (original_patches : ∀ j : Fin 42, LatticeTile (⟨(mixedSelection j).biUnion (fun a =>
            (original a).cells),0⟩ : ProtoTile)),
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        let component (r : Fin 6) (s : Fin 3) := unionOf (componentIndices r s)
        let selectionIndex (r : Fin 6) (s : Fin 7) : Fin 42 := ⟨r.val * 7 + s.val,by omega⟩
        (∀ (r : Fin 6), mixedSelection (selectionIndex r 0) = componentIndices r 0 ∧
            mixedSelection (selectionIndex r 1) = componentIndices r 1 ∧ mixedSelection
            (selectionIndex r 3) = componentIndices r 2 ∧ mixedSelection (selectionIndex r 2) =
            componentIndices r 0 ∪ componentIndices r 1 ∧ mixedSelection (selectionIndex r 5) =
            componentIndices r 1 ∪ componentIndices r 2 ∧ mixedSelection (selectionIndex r 4) =
            componentIndices r 2 ∪ componentIndices r 0 ∧ mixedSelection (selectionIndex r 6) =
            componentIndices r 0 ∪ componentIndices r 1 ∪ componentIndices r 2) → ((∀ (r : Fin
            6), ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) → (Disjoint (component r s).cells
            (component r t).cells)) → ((∀ (r : Fin 6), ∀ (s : Fin 3), ∀ (t : Fin 3), (s ≠ t) →
            ((FootprintEdges (component r s) ∩ FootprintEdges (component r t)).Nonempty)) → (∀ (r
            : Fin 6), J (component r 0) (component r 1) (component r 2)))) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock mixedComponents mixedSelection original original_patches J
      componentIndices unionOf component selectionIndex selection_certificate component_disjoint
      component_edges r
  obtain ⟨h₀,h₁,h₂,h₀₁,h₁₂,h₂₀,h₀₁₂⟩ := selection_certificate r
  have diskOf (s : Fin 7) := original_patches (selectionIndex r s)
  refine ⟨unionOf (componentIndices r 0 ∪ componentIndices r 1),
    unionOf (componentIndices r 1 ∪ componentIndices r 2),
    unionOf (componentIndices r 2 ∪ componentIndices r 0),
    unionOf (componentIndices r 0 ∪ componentIndices r 1 ∪ componentIndices r 2),
    ?_,?_,?_,?_,?_,?_,?_,
    component_disjoint r 0 1 (by decide),component_disjoint r 1 2 (by decide),
    component_disjoint r 2 0 (by decide),?_,?_,?_,?_,
    component_edges r 0 1 (by decide),component_edges r 1 2 (by decide),
    component_edges r 2 0 (by decide)⟩
  · simpa only [h₀] using diskOf 0
  · simpa only [h₁] using diskOf 1
  · simpa only [h₂] using diskOf 3
  · simpa only [h₀₁] using diskOf 2
  · simpa only [h₁₂] using diskOf 5
  · simpa only [h₂₀] using diskOf 4
  · simpa only [h₀₁₂] using diskOf 6
  all_goals
    intro z
    simp only [unionOf,component,Finset.union_biUnion,Finset.mem_union,or_assoc]

private theorem retarget :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells = Y.cells) → (LatticeTile X ↔ LatticeTile
            Y)) → (
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' :
            ProtoTile), ∀ (C' : ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) →
            ((C.cells = C'.cells) → ((J A B C) → (J A' B' C'))))) ) := by
  classical
  intro cellDisk J A B C A' B' C' hA hB hC h
  have eA : FootprintEdges A = FootprintEdges A' := by simp only [FootprintEdges,hA]
  have eB : FootprintEdges B = FootprintEdges B' := by simp only [FootprintEdges,hB]
  have eC : FootprintEdges C = FootprintEdges C' := by simp only [FootprintEdges,hC]
  simpa only [J,hA,hB,hC,eA,eB,eC,cellDisk A A' hA,cellDisk B B' hB,cellDisk C C' hC] using h

private theorem imageJ :
    (by
      classical
      exact
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        ∀ (F : ProtoTile → ProtoTile), ∀ (f : GaussianInt → GaussianInt), ∀ (g : GaussianInt →
            GaussianInt), (Function.Injective f) → ((∀ S, (F S).cells = S.cells.image f) → ((∀ S,
            LatticeTile S → LatticeTile (F S)) → ((∀ S, FootprintEdges (F S) =
            (fun e : Finset GaussianInt => e.image g) '' FootprintEdges S) → (∀ (A : ProtoTile),
                ∀ (B : ProtoTile), ∀ (C : ProtoTile), (J A B C) → (J (F A) (F B) (F C)))))) ) := by
  classical
  intro J F f g hf cells disk edges A B C h
  rcases h with ⟨AB,BC,CA,ABC,hA,hB,hC,hAB,hBC,hCA,hABC,dAB,dBC,dCA,uAB,uBC,uCA,uABC,eAB,eBC,eCA⟩
  have dj (S R : ProtoTile) (hd : Disjoint S.cells R.cells) :
      Disjoint (F S).cells (F R).cells := by
    apply Finset.disjoint_left.mpr
    intro z hz hr
    rw [cells] at hz hr
    obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,hyz⟩ := Finset.mem_image.mp hr
    have hxy := hf (hxz.trans hyz.symm)
    exact Finset.disjoint_left.mp hd hx (hxy.symm ▸ hy)
  have pair (S R D : ProtoTile)
      (hu : ∀ z, z ∈ D.cells ↔ z ∈ S.cells ∨ z ∈ R.cells) :
      ∀ z, z ∈ (F D).cells ↔ z ∈ (F S).cells ∨ z ∈ (F R).cells := by
    have he : D.cells = S.cells ∪ R.cells := by
      ext z
      simpa only [Finset.mem_union] using hu z
    intro z
    rw [cells,cells,cells,he,Finset.image_union,Finset.mem_union]
  have triple : ∀ z, z ∈ (F ABC).cells ↔
      z ∈ (F A).cells ∨ z ∈ (F B).cells ∨ z ∈ (F C).cells := by
    have he : ABC.cells = A.cells ∪ (B.cells ∪ C.cells) := by
      ext z
      simpa only [Finset.mem_union] using uABC z
    intro z
    rw [cells,cells,cells,cells,he,Finset.image_union,Finset.image_union]
    simp only [Finset.mem_union]
  have ed (S R : ProtoTile)
      (he : (FootprintEdges S ∩ FootprintEdges R).Nonempty) :
      (FootprintEdges (F S) ∩ FootprintEdges (F R)).Nonempty := by
    obtain ⟨e,heS,heR⟩ := he
    refine ⟨e.image g,?_,?_⟩
    · rw [edges]
      exact ⟨e,heS,rfl⟩
    · rw [edges]
      exact ⟨e,heR,rfl⟩
  exact ⟨F AB,F BC,F CA,F ABC,disk A hA,disk B hB,disk C hC,
    disk AB hAB,disk BC hBC,disk CA hCA,disk ABC hABC,
    dj A B dAB,dj B C dBC,dj C A dCA,
    pair A B AB uAB,pair B C BC uBC,pair C A CA uCA,triple,
    ed A B eAB,ed B C eBC,ed C A eCA⟩

private theorem quarterJ :
    (by
      classical
      exact
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        (∀ (F : ProtoTile → ProtoTile), ∀ (f : GaussianInt → GaussianInt), ∀ (g : GaussianInt →
            GaussianInt), (Function.Injective f) → ((∀ S, (F S).cells = S.cells.image f) → ((∀ S,
            LatticeTile S → LatticeTile (F S)) → ((∀ S, FootprintEdges (F S) = (fun e : Finset
            GaussianInt => e.image g) '' FootprintEdges S) → (∀ (A : ProtoTile), ∀ (B :
            ProtoTile), ∀ (C : ProtoTile), (J A B C) → (J (F A) (F B) (F C))))))) → (∀ (A :
            ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (J A B C) → (J (TileQuarterTurn A)
            (TileQuarterTurn B) (TileQuarterTurn C))) ) := by
  classical
  intro J imageJ A B C h
  refine imageJ TileQuarterTurn (fun x => GaussianQuarterTurn x - 1) GaussianQuarterTurn ?_
    (fun S => (TileQuarterTurnFormulas S).1)
    (fun S hs => (TileDiskAreaCovariance S 0).2.1.mp hs) ?_ A B C h
  · intro x y hxy
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) hxy
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) hxy
  · intro S
    exact (TileQuarterTurnFormulas S).2.2.2.2.2.2.1

private theorem translateJ :
    (by
      classical
      exact
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        (∀ (F : ProtoTile → ProtoTile), ∀ (f : GaussianInt → GaussianInt), ∀ (g : GaussianInt →
            GaussianInt), (Function.Injective f) → ((∀ S, (F S).cells = S.cells.image f) → ((∀ S,
            LatticeTile S → LatticeTile (F S)) → ((∀ S, FootprintEdges (F S) = (fun e : Finset
            GaussianInt => e.image g) '' FootprintEdges S) → (∀ (A : ProtoTile), ∀ (B :
            ProtoTile), ∀ (C : ProtoTile), (J A B C) → (J (F A) (F B) (F C))))))) → (∀ (u :
            GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (J A B C) → (J
            (TileTranslation A u) (TileTranslation B u) (TileTranslation C u))) ) := by
  classical
  intro J imageJ u A B C h
  exact imageJ (fun S => TileTranslation S u) (GaussianTranslation u) (GaussianTranslation u)
    (fun x y hxy => add_right_cancel hxy)
    (fun S => (TileTranslationFormulas S u).1)
    (fun S hs => (TileDiskAreaCovariance S u).1.mp hs)
    (fun S => (TileTranslationFormulas S u).2.2.2.2.2.2.1) A B C h

private theorem back_turn :
    (by
      classical
      exact
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        let turn (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn S) c
        ∀ (c : GaussianInt), ∀ (S : ProtoTile), back c (turn c S) = S ) := by
  classical
  intro back turn c S
  cases S with
  | mk D a =>
    dsimp only [back,turn,TileTranslation,TileQuarterTurn]
    apply congrArg₂ ProtoTile.mk
    · simp only [Finset.image_image]
      have h : (fun x : GaussianInt =>
          GaussianTranslation (GaussianQuarterTurn c)
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
              (GaussianTranslation c (GaussianQuarterTurn x - 1)) - 1) - 1) - 1)) = id := by
        funext x
        apply Zsqrtd.ext <;> simp [GaussianQuarterTurn,GaussianTranslation]; ring
      simp only [Function.comp_def, h, Finset.image_id]
    · apply Zsqrtd.ext <;> simp [GaussianQuarterTurn,GaussianTranslation]

private theorem back_shift :
    (by
      classical
      exact
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        ∀ (c : GaussianInt), ∀ (d : GaussianInt), ∀ (a : GaussianInt), ∀ (S : ProtoTile), back c
            (TileTranslation S a) = TileTranslation (back d S) (GaussianQuarterTurn (c-d-a)) ) := by
  classical
  intro back c d a S
  dsimp only [back,TileTranslation,TileQuarterTurn]
  apply congrArg₂ ProtoTile.mk
  · simp only [Finset.image_image]
    congr 1
    funext x
    apply Zsqrtd.ext <;> simp [GaussianQuarterTurn,GaussianTranslation] <;> ring
  · apply Zsqrtd.ext <;> simp [GaussianQuarterTurn,GaussianTranslation] <;> ring

private theorem back_congr :
    (by
      classical
      exact
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        ∀ (c : GaussianInt), ∀ (S : ProtoTile), ∀ (R : ProtoTile), (S.cells = R.cells) → ((back c
            S).cells = (back c R).cells) ) := by
  classical
  intro back c S R hc
  simp only [back,TileTranslation,TileQuarterTurn,hc]

private theorem backJ :
    (by
      classical
      exact
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (J A B C) → (J (TileQuarterTurn
            A) (TileQuarterTurn B) (TileQuarterTurn C))) → ((∀ (u : GaussianInt), ∀ (A :
            ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (J A B C) → (J (TileTranslation A
            u) (TileTranslation B u) (TileTranslation C u))) → (
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        ∀ (c : GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (J A B C) →
            (J (back c A) (back c B) (back c C)))) ) := by
  classical
  intro J quarterJ translateJ back c A B C h
  exact translateJ (GaussianQuarterTurn c) _ _ _ (quarterJ _ _ _ (quarterJ _ _ _ (quarterJ _ _
      _ h)))

private theorem back_centroid :
    (by
      classical
      exact
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        ∀ (c : GaussianInt), ∀ (S : ProtoTile), TileCentroid (back c S) = ((TileCentroid S).2 -
            (c.im : Real),-(TileCentroid S).1 + (c.re : Real)) ) := by
  classical
  intro back c S
  simp only [back,(TileTranslationFormulas _ _).2.2.2.2.1,
    (TileQuarterTurnFormulas _).2.2.2.2.1]
  apply Prod.ext <;> simp [GaussianQuarterTurn]; ring

private theorem back_symmetric :
    (by
      classical
      exact
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        let turn (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn S) c
        (∀ (c : GaussianInt), ∀ (S : ProtoTile), back c (turn c S) = S) → ((∀ (c : GaussianInt),
            ∀ (S : ProtoTile), ∀ (R : ProtoTile), (S.cells = R.cells) → ((back c S).cells = (back
            c R).cells)) → (∀ (c : GaussianInt), ∀ (S : ProtoTile), ((turn c S).cells = S.cells)
            → ((back c S).cells = S.cells))) ) := by
  classical
  intro back turn back_turn back_congr c S hc
  calc
    (back c S).cells = (back c (turn c S)).cells := back_congr _ _ _ hc.symm
    _ = S.cells := congrArg ProtoTile.cells (back_turn c S)

private theorem outer_cells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (x : LatticeCell), x ∈ T.cells ↔ x ∈ (cert.P 0 true).cells ∨ x ∈ (cert.P 0
            false).cells ∨ x ∈ (cert.P 1 true).cells ∨ x ∈ (cert.P 1 false).cells ∨ x ∈ (cert.P 2
            true).cells ∨ x ∈ (cert.P 2 false).cells ) := by
  classical
  intro q cfg C₀ T cert x
  rw [cert.outer_union x]
  constructor
  · rintro ⟨i,s,hx⟩
    fin_cases i <;> cases s
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  · rintro (h | h | h | h | h | h)
    · exact ⟨0,true,h⟩
    · exact ⟨0,false,h⟩
    · exact ⟨1,true,h⟩
    · exact ⟨1,false,h⟩
    · exact ⟨2,true,h⟩
    · exact ⟨2,false,h⟩

private theorem core_cells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        (∀ (x : LatticeCell), x ∈ T.cells ↔ x ∈ (cert.P 0 true).cells ∨ x ∈ (cert.P 0
            false).cells ∨ x ∈ (cert.P 1 true).cells ∨ x ∈ (cert.P 1 false).cells ∨ x ∈ (cert.P 2
            true).cells ∨ x ∈ (cert.P 2 false).cells) → ((unionOf (mixedBlock 0 0)).cells =
            T.cells) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock original unionOf outer_cells
  ext x
  rw [outer_cells x]
  simp [unionOf,mixedBlock,original,SubtileOccurrenceInterpretation,
    TileTranslation,GaussianTranslation]

private theorem component_zero :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        let component (r : Fin 6) (s : Fin 3) := unionOf (componentIndices r s)
        ((unionOf (mixedBlock 0 0)).cells = T.cells) → (∀ (r : Fin 6), (component r 0).cells =
            T.cells) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock mixedComponents original componentIndices unionOf component
      core_cells r
  change (unionOf (mixedBlock 0 0)).cells = T.cells
  exact core_cells

private theorem shifted_core :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        ((unionOf (mixedBlock 0 0)).cells = T.cells) → (∀ (m : Int), ∀ (n : Int), (unionOf
            (mixedBlock m n)).cells = (TileTranslation T ((m : GaussianInt) * cert.u + (n :
            GaussianInt) * cert.v)).cells) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock original unionOf core_cells m n
  change (unionOf (mixedBlock m n)).cells =
    T.cells.image (GaussianTranslation ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v))
  rw [← core_cells]
  have t0 : GaussianTranslation 0 = id := by
    funext x
    simp [GaussianTranslation]
  simp only [unionOf,mixedBlock,original,SubtileOccurrenceInterpretation,
    TileTranslation,Finset.biUnion_insert,Finset.singleton_biUnion,
    Int.cast_zero,zero_mul,zero_add,t0,Finset.image_id,Finset.image_union]

private theorem first_canonical :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        let component (r : Fin 6) (s : Fin 3) := unionOf (componentIndices r s)
        (∀ (r : Fin 6), J (component r 0) (component r 1) (component r 2)) → ((∀ (A : ProtoTile),
            ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' :
            ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) → ((C.cells = C'.cells) →
            ((J A B C) → (J A' B' C'))))) → ((∀ (r : Fin 6), (component r 0).cells = T.cells) →
            ((∀ (m : Int), ∀ (n : Int), (unionOf (mixedBlock m n)).cells = (TileTranslation T ((m
            : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells) → (
        let firstPeriod (i : Fin 3) : GaussianInt := match i.val with
          | 0 => cert.u
          | 1 => cert.v
          | _ => -cert.u-cert.v
        let firstShift (i : Fin 3) : GaussianInt := match i.val with
          | 0 => cert.u+cert.v
          | 1 => -cert.u
          | _ => -cert.v
        let firstParent (i : Fin 3) := TileTranslation (cert.P i false) (firstShift i)
        ∀ (i : Fin 3), J T (TileTranslation T (firstPeriod i)) (firstParent i))))) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock mixedComponents original J componentIndices unionOf component
      literal_junctions retarget component_zero shifted_core firstPeriod firstShift firstParent i
  let r : Fin 6 := ⟨i.val,by omega⟩
  refine retarget (component r 0) (component r 1) (component r 2)
    T (TileTranslation T (firstPeriod i)) (firstParent i)
    (component_zero r) ?_ ?_ (literal_junctions r)
  · fin_cases i
    · change (unionOf (mixedBlock 1 0)).cells = (TileTranslation T cert.u).cells
      simpa only [Int.cast_one,Int.cast_zero,one_mul,zero_mul,add_zero] using shifted_core 1 0
    · change (unionOf (mixedBlock 0 1)).cells = (TileTranslation T cert.v).cells
      simpa only [Int.cast_one,Int.cast_zero,one_mul,zero_mul,zero_add] using shifted_core 0 1
    · change (unionOf (mixedBlock (-1) (-1))).cells = (TileTranslation T (-cert.u-cert.v)).cells
      simpa only [Int.cast_neg,Int.cast_one,neg_one_mul,sub_eq_add_neg] using shifted_core (-1)
          (-1)
  · fin_cases i
    · change (unionOf {⟨.B,1,1⟩}).cells = (TileTranslation (cert.P 0 false) (cert.u+cert.v)).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_one,one_mul]
    · change (unionOf {⟨.D,-1,0⟩}).cells = (TileTranslation (cert.P 1 false) (-cert.u)).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_neg,Int.cast_one,neg_one_mul,Int.cast_zero,zero_mul,add_zero]
    · change (unionOf {⟨.F,0,-1⟩}).cells = (TileTranslation (cert.P 2 false) (-cert.v)).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_neg,Int.cast_one,neg_one_mul,Int.cast_zero,zero_mul,zero_add]

private theorem all_centroids :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let firstPeriod (i : Fin 3) : GaussianInt := match i.val with
          | 0 => cert.u
          | 1 => cert.v
          | _ => -cert.u-cert.v
        let firstShift (i : Fin 3) : GaussianInt := match i.val with
          | 0 => cert.u+cert.v
          | 1 => -cert.u
          | _ => -cert.v
        let firstParent (i : Fin 3) := TileTranslation (cert.P i false) (firstShift i)
        let plusRepresentative (i : Fin 3) : ProtoTile := match i.val with
          | 0 => TileTranslation (cert.P 0 true) (-cert.v)
          | 1 => TileTranslation (cert.P 1 true) (cert.u + cert.v)
          | _ => TileTranslation (cert.P 2 true) (-cert.u)
        let minusRepresentative (i : Fin 3) : ProtoTile := match i.val with
          | 0 => TileTranslation (cert.P 1 true) cert.u
          | 1 => TileTranslation (cert.P 2 true) cert.v
          | _ => TileTranslation (cert.P 0 true) (-cert.u - cert.v)
        (∀ i : Fin 3, TileCentroid (plusRepresentative i) - TileCentroid T = (1/2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ)))) ∧ (∀ i : Fin 3, TileCentroid (minusRepresentative
            i) - TileCentroid T = (1/2 : Real) • (GaussianRealPoint (BandVectors.1 (q
            ((i+1).succ)) (q 0)) - GaussianRealPoint (BandVectors.1 (q 0) (q ((i+1).succ))))) ∧
            (∀ i : Fin 3, TileCentroid (firstParent i) - TileCentroid T = (1/2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) - GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0)))) ∧ (∀ i : Fin 3, GaussianRealPoint (firstPeriod i)
            = GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) ) := by
  classical
  intro q cfg C₀ T cert firstPeriod firstShift firstParent plusRepresentative minusRepresentative
  have laws := VectorRecursionLaws q cfg.proper.1
  have laws₁ := VectorRecursionLaws ![q 0,q 2,q 3,q 1] (SemiProperQuadruple.rotate cfg.proper.1)
  have laws₂ := VectorRecursionLaws ![q 0,q 3,q 1,q 2]
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.proper.1))
  have sumV := congrArg GaussianRealPoint laws.1
  have v₁ := congrArg GaussianRealPoint laws.2.2.1
  have v₂ := congrArg GaussianRealPoint laws₁.2.2.1
  have v₃ := congrArg GaussianRealPoint laws₂.2.2.1
  change GaussianRealPoint (BandVectors.1 (q 2) (q 0)) =
    GaussianRealPoint (BandVectors.1 (q 2) (q 1) -
      (⟨0,1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 2)) at v₂
  change GaussianRealPoint (BandVectors.1 (q 3) (q 0)) =
    GaussianRealPoint (BandVectors.1 (q 3) (q 2) -
      (⟨0,1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 3)) at v₃
  have u := congrArg GaussianRealPoint (cert.period_u.trans ((laws.2.2.2.2 cfg.proper 0).1))
  have v := congrArg GaussianRealPoint (cert.period_v.trans ((laws.2.2.2.2 cfg.proper 1).1))
  have f₁ := congrArg GaussianRealPoint ((laws.2.2.2.2 cfg.proper 0).1)
  have f₂ := congrArg GaussianRealPoint ((laws.2.2.2.2 cfg.proper 1).1)
  have f₃ := congrArg GaussianRealPoint ((laws.2.2.2.2 cfg.proper 2).1)
  have c₁ := (cert.outer_occurrence 0 true).2.2
  have c₂ := (cert.outer_occurrence 1 true).2.2
  have c₃ := (cert.outer_occurrence 2 true).2.2
  have d₁ := (cert.outer_occurrence 0 false).2.2
  have d₂ := (cert.outer_occurrence 1 false).2.2
  have d₃ := (cert.outer_occurrence 2 false).2.2
  norm_num [Prod.ext_iff,GaussianRealPoint,Fin.succ,Fin.add,Fin.add_def,Fin.ofNat,Matrix.cons_val]
    at sumV v₁ v₂ v₃ u v f₁ f₂ f₃ c₁ c₂ c₃ d₁ d₂ d₃
  have fin2 : (⟨2,by decide⟩ : Fin 4) = 2 := rfl
  have fin3 : (⟨3,by decide⟩ : Fin 4) = 3 := rfl
  have fin2_3 : (⟨2,by decide⟩ : Fin 3) = 2 := rfl
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro i; fin_cases i
  all_goals dsimp only [plusRepresentative,minusRepresentative,firstPeriod,firstParent,firstShift]
  all_goals try simp only [(TileTranslationFormulas _ _).2.2.2.2.1]
  all_goals apply Prod.ext <;>
    norm_num
        [Prod.ext_iff,GaussianRealPoint,Fin.succ,Fin.add,Fin.add_def,Fin.ofNat,Matrix.cons_val]
  · linear_combination (-1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + (-1 / 2 : Real) *
      v₁.1 + (1 / 2 : Real) * v₁.2 + v₂.2 + (-1 : Real) * v.1 + (-1 / 2 : Real) * f₁.1 + c₁.1
  · linear_combination (-1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 / 2 : Real) *
      v₁.1 + (-1 / 2 : Real) * v₁.2 + (-1 : Real) * v₂.1 + (-1 : Real) * v.2 + (-1 / 2 : Real)
      * f₁.2 + c₁.2
  · linear_combination (1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 : Real) * v₁.2
      + (-1 / 2 : Real) * v₂.1 + (-1 / 2 : Real) * v₂.2 + u.1 + v.1 + (-1 / 2 : Real) * f₂.1 +
      c₂.1
  · linear_combination (1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + v₁.1 + (1 / 2 :
      Real) * v₂.1 + (-1 / 2 : Real) * v₂.2 + u.2 + v.2 + (-1 / 2 : Real) * f₂.2 + c₂.2
  · linear_combination (-1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + v₁.2 + (-1 / 2 :
      Real) * v₃.1 + (1 / 2 : Real) * v₃.2 + (-1 : Real) * u.1 + (-1 / 2 : Real) * f₃.1 + c₃.1
  · linear_combination (-1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 : Real) * v₁.1
      + (-1 / 2 : Real) * v₃.1 + (-1 / 2 : Real) * v₃.2 + (-1 : Real) * u.2 + (-1 / 2 : Real) *
      f₃.2 + c₃.2
  · linear_combination (1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 : Real) * v₁.2
      + (-1 / 2 : Real) * v₂.1 + (-1 / 2 : Real) * v₂.2 + u.1 + (1 / 2 : Real) * f₂.1 + c₂.1
  · linear_combination (1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + v₁.1 + (1 / 2 :
      Real) * v₂.1 + (-1 / 2 : Real) * v₂.2 + u.2 + (1 / 2 : Real) * f₂.2 + c₂.2
  · linear_combination (1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 : Real) * v₂.2
      + (-1 / 2 : Real) * v₃.1 + (-1 / 2 : Real) * v₃.2 + v.1 + (1 / 2 : Real) * f₃.1 + c₃.1
  · linear_combination (1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + v₂.1 + (1 / 2 :
      Real) * v₃.1 + (-1 / 2 : Real) * v₃.2 + v.2 + (1 / 2 : Real) * f₃.2 + c₃.2
  · linear_combination (-1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + (-1 / 2 : Real) *
      v₁.1 + (1 / 2 : Real) * v₁.2 + v₂.2 + (-1 : Real) * u.1 + (-1 : Real) * v.1 + (1 / 2 :
      Real) * f₁.1 + c₁.1
  · linear_combination (-1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 / 2 : Real) *
      v₁.1 + (-1 / 2 : Real) * v₁.2 + (-1 : Real) * v₂.1 + (-1 : Real) * u.2 + (-1 : Real) *
      v.2 + (1 / 2 : Real) * f₁.2 + c₁.2
  · linear_combination (1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (1 / 2 : Real) *
      v₁.1 + (-1 / 2 : Real) * v₁.2 + (-1 : Real) * v₂.2 + u.1 + v.1 + (-1 / 2 : Real) * f₁.1 +
      d₁.1
  · linear_combination (1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + (1 / 2 : Real) *
      v₁.1 + (1 / 2 : Real) * v₁.2 + v₂.1 + u.2 + v.2 + (-1 / 2 : Real) * f₁.2 + d₁.2
  · linear_combination (-1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + v₁.2 + (1 / 2 :
      Real) * v₂.1 + (1 / 2 : Real) * v₂.2 + (-1 : Real) * u.1 + (-1 / 2 : Real) * f₂.1 + d₂.1
  · linear_combination (-1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 : Real) * v₁.1
      + (-1 / 2 : Real) * v₂.1 + (1 / 2 : Real) * v₂.2 + (-1 : Real) * u.2 + (-1 / 2 : Real) *
      f₂.2 + d₂.2
  · linear_combination (-1 / 2 : Real) * sumV.1 + (1 / 2 : Real) * sumV.2 + v₂.2 + (1 / 2 :
      Real) * v₃.1 + (1 / 2 : Real) * v₃.2 + (-1 : Real) * v.1 + (-1 / 2 : Real) * f₃.1 + d₃.1
  · linear_combination (-1 / 2 : Real) * sumV.1 + (-1 / 2 : Real) * sumV.2 + (-1 : Real) * v₂.1
      + (-1 / 2 : Real) * v₃.1 + (1 / 2 : Real) * v₃.2 + (-1 : Real) * v.2 + (-1 / 2 : Real) *
      f₃.2 + d₃.2
  · linear_combination u.1 + (-1 : Real) * f₁.1
  · linear_combination u.2 + (-1 : Real) * f₁.2
  · linear_combination v.1 + (-1 : Real) * f₂.1
  · linear_combination v.2 + (-1 : Real) * f₂.2
  · linear_combination (-1 : Real) * sumV.1 + sumV.2 + v₁.2 + v₂.2 + v₃.2 + (-1 : Real) * u.1 +
      (-1 : Real) * v.1 + (-1 : Real) * f₃.1
  · linear_combination (-1 : Real) * sumV.1 + (-1 : Real) * sumV.2 + (-1 : Real) * v₁.1 + (-1 :
      Real) * v₂.1 + (-1 : Real) * v₃.1 + (-1 : Real) * u.2 + (-1 : Real) * v.2 + (-1 : Real) *
      f₃.2

private theorem second_canonical :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
          {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
        let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
            Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
          (mixedBlock 0 0, match r with
            | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
            | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
            | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
            | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
            | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
            | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
        let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        let componentIndices (r : Fin 6) (s : Fin 3) :=
          let c := mixedComponents r.val
          if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
        let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
          ⟨D.biUnion (fun a => (original a).cells),0⟩
        let component (r : Fin 6) (s : Fin 3) := unionOf (componentIndices r s)
        (∀ (r : Fin 6), J (component r 0) (component r 1) (component r 2)) → ((∀ (A : ProtoTile),
            ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' : ProtoTile), ∀ (C' :
            ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) → ((C.cells = C'.cells) →
            ((J A B C) → (J A' B' C'))))) → ((∀ (r : Fin 6), (component r 0).cells = T.cells) → (
        let plusRepresentative (i : Fin 3) : ProtoTile := match i.val with
          | 0 => TileTranslation (cert.P 0 true) (-cert.v)
          | 1 => TileTranslation (cert.P 1 true) (cert.u + cert.v)
          | _ => TileTranslation (cert.P 2 true) (-cert.u)
        let minusRepresentative (i : Fin 3) : ProtoTile := match i.val with
          | 0 => TileTranslation (cert.P 1 true) cert.u
          | 1 => TileTranslation (cert.P 2 true) cert.v
          | _ => TileTranslation (cert.P 0 true) (-cert.u - cert.v)
        ∀ (i : Fin 3), J T (plusRepresentative i) (minusRepresentative i)))) ) := by
  classical
  intro q cfg C₀ T cert mixedBlock mixedComponents original J componentIndices unionOf component
      literal_junctions retarget component_zero plusRepresentative minusRepresentative i
  let r : Fin 6 := ⟨i.val+3,by omega⟩
  refine retarget (component r 0) (component r 1) (component r 2)
    T (plusRepresentative i) (minusRepresentative i) (component_zero r) ?_ ?_
        (literal_junctions r)
  · fin_cases i
    · change (unionOf {⟨.A,0,-1⟩}).cells = (TileTranslation (cert.P 0 true) (-cert.v)).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_neg,Int.cast_one,neg_one_mul,Int.cast_zero,zero_mul,zero_add]
    · change (unionOf {⟨.C,1,1⟩}).cells = (TileTranslation (cert.P 1 true) (cert.u+cert.v)).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_one,one_mul]
    · change (unionOf {⟨.E,-1,0⟩}).cells = (TileTranslation (cert.P 2 true) (-cert.u)).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_neg,Int.cast_one,neg_one_mul,Int.cast_zero,zero_mul,add_zero]
  · fin_cases i
    · change (unionOf {⟨.C,1,0⟩}).cells = (TileTranslation (cert.P 1 true) cert.u).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_one,one_mul,Int.cast_zero,zero_mul,add_zero]
    · change (unionOf {⟨.E,0,1⟩}).cells = (TileTranslation (cert.P 2 true) cert.v).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_one,one_mul,Int.cast_zero,zero_mul,zero_add]
    · change (unionOf {⟨.A,-1,-1⟩}).cells = (TileTranslation (cert.P 0 true)
        (-cert.u-cert.v)).cells
      simp only [unionOf,Finset.singleton_biUnion,original,SubtileOccurrenceInterpretation,
        TileTranslation,Int.cast_neg,Int.cast_one,neg_one_mul,sub_eq_add_neg]

private theorem symmetric_back_proxy :
    (by
      classical
      exact
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        let turn (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn S) c
        (∀ (c : GaussianInt), ∀ (d : GaussianInt), ∀ (a : GaussianInt), ∀ (S : ProtoTile), back c
            (TileTranslation S a) = TileTranslation (back d S) (GaussianQuarterTurn (c-d-a))) →
            ((∀ (c : GaussianInt), ∀ (S : ProtoTile), ((turn c S).cells = S.cells) → ((back c
            S).cells = S.cells)) → (∀ (C : CircleCoordinates), ∀ (S : ProtoTile), (BandPrototile
            C S) → ((LatticeTile S) → ((QuarterTurnSymmetric S) → (∀ (c : GaussianInt), ∀ (a :
            GaussianInt), ∃ R : ProtoTile, BandPrototile C R ∧ (back c (TileTranslation S
            a)).cells = R.cells ∧ TileCentroid R = TileCentroid (back c (TileTranslation S
            a))))))) ) := by
  classical
  intro back turn back_shift back_symmetric C S hB hS hQ c a
  obtain ⟨d,hd,hcells,hanchor,hfoot,hcent⟩ :=
    QuarterTurnSymmetricCenteredTransport S hQ
  let R := TileTranslation S (GaussianQuarterTurn (c-d-a))
  have hc : (back c (TileTranslation S a)).cells = R.cells := by
    rw [back_shift c d a S]
    simp only [R,TileTranslation,back_symmetric d S hcells]
  have hn : R.cells.Nonempty := by
    exact Finset.image_nonempty.mpr (LatticeTileGridStructure S hS).1.1
  have ha : (back c (TileTranslation S a)).cells = ∅ →
      (back c (TileTranslation S a)).anchor = R.anchor := by
    intro he
    rw [← hc,he] at hn
    exact False.elim (Finset.not_nonempty_empty hn)
  exact ⟨R,BandPrototileTranslation C S _ hB,hc,
    (ProtoTileObservableExtensionality _ _ hc ha).2.2.2.2.symm⟩

private theorem centered_back_displacement :
    (by
      classical
      exact
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        (∀ (c : GaussianInt), ∀ (S : ProtoTile), TileCentroid (back c S) = ((TileCentroid S).2 -
            (c.im : Real),-(TileCentroid S).1 + (c.re : Real))) → (∀ (S : ProtoTile), ∀ (T :
            ProtoTile), ∀ (c : GaussianInt), ∀ (w : GaussianInt), ∀ (v : GaussianInt),
            (GaussianRealPoint c =
            ((TileCentroid T).1+(TileCentroid T).2,(TileCentroid T).2-(TileCentroid T).1)) → ((v
                = (⟨0,1⟩ : GaussianInt) * w) → ((TileCentroid S - TileCentroid T =
            (1/2 : Real) • (GaussianRealPoint v - GaussianRealPoint w)) → (TileCentroid (back c
                S) - TileCentroid T = (1/2 : Real) • (GaussianRealPoint w + GaussianRealPoint
                v))))) ) := by
  classical
  intro back back_centroid S T c w v hc hv hd
  have hvp : GaussianRealPoint v =
      (-(GaussianRealPoint w).2,(GaussianRealPoint w).1) := by
    rw [hv]
    ext <;> simp [GaussianRealPoint]
  change ((c.re : Real),(c.im : Real)) =
    ((TileCentroid T).1+(TileCentroid T).2,(TileCentroid T).2-(TileCentroid T).1) at hc
  norm_num [Prod.ext_iff,GaussianRealPoint] at hc hd hvp
  rw [back_centroid]
  apply Prod.ext <;> norm_num [GaussianRealPoint] <;>
    linarith only [hc.1,hc.2,hd.1,hd.2,hvp.1,hvp.2]

private abbrev point_injective := ApollonianSuperharmonic.GaussianRealPointProperties.injective

private theorem first_requested :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (QuarterTurnSymmetric T) → (
        let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
          ∃ AB BC CA ABC : ProtoTile,
            LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
            Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
            (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
            (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
            (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
            (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
            (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
            (FootprintEdges C ∩ FootprintEdges A).Nonempty
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' :
            ProtoTile), ∀ (C' : ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) →
            ((C.cells = C'.cells) → ((J A B C) → (J A' B' C'))))) → (
        let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S)))
              (GaussianQuarterTurn c)
        let turn (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
          TileTranslation (TileQuarterTurn S) c
        (∀ (c : GaussianInt), ∀ (d : GaussianInt), ∀ (a : GaussianInt), ∀ (S : ProtoTile), back c
            (TileTranslation S a) = TileTranslation (back d S) (GaussianQuarterTurn (c-d-a))) →
            ((∀ (c : GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (J A
            B C) → (J (back c A) (back c B) (back c C))) → ((∀ (c : GaussianInt), ∀ (S :
            ProtoTile), ((turn c S).cells = S.cells) → ((back c S).cells = S.cells)) → (
        let firstPeriod (i : Fin 3) : GaussianInt := match i.val with
          | 0 => cert.u
          | 1 => cert.v
          | _ => -cert.u-cert.v
        let firstShift (i : Fin 3) : GaussianInt := match i.val with
          | 0 => cert.u+cert.v
          | 1 => -cert.u
          | _ => -cert.v
        let firstParent (i : Fin 3) := TileTranslation (cert.P i false) (firstShift i)
        (∀ (i : Fin 3), J T (TileTranslation T (firstPeriod i)) (firstParent i)) → (
        let plusRepresentative (i : Fin 3) : ProtoTile := match i.val with
          | 0 => TileTranslation (cert.P 0 true) (-cert.v)
          | 1 => TileTranslation (cert.P 1 true) (cert.u + cert.v)
          | _ => TileTranslation (cert.P 2 true) (-cert.u)
        let minusRepresentative (i : Fin 3) : ProtoTile := match i.val with
          | 0 => TileTranslation (cert.P 1 true) cert.u
          | 1 => TileTranslation (cert.P 2 true) cert.v
          | _ => TileTranslation (cert.P 0 true) (-cert.u - cert.v)
        (∀ (i : Fin 3), BandPrototile (q i.succ) (plusRepresentative i)) → (((∀ i : Fin 3,
            TileCentroid (plusRepresentative i) - TileCentroid T = (1/2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ)))) ∧ (∀ i : Fin 3, TileCentroid (minusRepresentative
            i) - TileCentroid T = (1/2 : Real) • (GaussianRealPoint (BandVectors.1 (q
            ((i+1).succ)) (q 0)) - GaussianRealPoint (BandVectors.1 (q 0) (q ((i+1).succ))))) ∧
            (∀ i : Fin 3, TileCentroid (firstParent i) - TileCentroid T = (1/2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) - GaussianRealPoint
            (BandVectors.1 (q i.succ) (q 0)))) ∧ (∀ i : Fin 3, GaussianRealPoint (firstPeriod i)
            = GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → ((∀ (C : CircleCoordinates),
            ∀ (S : ProtoTile), (BandPrototile C S) → ((LatticeTile S) → ((QuarterTurnSymmetric S)
            → (∀ (c : GaussianInt), ∀ (a : GaussianInt), ∃ R : ProtoTile, BandPrototile C R ∧
            (back c (TileTranslation S a)).cells = R.cells ∧ TileCentroid R = TileCentroid (back
            c (TileTranslation S a)))))) → ((∀ (S : ProtoTile), ∀ (T : ProtoTile), ∀ (c :
            GaussianInt), ∀ (w : GaussianInt), ∀ (v : GaussianInt), (GaussianRealPoint c =
            ((TileCentroid T).1+(TileCentroid T).2,(TileCentroid T).2-(TileCentroid T).1)) → ((v
            = (⟨0,1⟩ : GaussianInt) * w) → ((TileCentroid S - TileCentroid T = (1/2 : Real) •
            (GaussianRealPoint v - GaussianRealPoint w)) → (TileCentroid (back c S) -
            TileCentroid T = (1/2 : Real) • (GaussianRealPoint w + GaussianRealPoint v))))) →
            ((Function.Injective GaussianRealPoint) → (∀ (i : Fin 3), J T (TileTranslation T
            (BandVectors.1 (q i.succ) (q 0))) (plusRepresentative i)))))))))))) ) := by
  classical
  intro q cfg C₀ T cert hsym J retarget back turn back_shift backJ back_symmetric firstPeriod
      firstShift firstParent first_canonical plusRepresentative minusRepresentative plus_band
      all_centroids symmetric_back_proxy centered_back_displacement point_injective i
  obtain ⟨c,hc,hcT,haT,hfT,htT⟩ := QuarterTurnSymmetricCenteredTransport T hsym
  have hroot : (back c T).cells = T.cells := back_symmetric c T hcT
  have hp : firstPeriod i = BandVectors.1 (q 0) (q i.succ) :=
    point_injective (all_centroids.2.2.2 i)
  have hf := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper i
  have hr : GaussianQuarterTurn (-(firstPeriod i)) =
      BandVectors.1 (q i.succ) (q 0) := by
    rw [hp,hf.1]
    apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]
  have hn : (back c (TileTranslation T (firstPeriod i))).cells =
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0))).cells := by
    rw [back_shift c c (firstPeriod i) T]
    simp only [sub_self,zero_sub,hr,TileTranslation,hroot]
  obtain ⟨R,hR,hcells,hcent⟩ := symmetric_back_proxy (q i.succ) (cert.P i false)
    (cert.outer_occurrence i false).1 (cert.parent_lattice i false)
    (cert.parent_quarter_turn i false) c (firstShift i)
  have hdisp : TileCentroid R - TileCentroid T =
      (1/2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) := by
    rw [hcent]
    exact centered_back_displacement (firstParent i) T c _ _ hc hf.1
      (all_centroids.2.2.1 i)
  have hRP := BandPrototileCentroidUnique _ _ _ hR (plus_band i)
    (sub_left_injective (hdisp.trans (all_centroids.1 i).symm))
  exact retarget _ _ _ T (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
    (plusRepresentative i) hroot hn (hcells.trans hRP.1)
    (backJ c _ _ _ (first_canonical i))

end MixedAggregateGeometry

theorem P1BandOrderedGeneralMixedAggregateJunctionData
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hsym : QuarterTurnSymmetric T) :
    let junctionData : ProtoTile → ProtoTile → ProtoTile → Prop :=
      fun A B C ↦ ∃ AB BC CA ABC : ProtoTile,
        LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
        LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧
        LatticeTile ABC ∧
        Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧
        Disjoint C.cells A.cells ∧
        (∀ z : LatticeCell,
          z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
        (∀ z : LatticeCell,
          z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
        (∀ z : LatticeCell,
          z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
        (∀ z : LatticeCell,
          z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
        (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
        (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
        (FootprintEdges C ∩ FootprintEdges A).Nonempty
    (∀ (i : Fin 3) (U : ProtoTile), BandPrototile (q i.succ) U →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      junctionData T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
    (∀ (i : Fin 3) (U V : ProtoTile), BandPrototile (q i.succ) U →
      BandPrototile (q ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      junctionData T U V) := by
-- BODY
  let mixedNeighbors (a : PeriodicSubtileIndex) : Finset PeriodicSubtileIndex :=
    let m := a.first
    let n := a.second
    match a.label with
    | .A => {⟨.B,m,n⟩, ⟨.B,m,n+1⟩, ⟨.B,m+1,n+1⟩, ⟨.C,m,n⟩,
        ⟨.C,m+1,n+1⟩, ⟨.D,m,n⟩, ⟨.E,m,n+1⟩, ⟨.F,m,n⟩}
    | .B => {⟨.A,m,n⟩, ⟨.A,m,n-1⟩, ⟨.A,m-1,n-1⟩, ⟨.C,m,n⟩,
        ⟨.D,m-1,n-1⟩, ⟨.D,m,n⟩, ⟨.E,m,n⟩, ⟨.F,m,n-1⟩}
    | .C => {⟨.A,m,n⟩, ⟨.A,m-1,n-1⟩, ⟨.B,m,n⟩, ⟨.D,m-1,n⟩,
        ⟨.E,m-1,n⟩, ⟨.F,m,n⟩}
    | .D => {⟨.A,m,n⟩, ⟨.B,m+1,n+1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩,
        ⟨.E,m,n⟩, ⟨.F,m+1,n⟩}
    | .E => {⟨.A,m,n-1⟩, ⟨.B,m,n⟩, ⟨.C,m+1,n⟩, ⟨.D,m,n⟩}
    | .F => {⟨.A,m,n⟩, ⟨.B,m,n+1⟩, ⟨.C,m,n⟩, ⟨.D,m-1,n⟩}
  have mixedNeighbors_iff := MixedAggregateGeometry.mixedNeighbors_iff
      (MixedAggregateGeometry.mixedNeighbors_symmetric)
  let mixedDecode (k : Nat) : PeriodicSubtileIndex :=
    ⟨match k % 6 with | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F,
      (k / 6 / 7 : Int) - 3, (k / 6 % 7 : Int) - 3⟩
  let mixedBlock (m n : Int) : Finset PeriodicSubtileIndex :=
    {⟨.A,m,n⟩,⟨.B,m,n⟩,⟨.C,m,n⟩,⟨.D,m,n⟩,⟨.E,m,n⟩,⟨.F,m,n⟩}
  let mixedComponents (r : Nat) : Finset PeriodicSubtileIndex ×
      Finset PeriodicSubtileIndex × Finset PeriodicSubtileIndex :=
    (mixedBlock 0 0, match r with
      | 0 => (mixedBlock 1 0, {⟨.B,1,1⟩})
      | 1 => (mixedBlock 0 1, {⟨.D,-1,0⟩})
      | 2 => (mixedBlock (-1) (-1), {⟨.F,0,-1⟩})
      | 3 => ({⟨.A,0,-1⟩}, {⟨.C,1,0⟩})
      | 4 => ({⟨.C,1,1⟩}, {⟨.E,0,1⟩})
      | _ => ({⟨.E,-1,0⟩}, {⟨.A,-1,-1⟩}))
  let mixedSelection (j : Fin 42) : Finset PeriodicSubtileIndex :=
    let c := mixedComponents (j.val / 7)
    let k := j.val % 7 + 1
    (if k % 2 = 1 then c.1 else ∅) ∪
      (if k / 2 % 2 = 1 then c.2.1 else ∅) ∪
      (if k / 4 % 2 = 1 then c.2.2 else ∅)
  let mixedTreeVertices (tree : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) :
      Finset PeriodicSubtileIndex :=
    tree.foldl (fun S e => insert (mixedDecode e.1) S) S
  let mixedTreeCheck (D : Finset PeriodicSubtileIndex) (inside : Bool)
      (es : List (Nat × Nat)) (S : Finset PeriodicSubtileIndex) : Bool :=
    es.foldr (fun (a,b) next S =>
      decide ((if inside then mixedDecode a ∈ D else mixedDecode a ∉ D) ∧
        mixedDecode b ∈ S ∧ mixedDecode b ∈ mixedNeighbors (mixedDecode a)) &&
      next (insert (mixedDecode a) S)) (fun _ => true) S
  let mixedInTrees : List (List (Nat × Nat)) := MixedAggregateGeometry.incomingCertificateTrees
  let mixedOutTrees : List (List (Nat × Nat)) := MixedAggregateGeometry.outgoingCertificateTrees
  let mixedInHubs : List Nat :=
      [144, 186, 144, 193, 144, 186, 144, 144, 150, 144, 105, 144, 150, 144, 144, 96, 144,
        143, 144, 96, 144, 144, 138, 144, 188, 144, 138, 144, 144, 194, 144, 154, 144, 194,
        144, 144, 106, 144, 96, 144, 106, 144]
  let original := SubtileOccurrenceInterpretation cert.P cert.u cert.v
  let offset (a : PeriodicSubtileIndex) : GaussianInt :=
    (a.first : GaussianInt) * cert.u + (a.second : GaussianInt) * cert.v
  let precursor (a : PeriodicSubtileIndex) := TileTranslation cert.O (offset a)
  let paired (a : PeriodicSubtileIndex) : PeriodicSubtileIndex := ⟨.B,a.first,a.second⟩
  have cellDisk := MixedAggregateGeometry.cellDisk
  have translation_complement := MixedAggregateGeometry.translation_complement
  have mod_nonA := MixedAggregateGeometry.mod_nonA q cfg C₀ T cert
  have mod_A := MixedAggregateGeometry.mod_A q cfg C₀ T cert translation_complement
  have precursor_subset_B := MixedAggregateGeometry.precursor_subset_B q cfg C₀ T cert
      (MixedAggregateGeometry.hOB q cfg C₀ T cert)
  have mod_subset := MixedAggregateGeometry.mod_subset q cfg C₀ T cert mod_nonA mod_A
  let exception (j : Fin 42) : Option PeriodicSubtileIndex :=
    if j.val / 7 = 3 ∧ (j.val % 7 + 1) / 2 % 2 = 1 then some ⟨.A,0,-1⟩ else
    if j.val / 7 = 5 ∧ (j.val % 7 + 1) / 4 % 2 = 1 then some ⟨.A,-1,-1⟩ else none
  let J : ProtoTile → ProtoTile → ProtoTile → Prop := fun A B C =>
    ∃ AB BC CA ABC : ProtoTile,
      LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
      LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
      Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
      (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
      (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
      (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
      (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
      (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
      (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
      (FootprintEdges C ∩ FootprintEdges A).Nonempty
  let componentIndices (r : Fin 6) (s : Fin 3) :=
    let c := mixedComponents r.val
    if s = 0 then c.1 else if s = 1 then c.2.1 else c.2.2
  let owners (D : Finset PeriodicSubtileIndex) :=
    D ∪ (D.filter (fun a => a.label = .A)).image paired
  let unionOf (D : Finset PeriodicSubtileIndex) : ProtoTile :=
    ⟨D.biUnion (fun a => (original a).cells),0⟩
  let component (r : Fin 6) (s : Fin 3) := unionOf (componentIndices r s)
  let selectionIndex (r : Fin 6) (s : Fin 7) : Fin 42 := ⟨r.val * 7 + s.val,by omega⟩
  have owners_mono {D E : Finset PeriodicSubtileIndex} (h : D ⊆ E) : owners D ⊆ owners E := by
    exact Finset.union_subset_union h (Finset.image_mono _ (Finset.filter_subset_filter _ h))
  have literal_junctions := MixedAggregateGeometry.literal_junctions q cfg C₀ T cert
      (MixedAggregateGeometry.original_patches q cfg C₀ T cert
      (MixedAggregateGeometry.mixed_patches mixedNeighbors_iff
      (MixedAggregateGeometry.mixed_reach_walk) (MixedAggregateGeometry.mixed_boundary_detour
      (MixedAggregateGeometry.mixed_walk_reach)) (MixedAggregateGeometry.mixedTree_sound)
      (MixedAggregateGeometry.mixed_certificates)) (MixedAggregateGeometry.restore_mixed)
      cellDisk translation_complement (MixedAggregateGeometry.original_lattice q cfg C₀ T cert)
      mod_nonA mod_A (MixedAggregateGeometry.precursor_subset_A q cfg C₀ T cert
      (MixedAggregateGeometry.hOA q cfg C₀ T cert)) precursor_subset_B mod_subset
      (MixedAggregateGeometry.exception_certificate) (MixedAggregateGeometry.shared_vertex))
      (MixedAggregateGeometry.selection_certificate) (MixedAggregateGeometry.component_disjoint q
      cfg C₀ T cert (MixedAggregateGeometry.owner_certificate)
      (MixedAggregateGeometry.original_owner q cfg C₀ T cert mod_nonA mod_A precursor_subset_B)
      owners_mono) (MixedAggregateGeometry.component_edges q cfg C₀ T cert mixedNeighbors_iff
      mod_subset (MixedAggregateGeometry.edge_certificate) (MixedAggregateGeometry.edges_mono))
  have retarget := MixedAggregateGeometry.retarget cellDisk
  have imageJ := MixedAggregateGeometry.imageJ
  let back (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
    TileTranslation (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn S))) (GaussianQuarterTurn c)
  let turn (c : GaussianInt) (S : ProtoTile) : ProtoTile :=
    TileTranslation (TileQuarterTurn S) c
  have back_shift := MixedAggregateGeometry.back_shift
  have back_symmetric := MixedAggregateGeometry.back_symmetric (MixedAggregateGeometry.back_turn)
      (MixedAggregateGeometry.back_congr)
  have core_cells := MixedAggregateGeometry.core_cells q cfg C₀ T cert
      (MixedAggregateGeometry.outer_cells q cfg C₀ T cert)
  have component_zero := MixedAggregateGeometry.component_zero q cfg C₀ T cert core_cells
  let firstPeriod (i : Fin 3) : GaussianInt := match i.val with
    | 0 => cert.u
    | 1 => cert.v
    | _ => -cert.u-cert.v
  let firstShift (i : Fin 3) : GaussianInt := match i.val with
    | 0 => cert.u+cert.v
    | 1 => -cert.u
    | _ => -cert.v
  let firstParent (i : Fin 3) := TileTranslation (cert.P i false) (firstShift i)
  let plusRepresentative (i : Fin 3) : ProtoTile := match i.val with
    | 0 => TileTranslation (cert.P 0 true) (-cert.v)
    | 1 => TileTranslation (cert.P 1 true) (cert.u + cert.v)
    | _ => TileTranslation (cert.P 2 true) (-cert.u)
  let minusRepresentative (i : Fin 3) : ProtoTile := match i.val with
    | 0 => TileTranslation (cert.P 1 true) cert.u
    | 1 => TileTranslation (cert.P 2 true) cert.v
    | _ => TileTranslation (cert.P 0 true) (-cert.u - cert.v)
  have plus_band (i : Fin 3) : BandPrototile (q i.succ) (plusRepresentative i) := by
    fin_cases i <;> exact BandPrototileTranslation _ _ _ (cert.outer_occurrence _ true).1
  have minus_band (i : Fin 3) : BandPrototile (q ((i+1).succ)) (minusRepresentative i) := by
    fin_cases i <;> exact BandPrototileTranslation _ _ _ (cert.outer_occurrence _ true).1
  have all_centroids := MixedAggregateGeometry.all_centroids q cfg C₀ T cert
  constructor
  · intro i U hU hUc
    have hPU := BandPrototileCentroidUnique _ _ _ (plus_band i) hU
      (sub_left_injective ((all_centroids.1 i).trans hUc.symm))
    exact retarget T (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
      (plusRepresentative i) T (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U
      rfl rfl hPU.1 ((MixedAggregateGeometry.first_requested q cfg C₀ T cert hsym retarget
          back_shift (MixedAggregateGeometry.backJ (MixedAggregateGeometry.quarterJ imageJ)
          (MixedAggregateGeometry.translateJ imageJ)) back_symmetric
          (MixedAggregateGeometry.first_canonical q cfg C₀ T cert literal_junctions retarget
          component_zero (MixedAggregateGeometry.shifted_core q cfg C₀ T cert core_cells))
          plus_band all_centroids (MixedAggregateGeometry.symmetric_back_proxy back_shift
          back_symmetric) (MixedAggregateGeometry.centered_back_displacement
          (MixedAggregateGeometry.back_centroid)) (MixedAggregateGeometry.point_injective)) i)
  · intro i U V hU hV hUc hVc
    have hPU := BandPrototileCentroidUnique _ _ _ (plus_band i) hU
      (sub_left_injective ((all_centroids.1 i).trans hUc.symm))
    have hPV := BandPrototileCentroidUnique _ _ _ (minus_band i) hV
      (sub_left_injective ((all_centroids.2.1 i).trans hVc.symm))
    exact retarget T (plusRepresentative i) (minusRepresentative i) T U V rfl hPU.1 hPV.1
      ((MixedAggregateGeometry.second_canonical q cfg C₀ T cert literal_junctions retarget
          component_zero) i)

end ApollonianSuperharmonic

end

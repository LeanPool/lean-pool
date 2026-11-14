/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPeriodicOdometer
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.LatticeQuadraticForm
public import LeanPool.ApollonianSuperharmonic.PeriodicBoundaryWebLaplacian
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: BandCanonicalPeriodicExtension]

/-!
# BandCanonicalPeriodicExtension

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandCanonicalPeriodicExtension (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hqC : q 0 = C.1.1) (T : ProtoTile) (h : PartialOdometer)
    (g : IntegerLatticeFunction) (hT : BandPrototile (q 0) T)
    (hodo : TileOdometer (q 0) T h)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
    (hext : GlobalOdometerExtends g h) :
    ∃ g₀ : IntegerLatticeFunction,
      GlobalOdometerExtends g₀ h ∧
      LatticeTile T ∧
      ExactTileTiling (RegularTileFamily T (TilingLattice C)) ∧
      (∀ x, x ∈ BoundaryFootprintVertices T →
        FourNeighborLaplacian g₀ x = 1) ∧
      (∃ b : ℝ × ℝ, ∀ v, v ∈ TilingLattice C → ∀ x,
        (g₀ (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
            (b.1 * (x + v).re + b.2 * (x + v).im) =
          (g₀ x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
            (b.1 * x.re + b.2 * x.im)) ∧
      (∀ x, x ∈ h.domain → x ∉ BoundaryFootprintVertices T →
        FourNeighborLaplacian g₀ x = FourNeighborLaplacian g x) := by
-- BODY
  classical
  obtain ⟨U, k, G, hU, hk, hG, hcocycle, hperiod⟩ := BandPeriodicOdometer C
  have hpos : 0 < (q 0).1 := (ProperBandCurvatureStructure q hq).1
  have hTC : BandPrototile C.1.1 T := by simpa [hqC] using hT
  have hodoC : TileOdometer C.1.1 T h := by simpa [hqC] using hodo
  obtain ⟨u, hu, hunique⟩ := TileOdometerTranslationUniqueness
    (q 0) T U h k hpos hodo (by simpa [hqC] using hk)
  obtain ⟨a, d, hdomu, hval⟩ := hu.2.2
  obtain ⟨c, hc⟩ := hG
  let g₀ : IntegerLatticeFunction := fun x =>
    G (x - u) + a.re * x.re + a.im * x.im - G (-u)
  have hext₀ : GlobalOdometerExtends g₀ h := by
    refine ⟨c - d - G (-u), ?_⟩
    intro x hx
    have hx' : x - u ∈ k.domain := (hdomu x).mp hx
    have hv := hval x hx
    have hg := hc (x - u) hx'
    dsimp [g₀]
    rw [hg]
    omega
  have htile := (BandTileSimultaneousInduction q hq T hT).1
  have htop := (BandTileTopologyApplication C q hq hqC T hT).1
  have hcocycle₀ : ∀ v, v ∈ TilingLattice C → ∃ aa : GaussianInt,
      Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
        ![(aa.re : ℝ), (aa.im : ℝ)] ∧
      ∀ x, g₀ (x + v) = g₀ x + x.re * aa.re + x.im * aa.im + g₀ v := by
    intro v hv
    obtain ⟨aa, haa, hgv⟩ := hcocycle v hv
    refine ⟨aa, haa, ?_⟩
    intro x
    have h1 : G (x + v - u) = G (x - u) + (x - u).re * aa.re +
        (x - u).im * aa.im + G v := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hgv (x - u)
    have h2 : G (v - u) = G (-u) + (-u).re * aa.re +
        (-u).im * aa.im + G v := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hgv (-u)
    dsimp [g₀]
    rw [h1, h2]
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    ring
  have hboundary : ∀ x, x ∈ BoundaryFootprintVertices T →
      FourNeighborLaplacian g₀ x = 1 := by
    intro x hx
    apply PeriodicBoundaryWebLaplacian C T h g₀ hTC hodoC hext₀ hcocycle₀
    refine ⟨0, (TilingLattice C).zero_mem, ?_⟩
    have hz := (TileTranslationFormulas T 0).2.2.2.2.2.2.2.1
    rw [hz]
    simpa [GaussianTranslation] using hx
  refine ⟨g₀, hext₀, htile, htop, hboundary, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hperiod
    obtain ⟨b0, hb0⟩ := PeriodicQuadraticRemainder C g₀ hcocycle₀
    refine ⟨b0, ?_⟩
    intro v hv x
    exact hb0 v hv x
  · intro x hx hxb
    have hfoot : x ∈ FootprintVertices T := by
      rw [← hdom]
      exact hx
    have hnonempty : T.cells.Nonempty := by
      by_contra hn
      have hxa : x = T.anchor := by
        simpa [FootprintVertices, hn] using hfoot
      apply hxb
      simp [BoundaryFootprintVertices, hn, hxa]
    have hfoot' := hfoot
    simp only [FootprintVertices, hnonempty, ↓reduceIte, Int.reduceNeg, Set.mem_ofPred_eq]
        at hfoot'
    have some : x ∈ T.cells ∨ x - 1 ∈ T.cells ∨
        x - 1 - ⟨0, 1⟩ ∈ T.cells ∨ x - ⟨0, 1⟩ ∈ T.cells := by
      rcases hfoot' with ⟨z, hz, rfl | rfl | rfl | rfl⟩
      · exact Or.inl hz
      · exact Or.inr (Or.inl (by simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          hz))
      · exact Or.inr (Or.inr (Or.inr (by simpa [sub_eq_add_neg, add_assoc, add_comm,
          add_left_comm] using hz)))
      · exact Or.inr (Or.inr (Or.inl (by simpa [sub_eq_add_neg, add_assoc, add_comm,
          add_left_comm] using hz)))
    have edge03a (p0 : x ∈ T.cells) (p3 : x - ⟨0, 1⟩ ∉ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x, x + 1}, ?_, by simp⟩
      exact ⟨x, Or.inl ⟨rfl, Or.inl ⟨p0, p3⟩⟩⟩
    have edge03b (p0 : x ∉ T.cells) (p3 : x - ⟨0, 1⟩ ∈ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x, x + 1}, ?_, by simp⟩
      exact ⟨x, Or.inl ⟨rfl, Or.inr ⟨p0, p3⟩⟩⟩
    have edge12a (p1 : x - 1 ∈ T.cells) (p2 : x - 1 - ⟨0, 1⟩ ∉ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x - 1, x}, ?_, by simp⟩
      exact ⟨x - 1, Or.inl ⟨(by ext; simp), Or.inl ⟨p1, p2⟩⟩⟩
    have edge12b (p1 : x - 1 ∉ T.cells) (p2 : x - 1 - ⟨0, 1⟩ ∈ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x - 1, x}, ?_, by simp⟩
      exact ⟨x - 1, Or.inl ⟨(by ext; simp), Or.inr ⟨p1, p2⟩⟩⟩
    have edge01a (p0 : x ∈ T.cells) (p1 : x - 1 ∉ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x, x + ⟨0, 1⟩}, ?_, by simp⟩
      exact ⟨x, Or.inr ⟨rfl, Or.inl ⟨p0, p1⟩⟩⟩
    have edge01b (p0 : x ∉ T.cells) (p1 : x - 1 ∈ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x, x + ⟨0, 1⟩}, ?_, by simp⟩
      exact ⟨x, Or.inr ⟨rfl, Or.inr ⟨p0, p1⟩⟩⟩
    have edge32a (p3 : x - ⟨0, 1⟩ ∈ T.cells) (p2 : x - 1 - ⟨0, 1⟩ ∉ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x - ⟨0, 1⟩, x}, ?_, by simp⟩
      refine ⟨x - ⟨0, 1⟩, Or.inr ⟨(by ext; simp), Or.inl ⟨p3, ?_⟩⟩⟩
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using p2
    have edge32b (p3 : x - ⟨0, 1⟩ ∉ T.cells) (p2 : x - 1 - ⟨0, 1⟩ ∈ T.cells) :
        x ∈ BoundaryFootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      refine ⟨{x - ⟨0, 1⟩, x}, ?_, by simp⟩
      refine ⟨x - ⟨0, 1⟩, Or.inr ⟨(by ext; simp), Or.inr ⟨p3, ?_⟩⟩⟩
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using p2
    have iff03 : x ∈ T.cells ↔ x - ⟨0, 1⟩ ∈ T.cells := by
      constructor <;> intro hp <;> by_contra hn
      · exact hxb (edge03a hp hn)
      · exact hxb (edge03b hn hp)
    have iff12 : x - 1 ∈ T.cells ↔ x - 1 - ⟨0, 1⟩ ∈ T.cells := by
      constructor <;> intro hp <;> by_contra hn
      · exact hxb (edge12a hp hn)
      · exact hxb (edge12b hn hp)
    have iff01 : x ∈ T.cells ↔ x - 1 ∈ T.cells := by
      constructor <;> intro hp <;> by_contra hn
      · exact hxb (edge01a hp hn)
      · exact hxb (edge01b hn hp)
    have iff32 : x - ⟨0, 1⟩ ∈ T.cells ↔ x - 1 - ⟨0, 1⟩ ∈ T.cells := by
      constructor <;> intro hp <;> by_contra hn
      · exact hxb (edge32a hp hn)
      · exact hxb (edge32b hn hp)
    have allfour : x ∈ T.cells ∧ x - 1 ∈ T.cells ∧
        x - 1 - ⟨0, 1⟩ ∈ T.cells ∧ x - ⟨0, 1⟩ ∈ T.cells := by
      rcases some with p0 | p1 | p2 | p3
      · have p1' := iff01.mp p0
        have p2' := iff12.mp p1'
        have p3' := iff03.mp p0
        exact ⟨p0, p1', p2', p3'⟩
      · have p0' := iff01.mpr p1
        have p2' := iff12.mp p1
        have p3' := iff03.mp p0'
        exact ⟨p0', p1, p2', p3'⟩
      · have p1' := iff12.mpr p2
        have p0' := iff01.mpr p1'
        have p3' := iff03.mp p0'
        exact ⟨p0', p1', p2, p3'⟩
      · have p0' := iff03.mpr p3
        have p1' := iff01.mp p0'
        have p2' := iff32.mp p3
        exact ⟨p0', p1', p2', p3⟩
    have hxp : x + 1 ∈ h.domain := by
      change x + 1 ∈ (h.domain : Set GaussianInt)
      rw [hdom]
      simp only [FootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      exact ⟨x, allfour.1, Or.inr (Or.inl rfl)⟩
    have hxm : x - 1 ∈ h.domain := by
      change x - 1 ∈ (h.domain : Set GaussianInt)
      rw [hdom]
      simp only [FootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      exact ⟨x - 1, allfour.2.1, Or.inl rfl⟩
    have hxpi : x + ⟨0, 1⟩ ∈ h.domain := by
      change x + ⟨0, 1⟩ ∈ (h.domain : Set GaussianInt)
      rw [hdom]
      simp only [FootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      exact ⟨x, allfour.1, Or.inr (Or.inr (Or.inl rfl))⟩
    have hxmi : x - ⟨0, 1⟩ ∈ h.domain := by
      change x - ⟨0, 1⟩ ∈ (h.domain : Set GaussianInt)
      rw [hdom]
      simp only [FootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      exact ⟨x - ⟨0, 1⟩, allfour.2.2.2, Or.inl rfl⟩
    obtain ⟨cg, hcg⟩ := hext
    obtain ⟨c0, hc0⟩ := hext₀
    simp only [FourNeighborLaplacian]
    rw [hc0 (x + 1) hxp, hc0 (x - 1) hxm, hc0 (x + ⟨0, 1⟩) hxpi,
      hc0 (x - ⟨0, 1⟩) hxmi, hc0 x hx]
    rw [hcg (x + 1) hxp, hcg (x - 1) hxm,
      hcg (x + ⟨0, 1⟩) hxpi, hcg (x - ⟨0, 1⟩) hxmi, hcg x hx]
    ring

end ApollonianSuperharmonic

end

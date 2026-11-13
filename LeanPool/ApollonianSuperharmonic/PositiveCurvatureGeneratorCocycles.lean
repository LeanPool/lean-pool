/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTranslatedOdometers
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.TileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.BandTileTopologyApplication

-- [TABLET NODE: PositiveCurvatureGeneratorCocycles]

/-!
# PositiveCurvatureGeneratorCocycles

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GeneratorCocycleGeometry

private theorem hcoords :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) →
            ((q (0 : Fin (4 : ℕ)) = C.1.1) → (∀ w : TilingLattice C, ∃ mn : Int × Int, (mn.1 :
            GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 : GaussianInt) * BandVectors.1 (q 2)
            (q 0) = (w : GaussianInt))) ) := by
  classical
  intro C q hq hqC w
  exact (TilingLatticeBasis C q hq hqC).2.2.1 w |>.exists

private theorem hlat :
    (by
      classical
      exact
        ∀ (C : BandCircle),
          ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            ∀ (T : ProtoTile),
              ∀ (h : PartialOdometer),
                ∀ (H : ℤ × ℤ → PartialOdometer),
                  (∀ (kl : ℤ × ℤ),
                      let w :=
                        (↑kl.1 : GaussianInt) *
                            BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) +
                          (↑kl.2 : GaussianInt) *
                            BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)));
                      let a :=
                        (↑kl.1 : GaussianInt) *
                            BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) +
                          (↑kl.2 : GaussianInt) *
                            BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)));
                      TileOdometer C.1.1 (TileTranslation T w) (H kl) ∧
                        (∀ (x : GaussianInt), x ∈ (H kl).domain ↔ x - w ∈ h.domain) ∧
                          ∀ x ∈ (H kl).domain,
                            (H kl).value x =
                              h.value (x - w) + a.re * x.re + a.im * x.im) →
                    (h.domain : Set GaussianInt) = FootprintVertices T →
                      ExactTileTiling (RegularTileFamily T (TilingLattice C)) →
                        LatticeTile T
    ) := by
  classical
  intro C q T h H htrans hdom tiling
  apply tiling.1 T
  refine ⟨0, (TilingLattice C).zero_mem, ?_⟩
  cases T
  congr 1
  · rw [show GaussianTranslation 0 = id by funext z; simp [GaussianTranslation]]
    simp only [Finset.image_id]
  · simp [GaussianTranslation]

private theorem hfamily :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile),
            (ProperBandQuadruple q) → ((q (0 : Fin (4 : ℕ)) = C.1.1) → ((ExactTileTiling
            (RegularTileFamily T (TilingLattice C))) → (∀ kl : Int × Int, LatticeTile
            (TileTranslation T ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (kl.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))))) ) := by
  classical
  intro C q T hq hqC tiling (kl : Int × Int)
  apply tiling.1
  refine ⟨_, ?_, rfl⟩
  exact (TilingLattice C).add_mem
    (by simpa using (TilingLattice C).zsmul_mem (by
      exact (TilingLatticeBasis C q hq hqC).1) kl.1)
    (by simpa using (TilingLattice C).zsmul_mem (by
      exact (TilingLatticeBasis C q hq hqC).2.1) kl.2)

private theorem hglobal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (H : ℤ × ℤ → PartialOdometer), (∀ (kl : ℤ × ℤ),
        let w := (↑kl.1 : GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ))) + (↑kl.2 : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ)));
        let a := (↑kl.1 : GaussianInt) * BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ))) + (↑kl.2 : GaussianInt) * BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ))); TileOdometer C.1.1 (TileTranslation T w) (H kl) ∧ (∀ (x : GaussianInt), x ∈ (H
            kl).domain ↔ x - w ∈ h.domain) ∧ ∀ x ∈ (H kl).domain, (H kl).value x = h.value (x -
            w) + a.re * x.re + a.im * x.im) → ((∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ),
            OdometerCompatibility (H kl) (H mn)) → ((∀ (c : CircleCoordinates), ∀ (U :
            ProtoTile), ∀ (k : PartialOdometer), TileOdometer c U k → (k.domain : Set
            GaussianInt) = FootprintVertices U) → (((h.domain : Set GaussianInt) =
            FootprintVertices T) → ((∀ w : TilingLattice C, ∃ mn : Int × Int, (mn.1 :
            GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 : GaussianInt) * BandVectors.1 (q 2)
            (q 0) = (w : GaussianInt)) → ((ExactTileTiling (RegularTileFamily T (TilingLattice
            C))) → ((∀ kl : Int × Int, LatticeTile (TileTranslation T ((kl.1 : GaussianInt) *
            BandVectors.1 (q 1) (q 0) + (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)))) → (∃
            g : IntegerLatticeFunction, (∀ i, ∃ c : ℤ, ∀ x, x ∈ (H i).domain → g x - (H i).value
            x = c) ∧ ∀ g' : IntegerLatticeFunction, (∀ i, ∃ c : ℤ, ∀ x, x ∈ (H i).domain → g' x -
            (H i).value x = c) → ∃ c : ℤ, ∀ x, g' x - g x = c))))))) ) := by
  classical
  intro C q T h H htrans hcompat domain_from_odo hdom hcoords tiling hfamily
  apply (OdometerGluing).2
  · intro i
    exact hfamily i
  · intro i
    exact domain_from_odo _ _ _ (htrans i).1
  · exact hcompat
  · intro x
    obtain ⟨U, hUF, hxU, _⟩ := tiling.2 x
    rcases hUF with ⟨w, hw, rfl⟩
    rcases hcoords ⟨w, hw⟩ with ⟨kl, hkl⟩
    refine ⟨kl, ?_⟩
    have hx := hxU
    have hkl' : (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
        (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = w := by
      simpa using hkl
    rw [← hkl'] at hx
    have base : x - ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
        (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) ∈ T.cells := by
      simp only [TileTranslation, Finset.mem_image, GaussianTranslation] at hx
      rcases hx with ⟨a, ha, he⟩
      have he' : x - ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) = a := by
        rw [← he]
        simp []
      rw [he']
      exact ha
    have vertex (z : GaussianInt)
        (hz : z = x - ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) ∨
          z = x - ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) + 1 ∨
          z = x - ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) + ⟨0, 1⟩ ∨
          z = x - ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) + 1 + ⟨0, 1⟩) :
        z ∈ h.domain := by
      change z ∈ (h.domain : Set GaussianInt)
      rw [hdom]
      have nonempty : T.cells.Nonempty := ⟨_, base⟩
      simp only [FootprintVertices, ite_eq_left nonempty, Set.mem_ofPred_eq]
      exact ⟨x - ((kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
        (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)), base, hz⟩
    refine ⟨(htrans kl).2.1 x |>.mpr (vertex _ (Or.inl rfl)), ?_, ?_, ?_⟩
    · apply (htrans kl).2.1 (x + 1) |>.mpr
      apply vertex _
      right; left; abel
    · apply (htrans kl).2.1 (x + ⟨0, 1⟩) |>.mpr
      apply vertex _
      right; right; left; abel
    · apply (htrans kl).2.1 (x + 1 + ⟨0, 1⟩) |>.mpr
      apply vertex _
      right; right; right; abel

private theorem shift_cocycle :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (H : ℤ × ℤ → PartialOdometer), (∀ (kl : ℤ × ℤ),
        let w := (↑kl.1 : GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ))) + (↑kl.2 : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ)));
        let a := (↑kl.1 : GaussianInt) * BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ))) + (↑kl.2 : GaussianInt) * BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ))); TileOdometer C.1.1 (TileTranslation T w) (H kl) ∧ (∀ (x : GaussianInt), x ∈ (H
            kl).domain ↔ x - w ∈ h.domain) ∧ ∀ x ∈ (H kl).domain, (H kl).value x = h.value (x -
            w) + a.re * x.re + a.im * x.im) → (∀ (g : IntegerLatticeFunction), (∀ (i : ℤ × ℤ), ∃
            (c : ℤ), ∀ x ∈ (H i).domain, g x - (H i).value x = c) → ((∀ (g' :
            IntegerLatticeFunction), (∀ (i : ℤ × ℤ), ∃ (c : ℤ), ∀ x ∈ (H i).domain, g' x - (H
            i).value x = c) → ∃ (c : ℤ), ∀ (x : GaussianInt), g' x - g x = c) → (∀ (d : Int ×
            Int), ∀ (v : GaussianInt), ∀ (a : GaussianInt), (∀ i : Int × Int, (↑(i.1 + d.1) :
            GaussianInt) * BandVectors.1 (q 1) (q 0) + (↑(i.2 + d.2) : GaussianInt) *
            BandVectors.1 (q 2) (q 0) = (↑i.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (↑i.2
            : GaussianInt) * BandVectors.1 (q 2) (q 0) + v) → (∀ i : Int × Int, (↑(i.1 + d.1) :
            GaussianInt) * BandVectors.2 (q 1) (q 0) + (↑(i.2 + d.2) : GaussianInt) *
            BandVectors.2 (q 2) (q 0) = (↑i.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) + (↑i.2
            : GaussianInt) * BandVectors.2 (q 2) (q 0) + a) → ∃ c : ℤ, ∀ x, g (x + v) - x.re *
            a.re - x.im * a.im - g x = c))) ) := by
  classical
  intro C q T h H htrans g hg huniq d v a hw ha
  let gs : IntegerLatticeFunction := fun x =>
    g (x + v) - x.re * a.re - x.im * a.im
  have gscomp : ∀ i, ∃ c : ℤ, ∀ x, x ∈ (H i).domain →
      gs x - (H i).value x = c := by
    intro i
    obtain ⟨c, hc⟩ := hg (i.1 + d.1, i.2 + d.2)
    let s := (↑i.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
      (↑i.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
    refine ⟨c + s.re * v.re + s.im * v.im + a.re * v.re + a.im * v.im, ?_⟩
    intro x hx
    have hx' : x + v ∈ (H (i.1 + d.1, i.2 + d.2)).domain := by
      apply (htrans (i.1 + d.1, i.2 + d.2)).2.1 (x + v) |>.mpr
      have hi := (htrans i).2.1 x |>.mp hx
      rw [hw i]
      convert hi using 1; ring
    have hi := (htrans i).2.2 x hx
    have hi' := (htrans (i.1 + d.1, i.2 + d.2)).2.2 (x + v) hx'
    have harg : (x + v) -
        ((↑(i.1 + d.1) : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (↑(i.2 + d.2) : GaussianInt) * BandVectors.1 (q 2) (q 0)) =
        x - ((↑i.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (↑i.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)) := by
      rw [hw i]
      ring
    rw [harg] at hi'
    dsimp [gs]
    have ha' := ha i
    calc
      g (x + v) - x.re * a.re - x.im * a.im - (H i).value x =
          (g (x + v) - (H (i.1 + d.1, i.2 + d.2)).value (x + v)) +
            ((H (i.1 + d.1, i.2 + d.2)).value (x + v) -
              x.re * a.re - x.im * a.im - (H i).value x) := by ring
      _ = c + s.re * v.re + s.im * v.im + a.re * v.re + a.im * v.im := by
        rw [hc (x + v) hx', hi', hi, ha']
        simp [s] at ⊢; ring
  obtain ⟨c, hc⟩ := huniq gs gscomp
  refine ⟨c, ?_⟩
  intro x
  have hz := hc x
  dsimp [gs] at hz
  have hz0 := hc 0
  dsimp [gs] at hz0
  have : c = g v - g 0 := by
    simpa using hz0.symm
  rw [this] at hz
  linarith

private theorem heqAt349 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (g : IntegerLatticeFunction), ∀ (x :
            GaussianInt), ∀ (c : ℤ), (g (x + BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ)))) - x.re * (BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))).re - x.im
            * (BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))).im - g x = c) → (g (x +
            BandVectors.1 (q 1) (q 0)) = g x + x.re * (BandVectors.2 (q 1) (q 0)).re + x.im *
            (BandVectors.2 (q 1) (q 0)).im + c) ) := by
  classical
  intro q g x c hz
  linarith [hz]

private theorem calibrationAtOrigin (g : IntegerLatticeFunction)
    (v a : GaussianInt) (c : Int)
    (hc : ∀ x : GaussianInt,
      g (x + v) - x.re * a.re - x.im * a.im - g x = c) :
    c = g v - g 0 := by
  have atOrigin := hc 0
  simpa using atOrigin.symm

private theorem heqAt366 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (g : IntegerLatticeFunction), ∀ (x :
            GaussianInt), ∀ (c : ℤ), (g (x + BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ)))) - x.re * (BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))).re - x.im
            * (BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))).im - g x = c) → (g (x +
            BandVectors.1 (q 2) (q 0)) = g x + x.re * (BandVectors.2 (q 2) (q 0)).re + x.im *
            (BandVectors.2 (q 2) (q 0)).im + c) ) := by
  classical
  intro q g x c hz
  linarith [hz]

private theorem hvAt384 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (BandVectors.1 (q (1 : Fin ((2 : ℕ) + (1 : ℕ) +
            (1 : ℕ)))) (q (0 : Fin (4 : ℕ))) + (BandVectors.1 (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1
            : ℕ)))) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ)))) = (0 : GaussianInt)) → (BandVectors.1 (q 3) (q 0) = -(BandVectors.1 (q 1) (q 0)
            + BandVectors.1 (q 2) (q 0))) ) := by
  classical
  intro q rr
  apply eq_neg_of_add_eq_zero_left
  linear_combination rr

private theorem hvAt395 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (BandVectors.2 (q (1 : Fin ((2 : ℕ) + (1 : ℕ) +
            (1 : ℕ)))) (q (0 : Fin (4 : ℕ))) + (BandVectors.2 (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1
            : ℕ)))) (q (0 : Fin (4 : ℕ))) + BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ)))) = (0 : GaussianInt)) → (BandVectors.2 (q 3) (q 0) = -(BandVectors.2 (q 1) (q 0)
            + BandVectors.2 (q 2) (q 0))) ) := by
  classical
  intro q rr
  apply eq_neg_of_add_eq_zero_left
  linear_combination rr

private theorem heqAt404 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (g : IntegerLatticeFunction), ∀ (x :
            GaussianInt), ∀ (c : ℤ), (g (x + BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (0 : Fin (4 :
            ℕ)))) - x.re * (BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))).re - x.im
            * (BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))).im - g x = c) → (g (x +
            BandVectors.1 (q 3) (q 0)) = g x + x.re * (BandVectors.2 (q 3) (q 0)).re + x.im *
            (BandVectors.2 (q 3) (q 0)).im + c) ) := by
  classical
  intro q g x c hz
  linarith [hz]

end GeneratorCocycleGeometry

theorem PositiveCurvatureGeneratorCocycles (C : BandCircle)
    (hc : 1 < C.1.1.1) :
    ∃ (q : Fin 4 → CircleCoordinates) (T : ProtoTile) (h : PartialOdometer)
        (g : IntegerLatticeFunction),
      ProperBandQuadruple q ∧ q 0 = C.1.1 ∧
      BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h ∧
      GlobalOdometerExtends g h ∧ g 0 = 0 ∧
      ∀ j : Fin 3, ∀ x,
        g (x + BandVectors.1 (q j.succ) (q 0)) = g x +
          x.re * (BandVectors.2 (q j.succ) (q 0)).re +
          x.im * (BandVectors.2 (q j.succ) (q 0)).im +
          g (BandVectors.1 (q j.succ) (q 0)) := by
-- BODY
  obtain ⟨q, T, h, H, hq, hqC, hT, hodo, htrans, hcompat⟩ :=
    PositiveCurvatureTranslatedOdometers C hc
  have domain_from_odo := TileOdometerDomain
  have hdom : (h.domain : Set GaussianInt) = FootprintVertices T :=
    domain_from_odo _ _ _ hodo
  have tiling : ExactTileTiling (RegularTileFamily T (TilingLattice C)) :=
    (BandTileTopologyApplication C q hq hqC T (by simpa [hqC] using hT)).1
  have hglobal := GeneratorCocycleGeometry.hglobal C q T h H htrans hcompat domain_from_odo hdom
      (GeneratorCocycleGeometry.hcoords C q hq hqC) tiling (GeneratorCocycleGeometry.hfamily C q
      T hq hqC tiling)
  rcases hglobal with ⟨g, hg, huniq⟩
  refine ⟨q, T, h, fun x => g x - g 0, hq, hqC, hT, hodo, ?_, ?_, ?_⟩
  · rcases hg (0, 0) with ⟨c, hc⟩
    refine ⟨c - g 0, ?_⟩
    intro x hx
    have hxH := (htrans (0, 0)).2.1 x |>.mpr (by simpa using hx)
    have hv := (htrans (0, 0)).2.2 x hxH
    dsimp
    calc
      g x - g 0 = (g x - (H (0, 0)).value x) +
          (H (0, 0)).value x - g 0 := by ring
      _ = c + h.value x - g 0 := by
        rw [hc x hxH]
        simpa using hv
      _ = h.value x + (c - g 0) := by ring
  · simp
  · intro j x
    have shift_cocycle := GeneratorCocycleGeometry.shift_cocycle C q T h H htrans g hg huniq
    have rel := IncomingSuperbasisRelation q hq
    fin_cases j
    · obtain ⟨c, hc⟩ := shift_cocycle (1, 0)
        (BandVectors.1 (q 1) (q 0)) (BandVectors.2 (q 1) (q 0))
        (by intro i; simp; ring) (by intro i; simp; ring)
      have hz := hc x
      have heq : g (x + BandVectors.1 (q 1) (q 0)) =
          g x + x.re * (BandVectors.2 (q 1) (q 0)).re +
            x.im * (BandVectors.2 (q 1) (q 0)).im + c := GeneratorCocycleGeometry.heqAt349 q g x
                c hz
      have hcval : c = g (BandVectors.1 (q 1) (q 0)) - g 0 :=
          GeneratorCocycleGeometry.calibrationAtOrigin g (BandVectors.1 (q 1) (q 0))
          (BandVectors.2 (q 1) (q 0)) c hc
      change g (x + BandVectors.1 (q 1) (q 0)) - g 0 =
        (g x - g 0) + x.re * (BandVectors.2 (q 1) (q 0)).re +
          x.im * (BandVectors.2 (q 1) (q 0)).im +
            (g (BandVectors.1 (q 1) (q 0)) - g 0)
      rw [heq, hcval]
      ring
    · obtain ⟨c, hc⟩ := shift_cocycle (0, 1)
        (BandVectors.1 (q 2) (q 0)) (BandVectors.2 (q 2) (q 0))
        (by intro i; simp; ring) (by intro i; simp; ring)
      have hz := hc x
      have heq : g (x + BandVectors.1 (q 2) (q 0)) =
          g x + x.re * (BandVectors.2 (q 2) (q 0)).re +
            x.im * (BandVectors.2 (q 2) (q 0)).im + c := GeneratorCocycleGeometry.heqAt366 q g x
                c hz
      have hcval : c = g (BandVectors.1 (q 2) (q 0)) - g 0 :=
          GeneratorCocycleGeometry.calibrationAtOrigin g (BandVectors.1 (q 2) (q 0))
          (BandVectors.2 (q 2) (q 0)) c hc
      change g (x + BandVectors.1 (q 2) (q 0)) - g 0 =
        (g x - g 0) + x.re * (BandVectors.2 (q 2) (q 0)).re +
          x.im * (BandVectors.2 (q 2) (q 0)).im +
            (g (BandVectors.1 (q 2) (q 0)) - g 0)
      rw [heq, hcval]
      ring
    · obtain ⟨c, hc⟩ := shift_cocycle (-1, -1)
        (BandVectors.1 (q 3) (q 0)) (BandVectors.2 (q 3) (q 0))
        (by
          have rr := rel.1
          simp only [Fin.isValue, Fin.sum_univ_succ, Fin.succ_zero_eq_one,
              Fin.succ_one_eq_two, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton, Fin.reduceSucc] at rr
          have hv : BandVectors.1 (q 3) (q 0) =
              -(BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0)) :=
                  GeneratorCocycleGeometry.hvAt384 q rr
          intro i
          norm_num
          rw [hv]
          ring)
        (by
          have rr := rel.2
          simp only [Fin.isValue, Fin.sum_univ_succ, Fin.succ_zero_eq_one,
              Fin.succ_one_eq_two, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton, Fin.reduceSucc] at rr
          have hv : BandVectors.2 (q 3) (q 0) =
              -(BandVectors.2 (q 1) (q 0) + BandVectors.2 (q 2) (q 0)) :=
                  GeneratorCocycleGeometry.hvAt395 q rr
          intro i
          norm_num
          rw [hv]
          ring)
      have hz := hc x
      have heq : g (x + BandVectors.1 (q 3) (q 0)) =
          g x + x.re * (BandVectors.2 (q 3) (q 0)).re +
            x.im * (BandVectors.2 (q 3) (q 0)).im + c := GeneratorCocycleGeometry.heqAt404 q g x
                c hz
      have hcval : c = g (BandVectors.1 (q 3) (q 0)) - g 0 :=
          GeneratorCocycleGeometry.calibrationAtOrigin g (BandVectors.1 (q 3) (q 0))
          (BandVectors.2 (q 3) (q 0)) c hc
      change g (x + BandVectors.1 (q 3) (q 0)) - g 0 =
        (g x - g 0) + x.re * (BandVectors.2 (q 3) (q 0)).re +
          x.im * (BandVectors.2 (q 3) (q 0)).im +
            (g (BandVectors.1 (q 3) (q 0)) - g 0)
      rw [heq, hcval]
      ring

end ApollonianSuperharmonic

end

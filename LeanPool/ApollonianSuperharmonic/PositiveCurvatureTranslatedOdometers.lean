/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileOdometerExists
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: PositiveCurvatureTranslatedOdometers]

/-!
# PositiveCurvatureTranslatedOdometers

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PositiveTranslationGeometry

private theorem slope_for :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates),
          ∀ (U : ProtoTile),
            ∀ (k : PartialOdometer),
              TileOdometer c U k → 1 < c.1 → ∃ p : ℝ × ℝ, PartialOdometerSlope k = some p
    ) := by
  classical
  intro c U k ho hc
  induction ho with
  | line w x hw hdom => omega
  | unit z x U hU hdom htrans => omega
  | @decompose q' hq' S U hs k hU hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
      have facts := ProperBandCurvatureStructure q' hq'
      have hp : ∃ i : Fin 3, 0 < (q' i.succ).1 := by
        by_cases h0 : 0 < (q' (0 : Fin 3).succ).1
        · exact ⟨0, h0⟩
        by_cases h1 : 0 < (q' (1 : Fin 3).succ).1
        · exact ⟨1, h1⟩
        by_cases h2 : 0 < (q' (2 : Fin 3).succ).1
        · exact ⟨2, h2⟩
        have n0 := facts.2.1 (0 : Fin 3)
        have n1 := facts.2.1 (1 : Fin 3)
        have z0 : (q' (0 : Fin 3).succ).1 = 0 := by omega
        have z1 : (q' (1 : Fin 3).succ).1 = 0 := by omega
        exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim
      rcases hp with ⟨i, hi⟩
      rcases hslope i false with hz | ⟨p, pi, hp, hpi, hpr, hpi'⟩
      · omega
      exact ⟨p, hp⟩

private theorem lattice_coords :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (q (0 : Fin (4 : ℕ)) =
            C.1.1) → ((ProperBandQuadruple q) → (
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ kl : Int × Int, shift kl ∈ TilingLattice C)) ) := by
  classical
  intro C q hqC hq shift kl
  dsimp [shift]
  exact (TilingLattice C).add_mem
    (by simpa using ((TilingLattice C).zsmul_mem (TilingLatticeBasis C q hq hqC).1 kl.1))
    (by simpa using ((TilingLattice C).zsmul_mem (TilingLatticeBasis C q hq hqC).2.1 kl.2))

private theorem index_injective :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (q (0 : Fin (4 : ℕ)) =
            C.1.1) → ((ProperBandQuadruple q) → (
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (lattice_coords : ∀ kl : Int × Int, shift kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        Function.Injective index)) ) := by
  classical
  intro C q hqC hq shift lattice_coords index kl mn heq
  have hu := (TilingLatticeBasis C q hq hqC).2.2.1 (index kl)
  have hk : (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
      (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (index kl : GaussianInt) := rfl
  have hm : (mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
      (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (index kl : GaussianInt) := by
    change shift mn = shift kl
    exact (congrArg (fun z : TilingLattice C => (z : GaussianInt)) heq).symm
  exact hu.unique hk hm

private theorem slope_step :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        ∀ (lattice_coords : ∀ kl : Int × Int, shift kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        (Function.Injective index) → (∀ (r : Int × Int), ∀ (s : Int × Int), ∀ (i : Fin 3), shift
            s - shift r = BandVectors.1 (q i.succ) (q 0) → slopeShift s - slopeShift r =
            BandVectors.2 (q i.succ) (q 0))) ) := by
  classical
  intro C q hq shift slopeShift lattice_coords index index_injective r s i hs
  have hsum := IncomingSuperbasisRelation q hq
  fin_cases i
  · have he : index (r.1 + 1, r.2) = index s := by
      apply Subtype.ext
      change shift (r.1 + 1, r.2) = shift s
      calc
        shift (r.1 + 1, r.2) = shift r + BandVectors.1 (q 1) (q 0) := by
          simp [shift, add_comm]
          ring
        _ = shift s := by
          have hh := sub_eq_iff_eq_add.mp hs
          simpa [add_comm] using hh.symm
    have hc := index_injective he
    dsimp [slopeShift]
    rw [← hc]
    push_cast
    ring
  · have he : index (r.1, r.2 + 1) = index s := by
      apply Subtype.ext
      change shift (r.1, r.2 + 1) = shift s
      calc
        shift (r.1, r.2 + 1) = shift r + BandVectors.1 (q 2) (q 0) := by
          simp [shift, add_comm, add_left_comm]
          ring
        _ = shift s := by
          have hh := sub_eq_iff_eq_add.mp hs
          simpa [add_comm] using hh.symm
    have hc := index_injective he
    dsimp [slopeShift]
    rw [← hc]
    push_cast
    ring
  · have h3 : BandVectors.1 (q (2 : Fin 3).succ) (q 0) =
        -BandVectors.1 (q 1) (q 0) - BandVectors.1 (q 2) (q 0) := by
      have finthree : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
      have expanded : BandVectors.1 (q 1) (q 0) +
          (BandVectors.1 (q 2) (q 0) + BandVectors.1 (q (Fin.succ (2 : Fin 3))) (q 0)) = 0 := by
        simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, zero_add,
          Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, finthree] using hsum.1
      linear_combination expanded
    have he : index (r.1 - 1, r.2 - 1) = index s := by
      apply Subtype.ext
      change shift (r.1 - 1, r.2 - 1) = shift s
      calc
        shift (r.1 - 1, r.2 - 1) = shift r + BandVectors.1 (q (2 : Fin 3).succ) (q 0) := by
          rw [h3]
          simp [shift, sub_eq_add_neg, add_assoc, add_left_comm]
          ring
        _ = shift s := by
          have hh := sub_eq_iff_eq_add.mp hs
          simpa [add_comm] using hh.symm
    have hc := index_injective he
    dsimp [slopeShift]
    have h3' : BandVectors.2 (q (2 : Fin 3).succ) (q 0) =
        -BandVectors.2 (q 1) (q 0) - BandVectors.2 (q 2) (q 0) := by
      have hsum' := IncomingSuperbasisRelation q hq
      have finthree : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
      have expanded : BandVectors.2 (q 1) (q 0) +
          (BandVectors.2 (q 2) (q 0) + BandVectors.2 (q (Fin.succ (2 : Fin 3))) (q 0)) = 0 := by
        simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, zero_add,
          Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, finthree] using hsum'.2
      linear_combination expanded
    have finthree : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
    rw [← finthree, h3']
    rw [← hc]
    push_cast
    ring

private theorem hidx :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (lattice_coords : ∀ kl : Int × Int, shift kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        (Function.Injective index) → (∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), (¬kl = mn) → (index kl ≠
            index mn)) ) := by
  classical
  intro C q shift lattice_coords index index_injective kl mn hkm he
  exact hkm (index_injective he)

private theorem hdom :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), (TileOdometer C.1.1 T h) → ((0 < C.1.1.1) → (
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        let H (kl : Int × Int) : PartialOdometer :=
          PartialOdometerAffineTranslate h (shift kl) (slopeShift kl) 0
        ∀ r : Int × Int, (H r).domain = FootprintVertices (TileTranslation T (shift r)))) ) := by
  classical
  intro C q T h hO hpos shift slopeShift H r
  exact PositiveCurvatureTileOdometerDomain C.1.1
    (TileTranslation T (shift r)) (H r) hpos
    (TileOdometerAffineTranslation C.1.1 T h (shift r)
      (slopeShift r) 0 hO)

private theorem hedgeP :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile),
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), (∀ (u : ↥(TilingLattice C)), P.tile u =
            TileTranslation T (↑u : GaussianInt)) → (∀ (lattice_coords : ∀ kl : Int × Int, shift
            kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ((FootprintEdges (TileTranslation T (shift kl)) ∩
            FootprintEdges (TileTranslation T (shift mn))).Nonempty) → ((FootprintEdges (P.tile
            (index kl)) ∩ FootprintEdges (P.tile (index mn))).Nonempty)) ) := by
  classical
  intro C q T shift P htile lattice_coords index kl mn hedge
  simpa [htile, index] using hedge

private theorem hr'At341 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (lattice_coords : ∀ kl : Int × Int, shift kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), (((↑(index mn) : GaussianInt) -
            (↑(index kl) : GaussianInt)).re = (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ)))).re) → (((shift mn).re : ℝ) - (shift kl).re = ((BandVectors.1 (q i.succ) (q
            0)).re : ℝ)) ) := by
  classical
  intro C q shift lattice_coords index kl mn i hr
  exact_mod_cast hr

private theorem hi'At344 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (lattice_coords : ∀ kl : Int × Int, shift kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), (((↑(index mn) : GaussianInt) -
            (↑(index kl) : GaussianInt)).im = (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ)))).im) → (((shift mn).im : ℝ) - (shift kl).im = ((BandVectors.1 (q i.succ) (q
            0)).im : ℝ)) ) := by
  classical
  intro C q shift lattice_coords index kl mn i hi
  exact_mod_cast hi

private theorem hr'At361 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), ((slopeShift mn - slopeShift kl).re
            = (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).re) → (((slopeShift mn).re : ℝ) -
            (slopeShift kl).re = ((BandVectors.2 (q i.succ) (q 0)).re : ℝ)) ) := by
  classical
  intro q slopeShift kl mn i hr
  exact_mod_cast hr

private theorem hi'At370 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), ((slopeShift mn - slopeShift kl).im
            = (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).im) → (((slopeShift mn).im : ℝ) -
            (slopeShift kl).im = ((BandVectors.2 (q i.succ) (q 0)).im : ℝ)) ) := by
  classical
  intro q slopeShift kl mn i hi
  exact_mod_cast hi

private theorem hstep'' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (lattice_coords : ∀ kl : Int × Int, shift kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), ((↑(index mn) : GaussianInt) -
            (↑(index kl) : GaussianInt) = -BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) →
            (shift mn - shift kl = -BandVectors.1 (q i.succ) (q 0)) ) := by
  classical
  intro C q shift lattice_coords index kl mn i hstep
  simpa [index] using hstep

private theorem hr'At406 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), ((shift mn - shift kl).re =
            (-BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).re) → (((shift mn).re : ℝ) - (shift
            kl).re = ((-BandVectors.1 (q i.succ) (q 0)).re : ℝ)) ) := by
  classical
  intro q shift kl mn i hr
  exact_mod_cast hr

private theorem hi'At416 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), ((shift mn - shift kl).im =
            (-BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).im) → (((shift mn).im : ℝ) - (shift
            kl).im = ((-BandVectors.1 (q i.succ) (q 0)).im : ℝ)) ) := by
  classical
  intro q shift kl mn i hi
  exact_mod_cast hi

private theorem hslope'At428 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), (slopeShift kl - slopeShift mn =
            BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))) → (slopeShift mn - slopeShift kl =
            -BandVectors.2 (q i.succ) (q 0)) ) := by
  classical
  intro q slopeShift kl mn i hslope
  rw [← hslope]
  ring

private theorem hr'At433 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), ((slopeShift mn - slopeShift kl).re
            = (-BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).re) → (((slopeShift mn).re : ℝ) -
            (slopeShift kl).re = ((-BandVectors.2 (q i.succ) (q 0)).re : ℝ)) ) := by
  classical
  intro q slopeShift kl mn i hr
  exact_mod_cast hr

private theorem hi'At448 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        ∀ (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), ∀ (i : Fin (3 : ℕ)), ((slopeShift mn - slopeShift kl).im
            = (-BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).im) → (((slopeShift mn).im : ℝ) -
            (slopeShift kl).im = ((-BandVectors.2 (q i.succ) (q 0)).im : ℝ)) ) := by
  classical
  intro q slopeShift kl mn i hi
  exact_mod_cast hi

end PositiveTranslationGeometry

namespace PositiveAdjacentCompatibility

private theorem adjacentCompatibility :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (q (0 : Fin (4 : ℕ)) =
            C.1.1) → ((ProperBandQuadruple q) → (∀ (T : ProtoTile), ∀ (h : PartialOdometer),
            (TileOdometer C.1.1 T h) → (
        let shift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        let slopeShift (kl : Int × Int) : GaussianInt :=
          (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
            (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        let H (kl : Int × Int) : PartialOdometer :=
          PartialOdometerAffineTranslate h (shift kl) (slopeShift kl) 0
        (∃ p : ℝ × ℝ, PartialOdometerSlope h = some p) → (∀ (P : PeriodicTileComplex
            ↥(TilingLattice C)), (∀ (u : ↥(TilingLattice C)), P.tile u = TileTranslation T (↑u :
            GaussianInt)) → ((∀ (u : ↥(TilingLattice C)), ∀ (v : ↥(TilingLattice C)),
            P.plane.adjacent u v ↔ ∃ (j : Fin (3 : ℕ)), (↑v : GaussianInt) - (↑u : GaussianInt) =
            BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∨ (↑v : GaussianInt) - (↑u :
            GaussianInt) = -BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ)))) → (∀ (lattice_coords
            : ∀ kl : Int × Int, shift kl ∈ TilingLattice C),
        let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
        (∀ (r : Int × Int), ∀ (s : Int × Int), ∀ (i : Fin 3), shift s - shift r = BandVectors.1
            (q i.succ) (q 0) → slopeShift s - slopeShift r = BandVectors.2 (q i.succ) (q 0)) → (∀
            (kl : ℤ × ℤ), ∀ (mn : ℤ × ℤ), (((FootprintEdges (P.tile (index kl)) ∩ FootprintEdges
            (P.tile (index mn))).Nonempty ↔ P.plane.adjacent (index kl) (index mn)) ∧
            ((FootprintEdges (P.tile (index kl)) ∩ FootprintEdges (P.tile (index mn))).Nonempty →
            SimpleGridPath (CommonFootprintEdgeVertices (P.tile (index kl)) (P.tile (index mn)))
            (FootprintEdges (P.tile (index kl)) ∩ FootprintEdges (P.tile (index mn))) ∧
            FootprintVertices (P.tile (index kl)) ∩ FootprintVertices (P.tile (index mn)) =
            CommonFootprintEdgeVertices (P.tile (index kl)) (P.tile (index mn))) ∧
            (¬(FootprintEdges (P.tile (index kl)) ∩ FootprintEdges (P.tile (index mn))).Nonempty
            → FootprintVertices (P.tile (index kl)) ∩ FootprintVertices (P.tile (index mn)) = ∅ ∨
            (FootprintVertices (P.tile (index kl)) ∩ FootprintVertices (P.tile (index
            mn))).Subsingleton)) → (((FootprintEdges (TileTranslation T (shift kl)) ∩
            FootprintEdges (TileTranslation T (shift mn))).Nonempty) → (OdometerCompatibility (H
            kl) (H mn)))))))))) ) := by
  classical
  intro C q hqC hq T h hO shift slopeShift H slope_exists P htile hadj lattice_coords index
      slope_step kl mn hclass hedge
  have hedgeP : (FootprintEdges (P.tile (index kl)) ∩
      FootprintEdges (P.tile (index mn))).Nonempty := PositiveTranslationGeometry.hedgeP
          C q T P htile lattice_coords kl mn hedge
  have hadj' := hclass.1.mp hedgeP
  have hstep := (hadj (index kl) (index mn)).mp hadj'
  rcases hstep with ⟨i, hstep | hstep⟩
  · have hOkl := TileOdometerAffineTranslation C.1.1 T h (shift kl)
      (slopeShift kl) 0 hO
    have hOmn := TileOdometerAffineTranslation C.1.1 T h (shift mn)
      (slopeShift mn) 0 hO
    apply (LeftAdjacentOdometerCompatibility C
      (TileTranslation T (shift kl)) (TileTranslation T (shift mn))
      (H kl) (H mn) ?_).1
    refine ⟨hOkl, hOmn, ?_⟩
    rcases slope_exists with ⟨p, hp⟩
    refine ⟨(p.1 + (slopeShift kl).re, p.2 + (slopeShift kl).im),
      (p.1 + (slopeShift mn).re, p.2 + (slopeShift mn).im), ?_, ?_, ?_⟩
    · rw [PartialOdometerAffineTranslateFormulas h (shift kl)
          (slopeShift kl) 0 |>.2.2.2.2.2, hp]
      simp
    · rw [PartialOdometerAffineTranslateFormulas h (shift mn)
          (slopeShift mn) 0 |>.2.2.2.2.2, hp]
      simp
    · refine Or.inr ⟨q, i, true, hq, ?_, ?_, ?_, ?_⟩
      · exact hqC
      · have hc1 := (TileTranslationFormulas T (shift kl)).2.2.2.2.1
        have hc2 := (TileTranslationFormulas T (shift mn)).2.2.2.2.1
        rw [hc2, hc1]
        simp only [ite_true]
        have hr := congrArg (fun z : GaussianInt => z.re) hstep
        have hi := congrArg (fun z : GaussianInt => z.im) hstep
        have hr' : ((shift mn).re : ℝ) - (shift kl).re =
            ((BandVectors.1 (q i.succ) (q 0)).re : ℝ) :=
                PositiveTranslationGeometry.hr'At341 C q lattice_coords kl mn i hr
        have hi' : ((shift mn).im : ℝ) - (shift kl).im =
            ((BandVectors.1 (q i.succ) (q 0)).im : ℝ) :=
                PositiveTranslationGeometry.hi'At344 C q lattice_coords kl mn i hi
        apply Prod.ext
        · simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
            Prod.mk_sub_mk, add_sub_add_left_eq_sub, GaussianRealPoint, Fin.isValue, one_smul]
          rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_re,
            ← GaussianInt.intCast_re]
          linarith
        · simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
            Prod.mk_sub_mk, add_sub_add_left_eq_sub, GaussianRealPoint, Fin.isValue, one_smul]
          rw [← GaussianInt.intCast_im, ← GaussianInt.intCast_im,
            ← GaussianInt.intCast_im]
          linarith
      · simp only [Int.reduceNeg, GaussianInt.intCast_re, add_sub_add_left_eq_sub, ↓reduceIte,
          Fin.isValue, one_mul]
        rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_re,
          ← GaussianInt.intCast_re]
        have hslope := slope_step kl mn i hstep
        have hr := congrArg (fun z : GaussianInt => z.re) hslope
        have hr' : ((slopeShift mn).re : ℝ) - (slopeShift kl).re =
            ((BandVectors.2 (q i.succ) (q 0)).re : ℝ) :=
                PositiveTranslationGeometry.hr'At361 q kl mn i hr
        linarith
      · simp only [Int.reduceNeg, GaussianInt.intCast_im, add_sub_add_left_eq_sub, ↓reduceIte,
          Fin.isValue, one_mul]
        rw [← GaussianInt.intCast_im, ← GaussianInt.intCast_im,
          ← GaussianInt.intCast_im]
        have hslope := slope_step kl mn i hstep
        have hi := congrArg (fun z : GaussianInt => z.im) hslope
        have hi' : ((slopeShift mn).im : ℝ) - (slopeShift kl).im =
            ((BandVectors.2 (q i.succ) (q 0)).im : ℝ) :=
                PositiveTranslationGeometry.hi'At370 q kl mn i hi
        linarith
  · have hstep' : shift kl - shift mn = BandVectors.1 (q i.succ) (q 0) := by
      simpa using congrArg Neg.neg hstep
    have hOkl := TileOdometerAffineTranslation C.1.1 T h (shift kl)
      (slopeShift kl) 0 hO
    have hOmn := TileOdometerAffineTranslation C.1.1 T h (shift mn)
      (slopeShift mn) 0 hO
    apply (LeftAdjacentOdometerCompatibility C
      (TileTranslation T (shift kl)) (TileTranslation T (shift mn))
      (H kl) (H mn) ?_).1
    refine ⟨hOkl, hOmn, ?_⟩
    rcases slope_exists with ⟨p, hp⟩
    refine ⟨(p.1 + (slopeShift kl).re, p.2 + (slopeShift kl).im),
      (p.1 + (slopeShift mn).re, p.2 + (slopeShift mn).im), ?_, ?_, ?_⟩
    · rw [PartialOdometerAffineTranslateFormulas h (shift kl)
          (slopeShift kl) 0 |>.2.2.2.2.2, hp]
      simp
    · rw [PartialOdometerAffineTranslateFormulas h (shift mn)
          (slopeShift mn) 0 |>.2.2.2.2.2, hp]
      simp
    · refine Or.inr ⟨q, i, false, hq, hqC, ?_, ?_, ?_⟩
      · have hc1 := (TileTranslationFormulas T (shift kl)).2.2.2.2.1
        have hc2 := (TileTranslationFormulas T (shift mn)).2.2.2.2.1
        rw [hc2, hc1]
        have hstep'' : shift mn - shift kl =
            -BandVectors.1 (q i.succ) (q 0) := PositiveTranslationGeometry.hstep'' C q
                lattice_coords kl mn i hstep
        have hr := congrArg (fun z : GaussianInt => z.re) hstep''
        have hi := congrArg (fun z : GaussianInt => z.im) hstep''
        apply Prod.ext
        · simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
            Prod.mk_sub_mk, add_sub_add_left_eq_sub, Bool.false_eq_true, ↓reduceIte,
            GaussianRealPoint, Fin.isValue, neg_smul, one_smul, Prod.neg_mk]
          rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_re,
            ← GaussianInt.intCast_re]
          have hr' : ((shift mn).re : ℝ) - (shift kl).re =
              ((-BandVectors.1 (q i.succ) (q 0)).re : ℝ) :=
                  PositiveTranslationGeometry.hr'At406 q kl mn i hr
          norm_num at hr'
          rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_re,
            ← GaussianInt.intCast_re] at hr'
          linarith
        · simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
            Prod.mk_sub_mk, add_sub_add_left_eq_sub, Bool.false_eq_true, ↓reduceIte,
            GaussianRealPoint, Fin.isValue, neg_smul, one_smul, Prod.neg_mk]
          rw [← GaussianInt.intCast_im, ← GaussianInt.intCast_im,
            ← GaussianInt.intCast_im]
          have hi' : ((shift mn).im : ℝ) - (shift kl).im =
              ((-BandVectors.1 (q i.succ) (q 0)).im : ℝ) :=
                  PositiveTranslationGeometry.hi'At416 q kl mn i hi
          norm_num at hi'
          rw [← GaussianInt.intCast_im, ← GaussianInt.intCast_im,
            ← GaussianInt.intCast_im] at hi'
          linarith
      · simp only []
        change (p.1 + (slopeShift mn).re -
          (p.1 + (slopeShift kl).re) : ℝ) =
          -1 * (BandVectors.2 (q i.succ) (q 0)).re
        have hslope := slope_step mn kl i hstep'
        have hslope' : slopeShift mn - slopeShift kl =
            -BandVectors.2 (q i.succ) (q 0) := PositiveTranslationGeometry.hslope'At428 q
                kl mn i hslope
        have hr := congrArg (fun z : GaussianInt => z.re) hslope'
        have hr' : ((slopeShift mn).re : ℝ) - (slopeShift kl).re =
            ((-BandVectors.2 (q i.succ) (q 0)).re : ℝ) :=
                PositiveTranslationGeometry.hr'At433 q kl mn i hr
        norm_num at hr' ⊢
        linarith
      · simp only []
        change (p.2 + (slopeShift mn).im -
          (p.2 + (slopeShift kl).im) : ℝ) =
          -1 * (BandVectors.2 (q i.succ) (q 0)).im
        have hslope := slope_step mn kl i hstep'
        have hslope' : slopeShift mn - slopeShift kl =
            -BandVectors.2 (q i.succ) (q 0) := PositiveTranslationGeometry.hslope'At428 q
                kl mn i hslope
        have hi := congrArg (fun z : GaussianInt => z.im) hslope'
        have hi' : ((slopeShift mn).im : ℝ) - (slopeShift kl).im =
            ((-BandVectors.2 (q i.succ) (q 0)).im : ℝ) :=
                PositiveTranslationGeometry.hi'At448 q kl mn i hi
        norm_num at hi' ⊢
        linarith

end PositiveAdjacentCompatibility

theorem PositiveCurvatureTranslatedOdometers (C : BandCircle)
    (hc : 1 < C.1.1.1) :
    ∃ (q : Fin 4 → CircleCoordinates) (T : ProtoTile) (h : PartialOdometer)
        (H : Int × Int → PartialOdometer),
      ProperBandQuadruple q ∧ q 0 = C.1.1 ∧
      BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h ∧
      (∀ kl,
        let w := (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
        let a := (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
          (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
        TileOdometer C.1.1 (TileTranslation T w) (H kl) ∧
        (∀ x, x ∈ (H kl).domain ↔ x - w ∈ h.domain) ∧
        ∀ x, x ∈ (H kl).domain →
          (H kl).value x = h.value (x - w) + a.re * x.re + a.im * x.im) ∧
      ∀ kl mn, OdometerCompatibility (H kl) (H mn) := by
-- BODY
  rcases BandGenealogy C with hunit | ⟨q, hqsemi, hqC, hless, huniq⟩
  · omega
  · have hq : ProperBandQuadruple q := ⟨hqsemi, by simpa [hqC] using hless⟩
    rcases TileOdometerExists C with ⟨T, h, hT, hO⟩
    have hpos : 0 < C.1.1.1 := by omega
    let shift (kl : Int × Int) : GaussianInt :=
      (kl.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
        (kl.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)
    let slopeShift (kl : Int × Int) : GaussianInt :=
      (kl.1 : GaussianInt) * BandVectors.2 (q 1) (q 0) +
        (kl.2 : GaussianInt) * BandVectors.2 (q 2) (q 0)
    let H (kl : Int × Int) : PartialOdometer :=
      PartialOdometerAffineTranslate h (shift kl) (slopeShift kl) 0
    have slope_for : ∀ (c : CircleCoordinates) (U : ProtoTile)
        (k : PartialOdometer), TileOdometer c U k → 1 < c.1 →
        ∃ p : ℝ × ℝ, PartialOdometerSlope k = some p := PositiveTranslationGeometry.slope_for
    have slope_exists : ∃ p : ℝ × ℝ, PartialOdometerSlope h = some p :=
      slope_for C.1.1 T h hO (by omega)
    obtain ⟨P, hPl, htile, hadj, hposition, hvcard, hecard, hfcard, hchart⟩ :=
      BandRegularTranslatePeriodicComplex C q hq hqC T (by simpa [hqC] using hT)
    have lattice_coords : ∀ kl : Int × Int, shift kl ∈ TilingLattice C :=
        PositiveTranslationGeometry.lattice_coords C q hqC hq
    let index (kl : Int × Int) : TilingLattice C := ⟨shift kl, lattice_coords kl⟩
    have index_injective : Function.Injective index :=
        PositiveTranslationGeometry.index_injective C q hqC hq lattice_coords
    have slope_step : ∀ (r s : Int × Int) (i : Fin 3),
        shift s - shift r = BandVectors.1 (q i.succ) (q 0) →
        slopeShift s - slopeShift r = BandVectors.2 (q i.succ) (q 0) :=
            PositiveTranslationGeometry.slope_step C q hq lattice_coords index_injective
    refine ⟨q, T, h, H, hq, hqC, hT, hO, ?_, ?_⟩
    · intro kl
      refine ⟨?_, ?_, ?_⟩
      · exact TileOdometerAffineTranslation C.1.1 T h (shift kl)
          (slopeShift kl) 0 hO
      · intro x
        exact (PartialOdometerAffineTranslateFormulas h (shift kl)
          (slopeShift kl) 0).2.1 x
      · intro x hx
        simpa [H, shift, slopeShift] using (PartialOdometerAffineTranslateFormulas h
          (shift kl) (slopeShift kl) 0).2.2.1 x hx
    · intro kl mn
      by_cases hkm : kl = mn
      · subst mn
        right
        refine ⟨0, ?_⟩
        intro x hx hx'
        simp
      · have hidx : index kl ≠ index mn := PositiveTranslationGeometry.hidx C q lattice_coords
          index_injective kl mn hkm
        have hdom : ∀ r : Int × Int,
            (H r).domain = FootprintVertices (TileTranslation T (shift r)) :=
                PositiveTranslationGeometry.hdom C q T h hO hpos
        have hclass := (PeriodicTileIntersectionClassification P).1
          (index kl) (index mn) hidx
        have hclass' := hclass.2.2
        rw [htile (index kl), htile (index mn)] at hclass'
        change ¬(FootprintEdges (TileTranslation T (shift kl)) ∩
            FootprintEdges (TileTranslation T (shift mn))).Nonempty → _ at hclass'
        by_cases hedge : (FootprintEdges (TileTranslation T (shift kl)) ∩
            FootprintEdges (TileTranslation T (shift mn))).Nonempty
        · have adjacentCompatibility : OdometerCompatibility (H kl) (H mn) :=
            PositiveAdjacentCompatibility.adjacentCompatibility C q hqC hq T h hO slope_exists P
            htile hadj lattice_coords slope_step kl mn hclass hedge
          exact adjacentCompatibility
        · rcases hclass' hedge with hempty | hsingle
          · left
            apply Set.disjoint_left.2
            intro x hx hy
            have hxv := (hdom kl).symm ▸ hx
            have hyv := (hdom mn).symm ▸ hy
            have : x ∈ (∅ : Set GaussianInt) := by rw [← hempty]; exact ⟨hxv, hyv⟩
            exact this.elim
          · by_cases hne : ∃ x, x ∈ (H kl).domain ∧ x ∈ (H mn).domain
            · rcases hne with ⟨x₀, hx₀, hy₀⟩
              right
              refine ⟨(H mn).value x₀ - (H kl).value x₀, ?_⟩
              intro x hx hy
              have hxv : x ∈ FootprintVertices (TileTranslation T (shift kl)) :=
                (hdom kl).symm ▸ hx
              have hyv : x ∈ FootprintVertices (TileTranslation T (shift mn)) :=
                (hdom mn).symm ▸ hy
              have heq : x = x₀ := hsingle ⟨hxv, hyv⟩ ⟨
                (hdom kl).symm ▸ hx₀, (hdom mn).symm ▸ hy₀⟩
              subst x
              rfl
            · left
              apply Set.disjoint_left.2
              intro x hx hy
              exact hne ⟨x, hx, hy⟩

end ApollonianSuperharmonic

end

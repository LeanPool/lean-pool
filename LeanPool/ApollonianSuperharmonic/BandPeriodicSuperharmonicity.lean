/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.CircleMatrixSymmetry

public import LeanPool.ApollonianSuperharmonic.BandOdometerInteriorTable
public import LeanPool.ApollonianSuperharmonic.BandTileTopologyApplication
public import LeanPool.ApollonianSuperharmonic.PeriodicBoundaryWebLaplacian

-- [TABLET NODE: BandPeriodicSuperharmonicity]

/-!
# BandPeriodicSuperharmonicity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PeriodicSuperharmonicGeometry

private theorem hRne :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (R : Finset GaussianInt), (LatticeFundamentalSet (TilingLattice C)
            R) → (R.Nonempty) ) := by
  classical
  intro C R hR
  obtain ⟨r, hr, hv⟩ := hR 0
  exact ⟨r, hr.1⟩

private theorem hvals :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ), ∀ (R : Finset
            GaussianInt), (R.Nonempty) → (
        let vals : Finset ℝ := R.image (fun r => |(g r : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) r -
            (b.1 * r.re + b.2 * r.im)|)
        vals.Nonempty) ) := by
  classical
  intro C g b R hRne vals
  obtain ⟨r, hr⟩ := hRne
  exact ⟨_, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩

private theorem hF :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ), ∀ (x : GaussianInt), ∀
            (r : GaussianInt), ((↑(g (r + (x - r))) : ℝ) - LatticeQuadraticForm (CircleMatrix C)
            (r + (x - r)) - (b.1 * (↑(r + (x - r)).re : ℝ) + b.2 * (↑(r + (x - r)).im : ℝ)) =
            (↑(g r) : ℝ) - LatticeQuadraticForm (CircleMatrix C) r - (b.1 * (↑r.re : ℝ) + b.2 *
            (↑r.im : ℝ))) → ((g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x - (b.1 * x.re +
            b.2 * x.im) = (g r : ℝ) - LatticeQuadraticForm (CircleMatrix C) r - (b.1 * r.re + b.2
            * r.im)) ) := by
  classical
  intro C g b x r hrem
  convert hrem using 1; simp [sub_eq_add_neg, add_assoc]

private theorem hM :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ), ∀ (R : Finset
            GaussianInt),
        let vals : Finset ℝ := R.image (fun r => |(g r : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) r -
            (b.1 * r.re + b.2 * r.im)|)
        ∀ (hvals : vals.Nonempty),
        let M : ℝ := vals.sup' hvals id
        ∀ (x : GaussianInt), ∀ (r : GaussianInt), (r ∈ R ∧ x - r ∈ TilingLattice C) → (|(g r : ℝ)
            - LatticeQuadraticForm (CircleMatrix C) r - (b.1 * r.re + b.2 * r.im)| ≤ M) ) := by
  classical
  intro C g b R vals hvals M x r hr
  dsimp [M, vals]
  exact Finset.le_sup' (id : ℝ → ℝ)
    (show |(g r : ℝ) - LatticeQuadraticForm (CircleMatrix C) r -
      (b.1 * r.re + b.2 * r.im)| ∈ vals from
      Finset.mem_image.mpr ⟨r, hr.1, rfl⟩)

private theorem hcross :
    (by
      classical
      exact
        ∀ (b : ℝ × ℝ), ∀ (ε : ℝ), ((0 : ℝ) < ε) → (∀ (x : GaussianInt), |b.1 * x.re + b.2 * x.im|
            ≤ ε / 4 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) + (b.1^2 + b.2^2) / ε) ) := by
  classical
  intro b ε hε x
  have ha : |b.1 * (x.re : ℝ)| ≤ ε / 4 * (x.re : ℝ)^2 + |b.1|^2 / ε := by
    have heq : ε / 4 * (x.re : ℝ)^2 + |b.1|^2 / ε =
        (ε^2 * (x.re : ℝ)^2 / 4 + |b.1|^2) / ε := by field_simp
    rw [heq]
    apply (le_div_iff₀ hε).2
    rw [abs_mul]
    have hs := sq_nonneg (ε * |(x.re : ℝ)| - 2 * |b.1|)
    nlinarith [sq_abs (x.re : ℝ), sq_abs b.1]
  have hb' : |b.2 * (x.im : ℝ)| ≤ ε / 4 * (x.im : ℝ)^2 + |b.2|^2 / ε := by
    have heq : ε / 4 * (x.im : ℝ)^2 + |b.2|^2 / ε =
        (ε^2 * (x.im : ℝ)^2 / 4 + |b.2|^2) / ε := by field_simp
    rw [heq]
    apply (le_div_iff₀ hε).2
    rw [abs_mul]
    have hs := sq_nonneg (ε * |(x.im : ℝ)| - 2 * |b.2|)
    nlinarith [sq_abs (x.im : ℝ), sq_abs b.2]
  calc
    |b.1 * x.re + b.2 * x.im| ≤ |b.1 * x.re| + |b.2 * x.im| := abs_add_le _ _
    _ ≤ (ε / 4 * (x.re : ℝ)^2 + |b.1|^2 / ε) +
      (ε / 4 * (x.im : ℝ)^2 + |b.2|^2 / ε) := add_le_add ha hb'
    _ = ε / 4 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) +
        (b.1^2 + b.2^2) / ε := by
          rw [sq_abs, sq_abs]
          field_simp [ne_of_gt hε]
          ring

private theorem hbase :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ), ∀ (R : Finset
            GaussianInt),
        let vals : Finset ℝ := R.image (fun r => |(g r : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) r -
            (b.1 * r.re + b.2 * r.im)|)
        ∀ (hvals : vals.Nonempty),
        let M : ℝ := vals.sup' hvals id
        ∀ (ε : ℝ), ((0 : ℝ) < ε) → (
        let K : ℝ := M + (b.1 ^ 2 + b.2 ^ 2) / ε
        ∀ (x : GaussianInt), ∀ (r : GaussianInt), ((g x : ℝ) - LatticeQuadraticForm (CircleMatrix
            C) x - (b.1 * x.re + b.2 * x.im) = (g r : ℝ) - LatticeQuadraticForm (CircleMatrix C)
            r - (b.1 * r.re + b.2 * r.im)) → ((|(g r : ℝ) - LatticeQuadraticForm (CircleMatrix C)
            r - (b.1 * r.re + b.2 * r.im)| ≤ M) → ((|b.1 * x.re + b.2 * x.im| ≤ ε / 4 * ((x.re :
            ℝ)^2 + (x.im : ℝ)^2) + (b.1^2 + b.2^2) / ε) → (|(g x : ℝ) - LatticeQuadraticForm
            (CircleMatrix C) x| ≤ ε / 2 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) + K)))) ) := by
  classical
  intro C g b R vals hvals M ε hε K x r hF hM hcross
  calc
    |↑(g x) - LatticeQuadraticForm (CircleMatrix C) x| =
        |(↑(g x) - LatticeQuadraticForm (CircleMatrix C) x -
          (b.1 * x.re + b.2 * x.im)) + (b.1 * x.re + b.2 * x.im)| := by
            congr 1
            ring
    _ ≤ |↑(g x) - LatticeQuadraticForm (CircleMatrix C) x -
          (b.1 * x.re + b.2 * x.im)| + |b.1 * x.re + b.2 * x.im| := abs_add_le _ _
    _ = |↑(g r) - LatticeQuadraticForm (CircleMatrix C) r -
          (b.1 * r.re + b.2 * r.im)| + |b.1 * x.re + b.2 * x.im| := by rw [hF]
    _ ≤ M + (ε / 2 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) +
          (b.1^2 + b.2^2) / ε) := by
            apply le_trans (add_le_add hM hcross)
            have hs : 0 ≤ ε / 4 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) := by positivity
            nlinarith [hs]
    _ = ε / 2 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) + K := by dsimp [K]; ring

private theorem hK :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ), ∀ (R : Finset
            GaussianInt),
        let vals : Finset ℝ := R.image (fun r => |(g r : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) r -
            (b.1 * r.re + b.2 * r.im)|)
        ∀ (hvals : vals.Nonempty),
        let M : ℝ := vals.sup' hvals id
        ∀ (ε : ℝ), ((0 : ℝ) < ε) → (
        let K : ℝ := M + (b.1 ^ 2 + b.2 ^ 2) / ε
        ∀ (x : GaussianInt), ((2 : ℝ) * K / ε ≤ (↑x.re : ℝ) ^ (2 : ℕ) + (↑x.im : ℝ) ^ (2 : ℕ)) →
            (K ≤ ε / 2 * ((x.re : ℝ)^2 + (x.im : ℝ)^2))) ) := by
  classical
  intro C g b R vals hvals M ε hε K x hx
  have hx' := (div_le_iff₀ hε).mp hx
  dsimp [K]
  nlinarith

private theorem local_bound :
    (by
      classical
      exact
        ∀ (g : IntegerLatticeFunction), (∀ (c : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k :
            PartialOdometer), TileOdometer c U k → BandPrototile c U) → (∀ (c :
            CircleCoordinates), ∀ (U : ProtoTile), ∀ (k : PartialOdometer), TileOdometer c U k →
            GlobalOdometerExtends g k → ∀ y, y ∈ FootprintVertices U → y ∉
            BoundaryFootprintVertices U → FourNeighborLaplacian g y ≤ 1) ) := by
  classical
  intro g tile_band c U k ho
  induction ho with
  | line w z hw k hd =>
      intro hg y hy hny
      exact (hny hy).elim
  | unit z x U k hU hd ht =>
      intro hglob y hy hny
      have hu : U.cells.Nonempty := by rw [hU]; simp
      rw [FootprintVertices, ite_eq_left hu, hU] at hy
      simp only [Set.mem_ofPred_eq, Finset.mem_singleton] at hy
      rcases hy with ⟨w, ⟨hw, hy⟩⟩
      subst w
      have hne : (⟨0, 1⟩ : GaussianInt) ≠ 0 := by
        intro hh
        have hm := congrArg (fun q : GaussianInt => q.im) hh
        norm_num at hm
      rcases hy with hy | hy | hy | hy
      · exfalso
        apply hny
        simp only [BoundaryFootprintVertices, ite_eq_left hu, Set.mem_ofPred_eq]
        refine ⟨{x, x + 1}, ?_, by simp [hy]⟩
        change ∃ z, _
        refine ⟨x, ?_⟩
        simp [hU, hne]
      · exfalso
        apply hny
        simp only [BoundaryFootprintVertices, ite_eq_left hu, Set.mem_ofPred_eq]
        refine ⟨{x, x + 1}, ?_, by simp [hy]⟩
        change ∃ z, _
        refine ⟨x, ?_⟩
        simp [hU, hne]
      · exfalso
        apply hny
        simp only [BoundaryFootprintVertices, ite_eq_left hu, Set.mem_ofPred_eq]
        refine ⟨{x, x + ⟨0, 1⟩}, ?_, by simp [hy]⟩
        change ∃ z, _
        refine ⟨x, ?_⟩
        simp [hU]
      · exfalso
        apply hny
        simp only [BoundaryFootprintVertices, ite_eq_left hu, Set.mem_ofPred_eq]
        refine ⟨{x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩}, ?_, by simp [hy]⟩
        change ∃ z, _
        refine ⟨x + ⟨0, 1⟩, ?_⟩
        simp [hU, add_assoc, add_comm, add_left_comm, hne]
  | @decompose q hq S U hs k hU hsub hc hf hcent hd hv hcomp hsl ih =>
      intro hglob y hy hny
      obtain ⟨cc, hcc⟩ := hglob
      have root_ext : GlobalOdometerExtends g k := ⟨cc, hcc⟩
      have child_ext (i : Fin 3) (s : Bool) :
          GlobalOdometerExtends g (hs i s) := by
        refine ⟨cc, ?_⟩
        intro t ht
        have ht' : t ∈ k.domain := (hd t).2 ⟨i, s, ht⟩
        have hv' := hv i s t ht
        rw [hcc t ht', hv']
      have root_band : BandPrototile (q 0) U :=
        BandPrototile.decompose hq (fun i s => tile_band _ _ _ (hsub i s)) hc hf hcent
      have root_odo : TileOdometer (q 0) U k :=
        TileOdometer.decompose hq hU hsub hc hf hcent hd hv hcomp hsl
      have occur (i : Fin 3) (s : Bool) : BandSubtileOccurrence q U i s (S i s) :=
        ⟨tile_band _ _ _ (hsub i s), hf i s, hcent i s⟩
      have table := BandOdometerInteriorTable q hq U S k hs g root_band
        root_odo root_ext
        (by intro i s; exact occur i s) hc
        (by intro i s; exact hsub i s)
        (by intro i s; exact child_ext i s) y hy hny
      dsimp at table
      rcases table with ⟨h2, h2c, h3, h4, h4c, hlast⟩
      let n : Nat := Nat.card {is : Fin 3 × Bool //
        y ∈ BoundaryFootprintVertices (S is.1 is.2)}
      by_cases hn2 : n = 2
      · by_cases hcxy : GaussianRealPoint y = TileCentroid U
        · rw [h2c hn2 hcxy]; omega
        · rw [h2 hn2 hcxy]
      by_cases hn3 : n = 3
      · rw [h3 hn3]; omega
      by_cases hn4 : n = 4
      · by_cases hcxy : GaussianRealPoint y = TileCentroid U
        · have hh := h4c hn4 hcxy
          omega
        · have hh := h4 hn4 hcxy
          omega
      rcases hlast with hcases | ⟨i, s, hp, hys, hyn⟩
      · exfalso
        omega
      · exact ih i s (child_ext i s) y hys hyn

private theorem lap_periodic :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), (∀ v, v ∈ TilingLattice C → ∃ a :
            GaussianInt, Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] = ![(a.re : ℝ),
            (a.im : ℝ)] ∧ ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v) → (∀ v, v ∈
            TilingLattice C → ∀ y, FourNeighborLaplacian g (y + v) = FourNeighborLaplacian g y) )
            := by
  classical
  intro C g hcocycle v hv y
  obtain ⟨a, ha, hs⟩ := hcocycle v hv
  simp only [FourNeighborLaplacian]
  rw [show y + v + 1 = (y + 1) + v by abel,
    show y + v - 1 = (y - 1) + v by abel,
    show y + v + ⟨0, 1⟩ = (y + ⟨0, 1⟩) + v by abel,
    show y + v - ⟨0, 1⟩ = (y - ⟨0, 1⟩) + v by abel]
  rw [hs (y + 1), hs (y - 1), hs (y + ⟨0, 1⟩), hs (y - ⟨0, 1⟩), hs y]
  simp
  ring

private theorem hb :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (z0 : GaussianInt), ∀ (anchor : GaussianInt),
        let v : GaussianInt := x - z0
        let T0 : ProtoTile := ⟨{z0}, anchor⟩
        (BoundaryFootprintVertices (TileTranslation T0 v) = GaussianTranslation v ''
            BoundaryFootprintVertices T0) → (x ∈ BoundaryFootprintVertices (TileTranslation T0
            v)) ) := by
  classical
  intro x z0 anchor v T0 hvertices
  rw [hvertices]
  refine ⟨z0, ?_, ?_⟩
  · have hz : (⟨0, 1⟩ : GaussianInt) ≠ 0 := by
      intro hh
      have hm := congrArg (fun q : GaussianInt => q.im) hh
      norm_num at hm
    simp only [BoundaryFootprintVertices, ite_eq_left (show T0.cells.Nonempty by simp [T0]),
      Set.mem_ofPred_eq]
    refine ⟨{z0, z0 + 1}, ?_, by simp⟩
    change ∃ z, _
    refine ⟨z0, ?_⟩
    simp [T0, hz]
  · simp [v, GaussianTranslation, sub_eq_add_neg]

private theorem hT0 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (z : GaussianInt), ∀ (z0 : GaussianInt), ∀ (anchor : GaussianInt),
            (C.1.1 = ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z)) → (
        let T0 : ProtoTile := ⟨{z0}, anchor⟩
        BandPrototile C.1.1 T0) ) := by
  classical
  intro C z z0 anchor hc T0
  rw [hc]
  simpa [T0] using (BandPrototile.unit z z0 anchor)

private theorem hzAt394 :
    (by
      classical
      exact
        ∀ (C : BandCircle), (C.1.1.1 = (1 : ℤ)) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple q) → (((0 : ℤ) < (q (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)),
            (0 : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), (q i.succ).1 = (0
            : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) → ((q 0 = C.1.1) → (∀ (i : Fin 3), (q
            i.succ).1 = 0)))) ) := by
  classical
  intro C hr q hq hcurv hq0 i
  have hn := hcurv.2.1 i
  have hi := hq.2 i
  rw [hq0] at hi
  omega

private theorem hyfoot :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (y : LatticeCell), (y ∈ T.cells) → (y ∈ FootprintVertices T) ) := by
  classical
  intro T y hyT
  rw [FootprintVertices, ite_eq_left ⟨y, hyT⟩]
  exact ⟨y, hyT, Or.inl rfl⟩

private theorem hyboundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (v : GaussianInt), (BoundaryFootprintVertices
            (TileTranslation T v) = GaussianTranslation v '' BoundaryFootprintVertices T) → (∀ (y
            : LatticeCell), (y + v = x) → ((x ∉ BoundaryFootprintVertices (TileTranslation T v))
            → (y ∉ BoundaryFootprintVertices T))) ) := by
  classical
  intro T x v hboundaryform y hxy hboundary hyb
  apply hboundary
  rw [hboundaryform]
  exact ⟨y, hyb, hxy⟩

end PeriodicSuperharmonicGeometry

theorem BandPeriodicSuperharmonicity (C : BandCircle)
    (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hT : BandPrototile C.1.1 T) (hodo : TileOdometer C.1.1 T h)
    (hext : GlobalOdometerExtends g h)
    (hcocycle : ∀ v, v ∈ TilingLattice C → ∃ a : GaussianInt,
      Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
        ![(a.re : ℝ), (a.im : ℝ)] ∧
      ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v)
    (hremainder : ∃ b : ℝ × ℝ, ∀ v, v ∈ TilingLattice C → ∀ x,
      (g (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
          (b.1 * (x + v).re + b.2 * (x + v).im) =
        (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
          (b.1 * x.re + b.2 * x.im)) :
    IntegerSuperharmonicRepresentative (CircleMatrix C) g := by
-- BODY
  classical
  unfold IntegerSuperharmonicRepresentative
  refine ⟨(CircleMatrixSymmetry.symmetric C), ?_, ?_⟩
  · unfold QuadraticGrowthAtInfinity
    obtain ⟨b, hb⟩ := hremainder
    obtain ⟨R, hR, hcard⟩ := TilingLatticeIndex C
    have hRne : R.Nonempty := PeriodicSuperharmonicGeometry.hRne C R hR
    let vals : Finset ℝ := R.image (fun r => |(g r : ℝ) -
      LatticeQuadraticForm (CircleMatrix C) r -
        (b.1 * r.re + b.2 * r.im)|)
    have hvals : vals.Nonempty := PeriodicSuperharmonicGeometry.hvals C g b R hRne
    let M : ℝ := vals.sup' hvals id
    intro ε hε
    let K : ℝ := M + (b.1 ^ 2 + b.2 ^ 2) / ε
    refine ⟨2 * K / ε, ?_⟩
    intro x hx
    obtain ⟨r, hr, hv⟩ := hR x
    have hper : x - r ∈ TilingLattice C := hr.2
    have hrem := hb (x - r) hper r
    have hF : (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
        (b.1 * x.re + b.2 * x.im) =
        (g r : ℝ) - LatticeQuadraticForm (CircleMatrix C) r -
        (b.1 * r.re + b.2 * r.im) := PeriodicSuperharmonicGeometry.hF C g b x r hrem
    have hM : |(g r : ℝ) - LatticeQuadraticForm (CircleMatrix C) r -
        (b.1 * r.re + b.2 * r.im)| ≤ M := PeriodicSuperharmonicGeometry.hM C g b R hvals x r hr
    have hcross : |b.1 * x.re + b.2 * x.im| ≤
        ε / 4 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) +
        (b.1^2 + b.2^2) / ε := PeriodicSuperharmonicGeometry.hcross b ε hε x
    have hnon : 0 ≤ (x.re : ℝ)^2 + (x.im : ℝ)^2 := by positivity
    have hbase : |(g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x| ≤
        ε / 2 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) + K := PeriodicSuperharmonicGeometry.hbase C g b R
            hvals ε hε x r hF hM hcross
    have hK : K ≤ ε / 2 * ((x.re : ℝ)^2 + (x.im : ℝ)^2) := PeriodicSuperharmonicGeometry.hK C g b
        R hvals ε hε x hx
    nlinarith
  · intro x
    have hlocal := (PeriodicSuperharmonicGeometry.local_bound g
        (TileOdometerBandPrototile)) _ _ _ hodo hext
    have lap_periodic := PeriodicSuperharmonicGeometry.lap_periodic C g hcocycle
    by_cases hr : C.1.1.1 = 1
    · generalize hc : C.1.1 = c at hT hodo
      cases hT with
      | line w z hw =>
          have hz := congrArg Prod.fst hc
          simp at hz
          omega
      | unit z z0 anchor =>
          have hlat : TilingLattice C = ⊤ := by simp [TilingLattice, hr]
          let v : GaussianInt := x - z0
          have hv : v ∈ TilingLattice C := by rw [hlat]; trivial
          let T0 : ProtoTile := ⟨{z0}, anchor⟩
          obtain ⟨_, _, _, _, _, _, _, hvertices, _⟩ := TileTranslationFormulas T0 v
          have hb : x ∈ BoundaryFootprintVertices (TileTranslation T0 v) :=
              PeriodicSuperharmonicGeometry.hb x z0 anchor hvertices
          have heq := PeriodicBoundaryWebLaplacian C T0 h g (PeriodicSuperharmonicGeometry.hT0 C
              z z0 anchor hc)
            (by rw [hc]; simpa [T0] using hodo) hext hcocycle x
            ⟨v, hv, hb⟩
          omega
      | @decompose q hq S U hs hcells hfoot hcent =>
          have hcurv := ProperBandCurvatureStructure q hq
          have hq0 : q 0 = C.1.1 := hc.symm
          have hz (i : Fin 3) : (q i.succ).1 = 0 := PeriodicSuperharmonicGeometry.hzAt394 C hr q
              hq hcurv hq0 i
          have hzero := hcurv.2.2 0 1 (hz 0) (hz 1)
          omega
    · have bg := BandGenealogy C
      rcases bg with hbad | ⟨q, hq, hq0, hlt, huniq⟩
      · exact (hr hbad).elim
      · have hq0' : q 0 = C.1.1 := hq0
        have hpq : ProperBandQuadruple q := ⟨hq, by simpa [hq0'] using hlt⟩
        have hT' : BandPrototile (q 0) T := by simpa [hq0'] using hT
        obtain ⟨htiling, hcount⟩ := BandTileTopologyApplication C q hpq hq0 T hT'
        obtain ⟨U, hUF, hxU, hunique⟩ := htiling.2 x
        obtain ⟨v, hv, rfl⟩ := hUF
        have hvL : v ∈ TilingLattice C := hv
        have hcell : x ∈ (TileTranslation T v).cells := hxU
        have hrepr := (TileTranslationFormulas T v).1
        obtain ⟨hcells, hanchor, hempty, hreal, hcentroid, hfootform, hedgeform,
          hboundaryform, hboundaryedgeform⟩ := TileTranslationFormulas T v
        have hy : ∃ y ∈ T.cells, y + v = x := by
          simpa [TileTranslation, GaussianTranslation, hrepr] using hcell
        obtain ⟨y, hyT, hxy⟩ := hy
        have hxy' : x = y + v := hxy.symm
        by_cases hboundary : x ∈ BoundaryFootprintVertices (TileTranslation T v)
        · have heq := PeriodicBoundaryWebLaplacian C T h g hT hodo hext hcocycle x
            ⟨v, hvL, hboundary⟩
          omega
        · have hyboundary := PeriodicSuperharmonicGeometry.hyboundary T x v hboundaryform y hxy
            hboundary
          rw [hxy']
          exact (lap_periodic v hvL y).trans_le (hlocal y (PeriodicSuperharmonicGeometry.hyfoot T
              y hyT) hyboundary)

end ApollonianSuperharmonic

end

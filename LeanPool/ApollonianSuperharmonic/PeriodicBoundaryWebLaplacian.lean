/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.OdometerWeb

-- [TABLET NODE: PeriodicBoundaryWebLaplacian]

/-!
# PeriodicBoundaryWebLaplacian

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace WebLaplacianGeometry

private theorem hunit :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), (∀ v ∈ TilingLattice C, ∃ (a :
            GaussianInt), (CircleMatrix C).mulVec ![(↑v.re : ℝ), (↑v.im : ℝ)] = ![(↑a.re : ℝ),
            (↑a.im : ℝ)] ∧ ∀ (x : GaussianInt), g (x + v) = g x + x.re * a.re + x.im * a.im + g
            v) → ((C.1.1.1 = (1 : ℤ)) → (∀ y, FourNeighborLaplacian g y = 1)) ) := by
  classical
  intro C g hcocycle hc
  obtain ⟨z, hz⟩ := CurvatureOneBandCircleClassification C hc
  have hlattice : TilingLattice C = ⊤ := by simp [TilingLattice, hc]
  have hmatrix : CircleMatrix C =
      let c : ℝ := C.1.1.1
      let x : ℝ := C.1.1.2.re
      let y : ℝ := C.1.1.2.im
      (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CircleMatrix, BandCircleEuclideanData]
    all_goals field_simp
  have hcoord := congrArg Prod.snd hz
  have hcoordR : (C.1.1.2.re : ℝ) = 1 + 2 * (z.re : ℝ) := by
    rw [hcoord]
    exact_mod_cast (show (1 + 2 * z).re = 1 + 2 * z.re by simp)
  have hcoordI : (C.1.1.2.im : ℝ) = 2 * (z.im : ℝ) := by
    rw [hcoord]
    exact_mod_cast (show (1 + 2 * z).im = 2 * z.im by simp)
  obtain ⟨_, _, hshift0⟩ := hcocycle 0 (by rw [hlattice]; simp)
  have hg0 : g 0 = 0 := by
    have h := hshift0 0
    simp at h
    linarith
  obtain ⟨aP, hP, hshiftP⟩ := hcocycle 1 (by rw [hlattice]; simp)
  obtain ⟨aM, hM, hshiftM⟩ := hcocycle (-1) (by rw [hlattice]; simp)
  obtain ⟨aI, hI, hshiftI⟩ := hcocycle ⟨0, 1⟩ (by rw [hlattice]; simp)
  obtain ⟨aMI, hMI, hshiftMI⟩ :=
    hcocycle (-(⟨0, 1⟩ : GaussianInt)) (by rw [hlattice]; simp)
  have hpcoords : (aP.re : ℝ) = 1 + (z.re : ℝ) ∧
      (aP.im : ℝ) = (z.im : ℝ) := by
    rw [hmatrix] at hP
    dsimp at hP
    rw [hc, hcoordR, hcoordI] at hP
    have h0 := congrFun hP 0
    have h1 := congrFun hP 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at h0 h1
    field_simp at h0
    constructor <;> linarith
  have hmcoords : (aM.re : ℝ) = -(1 + (z.re : ℝ)) ∧
      (aM.im : ℝ) = -(z.im : ℝ) := by
    rw [hmatrix] at hM
    dsimp at hM
    rw [hc, hcoordR, hcoordI] at hM
    have h0 := congrFun hM 0
    have h1 := congrFun hM 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at h0 h1
    field_simp at h0
    constructor <;> linarith
  have hic : (aI.re : ℝ) = (z.im : ℝ) ∧
      (aI.im : ℝ) = -(z.re : ℝ) := by
    rw [hmatrix] at hI
    dsimp at hI
    rw [hc, hcoordR, hcoordI] at hI
    have h0 := congrFun hI 0
    have h1 := congrFun hI 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at h0 h1
    constructor <;> linarith
  have hmic : (aMI.re : ℝ) = -(z.im : ℝ) ∧
      (aMI.im : ℝ) = (z.re : ℝ) := by
    rw [hmatrix] at hMI
    dsimp at hMI
    rw [hc, hcoordR, hcoordI] at hMI
    have h0 := congrFun hMI 0
    have h1 := congrFun hMI 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at h0 h1
    constructor <;> linarith
  have hRe : aM.re = -aP.re := by
    exact_mod_cast (by linarith [hpcoords.1, hmcoords.1] :
      (aM.re : ℝ) = -(aP.re : ℝ))
  have hImP : aM.im = -aP.im := by
    exact_mod_cast (by linarith [hpcoords.2, hmcoords.2] :
      (aM.im : ℝ) = -(aP.im : ℝ))
  have hReI : aMI.re = -aI.re := by
    exact_mod_cast (by linarith [hic.1, hmic.1] :
      (aMI.re : ℝ) = -(aI.re : ℝ))
  have hIm : aMI.im = -aI.im := by
    exact_mod_cast (by linarith [hic.2, hmic.2] :
      (aMI.im : ℝ) = -(aI.im : ℝ))
  have hpconst : g 1 + g (-1) = aP.re := by
    have h := hshiftP (-1)
    have hadd : (-1 : GaussianInt) + 1 = 0 := by ext <;> norm_num
    rw [hadd, hg0] at h
    norm_num at h
    omega
  have hiconst : g ⟨0, 1⟩ + g (-(⟨0, 1⟩ : GaussianInt)) = aI.im := by
    have h := hshiftI (-(⟨0, 1⟩ : GaussianInt))
    have hadd : -(⟨0, 1⟩ : GaussianInt) + ⟨0, 1⟩ = 0 := by
      ext <;> norm_num
    rw [hadd, hg0] at h
    norm_num at h
    omega
  intro y
  have hre (x w : GaussianInt) : (x + w).re = x.re + w.re := by
    cases x; cases w; rfl
  have him (x w : GaussianInt) : (x + w).im = x.im + w.im := by
    cases x; cases w; rfl
  have hpairs : g (y + 1) + g (y - 1) - 2 * g y =
      g 1 + g (-1) := by
    have hsub : y - 1 = y + (-1) := by abel
    rw [hsub, hshiftP y, hshiftM y, hRe, hImP]
    ring
  have hipairs : g (y + ⟨0, 1⟩) + g (y - ⟨0, 1⟩) - 2 * g y =
      g ⟨0, 1⟩ + g (-(⟨0, 1⟩ : GaussianInt)) := by
    have hsub : y - ⟨0, 1⟩ = y + -(⟨0, 1⟩ : GaussianInt) := by abel
    rw [hsub, hshiftI y, hshiftMI y, hReI, hIm]
    ring
  have hsum : g (y + 1) + g (y - 1) + g (y + ⟨0, 1⟩) +
      g (y - ⟨0, 1⟩) - 4 * g y =
      (g 1 + g (-1)) +
        (g ⟨0, 1⟩ + g (-(⟨0, 1⟩ : GaussianInt))) := by
    linarith [hpairs, hipairs]
  rw [FourNeighborLaplacian, hsum, hpconst, hiconst]
  have htrace : (aP.re : ℝ) + (aI.im : ℝ) = 1 := by
    linarith [hpcoords.1, hic.2]
  exact_mod_cast htrace

private theorem hproper :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (SemiProperQuadruple q) →
            ((q (0 : Fin (4 : ℕ)) = C.1.1) → ((∀ (j : Fin (3 : ℕ)), (q j.succ).1 < C.1.1.1) →
            (ProperBandQuadruple q))) ) := by
  classical
  intro C q hsemi hqC hless
  refine ⟨hsemi, ?_⟩
  intro j
  simpa [hqC] using hless j

private theorem hcells :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (v : GaussianInt), ∀ (hv : v ∈ TilingLattice C), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)),
        let iv : TilingLattice C := ⟨v, hv⟩
        (P.tile iv).cells.Nonempty ) := by
  classical
  intro C v hv P iv
  have hreal : (TileRealization (P.tile iv)).Nonempty := by
    rcases P.tiles_are_disks iv with ⟨e⟩
    let z : Metric.closedBall (0 : ℝ × ℝ) 1 := ⟨0, by simp⟩
    exact ⟨e z, (e z).property⟩
  rcases hreal with ⟨z, hz⟩
  simp only [TileRealization, Set.mem_iUnion] at hz
  rcases hz with ⟨c, hc, _⟩
  exact ⟨c, hc⟩

private theorem hcorner :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (v : GaussianInt), ∀ (hv :
            v ∈ TilingLattice C), (x ∈ BoundaryFootprintVertices (TileTranslation T v)) → (∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)),
        let iv : TilingLattice C := ⟨v, hv⟩
        (x ∈ BoundaryFootprintVertices (P.tile iv)) → (((P.tile iv).cells.Nonempty) → (∃ y ∈
            (P.tile iv).cells, y = x ∨ y = x - 1 ∨ y = x - 1 - ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩))) ) := by
  classical
  intro C T x v hv hx P iv hxi hcells
  rw [BoundaryFootprintVertices, ite_eq_left hcells] at hxi
  rcases hxi with ⟨e, he, hxe⟩
  rcases he with ⟨z, ⟨rfl, hs⟩ | ⟨rfl, hs⟩⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hs with ⟨hz, _⟩ | ⟨_, hz⟩
    · rcases hxe with h | h
      · subst x
        exact ⟨z, hz, Or.inl rfl⟩
      · have hz' : z = x - 1 := by rw [h]; abel
        exact ⟨z, hz, Or.inr (Or.inl hz')⟩
    · rcases hxe with h | h
      · subst x
        exact ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr rfl))⟩
      · have hz' : z = x - 1 := by rw [h]; abel
        refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        rw [h]
        abel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hs with ⟨hz, _⟩ | ⟨_, hz⟩
    · rcases hxe with h | h
      · subst x
        exact ⟨z, hz, Or.inl rfl⟩
      · have hz' : z = x - ⟨0, 1⟩ := by rw [h]; abel
        exact ⟨z, hz, Or.inr (Or.inr (Or.inr hz'))⟩
    · rcases hxe with h | h
      · subst x
        exact ⟨z - 1, hz, Or.inr (Or.inl rfl)⟩
      · have hz' : z = x - ⟨0, 1⟩ := by rw [h]; abel
        refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        rw [h]
        abel

private theorem hcornerOutside :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (v : GaussianInt), ∀ (hv :
            v ∈ TilingLattice C), (x ∈ BoundaryFootprintVertices (TileTranslation T v)) → (∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)),
        let iv : TilingLattice C := ⟨v, hv⟩
        (x ∈ BoundaryFootprintVertices (P.tile iv)) → (((P.tile iv).cells.Nonempty) → ((∃ y ∈
            (P.tile iv).cells, y = x ∨ y = x - 1 ∨ y = x - 1 - ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) → (∃ y, y
            ∉ (P.tile iv).cells ∧ (y = x ∨ y = x - 1 ∨ y = x - 1 - ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩))))) )
            := by
  classical
  intro C T x v hv hx P iv hxi hcells hcorner
  rw [BoundaryFootprintVertices, ite_eq_left hcells] at hxi
  rcases hxi with ⟨e, he, hxe⟩
  rcases he with ⟨z, ⟨rfl, hs⟩ | ⟨rfl, hs⟩⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hs with ⟨_, hz⟩ | ⟨hz, _⟩
    · rcases hxe with h | h
      · subst x
        exact ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr rfl))⟩
      · have hz' : z = x - 1 := by rw [h]; abel
        refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        rw [h]
        abel
    · rcases hxe with h | h
      · subst x
        exact ⟨z, hz, Or.inl rfl⟩
      · have hz' : z = x - 1 := by rw [h]; abel
        exact ⟨z, hz, Or.inr (Or.inl hz')⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hs with ⟨_, hz⟩ | ⟨hz, _⟩
    · rcases hxe with h | h
      · subst x
        exact ⟨z - 1, hz, Or.inr (Or.inl rfl)⟩
      · have hz' : z = x - ⟨0, 1⟩ := by rw [h]; abel
        refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        rw [h]
        abel
    · rcases hxe with h | h
      · subst x
        exact ⟨z, hz, Or.inl rfl⟩
      · have hz' : z = x - ⟨0, 1⟩ := by rw [h]; abel
        exact ⟨z, hz, Or.inr (Or.inr (Or.inr hz'))⟩

private theorem hvowner :
    (by
      classical
        exact
        ∀ (C : BandCircle),
          ∀ (x : GaussianInt),
            ∀ (v : GaussianInt),
              ∀ (hv : v ∈ TilingLattice C),
                (∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
                  let iv : TilingLattice C := ⟨v, hv⟩;
                  ((∃ y ∈ (P.tile iv).cells,
                      y = x ∨ y = x - 1 ∨ y = x - 1 - ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) →
                    (∀ (a0 : ↥(TilingLattice C)),
                      ((∀ (y : ↥(TilingLattice C)),
                          (fun (a : ↥(TilingLattice C)) => x ∈ (P.tile a).cells) y →
                            y = a0) →
                        (∀ (a1 : ↥(TilingLattice C)),
                          ((∀ (y : ↥(TilingLattice C)),
                              (fun (a : ↥(TilingLattice C)) =>
                                    x - (1 : LatticeCell) ∈ (P.tile a).cells)
                                  y →
                                y = a1) →
                            (∀ (a2 : ↥(TilingLattice C)),
                              ((∀ (y : ↥(TilingLattice C)),
                                  (fun (a : ↥(TilingLattice C)) =>
                                        x - (1 : LatticeCell) -
                                            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈
                                          (P.tile a).cells)
                                      y →
                                    y = a2) →
                                (∀ (a3 : ↥(TilingLattice C)),
                                  ((∀ (y : ↥(TilingLattice C)),
                                      (fun (a : ↥(TilingLattice C)) =>
                                            x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈
                                              (P.tile a).cells)
                                          y →
                                        y = a3) →
                                    (iv = a0 ∨
                                      iv = a1 ∨ iv = a2 ∨ iv = a3)))))))))))) := by
  classical
  intro C x v hv P iv hcorner a0 hu0 a1 hu1 a2 hu2 a3 hu3
  rcases hcorner with ⟨y, hy, rfl | rfl | rfl | rfl⟩
  · exact Or.inl (hu0 iv hy)
  · exact Or.inr (Or.inl (hu1 iv hy))
  · exact Or.inr (Or.inr (Or.inl (hu2 iv hy)))
  · exact Or.inr (Or.inr (Or.inr (hu3 iv hy)))

private theorem hvnotfour :
    (by
      classical
      exact
        ∀ (C : BandCircle) (x v : GaussianInt)
          (hv : v ∈ TilingLattice C)
          (P :
            PeriodicTileComplex
              ↥(TilingLattice C)),
          let iv := ⟨v, hv⟩;
          (∃ y ∉ (P.tile iv).cells,
              y = x ∨
                y = x - (1 : LatticeCell) ∨
                  y =
                      x - (1 : LatticeCell) -
                        { re := (0 : ℤ), im := (1 : ℤ) } ∨
                    y = x - { re := (0 : ℤ), im := (1 : ℤ) }) →
            ∀ (a0 : ↥(TilingLattice C)),
              x ∈ (P.tile a0).cells →
                ∀ (a1 : ↥(TilingLattice C)),
                  x - (1 : LatticeCell) ∈ (P.tile a1).cells →
                    ∀ (a2 : ↥(TilingLattice C)),
                      x - (1 : LatticeCell) -
                            { re := (0 : ℤ), im := (1 : ℤ) } ∈
                          (P.tile a2).cells →
                        ∀ (a3 : ↥(TilingLattice C)),
                          x - { re := (0 : ℤ), im := (1 : ℤ) } ∈ (P.tile a3).cells →
                            ¬(iv = a0 ∧ iv = a1 ∧ iv = a2 ∧ iv = a3)) := by
  classical
  intro C x v hv P iv hcornerOutside a0 ha0 a1 ha1 a2 ha2 a3 ha3
  rintro ⟨h0, h1, h2, h3⟩
  rcases hcornerOutside with ⟨y, hy, rfl | rfl | rfl | rfl⟩
  · exact hy (by simpa [h0] using ha0)
  · exact hy (by simpa [h1] using ha1)
  · exact hy (by simpa [h2] using ha2)
  · exact hy (by simpa [h3] using ha3)

private theorem atMostOneRemaining :
    (by
      classical
      exact
        ∀ a b c i j : Fin 4, a ≠ b → c ≠ a → c ≠ b → i ≠ a → i ≠ b → i ≠ c → j ≠ a → j ≠ b → j ≠
            c → i = j ) := by
  classical
  decide +kernel

private theorem secondOwnerCoversThree :
    (by
      classical
      exact
        (∀ a b c i j : Fin 4, a ≠ b → c ≠ a → c ≠ b → i ≠ a → i ≠ b → i ≠ c → j ≠ a → j ≠ b → j ≠
            c → i = j) → (∀ {I : Type}, ∀ (f : Fin 4 → I), ∀ (m : Fin 4), (∃ w, f w ≠ f m) → ((¬
            Function.Injective f) → (∃ w, f w ≠ f m ∧ ∀ i, ∀ j, f i ≠ f m → f i ≠ f w → f j ≠ f m
            → f j ≠ f w → i = j))) ) := by
  classical
  intro atMostOneRemaining I f m hother hnotinj
  classical
  have hrepeat : ∃ a b, f a = f b ∧ a ≠ b := by
    by_contra h
    apply hnotinj
    intro a b hab
    by_contra hne
    exact h ⟨a, b, hab, hne⟩
  obtain ⟨a, b, hab, hne⟩ := hrepeat
  by_cases ha : f a = f m
  · obtain ⟨w, hw⟩ := hother
    have hb : f b = f m := hab.symm.trans ha
    have hwa : w ≠ a := by
      intro h
      exact hw ((congrArg f h).trans ha)
    have hwb : w ≠ b := by
      intro h
      exact hw ((congrArg f h).trans hb)
    refine ⟨w, hw, ?_⟩
    intro i j him hiw hjm hjw
    apply atMostOneRemaining a b w i j hne hwa hwb
    · intro h
      exact him ((congrArg f h).trans ha)
    · intro h
      exact him ((congrArg f h).trans hb)
    · intro h
      exact hiw (congrArg f h)
    · intro h
      exact hjm ((congrArg f h).trans ha)
    · intro h
      exact hjm ((congrArg f h).trans hb)
    · intro h
      exact hjw (congrArg f h)
  · have hma : m ≠ a := by
      intro h
      exact ha (congrArg f h.symm)
    have hmb : m ≠ b := by
      intro h
      exact ha (hab.trans (congrArg f h.symm))
    refine ⟨a, ha, ?_⟩
    intro i j him hia hjm hja
    apply atMostOneRemaining a b m i j hne hma hmb
    · intro h
      exact hia (congrArg f h)
    · intro h
      exact hia ((congrArg f h).trans hab.symm)
    · intro h
      exact him (congrArg f h)
    · intro h
      exact hja (congrArg f h)
    · intro h
      exact hja ((congrArg f h).trans hab.symm)
    · intro h
      exact hjm (congrArg f h)

private theorem hmexists :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (v : GaussianInt), ∀ (hv : v ∈ TilingLattice C),
        let iv : TilingLattice C := ⟨v, hv⟩
        ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀
            (a3 : ↥(TilingLattice C)), (iv = a0 ∨ iv = a1 ∨ iv = a2 ∨ iv = a3) → (
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∃ m : Fin 4, owner m = iv) ) := by
  classical
  intro C v hv iv a0 a1 a2 a3 hvowner owner
  rcases hvowner with h | h | h | h
  · exact ⟨0, by simpa [owner] using h.symm⟩
  · exact ⟨1, by simpa [owner] using h.symm⟩
  · exact ⟨2, by simpa [owner] using h.symm⟩
  · exact ⟨3, by simpa [owner] using h.symm⟩

private theorem hnotinj :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 :
            ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)), (a0 = a1 ∨ a0 = a2 ∨ a0 = a3 ∨ a1 =
            a2 ∨ a1 = a3 ∨ a2 = a3) → (
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ¬ Function.Injective owner) ) := by
  classical
  intro C a0 a1 a2 a3 hfour owner hi
  rcases hfour with h01 | h02 | h03 | h12 | h13 | h23
  · have hh : (0 : Fin 4) = 1 := hi (by simpa [owner] using h01)
    exact (by decide : (0 : Fin 4) ≠ 1) hh
  · have hh : (0 : Fin 4) = 2 := hi (by simpa [owner] using h02)
    exact (by decide : (0 : Fin 4) ≠ 2) hh
  · have hh : (0 : Fin 4) = 3 := hi (by simpa [owner] using h03)
    exact (by decide : (0 : Fin 4) ≠ 3) hh
  · have hh : (1 : Fin 4) = 2 := hi (by simpa [owner] using h12)
    exact (by decide : (1 : Fin 4) ≠ 2) hh
  · have hh : (1 : Fin 4) = 3 := hi (by simpa [owner] using h13)
    exact (by decide : (1 : Fin 4) ≠ 3) hh
  · have hh : (2 : Fin 4) = 3 := hi (by simpa [owner] using h23)
    exact (by decide : (2 : Fin 4) ≠ 3) hh

private theorem hnotall :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (v : GaussianInt), ∀ (hv : v ∈ TilingLattice C),
        let iv : TilingLattice C := ⟨v, hv⟩
        ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀
            (a3 : ↥(TilingLattice C)), (¬ (iv = a0 ∧ iv = a1 ∧ iv = a2 ∧ iv = a3)) → (
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ¬ ∀ i, owner i = iv) ) := by
  classical
  intro C v hv iv a0 a1 a2 a3 hvnotfour owner hall
  apply hvnotfour
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [owner] using (hall 0).symm
  · simpa [owner] using (hall 1).symm
  · simpa [owner] using (hall 2).symm
  · simpa [owner] using (hall 3).symm

private theorem hother :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (v : GaussianInt), ∀ (hv : v ∈ TilingLattice C),
        let iv : TilingLattice C := ⟨v, hv⟩
        ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀
            (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), (owner m = iv) → ((¬ ∀ i, owner i = iv) → (∃ w, owner w ≠ owner m))
            ) := by
  classical
  intro C v hv iv a0 a1 a2 a3 owner m hm hnotall
  by_contra hn
  push Not at hn
  apply hnotall
  intro i
  exact (hn i).trans hm

private theorem colorCycle :
    (by
      classical
      exact
        let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
        ∀ col : Fin 4 → Fin 3, (∃ i, col i = 0) → (∃ i, col i = 1) → (∀ i, ∀ j, col i = 2 → col j
            = 2 → i = j) → ∃ i, (col i = 0 ∧ col (next i) = 1) ∨ (col i = 1 ∧ col (next i) = 0) )
            := by
  classical
  intro next
  decide +kernel

private theorem hcol2unique :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 :
            ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), (owner w ≠ owner m) → ((∀ (i : Fin (4 : ℕ)), ∀
            (j : Fin (4 : ℕ)), owner i ≠ owner m → owner i ≠ owner w → owner j ≠ owner m → owner
            j ≠ owner w → i = j) → (
        let col : Fin 4 → Fin 3 := fun i =>
          if owner i = owner m then 0 else if owner i = owner w then 1 else 2
        ∀ i, ∀ j, col i = 2 → col j = 2 → i = j)) ) := by
  classical
  intro C a0 a1 a2 a3 owner m w hmw hcover col i j hi hj
  have hiA : owner i ≠ owner m := by
    intro h
    have hc : col i = 0 := by simp [col, h]
    exact (by decide : (0 : Fin 3) ≠ 2) (hc.symm.trans hi)
  have hiB : owner i ≠ owner w := by
    intro h
    have hc : col i = 1 := by simp [col, h, hmw]
    exact (by decide : (1 : Fin 3) ≠ 2) (hc.symm.trans hi)
  have hjA : owner j ≠ owner m := by
    intro h
    have hc : col j = 0 := by simp [col, h]
    exact (by decide : (0 : Fin 3) ≠ 2) (hc.symm.trans hj)
  have hjB : owner j ≠ owner w := by
    intro h
    have hc : col j = 1 := by simp [col, h, hmw]
    exact (by decide : (1 : Fin 3) ≠ 2) (hc.symm.trans hj)
  exact hcover i j hiA hiB hjA hjB

private theorem hepair :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 :
            ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)),
        let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
        let col : Fin 4 → Fin 3 := fun i =>
          if owner i = owner m then 0 else if owner i = owner w then 1 else 2
        ∀ (e : Fin (4 : ℕ)), (col e = (0 : Fin (3 : ℕ)) ∧ col (next e) = (1 : Fin (3 : ℕ)) ∨ col
            e = (1 : Fin (3 : ℕ)) ∧ col (next e) = (0 : Fin (3 : ℕ))) → ((owner e = owner m ∧
            owner (next e) = owner w) ∨ (owner e = owner w ∧ owner (next e) = owner m)) ) := by
  classical
  intro C a0 a1 a2 a3 owner m w next col e hecolor
  rcases hecolor with h | h
  · left
    have h0 := h.1
    have h1 := h.2
    constructor
    · by_contra hn
      change (if owner e = owner m then 0 else
        if owner e = owner w then 1 else 2) = 0 at h0
      rw [ite_eq_right hn] at h0
      by_cases hew : owner e = owner w
      · rw [ite_eq_left hew] at h0
        exact (by decide : (1 : Fin 3) ≠ 0) h0
      · rw [ite_eq_right hew] at h0
        exact (by decide : (2 : Fin 3) ≠ 0) h0
    · have hne : owner (next e) ≠ owner m := by
        intro hh
        have hc : col (next e) = 0 := by simp [col, hh]
        exact (by decide : (0 : Fin 3) ≠ 1) (hc.symm.trans h1)
      change (if owner (next e) = owner m then 0 else
        if owner (next e) = owner w then 1 else 2) = 1 at h1
      rw [ite_eq_right hne] at h1
      by_contra hn
      rw [ite_eq_right hn] at h1
      exact (by decide : (2 : Fin 3) ≠ 1) h1
  · right
    have h0 := h.1
    have h1 := h.2
    constructor
    · have hne : owner e ≠ owner m := by
        intro hh
        have hc : col e = 0 := by simp [col, hh]
        exact (by decide : (0 : Fin 3) ≠ 1) (hc.symm.trans h0)
      change (if owner e = owner m then 0 else
        if owner e = owner w then 1 else 2) = 1 at h0
      rw [ite_eq_right hne] at h0
      by_contra hn
      rw [ite_eq_right hn] at h0
      exact (by decide : (2 : Fin 3) ≠ 1) h0
    · by_contra hn
      change (if owner (next e) = owner m then 0 else
        if owner (next e) = owner w then 1 else 2) = 0 at h1
      rw [ite_eq_right hn] at h1
      by_cases hew : owner (next e) = owner w
      · rw [ite_eq_left hew] at h1
        exact (by decide : (1 : Fin 3) ≠ 0) h1
      · rw [ite_eq_right hew] at h1
        exact (by decide : (2 : Fin 3) ≠ 0) h1

private theorem hsector :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), (x ∈ (P.tile a0).cells) → (∀ (a1 : ↥(TilingLattice C)),
            (x - (1 : LatticeCell) ∈ (P.tile a1).cells) → (∀ (a2 : ↥(TilingLattice C)), (x - (1 :
            LatticeCell) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a2).cells) → (∀ (a3 :
            ↥(TilingLattice C)), (x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a3).cells) → (
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        ∀ i, sector i ∈ (P.tile (owner i)).cells)))) ) := by
  classical
  intro C x P a0 ha0 a1 ha1 a2 ha2 a3 ha3 owner sector i
  fin_cases i
  · simpa [sector, owner] using ha0
  · simpa [sector, owner] using ha1
  · simpa [sector, owner] using ha2
  · simpa [sector, owner] using ha3

private theorem hsectorNot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice
            C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        (∀ i, sector i ∈ (P.tile (owner i)).cells) → (∀ (i : Fin 4), ∀ (j : Fin 4), (owner i ≠
            owner j) → (sector j ∉ (P.tile (owner i)).cells)) ) := by
  classical
  intro C x P a0 a1 a2 a3 owner sector hsector i j hij hmem
  have huniq := PeriodicTileIndexedMultiplicityOne P (sector j)
  have hji := huniq.unique (hsector j) hmem
  exact hij hji.symm

private theorem hedgeBoundary :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), (x ∈ (P.tile a0).cells) → (∀ (a1 : ↥(TilingLattice C)),
            (x - (1 : LatticeCell) ∈ (P.tile a1).cells) → (∀ (a2 : ↥(TilingLattice C)), (x - (1 :
            LatticeCell) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a2).cells) → (∀ (a3 :
            ↥(TilingLattice C)), (x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a3).cells) → (
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        let edge : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (i : Fin 4), ∀ (j : Fin 4), (owner i ≠ owner j) → (sector j ∉ (P.tile (owner
            i)).cells)) → (∀ (i : Fin 4), (owner i ≠ owner (next i)) → (edge i ∈
            BoundaryFootprintEdges (P.tile (owner i)) ∧ edge i ∈ BoundaryFootprintEdges (P.tile
            (owner (next i))))))))) ) := by
  classical
  intro C x P a0 ha0 a1 ha1 a2 ha2 a3 ha3 owner next sector edge hsectorNot i hij
  fin_cases i
  · constructor
    · refine ⟨x, Or.inr ⟨by simp [edge], Or.inl ⟨?_, ?_⟩⟩⟩
      · simpa [sector, owner] using ha0
      · exact hsectorNot 0 1 (by simpa [owner, next] using hij)
    · refine ⟨x, Or.inr ⟨by simp [edge], Or.inr ⟨?_, ?_⟩⟩⟩
      · exact hsectorNot 1 0 (by simpa [owner, next] using hij.symm)
      · simpa [sector, owner, next] using ha1
  · constructor
    · refine ⟨x - 1, Or.inl ⟨by simp [edge], Or.inl ⟨?_, ?_⟩⟩⟩
      · simpa [sector, owner] using ha1
      · exact hsectorNot 1 2 (by simpa [owner, next] using hij)
    · refine ⟨x - 1, Or.inl ⟨by simp [edge], Or.inr ⟨?_, ?_⟩⟩⟩
      · exact hsectorNot 2 1 (by simpa [owner, next] using hij.symm)
      · simpa [sector, owner, next] using ha2
  · constructor
    · refine ⟨x - ⟨0, 1⟩, Or.inr ⟨by simp [edge], Or.inr ⟨?_, ?_⟩⟩⟩
      · exact hsectorNot 2 3 (by simpa [owner, next] using hij)
      · have hcoord : x - ⟨0, 1⟩ - 1 = x - 1 - ⟨0, 1⟩ := by abel
        rw [hcoord]
        exact ha2
    · refine ⟨x - ⟨0, 1⟩, Or.inr ⟨by simp [edge], Or.inl ⟨?_, ?_⟩⟩⟩
      · simpa [sector, owner, next] using ha3
      · have hcoord : x - ⟨0, 1⟩ - 1 = x - 1 - ⟨0, 1⟩ := by abel
        rw [hcoord]
        exact hsectorNot 3 2 (by simpa [owner, next] using hij.symm)
  · constructor
    · refine ⟨x, Or.inl ⟨by simp [edge], Or.inr ⟨?_, ?_⟩⟩⟩
      · exact hsectorNot 3 0 (by simpa [owner, next] using hij)
      · simpa [sector, owner] using ha3
    · refine ⟨x, Or.inl ⟨by simp [edge], Or.inl ⟨?_, ?_⟩⟩⟩
      · simpa [sector, owner, next] using ha0
      · exact hsectorNot 0 3 (by simpa [owner, next] using hij.symm)

private theorem boundaryEdge :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈
            FootprintEdges U) ) := by
  classical
  intro U e he
  let I : GaussianInt := ⟨0, 1⟩
  rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inl rfl⟩
    · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
      congr 1 <;> simp [I, Zsqrtd.ext_iff]
  · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
      congr 1 <;> simp []

private theorem hnewe :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 :
            ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), (owner w ≠ owner m) → (
        let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
        ∀ (e : Fin (4 : ℕ)), ((owner e = owner m ∧ owner (next e) = owner w) ∨ (owner e = owner w
            ∧ owner (next e) = owner m)) → (owner e ≠ owner (next e))) ) := by
  classical
  intro C a0 a1 a2 a3 owner m w hmw next e hepair heq
  rcases hepair with ⟨heA, henB⟩ | ⟨heB, henA⟩
  · apply hmw
    calc
      owner w = owner (next e) := henB.symm
      _ = owner e := heq.symm
      _ = owner m := heA
  · apply hmw
    calc
      owner w = owner e := heB.symm
      _ = owner (next e) := heq
      _ = owner m := henA

private theorem hcommon :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice
            C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)),
        let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
        ∀ (e : Fin (4 : ℕ)), ((owner e = owner m ∧ owner (next e) = owner w) ∨ (owner e = owner w
            ∧ owner (next e) = owner m)) → (
        let edge : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈
            FootprintEdges U)) → ((edge e ∈ BoundaryFootprintEdges (P.tile (owner e))) → ((edge e
            ∈ BoundaryFootprintEdges (P.tile (owner (next e)))) → ((FootprintEdges (P.tile (owner
            m)) ∩ FootprintEdges (P.tile (owner w))).Nonempty)))) ) := by
  classical
  intro C x P a0 a1 a2 a3 owner m w next e hepair edge boundaryEdge edge_mem_e edge_mem_next
  refine ⟨edge e, ?_⟩
  rcases hepair with ⟨heA, henB⟩ | ⟨heB, henA⟩
  · constructor
    · simpa [heA] using boundaryEdge (P.tile (owner e)) (edge e) edge_mem_e
    · simpa [henB] using boundaryEdge (P.tile (owner (next e)))
        (edge e) edge_mem_next
  · constructor
    · simpa [henA] using boundaryEdge (P.tile (owner (next e)))
        (edge e) edge_mem_next
    · simpa [heB] using boundaryEdge (P.tile (owner e)) (edge e) edge_mem_e

private theorem hadj :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (a0 :
            ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3
            : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), (owner m ≠ owner w) → (((FootprintEdges (P.tile
            (owner m)) ∩ FootprintEdges (P.tile (owner w))).Nonempty) → (P.plane.adjacent (owner
            m) (owner w))) ) := by
  classical
  intro C P a0 a1 a2 a3 owner m w hneq hcommon
  have hclass := (PeriodicTileIntersectionClassification P).1
  exact (hclass (owner m) (owner w) hneq).1.mp hcommon

private theorem slope_for :
    (by
      classical
      exact
        ∀ (C : BandCircle), (PeriodicTileComplex ↥(TilingLattice C)) → ((↥(TilingLattice C)) →
            ((↥(TilingLattice C)) → ((↥(TilingLattice C)) → ((↥(TilingLattice C)) → ((Fin (4 :
            ℕ)) → ((Fin (4 : ℕ)) → (∀ (c : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k :
            PartialOdometer), TileOdometer c U k → 1 < c.1 → ∃ p : ℝ × ℝ, PartialOdometerSlope k
            = some p))))))) ) := by
  classical
  intro C P a0 a1 a2 a3 m w c U k ho hcpos
  induction ho with
  | line w y hw hdom => omega
  | unit z y U hU hdom htrans => omega
  | @decompose qd hqd S U hs k hU hsub hcells hfoot hcentroid hdom hvalue
      hcompat hslope ih =>
    have facts := ProperBandCurvatureStructure qd hqd
    have hp : ∃ i : Fin 3, 0 < (qd i.succ).1 := by
      by_cases h0 : 0 < (qd (0 : Fin 3).succ).1
      · exact ⟨0, h0⟩
      by_cases h1 : 0 < (qd (1 : Fin 3).succ).1
      · exact ⟨1, h1⟩
      by_cases h2 : 0 < (qd (2 : Fin 3).succ).1
      · exact ⟨2, h2⟩
      have n0 := facts.2.1 (0 : Fin 3)
      have n1 := facts.2.1 (1 : Fin 3)
      have z0 : (qd (0 : Fin 3).succ).1 = 0 := by omega
      have z1 : (qd (1 : Fin 3).succ).1 = 0 := by omega
      exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim
    rcases hp with ⟨i, hi⟩
    rcases hslope i false with hz | ⟨p, pi, hp, hpi, hpr, hpi'⟩
    · omega
    · exact ⟨p, hp⟩

private theorem hcurvature :
    (by
      classical
      exact
        ∀ (C : BandCircle), (¬C.1.1.1 = (1 : ℤ)) → ((PeriodicTileComplex ↥(TilingLattice C)) → (∀
            (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)),
            ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)),
        let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
        let col : Fin 4 → Fin 3 := fun i =>
          if owner i = owner m then 0 else if owner i = owner w then 1 else 2
        ∀ (e : Fin (4 : ℕ)), (col e = (0 : Fin (3 : ℕ)) ∧ col (next e) = (1 : Fin (3 : ℕ)) ∨ col
            e = (1 : Fin (3 : ℕ)) ∧ col (next e) = (0 : Fin (3 : ℕ))) → (1 < C.1.1.1))) ) := by
  classical
  intro C hc P a0 a1 a2 a3 owner m w next col e hecolor
  have hpos : 0 < C.1.1.1 := C.2
  omega

private theorem hu_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (v : GaussianInt), ∀ (hv : v ∈ TilingLattice C),
        let iv : TilingLattice C := ⟨v, hv⟩
        ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀
            (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), (owner m = iv) → (
        let u : GaussianInt := owner m
        u = v) ) := by
  classical
  intro C v hv iv a0 a1 a2 a3 owner m hm u
  change (owner m : GaussianInt) = v
  rw [hm]

private theorem translateExtends :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (g : IntegerLatticeFunction), (GlobalOdometerExtends g h) → (∀
            (t : GaussianInt), ∀ (a : GaussianInt), (∀ y, g (y + t) = g y + y.re * a.re + y.im *
            a.im + g t) → (GlobalOdometerExtends g (PartialOdometerAffineTranslate h t a 0))) )
            := by
  classical
  intro h g hext t a hshift
  rcases hext with ⟨c, hc⟩
  refine ⟨c + g t - t.re * a.re - t.im * a.im, ?_⟩
  intro y hy
  have hy' := (PartialOdometerAffineTranslateFormulas h t a 0).2.1 y |>.mp hy
  have hval := (PartialOdometerAffineTranslateFormulas h t a 0).2.2.1 y hy
  have hext' := hc (y - t) hy'
  have hsum : y - t + t = y := by abel
  have hRe : (y - t).re + t.re = y.re := by
    have hh := congrArg Zsqrtd.re hsum
    simp
  have hIm : (y - t).im + t.im = y.im := by
    have hh := congrArg Zsqrtd.im hsum
    simp
  have hgy := hshift (y - t)
  rw [hsum] at hgy
  rw [hgy, hext', hval]
  rw [← hRe, ← hIm]
  ring

private theorem centroidShift :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (z : GaussianInt), TileCentroid (TileTranslation T z) = TileCentroid
            T + GaussianRealPoint z ) := by
  classical
  intro T z
  rw [(TileTranslationFormulas T z).2.2.2.2.1]
  ext <;> simp [GaussianRealPoint]

private theorem hcentDiff :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 :
            ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)),
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        (∀ (z : GaussianInt), TileCentroid (TileTranslation T z) = TileCentroid T +
            GaussianRealPoint z) → (TileCentroid (TileTranslation T u') - TileCentroid
            (TileTranslation T u) = GaussianRealPoint (u' - u)) ) := by
  classical
  intro C T a0 a1 a2 a3 owner m w u u' centroidShift
  rw [centroidShift u', centroidShift u]
  ext <;> simp [GaussianRealPoint]

private theorem hmatrixDiff :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 :
            ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)),
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        ∀ (au : GaussianInt), ((CircleMatrix C).mulVec ![(↑u.re : ℝ), (↑u.im : ℝ)] = ![(↑au.re :
            ℝ), (↑au.im : ℝ)]) → (∀ (au' : GaussianInt), ((CircleMatrix C).mulVec ![(↑u'.re : ℝ),
            (↑u'.im : ℝ)] = ![(↑au'.re : ℝ), (↑au'.im : ℝ)]) → (Matrix.mulVec (CircleMatrix C)
            ![((u' - u).re : ℝ), ((u' - u).im : ℝ)] = ![((au' - au).re : ℝ), ((au' - au).im :
            ℝ)])) ) := by
  classical
  intro C a0 a1 a2 a3 owner m w u u' au hAu au' hAu'
  have hre : (u' - u).re = u'.re - u.re := by
    cases u; cases u'; rfl
  have him : (u' - u).im = u'.im - u.im := by
    cases u; cases u'; rfl
  have hA0 := congrFun hAu 0
  have hA1 := congrFun hAu 1
  have hA0' := congrFun hAu' 0
  have hA1' := congrFun hAu' 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hA0 hA1 hA0' hA1'
  ext k
  fin_cases k
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hre, him]
    linarith
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hre, him]
    linarith

private theorem hAdiff :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a0 : ↥(TilingLattice C)),
            ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), ∀ (j : Fin (3 : ℕ)), ((↑(owner w) :
            GaussianInt) - (↑(owner m) : GaussianInt) = BandVectors.1 (q j.succ) (q (0 : Fin (4 :
            ℕ))) ∨ (↑(owner w) : GaussianInt) - (↑(owner m) : GaussianInt) = -BandVectors.1 (q
            j.succ) (q (0 : Fin (4 : ℕ)))) → (
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        ∀ (au : GaussianInt), ∀ (au' : GaussianInt), (Matrix.mulVec (CircleMatrix C) ![((u' -
            u).re : ℝ), ((u' - u).im : ℝ)] = ![((au' - au).re : ℝ), ((au' - au).im : ℝ)]) →
            (((CircleMatrix C).mulVec ![(↑(BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ)))).re :
            ℝ), (↑(BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ)))).im : ℝ)] = ![(↑(BandVectors.2
            (q j.succ) (q (0 : Fin (4 : ℕ)))).re : ℝ), (↑(BandVectors.2 (q j.succ) (q (0 : Fin (4
            : ℕ)))).im : ℝ)]) → (au' - au = BandVectors.2 (q j.succ) (q 0) ∨ au' - au =
            -BandVectors.2 (q j.succ) (q 0)))) ) := by
  classical
  intro C q a0 a1 a2 a3 owner m w j hsign u u' au au' hmatrixDiff hincoming
  rcases hsign with hplus | hminus
  · have hmd := hmatrixDiff
    rw [hplus] at hmd
    left
    have hvec := hmd.symm.trans hincoming
    ext
    · have hh : ((au' - au).re : ℝ) =
          ((BandVectors.2 (q j.succ) (q 0)).re : ℝ) := by
        simpa using congrFun hvec 0
      exact_mod_cast hh
    · have hh : ((au' - au).im : ℝ) =
          ((BandVectors.2 (q j.succ) (q 0)).im : ℝ) := by
        simpa using congrFun hvec 1
      exact_mod_cast hh
  · have hmd := hmatrixDiff
    rw [hminus] at hmd
    right
    have hneg' : Matrix.mulVec (CircleMatrix C)
        ![(-((BandVectors.1 (q j.succ) (q 0)).re : ℝ)),
          (-((BandVectors.1 (q j.succ) (q 0)).im : ℝ))] =
        ![(-((BandVectors.2 (q j.succ) (q 0)).re : ℝ)),
          (-((BandVectors.2 (q j.succ) (q 0)).im : ℝ))] := by
      ext k
      fin_cases k
      · have hc := congrFun hincoming 0
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc ⊢
        linarith
      · have hc := congrFun hincoming 1
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc ⊢
        linarith
    have hneg : Matrix.mulVec (CircleMatrix C)
        ![((-BandVectors.1 (q j.succ) (q 0)).re : ℝ),
          ((-BandVectors.1 (q j.succ) (q 0)).im : ℝ)] =
        ![((-BandVectors.2 (q j.succ) (q 0)).re : ℝ),
          ((-BandVectors.2 (q j.succ) (q 0)).im : ℝ)] := by
      simpa [Zsqrtd.re_neg, Zsqrtd.im_neg] using hneg'
    have hmd' := hmd
    simp only [Zsqrtd.re_neg, Zsqrtd.im_neg] at hmd'
    have hvec := hmd'.symm.trans hneg
    ext
    · have hh : ((au' - au).re : ℝ) =
          (-((BandVectors.2 (q j.succ) (q 0)).re : ℝ)) := by
        simpa using congrFun hvec 0
      exact_mod_cast hh
    · have hh : ((au' - au).im : ℝ) =
          (-((BandVectors.2 (q j.succ) (q 0)).im : ℝ)) := by
        simpa using congrFun hvec 1
      exact_mod_cast hh

private theorem aDiffPlus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a0 : ↥(TilingLattice C)),
            ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), ∀ (j : Fin (3 : ℕ)),
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        ∀ (au : GaussianInt), ∀ (au' : GaussianInt), (Matrix.mulVec (CircleMatrix C) ![((u' -
            u).re : ℝ), ((u' - u).im : ℝ)] = ![((au' - au).re : ℝ), ((au' - au).im : ℝ)]) →
            (((CircleMatrix C).mulVec ![(↑(BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ)))).re :
            ℝ), (↑(BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ)))).im : ℝ)] = ![(↑(BandVectors.2
            (q j.succ) (q (0 : Fin (4 : ℕ)))).re : ℝ), (↑(BandVectors.2 (q j.succ) (q (0 : Fin (4
            : ℕ)))).im : ℝ)]) → ((u' - u = BandVectors.1 (q j.succ) (q 0)) → (au' - au =
            BandVectors.2 (q j.succ) (q 0)))) ) := by
  classical
  intro C q a0 a1 a2 a3 owner m w j u u' au au' hmatrixDiff hincoming hplus
  have hmd := hmatrixDiff
  rw [hplus] at hmd
  have hvec := hmd.symm.trans hincoming
  ext
  · have hh : ((au' - au).re : ℝ) =
        ((BandVectors.2 (q j.succ) (q 0)).re : ℝ) := by
      simpa using congrFun hvec 0
    exact_mod_cast hh
  · have hh : ((au' - au).im : ℝ) =
        ((BandVectors.2 (q j.succ) (q 0)).im : ℝ) := by
      simpa using congrFun hvec 1
    exact_mod_cast hh

private theorem aDiffMinus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a0 : ↥(TilingLattice C)),
            ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), ∀ (j : Fin (3 : ℕ)),
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        ∀ (au : GaussianInt), ∀ (au' : GaussianInt), (Matrix.mulVec (CircleMatrix C) ![((u' -
            u).re : ℝ), ((u' - u).im : ℝ)] = ![((au' - au).re : ℝ), ((au' - au).im : ℝ)]) →
            (((CircleMatrix C).mulVec ![(↑(BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ)))).re :
            ℝ), (↑(BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ)))).im : ℝ)] = ![(↑(BandVectors.2
            (q j.succ) (q (0 : Fin (4 : ℕ)))).re : ℝ), (↑(BandVectors.2 (q j.succ) (q (0 : Fin (4
            : ℕ)))).im : ℝ)]) → ((u' - u = -BandVectors.1 (q j.succ) (q 0)) → (au' - au =
            -BandVectors.2 (q j.succ) (q 0)))) ) := by
  classical
  intro C q a0 a1 a2 a3 owner m w j u u' au au' hmatrixDiff hincoming hminus
  have hmd := hmatrixDiff
  rw [hminus] at hmd
  have hneg' : Matrix.mulVec (CircleMatrix C)
      ![(-((BandVectors.1 (q j.succ) (q 0)).re : ℝ)),
        (-((BandVectors.1 (q j.succ) (q 0)).im : ℝ))] =
      ![(-((BandVectors.2 (q j.succ) (q 0)).re : ℝ)),
        (-((BandVectors.2 (q j.succ) (q 0)).im : ℝ))] := by
    ext k
    fin_cases k
    · have hc := congrFun hincoming 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc ⊢
      linarith
    · have hc := congrFun hincoming 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc ⊢
      linarith
  have hneg : Matrix.mulVec (CircleMatrix C)
      ![((-BandVectors.1 (q j.succ) (q 0)).re : ℝ),
        ((-BandVectors.1 (q j.succ) (q 0)).im : ℝ)] =
      ![((-BandVectors.2 (q j.succ) (q 0)).re : ℝ),
        ((-BandVectors.2 (q j.succ) (q 0)).im : ℝ)] := by
    simpa [Zsqrtd.re_neg, Zsqrtd.im_neg] using hneg'
  simp only [Zsqrtd.re_neg, Zsqrtd.im_neg] at hmd
  have hvec := hmd.symm.trans hneg
  ext
  · have hh : ((au' - au).re : ℝ) =
        (-((BandVectors.2 (q j.succ) (q 0)).re : ℝ)) := by
      simpa using congrFun hvec 0
    exact_mod_cast hh
  · have hh : ((au' - au).im : ℝ) =
        (-((BandVectors.2 (q j.succ) (q 0)).im : ℝ)) := by
      simpa using congrFun hvec 1
    exact_mod_cast hh

private theorem hslopeU :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (h : PartialOdometer), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 :
            ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (p : ℝ × ℝ), (PartialOdometerSlope h = some p) → (
        let u : GaussianInt := owner m
        ∀ (au : GaussianInt),
        let huOdo : PartialOdometer := PartialOdometerAffineTranslate h u au 0
        PartialOdometerSlope huOdo = some (p.1 + (au.re : ℝ), p.2 + (au.im : ℝ))) ) := by
  classical
  intro C h a0 a1 a2 a3 owner m p hp u au huOdo
  rw [(PartialOdometerAffineTranslateFormulas h u au 0).2.2.2.2.2, hp]
  rfl

private theorem hslopeU' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (h : PartialOdometer), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 :
            ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (w : Fin (4 : ℕ)), ∀ (p : ℝ × ℝ), (PartialOdometerSlope h = some p) → (
        let u' : GaussianInt := owner w
        ∀ (au' : GaussianInt),
        let hu'Odo : PartialOdometer := PartialOdometerAffineTranslate h u' au' 0
        PartialOdometerSlope hu'Odo = some (p.1 + (au'.re : ℝ), p.2 + (au'.im : ℝ))) ) := by
  classical
  intro C h a0 a1 a2 a3 owner w p hp u' au' hu'Odo
  rw [(PartialOdometerAffineTranslateFormulas h u' au' 0).2.2.2.2.2, hp]
  rfl

private theorem cellVertex :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice
            C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        (∀ i, sector i ∈ (P.tile (owner i)).cells) → ((∀ (i : Fin 4), (P.tile (owner
            i)).cells.Nonempty) → (∀ (i : Fin 4), ∀ (y : GaussianInt), (y = sector i ∨ y = sector
            i + 1 ∨
            y = sector i + ⟨0, 1⟩ ∨ y = sector i + 1 + ⟨0, 1⟩) → (y ∈ FootprintVertices (P.tile
                (owner i))))) ) := by
  classical
  intro C x P a0 a1 a2 a3 owner sector hsector ownerNonempty i y hy
  simp only [FootprintVertices, ownerNonempty i, ite_true]
  exact ⟨sector i, hsector i, hy⟩

private theorem sectorCornerX :
    (by
      classical
      exact
        ∀ (x : GaussianInt),
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        ∀ i : Fin 4, x = sector i ∨ x = sector i + 1 ∨ x = sector i + ⟨0, 1⟩ ∨ x = sector i + 1 +
            ⟨0, 1⟩ ) := by
  classical
  intro x sector i
  fin_cases i <;> simp [sector]; abel; simp

private theorem pairCovered :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 :
            ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)),
            owner i ≠ owner m → owner i ≠ owner w → owner j ≠ owner m → owner j ≠ owner w → i =
            j) → (∀ (i : Fin 4), ∀ (j : Fin 4), (i ≠ j) → (owner i = owner m ∨ owner i = owner w
            ∨ owner j = owner m ∨ owner j = owner w)) ) := by
  classical
  intro C a0 a1 a2 a3 owner m w hcover i j hij
  by_contra hn
  push Not at hn
  have heq := hcover i j hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  exact hij heq

private theorem toDomains :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (P :
            PeriodicTileComplex ↥(TilingLattice C)), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 :
            ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)),
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        ∀ (au : GaussianInt), ∀ (au' : GaussianInt),
        let huOdo : PartialOdometer := PartialOdometerAffineTranslate h u au 0
        let hu'Odo : PartialOdometer := PartialOdometerAffineTranslate h u' au' 0
        ((huOdo.domain : Set GaussianInt) = FootprintVertices (TileTranslation T u)) →
            (((hu'Odo.domain : Set GaussianInt) = FootprintVertices (TileTranslation T u')) →
            ((P.tile (owner m) = TileTranslation T u) → ((P.tile (owner w) = TileTranslation T
            u') → (∀ (y : GaussianInt), (y ∈ FootprintVertices (P.tile (owner m)) ∨
            y ∈ FootprintVertices (P.tile (owner w))) → (y ∈ huOdo.domain ∨ y ∈
                hu'Odo.domain))))) ) := by
  classical
  intro C T h P a0 a1 a2 a3 owner m w u u' au au' huOdo hu'Odo hdomu hdomu' tileM tileW y hy
  rcases hy with hy | hy
  · have hy' : y ∈ FootprintVertices (TileTranslation T u) := by
      simpa [tileM] using hy
    exact Or.inl ((Set.ext_iff.mp hdomu y).mpr hy')
  · have hy' : y ∈ FootprintVertices (TileTranslation T u') := by
      simpa [tileW] using hy
    exact Or.inr ((Set.ext_iff.mp hdomu' y).mpr hy')

private theorem hxM :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (x : GaussianInt), ∀ (P
            : PeriodicTileComplex ↥(TilingLattice C)), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 :
            ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)),
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        let u : GaussianInt := owner m
        ∀ (au : GaussianInt),
        let huOdo : PartialOdometer := PartialOdometerAffineTranslate h u au 0
        ((huOdo.domain : Set GaussianInt) = FootprintVertices (TileTranslation T u)) → ((P.tile
            (owner m) = TileTranslation T u) → ((∀ (i : Fin 4), ∀ (y : GaussianInt), (y = sector
            i ∨ y = sector i + 1 ∨ y = sector i + ⟨0, 1⟩ ∨ y = sector i + 1 + ⟨0, 1⟩) → (y ∈
            FootprintVertices (P.tile (owner i)))) → ((∀ i : Fin 4, x = sector i ∨ x = sector i +
            1 ∨ x = sector i + ⟨0, 1⟩ ∨ x = sector i + 1 + ⟨0, 1⟩) → (x ∈ huOdo.domain)))) ) := by
  classical
  intro C T h x P a0 a1 a2 a3 owner m sector u au huOdo hdomu tileM cellVertex sectorCornerX
  have hxv := cellVertex m x (sectorCornerX m)
  have hxv' : x ∈ FootprintVertices (TileTranslation T u) := by
    simpa [tileM] using hxv
  exact (Set.ext_iff.mp hdomu x).mpr hxv'

private theorem hxW :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (x : GaussianInt), ∀ (P
            : PeriodicTileComplex ↥(TilingLattice C)), ∀ (a0 : ↥(TilingLattice C)), ∀ (a1 :
            ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀ (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (w : Fin (4 : ℕ)),
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        let u' : GaussianInt := owner w
        ∀ (au' : GaussianInt),
        let hu'Odo : PartialOdometer := PartialOdometerAffineTranslate h u' au' 0
        ((hu'Odo.domain : Set GaussianInt) = FootprintVertices (TileTranslation T u')) → ((P.tile
            (owner w) = TileTranslation T u') → ((∀ (i : Fin 4), ∀ (y : GaussianInt), (y = sector
            i ∨ y = sector i + 1 ∨ y = sector i + ⟨0, 1⟩ ∨ y = sector i + 1 + ⟨0, 1⟩) → (y ∈
            FootprintVertices (P.tile (owner i)))) → ((∀ i : Fin 4, x = sector i ∨ x = sector i +
            1 ∨ x = sector i + ⟨0, 1⟩ ∨ x = sector i + 1 + ⟨0, 1⟩) → (x ∈ hu'Odo.domain)))) ) := by
  classical
  intro C T h x P a0 a1 a2 a3 owner w sector u' au' hu'Odo hdomu' tileW cellVertex sectorCornerX
  have hxv := cellVertex w x (sectorCornerX w)
  have hxv' : x ∈ FootprintVertices (TileTranslation T u') := by
    simpa [tileW] using hxv
  exact (Set.ext_iff.mp hdomu' x).mpr hxv'

private theorem hstar :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (x : GaussianInt), ∀ (v
            : GaussianInt), ∀ (hv : v ∈ TilingLattice C), (x ∈ BoundaryFootprintVertices
            (TileTranslation T v)) → (∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
        let iv : TilingLattice C := ⟨v, hv⟩
        (x ∈ BoundaryFootprintVertices (P.tile iv)) → ((∃ y ∈ (P.tile iv).cells, y = x ∨ y = x -
            1 ∨ y = x - 1 - ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) → ((∃ y, y ∉ (P.tile iv).cells ∧ (y = x ∨ y
            = x - 1 ∨ y = x - 1 - ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩)) → (∀ (a0 : ↥(TilingLattice C)), (x ∈
            (P.tile a0).cells) → ((∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x
            ∈ (P.tile a).cells) y → y = a0) → (∀ (a1 : ↥(TilingLattice C)), (x - (1 :
            LatticeCell) ∈ (P.tile a1).cells) → ((∀ (y : ↥(TilingLattice C)), (fun (a :
            ↥(TilingLattice C)) => x - (1 : LatticeCell) ∈ (P.tile a).cells) y → y = a1) → (∀ (a2
            : ↥(TilingLattice C)), (x - (1 : LatticeCell) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈
            (P.tile a2).cells) → ((∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x
            - (1 : LatticeCell) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a).cells) y → y =
            a2) → (∀ (a3 : ↥(TilingLattice C)), (x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile
            a3).cells) → ((∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x - (⟨(0
            : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a).cells) y → y = a3) → (
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)),
        let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
        ∀ (e : Fin (4 : ℕ)),
        let sector : Fin 4 → GaussianInt :=
          ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
        let edge : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ i, sector i ∈ (P.tile (owner i)).cells) → ((∀ (i : Fin 4), ∀ (j : Fin 4), (owner i ≠
            owner j) → (sector j ∉ (P.tile (owner i)).cells)) → ((∀ (i : Fin 4), (owner i ≠ owner
            (next i)) → (edge i ∈ BoundaryFootprintEdges (P.tile (owner i)) ∧ edge i ∈
            BoundaryFootprintEdges (P.tile (owner (next i))))) → ((edge e ∈
            BoundaryFootprintEdges (P.tile (owner e))) → ((edge e ∈ BoundaryFootprintEdges
            (P.tile (owner (next e)))) → (
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        ∀ (au : GaussianInt), ∀ (au' : GaussianInt),
        let huOdo : PartialOdometer := PartialOdometerAffineTranslate h u au 0
        let hu'Odo : PartialOdometer := PartialOdometerAffineTranslate h u' au' 0
        (∀ (i : Fin 4), ∀ (y : GaussianInt), (y = sector i ∨ y = sector i + 1 ∨ y = sector i +
            ⟨0, 1⟩ ∨ y = sector i + 1 + ⟨0, 1⟩) → (y ∈ FootprintVertices (P.tile (owner i)))) →
            ((∀ i : Fin 4, x = sector i ∨ x = sector i + 1 ∨ x = sector i + ⟨0, 1⟩ ∨ x = sector i
            + 1 + ⟨0, 1⟩) → ((∀ (i : Fin 4), ∀ (j : Fin 4), (i ≠ j) → (owner i = owner m ∨ owner
            i = owner w ∨ owner j = owner m ∨ owner j = owner w)) → ((∀ (y : GaussianInt), (y ∈
            FootprintVertices (P.tile (owner m)) ∨ y ∈ FootprintVertices (P.tile (owner w))) → (y
            ∈ huOdo.domain ∨ y ∈ hu'Odo.domain)) → ((x ∈ huOdo.domain) → ((x ∈ hu'Odo.domain) →
            (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈
            huOdo.domain ∨ y ∈ hu'Odo.domain))))))))))))))))))))))) ) := by
  classical
  intro C T h x v hv hx P iv hxi hcorner hcornerOutside a0 ha0 hu0 a1 ha1 hu1 a2 ha2 hu2 a3 ha3
      hu3 owner m w next e sector edge hsector hsectorNot hedgeBoundary edge_mem_e edge_mem_next
      u u' au au' huOdo hu'Odo cellVertex sectorCornerX pairCovered toDomains hxM hxW y hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hxM
  · have hpair : x + 1 ∈ FootprintVertices (P.tile (owner m)) ∨
        x + 1 ∈ FootprintVertices (P.tile (owner w)) := by
      rcases pairCovered 0 3 (by decide) with h0 | h0 | h3 | h3
      · exact Or.inl (by simpa [h0] using
          (cellVertex 0 (x + 1) (Or.inr (Or.inl (by simp [sector])))))
      · exact Or.inr (by simpa [h0] using
          (cellVertex 0 (x + 1) (Or.inr (Or.inl (by simp [sector])))))
      · exact Or.inl (by simpa [h3] using
          (cellVertex 3 (x + 1) (Or.inr (Or.inr (Or.inr
            (by simp [sector]; abel))))))
      · exact Or.inr (by simpa [h3] using
          (cellVertex 3 (x + 1) (Or.inr (Or.inr (Or.inr
            (by simp [sector]; abel))))))
    exact toDomains (x + 1) hpair
  · have hpair : x - 1 ∈ FootprintVertices (P.tile (owner m)) ∨
        x - 1 ∈ FootprintVertices (P.tile (owner w)) := by
      rcases pairCovered 1 2 (by decide) with h1 | h1 | h2 | h2
      · exact Or.inl (by simpa [h1] using
          (cellVertex 1 (x - 1) (Or.inl (by simp [sector]))) )
      · exact Or.inr (by simpa [h1] using
          (cellVertex 1 (x - 1) (Or.inl (by simp [sector]))) )
      · exact Or.inl (by simpa [h2] using
          (cellVertex 2 (x - 1) (Or.inr (Or.inr (Or.inl
            (by simp [sector] ))))) )
      · exact Or.inr (by simpa [h2] using
          (cellVertex 2 (x - 1) (Or.inr (Or.inr (Or.inl
            (by simp [sector] ))))) )
    exact toDomains (x - 1) hpair
  · have hpair : x + ⟨0, 1⟩ ∈ FootprintVertices (P.tile (owner m)) ∨
        x + ⟨0, 1⟩ ∈ FootprintVertices (P.tile (owner w)) := by
      rcases pairCovered 0 1 (by decide) with h0 | h0 | h1 | h1
      · exact Or.inl (by simpa [h0] using
          (cellVertex 0 (x + ⟨0, 1⟩)
            (Or.inr (Or.inr (Or.inl (by simp [sector]))))) )
      · exact Or.inr (by simpa [h0] using
          (cellVertex 0 (x + ⟨0, 1⟩)
            (Or.inr (Or.inr (Or.inl (by simp [sector]))))) )
      · exact Or.inl (by simpa [h1] using
          (cellVertex 1 (x + ⟨0, 1⟩)
            (Or.inr (Or.inr (Or.inr (by simp [sector] ))))) )
      · exact Or.inr (by simpa [h1] using
          (cellVertex 1 (x + ⟨0, 1⟩)
            (Or.inr (Or.inr (Or.inr (by simp [sector] ))))) )
    exact toDomains (x + ⟨0, 1⟩) hpair
  · have hpair : x - ⟨0, 1⟩ ∈ FootprintVertices (P.tile (owner m)) ∨
        x - ⟨0, 1⟩ ∈ FootprintVertices (P.tile (owner w)) := by
      rcases pairCovered 2 3 (by decide) with h2 | h2 | h3 | h3
      · exact Or.inl (by simpa [h2] using
          (cellVertex 2 (x - ⟨0, 1⟩)
            (Or.inr (Or.inl (by simp [sector]; abel)))) )
      · exact Or.inr (by simpa [h2] using
          (cellVertex 2 (x - ⟨0, 1⟩)
            (Or.inr (Or.inl (by simp [sector]; abel)))) )
      · exact Or.inl (by simpa [h3] using
          (cellVertex 3 (x - ⟨0, 1⟩) (Or.inl (by simp [sector]))) )
      · exact Or.inr (by simpa [h3] using
          (cellVertex 3 (x - ⟨0, 1⟩) (Or.inl (by simp [sector]))) )
    exact toDomains (x - ⟨0, 1⟩) hpair

private theorem hadjOdo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), (q (0 : Fin (4 : ℕ)) = C.1.1) → ((ProperBandQuadruple q) → (∀ (a0
            : ↥(TilingLattice C)), ∀ (a1 : ↥(TilingLattice C)), ∀ (a2 : ↥(TilingLattice C)), ∀
            (a3 : ↥(TilingLattice C)),
        let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
        ∀ (m : Fin (4 : ℕ)), ∀ (w : Fin (4 : ℕ)), ∀ (j : Fin (3 : ℕ)), ((↑(owner w) :
            GaussianInt) - (↑(owner m) : GaussianInt) = BandVectors.1 (q j.succ) (q (0 : Fin (4 :
            ℕ))) ∨ (↑(owner w) : GaussianInt) - (↑(owner m) : GaussianInt) = -BandVectors.1 (q
            j.succ) (q (0 : Fin (4 : ℕ)))) → (∀ (p : ℝ × ℝ),
        let u : GaussianInt := owner m
        let u' : GaussianInt := owner w
        ∀ (au : GaussianInt), ∀ (au' : GaussianInt),
        let huOdo : PartialOdometer := PartialOdometerAffineTranslate h u au 0
        let hu'Odo : PartialOdometer := PartialOdometerAffineTranslate h u' au' 0
        (TileOdometer C.1.1 (TileTranslation T u) huOdo) → ((TileOdometer C.1.1 (TileTranslation
            T u') hu'Odo) → ((TileCentroid (TileTranslation T u') - TileCentroid (TileTranslation
            T u) = GaussianRealPoint (u' - u)) → (((u' - u = BandVectors.1 (q j.succ) (q 0)) →
            (au' - au = BandVectors.2 (q j.succ) (q 0))) → (((u' - u = -BandVectors.1 (q j.succ)
            (q 0)) → (au' - au = -BandVectors.2 (q j.succ) (q 0))) → ((PartialOdometerSlope huOdo
            = some (p.1 + (au.re : ℝ), p.2 + (au.im : ℝ))) → ((PartialOdometerSlope hu'Odo = some
            (p.1 + (au'.re : ℝ), p.2 + (au'.im : ℝ))) → (LeftLatticeAdjacent C (TileTranslation T
            u) (TileTranslation T u') huOdo hu'Odo)))))))))) ) := by
  classical
  intro C T h q hqC hproper a0 a1 a2 a3 owner m w j hsign p u u' au au' huOdo hu'Odo htransOdo
      htrans'Odo hcentDiff aDiffPlus aDiffMinus hslopeU hslopeU'
  refine ⟨htransOdo, htrans'Odo, ?_⟩
  refine ⟨(p.1 + (au.re : ℝ), p.2 + (au.im : ℝ)),
    (p.1 + (au'.re : ℝ), p.2 + (au'.im : ℝ)), hslopeU, hslopeU', ?_⟩
  rcases hsign with hplus | hminus
  · right
    refine ⟨q, j, true, hproper, hqC, ?_, ?_, ?_⟩
    · have hstep' : u' - u = BandVectors.1 (q j.succ) (q 0) := by
        simpa [u, u'] using hplus
      rw [hstep'] at hcentDiff
      simpa [GaussianRealPoint] using hcentDiff
    · have ha := aDiffPlus (by simpa [u, u'] using hplus)
      have hre : au'.re - au.re =
          (BandVectors.2 (q j.succ) (q 0)).re := by
        have hh := congrArg Zsqrtd.re ha
        simpa using hh
      dsimp
      have hr : (p.1 + (au'.re : ℝ)) - (p.1 + (au.re : ℝ)) =
          ((BandVectors.2 (q j.succ) (q 0)).re : ℝ) := by
        have hreal : (au'.re : ℝ) - (au.re : ℝ) =
            ((BandVectors.2 (q j.succ) (q 0)).re : ℝ) := by
          exact_mod_cast hre
        linarith
      simpa using hr
    · have ha := aDiffPlus (by simpa [u, u'] using hplus)
      have him : au'.im - au.im =
          (BandVectors.2 (q j.succ) (q 0)).im := by
        have hh := congrArg Zsqrtd.im ha
        simpa using hh
      dsimp
      have hr : (p.2 + (au'.im : ℝ)) - (p.2 + (au.im : ℝ)) =
          ((BandVectors.2 (q j.succ) (q 0)).im : ℝ) := by
        have hreal : (au'.im : ℝ) - (au.im : ℝ) =
            ((BandVectors.2 (q j.succ) (q 0)).im : ℝ) := by
          exact_mod_cast him
        linarith
      simpa using hr
  · right
    refine ⟨q, j, false, hproper, hqC, ?_, ?_, ?_⟩
    · have hstep' : u' - u = -BandVectors.1 (q j.succ) (q 0) := by
        simpa [u, u'] using hminus
      rw [hstep'] at hcentDiff
      simpa [GaussianRealPoint, smul_eq_mul] using hcentDiff
    · have ha := aDiffMinus (by simpa [u, u'] using hminus)
      have hre : au'.re - au.re =
          -(BandVectors.2 (q j.succ) (q 0)).re := by
        have hh := congrArg Zsqrtd.re ha
        simpa using hh
      dsimp
      have hr : (p.1 + (au'.re : ℝ)) - (p.1 + (au.re : ℝ)) =
          -((BandVectors.2 (q j.succ) (q 0)).re : ℝ) := by
        have hreal : (au'.re : ℝ) - (au.re : ℝ) =
            -((BandVectors.2 (q j.succ) (q 0)).re : ℝ) := by
          exact_mod_cast hre
        linarith
      simpa using hr
    · have ha := aDiffMinus (by simpa [u, u'] using hminus)
      have him : au'.im - au.im =
          -(BandVectors.2 (q j.succ) (q 0)).im := by
        have hh := congrArg Zsqrtd.im ha
        simpa using hh
      dsimp
      have hr : (p.2 + (au'.im : ℝ)) - (p.2 + (au.im : ℝ)) =
          -((BandVectors.2 (q j.succ) (q 0)).im : ℝ) := by
        have hreal : (au'.im : ℝ) - (au.im : ℝ) =
            -((BandVectors.2 (q j.succ) (q 0)).im : ℝ) := by
          exact_mod_cast him
        linarith
      simpa using hr

private theorem hnoCheckerboard0 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), (x ∈ (P.tile a0).cells) → (∀ (a1 : ↥(TilingLattice C)),
            (∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x - (1 : LatticeCell) ∈
            (P.tile a).cells) y → y = a1) → (∀ (a2 : ↥(TilingLattice C)), (x - (1 : LatticeCell)
            - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a2).cells) → (∀ (a3 : ↥(TilingLattice
            C)), (∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x - (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∈ (P.tile a).cells) y → y = a3) → (a0 = a2 → a0 = a1 ∨ a0 =
            a3)))) ) := by
  classical
  intro C x P a0 ha0 a1 hu1 a2 ha2 a3 hu3 h02
  by_cases h01 : a0 = a1
  · exact Or.inl h01
  by_cases h03 : a0 = a3
  · exact Or.inr h03
  have hx1 : x - 1 ∉ (P.tile a0).cells := by
    intro hx1
    exact h01 (hu1 a0 hx1)
  have hx3 : x - ⟨0, 1⟩ ∉ (P.tile a0).cells := by
    intro hx3
    exact h03 (hu3 a0 hx3)
  have hnc := (LatticeTileGridStructure (P.tile a0)
    (P.tiles_are_disks a0)).2.1
  exact (hnc x (Or.inl ⟨ha0, by simpa [h02] using ha2, hx1, hx3⟩)).elim

private theorem hnoCheckerboard1 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), (∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice
            C)) => x ∈ (P.tile a).cells) y → y = a0) → (∀ (a1 : ↥(TilingLattice C)), (x - (1 :
            LatticeCell) ∈ (P.tile a1).cells) → (∀ (a2 : ↥(TilingLattice C)), (∀ (y :
            ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x - (1 : LatticeCell) - (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a).cells) y → y = a2) → (∀ (a3 :
            ↥(TilingLattice C)), (x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a3).cells) →
            (a1 = a3 → a1 = a0 ∨ a1 = a2)))) ) := by
  classical
  intro C x P a0 hu0 a1 ha1 a2 hu2 a3 ha3 h13
  by_cases h10 : a1 = a0
  · exact Or.inl h10
  by_cases h12 : a1 = a2
  · exact Or.inr h12
  have hx0 : x ∉ (P.tile a1).cells := by
    intro hx0
    exact h10 (hu0 a1 hx0)
  have hx2 : x - 1 - ⟨0, 1⟩ ∉ (P.tile a1).cells := by
    intro hx2
    exact h12 (hu2 a1 hx2)
  have hnc := (LatticeTileGridStructure (P.tile a1)
    (P.tiles_are_disks a1)).2.1
  exact (hnc x (Or.inr ⟨ha1, by simpa [h13] using ha3, hx0, hx2⟩)).elim

private theorem hnoCheckerboard2 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), (x ∈ (P.tile a0).cells) → (∀ (a1 : ↥(TilingLattice C)),
            (∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x - (1 : LatticeCell) ∈
            (P.tile a).cells) y → y = a1) → (∀ (a2 : ↥(TilingLattice C)), (x - (1 : LatticeCell)
            - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a2).cells) → (∀ (a3 : ↥(TilingLattice
            C)), (∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x - (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∈ (P.tile a).cells) y → y = a3) → (a2 = a0 → a2 = a1 ∨ a2 =
            a3)))) ) := by
  classical
  intro C x P a0 ha0 a1 hu1 a2 ha2 a3 hu3 h20
  by_cases h21 : a2 = a1
  · exact Or.inl h21
  by_cases h23 : a2 = a3
  · exact Or.inr h23
  have hx1 : x - 1 ∉ (P.tile a2).cells := by
    intro hx1
    exact h21 (hu1 a2 hx1)
  have hx3 : x - ⟨0, 1⟩ ∉ (P.tile a2).cells := by
    intro hx3
    exact h23 (hu3 a2 hx3)
  have hnc := (LatticeTileGridStructure (P.tile a2)
    (P.tiles_are_disks a2)).2.1
  exact (hnc x (Or.inl ⟨by simpa [h20] using ha0, ha2, hx1, hx3⟩)).elim

private theorem hnoCheckerboard3 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            ∀ (a0 : ↥(TilingLattice C)), (∀ (y : ↥(TilingLattice C)), (fun (a : ↥(TilingLattice
            C)) => x ∈ (P.tile a).cells) y → y = a0) → (∀ (a1 : ↥(TilingLattice C)), (x - (1 :
            LatticeCell) ∈ (P.tile a1).cells) → (∀ (a2 : ↥(TilingLattice C)), (∀ (y :
            ↥(TilingLattice C)), (fun (a : ↥(TilingLattice C)) => x - (1 : LatticeCell) - (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a).cells) y → y = a2) → (∀ (a3 :
            ↥(TilingLattice C)), (x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ (P.tile a3).cells) →
            (a3 = a1 → a3 = a0 ∨ a3 = a2)))) ) := by
  classical
  intro C x P a0 hu0 a1 ha1 a2 hu2 a3 ha3 h31
  by_cases h30 : a3 = a0
  · exact Or.inl h30
  by_cases h32 : a3 = a2
  · exact Or.inr h32
  have hx0 : x ∉ (P.tile a3).cells := by
    intro hx0
    exact h30 (hu0 a3 hx0)
  have hx2 : x - 1 - ⟨0, 1⟩ ∉ (P.tile a3).cells := by
    intro hx2
    exact h32 (hu2 a3 hx2)
  have hnc := (LatticeTileGridStructure (P.tile a3)
    (P.tiles_are_disks a3)).2.1
  exact (hnc x (Or.inr ⟨by simpa [h31] using ha1, ha3, hx0, hx2⟩)).elim

end WebLaplacianGeometry

theorem PeriodicBoundaryWebLaplacian (C : BandCircle)
    (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hT : BandPrototile C.1.1 T) (hodo : TileOdometer C.1.1 T h)
    (hext : GlobalOdometerExtends g h)
    (hcocycle : ∀ v, v ∈ TilingLattice C → ∃ a : GaussianInt,
      Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
        ![(a.re : ℝ), (a.im : ℝ)] ∧
      ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v) :
    ∀ x, (∃ v, v ∈ TilingLattice C ∧
      x ∈ BoundaryFootprintVertices (TileTranslation T v)) →
      FourNeighborLaplacian g x = 1 := by
-- BODY
  classical
  intro x
  rintro ⟨v, hv, hx⟩
  by_cases hc : C.1.1.1 = 1
  · have hunit := WebLaplacianGeometry.hunit C g hcocycle hc
    exact hunit x
  · obtain ⟨q, hsemi, hqC, hless, _⟩ := Or.resolve_left (BandGenealogy C) hc
    have hproper := WebLaplacianGeometry.hproper C q hsemi hqC hless
    have hT' : BandPrototile (q 0) T := by simpa [hqC] using hT
    obtain ⟨P, hPlat, hPtile, hPadj, hPposition, hPvertices,
        hPedges, hPfaces, hPchart⟩ :=
      BandRegularTranslatePeriodicComplex C q hproper hqC T hT'
    obtain ⟨chart⟩ := hPchart
    let tileAt := fun mn : Int × Int =>
      TileTranslation T
        ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0))
    let iv : TilingLattice C := ⟨v, hv⟩
    have hPv : P.tile iv = TileTranslation T v := by simpa [iv] using hPtile iv
    have hxi : x ∈ BoundaryFootprintVertices (P.tile iv) := by
      simpa [hPv] using hx
    have hcells := WebLaplacianGeometry.hcells C v hv P
    have hcorner := WebLaplacianGeometry.hcorner C T x v hv hx P hxi hcells
    have hcornerOutside := WebLaplacianGeometry.hcornerOutside C T x v hv hx P hxi hcells hcorner
    obtain ⟨a0, ha0, hu0⟩ := PeriodicTileIndexedMultiplicityOne P x
    obtain ⟨a1, ha1, hu1⟩ := PeriodicTileIndexedMultiplicityOne P (x - 1)
    obtain ⟨a2, ha2, hu2⟩ :=
      PeriodicTileIndexedMultiplicityOne P (x - 1 - ⟨0, 1⟩)
    obtain ⟨a3, ha3, hu3⟩ := PeriodicTileIndexedMultiplicityOne P (x - ⟨0, 1⟩)
    have hvnotfour := WebLaplacianGeometry.hvnotfour C x v hv P hcornerOutside
        a0 ha0 a1 ha1 a2 ha2 a3 ha3
    have hfour := AffineTriangularNoFourfoldCellOwners P tileAt chart x
      a0 a1 a2 a3 ha0 ha1 ha2 ha3
    have secondOwnerCoversThree {I : Type} (f : Fin 4 → I)
        (m : Fin 4) (hother : ∃ w, f w ≠ f m)
        (hnotinj : ¬ Function.Injective f) := WebLaplacianGeometry.secondOwnerCoversThree
            (WebLaplacianGeometry.atMostOneRemaining) (I := I) f m hother hnotinj
    let owner : Fin 4 → TilingLattice C := ![a0, a1, a2, a3]
    have hmexists := WebLaplacianGeometry.hmexists C v hv a0 a1 a2 a3
        (WebLaplacianGeometry.hvowner C x v hv P hcorner a0 hu0 a1 hu1 a2 hu2 a3 hu3)
    obtain ⟨m, hm⟩ := hmexists
    have hnotinj := WebLaplacianGeometry.hnotinj C a0 a1 a2 a3 hfour
    have hother := WebLaplacianGeometry.hother C v hv a0 a1 a2 a3 m hm
        (WebLaplacianGeometry.hnotall C v hv a0 a1 a2 a3 hvnotfour)
    obtain ⟨w, hmw, hcover⟩ := secondOwnerCoversThree owner m hother hnotinj
    let next : Fin 4 → Fin 4 := ![1, 2, 3, 0]
    have colorCycle := WebLaplacianGeometry.colorCycle
    let col : Fin 4 → Fin 3 := fun i =>
      if owner i = owner m then 0 else if owner i = owner w then 1 else 2
    have hmcol : col m = 0 := by simp [col]
    have hwcol : col w = 1 := by simp [col, hmw]
    have hcol2unique := WebLaplacianGeometry.hcol2unique C a0 a1 a2 a3 m w hmw hcover
    obtain ⟨e, hecolor⟩ := colorCycle col ⟨m, hmcol⟩ ⟨w, hwcol⟩ hcol2unique
    have hepair := WebLaplacianGeometry.hepair C a0 a1 a2 a3 m w e hecolor
    let sector : Fin 4 → GaussianInt :=
      ![x, x - 1, x - 1 - ⟨0, 1⟩, x - ⟨0, 1⟩]
    let edge : Fin 4 → Finset GaussianInt :=
      ![{x, x + ⟨0, 1⟩}, {x - 1, x},
        {x - ⟨0, 1⟩, x}, {x, x + 1}]
    have hsector := WebLaplacianGeometry.hsector C x P a0 ha0 a1 ha1 a2 ha2 a3 ha3
    have hsectorNot := WebLaplacianGeometry.hsectorNot C x P a0 a1 a2 a3 hsector
    have hedgeBoundary := WebLaplacianGeometry.hedgeBoundary C x P a0 ha0 a1 ha1 a2 ha2 a3 ha3
        hsectorNot
    have boundaryEdge := WebLaplacianGeometry.boundaryEdge
    have hneq : owner m ≠ owner w := hmw.symm
    have hnewe := WebLaplacianGeometry.hnewe C a0 a1 a2 a3 m w hmw e hepair
    obtain ⟨edge_mem_e, edge_mem_next⟩ := hedgeBoundary e hnewe
    have hdisplacement := (hPadj (owner m) (owner w)).mp (WebLaplacianGeometry.hadj C P a0 a1 a2
        a3 m w hneq (WebLaplacianGeometry.hcommon C x P a0 a1 a2 a3 m w e hepair boundaryEdge
        edge_mem_e edge_mem_next))
    obtain ⟨j, hsign⟩ := hdisplacement
    have slope_for := WebLaplacianGeometry.slope_for C P a0 a1 a2 a3 m w
    have hcurvature := WebLaplacianGeometry.hcurvature C hc P a0 a1 a2 a3 m w e hecolor
    obtain ⟨p, hp⟩ := slope_for C.1.1 T h hodo hcurvature
    let u : GaussianInt := owner m
    let u' : GaussianInt := owner w
    have hu_eq := WebLaplacianGeometry.hu_eq C v hv a0 a1 a2 a3 m hm
    have hu_mem : u ∈ TilingLattice C := (owner m).property
    have hu'_mem : u' ∈ TilingLattice C := (owner w).property
    obtain ⟨au, hAu, hshiftu⟩ := hcocycle u hu_mem
    obtain ⟨au', hAu', hshiftu'⟩ := hcocycle u' hu'_mem
    let huOdo : PartialOdometer := PartialOdometerAffineTranslate h u au 0
    let hu'Odo : PartialOdometer := PartialOdometerAffineTranslate h u' au' 0
    have htransOdo : TileOdometer C.1.1 (TileTranslation T u) huOdo :=
      TileOdometerAffineTranslation C.1.1 T h u au 0 hodo
    have htrans'Odo : TileOdometer C.1.1 (TileTranslation T u') hu'Odo :=
      TileOdometerAffineTranslation C.1.1 T h u' au' 0 hodo
    have hdom : (h.domain : Set GaussianInt) = FootprintVertices T :=
      PositiveCurvatureTileOdometerDomain C.1.1 T h (by omega) hodo
    have hdomu : (huOdo.domain : Set GaussianInt) =
        FootprintVertices (TileTranslation T u) :=
      (PartialOdometerAffineTranslateFormulas h u au 0).2.2.2.2.1 T hdom
    have hdomu' : (hu'Odo.domain : Set GaussianInt) =
        FootprintVertices (TileTranslation T u') :=
      (PartialOdometerAffineTranslateFormulas h u' au' 0).2.2.2.2.1 T hdom
    have translateExtends (t a : GaussianInt)
        (hshift : ∀ y, g (y + t) = g y + y.re * a.re + y.im * a.im + g t) :
        GlobalOdometerExtends g (PartialOdometerAffineTranslate h t a 0) :=
            WebLaplacianGeometry.translateExtends h g hext t a hshift
    have hextu : GlobalOdometerExtends g huOdo := by
      simpa [huOdo] using translateExtends u au hshiftu
    have hextu' : GlobalOdometerExtends g hu'Odo := by
      simpa [hu'Odo] using translateExtends u' au' hshiftu'
    have hmatrixDiff := WebLaplacianGeometry.hmatrixDiff C a0 a1 a2 a3 m w au hAu au' hAu'
    have hincoming := CircleMatrixIncomingVector C q hsemi hqC j
    have hAdiff := WebLaplacianGeometry.hAdiff C q a0 a1 a2 a3 m w j hsign au au' hmatrixDiff
        hincoming
    have tileM : P.tile (owner m) = TileTranslation T u := by
      simpa [u] using hPtile (owner m)
    have tileW : P.tile (owner w) = TileTranslation T u' := by
      simpa [u'] using hPtile (owner w)
    have ownerNonempty (i : Fin 4) : (P.tile (owner i)).cells.Nonempty :=
      (LatticeTileGridStructure _ (P.tiles_are_disks (owner i))).1.1
    have cellVertex := WebLaplacianGeometry.cellVertex C x P a0 a1 a2 a3 hsector ownerNonempty
    have sectorCornerX := WebLaplacianGeometry.sectorCornerX x
    have hxM := WebLaplacianGeometry.hxM C T h x P a0 a1 a2 a3 m au hdomu tileM cellVertex
        sectorCornerX
    have hxW := WebLaplacianGeometry.hxW C T h x P a0 a1 a2 a3 w au' hdomu' tileW cellVertex
        sectorCornerX
    have hadjOdo := WebLaplacianGeometry.hadjOdo C T h q hqC hproper a0 a1 a2 a3 m w j hsign p au
        au' htransOdo htrans'Odo (WebLaplacianGeometry.hcentDiff C T a0 a1 a2 a3 m w
        (WebLaplacianGeometry.centroidShift T)) (WebLaplacianGeometry.aDiffPlus C q a0 a1 a2 a3 m
        w j au au' hmatrixDiff hincoming) (WebLaplacianGeometry.aDiffMinus C q a0 a1 a2 a3 m w j
        au au' hmatrixDiff hincoming) (WebLaplacianGeometry.hslopeU C h a0 a1 a2 a3 m p hp au)
        (WebLaplacianGeometry.hslopeU' C h a0 a1 a2 a3 w p hp au')
    have hnoCheckerboard0 := WebLaplacianGeometry.hnoCheckerboard0 C x P a0 ha0 a1 hu1 a2 ha2 a3 hu3
    have hnoCheckerboard1 := WebLaplacianGeometry.hnoCheckerboard1 C x P a0 hu0 a1 ha1 a2 hu2 a3 ha3
    have hnoCheckerboard2 := WebLaplacianGeometry.hnoCheckerboard2 C x P a0 ha0 a1 hu1 a2 ha2 a3 hu3
    have hnoCheckerboard3 := WebLaplacianGeometry.hnoCheckerboard3 C x P a0 hu0 a1 ha1 a2 hu2 a3 ha3
    have hcompat : OdometerCompatibility huOdo hu'Odo :=
      (LeftAdjacentOdometerCompatibility C (TileTranslation T u)
        (TileTranslation T u') huOdo hu'Odo hadjOdo).1
    have hweb := (OdometerWeb).1 C (TileTranslation T u)
      (TileTranslation T u') huOdo hu'Odo g x hcompat hextu hextu' hxM hxW
          (WebLaplacianGeometry.hstar C T h x v hv hx P hxi hcorner hcornerOutside a0 ha0 hu0 a1
          ha1 hu1 a2 ha2 hu2 a3 ha3 hu3 m w e hsector hsectorNot hedgeBoundary edge_mem_e
          edge_mem_next au au' cellVertex sectorCornerX (WebLaplacianGeometry.pairCovered C a0 a1
          a2 a3 m w hcover) (WebLaplacianGeometry.toDomains C T h P a0 a1 a2 a3 m w au au' hdomu
          hdomu' tileM tileW) hxM hxW)
    exact hweb.1 hadjOdo

end ApollonianSuperharmonic

end

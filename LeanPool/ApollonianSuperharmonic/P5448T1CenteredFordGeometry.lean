/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5472T1FordNormalization
public import LeanPool.ApollonianSuperharmonic.P5472T1CyclicPhaseCovariance
public import LeanPool.ApollonianSuperharmonic.P5472T1LiteralFordPlacement
public import LeanPool.ApollonianSuperharmonic.P5472T1FordSlopeDifference
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryGlobalOdometerTransport

-- [TABLET NODE: P5448T1CenteredFordGeometry]

/-!
# P5448T1CenteredFordGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5448T1CenteredFordGeometry
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (h : PartialOdometer)
    (P : Fin 3 → Bool → ProtoTile)
    (r : Fin 3 → Bool → PartialOdometer)
    (Q S : Fin 3 → Bool → ProtoTile)
    (u v : Fin 3 → Bool → PartialOdometer)
    (g : IntegerLatticeFunction) (x : GaussianInt)
    (data : BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g)
    (hext : GlobalOdometerExtends g h)
    (hcenter : GaussianRealPoint x = TileCentroid T)
    (hzero : (cfg.firstPredecessor 1).1 = 0) :
    ∃ (F : FordFareyParameter) (s : BandPackingSymmetry) (delta : Bool)
        (f : IntegerLatticeFunction),
      let c := BandPackingSymmetryVectorAction s x
      let H := PartialOdometerAffineTranslate
        (BandPackingSymmetryPartialOdometerAction s h) (-c) 0 0
      let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
      let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
      let hp := PartialOdometerAffineTranslate
        (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
      let hm := PartialOdometerAffineTranslate
        (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
      1 < F.q ∧
      BandPackingSymmetryReversesOrientation s = false ∧
      BandPackingSymmetryScopedPhase s q delta ∧
      BandPackingSymmetryQuadrupleAction s
        ![cfg.firstPredecessor 0, cfg.firstPredecessor 2,
          cfg.firstPredecessor 3, cfg.firstPredecessor 1] =
        FordRecursiveQuadruple F ∧
      U.cells = (TileTranslation (FordTile F.q) ⟨-(F.q₁ : Int), 0⟩).cells ∧
      V.cells = (TileTranslation (FordTile F.q) ⟨-(F.q₂ : Int), -(F.q : Int)⟩).cells ∧
      TileOdometer (FordCircleCoordinate F.p F.q) U hp ∧
      TileOdometer (FordCircleCoordinate F.p F.q) V hm ∧
      (∀ z : GaussianInt, z ∈ hp.domain ↔
        -(F.q₁ : Int) ≤ z.re ∧ z.re ≤ F.q₂ ∧ 0 ≤ z.im ∧ z.im ≤ F.q) ∧
      (∀ z : GaussianInt, z ∈ hm.domain ↔
        -(F.q₂ : Int) ≤ z.re ∧ z.re ≤ F.q₁ ∧ -(F.q : Int) ≤ z.im ∧ z.im ≤ 0) ∧
      (∃ sp sm : Real × Real,
        PartialOdometerSlope hp = some sp ∧ PartialOdometerSlope hm = some sm ∧
        sm.1 - sp.1 = -(F.p : Real) ∧ sm.2 - sp.2 = (F.p₁ : Real) - F.p₂) ∧
      (∀ z, z ∈ hp.domain → z ∈ H.domain ∧ H.value z = hp.value z) ∧
      (∀ z, z ∈ hm.domain → z ∈ H.domain ∧ H.value z = hm.value z) ∧
      GlobalOdometerExtends f H ∧
      FourNeighborLaplacian f 0 = FourNeighborLaplacian g x := by
-- BODY
  obtain ⟨F, s, hFq, hrev, hword, hford, hrootCircle, hW, hA⟩ :=
    P5472T1FordNormalization q cfg hzero
  obtain ⟨delta, hphase, hcyclic⟩ :=
    P5472T1CyclicPhaseCovariance s q cfg.proper hrev hword
  have hplacement := P5472T1LiteralFordPlacement q cfg C0 T cert h P r Q S u v g x
    data hcenter F s delta hrev hword hphase hrootCircle hW
  have hslope := P5472T1FordSlopeDifference q cfg C0 T cert h P r Q S u v g x
    data F s delta hword hrootCircle hA (by
      dsimp only
      rw [hcyclic]
      split <;> rfl)
  let c := BandPackingSymmetryVectorAction s x
  let H := PartialOdometerAffineTranslate
    (BandPackingSymmetryPartialOdometerAction s h) (-c) 0 0
  let U := TileTranslation (BandPackingSymmetryTileAction s (P 0 (!delta))) (-c)
  let V := TileTranslation (BandPackingSymmetryTileAction s (P 0 delta)) (-c)
  let hp := PartialOdometerAffineTranslate
    (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
  let hm := PartialOdometerAffineTranslate
    (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
  obtain ⟨g', hext', hlap'⟩ :=
    BandPackingSymmetryGlobalOdometerTransport s g h x hext
  let f : IntegerLatticeFunction := fun z => g' (z + c)
  have hextH : GlobalOdometerExtends f H := by
    obtain ⟨K, hK⟩ := hext'
    refine ⟨K, ?_⟩
    intro z hz
    have hz' : z + c ∈
        (BandPackingSymmetryPartialOdometerAction s h).domain := by
      have hmem := (PartialOdometerAffineTranslateFormulas
        (BandPackingSymmetryPartialOdometerAction s h) (-c) 0 0).2.1 z
      have := hmem.mp hz
      simpa using this
    have hv := hK (z + c) hz'
    have hv' := (PartialOdometerAffineTranslateFormulas
      (BandPackingSymmetryPartialOdometerAction s h) (-c) 0 0).2.2.1 z hz
    change g' (z + c) = H.value z + K
    rw [hv, hv']
    simp [sub_neg_eq_add, zero_mul, Zsqrtd.re_zero, Zsqrtd.im_zero]
  have hlap : FourNeighborLaplacian f 0 = FourNeighborLaplacian g x := by
    have hh := hlap'
    change FourNeighborLaplacian g' c = FourNeighborLaplacian g x at hh
    simpa [f, FourNeighborLaplacian, c, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using hh
  have restrictShift (w : GaussianInt) (a b : PartialOdometer)
      (hd : ∀ z, z ∈ a.domain → z ∈ b.domain ∧ b.value z = a.value z) :
      ∀ z, z ∈ (BandPackingSymmetryPartialOdometerAction (.shift w) a).domain →
        z ∈ (BandPackingSymmetryPartialOdometerAction (.shift w) b).domain ∧
        (BandPackingSymmetryPartialOdometerAction (.shift w) b).value z =
          (BandPackingSymmetryPartialOdometerAction (.shift w) a).value z := by
    intro z hz
    change z ∈ a.domain at hz
    obtain ⟨hz', hv⟩ := hd z hz
    refine ⟨hz', ?_⟩
    simp only [BandPackingSymmetryPartialOdometerAction, ite_eq_left hz, ite_eq_left hz', hv]
  have restrictNegate (a b : PartialOdometer)
      (hd : ∀ z, z ∈ a.domain → z ∈ b.domain ∧ b.value z = a.value z) :
      ∀ z, z ∈ (BandPackingSymmetryPartialOdometerAction .negate a).domain →
        z ∈ (BandPackingSymmetryPartialOdometerAction .negate b).domain ∧
        (BandPackingSymmetryPartialOdometerAction .negate b).value z =
          (BandPackingSymmetryPartialOdometerAction .negate a).value z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    change GaussianQuarterTurn y ∈ a.domain.image GaussianQuarterTurn at hz
    obtain ⟨hy', hv⟩ := hd y hy
    have hz' : GaussianQuarterTurn y ∈ b.domain.image GaussianQuarterTurn :=
      Finset.mem_image.mpr ⟨y, hy', rfl⟩
    refine ⟨hz', ?_⟩
    have inv : -GaussianQuarterTurn (GaussianQuarterTurn y) = y := by
      ext <;> simp [GaussianQuarterTurn]
    simp only [BandPackingSymmetryPartialOdometerAction, ite_eq_left hz,
      ite_eq_left hz', inv, hv]
  have hrestriction (b : Bool) :
      ∀ z, z ∈ (PartialOdometerAffineTranslate
          (BandPackingSymmetryPartialOdometerAction s (r 0 b)) (-c) 0 0).domain →
        z ∈ H.domain ∧ H.value z =
          (PartialOdometerAffineTranslate
            (BandPackingSymmetryPartialOdometerAction s (r 0 b)) (-c) 0 0).value z := by
    have hd : ∀ z, z ∈ (r 0 b).domain → z ∈ h.domain ∧ h.value z = (r 0 b).value z := by
      intro z hz
      exact ⟨(data.hPdom z).mpr ⟨0, b, hz⟩, data.hPvalue 0 b z hz⟩
    have hd' : ∀ z, z ∈ (BandPackingSymmetryPartialOdometerAction s (r 0 b)).domain →
        z ∈ (BandPackingSymmetryPartialOdometerAction s h).domain ∧
        (BandPackingSymmetryPartialOdometerAction s h).value z =
          (BandPackingSymmetryPartialOdometerAction s (r 0 b)).value z := by
      rcases hword with ⟨w, hs | hs⟩
      · rw [hs]
        exact restrictShift w _ _ hd
      · rw [hs]
        exact restrictShift w _ _ (restrictNegate _ _ hd)
    intro z hz
    have hz0 := (PartialOdometerAffineTranslateFormulas _ (-c) 0 0).2.1 z |>.mp hz
    obtain ⟨hz1, hv⟩ := hd' (z - -c) hz0
    have hzH : z ∈ H.domain :=
      (PartialOdometerAffineTranslateFormulas _ (-c) 0 0).2.1 z |>.mpr hz1
    refine ⟨hzH, ?_⟩
    rw [(PartialOdometerAffineTranslateFormulas _ (-c) 0 0).2.2.1 z hzH,
      (PartialOdometerAffineTranslateFormulas _ (-c) 0 0).2.2.1 z hz, hv]
  refine ⟨F, s, delta, f, hFq, hrev, hphase, hford, ?_⟩
  exact ⟨hplacement.1, hplacement.2.1, hplacement.2.2.1,
    hplacement.2.2.2.1, hplacement.2.2.2.2.1, hplacement.2.2.2.2.2,
    hslope, hrestriction (!delta), hrestriction delta, hextH, hlap⟩

end ApollonianSuperharmonic

end

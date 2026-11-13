/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty

public import LeanPool.ApollonianSuperharmonic.AncestorOdometerCentralCovariance
public import LeanPool.ApollonianSuperharmonic.AncestorOdometerOuterSupportNormalization
public import LeanPool.ApollonianSuperharmonic.BoundaryStringOdometerRespect
public import LeanPool.ApollonianSuperharmonic.ForwardBoundaryStringData
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespectRegularFamilyCentralCovariance
public import LeanPool.ApollonianSuperharmonic.TileStringRegularFamilyCentralCovariance

-- [TABLET NODE: OpposingBoundaryOdometerStrings]

/-!
# OpposingBoundaryOdometerStrings

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OpposingBoundaryGeometry

private theorem horientationExists :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (ProperBandQuadruple q) → (∀ (Cᵢ : BandCircle), ∀ (i
            : Fin 3), (q i.succ = Cᵢ.1.1) → (∃ o : Bool, Cᵢ.1.1.1 = 1 → UnitOccurrenceOrientation
            q i o)) ) := by
  classical
  intro q hq Cᵢ i hCᵢ
  by_cases hc : Cᵢ.1.1.1 = 1
  · obtain ⟨o, ho⟩ := (UnitOccurrenceOrientationUnique.1 q hq i
      (by simpa only [hCᵢ] using hc)).exists
    exact ⟨o, fun _ => ho⟩
  · exact ⟨false, fun h => (hc h).elim⟩

private theorem hpouter_eq :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), ∀ (p₀ : Real × Real), (PartialOdometerSlope h₀ = some p₀) → (∀
            (pouter : ℝ × ℝ), (PartialOdometerSlope h₀ = some pouter) → (pouter = p₀)) ) := by
  classical
  intro h₀ p₀ hs₀ pouter hpouter
  have heq := hpouter.symm.trans hs₀
  exact Option.some.inj heq

private theorem htranslateZero :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile),
          TileTranslation Rminus (0 : GaussianInt) = Rminus) := by
  classical
  intro Rminus
  cases Rminus with
  | mk cs anchor =>
    have hfun : GaussianTranslation (0 : GaussianInt) = id := by
      funext z
      simp [GaussianTranslation]
    simp [TileTranslation, hfun]

private theorem hOminus :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), ∀ (Rminus :
            ProtoTile), ∀ (hseed : PartialOdometer), (TileOdometer Cᵢ.1.1 Rminus hseed) → (
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        (TileTranslation Rminus (0 : GaussianInt) = Rminus) → (TileOdometer Cᵢ.1.1 Rminus
            hminus)) ) := by
  classical
  intro q Cᵢ i Rminus hseed hseedO d hminus htranslateZero
  rw [← htranslateZero]
  exact TileOdometerAffineTranslation Cᵢ.1.1 Rminus hseed 0 d 0 hseedO

private theorem hsminus :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (hseed :
            PartialOdometer), ∀ (pseed : ℝ × ℝ), (PartialOdometerSlope hseed = some pseed) → (
        let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        (pseed + GaussianRealPoint d = pminus) → (PartialOdometerSlope hminus = some pminus)) )
            := by
  classical
  intro q i p₀ hseed pseed hseedSlope pminus d hminus hminusSlopeCalc
  have hs := (PartialOdometerAffineTranslateFormulas hseed 0 d 0).2.2.2.2.2
  rw [hs, hseedSlope]
  apply congrArg some
  apply Prod.ext
  · simpa [GaussianRealPoint, d] using congrArg Prod.fst hminusSlopeCalc
  · simpa [GaussianRealPoint, d] using congrArg Prod.snd hminusSlopeCalc

private theorem hC₀positive :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (ProperBandQuadruple q) → (∀ (C₀ : BandCircle), ∀ (Cᵢ
            : BandCircle), ∀ (i : Fin 3), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → ((q i.succ = Cᵢ.1.1) →
            (((0 : ℤ) < Cᵢ.1.1.1) → (0 < C₀.1.1.1)))) ) := by
  classical
  intro q hq C₀ Cᵢ i hC₀ hCᵢ hpositive
  have hlt := hq.2 i
  have hpos : 0 < (q i.succ).1 := by simpa only [hCᵢ] using hpositive
  rw [hC₀] at hlt
  omega

private theorem hbarO :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (h₀ : PartialOdometer), (TileOdometer C₀.1.1
            T₀ h₀) → (∀ (centerShift : GaussianInt),
        let hbar := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift 0 0
        let Tbar := TileTranslation (TileHalfTurn T₀) centerShift
        TileOdometer C₀.1.1 Tbar hbar) ) := by
  classical
  intro C₀ T₀ h₀ hO₀ centerShift hbar Tbar
  exact TileOdometerAffineTranslation C₀.1.1 (TileHalfTurn T₀)
    (PartialOdometerHalfTurn h₀) centerShift 0 0
    (TileOdometerCentralSymmetry C₀.1.1 T₀ h₀ hO₀).1

private theorem hsumCentroid :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (i : Fin
            3), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → ((q i.succ = Cᵢ.1.1) → (∀ (T₀ : ProtoTile), ∀
            (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), (q' (0 : Fin (4 : ℕ)) = C₀.1.1) → ((q' i.succ = Cᵢ.1.1) →
            ((TileCentroid Rminus - TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (q' i.succ) (q' (0 : Fin (4 : ℕ))) - BandVectors.1 (q' (0 : Fin (4 :
            ℕ))) (q' i.succ))) → ((TileCentroid Rplus - TileCentroid T₀ = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (q' i.succ) (q' (0 : Fin (4 : ℕ))) + BandVectors.1
            (q' (0 : Fin (4 : ℕ))) (q' i.succ))) → (TileCentroid Rminus + TileCentroid Rplus =
            TileCentroid T₀ + TileCentroid T₀ + GaussianRealPoint (BandVectors.1 (q i.succ) (q
            0)))))))) ) := by
  classical
  intro q C₀ Cᵢ i hC₀ hCᵢ T₀ Rminus Rplus q' hq0 hqi hcentroidMinus hcentroidPlus
  have hcm := hcentroidMinus
  have hcp := hcentroidPlus
  rw [hqi, hq0, ← hCᵢ, ← hC₀] at hcm hcp
  have hcmr := congrArg Prod.fst hcm
  have hcpr := congrArg Prod.fst hcp
  have hcmi := congrArg Prod.snd hcm
  have hcpi := congrArg Prod.snd hcp
  simp only [Prod.fst_sub, GaussianRealPoint,
    Prod.snd_sub] at hcmr hcpr hcmi hcpi
  norm_num [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
    Int.cast_sub, Int.cast_add] at hcmr hcpr hcmi hcpi
  apply Prod.ext
  · simp only [Prod.fst_add, GaussianRealPoint,
      GaussianInt.intCast_re] at ⊢
    linarith
  · simp only [Prod.snd_add, GaussianRealPoint,
      GaussianInt.intCast_im] at ⊢
    linarith

private theorem hcentbar :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (T₀' :
            ProtoTile), (TileCentroid T₀' - TileCentroid T₀ = GaussianRealPoint (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))))) → (∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀
            (centerShift : GaussianInt), (GaussianRealPoint centerShift = TileCentroid Rminus +
            TileCentroid Rplus) → (
        let Tbar := TileTranslation (TileHalfTurn T₀) centerShift
        (TileCentroid Rminus + TileCentroid Rplus = TileCentroid T₀ + TileCentroid T₀ +
            GaussianRealPoint (BandVectors.1 (q i.succ) (q 0))) → (TileCentroid Tbar =
            TileCentroid T₀'))) ) := by
  classical
  intro q i T₀ T₀' hcentroid Rminus Rplus centerShift hcenters Tbar hsumCentroid
  have hcentformula := (TileTranslationFormulas (TileHalfTurn T₀) centerShift).2.2.2.2.1
  have hhalfcent := (TileHalfTurnFormulas T₀).2.2.2.2.2.2.2.1
  rw [hcentformula, hhalfcent]
  have hcentin := congrArg Prod.fst hcentroid
  have hcentout := congrArg Prod.snd hcentroid
  have hshiftr : (centerShift.re : Real) =
      (TileCentroid Rminus + TileCentroid Rplus).1 := by
    simpa only [GaussianRealPoint] using congrArg Prod.fst hcenters
  have hshifti : (centerShift.im : Real) =
      (TileCentroid Rminus + TileCentroid Rplus).2 := by
    simpa only [GaussianRealPoint] using congrArg Prod.snd hcenters
  have hsumr : (TileCentroid Rminus).1 + (TileCentroid Rplus).1 =
      (TileCentroid T₀).1 + (TileCentroid T₀).1 +
        (BandVectors.1 (q i.succ) (q 0)).re := by
    simpa only [Prod.fst_add, GaussianRealPoint] using congrArg Prod.fst hsumCentroid
  have hsumi : (TileCentroid Rminus).2 + (TileCentroid Rplus).2 =
      (TileCentroid T₀).2 + (TileCentroid T₀).2 +
        (BandVectors.1 (q i.succ) (q 0)).im := by
    simpa only [Prod.snd_add, GaussianRealPoint] using congrArg Prod.snd hsumCentroid
  have hcentin' : (TileCentroid T₀').1 - (TileCentroid T₀).1 =
      (BandVectors.1 (q i.succ) (q 0)).re := by
    simpa only [Prod.fst_sub, GaussianRealPoint] using hcentin
  have hcentout' : (TileCentroid T₀').2 - (TileCentroid T₀).2 =
      (BandVectors.1 (q i.succ) (q 0)).im := by
    simpa only [Prod.snd_sub, GaussianRealPoint] using hcentout
  apply Prod.ext
  · change -(TileCentroid T₀).1 + (centerShift.re : Real) = (TileCentroid T₀').1
    calc
      -(TileCentroid T₀).1 + (centerShift.re : Real) =
          -(TileCentroid T₀).1 + ((TileCentroid Rminus).1 +
            (TileCentroid Rplus).1) := by rw [hshiftr]; rfl
      _ = -(TileCentroid T₀).1 + ((TileCentroid T₀).1 +
            (TileCentroid T₀).1 + (BandVectors.1 (q i.succ) (q 0)).re) := by rw [hsumr]
      _ = (TileCentroid T₀').1 := by linarith [hcentin']
  · change -(TileCentroid T₀).2 + (centerShift.im : Real) = (TileCentroid T₀').2
    calc
      -(TileCentroid T₀).2 + (centerShift.im : Real) =
          -(TileCentroid T₀).2 + ((TileCentroid Rminus).2 +
            (TileCentroid Rplus).2) := by rw [hshifti]; rfl
      _ = -(TileCentroid T₀).2 + ((TileCentroid T₀).2 +
            (TileCentroid T₀).2 + (BandVectors.1 (q i.succ) (q 0)).im) := by rw [hsumi]
      _ = (TileCentroid T₀').2 := by linarith [hcentout']

private theorem htranslateInjective :
    (by
      classical
      exact
        ∀ (touter : GaussianInt), Function.Injective (GaussianTranslation touter) ) := by
  classical
  intro touter x y hxy
  dsimp [GaussianTranslation] at hxy
  exact add_right_cancel hxy

private theorem hbarDomains :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), ∀ (h₀' : PartialOdometer), ∀ (centerShift : GaussianInt),
        let hbar := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift 0 0
        ∀ (touter : GaussianInt), (∀ (x : GaussianInt), x ∈ hbar.domain ↔ x - touter ∈
            h₀'.domain) → ((touter = 0) → (∀ x, x ∈ hbar.domain ↔ x ∈ h₀'.domain)) ) := by
  classical
  intro h₀ h₀' centerShift hbar touter hdomainShift htouterZero x
  simpa [htouterZero] using hdomainShift x

private theorem hbarOuterDomain :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), ∀ (centerShift : GaussianInt),
        let hbar := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift 0 0
        ∀ (couter : GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        let houterAffine := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift a b
        hbar.domain = houterAffine.domain ) := by
  classical
  intro h₀ centerShift hbar couter eouter a b houterAffine
  simp only [hbar, houterAffine,
    (PartialOdometerAffineTranslateFormulas (PartialOdometerHalfTurn h₀)
      centerShift 0 0).1,
    (PartialOdometerAffineTranslateFormulas (PartialOdometerHalfTurn h₀)
      centerShift a b).1]

private theorem houterAffineDomain :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), ∀ (h₀' : PartialOdometer), ∀ (centerShift : GaussianInt),
        let hbar := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift 0 0
        ∀ (couter : GaussianInt), ∀ (eouter : ℤ), (∀ x, x ∈ hbar.domain ↔ x ∈ h₀'.domain) → (
        let a : GaussianInt := -couter
        let b : Int := -eouter
        let houterAffine := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift a b
        (hbar.domain = houterAffine.domain) → (h₀'.domain = houterAffine.domain)) ) := by
  classical
  intro h₀ h₀' centerShift hbar couter eouter hbarDomains a b houterAffine hbarOuterDomain
  ext x
  have hx := hbarDomains x
  rw [hbarOuterDomain] at hx
  exact hx.symm

private theorem houterAffineEq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (T₀' : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (h₀' :
            PartialOdometer), (TileOdometer C₀.1.1 T₀' h₀') → (∀ (p₀' : Real × Real),
            (PartialOdometerSlope h₀' = some p₀') → (∀ (centerShift : GaussianInt),
        let hbar := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift 0 0
        (∃! u : GaussianInt, T₀'.cells = (TileTranslation T₀' u).cells ∧ (T₀'.cells = ∅ →
            T₀'.anchor = (TileTranslation T₀' u).anchor) ∧ ∃ (a : GaussianInt) (b : ℤ), (∀ (x :
            GaussianInt), x ∈ hbar.domain ↔ x - u ∈ h₀'.domain) ∧ ∀ x ∈ hbar.domain, hbar.value x
            = h₀'.value (x - u) + a.re * x.re + a.im * x.im + b) → (∀ (touter : GaussianInt), ∀
            (couter : GaussianInt), ∀ (eouter : ℤ), (∀ (x : GaussianInt), x ∈ hbar.domain ↔ x -
            touter ∈ h₀'.domain) → ((∀ x ∈ hbar.domain, hbar.value x = h₀'.value (x - touter) +
            couter.re * x.re + couter.im * x.im + eouter) → ((touter = 0) → ((∀ x, x ∈
            hbar.domain ↔ x ∈ h₀'.domain) → (
        let a : GaussianInt := -couter
        let b : Int := -eouter
        let houterAffine := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift a b
        (hbar.domain = houterAffine.domain) → ((h₀'.domain = houterAffine.domain) → (h₀' =
            houterAffine))))))))) ) := by
  classical
  intro C₀ T₀' h₀ h₀' hO₀' p₀' hs₀' centerShift hbar houterUnique touter couter eouter
      hdomainShift hvalueShift htouterZero hbarDomains a b houterAffine hbarOuterDomain
      houterAffineDomain
  cases h₀' with
  | mk dom val hout =>
    have hdom : dom = houterAffine.domain := houterAffineDomain
    subst dom
    congr 1
    funext x
    by_cases hx : x ∈ houterAffine.domain
    · have hxbar : x ∈ hbar.domain := by rw [hbarOuterDomain]; exact hx
      have hv := by simpa [htouterZero] using hvalueShift x hxbar
      have hvbar := (PartialOdometerAffineTranslateFormulas
        (PartialOdometerHalfTurn h₀) centerShift 0 0).2.2.1 x hxbar
      have hvaff := (PartialOdometerAffineTranslateFormulas
        (PartialOdometerHalfTurn h₀) centerShift a b).2.2.1 x hx
      rw [hvbar] at hv
      change val x = (PartialOdometerAffineTranslate
        (PartialOdometerHalfTurn h₀) centerShift a b).value x
      rw [hvaff]
      norm_num [a, b, Zsqrtd.re_neg, Zsqrtd.im_neg] at hv ⊢
      linarith
    · have hxbar : x ∉ hbar.domain := by
        intro hm
        apply hx
        rw [← hbarOuterDomain]
        exact hm
      rw [hout x hx]
      change 0 = (PartialOdometerAffineTranslate
        (PartialOdometerHalfTurn h₀) centerShift a b).value x
      exact (houterAffine.value_outside x hx).symm

private theorem hhalfSlope :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), ∀ (p₀ : Real × Real), (PartialOdometerSlope h₀ = some p₀) →
            (PartialOdometerSlope (PartialOdometerHalfTurn h₀) = some (-p₀.1, -p₀.2)) ) := by
  classical
  intro h₀ p₀ hs₀
  have hs := (PartialOdometerHalfTurnFormulas h₀).2.2.2.2.2.2
  rw [hs₀] at hs
  simpa using hs

private theorem houterSlope :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), ∀ (p₀ : Real × Real), ∀ (centerShift : GaussianInt), ∀ (couter
            : GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        let houterAffine := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift a b
        (PartialOdometerSlope (PartialOdometerHalfTurn h₀) = some (-p₀.1, -p₀.2)) →
            (PartialOdometerSlope houterAffine = some (-p₀.1 + (a.re : Real), -p₀.2 + (a.im :
            Real))) ) := by
  classical
  intro h₀ p₀ centerShift couter eouter a b houterAffine hhalfSlope
  have hs := (PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn h₀) centerShift a b).2.2.2.2.2
  rw [hhalfSlope] at hs
  simpa [houterAffine] using hs

private theorem haSlope :
    (by
      classical
      exact
        ∀ (p₀ : Real × Real), ∀ (p₀' : Real × Real), ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        ((-p₀.1 + (↑a.re : ℝ), -p₀.2 + (↑a.im : ℝ)) = p₀') → (p₀ + p₀' = GaussianRealPoint a) )
            := by
  classical
  intro p₀ p₀' couter a houterSlopeEq
  apply Prod.ext
  · have h := congrArg Prod.fst houterSlopeEq
    change -p₀.1 + (a.re : Real) = p₀'.1 at h
    change p₀.1 + p₀'.1 = (a.re : Real)
    linarith
  · have h := congrArg Prod.snd houterSlopeEq
    change -p₀.2 + (a.im : Real) = p₀'.2 at h
    change p₀.2 + p₀'.2 = (a.im : Real)
    linarith

private theorem hRplusBand :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle)
          (base Rplus : ProtoTile),
          BandPrototile
              Cᵢ.1.1
              base →
            Rplus ∈
                RegularTileFamily base
                  (TilingLattice Cᵢ) →
              BandPrototile
                Cᵢ.1.1
                Rplus) := by
  classical
  intro Cᵢ base Rplus hbase hRplus
  rcases hRplus with ⟨w, hw, rfl⟩
  exact BandPrototileTranslation Cᵢ.1.1 base w hbase

private theorem hplusRawO :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), ∀ (Rminus :
            ProtoTile), ∀ (hseed : PartialOdometer), ∀ (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        (TileOdometer Cᵢ.1.1 Rminus hminus) → (∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        TileOdometer Cᵢ.1.1 (TileTranslation (TileHalfTurn Rminus) centerShift) hplus) ) := by
  classical
  intro q Cᵢ i Rminus hseed centerShift d hminus hOminus couter a hplus
  exact TileOdometerAffineTranslation Cᵢ.1.1 (TileHalfTurn Rminus)
    (PartialOdometerHalfTurn hminus) centerShift a 0
    (TileOdometerCentralSymmetry Cᵢ.1.1 Rminus hminus hOminus).1

private theorem hslopeDifferenceRe :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (p₀' : Real ×
            Real), (p₀' - p₀ = GaussianRealPoint (BandVectors.2 (q i.succ) (q (0 : Fin (4 :
            ℕ))))) → (p₀'.1 - p₀.1 = (BandVectors.2 (q i.succ) (q 0)).re) ) := by
  classical
  intro q i p₀ p₀' hslope
  simpa only [Prod.fst_sub, GaussianRealPoint] using congrArg Prod.fst hslope

private theorem hslopeDifferenceIm :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (p₀' : Real ×
            Real), (p₀' - p₀ = GaussianRealPoint (BandVectors.2 (q i.succ) (q (0 : Fin (4 :
            ℕ))))) → (p₀'.2 - p₀.2 = (BandVectors.2 (q i.succ) (q 0)).im) ) := by
  classical
  intro q i p₀ p₀' hslope
  simpa only [Prod.snd_sub, GaussianRealPoint] using congrArg Prod.snd hslope

private theorem hplusSlopeCalc :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (p₀' : Real ×
            Real),
        let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
        let pplus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        (p₀'.1 - p₀.1 = (BandVectors.2 (q i.succ) (q 0)).re) → ((p₀'.2 - p₀.2 = (BandVectors.2 (q
            i.succ) (q 0)).im) → ((p₀.1 + p₀'.1 = (a.re : Real)) → ((p₀.2 + p₀'.2 = (a.im :
            Real)) → ((-pminus.1 + (a.re : Real), -pminus.2 + (a.im : Real)) = pplus)))) ) := by
  classical
  intro q i p₀ p₀' pminus pplus couter a hslopeDifferenceRe hslopeDifferenceIm haRe haIm
  apply Prod.ext
  · simp [pminus, pplus, GaussianRealPoint, Prod.smul_mk,
      Zsqrtd.re_sub, Zsqrtd.re_add, Int.cast_sub, Int.cast_add,
      GaussianInt.intCast_re] at hslopeDifferenceRe haRe ⊢
    linarith
  · simp [pminus, pplus, GaussianRealPoint, Prod.smul_mk,
      Zsqrtd.im_sub, Zsqrtd.im_add, Int.cast_sub, Int.cast_add,
      GaussianInt.intCast_im] at hslopeDifferenceIm haIm ⊢
    linarith

private theorem hsplus :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (hseed :
            PartialOdometer), ∀ (centerShift : GaussianInt),
        let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
        let pplus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        (PartialOdometerSlope hminus = some pminus) → (∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        ((-pminus.1 + (a.re : Real), -pminus.2 + (a.im : Real)) = pplus) → (PartialOdometerSlope
            hplus = some pplus)) ) := by
  classical
  intro q i p₀ hseed centerShift pminus pplus d hminus hsminus couter a hplus hplusSlopeCalc
  have hsHalf := (PartialOdometerHalfTurnFormulas hminus).2.2.2.2.2.2
  rw [hsminus] at hsHalf
  have hsAff := (PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn hminus) centerShift a 0).2.2.2.2.2
  rw [hsHalf] at hsAff
  simpa [hplus] using hsAff.trans (by
    simp only [Option.map_some]
    exact congrArg (fun p : Real × Real => some p) hplusSlopeCalc)

private theorem finiteTranslationFix :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), T.cells.Nonempty → T.cells = (TileTranslation T
            u).cells → u = 0 ) := by
  classical
  intro T u hne hcells
  have hinj : Function.Injective (GaussianTranslation u) := by
    intro x y hxy
    dsimp [GaussianTranslation] at hxy
    exact add_right_cancel hxy
  have hsumRe := congrArg (fun s : Finset GaussianInt => ∑ z ∈ s, z.re) hcells
  rw [(TileTranslationFormulas T u).1, Finset.sum_image hinj.injOn] at hsumRe
  simp only [GaussianTranslation, Zsqrtd.re_add] at hsumRe
  rw [Finset.sum_add_distrib, Finset.sum_const] at hsumRe
  simp only [nsmul_eq_mul] at hsumRe
  have hcardNe : (T.cells.card : Int) ≠ 0 := by
    exact_mod_cast hne.card_pos.ne'
  have hmulRe : (T.cells.card : Int) * u.re = 0 := by linarith
  have huRe : u.re = 0 := (mul_eq_zero.mp hmulRe).resolve_left hcardNe
  have hsumIm := congrArg (fun s : Finset GaussianInt => ∑ z ∈ s, z.im) hcells
  rw [(TileTranslationFormulas T u).1, Finset.sum_image hinj.injOn] at hsumIm
  simp only [GaussianTranslation, Zsqrtd.im_add] at hsumIm
  rw [Finset.sum_add_distrib, Finset.sum_const] at hsumIm
  simp only [nsmul_eq_mul] at hsumIm
  have hmulIm : (T.cells.card : Int) * u.im = 0 := by linarith
  have huIm : u.im = 0 := (mul_eq_zero.mp hmulIm).resolve_left hcardNe
  apply Zsqrtd.ext <;> assumption

private theorem hRminusBand :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle)
          (base Rminus : ProtoTile),
          BandPrototile
              Cᵢ.1.1
              base →
            Rminus ∈
                RegularTileFamily base
                  (TilingLattice Cᵢ) →
              BandPrototile
                Cᵢ.1.1
                Rminus) := by
  classical
  intro Cᵢ base Rminus hbase hRminus
  rcases hRminus with ⟨w, hw, rfl⟩
  exact BandPrototileTranslation Cᵢ.1.1 base w hbase

private theorem hbackRawO :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), ∀ (Rplus :
            ProtoTile), ∀ (hseed : PartialOdometer), ∀ (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        (TileOdometer Cᵢ.1.1 Rplus hplus) → (
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        TileOdometer Cᵢ.1.1 (TileTranslation (TileHalfTurn Rplus) centerShift) hback) ) := by
  classical
  intro q Cᵢ i Rplus hseed centerShift d hminus couter a hplus hOplus hback
  change TileOdometer Cᵢ.1.1 (TileTranslation (TileHalfTurn Rplus) centerShift)
    (PartialOdometerAffineTranslate (PartialOdometerHalfTurn hplus) centerShift a 0)
  exact TileOdometerAffineTranslation Cᵢ.1.1 (TileHalfTurn Rplus)
    (PartialOdometerHalfTurn hplus) centerShift a 0
    (TileOdometerCentralSymmetry Cᵢ.1.1 Rplus hplus hOplus).1

private theorem haEndpoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real),
        let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
        let pplus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        ((-pminus.1 + (a.re : Real), -pminus.2 + (a.im : Real)) = pplus) → (pminus + pplus =
            GaussianRealPoint a) ) := by
  classical
  intro q i p₀ pminus pplus couter a hplusSlopeCalc
  apply Prod.ext
  · have he := congrArg Prod.fst hplusSlopeCalc
    change -pminus.1 + (a.re : Real) = pplus.1 at he
    change pminus.1 + pplus.1 = (a.re : Real)
    linarith
  · have he := congrArg Prod.snd hplusSlopeCalc
    change -pminus.2 + (a.im : Real) = pplus.2 at he
    change pminus.2 + pplus.2 = (a.im : Real)
    linarith

private theorem hhalfSlopePlus :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (hseed :
            PartialOdometer), ∀ (centerShift : GaussianInt),
        let pplus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        (PartialOdometerSlope hplus = some pplus) → (PartialOdometerSlope
            (PartialOdometerHalfTurn hplus) = some (-pplus.1, -pplus.2)) ) := by
  classical
  intro q i p₀ hseed centerShift pplus d hminus couter a hplus hsplus
  have hs := (PartialOdometerHalfTurnFormulas hplus).2.2.2.2.2.2
  rw [hsplus] at hs
  simpa using hs

private theorem hsback :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (hseed :
            PartialOdometer), ∀ (centerShift : GaussianInt),
        let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
        let pplus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        (pminus + pplus = GaussianRealPoint a) → ((PartialOdometerSlope (PartialOdometerHalfTurn
            hplus) = some (-pplus.1, -pplus.2)) → (PartialOdometerSlope hback = some pminus)) )
            := by
  classical
  intro q i p₀ hseed centerShift pminus pplus d hminus couter a hplus hback haEndpoint
      hhalfSlopePlus
  have hs := (PartialOdometerAffineTranslateFormulas
    (PartialOdometerHalfTurn hplus) centerShift a 0).2.2.2.2.2
  rw [hhalfSlopePlus] at hs
  have hpair : (-pplus.1 + (a.re : Real), -pplus.2 + (a.im : Real)) = pminus := by
    apply Prod.ext
    · have ha := congrArg Prod.fst haEndpoint
      change pminus.1 + pplus.1 = (a.re : Real) at ha
      linarith
    · have ha := congrArg Prod.snd haEndpoint
      change pminus.2 + pplus.2 = (a.im : Real) at ha
      linarith
  simpa [hback] using hs.trans (congrArg (fun p : Real × Real => some p) hpair)

private theorem hbackSameDomain :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hseed : PartialOdometer), ∀
            (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        ∀ (tback : GaussianInt), (∀ (x : GaussianInt), x ∈ hback.domain ↔ x - tback ∈
            hminus.domain) → ((tback = (0 : GaussianInt)) → (∀ x, x ∈ hback.domain ↔ x ∈
            hminus.domain)) ) := by
  classical
  intro q i hseed centerShift d hminus couter a hplus hback tback hbackDomains htbackZero x
  simpa [htbackZero] using hbackDomains x

private theorem hbackAffineDomain :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hseed : PartialOdometer), ∀
            (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        ∀ (cback : GaussianInt), ∀ (eback : ℤ), (∀ x, x ∈ hback.domain ↔ x ∈ hminus.domain) → (
        let hminusAffine := PartialOdometerAffineTranslate hminus 0 cback eback
        hback.domain = hminusAffine.domain) ) := by
  classical
  intro q i hseed centerShift d hminus couter a hplus hback cback eback hbackSameDomain hminusAffine
  ext x
  simp only [hminusAffine,
    (PartialOdometerAffineTranslateFormulas hminus 0 cback eback).2.1]
  simp [hbackSameDomain]

private theorem hbackAffineEq :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hseed : PartialOdometer), ∀
            (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        ∀ (tback : GaussianInt), ∀ (cback : GaussianInt), ∀ (eback : ℤ), (∀ x ∈ hback.domain,
            hback.value x = hminus.value (x - tback) + cback.re * x.re + cback.im * x.im + eback)
            → ((tback = (0 : GaussianInt)) → ((∀ x, x ∈ hback.domain ↔ x ∈ hminus.domain) → (
        let hminusAffine := PartialOdometerAffineTranslate hminus 0 cback eback
        (hback.domain = hminusAffine.domain) → (hback = hminusAffine)))) ) := by
  classical
  intro q i hseed centerShift d hminus couter a hplus hback tback cback eback hbackValues
      htbackZero hbackSameDomain hminusAffine hbackAffineDomain
  have partial_ext (h k : PartialOdometer) (hd : h.domain = k.domain)
      (hv : ∀ x, h.value x = k.value x) : h = k := by
    cases h
    cases k
    dsimp at hd hv
    subst hd
    have he := funext hv
    subst he
    rfl
  apply partial_ext
  · exact hbackAffineDomain
  · intro x
    by_cases hx : x ∈ hminusAffine.domain
    · have hxback : x ∈ hback.domain := by rw [hbackAffineDomain]; exact hx
      have hv := by simpa [htbackZero, sub_zero] using hbackValues x hxback
      have hvaff := (PartialOdometerAffineTranslateFormulas
        hminus 0 cback eback).2.2.1 x hx
      rw [hvaff]
      simpa [sub_zero] using hv
    · have hxₘ : x ∉ hminus.domain := by
        intro hm
        apply hx
        exact (hbackAffineDomain ▸ (hbackSameDomain x).mpr hm)
      rw [hback.value_outside x (by
        intro hxback
        apply hx
        exact (hbackAffineDomain ▸ hxback))]
      exact (hminusAffine.value_outside x hx).symm

private theorem hbackLinearZero :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (p₀ : Real × Real), ∀ (hseed :
            PartialOdometer), ∀ (centerShift : GaussianInt),
        let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        (PartialOdometerSlope hminus = some pminus) → (∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        ∀ (cback : GaussianInt), ∀ (eback : ℤ), (PartialOdometerSlope hback = some pminus) → (
        let hminusAffine := PartialOdometerAffineTranslate hminus 0 cback eback
        (hback = hminusAffine) → (cback = 0))) ) := by
  classical
  intro q i p₀ hseed centerShift pminus d hminus hsminus couter a hplus hback cback eback hsback
      hminusAffine hbackAffineEq
  have hbackSlopeFormula := (PartialOdometerAffineTranslateFormulas
    hminus 0 cback eback).2.2.2.2.2
  have hcomparisonSlope := hsback
  rw [hbackAffineEq] at hcomparisonSlope
  rw [hbackSlopeFormula, hsminus] at hcomparisonSlope
  have hp := Option.some.inj hcomparisonSlope
  apply Zsqrtd.ext
  · have he := congrArg Prod.fst hp
    change pminus.1 + (cback.re : Real) = pminus.1 at he
    have hre : (cback.re : Real) = 0 := by linarith
    exact_mod_cast hre
  · have he := congrArg Prod.snd hp
    change pminus.2 + (cback.im : Real) = pminus.2 at he
    have him : (cback.im : Real) = 0 := by linarith
    exact_mod_cast him

private theorem hbackBackDomain :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hseed : PartialOdometer), ∀
            (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        let hminusBack := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a bplus
        hback.domain = hminusBack.domain ) := by
  classical
  intro q i hseed centerShift d hminus couter a hplus hback eback bplus hminusBack
  ext x
  simp only [hback, hminusBack,
    (PartialOdometerAffineTranslateFormulas (PartialOdometerHalfTurn hplus)
      centerShift a 0).2.1,
    (PartialOdometerAffineTranslateFormulas (PartialOdometerHalfTurn hplus)
      centerShift a bplus).2.1]

private theorem hminusBackDomain :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hseed : PartialOdometer), ∀
            (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        ∀ (eback : ℤ), (∀ x, x ∈ hback.domain ↔ x ∈ hminus.domain) → (
        let bplus : Int := -eback
        let hminusBack := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a bplus
        (hback.domain = hminusBack.domain) → (hminus.domain = hminusBack.domain)) ) := by
  classical
  intro q i hseed centerShift d hminus couter a hplus hback eback hbackSameDomain bplus
      hminusBack hbackBackDomain
  ext x
  have hx := hbackSameDomain x
  rw [hbackBackDomain] at hx
  exact hx.symm

private theorem hminusBackEq :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hseed : PartialOdometer), ∀
            (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt),
        let a : GaussianInt := -couter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        let hback := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a 0
        ∀ (tback : GaussianInt), ∀ (cback : GaussianInt), ∀ (eback : ℤ), (∀ x ∈ hback.domain,
            hback.value x = hminus.value (x - tback) + cback.re * x.re + cback.im * x.im + eback)
            → ((tback = (0 : GaussianInt)) → ((∀ x, x ∈ hback.domain ↔ x ∈ hminus.domain) →
            ((cback = 0) → (
        let bplus : Int := -eback
        let hminusBack := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a bplus
        (hback.domain = hminusBack.domain) → ((hminus.domain = hminusBack.domain) → (hminus =
            hminusBack)))))) ) := by
  classical
  intro q i hseed centerShift d hminus couter a hplus hback tback cback eback hbackValues
      htbackZero hbackSameDomain hbackLinearZero bplus hminusBack hbackBackDomain hminusBackDomain
  have partial_ext (h k : PartialOdometer) (hd : h.domain = k.domain)
      (hv : ∀ x, h.value x = k.value x) : h = k := by
    cases h
    cases k
    dsimp at hd hv
    subst hd
    have he := funext hv
    subst he
    rfl
  apply partial_ext
  · exact hminusBackDomain
  · intro x
    by_cases hx : x ∈ hminusBack.domain
    · have hxback : x ∈ hback.domain := by rw [hbackBackDomain]; exact hx
      have hv := by simpa [htbackZero, sub_zero] using hbackValues x hxback
      have hvalBack := (PartialOdometerAffineTranslateFormulas
        (PartialOdometerHalfTurn hplus) centerShift a 0).2.2.1 x hxback
      have hvalTarget := (PartialOdometerAffineTranslateFormulas
        (PartialOdometerHalfTurn hplus) centerShift a bplus).2.2.1 x hx
      rw [hvalBack] at hv
      rw [hvalTarget]
      simp [hbackLinearZero, bplus] at hv ⊢
      linarith
    · have hxminus : x ∉ hminus.domain := by
        intro hm
        apply hx
        exact (hminusBackDomain ▸ (hbackSameDomain x).mpr hm)
      rw [hminus.value_outside x hxminus]
      exact (hminusBack.value_outside x hx).symm

private theorem hcentroidEndpoints :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (T₀ : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (q' :
            Fin (4 : ℕ) → CircleCoordinates), (TileCentroid Rminus - TileCentroid T₀ = (1 / 2 :
            ℝ) • GaussianRealPoint (BandVectors.1 (q' i.succ) (q' (0 : Fin (4 : ℕ))) -
            BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ))) → ((TileCentroid Rplus -
            TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (q' i.succ) (q' (0 :
            Fin (4 : ℕ))) + BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' i.succ))) → (TileCentroid
            Rplus - TileCentroid Rminus = GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ))))
            ) := by
  classical
  intro i T₀ Rminus Rplus q' hcentroidMinus hcentroidPlus
  have hcm := hcentroidMinus
  have hcp := hcentroidPlus
  calc
    TileCentroid Rplus - TileCentroid Rminus =
        (TileCentroid Rplus - TileCentroid T₀) -
          (TileCentroid Rminus - TileCentroid T₀) := by
            apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
    _ = (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.1 (q' i.succ) (q' 0) + BandVectors.1 (q' 0) (q' i.succ)) -
        (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.1 (q' i.succ) (q' 0) - BandVectors.1 (q' 0) (q' i.succ)) := by
            rw [hcp, hcm]
    _ = GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ)) := by
        apply Prod.ext <;>
          simp [GaussianRealPoint, Prod.smul_mk, Zsqrtd.re_add,
            Zsqrtd.re_sub, Zsqrtd.im_add, Zsqrtd.im_sub,
            Int.cast_add, Int.cast_sub] <;> ring

private theorem hpositive' :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), ((0 : ℤ) < Cᵢ.1.1.1) → (∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), (q' i.succ = Cᵢ.1.1) → (0 < (q' i.succ).1)) ) := by
  classical
  intro Cᵢ i hpositive q' hqi
  rw [hqi]
  exact hpositive

private theorem hgaussianPointZero :
    (by
      classical
      exact
        ∀ z : GaussianInt, GaussianRealPoint z = (0, 0) → z = 0 ) := by
  classical
  intro z hz
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hz
    simp only [GaussianRealPoint] at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hz
    simp only [GaussianRealPoint] at h
    exact_mod_cast h

private theorem hRminusNeRplus :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (q' : Fin (4 : ℕ) →
            CircleCoordinates), (TileCentroid Rplus - TileCentroid Rminus = GaussianRealPoint
            (BandVectors.1 (q' 0) (q' i.succ))) → ((BandVectors.1 (q' 0) (q' i.succ) ≠ 0) → ((∀ z
            : GaussianInt, GaussianRealPoint z = (0, 0) → z = 0) → (Rminus ≠ Rplus))) ) := by
  classical
  intro i Rminus Rplus q' hcentroidEndpoints hvectorNe hgaussianPointZero heq
  have hcentEq := congrArg TileCentroid heq.symm
  have hzero : GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ)) = (0, 0) := by
    calc
      GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ)) =
          TileCentroid Rplus - TileCentroid Rminus := hcentroidEndpoints.symm
      _ = (0, 0) := by
        calc
          TileCentroid Rplus - TileCentroid Rminus =
              TileCentroid Rminus - TileCentroid Rminus := by rw [hcentEq]
          _ = 0 := sub_self _
          _ = (0, 0) := rfl
  exact hvectorNe (hgaussianPointZero _ hzero)

private theorem htilesHead :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), ∀
            (horientationExists : ∃ o : Bool, Cᵢ.1.1.1 = 1 → UnitOccurrenceOrientation q i o),
        let orientation := Classical.choose horientationExists
        ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List
            ProtoTile), (TileString Cᵢ orientation base Rminus Rplus tiles) → (tiles.head? = some
            Rminus) ) := by
  classical
  intro q Cᵢ i horientationExists orientation base Rminus Rplus tiles hstring
  have hh := hstring
  unfold TileString at hh
  exact hh.2.1

private theorem htilesLast :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), ∀
            (horientationExists : ∃ o : Bool, Cᵢ.1.1.1 = 1 → UnitOccurrenceOrientation q i o),
        let orientation := Classical.choose horientationExists
        ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List
            ProtoTile), (TileString Cᵢ orientation base Rminus Rplus tiles) → (tiles.getLast? =
            some Rplus) ) := by
  classical
  intro q Cᵢ i horientationExists orientation base Rminus Rplus tiles hstring
  have hh := hstring
  unfold TileString at hh
  exact hh.2.2.1

private theorem htilesLength :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (i : Fin
            3), ∀ (T₀ : ProtoTile), ∀ (horientationExists : ∃ o : Bool, Cᵢ.1.1.1 = 1 →
            UnitOccurrenceOrientation q i o),
        let orientation := Classical.choose horientationExists
        ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List
            ProtoTile), (BoundaryString C₀ Cᵢ i orientation T₀ base Rminus Rplus tiles) →
            ((TileString Cᵢ orientation base Rminus Rplus tiles) → (∀ (centerShift :
            GaussianInt), ∀ (reverseTiles : List ProtoTile), (List.Forall₂ (fun (T U : ProtoTile)
            => (TileTranslation (TileHalfTurn T) centerShift).cells = U.cells) tiles
            reverseTiles) → ((Rminus ≠ Rplus) → ((tiles.head? = some Rminus) → ((tiles.getLast? =
            some Rplus) → (2 ≤ tiles.length)))))) ) := by
  classical
  intro q C₀ Cᵢ i T₀ horientationExists orientation base Rminus Rplus tiles hboundaryOriginal
      hstring centerShift reverseTiles hcellPairs hRminusNeRplus htilesHead htilesLast
  cases tiles with
  | nil => simp at htilesHead
  | cons first rest =>
    cases rest with
    | nil =>
      have hfirst : first = Rminus := by simpa using htilesHead
      have hlast : first = Rplus := by simpa using htilesLast
      exact (hRminusNeRplus (hfirst.symm.trans hlast)).elim
    | cons second rest => simp

private theorem transformForall :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt), ∀ (couter : GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        ∀ (hs : List PartialOdometer),
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        ∀ n, ∀ l, List.Forall₂ (fun h g => ∃ c : Int, g = PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn h) centerShift a c) l (l.mapIdx (fun j h => transformAt (n +
            j) h)) ) := by
  classical
  intro centerShift couter eouter a b eback bplus hs constAt transformAt n l
  induction l generalizing n with
  | nil => simp
  | cons h tl ih =>
      simp only [List.mapIdx_cons]
      constructor
      · exact ⟨constAt n, by simp [transformAt]⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

private theorem htransform :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt), ∀ (couter : GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        ∀ (hs : List PartialOdometer),
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        let gs := hs.mapIdx transformAt
        (∀ n, ∀ l, List.Forall₂ (fun h g => ∃ c : Int, g = PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn h) centerShift a c) l (l.mapIdx (fun j h => transformAt (n +
            j) h))) → (List.Forall₂ (fun h g => ∃ c : Int, g = PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn h) centerShift a c) hs gs) ) := by
  classical
  intro centerShift couter eouter a b eback bplus hs constAt transformAt gs transformForall
  simpa [gs, transformAt, Nat.zero_add] using transformForall 0 hs

private theorem hgsHead :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (i : Fin 3), ∀ (hseed : PartialOdometer), ∀
            (centerShift : GaussianInt),
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        ∀ (couter : GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        ∀ (hs : List PartialOdometer), (hs.head? = some hminus) → (
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        let gs := hs.mapIdx transformAt
        gs.head? = some hplus) ) := by
  classical
  intro q i hseed centerShift d hminus couter eouter a b hplus eback bplus hs hhsHead constAt
      transformAt gs
  rw [List.head?_mapIdx, hhsHead]
  simp [transformAt, constAt, hplus]

private theorem forall2_dropLast :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ (r : α → β → Prop), ∀ {xs : List α}, ∀ {ys : List β},
            List.Forall₂ r xs ys → List.Forall₂ r xs.dropLast ys.dropLast ) := by
  classical
  intro α β r xs ys hxy
  induction hxy with
  | nil => simp
  | @cons x y xs ys hxy hrest ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp
      | cons y' ys' => cases hrest
    | cons x' xs' =>
      cases ys with
      | nil => cases hrest
      | cons y' ys' =>
        simpa only [List.dropLast_cons_cons] using List.Forall₂.cons hxy ih

private theorem hinteriorCells :
    (by
      classical
      exact
        ∀ (tiles : List ProtoTile) (centerShift : GaussianInt)
          (reverseTiles : List ProtoTile),
          List.Forall₂
              (fun (T U : ProtoTile) =>
                (TileTranslation
                      (TileHalfTurn T) centerShift).cells =
                  U.cells)
              tiles reverseTiles →
            (2 : ℕ) ≤ tiles.length →
              (∀ {α β : Type} (r : α → β → Prop) {xs : List α} {ys : List β},
                  List.Forall₂ r xs ys → List.Forall₂ r xs.dropLast ys.dropLast) →
                let cellRelation := fun (T U : ProtoTile) =>
                  (TileTranslation
                        (TileHalfTurn T) centerShift).cells =
                    U.cells;
                List.Forall₂ cellRelation (List.drop (1 : ℕ) tiles).dropLast
                  (List.drop (1 : ℕ) reverseTiles).dropLast) := by
  classical
  intro tiles centerShift reverseTiles hcellPairs htilesLength forall2_dropLast cellRelation
  cases hcellPairs with
  | nil => simp at htilesLength
  | cons hfirst htail =>
    simpa using forall2_dropLast cellRelation htail

private theorem interiorTransforms :
    (by
      classical
      exact
        (BandCircle) → ((BandCircle) → ((Fin 3) → ((ProtoTile) → ((List ProtoTile) → ((Fin (4 :
            ℕ) → CircleCoordinates) → (∀ (centerShift : GaussianInt), (GaussianInt) → (∀ (couter
            : GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        ∀ (hs : List PartialOdometer),
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        ∀ n, ∀ (l : List PartialOdometer), 0 < n → hs.length = n + l.length → List.Forall₂ (fun h
            g => g = PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a b)
            l.dropLast ((l.mapIdx (fun j h => transformAt (n + j) h)).dropLast)))))))) ) := by
  classical
  intro C₀ Cᵢ i T₀' tiles q' centerShift touter couter eouter a b eback bplus hs constAt
      transformAt n l
  induction l generalizing n with
  | nil => intro hn hlen; simp
  | cons x xs ih =>
    intro hn hlen
    cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.length_cons] at hlen
      simp only [List.dropLast_cons_cons, List.mapIdx_cons]
      constructor
      · dsimp [transformAt, constAt]
        have hn0 : n ≠ 0 := by omega
        have hnlast : n + 1 ≠ hs.length := by omega
        simp [hn0, hnlast]
      · have hlen' : hs.length = (n + 1) + (y :: ys).length := by
          simp only [List.length_cons] at hlen ⊢
          omega
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (n + 1) (by omega) hlen'

private theorem hgsTail :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (i : Fin 3),
            ∀ (hseed : PartialOdometer),
              ∀ (centerShift : GaussianInt),
                let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ);
                let hminus := PartialOdometerAffineTranslate hseed 0 d 0;
                ∀ (couter : GaussianInt),
                  ∀ (eouter : ℤ),
                    let a : GaussianInt := -couter;
                    let b : Int := -eouter;
                    ∀ (eback : ℤ),
                      let bplus : Int := -eback;
                      ∀ (hs : List PartialOdometer),
                        (hs.head? = some hminus) →
                          (let constAt : Nat → Int := fun n =>
                            if n = 0 then 0
                            else if n + 1 = hs.length then bplus else b;
                          let transformAt :
                            Nat → PartialOdometer → PartialOdometer := fun n h =>
                            PartialOdometerAffineTranslate
                              (PartialOdometerHalfTurn h) centerShift a (constAt n);
                          let gs := hs.mapIdx transformAt;
                          (gs.drop 1 =
                            hs.tail.mapIdx (fun j h => transformAt (1 + j) h)))) := by
  classical
  intro q i hseed centerShift d hminus couter eouter a b eback bplus hs hhsHead constAt
      transformAt gs
  change (List.mapIdx transformAt hs).drop 1 = _
  cases hs with
  | nil => simp at hhsHead
  | cons x xs => simp [List.mapIdx_cons, List.drop, Nat.add_comm]

private theorem htailLength :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (i : Fin 3),
            (∀ (hseed : PartialOdometer),
              (let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ);
              let hminus := PartialOdometerAffineTranslate hseed 0 d 0;
              (∀ (hs : List PartialOdometer),
                (hs.head? = some hminus) → (hs.length = 1 + hs.tail.length))))) := by
  classical
  intro q i hseed d hminus hs hhsHead
  cases hs with
  | nil => simp at hhsHead
  | cons x xs => simp [List.length_cons, List.tail]; omega

private theorem hinteriorTransforms :
    (by
      classical
        exact
        (∀ (centerShift : GaussianInt),
          (∀ (couter : GaussianInt),
            ∀ (eouter : ℤ),
              let a : GaussianInt := -couter;
              let b : Int := -eouter;
              ∀ (eback : ℤ),
                let bplus : Int := -eback;
                ∀ (hs : List PartialOdometer),
                  let constAt : Nat → Int := fun n =>
                    if n = 0 then 0 else if n + 1 = hs.length then bplus else b;
                  let transformAt : Nat → PartialOdometer → PartialOdometer :=
                    fun n h =>
                    PartialOdometerAffineTranslate (PartialOdometerHalfTurn h)
                      centerShift a (constAt n);
                  let gs := hs.mapIdx transformAt;
                  (∀ n,
                      ∀ (l : List PartialOdometer),
                        0 < n →
                          hs.length = n + l.length →
                            List.Forall₂
                              (fun h g =>
                                g =
                                  PartialOdometerAffineTranslate
                                    (PartialOdometerHalfTurn h) centerShift a b)
                              l.dropLast
                              ((l.mapIdx
                                  (fun j h => transformAt (n + j) h)).dropLast)) →
                    ((gs.drop 1 =
                        hs.tail.mapIdx (fun j h => transformAt (1 + j) h)) →
                      ((hs.length = 1 + hs.tail.length) →
                        (List.Forall₂
                          (fun h g =>
                            g =
                              PartialOdometerAffineTranslate
                                (PartialOdometerHalfTurn h) centerShift a b)
                          ((hs.drop 1).dropLast) ((gs.drop 1).dropLast))))))) := by
  classical
  intro centerShift couter eouter a b eback bplus hs constAt transformAt gs interiorTransforms
      hgsTail htailLength
  simpa [hgsTail] using interiorTransforms 1 hs.tail (by omega) htailLength

private theorem zipForall₂ :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {γ : Type}, ∀ {δ : Type}, ∀ {r : α → γ → Prop}, ∀
            {s : β → δ → Prop}, ∀ {xs : List α}, ∀ {ys : List β}, ∀ {us : List γ}, ∀
            {vs : List δ}, List.Forall₂ r xs us → List.Forall₂ s ys vs → List.Forall₂ (fun x y =>
            r x.1 y.1 ∧ s x.2 y.2) (xs.zip ys) (us.zip vs) ) := by
  classical
  intro α β γ δ r s xs ys us vs hxs
  induction hxs generalizing ys vs with
  | nil => intro hys; cases hys <;> simp
  | @cons x u xs us hxu hrest ih =>
    intro hys
    cases hys with
    | nil => simp
    | cons hyv hys =>
      simp only [List.zip_cons_cons]
      exact List.Forall₂.cons ⟨hxu, hyv⟩ (ih hys)

private theorem zip_dropLast_eq :
    (by
      classical
      exact
        (BandCircle) → ((BandCircle) → ((Fin 3) → ((ProtoTile) → ((List ProtoTile) → ((Fin (4 :
            ℕ) → CircleCoordinates) → ((GaussianInt) → ((List PartialOdometer) → (∀ {α : Type}, ∀
            {β : Type}, ∀ (xs : List α), ∀ (ys : List β), xs.length = ys.length → xs.dropLast.zip
            ys.dropLast = (xs.zip ys).dropLast)))))))) ) := by
  classical
  intro C₀ Cᵢ i T₀' tiles q' touter hs α β xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp at h ⊢
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons] at h
      cases xs with
      | nil => cases ys <;> simp at h ⊢
      | cons x' xs' =>
        cases ys with
        | nil => simp at h
        | cons y' ys' =>
          have hlen : xs'.length = ys'.length := by
            simp only [List.length_cons] at h
            omega
          simp only [List.dropLast_cons_cons, List.zip_cons_cons]
          rw [ih (y' :: ys') (by simpa using hlen)]
          simp only [List.zip_cons_cons]

private theorem hzipDropOne :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (i : Fin 3),
            ∀ (Rminus : ProtoTile),
              ∀ (tiles : List ProtoTile),
                ∀ (hseed : PartialOdometer),
                  (let d : GaussianInt :=
                    -BandVectors.2 (q ((i + 1).succ)) (q i.succ);
                  let hminus := PartialOdometerAffineTranslate hseed 0 d 0;
                  (tiles.head? = some Rminus) →
                    (∀ (hs : List PartialOdometer),
                      (hs.head? = some hminus) →
                        ((tiles.drop 1).zip (hs.drop 1) = (tiles.zip hs).drop 1)))) := by
  classical
  intro q i Rminus tiles hseed d hminus htilesHead hs hhsHead
  cases tiles with
  | nil => simp at htilesHead
  | cons T ts =>
    cases hs with
    | nil => simp at hhsHead
    | cons h ht => rfl

private theorem htailOdoLength :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (i : Fin 3),
            (∀ (Rminus : ProtoTile),
              ∀ (tiles : List ProtoTile),
                ∀ (hseed : PartialOdometer),
                  (let d : GaussianInt :=
                    -BandVectors.2 (q ((i + 1).succ)) (q i.succ);
                  let hminus := PartialOdometerAffineTranslate hseed 0 d 0;
                  ((tiles.head? = some Rminus) →
                    (∀ (hs : List PartialOdometer),
                      (hs.head? = some hminus) →
                        ((hs.length = tiles.length) →
                          ((tiles.drop 1).length = (hs.drop 1).length))))))) := by
  classical
  intro q i Rminus tiles hseed d hminus htilesHead hs hhsHead hlengthEq
  cases tiles with
  | nil => simp at htilesHead
  | cons T ts =>
    cases hs with
    | nil => simp at hhsHead
    | cons h ht =>
      simp only [List.length_cons, List.drop] at hlengthEq ⊢
      omega

private theorem hzipInteriorEq :
    (by
      classical
      exact
        ∀ (tiles : List ProtoTile), ∀ (hs : List PartialOdometer), (∀ {α : Type}, ∀ {β : Type}, ∀
            (xs : List α), ∀ (ys : List β), xs.length = ys.length → xs.dropLast.zip ys.dropLast =
            (xs.zip ys).dropLast) → (((tiles.drop 1).zip (hs.drop 1) = (tiles.zip hs).drop 1) →
            (((tiles.drop 1).length = (hs.drop 1).length) → ((((tiles.drop 1).dropLast).zip
            ((hs.drop 1).dropLast)) = ((tiles.zip hs).drop 1).dropLast))) ) := by
  classical
  intro tiles hs zip_dropLast_eq hzipDropOne htailOdoLength
  rw [← hzipDropOne]
  exact zip_dropLast_eq (tiles.drop 1) (hs.drop 1) htailOdoLength

private theorem zip_mem_left :
    (by
      classical
      exact
        (BandCircle) → ((BandCircle) → ((Fin 3) → ((ProtoTile) → ((List ProtoTile) → ((Fin (4 :
            ℕ) → CircleCoordinates) → ((GaussianInt) → ((List PartialOdometer) → (∀ {α : Type}, ∀
            {β : Type}, ∀ (xs : List α), ∀ (ys : List β), xs.length = ys.length → ∀ x, x ∈ xs → ∃
            y, (x, y) ∈ xs.zip ys)))))))) ) := by
  classical
  intro C₀ Cᵢ i T₀' tiles q' touter hs α β xs
  induction xs with
  | nil => intro ys h x hx; simp at hx
  | cons a xs ih =>
    intro ys h x hx
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨b, by simp⟩
      · obtain ⟨y, hy⟩ := ih ys (by omega) x hx
        exact ⟨y, by
          simp only [List.zip_cons_cons, List.mem_cons]
          right
          exact hy⟩

private theorem zip_fst_mem :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {xs : List α}, ∀ {ys : List β}, ∀ {x : α}, ∀ {y : β}, (x,
            y) ∈ xs.zip ys → x ∈ xs ) := by
  classical
  intro α β xs
  induction xs with
  | nil => intro ys x y h; simp at h
  | cons a xs ih =>
    intro ys x y h
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      simp only [List.mem_cons]
      rcases h with h | h
      · left; exact congrArg Prod.fst h
      · right; exact ih h

private theorem zip_pair_unique :
    (by
      classical
      exact
        (∀ {α : Type}, ∀ {β : Type}, ∀ {xs : List α}, ∀ {ys : List β}, ∀ {x : α}, ∀ {y : β}, (x,
            y) ∈ xs.zip ys → x ∈ xs) → (∀ {α : Type}, ∀ {β : Type}, ∀ {xs : List α}, ∀
            {ys : List β}, (xs.Pairwise (fun x y => x ≠ y)) → (∀ {x : α}, ∀ {y : β}, ∀ {z : β},
            (x, y) ∈ xs.zip ys → (x, z) ∈ xs.zip ys → y = z)) ) := by
  classical
  intro zip_fst_mem α β xs
  induction xs with
  | nil => intro ys hp x y z hy hz; simp at hy
  | cons a xs ih =>
    intro ys hp x y z hy hz
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      cases hp with
      | cons hhead htail =>
        simp only [List.zip_cons_cons, List.mem_cons] at hy hz
        rcases hy with hy | hy
        · rcases hz with hz | hz
          · have hY : y = b := congrArg Prod.snd hy
            have hZ : z = b := congrArg Prod.snd hz
            exact hY.trans hZ.symm
          · have hx := zip_fst_mem hz
            have hxeq : x = a := congrArg Prod.fst hy
            exact False.elim ((hhead x hx) hxeq.symm)
        · rcases hz with hz | hz
          · have hx := zip_fst_mem hy
            have hxeq : x = a := congrArg Prod.fst hz
            exact False.elim ((hhead x hx) hxeq.symm)
          · exact ih htail hy hz

private theorem hreverseTilesNonempty :
    (by
      classical
      exact
        ∀ (Rplus : ProtoTile), ∀ (reverseTiles : List ProtoTile), (reverseTiles.head? = some
            Rplus) → (reverseTiles ≠ []) ) := by
  classical
  intro Rplus reverseTiles hreverseHead h
  rw [h] at hreverseHead
  simp at hreverseHead

private theorem forall2_length :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {r : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
            List.Forall₂ r xs ys → xs.length = ys.length ) := by
  classical
  intro α β r xs ys hxy
  induction hxy with
  | nil => rfl
  | cons hxy htail ih => simp only [List.length_cons, ih]

private theorem forall2_mem_right :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {r : α → β → Prop}, ∀ {xs : List α}, ∀ {ys : List β},
            List.Forall₂ r xs ys → ∀ {y}, y ∈ ys → ∃ x, x ∈ xs ∧ r x y ) := by
  classical
  intro α β r xs ys hxy
  induction hxy with
  | nil => intro y hy; simp at hy
  | @cons x y xs ys hxy htail ih =>
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨x, by simp, hxy⟩
    · obtain ⟨x', hx', hrel⟩ := ih hz
      exact ⟨x', by simp [hx'], hrel⟩

private theorem trimSublist :
    (by
      classical
      exact
        ∀ (xs : List ProtoTile), ((xs.drop 1).dropLast).Sublist xs ) := by
  classical
  intro xs
  exact (List.dropLast_sublist (xs.drop 1)).trans (List.drop_sublist 1 xs)

private theorem hreverseZipDropOne :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt), ∀ (reverseTiles : List ProtoTile), ∀ (couter :
            GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        ∀ (hs : List PartialOdometer),
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        let gs := hs.mapIdx transformAt
        (reverseTiles.drop 1).zip (gs.drop 1) = (reverseTiles.zip gs).drop 1 ) := by
  classical
  intro centerShift reverseTiles couter eouter a b eback bplus hs constAt transformAt gs
  rw [List.zip_eq_zipWith, List.zip_eq_zipWith, List.drop_zipWith]

private theorem hreverseDropLength :
    (by
      classical
        exact
        (∀ (centerShift : GaussianInt),
          ∀ (reverseTiles : List ProtoTile),
            (∀ (couter : GaussianInt),
              ∀ (eouter : ℤ),
                let a : GaussianInt := -couter;
                let b : Int := -eouter;
                ∀ (eback : ℤ),
                  let bplus : Int := -eback;
                  ∀ (hs : List PartialOdometer),
                    let constAt : Nat → Int := fun n =>
                      if n = 0 then 0 else if n + 1 = hs.length then bplus else b;
                    let transformAt : Nat → PartialOdometer → PartialOdometer :=
                      fun n h =>
                      PartialOdometerAffineTranslate (PartialOdometerHalfTurn h)
                        centerShift a (constAt n);
                    let gs := hs.mapIdx transformAt;
                    (reverseTiles.length = gs.length) →
                      ((reverseTiles.drop 1).length = (gs.drop 1).length)))) := by
  classical
  intro centerShift reverseTiles couter eouter a b eback bplus hs constAt transformAt gs
      hreverseFullLength
  simp only [List.length_drop] at hreverseFullLength ⊢
  omega

private theorem hreverseInteriorLength :
    (by
      classical
        exact
        (∀ (centerShift : GaussianInt),
          ∀ (reverseTiles : List ProtoTile),
            (∀ (couter : GaussianInt),
              ∀ (eouter : ℤ),
                let a : GaussianInt := -couter;
                let b : Int := -eouter;
                ∀ (eback : ℤ),
                  let bplus : Int := -eback;
                  ∀ (hs : List PartialOdometer),
                    let constAt : Nat → Int := fun n =>
                      if n = 0 then 0 else if n + 1 = hs.length then bplus else b;
                    let transformAt : Nat → PartialOdometer → PartialOdometer :=
                      fun n h =>
                      PartialOdometerAffineTranslate (PartialOdometerHalfTurn h)
                        centerShift a (constAt n);
                    let gs := hs.mapIdx transformAt;
                    ((reverseTiles.drop 1).length = (gs.drop 1).length) →
                      (((reverseTiles.drop 1).dropLast).length =
                        ((gs.drop 1).dropLast).length)))) := by
  classical
  intro centerShift reverseTiles couter eouter a b eback bplus hs constAt transformAt gs
      hreverseDropLength
  simp only [List.length_dropLast] at hreverseDropLength ⊢
  omega

private theorem hreverseZipInteriorEq :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt), ∀ (reverseTiles : List ProtoTile), ∀ (couter :
            GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        ∀ (hs : List PartialOdometer),
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        let gs := hs.mapIdx transformAt
        (∀ {α : Type}, ∀ {β : Type}, ∀ (xs : List α), ∀ (ys : List β), xs.length = ys.length →
            xs.dropLast.zip ys.dropLast = (xs.zip ys).dropLast) → (((reverseTiles.drop 1).zip
            (gs.drop 1) = (reverseTiles.zip gs).drop 1) → (((reverseTiles.drop 1).length =
            (gs.drop 1).length) → ((((reverseTiles.drop 1).dropLast).zip ((gs.drop 1).dropLast))
            = ((reverseTiles.zip gs).drop 1).dropLast))) ) := by
  classical
  intro centerShift reverseTiles couter eouter a b eback bplus hs constAt transformAt gs
      zip_dropLast_eq hreverseZipDropOne hreverseDropLength
  rw [← hreverseZipDropOne]
  exact zip_dropLast_eq (reverseTiles.drop 1) (gs.drop 1) hreverseDropLength

private theorem htilesPairwise :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (Cᵢ : BandCircle), ∀ (i : Fin 3), ∀
            (horientationExists : ∃ o : Bool, Cᵢ.1.1.1 = 1 → UnitOccurrenceOrientation q i o),
        let orientation := Classical.choose horientationExists
        ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List
            ProtoTile), (TileString Cᵢ orientation base Rminus Rplus tiles) → (tiles.Pairwise
            (fun T U => T ≠ U)) ) := by
  classical
  intro q Cᵢ i horientationExists orientation base Rminus Rplus tiles hstring
  rcases hstring with ⟨_, _, _, hpairwise, _, _, _⟩
  exact hpairwise

private theorem hTgTrim :
    (by
      classical
      exact
        ∀ (centerShift : GaussianInt), ∀ (reverseTiles : List ProtoTile), ∀ (couter :
            GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        ∀ (eback : ℤ),
        let bplus : Int := -eback
        ∀ (hs : List PartialOdometer),
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        let gs := hs.mapIdx transformAt
        ((((reverseTiles.drop 1).dropLast).zip ((gs.drop 1).dropLast)) = ((reverseTiles.zip
            gs).drop 1).dropLast) → (∀ (T : ProtoTile), ∀ (g : PartialOdometer), ((T, g) ∈
            (List.drop (1 : ℕ) reverseTiles).dropLast.zip (List.drop (1 : ℕ) gs).dropLast) → ((T,
            g) ∈ ((reverseTiles.zip gs).drop 1).dropLast)) ) := by
  classical
  intro centerShift reverseTiles couter eouter a b eback bplus hs constAt transformAt gs
      hreverseZipInteriorEq T g hTgInterior
  rw [← hreverseZipInteriorEq]
  exact hTgInterior

private theorem hUhTrim :
    (by
      classical
      exact
        ∀ (tiles : List ProtoTile), ∀ (hs : List PartialOdometer), ((((tiles.drop
            1).dropLast).zip ((hs.drop 1).dropLast)) = ((tiles.zip hs).drop 1).dropLast) → (∀ (U
            : ProtoTile), ∀ (h : PartialOdometer), ((U, h) ∈ (List.drop (1 : ℕ)
            tiles).dropLast.zip (List.drop (1 : ℕ) hs).dropLast) → ((U, h) ∈ ((tiles.zip hs).drop
            1).dropLast)) ) := by
  classical
  intro tiles hs hzipInteriorEq U h hUhInterior
  rw [← hzipInteriorEq]
  exact hUhInterior

private theorem hTband :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates)
          (Cᵢ : BandCircle) (i : Fin (3 : ℕ))
          (horientationExists :
            ∃ (o : Bool),
              Cᵢ.1.1.1 =
                  (1 : ℤ) →
                UnitOccurrenceOrientation q i o),
          let orientation := Classical.choose horientationExists;
          ∀ (base Rminus Rplus : ProtoTile)
            (reverseTiles : List ProtoTile),
            TileString Cᵢ orientation base Rplus Rminus
                reverseTiles →
              (∀ (xs : List ProtoTile),
                  (List.drop (1 : ℕ) xs).dropLast.Sublist xs) →
                ∀ T ∈ (List.drop (1 : ℕ) reverseTiles).dropLast,
                  BandPrototile
                    Cᵢ.1.1
                    T) := by
  classical
  intro q Cᵢ i horientationExists orientation base Rminus Rplus reverseTiles hreverse
      trimSublist T hT
  rcases hreverse with ⟨hbaseR, _, _, _, hmemR, _, _⟩
  have hTmem : T ∈ reverseTiles := (trimSublist reverseTiles).subset hT
  rcases hmemR T hTmem with ⟨v, hv, rfl⟩
  exact BandPrototileTranslation Cᵢ.1.1 base v hbaseR

private theorem hcentralTarget :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀
            (centerShift : GaussianInt), ∀ (couter : GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        let houterAffine := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift a b
        let cellRelation : ProtoTile → ProtoTile → Prop := fun T U =>
          (TileTranslation (TileHalfTurn T) centerShift).cells = U.cells
        ∀ (T : ProtoTile), ∀ (g : PartialOdometer), ∀ (U : ProtoTile), ∀ (h : PartialOdometer),
            (cellRelation (U, h).1 (T, g).1 ∧ (T, g).2 = PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn (U, h).2) centerShift a b) → ((AncestorOdometer Cᵢ.1.1
            C₀.1.1 (TileTranslation (TileHalfTurn U) centerShift) (TileTranslation (TileHalfTurn
            T₀) centerShift) (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h)
            centerShift a b) (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h₀)
            centerShift a b)) → (AncestorOdometer Cᵢ.1.1 C₀.1.1 (TileTranslation (TileHalfTurn U)
            centerShift) (TileTranslation (TileHalfTurn T₀) centerShift) g houterAffine)) ) := by
  classical
  intro C₀ Cᵢ T₀ h₀ centerShift couter eouter a b houterAffine cellRelation T g U h hpairedData
      hcentral
  have hfunc : g = PartialOdometerAffineTranslate
      (PartialOdometerHalfTurn h) centerShift a b := by
    simpa using hpairedData.2
  rw [hfunc]
  simpa [houterAffine] using hcentral

end OpposingBoundaryGeometry

namespace OpposingBoundaryConclusion

private theorem opposingBoundaryConclusion :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (ProperBandQuadruple q) → (∀ (C₀ : BandCircle), ∀ (Cᵢ
            : BandCircle), ∀ (i : Fin 3), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → ((q i.succ = Cᵢ.1.1) →
            (∀ (T₀ : ProtoTile), ∀ (T₀' : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (h₀' :
            PartialOdometer), ((0 : ℤ) < Cᵢ.1.1.1) → (∀ (p₀ : Real × Real), ∀ (horientationExists
            : ∃ o : Bool, Cᵢ.1.1.1 = 1 → UnitOccurrenceOrientation q i o),
        let orientation := Classical.choose horientationExists
        ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List
            ProtoTile), ∀ (hseed : PartialOdometer), (BoundaryString C₀ Cᵢ i orientation T₀ base
            Rminus Rplus tiles) → ((Fin (4 : ℕ) → CircleCoordinates) → ((TileString Cᵢ
            orientation base Rminus Rplus tiles) → (∀ (centerShift : GaussianInt), ∀
            (reverseTiles : List ProtoTile), (TileString Cᵢ orientation base Rplus Rminus
            reverseTiles) → (((TileTranslation (TileHalfTurn Rminus) centerShift).cells =
            Rplus.cells) → (((TileTranslation (TileHalfTurn Rplus) centerShift).cells =
            Rminus.cells) → ((List.Forall₂ (fun (T U : ProtoTile) => (TileTranslation
            (TileHalfTurn T) centerShift).cells = U.cells) tiles reverseTiles) → (
        let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
        let pplus := p₀ + (1 / 2 : Real) • GaussianRealPoint
          (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))
        let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
        let hminus := PartialOdometerAffineTranslate hseed 0 d 0
        (TileOdometer Cᵢ.1.1 Rminus hminus) → ((PartialOdometerSlope hminus = some pminus) → ((0
            < C₀.1.1.1) → (
        let Tbar := TileTranslation (TileHalfTurn T₀) centerShift
        (BandPrototile C₀.1.1 T₀') → ((Tbar.cells = T₀'.cells) → ((GaussianInt) → (∀ (couter :
            GaussianInt), ∀ (eouter : ℤ),
        let a : GaussianInt := -couter
        let b : Int := -eouter
        let houterAffine := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn h₀) centerShift a b
        (h₀' = houterAffine) → (
        let hplus := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hminus) centerShift a 0
        (TileOdometer Cᵢ.1.1 Rplus hplus) → ((PartialOdometerSlope hplus = some pplus) → (∀
            (eback : ℤ),
        let bplus : Int := -eback
        let hminusBack := PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn hplus) centerShift a bplus
        (hminus = hminusBack) → ((tiles.head? = some Rminus) → ((tiles.getLast? = some Rplus) →
            ((2 ≤ tiles.length) → (∀ (hs : List PartialOdometer), (hs.head? = some hminus) →
            ((hs.getLast? = some hplus) → ((OdometerStringRespect Cᵢ orientation base Rminus
            Rplus tiles hs) → ((∀ T ∈ (List.drop (1 : ℕ) tiles).dropLast, ∃ (h :
            PartialOdometer), (T, h) ∈ tiles.zip hs ∧ AncestorOdometer Cᵢ.1.1 C₀.1.1 T T₀ h h₀) →
            ((hs.length = tiles.length) → ((2 ≤ hs.length) → (
        let constAt : Nat → Int := fun n =>
          if n = 0 then 0 else if n + 1 = hs.length then bplus else b
        let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
          PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
        let gs := hs.mapIdx transformAt
        (∀ n, ∀ l, List.Forall₂ (fun h g => ∃ c : Int, g = PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn h) centerShift a c) l (l.mapIdx (fun j h => transformAt (n +
            j) h))) → ((List.Forall₂ (fun h g => ∃ c : Int, g = PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn h) centerShift a c) hs gs) → (exists orientation : Bool,
            exists centerShift : GaussianInt, exists base Rminus Rplus : ProtoTile, exists tiles
            reverseTiles : List ProtoTile, exists hs reverseHs : List PartialOdometer, exists
            hminus hplus : PartialOdometer, exists pminus pplus : Real × Real, exists a :
            GaussianInt, exists b bminus bplus : Int, BoundaryString C₀ Cᵢ i orientation T₀ base
            Rminus Rplus tiles /\ (TileTranslation (TileHalfTurn Rminus) centerShift).cells =
            Rplus.cells /\ (TileTranslation (TileHalfTurn Rplus) centerShift).cells =
            Rminus.cells /\ List.Forall₂ (fun T U => (TileTranslation (TileHalfTurn T)
            centerShift).cells = U.cells) tiles reverseTiles /\ TileString Cᵢ orientation base
            Rplus Rminus reverseTiles /\ OdometerStringRespect Cᵢ orientation base Rminus Rplus
            tiles hs /\ OdometerStringRespect Cᵢ orientation base Rplus Rminus reverseTiles
            reverseHs /\ hs.head? = some hminus /\ hs.getLast? = some hplus /\ reverseHs.head? =
            some hplus /\ reverseHs.getLast? = some hminus /\ TileOdometer Cᵢ.1.1 Rminus hminus
            /\ TileOdometer Cᵢ.1.1 Rplus hplus /\ PartialOdometerSlope hminus = some pminus /\
            PartialOdometerSlope hplus = some pplus /\ pminus - p₀ = (1 / 2 : Real) •
            GaussianRealPoint (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
            /\ pplus - p₀ = (1 / 2 : Real) • GaussianRealPoint (BandVectors.2 (q i.succ) (q 0) +
            BandVectors.2 (q 0) (q i.succ)) /\ h₀' = PartialOdometerAffineTranslate
            (PartialOdometerHalfTurn h₀) centerShift a b /\ hplus =
            PartialOdometerAffineTranslate (PartialOdometerHalfTurn hminus) centerShift a bminus
            /\ hminus = PartialOdometerAffineTranslate (PartialOdometerHalfTurn hplus)
            centerShift a bplus /\ (forall T, T ∈ (tiles.drop 1).dropLast -> exists h, (T, h) ∈
            tiles.zip hs /\ AncestorOdometer Cᵢ.1.1 C₀.1.1 T T₀ h h₀) /\ forall T, T ∈
            (reverseTiles.drop 1).dropLast -> exists h, (T, h) ∈ reverseTiles.zip reverseHs /\
            AncestorOdometer Cᵢ.1.1 C₀.1.1 T T₀' h h₀')))))))))))))))))))))))))))))))) ) := by
  classical
  intro q hq C₀ Cᵢ i hC₀ hCᵢ T₀ T₀' h₀ h₀' hpositive p₀ horientationExists orientation base
      Rminus Rplus tiles hseed hboundaryOriginal q' hstring centerShift reverseTiles hreverse
      hminusCells hplusCells hcellPairs pminus pplus d hminus hOminus hsminus hC₀positive Tbar
      hT₀'band houterCells touter couter eouter a b houterAffine houterAffineEq hplus hOplus
      hsplus eback bplus hminusBack hminusBackEq htilesHead htilesLast htilesLength hs hhsHead
      hhsLast hrespect hancestorForward hlengthEq hlengthHs constAt transformAt gs
      transformForall htransform
  have hgsHead := OpposingBoundaryGeometry.hgsHead q i hseed centerShift couter eouter eback hs
      hhsHead
  have hgsLast := (show
      gs.getLast? = some hminus
    from by
      classical
      rw [List.getLast?_mapIdx, hhsLast]
      have hlastIndex : hs.length - 1 + 1 = hs.length := by omega
      have hlastNotZero : hs.length - 1 ≠ 0 := by omega
      simp only [Option.map_some]
      apply congrArg some
      dsimp [transformAt, constAt]
      rw [ite_eq_right hlastNotZero, ite_eq_left hlastIndex]
      exact hminusBackEq.symm)
  let cellRelation : ProtoTile → ProtoTile → Prop := fun T U =>
    (TileTranslation (TileHalfTurn T) centerShift).cells = U.cells
  have hinteriorCells := OpposingBoundaryGeometry.hinteriorCells tiles centerShift
      reverseTiles hcellPairs htilesLength (OpposingBoundaryGeometry.forall2_dropLast)
  have interiorTransforms := OpposingBoundaryGeometry.interiorTransforms C₀ Cᵢ i T₀' tiles q'
      centerShift touter couter eouter eback hs
  have hgsTail := OpposingBoundaryGeometry.hgsTail q i hseed centerShift couter eouter eback hs
      hhsHead
  have htailLength := OpposingBoundaryGeometry.htailLength q i hseed hs hhsHead
  have hinteriorTransforms := OpposingBoundaryGeometry.hinteriorTransforms
      centerShift couter eouter eback hs interiorTransforms hgsTail htailLength
  have hinteriorZip : List.Forall₂
      (fun X Y => cellRelation X.1 Y.1 ∧
        Y.2 = PartialOdometerAffineTranslate
          (PartialOdometerHalfTurn X.2) centerShift a b)
      (((tiles.drop 1).dropLast).zip ((hs.drop 1).dropLast))
      (((reverseTiles.drop 1).dropLast).zip ((gs.drop 1).dropLast)) :=
    (OpposingBoundaryGeometry.zipForall₂) hinteriorCells hinteriorTransforms
  have zip_dropLast_eq :
    ∀ {α β : Type} (xs : List α) (ys : List β),
          xs.length = ys.length →
          xs.dropLast.zip ys.dropLast = (xs.zip ys).dropLast :=
              @OpposingBoundaryGeometry.zip_dropLast_eq C₀ Cᵢ i T₀' tiles q' touter hs
  have hzipDropOne := OpposingBoundaryGeometry.hzipDropOne q i Rminus tiles hseed htilesHead hs
      hhsHead
  have hzipInteriorEq := OpposingBoundaryGeometry.hzipInteriorEq tiles hs zip_dropLast_eq
      hzipDropOne (OpposingBoundaryGeometry.htailOdoLength q i Rminus tiles hseed htilesHead hs
          hhsHead hlengthEq)
  have zip_mem_left :
    ∀ {α β : Type} (xs : List α) (ys : List β),
          xs.length = ys.length → ∀ x, x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys :=
              @OpposingBoundaryGeometry.zip_mem_left C₀ Cᵢ i T₀' tiles q' touter hs
  have zip_fst_mem :
    ∀ {α β : Type} {xs : List α} {ys : List β}
          {x : α} {y : β}, (x, y) ∈ xs.zip ys → x ∈ xs := @OpposingBoundaryGeometry.zip_fst_mem
  have zip_pair_unique :
    ∀ {α β : Type} {xs : List α} {ys : List β}
          (hp : xs.Pairwise (fun x y => x ≠ y)) {x : α} {y z : β},
          (x, y) ∈ xs.zip ys → (x, z) ∈ xs.zip ys → y = z :=
              @OpposingBoundaryGeometry.zip_pair_unique zip_fst_mem
  have hreverseRespect := OdometerStringRespectRegularFamilyCentralCovariance
    Cᵢ orientation base Rminus Rplus tiles reverseTiles hs gs centerShift a
    hrespect hreverse hcellPairs htransform
  have hreverseHead : reverseTiles.head? = some Rplus := hreverse.2.1
  have hreverseTilesNonempty := OpposingBoundaryGeometry.hreverseTilesNonempty Rplus reverseTiles
      hreverseHead
  have hgsNonempty : gs ≠ [] := by
    have hhead : gs.head? = some hplus := hgsHead
    intro h
    simp [h] at hhead
  have forall2_mem_right :
    ∀ {α β : Type} {r : α → β → Prop}
          {xs : List α} {ys : List β}, List.Forall₂ r xs ys →
          ∀ {y}, y ∈ ys → ∃ x, x ∈ xs ∧ r x y := @OpposingBoundaryGeometry.forall2_mem_right
  have trimSublist := OpposingBoundaryGeometry.trimSublist
  have hreverseFullLength := (OpposingBoundaryGeometry.forall2_length) hreverseRespect.2.1
  have hreverseDropLength := OpposingBoundaryGeometry.hreverseDropLength
      centerShift reverseTiles couter eouter eback hs hreverseFullLength
  have hreverseInteriorLength := OpposingBoundaryGeometry.hreverseInteriorLength centerShift
      reverseTiles couter eouter eback hs hreverseDropLength
  have hreverseZipInteriorEq := OpposingBoundaryGeometry.hreverseZipInteriorEq centerShift
      reverseTiles couter eouter eback hs zip_dropLast_eq
      (OpposingBoundaryGeometry.hreverseZipDropOne centerShift reverseTiles couter eouter eback
      hs) hreverseDropLength
  have hreverseZipTrim : ((reverseTiles.zip gs).drop 1).dropLast.Sublist
      (reverseTiles.zip gs) :=
    (List.dropLast_sublist ((reverseTiles.zip gs).drop 1)).trans
      (List.drop_sublist 1 (reverseTiles.zip gs))
  have hsourceZipTrim : ((tiles.zip hs).drop 1).dropLast.Sublist
      (tiles.zip hs) :=
    (List.dropLast_sublist ((tiles.zip hs).drop 1)).trans
      (List.drop_sublist 1 (tiles.zip hs))
  have htilesPairwise := OpposingBoundaryGeometry.htilesPairwise q Cᵢ i horientationExists base
      Rminus Rplus tiles hstring
  have hstrict : Cᵢ.1.1.1 < C₀.1.1.1 := by
    simpa only [hCᵢ, hC₀] using hq.2 i
  refine ⟨orientation, centerShift, base, Rminus, Rplus, tiles, reverseTiles,
    hs, gs, hminus, hplus, pminus, pplus, a, b, (0 : Int), bplus, ?_⟩
  refine ⟨hboundaryOriginal, hminusCells, hplusCells, hcellPairs, hreverse,
    hrespect, hreverseRespect, hhsHead, hhsLast, hgsHead, hgsLast,
    hOminus, hOplus, hsminus, hsplus, ?_⟩
  refine ⟨(by dsimp [pminus]; abel), ?_⟩
  refine ⟨(by dsimp [pplus]; abel), ?_⟩
  refine ⟨(by simpa [houterAffine] using houterAffineEq), ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨hminusBackEq, ?_⟩
  refine ⟨hancestorForward, ?_⟩
  intro T hT
  obtain ⟨g, hTgInterior⟩ := zip_mem_left
    ((reverseTiles.drop 1).dropLast) ((gs.drop 1).dropLast)
    hreverseInteriorLength T hT
  have hTgTrim := OpposingBoundaryGeometry.hTgTrim centerShift reverseTiles couter eouter eback
      hs hreverseZipInteriorEq T g hTgInterior
  rcases forall2_mem_right hinteriorZip hTgInterior with
    ⟨⟨U, h⟩, hUhInterior, hpairedData⟩
  have hUinterior : U ∈ (tiles.drop 1).dropLast :=
    zip_fst_mem hUhInterior
  rcases hancestorForward U hUinterior with ⟨h', hUhFull, hancestor⟩
  have hUhFull' : (U, h) ∈ tiles.zip hs := hsourceZipTrim.subset
      (OpposingBoundaryGeometry.hUhTrim tiles hs hzipInteriorEq U h hUhInterior)
  have hhh' : h = h' := zip_pair_unique htilesPairwise hUhFull' hUhFull
  subst h'
  have hcentral := AncestorOdometerCentralCovariance
    Cᵢ.1.1 C₀.1.1 U T₀ h h₀ centerShift a b hancestor
  have hinner := AncestorOdometerInnerSupportNormalization
    Cᵢ.1.1 C₀.1.1 (TileTranslation (TileHalfTurn U) centerShift)
    T (TileTranslation (TileHalfTurn T₀) centerShift) g houterAffine
    hpositive hstrict (OpposingBoundaryGeometry.hcentralTarget C₀ Cᵢ T₀ h₀ centerShift couter
        eouter T g U h hpairedData hcentral) (OpposingBoundaryGeometry.hTband q Cᵢ i
        horientationExists base Rminus Rplus reverseTiles hreverse trimSublist T hT) hpairedData.1
  have houter := AncestorOdometerOuterSupportNormalization
    Cᵢ.1.1 C₀.1.1 T (TileTranslation (TileHalfTurn T₀) centerShift)
    T₀' g houterAffine hC₀positive hstrict hinner hT₀'band houterCells
  refine ⟨g, hreverseZipTrim.subset hTgTrim, ?_⟩
  simpa [houterAffineEq] using houter

end OpposingBoundaryConclusion

theorem OpposingBoundaryOdometerStrings
    (q : Fin 4 -> CircleCoordinates) (hq : ProperBandQuadruple q)
    (C₀ Cᵢ : BandCircle) (i : Fin 3)
    (hC₀ : q 0 = C₀.1.1) (hCᵢ : q i.succ = Cᵢ.1.1)
    (T₀ T₀' : ProtoTile) (h₀ h₀' : PartialOdometer)
    (hO₀ : TileOdometer C₀.1.1 T₀ h₀)
    (hO₀' : TileOdometer C₀.1.1 T₀' h₀')
    (hpositive : 0 < Cᵢ.1.1.1)
    (p₀ p₀' : Real × Real)
    (hs₀ : PartialOdometerSlope h₀ = some p₀)
    (hs₀' : PartialOdometerSlope h₀' = some p₀')
    (hcentroid : TileCentroid T₀' - TileCentroid T₀ =
      GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (hslope : p₀' - p₀ =
      GaussianRealPoint (BandVectors.2 (q i.succ) (q 0))) :
    exists orientation : Bool, exists centerShift : GaussianInt,
    exists base Rminus Rplus : ProtoTile,
    exists tiles reverseTiles : List ProtoTile,
    exists hs reverseHs : List PartialOdometer,
    exists hminus hplus : PartialOdometer,
    exists pminus pplus : Real × Real,
    exists a : GaussianInt, exists b bminus bplus : Int,
      BoundaryString C₀ Cᵢ i orientation T₀ base Rminus Rplus tiles /\
      (TileTranslation (TileHalfTurn Rminus) centerShift).cells =
        Rplus.cells /\
      (TileTranslation (TileHalfTurn Rplus) centerShift).cells =
        Rminus.cells /\
      List.Forall₂ (fun T U =>
        (TileTranslation (TileHalfTurn T) centerShift).cells = U.cells)
        tiles reverseTiles /\
      TileString Cᵢ orientation base Rplus Rminus reverseTiles /\
      OdometerStringRespect Cᵢ orientation base Rminus Rplus tiles hs /\
      OdometerStringRespect Cᵢ orientation base Rplus Rminus
        reverseTiles reverseHs /\
      hs.head? = some hminus /\ hs.getLast? = some hplus /\
      reverseHs.head? = some hplus /\ reverseHs.getLast? = some hminus /\
      TileOdometer Cᵢ.1.1 Rminus hminus /\
      TileOdometer Cᵢ.1.1 Rplus hplus /\
      PartialOdometerSlope hminus = some pminus /\
      PartialOdometerSlope hplus = some pplus /\
      pminus - p₀ = (1 / 2 : Real) • GaussianRealPoint
        (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ)) /\
      pplus - p₀ = (1 / 2 : Real) • GaussianRealPoint
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)) /\
      h₀' = PartialOdometerAffineTranslate (PartialOdometerHalfTurn h₀)
        centerShift a b /\
      hplus = PartialOdometerAffineTranslate (PartialOdometerHalfTurn hminus)
        centerShift a bminus /\
      hminus = PartialOdometerAffineTranslate (PartialOdometerHalfTurn hplus)
        centerShift a bplus /\
      (forall T, T ∈ (tiles.drop 1).dropLast ->
        exists h, (T, h) ∈ tiles.zip hs /\
          AncestorOdometer Cᵢ.1.1 C₀.1.1 T T₀ h h₀) /\
      forall T, T ∈ (reverseTiles.drop 1).dropLast ->
        exists h, (T, h) ∈ reverseTiles.zip reverseHs /\
          AncestorOdometer Cᵢ.1.1 C₀.1.1 T T₀' h h₀' := by
-- BODY
  classical
  have horientationExists := OpposingBoundaryGeometry.horientationExists q hq Cᵢ i hCᵢ
  let orientation := Classical.choose horientationExists
  have hforward := ForwardBoundaryStringData q hq C₀ Cᵢ i hC₀ hCᵢ
    orientation T₀ h₀ hO₀ hpositive (Classical.choose_spec horientationExists)
  obtain ⟨base, Rminus, Rplus, tiles, hseed, pseed, pouter,
      hbase, hRminus, hRplus, hseedO, hseedSlope, hpouter,
      hseedSlopeData, hboundary⟩ := hforward
  have hboundaryOriginal := hboundary
  rcases hboundary with ⟨q', hq', hq0, hqi, hT₀band, hunitOrientation,
    hstring, hcentroidMinus, hcentroidPlus⟩
  obtain ⟨centerShift, reverseTiles, hcenters, hreverse, hminusCells,
      hplusCells, hcellPairs⟩ :=
    TileStringRegularFamilyCentralCovariance Cᵢ orientation base Rminus Rplus
      tiles hstring
  have tile_string_normalization :=
    @TileStringRegularFamilyCentralCovariance
  have odometer_string_normalization :=
    @OdometerStringRespectRegularFamilyCentralCovariance
  have ancestor_inner_normalization :=
    @AncestorOdometerInnerSupportNormalization
  have hpouter_eq : pouter = p₀ := OpposingBoundaryGeometry.hpouter_eq h₀ p₀ hs₀ pouter hpouter
  let pminus := p₀ + (1 / 2 : Real) • GaussianRealPoint
    (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))
  let pplus := p₀ + (1 / 2 : Real) • GaussianRealPoint
    (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))
  let d : GaussianInt := -BandVectors.2 (q ((i + 1).succ)) (q i.succ)
  let hminus := PartialOdometerAffineTranslate hseed 0 d 0
  have htranslateZero := OpposingBoundaryGeometry.htranslateZero Rminus
  have hOminus := OpposingBoundaryGeometry.hOminus q Cᵢ i Rminus hseed hseedO htranslateZero
  have hminusSlopeCalc : pseed + GaussianRealPoint d = pminus := by
    simpa [pminus, d, hpouter_eq] using hseedSlopeData
  have hsminus := OpposingBoundaryGeometry.hsminus q i p₀ hseed pseed hseedSlope hminusSlopeCalc
  have hC₀positive := OpposingBoundaryGeometry.hC₀positive q hq C₀ Cᵢ i hC₀ hCᵢ hpositive
  have positive_cells := BandPrototileNonempty.positive
  let hbar := PartialOdometerAffineTranslate
    (PartialOdometerHalfTurn h₀) centerShift 0 0
  let Tbar := TileTranslation (TileHalfTurn T₀) centerShift
  have hbarO := OpposingBoundaryGeometry.hbarO C₀ T₀ h₀ hO₀ centerShift
  have hbarBand : BandPrototile C₀.1.1 Tbar :=
    TileOdometerBandPrototile C₀.1.1 Tbar hbar hbarO
  have hT₀'band : BandPrototile C₀.1.1 T₀' :=
    TileOdometerBandPrototile C₀.1.1 T₀' h₀' hO₀'
  have hsumCentroid := OpposingBoundaryGeometry.hsumCentroid q C₀ Cᵢ i hC₀ hCᵢ T₀ Rminus Rplus q'
      hq0 hqi hcentroidMinus hcentroidPlus
  have houterCells := (BandPrototileCentroidUnique C₀.1.1 Tbar T₀'
    hbarBand hT₀'band (OpposingBoundaryGeometry.hcentbar q i T₀ T₀' hcentroid Rminus Rplus
        centerShift hcenters hsumCentroid)).1
  have hbarO' : TileOdometer C₀.1.1 T₀' hbar :=
    PositiveCurvatureTileOdometerSupportTransport C₀.1.1 Tbar T₀' hbar
      hC₀positive hbarO hT₀'band houterCells
  have houterUnique := TileOdometerTranslationUniqueness C₀.1.1 T₀' T₀'
    hbar h₀' hC₀positive hbarO' hO₀'
  obtain ⟨touter, htouter⟩ := houterUnique.exists
  rcases htouter with ⟨hcellShift, hanchorShift, houterData⟩
  rcases houterData with ⟨couter, eouter, hdomainShift, hvalueShift⟩
  have hT₀'cells : T₀'.cells.Nonempty :=
    positive_cells C₀.1.1 T₀' hC₀positive hT₀'band
  have htranslateInjective : Function.Injective (GaussianTranslation touter) :=
      OpposingBoundaryGeometry.htranslateInjective touter
  have hsumReShift := congrArg (fun s : Finset GaussianInt => ∑ z ∈ s, z.re) hcellShift
  rw [(TileTranslationFormulas T₀' touter).1,
    Finset.sum_image htranslateInjective.injOn] at hsumReShift
  simp only [GaussianTranslation, Zsqrtd.re_add] at hsumReShift
  rw [Finset.sum_add_distrib, Finset.sum_const] at hsumReShift
  simp only [nsmul_eq_mul] at hsumReShift
  have hcardCastNe : (T₀'.cells.card : Int) ≠ 0 := by
    exact_mod_cast hT₀'cells.card_pos.ne'
  have hmulRe : (T₀'.cells.card : Int) * touter.re = 0 := by
    linarith
  have htRe : touter.re = 0 := (mul_eq_zero.mp hmulRe).resolve_left hcardCastNe
  have hsumImShift := congrArg (fun s : Finset GaussianInt => ∑ z ∈ s, z.im) hcellShift
  rw [(TileTranslationFormulas T₀' touter).1,
    Finset.sum_image htranslateInjective.injOn] at hsumImShift
  simp only [GaussianTranslation, Zsqrtd.im_add] at hsumImShift
  rw [Finset.sum_add_distrib, Finset.sum_const] at hsumImShift
  simp only [nsmul_eq_mul] at hsumImShift
  have hmulIm : (T₀'.cells.card : Int) * touter.im = 0 := by
    linarith
  have htIm : touter.im = 0 := (mul_eq_zero.mp hmulIm).resolve_left hcardCastNe
  have htouterZero : touter = 0 := by
    apply Zsqrtd.ext <;> assumption
  have hbarDomains := OpposingBoundaryGeometry.hbarDomains h₀ h₀' centerShift touter hdomainShift
      htouterZero
  let a : GaussianInt := -couter
  let b : Int := -eouter
  let houterAffine := PartialOdometerAffineTranslate
    (PartialOdometerHalfTurn h₀) centerShift a b
  have hbarOuterDomain := OpposingBoundaryGeometry.hbarOuterDomain h₀ centerShift couter eouter
  have houterAffineEq : h₀' = houterAffine := OpposingBoundaryGeometry.houterAffineEq C₀ T₀' h₀
      h₀' hO₀' p₀' hs₀' centerShift houterUnique touter couter eouter hdomainShift hvalueShift
      htouterZero hbarDomains hbarOuterDomain (OpposingBoundaryGeometry.houterAffineDomain h₀ h₀'
      centerShift couter eouter hbarDomains hbarOuterDomain)
  have haSlope : p₀ + p₀' = GaussianRealPoint a := OpposingBoundaryGeometry.haSlope p₀ p₀' couter
      (Option.some.inj ((OpposingBoundaryGeometry.houterSlope h₀ p₀ centerShift couter eouter
      (OpposingBoundaryGeometry.hhalfSlope h₀ p₀ hs₀)).symm.trans (by
        change PartialOdometerSlope houterAffine = some p₀'
        rw [← houterAffineEq]
        exact hs₀')))
  let hplus := PartialOdometerAffineTranslate
    (PartialOdometerHalfTurn hminus) centerShift a 0
  have hplusRawO := OpposingBoundaryGeometry.hplusRawO q Cᵢ i Rminus hseed centerShift hOminus
      couter
  have hOplus : TileOdometer Cᵢ.1.1 Rplus hplus :=
    PositiveCurvatureTileOdometerSupportTransport Cᵢ.1.1
      (TileTranslation (TileHalfTurn Rminus) centerShift) Rplus hplus
      hpositive hplusRawO (OpposingBoundaryGeometry.hRplusBand Cᵢ
          base Rplus hbase hRplus)
          hminusCells
  have haRe : p₀.1 + p₀'.1 = (a.re : Real) := by
    simpa only [Prod.fst_add, GaussianRealPoint] using congrArg Prod.fst haSlope
  have haIm : p₀.2 + p₀'.2 = (a.im : Real) := by
    simpa only [Prod.snd_add, GaussianRealPoint] using congrArg Prod.snd haSlope
  have hplusSlopeCalc := OpposingBoundaryGeometry.hplusSlopeCalc q i p₀ p₀' couter
      (OpposingBoundaryGeometry.hslopeDifferenceRe q i p₀ p₀' hslope)
      (OpposingBoundaryGeometry.hslopeDifferenceIm q i p₀ p₀' hslope) haRe haIm
  have hsplus := OpposingBoundaryGeometry.hsplus q i p₀ hseed centerShift hsminus couter
      hplusSlopeCalc
  have finiteTranslationFix := OpposingBoundaryGeometry.finiteTranslationFix
  have hRminusBand := OpposingBoundaryGeometry.hRminusBand Cᵢ base
      Rminus hbase hRminus
  let hback := PartialOdometerAffineTranslate
    (PartialOdometerHalfTurn hplus) centerShift a 0
  have hbackO : TileOdometer Cᵢ.1.1 Rminus hback :=
    PositiveCurvatureTileOdometerSupportTransport Cᵢ.1.1
      (TileTranslation (TileHalfTurn Rplus) centerShift) Rminus hback
      hpositive (OpposingBoundaryGeometry.hbackRawO q Cᵢ i Rplus hseed centerShift couter hOplus)
          hRminusBand hplusCells
  have hbackUnique := TileOdometerTranslationUniqueness Cᵢ.1.1 Rminus Rminus
    hback hminus hpositive hbackO hOminus
  obtain ⟨tback, htback⟩ := hbackUnique.exists
  rcases htback with ⟨hbackCells, hbackAnchor, hbackData⟩
  rcases hbackData with ⟨cback, eback, hbackDomains, hbackValues⟩
  have hRminusCells : Rminus.cells.Nonempty :=
    positive_cells Cᵢ.1.1 Rminus hpositive hRminusBand
  have htbackZero := finiteTranslationFix Rminus tback hRminusCells hbackCells
  have hbackSameDomain := OpposingBoundaryGeometry.hbackSameDomain q i hseed centerShift couter
      tback hbackDomains htbackZero
  let hminusAffine := PartialOdometerAffineTranslate hminus 0 cback eback
  let bplus : Int := -eback
  let hminusBack := PartialOdometerAffineTranslate
    (PartialOdometerHalfTurn hplus) centerShift a bplus
  have hbackBackDomain := OpposingBoundaryGeometry.hbackBackDomain q i hseed centerShift couter
      eback
  have hminusBackEq := OpposingBoundaryGeometry.hminusBackEq q i hseed centerShift couter tback
      cback eback hbackValues htbackZero hbackSameDomain
      (OpposingBoundaryGeometry.hbackLinearZero q i p₀ hseed centerShift hsminus couter cback
      eback (OpposingBoundaryGeometry.hsback q i p₀ hseed centerShift couter
      (OpposingBoundaryGeometry.haEndpoint q i p₀ couter hplusSlopeCalc)
      (OpposingBoundaryGeometry.hhalfSlopePlus q i p₀ hseed centerShift couter hsplus))
      (OpposingBoundaryGeometry.hbackAffineEq q i hseed centerShift couter tback cback eback
      hbackValues htbackZero hbackSameDomain (OpposingBoundaryGeometry.hbackAffineDomain q i
      hseed centerShift couter cback eback hbackSameDomain))) hbackBackDomain
      (OpposingBoundaryGeometry.hminusBackDomain q i hseed centerShift couter eback
      hbackSameDomain hbackBackDomain)
  have hindexNe : (0 : Fin 4) ≠ i.succ := by
    fin_cases i <;> decide
  have hvectorNe : BandVectors.1 (q' 0) (q' i.succ) ≠ 0 :=
    VectorNonvanishing q' hq'.1 0 i.succ hindexNe (Or.inr (OpposingBoundaryGeometry.hpositive' Cᵢ
        i hpositive q' hqi))
  have htilesHead := OpposingBoundaryGeometry.htilesHead q Cᵢ i horientationExists base Rminus
      Rplus tiles hstring
  have htilesLast := OpposingBoundaryGeometry.htilesLast q Cᵢ i horientationExists base Rminus
      Rplus tiles hstring
  have htilesLength := OpposingBoundaryGeometry.htilesLength q C₀ Cᵢ i T₀ horientationExists base
      Rminus Rplus tiles hboundaryOriginal hstring centerShift reverseTiles hcellPairs
      (OpposingBoundaryGeometry.hRminusNeRplus i Rminus Rplus q'
      (OpposingBoundaryGeometry.hcentroidEndpoints i T₀ Rminus Rplus q' hcentroidMinus
      hcentroidPlus) hvectorNe (OpposingBoundaryGeometry.hgaussianPointZero)) htilesHead htilesLast
  have hrespectResult := BoundaryStringOdometerRespect q hq C₀ Cᵢ i
    hC₀ hCᵢ orientation T₀ base Rminus Rplus tiles h₀ hminus hplus
    hO₀ hboundaryOriginal hOminus hOplus p₀ pminus pplus hs₀ hsminus hsplus
    (by dsimp [pminus]; abel) (by dsimp [pplus]; abel)
  rcases hrespectResult with ⟨_, _, _, hs, hhsHead, hhsLast, hrespect, hancestorForward⟩
  have hlengthEq : hs.length = tiles.length := hrespect.2.1.length_eq.symm
  have hlengthHs : 2 ≤ hs.length := by omega
  let constAt : Nat → Int := fun n =>
    if n = 0 then 0 else if n + 1 = hs.length then bplus else b
  let transformAt : Nat → PartialOdometer → PartialOdometer := fun n h =>
    PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) centerShift a (constAt n)
  let gs := hs.mapIdx transformAt
  have transformForall := OpposingBoundaryGeometry.transformForall centerShift couter eouter
      eback hs
  exact (OpposingBoundaryConclusion.opposingBoundaryConclusion q hq C₀ Cᵢ i hC₀ hCᵢ T₀ T₀' h₀ h₀'
      hpositive p₀ horientationExists base Rminus Rplus tiles hseed hboundaryOriginal q' hstring
      centerShift reverseTiles hreverse hminusCells hplusCells hcellPairs hOminus hsminus
      hC₀positive hT₀'band houterCells touter couter eouter houterAffineEq hOplus hsplus eback
      hminusBackEq htilesHead htilesLast htilesLength hs hhsHead hhsLast hrespect
      hancestorForward hlengthEq hlengthHs transformForall (OpposingBoundaryGeometry.htransform
      centerShift couter eouter eback hs transformForall))


end ApollonianSuperharmonic

end

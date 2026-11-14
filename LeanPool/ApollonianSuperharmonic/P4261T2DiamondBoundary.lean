/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness

-- [TABLET NODE: P4261T2DiamondBoundary]

/-!
# P4261T2DiamondBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T2DiamondBoundary
    (K : DiamondParameter) (C : BandCircle)
    (hC : DiamondRecursiveQuadruple K 0 = C.1.1)
    (i : Fin 3) (T U : ProtoTile) (h k : PartialOdometer)
    (hh : TileOdometer C.1.1 T h) (hk : TileOdometer C.1.1 U k)
    (p r : Real × Real)
    (hp : PartialOdometerSlope h = some p) (hr : PartialOdometerSlope k = some r)
    (hc : TileCentroid U - TileCentroid T =
      GaussianRealPoint (BandVectors.1 (DiamondRecursiveQuadruple K i.succ)
        (DiamondRecursiveQuadruple K 0)))
    (hs : r - p =
      GaussianRealPoint (BandVectors.2 (DiamondRecursiveQuadruple K i.succ)
        (DiamondRecursiveQuadruple K 0))) :
    OdometerCompatibility h k := by
-- BODY
  classical
  obtain ⟨H, hH, hdomH, hfootH, hsquaresH, hvaluesH, hslopeH⟩ :=
    DiamondTileOdometerRestriction K
  have affine_eq (f l : PartialOdometer) (u a : GaussianInt) (b : Int)
      (hd : ∀ x, x ∈ f.domain ↔ x - u ∈ l.domain)
      (hv : ∀ x, x ∈ f.domain → f.value x = l.value (x - u) +
        a.re * x.re + a.im * x.im + b) :
      f = PartialOdometerAffineTranslate l u a b := by
    have hh : f.domain = (PartialOdometerAffineTranslate l u a b).domain := by
      ext x
      rw [(PartialOdometerAffineTranslateFormulas l u a b).2.1]
      exact hd x
    have vv : f.value = (PartialOdometerAffineTranslate l u a b).value := by
      funext x
      by_cases hx : x ∈ f.domain
      · rw [hv x hx, (PartialOdometerAffineTranslateFormulas l u a b).2.2.1 x
          (by rwa [← hh])]
      · rw [f.value_outside x hx,
          (PartialOdometerAffineTranslate l u a b).value_outside x (by rwa [← hh])]
    cases f
    simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
    exact ⟨hh, vv⟩
  obtain ⟨u, ⟨hcells, hanchor, a, b, hdom, hval⟩, _⟩ :=
    TileOdometerTranslationUniqueness C.1.1 T (DiamondTile K.1) h H C.2 hh
      (by simpa only [hC] using hH)
  obtain ⟨u', ⟨hcells', hanchor', a', b', hdom', hval'⟩, _⟩ :=
    TileOdometerTranslationUniqueness C.1.1 U (DiamondTile K.1) k H C.2 hk
      (by simpa only [hC] using hH)
  have hcentT := (ProtoTileObservableExtensionality T _ hcells hanchor).2.2.2.2
  have hcentU := (ProtoTileObservableExtensionality U _ hcells' hanchor').2.2.2.2
  rw [(TileTranslationFormulas (DiamondTile K.1) u).2.2.2.2.1] at hcentT
  rw [(TileTranslationFormulas (DiamondTile K.1) u').2.2.2.2.1] at hcentU
  let d := BandVectors.1 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0)
  let A := BandVectors.2 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0)
  have hshift : u' - u = d := by
    have hc0 := congrArg Prod.fst hc
    have hc1 := congrArg Prod.snd hc
    rw [hcentT, hcentU] at hc0 hc1
    apply Zsqrtd.ext
    · have he : (u'.re : Real) - (u.re : Real) = (d.re : Real) := by
        simpa [d, GaussianRealPoint] using hc0
      exact_mod_cast he
    · have he : (u'.im : Real) - (u.im : Real) = (d.im : Real) := by
        simpa [d, GaussianRealPoint] using hc1
      exact_mod_cast he
  have hpeq : p = ((K.1 : Real) / 2 + (a.re : Real),
      -((K.1 : Real) / 2) + (a.im : Real)) := by
    have hf := congrArg PartialOdometerSlope (affine_eq h H u a b hdom hval)
    rw [hp, (PartialOdometerAffineTranslateFormulas H u a b).2.2.2.2.2, hslopeH] at hf
    exact Option.some.inj hf
  have hreq : r = ((K.1 : Real) / 2 + (a'.re : Real),
      -((K.1 : Real) / 2) + (a'.im : Real)) := by
    have hf := congrArg PartialOdometerSlope (affine_eq k H u' a' b' hdom' hval')
    rw [hr, (PartialOdometerAffineTranslateFormulas H u' a' b').2.2.2.2.2, hslopeH] at hf
    exact Option.some.inj hf
  have hare : a'.re = a.re + A.re := by
    have he := congrArg Prod.fst hs
    rw [hpeq, hreq] at he
    have he' : (a'.re : Real) - (a.re : Real) = (A.re : Real) := by
      change ((K.1 : Real) / 2 + (a'.re : Real)) -
        ((K.1 : Real) / 2 + (a.re : Real)) = (A.re : Real) at he
      linarith
    exact_mod_cast (show (a'.re : Real) = (a.re : Real) + (A.re : Real) by linarith)
  have haim : a'.im = a.im + A.im := by
    have he := congrArg Prod.snd hs
    rw [hpeq, hreq] at he
    have he' : (a'.im : Real) - (a.im : Real) = (A.im : Real) := by
      change (-((K.1 : Real) / 2) + (a'.im : Real)) -
        (-((K.1 : Real) / 2) + (a.im : Real)) = (A.im : Real) at he
      linarith
    exact_mod_cast (show (a'.im : Real) = (a.im : Real) + (A.im : Real) by linarith)
  let c : Int := ![(K.1 : Int) * (K.1 + 1) / 2,
    -((K.1 : Int) * (K.1 + 1) / 2), -((K.1 : Int) * (K.1 - 2))] i
  have hcocycle : ∀ z, DiamondOdometer K (z + d) = DiamondOdometer K z +
      A.re * z.re + A.im * z.im + c := by
    have hG := (Classical.choose_spec (DiamondOdometerExistsUnique K)).1
    change (∀ z, DiamondOdometer K (z + ⟨0, -(2 * K.1 : Int)⟩) = _) ∧ _ at hG
    obtain ⟨_, _, hv1, hv2, hv3, ha1, ha2, ha3, _⟩ := DiamondCoordinateConfiguration K
    intro z
    fin_cases i
    · simpa [d, A, c, hv1, ha1, DiamondOdometer, add_assoc] using hG.2.1 z
    · simpa [d, A, c, hv2, ha2, DiamondOdometer, sub_eq_add_neg, add_assoc] using hG.2.2.1 z
    · simpa [d, A, c, hv3, ha3, DiamondOdometer, sub_eq_add_neg, add_assoc] using hG.1 z
  right
  refine ⟨A.re * u'.re + A.im * u'.im - c + b' - b, ?_⟩
  intro z hz hz'
  have hzH := (hdom z).mp hz
  have hzH' := (hdom' z).mp hz'
  have he := hcocycle (z - u')
  have hpoint : z - u' + d = z - u := by rw [← hshift]; abel
  rw [hpoint] at he
  rw [hval z hz, hval' z hz', hvaluesH _ hzH, hvaluesH _ hzH', he,
    hare, haim]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  ring

end ApollonianSuperharmonic

end

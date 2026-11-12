/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5352T2SourceCertificates
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: P5352T2LiteralNormalization]

/-!
# P5352T2LiteralNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5352T2LiteralNormalization (K : DiamondParameter) (hk : 1 < K.1)
    (j : Fin 4) (T U : ProtoTile) (h l : PartialOdometer)
    (p r : ℝ × ℝ) (g : IntegerLatticeFunction)
    (hT : TileOdometer ((DiamondRecursiveQuadruple K) 0) T h)
    (hU : TileOdometer ((DiamondRecursiveQuadruple K) j) U l)
    (hp : PartialOdometerSlope h = some p)
    (hr : PartialOdometerSlope l = some r)
    (he : GlobalOdometerExtends g h) (he' : GlobalOdometerExtends g l) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk j
    ∃ (w d a : GaussianInt) (B : Int) (f : IntegerLatticeFunction),
      (∀ x, x ∈ h.domain ↔ x - w ∈ FootprintVertices A.1) ∧
      (∀ x, x ∈ l.domain ↔ x - w - d ∈ FootprintVertices D.1) ∧
      (∀ x, x ∈ T.cells ↔ x - w ∈ A.1.cells) ∧
      (∀ x, x ∈ U.cells ↔ x - w - d ∈ D.1.cells) ∧
      (∀ x v, x ∈ FootprintVertices (TileTranslation T v) ↔
        x - w - v ∈ FootprintVertices A.1) ∧
      TileCentroid U - TileCentroid T =
        (D.2.2.1.1 - A.2.2.1.1 + d.re, D.2.2.1.2 - A.2.2.1.2 + d.im) ∧
      r.1 - p.1 = D.2.2.2.1 - A.2.2.2.1 + a.re ∧
      r.2 - p.2 = D.2.2.2.2 - A.2.2.2.2 + a.im ∧
      (∀ y, y ∈ FootprintVertices A.1 → f y = A.2.1 y) ∧
      (∀ y, y - d ∈ FootprintVertices D.1 →
        f y = D.2.1 (y - d) + a.re * y.re + a.im * y.im + B) ∧
      (∀ x, FourNeighborLaplacian g x = FourNeighborLaplacian f (x - w)) := by
-- BODY
  classical
  dsimp only
  let S := P5352T2Sources K hk
  have memtr (V : ProtoTile) (u x : GaussianInt) :
      x ∈ (TileTranslation V u).cells ↔ x-u ∈ V.cells := by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa [GaussianTranslation] using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x-u, hx, by simp [GaussianTranslation]⟩
  have memim (E : Set GaussianInt) (u x : GaussianInt) :
      x ∈ GaussianTranslation u '' E ↔ x-u ∈ E := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [GaussianTranslation] using hy
    · intro hx
      exact ⟨x-u, hx, by simp [GaussianTranslation]⟩
  have normal (i : Fin 4) (V : ProtoTile) (H : PartialOdometer)
      (p : ℝ × ℝ) (ho : TileOdometer ((DiamondRecursiveQuadruple K) i) V H)
      (hs : PartialOdometerSlope H = some p) (hg : GlobalOdometerExtends g H) :
      ∃ (u a : GaussianInt) (b : Int),
        V.cells = (TileTranslation (S i).1 u).cells ∧
        FootprintVertices V = FootprintVertices (TileTranslation (S i).1 u) ∧
        (∀ x, x ∈ H.domain ↔ x-u ∈ FootprintVertices (S i).1) ∧
        (∀ x, x ∈ H.domain →
          g x = (S i).2.1 (x-u) + a.re*x.re + a.im*x.im+b) ∧
        TileCentroid V = ((S i).2.2.1.1+u.re, (S i).2.2.1.2+u.im) ∧
        p = ((S i).2.2.2.1+a.re, (S i).2.2.2.2+a.im) := by
    obtain ⟨hc, hcent, Hc, hOc, hDc, hVc, hPc⟩ := P5352T2SourceCertificates K hk i
    obtain ⟨u, ⟨hcell, hanchor, a, b, hd, hv⟩, _⟩ :=
      TileOdometerTranslationUniqueness _ V (S i).1 H Hc hc ho hOc
    obtain ⟨c, hg⟩ := hg
    have hh : H = PartialOdometerAffineTranslate Hc u a b := by
      have he : H.domain = (PartialOdometerAffineTranslate Hc u a b).domain := by
        ext x
        rw [(PartialOdometerAffineTranslateFormulas Hc u a b).2.1]
        exact hd x
      have ve : H.value = (PartialOdometerAffineTranslate Hc u a b).value := by
        funext x
        by_cases hx : x ∈ H.domain
        · rw [hv x hx, (PartialOdometerAffineTranslateFormulas Hc u a b).2.2.1
            x (by rwa [← he])]
        · rw [H.value_outside x hx,
            (PartialOdometerAffineTranslate Hc u a b).value_outside x (by rwa [← he])]
      cases H
      simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
      exact ⟨he, ve⟩
    have obs := ProtoTileObservableExtensionality V _ hcell hanchor
    refine ⟨u, a, b+c, hcell, obs.1, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [hd x]
      exact Set.ext_iff.mp hDc (x-u)
    · intro x hx
      rw [hg x hx, hv x hx, hVc (x-u) ((hd x).mp hx)]
      ring
    · rw [obs.2.2.2.2, (TileTranslationFormulas (S i).1 u).2.2.2.2.1, hcent]
    · apply Option.some.inj
      rw [← hs, hh, (PartialOdometerAffineTranslateFormulas Hc u a b).2.2.2.2.2, hPc]
      rfl
  obtain ⟨w, b, c, hc, hf, hd, hv, hC, hP⟩ := normal 0 T h p hT hp he
  obtain ⟨v, b', c', hc', hf', hd', hv', hC', hP'⟩ := normal j U l r hU hr he'
  let f : IntegerLatticeFunction := fun y =>
    g (y+w) - b.re*(y+w).re - b.im*(y+w).im-c
  refine ⟨w, v-w, b'-b, c'-c+(b'.re-b.re)*w.re+(b'.im-b.im)*w.im,
    f, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [show x-w-(v-w) = x-v by abel] using hd' x
  · intro x
    rw [hc, memtr]
  · intro x
    rw [hc', memtr]
    simp only [show x-w-(v-w) = x-v by abel]
    rfl
  · intro x u
    rw [(TileTranslationFormulas T u).2.2.2.2.2.1, memim, hf,
      (TileTranslationFormulas (S 0).1 w).2.2.2.2.2.1, memim]
    rw [show x-u-w = x-w-u by abel]
  · rw [hC, hC']
    ext <;> simp <;> ring
  · rw [hP, hP']
    simp only [Zsqrtd.re_sub]
    push_cast
    ring
  · rw [hP, hP']
    simp only [Zsqrtd.im_sub]
    push_cast
    ring
  · intro y hy
    have hy' : y+w ∈ h.domain := (hd _).mpr (by simpa using hy)
    dsimp only [f]
    rw [hv _ hy']
    simp only [add_sub_cancel_right]
    ring
  · intro y hy
    have hy' : y+w ∈ l.domain := (hd' _).mpr (by
      simpa only [show y+w-v = y-(v-w) by abel] using hy)
    dsimp only [f]
    rw [hv' _ hy', show y+w-v = y-(v-w) by abel]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    ring
  · intro x
    unfold FourNeighborLaplacian
    dsimp only [f]
    simp only [sub_add_cancel]
    rw [show x-w+1+w = x+1 by abel, show x-w-1+w = x-1 by abel,
      show x-w+⟨0,1⟩+w = x+⟨0,1⟩ by abel,
      show x-w-⟨0,1⟩+w = x-⟨0,1⟩ by abel]
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_one, Zsqrtd.im_one]
    ring

end ApollonianSuperharmonic

end

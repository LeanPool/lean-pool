/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.P5448T1CanonicalFordBoundary

-- [TABLET NODE: P5448T1CommonAffineFordPair]

/-!
# P5448T1CommonAffineFordPair

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5448T1CommonAffineFordPair
    (F : FordFareyParameter) (hq : 1 < F.q)
    (U V : ProtoTile) (hp hm : PartialOdometer)
    (hplus : TileOdometer (FordCircleCoordinate F.p F.q) U hp)
    (hminus : TileOdometer (FordCircleCoordinate F.p F.q) V hm)
    (hdp : ∀ z : GaussianInt, z ∈ hp.domain ↔
      -(F.q₁ : Int) ≤ z.re ∧ z.re ≤ F.q₂ ∧ 0 ≤ z.im ∧ z.im ≤ F.q)
    (hdm : ∀ z : GaussianInt, z ∈ hm.domain ↔
      -(F.q₂ : Int) ≤ z.re ∧ z.re ≤ F.q₁ ∧ -(F.q : Int) ≤ z.im ∧ z.im ≤ 0)
    (sp sm : Real × Real)
    (hsp : PartialOdometerSlope hp = some sp)
    (hsm : PartialOdometerSlope hm = some sm)
    (hsx : sm.1 - sp.1 = -(F.p : Real))
    (hsy : sm.2 - sp.2 = (F.p₁ : Real) - F.p₂)
    (hshared : hp.value 0 = hm.value 0) :
    ∃ (a : GaussianInt) (b : Int),
      (∀ z, z ∈ hp.domain → hp.value z =
        FordOdometer F (z + ⟨(F.q₁ : Int), 0⟩) - F.p₁ * z.im +
          a.re * z.re + a.im * z.im + b) ∧
      (∀ z, z ∈ hm.domain → hm.value z =
        FordOdometer F (z + ⟨(F.q₂ : Int), (F.q : Int)⟩) -
          F.p * z.re - F.p₂ * z.im - F.p * (F.q₂ : Int) +
          a.re * z.re + a.im * z.im + b) := by
-- BODY
  obtain ⟨k, hk, hkd, hkv⟩ := FordTileOdometerRestriction F
  have hC : 0 < (FordCircleCoordinate F.p F.q).1 := by
    simp only [FordCircleCoordinate, Nat.cast_mul]
    positivity
  obtain ⟨up, ⟨_, _, ap, bp, dp, vp⟩, _⟩ :=
    TileOdometerTranslationUniqueness _ U (FordTile F.q) hp k hC hplus hk
  obtain ⟨um, ⟨_, _, am, bm, dm, vm⟩, _⟩ :=
    TileOdometerTranslationUniqueness _ V (FordTile F.q) hm k hC hminus hk
  have kmem (z : GaussianInt) : z ∈ k.domain ↔ z ∈ FordVertexDomain F.q :=
    Set.ext_iff.mp hkd z
  have k0 : (0 : GaussianInt) ∈ k.domain := by
    rw [kmem]
    simp [FordVertexDomain]
  have kqq : (⟨(F.q : Int), (F.q : Int)⟩ : GaussianInt) ∈ k.domain := by
    rw [kmem]
    simp [FordVertexDomain]
  have hsum : (F.q : Int) = F.q₁ + F.q₂ := by exact_mod_cast F.sum_q
  have hup : up = ⟨-(F.q₁ : Int), 0⟩ := by
    have h0 := (hdp up).mp ((dp up).mpr (by simpa using k0))
    have h1 := (hdp (up + ⟨(F.q : Int), (F.q : Int)⟩)).mp
      ((dp _).mpr (by simpa using kqq))
    apply Zsqrtd.ext <;> dsimp at h0 h1 ⊢ <;> omega
  have hum : um = ⟨-(F.q₂ : Int), -(F.q : Int)⟩ := by
    have h0 := (hdm um).mp ((dm um).mpr (by simpa using k0))
    have h1 := (hdm (um + ⟨(F.q : Int), (F.q : Int)⟩)).mp
      ((dm _).mpr (by simpa using kqq))
    apply Zsqrtd.ext <;> dsimp at h0 h1 ⊢ <;> omega
  have affineEq (l : PartialOdometer) (w a : GaussianInt) (b : Int)
      (hd : ∀ z, z ∈ l.domain ↔ z - w ∈ k.domain)
      (hv : ∀ z, z ∈ l.domain →
        l.value z = k.value (z - w) + a.re * z.re + a.im * z.im + b) :
      l = PartialOdometerAffineTranslate k w a b := by
    have he : l.domain = (PartialOdometerAffineTranslate k w a b).domain := by
      ext z
      rw [(PartialOdometerAffineTranslateFormulas k w a b).2.1]
      exact hd z
    have ve : l.value = (PartialOdometerAffineTranslate k w a b).value := by
      funext z
      by_cases hz : z ∈ l.domain
      · rw [hv z hz, (PartialOdometerAffineTranslateFormulas k w a b).2.2.1 z
          (by rwa [← he])]
      · rw [l.value_outside z hz,
          (PartialOdometerAffineTranslate k w a b).value_outside z (by rwa [← he])]
    have same : ∀ l m : PartialOdometer,
        l.domain = m.domain → l.value = m.value → l = m := by
      rintro ⟨ld, lv, lo⟩ ⟨md, mv, mo⟩ hd hv
      dsimp at hd hv
      cases hd
      cases hv
      rfl
    exact same _ _ he ve
  have heP := affineEq hp up ap bp dp vp
  have heM := affineEq hm um am bm dm vm
  have slP := (PartialOdometerAffineTranslateFormulas k up ap bp).2.2.2.2.2
  have slM := (PartialOdometerAffineTranslateFormulas k um am bm).2.2.2.2.2
  rw [← heP, hsp] at slP
  rw [← heM, hsm] at slM
  obtain ⟨sk, hsk⟩ : ∃ sk, PartialOdometerSlope k = some sk := by
    cases hs : PartialOdometerSlope k with
    | none => simp [hs] at slP
    | some sk => exact ⟨sk, rfl⟩
  have eqP : sp = (sk.1 + (ap.re : Real), sk.2 + (ap.im : Real)) :=
    Option.some.inj (by simpa [hsk] using slP)
  have eqM : sm = (sk.1 + (am.re : Real), sk.2 + (am.im : Real)) :=
    Option.some.inj (by simpa [hsk] using slM)
  have ax : am.re = ap.re - F.p := by
    apply Int.cast_injective (α := Real)
    push_cast
    rw [eqP, eqM] at hsx
    dsimp at hsx
    linarith
  have ay : am.im = ap.im + F.p₁ - F.p₂ := by
    apply Int.cast_injective (α := Real)
    push_cast
    rw [eqP, eqM] at hsy
    dsimp at hsy
    linarith
  have valP (z : GaussianInt) (hz : z ∈ hp.domain) : hp.value z =
      FordOdometer F (z + ⟨(F.q₁ : Int), 0⟩) +
        ap.re * z.re + ap.im * z.im + bp := by
    have he : z - up = z + ⟨(F.q₁ : Int), 0⟩ := by
      rw [hup]
      ext <;> simp
    rw [vp z hz, hkv _ ((dp z).mp hz), he]
  have valM (z : GaussianInt) (hz : z ∈ hm.domain) : hm.value z =
      FordOdometer F (z + ⟨(F.q₂ : Int), (F.q : Int)⟩) +
        am.re * z.re + am.im * z.im + bm := by
    have he : z - um = z + ⟨(F.q₂ : Int), (F.q : Int)⟩ := by
      rw [hum]
      ext <;> simp
    rw [vm z hz, hkv _ ((dm z).mp hz), he]
  have hp0 := (hdp 0).mpr (by simp)
  have hm0 := (hdm 0).mpr (by simp)
  have bounds := P5130T5ParentArithmetic F hq
  have edge := (P5448T1CanonicalFordBoundary F hq).1
  have p0 := valP 0 hp0
  have m0 := valM 0 hm0
  simp only [zero_add, Zsqrtd.re_zero, Zsqrtd.im_zero, mul_zero, add_zero,
    (edge (F.q₁ : Int) (by omega) (by omega)).1,
    (edge (F.q₂ : Int) (by omega) (by omega)).2] at p0 m0
  have bc : bm = bp - F.p * (F.q₂ : Int) := by omega
  refine ⟨⟨ap.re, ap.im + F.p₁⟩, bp, ?_, ?_⟩
  · intro z hz
    rw [valP z hz]
    dsimp
    ring
  · intro z hz
    rw [valM z hz, ax, ay, bc]
    dsimp
    ring

end ApollonianSuperharmonic

end

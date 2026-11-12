/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: P4261T2UnitBoundary]

/-!
# P4261T2UnitBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace UnitBoundaryProof

private theorem unitForm :
    (by
      classical
      exact
        (BandCircle) → (∀ (c : CircleCoordinates), (c.1 = 1) → (∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), TileOdometer c T h → ∃ z x, c = (1, 1 + 2 * z) ∧ T.cells = {x} ∧
            (h.domain : Set GaussianInt) = FootprintVertices T ∧ OdometerTranslation h
            (CurvatureOneOdometer z)))
    ) := by
  classical
  intro C c hc T h ho
  induction ho with
  | line w x hw h hdom => simp at hc
  | @unit z x T h hT hdom htrans => exact ⟨z, x, rfl, hT, hdom, htrans⟩
  | @decompose q hq S T hs h hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope =>
      have facts := ProperBandCurvatureStructure q hq
      have allzero : ∀ i : Fin 3, (q i.succ).1 = 0 := by
        intro i
        have hlt := hq.2 i
        have hn := facts.2.1 i
        omega
      have contradiction := facts.2.2 0 1 (allzero 0) (allzero 1)
      norm_num at contradiction

private theorem unitData :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), ∀ (x : GaussianInt), ∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), T.cells = {x} → (h.domain : Set GaussianInt) = FootprintVertices T
            → OdometerTranslation h (CurvatureOneOdometer z) → ∃ a : GaussianInt, ∃ b : ℤ, h =
            PartialOdometerAffineTranslate (CurvatureOneOdometer z) x a b)
    ) := by
  classical
  intro C z x T h hT hdom htrans
  obtain ⟨v, a, b, hd, hv⟩ := htrans
  have hdomSq : (h.domain : Set GaussianInt) =
      {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩} := by
    ext y
    simp [hdom, FootprintVertices, hT]
  have vmem : v ∈ h.domain := by
    apply (hd v).mpr
    simp [CurvatureOneOdometer]
  have v1mem : v + 1 ∈ h.domain := by
    apply (hd (v + 1)).mpr
    simp [CurvatureOneOdometer]
  have vimem : v + ⟨0, 1⟩ ∈ h.domain := by
    apply (hd (v + ⟨0, 1⟩)).mpr
    simp [CurvatureOneOdometer]
  have vmem' : v = x ∨ v = x + 1 ∨ v = x + ⟨0, 1⟩ ∨
      v = x + 1 + ⟨0, 1⟩ := by
    change v ∈ (h.domain : Set GaussianInt) at vmem
    rw [hdomSq] at vmem
    simpa using vmem
  have v1mem' : v + 1 = x ∨ v + 1 = x + 1 ∨
      v + 1 = x + ⟨0, 1⟩ ∨ v + 1 = x + 1 + ⟨0, 1⟩ := by
    change v + 1 ∈ (h.domain : Set GaussianInt) at v1mem
    rw [hdomSq] at v1mem
    simpa using v1mem
  have vimem' : v + ⟨0, 1⟩ = x ∨ v + ⟨0, 1⟩ = x + 1 ∨
      v + ⟨0, 1⟩ = x + ⟨0, 1⟩ ∨
      v + ⟨0, 1⟩ = x + 1 + ⟨0, 1⟩ := by
    change v + ⟨0, 1⟩ ∈ (h.domain : Set GaussianInt) at vimem
    rw [hdomSq] at vimem
    simpa using vimem
  have hvx : v = x := by
    have hre : v.re = x.re ∨ v.re = x.re + 1 := by
      rcases vmem' with h | h | h | h
      · left; exact congrArg Zsqrtd.re h
      · right; simpa using congrArg Zsqrtd.re h
      · left; simpa using congrArg Zsqrtd.re h
      · right; simpa using congrArg Zsqrtd.re h
    have hre1 : v.re + 1 = x.re ∨ v.re + 1 = x.re + 1 := by
      rcases v1mem' with h | h | h | h
      · left; simpa using congrArg Zsqrtd.re h
      · right; simpa using congrArg Zsqrtd.re h
      · left; simpa using congrArg Zsqrtd.re h
      · right; simpa using congrArg Zsqrtd.re h
    have him : v.im = x.im ∨ v.im = x.im + 1 := by
      rcases vmem' with h | h | h | h
      · left; exact congrArg Zsqrtd.im h
      · left; simpa using congrArg Zsqrtd.im h
      · right; simpa using congrArg Zsqrtd.im h
      · right; simpa using congrArg Zsqrtd.im h
    have him1 : v.im + 1 = x.im ∨ v.im + 1 = x.im + 1 := by
      rcases vimem' with h | h | h | h
      · left; simpa using congrArg Zsqrtd.im h
      · left; simpa using congrArg Zsqrtd.im h
      · right; simpa using congrArg Zsqrtd.im h
      · right; simpa using congrArg Zsqrtd.im h
    apply Zsqrtd.ext <;> omega
  subst v
  have hdeq : h.domain =
      (PartialOdometerAffineTranslate (CurvatureOneOdometer z) x a b).domain := by
    ext y
    rw [(PartialOdometerAffineTranslateFormulas _ x a b).2.1]
    exact hd y
  have hveq : h.value =
      (PartialOdometerAffineTranslate (CurvatureOneOdometer z) x a b).value := by
    funext y
    by_cases hy : y ∈ h.domain
    · rw [hv y hy, (PartialOdometerAffineTranslateFormulas _ x a b).2.2.1
        y (by rwa [← hdeq])]
    · rw [h.value_outside y hy,
        (PartialOdometerAffineTranslate _ x a b).value_outside y
          (by rwa [← hdeq])]
  refine ⟨a, b, ?_⟩
  cases h
  simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
  exact ⟨hdeq, hveq⟩

private theorem hReMem :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (u : LatticeCell), ((h.domain : Set GaussianInt) = {u, u + 1,
            u + ⟨0, 1⟩, u + 1 + ⟨0, 1⟩}) → (∀ y ∈ h.domain, y.re = u.re ∨ y.re = u.re + (1 : ℤ))
    ) := by
  classical
  intro h u hdomSq y hy
  change y ∈ (h.domain : Set GaussianInt) at hy
  rw [hdomSq] at hy
  rcases (by simpa using hy : y = u ∨ y = u + 1 ∨
    y = u + ⟨0, 1⟩ ∨ y = u + 1 + ⟨0, 1⟩) with e | e | e | e
  · left; exact congrArg Zsqrtd.re e
  · right; simpa using congrArg Zsqrtd.re e
  · left; simpa using congrArg Zsqrtd.re e
  · right; simpa using congrArg Zsqrtd.re e

private theorem hImMem :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (u : LatticeCell), ((h.domain : Set GaussianInt) = {u, u + 1,
            u + ⟨0, 1⟩, u + 1 + ⟨0, 1⟩}) → (∀ y ∈ h.domain, y.im = u.im ∨ y.im = u.im + (1 : ℤ))
    ) := by
  classical
  intro h u hdomSq y hy
  change y ∈ (h.domain : Set GaussianInt) at hy
  rw [hdomSq] at hy
  rcases (by simpa using hy : y = u ∨ y = u + 1 ∨
    y = u + ⟨0, 1⟩ ∨ y = u + 1 + ⟨0, 1⟩) with e | e | e | e
  · left; exact congrArg Zsqrtd.im e
  · left; simpa using congrArg Zsqrtd.im e
  · right; simpa using congrArg Zsqrtd.im e
  · right; simpa using congrArg Zsqrtd.im e

private theorem kReMem :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (v : LatticeCell), ((k.domain : Set GaussianInt) = {v, v + 1,
            v + ⟨0, 1⟩, v + 1 + ⟨0, 1⟩}) → (∀ y ∈ k.domain, y.re = v.re ∨ y.re = v.re + (1 : ℤ))
    ) := by
  classical
  intro k v kdomSq y hy
  change y ∈ (k.domain : Set GaussianInt) at hy
  rw [kdomSq] at hy
  rcases (by simpa using hy : y = v ∨ y = v + 1 ∨
    y = v + ⟨0, 1⟩ ∨ y = v + 1 + ⟨0, 1⟩) with e | e | e | e
  · left; exact congrArg Zsqrtd.re e
  · right; simpa using congrArg Zsqrtd.re e
  · left; simpa using congrArg Zsqrtd.re e
  · right; simpa using congrArg Zsqrtd.re e

private theorem kImMem :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (v : LatticeCell), ((k.domain : Set GaussianInt) = {v, v + 1,
            v + ⟨0, 1⟩, v + 1 + ⟨0, 1⟩}) → (∀ y ∈ k.domain, y.im = v.im ∨ y.im = v.im + (1 : ℤ))
    ) := by
  classical
  intro k v kdomSq y hy
  change y ∈ (k.domain : Set GaussianInt) at hy
  rw [kdomSq] at hy
  rcases (by simpa using hy : y = v ∨ y = v + 1 ∨
    y = v + ⟨0, 1⟩ ∨ y = v + 1 + ⟨0, 1⟩) with e | e | e | e
  · left; exact congrArg Zsqrtd.im e
  · left; simpa using congrArg Zsqrtd.im e
  · right; simpa using congrArg Zsqrtd.im e
  · right; simpa using congrArg Zsqrtd.im e

private theorem horizontalPositive :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), (LatticeCell) → ((LatticeCell) → ((GaussianInt) →
            ((GaussianInt) → (∀ (f : PartialOdometer), ∀ (g : PartialOdometer), ∀ (x :
            GaussianInt), ∀ (y : GaussianInt), ∀ (α : GaussianInt), ∀ (β : GaussianInt), ∀ (B :
            ℤ), ∀ (D : ℤ), (↑f.domain : Set GaussianInt) = {x, x + (1 : GaussianInt),
            x + ⟨(0 : ℤ), (1 : ℤ)⟩, x + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} → (↑g.domain :
            Set GaussianInt) = {y, y + (1 : GaussianInt), y + ⟨(0 : ℤ), (1 : ℤ)⟩,
            y + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} → (∀ t ∈ f.domain, f.value t =
            (CurvatureOneOdometer z).value (t - x) + α.re * t.re + α.im * t.im + B) → (∀ t ∈
            g.domain, g.value t = (CurvatureOneOdometer z).value (t - y) + β.re * t.re + β.im *
            t.im + D) → y = x + (1 : GaussianInt) → β.im - α.im = z.im → OdometerCompatibility f
            g)))))
    ) := by
  classical
  intro C z u v a a' f g x y α β B D df dg vf vg hstep hcoef
  subst y
  have fRe (t : GaussianInt) (ht : t ∈ f.domain) :
      t.re = x.re ∨ t.re = x.re + 1 := by
    change t ∈ (f.domain : Set GaussianInt) at ht
    rw [df] at ht
    rcases (by simpa using ht : t = x ∨ t = x + 1 ∨
      t = x + ⟨0, 1⟩ ∨ t = x + 1 + ⟨0, 1⟩) with e | e | e | e
    · left; exact congrArg Zsqrtd.re e
    · right; simpa using congrArg Zsqrtd.re e
    · left; simpa using congrArg Zsqrtd.re e
    · right; simpa using congrArg Zsqrtd.re e
  have fIm (t : GaussianInt) (ht : t ∈ f.domain) :
      t.im = x.im ∨ t.im = x.im + 1 := by
    change t ∈ (f.domain : Set GaussianInt) at ht
    rw [df] at ht
    rcases (by simpa using ht : t = x ∨ t = x + 1 ∨
      t = x + ⟨0, 1⟩ ∨ t = x + 1 + ⟨0, 1⟩) with e | e | e | e
    · left; exact congrArg Zsqrtd.im e
    · left; simpa using congrArg Zsqrtd.im e
    · right; simpa using congrArg Zsqrtd.im e
    · right; simpa using congrArg Zsqrtd.im e
  have gRe (t : GaussianInt) (ht : t ∈ g.domain) :
      t.re = x.re + 1 ∨ t.re = x.re + 2 := by
    have hm : t.re = (x + 1).re ∨ t.re = (x + 1).re + 1 := by
      change t ∈ (g.domain : Set GaussianInt) at ht
      rw [dg] at ht
      rcases (by simpa using ht : t = x + 1 ∨ t = x + 1 + 1 ∨
        t = x + 1 + ⟨0, 1⟩ ∨ t = x + 1 + 1 + ⟨0, 1⟩) with e | e | e | e
      · left; exact congrArg Zsqrtd.re e
      · right; simpa using congrArg Zsqrtd.re e
      · left; simpa using congrArg Zsqrtd.re e
      · right; simpa using congrArg Zsqrtd.re e
    rcases hm with hm | hm
    · left; simpa [Zsqrtd.add_def] using hm
    · right
      have hm' : t.re = x.re + 1 + 1 := by simpa [Zsqrtd.add_def] using hm
      omega
  have gIm (t : GaussianInt) (ht : t ∈ g.domain) :
      t.im = x.im ∨ t.im = x.im + 1 := by
    have hm : t.im = (x + 1).im ∨ t.im = (x + 1).im + 1 := by
      change t ∈ (g.domain : Set GaussianInt) at ht
      rw [dg] at ht
      rcases (by simpa using ht : t = x + 1 ∨ t = x + 1 + 1 ∨
        t = x + 1 + ⟨0, 1⟩ ∨ t = x + 1 + 1 + ⟨0, 1⟩) with e | e | e | e
      · left; exact congrArg Zsqrtd.im e
      · left; simpa using congrArg Zsqrtd.im e
      · right; simpa using congrArg Zsqrtd.im e
      · right; simpa using congrArg Zsqrtd.im e
    simpa [Zsqrtd.add_def] using hm
  have common : ∀ t, t ∈ f.domain → t ∈ g.domain →
      t = x + 1 ∨ t = x + 1 + ⟨0, 1⟩ := by
    intro t ht kt
    have hre : t.re = (x + 1).re := by
      change t.re = x.re + 1
      rcases fRe t ht with h | h <;> rcases gRe t kt with h' | h' <;> omega
    rcases fIm t ht with hi | hi <;> rcases gIm t kt with hi' | hi'
    · left
      apply Zsqrtd.ext
      · simpa [Zsqrtd.add_def] using hre
      · simpa [Zsqrtd.add_def] using hi
    · right
      apply Zsqrtd.ext
      · simpa [Zsqrtd.add_def] using hre
      · simpa [Zsqrtd.add_def] using hi'
    · right
      exfalso
      omega
    · right
      apply Zsqrtd.ext
      · simpa [Zsqrtd.add_def] using hre
      · simpa [Zsqrtd.add_def] using hi
  have x1f : x + 1 ∈ f.domain := by change x + 1 ∈ (f.domain : Set _); rw [df]; simp
  have x1g : x + 1 ∈ g.domain := by change x + 1 ∈ (g.domain : Set _); rw [dg]; simp
  have x1if : x + 1 + ⟨0, 1⟩ ∈ f.domain := by
    change x + 1 + ⟨0, 1⟩ ∈ (f.domain : Set _); rw [df]; simp
  have x1ig : x + 1 + ⟨0, 1⟩ ∈ g.domain := by
    change x + 1 + ⟨0, 1⟩ ∈ (g.domain : Set _)
    rw [dg]
    simp [add_assoc, add_comm, add_left_comm]
  have endpoint : g.value (x + 1 + ⟨0, 1⟩) -
      f.value (x + 1 + ⟨0, 1⟩) =
      g.value (x + 1) - f.value (x + 1) := by
    rw [vg _ x1ig, vf _ x1if, vg _ x1g, vf _ x1f]
    have h01 : (x + 1) - x = 1 := by abel
    have h11 : (x + 1 + ⟨0, 1⟩) - x = 1 + ⟨0, 1⟩ := by abel
    have h00 : (x + 1) - (x + 1) = 0 := by simp
    have h10 : (x + 1 + ⟨0, 1⟩) - (x + 1) = ⟨0, 1⟩ := by abel
    have hcoefMul : x.im * β.im - x.im * α.im = x.im * z.im := by
      calc
        x.im * β.im - x.im * α.im = x.im * (β.im - α.im) := by ring
        _ = x.im * z.im := by rw [hcoef]
    simp [CurvatureOneOdometer, h01, h11, h10,
      Zsqrtd.ext_iff]
    ring_nf at hcoefMul ⊢
    omega
  right
  refine ⟨g.value (x + 1) - f.value (x + 1), ?_⟩
  intro t ht kt
  rcases common t ht kt with rfl | rfl
  · rfl
  · exact endpoint

private theorem verticalPositive :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), (LatticeCell) → ((LatticeCell) → ((GaussianInt) →
            ((GaussianInt) → (∀ (f : PartialOdometer), ∀ (g : PartialOdometer), ∀ (x :
            GaussianInt), ∀ (y : GaussianInt), ∀ (α : GaussianInt), ∀ (β : GaussianInt), ∀ (B :
            ℤ), ∀ (D : ℤ), (↑f.domain : Set GaussianInt) = {x, x + (1 : GaussianInt),
            x + ⟨(0 : ℤ), (1 : ℤ)⟩, x + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} → (↑g.domain :
            Set GaussianInt) = {y, y + (1 : GaussianInt), y + ⟨(0 : ℤ), (1 : ℤ)⟩,
            y + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩} → (∀ t ∈ f.domain, f.value t =
            (CurvatureOneOdometer z).value (t - x) + α.re * t.re + α.im * t.im + B) → (∀ t ∈
            g.domain, g.value t = (CurvatureOneOdometer z).value (t - y) + β.re * t.re + β.im *
            t.im + D) → y = x + ⟨(0 : ℤ), (1 : ℤ)⟩ → β.re - α.re = z.im → OdometerCompatibility f
            g)))))
    ) := by
  classical
  intro C z u v a a' f g x y α β B D df dg vf vg hstep hcoef
  subst y
  have fRe (t : GaussianInt) (ht : t ∈ f.domain) :
      t.re = x.re ∨ t.re = x.re + 1 := by
    change t ∈ (f.domain : Set GaussianInt) at ht
    rw [df] at ht
    rcases (by simpa using ht : t = x ∨ t = x + 1 ∨
      t = x + ⟨0, 1⟩ ∨ t = x + 1 + ⟨0, 1⟩) with e | e | e | e
    · left; exact congrArg Zsqrtd.re e
    · right; simpa using congrArg Zsqrtd.re e
    · left; simpa using congrArg Zsqrtd.re e
    · right; simpa using congrArg Zsqrtd.re e
  have fIm (t : GaussianInt) (ht : t ∈ f.domain) :
      t.im = x.im ∨ t.im = x.im + 1 := by
    change t ∈ (f.domain : Set GaussianInt) at ht
    rw [df] at ht
    rcases (by simpa using ht : t = x ∨ t = x + 1 ∨
      t = x + ⟨0, 1⟩ ∨ t = x + 1 + ⟨0, 1⟩) with e | e | e | e
    · left; exact congrArg Zsqrtd.im e
    · left; simpa using congrArg Zsqrtd.im e
    · right; simpa using congrArg Zsqrtd.im e
    · right; simpa using congrArg Zsqrtd.im e
  have gRe (t : GaussianInt) (ht : t ∈ g.domain) :
      t.re = x.re ∨ t.re = x.re + 1 := by
    have hm : t.re = (x + ⟨0, 1⟩).re ∨ t.re = (x + ⟨0, 1⟩).re + 1 := by
      change t ∈ (g.domain : Set GaussianInt) at ht
      rw [dg] at ht
      rcases (by simpa using ht : t = x + ⟨0, 1⟩ ∨
        t = x + ⟨0, 1⟩ + 1 ∨ t = x + ⟨0, 1⟩ + ⟨0, 1⟩ ∨
        t = x + ⟨0, 1⟩ + 1 + ⟨0, 1⟩) with e | e | e | e
      · left; exact congrArg Zsqrtd.re e
      · right; simpa using congrArg Zsqrtd.re e
      · left; simpa using congrArg Zsqrtd.re e
      · right; simpa using congrArg Zsqrtd.re e
    simpa [Zsqrtd.add_def] using hm
  have gIm (t : GaussianInt) (ht : t ∈ g.domain) :
      t.im = x.im + 1 ∨ t.im = x.im + 2 := by
    have hm : t.im = (x + ⟨0, 1⟩).im ∨
        t.im = (x + ⟨0, 1⟩).im + 1 := by
      change t ∈ (g.domain : Set GaussianInt) at ht
      rw [dg] at ht
      rcases (by simpa using ht : t = x + ⟨0, 1⟩ ∨
        t = x + ⟨0, 1⟩ + 1 ∨ t = x + ⟨0, 1⟩ + ⟨0, 1⟩ ∨
        t = x + ⟨0, 1⟩ + 1 + ⟨0, 1⟩) with e | e | e | e
      · left; exact congrArg Zsqrtd.im e
      · left; simpa using congrArg Zsqrtd.im e
      · right; simpa using congrArg Zsqrtd.im e
      · right; simpa using congrArg Zsqrtd.im e
    rcases hm with hm | hm
    · left; simpa [Zsqrtd.add_def] using hm
    · right
      have hm' : t.im = x.im + 1 + 1 := by simpa [Zsqrtd.add_def] using hm
      omega
  have common : ∀ t, t ∈ f.domain → t ∈ g.domain →
      t = x + ⟨0, 1⟩ ∨ t = x + 1 + ⟨0, 1⟩ := by
    intro t ht kt
    have him : t.im = (x + ⟨0, 1⟩).im := by
      change t.im = x.im + 1
      rcases fIm t ht with h | h <;> rcases gIm t kt with h' | h' <;> omega
    rcases fRe t ht with hr | hr <;> rcases gRe t kt with hr' | hr'
    · left
      apply Zsqrtd.ext
      · simpa [Zsqrtd.add_def] using hr
      · simpa [Zsqrtd.add_def] using him
    · right
      apply Zsqrtd.ext
      · simpa [Zsqrtd.add_def] using hr'
      · simpa [Zsqrtd.add_def] using him
    · exfalso; omega
    · right
      apply Zsqrtd.ext
      · simpa [Zsqrtd.add_def] using hr
      · simpa [Zsqrtd.add_def] using him
  have xif : x + ⟨0, 1⟩ ∈ f.domain := by
    change x + ⟨0, 1⟩ ∈ (f.domain : Set _); rw [df]; simp
  have xig : x + ⟨0, 1⟩ ∈ g.domain := by
    change x + ⟨0, 1⟩ ∈ (g.domain : Set _); rw [dg]; simp
  have x1if : x + 1 + ⟨0, 1⟩ ∈ f.domain := by
    change x + 1 + ⟨0, 1⟩ ∈ (f.domain : Set _); rw [df]; simp
  have x1ig : x + 1 + ⟨0, 1⟩ ∈ g.domain := by
    change x + 1 + ⟨0, 1⟩ ∈ (g.domain : Set _)
    rw [dg]
    simp [add_assoc, add_comm, add_left_comm]
  have endpoint : g.value (x + 1 + ⟨0, 1⟩) -
      f.value (x + 1 + ⟨0, 1⟩) =
      g.value (x + ⟨0, 1⟩) - f.value (x + ⟨0, 1⟩) := by
    rw [vg _ x1ig, vf _ x1if, vg _ xig, vf _ xif]
    have h01 : (x + ⟨0, 1⟩) - x = ⟨0, 1⟩ := by abel
    have h11 : (x + 1 + ⟨0, 1⟩) - x = 1 + ⟨0, 1⟩ := by abel
    have h00 : (x + ⟨0, 1⟩) - (x + ⟨0, 1⟩) = 0 := by simp
    have h10 : (x + 1 + ⟨0, 1⟩) - (x + ⟨0, 1⟩) = 1 := by abel
    simp only [CurvatureOneOdometer, Int.reduceNeg, Zsqrtd.ext_iff, Zsqrtd.re_add,
        Zsqrtd.re_one, add_zero, Zsqrtd.im_add, Zsqrtd.im_one, zero_add, h10, zero_ne_one,
        and_false, ↓reduceIte, h11, and_self, sub_self, Zsqrtd.re_zero, Zsqrtd.im_zero, h01,
        and_true]
    have hcoefMul : x.re * β.re - x.re * α.re = x.re * z.im := by
      calc
        x.re * β.re - x.re * α.re = x.re * (β.re - α.re) := by ring
        _ = x.re * z.im := by rw [hcoef]
    ring_nf at hcoefMul ⊢
    omega
  right
  refine ⟨g.value (x + ⟨0, 1⟩) - f.value (x + ⟨0, 1⟩), ?_⟩
  intro t ht kt
  rcases common t ht kt with rfl | rfl
  · rfl
  · exact endpoint

private theorem diagonalUnique :
    (by
      classical
      exact
        (BandCircle) → (∀ (h : PartialOdometer), ∀ (k : PartialOdometer), (GaussianInt) → (∀ (u :
            LatticeCell), ∀ (v : LatticeCell), (GaussianInt) → ((GaussianInt) → ((∀ (y :
            GaussianInt), (y ∈ h.domain) → (y.re = u.re ∨ y.re = u.re + 1)) → ((∀ (y :
            GaussianInt), (y ∈ h.domain) → (y.im = u.im ∨ y.im = u.im + 1)) → ((∀ (y :
            GaussianInt), (y ∈ k.domain) → (y.re = v.re ∨ y.re = v.re + 1)) → ((∀ (y :
            GaussianInt), (y ∈ k.domain) → (y.im = v.im ∨ y.im = v.im + 1)) → (v.re - u.re = (-1
            : ℤ) ∨ v.re - u.re = (1 : ℤ) → v.im - u.im = (-1 : ℤ) ∨ v.im - u.im = (1 : ℤ) → ∀ (s
            : GaussianInt), ∀ (t : GaussianInt), s ∈ h.domain → s ∈ k.domain → t ∈ h.domain → t ∈
            k.domain → s = t))))))))
    ) := by
  classical
  intro C h k z u v a a' hReMem hImMem kReMem kImMem hx hy s t hs ks ht kt
  have hre : s.re = t.re := by
    rcases hx with hx | hx
    · rcases hReMem s hs with hs0 | hs1 <;>
        rcases kReMem s ks with ks0 | ks1 <;>
        rcases hReMem t ht with ht0 | ht1 <;>
        rcases kReMem t kt with kt0 | kt1 <;> omega
    · rcases hReMem s hs with hs0 | hs1 <;>
        rcases kReMem s ks with ks0 | ks1 <;>
        rcases hReMem t ht with ht0 | ht1 <;>
        rcases kReMem t kt with kt0 | kt1 <;> omega
  have him : s.im = t.im := by
    rcases hy with hy | hy
    · rcases hImMem s hs with hs0 | hs1 <;>
        rcases kImMem s ks with ks0 | ks1 <;>
        rcases hImMem t ht with ht0 | ht1 <;>
        rcases kImMem t kt with kt0 | kt1 <;> omega
    · rcases hImMem s hs with hs0 | hs1 <;>
        rcases kImMem s ks with ks0 | ks1 <;>
        rcases hImMem t ht with ht0 | ht1 <;>
        rcases kImMem t kt with kt0 | kt1 <;> omega
  apply Zsqrtd.ext <;> assumption

private theorem compatibilitySymm :
    (by
      classical
      exact
        (BandCircle) → ((GaussianInt) → ((LatticeCell) → ((LatticeCell) → ((GaussianInt) →
            ((GaussianInt) → (∀ (f : PartialOdometer), ∀ (g : PartialOdometer),
            OdometerCompatibility f g → OdometerCompatibility g f))))))
    ) := by
  classical
  intro C z u v a a' f g hfg
  rcases hfg with hdisj | ⟨c, hc⟩
  · apply Or.inl
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact ((Set.disjoint_left.mp hdisj) hy) hx
  · right
    refine ⟨-c, ?_⟩
    intro x hx hy
    have h := hc x hy hx
    omega

end UnitBoundaryProof

namespace UnitBoundaryDetails

private theorem hzz :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (z : GaussianInt), (C.1.1 = ((1 : ℤ), (1 : GaussianInt) + (2 :
            GaussianInt) * z)) → (∀ (z' :
            GaussianInt), (C.1.1 = ((1 : ℤ), (1 :
            GaussianInt) + (2 : GaussianInt) * z')) → (z = z')) ) := by
  classical
  intro C z hCz z' hCz'
  have hcoord := congrArg Prod.snd (hCz.symm.trans hCz')
  have hreal := congrArg Zsqrtd.re hcoord
  have himag := congrArg Zsqrtd.im hcoord
  simp at hreal himag
  apply Zsqrtd.ext <;> omega

private theorem canonicalSlope :
    (by
      classical
      exact
        ∀ (w : GaussianInt), PartialOdometerSlope (CurvatureOneOdometer w) = some ((↑w.im : ℝ) /
            (2 : ℝ), (↑w.im : ℝ) / (2 : ℝ)) ) := by
  classical
  intro w
  have hs : PartialOdometerSquares (CurvatureOneOdometer w) = {0} := by
    change PartialOdometerSquares (CurvatureOneOdometer 0) = {0}
    decide +kernel
  unfold PartialOdometerSlope
  rw [hs]
  norm_num [CurvatureOneOdometer, Zsqrtd.ext_iff]

private theorem hpform :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (a : GaussianInt), ∀
            (b : ℤ), (h = PartialOdometerAffineTranslate (CurvatureOneOdometer z) u a b) → ((∀ (w
            : GaussianInt), PartialOdometerSlope (CurvatureOneOdometer w) = some (((w.im : ℝ) /
            2), ((w.im : ℝ) / 2))) → (PartialOdometerSlope h = some ((z.im : ℝ) / 2 + a.re, (z.im
            : ℝ) / 2 + a.im))) ) := by
  classical
  intro h z u a b hheq canonicalSlope
  rw [hheq, (PartialOdometerAffineTranslateFormulas _ u a b).2.2.2.2.2,
    canonicalSlope]
  rfl

private theorem hrform :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (z : GaussianInt), ∀ (v : LatticeCell), ∀ (a' : GaussianInt),
            ∀ (b' : ℤ), (k = PartialOdometerAffineTranslate (CurvatureOneOdometer z) v a' b') →
            ((∀ (w : GaussianInt), PartialOdometerSlope (CurvatureOneOdometer w) = some (((w.im :
            ℝ) / 2), ((w.im : ℝ) / 2))) → (PartialOdometerSlope k = some ((z.im : ℝ) / 2 + a'.re,
            (z.im : ℝ) / 2 + a'.im))) ) := by
  classical
  intro k z v a' b' hkeq canonicalSlope
  rw [hkeq, (PartialOdometerAffineTranslateFormulas _ v a' b').2.2.2.2.2,
    canonicalSlope]
  rfl

private theorem hmatrix :
    (by
      classical
      exact
        ∀ (C : BandCircle), (C.1.1.1 = (1 : ℤ)) →
            (CircleMatrix C =
          let c : ℝ := C.1.1.1
          let x : ℝ := C.1.1.2.re
          let y : ℝ := C.1.1.2.im
          (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]]) ) := by
  classical
  intro C hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CircleMatrix, BandCircleEuclideanData]
  all_goals field_simp

private theorem hRe :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (z : GaussianInt), (C.1.1 = ((1 : ℤ), (1 : GaussianInt) + (2 :
            GaussianInt) * z)) →
            ((C.1.1.2.re : ℝ) = 1 + 2 * (z.re : ℝ)) ) := by
  classical
  intro C z hCz
  have he := congrArg (fun q : CircleCoordinates => q.2.re) hCz
  simp only [Int.reduceNeg, Zsqrtd.re_add, Zsqrtd.re_one, Zsqrtd.re_mul, Zsqrtd.re_ofNat,
      Nat.cast_ofNat, Zsqrtd.im_ofNat, mul_zero, zero_mul, add_zero] at he
  exact_mod_cast he

private theorem hIm :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (z : GaussianInt), (C.1.1 = ((1 : ℤ), (1 : GaussianInt) + (2 :
            GaussianInt) * z)) →
            ((C.1.1.2.im : ℝ) = 2 * (z.im : ℝ)) ) := by
  classical
  intro C z hCz
  have he := congrArg (fun q : CircleCoordinates => q.2.im) hCz
  simp only [Int.reduceNeg, Zsqrtd.im_add, Zsqrtd.im_one, Zsqrtd.im_mul, Zsqrtd.re_ofNat,
      Nat.cast_ofNat, Zsqrtd.im_ofNat, zero_mul, add_zero, zero_add] at he
  exact_mod_cast he

private theorem hmatrixUnit :
    (by
      classical
      exact
        ∀ (C : BandCircle), (C.1.1.1 = (1 : ℤ)) → (∀
            (z : GaussianInt), (CircleMatrix C =
          let c : ℝ := C.1.1.1
          let x : ℝ := C.1.1.2.re
          let y : ℝ := C.1.1.2.im
          (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]]) → (((C.1.1.2.re : ℝ) = 1 + 2 * (z.re : ℝ)) →
              (((C.1.1.2.im : ℝ) = 2 * (z.im : ℝ)) → (CircleMatrix C = ![![1 + (z.re : ℝ), (z.im
              : ℝ)], ![(z.im : ℝ), -(z.re : ℝ)]])))) ) := by
  classical
  intro C hc z hmatrix hRe hIm
  rw [hmatrix]
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hc, hRe, hIm]; field_simp; ring

private theorem hcent :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (V : ProtoTile), V.cells = {x} → TileCentroid V = ((↑x.re : ℝ) +
            (1 / 2 : ℝ), (↑x.im : ℝ) + (1 / 2 : ℝ)) ) := by
  classical
  intro x V hV
  simp [TileCentroid, hV]

private theorem h0Real :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a : GaussianInt), ∀ (a'
            : GaussianInt), (((↑z.im : ℝ) / (2 : ℝ) + (↑a'.re : ℝ), (↑z.im : ℝ) / (2 : ℝ) +
            (↑a'.im : ℝ)).1 - ((↑z.im : ℝ) / (2 : ℝ) + (↑a.re : ℝ), (↑z.im : ℝ) / (2 : ℝ) +
            (↑a.im : ℝ)).1 = ![![(1 : ℝ) + (↑z.re : ℝ), (↑z.im : ℝ)], ![(↑z.im : ℝ), -(↑z.re :
            ℝ)]] (0 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * (((↑v.re : ℝ) + (1 / 2 : ℝ), (↑v.im : ℝ) +
            (1 / 2 : ℝ)).1 - ((↑u.re : ℝ) + (1 / 2 : ℝ), (↑u.im : ℝ) + (1 / 2 : ℝ)).1) + ![![(1 :
            ℝ) + (↑z.re : ℝ), (↑z.im : ℝ)], ![(↑z.im : ℝ), -(↑z.re : ℝ)]] (0 : Fin (2 : ℕ)) (1 :
            Fin (2 : ℕ)) * (((↑v.re : ℝ) + (1 / 2 : ℝ), (↑v.im : ℝ) + (1 / 2 : ℝ)).2 - ((↑u.re :
            ℝ) + (1 / 2 : ℝ), (↑u.im : ℝ) + (1 / 2 : ℝ)).2)) → ((a'.re : ℝ) - a.re = (1 + (z.re :
            ℝ)) * ((v.re : ℝ) - u.re) + (z.im : ℝ) * ((v.im : ℝ) - u.im)) ) := by
  classical
  intro z u v a a' h0
  dsimp at h0
  nlinarith [h0]

private theorem h1Real :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a : GaussianInt), ∀ (a'
            : GaussianInt), (((↑z.im : ℝ) / (2 : ℝ) + (↑a'.re : ℝ), (↑z.im : ℝ) / (2 : ℝ) +
            (↑a'.im : ℝ)).2 - ((↑z.im : ℝ) / (2 : ℝ) + (↑a.re : ℝ), (↑z.im : ℝ) / (2 : ℝ) +
            (↑a.im : ℝ)).2 = ![![(1 : ℝ) + (↑z.re : ℝ), (↑z.im : ℝ)], ![(↑z.im : ℝ), -(↑z.re :
            ℝ)]] (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * (((↑v.re : ℝ) + (1 / 2 : ℝ), (↑v.im : ℝ) +
            (1 / 2 : ℝ)).1 - ((↑u.re : ℝ) + (1 / 2 : ℝ), (↑u.im : ℝ) + (1 / 2 : ℝ)).1) + ![![(1 :
            ℝ) + (↑z.re : ℝ), (↑z.im : ℝ)], ![(↑z.im : ℝ), -(↑z.re : ℝ)]] (1 : Fin (2 : ℕ)) (1 :
            Fin (2 : ℕ)) * (((↑v.re : ℝ) + (1 / 2 : ℝ), (↑v.im : ℝ) + (1 / 2 : ℝ)).2 - ((↑u.re :
            ℝ) + (1 / 2 : ℝ), (↑u.im : ℝ) + (1 / 2 : ℝ)).2)) → ((a'.im : ℝ) - a.im = (z.im : ℝ) *
            ((v.re : ℝ) - u.re) - (z.re : ℝ) * ((v.im : ℝ) - u.im)) ) := by
  classical
  intro z u v a a' h1
  dsimp at h1
  nlinarith [h1]

private theorem h0Int :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a : GaussianInt), ∀ (a'
            : GaussianInt), ((a'.re : ℝ) - a.re = (1 + (z.re : ℝ)) * ((v.re : ℝ) - u.re) + (z.im
            : ℝ) * ((v.im : ℝ) - u.im)) → (a'.re - a.re = (1 + z.re) * (v.re - u.re) + z.im *
            (v.im - u.im)) ) := by
  classical
  intro z u v a a' h0Real
  exact_mod_cast h0Real

private theorem h1Int :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a : GaussianInt), ∀ (a'
            : GaussianInt), ((a'.im : ℝ) - a.im = (z.im : ℝ) * ((v.re : ℝ) - u.re) - (z.re : ℝ) *
            ((v.im : ℝ) - u.im)) → (a'.im - a.im = z.im * (v.re - u.re) - z.re * (v.im - u.im)) )
            := by
  classical
  intro z u v a a' h1Real
  exact_mod_cast h1Real

private theorem hdomSq :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (u : LatticeCell), (T.cells = {u}) →
            (((↑h.domain : Set GaussianInt) = FootprintVertices T) → ((h.domain : Set
            GaussianInt) = {u, u + 1, u + ⟨0, 1⟩, u + 1 + ⟨0, 1⟩})) ) := by
  classical
  intro T h u hTu hdu
  ext y
  simp [hdu, FootprintVertices, hTu]

private theorem kdomSq :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (v : LatticeCell), (U.cells = {v}) →
            (((↑k.domain : Set GaussianInt) = FootprintVertices U) → ((k.domain : Set
            GaussianInt) = {v, v + 1, v + ⟨0, 1⟩, v + 1 + ⟨0, 1⟩})) ) := by
  classical
  intro U k v hUv hdu'
  ext y
  simp [hdu', FootprintVertices, hUv]

private theorem hval :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (a : GaussianInt), ∀
            (b : ℤ), (h = PartialOdometerAffineTranslate (CurvatureOneOdometer z) u a b) → (∀ y ∈
            h.domain, h.value y = (CurvatureOneOdometer z).value (y - u) + a.re * y.re + a.im *
            y.im + b) ) := by
  classical
  intro h z u a b hheq y hy
  rw [hheq] at hy ⊢
  exact (PartialOdometerAffineTranslateFormulas _ u a b).2.2.1 y hy

private theorem kval :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (z : GaussianInt), ∀ (v : LatticeCell), ∀ (a' : GaussianInt),
            ∀ (b' : ℤ), (k = PartialOdometerAffineTranslate (CurvatureOneOdometer z) v a' b') →
            (∀ y ∈ k.domain, k.value y = (CurvatureOneOdometer z).value (y - v) + a'.re * y.re +
            a'.im * y.im + b') ) := by
  classical
  intro k z v a' b' hkeq y hy
  rw [hkeq] at hy ⊢
  exact (PartialOdometerAffineTranslateFormulas _ v a' b').2.2.1 y hy

private theorem overlapBounds :
    (by
      classical
      exact
        (BandCircle) → (∀ (h : PartialOdometer), ∀ (k : PartialOdometer), (GaussianInt) → (∀ (u :
            LatticeCell), ∀ (v : LatticeCell), (GaussianInt) → ((GaussianInt) → ((∀ (y :
            GaussianInt), (y ∈ h.domain) → (y.re = u.re ∨ y.re = u.re + 1)) → ((∀ (y :
            GaussianInt), (y ∈ h.domain) → (y.im = u.im ∨ y.im = u.im + 1)) → ((∀ (y :
            GaussianInt), (y ∈ k.domain) → (y.re = v.re ∨ y.re = v.re + 1)) → ((∀ (y :
            GaussianInt), (y ∈ k.domain) → (y.im = v.im ∨ y.im = v.im + 1)) → (∀ y ∈ h.domain, y
            ∈ k.domain → (-1 : ℤ) ≤ v.re - u.re ∧ v.re - u.re ≤ (1 : ℤ) ∧ (-1 : ℤ) ≤ v.im - u.im
            ∧ v.im - u.im ≤ (1 : ℤ))))))))) ) := by
  classical
  intro C h k z u v a a' hReMem hImMem kReMem kImMem y hy ky
  rcases hReMem y hy with h0 | h1 <;> rcases kReMem y ky with k0 | k1 <;>
    rcases hImMem y hy with hi0 | hi1 <;> rcases kImMem y ky with ki0 | ki1 <;>
    omega

private theorem hcoefAt798 :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a :
            GaussianInt), ∀ (a' : GaussianInt), (a'.im - a.im = z.im * (v.re - u.re) - z.re *
            (v.im - u.im)) → ((v.re - u.re = (-1 : ℤ)) → ((v.im - u.im = (0 : ℤ)) → (a.im - a'.im
            = z.im)))) ) := by
  classical
  intro C z u v a a' h1Int hx hy
  rw [hx, hy] at h1Int
  omega

private theorem hcoefAt810 :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a :
            GaussianInt), ∀ (a' : GaussianInt), (a'.re - a.re = (1 + z.re) * (v.re - u.re) + z.im
            * (v.im - u.im)) → ((v.re - u.re = (0 : ℤ)) → ((v.im - u.im = (-1 : ℤ)) → (a.re -
            a'.re = z.im)))) ) := by
  classical
  intro C z u v a a' h0Int hx hy
  rw [hx, hy] at h0Int
  omega

private theorem hAre :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a :
            GaussianInt), ∀ (a' : GaussianInt), (a'.re - a.re = (1 + z.re) * (v.re - u.re) + z.im
            * (v.im - u.im)) → ((v.re - u.re = (0 : ℤ)) → ((v.im - u.im = (0 : ℤ)) → (a'.re =
            a.re)))) ) := by
  classical
  intro C z u v a a' h0Int hx hy
  rw [hx, hy] at h0Int
  omega

private theorem hAim :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a :
            GaussianInt), ∀ (a' : GaussianInt), (a'.im - a.im = z.im * (v.re - u.re) - z.re *
            (v.im - u.im)) → ((v.re - u.re = (0 : ℤ)) → ((v.im - u.im = (0 : ℤ)) → (a'.im =
            a.im)))) ) := by
  classical
  intro C z u v a a' h1Int hx hy
  rw [hx, hy] at h1Int
  omega

private theorem hcoefAt830 :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a :
            GaussianInt), ∀ (a' : GaussianInt), (a'.re - a.re = (1 + z.re) * (v.re - u.re) + z.im
            * (v.im - u.im)) → ((v.re - u.re = (0 : ℤ)) → ((v.im - u.im = (1 : ℤ)) → (a'.re -
            a.re = z.im)))) ) := by
  classical
  intro C z u v a a' h0Int hx hy
  rw [hx, hy] at h0Int
  omega

private theorem hcoefAt842 :
    (by
      classical
      exact
        (BandCircle) → (∀ (z : GaussianInt), ∀ (u : LatticeCell), ∀ (v : LatticeCell), ∀ (a :
            GaussianInt), ∀ (a' : GaussianInt), (a'.im - a.im = z.im * (v.re - u.re) - z.re *
            (v.im - u.im)) → ((v.re - u.re = (1 : ℤ)) → ((v.im - u.im = (0 : ℤ)) → (a'.im - a.im
            = z.im)))) ) := by
  classical
  intro C z u v a a' h1Int hx hy
  rw [hx, hy] at h1Int
  omega

end UnitBoundaryDetails

theorem P4261T2UnitBoundary
    (C : BandCircle) (hc : C.1.1.1 = 1)
    (T U : ProtoTile) (h k : PartialOdometer)
    (hh : TileOdometer C.1.1 T h) (hk : TileOdometer C.1.1 U k)
    (p r : Real × Real)
    (hp : PartialOdometerSlope h = some p) (hr : PartialOdometerSlope k = some r)
    (h0 : r.1 - p.1 = CircleMatrix C 0 0 * ((TileCentroid U).1 - (TileCentroid T).1) +
      CircleMatrix C 0 1 * ((TileCentroid U).2 - (TileCentroid T).2))
    (h1 : r.2 - p.2 = CircleMatrix C 1 0 * ((TileCentroid U).1 - (TileCentroid T).1) +
      CircleMatrix C 1 1 * ((TileCentroid U).2 - (TileCentroid T).2)) :
    OdometerCompatibility h k := by
-- BODY
  classical
  have unitForm : ∀ (c : CircleCoordinates) (hc : c.1 = 1)
      (T : ProtoTile) (h : PartialOdometer), TileOdometer c T h →
      ∃ z x, c = (1, 1 + 2 * z) ∧ T.cells = {x} ∧
        (h.domain : Set GaussianInt) = FootprintVertices T ∧
        OdometerTranslation h (CurvatureOneOdometer z) := UnitBoundaryProof.unitForm C
  obtain ⟨z, u, hCz, hTu, hdu, hth⟩ :=
    unitForm C.1.1 hc T h hh
  obtain ⟨z', v, hCz', hUv, hdu', hku⟩ :=
    unitForm C.1.1 hc U k hk
  have hzz : z = z' := UnitBoundaryDetails.hzz C z hCz z' hCz'
  subst z'
  obtain ⟨⟨a, b, hheq⟩, ⟨a', b', hkeq⟩⟩ :
      (∃ a : GaussianInt, ∃ b : ℤ,
        h = PartialOdometerAffineTranslate (CurvatureOneOdometer z) u a b) ∧
      (∃ a : GaussianInt, ∃ b : ℤ,
        k = PartialOdometerAffineTranslate (CurvatureOneOdometer z) v a b) := by
    -- The translation is anchored by the least vertex of the four-corner domain.
    have unitData : ∀ (x : GaussianInt) (T : ProtoTile) (h : PartialOdometer),
        T.cells = {x} → (h.domain : Set GaussianInt) = FootprintVertices T →
        OdometerTranslation h (CurvatureOneOdometer z) →
        ∃ a : GaussianInt, ∃ b : ℤ,
          h = PartialOdometerAffineTranslate (CurvatureOneOdometer z) x a b :=
              UnitBoundaryProof.unitData C z
    exact ⟨unitData u T h hTu hdu hth,
      unitData v U k hUv hdu' hku⟩
  have canonicalSlope (w : GaussianInt) :
      PartialOdometerSlope (CurvatureOneOdometer w) =
        some (((w.im : ℝ) / 2), ((w.im : ℝ) / 2)) := UnitBoundaryDetails.canonicalSlope w
  have hpform : PartialOdometerSlope h =
      some ((z.im : ℝ) / 2 + a.re, (z.im : ℝ) / 2 + a.im) := UnitBoundaryDetails.hpform h z u a b
          hheq canonicalSlope
  have hrform : PartialOdometerSlope k =
      some ((z.im : ℝ) / 2 + a'.re, (z.im : ℝ) / 2 + a'.im) := UnitBoundaryDetails.hrform k z v
          a' b' hkeq canonicalSlope
  have hp' : p = ((z.im : ℝ) / 2 + a.re, (z.im : ℝ) / 2 + a.im) :=
    Option.some.inj (hp.symm.trans hpform)
  have hr' : r = ((z.im : ℝ) / 2 + a'.re, (z.im : ℝ) / 2 + a'.im) :=
    Option.some.inj (hr.symm.trans hrform)
  have hmatrix : CircleMatrix C =
      let c : ℝ := C.1.1.1
      let x : ℝ := C.1.1.2.re
      let y : ℝ := C.1.1.2.im
      (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]] := UnitBoundaryDetails.hmatrix C hc
  have hRe : (C.1.1.2.re : ℝ) = 1 + 2 * (z.re : ℝ) := UnitBoundaryDetails.hRe C z hCz
  have hIm : (C.1.1.2.im : ℝ) = 2 * (z.im : ℝ) := UnitBoundaryDetails.hIm C z hCz
  have hmatrixUnit : CircleMatrix C =
      ![![1 + (z.re : ℝ), (z.im : ℝ)],
        ![(z.im : ℝ), -(z.re : ℝ)]] := UnitBoundaryDetails.hmatrixUnit C hc z hmatrix hRe hIm
  have hcent (x : GaussianInt) (V : ProtoTile) (hV : V.cells = {x}) :
      TileCentroid V = (((x.re : ℝ) + 1 / 2), ((x.im : ℝ) + 1 / 2)) := UnitBoundaryDetails.hcent
          x V hV
  rw [hp', hr', hmatrixUnit,
    hcent u T hTu, hcent v U hUv] at h0 h1
  have h0Real : (a'.re : ℝ) - a.re =
      (1 + (z.re : ℝ)) * ((v.re : ℝ) - u.re) +
        (z.im : ℝ) * ((v.im : ℝ) - u.im) := UnitBoundaryDetails.h0Real z u v a a' h0
  have h1Real : (a'.im : ℝ) - a.im =
      (z.im : ℝ) * ((v.re : ℝ) - u.re) -
        (z.re : ℝ) * ((v.im : ℝ) - u.im) := UnitBoundaryDetails.h1Real z u v a a' h1
  have h0Int : a'.re - a.re =
      (1 + z.re) * (v.re - u.re) + z.im * (v.im - u.im) := UnitBoundaryDetails.h0Int z u v a a'
          h0Real
  have h1Int : a'.im - a.im =
      z.im * (v.re - u.re) - z.re * (v.im - u.im) := UnitBoundaryDetails.h1Int z u v a a' h1Real
  have hdomSq : (h.domain : Set GaussianInt) =
      {u, u + 1, u + ⟨0, 1⟩, u + 1 + ⟨0, 1⟩} := UnitBoundaryDetails.hdomSq T h u hTu hdu
  have kdomSq : (k.domain : Set GaussianInt) =
      {v, v + 1, v + ⟨0, 1⟩, v + 1 + ⟨0, 1⟩} := UnitBoundaryDetails.kdomSq U k v hUv hdu'
  have hval (y : GaussianInt) (hy : y ∈ h.domain) :
      h.value y = (CurvatureOneOdometer z).value (y - u) +
        a.re * y.re + a.im * y.im + b := UnitBoundaryDetails.hval h z u a b hheq y hy
  have kval (y : GaussianInt) (hy : y ∈ k.domain) :
      k.value y = (CurvatureOneOdometer z).value (y - v) +
        a'.re * y.re + a'.im * y.im + b' := UnitBoundaryDetails.kval k z v a' b' hkeq y hy
  have hReMem (y : GaussianInt) (hy : y ∈ h.domain) :
      y.re = u.re ∨ y.re = u.re + 1 := UnitBoundaryProof.hReMem h u hdomSq y hy
  have hImMem (y : GaussianInt) (hy : y ∈ h.domain) :
      y.im = u.im ∨ y.im = u.im + 1 := UnitBoundaryProof.hImMem h u hdomSq y hy
  have kReMem (y : GaussianInt) (hy : y ∈ k.domain) :
      y.re = v.re ∨ y.re = v.re + 1 := UnitBoundaryProof.kReMem k v kdomSq y hy
  have kImMem (y : GaussianInt) (hy : y ∈ k.domain) :
      y.im = v.im ∨ y.im = v.im + 1 := UnitBoundaryProof.kImMem k v kdomSq y hy
  have overlapBounds (y : GaussianInt) (hy : y ∈ h.domain) (ky : y ∈ k.domain) :
      -1 ≤ v.re - u.re ∧ v.re - u.re ≤ 1 ∧
      -1 ≤ v.im - u.im ∧ v.im - u.im ≤ 1 := UnitBoundaryDetails.overlapBounds C h k z u v a a'
          hReMem hImMem kReMem kImMem y hy ky
  have horizontalPositive (f g : PartialOdometer) (x y α β : GaussianInt)
      (B D : ℤ)
      (df : (f.domain : Set GaussianInt) =
        {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
      (dg : (g.domain : Set GaussianInt) =
        {y, y + 1, y + ⟨0, 1⟩, y + 1 + ⟨0, 1⟩})
      (vf : ∀ t, t ∈ f.domain → f.value t =
        (CurvatureOneOdometer z).value (t - x) +
          α.re * t.re + α.im * t.im + B)
      (vg : ∀ t, t ∈ g.domain → g.value t =
        (CurvatureOneOdometer z).value (t - y) +
          β.re * t.re + β.im * t.im + D)
      (hstep : y = x + 1) (hcoef : β.im - α.im = z.im) :
      OdometerCompatibility f g := UnitBoundaryProof.horizontalPositive C z u v a a' f g x y α β
          B D df dg vf vg hstep hcoef
  have verticalPositive (f g : PartialOdometer) (x y α β : GaussianInt)
      (B D : ℤ)
      (df : (f.domain : Set GaussianInt) =
        {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
      (dg : (g.domain : Set GaussianInt) =
        {y, y + 1, y + ⟨0, 1⟩, y + 1 + ⟨0, 1⟩})
      (vf : ∀ t, t ∈ f.domain → f.value t =
        (CurvatureOneOdometer z).value (t - x) +
          α.re * t.re + α.im * t.im + B)
      (vg : ∀ t, t ∈ g.domain → g.value t =
        (CurvatureOneOdometer z).value (t - y) +
          β.re * t.re + β.im * t.im + D)
      (hstep : y = x + ⟨0, 1⟩) (hcoef : β.re - α.re = z.im) :
      OdometerCompatibility f g := UnitBoundaryProof.verticalPositive C z u v a a' f g x y α β B
          D df dg vf vg hstep hcoef
  have diagonalUnique
      (hx : v.re - u.re = -1 ∨ v.re - u.re = 1)
      (hy : v.im - u.im = -1 ∨ v.im - u.im = 1)
      (s t : GaussianInt) (hs : s ∈ h.domain) (ks : s ∈ k.domain)
      (ht : t ∈ h.domain) (kt : t ∈ k.domain) : s = t := UnitBoundaryProof.diagonalUnique C h k z
          u v a a' hReMem hImMem kReMem kImMem hx hy s t hs ks ht kt
  have compatibilitySymm (f g : PartialOdometer) :
      OdometerCompatibility f g → OdometerCompatibility g f :=
          UnitBoundaryProof.compatibilitySymm C z u v a a' f g
  by_cases hoverlap : ∃ y, y ∈ h.domain ∧ y ∈ k.domain
  · obtain ⟨w, wh, wk⟩ := hoverlap
    have bounds := overlapBounds w wh wk
    rcases bounds with ⟨hre0, hre1, him0, him1⟩
    have hx : v.re - u.re = -1 ∨ v.re - u.re = 0 ∨ v.re - u.re = 1 := by omega
    have hy : v.im - u.im = -1 ∨ v.im - u.im = 0 ∨ v.im - u.im = 1 := by omega
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · right
      refine ⟨k.value w - h.value w, ?_⟩
      intro y yh yk
      have hEq := diagonalUnique (Or.inl hx) (Or.inl hy) y w yh yk wh wk
      rw [hEq]
    · have vu : u = v + 1 := by
        apply Zsqrtd.ext <;> simp [] <;> omega
      have hcoef : a.im - a'.im = z.im := UnitBoundaryDetails.hcoefAt798 C z u v a a' h1Int hx hy
      exact compatibilitySymm k h (horizontalPositive k h v u a' a b' b
        kdomSq hdomSq kval hval vu hcoef)
    · right
      refine ⟨k.value w - h.value w, ?_⟩
      intro y yh yk
      have hEq := diagonalUnique (Or.inl hx) (Or.inr hy) y w yh yk wh wk
      rw [hEq]
    · have vu : u = v + ⟨0, 1⟩ := by
        apply Zsqrtd.ext <;> simp [] <;> omega
      have hcoef : a.re - a'.re = z.im := UnitBoundaryDetails.hcoefAt810 C z u v a a' h0Int hx hy
      exact compatibilitySymm k h (verticalPositive k h v u a' a b' b
        kdomSq hdomSq kval hval vu hcoef)
    · have vu : v = u := by
        apply Zsqrtd.ext <;> omega
      have hAre : a'.re = a.re := UnitBoundaryDetails.hAre C z u v a a' h0Int hx hy
      have hAim : a'.im = a.im := UnitBoundaryDetails.hAim C z u v a a' h1Int hx hy
      right
      refine ⟨b' - b, ?_⟩
      intro y yh yk
      rw [kval y yk, hval y yh, vu, hAre, hAim]
      ring
    · have vu : v = u + ⟨0, 1⟩ := by
        apply Zsqrtd.ext <;> simp [] <;> omega
      have hcoef : a'.re - a.re = z.im := UnitBoundaryDetails.hcoefAt830 C z u v a a' h0Int hx hy
      exact verticalPositive h k u v a a' b b'
        hdomSq kdomSq hval kval vu hcoef
    · right
      refine ⟨k.value w - h.value w, ?_⟩
      intro y yh yk
      have hEq := diagonalUnique (Or.inr hx) (Or.inl hy) y w yh yk wh wk
      rw [hEq]
    · have vu : v = u + 1 := by
        apply Zsqrtd.ext <;> simp [] <;> omega
      have hcoef : a'.im - a.im = z.im := UnitBoundaryDetails.hcoefAt842 C z u v a a' h1Int hx hy
      exact horizontalPositive h k u v a a' b b'
        hdomSq kdomSq hval kval vu hcoef
    · right
      refine ⟨k.value w - h.value w, ?_⟩
      intro y yh yk
      have hEq := diagonalUnique (Or.inr hx) (Or.inr hy) y w yh yk wh wk
      rw [hEq]
  · left
    apply Set.disjoint_left.mpr
    intro y hy ky
    exact hoverlap ⟨y, hy, ky⟩

end ApollonianSuperharmonic

end

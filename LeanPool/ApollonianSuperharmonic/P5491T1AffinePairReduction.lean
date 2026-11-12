/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5491T1AffinePairReduction]

/-!
# P5491T1AffinePairReduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5491T1AffinePairReduction
    (C D : CircleCoordinates) (U V T S : ProtoTile)
    (f g h k : PartialOdometer) (p q r t : ℝ × ℝ)
    (d a : GaussianInt)
    (hC : 0 < C.1) (hD : 0 < D.1)
    (hf : TileOdometer C U f) (hg : TileOdometer D V g)
    (hh : TileOdometer C T h) (hk : TileOdometer D S k)
    (hpf : PartialOdometerSlope f = some p)
    (hqg : PartialOdometerSlope g = some q)
    (hrh : PartialOdometerSlope h = some r)
    (htk : PartialOdometerSlope k = some t)
    (hc : TileCentroid S - TileCentroid T =
      TileCentroid V - TileCentroid U + GaussianRealPoint d)
    (ha : t.1 - r.1 = q.1 - p.1 + (a.re : ℝ))
    (hb : t.2 - r.2 = q.2 - p.2 + (a.im : ℝ)) :
    ∃ u : GaussianInt, ∃ b : ℤ,
      (∀ x, (x ∈ h.domain ∧ x ∈ k.domain) ↔
        (x - u ∈ f.domain ∧ x - u - d ∈ g.domain)) ∧
      ∀ x, x ∈ h.domain → x ∈ k.domain →
        k.value x - h.value x =
          g.value (x - u - d) + a.re * (x - u).re +
            a.im * (x - u).im - f.value (x - u) + b := by
-- BODY
  obtain ⟨u, ⟨hu, heu, a₀, b₀, hdu, hvu⟩, _⟩ :=
    TileOdometerTranslationUniqueness C T U h f hC hh hf
  obtain ⟨v, ⟨hv, hev, a₁, b₁, hdv, hvv⟩, _⟩ :=
    TileOdometerTranslationUniqueness D S V k g hD hk hg
  have representation (l m : PartialOdometer) (w c : GaussianInt) (b : ℤ)
      (hd : ∀ x, x ∈ l.domain ↔ x - w ∈ m.domain)
      (he : ∀ x, x ∈ l.domain →
        l.value x = m.value (x - w) + c.re*x.re + c.im*x.im + b) :
      l = PartialOdometerAffineTranslate m w c b := by
    have hdom : l.domain = (PartialOdometerAffineTranslate m w c b).domain := by
      ext x
      exact (hd x).trans ((PartialOdometerAffineTranslateFormulas m w c b).2.1 x).symm
    have hval : l.value = (PartialOdometerAffineTranslate m w c b).value := by
      funext x
      by_cases hx : x ∈ l.domain
      · exact (he x hx).trans
          ((PartialOdometerAffineTranslateFormulas m w c b).2.2.1 x (hdom ▸ hx)).symm
      · rw [l.value_outside x hx,
          (PartialOdometerAffineTranslate m w c b).value_outside x (by rwa [← hdom])]
    have ext (l m : PartialOdometer) (hd : l.domain = m.domain)
        (hv : l.value = m.value) : l = m := by
      cases l
      cases m
      dsimp at hd hv
      subst_vars
      rfl
    exact ext l _ hdom hval
  have hsr : r = (p.1 + (a₀.re : ℝ), p.2 + (a₀.im : ℝ)) := by
    apply Option.some.inj
    rw [← hrh, representation h f u a₀ b₀ hdu hvu,
      (PartialOdometerAffineTranslateFormulas f u a₀ b₀).2.2.2.2.2, hpf]
    rfl
  have hst : t = (q.1 + (a₁.re : ℝ), q.2 + (a₁.im : ℝ)) := by
    apply Option.some.inj
    rw [← htk, representation k g v a₁ b₁ hdv hvv,
      (PartialOdometerAffineTranslateFormulas g v a₁ b₁).2.2.2.2.2, hqg]
    rfl
  have hcu : TileCentroid T = TileCentroid U + GaussianRealPoint u := by
    exact (ProtoTileObservableExtensionality T (TileTranslation U u) hu heu).2.2.2.2 |>.trans
      (TileTranslationFormulas U u).2.2.2.2.1
  have hcv : TileCentroid S = TileCentroid V + GaussianRealPoint v := by
    exact (ProtoTileObservableExtensionality S (TileTranslation V v) hv hev).2.2.2.2 |>.trans
      (TileTranslationFormulas V v).2.2.2.2.1
  have hshift : v = u + d := by
    rw [hcu, hcv] at hc
    apply Zsqrtd.ext
    · have he := congrArg Prod.fst hc
      simp only [Prod.fst_add, Prod.fst_sub, GaussianRealPoint] at he
      have he' : (v.re : ℝ) = (u.re : ℝ) + (d.re : ℝ) := by linarith
      exact_mod_cast he'
    · have he := congrArg Prod.snd hc
      simp only [Prod.snd_add, Prod.snd_sub, GaussianRealPoint] at he
      have he' : (v.im : ℝ) = (u.im : ℝ) + (d.im : ℝ) := by linarith
      exact_mod_cast he'
  have har : a₁.re - a₀.re = a.re := by
    rw [hsr, hst] at ha
    dsimp at ha
    have he : (a₁.re : ℝ) - (a₀.re : ℝ) = (a.re : ℝ) := by linarith
    exact_mod_cast he
  have hai : a₁.im - a₀.im = a.im := by
    rw [hsr, hst] at hb
    dsimp at hb
    have he : (a₁.im : ℝ) - (a₀.im : ℝ) = (a.im : ℝ) := by linarith
    exact_mod_cast he
  have arg (x : GaussianInt) : x - v = x - u - d := by rw [hshift]; abel
  refine ⟨u, a.re*u.re + a.im*u.im + b₁-b₀, ?_, ?_⟩
  · intro x
    rw [hdu x, hdv x, arg]
  · intro x hx hy
    rw [hvv x hy, hvu x hx, arg]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
    rw [← har, ← hai]
    ring

end ApollonianSuperharmonic

end

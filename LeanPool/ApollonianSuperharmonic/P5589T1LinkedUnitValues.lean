/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4261T2UnitStringTelescoping
public import LeanPool.ApollonianSuperharmonic.P5570T1UnitNormalForm
public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends

-- [TABLET NODE: P5589T1LinkedUnitValues]

/-!
# P5589T1LinkedUnitValues

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5589T1LinkedUnitValues
    (C D : BandCircle) (z : GaussianInt) (hz : D.1.1 = (1, 1 + 2 * z))
    (o : Bool) (base R S U V : ProtoTile)
    (ts rs : List ProtoTile) (hs ks : List PartialOdometer)
    (hm hp f k : PartialOdometer) (g : IntegerLatticeFunction) (x : GaussianInt)
    (hf : OdometerStringRespect D o base R S ts hs)
    (hr : OdometerStringRespect D o base S R rs ks)
    (hhead : hs.head? = some hm) (hlast : hs.getLast? = some hp)
    (hrlast : ks.getLast? = some hm)
    (hgf : GlobalOdometerExtends g f) (hgk : GlobalOdometerExtends g k)
    (hxf : x ∈ f.domain) (hxk : x ∈ k.domain)
    (hcompat : OdometerCompatibility f hm ∧ OdometerCompatibility f hp ∧
      OdometerCompatibility k hm ∧ OdometerCompatibility k hp)
    (hcover : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
      y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ f.domain ∨ y ∈ k.domain)
    (hselect : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
      y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      ∃ T h, ((T, h) ∈ ts.zip hs ∨ (T, h) ∈ rs.zip ks) ∧
        x ∈ h.domain ∧ y ∈ h.domain ∧
        (AncestorOdometer D.1.1 C.1.1 T U h f ∨
          AncestorOdometer D.1.1 C.1.1 T V h k ∨ h = hm ∨ h = hp)) :
    ∃ a : GaussianInt, ∃ b : ℤ, ∀ y,
      y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      g y = P5570T1UnitQuadratic z y + a.re * y.re + a.im * y.im + b := by
-- BODY
  have hc : D.1.1.1 = 1 := by rw [hz]
  have headZip : (R, hm) ∈ ts.zip hs := by
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hf.1.2.1
    obtain ⟨s, hs'⟩ := List.head?_eq_some_iff.mp hhead
    simp [ht, hs']
  have lastZip : (S, hp) ∈ ts.zip hs := by
    obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp hf.1.2.2.1
    obtain ⟨s, hs'⟩ := List.getLast?_eq_some_iff.mp hlast
    have hlen : t.length = s.length := by
      have he := List.Forall₂.length_eq hf.2.1
      rw [ht, hs', List.length_append, List.length_append] at he
      simpa using he
    simp [ht, hs', List.zip_append hlen]
  have reverseLast : (R, hm) ∈ rs.zip ks := by
    obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp hr.1.2.2.1
    obtain ⟨s, hs'⟩ := List.getLast?_eq_some_iff.mp hrlast
    have hlen : t.length = s.length := by
      have he := List.Forall₂.length_eq hr.2.1
      rw [ht, hs', List.length_append, List.length_append] at he
      simpa using he
    simp [ht, hs', List.zip_append hlen]
  have hmatrix : CircleMatrix D =
      ![![((1 + z.re : ℤ) : ℝ), (z.im : ℝ)],
        ![(z.im : ℝ), (-z.re : ℝ)]] := by
    unfold CircleMatrix BandCircleEuclideanData
    simp only [hc, show D.1.1.2 = 1 + 2 * z by rw [hz]]
    ext i j; fin_cases i <;> fin_cases j
    all_goals simp only [
      Complex.div_re, Complex.div_im, GaussianInt.toComplex_def,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im]
    all_goals norm_num
    all_goals ring
  obtain ⟨u₀, a, b₀, _, _, hc₀, hv₀, hs₀⟩ :=
    P5570T1UnitNormalForm D z R hm hz (List.forall₂_zip hf.2.1 headZip)
  have common (T : ProtoTile) (h : PartialOdometer)
      (hmem : (T, h) ∈ ts.zip hs ∨ (T, h) ∈ rs.zip ks) :
      ∃ b : ℤ, ∀ y, y ∈ h.domain →
        h.value y = P5570T1UnitQuadratic z y + a.re * y.re + a.im * y.im + b := by
    have hO : TileOdometer D.1.1 T h := by
      rcases hmem with hmem | hmem
      · exact List.forall₂_zip hf.2.1 hmem
      · exact List.forall₂_zip hr.2.1 hmem
    obtain ⟨u, a', b, _, _, hcent, hval, hslope⟩ :=
      P5570T1UnitNormalForm D z T h hz hO
    have telescope : ∃ s t : ℝ × ℝ,
        PartialOdometerSlope hm = some s ∧ PartialOdometerSlope h = some t ∧
        t.1 - s.1 = CircleMatrix D 0 0 * ((TileCentroid T).1 - (TileCentroid R).1) +
          CircleMatrix D 0 1 * ((TileCentroid T).2 - (TileCentroid R).2) ∧
        t.2 - s.2 = CircleMatrix D 1 0 * ((TileCentroid T).1 - (TileCentroid R).1) +
          CircleMatrix D 1 1 * ((TileCentroid T).2 - (TileCentroid R).2) := by
      rcases hmem with hmem | hmem
      · obtain ⟨t, s, ht, hs, he₁, he₂⟩ := P4261T2UnitStringTelescoping D hc o
          base R S ts rs hs ks hf hr hm hhead hrlast T R h hm hmem reverseLast
        exact ⟨s, t, hs, ht, by linear_combination -he₁, by linear_combination -he₂⟩
      · exact P4261T2UnitStringTelescoping D hc o base R S ts rs hs ks hf hr
          hm hhead hrlast R T hm h headZip hmem
    obtain ⟨s, t, hs, ht, he₁, he₂⟩ := telescope
    have es := Option.some.inj (hs.symm.trans hs₀)
    have et := Option.some.inj (ht.symm.trans hslope)
    rw [es, et, hc₀, hcent, hmatrix] at he₁ he₂
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one] at he₁ he₂
    have ear : (a'.re : ℝ) = a.re := by
      push_cast at he₁
      nlinarith only [he₁]
    have eai : (a'.im : ℝ) = a.im := by
      nlinarith only [he₂]
    have ea : a' = a := by
      apply Zsqrtd.ext
      · exact_mod_cast ear
      · exact_mod_cast eai
    subst a'
    exact ⟨b, hval⟩
  have endpoint (v h : PartialOdometer) (hv : GlobalOdometerExtends g v)
      (hvh : OdometerCompatibility v h) (hxh : x ∈ h.domain)
      (hxv : x ∈ v.domain) (y : GaussianInt) (hyh : y ∈ h.domain)
      (hyv : y ∈ v.domain) : g y - g x = h.value y - h.value x := by
    obtain ⟨c, hc⟩ := hv
    rcases hvh with hd | ⟨b, hb⟩
    · exact (Set.disjoint_left.mp hd hxv hxh).elim
    · have he₁ := hb x hxv hxh
      have he₂ := hb y hyv hyh
      rw [hc y hyv, hc x hxv]
      omega
  have increment (T : ProtoTile) (h : PartialOdometer) (y : GaussianInt)
      (hy : y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩)
      (hxh : x ∈ h.domain) (hyh : y ∈ h.domain)
      (hroute : AncestorOdometer D.1.1 C.1.1 T U h f ∨
        AncestorOdometer D.1.1 C.1.1 T V h k ∨ h = hm ∨ h = hp) :
      g y - g x = h.value y - h.value x := by
    rcases hroute with hf' | hk' | rfl | rfl
    · obtain ⟨c, hc⟩ := hgf
      rw [hc y (hf'.2.2.2.1 hyh), hc x (hf'.2.2.2.1 hxh),
        ← hf'.2.2.2.2 y hyh, ← hf'.2.2.2.2 x hxh]
      omega
    · obtain ⟨c, hc⟩ := hgk
      rw [hc y (hk'.2.2.2.1 hyh), hc x (hk'.2.2.2.1 hxh),
        ← hk'.2.2.2.2 y hyh, ← hk'.2.2.2.2 x hxh]
      omega
    · -- Compatibility is used only on the covered part of the endpoint.
      rcases hcover y hy with hyf | hyk
      · exact endpoint f h hgf hcompat.1 hxh hxf y hyh hyf
      · exact endpoint k h hgk hcompat.2.2.1 hxh hxk y hyh hyk
    · rcases hcover y hy with hyf | hyk
      · exact endpoint f h hgf hcompat.2.1 hxh hxf y hyh hyf
      · exact endpoint k h hgk hcompat.2.2.2 hxh hxk y hyh hyk
  refine ⟨a, g x - P5570T1UnitQuadratic z x - a.re * x.re - a.im * x.im, ?_⟩
  intro y hy
  obtain ⟨T, h, hm, hx, hyh, hroute⟩ := hselect y hy
  obtain ⟨b, hb⟩ := common T h hm
  have he := increment T h y hy hx hyh hroute
  rw [hb y hyh, hb x hx] at he
  omega

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: P5332T1LiteralNormalization]

/-!
# P5332T1LiteralNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1LiteralNormalization (A D : FordFareyParameter)
    (T U : ProtoTile) (h k : PartialOdometer) (p p' : ℝ × ℝ)
    (g : IntegerLatticeFunction)
    (hT : TileOdometer (FordCircleCoordinate A.p A.q) T h)
    (hU : TileOdometer (FordCircleCoordinate D.p D.q) U k)
    (hp : PartialOdometerSlope h = some p)
    (hp' : PartialOdometerSlope k = some p')
    (he : GlobalOdometerExtends g h) (he' : GlobalOdometerExtends g k) :
    ∃ (u d a : GaussianInt) (B : Int) (f : IntegerLatticeFunction),
      (∀ x, x ∈ h.domain ↔ x - u ∈ FordVertexDomain A.q) ∧
      (∀ x, x ∈ k.domain ↔ x - u - d ∈ FordVertexDomain D.q) ∧
      (∀ x, x ∈ T.cells ↔ x - u ∈ (FordTile A.q).cells) ∧
      (∀ x, x ∈ U.cells ↔ x - u - d ∈ (FordTile D.q).cells) ∧
      (∀ x w, x ∈ FootprintVertices (TileTranslation T w) ↔
        x - u - w ∈ FordVertexDomain A.q) ∧
      TileCentroid U - TileCentroid T =
        (((D.q : ℝ) - A.q) / 2 + d.re, ((D.q : ℝ) - A.q) / 2 + d.im) ∧
      p'.1 - p.1 = ((D.p : ℝ) - A.p) / 2 + a.re ∧
      p'.2 - p.2 = ((D.p : ℝ) - A.p) / 2 + a.im ∧
      (∀ y, y ∈ FordVertexDomain A.q → f y = FordOdometer A y) ∧
      (∀ y, y - d ∈ FordVertexDomain D.q →
        f y = FordOdometer D (y - d) + a.re * y.re + a.im * y.im + B) ∧
      (∀ x, FourNeighborLaplacian g x = FourNeighborLaplacian f (x - u)) := by
-- BODY
  classical
  have memtr (F : ProtoTile) (u x : GaussianInt) :
      x ∈ (TileTranslation F u).cells ↔ x-u ∈ F.cells := by
    change x ∈ F.cells.image (GaussianTranslation u) ↔ _
    constructor
    · rintro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      simpa [GaussianTranslation] using hz
    · intro hx
      exact Finset.mem_image.mpr ⟨x-u, hx, by simp [GaussianTranslation]⟩
  have memimage (S : Set GaussianInt) (u x : GaussianInt) :
      x ∈ GaussianTranslation u '' S ↔ x-u ∈ S := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [GaussianTranslation] using hz
    · intro hx
      exact ⟨x-u, hx, by simp [GaussianTranslation]⟩
  have nonempty (n : Nat) (hn : 0 < n) : (FordTile n).cells.Nonempty := by
    refine ⟨0, ((P4210T1FordCellRectangles n 0).1).mpr ?_⟩
    simp only [Zsqrtd.re_zero, Zsqrtd.im_zero]
    exact ⟨le_rfl, by exact_mod_cast hn, le_rfl, by exact_mod_cast hn⟩
  have normal (R : FordFareyParameter) (S : ProtoTile) (H : PartialOdometer)
      (p : ℝ × ℝ) (hS : TileOdometer (FordCircleCoordinate R.p R.q) S H)
      (hp : PartialOdometerSlope H = some p) (he : GlobalOdometerExtends g H) :
      ∃ (u a : GaussianInt) (b : Int),
        S.cells = (TileTranslation (FordTile R.q) u).cells ∧
        (∀ x, x ∈ H.domain ↔ x-u ∈ FordVertexDomain R.q) ∧
        (∀ x, x ∈ H.domain →
          g x = FordOdometer R (x-u) + a.re*x.re + a.im*x.im + b) ∧
        TileCentroid S = ((R.q : ℝ)/2+u.re, (R.q : ℝ)/2+u.im) ∧
        p = ((R.p : ℝ)/2+a.re, (R.p : ℝ)/2+a.im) := by
    obtain ⟨K, hK, hD, hV⟩ := FordTileOdometerRestriction R
    have mem (x : GaussianInt) : x ∈ K.domain ↔ x ∈ FordVertexDomain R.q :=
      Set.ext_iff.mp hD x
    have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
    change (∀ R x, R.q = 1 → FordOdometer R x = _) ∧ _ at laws
    have boundary (x : GaussianInt) (hx : x ∈ FordVertexDomain R.q)
        (hs : x.re = 0 ∨ x.re = R.q ∨ x.im = 0 ∨ x.im = R.q) :
        K.value x = IntegerCeilDiv (R.p*x.re*x.im) R.q
          (by exact_mod_cast R.q_pos.ne') := by
      rw [hV x ((mem x).mpr hx)]
      apply laws.2.1
      refine ⟨hx, ?_⟩
      rcases hs with hs | hs | hs | hs <;> simp only [hs] <;> omega
    have left (y : Int) (hy : 0 ≤ y) (hyq : y ≤ R.q) : K.value ⟨0,y⟩ = 0 := by
      rw [boundary _ (by exact ⟨le_rfl, by dsimp; omega, hy, hyq⟩) (Or.inl rfl)]
      simp [IntegerCeilDiv]
    have right (y : Int) (hy : 0 ≤ y) (hyq : y ≤ R.q) :
        K.value ⟨(R.q : Int),y⟩ = R.p*y := by
      rw [boundary _ (by exact ⟨by dsimp; omega, le_rfl, hy, hyq⟩) (Or.inr (Or.inl rfl))]
      simp only [IntegerCeilDiv]
      rw [show -(R.p*(R.q : Int)*y) = -(R.p*y)*(R.q : Int) by ring,
        Int.mul_ediv_cancel _ (by exact_mod_cast R.q_pos.ne')]
      simp
    have bottom (x : Int) (hx : 0 ≤ x) (hxq : x ≤ R.q) : K.value ⟨x,0⟩ = 0 := by
      rw [boundary _ (by exact ⟨hx, hxq, le_rfl, by dsimp; omega⟩) (Or.inr (Or.inr (Or.inl rfl)))]
      simp [IntegerCeilDiv]
    have top (x : Int) (hx : 0 ≤ x) (hxq : x ≤ R.q) :
        K.value ⟨x,(R.q : Int)⟩ = R.p*x := by
      rw [boundary _ (by exact ⟨hx, hxq, by dsimp; omega, le_rfl⟩) (Or.inr (Or.inr (Or.inr rfl)))]
      change -(-(R.p*x*(R.q : Int))/(R.q : Int)) = R.p*x
      rw [← neg_mul, Int.mul_ediv_cancel _ (by exact_mod_cast R.q_pos.ne')]
      simp
    have slopeK : PartialOdometerSlope K = some ((R.p : ℝ)/2,(R.p : ℝ)/2) := by
      have hs := P4217T2RectangularBoundarySlope K R.q R.q R.q_pos R.q_pos R.p R.p
        hD left right bottom top
      have hn : (R.q : ℝ) ≠ 0 := by exact_mod_cast R.q_pos.ne'
      convert hs using 1; congr 2 <;> field_simp
    have hcurv : 0 < (FordCircleCoordinate R.p R.q).1 := by
      dsimp [FordCircleCoordinate]
      have := R.q_pos
      positivity
    obtain ⟨u, ⟨hc, _, a, b, hd, hv⟩, _⟩ :=
      TileOdometerTranslationUniqueness _ S (FordTile R.q) H K hcurv hS hK
    have hn := (nonempty R.q R.q_pos).image (GaussianTranslation u)
    have hcent : TileCentroid S = TileCentroid (TileTranslation (FordTile R.q) u) := by
      have hnS : S.cells.Nonempty := by rw [hc]; exact hn
      have hnU : (TileTranslation (FordTile R.q) u).cells.Nonempty := hn
      rw [TileCentroid, ite_eq_left hnS, TileCentroid, ite_eq_left hnU, hc]
    have H_eq : H = PartialOdometerAffineTranslate K u a b := by
      have hde : H.domain = (PartialOdometerAffineTranslate K u a b).domain := by
        ext x
        exact (hd x).trans ((PartialOdometerAffineTranslateFormulas K u a b).2.1 x).symm
      have hve : H.value = (PartialOdometerAffineTranslate K u a b).value := by
        funext x
        by_cases hx : x ∈ H.domain
        · exact (hv x hx).trans
            ((PartialOdometerAffineTranslateFormulas K u a b).2.2.1 x (hde ▸ hx)).symm
        · rw [H.value_outside x hx,
            (PartialOdometerAffineTranslate K u a b).value_outside x (by rwa [← hde])]
      have ext (H K : PartialOdometer) (hd : H.domain = K.domain)
          (hv : H.value = K.value) : H = K := by
        cases H
        cases K
        cases hd
        cases hv
        rfl
      exact ext _ _ hde hve
    have hp' : p = ((R.p : ℝ)/2+a.re,(R.p : ℝ)/2+a.im) := by
      have hh := congrArg PartialOdometerSlope H_eq
      rw [hp, (PartialOdometerAffineTranslateFormulas K u a b).2.2.2.2.2, slopeK] at hh
      exact Option.some.inj hh
    obtain ⟨e, he⟩ := he
    refine ⟨u,a,b+e,hc,?_,?_,?_,hp'⟩
    · intro x
      exact (hd x).trans (mem (x-u))
    · intro x hx
      rw [he x hx, hv x hx, hV (x-u) ((hd x).mp hx)]
      ring
    · rw [hcent, (TileTranslationFormulas (FordTile R.q) u).2.2.2.2.1,
        P4210T1FordSquareCentroid R.q R.q_pos]
  obtain ⟨u, l, b, hc, hd, hv, hcent, hslope⟩ := normal A T h p hT hp he
  obtain ⟨v, m, c, hc', hd', hv', hcent', hslope'⟩ := normal D U k p' hU hp' he'
  let f : IntegerLatticeFunction := fun z =>
    g (z+u) - l.re*(z+u).re - l.im*(z+u).im - b
  refine ⟨u,v-u,m-l,(m-l).re*u.re+(m-l).im*u.im+c-b,f,hd,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x
    have eq : x-u-(v-u) = x-v := by abel
    simpa only [eq] using hd' x
  · intro x
    rw [hc]
    exact memtr _ _ _
  · intro x
    rw [hc', memtr]
    have eq : x-u-(v-u) = x-v := by abel
    rw [eq]
  · intro x w
    have hn := (nonempty A.q A.q_pos).image (GaussianTranslation u)
    have hf : FootprintVertices T = FootprintVertices (TileTranslation (FordTile A.q) u) := by
      have hnT : T.cells.Nonempty := by rw [hc]; exact hn
      have hnU : (TileTranslation (FordTile A.q) u).cells.Nonempty := hn
      rw [FootprintVertices, ite_eq_left hnT, FootprintVertices, ite_eq_left hnU, hc]
    rw [(TileTranslationFormulas T w).2.2.2.2.2.1, memimage, hf,
      (TileTranslationFormulas (FordTile A.q) u).2.2.2.2.2.1, memimage,
      (P4062T1CanonicalSupport A.q A.q_pos).1]
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · rw [hcent, hcent']
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Zsqrtd.re_sub,
      Zsqrtd.im_sub, Int.cast_sub] <;> ring
  · rw [hslope, hslope']
    simp only [Zsqrtd.re_sub, Int.cast_sub]
    ring
  · rw [hslope, hslope']
    simp only [Zsqrtd.im_sub, Int.cast_sub]
    ring
  · intro y hy
    have hy' : y+u ∈ h.domain := (hd _).mpr (by simpa using hy)
    dsimp only [f]
    rw [hv _ hy']
    simp only [add_sub_cancel_right]
    ring
  · intro y hy
    have hy' : y+u ∈ k.domain := (hd' _).mpr (by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hy)
    dsimp only [f]
    rw [hv' _ hy']
    have eq : y+u-v = y-(v-u) := by abel
    rw [eq]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    ring
  · intro x
    unfold FourNeighborLaplacian
    dsimp only [f]
    simp only [sub_add_cancel]
    have e1 : x-u+1+u = x+1 := by abel
    have e2 : x-u-1+u = x-1 := by abel
    have e3 : x-u+⟨0,1⟩+u = x+⟨0,1⟩ := by abel
    have e4 : x-u-⟨0,1⟩+u = x-⟨0,1⟩ := by abel
    rw [e1,e2,e3,e4]
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_one, Zsqrtd.im_one]
    ring

end ApollonianSuperharmonic

end

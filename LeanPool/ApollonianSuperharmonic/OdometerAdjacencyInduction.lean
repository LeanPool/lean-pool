/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.OrderedGeneralOdometerAdjacencyClassification
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.FordFareyParentsExist
public import LeanPool.ApollonianSuperharmonic.P5491T1ExceptionalPresentation
public import LeanPool.ApollonianSuperharmonic.P5491T1AffinePairReduction
public import LeanPool.ApollonianSuperharmonic.P5491T1FordBoundarySlope
public import LeanPool.ApollonianSuperharmonic.P5491T1FordRightBoundary
public import LeanPool.ApollonianSuperharmonic.P5491T1FordParentBoundary
public import LeanPool.ApollonianSuperharmonic.P5491T1DiamondRightBoundary
public import LeanPool.ApollonianSuperharmonic.P5491T1DiamondParentBoundary
public import LeanPool.ApollonianSuperharmonic.P5332T1VectorPlacements
public import LeanPool.ApollonianSuperharmonic.P5352T2VectorPlacements
public import LeanPool.ApollonianSuperharmonic.P5352T2SourceCertificates
public import LeanPool.ApollonianSuperharmonic.P4210T1FordSquareCentroid
public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic

-- [TABLET NODE: OdometerAdjacencyInduction]

/-!
# OdometerAdjacencyInduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace AdjacencyInductionGeometry

private theorem compare :
    (by
      classical
      exact
        ∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (f : PartialOdometer), ∀ (g :
            PartialOdometer), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀ (p : ℝ × ℝ), ∀
            (q : ℝ × ℝ), ∀ (r : ℝ × ℝ), ∀ (t : ℝ × ℝ), ∀ (d : GaussianInt), ∀ (a : GaussianInt),
            (0 < C.1) → ((0 < D.1) → ((TileOdometer C U f) → ((TileOdometer D V g) →
            ((TileOdometer C T h) → ((TileOdometer D S k) → ((PartialOdometerSlope f = some p) →
            ((PartialOdometerSlope g = some q) → ((PartialOdometerSlope h = some r) →
            ((PartialOdometerSlope k = some t) → ((TileCentroid S - TileCentroid T =
            TileCentroid V - TileCentroid U + GaussianRealPoint d) → ((t.1-r.1 = q.1-p.1+(a.re :
                ℝ)) → ((t.2-r.2 = q.2-p.2+(a.im : ℝ)) → ((∃ b : ℤ, ∀ x : GaussianInt, x ∈
                f.domain → x-d ∈ g.domain →
            g.value (x-d)+a.re*x.re+a.im*x.im-f.value x=b) → (OdometerCompatibility h
                k)))))))))))))) ) := by
  classical
  intro C D U V T S f g h k p q r t d a hC hD hf hg hh hk hpf hqg hrh htk hc ha hb hraw
  obtain ⟨u,b,hd,hv⟩ := P5491T1AffinePairReduction C D U V T S f g h k
    p q r t d a hC hD hf hg hh hk hpf hqg hrh htk hc ha hb
  obtain ⟨c,hc⟩ := hraw
  right
  refine ⟨c+b, ?_⟩
  intro x hx hy
  obtain ⟨hx',hy'⟩ := (hd x).mp ⟨hx,hy⟩
  rw [hv x hx hy, hc (x-u) hx' hy']

private theorem fordRight :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (f : PartialOdometer), ∀ (g :
            PartialOdometer), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀ (p : ℝ × ℝ), ∀
            (q : ℝ × ℝ), ∀ (r : ℝ × ℝ), ∀ (t : ℝ × ℝ), ∀ (d : GaussianInt), ∀ (a : GaussianInt),
            (0 < C.1) → ((0 < D.1) → ((TileOdometer C U f) → ((TileOdometer D V g) →
            ((TileOdometer C T h) → ((TileOdometer D S k) → ((PartialOdometerSlope f = some p) →
            ((PartialOdometerSlope g = some q) → ((PartialOdometerSlope h = some r) →
            ((PartialOdometerSlope k = some t) → ((TileCentroid S - TileCentroid T = TileCentroid
            V - TileCentroid U + GaussianRealPoint d) → ((t.1-r.1 = q.1-p.1+(a.re : ℝ)) →
            ((t.2-r.2 = q.2-p.2+(a.im : ℝ)) → ((∃ b : ℤ, ∀ x : GaussianInt, x ∈ f.domain → x-d ∈
            g.domain → g.value (x-d)+a.re*x.re+a.im*x.im-f.value x=b) → (OdometerCompatibility h
            k))))))))))))))) → (∀ (P : FordFareyParameter), (1 < P.q) → (∀ (i : Fin 3), ∀ (e :
            Bool), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (p : ℝ × ℝ), ∀ (q : ℝ × ℝ), (TileOdometer (FordRecursiveQuadruple
            P 0) T h) → ((TileOdometer (FordRecursiveQuadruple P 0) S k) → ((PartialOdometerSlope
            h = some p) → ((PartialOdometerSlope k = some q) → ((TileCentroid S - TileCentroid T =
            (if e = true then (1 : ℝ) else -1) • GaussianRealPoint
              (BandVectors.1 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ))) →
                  ((q.1-p.1 = (if e = true then (1 : ℝ) else -1) *
            (BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)).re) →
                ((q.2-p.2 = (if e = true then (1 : ℝ) else -1) *
            (BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)).im) →
                (OdometerCompatibility h k))))))))) ) := by
  classical
  intro compare P hP i e T S h k p q hh hk hp hq hc ha hb
  obtain ⟨f,hf,hd,hv⟩ := FordTileOdometerRestriction P
  have hs := P5491T1FordBoundarySlope P f hd hv
  let R := P5332T1RightRows P i 0
  let d := if e then R.displacement else -R.displacement
  let a := if e then R.linear else -R.linear
  have vec := (P5332T1VectorPlacements P hP).1 i
  have hc' : TileCentroid S - TileCentroid T =
      TileCentroid (FordTile P.q) - TileCentroid (FordTile P.q) + GaussianRealPoint d := by
    rw [hc, vec.1, sub_self, zero_add]
    cases e <;> simp [d, R, GaussianRealPoint]
  have ha' : q.1-p.1 = (P.p : ℝ)/2-(P.p : ℝ)/2+(a.re : ℝ) := by
    rw [ha, vec.2]
    cases e <;> simp [a, R]
  have hb' : q.2-p.2 = (P.p : ℝ)/2-(P.p : ℝ)/2+(a.im : ℝ) := by
    rw [hb, vec.2]
    cases e <;> simp [a, R]
  apply compare _ _ _ _ _ _ f f h k _ _ p q d a
    (by change (0 : ℤ) < ↑(P.q*P.q); exact_mod_cast Nat.mul_pos P.q_pos P.q_pos)
    (by change (0 : ℤ) < ↑(P.q*P.q); exact_mod_cast Nat.mul_pos P.q_pos P.q_pos)
    hf hf hh hk hs hs hp hq hc' ha' hb'
  obtain ⟨b,hb⟩ := P5491T1FordRightBoundary P hP i e
  refine ⟨b, ?_⟩
  intro x hx hy
  rw [hv x hx, hv (x-d) hy]
  exact hb x (by change x ∈ (f.domain : Set GaussianInt) at hx; rwa [hd] at hx)
    (by change x-d ∈ (f.domain : Set GaussianInt) at hy; rwa [hd] at hy)

private theorem fordParent :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (f : PartialOdometer), ∀ (g :
            PartialOdometer), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀ (p : ℝ × ℝ), ∀
            (q : ℝ × ℝ), ∀ (r : ℝ × ℝ), ∀ (t : ℝ × ℝ), ∀ (d : GaussianInt), ∀ (a : GaussianInt),
            (0 < C.1) → ((0 < D.1) → ((TileOdometer C U f) → ((TileOdometer D V g) →
            ((TileOdometer C T h) → ((TileOdometer D S k) → ((PartialOdometerSlope f = some p) →
            ((PartialOdometerSlope g = some q) → ((PartialOdometerSlope h = some r) →
            ((PartialOdometerSlope k = some t) → ((TileCentroid S - TileCentroid T = TileCentroid
            V - TileCentroid U + GaussianRealPoint d) → ((t.1-r.1 = q.1-p.1+(a.re : ℝ)) →
            ((t.2-r.2 = q.2-p.2+(a.im : ℝ)) → ((∃ b : ℤ, ∀ x : GaussianInt, x ∈ f.domain → x-d ∈
            g.domain → g.value (x-d)+a.re*x.re+a.im*x.im-f.value x=b) → (OdometerCompatibility h
            k))))))))))))))) → (∀ (P : FordFareyParameter), (1 < P.q) → (∀ (i : Fin 3), ∀ (s :
            Fin 4), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (p : ℝ × ℝ), ∀ (q : ℝ × ℝ), (0 < (FordRecursiveQuadruple P
            i.succ).1) → ((TileOdometer (FordRecursiveQuadruple P 0) T h) → ((TileOdometer
            (FordRecursiveQuadruple P i.succ) S k) → ((PartialOdometerSlope h = some p) →
            ((PartialOdometerSlope k = some q) → ((TileCentroid S - TileCentroid T = (1/2 : ℝ) •
            GaussianRealPoint
            ((⟨0,1⟩ : GaussianInt)^s.val *
              (BandVectors.1 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P 0) +
               BandVectors.1 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)))) →
                   ((q.1-p.1 = ((1/2 : ℝ) • GaussianRealPoint
            ((-⟨0,1⟩ : GaussianInt)^s.val *
              (BandVectors.2 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P 0) +
               BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)))).1)
                   → ((q.2-p.2 = ((1/2 : ℝ) • GaussianRealPoint
            ((-⟨0,1⟩ : GaussianInt)^s.val *
              (BandVectors.2 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P 0) +
               BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)))).2)
                   → (OdometerCompatibility h k)))))))))) ) := by
  classical
  intro compare P hP i s T S h k p q hpos hh hk hp hq hc ha hb
  have hi : i.val < 2 := by
    fin_cases i
    · decide
    · decide
    · norm_num [FordRecursiveQuadruple] at hpos
  let j : Fin 2 := ⟨i.val,hi⟩
  have ij : (⟨j.val, by omega⟩ : Fin 3) = i := rfl
  have ar := P5130T5ParentArithmetic P hP
  have hden : 0 < ![P.q₁,P.q₂] j := by
    by_cases hj : j = 0
    · rw [hj]; exact ar.1
    · have hj' : j = 1 := by omega
      rw [hj']; exact ar.2.2.1
  have hred : Nat.Coprime (![P.q₁,P.q₂] j) (![P.p₁,P.p₂] j).natAbs := by
    by_cases hj : j = 0
    · rw [hj]; exact ar.2.2.2.2.1
    · have hj' : j = 1 := by omega
      rw [hj']; exact ar.2.2.2.2.2.1
  obtain ⟨A,⟨hAp,hAq⟩,_⟩ := FordFareyParentsExist _ _ hden hred
  have parent : FordRecursiveQuadruple P i.succ = FordCircleCoordinate A.p A.q := by
    rw [hAp,hAq]
    fin_cases i
    · simp [j,FordRecursiveQuadruple, Nat.ne_of_gt ar.1]
    · simp [j,FordRecursiveQuadruple]
    · norm_num [FordRecursiveQuadruple] at hpos
  obtain ⟨f,hf,hdf,hvf⟩ := FordTileOdometerRestriction P
  obtain ⟨g,hg,hdg,hvg⟩ := FordTileOdometerRestriction A
  have hsf := P5491T1FordBoundarySlope P f hdf hvf
  have hsg := P5491T1FordBoundarySlope A g hdg hvg
  let R := P5332T1ParentRows P j s 0
  obtain ⟨vc,va,_⟩ := (P5332T1VectorPlacements P hP).2 j s
  rw [ij] at vc va
  have hc' : TileCentroid S - TileCentroid T =
      TileCentroid (FordTile A.q) - TileCentroid (FordTile P.q) +
        GaussianRealPoint R.displacement := by
    rw [hc,vc,P4210T1FordSquareCentroid A.q A.q_pos,
      P4210T1FordSquareCentroid P.q P.q_pos,hAq]
    ext <;> simp [GaussianRealPoint,R] <;> ring
  have ha' : q.1-p.1 = (A.p : ℝ)/2-(P.p : ℝ)/2+(R.linear.re : ℝ) := by
    rw [ha,va,hAp]
    dsimp
    ring
  have hb' : q.2-p.2 = (A.p : ℝ)/2-(P.p : ℝ)/2+(R.linear.im : ℝ) := by
    rw [hb,va,hAp]
    dsimp
    ring
  apply compare _ _ _ _ _ _ f g h k _ _ p q R.displacement R.linear
    (by change (0 : ℤ) < ↑(P.q*P.q); exact_mod_cast Nat.mul_pos P.q_pos P.q_pos)
    (by change (0 : ℤ) < ↑(A.q*A.q); exact_mod_cast Nat.mul_pos A.q_pos A.q_pos)
    hf hg hh (parent ▸ hk) hsf hsg hp hq hc' ha' hb'
  obtain ⟨b,hb⟩ := P5491T1FordParentBoundary P A hP j s hAp hAq
  refine ⟨b, ?_⟩
  intro x hx hy
  rw [hvg (x-R.displacement) hy,hvf x hx]
  exact hb x (by change x ∈ (f.domain : Set GaussianInt) at hx; rwa [hdf] at hx)
    (by change x-R.displacement ∈ (g.domain : Set GaussianInt) at hy; rwa [hdg] at hy)

private theorem diamondRight :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (f : PartialOdometer), ∀ (g :
            PartialOdometer), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀ (p : ℝ × ℝ), ∀
            (q : ℝ × ℝ), ∀ (r : ℝ × ℝ), ∀ (t : ℝ × ℝ), ∀ (d : GaussianInt), ∀ (a : GaussianInt),
            (0 < C.1) → ((0 < D.1) → ((TileOdometer C U f) → ((TileOdometer D V g) →
            ((TileOdometer C T h) → ((TileOdometer D S k) → ((PartialOdometerSlope f = some p) →
            ((PartialOdometerSlope g = some q) → ((PartialOdometerSlope h = some r) →
            ((PartialOdometerSlope k = some t) → ((TileCentroid S - TileCentroid T = TileCentroid
            V - TileCentroid U + GaussianRealPoint d) → ((t.1-r.1 = q.1-p.1+(a.re : ℝ)) →
            ((t.2-r.2 = q.2-p.2+(a.im : ℝ)) → ((∃ b : ℤ, ∀ x : GaussianInt, x ∈ f.domain → x-d ∈
            g.domain → g.value (x-d)+a.re*x.re+a.im*x.im-f.value x=b) → (OdometerCompatibility h
            k))))))))))))))) → (∀ (K : DiamondParameter), (1 < K.1) → (∀ (i : Fin 3), ∀ (e :
            Bool), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (p : ℝ × ℝ), ∀ (q : ℝ × ℝ), (TileOdometer
            (DiamondRecursiveQuadruple K 0) T h) → ((TileOdometer (DiamondRecursiveQuadruple K 0)
            S k) → ((PartialOdometerSlope h = some p) → ((PartialOdometerSlope k = some q) →
            ((TileCentroid S - TileCentroid T =
            (if e = true then (1 : ℝ) else -1) • GaussianRealPoint
              (BandVectors.1 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K
                  i.succ))) → ((q.1-p.1 = (if e = true then (1 : ℝ) else -1) *
            (BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K
                i.succ)).re) → ((q.2-p.2 = (if e = true then (1 : ℝ) else -1) *
            (BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K
                i.succ)).im) → (OdometerCompatibility h k))))))))) ) := by
  classical
  intro compare K hK i e T S h k p q hh hk hp hq hc ha hb
  let A := P5352T2Sources K hK 0
  let M := (P5352T2PlacementData K.1 i).1
  let d := if e then M.1 else -M.1
  let a := if e then M.2 else -M.2
  obtain ⟨hpos,hcent,f,hf,hd,hv,hs⟩ := P5352T2SourceCertificates K hK 0
  obtain ⟨vc,va,_⟩ := P5352T2VectorPlacements K hK i 0
  have hc' : TileCentroid S - TileCentroid T =
      TileCentroid A.1 - TileCentroid A.1 + GaussianRealPoint d := by
    rw [hc,vc,sub_self,zero_add]
    cases e <;> simp [d,M,GaussianRealPoint]
  have ha' : q.1-p.1 = A.2.2.2.1-A.2.2.2.1+(a.re : ℝ) := by
    rw [ha,va]
    cases e <;> simp [a,M]
  have hb' : q.2-p.2 = A.2.2.2.2-A.2.2.2.2+(a.im : ℝ) := by
    rw [hb,va]
    cases e <;> simp [a,M]
  apply compare _ _ A.1 A.1 _ _ f f h k _ _ p q d a
    hpos hpos hf hf hh hk hs hs hp hq hc' ha' hb'
  obtain ⟨b,hb⟩ := P5491T1DiamondRightBoundary K hK i e
  refine ⟨b, ?_⟩
  intro x hx hy
  rw [hv x hx,hv (x-d) hy]
  exact hb x (by change x ∈ (f.domain : Set GaussianInt) at hx; rwa [hd] at hx)
    (by change x-d ∈ (f.domain : Set GaussianInt) at hy; rwa [hd] at hy)

private theorem diamondParent :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (f : PartialOdometer), ∀ (g :
            PartialOdometer), ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), ∀ (p : ℝ × ℝ), ∀
            (q : ℝ × ℝ), ∀ (r : ℝ × ℝ), ∀ (t : ℝ × ℝ), ∀ (d : GaussianInt), ∀ (a : GaussianInt),
            (0 < C.1) → ((0 < D.1) → ((TileOdometer C U f) → ((TileOdometer D V g) →
            ((TileOdometer C T h) → ((TileOdometer D S k) → ((PartialOdometerSlope f = some p) →
            ((PartialOdometerSlope g = some q) → ((PartialOdometerSlope h = some r) →
            ((PartialOdometerSlope k = some t) → ((TileCentroid S - TileCentroid T = TileCentroid
            V - TileCentroid U + GaussianRealPoint d) → ((t.1-r.1 = q.1-p.1+(a.re : ℝ)) →
            ((t.2-r.2 = q.2-p.2+(a.im : ℝ)) → ((∃ b : ℤ, ∀ x : GaussianInt, x ∈ f.domain → x-d ∈
            g.domain → g.value (x-d)+a.re*x.re+a.im*x.im-f.value x=b) → (OdometerCompatibility h
            k))))))))))))))) → (∀ (K : DiamondParameter), (1 < K.1) → (∀ (i : Fin 3), ∀ (s : Fin
            4), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (p : ℝ × ℝ), ∀ (q : ℝ × ℝ), (TileOdometer
            (DiamondRecursiveQuadruple K 0) T h) → ((TileOdometer (DiamondRecursiveQuadruple K
            i.succ) S k) → ((PartialOdometerSlope h = some p) → ((PartialOdometerSlope k = some
            q) → ((TileCentroid S - TileCentroid T = (1/2 : ℝ) • GaussianRealPoint
            ((⟨0,1⟩ : GaussianInt)^s.val *
              (BandVectors.1 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0) +
               BandVectors.1 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K
                   i.succ)))) → ((q.1-p.1 = ((1/2 : ℝ) • GaussianRealPoint
            ((-⟨0,1⟩ : GaussianInt)^s.val *
              (BandVectors.2 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0) +
               BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K
                   i.succ)))).1) → ((q.2-p.2 = ((1/2 : ℝ) • GaussianRealPoint
            ((-⟨0,1⟩ : GaussianInt)^s.val *
              (BandVectors.2 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0) +
               BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K
                   i.succ)))).2) → (OdometerCompatibility h k))))))))) ) := by
  classical
  intro compare K hK i s T S h k p q hh hk hp hq hc ha hb
  let A := P5352T2Sources K hK 0
  let D := P5352T2Sources K hK i.succ
  let M := (P5352T2PlacementData K.1 i).2 s
  obtain ⟨hpos,hcent,f,hf,hd,hv,hs⟩ := P5352T2SourceCertificates K hK 0
  obtain ⟨hpos',hcent',g,hg,hd',hv',hs'⟩ := P5352T2SourceCertificates K hK i.succ
  obtain ⟨_,_,vc,va,_⟩ := P5352T2VectorPlacements K hK i s
  have hc' : TileCentroid S - TileCentroid T =
      TileCentroid D.1 - TileCentroid A.1 + GaussianRealPoint M.1 := by
    rw [hc,vc,hcent,hcent']
    rfl
  have ha' : q.1-p.1 = D.2.2.2.1-A.2.2.2.1+(M.2.1.re : ℝ) := by rw [ha,va]
  have hb' : q.2-p.2 = D.2.2.2.2-A.2.2.2.2+(M.2.1.im : ℝ) := by rw [hb,va]
  apply compare _ _ A.1 D.1 _ _ f g h k _ _ p q M.1 M.2.1
    hpos hpos' hf hg hh hk hs hs' hp hq hc' ha' hb'
  obtain ⟨b,hb⟩ := P5491T1DiamondParentBoundary K hK i s
  refine ⟨b, ?_⟩
  intro x hx hy
  rw [hv x hx,hv' (x-M.1) hy]
  exact hb x (by change x ∈ (f.domain : Set GaussianInt) at hx; rwa [hd] at hx)
    (by change x-M.1 ∈ (g.domain : Set GaussianInt) at hy; rwa [hd'] at hy)

private theorem hpos' :
    (by
      classical
      exact
        ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (S : ProtoTile), ∀ (k : PartialOdometer), ∀ (p :
            ℝ × ℝ), ∀ (q : ℝ × ℝ), ∀ (Q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
            (TileOdometer (Q i.succ) S k) → (∀ (s : Fin (4 : ℕ)), (Q i.succ = D.1.1) →
            ((TileCentroid S - TileCentroid T = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (Q i.succ) (Q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (Q (0 : Fin (4 : ℕ))) (Q i.succ)))) → ((q.1 - p.1 = ((1 / 2 : ℝ) •
            GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2
            (Q i.succ) (Q (0 : Fin (4 : ℕ))) + BandVectors.2 (Q (0 : Fin (4 : ℕ))) (Q
            i.succ)))).1) → ((q.2 - p.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (Q i.succ) (Q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (Q (0 : Fin (4 : ℕ))) (Q i.succ)))).2) → (((0 : ℤ) < (Q i.succ).1) → (∀
            (g : BandPackingSymmetry), ∀ (r : ℝ × ℝ), ∀ (t : ℝ × ℝ), ∀ (s' : Fin (4 : ℕ)),
            (TileOdometer (BandPackingSymmetryQuadrupleAction g Q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryTileAction g S) (BandPackingSymmetryPartialOdometerAction g k)) →
            ((TileCentroid (BandPackingSymmetryTileAction g S) - TileCentroid
            (BandPackingSymmetryTileAction g T) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ^ (↑s' : ℕ) * (BandVectors.1 (BandPackingSymmetryQuadrupleAction
            g Q ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j) i).succ) (BandPackingSymmetryQuadrupleAction g Q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (BandPackingSymmetryQuadrupleAction g Q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g Q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))) → ((t.1 -
            r.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s'
            : ℕ) * (BandVectors.2 (BandPackingSymmetryQuadrupleAction g Q ((fun (j : Fin (3 : ℕ))
            => if BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryQuadrupleAction g Q (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction g Q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g Q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))).1) →
            ((t.2 - r.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ^ (↑s' : ℕ) * (BandVectors.2 (BandPackingSymmetryQuadrupleAction g Q ((fun (j : Fin
            (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true then -j else j)
            i).succ) (BandPackingSymmetryQuadrupleAction g Q (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction g Q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g Q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))).2) → (0 <
            ((BandPackingSymmetryQuadrupleAction g Q) (if BandPackingSymmetryReversesOrientation
            g then -i else i).succ).1)))))))))) ) := by
  classical
  intro D T S k p q Q i hk s hparent hc ha hb hpos g r t s' hk' hc' ha' hb'
  have hp' := (BandPackingSymmetryCovariance g).1 (Q i.succ)
  cases hg : BandPackingSymmetryReversesOrientation g <;> fin_cases i <;>
    simpa [BandPackingSymmetryQuadrupleAction,hg] using hp'.symm ▸ hpos

end AdjacencyInductionGeometry

theorem OdometerAdjacencyInduction :
    (∀ (C : BandCircle),
      (¬ ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
              BandPackingSymmetryCircleAction g
                (FordCircleCoordinate P.p P.q) = C.1.1) ∨
            (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
              BandPackingSymmetryCircleAction g
                (DiamondRecursiveQuadruple K 0) = C.1.1))) →
      (∀ (T T₀ : ProtoTile) (h h₀ : PartialOdometer),
        RightLatticeAdjacent C T T₀ h h₀ →
        ∀ (C' : BandCircle) (T' : ProtoTile) (h' : PartialOdometer),
          TileSubodometer C.1.1 C'.1.1 T T' h h' →
          (FootprintEdges T' ∩ FootprintEdges T₀).Nonempty →
          SubtileLatticeAdjacent C C' T₀ T' h₀ h') ∧
      (∀ (Cᵢ : BandCircle) (T T₀ : ProtoTile)
          (h h₀ : PartialOdometer),
        SubtileLatticeAdjacent C Cᵢ T₀ T h₀ h →
        ∀ (C' : BandCircle) (T' : ProtoTile) (h' : PartialOdometer),
          TileSubodometer C.1.1 C'.1.1 T₀ T' h₀ h' →
          (∃ x, x ∈ h'.domain ∧ x ∈ h.domain) →
          (((h'.domain : Set GaussianInt) ∩
              (h.domain : Set GaussianInt)).Subsingleton ∨
            (C' = Cᵢ ∧ LeftLatticeAdjacent Cᵢ T T' h h') ∨
            SubtileLatticeAdjacent Cᵢ C' T T' h h' ∨
            SubtileLatticeAdjacent C' Cᵢ T' T h' h))) ∧
    (∀ (C : BandCircle),
      ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
              BandPackingSymmetryCircleAction g
                (FordCircleCoordinate P.p P.q) = C.1.1) ∨
            (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
              BandPackingSymmetryCircleAction g
                (DiamondRecursiveQuadruple K 0) = C.1.1)) →
      (∀ (T T' : ProtoTile) (h h' : PartialOdometer),
        RightLatticeAdjacent C T T' h h' →
        OdometerCompatibility h h') ∧
      ∀ (Cᵢ : BandCircle) (T Tᵢ : ProtoTile)
          (h hᵢ : PartialOdometer),
        SubtileLatticeAdjacent C Cᵢ T Tᵢ h hᵢ →
        OdometerCompatibility h hᵢ) := by
-- BODY
  have compare (C D : CircleCoordinates) (U V T S : ProtoTile)
      (f g h k : PartialOdometer) (p q r t : ℝ × ℝ) (d a : GaussianInt)
      (hC : 0 < C.1) (hD : 0 < D.1)
      (hf : TileOdometer C U f) (hg : TileOdometer D V g)
      (hh : TileOdometer C T h) (hk : TileOdometer D S k)
      (hpf : PartialOdometerSlope f = some p)
      (hqg : PartialOdometerSlope g = some q)
      (hrh : PartialOdometerSlope h = some r)
      (htk : PartialOdometerSlope k = some t)
      (hc : TileCentroid S - TileCentroid T =
        TileCentroid V - TileCentroid U + GaussianRealPoint d)
      (ha : t.1-r.1 = q.1-p.1+(a.re : ℝ))
      (hb : t.2-r.2 = q.2-p.2+(a.im : ℝ))
      (hraw : ∃ b : ℤ, ∀ x : GaussianInt, x ∈ f.domain → x-d ∈ g.domain →
        g.value (x-d)+a.re*x.re+a.im*x.im-f.value x=b) :
      OdometerCompatibility h k := AdjacencyInductionGeometry.compare C D U V T S f g h k p q r t
          d a hC hD hf hg hh hk hpf hqg hrh htk hc ha hb hraw
  have fordRight (P : FordFareyParameter) (hP : 1 < P.q)
      (i : Fin 3) (e : Bool) (T S : ProtoTile) (h k : PartialOdometer)
      (p q : ℝ × ℝ)
      (hh : TileOdometer (FordRecursiveQuadruple P 0) T h)
      (hk : TileOdometer (FordRecursiveQuadruple P 0) S k)
      (hp : PartialOdometerSlope h = some p)
      (hq : PartialOdometerSlope k = some q)
      (hc : TileCentroid S - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) • GaussianRealPoint
          (BandVectors.1 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)))
      (ha : q.1-p.1 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)).re)
      (hb : q.2-p.2 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)).im) :
      OdometerCompatibility h k := AdjacencyInductionGeometry.fordRight compare P hP i e T S h k
          p q hh hk hp hq hc ha hb
  have fordParent (P : FordFareyParameter) (hP : 1 < P.q)
      (i : Fin 3) (s : Fin 4) (T S : ProtoTile) (h k : PartialOdometer)
      (p q : ℝ × ℝ) (hpos : 0 < (FordRecursiveQuadruple P i.succ).1)
      (hh : TileOdometer (FordRecursiveQuadruple P 0) T h)
      (hk : TileOdometer (FordRecursiveQuadruple P i.succ) S k)
      (hp : PartialOdometerSlope h = some p)
      (hq : PartialOdometerSlope k = some q)
      (hc : TileCentroid S - TileCentroid T = (1/2 : ℝ) • GaussianRealPoint
        ((⟨0,1⟩ : GaussianInt)^s.val *
          (BandVectors.1 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P 0) +
           BandVectors.1 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ))))
      (ha : q.1-p.1 = ((1/2 : ℝ) • GaussianRealPoint
        ((-⟨0,1⟩ : GaussianInt)^s.val *
          (BandVectors.2 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P 0) +
           BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)))).1)
      (hb : q.2-p.2 = ((1/2 : ℝ) • GaussianRealPoint
        ((-⟨0,1⟩ : GaussianInt)^s.val *
          (BandVectors.2 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P 0) +
           BandVectors.2 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P i.succ)))).2) :
      OdometerCompatibility h k := AdjacencyInductionGeometry.fordParent compare P hP i s T S h k
          p q hpos hh hk hp hq hc ha hb
  have diamondRight (K : DiamondParameter) (hK : 1 < K.1)
      (i : Fin 3) (e : Bool) (T S : ProtoTile) (h k : PartialOdometer)
      (p q : ℝ × ℝ)
      (hh : TileOdometer (DiamondRecursiveQuadruple K 0) T h)
      (hk : TileOdometer (DiamondRecursiveQuadruple K 0) S k)
      (hp : PartialOdometerSlope h = some p)
      (hq : PartialOdometerSlope k = some q)
      (hc : TileCentroid S - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) • GaussianRealPoint
          (BandVectors.1 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K i.succ)))
      (ha : q.1-p.1 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K i.succ)).re)
      (hb : q.2-p.2 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K i.succ)).im) :
      OdometerCompatibility h k := AdjacencyInductionGeometry.diamondRight compare K hK i e T S h
          k p q hh hk hp hq hc ha hb
  have diamondParent (K : DiamondParameter) (hK : 1 < K.1)
      (i : Fin 3) (s : Fin 4) (T S : ProtoTile) (h k : PartialOdometer)
      (p q : ℝ × ℝ)
      (hh : TileOdometer (DiamondRecursiveQuadruple K 0) T h)
      (hk : TileOdometer (DiamondRecursiveQuadruple K i.succ) S k)
      (hp : PartialOdometerSlope h = some p)
      (hq : PartialOdometerSlope k = some q)
      (hc : TileCentroid S - TileCentroid T = (1/2 : ℝ) • GaussianRealPoint
        ((⟨0,1⟩ : GaussianInt)^s.val *
          (BandVectors.1 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0) +
           BandVectors.1 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K i.succ))))
      (ha : q.1-p.1 = ((1/2 : ℝ) • GaussianRealPoint
        ((-⟨0,1⟩ : GaussianInt)^s.val *
          (BandVectors.2 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0) +
           BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K i.succ)))).1)
      (hb : q.2-p.2 = ((1/2 : ℝ) • GaussianRealPoint
        ((-⟨0,1⟩ : GaussianInt)^s.val *
          (BandVectors.2 (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K 0) +
           BandVectors.2 (DiamondRecursiveQuadruple K 0) (DiamondRecursiveQuadruple K
               i.succ)))).2) :
      OdometerCompatibility h k := AdjacencyInductionGeometry.diamondParent compare K hK i s T S
          h k p q hh hk hp hq hc ha hb
  refine ⟨OrderedGeneralOdometerAdjacencyClassification, ?_⟩
  intro C he
  constructor
  · intro T S h k hadj
    obtain ⟨hh,hk,p,q,hp,hq,Q,i,e,hQ,hchild,hc,ha,hb⟩ := hadj
    rw [← hchild] at hh hk he
    obtain ⟨g,hcanon⟩ := P5491T1ExceptionalPresentation Q hQ he
    obtain ⟨neg,r,t,_,hh',hk',hr,ht,hc',ha',hb',hcompat⟩ :=
      RightLatticeAdjacentPackingSymmetryTransport g Q hQ i e T S h k p q
        hh hk hp hq hc ha hb
    apply hcompat.mp
    rcases hcanon with ⟨P,hP,h0,hparents⟩ | ⟨K,hK,h0,hparents⟩
    · obtain ⟨j,hj⟩ := hparents (if BandPackingSymmetryReversesOrientation g then -i else i)
      rw [h0] at hh' hk'
      rw [h0,hj] at hc' ha' hb'
      exact fordRight P hP j _ _ _ _ _ r t hh' hk' hr ht hc' ha' hb'
    · obtain ⟨j,hj⟩ := hparents (if BandPackingSymmetryReversesOrientation g then -i else i)
      rw [h0] at hh' hk'
      rw [h0,hj] at hc' ha' hb'
      exact diamondRight K hK j _ _ _ _ _ r t hh' hk' hr ht hc' ha' hb'
  · intro D T S h k hadj
    obtain ⟨hh,hk,p,q,hp,hq,Q,i,s,hQ,hchild,hparent,hc,ha,hb⟩ := hadj
    have hpos : 0 < (Q i.succ).1 := by rw [hparent]; exact D.2
    rw [← hchild] at hh he
    rw [← hparent] at hk
    obtain ⟨g,hcanon⟩ := P5491T1ExceptionalPresentation Q hQ he
    obtain ⟨neg,r,t,s',_,_,hh',hk',hr,ht,hc',ha',hb',hcompat⟩ :=
      SubtileLatticeAdjacentPackingSymmetryTransport g Q hQ i s hpos
        T S h k p q hh hk hp hq hc ha hb
    apply hcompat.mp
    have hpos' : 0 < ((BandPackingSymmetryQuadrupleAction g Q)
        (if BandPackingSymmetryReversesOrientation g then -i else i).succ).1 :=
            AdjacencyInductionGeometry.hpos' D T S k p q Q i hk s hparent hc ha hb hpos g r t s'
            hk' hc' ha' hb'
    rcases hcanon with ⟨P,hP,h0,hparents⟩ | ⟨K,hK,h0,hparents⟩
    · obtain ⟨j,hj⟩ := hparents (if BandPackingSymmetryReversesOrientation g then -i else i)
      rw [h0] at hh'
      rw [hj] at hk' hpos'
      rw [h0,hj] at hc' ha' hb'
      exact fordParent P hP j s' _ _ _ _ r t hpos' hh' hk' hr ht hc' ha' hb'
    · obtain ⟨j,hj⟩ := hparents (if BandPackingSymmetryReversesOrientation g then -i else i)
      rw [h0] at hh'
      rw [hj] at hk'
      rw [h0,hj] at hc' ha' hb'
      exact diamondParent K hK j s' _ _ _ _ r t hh' hk' hr ht hc' ha' hb'

end ApollonianSuperharmonic

end

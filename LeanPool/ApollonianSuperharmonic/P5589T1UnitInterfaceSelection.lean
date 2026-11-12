/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.OpposingStringInterfacePath
public import LeanPool.ApollonianSuperharmonic.P4366T2WalkExhaustion
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect
public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.P4158T1AncestorCells
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: P5589T1UnitInterfaceSelection]

/-!
# P5589T1UnitInterfaceSelection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5589T1UnitInterfaceSelection
    (C D : BandCircle) (hunit : D.1.1.1 = 1)
    (o : Bool) (base R S U V : ProtoTile)
    (ts rs : List ProtoTile) (hs ks : List PartialOdometer)
    (hm hp f k : PartialOdometer)
    (hOf : TileOdometer C.1.1 U f) (hOk : TileOdometer C.1.1 V k)
    (hUn : U.cells.Nonempty) (hVn : V.cells.Nonempty)
    (hf : OdometerStringRespect D o base R S ts hs)
    (hr : OdometerStringRespect D o base S R rs ks)
    (hhead : hs.head? = some hm) (hlast : hs.getLast? = some hp)
    (hRS : R ≠ S)
    (hnadj : ¬ ∃ v : GaussianInt, UnitTriangularStep o v ∧
      TileCentroid S - TileCentroid R = GaussianRealPoint v)
    (hanc : ∀ T, T ∈ (ts.drop 1).dropLast →
      ∃ h, (T, h) ∈ ts.zip hs ∧ AncestorOdometer D.1.1 C.1.1 T U h f)
    (hranc : ∀ T, T ∈ (rs.drop 1).dropLast →
      ∃ h, (T, h) ∈ rs.zip ks ∧ AncestorOdometer D.1.1 C.1.1 T V h k)
    (ER : ExactTileInterfaceTriple U V R) (ES : ExactTileInterfaceTriple U V S)
    (htR : TouchingTriple U V R) (htS : TouchingTriple U V S)
    (hcross : ER.otherAB = ES.point)
    (x : GaussianInt) (hxf : x ∈ f.domain) (hxk : x ∈ k.domain) :
    ∀ y, y = x ∨ y = x+1 ∨ y = x-1 ∨ y = x+⟨0,1⟩ ∨ y = x-⟨0,1⟩ →
      ∃ T h, ((T, h) ∈ ts.zip hs ∨ (T, h) ∈ rs.zip ks) ∧
        x ∈ h.domain ∧ y ∈ h.domain ∧
        (AncestorOdometer D.1.1 C.1.1 T U h f ∨
          AncestorOdometer D.1.1 C.1.1 T V h k ∨ h = hm ∨ h = hp) := by
-- BODY
  obtain ⟨walk, ⟨a, ha, haR⟩, ⟨b, hb, hbS⟩, hchain, hverts, hedges⟩ :=
    OpposingStringInterfacePath D o base R S hRS (by simpa [hunit] using hnadj)
      ts rs hf.1 hr.1
  have hdomf := PositiveCurvatureTileOdometerDomain C.1.1 U f C.property hOf
  have hdomk := PositiveCurvatureTileOdometerDomain C.1.1 V k C.property hOk
  have hv (z : GaussianInt) (hz : z ∈ walk) :
      z ∈ FootprintVertices U ∩ FootprintVertices V := by
    obtain ⟨⟨A,hA,hzA⟩,⟨B,hB,hzB⟩⟩ := hverts z hz
    obtain ⟨h,_,hh⟩ := hanc A hA
    obtain ⟨l,_,hl⟩ := hranc B hB
    have hzh : z ∈ h.domain := by rw [← hh.2.2.1] at hzA; exact hzA
    have hzl : z ∈ l.domain := by rw [← hl.2.2.1] at hzB; exact hzB
    exact ⟨hdomf ▸ hh.2.2.2.1 hzh, hdomk ▸ hl.2.2.2.1 hzl⟩
  have ha' : a = ER.point :=
    (ER.unique_common a).mp ⟨hv a (List.mem_of_head? ha), haR⟩
  have hb' : b = ES.point :=
    (ES.unique_common b).mp ⟨hv b (List.mem_of_getLast? hb), hbS⟩
  have hedge (a b : GaussianInt) (l r : List GaussianInt)
      (he : walk = l ++ a :: b :: r) :
      {a,b} ∈ FootprintEdges U ∩ FootprintEdges V := by
    obtain ⟨⟨A,hA,heA⟩,⟨B,hB,heB⟩⟩ := hedges a b l r he
    obtain ⟨h,_,hh⟩ := hanc A hA
    obtain ⟨k',_,hk'⟩ := hranc B hB
    have lift (A B : ProtoTile) (hAB : A.cells ⊆ B.cells)
        (he : {a,b} ∈ FootprintEdges A) : {a,b} ∈ FootprintEdges B := by
      obtain ⟨c,hc,he⟩ := he
      exact ⟨c,hAB hc,he⟩
    exact ⟨lift A U (P4158T1AncestorCells _ _ _ _ hh.2.1) heA,
      lift B V (P4158T1AncestorCells _ _ _ _ hk'.2.1) heB⟩
  have hexhaust := P4366T2WalkExhaustion ER.pathAB walk
    (ha.trans (congrArg some ha'))
    (by rw [hcross]; exact hb.trans (congrArg some hb')) hedge
  classical
  let inc := LatticeVertexIncidentCell x
  let route := fun (T : ProtoTile) (h : PartialOdometer) =>
    AncestorOdometer D.1.1 C.1.1 T U h f ∨
      AncestorOdometer D.1.1 C.1.1 T V h k ∨ h = hm ∨ h = hp
  let good := fun j : Fin 4 => ∃ T h,
    ((T, h) ∈ ts.zip hs ∨ (T, h) ∈ rs.zip ks) ∧
      inc j ∈ T.cells ∧ (h.domain : Set GaussianInt) = FootprintVertices T ∧ route T h
  have corner (T : ProtoTile) (u y : GaussianInt) (hu : u ∈ T.cells)
      (hy : y = u ∨ y = u+1 ∨ y = u+⟨0,1⟩ ∨ y = u+1+⟨0,1⟩) :
      y ∈ FootprintVertices T := by
    exact (show FootprintVertices T = _ from ite_eq_left (show T.cells.Nonempty from ⟨u,hu⟩)) ▸
      (show y ∈ {v | ∃ c ∈ T.cells,
        v = c ∨ v = c+1 ∨ v = c+⟨0,1⟩ ∨ v = c+1+⟨0,1⟩} from ⟨u,hu,hy⟩)
  have atX (j : Fin 4) :
      x = inc j ∨ x = inc j+1 ∨ x = inc j+⟨0,1⟩ ∨ x = inc j+1+⟨0,1⟩ := by
    fin_cases j <;> simp [inc, LatticeVertexIncidentCell, Zsqrtd.ext_iff]
  have hdis : Disjoint U.cells V.cells := by
    rcases htR.1 with h | h | h
    · exact h.2.2.1
    · exact (hUn.ne_empty h.1).elim
    · exact (hVn.ne_empty h.1).elim
  have edgeGood (e : Finset GaussianInt) (hxe : x ∈ e)
      (he : e ∈ FootprintEdges U ∩ FootprintEdges V) :
      ∃ j : Fin 4,
        e = ![{x,x+⟨0,1⟩},{x-1,x},{x-⟨0,1⟩,x},{x,x+1}] j ∧
          good j ∧ good (j+1) ∧
          ((inc j ∈ U.cells ∧ inc (j+1) ∈ V.cells) ∨
            (inc j ∈ V.cells ∧ inc (j+1) ∈ U.cells)) := by
    obtain ⟨a,b,l,r,hw,heq⟩ := hexhaust.2 e he
    obtain ⟨⟨A,hA,heA⟩,⟨B,hB,heB⟩⟩ := hedges a b l r hw
    obtain ⟨h,hmA,hh⟩ := hanc A hA
    obtain ⟨k',hmB,hk'⟩ := hranc B hB
    have hAU := P4158T1AncestorCells _ _ _ _ hh.2.1
    have hBV := P4158T1AncestorCells _ _ _ _ hk'.2.1
    have hAB : Disjoint A.cells B.cells := Finset.disjoint_left.mpr
      (fun c hc hd => Finset.disjoint_left.mp hdis (hAU hc) (hBV hd))
    obtain ⟨j,hj,hcells⟩ := P3102T2CommonEdgeSectorTransition A B x e hAB hxe
      (by rw [heq]; exact ⟨heA,heB⟩)
    refine ⟨j,hj,?_,?_,?_⟩
    · rcases hcells with hcells | hcells
      · exact ⟨A,h,Or.inl hmA,hcells.1,hh.2.2.1,Or.inl hh⟩
      · exact ⟨B,k',Or.inr hmB,hcells.1,hk'.2.2.1,Or.inr (Or.inl hk')⟩
    · rcases hcells with hcells | hcells
      · exact ⟨B,k',Or.inr hmB,hcells.2,hk'.2.2.1,Or.inr (Or.inl hk')⟩
      · exact ⟨A,h,Or.inl hmA,hcells.2,hh.2.2.1,Or.inl hh⟩
    · rcases hcells with hcells | hcells
      · exact Or.inl ⟨hAU hcells.1,hBV hcells.2⟩
      · exact Or.inr ⟨hBV hcells.1,hAU hcells.2⟩
  have incident (T : ProtoTile) (hT : T.cells.Nonempty) (hx : x ∈ FootprintVertices T) :
      ∃ j : Fin 4, inc j ∈ T.cells := by
    simp only [FootprintVertices, ite_eq_left hT, Set.mem_ofPred_eq] at hx
    obtain ⟨c,hc,hx⟩ := hx
    rcases hx with hx | hx | hx | hx
    · refine ⟨0,?_⟩; simpa [inc,LatticeVertexIncidentCell,hx] using hc
    · refine ⟨1,?_⟩; simpa [inc,LatticeVertexIncidentCell,hx] using hc
    · refine ⟨3,?_⟩; simpa [inc,LatticeVertexIncidentCell,hx] using hc
    · refine ⟨2,?_⟩; simpa [inc,LatticeVertexIncidentCell,hx,sub_sub] using hc
  have endpointGood (T : ProtoTile) (h : PartialOdometer)
      (hzip : (T, h) ∈ ts.zip hs) (ht : TouchingTriple U V T)
      (hx : x ∈ FootprintVertices T) (hr : h = hm ∨ h = hp)
      (e : Finset GaussianInt) (hxe : x ∈ e)
      (he : e ∈ FootprintEdges U ∩ FootprintEdges V) :
      ∃ j l : Fin 4, j ≠ l ∧ j ≠ l+1 ∧ good j ∧ good l ∧ good (l+1) := by
    have hOh := List.forall₂_zip hf.2.1 hzip
    obtain ⟨u,hu⟩ := CurvatureOneBandPrototileSingleton D T hunit
      (TileOdometerBandPrototile _ _ _ hOh)
    have hTn : T.cells.Nonempty := by simp [hu]
    have hTU : Disjoint T.cells U.cells := by
      rcases ht.2.2.1 with h | h | h
      · exact h.2.2.1
      · exact (hTn.ne_empty h.1).elim
      · exact (hUn.ne_empty h.1).elim
    have hTV : Disjoint T.cells V.cells := by
      rcases ht.2.1 with h | h | h
      · exact h.2.2.1.symm
      · exact (hVn.ne_empty h.1).elim
      · exact (hTn.ne_empty h.1).elim
    obtain ⟨j,hj⟩ := incident T hTn hx
    obtain ⟨l,_,hg₁,hg₂,htiles⟩ := edgeGood e hxe he
    have hjs (r : Fin 4) (hr : inc r ∈ U.cells ∨ inc r ∈ V.cells) : j ≠ r := by
      intro h; subst r
      rcases hr with hr | hr
      · exact Finset.disjoint_left.mp hTU hj hr
      · exact Finset.disjoint_left.mp hTV hj hr
    have hj₁ : j ≠ l := hjs l (htiles.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
    have hj₂ : j ≠ l+1 := hjs (l+1)
      (htiles.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2))
    refine ⟨j,l,hj₁,hj₂,?_,hg₁,hg₂⟩
    exact ⟨T,h,Or.inl hzip,hj,
      PositiveCurvatureTileOdometerDomain _ _ _ D.property hOh,Or.inr (Or.inr hr)⟩
  have hxV : x ∈ FootprintVertices U ∩ FootprintVertices V :=
    ⟨hdomf ▸ hxf,hdomk ▸ hxk⟩
  have hsimple : SimpleGridPath (FootprintVertices U ∩ FootprintVertices V)
      (FootprintEdges U ∩ FootprintEdges V) := by
    obtain ⟨p,hnd,hlen,_,_,hvs,hsteps,hes⟩ := ER.pathAB
    exact ⟨p,hnd,hlen,hvs,hsteps,hes⟩
  obtain ⟨e,hxe,he⟩ := SimpleGridPathVertexIncidentEdge _ _ hsimple x hxV
  have internalFinite : ∀ j k : Fin 4, j ≠ k → ∃ a : Fin 4,
      (a = j ∨ a = j+1 ∨ a = k ∨ a = k+1) ∧
      (a+2 = j ∨ a+2 = j+1 ∨ a+2 = k ∨ a+2 = k+1) := by decide +kernel
  have endpointFinite : ∀ j k : Fin 4, j ≠ k → j ≠ k+1 → ∃ a : Fin 4,
      (a = j ∨ a = k ∨ a = k+1) ∧ (a+2 = j ∨ a+2 = k ∨ a+2 = k+1) := by decide +kernel
  have hg : ∃ j : Fin 4, good j ∧ good (j+2) := by
    rcases SimpleGridPathPointTrichotomy _ _ _ _ x ER.pathAB ⟨e,hxe,he⟩ with hx | hx | htwo
    · have hxR := (ER.unique_common x).mpr hx |>.2
      have hzip : (R,hm) ∈ ts.zip hs := by
        obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp hf.1.2.1
        obtain ⟨s,hs'⟩ := List.head?_eq_some_iff.mp hhead
        simp [ht,hs']
      obtain ⟨j,l,hj,hl,hgj,hgl,hgl'⟩ := endpointGood R hm hzip htR hxR (Or.inl rfl) e hxe he
      obtain ⟨a,ha,hb⟩ := endpointFinite j l hj hl
      refine ⟨a,?_,?_⟩
      · rcases ha with rfl | rfl | rfl <;> assumption
      · rcases hb with hb | hb | hb <;> rw [hb] <;> assumption
    · have hxS := (ES.unique_common x).mpr (hx.trans hcross) |>.2
      have hzip : (S,hp) ∈ ts.zip hs := by
        obtain ⟨t,ht⟩ := List.getLast?_eq_some_iff.mp hf.1.2.2.1
        obtain ⟨s,hs'⟩ := List.getLast?_eq_some_iff.mp hlast
        have hlen : t.length = s.length := by
          have he := List.Forall₂.length_eq hf.2.1
          rw [ht,hs',List.length_append,List.length_append] at he
          simpa using he
        simp [ht,hs',List.zip_append hlen]
      obtain ⟨j,l,hj,hl,hgj,hgl,hgl'⟩ := endpointGood S hp hzip htS hxS (Or.inr rfl) e hxe he
      obtain ⟨a,ha,hb⟩ := endpointFinite j l hj hl
      refine ⟨a,?_,?_⟩
      · rcases ha with rfl | rfl | rfl <;> assumption
      · rcases hb with hb | hb | hb <;> rw [hb] <;> assumption
    · obtain ⟨e,f,hne,hxe,hxf,he,hf⟩ := htwo
      obtain ⟨j,hj,hgj,hgj',_⟩ := edgeGood e hxe he
      obtain ⟨k,hk,hgk,hgk',_⟩ := edgeGood f hxf hf
      have hjk : j ≠ k := by intro h; exact hne (hj.trans (h ▸ hk.symm))
      obtain ⟨a,ha,hb⟩ := internalFinite j k hjk
      refine ⟨a,?_,?_⟩
      · rcases ha with rfl | rfl | rfl | rfl <;> assumption
      · rcases hb with hb | hb | hb | hb <;> rw [hb] <;> assumption
  obtain ⟨j,hj,hj'⟩ := hg
  intro y hy
  have hycover :
      (y = inc j ∨ y = inc j+1 ∨ y = inc j+⟨0,1⟩ ∨ y = inc j+1+⟨0,1⟩) ∨
      (y = inc (j+2) ∨ y = inc (j+2)+1 ∨ y = inc (j+2)+⟨0,1⟩ ∨
        y = inc (j+2)+1+⟨0,1⟩) := by
    fin_cases j <;> rcases hy with rfl | rfl | rfl | rfl | rfl
    all_goals simp [inc,LatticeVertexIncidentCell,Zsqrtd.ext_iff]
  rcases hycover with hy | hy
  · obtain ⟨T,h,hm,hc,hd,hr⟩ := hj
    refine ⟨T,h,hm,?_,?_,hr⟩
    · change x ∈ (h.domain : Set GaussianInt)
      rw [hd]
      exact corner T (inc j) x hc (atX j)
    · change y ∈ (h.domain : Set GaussianInt)
      rw [hd]
      exact corner T (inc j) y hc hy
  · obtain ⟨T,h,hm,hc,hd,hr⟩ := hj'
    refine ⟨T,h,hm,?_,?_,hr⟩
    · change x ∈ (h.domain : Set GaussianInt)
      rw [hd]
      exact corner T (inc (j+2)) x hc (atX (j+2))
    · change y ∈ (h.domain : Set GaussianInt)
      rw [hd]
      exact corner T (inc (j+2)) y hc hy

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4715T1PatchEnumeration
public import LeanPool.ApollonianSuperharmonic.P4677T2IncidenceLedger
public import LeanPool.ApollonianSuperharmonic.P4802T1PatchFaceRestriction
public import LeanPool.ApollonianSuperharmonic.P4802T1CrossPatchFaces

-- [TABLET NODE: P4715T1CoefficientEdges]

/-!
# P4715T1CoefficientEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1CoefficientEdges :
    (∀ a b, P4715T1Arc a b = P4715T1Arc b a) ∧
    (∀ a b, AllowedSubtileIncidence a b →
      ∃ h : Set.Icc (0 : Real) 1 ≃ₜ P4715T1Arc a b,
        ((h ⟨0, by norm_num⟩ : P4715T1Arc a b) : Real × Real) =
          P4715T1Position a ∧
        ((h ⟨1, by norm_num⟩ : P4715T1Arc a b) : Real × Real) =
          P4715T1Position b) ∧
    ∀ a b c d, AllowedSubtileIncidence a b → AllowedSubtileIncidence c d →
      ({a, b} : Set PeriodicSubtileIndex) ≠ {c, d} →
      P4715T1Arc a b ∩ P4715T1Arc c d =
        P4715T1Position '' (({a, b} : Set PeriodicSubtileIndex) ∩ {c, d}) := by
-- BODY
  classical
  refine ⟨fun a b => segment_symm Real _ _, ?_, ?_⟩
  · intro a b hab
    have hn : a ≠ b := by
      intro h
      subst b
      exact P4677T2IncidenceLedger.2.1 a hab
    have hne := P4715T1PositionInjective.ne hn
    let g : Set.Icc (0 : Real) 1 → P4715T1Arc a b := fun t =>
      ⟨AffineMap.lineMap (P4715T1Position a) (P4715T1Position b) (t : Real),
        lineMap_mem_segment Real _ _ t.property⟩
    have hg : Function.Bijective g := by
      constructor
      · intro s t h
        apply Subtype.ext
        exact AffineMap.lineMap_injective Real hne (congrArg Subtype.val h)
      · intro p
        have hp : (p : Real × Real) ∈
            AffineMap.lineMap (P4715T1Position a) (P4715T1Position b) ''
              Set.Icc (0 : Real) 1 := by
          simpa only [P4715T1Arc, segment_eq_image_lineMap] using p.property
        obtain ⟨t, ht, heq⟩ := hp
        exact ⟨⟨t, ht⟩, Subtype.ext heq⟩
    let e := Equiv.ofBijective g hg
    have hc : Continuous (e : Set.Icc (0 : Real) 1 → P4715T1Arc a b) := by
      change Continuous g
      fun_prop
    refine ⟨hc.homeoOfEquivCompactToT2, ?_, ?_⟩
    · change AffineMap.lineMap _ _ (0 : Real) = _
      simp
    · change AffineMap.lineMap _ _ (1 : Real) = _
      simp
  · intro a b c d hab hcd hne
    obtain ⟨f, g, hfg, hfab, hgab, hfaces⟩ :=
      P4677T2IncidenceLedger.2.2.2.2.2 a b hab
    obtain ⟨⟨k, i⟩, hki, haddress⟩ := P4715T1PatchEnumeration f
    obtain ⟨f', g', hfg', hfcd, hgcd, hfaces'⟩ :=
      P4677T2IncidenceLedger.2.2.2.2.2 c d hcd
    obtain ⟨⟨l, j⟩, hlj, haddress'⟩ := P4715T1PatchEnumeration f'
    have hsub : (({a,b} : Set PeriodicSubtileIndex) ∩ {c,d}).Subsingleton := by
      intro x hx y hy
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      by_contra hxy
      apply hne
      rcases hx with ⟨hxa,hxc⟩
      rcases hy with ⟨hya,hyc⟩
      rcases hxa with hxa | hxa <;> rcases hya with hya | hya <;>
        rcases hxc with hxc | hxc <;> rcases hyc with hyc | hyc <;>
        subst_vars <;> simp_all [Set.pair_comm]
    have hrhs : convexHull Real
        (P4715T1Position '' (({a,b} : Set PeriodicSubtileIndex) ∩ {c,d})) =
        P4715T1Position '' (({a,b} : Set PeriodicSubtileIndex) ∩ {c,d}) :=
      convexHull_eq_self.mpr (hsub.image _).convex
    have habHull : P4715T1Arc a b =
        convexHull Real (P4715T1Position '' ({a,b} : Set PeriodicSubtileIndex)) := by
      simp only [P4715T1Arc, Set.image_pair, convexHull_pair]
    have hcdHull : P4715T1Arc c d =
        convexHull Real (P4715T1Position '' ({c,d} : Set PeriodicSubtileIndex)) := by
      simp only [P4715T1Arc, Set.image_pair, convexHull_pair]
    rw [habHull,hcdHull,← hrhs]
    have hinside (k : Int × Int) (i : Fin 12) (f : PeriodicSubtileFaceIndex)
        (hki : P4715T1FaceShift k (P4715T1PatchFaces i) = f)
        (z : PeriodicSubtileIndex) (hz : z ∈ Set.range (SixSubtileFaceVertices f)) :
        P4715T1Position z ∈
          (fun x : Real × Real => x + ((k.1 : Real),(k.2 : Real))) ''
            P4715T1Hexagon := by
      obtain ⟨t,ht⟩ := hz
      have hv := P4715T1IndexAction.2.2.2.2.2 k (P4715T1PatchFaces i) t
      rw [hki] at hv
      have hsz : P4715T1VertexShift k
          (SixSubtileFaceVertices (P4715T1PatchFaces i) t) = z := hv.symm.trans ht
      refine ⟨P4715T1Position (SixSubtileFaceVertices (P4715T1PatchFaces i) t), ?_, ?_⟩
      · rw [← P4715T1HexagonSubdivision.1]
        exact Set.mem_iUnion.mpr ⟨i,
          subset_convexHull Real _ ⟨_,⟨t,rfl⟩,rfl⟩⟩
      · exact ((P4715T1CoefficientTranslation k).1 _).symm.trans
          (congrArg P4715T1Position hsz)
    by_cases hkl : k = l
    · subst l
      obtain ⟨ia,hia⟩ := hfab.1
      obtain ⟨ib,hib⟩ := hfab.2
      obtain ⟨ic,hic⟩ := hfcd.1
      obtain ⟨id,hid⟩ := hfcd.2
      let A := SixSubtileFaceVertices (P4715T1PatchFaces i) ia
      let B := SixSubtileFaceVertices (P4715T1PatchFaces i) ib
      let C := SixSubtileFaceVertices (P4715T1PatchFaces j) ic
      let D := SixSubtileFaceVertices (P4715T1PatchFaces j) id
      have hA : P4715T1VertexShift k A = a := by
        rw [← P4715T1IndexAction.2.2.2.2.2, hki]; exact hia
      have hB : P4715T1VertexShift k B = b := by
        rw [← P4715T1IndexAction.2.2.2.2.2, hki]; exact hib
      have hC : P4715T1VertexShift k C = c := by
        rw [← P4715T1IndexAction.2.2.2.2.2, hlj]; exact hic
      have hD : P4715T1VertexShift k D = d := by
        rw [← P4715T1IndexAction.2.2.2.2.2, hlj]; exact hid
      have hSA : ({a,b} : Set PeriodicSubtileIndex) =
          P4715T1VertexShift k '' ({A,B} : Set PeriodicSubtileIndex) := by
        simp only [Set.image_pair,hA,hB]
      have hTC : ({c,d} : Set PeriodicSubtileIndex) =
          P4715T1VertexShift k '' ({C,D} : Set PeriodicSubtileIndex) := by
        simp only [Set.image_pair,hC,hD]
      have hAB : ({A,B} : Set PeriodicSubtileIndex) ⊆
          Set.range (SixSubtileFaceVertices (P4715T1PatchFaces i)) := by
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨ia,rfl⟩
        · rcases hz with rfl; exact ⟨ib,rfl⟩
      have hCD : ({C,D} : Set PeriodicSubtileIndex) ⊆
          Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j)) := by
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨ic,rfl⟩
        · rcases hz with rfl; exact ⟨id,rfl⟩
      have hull_shift (S : Set PeriodicSubtileIndex) :
          convexHull Real (P4715T1Position '' (P4715T1VertexShift k '' S)) =
          (fun x : Real × Real => x + ((k.1 : Real),(k.2 : Real))) ''
            convexHull Real (P4715T1Position '' S) := by
        let G : (Real × Real) →ᵃ[Real] (Real × Real) :=
          AffineMap.id Real (Real × Real) +
            AffineMap.const Real (Real × Real) ((k.1 : Real),(k.2 : Real))
        change convexHull Real (P4715T1Position '' (P4715T1VertexShift k '' S)) =
          G '' convexHull Real (P4715T1Position '' S)
        rw [G.image_convexHull, Set.image_image, Set.image_image]
        congr 2
        funext z
        exact (P4715T1CoefficientTranslation k).1 z
      apply Set.Subset.antisymm
      · intro p hp
        have hp1 := hp.1
        have hp2 := hp.2
        rw [hSA,hull_shift] at hp1
        rw [hTC,hull_shift] at hp2
        obtain ⟨x,hx,hxp⟩ := hp1
        obtain ⟨y,hy,hyp⟩ := hp2
        have hxy : x = y := add_right_cancel (hxp.trans hyp.symm)
        subst y
        have hxST : x ∈ convexHull Real
            (P4715T1Position '' (({A,B} : Set PeriodicSubtileIndex) ∩ {C,D})) := by
          rw [← P4802T1PatchFaceRestriction i j _ _ hAB hCD]
          exact ⟨hx,hy⟩
        have hpST : p ∈ convexHull Real (P4715T1Position ''
            (P4715T1VertexShift k '' (({A,B} : Set PeriodicSubtileIndex) ∩ {C,D}))) := by
          rw [hull_shift]
          exact ⟨x,hxST,hxp⟩
        have hs : P4715T1VertexShift k ''
            (({A,B} : Set PeriodicSubtileIndex) ∩ {C,D}) ⊆
            ({a,b} : Set PeriodicSubtileIndex) ∩ {c,d} := by
          rintro _ ⟨z,hz,rfl⟩
          constructor
          · rw [hSA]; exact ⟨z,hz.1,rfl⟩
          · rw [hTC]; exact ⟨z,hz.2,rfl⟩
        exact convexHull_mono (Set.image_mono hs) hpST
      · exact Set.subset_inter
          (convexHull_mono (Set.image_mono Set.inter_subset_left))
          (convexHull_mono (Set.image_mono Set.inter_subset_right))
    · apply P4802T1CrossPatchFaces k l hkl
      · intro z hz
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hinside k i f hki _ hfab.1
        · exact hinside k i f hki _ hfab.2
      · intro z hz
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hinside l j f' hlj _ hfcd.1
        · exact hinside l j f' hlj _ hfcd.2

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.OdometerStringSlopeTelescoping
public import LeanPool.ApollonianSuperharmonic.BandPrototileQuarterTurn

public import LeanPool.ApollonianSuperharmonic.P4261T2DiamondBoundary
public import LeanPool.ApollonianSuperharmonic.P4261T2RegularEdgeReduction
public import LeanPool.ApollonianSuperharmonic.P4261T2InterfacePropagation
public import LeanPool.ApollonianSuperharmonic.P4261T2UnitInterface
public import LeanPool.ApollonianSuperharmonic.P4261T2PairNormalization
public import LeanPool.ApollonianSuperharmonic.P4261T2AncestorSymmetry
public import LeanPool.ApollonianSuperharmonic.FordLeftBoundaryCompatibility
public import LeanPool.ApollonianSuperharmonic.FordOpposingBoundaryStarLocalization
public import LeanPool.ApollonianSuperharmonic.DiamondOpposingBoundaryStarLocalization
public import LeanPool.ApollonianSuperharmonic.OpposingBoundaryStarLocalization

-- [TABLET NODE: LeftAdjacentOdometerCompatibility]

/-!
# LeftAdjacentOdometerCompatibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LeftCompatibilityGeometry

private theorem compatibility_symm :
    (by
      classical
      exact
        ∀ (a : PartialOdometer), ∀ (b : PartialOdometer), (OdometerCompatibility a b) →
            (OdometerCompatibility b a) ) := by
  classical
  intro a b hc
  rcases hc with hd | ⟨c, hc⟩
  · exact Or.inl hd.symm
  · exact Or.inr ⟨-c, by intro x hb ha; have := hc x ha hb; omega⟩

private theorem adjacency_symm :
    (by
      classical
      exact
        ∀ (D : BandCircle), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (a : PartialOdometer), ∀ (b :
            PartialOdometer), (1 < D.1.1.1) → ((LeftLatticeAdjacent D A B a b) →
            (LeftLatticeAdjacent D B A b a)) ) := by
  classical
  intro D A B a b hl ha
  obtain ⟨hA, hB, p, r, hp, hr, hu | ⟨q, j, e, hq, hD, hc, hs, ht⟩⟩ := ha
  · omega
  · refine ⟨hB, hA, r, p, hr, hp, Or.inr ⟨q, j, !e, hq, hD, ?_, ?_, ?_⟩⟩
    · cases e <;> simpa using congrArg Neg.neg hc
    · cases e <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, one_mul, neg_one_mul] <;> linarith
    · cases e <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, one_mul, neg_one_mul] <;> linarith

private theorem adjacency_action :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (D : BandCircle), ∀ (E : BandCircle), (E.1.1 =
            BandPackingSymmetryCircleAction g D.1.1) → ((1 < D.1.1.1) → (∀ (A : ProtoTile), ∀ (B
            : ProtoTile), ∀ (a : PartialOdometer), ∀ (b : PartialOdometer), (LeftLatticeAdjacent
            D A B a b) → (LeftLatticeAdjacent E (BandPackingSymmetryTileAction g A)
            (BandPackingSymmetryTileAction g B) (BandPackingSymmetryPartialOdometerAction g a)
            (BandPackingSymmetryPartialOdometerAction g b)))) ) := by
  classical
  intro g D E hE hl A B a b ha
  obtain ⟨hA, hB, p, r, hp, hr, hu | ⟨q, j, e, hq, hD, hc, hs, ht⟩⟩ := ha
  · omega
  · obtain ⟨negative, s, t, _, hAn, hBn, hpn, hrn, hcn, hsn, htn, _⟩ :=
      LeftLatticeAdjacentPackingSymmetryTransport g q hq j e A B a b p r
        (by simpa [hD] using hA) (by simpa [hD] using hB) hp hr hc hs ht
    have hEn : BandPackingSymmetryQuadrupleAction g q 0 = E.1.1 := by
      simpa [BandPackingSymmetryQuadrupleAction, hD] using hE.symm
    refine ⟨by simpa only [hEn] using hAn, by simpa only [hEn] using hBn,
      s, t, hpn, hrn, Or.inr ⟨BandPackingSymmetryQuadrupleAction g q,
        (if BandPackingSymmetryReversesOrientation g then -j else j),
        xor e negative, BandPackingSymmetryProperCovariance g q hq,
        hEn, hcn, hsn, htn⟩⟩

private theorem membership_action :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (a : PartialOdometer), ∀ (x : GaussianInt),
            BandPackingSymmetryVectorAction g x ∈ (BandPackingSymmetryPartialOdometerAction g
            a).domain ↔ x ∈ a.domain ) := by
  classical
  intro g a x
  obtain ⟨f, hf, _, _⟩ := P4055T1PackingGridEquivalence g
  have hi : Function.Injective (BandPackingSymmetryVectorAction g) := by
    intro u v huv
    apply f.injective
    simpa only [hf] using huv
  change _ ∈ ((BandPackingSymmetryPartialOdometerAction g a).domain :
    Set GaussianInt) ↔ _
  rw [(BandPackingSymmetryPartialOdometerActionFormulas g a a).1]
  constructor
  · rintro ⟨z, hz, he⟩
    exact hi he ▸ hz
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem star_action :
    (by
      classical
      exact
        (∀ (g : BandPackingSymmetry), ∀ (a : PartialOdometer), ∀ (x : GaussianInt),
            BandPackingSymmetryVectorAction g x ∈ (BandPackingSymmetryPartialOdometerAction g
            a).domain ↔ x ∈ a.domain) → (∀ (g : BandPackingSymmetry), ∀ (a : PartialOdometer), ∀
            (b : PartialOdometer), ∀ (x : GaussianInt), (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
              y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ a.domain ∨ y ∈ b.domain) → (∀ y, y =
                  BandPackingSymmetryVectorAction g x ∨ y = BandPackingSymmetryVectorAction g x +
                  1 ∨ y = BandPackingSymmetryVectorAction g x - 1 ∨ y =
                  BandPackingSymmetryVectorAction g x + ⟨0, 1⟩ ∨ y =
                  BandPackingSymmetryVectorAction g x - ⟨0, 1⟩ → y ∈
                  (BandPackingSymmetryPartialOdometerAction g a).domain ∨ y ∈
                  (BandPackingSymmetryPartialOdometerAction g b).domain)) ) := by
  classical
  intro membership_action g a b x hs y hy
  obtain ⟨f, hf, _, hback⟩ := P4055T1PackingGridEquivalence g
  have hy' : f.symm y = x ∨ f.symm y = x + 1 ∨ f.symm y = x - 1 ∨
      f.symm y = x + ⟨0, 1⟩ ∨ f.symm y = x - ⟨0, 1⟩ := by
    rcases hy with he | hn
    · left
      rw [← hf x] at he
      simp [he]
    · right
      have hn' : y = f x + 1 ∨ y = f x - 1 ∨
          y = f x + ⟨0, 1⟩ ∨ y = f x - ⟨0, 1⟩ := by simpa only [hf] using hn
      simpa using hback (f x) y hn'
  rcases hs (f.symm y) hy' with ha | hb
  · left
    have hm := (membership_action g a (f.symm y)).mpr ha
    simpa only [← hf, Equiv.apply_symm_apply] using hm
  · right
    have hm := (membership_action g b (f.symm y)).mpr hb
    simpa only [← hf, Equiv.apply_symm_apply] using hm

private theorem layout :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (D :
            BandCircle), (q 0 = D.1.1) → (∀ (A : ProtoTile), (BandPrototile (q 0) A) → (Nonempty
            (BandOrderedGeneralLayoutCertificate q cfg D A) ∧ QuarterTurnSymmetric A)) ) := by
  classical
  intro q cfg D hD A hA
  refine ⟨?_, (BandTileSimultaneousInduction q cfg.proper A hA).2.2.2.1⟩
  apply BandOrderedGeneralLayout q cfg D hD A hA
  · intro q' T' S' hq' hT' hocc hcells _
    have hI := BandTileSimultaneousInduction q' hq' T' hT'
    exact ⟨hI.1, hI.2.1, hI.2.2.1 S' hocc hcells⟩
  · intro E U hU _
    exact BandPrototileQuarterTurn.symmetry E U hU
  · intro q' T' U hq' hT' _ hlarge i hU hcentU
    exact (BandTileSimultaneousInduction q' hq' T' hT').2.2.2.2.2.1
      hlarge i U hU hcentU
  · intro q' T' U V hq' hT' _ i hU hV hcentU hcentV
    exact (BandTileSimultaneousInduction q' hq' T' hT').2.2.2.2.2.2.1
      i U V hU hV hcentU hcentV

private theorem make_adj :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (D : BandCircle), (q 0 =
            D.1.1) → (∀ (j : Fin 3), ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (a :
            PartialOdometer), ∀ (b : PartialOdometer), ∀ (p : Real × Real), ∀ (r : Real × Real),
            (TileOdometer D.1.1 A a) → ((TileOdometer D.1.1 B b) → ((PartialOdometerSlope a =
            some p) → ((PartialOdometerSlope b = some r) → ((TileCentroid B - TileCentroid A =
            GaussianRealPoint (BandVectors.1 (q j.succ) (q 0))) → ((r - p = GaussianRealPoint
                (BandVectors.2 (q j.succ) (q 0))) → (LeftLatticeAdjacent D A B a b)))))))) ) := by
  classical
  intro q hq D hD j A B a b p r hA hB hp hr hc hs
  refine ⟨hA, hB, p, r, hp, hr, Or.inr ⟨q, j, true, hq, hD, ?_, ?_, ?_⟩⟩
  · simpa using hc
  · simpa [GaussianRealPoint] using congrArg Prod.fst hs
  · simpa [GaussianRealPoint] using congrArg Prod.snd hs

private theorem compatibility :
    (by
      classical
      exact
        (∀ (a : PartialOdometer), ∀ (b : PartialOdometer), (OdometerCompatibility a b) →
            (OdometerCompatibility b a)) → ((∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
            BandOrderedGeneralConfiguration q), ∀ (D : BandCircle), (q 0 = D.1.1) → (∀ (A :
            ProtoTile), (BandPrototile (q 0) A) → (Nonempty (BandOrderedGeneralLayoutCertificate
            q cfg D A) ∧ QuarterTurnSymmetric A))) → ((∀ (q : Fin 4 → CircleCoordinates),
            (ProperBandQuadruple q) → (∀ (D : BandCircle), (q 0 = D.1.1) → (∀ (j : Fin 3), ∀ (A :
            ProtoTile), ∀ (B : ProtoTile), ∀ (a : PartialOdometer), ∀ (b : PartialOdometer), ∀ (p
            : Real × Real), ∀ (r : Real × Real), (TileOdometer D.1.1 A a) → ((TileOdometer D.1.1
            B b) → ((PartialOdometerSlope a = some p) → ((PartialOdometerSlope b = some r) →
            ((TileCentroid B - TileCentroid A = GaussianRealPoint (BandVectors.1 (q j.succ) (q
            0))) → ((r - p = GaussianRealPoint (BandVectors.2 (q j.succ) (q 0))) →
            (LeftLatticeAdjacent D A B a b))))))))) → (∀ n : Nat, ∀ (D : BandCircle), ∀ (A :
            ProtoTile), ∀ (B : ProtoTile), ∀ (a : PartialOdometer), ∀ (b : PartialOdometer),
            D.1.1.1.toNat = n → LeftLatticeAdjacent D A B a b → OdometerCompatibility a b))) ) := by
  classical
  intro compatibility_symm layout make_adj n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D A B a b hn ha
    by_cases hu : D.1.1.1 = 1
    · obtain ⟨p, r, hp, hr, h0, h1⟩ := P4261T2AdjacentMatrixSlope D A B a b ha
      exact P4261T2UnitBoundary D hu A B a b ha.1 ha.2.1 p r hp hr h0 h1
    have ha_original := ha
    obtain ⟨hA, hB, p, r, hp, hr, hunit | ⟨q, j, e, hq, hD, hc, hs, ht⟩⟩ := ha
    · exact (hu hunit.1).elim
    by_cases hline : ∃ j : Fin 4, (q j).1 = 0
    · exact FordLeftBoundaryCompatibility D A B a b ha_original q hq hD hline
    have hj : 0 < (q j.succ).1 := by
      have hn := (ProperBandCurvatureStructure q hq).2.1 j
      have hz : (q j.succ).1 ≠ 0 := by intro hz; exact hline ⟨j.succ, hz⟩
      omega
    let E : BandCircle := ⟨⟨q j.succ,
      ⟨Or.inl hj, ⟨q, hq.1, j.succ, rfl⟩⟩⟩, hj⟩
    have hsr : r - p = (if e = true then (1 : Real) else -1) •
        GaussianRealPoint (BandVectors.2 (q j.succ) (q 0)) := by
      exact Prod.ext hs ht
    obtain ⟨g, qn, Dn, En, jn, en, pn, rn, hqn, hDn, hEn, hDact, hEact,
        hDcurv, hEcurv, hAn, hBn, hpn, hrn, hcn, hsn, hreg⟩ :=
      P4261T2PairNormalization q hq D E j e hD rfl A B a b hA hB p r hp hr hc hsr
    have smaller : ∀ (F : BandCircle) (U V : ProtoTile) (f k : PartialOdometer),
        F.1.1.1 < Dn.1.1.1 → LeftLatticeAdjacent F U V f k →
          OdometerCompatibility f k := by
      intro F U V f k hless hadj
      have hpos := F.2
      have hlt : F.1.1.1.toNat < n := by omega
      exact ih F.1.1.1.toNat hlt F U V f k rfl hadj
    have positive : ∀ (U V : ProtoTile) (f k : PartialOdometer) (s t : Real × Real),
        TileOdometer Dn.1.1 U f → TileOdometer Dn.1.1 V k →
        PartialOdometerSlope f = some s → PartialOdometerSlope k = some t →
        TileCentroid V - TileCentroid U =
          GaussianRealPoint (BandVectors.1 (qn jn.succ) (qn 0)) →
        t - s = GaussianRealPoint (BandVectors.2 (qn jn.succ) (qn 0)) →
        OdometerCompatibility f k := by
      intro U V f k s t hU hV hsf htk hcent hslope
      rcases hreg with ⟨P, hP, hFord⟩ | ⟨K, hK, hDiamond⟩ | ⟨cfg⟩
      · apply FordLeftBoundaryCompatibility Dn U V f k
          (make_adj qn hqn Dn hDn jn U V f k s t hU hV hsf htk hcent hslope) qn hqn hDn
        exact ⟨3, by simp [hFord, FordRecursiveQuadruple]⟩
      · exact P4261T2DiamondBoundary K Dn (by simpa [hDiamond] using hDn)
          jn U V f k hU hV s t hsf htk
          (by simpa [hDiamond] using hcent) (by simpa [hDiamond] using hslope)
      · obtain ⟨cfg⟩ := cfg
        have hproto : BandPrototile (qn 0) U := by
          simpa only [hDn] using TileOdometerBandPrototile Dn.1.1 U f hU
        obtain ⟨⟨cert⟩, hsym⟩ := layout qn cfg Dn hDn U hproto
        have hpkg : Nonempty (P4261T2LiteralInterface En Dn U V f k) := by
          by_cases hunit : En.1.1.1 = 1
          · exact P4261T2UnitInterface qn cfg Dn En jn hDn hEn U V f k cert hsym
              hU hV hunit s t hsf htk hcent hslope
          · have hlarge : 1 < En.1.1.1 := by have hpos := En.2; omega
            obtain ⟨o, base, Rm, Rp, tiles, reverseTiles, fs, ks, hm, hp,
                pm, pp, path, hboundary, hreverse, hforward, hbackward,
                hhead, hlast, hhead', hlast', hOm, hOp, hpm, hpp,
                hminusSlope, hplusSlope, htriplem, htriplep, hnodup, hlen,
                hfirst, hfinal, hvertices, hedges, hvertexRestrictions,
                hedgeRestrictions⟩ :=
              OpposingBoundaryInterfaceExhaustion qn cfg Dn En jn hDn hEn
                U V f k cert hsym hU hV hlarge s t hsf htk hcent hslope
            refine ⟨⟨o, base, Rm, Rp, tiles, reverseTiles, fs, ks, hm, hp, path,
              hforward, hbackward, hhead, hlast, hhead', hlast', hnodup,
              hlen, hvertices, hedges, ?_⟩⟩
            intro x y pre post he
            obtain ⟨⟨W, a, _, hWa, heW, ha⟩, ⟨X, b, _, hXb, heX, hb⟩, _⟩ :=
              hedgeRestrictions x y pre post he
            exact ⟨W, X, a, b, hWa, hXb, ⟨heW, heX⟩, ha, hb⟩
        obtain ⟨pkg⟩ := hpkg
        apply P4261T2InterfacePropagation En Dn U V f k hU hV pkg
        intro W X a b hWa hXb he
        have htelescope : ∃ s t : Real × Real,
            PartialOdometerSlope a = some s ∧ PartialOdometerSlope b = some t ∧
            t.1 - s.1 = CircleMatrix En 0 0 * ((TileCentroid X).1 - (TileCentroid W).1) +
              CircleMatrix En 0 1 * ((TileCentroid X).2 - (TileCentroid W).2) ∧
            t.2 - s.2 = CircleMatrix En 1 0 * ((TileCentroid X).1 - (TileCentroid W).1) +
              CircleMatrix En 1 1 * ((TileCentroid X).2 - (TileCentroid W).2) := by
          exact odometerStringSlopeTelescoping En pkg.orientation pkg.base
            pkg.minus pkg.plus pkg.tiles pkg.reverseTiles pkg.functions pkg.reverseFunctions
            pkg.forward pkg.backward pkg.hminus pkg.head_forward pkg.last_backward W X a b
            hWa hXb
        obtain ⟨s, t, hs, ht, h0, h1⟩ := htelescope
        have hOW := List.forall₂_zip pkg.forward.2.1 hWa
        have hOX := List.forall₂_zip pkg.backward.2.1 hXb
        have hWmem : W ∈ pkg.tiles := (List.of_mem_zip hWa).1
        have hXmem : X ∈ pkg.reverseTiles := (List.of_mem_zip hXb).1
        rcases P4261T2RegularEdgeReduction En pkg.base W X pkg.forward.1.1
            (pkg.forward.1.2.2.2.2.1 W hWmem) (pkg.backward.1.2.2.2.2.1 X hXmem)
            a b hOW hOX s t hs ht h0 h1 he with hc | ha
        · exact hc
        · apply smaller En W X a b _ ha
          simpa only [hEn, hDn] using hqn.2 jn
    have hncompat : OdometerCompatibility
        (BandPackingSymmetryPartialOdometerAction g a)
        (BandPackingSymmetryPartialOdometerAction g b) := by
      cases en with
      | false =>
          apply compatibility_symm
          apply positive _ _ _ _ rn pn hBn hAn hrn hpn
          · simpa using congrArg Neg.neg hcn
          · simpa using congrArg Neg.neg hsn
      | true =>
          exact positive _ _ _ _ pn rn hAn hBn hpn hrn (by simpa using hcn) (by simpa using hsn)
    exact (BandPackingSymmetryPartialOdometerActionFormulas g a b).2.2.2.2.2.2.1.mp hncompat

private theorem hslope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (e : Bool), ∀ (p : ℝ × ℝ), ∀ (r : ℝ × ℝ),
            (r.1 - p.1 = CircleMatrix C (0 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * ((TileCentroid
            T').1 - (TileCentroid T).1) + CircleMatrix C (0 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) *
            ((TileCentroid T').2 - (TileCentroid T).2)) → ((r.2 - p.2 = CircleMatrix C (1 : Fin
            (2 : ℕ)) (0 : Fin (2 : ℕ)) * ((TileCentroid T').1 - (TileCentroid T).1) +
            CircleMatrix C (1 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) * ((TileCentroid T').2 -
            (TileCentroid T).2)) → ((CircleMatrix C (0 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) *
            (↑(BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).re : ℝ) + CircleMatrix C (0 : Fin
            (2 : ℕ)) (1 : Fin (2 : ℕ)) * (↑(BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).im :
            ℝ) = (↑(BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).re : ℝ)) → ((CircleMatrix C
            (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * (↑(BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ)))).re : ℝ) + CircleMatrix C (1 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) * (↑(BandVectors.1
            (q i.succ) (q (0 : Fin (4 : ℕ)))).im : ℝ) = (↑(BandVectors.2 (q i.succ) (q (0 : Fin
            (4 : ℕ)))).im : ℝ)) → (((TileCentroid T').1 - (TileCentroid T).1 = (if e = true then
            (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).re : ℝ))
            → (((TileCentroid T').2 - (TileCentroid T).2 = (if e = true then (1 : ℝ) else (-1 :
            ℝ)) * (↑(BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).im : ℝ)) → (r - p = (if e =
            true then (1 : Real) else -1) • GaussianRealPoint (BandVectors.2 (q i.succ) (q
            0)))))))) ) := by
  classical
  intro C T T' q i e p r h0 h1 hin0 hin1 hc0 hc1
  apply Prod.ext
  · change r.1 - p.1 = (if e = true then (1 : Real) else -1) *
      ((BandVectors.2 (q i.succ) (q 0)).re : Real)
    rw [hc0, hc1] at h0
    linear_combination h0 + (if e = true then (1 : Real) else -1) * hin0
  · change r.2 - p.2 = (if e = true then (1 : Real) else -1) *
      ((BandVectors.2 (q i.succ) (q 0)).im : Real)
    rw [hc0, hc1] at h1
    linear_combination h1 + (if e = true then (1 : Real) else -1) * hin1

private theorem positive_star :
    (by
      classical
      exact
        (∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (D :
            BandCircle), (q 0 = D.1.1) → (∀ (A : ProtoTile), (BandPrototile (q 0) A) → (Nonempty
            (BandOrderedGeneralLayoutCertificate q cfg D A) ∧ QuarterTurnSymmetric A))) → (∀ (qn
            : Fin (4 : ℕ) → CircleCoordinates), ∀ (Cn : BandCircle), ∀ (Din : BandCircle), ∀ (j :
            Fin (3 : ℕ)), (ProperBandQuadruple qn) → ((qn (0 : Fin (4 : ℕ)) = Cn.1.1) → ((qn
            j.succ = Din.1.1) → (((∃ (P : FordFareyParameter), (1 : ℕ) < P.q ∧ qn =
            FordRecursiveQuadruple P) ∨ (∃ (K : DiamondParameter), (1 : ℕ) < K.1 ∧ qn =
            DiamondRecursiveQuadruple K) ∨ Nonempty (BandOrderedGeneralConfiguration qn)) → ((1 <
            Din.1.1.1) → (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (a : PartialOdometer), ∀ (b :
            PartialOdometer), ∀ (s : Real × Real), ∀ (t : Real × Real), TileOdometer Cn.1.1 A a →
            TileOdometer Cn.1.1 B b → PartialOdometerSlope a = some s → PartialOdometerSlope b =
            some t → TileCentroid B - TileCentroid A = GaussianRealPoint (BandVectors.1 (qn
            j.succ) (qn 0)) → t - s = GaussianRealPoint (BandVectors.2 (qn j.succ) (qn 0)) → ∀ z,
            z ∈ a.domain → z ∈ b.domain → (∀ y, y = z ∨ y = z + 1 ∨ y = z - 1 ∨ y = z + ⟨0, 1⟩ ∨
            y = z - ⟨0, 1⟩ → y ∈ a.domain ∨ y ∈ b.domain) → ∃ (U V : ProtoTile) (f k :
            PartialOdometer), AncestorOdometer Din.1.1 Cn.1.1 U A f a ∧ AncestorOdometer Din.1.1
            Cn.1.1 V B k b ∧ LeftLatticeAdjacent Din U V f k ∧ z ∈ f.domain ∧ z ∈ k.domain ∧ ∀ y,
            y = z ∨ y = z + 1 ∨ y = z - 1 ∨ y = z + ⟨0, 1⟩ ∨ y = z - ⟨0, 1⟩ → y ∈ f.domain ∨ y ∈
            k.domain)))))) ) := by
  classical
  intro layout qn Cn Din j hqn hCn hDin hreg hlargeN A B a b s t hA hB hsa htb hc hs z hza hzb hzs
  rcases hreg with ⟨P, hP, heq⟩ | ⟨K, hK, heq⟩ | ⟨cfg⟩
  · apply FordOpposingBoundaryStarLocalization P (by simpa [← heq] using hqn)
      Cn Din j (by simpa [← heq] using hCn) (by simpa [← heq] using hDin)
      A B a b hA hB hlargeN s t hsa htb
      (by simpa [← heq] using hc) (by simpa [← heq] using hs) z hza hzb hzs
  · exact DiamondOpposingBoundaryStarLocalization K (by simpa [← heq] using hqn)
      Cn Din j (by simpa [← heq] using hCn) (by simpa [← heq] using hDin)
      A B a b hA hB hlargeN s t hsa htb
      (by simpa [← heq] using hc) (by simpa [← heq] using hs) z hza hzb hzs
  · obtain ⟨cfg⟩ := cfg
    have hproto : BandPrototile (qn 0) A := by
      simpa only [hCn] using TileOdometerBandPrototile Cn.1.1 A a hA
    obtain ⟨⟨cert⟩, hsym⟩ := layout qn cfg Cn hCn A hproto
    obtain ⟨o, base, Rm, Rp, tiles, reverseTiles, fs, ks, hm, hp, path,
        U, V, f, k, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        ha, hb, hadj, hz, hz', hcover, _⟩ :=
      OpposingBoundaryStarLocalization qn cfg Cn Din j hCn hDin
        A B a b cert hsym hA hB hlargeN s t hsa htb hc hs z hza hzb hzs
    exact ⟨U, V, f, k, ha, hb, hadj, hz, hz', hcover⟩

end LeftCompatibilityGeometry

theorem LeftAdjacentOdometerCompatibility
    (C : BandCircle) (T T' : ProtoTile) (h h' : PartialOdometer)
    (hadj : LeftLatticeAdjacent C T T' h h') :
    OdometerCompatibility h h' ∧
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (i : Fin 3), ∀ (e : Bool), ∀
        (Cᵢ : BandCircle), q 0 = C.1.1 → q i.succ = Cᵢ.1.1 → 1 < Cᵢ.1.1.1 →
      TileCentroid T' - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) →
      ∀ x, x ∈ h.domain → x ∈ h'.domain →
        (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ h.domain ∨ y ∈ h'.domain) →
        ∃ (U U' : ProtoTile) (g g' : PartialOdometer),
          AncestorOdometer Cᵢ.1.1 C.1.1 U T g h ∧
          AncestorOdometer Cᵢ.1.1 C.1.1 U' T' g' h' ∧
          LeftLatticeAdjacent Cᵢ U U' g g' ∧
          x ∈ g.domain ∧ x ∈ g'.domain ∧
          ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
              y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
            y ∈ g.domain ∨ y ∈ g'.domain) := by
-- BODY
  classical
  have adjacency_symm := LeftCompatibilityGeometry.adjacency_symm
  have adjacency_action := LeftCompatibilityGeometry.adjacency_action
  have membership_action (g : BandPackingSymmetry) (a : PartialOdometer)
      (x : GaussianInt) :
      BandPackingSymmetryVectorAction g x ∈
          (BandPackingSymmetryPartialOdometerAction g a).domain ↔ x ∈ a.domain :=
              LeftCompatibilityGeometry.membership_action g a x
  have star_action (g : BandPackingSymmetry) (a b : PartialOdometer)
      (x : GaussianInt)
      (hs : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ a.domain ∨ y ∈ b.domain) :
      ∀ y, y = BandPackingSymmetryVectorAction g x ∨
          y = BandPackingSymmetryVectorAction g x + 1 ∨
          y = BandPackingSymmetryVectorAction g x - 1 ∨
          y = BandPackingSymmetryVectorAction g x + ⟨0, 1⟩ ∨
          y = BandPackingSymmetryVectorAction g x - ⟨0, 1⟩ →
        y ∈ (BandPackingSymmetryPartialOdometerAction g a).domain ∨
          y ∈ (BandPackingSymmetryPartialOdometerAction g b).domain :=
              LeftCompatibilityGeometry.star_action membership_action g a b x hs
  have layout := LeftCompatibilityGeometry.layout
  refine ⟨(LeftCompatibilityGeometry.compatibility (LeftCompatibilityGeometry.compatibility_symm)
      layout (LeftCompatibilityGeometry.make_adj)) C.1.1.1.toNat C T T' h h' rfl hadj, ?_⟩
  intro q hq i e Ci hC hCi hlarge hcent x hx hx' hstar
  -- The moreover presentation is independent of the presentation inside hadj.
  obtain ⟨p, r, hp, hr, h0, h1⟩ := P4261T2AdjacentMatrixSlope C T T' h h' hadj
  have hin := CircleMatrixIncomingVector C q hq.1 hC i
  have hin0 := congrFun hin 0
  have hin1 := congrFun hin 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hin0 hin1
  have hc0 := congrArg Prod.fst hcent
  have hc1 := congrArg Prod.snd hcent
  change (TileCentroid T').1 - (TileCentroid T).1 =
    (if e = true then (1 : Real) else -1) *
      ((BandVectors.1 (q i.succ) (q 0)).re : Real) at hc0
  change (TileCentroid T').2 - (TileCentroid T).2 =
    (if e = true then (1 : Real) else -1) *
      ((BandVectors.1 (q i.succ) (q 0)).im : Real) at hc1
  have hslope := LeftCompatibilityGeometry.hslope C T T' q i e p r h0 h1 hin0 hin1 hc0 hc1
  obtain ⟨g, qn, Cn, Din, j, en, pn, rn, hqn, hCn, hDin, hCact, hDiact,
      hCcurv, hDicurv, hTn, hTn', hpn, hrn, hcn, hsn, hreg⟩ :=
    P4261T2PairNormalization q hq C Ci i e hC hCi T T' h h' hadj.1 hadj.2.1
      p r hp hr hcent hslope
  have hlargeN : 1 < Din.1.1.1 := by omega
  have positive_star := LeftCompatibilityGeometry.positive_star layout qn Cn Din j hqn hCn hDin
      hreg hlargeN
  have hxn := (membership_action g h x).mpr hx
  have hxn' := (membership_action g h' x).mpr hx'
  have hstarn := star_action g h h' x hstar
  obtain ⟨U, V, f, k, ha, hb, hinner, hxf, hxk, hcover⟩ :
      ∃ (U V : ProtoTile) (f k : PartialOdometer),
        AncestorOdometer Din.1.1 Cn.1.1 U (BandPackingSymmetryTileAction g T)
          f (BandPackingSymmetryPartialOdometerAction g h) ∧
        AncestorOdometer Din.1.1 Cn.1.1 V (BandPackingSymmetryTileAction g T')
          k (BandPackingSymmetryPartialOdometerAction g h') ∧
        LeftLatticeAdjacent Din U V f k ∧
        BandPackingSymmetryVectorAction g x ∈ f.domain ∧
        BandPackingSymmetryVectorAction g x ∈ k.domain ∧
        ∀ y, y = BandPackingSymmetryVectorAction g x ∨
            y = BandPackingSymmetryVectorAction g x + 1 ∨
            y = BandPackingSymmetryVectorAction g x - 1 ∨
            y = BandPackingSymmetryVectorAction g x + ⟨0, 1⟩ ∨
            y = BandPackingSymmetryVectorAction g x - ⟨0, 1⟩ →
          y ∈ f.domain ∨ y ∈ k.domain := by
    cases en with
    | true =>
        exact positive_star _ _ _ _ pn rn hTn hTn' hpn hrn
          (by simpa using hcn) (by simpa using hsn) _ hxn hxn' hstarn
    | false =>
        obtain ⟨V, U, k, f, hb, ha, hadj', hxk, hxf, hcov⟩ :=
          positive_star _ _ _ _ rn pn hTn' hTn hrn hpn
            (by simpa using congrArg Neg.neg hcn)
            (by simpa using congrArg Neg.neg hsn) _ hxn' hxn
            (by intro y hy; exact (hstarn y hy).symm)
        exact ⟨U, V, f, k, ha, hb, adjacency_symm Din V U k f hlargeN hadj',
          hxf, hxk, by intro y hy; exact (hcov y hy).symm⟩
  obtain ⟨inverse, hcircle, _, _, _, htile, _, hvector, _, hfunction, _, _⟩ :=
    BandPackingSymmetryInversePhaseCancellation.2 g
  have hCcancel : BandPackingSymmetryCircleAction inverse Cn.1.1 = C.1.1 := by
    rw [hCact, hcircle]
  have hDicancel : BandPackingSymmetryCircleAction inverse Din.1.1 = Ci.1.1 := by
    rw [hDiact, hcircle]
  refine ⟨BandPackingSymmetryTileAction inverse U, BandPackingSymmetryTileAction inverse V,
    BandPackingSymmetryPartialOdometerAction inverse f,
    BandPackingSymmetryPartialOdometerAction inverse k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ht := P4261T2AncestorSymmetry inverse Din.1.1 Cn.1.1 U
      (BandPackingSymmetryTileAction g T) f (BandPackingSymmetryPartialOdometerAction g h) ha
    simpa only [hCcancel, hDicancel, htile, hfunction] using ht
  · have ht := P4261T2AncestorSymmetry inverse Din.1.1 Cn.1.1 V
      (BandPackingSymmetryTileAction g T') k (BandPackingSymmetryPartialOdometerAction g h') hb
    simpa only [hCcancel, hDicancel, htile, hfunction] using ht
  · exact adjacency_action inverse Din Ci hDicancel.symm hlargeN U V f k hinner
  · simpa only [hvector] using (membership_action inverse f _).mpr hxf
  · simpa only [hvector] using (membership_action inverse k _).mpr hxk
  · simpa only [hvector] using star_action inverse f k _ hcover

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototileExists
public import LeanPool.ApollonianSuperharmonic.P4250T1ParentSlopePhase
public import LeanPool.ApollonianSuperharmonic.P4250T1IntegralAffinePlacement
public import LeanPool.ApollonianSuperharmonic.P4250T1OrdinaryCompatibility
public import LeanPool.ApollonianSuperharmonic.P4250T1NestedCompatibility
public import LeanPool.ApollonianSuperharmonic.P4250T1ReflectedGluingSlope

-- [TABLET NODE: TileOdometerExists]

/-!
# TileOdometerExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TileOdometerExistenceGeometry

private theorem hcurv :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (q' 0 = BandPackingSymmetryCircleAction g C.1.1) → ((q' 0).1 = C.1.1.1) ) := by
  classical
  intro C q r g q' hq'0
  rw [hq'0]
  exact (BandPackingSymmetryCovariance g).1 _

private theorem restore :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (q' 0 = BandPackingSymmetryCircleAction g C.1.1) → (∀ (inverse : BandPackingSymmetry), (∀
            (C : CircleCoordinates), BandPackingSymmetryCircleAction inverse
            (BandPackingSymmetryCircleAction g C) = C) → (∀ (U : ProtoTile), ∀ (k :
            PartialOdometer), (TileOdometer (q' 0) U k) → (∃ (T : ProtoTile) (h :
            PartialOdometer), BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h))) ) := by
  classical
  intro C q r g q' hq'0 inverse hinverse U k hk
  have ho := (BandPackingSymmetryTileOdometerCovariance
    inverse (q' 0) U k hk).1
  rw [hq'0, hinverse] at ho
  exact ⟨_, _, TileOdometerBandPrototile _ _ _ ho, ho⟩

private theorem hpositive :
    (by
      classical
      exact
        (BandCircle) → ((ℕ) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g
            : BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (BandOrderedGeneralConfiguration q') → (∀ (i : Fin 3), 0 < (q' i.succ).1))) ) := by
  classical
  intro C n q r g q' cfg i
  have hnonneg := (ProperBandCurvatureStructure q' cfg.proper).2.1 i
  have hnonzero := cfg.noLine i.succ
  omega

private theorem smallT1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (p : Fin 4 → CircleCoordinates), ∀ (V : ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile),
            ProperBandQuadruple p → BandPrototile (p 0) V → (∀ i, ∀ s, BandSubtileOccurrence p V
            i s (S i s)) → (∀ x, x ∈ V.cells ↔ ∃ i s, x ∈ (S i s).cells) → Int.toNat (p 0).1 <
            Int.toNat (q' 0).1 → LatticeTile V ∧ TileArea V = Int.toNat (p 0).1 ∧ ∀ i, ∀ s,
            LatticeTile (TileCellComplement V (S i s)) ∧ TileTouching (TileCellComplement V (S i
            s)) (S i s) ) := by
  classical
  intro q r g q' p V S hp hV hS hcover _
  have facts := BandTileSimultaneousInduction p hp V hV
  exact ⟨facts.1, facts.2.1, facts.2.2.1 S hS hcover⟩

private theorem smallT2 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (D : CircleCoordinates), ∀ (V : ProtoTile), BandPrototile D V → Int.toNat D.1 <
            Int.toNat (q' 0).1 → QuarterTurnSymmetric V ) := by
  classical
  intro q r g q' D V hV _
  cases hV with
  | line w x hw =>
      simp [QuarterTurnSymmetric, TileRealization]
  | unit z x anchor =>
      intro p
      norm_num [TileRealization, TileCentroid, ClosedSquareRealization]
      constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩
      all_goals constructor <;> constructor <;> linarith
  | decompose hp hS hcells hfoot hcentroid =>
      exact (BandTileSimultaneousInduction _ hp _
        (.decompose hp hS hcells hfoot hcentroid)).2.2.2.1

private theorem parents :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (n : ℕ), (∀ m < n, ∀ (C : BandCircle), C.1.1.1.toNat = m → ∃ (T :
            ProtoTile) (h : PartialOdometer), BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h) →
            ((C.1.1.1.toNat = n) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)),
                ∀ (g : BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ((q' 0).1 = C.1.1.1) → ((BandOrderedGeneralConfiguration q') → ((∀ (i : Fin 3), 0 < (q'
            i.succ).1) → (∀ i : Fin 3, ∃ U k, BandPrototile (q' i.succ) U ∧ TileOdometer (q'
            i.succ) U k)))))) := by
  classical
  intro C n ih hn q r g q' hcurv cfg hpositive i
  let D : Fin 3 → BandCircle := fun i =>
    ⟨⟨q' i.succ, Or.inl (hpositive i),
      q', cfg.proper.1, i.succ, rfl⟩, hpositive i⟩
  apply ih (q' i.succ).1.toNat ?_ (D i) rfl
  rw [← hn, ← hcurv]
  exact (Int.toNat_lt_toNat (by simpa [hcurv] using C.2)).2
    (cfg.proper.2 i)

private theorem placements :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (hcurv : (q' 0).1 = C.1.1.1), ∀ (cfg : BandOrderedGeneralConfiguration q'), ∀
            (hpositive : ∀ (i : Fin 3), 0 < (q' i.succ).1),
        let C' : BandCircle :=
          ⟨⟨q' 0, Or.inl (by simpa [hcurv] using C.2),
            q', cfg.proper.1, 0, rfl⟩, by simpa [hcurv] using C.2⟩
        ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q' cfg C' T), ∀ (U : Fin
            (3 : ℕ) → ProtoTile), ∀ (k : Fin (3 : ℕ) → PartialOdometer), (∀ (i : Fin (3 : ℕ)),
            TileOdometer (q' i.succ) (U i) (k i)) → (∀ (p : Fin (3 : ℕ) → ℝ × ℝ), (∀ (i : Fin (3
            : ℕ)), PartialOdometerSlope (k i) = some (p i)) → (∀ (s0 : ℝ × ℝ), ∀ (z : Fin (3 : ℕ)
            → GaussianInt),
        let w : Fin 3 → GaussianInt := fun i =>
          BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ))
        (∀ (i : Fin (3 : ℕ)), p i = s0 + P4250T1SlopeOffset (w i) + GaussianRealPoint (z i)) →
            (∀ (i : Fin 3), ∀ (s : Bool), ∃ h, TileOdometer (q' i.succ) (cert.P i s) h ∧
            PartialOdometerSlope h = some (s0 + (if s = true then (1 : Real) else -1) •
            P4250T1SlopeOffset (w i))))) ) := by
  classical
  intro C q r g q' hcurv cfg hpositive C' T cert U k hk p hp s0 z w hphase i s
  let ai : GaussianInt := if s = true then -z i
    else -z i - (w i + GaussianQuarterTurn (w i))
  obtain ⟨h, ho, hs⟩ := P4250T1IntegralAffinePlacement
    (q' i.succ) (U i) (cert.P i s) (k i) (p i) ai
    (hpositive i) (hk i) (cert.outer_occurrence i s).1 (hp i)
  refine ⟨h, ho, ?_⟩
  rw [hs]
  congr 1
  have hr := congrArg Prod.fst (hphase i)
  have hi := congrArg Prod.snd (hphase i)
  cases s <;> apply Prod.ext
  all_goals
    simp [ai, P4250T1SlopeOffset, GaussianRealPoint,
      GaussianQuarterTurn] at hr hi ⊢
    linarith

private theorem compat_symm :
    (by
      classical
      exact
        (BandCircle) → ((ℕ) → ((Fin (4 : ℕ) → CircleCoordinates) → ((Fin (3 : ℕ)) →
            ((BandPackingSymmetry) → (∀ (h : PartialOdometer), ∀ (k : PartialOdometer),
            (OdometerCompatibility h k) → (OdometerCompatibility k h)))))) ) := by
  classical
  intro C n q r g h k hc
  rcases hc with hd | ⟨c, hc⟩
  · exact Or.inl hd.symm
  · refine Or.inr ⟨-c, ?_⟩
    intro x hx hy
    have he := hc x hy hx
    omega

private theorem hcompat :
    (by
      classical
      exact
        ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j :
            Fin (3 : ℕ)), ∀ (t : Bool), ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ)) ∧ s ≠ t ∨
            (i = (0 : Fin (3 : ℕ)) ∧ j = (1 : Fin (3 : ℕ)) ∨ i = (1 : Fin (3 : ℕ)) ∧ j = (0 : Fin
            (3 : ℕ))) ∧ s = t) → OdometerCompatibility (hs i s) (hs j t)) →
            ((OdometerCompatibility (hs (0 : Fin (3 : ℕ)) true) (hs (1 : Fin (3 : ℕ)) true) ∧
            OdometerCompatibility (hs (0 : Fin (3 : ℕ)) false) (hs (1 : Fin (3 : ℕ)) false) ∧
            OdometerCompatibility (hs (0 : Fin (3 : ℕ)) true) (hs (0 : Fin (3 : ℕ)) false)) → ((∀
            (h : PartialOdometer), ∀ (k : PartialOdometer), (OdometerCompatibility h k) →
            (OdometerCompatibility k h)) → (∀ i, ∀ s, ∀ j, ∀ t, OdometerCompatibility (hs i s)
            (hs j t)))) ) := by
  classical
  intro hs hord hnest compat_symm i s j t
  fin_cases i <;> fin_cases j <;> cases s <;> cases t
  all_goals first
    | exact hord _ _ _ _ (by decide)
    | exact hnest.1
    | exact hnest.2.1
    | exact hnest.2.2
    | exact compat_symm _ _ hnest.1
    | exact compat_symm _ _ hnest.2.1
    | exact compat_symm _ _ hnest.2.2

private theorem hTne :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (hcurv : (q' 0).1 = C.1.1.1), ∀ (cfg : BandOrderedGeneralConfiguration q'),
        let C' : BandCircle :=
          ⟨⟨q' 0, Or.inl (by simpa [hcurv] using C.2),
            q', cfg.proper.1, 0, rfl⟩, by simpa [hcurv] using C.2⟩
        ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q' cfg C' T), (∀ (i :
            Fin 3), ∀ (s : Bool), (cert.P i s).cells.Nonempty) → (T.cells.Nonempty) ) := by
  classical
  intro C q r g q' hcurv cfg C' T cert hPne
  obtain ⟨x, hx⟩ := hPne 0 true
  exact ⟨x, (cert.outer_union x).2 ⟨0, true, hx⟩⟩

private theorem hcover :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (hcurv : (q' 0).1 = C.1.1.1), ∀ (cfg : BandOrderedGeneralConfiguration q'),
        let C' : BandCircle :=
          ⟨⟨q' 0, Or.inl (by simpa [hcurv] using C.2),
            q', cfg.proper.1, 0, rfl⟩, by simpa [hcurv] using C.2⟩
        ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q' cfg C' T), ∀ (hs :
            Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (s : Bool), ((hs i s).domain
            : Set GaussianInt) = FootprintVertices (cert.P i s)) → ((∀ (i : Fin 3), ∀ (s : Bool),
            (cert.P i s).cells.Nonempty) → ((T.cells.Nonempty) → (∀ x, x ∈ FootprintVertices T ↔
            ∃ i s, x ∈ (hs i s).domain))) ) := by
  classical
  intro C q r g q' hcurv cfg C' T cert hs hdomain hPne hTne x
  constructor
  · intro hx
    rw [FootprintVertices, ite_eq_left hTne] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨i, s, hi⟩ := (cert.outer_union y).1 hy
    refine ⟨i, s, ?_⟩
    change x ∈ ((hs i s).domain : Set GaussianInt)
    rw [hdomain, FootprintVertices, ite_eq_left (hPne i s)]
    exact ⟨y, hi, hxy⟩
  · rintro ⟨i, s, hx⟩
    apply (cert.outer_occurrence i s).2.1
    rw [← hdomain]
    exact hx

private theorem h0compat' :
    (by
      classical
      exact
        ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer),
        let e : Fin 6 ≃ Fin 3 × Bool := (Fintype.equivFin (Fin 3 × Bool)).symm
        ∀ (h0 : PartialOdometer), (∀ (i : Fin (6 : ℕ)), OdometerCompatibility h0 (hs ((e : Fin (6
            : ℕ) → Fin (3 : ℕ) × Bool) i).1 ((e : Fin (6 : ℕ) → Fin (3 : ℕ) × Bool) i).2)) → (∀
            i, ∀ s, OdometerCompatibility h0 (hs i s)) ) := by
  classical
  intro hs e h0 h0compat i s
  simpa using h0compat (e.symm (i, s))

private theorem offsets :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (hcurv : (q' 0).1 = C.1.1.1), ∀ (cfg : BandOrderedGeneralConfiguration q'),
        let C' : BandCircle :=
          ⟨⟨q' 0, Or.inl (by simpa [hcurv] using C.2),
            q', cfg.proper.1, 0, rfl⟩, by simpa [hcurv] using C.2⟩
        ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q' cfg C' T), ∀ (hs :
            Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (s : Bool), ((hs i s).domain
            : Set GaussianInt) = FootprintVertices (cert.P i s)) → ((∀ (i : Fin 3), ∀ (s : Bool),
            (cert.P i s).cells.Nonempty) → ((∀ x, x ∈ FootprintVertices T ↔ ∃ i s, x ∈ (hs i
            s).domain) → (∀ (h0 : PartialOdometer), ((↑h0.domain : Set GaussianInt) =
            FootprintVertices T) → ((∀ i, ∀ s, OdometerCompatibility h0 (hs i s)) → (∀ i, ∀ s, ∃
            c : Int, ∀ x, x ∈ (hs i s).domain → (hs i s).value x - h0.value x = c))))) ) := by
  classical
  intro C q r g q' hcurv cfg C' T cert hs hdomain hPne hcover h0 h0dom h0compat' i s
  have hne : (hs i s).domain.Nonempty := by
    obtain ⟨x, hx⟩ := hPne i s
    refine ⟨x, ?_⟩
    change x ∈ ((hs i s).domain : Set GaussianInt)
    rw [hdomain, FootprintVertices, ite_eq_left (hPne i s)]
    exact ⟨x, hx, Or.inl rfl⟩
  rcases h0compat' i s with hd | ⟨c, hc⟩
  · obtain ⟨x, hx⟩ := hne
    have hx0 : x ∈ h0.domain := by
      change x ∈ (h0.domain : Set GaussianInt)
      rw [h0dom]
      exact (hcover x).2 ⟨i, s, hx⟩
    exact (Set.disjoint_left.mp hd hx0 hx).elim
  · refine ⟨c, ?_⟩
    intro x hx
    apply hc x _ hx
    change x ∈ (h0.domain : Set GaussianInt)
    rw [h0dom]
    exact (hcover x).2 ⟨i, s, hx⟩

private theorem hndom :
    (by
      classical
      exact
        ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (c : Fin (3 : ℕ) → Bool → ℤ),
        let hn : Fin 3 → Bool → PartialOdometer := fun i s =>
          PartialOdometerAffineTranslate (hs i s) 0 0 (-c i s)
        ∀ (i : Fin 3), ∀ (s : Bool), ∀ (x : GaussianInt), x ∈ (hn i s).domain ↔ x ∈ (hs i
            s).domain ) := by
  classical
  intro hs c hn i s x
  simpa [hn] using
    (PartialOdometerAffineTranslateFormulas (hs i s) 0 0 (-c i s)).2.1 x

private theorem hnvalue :
    (by
      classical
      exact
        (BandCircle) → ((ℕ) → (∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (c : Fin (3 : ℕ)
            → Bool → ℤ),
        let hn : Fin 3 → Bool → PartialOdometer := fun i s =>
          PartialOdometerAffineTranslate (hs i s) 0 0 (-c i s)
        ∀ (h0 : PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (hs i s).domain, (hs
            i s).value x - h0.value x = c i s) → ((Fin (4 : ℕ) → CircleCoordinates) → ((Fin (3 :
            ℕ)) → ((BandPackingSymmetry) → ((∀ (i : Fin 3), ∀ (s : Bool), ∀ (x : GaussianInt), x
            ∈ (hn i s).domain ↔ x ∈ (hs i s).domain) → (∀ (i : Fin 3), ∀ (s : Bool), ∀ (x :
            GaussianInt), (x ∈ (hn i s).domain) → (h0.value x = (hn i s).value x)))))))) ) := by
  classical
  intro C n hs c hn h0 hc q r g hndom i s x hx
  have hv := (PartialOdometerAffineTranslateFormulas
    (hs i s) 0 0 (-c i s)).2.2.1 x hx
  have he := hc i s x ((hndom i s x).1 hx)
  simp only [sub_zero, Int.reduceNeg, Zsqrtd.re_zero, zero_mul, add_zero, Zsqrtd.im_zero]
      at hv
  change (hn i s).value x = (hs i s).value x + -c i s at hv
  omega

private theorem hnsub :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (c : Fin (3 : ℕ) →
            Bool → ℤ),
        let hn : Fin 3 → Bool → PartialOdometer := fun i s =>
          PartialOdometerAffineTranslate (hs i s) 0 0 (-c i s)
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (hcurv : (q' 0).1 = C.1.1.1), ∀ (cfg : BandOrderedGeneralConfiguration q'), (∀ (i : Fin
            3), 0 < (q' i.succ).1) → (
        let C' : BandCircle :=
          ⟨⟨q' 0, Or.inl (by simpa [hcurv] using C.2),
            q', cfg.proper.1, 0, rfl⟩, by simpa [hcurv] using C.2⟩
        ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q' cfg C' T), (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q' i.succ) (cert.P i s) (hs i s)) → (∀ (i :
            Fin 3), ∀ (s : Bool), TileOdometer (q' i.succ) (cert.P i s) (hn i s)))) := by
  classical
  intro C hs c hn q r g q' hcurv cfg hpositive C' T cert hsub i s
  apply PositiveCurvatureTileOdometerSupportTransport _
    (TileTranslation (cert.P i s) 0) _ _ (hpositive i)
    (TileOdometerAffineTranslation _ _ _ 0 0 (-c i s) (hsub i s))
    (cert.outer_occurrence i s).1
  have hzero : GaussianTranslation 0 = id := by
    funext x
    simp [GaussianTranslation]
  simp [TileTranslation, hzero]

private theorem hnslope :
    (by
      classical
      exact
        ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (c : Fin (3 : ℕ) → Bool → ℤ),
        let hn : Fin 3 → Bool → PartialOdometer := fun i s =>
          PartialOdometerAffineTranslate (hs i s) 0 0 (-c i s)
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (s0 : ℝ × ℝ),
        let w : Fin 3 → GaussianInt := fun i =>
          BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ))
        (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), PartialOdometerSlope (hs i s) = some (s0 + (if s =
            true then (1 : ℝ) else (-1 : ℝ)) • P4250T1SlopeOffset (w i))) → (∀ (i : Fin 3), ∀
            (s : Bool), PartialOdometerSlope (hn i s) = some (s0 + (if s = true then (1 : Real)
            else -1) • P4250T1SlopeOffset (w i))) ) := by
  classical
  intro hs c hn q r g q' s0 w hslope i s
  change PartialOdometerSlope
    (PartialOdometerAffineTranslate (hs i s) 0 0 (-c i s)) = _
  rw [(PartialOdometerAffineTranslateFormulas
    (hs i s) 0 0 (-c i s)).2.2.2.2.2, hslope]
  simp only [Option.map_some,
    show (0 : GaussianInt).re = 0 from rfl,
    show (0 : GaussianInt).im = 0 from rfl,
    Int.cast_zero, add_zero]

end TileOdometerExistenceGeometry

theorem TileOdometerExists (C : BandCircle) :
    ∃ (T : ProtoTile) (h : PartialOdometer),
      BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h := by
-- BODY
  classical
  have existence : ∀ n : Nat, ∀ C : BandCircle, C.1.1.1.toNat = n →
      ∃ (T : ProtoTile) (h : PartialOdometer),
        BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C hn
      by_cases hc : C.1.1.1 = 1
      · obtain ⟨z, hz⟩ := CurvatureOneBandCircleClassification C hc
        let T : ProtoTile := ⟨{0}, 0⟩
        let h := CurvatureOneOdometer z
        refine ⟨T, h, ?_, ?_⟩
        · rw [hz]
          exact BandPrototile.unit z 0 0
        · rw [hz]
          apply TileOdometer.unit z 0 T h
          · rfl
          · ext x
            simp [h, T, FootprintVertices, CurvatureOneOdometer]
          · refine ⟨0, 0, 0, ?_, ?_⟩
            · intro x
              simp [h]
            · intro x hx
              simp [h]
      · obtain hunit | ⟨q, hq, hq0, hsmall, _⟩ := BandGenealogy C
        · exact (hc hunit).elim
        have hproper : ProperBandQuadruple q :=
          ⟨hq, by simpa [hq0] using hsmall⟩
        obtain ⟨r, g, hregime⟩ := BandRegimeClassification q hproper
        let q' := BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        change Xor (∃ P : FordFareyParameter, 1 < P.q ∧
          q' = FordRecursiveQuadruple P)
          (Xor (∃ K : DiamondParameter, 1 < K.1 ∧
            q' = DiamondRecursiveQuadruple K)
            (Nonempty (BandOrderedGeneralConfiguration q'))) at hregime
        have hq'0 : q' 0 = BandPackingSymmetryCircleAction g C.1.1 := by
          simp [q', BandPackingSymmetryQuadrupleAction, hq0]
        have hcurv : (q' 0).1 = C.1.1.1 := TileOdometerExistenceGeometry.hcurv C q r g hq'0
        obtain ⟨inverse, hinverse, _⟩ :=
          BandPackingSymmetryInversePhaseCancellation.2 g
        have restore := TileOdometerExistenceGeometry.restore C q r g hq'0 inverse hinverse
        have normalized : ∃ U k, TileOdometer (q' 0) U k := by
          rcases hregime with ⟨⟨P, _, hP⟩, _⟩ | ⟨hother, _⟩
          · obtain ⟨h, ho, _⟩ := FordTileOdometerRestriction P
            refine ⟨FordTile P.q, h, ?_⟩
            simpa [hP, FordRecursiveQuadruple] using ho
          · rcases hother with ⟨⟨K, _, hK⟩, _⟩ | ⟨⟨cfg⟩, _⟩
            · obtain ⟨h, ho, _⟩ := DiamondTileOdometerRestriction K
              exact ⟨DiamondTile K.1, h, by simpa [hK] using ho⟩
            · have hpositive (i : Fin 3) := TileOdometerExistenceGeometry.hpositive C n q r g cfg i
              let C' : BandCircle :=
                ⟨⟨q' 0, Or.inl (by simpa [hcurv] using C.2),
                  q', cfg.proper.1, 0, rfl⟩, by simpa [hcurv] using C.2⟩
              obtain ⟨T, hT⟩ := BandPrototileExists C'.1
              change BandPrototile (q' 0) T at hT
              -- Discharge the smaller layout premises, including line and unit T2.
              have smallT1 := TileOdometerExistenceGeometry.smallT1 q r g
              have smallT2 := TileOdometerExistenceGeometry.smallT2 q r g
              obtain ⟨cert⟩ := BandOrderedGeneralLayout q' cfg C' rfl T hT
                smallT1 smallT2
                (by
                  intro p V U hp hV _ hlarge i hU hcent
                  exact (BandTileSimultaneousInduction p hp V hV).2.2.2.2.2.1
                    hlarge i U hU hcent)
                (by
                  intro p V U W hp hV _ i hU hW hcU hcW
                  exact (BandTileSimultaneousInduction p hp V hV).2.2.2.2.2.2.1
                    i U W hU hW hcU hcW)
              let D : Fin 3 → BandCircle := fun i =>
                ⟨⟨q' i.succ, Or.inl (hpositive i),
                  q', cfg.proper.1, i.succ, rfl⟩, hpositive i⟩
              choose U k hU hk using (TileOdometerExistenceGeometry.parents C n ih hn q r g hcurv
                  cfg hpositive)
              choose p a hp ha hnonempty using fun i =>
                P4250T1DefinedHalfIntegralSlope _ (U i) (k i) (hpositive i) (hk i)
              obtain ⟨s0, b, z, hb, hphase⟩ :=
                P4250T1ParentSlopePhase q' cfg U k p (a 0) hk hp (ha 0)
              let w : Fin 3 → GaussianInt := fun i =>
                BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ))
              change ∀ i, p i = s0 + P4250T1SlopeOffset (w i) +
                GaussianRealPoint (z i) at hphase
              choose hs hsub hslope using (TileOdometerExistenceGeometry.placements C q r g hcurv
                  cfg hpositive T cert U k hk p hp s0 z hphase)
              have hord := P4250T1OrdinaryCompatibility
                q' cfg C' T cert hs s0 hsub hslope
              have hnest := P4250T1NestedCompatibility
                q' cfg C' T cert hs s0 hsub hslope
              have hcompat := TileOdometerExistenceGeometry.hcompat hs hord hnest
                  (TileOdometerExistenceGeometry.compat_symm C n q r g)
              have hdomain (i : Fin 3) (s : Bool) :
                  ((hs i s).domain : Set GaussianInt) = FootprintVertices (cert.P i s) :=
                PositiveCurvatureTileOdometerDomain _ _ _ (hpositive i) (hsub i s)
              have hPne (i : Fin 3) (s : Bool) : (cert.P i s).cells.Nonempty :=
                (P4250T1DefinedHalfIntegralSlope _ _ _ (hpositive i) (hsub i s))
                  |>.choose_spec.choose_spec.2.2
              have hcover : ∀ x, x ∈ FootprintVertices T ↔ ∃ i s, x ∈ (hs i s).domain :=
                  TileOdometerExistenceGeometry.hcover C q r g hcurv cfg T cert hs hdomain hPne
                  (TileOdometerExistenceGeometry.hTne C q r g hcurv cfg T cert hPne)
              -- Use the finite-cover gluing theorem on these actual six functions.
              let e : Fin 6 ≃ Fin 3 × Bool := (Fintype.equivFin (Fin 3 × Bool)).symm
              obtain ⟨h0, h0dom, h0compat, h0unique⟩ := OdometerGluing.1
                (T := T) (U := fun j => cert.P (e j).1 (e j).2)
                (h := fun j => hs (e j).1 (e j).2)
                (BandTileSimultaneousInduction q' cfg.proper T hT).1
                (fun j => cert.parent_lattice (e j).1 (e j).2)
                (fun j => hdomain (e j).1 (e j).2)
                (fun j k => hcompat _ _ _ _)
                (by
                  intro x
                  constructor
                  · intro hx
                    obtain ⟨i, s, hx⟩ := (cert.outer_union x).1 hx
                    exact ⟨e.symm (i, s), by simpa using hx⟩
                  · rintro ⟨j, hx⟩
                    exact (cert.outer_union x).2 ⟨(e j).1, (e j).2, hx⟩)
                (by
                  intro x
                  constructor
                  · intro hx
                    obtain ⟨i, s, hx⟩ := (hcover x).1 hx
                    exact ⟨e.symm (i, s), by simpa using hx⟩
                  · rintro ⟨j, hx⟩
                    exact (hcover x).2 ⟨(e j).1, (e j).2, hx⟩)
              have h0compat' := TileOdometerExistenceGeometry.h0compat' hs h0 h0compat
              obtain ⟨u, a0, hu, ha0, h0slope⟩ :=
                P4250T1ReflectedGluingSlope q' cfg C' T cert hs s0 hsub hslope
                  h0 h0dom h0compat' (by
                    intro g hg hgc
                    exact h0unique g hg (fun j => hgc (e j).1 (e j).2))
              -- Normalize the six additive constants without changing their slopes.
              choose c hc using (TileOdometerExistenceGeometry.offsets C q r g hcurv cfg T cert
                  hs hdomain hPne hcover h0 h0dom h0compat')
              let hn : Fin 3 → Bool → PartialOdometer := fun i s =>
                PartialOdometerAffineTranslate (hs i s) 0 0 (-c i s)
              have hndom := TileOdometerExistenceGeometry.hndom hs c
              have hnvalue (i : Fin 3) (s : Bool) (x : GaussianInt)
                  (hx : x ∈ (hn i s).domain) : h0.value x = (hn i s).value x :=
                      TileOdometerExistenceGeometry.hnvalue C n hs c h0 hc q r g hndom i s x hx
              refine ⟨T, h0, ?_⟩
              apply TileOdometer.decompose cfg.proper hT (TileOdometerExistenceGeometry.hnsub C
                  hs c q r g hcurv cfg hpositive T cert hsub) cert.outer_union
                (fun i s => (cert.outer_occurrence i s).2.1)
                (fun i s => (cert.outer_occurrence i s).2.2)
              · intro x
                change x ∈ (h0.domain : Set GaussianInt) ↔ _
                rw [h0dom, hcover]
                exact exists_congr fun i => exists_congr fun s => (hndom i s x).symm
              · exact hnvalue
              · intro i s j t
                refine Or.inr ⟨0, ?_⟩
                intro x hx hy
                rw [← hnvalue i s x hx, ← hnvalue j t x hy]
                omega
              · intro i s
                right
                refine ⟨s0, _, h0slope, (TileOdometerExistenceGeometry.hnslope hs c q r g s0
                    hslope) i s, ?_, ?_⟩
                all_goals cases s <;> simp [P4250T1SlopeOffset] <;> ring
        obtain ⟨U, k, hk⟩ := normalized
        exact restore U k hk
  exact existence _ C rfl

end ApollonianSuperharmonic

end

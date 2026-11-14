/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.GaussianCoordinateFacts

public import LeanPool.ApollonianSuperharmonic.PartialOdometerHalfTurn
public import LeanPool.ApollonianSuperharmonic.PartialOdometerHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: TileOdometerCentralSymmetry]

/-!
# TileOdometerCentralSymmetry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CentralSymmetryGeometry

private abbrev gaussian_equal := ApollonianSuperharmonic.GaussianCoordinateFacts.equal

private theorem unit_reflection :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (r : GaussianInt), (r ∈ (CurvatureOneOdometer z).domain) → (1 +
            (⟨0, 1⟩ : GaussianInt) - r ∈ (CurvatureOneOdometer z).domain ∧ (CurvatureOneOdometer
            z).value r - (CurvatureOneOdometer z).value (1 + ⟨0, 1⟩ - r) = z.im * (r.re + r.im -
            1)) ) := by
  classical
  intro z r hr
  simp only [CurvatureOneOdometer, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    norm_num [CurvatureOneOdometer, Zsqrtd.ext_iff]

private theorem unit_domain :
    (by
      classical
      exact
        (∀ (z : GaussianInt), ∀ (r : GaussianInt), (r ∈ (CurvatureOneOdometer z).domain) → (1 +
            (⟨0, 1⟩ : GaussianInt) - r ∈ (CurvatureOneOdometer z).domain ∧ (CurvatureOneOdometer
            z).value r - (CurvatureOneOdometer z).value (1 + ⟨0, 1⟩ - r) = z.im * (r.re + r.im -
            1))) → (∀ (z : GaussianInt), ∀ (r : GaussianInt), r ∈ (CurvatureOneOdometer z).domain
            ↔ 1 + (⟨0, 1⟩ : GaussianInt) - r ∈ (CurvatureOneOdometer z).domain) ) := by
  classical
  intro unit_reflection z r
  constructor
  · intro hr
    exact (unit_reflection z r hr).1
  · intro hr
    have hr' := (unit_reflection z (1 + ⟨0, 1⟩ - r) hr).1
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hr'

private theorem hdom' :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (x : GaussianInt), (h.domain = {x}) →
            ((PartialOdometerHalfTurn h).domain = {-x}) ) := by
  classical
  intro h x hdom
  ext y
  rw [(PartialOdometerHalfTurnFormulas h).1, hdom]
  simp only [Finset.mem_singleton]
  constructor <;> intro hy
  · simpa using congrArg Neg.neg hy
  · simpa using congrArg Neg.neg hy

private theorem hy'At170 :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), (y - (-2 : GaussianInt) * x = x) → (y = -x) )
            := by
  classical
  intro x y hy
  have he : y + x + x = x := by
    simpa [sub_eq_add_neg, two_mul, add_assoc] using hy
  have := congrArg (fun t : GaussianInt => t - x - x) he
  simpa [sub_eq_add_neg, add_assoc] using this

private theorem hy'At178 :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (x : GaussianInt), (h.domain = {x}) → (∀ (y : GaussianInt), (y
            ∈ (PartialOdometerHalfTurn h).domain) → (y = -x)) ) := by
  classical
  intro h x hdom y hy
  have hx := ((PartialOdometerHalfTurnFormulas h).1 y).mp hy
  have hx' : -y = x := by simpa [hdom] using hx
  simpa using congrArg Neg.neg hx'

private theorem reflected_translation :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), (∀ (z : GaussianInt), ∀ (r : GaussianInt), (r ∈
            (CurvatureOneOdometer z).domain) → (1 + (⟨0, 1⟩ : GaussianInt) - r ∈
            (CurvatureOneOdometer z).domain ∧ (CurvatureOneOdometer z).value r -
            (CurvatureOneOdometer z).value (1 + ⟨0, 1⟩ - r) = z.im * (r.re + r.im - 1))) → ((∀ (z
            : GaussianInt), ∀ (r : GaussianInt), r ∈ (CurvatureOneOdometer z).domain ↔ 1 + (⟨0,
            1⟩ : GaussianInt) - r ∈ (CurvatureOneOdometer z).domain) → (∀ (z : GaussianInt),
            (OdometerTranslation h (CurvatureOneOdometer z)) → (OdometerTranslation
            (PartialOdometerHalfTurn h) (CurvatureOneOdometer z)))) ) := by
  classical
  intro h unit_reflection unit_domain z htrans
  rcases htrans with ⟨v, a, b, hvdom, hvvalue⟩
  refine ⟨-v - 1 - ⟨0, 1⟩, ⟨-z.im - a.re, -z.im - a.im⟩,
    b - z.im * (v.re + v.im + 1), ?_, ?_⟩
  · intro y
    rw [(PartialOdometerHalfTurnFormulas h).1, hvdom,
      unit_domain z (-y - v)]
    have heq : 1 + (⟨0, 1⟩ : GaussianInt) - (-y - v) =
        y - (-v - 1 - ⟨0, 1⟩) := by abel
    rw [heq]
  · intro y hy
    have hmy := ((PartialOdometerHalfTurnFormulas h).1 y).mp hy
    have hr := (hvdom (-y)).mp hmy
    have hcalc := (unit_reflection z (-y - v) hr).2
    have heq : 1 + (⟨0, 1⟩ : GaussianInt) - (-y - v) =
        y - (-v - 1 - ⟨0, 1⟩) := by abel
    rw [heq] at hcalc
    rw [(PartialOdometerHalfTurnFormulas h).2.1 y hy, hvvalue (-y) hmy]
    dsimp at hcalc ⊢
    nlinarith

private theorem reflected_domain :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ((↑h.domain : Set GaussianInt) =
            FootprintVertices T) → (((PartialOdometerHalfTurn h).domain : Set GaussianInt) =
            FootprintVertices (TileHalfTurn T)) ) := by
  classical
  intro T h hdom
  rw [(TileHalfTurnFormulas T).2.2.2.2.2.2.1]
  ext y
  simp only [Finset.mem_coe, Set.mem_image]
  rw [(PartialOdometerHalfTurnFormulas h).1]
  constructor
  · intro hy
    refine ⟨-y, ?_, by simp⟩
    change -y ∈ (h.domain : Set GaussianInt) at hy
    rwa [hdom] at hy
  · rintro ⟨r, hr, rfl⟩
    simp only [neg_neg]
    change r ∈ (h.domain : Set GaussianInt)
    rwa [hdom]

private theorem reflectedAt226 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (z : GaussianInt), ∀ (x : GaussianInt),
            (T.cells = {x}) → ((OdometerTranslation (PartialOdometerHalfTurn h)
            (CurvatureOneOdometer z)) → ((((PartialOdometerHalfTurn h).domain : Set GaussianInt)
            = FootprintVertices (TileHalfTurn T)) → (TileOdometer (1, 1 + 2 * z) (TileHalfTurn T)
            (PartialOdometerHalfTurn h)))) ) := by
  classical
  intro T h z x hT reflected_translation reflected_domain
  apply TileOdometer.unit z (-x - 1 - ⟨0, 1⟩)
  · rw [(TileHalfTurnFormulas T).1, hT]
    simp
  · exact reflected_domain
  · exact reflected_translation

private theorem reflected_cells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (x : LatticeCell), x ∈
            T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) → (∀ x, x ∈
            (TileHalfTurn T).cells ↔ ∃ i s, x ∈ (TileHalfTurn (S i (!s))).cells) ) := by
  classical
  intro T S hcells x
  rw [(TileHalfTurnFormulas T).1]
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    rcases (hcells r).mp hr with ⟨i, s, hs⟩
    refine ⟨i, !s, ?_⟩
    simp only [Bool.not_not]
    rw [(TileHalfTurnFormulas (S i s)).1]
    exact Finset.mem_image.mpr ⟨r, hs, rfl⟩
  · rintro ⟨i, s, hx⟩
    rw [(TileHalfTurnFormulas (S i (!s))).1] at hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, (hcells r).mpr ⟨i, !s, hr⟩, rfl⟩

private theorem reflected_foot :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), FootprintVertices (S i s) ⊆ FootprintVertices T) → (∀ i, ∀ s,
            FootprintVertices (TileHalfTurn (S i (!s))) ⊆ FootprintVertices (TileHalfTurn T)) )
            := by
  classical
  intro T S hfoot i s y hy
  rw [(TileHalfTurnFormulas (S i (!s))).2.2.2.2.2.2.1] at hy
  rw [(TileHalfTurnFormulas T).2.2.2.2.2.2.1]
  rcases hy with ⟨r, hr, rfl⟩
  exact ⟨r, hfoot i (!s) hr, rfl⟩

private theorem reflected_centroid :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) - TileCentroid T
            = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let d (i : Fin 3) : Real × Real :=
          let w := GaussianRealPoint
            (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))
          (1 / 2 : Real) • (w - (-w.2, w.1))
        ∀ i, ∀ s, TileCentroid (TileHalfTurn (S i (!s))) - TileCentroid (TileHalfTurn T) = (if s
            = true then (1 : Real) else -1) • d i) ) := by
  classical
  intro T q S hcentroid d i s
  rw [(TileHalfTurnFormulas (S i (!s))).2.2.2.2.2.2.2.1,
    (TileHalfTurnFormulas T).2.2.2.2.2.2.2.1]
  have hc := hcentroid i (!s)
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  cases s <;> apply Prod.ext <;> dsimp [d] at hx hy ⊢ <;> linarith

private theorem reflectedAt278 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple q) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs : Fin (3 :
            ℕ) → Bool → PartialOdometer),
                                        ((∀ (x : GaussianInt), x ∈ h.domain ↔ ∃ (i : Fin (3 : ℕ))
            (s : Bool), x ∈ (hs i s).domain) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (hs i
            s).domain, h.value x = (hs i s).value x) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j
            : Fin (3 : ℕ)), ∀ (t : Bool), OdometerCompatibility (hs i s) (hs j t)) → ((∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), (q i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ),
            PartialOdometerSlope h = some p ∧ PartialOdometerSlope (hs i s) = some p_i ∧ p_i.1 -
            p.1 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
            ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 /
            2 : ℝ) * ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 :
            ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 :
            Fin (3 : ℕ))).succ)).re : ℝ))) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q
            i.succ) (TileHalfTurn (S i s)) (PartialOdometerHalfTurn (hs i s)) ∧
            OdometerTranslation (PartialOdometerHalfTurn (hs i s)) (hs i s)) → ((∀ x, x ∈
            (TileHalfTurn T).cells ↔ ∃ i s, x ∈ (TileHalfTurn (S i (!s))).cells) → ((∀ i, ∀ s,
            FootprintVertices (TileHalfTurn (S i (!s))) ⊆ FootprintVertices (TileHalfTurn T)) → (
        let d (i : Fin 3) : Real × Real :=
          let w := GaussianRealPoint
            (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))
          (1 / 2 : Real) • (w - (-w.2, w.1))
        (∀ i, ∀ s, TileCentroid (TileHalfTurn (S i (!s))) - TileCentroid (TileHalfTurn T) = (if s
            = true then (1 : Real) else -1) • d i) → (TileOdometer (q 0) (TileHalfTurn T)
            (PartialOdometerHalfTurn h))))))))))) ) := by
  classical
  intro T h q hq S hs hdom hvalue hcompat hslope ih reflected_cells reflected_foot d
      reflected_centroid
  apply TileOdometer.decompose (S := fun i s => TileHalfTurn (S i (!s)))
    (hs := fun i s => PartialOdometerHalfTurn (hs i (!s))) hq
  · exact BandPrototile.decompose hq
      (fun i s => TileOdometerBandPrototile _ _ _ (ih i (!s)).1)
      reflected_cells reflected_foot reflected_centroid
  · intro i s
    exact (ih i (!s)).1
  · exact reflected_cells
  · exact reflected_foot
  · exact reflected_centroid
  · intro y
    rw [(PartialOdometerHalfTurnFormulas h).1, hdom]
    constructor
    · rintro ⟨i, s, hy⟩
      refine ⟨i, !s, ?_⟩
      simp only [Bool.not_not]
      exact ((PartialOdometerHalfTurnFormulas (hs i s)).1 y).mpr hy
    · rintro ⟨i, s, hy⟩
      exact ⟨i, !s, ((PartialOdometerHalfTurnFormulas (hs i (!s))).1 y).mp hy⟩
  · intro i s y hy
    have hmy := ((PartialOdometerHalfTurnFormulas (hs i (!s))).1 y).mp hy
    have houter := ((PartialOdometerHalfTurnFormulas h).1 y).mpr
      ((hdom (-y)).mpr ⟨i, !s, hmy⟩)
    rw [(PartialOdometerHalfTurnFormulas h).2.1 y houter,
      (PartialOdometerHalfTurnFormulas (hs i (!s))).2.1 y hy]
    exact hvalue i (!s) (-y) hmy
  · intro i s j t
    rcases hcompat i (!s) j (!t) with hd | ⟨c, hc⟩
    · left
      apply Set.disjoint_left.mpr
      intro y hy hz
      exact Set.disjoint_left.mp hd
        (((PartialOdometerHalfTurnFormulas (hs i (!s))).1 y).mp hy)
        (((PartialOdometerHalfTurnFormulas (hs j (!t))).1 y).mp hz)
    · right
      refine ⟨c, ?_⟩
      intro y hy hz
      rw [(PartialOdometerHalfTurnFormulas (hs i (!s))).2.1 y hy,
        (PartialOdometerHalfTurnFormulas (hs j (!t))).2.1 y hz]
      exact hc (-y)
        (((PartialOdometerHalfTurnFormulas (hs i (!s))).1 y).mp hy)
        (((PartialOdometerHalfTurnFormulas (hs j (!t))).1 y).mp hz)
  · intro i s
    rcases hslope i (!s) with hz | ⟨p, pi, hp, hpi, hx, hy⟩
    · exact Or.inl hz
    · right
      refine ⟨(-p.1, -p.2), (-pi.1, -pi.2), ?_, ?_, ?_, ?_⟩
      · rw [(PartialOdometerHalfTurnFormulas h).2.2.2.2.2.2, hp]
        rfl
      · rw [(PartialOdometerHalfTurnFormulas (hs i (!s))).2.2.2.2.2.2, hpi]
        rfl
      · cases s <;> dsimp at hx ⊢ <;> linarith
      · cases s <;> dsimp at hy ⊢ <;> linarith

end CentralSymmetryGeometry

theorem TileOdometerCentralSymmetry
    (C : CircleCoordinates) (T : ProtoTile) (h : PartialOdometer)
    (hO : TileOdometer C T h) :
    TileOdometer C (TileHalfTurn T)
        (PartialOdometerHalfTurn h) ∧
      OdometerTranslation (PartialOdometerHalfTurn h) h := by
-- BODY
  classical
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := CentralSymmetryGeometry.gaussian_equal u v hre him
  have unit_reflection (z r : GaussianInt)
      (hr : r ∈ (CurvatureOneOdometer z).domain) :
      1 + (⟨0, 1⟩ : GaussianInt) - r ∈ (CurvatureOneOdometer z).domain ∧
      (CurvatureOneOdometer z).value r -
        (CurvatureOneOdometer z).value (1 + ⟨0, 1⟩ - r) =
        z.im * (r.re + r.im - 1) := CentralSymmetryGeometry.unit_reflection z r hr
  have unit_domain (z r : GaussianInt) :
      r ∈ (CurvatureOneOdometer z).domain ↔
        1 + (⟨0, 1⟩ : GaussianInt) - r ∈ (CurvatureOneOdometer z).domain :=
            CentralSymmetryGeometry.unit_domain unit_reflection z r
  induction hO with
  | line w x hw h hdom =>
      constructor
      · have hdom' : (PartialOdometerHalfTurn h).domain = {-x} := CentralSymmetryGeometry.hdom' h
          x hdom
        have htile : TileHalfTurn (⟨∅, x⟩ : ProtoTile) = ⟨∅, -x⟩ := by
          simp [TileHalfTurn]
        rw [htile]
        exact TileOdometer.line w (-x) hw (PartialOdometerHalfTurn h) hdom'
      · refine ⟨-2 * x, 0, 0, ?_, ?_⟩
        · intro y
          rw [(PartialOdometerHalfTurnFormulas h).1, hdom]
          simp only [Finset.mem_singleton]
          constructor
          · intro hy
            have hy' : y = -x := by simpa using congrArg Neg.neg hy
            subst y
            simp [two_mul]
          · intro hy
            have hy' : y = -x := CentralSymmetryGeometry.hy'At170 x y hy
            subst y
            simp []
        · intro y hy
          have hy' : y = -x := CentralSymmetryGeometry.hy'At178 h x hdom y hy
          subst y
          rw [(PartialOdometerHalfTurnFormulas h).2.1 (-x) hy]
          have heq : -x - -2 * x = x := by
            apply gaussian_equal <;> simp <;> ring
          rw [heq]
          simp
  | unit z x T h hT hdom htrans =>
      have reflected_translation :
          OdometerTranslation (PartialOdometerHalfTurn h) (CurvatureOneOdometer z) :=
              CentralSymmetryGeometry.reflected_translation h unit_reflection unit_domain z htrans
      have reflected_domain :
          ((PartialOdometerHalfTurn h).domain : Set GaussianInt) =
            FootprintVertices (TileHalfTurn T) := CentralSymmetryGeometry.reflected_domain T h hdom
      have reflected : TileOdometer (1, 1 + 2 * z)
          (TileHalfTurn T) (PartialOdometerHalfTurn h) := CentralSymmetryGeometry.reflectedAt226
              T h z x hT reflected_translation reflected_domain
      refine ⟨reflected, ?_⟩
      obtain ⟨v, hv, _⟩ := TileOdometerTranslationUniqueness
        (1, 1 + 2 * z) (TileHalfTurn T) T (PartialOdometerHalfTurn h) h
        (by norm_num) reflected (TileOdometer.unit z x T h hT hdom htrans)
      rcases hv.2.2 with ⟨a, b, hdomains, hvalues⟩
      exact ⟨v, a, b, hdomains, hvalues⟩
  | @decompose q hq S T hs h hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
      have reflected_cells : ∀ x, x ∈ (TileHalfTurn T).cells ↔
          ∃ i s, x ∈ (TileHalfTurn (S i (!s))).cells := CentralSymmetryGeometry.reflected_cells T
              S hcells
      have reflected_foot : ∀ i s,
          FootprintVertices (TileHalfTurn (S i (!s))) ⊆
            FootprintVertices (TileHalfTurn T) := CentralSymmetryGeometry.reflected_foot T S hfoot
      let d (i : Fin 3) : Real × Real :=
        let w := GaussianRealPoint
          (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)))
        (1 / 2 : Real) • (w - (-w.2, w.1))
      have reflected_centroid : ∀ i s,
          TileCentroid (TileHalfTurn (S i (!s))) - TileCentroid (TileHalfTurn T) =
            (if s = true then (1 : Real) else -1) • d i :=
                CentralSymmetryGeometry.reflected_centroid T q S hcentroid
      have reflected : TileOdometer (q 0)
          (TileHalfTurn T) (PartialOdometerHalfTurn h) := CentralSymmetryGeometry.reflectedAt278
              T h q hq S hs hdom hvalue hcompat hslope ih reflected_cells reflected_foot
              reflected_centroid
      refine ⟨reflected, ?_⟩
      obtain ⟨v, hv, _⟩ := TileOdometerTranslationUniqueness
        (q 0) (TileHalfTurn T) T (PartialOdometerHalfTurn h) h
        (ProperBandCurvatureStructure q hq).1 reflected
        (TileOdometer.decompose hq hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope)
      rcases hv.2.2 with ⟨a, b, hdomains, hvalues⟩
      exact ⟨v, a, b, hdomains, hvalues⟩

end ApollonianSuperharmonic

end

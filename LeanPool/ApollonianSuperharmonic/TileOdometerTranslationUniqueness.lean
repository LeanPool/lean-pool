/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty

public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.OdometerGluing
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition

-- [TABLET NODE: TileOdometerTranslationUniqueness]

/-!
# TileOdometerTranslationUniqueness

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OdometerTranslationGeometry

private theorem positive_parent :
    (by
      classical
      exact
        ∀ q, ProperBandQuadruple q → ∃ i : Fin 3, 0 < (q i.succ).1
    ) := by
  classical
  intro q hq
  have f := ProperBandCurvatureStructure q hq
  by_cases h0 : 0 < (q (0 : Fin 3).succ).1
  · exact ⟨0, h0⟩
  by_cases h1 : 0 < (q (1 : Fin 3).succ).1
  · exact ⟨1, h1⟩
  have n0 := f.2.1 0
  have n1 := f.2.1 1
  have z0 : (q (0 : Fin 3).succ).1 = 0 := by omega
  have z1 : (q (1 : Fin 3).succ).1 = 0 := by omega
  exact ((by decide : (0 : Fin 3) ≠ 1) (f.2.2 0 1 z0 z1)).elim

private theorem proper_large :
    (by
      classical
      exact
        (∀ q, ProperBandQuadruple q → ∃ i : Fin 3, 0 < (q i.succ).1) →
          ∀ q, ProperBandQuadruple q → 1 < (q 0).1
    ) := by
  classical
  intro positive_parent q hq
  obtain ⟨i, hi⟩ := positive_parent q hq
  have hb := hq.2 i
  omega

private theorem zero_cells :
    (by
      classical
      exact
        ∀ D, ∀ V, BandPrototile D V → D.1 = 0 → V.cells = ∅ ) := by
  classical
  intro D V hV hz
  cases hV with
  | line w x hw => rfl
  | unit z x anchor => simp at hz
  | decompose hq hS hc hf hcent =>
      have hp := (ProperBandCurvatureStructure _ hq).1
      rw [hz] at hp
      exact (lt_irrefl _ hp).elim

private theorem cent_eq :
    (by
      classical
      exact
        ∀ V W : ProtoTile, V.cells = W.cells → (V.cells = ∅ → V.anchor = W.anchor) → TileCentroid
            V = TileCentroid W ) := by
  classical
  intro V W hc ha
  by_cases hn : V.cells.Nonempty
  · have hm : W.cells.Nonempty := hc ▸ hn
    simp only [TileCentroid, ite_eq_left hm, hc]
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm : ¬ W.cells.Nonempty := by rwa [← hc]
    simp only [TileCentroid, ite_eq_right hn, ite_eq_right hm, ha hz]

private theorem foot_eq :
    (by
      classical
      exact
        ∀ V W : ProtoTile, V.cells = W.cells → (V.cells = ∅ → V.anchor = W.anchor) →
            FootprintVertices V = FootprintVertices W ) := by
  classical
  intro V W hc ha
  by_cases hn : V.cells.Nonempty
  · have hm : W.cells.Nonempty := hc ▸ hn
    simp only [FootprintVertices, ite_eq_left hm, hc]
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm : ¬ W.cells.Nonempty := by rwa [← hc]
    simp only [FootprintVertices, ite_eq_right hn, ite_eq_right hm, ha hz]

private theorem domains :
    (by
      classical
      exact
        (∀ V W : ProtoTile, V.cells = W.cells → (V.cells = ∅ → V.anchor = W.anchor) →
            FootprintVertices V = FootprintVertices W) → (∀ D, ∀ V, ∀ W, ∀ k, ∀ l, 0 < D.1 →
            TileOdometer D V k → TileOdometer D W l → ∀ u, V.cells = (TileTranslation W u).cells
            → (V.cells = ∅ → V.anchor = (TileTranslation W u).anchor) → ∀ x, x ∈ k.domain ↔ x-u ∈
            l.domain) ) := by
  classical
  intro foot_eq D V W k l hp hk hl u hc ha x
  have hd := PositiveCurvatureTileOdometerDomain D V k hp hk
  have he := PositiveCurvatureTileOdometerDomain D W l hp hl
  have ht := (PartialOdometerAffineTranslateFormulas l u 0 0).2.2.2.2.1 W he
  have hf := foot_eq V (TileTranslation W u) hc ha
  have hsame : (k.domain : Set GaussianInt) =
      ((PartialOdometerAffineTranslate l u 0 0).domain : Set GaussianInt) :=
    hd.trans (hf.trans ht.symm)
  rw [← (PartialOdometerAffineTranslateFormulas l u 0 0).2.1]
  exact Set.ext_iff.mp hsame x

private theorem affine_eq :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (l : PartialOdometer), ∀ (u : GaussianInt), ∀ (a :
            GaussianInt), ∀ (b : ℤ), (∀ x, x ∈ k.domain ↔ x-u ∈ l.domain) → (∀ x, x ∈ k.domain →
            k.value x = l.value (x-u) + a.re*x.re + a.im*x.im+b) → k =
            PartialOdometerAffineTranslate l u a b ) := by
  classical
  intro k l u a b hd hv
  have hh : k.domain = (PartialOdometerAffineTranslate l u a b).domain := by
    ext x
    rw [(PartialOdometerAffineTranslateFormulas l u a b).2.1]
    exact hd x
  have vv : k.value = (PartialOdometerAffineTranslate l u a b).value := by
    funext x
    by_cases hx : x ∈ k.domain
    · rw [hv x hx, (PartialOdometerAffineTranslateFormulas l u a b).2.2.1 x
        (by rwa [← hh])]
    · rw [k.value_outside x hx,
        (PartialOdometerAffineTranslate l u a b).value_outside x (by rwa [← hh])]
  cases k
  simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
  exact ⟨hh, vv⟩

private theorem unit_shift :
    (by
      classical
      exact
        ∀ (z : GaussianInt),
          ∀ (x : GaussianInt),
            ∀ (V : ProtoTile),
              ∀ (k : PartialOdometer),
                V.cells = { x } →
                  (k.domain : Set GaussianInt) = FootprintVertices V →
                    ∀ v,
                      (∀ y, y ∈ k.domain ↔ y - v ∈ (CurvatureOneOdometer z).domain) →
                        v = x
    ) := by
  classical
  intro z x V k hc hd v hv
  have h0 : v ∈ FootprintVertices V := by
    rw [← hd]
    exact (hv v).mpr (by simp [CurvatureOneOdometer])
  have h1 : v+1+(⟨0,1⟩ : GaussianInt) ∈ FootprintVertices V := by
    rw [← hd]
    apply (hv _).mpr
    rw [show v+1+(⟨0,1⟩ : GaussianInt)-v = 1+⟨0,1⟩ by abel]
    simp [CurvatureOneOdometer]
  simp only [FootprintVertices, hc,
    Finset.mem_singleton, exists_eq_left] at h0 h1
  apply Zsqrtd.ext
  · rcases h0 with h0 | h0 | h0 | h0 <;>
      rcases h1 with h1 | h1 | h1 | h1
    all_goals have a := congrArg (fun w : GaussianInt => w.re) h0
    all_goals have b := congrArg (fun w : GaussianInt => w.re) h1
    all_goals simp at a b
    all_goals omega
  · rcases h0 with h0 | h0 | h0 | h0 <;>
      rcases h1 with h1 | h1 | h1 | h1
    all_goals have a := congrArg (fun w : GaussianInt => w.im) h0
    all_goals have b := congrArg (fun w : GaussianInt => w.im) h1
    all_goals simp at a b
    all_goals omega

private theorem square_disk :
    (by
      classical
      exact
        ∀ (V : ProtoTile), ∀ (x : GaussianInt), V.cells = {x} → LatticeTile V ) := by
  classical
  intro V x hx
  let f : ℝ × ℝ → ℝ × ℝ := fun p =>
    (p.1/2+(x.re : ℝ)+1/2, p.2/2+(x.im : ℝ)+1/2)
  let g : ℝ × ℝ → ℝ × ℝ := fun p =>
    (2*(p.1-(x.re : ℝ)-1/2), 2*(p.2-(x.im : ℝ)-1/2))
  have hf : ∀ p, p ∈ Metric.closedBall (0 : ℝ × ℝ) 1 → f p ∈ TileRealization V := by
    intro p hp
    simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq,
      Prod.fst_zero, Prod.snd_zero, sub_zero, max_le_iff, abs_le] at hp
    simp [TileRealization, hx, ClosedSquareRealization, f, Prod.le_def]
    constructor <;> constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hg : ∀ p, p ∈ TileRealization V → g p ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    intro p hp
    simp only [TileRealization, hx, Finset.mem_singleton, ClosedSquareRealization,
        Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
        Set.iUnion_iUnion_eq_left, Set.mem_Icc, Prod.le_def] at hp
    rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at hp
    simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq,
      Prod.fst_zero, Prod.snd_zero, sub_zero, max_le_iff, abs_le, g]
    constructor <;> constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hgf : ∀ p, g (f p) = p := by intro p; ext <;> dsimp [f,g] <;> ring
  have hfg : ∀ p, f (g p) = p := by intro p; ext <;> dsimp [f,g] <;> ring
  refine ⟨{
    toEquiv := {
      toFun := fun p => ⟨f p, hf p p.property⟩
      invFun := fun p => ⟨g p, hg p p.property⟩
      left_inv := fun p => Subtype.ext (hgf p)
      right_inv := fun p => Subtype.ext (hfg p) }
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩
  · apply Continuous.subtype_mk
    exact (by fun_prop : Continuous f).comp continuous_subtype_val
  · apply Continuous.subtype_mk
    exact (by fun_prop : Continuous g).comp continuous_subtype_val

private theorem disk :
    (by
      classical
      exact
        (∀ (V : ProtoTile), ∀ (x : GaussianInt), V.cells = {x} → LatticeTile V) → (∀ D, ∀ V, ∀ k,
            TileOdometer D V k → 0 < D.1 → LatticeTile V) ) := by
  classical
  intro square_disk D V k hk hp
  cases hk with
  | line w x hw k hd => simp at hp
  | unit z x V k hc hd ht => exact square_disk V x hc
  | decompose hq hV hsub hc hf hcent hd hv hcompat hslope =>
      exact (BandTileSimultaneousInduction _ hq V hV).1

private theorem hzAt354 :
    (by
      classical
      exact
        ∀ (z : GaussianInt),
          ∀ (z' : GaussianInt),
            ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z') =
                ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z) →
              z = z'
    ) := by
  classical
  intro z z' he
  have hh := congrArg (fun D : CircleCoordinates => D.2) he
  apply Zsqrtd.ext
  · have hr := congrArg (fun w : GaussianInt => w.re) hh
    simp at hr
    omega
  · have hi := congrArg (fun w : GaussianInt => w.im) hh
    simp at hi
    omega

private theorem matched :
    (by
      classical
      exact
        (∀ D, ∀ V, ∀ k, TileOdometer D V k → BandPrototile D V) → (∀ (V : ProtoTile), ∀ (q : Fin
            (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs : Fin (3
            : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q
            i.succ) (S i s) (hs i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s)
            - TileCentroid V = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (W :
            ProtoTile), ∀ (u : GaussianInt), ∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (rs : Fin
            (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer
            (q i.succ) (R i s) (rs i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (R i
            s) - TileCentroid W = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) →
            ((TileCentroid V = TileCentroid (TileTranslation W u)) → (∀ i, ∀ s, (S i s).cells =
            (TileTranslation (R i s) u).cells ∧ ((S i s).cells = ∅ → (S i s).anchor =
            (TileTranslation (R i s) u).anchor))))))) ) := by
  classical
  intro proto V q S hs hsub hcentroid W u R rs rsub rcent houter i s
  have hcent : TileCentroid (S i s) = TileCentroid (TileTranslation (R i s) u) := by
    rw [(TileTranslationFormulas (R i s) u).2.2.2.2.1]
    apply Prod.ext
    · have he := congrArg Prod.fst houter
      rw [(TileTranslationFormulas W u).2.2.2.2.1] at he
      have h1 := congrArg Prod.fst (hcentroid i s)
      have h2 := congrArg Prod.fst (rcent i s)
      dsimp at he h1 h2 ⊢
      linarith
    · have he := congrArg Prod.snd houter
      rw [(TileTranslationFormulas W u).2.2.2.2.1] at he
      have h1 := congrArg Prod.snd (hcentroid i s)
      have h2 := congrArg Prod.snd (rcent i s)
      dsimp at he h1 h2 ⊢
      linarith
  exact BandPrototileCentroidUnique _ (S i s) (TileTranslation (R i s) u)
    (proto _ _ _ (hsub i s))
    (BandPrototileTranslation _ _ u (proto _ _ _ (rsub i s))) hcent

private theorem pieces :
    (by
      classical
      exact
        (∀ D, ∀ V, ∀ W, ∀ k, ∀ l, 0 < D.1 → TileOdometer D V k → TileOdometer D W l → ∀ u,
            V.cells = (TileTranslation W u).cells → (V.cells = ∅ → V.anchor = (TileTranslation W
            u).anchor) → ∀ x, x ∈ k.domain ↔ x-u ∈ l.domain) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs : Fin (3 : ℕ) →
            Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ)
            (S i s) (hs i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (0 : ℤ) < (q i.succ).1 → ∀
            (W : ProtoTile), ∀ (l : PartialOdometer), TileOdometer (q i.succ) W l → ∀ (u :
            GaussianInt), (S i s).cells = (TileTranslation W u).cells → ((S i s).cells = ∅ → (S i
            s).anchor = (TileTranslation W u).anchor) → ∃ (a : GaussianInt) (b : ℤ), ∀ x ∈ (hs i
            s).domain, (hs i s).value x = l.value (x - u) + a.re * x.re + a.im * x.im + b) → (∀
            (u : GaussianInt), ∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (rs : Fin (3 : ℕ) → Bool
            → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (R i
            s) (rs i s)) → ((∀ i, ∀ s, (S i s).cells = (TileTranslation (R i s) u).cells ∧ ((S i
            s).cells = ∅ → (S i s).anchor = (TileTranslation (R i s) u).anchor)) → (∀ i, ∀ s, 0 <
            (q i.succ).1 → ∃ a : GaussianInt, ∃ b : ℤ, (∀ x, x ∈ (hs i s).domain ↔ x-u ∈ (rs i
            s).domain) ∧ ∀ x, x ∈ (hs i s).domain → (hs i s).value x = (rs i s).value
            (x-u)+a.re*x.re+a.im*x.im+b))))) ) := by
  classical
  intro domains q S hs hsub ih u R rs rsub matched i s hi
  obtain ⟨a,b,hv⟩ := ih i s hi (R i s) (rs i s) (rsub i s) u
    (matched i s).1 (matched i s).2
  exact ⟨a,b,domains _ _ _ _ _ hi (hsub i s) (rsub i s) u
    (matched i s).1 (matched i s).2,hv⟩

private theorem coefficients :
    (by
      classical
      exact
        (∀ (k : PartialOdometer),
            ∀ (l : PartialOdometer),
              ∀ (u : GaussianInt),
                ∀ (a : GaussianInt),
                  ∀ (b : ℤ),
                    (∀ x, x ∈ k.domain ↔ x - u ∈ l.domain) →
                      (∀ x,
                          x ∈ k.domain →
                            k.value x = l.value (x - u) + a.re * x.re + a.im * x.im + b) →
                        k = PartialOdometerAffineTranslate l u a b) →
          ∀ (k : PartialOdometer),
            ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
              ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer),
                (∀ (i : Fin (3 : ℕ)),
                    ∀ (s : Bool),
                      (q i.succ).1 = (0 : ℤ) ∨
                        ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ),
                          PartialOdometerSlope k = some p ∧
                            PartialOdometerSlope (hs i s) = some p_i ∧
                              p_i.1 - p.1 =
                                (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                                ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                                ℝ) -
                                (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                                ℝ)) ∧
                                p_i.2 - p.2 =
                                (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                                ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                                ℝ) +
                                (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                                ℝ))) →
                  ∀ (l : PartialOdometer),
                    ∀ (u : GaussianInt),
                      ∀ (rs : Fin (3 : ℕ) → Bool → PartialOdometer),
                        (∀ (i : Fin (3 : ℕ)),
                            ∀ (s : Bool),
                              (q i.succ).1 = (0 : ℤ) ∨
                                ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ),
                                PartialOdometerSlope l = some p ∧
                                PartialOdometerSlope (rs i s) = some p_i ∧
                                p_i.1 - p.1 =
                                (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                                ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                                ℝ) -
                                (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                                ℝ)) ∧
                                p_i.2 - p.2 =
                                (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
                                ((↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).im :
                                ℝ) +
                                (↑(BandVectors.2 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ)).re :
                                ℝ))) →
                          ∀ (p : ℝ × ℝ),
                            PartialOdometerSlope k = some p →
                              ∀ (p' : ℝ × ℝ),
                                PartialOdometerSlope l = some p' →
                                ∀ i,
                                ∀ s,
                                0 < (q i.succ).1 →
                                ∀ (ai : GaussianInt),
                                ∀ (bi : ℤ),
                                (∀ x, x ∈ (hs i s).domain ↔ x - u ∈ (rs i s).domain) →
                                (∀ x,
                                x ∈ (hs i s).domain →
                                (hs i s).value x =
                                (rs i s).value (x - u) + ai.re * x.re + ai.im * x.im +
                                bi) →
                                (ai.re : ℝ) = p.1 - p'.1 ∧ (ai.im : ℝ) = p.2 - p'.2
    ) := by
  classical
  intro affine_eq k q hs hslope l u rs rslope p hp0 p' hp1 i s hi ai bi hd hv
  obtain ⟨pp,ii,hpp,hii,dx,dy⟩ := (hslope i s).resolve_left (by omega)
  obtain ⟨qq,jj,hqq,hjj,ex,ey⟩ := (rslope i s).resolve_left (by omega)
  have heq := affine_eq (hs i s) (rs i s) u ai bi hd hv
  have hsl : ii = (jj.1+(ai.re : ℝ), jj.2+(ai.im : ℝ)) := by
    apply Option.some.inj
    rw [← hii,heq,(PartialOdometerAffineTranslateFormulas (rs i s) u ai bi).2.2.2.2.2,hjj]
    rfl
  have hpp' : pp=p := Option.some.inj (hpp.symm.trans hp0)
  have hqq' : qq=p' := Option.some.inj (hqq.symm.trans hp1)
  subst pp
  subst qq
  have hx := congrArg Prod.fst hsl
  have hy := congrArg Prod.snd hsl
  dsimp at hx hy
  constructor <;> linarith

private theorem common :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), ∀
            (u : GaussianInt), ∀ (rs : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ i, ∀ s, 0 < (q
            i.succ).1 → ∃ a : GaussianInt, ∃ b : ℤ, (∀ x, x ∈ (hs i s).domain ↔ x-u ∈ (rs i
            s).domain) ∧ ∀ x, x ∈ (hs i s).domain → (hs i s).value x = (rs i s).value
            (x-u)+a.re*x.re+a.im*x.im+b) → (∀ (a : GaussianInt), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ),
            (∀ i, ∀ s, 0 < (q i.succ).1 → ∀ (ai : GaussianInt), ∀ (bi : ℤ), (∀ x, x ∈ (hs i
            s).domain ↔ x-u ∈ (rs i s).domain) → (∀ x, x ∈ (hs i s).domain → (hs i s).value x =
            (rs i s).value (x-u)+ai.re*x.re+ai.im*x.im+bi) → (ai.re : ℝ) = p.1-p'.1 ∧ (ai.im : ℝ)
            = p.2-p'.2) → (((↑a.re : ℝ) = p.1 - p'.1 ∧ (↑a.im : ℝ) = p.2 - p'.2) → (∀ i, ∀ s, 0 <
            (q i.succ).1 → ∃ b : ℤ, (∀ x, x ∈ (hs i s).domain ↔ x-u ∈ (rs i s).domain) ∧ ∀ x, x ∈
            (hs i s).domain → (hs i s).value x = (rs i s).value (x-u)+a.re*x.re+a.im*x.im+b))) )
            := by
  classical
  intro q hs u rs pieces a p p' coefficients ca i s hi
  obtain ⟨ai,bi,hd,hv⟩ := pieces i s hi
  have ci := coefficients i s hi ai bi hd hv
  have eq : ai=a := by
    apply Zsqrtd.ext
    · exact_mod_cast ci.1.trans ca.1.symm
    · exact_mod_cast ci.2.trans ca.2.symm
  subst ai
  exact ⟨bi,hd,hv⟩

private theorem chosen_positive :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), ((0 : ℤ) < (q j.succ).1) → (
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        ∀ t, 0 < (q (chooseSlot t).1.succ).1) ) := by
  classical
  intro q j hj chooseSlot t
  dsimp [chooseSlot]
  split_ifs with ht
  · exact ht
  · exact hj

private theorem parent_positive :
    (by
      classical
      exact
        (∀ D, ∀ V, ∀ k, TileOdometer D V k → BandPrototile D V) →
          (∀ D, ∀ V, BandPrototile D V → D.1 = 0 → V.cells = ∅) →
            ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
              ProperBandQuadruple q →
                ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
                  ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer),
                    (∀ (i : Fin (3 : ℕ)),
                        ∀ (s : Bool), TileOdometer (q i.succ) (S i s) (hs i s)) →
                      ∀ (i : Fin 3),
                        ∀ (s : Bool),
                          ∀ (x : GaussianInt), x ∈ (S i s).cells → 0 < (q i.succ).1
    )
            := by
  classical
  intro proto zero_cells q hq S hs hsub i s x hx
  have hn := (ProperBandCurvatureStructure q hq).2.1 i
  by_contra hn'
  have hz : (q i.succ).1 = 0 := by omega
  have he := zero_cells _ _ (proto _ _ _ (hsub i s)) hz
  rw [he] at hx
  simp at hx

private theorem cellcover :
    (by
      classical
      exact
        ∀ (V : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (x : LatticeCell), x ∈ V.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈
            (S i s).cells) → (∀ (j : Fin (3 : ℕ)),
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let tiles := fun t => S (slot t).1 (slot t).2
        (∀ (i : Fin 3), ∀ (s : Bool), (0 < (q i.succ).1) → (slot (e (i,s)) = (i,s))) → ((∀ (i :
            Fin 3), ∀ (s : Bool), ∀ (x : GaussianInt), (x ∈ (S i s).cells) → (0 < (q i.succ).1))
            → (∀ x, x ∈ V.cells ↔ ∃ t, x ∈ (tiles t).cells))) ) := by
  classical
  intro V q S hcells j chooseSlot e slot tiles selected parent_positive x
  constructor
  · intro hx
    obtain ⟨i,s,hxi⟩ := (hcells x).mp hx
    refine ⟨e (i,s), ?_⟩
    simpa only [tiles,selected i s (parent_positive i s x hxi)] using hxi
  · rintro ⟨t,ht⟩
    exact (hcells x).mpr ⟨(slot t).1,(slot t).2,ht⟩

private theorem ododom :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs :
            Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (q i.succ) (S i s) (hs i s)) → (∀ (j : Fin (3 : ℕ)),
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        (∀ t, 0 < (q (chooseSlot t).1.succ).1) → (
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let tiles := fun t => S (slot t).1 (slot t).2
        let odos := fun t => hs (slot t).1 (slot t).2
        ∀ t, ((odos t).domain : Set GaussianInt) = FootprintVertices (tiles t))) ) := by
  classical
  intro q S hs hsub j chooseSlot chosen_positive e slot tiles odos t
  exact PositiveCurvatureTileOdometerDomain _ _ _ (chosen_positive _)
    (hsub (slot t).1 (slot t).2)

private theorem footcover :
    (by
      classical
      exact
        ∀ (V : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s
            : Bool), FootprintVertices (S i s) ⊆ FootprintVertices V) → (∀ (j : Fin (3 : ℕ)),
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let tiles := fun t => S (slot t).1 (slot t).2
        let odos := fun t => hs (slot t).1 (slot t).2
        (V.cells.Nonempty) → ((∀ x, x ∈ V.cells ↔ ∃ t, x ∈ (tiles t).cells) → ((∀ t, ((odos
            t).domain : Set GaussianInt) = FootprintVertices (tiles t)) → (∀ x, x ∈
            FootprintVertices V ↔ ∃ t, x ∈ (odos t).domain)))) ) := by
  classical
  intro V q S hs hfoot j chooseSlot e slot tiles odos tilene cellcover ododom x
  constructor
  · intro hx
    simp only [FootprintVertices, ite_eq_left tilene, Set.mem_ofPred_eq] at hx
    obtain ⟨y,hy,hxy⟩ := hx
    obtain ⟨t,ht⟩ := (cellcover y).mp hy
    have hne : (tiles t).cells.Nonempty := ⟨y,ht⟩
    refine ⟨t,?_⟩
    have hf : x ∈ FootprintVertices (tiles t) := by
      simp only [FootprintVertices,ite_eq_left hne,Set.mem_ofPred_eq]
      exact ⟨y,ht,hxy⟩
    exact (Set.ext_iff.mp (ododom t) x).mpr hf
  · rintro ⟨t,ht⟩
    exact hfoot (slot t).1 (slot t).2 ((Set.ext_iff.mp (ododom t) x).mp ht)

private theorem coverdisk :
    (by
      classical
      exact
        (∀ D, ∀ V, ∀ k, TileOdometer D V k → 0 < D.1 → LatticeTile V) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs : Fin (3 : ℕ) →
            Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ)
            (S i s) (hs i s)) → (∀ (j : Fin (3 : ℕ)),
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        (∀ t, 0 < (q (chooseSlot t).1.succ).1) → (
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let tiles := fun t => S (slot t).1 (slot t).2
        ∀ t, LatticeTile (tiles t)))) ) := by
  classical
  intro disk q S hs hsub j chooseSlot chosen_positive e slot tiles t
  exact disk _ _ _ (hsub (slot t).1 (slot t).2) (chosen_positive _)

private theorem covercompat :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer),
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j : Fin (3 : ℕ)), ∀ (t : Bool),
            OdometerCompatibility (hs i s) (hs j t)) → (∀ (j : Fin (3 : ℕ)),
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let odos := fun t => hs (slot t).1 (slot t).2
        ∀ t, ∀ v, OdometerCompatibility (odos t) (odos v)) ) := by
  classical
  intro q hs hcompat j chooseSlot e slot odos t v
  exact hcompat _ _ _ _

private theorem hkcompat :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (hs : Fin (3 : ℕ) →
            Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (hs i s).domain,
            k.value x = (hs i s).value x) → (∀ (j : Fin (3 : ℕ)),
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let odos := fun t => hs (slot t).1 (slot t).2
        ∀ t, OdometerCompatibility k (odos t)) ) := by
  classical
  intro k q hs hvalue j chooseSlot e slot odos t
  right
  refine ⟨0,?_⟩
  intro x hx hy
  rw [hvalue (slot t).1 (slot t).2 x hy]
  simp only [odos,sub_self]

private theorem htcompat :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), ∀
            (l : PartialOdometer), ∀ (u : GaussianInt), ∀ (rs : Fin (3 : ℕ) → Bool →
            PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (rs i s).domain, l.value
            x = (rs i s).value x) → (∀ (j : Fin (3 : ℕ)), ∀ (a : GaussianInt), (∀ i, ∀ s, 0 < (q
            i.succ).1 → ∃ b : ℤ, (∀ x, x ∈ (hs i s).domain ↔ x-u ∈ (rs i s).domain) ∧ ∀ x, x ∈
            (hs i s).domain → (hs i s).value x = (rs i s).value (x-u)+a.re*x.re+a.im*x.im+b) → (
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        (∀ t, 0 < (q (chooseSlot t).1.succ).1) → (
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let odos := fun t => hs (slot t).1 (slot t).2
        let translated := PartialOdometerAffineTranslate l u a 0
        ∀ t, OdometerCompatibility translated (odos t)))) ) := by
  classical
  intro q hs l u rs rvalue j a common chooseSlot chosen_positive e slot odos translated t
  obtain ⟨b,hd,hv⟩ := common (slot t).1 (slot t).2 (chosen_positive _)
  right
  refine ⟨b,?_⟩
  intro x hx hy
  have hxr : x-u ∈ (rs (slot t).1 (slot t).2).domain := (hd x).mp hy
  rw [hv x hy, (PartialOdometerAffineTranslateFormulas l u a 0).2.2.1 x hx,
    rvalue (slot t).1 (slot t).2 (x-u) hxr]
  ring

end OdometerTranslationGeometry

theorem TileOdometerTranslationUniqueness
    (C : CircleCoordinates) (T U : ProtoTile) (h g : PartialOdometer)
    (hC : 0 < C.1) (hT : TileOdometer C T h)
    (hU : TileOdometer C U g) :
    ∃! u : GaussianInt,
      T.cells = (TileTranslation U u).cells ∧
      (T.cells = ∅ → T.anchor = (TileTranslation U u).anchor) ∧
      ∃ a : GaussianInt, ∃ b : ℤ,
        (∀ x, x ∈ h.domain ↔ x - u ∈ g.domain) ∧
        ∀ x, x ∈ h.domain →
          h.value x = g.value (x - u) +
            a.re * x.re + a.im * x.im + b := by
-- BODY
  classical
  have hTproto : BandPrototile C T := TileOdometerBandPrototile C T h hT
  have hUproto : BandPrototile C U := TileOdometerBandPrototile C U g hU
  have proto : ∀ D V k, TileOdometer D V k → BandPrototile D V := TileOdometerBandPrototile
  have positive_parent : ∀ q, ProperBandQuadruple q →
      ∃ i : Fin 3, 0 < (q i.succ).1 := OdometerTranslationGeometry.positive_parent
  have proper_large : ∀ q, ProperBandQuadruple q → 1 < (q 0).1 :=
      OdometerTranslationGeometry.proper_large positive_parent
  have positive_cells : ∀ D V, BandPrototile D V → 0 < D.1 →
      V.cells.Nonempty := (fun D V hV hD => BandPrototileNonempty.positive D V hD hV)
  have zero_cells : ∀ D V, BandPrototile D V → D.1 = 0 → V.cells = ∅ :=
      OdometerTranslationGeometry.zero_cells
  have cent_eq : ∀ V W : ProtoTile, V.cells = W.cells →
      (V.cells = ∅ → V.anchor = W.anchor) → TileCentroid V = TileCentroid W :=
          OdometerTranslationGeometry.cent_eq
  have foot_eq : ∀ V W : ProtoTile, V.cells = W.cells →
      (V.cells = ∅ → V.anchor = W.anchor) → FootprintVertices V = FootprintVertices W :=
          OdometerTranslationGeometry.foot_eq
  have domains : ∀ D V W k l, 0 < D.1 →
      TileOdometer D V k → TileOdometer D W l → ∀ u,
      V.cells = (TileTranslation W u).cells →
      (V.cells = ∅ → V.anchor = (TileTranslation W u).anchor) →
      ∀ x, x ∈ k.domain ↔ x-u ∈ l.domain := OdometerTranslationGeometry.domains foot_eq
  have affine_eq : ∀ (k l : PartialOdometer) (u a : GaussianInt) (b : ℤ),
      (∀ x, x ∈ k.domain ↔ x-u ∈ l.domain) →
      (∀ x, x ∈ k.domain → k.value x = l.value (x-u) +
        a.re*x.re + a.im*x.im+b) →
      k = PartialOdometerAffineTranslate l u a b := OdometerTranslationGeometry.affine_eq
  have unit_shift : ∀ (z x : GaussianInt) (V : ProtoTile) (k : PartialOdometer),
      V.cells = {x} → (k.domain : Set GaussianInt) = FootprintVertices V →
      ∀ v, (∀ y, y ∈ k.domain ↔ y-v ∈ (CurvatureOneOdometer z).domain) → v=x :=
          OdometerTranslationGeometry.unit_shift
  have square_disk : ∀ (V : ProtoTile) (x : GaussianInt), V.cells = {x} →
      LatticeTile V := OdometerTranslationGeometry.square_disk
  have disk : ∀ D V k, TileOdometer D V k → 0 < D.1 → LatticeTile V :=
      OdometerTranslationGeometry.disk square_disk
  have comparison : ∀ D V k, TileOdometer D V k → 0 < D.1 →
      ∀ W l, TileOdometer D W l → ∀ u,
      V.cells = (TileTranslation W u).cells →
      (V.cells = ∅ → V.anchor = (TileTranslation W u).anchor) →
      ∃ a : GaussianInt, ∃ b : ℤ,
        ∀ x, x ∈ k.domain → k.value x = l.value (x-u) +
          a.re*x.re + a.im*x.im+b := by
    intro D V k hk
    induction hk with
    | line w x hw k hd => simp
    | unit z x V k hc hd ht =>
        intro hp W l hl u hcells hempty
        refine TileOdometer.rec (motive := fun E W l _ =>
          E = (1,1+2*z) → V.cells = (TileTranslation W u).cells →
          (V.cells = ∅ → V.anchor = (TileTranslation W u).anchor) →
          ∃ a : GaussianInt, ∃ b : ℤ, ∀ t, t ∈ k.domain →
            k.value t = l.value (t-u)+a.re*t.re+a.im*t.im+b)
          ?_ ?_ ?_ hl rfl hcells hempty
        · intro w y hw l hdl he hcells hempty
          have hh := congrArg (fun D : CircleCoordinates => D.1) he
          norm_num at hh
        · intro z' y W l hcy hdy hty he hcells hempty
          have hz : z = z' := OdometerTranslationGeometry.hzAt354 z z' he
          subst z'
          obtain ⟨v,a,b,hv,hval⟩ := ht
          obtain ⟨w,c,d,hw,hval'⟩ := hty
          have vx : v=x := unit_shift z x V k hc hd v hv
          have wy : w=y := unit_shift z y W l hcy hdy w hw
          subst v
          subst w
          have hxy : x=y+u := by
            simpa [hc, hcy, TileTranslation, GaussianTranslation] using hcells
          refine ⟨a-c, b-d+c.re*u.re+c.im*u.im, ?_⟩
          intro t ht
          have htl : t-u ∈ l.domain := (domains _ V W k l hp
            (TileOdometer.unit z x V k hc hd ⟨x,a,b,hv,hval⟩)
            (TileOdometer.unit z y W l hcy hdy ⟨y,c,d,hw,hval'⟩)
            u hcells hempty t).mp ht
          rw [hval t ht, hval' (t-u) htl,
            show t-u-y = t-x by rw [hxy]; abel]
          dsimp
          ring
        · intro q' hq S' W hs' l hW hsub hcell hf hcent hdl hvl hcompat hslope ih'
            he hcells hempty
          have hh := congrArg (fun D : CircleCoordinates => D.1) he
          have hb := proper_large _ hq
          simp only [] at hh
          rw [hh] at hb
          norm_num at hb
    | @decompose q hq S V hs k hV hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
        intro hp W l hl u hc ha
        obtain ⟨R,rs,hW,rsub,rcells,rfoot,rcent,rdom,rvalue,rcompat,rslope⟩ :=
          TileOdometerReindexedDecomposition q hq W l (proper_large q hq) hl
        have houter := cent_eq V (TileTranslation W u) hc ha
        have matched : ∀ i s,
            (S i s).cells = (TileTranslation (R i s) u).cells ∧
            ((S i s).cells = ∅ → (S i s).anchor = (TileTranslation (R i s) u).anchor) :=
                OdometerTranslationGeometry.matched proto V q S hs hsub hcentroid W u R rs rsub
                rcent houter
        have pieces : ∀ i s, 0 < (q i.succ).1 →
            ∃ a : GaussianInt, ∃ b : ℤ,
              (∀ x, x ∈ (hs i s).domain ↔ x-u ∈ (rs i s).domain) ∧
              ∀ x, x ∈ (hs i s).domain → (hs i s).value x =
                (rs i s).value (x-u)+a.re*x.re+a.im*x.im+b := OdometerTranslationGeometry.pieces
                    domains q S hs hsub ih u R rs rsub matched
        obtain ⟨j,hj⟩ := positive_parent q hq
        obtain ⟨a,b0,hd0,hv0⟩ := pieces j false hj
        obtain ⟨p,pi,hp0,hpi,dx0,dy0⟩ := (hslope j false).resolve_left (by omega)
        obtain ⟨p',qi,hp1,hqi,dx1,dy1⟩ := (rslope j false).resolve_left (by omega)
        have coefficients : ∀ i s, 0 < (q i.succ).1 →
            ∀ (ai : GaussianInt) (bi : ℤ),
              (∀ x, x ∈ (hs i s).domain ↔ x-u ∈ (rs i s).domain) →
              (∀ x, x ∈ (hs i s).domain → (hs i s).value x =
                (rs i s).value (x-u)+ai.re*x.re+ai.im*x.im+bi) →
              (ai.re : ℝ) = p.1-p'.1 ∧ (ai.im : ℝ) = p.2-p'.2 :=
                  OdometerTranslationGeometry.coefficients affine_eq k q hs hslope l u rs
                  rslope p hp0 p' hp1
        have ca := coefficients j false hj a b0 hd0 hv0
        have common : ∀ i s, 0 < (q i.succ).1 → ∃ b : ℤ,
            (∀ x, x ∈ (hs i s).domain ↔ x-u ∈ (rs i s).domain) ∧
            ∀ x, x ∈ (hs i s).domain → (hs i s).value x =
              (rs i s).value (x-u)+a.re*x.re+a.im*x.im+b := OdometerTranslationGeometry.common q
                  hs u rs pieces a p p' coefficients ca
        -- Replace zero-curvature slots by a positive slot in the finite disk cover.
        let chooseSlot : Fin 3 × Bool → Fin 3 × Bool := fun t =>
          if 0 < (q t.1.succ).1 then t else (j,false)
        have chosen_positive : ∀ t, 0 < (q (chooseSlot t).1.succ).1 :=
            OdometerTranslationGeometry.chosen_positive q j hj
        let e := Fintype.equivFin (Fin 3 × Bool)
        let slot := fun t : Fin (Fintype.card (Fin 3 × Bool)) => chooseSlot (e.symm t)
        let tiles := fun t => S (slot t).1 (slot t).2
        let odos := fun t => hs (slot t).1 (slot t).2
        have selected (i : Fin 3) (s : Bool) (hi : 0 < (q i.succ).1) :
            slot (e (i,s)) = (i,s) := by simp [slot,chooseSlot,hi]
        have tilene : V.cells.Nonempty := positive_cells _ V hV hp
        have parent_positive (i : Fin 3) (s : Bool) (x : GaussianInt)
            (hx : x ∈ (S i s).cells) : 0 < (q i.succ).1 :=
                OdometerTranslationGeometry.parent_positive proto zero_cells q hq S hs hsub i
                s x hx
        have cellcover : ∀ x, x ∈ V.cells ↔ ∃ t, x ∈ (tiles t).cells :=
            OdometerTranslationGeometry.cellcover V q S hcells j selected parent_positive
        have ododom : ∀ t, ((odos t).domain : Set GaussianInt) = FootprintVertices (tiles t) :=
            OdometerTranslationGeometry.ododom q S hs hsub j chosen_positive
        have footcover : ∀ x, x ∈ FootprintVertices V ↔ ∃ t, x ∈ (odos t).domain :=
            OdometerTranslationGeometry.footcover V q S hs hfoot j tilene cellcover ododom
        have coverdisk : ∀ t, LatticeTile (tiles t) := OdometerTranslationGeometry.coverdisk disk
            q S hs hsub j chosen_positive
        have covercompat : ∀ t v, OdometerCompatibility (odos t) (odos v) :=
            OdometerTranslationGeometry.covercompat q hs hcompat j
        obtain ⟨glued,hgd,hgc,huniq⟩ := OdometerGluing.1
          (T := V) (U := tiles) (h := odos)
          (BandTileSimultaneousInduction q hq V hV).1 coverdisk ododom covercompat
          cellcover footcover
        have hk : TileOdometer (q 0) V k :=
          TileOdometer.decompose hq hV hsub hcells hfoot hcentroid hdom hvalue hcompat hslope
        have hkd := PositiveCurvatureTileOdometerDomain _ _ _ hp hk
        have hld := PositiveCurvatureTileOdometerDomain _ _ _ hp hl
        let translated := PartialOdometerAffineTranslate l u a 0
        have htd : (translated.domain : Set GaussianInt) = FootprintVertices V :=
          ((PartialOdometerAffineTranslateFormulas l u a 0).2.2.2.2.1 W hld).trans
            (foot_eq V (TileTranslation W u) hc ha).symm
        have hkcompat : ∀ t, OdometerCompatibility k (odos t) :=
            OdometerTranslationGeometry.hkcompat k q hs hvalue j
        have htcompat : ∀ t, OdometerCompatibility translated (odos t) :=
            OdometerTranslationGeometry.htcompat q hs l u rs rvalue j a common chosen_positive
        obtain ⟨b1,hb1⟩ := huniq k hkd hkcompat
        obtain ⟨b2,hb2⟩ := huniq translated htd htcompat
        refine ⟨a,b1-b2,?_⟩
        intro x hx
        have hxg : x ∈ glued.domain := (Set.ext_iff.mp (hkd.trans hgd.symm) x).mp hx
        have hxt : x ∈ translated.domain := (Set.ext_iff.mp (hkd.trans htd.symm) x).mp hx
        have h1 := hb1 x hxg
        have h2 := hb2 x hxg
        rw [(PartialOdometerAffineTranslateFormulas l u a 0).2.2.1 x hxt] at h2
        linarith
  obtain ⟨u,hcells,hempty⟩ := BandPrototileTranslationNormalForm C T U hTproto hUproto
  obtain ⟨a,b,hval⟩ := comparison C T h hT hC U g hU u hcells hempty
  refine ⟨u, ⟨hcells,hempty,a,b,domains C T U h g hC hT hU u hcells hempty,hval⟩, ?_⟩
  intro v hv
  have hcent : TileCentroid (TileTranslation U v) = TileCentroid (TileTranslation U u) :=
    (cent_eq T (TileTranslation U v) hv.1 hv.2.1).symm.trans
      (cent_eq T (TileTranslation U u) hcells hempty)
  rw [(TileTranslationFormulas U v).2.2.2.2.1,
    (TileTranslationFormulas U u).2.2.2.2.1] at hcent
  apply Zsqrtd.ext
  · have hh := congrArg Prod.fst hcent
    dsimp at hh
    exact_mod_cast (add_left_cancel hh : (v.re : ℝ) = (u.re : ℝ))
  · have hh := congrArg Prod.snd hcent
    dsimp at hh
    exact_mod_cast (add_left_cancel hh : (v.im : ℝ) = (u.im : ℝ))

end ApollonianSuperharmonic

end

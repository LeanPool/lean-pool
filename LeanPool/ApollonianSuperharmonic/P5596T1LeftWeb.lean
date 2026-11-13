/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandCircleClassification
public import LeanPool.ApollonianSuperharmonic.P3996T1AdjacentParentPlacement
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentIncomingEndpoint
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceDisjointCompanionEndpoints
public import LeanPool.ApollonianSuperharmonic.P5589T1EndpointCompatibility
public import LeanPool.ApollonianSuperharmonic.P5589T1UnitInterfaceSelection
public import LeanPool.ApollonianSuperharmonic.P5589T1LinkedUnitValues
public import LeanPool.ApollonianSuperharmonic.P5596T1LineParent

-- [TABLET NODE: P5596T1LeftWeb]

/-!
# P5596T1LeftWeb

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LeftWebGeometry

private theorem hdata :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T₁ : ProtoTile), ∀ (T₂ : ProtoTile), (ℕ) → ((C.1.1.1 = (1 : ℤ)) →
            (∀ (p₁ : ℝ × ℝ), ∀ (p₂ : ℝ × ℝ), ((C.1.1.1 = (1 : ℤ) ∧ ∃ (orientation : Bool) (v :
            GaussianInt), UnitTriangularStep orientation v ∧ TileCentroid T₂ - TileCentroid T₁ =
            GaussianRealPoint v ∧ p₂.1 - p₁.1 = CircleMatrix C (0 : Fin (2 : ℕ)) (0 : Fin (2 :
            ℕ)) * (↑v.re : ℝ) + CircleMatrix C (0 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) * (↑v.im : ℝ)
            ∧ p₂.2 - p₁.2 = CircleMatrix C (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * (↑v.re : ℝ) +
            CircleMatrix C (1 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) * (↑v.im : ℝ)) ∨ ∃ (q : Fin (4 :
            ℕ) → CircleCoordinates) (i : Fin (3 : ℕ)) (e : Bool), ProperBandQuadruple q ∧ q (0 :
            Fin (4 : ℕ)) = C.1.1 ∧ TileCentroid T₂ - TileCentroid T₁ = (if e = true then (1 : ℝ)
            else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) ∧
            p₂.1 - p₁.1 = (if e = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q i.succ)
            (q (0 : Fin (4 : ℕ)))).re : ℝ) ∧ p₂.2 - p₁.2 = (if e = true then (1 : ℝ) else (-1 :
            ℝ)) * (↑(BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).im : ℝ)) → (∃ v :
            GaussianInt, TileCentroid T₂ - TileCentroid T₁ = GaussianRealPoint v ∧ p₂.1-p₁.1 =
            CircleMatrix C 0 0*v.re + CircleMatrix C 0 1*v.im ∧ p₂.2-p₁.2 = CircleMatrix C 1
            0*v.re + CircleMatrix C 1 1*v.im))) ) := by
  classical
  intro C T₁ T₂ n hc p₁ p₂ hstep
  rcases hstep with ⟨_, orientation, v, _, hv, hr, hi⟩ | ⟨q,i,e,hq,hqC,_⟩
  · exact ⟨v,hv,hr,hi⟩
  · have hqone : (q 0).1 = 1 := by rw [hqC, hc]
    have hs := ProperBandCurvatureStructure q hq
    have hn (j : Fin 3) : (q j.succ).1 = 0 := by
      have hb := hq.2 j
      have hzj := hs.2.1 j
      omega
    exact ((by decide : (0 : Fin 3) ≠ 1)
      (hs.2.2 0 1 (hn 0) (hn 1))).elim

private theorem hmatrixAt187 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (z : GaussianInt), (C.1.1 = ((1 : ℤ), (1 : GaussianInt) + (2 :
            GaussianInt) * z)) → (CircleMatrix C = ![![((1+z.re : ℤ) : ℝ), (z.im : ℝ)], ![(z.im :
            ℝ), (-z.re : ℝ)]]) ) := by
  classical
  intro C z hz
  unfold CircleMatrix BandCircleEuclideanData
  simp only [show C.1.1.1 = 1 by rw [hz],
    show C.1.1.2 = 1+2*z by rw [hz]]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp only [
    Complex.div_re, Complex.div_im, GaussianInt.toComplex_def,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im]
  all_goals norm_num
  all_goals ring

private theorem har :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (u₁ : GaussianInt), ∀ (a₁ : GaussianInt), ∀ (u₂ : GaussianInt), ∀
            (a₂ : GaussianInt), (((1 : ℝ) + (↑z.re : ℝ)) * (↑u₂.re : ℝ) + (↑z.im : ℝ) * (↑u₂.im :
            ℝ) + (↑a₂.re : ℝ) + (↑z.im : ℝ) / (2 : ℝ) - (((1 : ℝ) + (↑z.re : ℝ)) * (↑u₁.re : ℝ) +
            (↑z.im : ℝ) * (↑u₁.im : ℝ) + (↑a₁.re : ℝ) + (↑z.im : ℝ) / (2 : ℝ)) = (↑((1 : ℤ) +
            z.re) : ℝ) * ((↑u₂.re : ℝ) - (↑u₁.re : ℝ)) + (↑z.im : ℝ) * ((↑u₂.im : ℝ) - (↑u₁.im :
            ℝ))) → ((a₁.re : ℝ) = a₂.re) ) := by
  classical
  intro z u₁ a₁ u₂ a₂ hr
  push_cast at hr
  nlinarith only [hr]

private theorem hai :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (u₁ : GaussianInt), ∀ (a₁ : GaussianInt), ∀ (u₂ : GaussianInt), ∀
            (a₂ : GaussianInt), ((↑z.im : ℝ) * (↑u₂.re : ℝ) - (↑z.re : ℝ) * (↑u₂.im : ℝ) +
            (↑a₂.im : ℝ) + (↑z.im : ℝ) / (2 : ℝ) - ((↑z.im : ℝ) * (↑u₁.re : ℝ) - (↑z.re : ℝ) *
            (↑u₁.im : ℝ) + (↑a₁.im : ℝ) + (↑z.im : ℝ) / (2 : ℝ)) = (↑z.im : ℝ) * ((↑u₂.re : ℝ) -
            (↑u₁.re : ℝ)) + -(↑z.re : ℝ) * ((↑u₂.im : ℝ) - (↑u₁.im : ℝ))) → ((a₁.im : ℝ) = a₂.im)
            ) := by
  classical
  intro z u₁ a₁ u₂ a₂ hi
  nlinarith only [hi]

private theorem haAt220 :
    (by
      classical
      exact
        ∀ (a₁ : GaussianInt), ∀ (a₂ : GaussianInt), ((a₁.re : ℝ) = a₂.re) → (((a₁.im : ℝ) =
            a₂.im) → (a₁ = a₂)) ) := by
  classical
  intro a₁ a₂ har hai
  apply Zsqrtd.ext
  · exact_mod_cast har
  · exact_mod_cast hai

private theorem hbAt227 :
    (by
      classical
      exact
        (∀ (h₁ : PartialOdometer), ∀ (h₂ : PartialOdometer), ∀ (g :
            IntegerLatticeFunction), ∀ (x : GaussianInt), ∀ (c₁ : ℤ), (∀ x ∈ h₁.domain, g x =
            h₁.value x + c₁) → (∀ (c₂ : ℤ), (∀ x ∈ h₂.domain, g x = h₂.value x + c₂) → ((x ∈
            h₁.domain) → ((x ∈ h₂.domain) → (
        (∀ (z : GaussianInt), ∀ (a₁ : GaussianInt), ∀
            (b₁ : ℤ), (∀ x ∈ h₁.domain, h₁.value x = P5570T1UnitQuadratic z x + a₁.re * x.re +
            a₁.im * x.im + b₁) → (∀ (b₂ : ℤ), (∀ x ∈ h₂.domain, h₂.value x =
            P5570T1UnitQuadratic z x + a₁.re * x.re + a₁.im * x.im + b₂) → (b₁+c₁ =
            b₂+c₂)))))))) ) := by
  classical
  intro h₁ h₂ g x c₁ hg₁ c₂ hg₂ hx₁ hx₂ z a₁ b₁ hval₁ b₂ hval₂
  have he₁ := hg₁ x hx₁
  have he₂ := hg₂ x hx₂
  rw [hval₁ x hx₁] at he₁
  rw [hval₂ x hx₂] at he₂
  omega

private theorem hvalues :
    (by
      classical
        exact
        (∀ (h₁ : PartialOdometer),
          ∀ (h₂ : PartialOdometer),
            ∀ (g : IntegerLatticeFunction),
              ∀ (x : GaussianInt),
                ∀ (c₁ : ℤ),
                  (∀ x ∈ h₁.domain, g x = h₁.value x + c₁) →
                    (∀ (c₂ : ℤ),
                      (∀ x ∈ h₂.domain, g x = h₂.value x + c₂) →
                        ((∀ (y : GaussianInt),
                            y = x ∨
                                y = x + (1 : GaussianInt) ∨
                                  y = x - (1 : GaussianInt) ∨
                                    y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                      y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                              y ∈ h₁.domain ∨ y ∈ h₂.domain) →
                          (∀ (z : GaussianInt),
                            ∀ (a₁ : GaussianInt),
                              ∀ (b₁ : ℤ),
                                (∀ x ∈ h₁.domain,
                                    h₁.value x =
                                      P5570T1UnitQuadratic z x + a₁.re * x.re +
                                          a₁.im * x.im +
                                        b₁) →
                                  (∀ (b₂ : ℤ),
                                    (∀ x ∈ h₂.domain,
                                        h₂.value x =
                                          P5570T1UnitQuadratic z x + a₁.re * x.re +
                                              a₁.im * x.im +
                                            b₂) →
                                      ((b₁ + c₁ = b₂ + c₂) →
                                        (∀ (y : GaussianInt),
                                          (y = x ∨
                                              y = x + 1 ∨
                                                y = x - 1 ∨
                                                  y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) →
                                            (g y =
                                              P5570T1UnitQuadratic z y +
                                                    a₁.re * y.re +
                                                  a₁.im * y.im +
                                                (b₁ + c₁)))))))))) := by
  classical
  intro h₁ h₂ g x c₁ hg₁ c₂ hg₂ hstar z a₁ b₁ hval₁ b₂ hval₂ hb y hy
  rcases hstar y hy with hy₁ | hy₂
  · rw [hg₁ y hy₁, hval₁ y hy₁]
    ring
  · rw [hg₂ y hy₂, hval₂ y hy₂]
    omega

private theorem translationAt244 :
    (by
      classical
      exact
        ∀ (C : BandCircle), (IntegerLatticeFunction) → (∀ (x : GaussianInt), (C.1.1.1 = (1 :
            ℤ)) → (∀ (z : GaussianInt), (CircleMatrix C = ![![(↑((1 : ℤ) + z.re) : ℝ), (↑z.im :
            ℝ)], ![(↑z.im : ℝ), -(↑z.re : ℝ)]]) → ((
        let g := fun (x : GaussianInt) => ((1 : ℤ) + z.re) * (x.re * (x.re - (1 : ℤ)) / (2 : ℤ))
            - z.re * (x.im * (x.im - (1 : ℤ)) / (2 : ℤ)) + z.im * x.re * x.im;
        let T := (⟨{(0 : LatticeCell)}, (0 : GaussianInt)⟩ : ProtoTile);
        let h := CurvatureOneOdometer z; BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h ∧
            (↑h.domain : Set GaussianInt) = FootprintVertices T ∧ (∀ x ∈ h.domain, g x = h.value
            x) ∧ GlobalOdometerExtends g h ∧ IntegerSuperharmonicRepresentative (CircleMatrix C)
            g ∧ (∀ v ∈ TilingLattice C, ∃ (a : GaussianInt), (CircleMatrix C).mulVec ![(↑v.re :
            ℝ), (↑v.im : ℝ)] = ![(↑a.re : ℝ), (↑a.im : ℝ)] ∧ ∀ (x : GaussianInt), g (x + v) = g x
            + x.re * a.re + x.im * a.im + g v) ∧ ∃ (b : ℝ × ℝ), ∀ v ∈ TilingLattice C, ∀ (x :
                GaussianInt), (↑(g (x + v)) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
            (b.1 * (↑(x + v).re : ℝ) + b.2 * (↑(x + v).im : ℝ)) = (↑(g x) : ℝ) -
            LatticeQuadraticForm (CircleMatrix C) x - (b.1 * (↑x.re : ℝ) + b.2 * (↑x.im : ℝ))) →
            (∀ (v : GaussianInt), P5570T1UnitQuadratic z (x+v) = P5570T1UnitQuadratic z x +
            P5570T1UnitQuadratic z v + ((1+z.re)*v.re+z.im*v.im)*x.re +
            (z.im*v.re-z.re*v.im)*x.im))))) := by
  classical
  intro C g x hc z hmatrix hperiodic v
  obtain ⟨w, hw, hshift⟩ := hperiodic.2.2.2.2.2.2.1 v
    (by simp [TilingLattice, hc])
  have hr : (1+z.re)*v.re+z.im*v.im = w.re := by
    have he := congrFun hw 0
    simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at he
    exact_mod_cast he
  have hi : z.im*v.re-z.re*v.im = w.im := by
    have he := congrFun hw 1
    simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at he
    have he' : z.im*v.re + -z.re*v.im = w.im := by exact_mod_cast he
    linear_combination he'
  have he : P5570T1UnitQuadratic z (x+v) =
      P5570T1UnitQuadratic z x + x.re*w.re + x.im*w.im +
        P5570T1UnitQuadratic z v := hshift x
  rw [← hr, ← hi] at he
  linear_combination he

private theorem hq :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (z : GaussianInt), ∀ (a₁ : GaussianInt), ∀ (b₁ : ℤ), ∀ (c₁ : ℤ),
            (∀ (v : GaussianInt), P5570T1UnitQuadratic z (x+v) = P5570T1UnitQuadratic z x +
            P5570T1UnitQuadratic z v + ((1+z.re)*v.re+z.im*v.im)*x.re +
            (z.im*v.re-z.re*v.im)*x.im) → (FourNeighborLaplacian (fun y => P5570T1UnitQuadratic
            z y + a₁.re*y.re + a₁.im*y.im + (b₁+c₁)) x = 1) ) := by
  classical
  intro x z a₁ b₁ c₁ translation
  have h1 := translation 1
  have hm1 := translation (-1)
  have hi := translation ⟨0,1⟩
  have hmi := translation (-⟨0,1⟩)
  simp only [sub_eq_add_neg, FourNeighborLaplacian]
  rw [h1, hm1, hi, hmi]
  norm_num [P5570T1UnitQuadratic]
  ring

private theorem hcminus3 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀
            (Rminus : ProtoTile), (TileCentroid Rminus - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) - BandVectors.1 (q
            (0 : Fin (4 : ℕ))) (q i.succ))) → ((BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) =
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))
            → (TileCentroid Rminus - TileCentroid U = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩
            : GaussianInt) ^ (3 : Fin 4).val * (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q
            0) (q i.succ))))) ) := by
  classical
  intro q i U Rminus hcminus flip
  rw [hcminus, flip]
  congr 2
  ext <;> simp [pow_succ] <;> ring

private theorem hmstep :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q i.succ)
            (q (0 : Fin (4 : ℕ)))) → ((⟨0, 1⟩ : GaussianInt) ^ (3 : Fin 4).val * (if Even (3 :
            Fin 4).val then BandVectors.1 (q i.succ) (q 0) else BandVectors.1 (q 0) (q i.succ)) =
            BandVectors.1 (q i.succ) (q 0)) ) := by
  classical
  intro q i flip
  rw [flip]
  norm_num [show ¬ Even 3 by decide, pow_succ]
  ext <;> simp

private theorem hd :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), (TileCentroid V - TileCentroid U = GaussianRealPoint (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))))) → (∀ (d : GaussianInt), (FootprintVertices V =
            FootprintVertices (TileTranslation U d) ∧ BoundaryFootprintVertices V =
            BoundaryFootprintVertices (TileTranslation U d) ∧ BoundaryFootprintEdges V =
            BoundaryFootprintEdges (TileTranslation U d) ∧ TileRealization V = TileRealization
            (TileTranslation U d) ∧ TileCentroid V = TileCentroid (TileTranslation U d)) → (d =
            BandVectors.1 (q i.succ) (q 0))) ) := by
  classical
  intro q i U V hcUV d hobs
  have he := hcUV
  rw [hobs.2.2.2.2, (TileTranslationFormulas U d).2.2.2.2.1] at he
  have hre := congrArg Prod.fst he
  have him := congrArg Prod.snd he
  dsimp [GaussianRealPoint] at hre him
  apply Zsqrtd.ext
  · have he : (d.re : Real) = (BandVectors.1 (q i.succ) (q 0)).re := by
      linarith
    exact_mod_cast he
  · have he : (d.im : Real) = (BandVectors.1 (q i.succ) (q 0)).im := by
      linarith
    exact_mod_cast he

private theorem haMV :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile),
        let M := TileTranslation U (BandVectors.1 (q i.succ) (q 0))
        (V.cells = (TileTranslation U (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))).cells) →
            ((V.cells = ∅ → V.anchor = (TileTranslation U (BandVectors.1 (q i.succ) (q (0 : Fin
            (4 : ℕ))))).anchor) → (M.cells = ∅ → M.anchor = V.anchor)) ) := by
  classical
  intro q i U V M hcells hanchor hempty
  exact (hanchor (hcells.trans hempty)).symm

private theorem hnV :
    (by
      classical
      exact
        (BandCircle) → ((ℕ) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), (Fin (3 : ℕ)) →
            ((ProperBandQuadruple q) → ((ProtoTile) → (∀ (V : ProtoTile), (LatticeTile V ∧
            TileArea V = (q (0 : Fin (4 : ℕ))).1.toNat ∧ (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
                (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q V i s (S i s)) → (∀
                (x : LatticeCell), x ∈ V.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i
                s).cells) → ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), LatticeTile (TileCellComplement V
                (S i s)) ∧
            TileTouching (TileCellComplement V (S i s)) (S i s)) ∧ QuarterTurnSymmetric V ∧ ((1 :
            ℤ) < (q (0 : Fin (4 : ℕ))).1 → ∀ (i : Fin (3 : ℕ)), TouchingTriple V (TileTranslation
            V (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation V
            (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) ∧ ((1 : ℤ)
            < (q (0 : Fin (4 : ℕ))).1 → ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q
            i.succ) U → TileCentroid U - TileCentroid V = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple V (TileTranslation V
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (U :
                ProtoTile), ∀ (V_1 : ProtoTile), BandPrototile (q i.succ) U → BandPrototile (q (i +
            (1 : Fin (3 : ℕ))).succ) V_1 → TileCentroid U - TileCentroid V = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid
            V_1 - TileCentroid V = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 :
            Fin (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → TouchingTriple V U V_1) ∧ ∀ (r :
                Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = q (1
            : Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = q
            (3 : Fin (4 : ℕ)) → (q (2 : Fin (4 : ℕ))).1 ≤ (q (1 : Fin (4 : ℕ))).1 → (q (3 : Fin
            (4 : ℕ))).1 ≤ (q (2 : Fin (4 : ℕ))).1 → (1 : ℤ) < (q (2 : Fin (4 : ℕ))).1 → ∀ (P :
                Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
                BandSubtileOccurrence q V i s (P i s)) → (∀ (x : LatticeCell), x ∈ V.cells ↔ ∃ (i :
            Fin (3 : ℕ)) (s : Bool), x ∈ (P i s).cells) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
                BandSubtileOccurrence r (P (0 : Fin (3 : ℕ)) true) i s (Q i s)) → (∀ (x :
                LatticeCell), x ∈ (P (0 : Fin (3 : ℕ)) true).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool),
            x ∈ (Q i s).cells) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence r (P
            (0 : Fin (3 : ℕ)) false) i s (S i s)) → (∀ (x : LatticeCell), x ∈ (P (0 : Fin (3 :
            ℕ)) false).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let u := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let v := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); (∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ((FootprintEdges
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)).Nonempty → AllowedSubtileIncidence a b) ∧
            (¬AllowedSubtileIncidence a b → FootprintVertices (SubtileOccurrenceInterpretation P
            u v a) ∩ FootprintVertices (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧ FootprintVertices (P (0 :
            Fin (3 : ℕ)) true) ∩ FootprintVertices (P (1 : Fin (3 : ℕ)) true) ⊆ FootprintVertices
            (Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (P (1 : Fin (3 : ℕ)) true) ∧
            FootprintVertices (P (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (P (0 : Fin (3 : ℕ))
            false) ⊆ FootprintVertices (Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (S (2 : Fin
            (3 : ℕ)) false) ∪ FootprintVertices (Q (0 : Fin (3 : ℕ)) false) ∪ FootprintVertices
            (Q (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (S (1 : Fin (3 : ℕ)) false)) →
            (V.cells ≠ ∅)))))) ) := by
  classical
  intro C n q i hq U V hgeomV
  have harea := hgeomV.2.1
  have hcpos := (ProperBandCurvatureStructure q hq).1
  intro he
  simp only [TileArea, he, Finset.card_empty] at harea
  omega

private theorem touchingRetarget :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile),
        let M := TileTranslation U (BandVectors.1 (q i.succ) (q 0))
        (M.cells = V.cells) → ((FootprintVertices M = FootprintVertices V ∧
            BoundaryFootprintVertices M = BoundaryFootprintVertices V ∧ BoundaryFootprintEdges M
            = BoundaryFootprintEdges V ∧ TileRealization M = TileRealization V ∧ TileCentroid M =
            TileCentroid V) → ((V.cells ≠ ∅) → (∀ (W : ProtoTile), (TouchingTriple U M W) →
            (TouchingTriple U V W)))) ) := by
  classical
  intro q i U V M hMV hobsMV hnV W ht
  simpa only [TouchingTriple, TileTouching, hMV,
    hobsMV.2.1, hobsMV.2.2.1, hnV, false_and, and_false,
    false_or, or_false] using ht

private theorem hsingletonDisk :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (u : GaussianInt), (W.cells = {u}) → (LatticeTile W) ) := by
  classical
  intro W u hu
  have hc : W.cells = (TileTranslation (FordTile 1) u).cells := by
    simpa [TileTranslation, FordTile, FordCellDomain, GaussianTranslation,
      show (⟨0, 0⟩ : GaussianInt) = 0 from rfl] using hu
  have ho := ProtoTileObservableExtensionality W _ hc
    (by simp [hu])
  change TopologicalDisk (TileRealization W)
  rw [ho.2.2.2.1]
  exact (TileDiskAreaCovariance (FordTile 1) u).1.mp
    (FordTileGeometry 1 (by decide)).1

private theorem hdisjoint :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (ProperBandQuadruple q) →
            (∀ (U : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), (TileCentroid
            Rminus - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (q i.succ)
            (q (0 : Fin (4 : ℕ))) - BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) →
            ((TileCentroid Rplus - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ)))
            (q i.succ))) → (∀ (um : GaussianInt), (Rminus.cells = {um}) → (∀ (up : GaussianInt),
            (Rplus.cells = {up}) → (Disjoint Rplus.cells Rminus.cells))))) ) := by
  classical
  intro q i hq U Rminus Rplus hcminus hcplus um hum up hup
  have hneq : up ≠ um := by
    intro he
    have hec : TileCentroid Rplus = TileCentroid Rminus := by
      simp [TileCentroid, hup, hum, he]
    have hre := congrArg Prod.fst hcplus
    have him := congrArg Prod.snd hcplus
    have hre' := congrArg Prod.fst hcminus
    have him' := congrArg Prod.snd hcminus
    rw [hec] at hre him
    have hz : BandVectors.1 (q 0) (q i.succ) = 0 := by
      apply Zsqrtd.ext
      · have : ((BandVectors.1 (q 0) (q i.succ)).re : Real) = 0 := by
          dsimp [GaussianRealPoint] at hre hre'
          push_cast at hre hre'
          linarith
        exact_mod_cast this
      · have : ((BandVectors.1 (q 0) (q i.succ)).im : Real) = 0 := by
          dsimp [GaussianRealPoint] at him him'
          push_cast at him him'
          linarith
        exact_mod_cast this
    exact VectorNonvanishing q hq.1 0 i.succ
      (Ne.symm (Fin.succ_ne_zero i))
      (Or.inl (ProperBandCurvatureStructure q hq).1) hz
  simpa [hup, hum] using hneq

private theorem hplusU :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (Rplus : ProtoTile), (TouchingTriple U V Rplus) →
            (∀ (up : GaussianInt), (Rplus.cells = {up}) → (Disjoint U.cells Rplus.cells)) ) := by
  classical
  intro U V Rplus htouchPlus up hup
  rcases htouchPlus.2.2.1 with h | h | h
  · exact h.2.2.1.symm
  · simp [hup] at h
  · simp [h.1]

private theorem hplusV :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (Rplus : ProtoTile), (V.cells ≠ ∅) →
            ((TouchingTriple U V Rplus) → (∀ (up : GaussianInt), (Rplus.cells = {up}) → (Disjoint
            V.cells Rplus.cells))) ) := by
  classical
  intro U V Rplus hnV htouchPlus up hup
  rcases htouchPlus.2.1 with h | h | h
  · exact h.2.2.1
  · exact (hnV h.1).elim
  · simp [hup] at h

private theorem hRS :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (up : GaussianInt), (Rplus.cells = {up})
            → ((Disjoint Rplus.cells Rminus.cells) → (Rminus ≠ Rplus)) ) := by
  classical
  intro Rminus Rplus up hup hdisjoint he
  have hn : up ∈ Rminus.cells := by rw [he, hup]; simp
  exact Finset.disjoint_left.mp hdisjoint (by simp [hup]) hn

private theorem hnorm :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (ProperBandQuadruple q) →
            (((q i.succ).1 = (1 : ℤ)) → (Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) = (q
            0).1+1)) ) := by
  classical
  intro q i hq hunit
  have hs := (VectorSquareProduct q hq.1 0 i.succ
    (Ne.symm (Fin.succ_ne_zero i))).1
  have ht := TangencyCoordinateIdentity q hq.1 0 i.succ
    (Ne.symm (Fin.succ_ne_zero i))
  have he : Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) ^ 2 =
      ((q 0).1+1)^2 := by
    rw [pow_two, ← Zsqrtd.norm_mul, ← pow_two, hs, ht, hunit]
  have hn := Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0)
    (BandVectors.1 (q 0) (q i.succ))
  have hp := (ProperBandCurvatureStructure q hq).1
  nlinarith

private theorem hnadj :
    (by
      classical
      exact
        (BandCircle) → ((ℕ) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀
            (hq : ProperBandQuadruple q), ((q i.succ).1 = (1 : ℤ)) → (∀ (hpos : 0 < (q i.succ).1),
        let Ci : BandCircle :=
          ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
        ∀ (U : ProtoTile), (ProtoTile) → (∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus
            : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (reverseTiles :
            List ProtoTile), ∀ (hs : List PartialOdometer), ∀ (reverseHs : List PartialOdometer),
            (TileString Ci orientation base Rplus Rminus reverseTiles) → ((OdometerStringRespect
            Ci orientation base Rminus Rplus tiles hs) → ((OdometerStringRespect Ci orientation
            base Rplus Rminus reverseTiles reverseHs) → (∀ (r : Fin (4 : ℕ) → CircleCoordinates),
            (Ci.1.1.1 = (1 : ℤ) → UnitOccurrenceOrientation r i orientation) → ((TileString Ci
            orientation base Rminus Rplus tiles) → ((TileCentroid Rminus - TileCentroid U = (1 /
            2 : ℝ) • GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) -
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((TileCentroid Rplus -
            TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((Zsqrtd.norm
            (BandVectors.1 (q 0) (q i.succ)) = (q 0).1+1) → (¬ ∃ v : GaussianInt,
            UnitTriangularStep orientation v ∧ TileCentroid Rplus - TileCentroid Rminus =
            GaussianRealPoint v)))))))))))) ) := by
  classical
  intro C n q i hq hunit hpos Ci U V orientation base Rminus Rplus tiles reverseTiles hs
      reverseHs hreverse hrespect hreverseRespect r horientation hstring hcminus hcplus hnorm
  rintro ⟨v,hv,hcv⟩
  have hveq : v = BandVectors.1 (q 0) (q i.succ) := by
    apply Zsqrtd.ext
    · have hr := congrArg Prod.fst hcv
      have hm := congrArg Prod.fst hcminus
      have hp := congrArg Prod.fst hcplus
      dsimp [GaussianRealPoint] at hr hm hp
      push_cast at hm hp
      have he : (v.re : ℝ) =
          ((BandVectors.1 (q 0) (q i.succ)).re : ℝ) := by linarith
      exact_mod_cast he
    · have hr := congrArg Prod.snd hcv
      have hm := congrArg Prod.snd hcminus
      have hp := congrArg Prod.snd hcplus
      dsimp [GaussianRealPoint] at hr hm hp
      push_cast at hm hp
      have he : (v.im : ℝ) =
          ((BandVectors.1 (q 0) (q i.succ)).im : ℝ) := by linarith
      exact_mod_cast he
  have hvnorm : Zsqrtd.norm v ≤ 2 := by
    cases orientation <;> simp only [UnitTriangularStep, Bool.false_eq_true,
      ite_false, ite_true, Finset.mem_insert,
      Finset.mem_singleton] at hv
    all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [Zsqrtd.norm]
  rw [hveq, hnorm] at hvnorm
  have hlt := hq.2 i
  omega

private theorem hUn :
    (by
      classical
      exact
        (
        (∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        ((ProperBandQuadruple q) → (∀ (U : ProtoTile), ∀ (V : ProtoTile), (LatticeTile U ∧
            TileArea U = (q (0 : Fin (4 : ℕ))).1.toNat ∧ (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
                (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q U i s (S i s)) → (∀
                (x : LatticeCell), x ∈ U.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i
                s).cells) → ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), LatticeTile (TileCellComplement U
                (S i s)) ∧
            TileTouching (TileCellComplement U (S i s)) (S i s)) ∧ QuarterTurnSymmetric U ∧ ((1 :
            ℤ) < (q (0 : Fin (4 : ℕ))).1 → ∀ (i : Fin (3 : ℕ)), TouchingTriple U (TileTranslation
            U (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation U
            (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) ∧ ((1 : ℤ)
            < (q (0 : Fin (4 : ℕ))).1 → ∀ (i : Fin (3 : ℕ)), ∀ (U_1 : ProtoTile), BandPrototile
            (q i.succ) U_1 → TileCentroid U_1 - TileCentroid U = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple U (TileTranslation U
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U_1) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (U_1
                : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U_1 → BandPrototile (q
                (i +
            (1 : Fin (3 : ℕ))).succ) V → TileCentroid U_1 - TileCentroid U = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V
            - TileCentroid U = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → TouchingTriple U U_1 V) ∧ ∀ (r : Fin
            (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = q (1 :
            Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = q (3
            : Fin (4 : ℕ)) → (q (2 : Fin (4 : ℕ))).1 ≤ (q (1 : Fin (4 : ℕ))).1 → (q (3 : Fin (4 :
            ℕ))).1 ≤ (q (2 : Fin (4 : ℕ))).1 → (1 : ℤ) < (q (2 : Fin (4 : ℕ))).1 → ∀ (P : Fin (3
            : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S : Fin (3 : ℕ)
            → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q U i
            s (P i s)) → (∀ (x : LatticeCell), x ∈ U.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈
            (P i s).cells) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence r (P (0 :
            Fin (3 : ℕ)) true) i s (Q i s)) → (∀ (x : LatticeCell), x ∈ (P (0 : Fin (3 : ℕ))
            true).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (Q i s).cells) → (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), BandSubtileOccurrence r (P (0 : Fin (3 : ℕ)) false) i s (S i s)) →
            (∀ (x : LatticeCell), x ∈ (P (0 : Fin (3 : ℕ)) false).cells ↔ ∃ (i : Fin (3 : ℕ)) (s
            : Bool), x ∈ (S i s).cells) →
        let u := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let v := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); (∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ((FootprintEdges
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)).Nonempty → AllowedSubtileIncidence a b) ∧
            (¬AllowedSubtileIncidence a b → FootprintVertices (SubtileOccurrenceInterpretation P
            u v a) ∩ FootprintVertices (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧ FootprintVertices (P (0 :
            Fin (3 : ℕ)) true) ∩ FootprintVertices (P (1 : Fin (3 : ℕ)) true) ⊆ FootprintVertices
            (Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (P (1 : Fin (3 : ℕ)) true) ∧
            FootprintVertices (P (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (P (0 : Fin (3 : ℕ))
            false) ⊆ FootprintVertices (Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (S (2 : Fin
            (3 : ℕ)) false) ∪ FootprintVertices (Q (0 : Fin (3 : ℕ)) false) ∪ FootprintVertices
            (Q (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (S (1 : Fin (3 : ℕ)) false)) →
            ((LatticeTile V ∧ TileArea V = (q (0 : Fin (4 : ℕ))).1.toNat ∧ (∀ (S : Fin (3 : ℕ) →
            Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q V i s
            (S i s)) → (∀ (x : LatticeCell), x ∈ V.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S
            i s).cells) → ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), LatticeTile (TileCellComplement V (S
            i s)) ∧ TileTouching (TileCellComplement V (S i s)) (S i s)) ∧ QuarterTurnSymmetric V
            ∧ ((1 : ℤ) < (q (0 : Fin (4 : ℕ))).1 → ∀ (i : Fin (3 : ℕ)), TouchingTriple V
            (TileTranslation V (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation
            V (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) ∧ ((1 :
            ℤ) < (q (0 : Fin (4 : ℕ))).1 → ∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile
            (q i.succ) U → TileCentroid U - TileCentroid V = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple V (TileTranslation V
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (U :
                ProtoTile), ∀ (V_1 : ProtoTile), BandPrototile (q i.succ) U → BandPrototile (q (i +
            (1 : Fin (3 : ℕ))).succ) V_1 → TileCentroid U - TileCentroid V = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid
            V_1 - TileCentroid V = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 :
            Fin (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → TouchingTriple V U V_1) ∧ ∀ (r :
                Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = q (1
            : Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = q
            (3 : Fin (4 : ℕ)) → (q (2 : Fin (4 : ℕ))).1 ≤ (q (1 : Fin (4 : ℕ))).1 → (q (3 : Fin
            (4 : ℕ))).1 ≤ (q (2 : Fin (4 : ℕ))).1 → (1 : ℤ) < (q (2 : Fin (4 : ℕ))).1 → ∀ (P :
                Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
                BandSubtileOccurrence q V i s (P i s)) → (∀ (x : LatticeCell), x ∈ V.cells ↔ ∃ (i :
            Fin (3 : ℕ)) (s : Bool), x ∈ (P i s).cells) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
                BandSubtileOccurrence r (P (0 : Fin (3 : ℕ)) true) i s (Q i s)) → (∀ (x :
                LatticeCell), x ∈ (P (0 : Fin (3 : ℕ)) true).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool),
            x ∈ (Q i s).cells) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence r (P
            (0 : Fin (3 : ℕ)) false) i s (S i s)) → (∀ (x : LatticeCell), x ∈ (P (0 : Fin (3 :
            ℕ)) false).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let u := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let v := BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); (∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ((FootprintEdges
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)).Nonempty → AllowedSubtileIncidence a b) ∧
            (¬AllowedSubtileIncidence a b → FootprintVertices (SubtileOccurrenceInterpretation P
            u v a) ∩ FootprintVertices (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧ FootprintVertices (P (0 :
            Fin (3 : ℕ)) true) ∩ FootprintVertices (P (1 : Fin (3 : ℕ)) true) ⊆ FootprintVertices
            (Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (P (1 : Fin (3 : ℕ)) true) ∧
            FootprintVertices (P (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (P (0 : Fin (3 : ℕ))
            false) ⊆ FootprintVertices (Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (S (2 : Fin
            (3 : ℕ)) false) ∪ FootprintVertices (Q (0 : Fin (3 : ℕ)) false) ∪ FootprintVertices
            (Q (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (S (1 : Fin (3 : ℕ)) false)) →
            (U.cells.Nonempty)))))) ) := by
  classical
  intro q hq U V hgeomU hgeomV
  have ha := hgeomU.2.1
  have hp := (ProperBandCurvatureStructure q hq).1
  by_contra he
  simp only [TileArea, Finset.not_nonempty_iff_eq_empty.mp he,
    Finset.card_empty] at ha
  omega

private theorem hmatrixAt529 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (hq : ProperBandQuadruple
            q), ∀ (hpos : 0 < (q i.succ).1),
        let Ci : BandCircle :=
          ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
        ∀ (z : GaussianInt), (Ci.1.1 = ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z)) →
            ((Ci.1.1.1 = 1) → (CircleMatrix Ci = ![![((1+z.re : ℤ) : ℝ), (z.im : ℝ)], ![(z.im :
            ℝ), (-z.re : ℝ)]])) ) := by
  classical
  intro q i hq hpos Ci z hz hCiunit
  unfold CircleMatrix BandCircleEuclideanData
  simp only [hCiunit, show Ci.1.1.2 = 1+2*z by rw [hz]]
  ext j k; fin_cases j <;> fin_cases k
  all_goals simp only [
    Complex.div_re, Complex.div_im,
    GaussianInt.toComplex_def, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
  all_goals norm_num
  all_goals ring

private theorem translationAt543 :
    (by
      classical
      exact
        (IntegerLatticeFunction) → (∀ (x : GaussianInt), ∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (hq : ProperBandQuadruple q), ∀ (hpos : 0
            < (q i.succ).1),
        let Ci : BandCircle :=
          ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
        ∀ (z : GaussianInt), (Ci.1.1.1 = 1) → ((CircleMatrix Ci = ![![((1+z.re : ℤ) : ℝ), (z.im :
            ℝ)], ![(z.im : ℝ), (-z.re : ℝ)]]) → ((
        let g := fun (x : GaussianInt) => ((1 : ℤ) + z.re) * (x.re * (x.re - (1 : ℤ)) / (2 : ℤ))
            - z.re * (x.im * (x.im - (1 : ℤ)) / (2 : ℤ)) + z.im * x.re * x.im;
        let T := (⟨{(0 : LatticeCell)}, (0 : GaussianInt)⟩ : ProtoTile);
        let h := CurvatureOneOdometer z; BandPrototile Ci.1.1 T ∧ TileOdometer Ci.1.1 T h ∧
            (↑h.domain : Set GaussianInt) = FootprintVertices T ∧ (∀ x ∈ h.domain, g x = h.value
            x) ∧ GlobalOdometerExtends g h ∧ IntegerSuperharmonicRepresentative (CircleMatrix Ci)
            g ∧ (∀ v ∈ TilingLattice Ci, ∃ (a : GaussianInt), (CircleMatrix Ci).mulVec ![(↑v.re :
            ℝ), (↑v.im : ℝ)] = ![(↑a.re : ℝ), (↑a.im : ℝ)] ∧ ∀ (x : GaussianInt), g (x + v) = g x
            + x.re * a.re + x.im * a.im + g v) ∧ ∃ (b : ℝ × ℝ), ∀ v ∈ TilingLattice Ci, ∀ (x :
                GaussianInt), (↑(g (x + v)) : ℝ) - LatticeQuadraticForm (CircleMatrix Ci) (x + v) -
            (b.1 * (↑(x + v).re : ℝ) + b.2 * (↑(x + v).im : ℝ)) = (↑(g x) : ℝ) -
            LatticeQuadraticForm (CircleMatrix Ci) x - (b.1 * (↑x.re : ℝ) + b.2 * (↑x.im : ℝ))) →
            (∀ (v : GaussianInt), P5570T1UnitQuadratic z (x+v) = P5570T1UnitQuadratic z x +
            P5570T1UnitQuadratic z v + ((1+z.re)*v.re+z.im*v.im)*x.re +
            (z.im*v.re-z.re*v.im)*x.im))))) := by
  classical
  intro g x q i hq hpos Ci z hCiunit hmatrix hperiodic v
  obtain ⟨w,hw,hshift⟩ := hperiodic.2.2.2.2.2.2.1 v
    (by simp [TilingLattice, hCiunit])
  have hr : (1+z.re)*v.re+z.im*v.im = w.re := by
    have he := congrFun hw 0
    simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at he
    exact_mod_cast he
  have hi : z.im*v.re-z.re*v.im = w.im := by
    have he := congrFun hw 1
    simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at he
    have he' : z.im*v.re + -z.re*v.im = w.im := by exact_mod_cast he
    linear_combination he'
  have he : P5570T1UnitQuadratic z (x+v) =
      P5570T1UnitQuadratic z x + x.re*w.re + x.im*w.im +
        P5570T1UnitQuadratic z v := hshift x
  rw [← hr, ← hi] at he
  linear_combination he

private theorem hquad :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (z : GaussianInt), ∀ (A : GaussianInt), ∀ (B : ℤ), (∀ (v :
            GaussianInt), P5570T1UnitQuadratic z (x+v) = P5570T1UnitQuadratic z x +
            P5570T1UnitQuadratic z v + ((1+z.re)*v.re+z.im*v.im)*x.re +
            (z.im*v.re-z.re*v.im)*x.im) → (FourNeighborLaplacian (fun y => P5570T1UnitQuadratic
            z y + A.re*y.re + A.im*y.im + B) x = 1) ) := by
  classical
  intro x z A B translation
  have h1 := translation 1
  have hm1 := translation (-1)
  have hi := translation ⟨0,1⟩
  have hmi := translation (-⟨0,1⟩)
  simp only [sub_eq_add_neg, FourNeighborLaplacian]
  rw [h1,hm1,hi,hmi]
  norm_num [P5570T1UnitQuadratic]
  ring

private theorem hposAt619 :
    (by
      classical
      exact
        (BandCircle) → ((ℕ) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
            (ProperBandQuadruple q) → ((¬(q i.succ).1 = (0 : ℤ)) → (0 < (q i.succ).1)))) ) := by
  classical
  intro C n q i hq hzero
  have hnonneg := (ProperBandCurvatureStructure q hq).2.1 i
  omega

private theorem hgf :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T₁ : ProtoTile), ∀ (h₁ : PartialOdometer), ∀ (g :
            IntegerLatticeFunction), (GlobalOdometerExtends g h₁) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (hq : ProperBandQuadruple q), ∀ (hpos : 0
            < (q i.succ).1),
        let Ci : BandCircle :=
          ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
        ∀ (U : ProtoTile), ∀ (f : PartialOdometer), (AncestorOdometer Ci.1.1 C.1.1 U T₁ f h₁) →
            (GlobalOdometerExtends g f)) ) := by
  classical
  intro C T₁ h₁ g hg₁ q i hq hpos Ci U f ha
  obtain ⟨c, hc⟩ := hg₁
  refine ⟨c, ?_⟩
  intro y hy
  rw [hc y (ha.2.2.2.1 hy), ha.2.2.2.2 y hy]

private abbrev hgk :=
  ApollonianSuperharmonic.LeftWebGeometry.hgf

private theorem hbelow :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (n : ℕ), (C.1.1.1.toNat = n) → ((¬C.1.1.1 = (1 : ℤ)) → (∀ (q : Fin
            (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (hq : ProperBandQuadruple q), (q
            (0 : Fin (4 : ℕ)) = C.1.1) → ((¬(q i.succ).1 = (1 : ℤ)) → ((¬(q i.succ).1 = (0 : ℤ))
            → (∀ (hpos : 0 < (q i.succ).1),
        let Ci : BandCircle :=
          ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
        Ci.1.1.1.toNat < n))))) ) := by
  classical
  intro C n hn hc q i hq hqC hunit hzero hpos Ci
  have hlt := hq.2 i
  rw [hqC] at hlt
  have hCpos := C.2
  change (q i.succ).1.toNat < n
  omega

end LeftWebGeometry

namespace LeftWebStep

private theorem positiveStep :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), (ℕ) → (∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (ProperBandQuadruple
            q) → ((q (0 : Fin (4 : ℕ)) = C.1.1) → (((q i.succ).1 = (1 : ℤ)) → ((0 < (q
            i.succ).1) → (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (f : PartialOdometer), ∀ (k :
                PartialOdometer), ∀ (p : Real × Real), ∀ (p' : Real × Real), (TileOdometer C.1.1
                U f) → ((TileOdometer
            C.1.1 V k) → ((PartialOdometerSlope f = some p) → ((PartialOdometerSlope k = some p')
            → ((TileCentroid V - TileCentroid U =
            GaussianRealPoint (BandVectors.1 (q i.succ) (q 0))) → ((p' - p = GaussianRealPoint
                (BandVectors.2 (q i.succ) (q 0))) → ((OdometerCompatibility f k) →
                ((GlobalOdometerExtends g f) → ((GlobalOdometerExtends g k) → ((x ∈ f.domain) →
                ((x ∈ k.domain) → ((∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
              y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
              y ∈ f.domain ∨ y ∈ k.domain) → (FourNeighborLaplacian g x = 1)))))))))))))))))) := by
  classical
  intro C g x n q i hq hqC hunit hpos U V f k p p' hOf hOk hpf hpk hcUV hpUV hcomp hgf hgk hxf
      hxk hcover
  let Ci : BandCircle :=
    ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
  classical
  obtain ⟨orientation, centerShift, base, Rminus, Rplus,
    tiles, reverseTiles, hs, reverseHs, hminus, hplus,
    pminus, pplus, a, b, bminus, bplus,
    hboundary, hminusCells, hplusCells, hcellPairs,
    hreverse, hrespect, hreverseRespect, hhead, hlast,
    hreverseHead, hreverseLast, hOminus, hOplus,
    hsminus, hsplus, hpminus, hpplus, houterReflection,
    hplusReflection, hminusReflection, hancestors, hreverseAncestors⟩ :=
    OpposingBoundaryOdometerStrings q hq C Ci i hqC rfl
      U V f k hOf hOk hpos p p' hpf hpk hcUV hpUV
  obtain ⟨r, hrproper, hrC, hrCi, hUband, horientation,
    hstring, hcminus, hcplus⟩ := hboundary
  -- The boundary string may use another proper presentation.
  have hforward : BandVectors.1 (r i.succ) (r 0) =
      BandVectors.1 (q i.succ) (q 0) := by rw [hrCi, hrC, hqC]
  have hbackward : BandVectors.1 (r 0) (r i.succ) =
      BandVectors.1 (q 0) (q i.succ) := by rw [hrCi, hrC, hqC]
  rw [hforward, hbackward] at hcminus hcplus
  have hU : BandPrototile (q 0) U := by simpa only [hqC] using hUband
  have hV : BandPrototile (q 0) V := by
    simpa only [hqC] using TileOdometerBandPrototile _ _ _ hOk
  have hRm : BandPrototile (q i.succ) Rminus :=
    TileOdometerBandPrototile _ _ _ hOminus
  have hRp : BandPrototile (q i.succ) Rplus :=
    TileOdometerBandPrototile _ _ _ hOplus
  have flip := ((VectorRecursionLaws q hq.1).2.2.2.2 hq i).1
  obtain ⟨Zm, hZm, hcZm⟩ :=
    P3996T1AdjacentParentPlacement q hq i 3 U hU
  obtain ⟨Zp, hZp, hcZp⟩ :=
    P3996T1AdjacentParentPlacement q hq i 0 U hU
  have hcminus3 : TileCentroid Rminus - TileCentroid U =
      (1 / 2 : Real) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ (3 : Fin 4).val *
          (BandVectors.1 (q i.succ) (q 0) +
            BandVectors.1 (q 0) (q i.succ))) := LeftWebGeometry.hcminus3 q i U Rminus
                hcminus flip
  have hmstep : (⟨0, 1⟩ : GaussianInt) ^ (3 : Fin 4).val *
      (if Even (3 : Fin 4).val then BandVectors.1 (q i.succ) (q 0)
        else BandVectors.1 (q 0) (q i.succ)) =
        BandVectors.1 (q i.succ) (q 0) := LeftWebGeometry.hmstep q i flip
  obtain ⟨Em, htouchm⟩ := BandOrientedChildParentIncomingEndpoint
    q hq i 3 U Rminus Zm hU hRm hZm
      (ProperBandCurvatureStructure q hq).1 hpos hcminus3 hcZm
  obtain ⟨Ep, htouchp⟩ := BandOrientedChildParentIncomingEndpoint
    q hq i 0 U Rplus Zp hU hRp hZp
      (ProperBandCurvatureStructure q hq).1 hpos (by simpa using hcplus) hcZp
  simp only [hmstep] at Em htouchm
  simp only [show (0 : Fin 4).val = 0 from rfl,
    show Even 0 by decide, pow_zero, ite_true, one_mul] at Ep htouchp
  let M := TileTranslation U (BandVectors.1 (q i.succ) (q 0))
  -- Identify observable middle-tile data, never ProtoTile records.
  obtain ⟨d, hcells, hanchor⟩ :=
    BandPrototileTranslationNormalForm (q 0) V U hV hU
  have hobs := ProtoTileObservableExtensionality _ _ hcells hanchor
  have hd : d = BandVectors.1 (q i.succ) (q 0) := LeftWebGeometry.hd q i U V hcUV d hobs
  subst d
  have hMV : M.cells = V.cells := hcells.symm
  have haMV : M.cells = ∅ → M.anchor = V.anchor := LeftWebGeometry.haMV q i U V
      hcells hanchor
  have hobsMV := ProtoTileObservableExtensionality M V hMV haMV
  obtain ⟨Eminus, hmPoint, hmAB, hmBC, hmCA⟩ :=
    ExactTileInterfaceTripleRetargetMiddle U M V Rminus hMV haMV Em
  obtain ⟨Eplus, hpPoint, hpAB, hpBC, hpCA⟩ :=
    ExactTileInterfaceTripleRetargetMiddle U M V Rplus hMV haMV Ep
  have hgeomU := BandTileSimultaneousInduction q hq U hU
  have hgeomV := BandTileSimultaneousInduction q hq V hV
  have hnV : V.cells ≠ ∅ := LeftWebGeometry.hnV C n q i hq U V hgeomV
  have touchingRetarget (W : ProtoTile) (ht : TouchingTriple U M W) :
      TouchingTriple U V W := LeftWebGeometry.touchingRetarget q i U V hMV hobsMV hnV
          W ht
  have htouchMinus := touchingRetarget Rminus htouchm
  have htouchPlus := touchingRetarget Rplus htouchp
  obtain ⟨um, hum⟩ := CurvatureOneBandPrototileSingleton Ci Rminus hunit hRm
  obtain ⟨up, hup⟩ := CurvatureOneBandPrototileSingleton Ci Rplus hunit hRp
  have hsingletonDisk (W : ProtoTile) (u : GaussianInt)
      (hu : W.cells = {u}) : LatticeTile W := LeftWebGeometry.hsingletonDisk W u hu
  have hdisjoint : Disjoint Rplus.cells Rminus.cells := LeftWebGeometry.hdisjoint q i
      hq U Rminus Rplus hcminus hcplus um hum up hup
  have hplusU : Disjoint U.cells Rplus.cells := LeftWebGeometry.hplusU U V Rplus
      htouchPlus up hup
  have hplusV : Disjoint V.cells Rplus.cells := LeftWebGeometry.hplusV U V Rplus hnV
      htouchPlus up hup
  obtain ⟨hEndpointNe, hCrossFirst, hCrossLast⟩ :=
    ExactTileInterfaceDisjointCompanionEndpoints U V Rplus Rminus
      Eplus Eminus hgeomU.1 hgeomV.1
      (hsingletonDisk Rplus up hup) (hsingletonDisk Rminus um hum)
      htouchPlus htouchMinus hplusU hplusV hdisjoint
  have hendpointCompat := P5589T1EndpointCompatibility q hq C Ci i hqC rfl
    U Rminus Rplus f k hminus hplus hOf hOminus hOplus p pminus pplus
    hpf hsminus hsplus hcminus hcplus hpminus hpplus
    centerShift a b bminus bplus houterReflection hplusReflection hminusReflection
  have hRS : Rminus ≠ Rplus := LeftWebGeometry.hRS Rminus Rplus up hup hdisjoint
  have hnorm : Zsqrtd.norm (BandVectors.1 (q 0) (q i.succ)) =
      (q 0).1+1 := LeftWebGeometry.hnorm q i hq hunit
  have hnadj : ¬ ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
      TileCentroid Rplus - TileCentroid Rminus = GaussianRealPoint v :=
          LeftWebGeometry.hnadj C n q i hq hunit hpos U V orientation base Rminus
          Rplus tiles reverseTiles hs reverseHs hreverse hrespect hreverseRespect r
          horientation hstring hcminus hcplus hnorm
  have hUn : U.cells.Nonempty := LeftWebGeometry.hUn q hq U V hgeomU hgeomV
  have hVn : V.cells.Nonempty := Finset.nonempty_iff_ne_empty.mpr hnV
  have hselection := P5589T1UnitInterfaceSelection C Ci hunit orientation
    base Rminus Rplus U V tiles reverseTiles hs reverseHs hminus hplus f k
    hOf hOk hUn hVn hrespect hreverseRespect hhead hlast hRS hnadj
    hancestors hreverseAncestors Eminus Eplus htouchMinus htouchPlus
    hCrossLast x hxf hxk
  obtain ⟨z,hz⟩ := CurvatureOneBandCircleClassification Ci hunit
  have hCiunit : Ci.1.1.1 = 1 := hunit
  obtain ⟨A,B,hvalues⟩ := P5589T1LinkedUnitValues C Ci z hz orientation
    base Rminus Rplus U V tiles reverseTiles hs reverseHs hminus hplus f k
    g x hrespect hreverseRespect hhead hlast hreverseLast hgf hgk hxf hxk
    hendpointCompat hcover hselection
  have hmatrix : CircleMatrix Ci =
      ![![((1+z.re : ℤ) : ℝ), (z.im : ℝ)],
        ![(z.im : ℝ), (-z.re : ℝ)]] := LeftWebGeometry.hmatrixAt529 q i hq hpos z hz
            hCiunit
  have hperiodic := CurvatureOnePeriodicOdometer Ci z hz
  have translation (v : GaussianInt) :
      P5570T1UnitQuadratic z (x+v) =
        P5570T1UnitQuadratic z x + P5570T1UnitQuadratic z v +
        ((1+z.re)*v.re+z.im*v.im)*x.re +
        (z.im*v.re-z.re*v.im)*x.im := LeftWebGeometry.translationAt543 g x q i hq
            hpos z hCiunit hmatrix hperiodic v
  have hquad : FourNeighborLaplacian
      (fun y => P5570T1UnitQuadratic z y + A.re*y.re + A.im*y.im + B) x = 1 :=
          LeftWebGeometry.hquad x z A B translation
  simpa only [FourNeighborLaplacian,
    hvalues x (Or.inl rfl),
    hvalues (x+1) (Or.inr (Or.inl rfl)),
    hvalues (x-1) (Or.inr (Or.inr (Or.inl rfl))),
    hvalues (x+⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hvalues (x-⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))] using hquad

end LeftWebStep

theorem P5596T1LeftWeb
    (C : BandCircle) (T₁ T₂ : ProtoTile) (h₁ h₂ : PartialOdometer)
    (g : IntegerLatticeFunction) (x : GaussianInt)
    (hcompat : OdometerCompatibility h₁ h₂)
    (hg₁ : GlobalOdometerExtends g h₁) (hg₂ : GlobalOdometerExtends g h₂)
    (hx₁ : x ∈ h₁.domain) (hx₂ : x ∈ h₂.domain)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h₁.domain ∨ y ∈ h₂.domain)
    (hleft : LeftLatticeAdjacent C T₁ T₂ h₁ h₂) :
    FourNeighborLaplacian g x = 1 := by
-- BODY
  have left : ∀ n : Nat,
      ∀ (C : BandCircle) (T₁ T₂ : ProtoTile) (h₁ h₂ : PartialOdometer)
        (g : IntegerLatticeFunction) (x : GaussianInt),
      C.1.1.1.toNat = n →
      OdometerCompatibility h₁ h₂ →
      GlobalOdometerExtends g h₁ → GlobalOdometerExtends g h₂ →
      x ∈ h₁.domain → x ∈ h₂.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h₁.domain ∨ y ∈ h₂.domain) →
      LeftLatticeAdjacent C T₁ T₂ h₁ h₂ → FourNeighborLaplacian g x = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C T₁ T₂ h₁ h₂ g x hn hcompat hg₁ hg₂ hx₁ hx₂ hstar hleft
      by_cases hc : C.1.1.1 = 1
      · obtain ⟨z, hz⟩ := CurvatureOneBandCircleClassification C hc
        obtain ⟨ht₁, ht₂, p₁, p₂, hp₁, hp₂, hstep⟩ := hleft
        have hdata := LeftWebGeometry.hdata C T₁ T₂ n hc p₁ p₂ hstep
        obtain ⟨v, hv, hr, hi⟩ := hdata
        obtain ⟨u₁, a₁, b₁, hu₁, hd₁, hcent₁, hval₁, hs₁⟩ :=
          P5570T1UnitNormalForm C z T₁ h₁ hz ht₁
        obtain ⟨u₂, a₂, b₂, hu₂, hd₂, hcent₂, hval₂, hs₂⟩ :=
          P5570T1UnitNormalForm C z T₂ h₂ hz ht₂
        have hmatrix : CircleMatrix C =
            ![![((1 + z.re : ℤ) : ℝ), (z.im : ℝ)],
              ![(z.im : ℝ), (-z.re : ℝ)]] := LeftWebGeometry.hmatrixAt187 C z hz
        have hpr₁ := Option.some.inj (hp₁.symm.trans hs₁)
        have hpr₂ := Option.some.inj (hp₂.symm.trans hs₂)
        subst p₁
        subst p₂
        rw [hcent₁, hcent₂] at hv
        have hvr := congrArg Prod.fst hv
        have hvi := congrArg Prod.snd hv
        dsimp [GaussianRealPoint] at hvr hvi
        have hvr' : (v.re : ℝ) = (u₂.re : ℝ) - (u₁.re : ℝ) := by linarith
        have hvi' : (v.im : ℝ) = (u₂.im : ℝ) - (u₁.im : ℝ) := by linarith
        rw [hmatrix] at hr hi
        norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one] at hr hi
        rw [hvr', hvi'] at hr hi
        have ha := LeftWebGeometry.haAt220 a₁ a₂ (LeftWebGeometry.har z u₁ a₁ u₂ a₂ hr)
            (LeftWebGeometry.hai z u₁ a₁ u₂ a₂ hi)
        subst a₂
        obtain ⟨c₁, hg₁⟩ := hg₁
        obtain ⟨c₂, hg₂⟩ := hg₂
        have hb := LeftWebGeometry.hbAt227 h₁ h₂ g x c₁ hg₁ c₂ hg₂ hx₁ hx₂ z a₁ b₁ hval₁ b₂
            hval₂
        have hvalues (y : GaussianInt)
            (hy : y = x ∨ y = x + 1 ∨ y = x - 1 ∨
              y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) :
            g y = P5570T1UnitQuadratic z y +
              a₁.re * y.re + a₁.im * y.im + (b₁ + c₁) := LeftWebGeometry.hvalues h₁ h₂ g x c₁
                  hg₁ c₂
                  hg₂ hstar z a₁ b₁ hval₁ b₂ hval₂ hb y hy
        have hperiodic := CurvatureOnePeriodicOdometer C z hz
        have hq : FourNeighborLaplacian
            (fun y => P5570T1UnitQuadratic z y +
              a₁.re * y.re + a₁.im * y.im + (b₁ + c₁)) x = 1 := LeftWebGeometry.hq x z a₁ b₁ c₁
                  (LeftWebGeometry.translationAt244 C g x hc z hmatrix hperiodic)
        simpa only [FourNeighborLaplacian,
          hvalues x (Or.inl rfl),
          hvalues (x + 1) (Or.inr (Or.inl rfl)),
          hvalues (x - 1) (Or.inr (Or.inr (Or.inl rfl))),
          hvalues (x + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
          hvalues (x - ⟨0, 1⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))] using hq
      · have horiginal := hleft
        obtain ⟨hO₁, hO₂, p₁, p₂, hp₁, hp₂, hstep⟩ := hleft
        rcases hstep with hunit | ⟨q, i, e, hq, hqC, hcent, hr, hi⟩
        · exact (hc hunit.1).elim
        · by_cases hunit : (q i.succ).1 = 1
          · have hpos : 0 < (q i.succ).1 := by rw [hunit]; norm_num
            let Ci : BandCircle :=
              ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
            have positiveStep (U V : ProtoTile) (f k : PartialOdometer)
                (p p' : Real × Real)
                (hOf : TileOdometer C.1.1 U f) (hOk : TileOdometer C.1.1 V k)
                (hpf : PartialOdometerSlope f = some p)
                (hpk : PartialOdometerSlope k = some p')
                (hcUV : TileCentroid V - TileCentroid U =
                  GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
                (hpUV : p' - p = GaussianRealPoint (BandVectors.2 (q i.succ) (q 0)))
                (hcomp : OdometerCompatibility f k)
                (hgf : GlobalOdometerExtends g f) (hgk : GlobalOdometerExtends g k)
                (hxf : x ∈ f.domain) (hxk : x ∈ k.domain)
                (hcover : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
                    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                    y ∈ f.domain ∨ y ∈ k.domain) :
                FourNeighborLaplacian g x = 1 := LeftWebStep.positiveStep C g x n q i hq hqC
                    hunit hpos U V f k p p' hOf hOk hpf hpk hcUV hpUV hcomp hgf hgk hxf hxk hcover
            cases e
            · apply positiveStep T₂ T₁ h₂ h₁ p₂ p₁ hO₂ hO₁ hp₂ hp₁
              · simp only [Bool.false_eq_true, ite_false, neg_one_smul] at hcent
                linear_combination -hcent
              · apply Prod.ext
                · simp only [Bool.false_eq_true, ite_false, neg_one_mul] at hr
                  simpa [GaussianRealPoint] using (show p₁.1 - p₂.1 =
                    ((BandVectors.2 (q i.succ) (q 0)).re : Real) by linarith)
                · simp only [Bool.false_eq_true, ite_false, neg_one_mul] at hi
                  simpa [GaussianRealPoint] using (show p₁.2 - p₂.2 =
                    ((BandVectors.2 (q i.succ) (q 0)).im : Real) by linarith)
              · rcases hcompat with hd | ⟨c, hh⟩
                · exact Or.inl hd.symm
                · exact Or.inr ⟨-c, fun y hy₂ hy₁ => by
                    have := hh y hy₁ hy₂
                    omega⟩
              · exact hg₂
              · exact hg₁
              · exact hx₂
              · exact hx₁
              · intro y hy
                exact (hstar y hy).symm
            · apply positiveStep T₁ T₂ h₁ h₂ p₁ p₂ hO₁ hO₂ hp₁ hp₂
              · simpa using hcent
              · apply Prod.ext
                · simpa [GaussianRealPoint] using hr
                · simpa [GaussianRealPoint] using hi
              · exact hcompat
              · exact hg₁
              · exact hg₂
              · exact hx₁
              · exact hx₂
              · exact hstar
          · by_cases hzero : (q i.succ).1 = 0
            · exact P5596T1LineParent q hq i e hzero T₁ T₂ h₁ h₂ p₁ p₂ g x
                (by simpa only [hqC] using hO₁) (by simpa only [hqC] using hO₂)
                hp₁ hp₂ hcent hr hi hg₁ hg₂ hx₁ hx₂ hstar
            · have hpos : 0 < (q i.succ).1 := LeftWebGeometry.hposAt619 C n q i hq hzero
              let Ci : BandCircle :=
                ⟨⟨q i.succ, Or.inl hpos, q, hq.1, i.succ, rfl⟩, hpos⟩
              have hlarge : 1 < Ci.1.1.1 := by change 1 < (q i.succ).1; omega
              obtain ⟨U, V, f, k, ha, hb, hadj, hxf, hxk, hcover⟩ :=
                (LeftAdjacentOdometerCompatibility C T₁ T₂ h₁ h₂ horiginal).2
                  q hq i e Ci hqC rfl hlarge hcent x hx₁ hx₂ hstar
              have hgf : GlobalOdometerExtends g f := LeftWebGeometry.hgf C T₁ h₁ g hg₁ q i hq
                  hpos U f ha
              have hgk : GlobalOdometerExtends g k := LeftWebGeometry.hgk C T₂ h₂ g hg₂ q i hq
                  hpos V k hb
              exact ih Ci.1.1.1.toNat (LeftWebGeometry.hbelow C n hn hc q i hq hqC hunit hzero
                  hpos) Ci U V f k g x rfl
                (LeftAdjacentOdometerCompatibility Ci U V f k hadj).1
                hgf hgk hxf hxk hcover hadj
  exact left C.1.1.1.toNat C T₁ T₂ h₁ h₂ g x rfl
    hcompat hg₁ hg₂ hx₁ hx₂ hstar hleft

end ApollonianSuperharmonic

end

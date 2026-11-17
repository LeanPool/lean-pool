/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.DiamondTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness

-- [TABLET NODE: DiamondOpposingBoundaryStarLocalization]

/-!
# DiamondOpposingBoundaryStarLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondBoundaryStarGeometry

private theorem hcurv :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (Ci : BandCircle), ∀ (i : Fin 3), (DiamondRecursiveQuadruple
            K i.succ = Ci.1.1) → (((1 : ℤ) < Ci.1.1.1) → (1 < (DiamondRecursiveQuadruple K
            (i.succ)).1)) ) := by
  classical
  intro K Ci i hCi hlarge
  rw [hCi]
  exact hlarge

private theorem index_two :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              DiamondRecursiveQuadruple K i.succ = Ci.1.1 →
                1 < (DiamondRecursiveQuadruple K i.succ).1 → i = 2
    ) := by
  classical
  intro K Ci i hCi hcurv
  fin_cases i
  · simp [DiamondRecursiveQuadruple] at hcurv
  · simp [DiamondRecursiveQuadruple] at hcurv
  · rfl

private theorem hk2 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          (1 : ℤ) < (DiamondRecursiveQuadruple K (Fin.succ (2 : Fin (3 : ℕ)))).1 →
            0 < K.1 → 2 ≤ K.1
    ) := by
  classical
  intro K hcurv hKpos
  by_contra hnot
  have hone : K.1 = 1 := by omega
  simp [DiamondRecursiveQuadruple, hone] at hcurv

private theorem hC0pos :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), (ProperBandQuadruple (DiamondRecursiveQuadruple K)) → (∀ (C0 :
            BandCircle), (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ)) = C0.1.1) → (
        0 < C0.1.1.1)) ) := by
  classical
  intro K hq C0 hC0
  let q := DiamondRecursiveQuadruple K
  rw [← hC0]
  exact (ProperBandCurvatureStructure q hq).1

private theorem hrootCell :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          0 < K.1 → 2 ≤ K.1 → (⟨0, 0⟩ : GaussianInt) ∈ DiamondCellDomain K.1
    ) := by
  classical
  intro K hKpos hk2
  simp only [DiamondCellDomain, Finset.mem_biUnion]
  refine ⟨0, by simp [hKpos], ?_⟩
  have hr : Nat.min (0 + 1) (2 * K.1 - 0) = 1 := by
    simp only [Nat.zero_add, Nat.sub_zero]
    exact Nat.min_eq_left (by omega : 1 ≤ 2 * K.1)
  rw [hr]
  simp only [Finset.mem_image]
  refine ⟨1, by simp, ?_⟩
  simp

private theorem hT0ne :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0 : ProtoTile), ∀ (u : GaussianInt), (T0.cells =
            (TileTranslation (DiamondTile K.1) u).cells) → (((DiamondTile K.1).cells.Nonempty) →
            (T0.cells.Nonempty)) ) := by
  classical
  intro K T0 u huCell hrootNonempty
  rw [huCell]
  exact Finset.image_nonempty.mpr hrootNonempty

private abbrev hT0'ne := ApollonianSuperharmonic.DiamondBoundaryStarGeometry.hT0ne

private theorem hT0cent :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0 : ProtoTile), ∀ (u : GaussianInt), (T0.cells =
            (TileTranslation (DiamondTile K.1) u).cells) → ((T0.cells.Nonempty) → (TileCentroid
            T0 = TileCentroid (DiamondTile K.1) + GaussianRealPoint u)) ) := by
  classical
  intro K T0 u huCell hT0ne
  have htrne : (TileTranslation (DiamondTile K.1) u).cells.Nonempty := by
    rw [← huCell]
    exact hT0ne
  have hc : TileCentroid T0 = TileCentroid (TileTranslation (DiamondTile K.1) u) := by
    unfold TileCentroid
    rw [ite_eq_left hT0ne, ite_eq_left htrne, huCell]
  rw [hc, (TileTranslationFormulas (DiamondTile K.1) u).2.2.2.2.1]
  rfl

private abbrev hT0'cent :=
  ApollonianSuperharmonic.DiamondBoundaryStarGeometry.hT0cent

private theorem hshift :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), (BandVectors.1
            (DiamondRecursiveQuadruple K (3 : Fin (4 : ℕ))) (DiamondRecursiveQuadruple K (0 : Fin
            (4 : ℕ))) = (⟨(0 : ℤ), -((2 : ℤ) * (↑K.1 : ℤ))⟩ : GaussianInt)) → ((TileCentroid T0'
            - TileCentroid T0 = GaussianRealPoint (BandVectors.1 (DiamondRecursiveQuadruple K
            (Fin.succ (2 : Fin (3 : ℕ)))) (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ))))) → (∀
            (u : GaussianInt), ∀ (u' : GaussianInt), (TileCentroid T0 = TileCentroid (DiamondTile
            K.1) + GaussianRealPoint u) → ((TileCentroid T0' = TileCentroid (DiamondTile K.1) +
            GaussianRealPoint u') → (u' - u = (⟨0, -(2 * (K.1 : Int))⟩ : GaussianInt))))) ) := by
  classical
  intro K T0 T0' hv30 hcentroid u u' hT0cent hT0'cent
  have hv30' : BandVectors.1 (DiamondRecursiveQuadruple K (Fin.succ 2))
      (DiamondRecursiveQuadruple K 0) = ⟨0, -(2 * (K.1 : Int))⟩ := by
    simpa using hv30
  have hh := hcentroid
  rw [hT0'cent, hT0cent, hv30'] at hh
  have hr' : (u'.re : ℝ) - u.re = 0 := by
    have h := congrArg Prod.fst hh
    simp only [GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re,
        GaussianInt.intCast_im, add_sub_add_left_eq_sub, Prod.mk_sub_mk, Int.cast_zero,
        Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at h
    rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_re] at h
    linarith
  have hi' : (u'.im : ℝ) - u.im = -(2 * (K.1 : Int)) := by
    have h := congrArg Prod.snd hh
    simp only [GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re,
        GaussianInt.intCast_im, add_sub_add_left_eq_sub, Prod.mk_sub_mk, Int.cast_zero,
        Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at h
    rw [← GaussianInt.intCast_im, ← GaussianInt.intCast_im] at h
    push_cast at h ⊢
    simpa [GaussianInt.intCast_im] using h
  have hr : (u' - u).re = 0 := by
    have h : u'.re - u.re = 0 := by exact_mod_cast hr'
    simpa [Zsqrtd.re_sub] using h
  have hi : (u' - u).im = -(2 * (K.1 : Int)) := by
    have h : u'.im - u.im = -(2 * (K.1 : Int)) := by exact_mod_cast hi'
    simpa [Zsqrtd.im_sub] using h
  apply Zsqrtd.ext
  · exact hr
  · exact hi

private theorem hshift' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt), ∀ (u' : GaussianInt), (u' - u = (⟨0, -(2 *
            (K.1 : Int))⟩ : GaussianInt)) → (u - u' = (⟨0, 2 * (K.1 : Int)⟩ : GaussianInt)) ) := by
  classical
  intro K u u' hshift
  apply Zsqrtd.ext
  · have h := congrArg (fun w : GaussianInt => -w) hshift
    simpa using congrArg (fun w : GaussianInt => w.re) h
  · have h := congrArg (fun w : GaussianInt => -w) hshift
    simpa using congrArg (fun w : GaussianInt => w.im) h

private theorem Hmem :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (H : PartialOdometer), ((↑H.domain : Set GaussianInt) =
            DiamondVertexDomains K false) → (∀ (w : GaussianInt), w ∈ H.domain ↔ w ∈
            DiamondVertexDomains K false) ) := by
  classical
  intro K H hHdom w
  have hh := Set.ext_iff.mp hHdom w
  simpa using hh

private theorem hzUpper :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (h0 : PartialOdometer), ∀ (x : GaussianInt), (x ∈ h0.domain)
            → (∀ (H : PartialOdometer), ∀ (u : GaussianInt), (∀ (x : GaussianInt), x ∈ h0.domain
            ↔ x - u ∈ H.domain) → ((∀ (w : GaussianInt), w ∈ H.domain ↔ w ∈ DiamondVertexDomains
            K false) → (
        let z := x - u
        z ∈ DiamondVertexDomains K false))) ) := by
  classical
  intro K h0 x hx0 H u huDom Hmem z
  have hx := (huDom x).mp hx0
  exact (Hmem (x - u)).mp (by simpa using hx)

private theorem hzLower :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (h0' : PartialOdometer), ∀ (x : GaussianInt), (x ∈
            h0'.domain) → (∀ (H : PartialOdometer), ∀ (u : GaussianInt), ∀ (u' : GaussianInt), (∀
            (x : GaussianInt), x ∈ h0'.domain ↔ x - u' ∈ H.domain) → ((u - u' = (⟨0, 2 * (K.1 :
            Int)⟩ : GaussianInt)) → ((∀ (w : GaussianInt), w ∈ H.domain ↔ w ∈
            DiamondVertexDomains K false) → (
        let z := x - u
        z + ⟨0, 2 * (K.1 : Int)⟩ ∈ DiamondVertexDomains K false)))) ) := by
  classical
  intro K h0' x hx0' H u u' hu'Dom hshift' Hmem z
  have hx := (hu'Dom x).mp hx0'
  have heq : x - u' = z + ⟨0, 2 * (K.1 : Int)⟩ := by
    calc
      x - u' = (x - u) + (u - u') := by abel
      _ = z + ⟨0, 2 * (K.1 : Int)⟩ := by rw [hshift']
  rw [heq] at hx
  exact (Hmem (z + ⟨0, 2 * (K.1 : Int)⟩)).mp (by simpa using hx)

private theorem overlap :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (x : GaussianInt),
            2 ≤ K.1 →
              ∀ (u : GaussianInt),
                let z := x - u
                z ∈ DiamondVertexDomains K false →
                  z + ⟨0, 2 * (K.1 : Int)⟩ ∈ DiamondVertexDomains K false →
                    z.im = 0 ∧ Int.natAbs z.re ≤ 1
    ) := by
  classical
  intro K x hk2 u z hzUpper hzLower
  change max (Int.natAbs z.re)
    (max (Int.natAbs (z.im - (K.1 : Int)))
      (Int.natAbs z.re + Int.natAbs (z.im - (K.1 : Int)) - 1)) ≤ K.1 at hzUpper
  change max (Int.natAbs (z.re + 0))
    (max (Int.natAbs (z.im + 2 * (K.1 : Int) - (K.1 : Int)))
      (Int.natAbs (z.re + 0) +
        Int.natAbs (z.im + 2 * (K.1 : Int) - (K.1 : Int)) - 1)) ≤ K.1 at hzLower
  simp only [max_le_iff, add_zero] at hzUpper hzLower
  omega

private theorem hwest :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (h0 : PartialOdometer), ∀ (h0' : PartialOdometer), ∀ (x :
            GaussianInt), (∀ (y : GaussianInt), y = x ∨ y = x + (1 : GaussianInt) ∨ y = x - (1 :
            GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) → y ∈ h0.domain ∨ y ∈ h0'.domain) → (∀ (H : PartialOdometer), ∀ (u
            : GaussianInt), (∀ (x : GaussianInt), x ∈ h0.domain ↔ x - u ∈ H.domain) → (∀ (u' :
            GaussianInt), (∀ (x : GaussianInt), x ∈ h0'.domain ↔ x - u' ∈ H.domain) → ((u - u' =
            (⟨0, 2 * (K.1 : Int)⟩ : GaussianInt)) → ((∀ (w : GaussianInt), w ∈ H.domain ↔ w ∈
            DiamondVertexDomains K false) → (
        let z := x - u
        z - 1 ∈ DiamondVertexDomains K false ∨ z - 1 + ⟨0, 2 * (K.1 : Int)⟩ ∈
            DiamondVertexDomains K false))))) ) := by
  classical
  intro K h0 h0' x hstar H u huDom u' hu'Dom hshift' Hmem z
  have hs := hstar (x - 1) (by simp)
  rcases hs with hs | hs
  · left
    have := (huDom (x - 1)).mp hs
    simpa [z, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (Hmem (x - 1 - u)).mp (by simpa using this)
  · right
    have := (hu'Dom (x - 1)).mp hs
    have heq : (x - 1) - u' = (z - 1) + ⟨0, 2 * (K.1 : Int)⟩ := by
      calc
        (x - 1) - u' = (x - u) - 1 + (u - u') := by abel
        _ = (z - 1) + ⟨0, 2 * (K.1 : Int)⟩ := by rw [hshift']
    rw [heq] at this
    exact (Hmem (z - 1 + ⟨0, 2 * (K.1 : Int)⟩)).mp (by simpa using this)

private theorem heast :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (h0 : PartialOdometer), ∀ (h0' : PartialOdometer), ∀ (x :
            GaussianInt), (∀ (y : GaussianInt), y = x ∨ y = x + (1 : GaussianInt) ∨ y = x - (1 :
            GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) → y ∈ h0.domain ∨ y ∈ h0'.domain) → (∀ (H : PartialOdometer), ∀ (u
            : GaussianInt), (∀ (x : GaussianInt), x ∈ h0.domain ↔ x - u ∈ H.domain) → (∀ (u' :
            GaussianInt), (∀ (x : GaussianInt), x ∈ h0'.domain ↔ x - u' ∈ H.domain) → ((u - u' =
            (⟨0, 2 * (K.1 : Int)⟩ : GaussianInt)) → ((∀ (w : GaussianInt), w ∈ H.domain ↔ w ∈
            DiamondVertexDomains K false) → (
        let z := x - u
        z + 1 ∈ DiamondVertexDomains K false ∨ z + 1 + ⟨0, 2 * (K.1 : Int)⟩ ∈
            DiamondVertexDomains K false))))) ) := by
  classical
  intro K h0 h0' x hstar H u huDom u' hu'Dom hshift' Hmem z
  have hs := hstar (x + 1) (by simp)
  rcases hs with hs | hs
  · left
    have := (huDom (x + 1)).mp hs
    simpa [z, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (Hmem (x + 1 - u)).mp (by simpa using this)
  · right
    have := (hu'Dom (x + 1)).mp hs
    have heq : (x + 1) - u' = (z + 1) + ⟨0, 2 * (K.1 : Int)⟩ := by
      calc
        (x + 1) - u' = (x - u) + 1 + (u - u') := by abel
        _ = (z + 1) + ⟨0, 2 * (K.1 : Int)⟩ := by rw [hshift']
    rw [heq] at this
    exact (Hmem (z + 1 + ⟨0, 2 * (K.1 : Int)⟩)).mp (by simpa using this)

private theorem hzzero :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (x : GaussianInt),
            2 ≤ K.1 →
              ∀ (u : GaussianInt),
                let z := x - u
                z.im = 0 ∧ Int.natAbs z.re ≤ 1 →
                  z - 1 ∈ DiamondVertexDomains K false ∨
                      z - 1 + ⟨0, 2 * (K.1 : Int)⟩ ∈ DiamondVertexDomains K false →
                    z + 1 ∈ DiamondVertexDomains K false ∨
                        z + 1 + ⟨0, 2 * (K.1 : Int)⟩ ∈ DiamondVertexDomains K false →
                      z = 0
    )
            := by
  classical
  intro K x hk2 u z overlap hwest heast
  obtain ⟨hy, hx⟩ := overlap
  let bound (w : GaussianInt) : Prop := max (Int.natAbs w.re)
    (max (Int.natAbs (w.im - (K.1 : Int)))
      (Int.natAbs w.re + Int.natAbs (w.im - (K.1 : Int)) - 1)) ≤ K.1
  change bound (z - 1) ∨ bound (z - 1 + ⟨0, 2 * (K.1 : Int)⟩) at hwest
  change bound (z + 1) ∨ bound (z + 1 + ⟨0, 2 * (K.1 : Int)⟩) at heast
  simp only [bound, max_le_iff, Zsqrtd.re_sub, Zsqrtd.im_sub,
    Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
    add_zero, sub_zero, hy] at hwest heast
  apply Zsqrtd.ext
  · change z.re = 0
    omega
  · exact hy

private theorem hx_eq_u :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (u : GaussianInt),
        let z := x - u
        (z = 0) → (x = u) ) := by
  classical
  intro x u z hzzero
  dsimp [z] at hzzero
  exact sub_eq_zero.mp hzzero

private theorem hroot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let q := DiamondRecursiveQuadruple K
        (2 ≤ K.1) → (1 < (q 0).1) ) := by
  classical
  intro K q hk2
  have hn : (1 : ℕ) < 2 * K.1 * (K.1 + 1) := by nlinarith [hk2]
  change (1 : ℤ) < (2 * K.1 * (K.1 + 1) : ℕ)
  exact_mod_cast hn

private theorem hATU :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle),
            (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ)) = C0.1.1) → (∀ (T0 : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        (ProperBandQuadruple q) → ((DiamondRecursiveQuadruple K (Fin.succ (2 : Fin (3 : ℕ))) =
            Ci.1.1) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gS : Fin (3 : ℕ) → Bool →
            PartialOdometer), (BandPrototile (q (0 : Fin (4 : ℕ))) T0) → ((∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), TileOdometer (q i.succ) (S i s) (gS i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), FootprintVertices (S i s) ⊆ FootprintVertices T0) → ((∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), TileCentroid (S i s) - TileCentroid T0 = (if s = true then (1 : ℝ) else
            (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).1))) → (
        let U := S 2 false
        AncestorTile Ci.1.1 C0.1.1 U T0))))))) ) := by
  classical
  intro K C0 Ci hC0 T0 q hqD hCi S gS hband0 hsub0 hfoot0 hcent0 U
  unfold AncestorTile
  apply Relation.ReflTransGen.single
  refine ⟨q, 2, false, hqD, ?_, ?_, ?_, ?_, hfoot0 2 false, ?_⟩
  · exact hC0
  · exact hCi
  · exact (by simpa only [← hC0] using hband0)
  · have hb := TileOdometerBandPrototile _ _ _ (hsub0 2 false)
    simpa only [← hCi] using hb
  · exact hcent0 2 false

private theorem hATV :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle),
            (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ)) = C0.1.1) → (∀ (T0' : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        (ProperBandQuadruple q) → ((DiamondRecursiveQuadruple K (Fin.succ (2 : Fin (3 : ℕ))) =
            Ci.1.1) → (∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gS' : Fin (3 : ℕ) → Bool →
            PartialOdometer), (BandPrototile (q (0 : Fin (4 : ℕ))) T0') → ((∀ (i : Fin (3 : ℕ)),
            ∀ (s : Bool), TileOdometer (q i.succ) (S' i s) (gS' i s)) → ((∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), FootprintVertices (S' i s) ⊆ FootprintVertices T0') → ((∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileCentroid (S' i s) - TileCentroid T0' = (if s = true then (1 :
            ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin
            (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).1))) → (
        let V := S' 2 true
        AncestorTile Ci.1.1 C0.1.1 V T0'))))))) ) := by
  classical
  intro K C0 Ci hC0 T0' q hqD hCi S' gS' hband0' hsub0' hfoot0' hcent0' V
  unfold AncestorTile
  apply Relation.ReflTransGen.single
  refine ⟨q, 2, true, hqD, ?_, ?_, ?_, ?_, hfoot0' 2 true, ?_⟩
  · exact hC0
  · exact hCi
  · exact (by simpa only [← hC0] using hband0')
  · have hb := TileOdometerBandPrototile _ _ _ (hsub0' 2 true)
    simpa only [← hCi] using hb
  · exact hcent0' 2 true

private theorem hAncU :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle),
            (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ)) = C0.1.1) → (∀ (T0 : ProtoTile), ∀ (h0
            : PartialOdometer), (TileOdometer C0.1.1 T0 h0) → (
        let q := DiamondRecursiveQuadruple K
        (DiamondRecursiveQuadruple K (Fin.succ (2 : Fin (3 : ℕ))) = Ci.1.1) → (∀ (S : Fin (3 : ℕ)
            → Bool → ProtoTile), ∀ (gS : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (S i s) (gS i s)) → ((∀ (x : GaussianInt),
            x ∈ h0.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (gS i s).domain) → ((∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (gS i s).domain, h0.value x = (gS i s).value x) → (
        let U := S 2 false
        let g := gS 2 false
        (0 < Ci.1.1.1) → ((AncestorTile Ci.1.1 C0.1.1 U T0) → (AncestorOdometer Ci.1.1 C0.1.1 U
            T0 g h0)))))))) ) := by
  classical
  intro K C0 Ci hC0 T0 h0 hO0 q hCi S gS hsub0 hdom0 hvalue0 U g hCiPos hATU
  refine ⟨by simpa only [← hC0] using hO0, hATU, ?_, ?_, ?_⟩
  · exact PositiveCurvatureTileOdometerDomain Ci.1.1 U g hCiPos
      (by simpa only [← hCi] using hsub0 2 false)
  · intro y hy
    exact (hdom0 y).mpr ⟨2, false, hy⟩
  · intro y hy
    exact (hvalue0 2 false y hy).symm

private theorem hAncV :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle),
            (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ)) = C0.1.1) → (∀ (T0' : ProtoTile), ∀
            (h0' : PartialOdometer), (TileOdometer C0.1.1 T0' h0') → (
        let q := DiamondRecursiveQuadruple K
        (DiamondRecursiveQuadruple K (Fin.succ (2 : Fin (3 : ℕ))) = Ci.1.1) → (∀ (S' : Fin (3 :
            ℕ) → Bool → ProtoTile), ∀ (gS' : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (S' i s) (gS' i s)) → ((∀ (x :
            GaussianInt), x ∈ h0'.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (gS' i s).domain)
            → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (gS' i s).domain, h0'.value x = (gS' i
            s).value x) → (
        let V := S' 2 true
        let k := gS' 2 true
        (0 < Ci.1.1.1) → ((AncestorTile Ci.1.1 C0.1.1 V T0') → (AncestorOdometer Ci.1.1 C0.1.1 V
            T0' k h0')))))))) ) := by
  classical
  intro K C0 Ci hC0 T0' h0' hO0' q hCi S' gS' hsub0' hdom0' hvalue0' V k hCiPos hATV
  refine ⟨by simpa only [← hC0] using hO0', hATV, ?_, ?_, ?_⟩
  · exact PositiveCurvatureTileOdometerDomain Ci.1.1 V k hCiPos
      (by simpa only [← hCi] using hsub0' 2 true)
  · intro y hy
    exact (hdom0' y).mpr ⟨2, true, hy⟩
  · intro y hy
    exact (hvalue0' 2 true y hy).symm

private theorem hUcent :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0 : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        ∀ (u : GaussianInt), (TileCentroid T0 = TileCentroid (DiamondTile K.1) +
            GaussianRealPoint u) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)),
            ∀ (s : Bool), TileCentroid (S i s) - TileCentroid T0 = (if s = true then (1 : ℝ) else
            (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).1))) → (
        let U := S 2 false
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence (DiamondRecursiveQuadruple K) (DiamondTile K.1) i s (Sc i s)) →
            (TileCentroid U = TileCentroid (TileTranslation (Sc 2 false) u)))) ) := by
  classical
  intro K T0 q u hT0cent S hcent0 U Sc hOcc
  have ha := hcent0 2 false
  have hb := (hOcc 2 false).2.2
  have ht := (TileTranslationFormulas (Sc 2 false) u).2.2.2.2.1
  have hdelta : TileCentroid U - TileCentroid T0 =
      TileCentroid (Sc 2 false) - TileCentroid (DiamondTile K.1) := by
    rw [ha, hb]
  calc
    TileCentroid U = (TileCentroid U - TileCentroid T0) + TileCentroid T0 := by abel
    _ = (TileCentroid (Sc 2 false) - TileCentroid (DiamondTile K.1)) +
          (TileCentroid (DiamondTile K.1) + GaussianRealPoint u) := by
            rw [hdelta, hT0cent]
    _ = TileCentroid (TileTranslation (Sc 2 false) u) := by
          rw [ht]
          apply Prod.ext <;> simp [GaussianRealPoint] <;> ring

private theorem hVcent :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0' : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        ∀ (u' : GaussianInt), (TileCentroid T0' = TileCentroid (DiamondTile K.1) +
            GaussianRealPoint u') → (∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileCentroid (S' i s) - TileCentroid T0' = (if s = true then (1 :
            ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin
            (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).1))) → (
        let V := S' 2 true
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence (DiamondRecursiveQuadruple K) (DiamondTile K.1) i s (Sc i s)) →
            (TileCentroid V = TileCentroid (TileTranslation (Sc 2 true) u')))) ) := by
  classical
  intro K T0' q u' hT0'cent S' hcent0' V Sc hOcc
  have ha := hcent0' 2 true
  have hb := (hOcc 2 true).2.2
  have ht := (TileTranslationFormulas (Sc 2 true) u').2.2.2.2.1
  have hdelta : TileCentroid V - TileCentroid T0' =
      TileCentroid (Sc 2 true) - TileCentroid (DiamondTile K.1) := by
    rw [ha, hb]
  calc
    TileCentroid V = (TileCentroid V - TileCentroid T0') + TileCentroid T0' := by abel
    _ = (TileCentroid (Sc 2 true) - TileCentroid (DiamondTile K.1)) +
          (TileCentroid (DiamondTile K.1) + GaussianRealPoint u') := by
            rw [hdelta, hT0'cent]
    _ = TileCentroid (TileTranslation (Sc 2 true) u') := by
          rw [ht]
          apply Prod.ext <;> simp [GaussianRealPoint] <;> ring

private theorem hUcells :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let q := DiamondRecursiveQuadruple K
        ∀ (u : GaussianInt), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gS : Fin (3 : ℕ) → Bool →
            PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (S i s)
            (gS i s)) → (
        let U := S 2 false
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence (DiamondRecursiveQuadruple K) (DiamondTile K.1) i s (Sc i s)) →
            ((TileCentroid U = TileCentroid (TileTranslation (Sc 2 false) u)) → (U.cells =
            (TileTranslation (Sc 2 false) u).cells))) ) := by
  classical
  intro K q u S gS hsub0 U Sc hOcc hUcent
  have hUb := TileOdometerBandPrototile _ _ _
    (hsub0 2 false)
  have hCb := BandPrototileTranslation (q 3) (Sc 2 false) u (hOcc 2 false).1
  exact (BandPrototileCentroidUnique _ _ _ hUb hCb hUcent).1

private theorem hVcells :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let q := DiamondRecursiveQuadruple K
        ∀ (u' : GaussianInt), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gS' : Fin (3 : ℕ) →
            Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ)
            (S' i s) (gS' i s)) → (
        let V := S' 2 true
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence (DiamondRecursiveQuadruple K) (DiamondTile K.1) i s (Sc i s)) →
            ((TileCentroid V = TileCentroid (TileTranslation (Sc 2 true) u')) → (V.cells =
            (TileTranslation (Sc 2 true) u').cells))) ) := by
  classical
  intro K q u' S' gS' hsub0' V Sc hOcc hVcent
  have hVb := TileOdometerBandPrototile _ _ _
    (hsub0' 2 true)
  have hCb := BandPrototileTranslation (q 3) (Sc 2 true) u' (hOcc 2 true).1
  exact (BandPrototileCentroidUnique _ _ _ hVb hCb hVcent).1

private theorem hmcast :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          2 ≤ K.1 →
            let m := K.1 - 1
            (m : Int) = (K.1 : Int) - 1
    ) := by
  classical
  intro K hk2 m
  dsimp [m]
  have hk : 1 ≤ K.1 := by omega
  simp [hk]

private theorem hcell0 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          let m := K.1 - 1
          0 < m → (0 : GaussianInt) ∈ DiamondCellDomain m
    ) := by
  classical
  intro K m hmpos
  simp only [DiamondCellDomain, Finset.mem_biUnion]
  refine ⟨0, by simp [hmpos], ?_⟩
  have hr : Nat.min (0 + 1) (2 * m - 0) = 1 := by
    simp only [Nat.zero_add, Nat.sub_zero]
    exact Nat.min_eq_left (by omega : 1 ≤ 2 * m)
  rw [hr]
  simp only [Finset.mem_image]
  exact ⟨1, by simp, by ext <;> simp⟩

private theorem hrow :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          let m := K.1 - 1
          0 < m → ((2 * m - 1 : Nat) : Int) = 2 * (m : Int) - 1
    ) := by
  classical
  intro K m hmpos
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
  push_cast
  ring

private theorem htop :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          let m := K.1 - 1
          0 < m →
            ((2 * m - 1 : Nat) : Int) = 2 * (m : Int) - 1 →
              (⟨-1, 2 * (m : Int) - 1⟩ : GaussianInt) ∈ DiamondCellDomain m
    ) := by
  classical
  intro K m hmpos hrow
  simp only [DiamondCellDomain, Finset.mem_biUnion]
  refine ⟨2 * m - 1, ?_, ?_⟩
  · simpa only [Finset.mem_range] using
      (Nat.sub_lt (by omega : 0 < 2 * m) (by norm_num : 0 < (1 : Nat)))
  have hr : Nat.min ((2 * m - 1) + 1) (2 * m - (2 * m - 1)) = 1 := by
    have hfirst : (2 * m - 1) + 1 = 2 * m := by omega
    have hsecond : 2 * m - (2 * m - 1) = 1 :=
      (Nat.sub_eq_iff_eq_add (by omega : 2 * m - 1 ≤ 2 * m)).2 (by omega)
    rw [hfirst, hsecond]
    exact Nat.min_eq_right (by omega)
  rw [hr]
  simp only [Finset.mem_image]
  refine ⟨0, by simp, ?_⟩
  ext <;> simp [hrow]

private theorem hbaseFoot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let m := K.1 - 1
        ∀ (w : GaussianInt), (w ∈ (DiamondTile m).cells) → (w ∈ FootprintVertices (DiamondTile m)
            ∧ w + 1 ∈ FootprintVertices (DiamondTile m) ∧ w + ⟨0, 1⟩ ∈ FootprintVertices
            (DiamondTile m) ∧ w + 1 + ⟨0, 1⟩ ∈ FootprintVertices (DiamondTile m)) ) := by
  classical
  intro K m w hw
  have hne : (DiamondTile m).cells.Nonempty := ⟨w, hw⟩
  simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
  exact ⟨⟨w, hw, Or.inl rfl⟩,
    ⟨w, hw, Or.inr (Or.inl rfl)⟩,
    ⟨w, hw, Or.inr (Or.inr (Or.inl rfl))⟩,
    ⟨w, hw, Or.inr (Or.inr (Or.inr rfl))⟩⟩

private theorem hVcells' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u' : GaussianInt), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
        let V := S' 2 true
        ∀ (Sc : Fin (3 : ℕ) → Bool → ProtoTile), (Sc (2 : Fin (3 : ℕ)) true = TileTranslation
            (DiamondTile (K.1 - (1 : ℕ))) (⟨(0 : ℤ), (2 : ℤ)⟩ : GaussianInt)) → ((V.cells =
            (TileTranslation (Sc 2 true) u').cells) → (
        let m := K.1 - 1
        V.cells = (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩) u').cells)) ) := by
  classical
  intro K u' S' V Sc h2t hVcells m
  simpa only [h2t] using hVcells

private theorem hUn :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let U := S 2 false
        let m := K.1 - 1
        ((0 : GaussianInt) ∈ DiamondCellDomain m) → ((U.cells = (TileTranslation (DiamondTile m)
            u).cells) → (U.cells.Nonempty)) ) := by
  classical
  intro K u S U m hcell0 hUcells'
  rw [hUcells']
  exact Finset.image_nonempty.mpr ⟨0, hcell0⟩

private theorem hUFoot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let U := S 2 false
        let m := K.1 - 1
        (U.cells = (TileTranslation (DiamondTile m) u).cells) → ((U.cells.Nonempty) →
            (((TileTranslation (DiamondTile m) u).cells.Nonempty) → (FootprintVertices U =
            FootprintVertices (TileTranslation (DiamondTile m) u)))) ) := by
  classical
  intro K u S U m hUcells' hUn hCn
  unfold FootprintVertices
  rw [ite_eq_left hUn, ite_eq_left hCn, hUcells']

private theorem hVn :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u' : GaussianInt), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
        let V := S' 2 true
        let m := K.1 - 1
        ((⟨-1, 2 * (m : Int) - 1⟩ : GaussianInt) ∈ DiamondCellDomain m) → ((V.cells =
            (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩) u').cells) →
            (V.cells.Nonempty)) ) := by
  classical
  intro K u' S' V m htop hVcells'
  rw [hVcells']
  apply Finset.image_nonempty.mpr
  apply Finset.image_nonempty.mpr
  exact ⟨⟨-1, 2 * (m : Int) - 1⟩, htop⟩

private theorem hCn' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u' : GaussianInt),
        let m := K.1 - 1
        ((⟨-1, 2 * (m : Int) - 1⟩ : GaussianInt) ∈ DiamondCellDomain m) → ((TileTranslation
            (TileTranslation (DiamondTile m) ⟨0, 2⟩) u').cells.Nonempty) ) := by
  classical
  intro K u' m htop
  apply Finset.image_nonempty.mpr
  apply Finset.image_nonempty.mpr
  exact ⟨⟨-1, 2 * (m : Int) - 1⟩, htop⟩

private theorem hVFoot :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u' : GaussianInt), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
        let V := S' 2 true
        let m := K.1 - 1
        (V.cells = (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩) u').cells) →
            ((V.cells.Nonempty) → (((TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩)
            u').cells.Nonempty) → (FootprintVertices V = FootprintVertices (TileTranslation
            (TileTranslation (DiamondTile m) ⟨0, 2⟩) u')))) ) := by
  classical
  intro K u' S' V m hVcells' hVn hCn'
  unfold FootprintVertices
  rw [ite_eq_left hVn, ite_eq_left hCn', hVcells']

private theorem hu' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt), ∀ (u' : GaussianInt), (u' - u = (⟨0, -(2 *
            (K.1 : Int))⟩ : GaussianInt)) → (u' = u + ⟨0, -(2 * (K.1 : Int))⟩) ) := by
  classical
  intro K u u' hshift
  have hh := congrArg (fun w : GaussianInt => w + u) hshift
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh

private theorem hUpperC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt),
        let m := K.1 - 1
        ((0 : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (1 :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (1 :
            GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile
            m)) → (u ∈ FootprintVertices (TileTranslation (DiamondTile m) u)) ) := by
  classical
  intro K u m hbase0
  rw [(TileTranslationFormulas (DiamondTile m) u).2.2.2.2.2.1]
  exact ⟨0, hbase0.1, by simp [GaussianTranslation, add_comm]⟩

private theorem hUpperE :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt),
        let m := K.1 - 1
        ((0 : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (1 :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (1 :
            GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile
            m)) → (u + 1 ∈ FootprintVertices (TileTranslation (DiamondTile m) u)) ) := by
  classical
  intro K u m hbase0
  rw [(TileTranslationFormulas (DiamondTile m) u).2.2.2.2.2.1]
  exact ⟨1, hbase0.2.1, by simp [GaussianTranslation, add_comm]⟩

private theorem hUpperN :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt),
        let m := K.1 - 1
        ((0 : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (1 :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (0 : GaussianInt) + (1 :
            GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile
            m)) → (u + ⟨0, 1⟩ ∈ FootprintVertices (TileTranslation (DiamondTile m) u)) ) := by
  classical
  intro K u m hbase0
  rw [(TileTranslationFormulas (DiamondTile m) u).2.2.2.2.2.1]
  exact ⟨⟨0, 1⟩, hbase0.2.2.1, by simp [GaussianTranslation, add_comm]⟩

private theorem hLowerC :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt), ∀ (u' : GaussianInt),
        let m := K.1 - 1
        ((m : Int) = (K.1 : Int) - 1) → (((⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) - (1 : ℤ)⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) -
            (1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧
            (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) - (1 : ℤ)⟩ : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) -
            (1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈
            FootprintVertices (DiamondTile m)) → ((u' = u + ⟨0, -(2 * (K.1 : Int))⟩) → (u ∈
            FootprintVertices (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩) u')))) )
            := by
  classical
  intro K u u' m hmcast hbaseTop hu'
  rw [(TileTranslationFormulas (TileTranslation (DiamondTile m) ⟨0, 2⟩) u').2.2.2.2.2.1,
    (TileTranslationFormulas (DiamondTile m) ⟨0, 2⟩).2.2.2.2.2.1]
  refine ⟨GaussianTranslation ⟨0, 2⟩
      (⟨-1, 2 * (m : Int) - 1⟩ + 1 + ⟨0, 1⟩),
    ⟨⟨-1, 2 * (m : Int) - 1⟩ + 1 + ⟨0, 1⟩,
      hbaseTop.2.2.2, rfl⟩, ?_⟩
  rw [hu']
  simp only [GaussianTranslation]
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
    Zsqrtd.im_one, add_zero, hmcast] <;> ring

private theorem hLowerW :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt), ∀ (u' : GaussianInt),
        let m := K.1 - 1
        ((m : Int) = (K.1 : Int) - 1) → (((⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) - (1 : ℤ)⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) -
            (1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧
            (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) - (1 : ℤ)⟩ : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) -
            (1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈
            FootprintVertices (DiamondTile m)) → ((u' = u + ⟨0, -(2 * (K.1 : Int))⟩) → (u - 1 ∈
            FootprintVertices (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩) u')))) )
            := by
  classical
  intro K u u' m hmcast hbaseTop hu'
  rw [(TileTranslationFormulas (TileTranslation (DiamondTile m) ⟨0, 2⟩) u').2.2.2.2.2.1,
    (TileTranslationFormulas (DiamondTile m) ⟨0, 2⟩).2.2.2.2.2.1]
  refine ⟨GaussianTranslation ⟨0, 2⟩
      (⟨-1, 2 * (m : Int) - 1⟩ + ⟨0, 1⟩),
    ⟨⟨-1, 2 * (m : Int) - 1⟩ + ⟨0, 1⟩,
      hbaseTop.2.2.1, rfl⟩, ?_⟩
  rw [hu']
  simp only [GaussianTranslation]
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
    Zsqrtd.im_one, Zsqrtd.re_sub, Zsqrtd.im_sub, add_zero, hmcast] <;> ring

private theorem hLowerS :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (u : GaussianInt), ∀ (u' : GaussianInt),
        let m := K.1 - 1
        ((m : Int) = (K.1 : Int) - 1) → (((⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) - (1 : ℤ)⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) -
            (1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧
            (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) - (1 : ℤ)⟩ : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ FootprintVertices (DiamondTile m) ∧ (⟨(-1 : ℤ), (2 : ℤ) * (↑m : ℤ) -
            (1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈
            FootprintVertices (DiamondTile m)) → ((u' = u + ⟨0, -(2 * (K.1 : Int))⟩) → (u - ⟨0,
            1⟩ ∈ FootprintVertices (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩)
            u')))) ) := by
  classical
  intro K u u' m hmcast hbaseTop hu'
  rw [(TileTranslationFormulas (TileTranslation (DiamondTile m) ⟨0, 2⟩) u').2.2.2.2.2.1,
    (TileTranslationFormulas (DiamondTile m) ⟨0, 2⟩).2.2.2.2.2.1]
  refine ⟨GaussianTranslation ⟨0, 2⟩
      (⟨-1, 2 * (m : Int) - 1⟩ + 1),
    ⟨⟨-1, 2 * (m : Int) - 1⟩ + 1,
      hbaseTop.2.1, rfl⟩, ?_⟩
  rw [hu']
  simp only [GaussianTranslation]
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
    Zsqrtd.im_one, Zsqrtd.re_sub, Zsqrtd.im_sub, add_zero, hmcast] <;> ring

private theorem hxu :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (x : GaussianInt), ∀ (u : GaussianInt), (x = u) → (∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile), ∀ (gS : Fin (3 : ℕ) → Bool → PartialOdometer),
        let U := S 2 false
        let g := gS 2 false
        let m := K.1 - 1
        (FootprintVertices U = FootprintVertices (TileTranslation (DiamondTile m) u)) → ((u ∈
            FootprintVertices (TileTranslation (DiamondTile m) u)) → (((g.domain : Set
            GaussianInt) = FootprintVertices U) → (x ∈ g.domain)))) ) := by
  classical
  intro K x u hx_eq_u S gS U g m hUFoot hUpperC hgFoot
  rw [hx_eq_u]
  change u ∈ (g.domain : Set GaussianInt)
  rw [hgFoot, hUFoot]
  exact hUpperC

private theorem hxk :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (x : GaussianInt), ∀ (u : GaussianInt), ∀ (u' : GaussianInt),
            (x = u) → (∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gS' : Fin (3 : ℕ) → Bool →
            PartialOdometer),
        let V := S' 2 true
        let k := gS' 2 true
        let m := K.1 - 1
        (FootprintVertices V = FootprintVertices (TileTranslation (TileTranslation (DiamondTile
            m) ⟨0, 2⟩) u')) → ((u ∈ FootprintVertices (TileTranslation (TileTranslation
            (DiamondTile m) ⟨0, 2⟩) u')) → (((k.domain : Set GaussianInt) = FootprintVertices V)
            → (x ∈ k.domain)))) ) := by
  classical
  intro K x u u' hx_eq_u S' gS' V k m hVFoot hLowerC hkFoot
  rw [hx_eq_u]
  change u ∈ (k.domain : Set GaussianInt)
  rw [hkFoot, hVFoot]
  exact hLowerC

private theorem hcoverage :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          ∀ (h0 : PartialOdometer),
            ∀ (h0' : PartialOdometer),
              ∀ (x : GaussianInt),
                (∀ (y : GaussianInt),
                    y = x ∨
                        y = x + (1 : GaussianInt) ∨
                          y = x - (1 : GaussianInt) ∨
                            y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                              y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                      y ∈ h0.domain ∨ y ∈ h0'.domain) →
                  ∀ (u : GaussianInt),
                    ∀ (u' : GaussianInt),
                      let z := x - u;
                      z.im = 0 ∧ Int.natAbs z.re ≤ 1 →
                        z = 0 →
                          x = u →
                            ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
                              ∀ (gS : Fin (3 : ℕ) → Bool → PartialOdometer),
                                ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
                                ∀ (gS' : Fin (3 : ℕ) → Bool → PartialOdometer),
                                let U := S 2 false;
                              let V := S' 2 true;
                              let g := gS 2 false;
                              let k := gS' 2 true;
                              let m := K.1 - 1;
                              FootprintVertices U =
                                FootprintVertices (TileTranslation (DiamondTile m) u) →
                                FootprintVertices V =
                                FootprintVertices
                                (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩)
                                u') →
                                u + 1 ∈
                                FootprintVertices (TileTranslation (DiamondTile m) u) →
                                u + ⟨0, 1⟩ ∈
                                FootprintVertices (TileTranslation (DiamondTile m) u) →
                                u - 1 ∈
                                FootprintVertices
                                (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩)
                                u') →
                                u - ⟨0, 1⟩ ∈
                                FootprintVertices
                                (TileTranslation (TileTranslation (DiamondTile m) ⟨0, 2⟩)
                                u') →
                                (g.domain : Set GaussianInt) = FootprintVertices U →
                                (k.domain : Set GaussianInt) = FootprintVertices V →
                                x ∈ g.domain →
                                ∀ y,
                                y = x ∨
                                y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                                y ∈ g.domain ∨ y ∈ k.domain
    ) := by
  classical
  intro K h0 h0' x hstar u u' z overlap hzzero hx_eq_u S gS S' gS' U V g k m hUFoot hVFoot
      hUpperE hUpperN hLowerW hLowerS hgFoot hkFoot hxu y hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hxu
  · left
    rw [hx_eq_u]
    change u + 1 ∈ (g.domain : Set GaussianInt)
    rw [hgFoot, hUFoot]
    exact hUpperE
  · right
    rw [hx_eq_u]
    change u - 1 ∈ (k.domain : Set GaussianInt)
    rw [hkFoot, hVFoot]
    exact hLowerW
  · left
    rw [hx_eq_u]
    change u + ⟨0, 1⟩ ∈ (g.domain : Set GaussianInt)
    rw [hgFoot, hUFoot]
    exact hUpperN
  · right
    rw [hx_eq_u]
    change u - ⟨0, 1⟩ ∈ (k.domain : Set GaussianInt)
    rw [hkFoot, hVFoot]
    exact hLowerS

private theorem h21 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let q := DiamondRecursiveQuadruple K
        (ProperBandQuadruple q) → ((BandVectors.2 (DiamondRecursiveQuadruple K (2 : Fin (4 : ℕ)))
            (DiamondRecursiveQuadruple K (1 : Fin (4 : ℕ))) = (⟨(0 : ℤ), (-1 : ℤ)⟩ :
            GaussianInt)) → (BandVectors.1 (q 2) (q 1) = (-1 + ⟨0, 1⟩ : GaussianInt))) ) := by
  classical
  intro K q hqD hA21
  have hp := (VectorSquareProduct q hqD.1 2 1 (by decide)).2
  have hq2 : q 2 = (1, (1 : GaussianInt)) := by
    simp [q, DiamondRecursiveQuadruple]
  have hq1 : q 1 = (1, (1 : GaussianInt) + 2 * (⟨0, 1⟩ : GaussianInt)) := by
    norm_num [q, DiamondRecursiveQuadruple, Zsqrtd.ext_iff]
  rw [hA21, hq2, hq1] at hp
  have hre := congrArg (fun z : GaussianInt => z.re) hp
  have him := congrArg (fun z : GaussianInt => z.im) hp
  norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
  have hreal : (BandVectors.1 (q 2) (q 1)).re = -1 := by
    change (BandVectors.1 (1, 1)
      (1, (1 : GaussianInt) + 2 * (⟨0, 1⟩ : GaussianInt))).re = -1
    linarith [him]
  have himag : (BandVectors.1 (q 2) (q 1)).im = 1 := by
    change (BandVectors.1 (1, 1)
      (1, (1 : GaussianInt) + 2 * (⟨0, 1⟩ : GaussianInt))).im = 1
    linarith [hre]
  apply Zsqrtd.ext
  · simpa using hreal
  · simpa using himag

private theorem hmreal :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let m := K.1 - 1
        ((K.1 : Real) = (m : Real) + 1) → ((m : Real) = (K.1 : Real) - 1) ) := by
  classical
  intro K m hKreal
  rw [hKreal]
  ring

private theorem hqprev0 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (Ci : BandCircle),
        (DiamondRecursiveQuadruple K (Fin.succ (2 : Fin (3 : ℕ))) = Ci.1.1) → (
        let m := K.1 - 1
        ∀ (hmpos : 0 < m),
        let Kprev : DiamondParameter := ⟨m, hmpos⟩
        let qprev := DiamondRecursiveQuadruple Kprev
        (m + 1 = K.1) → (((K.1 : Int) = (m : Int) + 1) → (qprev 0 = Ci.1.1))) ) := by
  classical
  intro K Ci hCi m hmpos Kprev qprev hKrel hKcast
  let q := DiamondRecursiveQuadruple K
  calc
    qprev 0 = q 3 := by
      apply Prod.ext
      · dsimp [qprev, Kprev, q, DiamondRecursiveQuadruple]
        rw [← hKrel]
        rw [Nat.succ_sub_one]
        push_cast
        ring
      · apply Zsqrtd.ext
        all_goals
          dsimp [qprev, Kprev, q, DiamondRecursiveQuadruple]
          all_goals rw [hKcast]
    _ = Ci.1.1 := hCi

private theorem hrootcent :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), (BandVectors.1
            (DiamondRecursiveQuadruple K (3 : Fin (4 : ℕ))) (DiamondRecursiveQuadruple K (0 : Fin
            (4 : ℕ))) = (⟨(0 : ℤ), -((2 : ℤ) * (↑K.1 : ℤ))⟩ : GaussianInt)) → ((TileCentroid T0'
            - TileCentroid T0 = GaussianRealPoint (BandVectors.1 (DiamondRecursiveQuadruple K
            (Fin.succ (2 : Fin (3 : ℕ)))) (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ))))) →
            (TileCentroid T0' - TileCentroid T0 = (0, -(2 * (K.1 : Real))))) ) := by
  classical
  intro K T0 T0' hv30 hcentroid
  have hvec : BandVectors.1 (DiamondRecursiveQuadruple K (Fin.succ 2))
      (DiamondRecursiveQuadruple K 0) =
      (⟨0, -(2 * (K.1 : Int))⟩ : GaussianInt) := by simpa using hv30
  rw [hcentroid]
  rw [hvec]
  simp [GaussianRealPoint]

private theorem hUoffset :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0 : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid
            (S i s) - TileCentroid T0 = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let U := S 2 false
        (BandVectors.1 (q 2) (q 1) = (-1 + ⟨0, 1⟩ : GaussianInt)) → (TileCentroid U -
            TileCentroid T0 = (0, -(1 / 2 : Real) * (1 + 1)))) ) := by
  classical
  intro K T0 q S hcent0 U h21
  have h := hcent0 2 false
  simpa [U, h21, GaussianRealPoint] using h

private theorem hUreverse :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let U := S 2 false
        (TileCentroid U - TileCentroid T0 = (0, -(1 / 2 : Real) * (1 + 1))) → (TileCentroid T0 -
            TileCentroid U = (0, (1 / 2 : Real) * (1 + 1))) ) := by
  classical
  intro T0 S U hUoffset
  calc
    TileCentroid T0 - TileCentroid U =
        -(TileCentroid U - TileCentroid T0) := by abel
    _ = (0, (1 / 2 : Real) * (1 + 1)) := by
        rw [hUoffset]
        apply Prod.ext
        · simp
        · norm_num

private theorem hVoffset :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0' : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid
            (S' i s) - TileCentroid T0' = (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ)
            • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let V := S' 2 true
        (BandVectors.1 (q 2) (q 1) = (-1 + ⟨0, 1⟩ : GaussianInt)) → (TileCentroid V -
            TileCentroid T0' = (0, (1 / 2 : Real) * (1 + 1)))) ) := by
  classical
  intro K T0' q S' hcent0' V h21
  have h := hcent0' 2 true
  simpa [V, h21, GaussianRealPoint] using h

private theorem hchildcent :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (S : Fin (3 : ℕ) →
            Bool → ProtoTile), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
        let U := S 2 false
        let V := S' 2 true
        let m := K.1 - 1
        ∀ (hmpos : 0 < m),
        let Kprev : DiamondParameter := ⟨m, hmpos⟩
        let qprev := DiamondRecursiveQuadruple Kprev
        (BandVectors.1 (DiamondRecursiveQuadruple Kprev (3 : Fin (4 : ℕ)))
            (DiamondRecursiveQuadruple Kprev (0 : Fin (4 : ℕ))) = (⟨(0 : ℤ), -((2 : ℤ) *
            (↑Kprev.1 : ℤ))⟩ : GaussianInt)) → (((K.1 : Real) = (m : Real) + 1) →
            ((TileCentroid T0' - TileCentroid T0 = (0, -(2 * (K.1 : Real)))) → ((TileCentroid T0
            - TileCentroid U = (0, (1 / 2 : Real) * (1 + 1))) → ((TileCentroid V - TileCentroid
            T0' = (0, (1 / 2 : Real) * (1 + 1))) → (TileCentroid V - TileCentroid U =
            GaussianRealPoint (BandVectors.1 (qprev 3) (qprev 0))))))) ) := by
  classical
  intro K T0 T0' S S' U V m hmpos Kprev qprev hcentprev hKreal hrootcent hUreverse hVoffset
  have hcalc : TileCentroid V - TileCentroid U =
      (0, -2 * (K.1 : Real) + 2) := by
    calc
      TileCentroid V - TileCentroid U =
          (TileCentroid V - TileCentroid T0') +
            (TileCentroid T0' - TileCentroid T0) +
            (TileCentroid T0 - TileCentroid U) := by
              abel
      _ = (0, (1 / 2 : Real) * (1 + 1)) +
            (0, -(2 * (K.1 : Real))) +
            (0, (1 / 2 : Real) * (1 + 1)) := by
            rw [hVoffset, hrootcent, hUreverse]
      _ = (0, -2 * (K.1 : Real) + 2) := by
            apply Prod.ext
            · simp
            · simp; ring
  have hcoords : GaussianRealPoint (BandVectors.1 (qprev 3) (qprev 0)) =
      (0, -2 * (K.1 : Real) + 2) := by
    rw [hcentprev]
    dsimp only [GaussianRealPoint, Kprev]
    apply Prod.ext
    · norm_num
    · push_cast
      rw [hKreal]
      ring
  exact hcalc.trans hcoords.symm

private theorem hrootSlope :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (p0 : Real × Real), ∀ (p0' : Real × Real), (BandVectors.2
            (DiamondRecursiveQuadruple K (3 : Fin (4 : ℕ))) (DiamondRecursiveQuadruple K (0 : Fin
            (4 : ℕ))) = (⟨-(↑K.1 : ℤ), (↑K.1 : ℤ) - (1 : ℤ)⟩ : GaussianInt)) → ((p0' - p0 =
            GaussianRealPoint (BandVectors.2 (DiamondRecursiveQuadruple K (Fin.succ (2 : Fin (3 :
            ℕ)))) (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ))))) → (p0' - p0 = (-(K.1 : Real),
            (K.1 : Real) - 1))) ) := by
  classical
  intro K p0 p0' hA30 hslope
  rw [hslope]
  have hA30' : BandVectors.2 (DiamondRecursiveQuadruple K (Fin.succ 2))
      (DiamondRecursiveQuadruple K 0) =
      (⟨-(K.1 : Int), (K.1 : Int) - 1⟩ : GaussianInt) := by
    exact hA30
  rw [hA30']
  simp [GaussianRealPoint]

private theorem hux' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (p0 : Real × Real),
        let q := DiamondRecursiveQuadruple K
        ∀ (pr : ℝ × ℝ), ∀ (pU : ℝ × ℝ), (pU.1 - pr.1 = (if false = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((pr = p0) → ((BandVectors.2 (q 2) (q 1)
            = (⟨0, -1⟩ : GaussianInt)) → (pU.1 - p0.1 = -(1 / 2 : Real)))) ) := by
  classical
  intro K p0 q pr pU hux hpr0 hA21q
  rw [← hpr0]
  simpa [hA21q] using hux

private theorem huy' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (p0 : Real × Real),
        let q := DiamondRecursiveQuadruple K
        ∀ (pr : ℝ × ℝ), ∀ (pU : ℝ × ℝ), (pU.2 - pr.2 = (if false = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((pr = p0) → ((BandVectors.2 (q 2) (q 1)
            = (⟨0, -1⟩ : GaussianInt)) → (pU.2 - p0.2 = (1 / 2 : Real)))) ) := by
  classical
  intro K p0 q pr pU huy hpr0 hA21q
  rw [← hpr0]
  simpa [hA21q] using huy

private theorem hvx' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (p0' : Real × Real),
        let q := DiamondRecursiveQuadruple K
        ∀ (pr' : ℝ × ℝ), ∀ (pV : ℝ × ℝ), (pV.1 - pr'.1 = (if true = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((pr' = p0') → ((BandVectors.2 (q 2) (q
            1) = (⟨0, -1⟩ : GaussianInt)) → (pV.1 - p0'.1 = (1 / 2 : Real)))) ) := by
  classical
  intro K p0' q pr' pV hvx hpr'0 hA21q
  rw [← hpr'0]
  simpa [hA21q] using hvx

private theorem hvy' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (p0' : Real × Real),
        let q := DiamondRecursiveQuadruple K
        ∀ (pr' : ℝ × ℝ), ∀ (pV : ℝ × ℝ), (pV.2 - pr'.2 = (if true = true then (1 : ℝ) else (-1 :
            ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → ((pr' = p0') → ((BandVectors.2 (q 2) (q
            1) = (⟨0, -1⟩ : GaussianInt)) → (pV.2 - p0'.2 = -(1 / 2 : Real)))) ) := by
  classical
  intro K p0' q pr' pV hvy hpr'0 hA21q
  rw [← hpr'0]
  simpa [hA21q] using hvy

private theorem huxRev :
    (by
      classical
      exact
        ∀ (p0 : Real × Real), ∀ (pU : ℝ × ℝ), (pU.1 - p0.1 = -(1 / 2 : Real)) → (p0.1 - pU.1 = (1
            / 2 : Real)) ) := by
  classical
  intro p0 pU hux'
  calc
    p0.1 - pU.1 = -(pU.1 - p0.1) := by ring
    _ = (1 / 2 : Real) := by rw [hux']; norm_num

private theorem huyRev :
    (by
      classical
      exact
        ∀ (p0 : Real × Real), ∀ (pU : ℝ × ℝ), (pU.2 - p0.2 = (1 / 2 : Real)) → (p0.2 - pU.2 = -(1
            / 2 : Real)) ) := by
  classical
  intro p0 pU huy'
  calc
    p0.2 - pU.2 = -(pU.2 - p0.2) := by ring
    _ = -(1 / 2 : Real) := by rw [huy']

private theorem hpx :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (p0 : Real × Real), ∀ (p0' : Real × Real),
        let m := K.1 - 1
        ((m : Real) = (K.1 : Real) - 1) → (∀ (pU : ℝ × ℝ), ∀ (pV : ℝ × ℝ), (p0'.1 - p0.1 = -(K.1
            : Real)) → ((pV.1 - p0'.1 = (1 / 2 : Real)) → ((p0.1 - pU.1 = (1 / 2 : Real)) → (pV.1
            - pU.1 = -(m : Real))))) ) := by
  classical
  intro K p0 p0' m hmreal pU pV hrootSx hvx' huxRev
  calc
    pV.1 - pU.1 = (pV.1 - p0'.1) + (p0'.1 - p0.1) + (p0.1 - pU.1) := by ring
    _ = (1 / 2) + (-(K.1 : Real)) + (1 / 2) := by rw [hvx', hrootSx, huxRev]
    _ = -(m : Real) := by rw [hmreal]; ring

private theorem hpy :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (p0 : Real × Real), ∀ (p0' : Real × Real),
        let m := K.1 - 1
        ((m : Real) = (K.1 : Real) - 1) → (∀ (pU : ℝ × ℝ), ∀ (pV : ℝ × ℝ), (p0'.2 - p0.2 = (K.1 :
            Real) - 1) → ((pV.2 - p0'.2 = -(1 / 2 : Real)) → ((p0.2 - pU.2 = -(1 / 2 : Real)) →
            (pV.2 - pU.2 = (m : Real) - 1)))) ) := by
  classical
  intro K p0 p0' m hmreal pU pV hrootSy hvy' huyRev
  calc
    pV.2 - pU.2 = (pV.2 - p0'.2) + (p0'.2 - p0.2) + (p0.2 - pU.2) := by ring
    _ = (-(1 / 2)) + ((K.1 : Real) - 1) - (1 / 2) := by rw [hvy', hrootSy, huyRev]; ring
    _ = (m : Real) - 1 := by rw [hmreal]; ring

private theorem hLeft :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (Ci : BandCircle), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀
            (gS : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
            ∀ (gS' : Fin (3 : ℕ) → Bool → PartialOdometer),
        let U := S 2 false
        let V := S' 2 true
        let g := gS 2 false
        let k := gS' 2 true
        let m := K.1 - 1
        ∀ (hmpos : 0 < m),
        let Kprev : DiamondParameter := ⟨m, hmpos⟩
        let qprev := DiamondRecursiveQuadruple Kprev
        (ProperBandQuadruple (DiamondRecursiveQuadruple Kprev)) → ((BandVectors.2
            (DiamondRecursiveQuadruple Kprev (3 : Fin (4 : ℕ))) (DiamondRecursiveQuadruple Kprev
            (0 : Fin (4 : ℕ))) = (⟨-(↑Kprev.1 : ℤ), (↑Kprev.1 : ℤ) - (1 : ℤ)⟩ :
            GaussianInt)) → (((m : Real) = (K.1 : Real) - 1) → ((qprev 0 = Ci.1.1) →
            ((TileCentroid V - TileCentroid U = GaussianRealPoint (BandVectors.1 (qprev 3) (qprev
            0))) → (∀ (pU : ℝ × ℝ), (PartialOdometerSlope (gS (2 : Fin (3 : ℕ)) false) = some pU)
            → (∀ (pV : ℝ × ℝ), (PartialOdometerSlope (gS' (2 : Fin (3 : ℕ)) true) = some pV) →
            ((pV.1 - pU.1 = -(m : Real)) → ((pV.2 - pU.2 = (m : Real) - 1) → ((TileOdometer
            Ci.1.1 U g) → ((TileOdometer Ci.1.1 V k) → (LeftLatticeAdjacent Ci U V g k)))))))))))
            ) := by
  classical
  intro K Ci S gS S' gS' U V g k m hmpos Kprev qprev hqprev hsloprev hmreal hqprev0 hchildcent pU
      hpu pV hpv hpx hpy hOg hOk
  refine ⟨hOg, hOk, pU, pV, hpu, hpv, Or.inr ?_⟩
  refine ⟨qprev, 2, true, hqprev, hqprev0, ?_, ?_, ?_⟩
  · simpa using hchildcent
  · have hsloprev' : BandVectors.2 (qprev (Fin.succ 2)) (qprev 0) =
        (⟨-(m : Int), (m : Int) - 1⟩ : GaussianInt) := by
      have hidx : (3 : Fin 4) = Fin.succ 2 := by decide
      simpa only [qprev, ← hidx] using hsloprev
    rw [hsloprev']
    simpa [GaussianInt, GaussianRealPoint, hmreal] using hpx
  · have hsloprev' : BandVectors.2 (qprev (Fin.succ 2)) (qprev 0) =
        (⟨-(m : Int), (m : Int) - 1⟩ : GaussianInt) := by
      have hidx : (3 : Fin 4) = Fin.succ 2 := by decide
      simpa only [qprev, ← hidx] using hsloprev
    rw [hsloprev']
    simpa [GaussianInt, GaussianRealPoint, hmreal] using hpy

end DiamondBoundaryStarGeometry

theorem DiamondOpposingBoundaryStarLocalization
    (K : DiamondParameter)
    (hq : ProperBandQuadruple (DiamondRecursiveQuadruple K))
    (C0 Ci : BandCircle) (i : Fin 3)
    (hC0 : (DiamondRecursiveQuadruple K) 0 = C0.1.1)
    (hCi : (DiamondRecursiveQuadruple K) i.succ = Ci.1.1)
    (T0 T0' : ProtoTile) (h0 h0' : PartialOdometer)
    (hO0 : TileOdometer C0.1.1 T0 h0)
    (hO0' : TileOdometer C0.1.1 T0' h0')
    (hlarge : 1 < Ci.1.1.1)
    (p0 p0' : Real × Real)
    (hs0 : PartialOdometerSlope h0 = some p0)
    (hs0' : PartialOdometerSlope h0' = some p0')
    (hcentroid : TileCentroid T0' - TileCentroid T0 =
      GaussianRealPoint
        (BandVectors.1 ((DiamondRecursiveQuadruple K) i.succ)
          ((DiamondRecursiveQuadruple K) 0)))
    (hslope : p0' - p0 =
      GaussianRealPoint
        (BandVectors.2 ((DiamondRecursiveQuadruple K) i.succ)
          ((DiamondRecursiveQuadruple K) 0)))
    (x : GaussianInt) (hx0 : x ∈ h0.domain) (hx0' : x ∈ h0'.domain)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h0.domain ∨ y ∈ h0'.domain) :
    ∃ (U V : ProtoTile) (g k : PartialOdometer),
      AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧
      AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧
      LeftLatticeAdjacent Ci U V g k ∧
      x ∈ g.domain ∧ x ∈ k.domain ∧
      ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ g.domain ∨ y ∈ k.domain := by
-- BODY
      classical
      let q := DiamondRecursiveQuadruple K
      have hqD : ProperBandQuadruple q := hq
      have coords := DiamondCoordinateConfiguration K
      rcases coords with ⟨_, _, _, _, hv30, _, _, hA30, _, _, hA21⟩
      have hcurv : 1 < (DiamondRecursiveQuadruple K (i.succ)).1 :=
          DiamondBoundaryStarGeometry.hcurv K Ci i hCi hlarge
      have index_two := DiamondBoundaryStarGeometry.index_two K Ci i hCi hcurv
      subst i
      have hKpos : 0 < K.1 := K.2
      have hk2 := DiamondBoundaryStarGeometry.hk2 K hcurv hKpos
      obtain ⟨H, hH, hHdom, hHfoot, hHsquares, hHvalue, hHslope⟩ :=
        DiamondTileOdometerRestriction K
      have hC0pos : 0 < C0.1.1.1 := DiamondBoundaryStarGeometry.hC0pos K hq C0 hC0
      obtain ⟨u, huCell, huEmpty, a, b, huDom, huValue⟩ :=
        (TileOdometerTranslationUniqueness C0.1.1 T0 (DiamondTile K.1) h0 H
          hC0pos hO0 (by simpa [hC0] using hH)).exists
      obtain ⟨u', hu'Cell, hu'Empty, a', b', hu'Dom, hu'Value⟩ :=
        (TileOdometerTranslationUniqueness C0.1.1 T0' (DiamondTile K.1) h0' H
          hC0pos hO0' (by simpa [hC0] using hH)).exists
      have hrootNonempty : (DiamondTile K.1).cells.Nonempty :=
        ⟨⟨0, 0⟩, (DiamondBoundaryStarGeometry.hrootCell K hKpos hk2)⟩
      have hT0cent := DiamondBoundaryStarGeometry.hT0cent K T0 u huCell
          (DiamondBoundaryStarGeometry.hT0ne K T0 u huCell hrootNonempty)
      have hT0'cent := DiamondBoundaryStarGeometry.hT0'cent K T0' u' hu'Cell
          (DiamondBoundaryStarGeometry.hT0'ne K T0' u' hu'Cell hrootNonempty)
      have hshift := DiamondBoundaryStarGeometry.hshift K T0 T0' hv30 hcentroid u u' hT0cent
          hT0'cent
      have hshift' := DiamondBoundaryStarGeometry.hshift' K u u' hshift
      have Hmem := DiamondBoundaryStarGeometry.Hmem K H hHdom
      have hzUpper := DiamondBoundaryStarGeometry.hzUpper K h0
          x hx0 H u huDom Hmem
      have hzLower := DiamondBoundaryStarGeometry.hzLower K h0' x hx0' H u u' hu'Dom hshift' Hmem
      have overlap := DiamondBoundaryStarGeometry.overlap K x hk2 u hzUpper hzLower
      have hwest := DiamondBoundaryStarGeometry.hwest K h0 h0' x hstar H u huDom u' hu'Dom
          hshift' Hmem
      have heast := DiamondBoundaryStarGeometry.heast K h0 h0' x hstar H u huDom u' hu'Dom
          hshift' Hmem
      have hzzero := DiamondBoundaryStarGeometry.hzzero K x hk2 u overlap hwest heast
      have hx_eq_u := DiamondBoundaryStarGeometry.hx_eq_u x u hzzero
      have hroot := DiamondBoundaryStarGeometry.hroot K hk2
      obtain ⟨S, gS, hband0, hsub0, hcells0, hfoot0, hcent0,
          hdom0, hvalue0, hcompat0, hslope0⟩ :=
        TileOdometerReindexedDecomposition q hqD T0 h0 hroot
          (by simpa only [← hC0] using hO0)
      obtain ⟨S', gS', hband0', hsub0', hcells0', hfoot0', hcent0',
          hdom0', hvalue0', hcompat0', hslope0'⟩ :=
        TileOdometerReindexedDecomposition q hqD T0' h0' hroot
          (by simpa only [← hC0] using hO0')
      let U := S 2 false
      let V := S' 2 true
      let g := gS 2 false
      let k := gS' 2 true
      have hCiPos : 0 < Ci.1.1.1 := by omega
      have hAncU := DiamondBoundaryStarGeometry.hAncU
          K C0 Ci hC0 T0 h0 hO0 hCi S gS hsub0 hdom0 hvalue0 hCiPos
              (DiamondBoundaryStarGeometry.hATU K C0 Ci hC0 T0 hqD hCi S gS hband0 hsub0 hfoot0
              hcent0)
      have hAncV := DiamondBoundaryStarGeometry.hAncV K C0 Ci hC0 T0' h0' hO0' hCi S' gS' hsub0'
          hdom0'
          hvalue0' hCiPos (DiamondBoundaryStarGeometry.hATV K C0 Ci hC0 T0' hqD hCi S' gS'
              hband0' hsub0' hfoot0' hcent0')
      obtain ⟨hDK, Sc, hOcc, hCells, h00t, h00f, h10t, h10f, h2f, h2t⟩ :=
        DiamondTileRecursiveIdentification K
      have hUcells : U.cells = (TileTranslation (Sc 2 false) u).cells :=
          DiamondBoundaryStarGeometry.hUcells K u S gS hsub0 Sc hOcc
              (DiamondBoundaryStarGeometry.hUcent K T0 u hT0cent S hcent0 Sc hOcc)
      let m := K.1 - 1
      have hmpos : 0 < m := by dsimp [m]; omega
      have hmcast := DiamondBoundaryStarGeometry.hmcast K
          hk2
      have hcell0 := DiamondBoundaryStarGeometry.hcell0
          K hmpos
      have htop := DiamondBoundaryStarGeometry.htop K hmpos
          (DiamondBoundaryStarGeometry.hrow K hmpos)
      have hbaseFoot := DiamondBoundaryStarGeometry.hbaseFoot K
      have hbase0 := hbaseFoot 0 hcell0
      have hbaseTop := hbaseFoot ⟨-1, 2 * (m : Int) - 1⟩ htop
      have hUcells' : U.cells = (TileTranslation (DiamondTile m) u).cells := by
        simpa only [h2f] using hUcells
      have hVcells' := DiamondBoundaryStarGeometry.hVcells' K u' S' Sc h2t
          (DiamondBoundaryStarGeometry.hVcells K u' S' gS' hsub0' Sc hOcc
          (DiamondBoundaryStarGeometry.hVcent K T0' u' hT0'cent S' hcent0' Sc hOcc))
      have hCn : (TileTranslation (DiamondTile m) u).cells.Nonempty := by
        exact Finset.image_nonempty.mpr ⟨0, hcell0⟩
      have hUFoot := DiamondBoundaryStarGeometry.hUFoot K u S hUcells'
          (DiamondBoundaryStarGeometry.hUn K u S hcell0 hUcells') hCn
      have hVFoot := DiamondBoundaryStarGeometry.hVFoot K u' S' hVcells'
          (DiamondBoundaryStarGeometry.hVn K u' S' htop hVcells')
          (DiamondBoundaryStarGeometry.hCn' K u' htop)
      have hu' := DiamondBoundaryStarGeometry.hu' K u u' hshift
      have hgFoot : (g.domain : Set GaussianInt) = FootprintVertices U := hAncU.2.2.1
      have hkFoot : (k.domain : Set GaussianInt) = FootprintVertices V := hAncV.2.2.1
      have hxu := DiamondBoundaryStarGeometry.hxu K x u hx_eq_u S gS hUFoot
          (DiamondBoundaryStarGeometry.hUpperC K u hbase0) hgFoot
      have hxk := DiamondBoundaryStarGeometry.hxk K x u u' hx_eq_u S' gS' hVFoot
          (DiamondBoundaryStarGeometry.hLowerC K u u' hmcast hbaseTop hu') hkFoot
      have hcoverage := DiamondBoundaryStarGeometry.hcoverage K h0 h0' x hstar u u' overlap hzzero
          hx_eq_u S gS S' gS' hUFoot hVFoot
                  (DiamondBoundaryStarGeometry.hUpperE K u hbase0)
              (DiamondBoundaryStarGeometry.hUpperN K u hbase0)
                  (DiamondBoundaryStarGeometry.hLowerW K u u' hmcast hbaseTop hu')
                  (DiamondBoundaryStarGeometry.hLowerS K u u' hmcast hbaseTop hu') hgFoot hkFoot
                  hxu
      have h21 := DiamondBoundaryStarGeometry.h21 K hqD hA21
      let Kprev : DiamondParameter := ⟨m, hmpos⟩
      rcases DiamondCoordinateConfiguration Kprev with
        ⟨_, hqprev, _, _, hcentprev, _, _, hsloprev, _, _, _⟩
      have hKrel : m + 1 = K.1 := by dsimp [m]; omega
      have hKcast : (K.1 : Int) = (m : Int) + 1 := by exact_mod_cast hKrel.symm
      have hKreal : (K.1 : Real) = (m : Real) + 1 := by exact_mod_cast hKrel.symm
      have hmreal := DiamondBoundaryStarGeometry.hmreal K hKreal
      have hqprev0 := DiamondBoundaryStarGeometry.hqprev0 K Ci hCi hmpos hKrel
          hKcast
      have hchildcent := DiamondBoundaryStarGeometry.hchildcent K T0 T0' S S' hmpos hcentprev hKreal
              (DiamondBoundaryStarGeometry.hrootcent K T0 T0' hv30 hcentroid)
                  (DiamondBoundaryStarGeometry.hUreverse T0 S
                  (DiamondBoundaryStarGeometry.hUoffset K T0 S hcent0 h21))
                  (DiamondBoundaryStarGeometry.hVoffset K T0' S' hcent0' h21)
      have hrootSlope : p0' - p0 = (-(K.1 : Real), (K.1 : Real) - 1) :=
          DiamondBoundaryStarGeometry.hrootSlope K p0 p0' hA30 hslope
      rcases hslope0 2 false with hzeroU | ⟨pr, pU, hpr, hpu, hux, huy⟩
      · have : (q 3).1 = 0 := hzeroU
        change (DiamondRecursiveQuadruple K (Fin.succ 2)).1 = 0 at this
        rw [hCi] at this hcurv
        omega
      rcases hslope0' 2 true with hzeroV | ⟨pr', pV, hpr', hpv, hvx, hvy⟩
      · have : (q 3).1 = 0 := hzeroV
        change (DiamondRecursiveQuadruple K (Fin.succ 2)).1 = 0 at this
        rw [hCi] at this hcurv
        omega
      have hpr0 : pr = p0 := by
        exact Option.some.inj (hpr.symm.trans hs0)
      have hpr'0 : pr' = p0' := by
        exact Option.some.inj (hpr'.symm.trans hs0')
      have hrootSx : p0'.1 - p0.1 = -(K.1 : Real) := by
        simpa using congrArg Prod.fst hrootSlope
      have hrootSy : p0'.2 - p0.2 = (K.1 : Real) - 1 := by
        simpa using congrArg Prod.snd hrootSlope
      have hA21q : BandVectors.2 (q 2) (q 1) = (⟨0, -1⟩ : GaussianInt) := by
        simpa only [q] using hA21
      have hOg : TileOdometer Ci.1.1 U g := by
        simpa only [← hCi] using hsub0 2 false
      have hOk : TileOdometer Ci.1.1 V k := by
        simpa only [← hCi] using hsub0' 2 true
      exact ⟨U, V, g, k, hAncU, hAncV, (DiamondBoundaryStarGeometry.hLeft K Ci S gS S' gS' hmpos
          hqprev hsloprev hmreal hqprev0 hchildcent pU hpu pV hpv
          (DiamondBoundaryStarGeometry.hpx K p0 p0' hmreal pU pV hrootSx
          (DiamondBoundaryStarGeometry.hvx' K p0' pr' pV hvx hpr'0 hA21q)
          (DiamondBoundaryStarGeometry.huxRev p0 pU (DiamondBoundaryStarGeometry.hux' K p0 pr pU
          hux hpr0 hA21q))) (DiamondBoundaryStarGeometry.hpy K p0 p0' hmreal pU pV hrootSy
          (DiamondBoundaryStarGeometry.hvy' K p0' pr' pV hvy hpr'0 hA21q)
          (DiamondBoundaryStarGeometry.huyRev p0 pU (DiamondBoundaryStarGeometry.huy' K p0 pr pU
          huy hpr0 hA21q))) hOg hOk), hxu, hxk, hcoverage⟩

end ApollonianSuperharmonic

end

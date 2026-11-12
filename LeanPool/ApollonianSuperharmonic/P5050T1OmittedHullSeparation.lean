/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedGap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.P4828T1Step
public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate
public import LeanPool.ApollonianSuperharmonic.P4953T1LiteralHulls
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology

-- [TABLET NODE: P5050T1OmittedHullSeparation]

/-!
# P5050T1OmittedHullSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OmittedHullLemmas

private theorem circleDistance :
    ∀ (v : Fin 4 → CircleCoordinates), (ProperBandQuadruple v) → ∀ (i : Fin 4), ∀ (k : Fin 4), (i
        ≠ k) → (0 < (v i).1) → (0 < (v k).1) → dist (((v i).2 : Complex) / (v i).1)
          (((v k).2 : Complex) / (v k).1) =
        1 / (v i).1 + 1 / (v k).1 := by
  classical
  intro v hv i k hik hi hk
  let w : GaussianInt := (v k).1 • (v i).2 - (v i).1 • (v k).2
  have ht := TangencyCoordinateIdentity v hv.1 i k hik
  have normCast (w : GaussianInt) :
      Complex.normSq (w : Complex) = (Zsqrtd.norm w : Real) := by
    simp [Complex.normSq, Zsqrtd.norm_def]
  have hn : Complex.normSq (w : Complex) =
      (((v i).1 + (v k).1 : ℤ)^2 : Real) := by
    change Complex.normSq
        (((v k).1 • (v i).2 - (v i).1 • (v k).2 : GaussianInt) : Complex) = _
    rw [normCast]
    exact_mod_cast ht
  have hnsq : ‖(w : Complex)‖ ^ 2 =
      (((v i).1 + (v k).1 : ℤ) : Real) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
  have hnorm : ‖(w : Complex)‖ =
      (((v i).1 + (v k).1 : ℤ) : Real) := by
    have hnonneg := norm_nonneg (w : Complex)
    have hsum : 0 ≤ (((v i).1 + (v k).1 : ℤ) : Real) := by positivity
    nlinarith
  have hdiff :
      ((v i).2 : Complex) / (v i).1 - ((v k).2 : Complex) / (v k).1 =
        (w : Complex) / (((v i).1 * (v k).1 : ℤ) : Complex) := by
    dsimp [w]
    push_cast
    simp only [map_sub, map_zsmul]
    have hia : (v i).1 ≠ 0 := ne_of_gt hi
    have hkb : (v k).1 ≠ 0 := ne_of_gt hk
    field_simp [hia, hkb]
    ring
  rw [Complex.dist_eq, hdiff, Complex.norm_div, Complex.norm_intCast, hnorm]
  have ha : 0 < ((v i).1 : Real) := by exact_mod_cast hi
  have hb : 0 < ((v k).1 : Real) := by exact_mod_cast hk
  have hab : 0 < (((v i).1 * (v k).1 : ℤ) : Real) := by
    exact_mod_cast mul_pos hi hk
  rw [abs_of_pos hab]
  push_cast
  field_simp [ne_of_gt ha, ne_of_gt hb]
  ring

private theorem projectionAffine :
    ∀ (a : Complex), ∀ (x : Complex), ∀ (d : Real), (d ≠ 0) → ∃ D : Complex →ᵃ[Real] Real,
        ∀ z, D z = ((x - a) * (starRingEnd Complex) (z - a)).re / d := by
  classical
  intro a x d hd
  let L : Complex →ₗ[Real] Real :=
    { toFun := fun z => ((x - a) * (starRingEnd Complex) z).re / d
      map_add' := by
        intro z w
        simp only [map_add, mul_add, Complex.add_re]
        ring
      map_smul' := by
        intro c z
        rw [Complex.real_smul]
        simp only [map_mul]
        rw [show (starRingEnd Complex) (c : Complex) = (c : Complex) by simp]
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, RingHom.id_apply]
        ring }
  let F : Complex → Real := fun z => L (z - a)
  have hF : ∀ z : Complex, F z = L (z -ᵥ a) +ᵥ F a := by
    intro z
    simp [F]
  let D := AffineMap.mk' F L a hF
  refine ⟨D, ?_⟩
  intro z
  rfl

private theorem projectionSphereBound :
    ∀ (a : Complex), ∀ (x : Complex), ∀ (z : Complex), ∀ (ρ : Real), ∀ (R : Real), (0 < ρ) → (0 <
        ρ + R) → (dist a x = ρ + R) → (dist z a = ρ) → ((x - a) * (starRingEnd Complex) (z -
        a)).re / (ρ + R) ≤ ρ := by
  classical
  intro a x z ρ R hρ hden hax hz
  have hnormx : ‖x - a‖ = ρ + R := by
    simpa [dist_eq_norm, norm_sub_rev] using hax
  have hnormz : ‖z - a‖ = ρ := by
    simpa [dist_eq_norm, norm_sub_rev] using hz
  have hprod : ‖(x - a) * (starRingEnd Complex) (z - a)‖ = (ρ + R) * ρ := by
    rw [Complex.norm_mul]
    rw [Complex.norm_conj, hnormx, hnormz]
  have habs : |((x - a) * (starRingEnd Complex) (z - a)).re| ≤
      ‖(x - a) * (starRingEnd Complex) (z - a)‖ :=
    Complex.abs_re_le_norm _
  have hreal : ((x - a) * (starRingEnd Complex) (z - a)).re ≤ (ρ + R) * ρ := by
    calc
      _ ≤ |((x - a) * (starRingEnd Complex) (z - a)).re| := le_abs_self _
      _ ≤ ‖(x - a) * (starRingEnd Complex) (z - a)‖ := habs
      _ = (ρ + R) * ρ := hprod
  apply (div_le_iff₀ hden).2
  nlinarith [hreal]

private theorem externalProjection :
    ∀ (a : Complex), ∀ (x : Complex), ∀ (z : Complex), ∀ (ρ : Real), ∀ (R : Real), ∀ (s : Real),
        (0 < ρ + R) → (dist a x = ρ + R) → (dist a z = ρ + s) → (dist x z = R + s) → ((x - a) *
        (starRingEnd Complex) (z - a)).re / (ρ + R) =
        ρ + s * (ρ - R) / (ρ + R) := by
  classical
  intro a x z ρ R s hpos hax haz hxz
  have hnorm (u v : Complex) (d : Real) (hd : dist u v = d) :
      Complex.normSq (u - v) = d ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, hd]
  have h1 : Complex.normSq (x - a) = (ρ + R) ^ 2 :=
    hnorm x a (ρ + R) (by simpa [dist_comm] using hax)
  have h2 : Complex.normSq (z - a) = (ρ + s) ^ 2 :=
    hnorm z a (ρ + s) (by simpa [dist_comm] using haz)
  have h3 : Complex.normSq ((x - a) - (z - a)) = (R + s) ^ 2 := by
    have hv : (x - a) - (z - a) = x - z := by abel
    rw [hv]
    exact hnorm x z (R + s) hxz
  have hdot : ((x - a) * (starRingEnd Complex) (z - a)).re =
      (Complex.normSq (x - a) + Complex.normSq (z - a) -
        Complex.normSq ((x - a) - (z - a))) / 2 := by
    have hf := Complex.normSq_sub (x - a) (z - a)
    nlinarith [hf]
  rw [hdot, h1, h2, h3]
  field_simp [ne_of_gt hpos]
  ring

private theorem hr :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3), (0 < (q j.succ).1) →
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    0 < r j.succ := by
  classical
  intro q j hj r
  exact one_div_pos.mpr (by exact_mod_cast hj)

private theorem hR :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    0 < r 0 := by
  classical
  intro q hq r
  exact one_div_pos.mpr
    (by exact_mod_cast (ProperBandCurvatureStructure q hq).1)

private theorem hden :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (0 < r j.succ) → (0 < r 0) → 0 < r j.succ + r 0 := by
  classical
  intro q j r hr hR
  exact add_pos hr hR

private theorem hax :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ∀ (j : Fin 3), (0 < (q
        j.succ).1) → (∀ (v : Fin 4 → CircleCoordinates), (ProperBandQuadruple v) → ∀ (i : Fin 4),
            ∀ (k : Fin 4), (i ≠ k) → (0 < (v i).1) → (0 < (v k).1) → dist (((v i).2 : Complex) / (v
        i).1) (((v k).2 : Complex) / (v k).1) = 1 / (v i).1 + 1 / (v k).1) →
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    dist (p j.succ) (p 0) = r j.succ + r 0 := by
  classical
  intro q hq j hj circleDistance p r
  exact circleDistance q hq j.succ 0 (Fin.succ_ne_zero j) hj
      (ProperBandCurvatureStructure q hq).1

end OmittedHullLemmas

namespace OmittedHullGeometry

private theorem signed :
    ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), (P4828T1LineSupport L q) →
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    ∀ (l : Fin (3 : ℕ)), ((q l.succ).1 = (0 : ℤ)) →
    let h : ℝ := if (q l.succ).2 = -1 then L else L + 2
    let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
    ∀ (i : Fin 4), (0 < (q i).1) → σ * ((p i).re - h) = r i := by
  classical
  intro L q hs p r l hl h σ i hi
  have hh := hs.signed l.succ i hl hi
  have hc : ((q i).1 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hi
  have hp : (p i).re = (q i).2.re / (q i).1 := by
    simp [p]
  rcases hs.normals l.succ hl with hn | hn
  · simp [σ, h, hn, hp, r]
    rw [hn] at hh
    norm_num at hh
    field_simp [hc]
    linarith
  · have hne : (q l.succ).2 ≠ -1 := by rw [hn]; norm_num
    simp [σ, h, hne, hp, r]
    rw [hn] at hh
    norm_num at hh
    field_simp [hc]
    linarith

private theorem hfootx :
    ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (0 < r j.succ) → (0 < r 0) → ∀ (D : ℂ →ᵃ[ℝ] ℝ), (∀ (z : ℂ), (D : ℂ → ℝ) z = ((p (0 : Fin (4 :
        ℕ)) - p j.succ) * (starRingEnd ℂ : ℂ → ℂ) (z - p j.succ)).re / (r j.succ + r (0 : Fin (4
        : ℕ)))) → ∀ (l : Fin (3 : ℕ)),
    let h : ℝ := if (q l.succ).2 = -1 then L else L + 2
    let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
    let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
    (σ ^ 2 = 1) → ((p 0).re = h + σ * r 0) → ((p j.succ).re = h + σ * r j.succ) → (((p 0).im - (p
        j.succ).im) ^ 2 = 4 * r j.succ * r 0) → D (foot (p 0)) = r j.succ +
      2 * r j.succ * r 0 / (r j.succ + r 0) := by
  classical
  intro L q j p r hr hR D hD l h σ foot hσ coord0 coorda hd2
  have hden : 0 < r j.succ + r 0 := add_pos hr hR
  rw [hD]
  have hre : (p 0).re - (p j.succ).re =
      σ * (r 0 - r j.succ) := by rw [coord0, coorda]; ring
  have hrf : h - (p j.succ).re = -σ * r j.succ := by
    rw [coorda]
    ring
  simp only [foot, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, mul_neg]
  rw [hre, hrf]
  field_simp [ne_of_gt hden]
  rw [hσ]
  nlinarith only [hd2]

private theorem hfootb :
    ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (0 < r j.succ) → (0 < r 0) → ∀ (D : ℂ →ᵃ[ℝ] ℝ), (∀ (z : ℂ), (D : ℂ → ℝ) z = ((p (0 : Fin (4 :
        ℕ)) - p j.succ) * (starRingEnd ℂ : ℂ → ℂ) (z - p j.succ)).re / (r j.succ + r (0 : Fin (4
        : ℕ)))) → ∀ (l : Fin (3 : ℕ)), ∀ (b : Fin (3 : ℕ)),
    let h : ℝ := if (q l.succ).2 = -1 then L else L + 2
    let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
    let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
    (σ ^ 2 = 1) → ((p 0).re = h + σ * r 0) → ((p j.succ).re = h + σ * r j.succ) → (((p 0).im - (p
        j.succ).im) * ((p b.succ).im - (p j.succ).im) = 2 * r j.succ * r 0 + 2 * r j.succ * r
        b.succ - 2 * r 0 * r b.succ) → D (foot (p b.succ)) = r j.succ +
      2 * r b.succ * (r j.succ - r 0) /
        (r j.succ + r 0) := by
  classical
  intro L q j p r hr hR D hD l b h σ foot hσ coord0 coorda hde
  have hden : 0 < r j.succ + r 0 := add_pos hr hR
  rw [hD]
  have hrf : h - (p j.succ).re = -σ * r j.succ := by
    rw [coorda]
    ring
  have hre : (p 0).re - (p j.succ).re =
      σ * (r 0 - r j.succ) := by rw [coord0, coorda]; ring
  simp only [foot, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, mul_neg]
  rw [hre, hrf]
  field_simp [ne_of_gt hden]
  rw [hσ]
  nlinarith only [hde]

private theorem hcB :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ∀ (j : Fin 3), (0 < (q
        j.succ).1) → (∀ (a : Complex), ∀ (x : Complex), ∀ (z : Complex), ∀ (ρ : Real), ∀ (R :
            Real), ∀ (s : Real), (0 < ρ + R) → (dist a x = ρ + R) → (dist a z = ρ + s) → (dist x z =
        R + s) → ((x - a) * (starRingEnd Complex) (z - a)).re / (ρ + R) = ρ + s * (ρ - R) / (ρ +
        R)) →
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (0 < r j.succ + r 0) → (dist (p j.succ) (p 0) = r j.succ + r 0) → ∀ (D : ℂ →ᵃ[ℝ] ℝ), (∀ (z :
        ℂ), (D : ℂ → ℝ) z = ((p (0 : Fin (4 : ℕ)) - p j.succ) * (starRingEnd ℂ : ℂ → ℂ) (z - p
        j.succ)).re / (r j.succ + r (0 : Fin (4 : ℕ)))) → ∀ (b : Fin (3 : ℕ)), (0 < (q b.succ).1)
        → (dist (p j.succ) (p b.succ) = r j.succ + r b.succ) → (dist (p 0) (p b.succ) = r 0 + r
        b.succ) → r j.succ < D (p b.succ) := by
  classical
  intro q hq j hj externalProjection p r hden hax D hD b hb hab hxb
  rw [hD, externalProjection (p j.succ) (p 0) (p b.succ)
    (r j.succ) (r 0) (r b.succ) hden hax hab hxb]
  have hlt : r 0 < r j.succ := by
    apply one_div_lt_one_div_of_lt (by exact_mod_cast hj)
    exact_mod_cast hq.2 j
  have hs : 0 < r b.succ := one_div_pos.mpr (by exact_mod_cast hb)
  have hh : 0 < r b.succ * (r j.succ - r 0) /
      (r j.succ + r 0) := div_pos (mul_pos hs (sub_pos.mpr hlt)) hden
  linarith

end OmittedHullGeometry

namespace OmittedHullBound

private theorem hull_bound :
    ∀ (L : ℝ), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (P4828T1LineSupport
        L q) → ∀ (j : Fin 3), (0 < (q j.succ).1) → (∀ (v : Fin 4 → CircleCoordinates),
        (ProperBandQuadruple v) → ∀ (i : Fin 4), ∀ (k : Fin 4), (i ≠ k) → (0 < (v i).1) → (0 < (v
        k).1) → dist (((v i).2 : Complex) / (v i).1) (((v k).2 : Complex) / (v k).1) = 1 / (v
        i).1 + 1 / (v k).1) → (∀ (a : Complex), ∀ (x : Complex), ∀ (z : Complex), ∀ (ρ : Real), ∀
        (R : Real), ∀ (s : Real), (0 < ρ + R) → (dist a x = ρ + R) → (dist a z = ρ + s) → (dist x
        z = R + s) → ((x - a) * (starRingEnd Complex) (z - a)).re / (ρ + R) = ρ + s * (ρ - R) /
        (ρ + R)) →
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (0 < r j.succ) → (0 < r 0) → (0 < r j.succ + r 0) → (dist (p j.succ) (p 0) = r j.succ + r 0)
        → ∀ (D : ℂ →ᵃ[ℝ] ℝ), (∀ (z : ℂ), (D : ℂ → ℝ) z = ((p (0 : Fin (4 : ℕ)) - p j.succ) *
        (starRingEnd ℂ : ℂ → ℂ) (z - p j.succ)).re / (r j.succ + r (0 : Fin (4 : ℕ)))) → ∀ z ∈
      P4909T1ParentPolygon L (P4828T1Step (P4828T1Rotate q j)),
      r j.succ < D z := by
  classical
  intro L q hq hs j hj circleDistance externalProjection p r hr hR hden hax D hD
  have hroot := (ProperBandCurvatureStructure q hq).1
  have hlt : r 0 < r j.succ := by
    apply one_div_lt_one_div_of_lt (by exact_mod_cast hj)
    exact_mod_cast hq.2 j
  have hnorm : ‖p 0 - p j.succ‖ = r j.succ + r 0 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hax
  have hDx : D (p 0) = r j.succ + r 0 := by
    rw [hD, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hnorm]
    field_simp
  let u := P4828T1Step (P4828T1Rotate q j)
  have slot (k : Fin 3) : u k.succ =
      if k = 0 then q 0 else q ((k + j).succ) := by
    fin_cases k <;> fin_cases j <;> rfl
  by_cases hall : ∀ i : Fin 3, 0 < (q i.succ).1
  · have hupos (k : Fin 3) : 0 < (u k.succ).1 := by
      rw [slot]
      split_ifs
      · exact hroot
      · exact hall (k + j)
    have hc (k : Fin 3) : r j.succ <
        D ((u k.succ).2 / ((u k.succ).1 : ℝ)) := by
      rw [slot]
      split_ifs with hk
      · change r j.succ < D (p 0)
        rw [hDx]
        linarith
      · have hkj : k + j ≠ j := by
          intro he
          have hv := congrArg Fin.val he
          omega
        have ha := circleDistance q hq j.succ (k + j).succ
          (fun he => hkj (Fin.succ_inj.mp he).symm) hj (hall _)
        have hx := circleDistance q hq 0 (k + j).succ
          (Fin.succ_ne_zero _).symm hroot (hall _)
        change r j.succ < D (p (k + j).succ)
        rw [hD, externalProjection (p j.succ) (p 0) (p (k + j).succ)
          (r j.succ) (r 0) (r (k + j).succ) hden hax ha hx]
        have hrk : 0 < r (k + j).succ :=
          one_div_pos.mpr (by exact_mod_cast hall (k + j))
        have hh : 0 < r (k + j).succ * (r j.succ - r 0) /
            (r j.succ + r 0) :=
          div_pos (mul_pos hrk (sub_pos.mpr hlt)) hden
        linarith
    have hhalf : Convex ℝ {z : ℂ | r j.succ < D z} :=
      (convex_Ioi (r j.succ)).affine_preimage D
    have hHull : P4909T1ParentPolygon L u ⊆ {z : ℂ | r j.succ < D z} := by
      apply convexHull_min ?_ hhalf
      rintro z ⟨k, hk, rfl | ⟨l, hl, _⟩⟩
      · exact hc k
      · exact ((ne_of_gt (hupos l)) hl).elim
    exact hHull
  · have facts := ProperBandCurvatureStructure q hq
    obtain ⟨l, hl⟩ : ∃ l : Fin 3, (q l.succ).1 = 0 := by
      by_contra hn
      push Not at hn
      exact hall (fun i => lt_of_le_of_ne (facts.2.1 i) (Ne.symm (hn i)))
    have hjl : j ≠ l := by
      intro he
      subst j
      omega
    obtain ⟨b, hbl, hbj⟩ : ∃ b : Fin 3, b ≠ l ∧ b ≠ j := by
      fin_cases l <;> fin_cases j
      all_goals try exact (hjl rfl).elim
      all_goals first
        | exact ⟨0, by decide, by decide⟩
        | exact ⟨1, by decide, by decide⟩
        | exact ⟨2, by decide, by decide⟩
    have hb : 0 < (q b.succ).1 := by
      have hn : (q b.succ).1 ≠ 0 := fun he => hbl (facts.2.2 b l he hl)
      exact lt_of_le_of_ne (facts.2.1 b) (Ne.symm hn)
    let h : ℝ := if (q l.succ).2 = -1 then L else L + 2
    let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
    let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
    have hσ : σ ^ 2 = 1 := by dsimp [σ]; split_ifs <;> norm_num
    have hσmul : σ * σ = 1 := by nlinarith [hσ]
    have signed (i : Fin 4) (hi : 0 < (q i).1) :
    σ * ((p i).re - h) = r i := OmittedHullGeometry.signed L q hs l hl i hi
    have hab : dist (p j.succ) (p b.succ) = r j.succ + r b.succ :=
      circleDistance q hq j.succ b.succ
        (fun he => hbj (Fin.succ_inj.mp he).symm) hj hb
    have hxb : dist (p 0) (p b.succ) = r 0 + r b.succ :=
      circleDistance q hq 0 b.succ (Fin.succ_ne_zero _).symm hroot hb
    have hhull := (P4953T1LiteralHulls L q l j b hjl hbl hbj.symm
      hl hj hb hroot).2.2.1
    change P4909T1ParentPolygon L (P4828T1Step (P4828T1Rotate q j)) =
      convexHull ℝ ({p 0, p b.succ, foot (p 0), foot (p b.succ)} : Set ℂ) at hhull
    have hsq (v w : ℂ) (t : ℝ) (ht : dist v w = t) :
        (v.re - w.re) ^ 2 + (v.im - w.im) ^ 2 = t ^ 2 := by
      have hn : Complex.normSq (v - w) = t ^ 2 := by
        rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, ht]
      rw [Complex.normSq_sub] at hn
      simp [Complex.normSq, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hn
      nlinarith
    have haxSq := hsq (p j.succ) (p 0) (r j.succ + r 0) hax
    have habSq := hsq (p j.succ) (p b.succ) (r j.succ + r b.succ) hab
    have hxbSq := hsq (p 0) (p b.succ) (r 0 + r b.succ) hxb
    have rel (i : Fin 4) (hi : 0 < (q i).1) :
        (p i).re - h = σ * r i := by
      calc
        (p i).re - h = σ * (σ * ((p i).re - h)) := by
          rw [← mul_assoc, hσmul]
          ring
        _ = σ * r i := by rw [signed i hi]
    have coord0 : (p 0).re = h + σ * r 0 := by linarith [rel 0 hroot]
    have coorda : (p j.succ).re = h + σ * r j.succ := by linarith [rel j.succ hj]
    have coordb : (p b.succ).re = h + σ * r b.succ := by linarith [rel b.succ hb]
    have haxRe : (p j.succ).re - (p 0).re =
        σ * (r j.succ - r 0) := by
      rw [coorda, coord0]
      ring
    have habRe : (p j.succ).re - (p b.succ).re =
        σ * (r j.succ - r b.succ) := by
      rw [coorda, coordb]
      ring
    have hxbRe : (p 0).re - (p b.succ).re =
        σ * (r 0 - r b.succ) := by
      rw [coord0, coordb]
      ring
    have haxReSq : ((p j.succ).re - (p 0).re) ^ 2 =
        (r j.succ - r 0) ^ 2 := by
      calc
        _ = (σ * (r j.succ - r 0)) ^ 2 := by rw [haxRe]
        _ = _ := by rw [mul_pow, hσ]; ring
    have habReSq : ((p j.succ).re - (p b.succ).re) ^ 2 =
        (r j.succ - r b.succ) ^ 2 := by
      calc
        _ = (σ * (r j.succ - r b.succ)) ^ 2 := by rw [habRe]
        _ = _ := by rw [mul_pow, hσ]; ring
    have hxbReSq : ((p 0).re - (p b.succ).re) ^ 2 =
        (r 0 - r b.succ) ^ 2 := by
      calc
        _ = (σ * (r 0 - r b.succ)) ^ 2 := by rw [hxbRe]
        _ = _ := by rw [mul_pow, hσ]; ring
    have hd2 : ((p 0).im - (p j.succ).im) ^ 2 = 4 * r j.succ * r 0 := by
      nlinarith only [haxSq, haxReSq]
    have he2 : ((p b.succ).im - (p j.succ).im) ^ 2 =
        4 * r j.succ * r b.succ := by
      nlinarith only [habSq, habReSq]
    have hde : ((p 0).im - (p j.succ).im) *
        ((p b.succ).im - (p j.succ).im) =
        2 * r j.succ * r 0 + 2 * r j.succ * r b.succ -
          2 * r 0 * r b.succ := by
      have hv : ((p 0).im - (p b.succ).im) ^ 2 =
          4 * r 0 * r b.succ := by nlinarith only [hxbSq, hxbReSq]
      nlinarith only [hd2, he2, hv]
    have hfootx : D (foot (p 0)) = r j.succ +
    2 * r j.succ * r 0 / (r j.succ + r 0) := OmittedHullGeometry.hfootx L q j hr hR D hD l hσ
        coord0 coorda hd2
    have hfootb : D (foot (p b.succ)) = r j.succ +
    2 * r b.succ * (r j.succ - r 0) /
      (r j.succ + r 0) := OmittedHullGeometry.hfootb L q j hr hR D hD l b hσ coord0 coorda hde
    have hcB : r j.succ < D (p b.succ) := OmittedHullGeometry.hcB q hq j hj externalProjection
        hden hax D hD b hb hab hxb
    have hfx : r j.succ < D (foot (p 0)) := by
      rw [hfootx]
      have : 0 < 2 * r j.succ * r 0 / (r j.succ + r 0) := by positivity
      linarith
    have hfb : r j.succ < D (foot (p b.succ)) := by
      rw [hfootb]
      have hlt : r 0 < r j.succ := by
        apply one_div_lt_one_div_of_lt (by exact_mod_cast hj)
        exact_mod_cast hq.2 j
      have : 0 < 2 * r b.succ * (r j.succ - r 0) /
          (r j.succ + r 0) := by positivity
      linarith
    have hhalf : Convex ℝ {z : ℂ | r j.succ < D z} :=
      (convex_Ioi (r j.succ)).affine_preimage D
    rw [hhull]
    apply convexHull_min ?_ hhalf
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · change r j.succ < D (p 0)
      rw [hDx]
      linarith
    constructor
    · exact hcB
    constructor
    · exact hfx
    · exact hfb

end OmittedHullBound

theorem P5050T1OmittedHullSeparation (L : ℝ)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q) (j : Fin 3) (hj : 0 < (q j.succ).1) :
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    ∃ D : ℂ →ᵃ[ℝ] ℝ,
      (∀ z, D z = ((p 0 - p j.succ) *
        (starRingEnd ℂ) (z - p j.succ)).re / (r j.succ + r 0)) ∧
      (∀ z ∈ Metric.sphere (p j.succ) (r j.succ), D z ≤ r j.succ) ∧
      ∀ z ∈ P4909T1ParentPolygon L (P4828T1Step (P4828T1Rotate q j)),
        r j.succ < D z := by
-- BODY
  have circleDistance (v : Fin 4 → CircleCoordinates)
      (hv : ProperBandQuadruple v) (i k : Fin 4) (hik : i ≠ k)
      (hi : 0 < (v i).1) (hk : 0 < (v k).1) :
      dist (((v i).2 : Complex) / (v i).1)
          (((v k).2 : Complex) / (v k).1) =
        1 / (v i).1 + 1 / (v k).1 := OmittedHullLemmas.circleDistance v hv i k hik hi hk
  have projectionAffine (a x : Complex) (d : Real) (hd : d ≠ 0) :
      ∃ D : Complex →ᵃ[Real] Real,
        ∀ z, D z = ((x - a) * (starRingEnd Complex) (z - a)).re / d :=
            OmittedHullLemmas.projectionAffine a x d hd
  have projectionSphereBound (a x z : Complex) (ρ R : Real)
      (hρ : 0 < ρ) (hden : 0 < ρ + R) (hax : dist a x = ρ + R)
      (hz : dist z a = ρ) :
      ((x - a) * (starRingEnd Complex) (z - a)).re / (ρ + R) ≤ ρ :=
          OmittedHullLemmas.projectionSphereBound a x z ρ R hρ hden hax hz
  have externalProjection (a x z : Complex) (ρ R s : Real)
      (hpos : 0 < ρ + R)
      (hax : dist a x = ρ + R) (haz : dist a z = ρ + s)
      (hxz : dist x z = R + s) :
      ((x - a) * (starRingEnd Complex) (z - a)).re / (ρ + R) =
        ρ + s * (ρ - R) / (ρ + R) := OmittedHullLemmas.externalProjection a x z ρ R s hpos hax
            haz hxz
  dsimp only
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  have hr : 0 < r j.succ := OmittedHullLemmas.hr q j hj
  have hR : 0 < r 0 := OmittedHullLemmas.hR q hq
  have hden : 0 < r j.succ + r 0 := OmittedHullLemmas.hden q j hr hR
  have hax : dist (p j.succ) (p 0) = r j.succ + r 0 := OmittedHullLemmas.hax q hq j hj
      circleDistance
  obtain ⟨D, hD⟩ := projectionAffine (p j.succ) (p 0)
    (r j.succ + r 0) (ne_of_gt hden)
  have hull_bound : ∀ z ∈
      P4909T1ParentPolygon L (P4828T1Step (P4828T1Rotate q j)),
      r j.succ < D z := OmittedHullBound.hull_bound L q hq hs j hj circleDistance
          externalProjection hr hR hden hax D hD
  refine ⟨D, hD, ?_, hull_bound⟩
  · intro z hz
    rw [hD]
    exact projectionSphereBound _ _ _ _ _ hr hden hax (Metric.mem_sphere.mp hz)

end ApollonianSuperharmonic

end

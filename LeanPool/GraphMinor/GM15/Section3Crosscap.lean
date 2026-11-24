/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section3Handle
import LeanPool.GraphMinor.GM14.DiscSlope

import LeanPool.GraphMinor.GM12.Section5Final

/-!
# Graph Minors XV, (3.3): Adding a Crosscap to a Surface Span

This file proves **Graph Minors XV, (3.3)** (`theorem_3_3 : GM12Theorem52Statement →
GM15Theorem33Statement`):
given a `Σ`-span `(H, η, T)` of order `θ`, a region `Λ` of `H` bounded by a circuit containing
vertices `a₁, …, a_φ, b₁, …, b_φ` in circular order (`3 ≤ φ ≤ θ`) such that
`{a₁, …, a_φ, b₁, …, b_φ}` is free with respect to `T`, and `φ` pairwise vertex-disjoint
`η(H)`-paths `P₁, …, P_φ` in `G` joining `η(a_i)` and `η(b_i)`, there exists a `Σ'`-span
`(H', η', T')` of order `φ` on the surface `Σ'` obtained from `Σ` by adding a crosscap.

The proof follows Robertson and Seymour, *Graph Minors. XV. Giant Steps*, pages 120–121:
1. Characterize `bd MobiusBand` as the range of a boundary circle embedding `mobBd : Circle →
  MobiusBand`
   sending antipodal points `z` and `-z` (`z.im > 0`) to `[(u, 0)]` and `[(u, 1)]`
   (`bd_mobiusBand`).
2. Cut `MobiusBand` along one vertical line `{u₀} × [0, 1]` to obtain a striped closed disc in
   `MobiusBand` (`exists_striped_disc_in_mobiusBand`).
3. Construct the unpinched and pinched crosscap splits (`isCappedSplit_crosscap_unpinched`,
   `exists_pinched_crosscapSplit`), verify `IsRigid H'` via `theorem_3_2`, `theorem_3_3_claim_2`,
   and `theorem_3_3_claim_3`, and apply XII (5.2) (`GM12Theorem52Statement`) to conclude
   `theorem_3_3`.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology Metric
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM12 GM14
open scoped unitInterval

universe u v w

/-! ## 1. Boundary and Striped Discs in `MobiusBand` -/

/-- Vertical flip `(u, v) ↦ (u, 1 - v)` on `MobiusBand`. -/
def mobFlip : MobiusBand → MobiusBand :=
  Quotient.lift
    (fun p : unitInterval × unitInterval =>
      Quotient.mk Surface.mobiusSetoid (p.1, unitInterval.symm p.2))
    (by
      intro p q h
      apply Quotient.sound
      rcases mobius_rel h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨h1, h2, by rw [h3]⟩
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨h1, h2, by rw [h3]⟩))

theorem continuous_mobFlip : Continuous mobFlip :=
  Continuous.quotient_lift (continuous_quotient_mk'.comp
    (continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd))) _

theorem mobFlip_involutive : Function.Involutive mobFlip := by
  intro y
  obtain ⟨⟨u, v⟩, rfl⟩ := Quotient.exists_rep y
  change Quotient.mk Surface.mobiusSetoid (u, unitInterval.symm (unitInterval.symm v)) =
    Quotient.mk Surface.mobiusSetoid (u, v)
  simp

/-- Horizontal half-shift on `unitInterval × unitInterval` into `MobiusBand`. -/
noncomputable def mobShiftAux (p : unitInterval × unitInterval) : MobiusBand :=
  if (p.1 : ℝ) ≤ 1 / 2 then
    Quotient.mk Surface.mobiusSetoid
      (projIcc 0 1 zero_le_one ((p.1 : ℝ) + 1 / 2), p.2)
  else
    Quotient.mk Surface.mobiusSetoid
      (projIcc 0 1 zero_le_one ((p.1 : ℝ) - 1 / 2), unitInterval.symm p.2)

theorem continuous_mobShiftAux : Continuous mobShiftAux := by
  unfold mobShiftAux
  refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_fst) continuous_const ?_
  · exact continuous_quotient_mk'.comp (by fun_prop)
  · exact continuous_quotient_mk'.comp (by fun_prop)
  · intro p hp
    have h1 : projIcc 0 1 zero_le_one ((p.1 : ℝ) + 1 / 2) = 1 := by
      rw [projIcc_of_mem zero_le_one ⟨by linarith, by linarith⟩]
      ext
      dsimp
      linarith
    have h0 : projIcc 0 1 zero_le_one ((p.1 : ℝ) - 1 / 2) = 0 := by
      rw [projIcc_of_mem zero_le_one ⟨by linarith, by linarith⟩]
      ext
      dsimp
      linarith
    rw [h1, h0]
    apply Quotient.sound
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl, by simp⟩)

/-- Horizontal half-shift on `MobiusBand`, sending `[(0, v)]` to `[(1/2, v)]`. -/
noncomputable def mobShift : MobiusBand → MobiusBand :=
  Quotient.lift mobShiftAux (by
    have hrel : ∀ p q : unitInterval × unitInterval,
        p.1 = 0 → q.1 = 1 → q.2 = unitInterval.symm p.2 → mobShiftAux p = mobShiftAux q := by
      intro p q hp1 hq1 hq2
      dsimp [mobShiftAux]
      simp only [hp1, hq1, hq2, Icc.coe_zero, Icc.coe_one, zero_add, unitInterval.symm_symm]
      norm_num
    intro p q h
    rcases mobius_rel h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rfl
    · exact hrel p q h1 h2 h3
    · exact (hrel q p h1 h2 h3).symm)

theorem continuous_mobShift : Continuous mobShift :=
  Continuous.quotient_lift continuous_mobShiftAux _

theorem mobShift_mobShift (y : MobiusBand) : mobShift (mobShift y) = mobFlip y := by
  obtain ⟨⟨u, v⟩, rfl⟩ := Quotient.exists_rep y
  change mobShift (mobShiftAux (u, v)) =
    Quotient.mk Surface.mobiusSetoid (u, unitInterval.symm v)
  dsimp [mobShiftAux]
  split_ifs with hu
  · have hmem : (u : ℝ) + 1 / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [u.2.1], by linarith⟩
    have hproj : projIcc 0 1 zero_le_one ((u : ℝ) + 1 / 2) = ⟨(u : ℝ) + 1 / 2, hmem⟩ :=
      projIcc_of_mem zero_le_one hmem
    change mobShiftAux (projIcc 0 1 zero_le_one ((u : ℝ) + 1 / 2), v) = _
    rw [hproj]
    dsimp [mobShiftAux]
    by_cases hzero : (u : ℝ) = 0
    · have hu0 : u = 0 := Subtype.ext hzero
      subst hu0
      simp only [Icc.coe_zero, zero_add, le_refl, ↓reduceIte]
      have h1 : projIcc 0 1 zero_le_one ((1 / 2 : ℝ) + 1 / 2) = 1 := by
        rw [projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩]
        ext; dsimp; norm_num
      rw [h1]
      apply Quotient.sound
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl, by simp⟩)
    · have hgt : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hzero)
      have hnot : ¬ ((u : ℝ) + 1 / 2 ≤ 1 / 2) := by linarith
      simp only [hnot, ↓reduceIte, add_sub_cancel_right]
      have hp : projIcc 0 1 zero_le_one (u : ℝ) = u := by
        rw [projIcc_of_mem zero_le_one u.2]
      rw [hp]
  · have hmem : (u : ℝ) - 1 / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [u.2.2]⟩
    have hproj : projIcc 0 1 zero_le_one ((u : ℝ) - 1 / 2) = ⟨(u : ℝ) - 1 / 2, hmem⟩ :=
      projIcc_of_mem zero_le_one hmem
    change mobShiftAux (projIcc 0 1 zero_le_one ((u : ℝ) - 1 / 2), unitInterval.symm v) = _
    rw [hproj]
    dsimp [mobShiftAux]
    have hle : (u : ℝ) - 1 / 2 ≤ 1 / 2 := by linarith [u.2.2]
    simp only [hle, ↓reduceIte, sub_add_cancel]
    have hp : projIcc 0 1 zero_le_one (u : ℝ) = u := by
      rw [projIcc_of_mem zero_le_one u.2]
    rw [hp]

/-- Homeomorphism of `MobiusBand` shifting the horizontal coordinate by `1 / 2`. -/
noncomputable def mobShiftHomeo : MobiusBand ≃ₜ MobiusBand where
  toFun := mobShift
  invFun := fun y => mobFlip (mobShift y)
  left_inv y := by
    dsimp
    rw [mobShift_mobShift, mobFlip_involutive]
  right_inv y := by
    dsimp
    have hflip : ∀ x, mobShift (mobFlip x) = mobFlip (mobShift x) := by
      intro x
      have h1 : mobShift (mobShift (mobShift x)) = mobShift (mobFlip x) :=
        congrArg mobShift (mobShift_mobShift x)
      rw [mobShift_mobShift (mobShift x)] at h1
      exact h1.symm
    rw [hflip, mobShift_mobShift, mobFlip_involutive]
  continuous_toFun := continuous_mobShift
  continuous_invFun := continuous_mobFlip.comp continuous_mobShift

/-- Any point `[(u, v)]` in `MobiusBand` with `0 < u < 1` and `0 < v < 1` is an interior point. -/
theorem mobius_interior_strict {u v : unitInterval}
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1) :
    IsInteriorPoint (Quotient.mk Surface.mobiusSetoid (u, v)) := by
  set s : ℝ := 1 - 2 * (u : ℝ)
  set d : ℝ := 2 * (v : ℝ) - 1
  let w : ℂ := ⟨(s + d) / 2, (s - d) / 2⟩
  have hw : nn w < 1 := by
    simp only [nn, w]
    rcases abs_cases ((s + d) / 2) with h1 | h1 <;>
      rcases abs_cases ((s - d) / 2) with h2 | h2 <;>
      linarith
  have hz : ‖mu w‖ < 1 := by rwa [norm_mu]
  have hmem : ((0 : ℕ), mu w) ∈ Dsk (sW mobW) := by
    refine ⟨?_, hz.le⟩
    rw [sW_zero]
    simp [mobW]
  have hz' : ‖((0 : ℕ), mu w).2‖ < 1 := hz
  have h3 : IsInteriorPoint ((fun a : ℕ × ℂ => mobG a.2) (0, mu w)) :=
    isInteriorPoint_of_lt (W := sW mobW) (finW_sW mobW) presents_mob hmem hz'
  replace h3 : IsInteriorPoint (mobG (mu w)) := h3
  have e : mobP (mu w) = (u, v) := by
    apply Prod.ext
    · apply Subtype.ext
      rw [mobP_fst hz.le]
      simp only [mobU, cylS, nu_mu, w]
      linarith
    · apply Subtype.ext
      rw [mobP_snd hz.le]
      simp only [mobV, nu_mu, w]
      linarith
  have h4 : mobG (mu w) = Quotient.mk Surface.mobiusSetoid (u, v) := by
    simp only [mobG, e]
  rwa [h4] at h3

/-- Any point `[(u, v)]` in `MobiusBand` with `0 < v < 1` is an interior point. -/
theorem mobius_interior {u v : unitInterval} (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1) :
    IsInteriorPoint (Quotient.mk Surface.mobiusSetoid (u, v)) := by
  rcases eq_or_lt_of_le u.2.1 with hu0 | hu0
  · have hu : u = 0 := Subtype.ext hu0.symm
    subst hu
    let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    have hshift : mobShiftHomeo (Quotient.mk Surface.mobiusSetoid (0, v)) =
        Quotient.mk Surface.mobiusSetoid (half, v) := by
      change mobShiftAux (0, v) = Quotient.mk Surface.mobiusSetoid (half, v)
      dsimp [mobShiftAux]
      have hle : (0 : ℝ) ≤ 1 / 2 := by norm_num
      simp only [hle, ↓reduceIte, zero_add]
      congr 2
      exact projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩
    have hint : IsInteriorPoint (Quotient.mk Surface.mobiusSetoid (half, v)) :=
      mobius_interior_strict (by change (0 : ℝ) < 1 / 2; norm_num)
        (by change (1 / 2 : ℝ) < 1; norm_num) hv0 hv1
    rw [← hshift] at hint
    exact (isInteriorPoint_homeomorph_iff mobShiftHomeo _).mp hint
  · rcases eq_or_lt_of_le u.2.2 with hu1 | hu1
    · have hu : u = 1 := Subtype.ext hu1
      subst hu
      have heq : Quotient.mk Surface.mobiusSetoid (1, v) =
          Quotient.mk Surface.mobiusSetoid (0, unitInterval.symm v) := by
        apply Quotient.sound
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl, by simp⟩)
      rw [heq]
      let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
      have hshift : mobShiftHomeo (Quotient.mk Surface.mobiusSetoid (0, unitInterval.symm v)) =
          Quotient.mk Surface.mobiusSetoid (half, unitInterval.symm v) := by
        change mobShiftAux (0, unitInterval.symm v) = _
        dsimp [mobShiftAux]
        have hle : (0 : ℝ) ≤ 1 / 2 := by norm_num
        simp only [hle, ↓reduceIte, zero_add]
        congr 2
        exact projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩
      have hint : IsInteriorPoint (Quotient.mk Surface.mobiusSetoid (half, unitInterval.symm v)) :=
        mobius_interior_strict (by change (0 : ℝ) < 1 / 2; norm_num)
          (by change (1 / 2 : ℝ) < 1; norm_num)
          (by simp only [unitInterval.coe_symm_eq]; linarith)
          (by simp only [unitInterval.coe_symm_eq]; linarith)
      rw [← hshift] at hint
      exact (isInteriorPoint_homeomorph_iff mobShiftHomeo _).mp hint
    · exact mobius_interior_strict hu0 hu1 hv0 hv1

/-- Upper semicircle parametrization from `unitInterval` to `Circle`:
`u ↦ ⟨1 - 2u, √(1 - (1 - 2u)²)⟩`. -/
noncomputable def circleTop (u : unitInterval) : Circle :=
  ⟨⟨1 - 2 * (u : ℝ), Real.sqrt (1 - (1 - 2 * (u : ℝ)) ^ 2)⟩, by
    refine mem_sphere_zero_iff_norm.mpr ?_
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    dsimp
    have hnonneg : 0 ≤ 1 - (1 - 2 * (u : ℝ)) ^ 2 := by
      have : 1 - (1 - 2 * (u : ℝ)) ^ 2 = 4 * (u : ℝ) * (1 - (u : ℝ)) := by ring
      rw [this]
      nlinarith [u.2.1, u.2.2]
    rw [Real.sq_sqrt hnonneg, add_sub_cancel, Real.sqrt_one]⟩

/-- Lower semicircle parametrization from `unitInterval` to `Circle`:
`u ↦ ⟨2u - 1, -√(1 - (1 - 2u)²)⟩`. -/
noncomputable def circleBot (u : unitInterval) : Circle :=
  ⟨⟨2 * (u : ℝ) - 1, - Real.sqrt (1 - (1 - 2 * (u : ℝ)) ^ 2)⟩, by
    refine mem_sphere_zero_iff_norm.mpr ?_
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    dsimp
    have hnonneg : 0 ≤ 1 - (1 - 2 * (u : ℝ)) ^ 2 := by
      have : 1 - (1 - 2 * (u : ℝ)) ^ 2 = 4 * (u : ℝ) * (1 - (u : ℝ)) := by ring
      rw [this]
      nlinarith [u.2.1, u.2.2]
    have hsq : (2 * (u : ℝ) - 1) ^ 2 = (1 - 2 * (u : ℝ)) ^ 2 := by ring
    rw [neg_sq, Real.sq_sqrt hnonneg, hsq, add_sub_cancel, Real.sqrt_one]⟩

theorem continuous_circleTop : Continuous circleTop := by
  unfold circleTop
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous (fun u : unitInterval => (1 - 2 * (u : ℝ) : ℂ)) := by fun_prop
  have h2 : Continuous (fun u : unitInterval =>
      ((Real.sqrt (1 - (1 - 2 * (u : ℝ)) ^ 2) : ℝ) : ℂ) * Complex.I) := by fun_prop
  refine (h1.add h2).congr fun u => ?_
  apply Complex.ext <;> simp

theorem continuous_circleBot : Continuous circleBot := by
  unfold circleBot
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous (fun u : unitInterval => (2 * (u : ℝ) - 1 : ℂ)) := by fun_prop
  have h2 : Continuous (fun u : unitInterval =>
      ((- Real.sqrt (1 - (1 - 2 * (u : ℝ)) ^ 2) : ℝ) : ℂ) * Complex.I) := by fun_prop
  refine (h1.add h2).congr fun u => ?_
  apply Complex.ext <;> simp

@[simp]
theorem circleTop_zero : circleTop 0 = 1 := by
  apply Subtype.ext
  apply Complex.ext <;> simp [circleTop]

@[simp]
theorem circleTop_one : circleTop 1 = -1 := by
  apply Subtype.ext
  apply Complex.ext <;> norm_num [circleTop]

@[simp]
theorem circleBot_zero : circleBot 0 = -1 := by
  apply Subtype.ext
  apply Complex.ext <;> norm_num [circleBot]

@[simp]
theorem circleBot_one : circleBot 1 = 1 := by
  apply Subtype.ext
  apply Complex.ext <;> norm_num [circleBot]

theorem circleTop_im_nonneg (u : unitInterval) : 0 ≤ (circleTop u : ℂ).im :=
  Real.sqrt_nonneg _

theorem circleBot_im_nonpos (u : unitInterval) : (circleBot u : ℂ).im ≤ 0 := by
  change - Real.sqrt _ ≤ 0
  linarith [Real.sqrt_nonneg (1 - (1 - 2 * (u : ℝ)) ^ 2)]

/-- First coordinate on `unitInterval` of a point `z : Circle` on the upper semicircle. -/
noncomputable def mobBdTopU (z : Circle) : unitInterval :=
  projIcc 0 1 zero_le_one ((1 - (z : ℂ).re) / 2)

/-- First coordinate on `unitInterval` of a point `z : Circle` on the lower semicircle. -/
noncomputable def mobBdBotU (z : Circle) : unitInterval :=
  projIcc 0 1 zero_le_one ((1 + (z : ℂ).re) / 2)

theorem circle_re_mem_Icc (z : Circle) : (z : ℂ).re ∈ Icc (-1 : ℝ) 1 := by
  have h1 : |(z : ℂ).re| ≤ ‖(z : ℂ)‖ := Complex.abs_re_le_norm z
  rw [Circle.norm_coe] at h1
  exact abs_le.mp h1

theorem circle_re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have h := Complex.normSq_eq_norm_sq (z : ℂ)
  rw [Circle.norm_coe, one_pow, Complex.normSq_apply] at h
  linarith

theorem mobBdTopU_coe (z : Circle) : (mobBdTopU z : ℝ) = (1 - (z : ℂ).re) / 2 := by
  have hre := circle_re_mem_Icc z
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hre.2], by linarith [hre.1]⟩)

theorem mobBdBotU_coe (z : Circle) : (mobBdBotU z : ℝ) = (1 + (z : ℂ).re) / 2 := by
  have hre := circle_re_mem_Icc z
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hre.1], by linarith [hre.2]⟩)

@[simp]
theorem mobBdTopU_circleTop (u : unitInterval) : mobBdTopU (circleTop u) = u := by
  apply Subtype.ext
  rw [mobBdTopU_coe]
  change (1 - (1 - 2 * (u : ℝ))) / 2 = (u : ℝ)
  ring

@[simp]
theorem mobBdBotU_circleBot (u : unitInterval) : mobBdBotU (circleBot u) = u := by
  apply Subtype.ext
  rw [mobBdBotU_coe]
  change (1 + (2 * (u : ℝ) - 1)) / 2 = (u : ℝ)
  ring

theorem circleTop_mobBdTopU {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    circleTop (mobBdTopU z) = z := by
  have hsq := circle_re_sq_add_im_sq z
  apply Subtype.ext
  apply Complex.ext
  · change 1 - 2 * (mobBdTopU z : ℝ) = (z : ℂ).re
    rw [mobBdTopU_coe]
    ring
  · change Real.sqrt (1 - (1 - 2 * (mobBdTopU z : ℝ)) ^ 2) = (z : ℂ).im
    rw [mobBdTopU_coe]
    have heq : 1 - (1 - 2 * ((1 - (z : ℂ).re) / 2)) ^ 2 = (z : ℂ).im ^ 2 := by linarith
    rw [heq, Real.sqrt_sq hz]

theorem circleBot_mobBdBotU {z : Circle} (hz : (z : ℂ).im ≤ 0) :
    circleBot (mobBdBotU z) = z := by
  have hsq := circle_re_sq_add_im_sq z
  apply Subtype.ext
  apply Complex.ext
  · change 2 * (mobBdBotU z : ℝ) - 1 = (z : ℂ).re
    rw [mobBdBotU_coe]
    ring
  · change - Real.sqrt (1 - (1 - 2 * (mobBdBotU z : ℝ)) ^ 2) = (z : ℂ).im
    rw [mobBdBotU_coe]
    have heq : 1 - (1 - 2 * ((1 + (z : ℂ).re) / 2)) ^ 2 = (- (z : ℂ).im) ^ 2 := by linarith
    rw [heq, Real.sqrt_sq (by linarith), neg_neg]

/-- Boundary circle parametrization of `MobiusBand`:
maps the upper semicircle (`0 ≤ z.im`) to `[(mobBdTopU z, 0)]` and the lower semicircle
(`z.im ≤ 0`) to `[(mobBdBotU z, 1)]`. -/
noncomputable def mobBd (z : Circle) : MobiusBand :=
  if 0 ≤ (z : ℂ).im then
    Quotient.mk Surface.mobiusSetoid (mobBdTopU z, 0)
  else
    Quotient.mk Surface.mobiusSetoid (mobBdBotU z, 1)

theorem mobBd_of_im_nonneg {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    mobBd z = Quotient.mk Surface.mobiusSetoid (mobBdTopU z, 0) := by
  dsimp [mobBd]
  simp only [hz, ↓reduceIte]

theorem mobBd_of_im_nonpos {z : Circle} (hz : (z : ℂ).im ≤ 0) :
    mobBd z = Quotient.mk Surface.mobiusSetoid (mobBdBotU z, 1) := by
  dsimp [mobBd]
  split_ifs with h
  · have him0 : (z : ℂ).im = 0 := le_antisymm hz h
    have hsq := circle_re_sq_add_im_sq z
    rw [him0] at hsq
    have hre_sq : (z : ℂ).re ^ 2 = 1 := by linarith
    rcases sq_eq_one_iff.mp hre_sq with hre1 | hre_neg1
    · have ht : mobBdTopU z = 0 := by
        apply Subtype.ext; rw [mobBdTopU_coe, hre1]; norm_num
      have hb : mobBdBotU z = 1 := by
        apply Subtype.ext; rw [mobBdBotU_coe, hre1]; norm_num
      rw [ht, hb]
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ ⟨rfl, rfl, by simp⟩
    · have ht : mobBdTopU z = 1 := by
        apply Subtype.ext; rw [mobBdTopU_coe, hre_neg1]; norm_num
      have hb : mobBdBotU z = 0 := by
        apply Subtype.ext; rw [mobBdBotU_coe, hre_neg1]; norm_num
      rw [ht, hb]
      apply Quotient.sound
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl, by simp⟩)
  · rfl

@[simp]
theorem mobBd_circleTop (u : unitInterval) :
    mobBd (circleTop u) = Quotient.mk Surface.mobiusSetoid (u, 0) := by
  rw [mobBd_of_im_nonneg (circleTop_im_nonneg u), mobBdTopU_circleTop]

@[simp]
theorem mobBd_circleBot (u : unitInterval) :
    mobBd (circleBot u) = Quotient.mk Surface.mobiusSetoid (u, 1) := by
  rw [mobBd_of_im_nonpos (circleBot_im_nonpos u), mobBdBotU_circleBot]

theorem continuous_mobBd : Continuous mobBd := by
  unfold mobBd
  refine Continuous.if_le ?_ ?_ continuous_const
    (Complex.continuous_im.comp continuous_subtype_val) ?_
  · unfold mobBdTopU
    exact continuous_quotient_mk'.comp (by fun_prop)
  · unfold mobBdBotU
    exact continuous_quotient_mk'.comp (by fun_prop)
  · intro z hz
    have h := mobBd_of_im_nonpos (z := z) (by linarith)
    dsimp [mobBd] at h
    have h0 : 0 ≤ (z : ℂ).im := by linarith
    simpa [h0] using h

theorem injective_mobBd : Function.Injective mobBd := by
  intro z₁ z₂ heq
  by_cases h1 : 0 ≤ (z₁ : ℂ).im <;> by_cases h2 : 0 ≤ (z₂ : ℂ).im
  · rw [mobBd_of_im_nonneg h1, mobBd_of_im_nonneg h2] at heq
    rcases mobius_rel (Quotient.exact heq) with h | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
    · have hu : mobBdTopU z₁ = mobBdTopU z₂ := Prod.ext_iff.mp h |>.1
      rw [← circleTop_mobBdTopU h1, ← circleTop_mobBdTopU h2, hu]
    · exact absurd (congrArg Subtype.val h3) (by simp)
    · exact absurd (congrArg Subtype.val h3) (by simp)
  · have h2' : (z₂ : ℂ).im < 0 := lt_of_not_ge h2
    rw [mobBd_of_im_nonneg h1, mobBd_of_im_nonpos h2'.le] at heq
    rcases mobius_rel (Quotient.exact heq) with h | ⟨hu1, hu2, _⟩ | ⟨hu2, hu1, _⟩
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.mp h).2) (by simp)
    · have hre : (z₂ : ℂ).re = 1 := by
        have hval : (mobBdBotU z₂ : ℝ) = 1 := congrArg Subtype.val hu2
        rw [mobBdBotU_coe] at hval
        linarith
      have hsq := circle_re_sq_add_im_sq z₂
      rw [hre] at hsq
      nlinarith
    · have hre : (z₂ : ℂ).re = -1 := by
        have hval : (mobBdBotU z₂ : ℝ) = 0 := congrArg Subtype.val hu2
        rw [mobBdBotU_coe] at hval
        linarith
      have hsq := circle_re_sq_add_im_sq z₂
      rw [hre] at hsq
      nlinarith
  · have h1' : (z₁ : ℂ).im < 0 := lt_of_not_ge h1
    rw [mobBd_of_im_nonpos h1'.le, mobBd_of_im_nonneg h2] at heq
    rcases mobius_rel (Quotient.exact heq) with h | ⟨hu1, hu2, _⟩ | ⟨hu2, hu1, _⟩
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.mp h).2) (by simp)
    · have hre : (z₁ : ℂ).re = -1 := by
        have hval : (mobBdBotU z₁ : ℝ) = 0 := congrArg Subtype.val hu1
        rw [mobBdBotU_coe] at hval
        linarith
      have hsq := circle_re_sq_add_im_sq z₁
      rw [hre] at hsq
      nlinarith
    · have hre : (z₁ : ℂ).re = 1 := by
        have hval : (mobBdBotU z₁ : ℝ) = 1 := congrArg Subtype.val hu1
        rw [mobBdBotU_coe] at hval
        linarith
      have hsq := circle_re_sq_add_im_sq z₁
      rw [hre] at hsq
      nlinarith
  · have h1' : (z₁ : ℂ).im < 0 := lt_of_not_ge h1
    have h2' : (z₂ : ℂ).im < 0 := lt_of_not_ge h2
    rw [mobBd_of_im_nonpos h1'.le, mobBd_of_im_nonpos h2'.le] at heq
    rcases mobius_rel (Quotient.exact heq) with h | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
    · have hu : mobBdBotU z₁ = mobBdBotU z₂ := Prod.ext_iff.mp h |>.1
      rw [← circleBot_mobBdBotU h1'.le, ← circleBot_mobBdBotU h2'.le, hu]
    · exact absurd (congrArg Subtype.val h3) (by simp)
    · exact absurd (congrArg Subtype.val h3) (by simp)

theorem isEmbedding_mobBd : IsEmbedding mobBd :=
  (continuous_mobBd.isClosedEmbedding injective_mobBd).isEmbedding

theorem range_mobBd :
    range mobBd = {y : MobiusBand | ∃ u : unitInterval,
      y = Quotient.mk Surface.mobiusSetoid (u, 0) ∨
      y = Quotient.mk Surface.mobiusSetoid (u, 1)} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : 0 ≤ (z : ℂ).im
    · exact ⟨mobBdTopU z, .inl (mobBd_of_im_nonneg hz)⟩
    · exact ⟨mobBdBotU z, .inr (mobBd_of_im_nonpos (lt_of_not_ge hz).le)⟩
  · rintro ⟨u, rfl | rfl⟩
    · exact ⟨circleTop u, mobBd_circleTop u⟩
    · exact ⟨circleBot u, mobBd_circleBot u⟩

/-- The boundary of `MobiusBand` is the range of `mobBd`. -/
theorem bd_mobiusBand : bd MobiusBand = range mobBd := by
  have hsub : bd MobiusBand ⊆ range mobBd := by
    intro y hy
    obtain ⟨⟨u, v⟩, rfl⟩ := Quotient.exists_rep y
    rw [range_mobBd]
    rcases eq_or_lt_of_le v.2.1 with hv0 | hv0
    · exact ⟨u, .inl (by congr 2; exact Subtype.ext hv0.symm)⟩
    · rcases eq_or_lt_of_le v.2.2 with hv1 | hv1
      · exact ⟨u, .inr (by congr 2; exact Subtype.ext hv1)⟩
      · exact (hy (mobius_interior hv0 hv1)).elim
  obtain ⟨m_mob⟩ := nonempty_mob_homeo
  have hO : IsOArc (bd MobiusBand) := isOArc_bd_one m_mob
  exact oarc_eq isEmbedding_mobBd.toHomeomorph hO hsub

/-- Map from `ℂ` to `MobiusBand` used to build striped closed discs by cutting along `{u₀} × [0,
1]`.
Here `z.re - 1 ∈ [0, 1]` is the vertical coordinate `v`, and `z.im` (or `z.im - 1`) is the
horizontal coordinate `u`. -/
noncomputable def mobRectMap (z : ℂ) : MobiusBand :=
  if z.im ≤ 1 then
    Quotient.mk Surface.mobiusSetoid
      (projIcc 0 1 zero_le_one z.im, projIcc 0 1 zero_le_one (z.re - 1))
  else
    Quotient.mk Surface.mobiusSetoid
      (projIcc 0 1 zero_le_one (z.im - 1),
        unitInterval.symm (projIcc 0 1 zero_le_one (z.re - 1)))

theorem continuous_mobRectMap : Continuous mobRectMap := by
  unfold mobRectMap
  refine Continuous.if_le ?_ ?_ Complex.continuous_im continuous_const ?_
  · exact continuous_quotient_mk'.comp (by fun_prop)
  · exact continuous_quotient_mk'.comp (by fun_prop)
  · intro z hz
    have h1 : projIcc 0 1 zero_le_one z.im = 1 := by
      rw [hz, projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩]
      rfl
    have h0 : projIcc 0 1 zero_le_one (z.im - 1) = 0 := by
      rw [hz, sub_self, projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩]
      rfl
    rw [h1, h0]
    apply Quotient.sound
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl, by simp⟩)

theorem injOn_mobRectMap (u₀ : unitInterval) (ε : ℝ)
    (hε0 : 0 < ε) (hε_u0 : ε < (u₀ : ℝ)) (hε_u1 : ε < 1 - (u₀ : ℝ)) :
    InjOn mobRectMap (Icc (1 : ℝ) 2 ×ℂ Icc ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε)) := by
  intro z₁ hz₁ z₂ hz₂ heq
  obtain ⟨hz₁_re, hz₁_im⟩ := Complex.mem_reProdIm.mp hz₁
  obtain ⟨hz₂_re, hz₂_im⟩ := Complex.mem_reProdIm.mp hz₂
  have hv₁ : (projIcc 0 1 zero_le_one (z₁.re - 1) : ℝ) = z₁.re - 1 :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz₁_re.1], by linarith
      [hz₁_re.2]⟩)
  have hv₂ : (projIcc 0 1 zero_le_one (z₂.re - 1) : ℝ) = z₂.re - 1 :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz₂_re.1], by linarith
      [hz₂_re.2]⟩)
  dsimp [mobRectMap] at heq
  split_ifs at heq with h1 h2 h2
  · have hu₁ : (projIcc 0 1 zero_le_one z₁.im : ℝ) = z₁.im :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz₁_im.1], h1⟩)
    have hu₂ : (projIcc 0 1 zero_le_one z₂.im : ℝ) = z₂.im :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz₂_im.1], h2⟩)
    rcases mobius_rel (Quotient.exact heq) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
    · have hp := Prod.ext_iff.mp h
      have him : z₁.im = z₂.im := by linarith [congrArg Subtype.val hp.1]
      have hre : z₁.re = z₂.re := by linarith [congrArg Subtype.val hp.2]
      exact Complex.ext hre him
    · have : (projIcc 0 1 zero_le_one z₁.im : ℝ) = 0 := congrArg Subtype.val ha
      linarith [hz₁_im.1]
    · have : (projIcc 0 1 zero_le_one z₂.im : ℝ) = 0 := congrArg Subtype.val ha
      linarith [hz₂_im.1]
  · have hu₁ : (projIcc 0 1 zero_le_one z₁.im : ℝ) = z₁.im :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz₁_im.1], h1⟩)
    have hu₂ : (projIcc 0 1 zero_le_one (z₂.im - 1) : ℝ) = z₂.im - 1 :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith, by linarith [hz₂_im.2]⟩)
    rcases mobius_rel (Quotient.exact heq) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
    · have hp := Prod.ext_iff.mp h
      have : z₁.im = z₂.im - 1 := by linarith [congrArg Subtype.val hp.1]
      linarith [hz₁_im.1, hz₂_im.2]
    · have : (projIcc 0 1 zero_le_one z₁.im : ℝ) = 0 := congrArg Subtype.val ha
      linarith [hz₁_im.1]
    · have : (projIcc 0 1 zero_le_one (z₂.im - 1) : ℝ) = 0 := congrArg Subtype.val ha
      linarith
  · have hu₁ : (projIcc 0 1 zero_le_one (z₁.im - 1) : ℝ) = z₁.im - 1 :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith, by linarith [hz₁_im.2]⟩)
    have hu₂ : (projIcc 0 1 zero_le_one z₂.im : ℝ) = z₂.im :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz₂_im.1], h2⟩)
    rcases mobius_rel (Quotient.exact heq) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
    · have hp := Prod.ext_iff.mp h
      have : z₁.im - 1 = z₂.im := by linarith [congrArg Subtype.val hp.1]
      linarith [hz₁_im.2, hz₂_im.1]
    · have : (projIcc 0 1 zero_le_one (z₁.im - 1) : ℝ) = 0 := congrArg Subtype.val ha
      linarith
    · have : (projIcc 0 1 zero_le_one z₂.im : ℝ) = 0 := congrArg Subtype.val ha
      linarith [hz₂_im.1]
  · have hu₁ : (projIcc 0 1 zero_le_one (z₁.im - 1) : ℝ) = z₁.im - 1 :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith, by linarith [hz₁_im.2]⟩)
    have hu₂ : (projIcc 0 1 zero_le_one (z₂.im - 1) : ℝ) = z₂.im - 1 :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith, by linarith [hz₂_im.2]⟩)
    rcases mobius_rel (Quotient.exact heq) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
    · have hp := Prod.ext_iff.mp h
      have him : z₁.im = z₂.im := by linarith [congrArg Subtype.val hp.1]
      have hsymm : projIcc 0 1 zero_le_one (z₁.re - 1) = projIcc 0 1 zero_le_one (z₂.re - 1) := by
        have := congrArg unitInterval.symm hp.2
        simpa using this
      have hre : z₁.re = z₂.re := by linarith [congrArg Subtype.val hsymm]
      exact Complex.ext hre him
    · have : (projIcc 0 1 zero_le_one (z₁.im - 1) : ℝ) = 0 := congrArg Subtype.val ha
      linarith
    · have : (projIcc 0 1 zero_le_one (z₂.im - 1) : ℝ) = 0 := congrArg Subtype.val ha
      linarith

private theorem compact_set_avoiding_vertical_line_lies_in_open_strip
    (u₀ : unitInterval)
    {K_all : Set MobiusBand} :
    let Q_all : Set (unitInterval × unitInterval) := Quotient.mk Surface.mobiusSetoid ⁻¹' K_all
    let U_set : Set unitInterval := Prod.fst '' Q_all ∪ {0, 1}
    ∀ (ε : ℝ),
    (0 < ε) →
    (ε < (u₀ : ℝ)) →
    (ε < 1 - (u₀ : ℝ)) →
    (ε < infDist u₀ U_set) →
    let U_ε : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Ioo ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε)
    K_all ⊆ mobRectMap '' U_ε := by
  intro Q_all U_set ε hε0 hε_u0 hε_u1 hε_dist U_ε y hy
  obtain ⟨⟨u, v⟩, rfl⟩ := Quotient.exists_rep y
  have hu_U : u ∈ U_set := .inl ⟨(u, v), hy, rfl⟩
  have hdist : Metric.infDist u₀ U_set ≤ dist u₀ u := Metric.infDist_le_dist_of_mem hu_U
  have h_abs : ε < |(u : ℝ) - (u₀ : ℝ)| := by
    have : Dist.dist u₀ u = |(u : ℝ) - (u₀ : ℝ)| := by
      rw [_root_.dist_comm]
      exact Real.dist_eq (u : ℝ) (u₀ : ℝ)
    exact hε_dist.trans_le (this ▸ hdist)
  have hu_ne : (u : ℝ) ≠ (u₀ : ℝ) := by
    intro heq
    rw [heq, sub_self, abs_zero] at h_abs
    exact (not_lt.mpr hε0.le h_abs)
  rcases lt_or_gt_of_ne hu_ne with hlt | hgt
  · have hu_lt : (u : ℝ) < (u₀ : ℝ) - ε := by
      rw [abs_of_neg (by linarith)] at h_abs
      linarith
    rcases eq_or_lt_of_le u.2.1 with hu0_eq | hu0_pos
    · have hu0 : u = 0 := Subtype.ext hu0_eq.symm
      subst hu0
      let z : ℂ := ⟨1 + (1 - (v : ℝ)), 1⟩
      have hz_re : z.re ∈ Icc (1 : ℝ) 2 := by
        constructor <;> dsimp [z] <;> linarith [v.2.2, v.2.1]
      have hz_im : z.im ∈ Ioo ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε) :=
        ⟨by dsimp [z]; linarith [hε_u1], by dsimp [z]; linarith [hε_u0, hu_lt]⟩
      refine ⟨z, Complex.mem_reProdIm.mpr ⟨hz_re, hz_im⟩, ?_⟩
      dsimp [mobRectMap, z]
      simp only [le_refl, ↓reduceIte, add_sub_cancel_left]
      have h1 : projIcc 0 1 zero_le_one (1 : ℝ) = 1 :=
        projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩
      have hv' : projIcc 0 1 zero_le_one (1 - (v : ℝ)) = unitInterval.symm v :=
        projIcc_of_mem zero_le_one (unitInterval.symm v).2
      rw [h1, hv']
      apply Quotient.sound
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl, rfl⟩)
    · let z : ℂ := ⟨1 + (1 - (v : ℝ)), (u : ℝ) + 1⟩
      have hz_re : z.re ∈ Icc (1 : ℝ) 2 := by
        constructor <;> dsimp [z] <;> linarith [v.2.2, v.2.1]
      have hz_im : z.im ∈ Ioo ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε) :=
        ⟨by dsimp [z]; linarith, by dsimp [z]; linarith⟩
      refine ⟨z, Complex.mem_reProdIm.mpr ⟨hz_re, hz_im⟩, ?_⟩
      dsimp [mobRectMap, z]
      have hnot : ¬ ((u : ℝ) + 1 ≤ 1) := by linarith
      simp only [hnot, ↓reduceIte, add_sub_cancel_right, add_sub_cancel_left]
      have hu' : projIcc 0 1 zero_le_one (u : ℝ) = u := projIcc_of_mem zero_le_one u.2
      have hv' : projIcc 0 1 zero_le_one (1 - (v : ℝ)) = unitInterval.symm v :=
        projIcc_of_mem zero_le_one (unitInterval.symm v).2
      rw [hu', hv', unitInterval.symm_symm]
  · have hu_gt : (u₀ : ℝ) + ε < (u : ℝ) := by
      rw [abs_of_pos (by linarith)] at h_abs
      linarith
    let z : ℂ := ⟨1 + (v : ℝ), (u : ℝ)⟩
    have hz_re : z.re ∈ Icc (1 : ℝ) 2 := by
        constructor <;> dsimp [z] <;> linarith [v.2.1, v.2.2]
    have hz_im : z.im ∈ Ioo ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε) :=
      ⟨by dsimp [z]; linarith, by dsimp [z]; linarith [u.2.2]⟩
    refine ⟨z, Complex.mem_reProdIm.mpr ⟨hz_re, hz_im⟩, ?_⟩
    dsimp [mobRectMap, z]
    simp only [u.2.2, ↓reduceIte, add_sub_cancel_left]
    have hu' : projIcc 0 1 zero_le_one (u : ℝ) = u := projIcc_of_mem zero_le_one u.2
    have hv' : projIcc 0 1 zero_le_one (v : ℝ) = v := projIcc_of_mem zero_le_one v.2
    rw [hu', hv']

private theorem closed_strip_avoids_vertical_line
    (u₀ : unitInterval)
    (ε : ℝ)
    (hε0 : 0 < ε)
    (hε_u0 : ε < (u₀ : ℝ))
    (hε_u1 : ε < 1 - (u₀ : ℝ)) :
    let R_ε : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Icc ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε)
    let D_mob : Set MobiusBand := mobRectMap '' R_ε
    Disjoint D_mob (Quotient.mk Surface.mobiusSetoid '' {u₀} ×ˢ univ) := by
  intro R_ε D_mob
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨z, hzR, rfl⟩ ⟨⟨u', v⟩, ⟨hu'_eq, _⟩, heq⟩
  have hu' : u₀ = u' := hu'_eq.symm
  subst hu'
  replace heq := heq.symm
  obtain ⟨_, hz_im⟩ := Complex.mem_reProdIm.mp hzR
  dsimp [mobRectMap] at heq
  split_ifs at heq with h1
  · have hu : (projIcc 0 1 zero_le_one z.im : ℝ) = z.im :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz_im.1], h1⟩)
    rcases mobius_rel (Quotient.exact heq) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
    · have : z.im = (u₀ : ℝ) := by linarith [congrArg Subtype.val (Prod.ext_iff.mp h).1]
      linarith [hz_im.1]
    · have : (projIcc 0 1 zero_le_one z.im : ℝ) = 0 := congrArg Subtype.val ha
      linarith [hz_im.1]
    · have : (u₀ : ℝ) = 0 := congrArg Subtype.val ha
      linarith
  · have hu : (projIcc 0 1 zero_le_one (z.im - 1) : ℝ) = z.im - 1 :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith, by linarith [hz_im.2]⟩)
    rcases mobius_rel (Quotient.exact heq) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
    · have : z.im - 1 = (u₀ : ℝ) := by linarith [congrArg Subtype.val (Prod.ext_iff.mp h).1]
      linarith [hz_im.2]
    · have : (projIcc 0 1 zero_le_one (z.im - 1) : ℝ) = 0 := congrArg Subtype.val ha
      linarith
    · have : (u₀ : ℝ) = 0 := congrArg Subtype.val ha
      linarith

/-- Cutting `MobiusBand` along a vertical line `{u₀} × [0, 1]` (`0 < u₀ < 1`) disjoint from a
closed set `K_all ⊆ MobiusBand` yields a closed disc `D_mob ⊆ MobiusBand` containing `K_all`. -/
theorem exists_striped_disc_in_mobiusBand (u₀ : unitInterval)
    (hu₀0 : 0 < (u₀ : ℝ)) (hu₀1 : (u₀ : ℝ) < 1)
    {K_all : Set MobiusBand} (hK_cl : IsClosed K_all)
    (hK_disj : Disjoint K_all (Quotient.mk Surface.mobiusSetoid '' ({u₀} ×ˢ univ))) :
    ∃ D_mob : Set MobiusBand,
      IsClosedDisc D_mob ∧
      K_all ⊆ D_mob ∧
      Disjoint D_mob (Quotient.mk Surface.mobiusSetoid '' ({u₀} ×ˢ univ)) ∧
      D_mob ∩ bd MobiusBand ⊆ discBd D_mob ∧
      ∀ u_j : unitInterval, 0 < (u_j : ℝ) → (u_j : ℝ) < 1 →
        Quotient.mk Surface.mobiusSetoid '' ({u_j} ×ˢ univ) ⊆ K_all →
        Quotient.mk Surface.mobiusSetoid '' ({u_j} ×ˢ univ) ⊆ D_mob ∧
        (Quotient.mk Surface.mobiusSetoid '' ({u_j} ×ˢ univ)) ∩ discBd D_mob =
          {Quotient.mk Surface.mobiusSetoid (u_j, 0),
           Quotient.mk Surface.mobiusSetoid (u_j, 1)} := by
  let Q_all : Set (unitInterval × unitInterval) :=
    Quotient.mk Surface.mobiusSetoid ⁻¹' K_all
  have hQ_cl : IsClosed Q_all := hK_cl.preimage continuous_quotient_mk'
  let U_set : Set unitInterval := (Prod.fst '' Q_all) ∪ {0, 1}
  have hU_cl : IsClosed U_set :=
    (hQ_cl.isCompact.image continuous_fst).isClosed.union
      ((isClosed_singleton.union isClosed_singleton))
  have hU_ne : U_set.Nonempty := ⟨0, .inr (.inl rfl)⟩
  have hu₀_not_U : u₀ ∉ U_set := by
    rintro (⟨⟨u, v⟩, hp, rfl⟩ | rfl | rfl)
    · exact Set.disjoint_left.mp hK_disj hp ⟨(u, v), ⟨rfl, mem_univ _⟩, rfl⟩
    · exact hu₀0.ne rfl
    · exact hu₀1.ne rfl
  have hdist_pos : 0 < Metric.infDist u₀ U_set :=
    (hU_cl.notMem_iff_infDist_pos hU_ne).mp hu₀_not_U
  let ε : ℝ := min ((u₀ : ℝ) / 2) (min ((1 - (u₀ : ℝ)) / 2) (Metric.infDist u₀ U_set / 2))
  have hε0 : 0 < ε := by
    dsimp [ε]
    refine lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε_u0 : ε < (u₀ : ℝ) := by
    have : ε ≤ (u₀ : ℝ) / 2 := min_le_left _ _
    linarith
  have hε_u1 : ε < 1 - (u₀ : ℝ) := by
    have : ε ≤ (1 - (u₀ : ℝ)) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hε_dist : ε < Metric.infDist u₀ U_set := by
    have : ε ≤ Metric.infDist u₀ U_set / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let R_ε : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Icc ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε)
  let U_ε : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Ioo ((u₀ : ℝ) + ε) ((u₀ : ℝ) + 1 - ε)
  have hR_comp : IsCompact R_ε := isCompact_Icc.reProdIm isCompact_Icc
  have hinj : InjOn mobRectMap R_ε :=
    injOn_mobRectMap u₀ ε hε0 hε_u0 hε_u1
  let D_mob : Set MobiusBand := mobRectMap '' R_ε
  obtain ⟨hD_rect, hbd_rect⟩ :=
    isClosedDisc_rect (a := 1) (b := 2)
      (c := (u₀ : ℝ) + ε) (d := (u₀ : ℝ) + 1 - ε) (by norm_num) (by linarith)
  obtain ⟨hD_img, hbd_img⟩ := hD_rect.image_injOn continuous_mobRectMap.continuousOn hinj
  have hD_disc : IsClosedDisc D_mob := hD_img
  have hD_bd : discBd D_mob = mobRectMap '' frontier R_ε :=
    hbd_img.trans (congrArg (mobRectMap '' ·) hbd_rect)
  have hK_sub_U : K_all ⊆ mobRectMap '' U_ε := by
    exact compact_set_avoiding_vertical_line_lies_in_open_strip u₀ (K_all := K_all) ε
      hε0 hε_u0 hε_u1 hε_dist
  have hU_sub_R : U_ε ⊆ R_ε := fun z hz =>
    Complex.mem_reProdIm.mpr
      ⟨(Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
  have hK_sub_D : K_all ⊆ D_mob := hK_sub_U.trans (image_mono hU_sub_R)
  have hD_disj : Disjoint D_mob (Quotient.mk Surface.mobiusSetoid '' ({u₀} ×ˢ univ)) := by
    exact closed_strip_avoids_vertical_line u₀ ε hε0 hε_u0 hε_u1
  have hbd_sub : D_mob ∩ bd MobiusBand ⊆ discBd D_mob := by
    rw [hD_bd, bd_mobiusBand, range_mobBd]
    rintro _ ⟨⟨z, hzR, rfl⟩, ⟨u, heq⟩⟩
    obtain ⟨hz_re, _⟩ := Complex.mem_reProdIm.mp hzR
    have hv : (projIcc 0 1 zero_le_one (z.re - 1) : ℝ) = z.re - 1 :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz_re.1], by linarith
        [hz_re.2]⟩)
    have hre_12 : z.re = 1 ∨ z.re = 2 := by
      dsimp [mobRectMap] at heq
      split_ifs at heq with h1
      · rcases heq with heq | heq <;>
          rcases mobius_rel (Quotient.exact heq) with h | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
        · left; have := congrArg Subtype.val (Prod.ext_iff.mp h).2; simp only [Icc.coe_zero]
            at this; linarith
        · right; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq,
            Icc.coe_zero] at this; linarith
        · right; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq,
            Icc.coe_zero] at this; linarith
        · right; have := congrArg Subtype.val (Prod.ext_iff.mp h).2; simp only [Icc.coe_one]
            at this; linarith
        · left; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq, Icc.coe_one]
            at this; linarith
        · left; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq, Icc.coe_one]
            at this; linarith
      · rcases heq with heq | heq <;>
          rcases mobius_rel (Quotient.exact heq) with h | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
        · right; have := congrArg Subtype.val (Prod.ext_iff.mp h).2; simp only
            [unitInterval.coe_symm_eq, Icc.coe_zero] at this; linarith
        · left; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq, Icc.coe_zero]
            at this; linarith
        · left; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq, Icc.coe_zero]
            at this; linarith
        · left; have := congrArg Subtype.val (Prod.ext_iff.mp h).2; simp only
            [unitInterval.coe_symm_eq, Icc.coe_one] at this; linarith
        · right; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq, Icc.coe_one]
            at this; linarith
        · right; have := congrArg Subtype.val h3; simp only [unitInterval.coe_symm_eq, Icc.coe_one]
            at this; linarith
    exact ⟨z, reProdIm_mem_frontier_of_re_eq hzR hre_12, rfl⟩
  refine ⟨D_mob, hD_disc, hK_sub_D, hD_disj, hbd_sub, fun u_j hu_j0 hu_j1 hu_j_sub => ?_⟩
  have hu_j_D : Quotient.mk Surface.mobiusSetoid '' ({u_j} ×ˢ univ) ⊆ D_mob :=
    hu_j_sub.trans hK_sub_D
  refine ⟨hu_j_D, Subset.antisymm ?_ ?_⟩
  · rintro y ⟨⟨⟨u', v⟩, ⟨hu'_eq, _⟩, rfl⟩, hy_bd⟩
    have hu' : u_j = u' := hu'_eq.symm
    subst hu'
    obtain ⟨z₁, hz₁U, h₁⟩ := hK_sub_U (hu_j_sub ⟨(u_j, v), ⟨rfl, mem_univ _⟩, rfl⟩)
    rw [hD_bd] at hy_bd
    obtain ⟨z₂, hz₂_fr, h₂⟩ := hy_bd
    have hz₂R : z₂ ∈ R_ε := (hR_comp.isClosed.frontier_eq ▸ hz₂_fr).1
    have hz_eq : z₁ = z₂ := hinj (hU_sub_R hz₁U) hz₂R (h₁.trans h₂.symm)
    subst hz_eq
    obtain ⟨hz₁_re, hz₁_im⟩ := Complex.mem_reProdIm.mp hz₁U
    have hre : z₁.re = 1 ∨ z₁.re = 2 := re_eq_of_mem_frontier_reProdIm hz₂_fr hz₁_im
    dsimp [mobRectMap] at h₁
    split_ifs at h₁ with h1
    · have hu₁ : (projIcc 0 1 zero_le_one z₁.im : ℝ) = z₁.im :=
        congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith [hz₁_im.1], h1⟩)
      have hu_eq : projIcc 0 1 zero_le_one z₁.im = u_j := by
        rcases mobius_rel (Quotient.exact h₁) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
        · exact (Prod.ext_iff.mp h).1
        · have : (projIcc 0 1 zero_le_one z₁.im : ℝ) = 0 := congrArg Subtype.val ha
          linarith [hz₁_im.1]
        · have : (u_j : ℝ) = 0 := congrArg Subtype.val ha
          linarith
      rcases hre with hre1 | hre2
      · left
        rw [← h₁, hre1, sub_self, hu_eq]
        have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
          projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩
        rw [h0]
      · right
        rw [← h₁, hre2, show (2 : ℝ) - 1 = 1 by ring, hu_eq]
        have h1' : projIcc 0 1 zero_le_one (1 : ℝ) = 1 :=
          projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩
        rw [h1']
        rfl
    · have hu₁ : (projIcc 0 1 zero_le_one (z₁.im - 1) : ℝ) = z₁.im - 1 :=
        congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith, by linarith [hz₁_im.2]⟩)
      have hu_eq : projIcc 0 1 zero_le_one (z₁.im - 1) = u_j := by
        rcases mobius_rel (Quotient.exact h₁) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
        · exact (Prod.ext_iff.mp h).1
        · have : (projIcc 0 1 zero_le_one (z₁.im - 1) : ℝ) = 0 := congrArg Subtype.val ha
          linarith
        · have : (u_j : ℝ) = 0 := congrArg Subtype.val ha
          linarith
      rcases hre with hre1 | hre2
      · right
        rw [← h₁, hre1, sub_self, hu_eq]
        have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
          projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩
        rw [h0, unitInterval.symm_zero]
        rfl
      · left
        rw [← h₁, hre2, show (2 : ℝ) - 1 = 1 by ring, hu_eq]
        have h1' : projIcc 0 1 zero_le_one (1 : ℝ) = 1 :=
          projIcc_of_mem zero_le_one ⟨by norm_num, by norm_num⟩
        rw [h1', unitInterval.symm_one]
  · rintro y (rfl | rfl)
    · refine ⟨⟨(u_j, 0), ⟨rfl, mem_univ _⟩, rfl⟩, hbd_sub ⟨hu_j_D ⟨(u_j, 0), ⟨rfl, mem_univ _⟩,
        rfl⟩, ?_⟩⟩
      rw [bd_mobiusBand, range_mobBd]
      exact ⟨u_j, .inl rfl⟩
    · refine ⟨⟨(u_j, 1), ⟨rfl, mem_univ _⟩, rfl⟩, hbd_sub ⟨hu_j_D ⟨(u_j, 1), ⟨rfl, mem_univ _⟩,
        rfl⟩, ?_⟩⟩
      rw [bd_mobiusBand, range_mobBd]
      exact ⟨u_j, .inr rfl⟩

/-! ## 2. Unpinched and Pinched Crosscap Splits -/

/-- A vertical segment `{u} × [0, 1]` (`0 < u < 1`) in `MobiusBand` is a line with ends
`[(u, 0)]` and `[(u, 1)]`. -/
theorem isLineWithEnds_mobVertical (u : unitInterval)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    IsLineWithEnds (Quotient.mk Surface.mobiusSetoid '' ({u} ×ˢ univ))
      (Quotient.mk Surface.mobiusSetoid (u, 0))
      (Quotient.mk Surface.mobiusSetoid (u, 1)) := by
  let f : unitInterval → MobiusBand := fun v => Quotient.mk Surface.mobiusSetoid (u, v)
  have hf_cont : Continuous f :=
    continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)
  have hf_inj : Function.Injective f := by
    intro v₁ v₂ heq
    rcases mobius_rel (Quotient.exact heq) with h | ⟨ha, _, _⟩ | ⟨ha, _, _⟩
    · exact (Prod.ext_iff.mp h).2
    · have : (u : ℝ) = 0 := congrArg Subtype.val ha
      linarith
    · have : (u : ℝ) = 0 := congrArg Subtype.val ha
      linarith
  have hf_emb : IsEmbedding f := (hf_cont.isClosedEmbedding hf_inj).isEmbedding
  have hrange : range f = Quotient.mk Surface.mobiusSetoid '' ({u} ×ˢ univ) := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(u, v), ⟨rfl, mem_univ _⟩, rfl⟩
    · rintro ⟨⟨u', v⟩, ⟨hu', _⟩, rfl⟩
      have : u' = u := hu'
      subst this
      exact ⟨v, rfl⟩
  exact ⟨hf_emb.toHomeomorph.trans (Homeomorph.setCongr hrange), rfl, rfl⟩

/-- Homeomorphism between `Circle` and `bd MobiusBand` induced by `mobBd`. -/
noncomputable def mobBdHomeo : Circle ≃ₜ ↥(bd MobiusBand) :=
  isEmbedding_mobBd.toHomeomorph.trans (Homeomorph.setCongr bd_mobiusBand.symm)

@[simp]
theorem mobBdHomeo_coe (z : Circle) : (mobBdHomeo z : MobiusBand) = mobBd z := rfl

@[simp]
theorem mobBdHomeo_symm_mobBd (z : Circle) (hz : mobBd z ∈ bd MobiusBand) :
    mobBdHomeo.symm ⟨mobBd z, hz⟩ = z := by
  apply mobBdHomeo.injective
  rw [mobBdHomeo.apply_symm_apply]
  rfl

/-- Gluing map from `bd MobiusBand` to `univ \ Λ` sending `mobBd z` to `g z`. -/
noncomputable def crosscapGlueMap {S : Type w} [TopologicalSpace S] {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ))
    (p : ↥(bd MobiusBand)) : ↥(univ \ Λ : Set S) :=
  ⟨(g (mobBdHomeo.symm p)).1, by
    have hmem : (g (mobBdHomeo.symm p)).1 ∈ closure Λ \ Λ := by
      rw [← hΛ_open.frontier_eq, ← subBd_eq_frontier]
      exact (g (mobBdHomeo.symm p)).2
    exact ⟨mem_univ _, hmem.2⟩⟩

@[simp]
theorem crosscapGlueMap_mobBd {S : Type w} [TopologicalSpace S] {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ)) (z : Circle) :
    (crosscapGlueMap hΛ_open g ⟨mobBd z, bd_mobiusBand.symm ▸ ⟨z, rfl⟩⟩).1 = (g z).1 := by
  dsimp [crosscapGlueMap]
  rw [mobBdHomeo_symm_mobBd]

theorem continuous_crosscapGlueMap {S : Type w} [TopologicalSpace S] {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ)) :
    Continuous (crosscapGlueMap hΛ_open g) :=
  Continuous.subtype_mk
    (continuous_subtype_val.comp (g.continuous.comp mobBdHomeo.symm.continuous)) _

theorem injective_crosscapGlueMap {S : Type w} [TopologicalSpace S] {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ)) :
    Function.Injective (crosscapGlueMap hΛ_open g) := by
  intro p q hpq
  have hval := congrArg Subtype.val hpq
  exact mobBdHomeo.symm.injective (g.injective (Subtype.ext hval))

theorem range_crosscapGlueMap {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Λ : Set S}
    (hΛ_open : IsOpen Λ) (hOArc : IsOArc (subBd Λ))
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    (g : Circle ≃ₜ ↥(subBd Λ)) :
    range (crosscapGlueMap hΛ_open g) = bd ↥(univ \ Λ : Set S) := by
  obtain ⟨_, _, hbd_eq, _⟩ := compl_open_isSurface hS hΛ_open hOArc hout
  rw [hbd_eq]
  apply Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    exact (g (mobBdHomeo.symm p)).2
  · intro y hy
    let z := g.symm ⟨y.1, hy⟩
    have hz : (g z).1 = y.1 := congrArg Subtype.val (g.apply_symm_apply ⟨y.1, hy⟩)
    refine ⟨mobBdHomeo z, Subtype.ext ?_⟩
    dsimp [crosscapGlueMap]
    rw [mobBdHomeo.symm_apply_apply, hz]

/-- Unpinched capped split on `GluedSpace hb_inj` for adding a crosscap. -/
theorem isCappedSplit_crosscap_unpinched {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Λ : Set S}
    (hΛ_open : IsOpen Λ) (hΛ : IsOpenDisc Λ) (hOArc : IsOArc (subBd Λ))
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    (g : Circle ≃ₜ ↥(subBd Λ))
    (hb_inj : Function.Injective (crosscapGlueMap hΛ_open g)) :
    let S' := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let S₂ : Set S' := range (GluedSpace.inr hb_inj)
    ∃ (C_unp : Fin 1 → Set S') (ι_unp : ↥S₁ → S),
      GM12.IsCappedSplit C_unp S₁ S₂ ι_unp ![Λ] ∧
      C_unp 0 = GluedSpace.inr hb_inj '' bd MobiusBand ∧
      range ι_unp = univ \ Λ ∧
      ∀ y : ↥(univ \ Λ : Set S),
        ι_unp ⟨GluedSpace.inl hb_inj y, ⟨y, rfl⟩⟩ = y.1 := by
  have : CompactSpace S := hS.1
  have hX_closed : IsClosed (univ \ Λ : Set S) := isClosed_univ.sdiff hΛ_open
  have : CompactSpace ↥(univ \ Λ : Set S) := isCompact_iff_compactSpace.mp hX_closed.isCompact
  obtain ⟨m_mob⟩ := nonempty_mob_homeo
  have hMob_surf : IsSurface MobiusBand := isSurface_of_homeo m_mob (isSurface_model 0 1 1).1
  have : CompactSpace MobiusBand := hMob_surf.1
  have hb_cont := continuous_crosscapGlueMap hΛ_open g
  have hb_range := range_crosscapGlueMap hS hΛ_open hOArc hout g
  have : T2Space (GluedSpace hb_inj) := GluedSpace.t2Space (isClosed_bd MobiusBand) hb_cont hb_inj
  obtain ⟨hS', hConn', _, hS₁_surf, hS₂_surf, hU_eq, hbd₁_eq, hbd₂_eq⟩ :=
    isClosedSurface_of_crosscap_glue hS hΛ hOArc hout hb_cont hb_inj hb_range
  let S' := GluedSpace hb_inj
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  let e₁ : ↥(univ \ Λ : Set S) ≃ₜ ↥S₁ := hinl_emb.isEmbedding.toHomeomorph
  let C_unp : Fin 1 → Set S' := ![GluedSpace.inr hb_inj '' bd MobiusBand]
  let ι_unp : ↥S₁ → S := fun x => (e₁.symm x).1
  have hι_emb : IsEmbedding ι_unp :=
    hX_closed.isClosedEmbedding_subtypeVal.isEmbedding.comp e₁.symm.isEmbedding
  have hι_inl : ∀ y : ↥(univ \ Λ : Set S),
      ι_unp ⟨GluedSpace.inl hb_inj y, ⟨y, rfl⟩⟩ = y.1 := by
    intro y
    change (e₁.symm (e₁ y)).1 = y.1
    rw [e₁.symm_apply_apply]
  have hι_range : range ι_unp = univ \ Λ := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (e₁.symm p).2
    · intro hx
      exact ⟨e₁ ⟨x, hx⟩, hι_inl ⟨x, hx⟩⟩
  have hiUnion1 : ∀ (F : Fin 1 → Set S'), (⋃ i, F i) = F 0 := by
    intro F; ext x; simp
  have hinter_eq : S₁ ∩ S₂ = ⋃ i, C_unp i := by
    rw [hiUnion1]
    exact GluedSpace.range_inl_inter_range_inr_eq_inr hb_inj
  refine ⟨C_unp, ι_unp, ?_, rfl, hι_range, hι_inl⟩
  refine
    { surface := ⟨hS', hConn'⟩
      isOArc := fun i => by
        fin_cases i
        change IsOArc (GluedSpace.inr hb_inj '' bd MobiusBand)
        exact isOArc_image hinr_emb.isEmbedding (isOArc_bd_one m_mob)
      disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
      manifold₁ := hS₁_surf
      manifold₂ := hS₂_surf
      union := hU_eq
      inter := hinter_eq
      bd₁ := hbd₁_eq.symm.trans hinter_eq
      bd₂ := hbd₂_eq.symm.trans hinter_eq
      surface_hat := hS
      isEmbedding := hι_emb
      isOpenDisc := fun i => by fin_cases i; exact hΛ
      bounds := fun i => by
        fin_cases i
        change subBd Λ = ι_unp '' (Subtype.val ⁻¹' (GluedSpace.inr hb_inj '' bd MobiusBand))
        ext x
        constructor
        · intro hx
          have hx_mem : x ∈ univ \ Λ := by
            have hmem : x ∈ closure Λ \ Λ := by
              rw [← hΛ_open.frontier_eq, ← subBd_eq_frontier]
              exact hx
            exact ⟨mem_univ _, hmem.2⟩
          let z := g.symm ⟨x, hx⟩
          have hz_bd : mobBd z ∈ bd MobiusBand := by rw [bd_mobiusBand]; exact ⟨z, rfl⟩
          have hb_z : crosscapGlueMap hΛ_open g ⟨mobBd z, hz_bd⟩ = ⟨x, hx_mem⟩ := by
            apply Subtype.ext
            rw [crosscapGlueMap_mobBd]
            exact congrArg Subtype.val (g.apply_symm_apply ⟨x, hx⟩)
          have hinl_eq : GluedSpace.inl hb_inj ⟨x, hx_mem⟩ =
              GluedSpace.inr hb_inj (mobBd z) := by
            rw [← hb_z]
            exact (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hz_bd, rfl⟩
          refine ⟨⟨GluedSpace.inl hb_inj ⟨x, hx_mem⟩, ⟨⟨x, hx_mem⟩, rfl⟩⟩, ?_, hι_inl ⟨x, hx_mem⟩⟩
          change GluedSpace.inl hb_inj ⟨x, hx_mem⟩ ∈ GluedSpace.inr hb_inj '' bd MobiusBand
          rw [hinl_eq]
          exact ⟨mobBd z, hz_bd, rfl⟩
        · rintro ⟨⟨_, ⟨y, rfl⟩⟩, ⟨p, hp_bd, heq⟩, rfl⟩
          rw [hι_inl y]
          obtain ⟨hp_bd', rfl⟩ := (GluedSpace.inl_eq_inr hb_inj).mp heq.symm
          exact (g (mobBdHomeo.symm ⟨p, hp_bd'⟩)).2
      disjoint_D := fun i j hij => (hij (Subsingleton.elim i j)).elim
      compl := by
        rw [hι_range]
        ext x
        simp only [mem_compl_iff, mem_sdiff, mem_univ, true_and, mem_iUnion,
          Fin.exists_fin_one, Matrix.cons_val_zero, not_not] }

/-- Homeomorphism between `MobiusBand` (`Quotient Surface.mobiusSetoid`) and
`Quotient GM12.mobiusSetoid`. -/
noncomputable def mobiusSetoidHomeo : MobiusBand ≃ₜ Quotient GM12.mobiusSetoid where
  toFun := Quotient.lift (Quotient.mk GM12.mobiusSetoid) (fun _ _ h => Quotient.sound h)
  invFun := Quotient.lift (Quotient.mk Surface.mobiusSetoid) (fun _ _ h => Quotient.sound h)
  left_inv y := by obtain ⟨p, rfl⟩ := Quotient.exists_rep y; rfl
  right_inv y := by obtain ⟨p, rfl⟩ := Quotient.exists_rep y; rfl
  continuous_toFun := Continuous.quotient_lift continuous_quotient_mk' _
  continuous_invFun := Continuous.quotient_lift continuous_quotient_mk' _

/-- Given `δ : Circle → ℝ`, the pinched subset `Q_mid` of `unitInterval × unitInterval`. -/
def mobPinchPairSet (δ : Circle → ℝ) : Set (unitInterval × unitInterval) :=
  {p | δ (circleTop p.1) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 - δ (circleBot p.1)}

theorem mobPinchPairSet_saturated (δ : Circle → ℝ) {p q : unitInterval × unitInterval}
    (h : Surface.mobiusSetoid p q) (hp : p ∈ mobPinchPairSet δ) :
    q ∈ mobPinchPairSet δ := by
  rcases mobius_rel h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact hp
  · obtain ⟨hp1, hp2⟩ := hp
    refine ⟨?_, ?_⟩
    · rw [h2, circleTop_one, h3, unitInterval.coe_symm_eq]
      rw [h1, circleBot_zero] at hp2
      linarith
    · rw [h2, circleBot_one, h3, unitInterval.coe_symm_eq]
      rw [h1, circleTop_zero] at hp1
      linarith
  · obtain ⟨hp1, hp2⟩ := hp
    refine ⟨?_, ?_⟩
    · rw [h1, circleTop_zero]
      have h3' : (q.2 : ℝ) = 1 - (p.2 : ℝ) := by
        have := congrArg Subtype.val h3
        simp only [unitInterval.coe_symm_eq] at this
        linarith
      rw [h2, circleBot_one] at hp2
      linarith
    · rw [h1, circleBot_zero]
      have h3' : (q.2 : ℝ) = 1 - (p.2 : ℝ) := by
        have := congrArg Subtype.val h3
        simp only [unitInterval.coe_symm_eq] at this
        linarith
      rw [h2, circleTop_one] at hp1
      linarith

theorem mk_mem_image_mobPinchPairSet_iff (δ : Circle → ℝ) (p : unitInterval × unitInterval) :
    Quotient.mk Surface.mobiusSetoid p ∈
      Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ ↔ p ∈ mobPinchPairSet δ := by
  constructor
  · rintro ⟨q, hq, heq⟩
    exact mobPinchPairSet_saturated δ (Quotient.exact heq) hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- Forward map of `pinchMobHomeo` on `unitInterval × unitInterval`. -/
noncomputable def pinchMobPair (δ : Circle → ℝ)
    (p : unitInterval × unitInterval) : unitInterval × unitInterval :=
  (p.1, projIcc 0 1 zero_le_one
    (δ (circleTop p.1) + (p.2 : ℝ) * (1 - δ (circleTop p.1) - δ (circleBot p.1))))

theorem pinchMobPair_snd_coe {δ : Circle → ℝ}
    (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) (p : unitInterval × unitInterval) :
    ((pinchMobPair δ p).2 : ℝ) =
      δ (circleTop p.1) + (p.2 : ℝ) * (1 - δ (circleTop p.1) - δ (circleBot p.1)) := by
  have h1 := hδ_bd (circleTop p.1)
  have h2 := hδ_bd (circleBot p.1)
  have hv := p.2.2
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one
    ⟨by nlinarith [h1.1, h1.2, h2.1, h2.2, hv.1, hv.2],
     by nlinarith [h1.1, h1.2, h2.1, h2.2, hv.1, hv.2]⟩)

theorem pinchMobPair_mem {δ : Circle → ℝ}
    (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) (p : unitInterval × unitInterval) :
    pinchMobPair δ p ∈ mobPinchPairSet δ := by
  have h1 := hδ_bd (circleTop p.1)
  have h2 := hδ_bd (circleBot p.1)
  have hv := p.2.2
  refine ⟨?_, ?_⟩
  · change δ (circleTop p.1) ≤ ((pinchMobPair δ p).2 : ℝ)
    rw [pinchMobPair_snd_coe hδ_bd]
    nlinarith [h1.1, h1.2, h2.1, h2.2, hv.1, hv.2]
  · change ((pinchMobPair δ p).2 : ℝ) ≤ 1 - δ (circleBot p.1)
    rw [pinchMobPair_snd_coe hδ_bd]
    nlinarith [h1.1, h1.2, h2.1, h2.2, hv.1, hv.2]

/-- Homeomorphism between `MobiusBand` and its pinched sub-band
`Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ`. -/
noncomputable def pinchMobHomeo {δ : Circle → ℝ}
    (hδ_cont : Continuous δ) (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    MobiusBand ≃ₜ ↥(Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ) := by
  let f_aux : unitInterval × unitInterval → MobiusBand :=
    fun p => Quotient.mk Surface.mobiusSetoid (pinchMobPair δ p)
  have hf_aux_cont : Continuous f_aux := by
    unfold f_aux pinchMobPair
    have := continuous_circleTop
    have := continuous_circleBot
    exact continuous_quotient_mk'.comp (by fun_prop)
  have hf_rel : ∀ p q : unitInterval × unitInterval,
      Surface.mobiusSetoid p q → f_aux p = f_aux q := by
    have hstep : ∀ p q : unitInterval × unitInterval,
        p.1 = 0 → q.1 = 1 → q.2 = unitInterval.symm p.2 → f_aux p = f_aux q := by
      intro p q hp1 hq1 hq2
      apply Quotient.sound
      refine Relation.EqvGen.rel _ _ ⟨hp1, hq1, ?_⟩
      apply Subtype.ext
      change ((pinchMobPair δ q).2 : ℝ) = 1 - ((pinchMobPair δ p).2 : ℝ)
      rw [pinchMobPair_snd_coe hδ_bd, pinchMobPair_snd_coe hδ_bd,
        hp1, hq1, hq2, circleTop_zero, circleBot_zero, circleTop_one, circleBot_one,
        unitInterval.coe_symm_eq]
      ring
    intro p q h
    rcases mobius_rel h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rfl
    · exact hstep p q h1 h2 h3
    · exact (hstep q p h1 h2 h3).symm
  let f_mob : MobiusBand → MobiusBand := Quotient.lift f_aux hf_rel
  have hf_mob_cont : Continuous f_mob := Continuous.quotient_lift hf_aux_cont _
  have hf_mob_mem : ∀ y : MobiusBand,
      f_mob y ∈ Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ := by
    intro y
    obtain ⟨p, rfl⟩ := Quotient.exists_rep y
    exact ⟨pinchMobPair δ p, pinchMobPair_mem hδ_bd p, rfl⟩
  let f : MobiusBand → ↥(Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ) :=
    fun y => ⟨f_mob y, hf_mob_mem y⟩
  have hf_cont : Continuous f := Continuous.subtype_mk hf_mob_cont _
  have hf_bij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro y₁ y₂ heq
      obtain ⟨p, rfl⟩ := Quotient.exists_rep y₁
      obtain ⟨q, rfl⟩ := Quotient.exists_rep y₂
      have h_eq : f_aux p = f_aux q := congrArg Subtype.val heq
      apply Quotient.sound
      rcases mobius_rel (Quotient.exact h_eq) with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · have hpq := Prod.ext_iff.mp h
        have hu : p.1 = q.1 := hpq.1
        have hv_eq : ((pinchMobPair δ p).2 : ℝ) = ((pinchMobPair δ q).2 : ℝ) :=
          congrArg Subtype.val hpq.2
        rw [pinchMobPair_snd_coe hδ_bd, pinchMobPair_snd_coe hδ_bd, ← hu] at hv_eq
        have hpos : 0 < 1 - δ (circleTop p.1) - δ (circleBot p.1) := by
          linarith [(hδ_bd (circleTop p.1)).2, (hδ_bd (circleBot p.1)).2]
        have hv : p.2 = q.2 := Subtype.ext (by nlinarith)
        rw [Prod.ext hu hv]
      · change p.1 = 0 at h1
        change q.1 = 1 at h2
        refine Relation.EqvGen.rel _ _ ⟨h1, h2, ?_⟩
        apply Subtype.ext
        simp only [unitInterval.coe_symm_eq]
        have hv_eq : ((pinchMobPair δ q).2 : ℝ) = 1 - ((pinchMobPair δ p).2 : ℝ) := by
          have := congrArg Subtype.val h3
          simpa [unitInterval.coe_symm_eq] using this
        rw [pinchMobPair_snd_coe hδ_bd, pinchMobPair_snd_coe hδ_bd,
          h1, h2, circleTop_zero, circleBot_zero, circleTop_one, circleBot_one] at hv_eq
        have hpos : 0 < 1 - δ 1 - δ (-1) := by
          linarith [(hδ_bd 1).2, (hδ_bd (-1)).2]
        nlinarith
      · change q.1 = 0 at h1
        change p.1 = 1 at h2
        refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨h1, h2, ?_⟩)
        apply Subtype.ext
        simp only [unitInterval.coe_symm_eq]
        have hv_eq : ((pinchMobPair δ p).2 : ℝ) = 1 - ((pinchMobPair δ q).2 : ℝ) := by
          have := congrArg Subtype.val h3
          simpa [unitInterval.coe_symm_eq] using this
        rw [pinchMobPair_snd_coe hδ_bd, pinchMobPair_snd_coe hδ_bd,
          h1, h2, circleTop_zero, circleBot_zero, circleTop_one, circleBot_one] at hv_eq
        have hpos : 0 < 1 - δ 1 - δ (-1) := by
          linarith [(hδ_bd 1).2, (hδ_bd (-1)).2]
        nlinarith
    · rintro ⟨_, ⟨⟨u, w⟩, ⟨hw1, hw2⟩, rfl⟩⟩
      dsimp at hw1 hw2
      have hpos : 0 < 1 - δ (circleTop u) - δ (circleBot u) := by
        linarith [(hδ_bd (circleTop u)).2, (hδ_bd (circleBot u)).2]
      let v_val : ℝ := ((w : ℝ) - δ (circleTop u)) / (1 - δ (circleTop u) - δ (circleBot u))
      have hv_mem : v_val ∈ Icc (0 : ℝ) 1 := by
        dsimp [v_val]
        exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩
      let v : unitInterval := ⟨v_val, hv_mem⟩
      refine ⟨Quotient.mk Surface.mobiusSetoid (u, v), Subtype.ext ?_⟩
      change Quotient.mk Surface.mobiusSetoid (pinchMobPair δ (u, v)) =
        Quotient.mk Surface.mobiusSetoid (u, w)
      congr 1
      refine Prod.ext rfl (Subtype.ext ?_)
      rw [pinchMobPair_snd_coe hδ_bd]
      change δ (circleTop u) + v_val * (1 - δ (circleTop u) - δ (circleBot u)) = (w : ℝ)
      dsimp [v_val]
      rw [div_mul_cancel₀ _ hpos.ne']
      ring
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij) hf_cont

/-- Collar coordinate map on `unitInterval × unitInterval`:
maps `(u, v)` with `v < 1 / 2` to `(v, circleTop u)` and `(u, v)` with `1 / 2 < v` to
`(1 - v, circleBot u)`. -/
noncomputable def collarCoordsAux (p : unitInterval × unitInterval) : ℝ × Circle :=
  if (p.2 : ℝ) < 1 / 2 then
    ((p.2 : ℝ), circleTop p.1)
  else if 1 / 2 < (p.2 : ℝ) then
    (1 - (p.2 : ℝ), circleBot p.1)
  else
    (1 / 2, 1)

theorem collarCoordsAux_rel {p q : unitInterval × unitInterval}
    (h : Surface.mobiusSetoid p q) : collarCoordsAux p = collarCoordsAux q := by
  have hstep : ∀ p q : unitInterval × unitInterval,
      p.1 = 0 → q.1 = 1 → q.2 = unitInterval.symm p.2 → collarCoordsAux p = collarCoordsAux q := by
    intro p q hp1 hq1 hq2
    dsimp [collarCoordsAux]
    have hq2_coe : (q.2 : ℝ) = 1 - (p.2 : ℝ) := by
      rw [hq2, unitInterval.coe_symm_eq]
    rw [hp1, hq1, hq2_coe, circleTop_zero, circleBot_zero, circleTop_one, circleBot_one]
    rcases lt_trichotomy (p.2 : ℝ) (1 / 2) with hlt | heq | hgt
    · have hnot1 : ¬ (1 - (p.2 : ℝ) < 1 / 2) := by linarith
      have hgt1 : 1 / 2 < 1 - (p.2 : ℝ) := by linarith
      simp only [hlt, hnot1, hgt1, ↓reduceIte, sub_sub_cancel]
    · have hnot1 : ¬ ((p.2 : ℝ) < 1 / 2) := by linarith
      have hnot2 : ¬ (1 / 2 < (p.2 : ℝ)) := by linarith
      have hnot3 : ¬ (1 - (p.2 : ℝ) < 1 / 2) := by linarith
      have hnot4 : ¬ (1 / 2 < 1 - (p.2 : ℝ)) := by linarith
      simp only [hnot1, hnot2, hnot3, hnot4, ↓reduceIte]
    · have hnot1 : ¬ ((p.2 : ℝ) < 1 / 2) := by linarith
      have hlt1 : 1 - (p.2 : ℝ) < 1 / 2 := by linarith
      simp only [hnot1, hgt, hlt1, ↓reduceIte]
  rcases mobius_rel h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rfl
  · exact hstep p q h1 h2 h3
  · exact (hstep q p h1 h2 h3).symm

/-- Collar coordinate map on `MobiusBand`. -/
noncomputable def collarCoords : MobiusBand → ℝ × Circle :=
  Quotient.lift collarCoordsAux (fun _ _ h => collarCoordsAux_rel h)

@[simp]
theorem collarCoords_mobBd (z : Circle) : collarCoords (mobBd z) = (0, z) := by
  by_cases hz : 0 ≤ (z : ℂ).im
  · rw [mobBd_of_im_nonneg hz]
    change collarCoordsAux (mobBdTopU z, 0) = (0, z)
    dsimp [collarCoordsAux]
    have hlt : (0 : ℝ) < 1 / 2 := by norm_num
    simp only [hlt, ↓reduceIte, circleTop_mobBdTopU hz]
  · have hz' : (z : ℂ).im ≤ 0 := (lt_of_not_ge hz).le
    rw [mobBd_of_im_nonpos hz']
    change collarCoordsAux (mobBdBotU z, 1) = (0, z)
    dsimp [collarCoordsAux]
    have hnot : ¬ ((1 : ℝ) < 1 / 2) := by norm_num
    have hgt : (1 / 2 : ℝ) < 1 := by norm_num
    simp only [hnot, hgt, ↓reduceIte, sub_self, circleBot_mobBdBotU hz']

/-- The collar subset of `unitInterval × unitInterval` for `δ : Circle → ℝ`. -/
def mobCollarPairSet (δ : Circle → ℝ) : Set (unitInterval × unitInterval) :=
  {p | (p.2 : ℝ) ≤ δ (circleTop p.1) ∨ 1 - δ (circleBot p.1) ≤ (p.2 : ℝ)}

/-- The cuff subset of `unitInterval × unitInterval` for `δ : Circle → ℝ`. -/
def mobCuffPairSet (δ : Circle → ℝ) : Set (unitInterval × unitInterval) :=
  {p | (p.2 : ℝ) = δ (circleTop p.1) ∨ (p.2 : ℝ) = 1 - δ (circleBot p.1)}

theorem mobCollarPairSet_saturated (δ : Circle → ℝ) {p q : unitInterval × unitInterval}
    (h : Surface.mobiusSetoid p q) (hp : p ∈ mobCollarPairSet δ) :
    q ∈ mobCollarPairSet δ := by
  rcases mobius_rel h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact hp
  · rcases hp with hp1 | hp2
    · right
      rw [h2, circleBot_one, h3, unitInterval.coe_symm_eq]
      rw [h1, circleTop_zero] at hp1
      linarith
    · left
      rw [h2, circleTop_one, h3, unitInterval.coe_symm_eq]
      rw [h1, circleBot_zero] at hp2
      linarith
  · have h3' : (q.2 : ℝ) = 1 - (p.2 : ℝ) := by
      have := congrArg Subtype.val h3
      simp only [unitInterval.coe_symm_eq] at this
      linarith
    rcases hp with hp1 | hp2
    · right
      rw [h1, circleBot_zero, h3']
      rw [h2, circleTop_one] at hp1
      linarith
    · left
      rw [h1, circleTop_zero, h3']
      rw [h2, circleBot_one] at hp2
      linarith

theorem mk_mem_image_mobCollarPairSet_iff (δ : Circle → ℝ) (p : unitInterval × unitInterval) :
    Quotient.mk Surface.mobiusSetoid p ∈
      Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ ↔ p ∈ mobCollarPairSet δ := by
  constructor
  · rintro ⟨q, hq, heq⟩
    exact mobCollarPairSet_saturated δ (Quotient.exact heq) hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem continuousOn_collarCoords {δ : Circle → ℝ}
    (hδ_cont : Continuous δ) (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    ContinuousOn collarCoords (Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ) := by
  let Q₁ : Set (unitInterval × unitInterval) := {p | (p.2 : ℝ) ≤ δ (circleTop p.1)}
  let Q₂ : Set (unitInterval × unitInterval) := {p | 1 - δ (circleBot p.1) ≤ (p.2 : ℝ)}
  have hQ₁_cl : IsClosed Q₁ := by
    have := continuous_circleTop
    refine isClosed_le (continuous_subtype_val.comp continuous_snd) (by fun_prop)
  have hQ₂_cl : IsClosed Q₂ := by
    have := continuous_circleBot
    refine isClosed_le (by fun_prop) (continuous_subtype_val.comp continuous_snd)
  have hQ_eq : mobCollarPairSet δ = Q₁ ∪ Q₂ := rfl
  have hQ_cl : IsClosed (mobCollarPairSet δ) := hQ₁_cl.union hQ₂_cl
  have : CompactSpace ↥(mobCollarPairSet δ) := isCompact_iff_compactSpace.mp hQ_cl.isCompact
  have hcont_Q₁ : ContinuousOn collarCoordsAux Q₁ := by
    have := continuous_circleTop
    refine (Continuous.prodMk (continuous_subtype_val.comp continuous_snd)
      (continuous_circleTop.comp continuous_fst)).continuousOn.congr ?_
    intro p hp
    have hlt : (p.2 : ℝ) < 1 / 2 := by
      linarith [show (p.2 : ℝ) ≤ δ (circleTop p.1) from hp, (hδ_bd (circleTop p.1)).2]
    dsimp [collarCoordsAux]
    simp only [hlt, ↓reduceIte]
  have hcont_Q₂ : ContinuousOn collarCoordsAux Q₂ := by
    have h_fn : Continuous (fun p : unitInterval × unitInterval =>
        (1 - (p.2 : ℝ), circleBot p.1)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).prodMk
        (continuous_circleBot.comp continuous_fst)
    refine h_fn.continuousOn.congr ?_
    intro p hp
    have hgt : 1 / 2 < (p.2 : ℝ) := by
      linarith [show 1 - δ (circleBot p.1) ≤ (p.2 : ℝ) from hp, (hδ_bd (circleBot p.1)).2]
    have hnot : ¬ ((p.2 : ℝ) < 1 / 2) := by linarith
    dsimp [collarCoordsAux]
    simp only [hnot, hgt, ↓reduceIte]
  have hcont_Q : ContinuousOn collarCoordsAux (mobCollarPairSet δ) :=
    hcont_Q₁.union_of_isClosed hcont_Q₂ hQ₁_cl hQ₂_cl
  let A_col := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
  let q_col : ↥(mobCollarPairSet δ) → ↥A_col :=
    fun p => ⟨Quotient.mk Surface.mobiusSetoid p.1, ⟨p.1, p.2, rfl⟩⟩
  have hq_cont : Continuous q_col :=
    Continuous.subtype_mk (continuous_quotient_mk'.comp continuous_subtype_val) _
  have hq_surj : Function.Surjective q_col := by
    rintro ⟨_, ⟨p, hp, rfl⟩⟩
    exact ⟨⟨p, hp⟩, rfl⟩
  have hq_quot : IsQuotientMap q_col :=
    hq_cont.isClosedMap.isQuotientMap hq_cont hq_surj
  rw [continuousOn_iff_continuous_domRestrict, hq_quot.continuous_iff]
  exact continuousOn_iff_continuous_domRestrict.mp hcont_Q

/-- Inverse map of `collarCoords` on `{q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ 1 / 4}`. -/
noncomputable def collarCoordsInv (q : ℝ × Circle) : MobiusBand :=
  if 0 ≤ (q.2 : ℂ).im then
    Quotient.mk Surface.mobiusSetoid (mobBdTopU q.2, projIcc 0 1 zero_le_one q.1)
  else
    Quotient.mk Surface.mobiusSetoid (mobBdBotU q.2, projIcc 0 1 zero_le_one (1 - q.1))

theorem circleBot_im_eq_zero_iff (u : unitInterval) :
    (circleBot u : ℂ).im = 0 ↔ u = 0 ∨ u = 1 := by
  constructor
  · intro h
    change - Real.sqrt (1 - (1 - 2 * (u : ℝ)) ^ 2) = 0 at h
    have hnonneg : 0 ≤ 1 - (1 - 2 * (u : ℝ)) ^ 2 := by
      have : 1 - (1 - 2 * (u : ℝ)) ^ 2 = 4 * (u : ℝ) * (1 - (u : ℝ)) := by ring
      rw [this]
      nlinarith [u.2.1, u.2.2]
    have h0 : 1 - (1 - 2 * (u : ℝ)) ^ 2 = 0 :=
      (Real.sqrt_eq_zero hnonneg).mp (by linarith)
    have hsq : (1 - 2 * (u : ℝ)) ^ 2 = 1 := by linarith
    rcases sq_eq_one_iff.mp hsq with h1 | h2
    · left; exact Subtype.ext (by change (u : ℝ) = 0; linarith)
    · right; exact Subtype.ext (by change (u : ℝ) = 1; linarith)
  · rintro (rfl | rfl) <;> simp

theorem collarCoordsInv_collarCoords {δ : Circle → ℝ}
    (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    {y : MobiusBand} (hy : y ∈ Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ) :
    collarCoordsInv (collarCoords y) = y := by
  obtain ⟨⟨u, v⟩, hp, rfl⟩ := hy
  rcases hp with hp1 | hp2
  · have hlt : (v : ℝ) < 1 / 2 := by
      linarith [show (v : ℝ) ≤ δ (circleTop u) from hp1, (hδ_bd (circleTop u)).2]
    have hc : collarCoords (Quotient.mk Surface.mobiusSetoid (u, v)) = ((v : ℝ), circleTop u) := by
      change collarCoordsAux (u, v) = ((v : ℝ), circleTop u)
      dsimp [collarCoordsAux]
      simp only [hlt, ↓reduceIte]
    rw [hc]
    dsimp [collarCoordsInv]
    simp only [circleTop_im_nonneg u, ↓reduceIte, mobBdTopU_circleTop,
      projIcc_of_mem zero_le_one v.2]
  · have hgt : 1 / 2 < (v : ℝ) := by
      linarith [show 1 - δ (circleBot u) ≤ (v : ℝ) from hp2, (hδ_bd (circleBot u)).2]
    have hnot : ¬ ((v : ℝ) < 1 / 2) := by linarith
    have hc : collarCoords (Quotient.mk Surface.mobiusSetoid (u, v)) =
        (1 - (v : ℝ), circleBot u) := by
      change collarCoordsAux (u, v) = (1 - (v : ℝ), circleBot u)
      dsimp [collarCoordsAux]
      simp only [hnot, hgt, ↓reduceIte]
    rw [hc]
    dsimp [collarCoordsInv]
    split_ifs with him
    · have him0 : (circleBot u : ℂ).im = 0 := le_antisymm (circleBot_im_nonpos u) him
      rcases (circleBot_im_eq_zero_iff u).mp him0 with rfl | rfl
      · simp only [circleBot_zero]
        have ht : mobBdTopU (-1 : Circle) = 1 := by
          apply Subtype.ext; rw [mobBdTopU_coe]; norm_num
        have hv' : projIcc 0 1 zero_le_one (1 - (v : ℝ)) = unitInterval.symm v :=
          projIcc_of_mem zero_le_one (unitInterval.symm v).2
        rw [ht, hv']
        apply Quotient.sound
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl, rfl⟩)
      · simp only [circleBot_one]
        have ht : mobBdTopU (1 : Circle) = 0 := by
          apply Subtype.ext; rw [mobBdTopU_coe]; norm_num
        have hv' : projIcc 0 1 zero_le_one (1 - (v : ℝ)) = unitInterval.symm v :=
          projIcc_of_mem zero_le_one (unitInterval.symm v).2
        rw [ht, hv']
        apply Quotient.sound
        exact Relation.EqvGen.rel _ _ ⟨rfl, rfl, by simp⟩
    · simp only [mobBdBotU_circleBot, sub_sub_cancel, projIcc_of_mem zero_le_one v.2]

theorem injOn_collarCoords {δ : Circle → ℝ} (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    InjOn collarCoords (Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ) := by
  intro x hx y hy h
  rw [← collarCoordsInv_collarCoords hδ_bd hx, ← collarCoordsInv_collarCoords hδ_bd hy, h]

theorem collarCoords_collarCoordsInv {δ : Circle → ℝ}
    (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    {q : ℝ × Circle} (hq : 0 ≤ q.1 ∧ q.1 ≤ δ q.2) :
    collarCoordsInv q ∈ Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ ∧
      collarCoords (collarCoordsInv q) = q := by
  have hδ := hδ_bd q.2
  have hq_mem : q.1 ∈ Icc (0 : ℝ) 1 := ⟨hq.1, by linarith [hq.2, hδ.2]⟩
  have h1q_mem : 1 - q.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hq.2, hδ.2], by linarith [hq.1]⟩
  by_cases him : 0 ≤ (q.2 : ℂ).im
  · have hinv : collarCoordsInv q =
        Quotient.mk Surface.mobiusSetoid (mobBdTopU q.2, ⟨q.1, hq_mem⟩) := by
      dsimp [collarCoordsInv]
      simp only [him, ↓reduceIte, projIcc_of_mem zero_le_one hq_mem]
    rw [hinv]
    refine ⟨⟨(mobBdTopU q.2, ⟨q.1, hq_mem⟩), .inl ?_, rfl⟩, ?_⟩
    · change q.1 ≤ δ (circleTop (mobBdTopU q.2))
      rw [circleTop_mobBdTopU him]
      exact hq.2
    · change collarCoordsAux (mobBdTopU q.2, ⟨q.1, hq_mem⟩) = q
      dsimp [collarCoordsAux]
      have hlt : q.1 < 1 / 2 := by linarith [hq.2, hδ.2]
      simp only [hlt, ↓reduceIte, circleTop_mobBdTopU him]
  · have him' : (q.2 : ℂ).im ≤ 0 := (lt_of_not_ge him).le
    have hinv : collarCoordsInv q =
        Quotient.mk Surface.mobiusSetoid (mobBdBotU q.2, ⟨1 - q.1, h1q_mem⟩) := by
      dsimp [collarCoordsInv]
      simp only [him, ↓reduceIte, projIcc_of_mem zero_le_one h1q_mem]
    rw [hinv]
    refine ⟨⟨(mobBdBotU q.2, ⟨1 - q.1, h1q_mem⟩), .inr ?_, rfl⟩, ?_⟩
    · change 1 - δ (circleBot (mobBdBotU q.2)) ≤ 1 - q.1
      rw [circleBot_mobBdBotU him']
      linarith [hq.2]
    · change collarCoordsAux (mobBdBotU q.2, ⟨1 - q.1, h1q_mem⟩) = q
      dsimp [collarCoordsAux]
      have hnot : ¬ (1 - q.1 < 1 / 2) := by linarith [hq.2, hδ.2]
      have hgt : 1 / 2 < 1 - q.1 := by linarith [hq.2, hδ.2]
      simp only [hnot, hgt, ↓reduceIte, sub_sub_cancel, circleBot_mobBdBotU him']

theorem image_collarCoords_collar {δ : Circle → ℝ}
    (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    collarCoords '' (Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ) =
      {q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ δ q.2} := by
  ext q
  constructor
  · rintro ⟨_, ⟨⟨u, v⟩, hp, rfl⟩, rfl⟩
    rcases hp with hp1 | hp2
    · have hlt : (v : ℝ) < 1 / 2 := by
        linarith [show (v : ℝ) ≤ δ (circleTop u) from hp1, (hδ_bd (circleTop u)).2]
      change collarCoordsAux (u, v) ∈ {q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ δ q.2}
      dsimp [collarCoordsAux]
      simp only [hlt, ↓reduceIte]
      exact ⟨v.2.1, hp1⟩
    · have hgt : 1 / 2 < (v : ℝ) := by
        linarith [show 1 - δ (circleBot u) ≤ (v : ℝ) from hp2, (hδ_bd (circleBot u)).2]
      have hnot : ¬ ((v : ℝ) < 1 / 2) := by linarith
      change collarCoordsAux (u, v) ∈ {q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ δ q.2}
      dsimp [collarCoordsAux]
      simp only [hnot, hgt, ↓reduceIte]
      exact ⟨by linarith [v.2.2], by linarith [show 1 - δ (circleBot u) ≤ (v : ℝ) from hp2]⟩
  · intro hq
    obtain ⟨hmem, heq⟩ := collarCoords_collarCoordsInv hδ_bd hq
    exact ⟨collarCoordsInv q, hmem, heq⟩

theorem image_collarCoords_cuff {δ : Circle → ℝ}
    (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    collarCoords '' (Quotient.mk Surface.mobiusSetoid '' mobCuffPairSet δ) =
      {q : ℝ × Circle | q.1 = δ q.2} := by
  ext q
  constructor
  · rintro ⟨_, ⟨⟨u, v⟩, hp, rfl⟩, rfl⟩
    rcases hp with hp1 | hp2
    · have hlt : (v : ℝ) < 1 / 2 := by
        linarith [show (v : ℝ) = δ (circleTop u) from hp1, (hδ_bd (circleTop u)).2]
      change (collarCoordsAux (u, v)).1 = δ (collarCoordsAux (u, v)).2
      dsimp [collarCoordsAux]
      simp only [hlt, ↓reduceIte]
      exact hp1
    · have hgt : 1 / 2 < (v : ℝ) := by
        linarith [show (v : ℝ) = 1 - δ (circleBot u) from hp2, (hδ_bd (circleBot u)).2]
      have hnot : ¬ ((v : ℝ) < 1 / 2) := by linarith
      change (collarCoordsAux (u, v)).1 = δ (collarCoordsAux (u, v)).2
      dsimp [collarCoordsAux]
      simp only [hnot, hgt, ↓reduceIte]
      linarith [show (v : ℝ) = 1 - δ (circleBot u) from hp2]
  · intro hq
    have hq_eq : q.1 = δ q.2 := hq
    have hδ := hδ_bd q.2
    have hq_mem : q.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
    have h1q_mem : 1 - q.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
    by_cases him : 0 ≤ (q.2 : ℂ).im
    · refine ⟨Quotient.mk Surface.mobiusSetoid (mobBdTopU q.2, ⟨q.1, hq_mem⟩),
        ⟨(mobBdTopU q.2, ⟨q.1, hq_mem⟩), .inl ?_, rfl⟩, ?_⟩
      · change q.1 = δ (circleTop (mobBdTopU q.2))
        rwa [circleTop_mobBdTopU him]
      · change collarCoordsAux (mobBdTopU q.2, ⟨q.1, hq_mem⟩) = q
        dsimp [collarCoordsAux]
        have hlt : q.1 < 1 / 2 := by linarith [hδ.2]
        simp only [hlt, ↓reduceIte, circleTop_mobBdTopU him]
    · have him' : (q.2 : ℂ).im ≤ 0 := (lt_of_not_ge him).le
      refine ⟨Quotient.mk Surface.mobiusSetoid (mobBdBotU q.2, ⟨1 - q.1, h1q_mem⟩),
        ⟨(mobBdBotU q.2, ⟨1 - q.1, h1q_mem⟩), .inr ?_, rfl⟩, ?_⟩
      · change 1 - q.1 = 1 - δ (circleBot (mobBdBotU q.2))
        rw [circleBot_mobBdBotU him', hq_eq]
      · change collarCoordsAux (mobBdBotU q.2, ⟨1 - q.1, h1q_mem⟩) = q
        dsimp [collarCoordsAux]
        have hnot : ¬ (1 - q.1 < 1 / 2) := by linarith [hδ.2]
        have hgt : 1 / 2 < 1 - q.1 := by linarith [hδ.2]
        simp only [hnot, hgt, ↓reduceIte, sub_sub_cancel, circleBot_mobBdBotU him']

/-- Pinched boundary circle embedding `Circle → MobiusBand`. -/
noncomputable def pinchMobBd {δ : Circle → ℝ}
    (hδ_cont : Continuous δ) (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) (z : Circle) : MobiusBand :=
  (pinchMobHomeo hδ_cont hδ_bd (mobBd z)).1

theorem isEmbedding_pinchMobBd {δ : Circle → ℝ}
    (hδ_cont : Continuous δ) (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    IsEmbedding (pinchMobBd hδ_cont hδ_bd) :=
  IsEmbedding.subtypeVal.comp ((pinchMobHomeo hδ_cont hδ_bd).isEmbedding.comp isEmbedding_mobBd)

theorem pinchMobBd_eq_mobBd_of_eq_zero {δ : Circle → ℝ}
    (hδ_cont : Continuous δ) (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    {z : Circle} (hz0 : δ z = 0) :
    pinchMobBd hδ_cont hδ_bd z = mobBd z := by
  by_cases him : 0 ≤ (z : ℂ).im
  · dsimp [pinchMobBd]
    rw [mobBd_of_im_nonneg him]
    change Quotient.mk Surface.mobiusSetoid (pinchMobPair δ (mobBdTopU z, 0)) =
      Quotient.mk Surface.mobiusSetoid (mobBdTopU z, 0)
    congr 1
    refine Prod.ext rfl (Subtype.ext ?_)
    rw [pinchMobPair_snd_coe hδ_bd, circleTop_mobBdTopU him, hz0]
    simp
  · have him' : (z : ℂ).im ≤ 0 := (lt_of_not_ge him).le
    dsimp [pinchMobBd]
    rw [mobBd_of_im_nonpos him']
    change Quotient.mk Surface.mobiusSetoid (pinchMobPair δ (mobBdBotU z, 1)) =
      Quotient.mk Surface.mobiusSetoid (mobBdBotU z, 1)
    congr 1
    refine Prod.ext rfl (Subtype.ext ?_)
    rw [pinchMobPair_snd_coe hδ_bd, circleBot_mobBdBotU him', hz0]
    simp

theorem range_pinchMobBd {δ : Circle → ℝ}
    (hδ_cont : Continuous δ) (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    range (pinchMobBd hδ_cont hδ_bd) =
      Quotient.mk Surface.mobiusSetoid '' mobCuffPairSet δ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    by_cases him : 0 ≤ (z : ℂ).im
    · dsimp [pinchMobBd]
      rw [mobBd_of_im_nonneg him]
      refine ⟨pinchMobPair δ (mobBdTopU z, 0), .inl ?_, rfl⟩
      change ((pinchMobPair δ (mobBdTopU z, 0)).2 : ℝ) = δ (circleTop (mobBdTopU z))
      rw [pinchMobPair_snd_coe hδ_bd]
      simp
    · have him' : (z : ℂ).im ≤ 0 := (lt_of_not_ge him).le
      dsimp [pinchMobBd]
      rw [mobBd_of_im_nonpos him']
      refine ⟨pinchMobPair δ (mobBdBotU z, 1), .inr ?_, rfl⟩
      change ((pinchMobPair δ (mobBdBotU z, 1)).2 : ℝ) = 1 - δ (circleBot (mobBdBotU z))
      rw [pinchMobPair_snd_coe hδ_bd]
      simp [Icc.coe_one]
      ring
  · rintro ⟨⟨u, v⟩, hp, rfl⟩
    rcases hp with hp1 | hp2
    · refine ⟨circleTop u, ?_⟩
      dsimp [pinchMobBd]
      rw [mobBd_circleTop]
      change Quotient.mk Surface.mobiusSetoid (pinchMobPair δ (u, 0)) =
        Quotient.mk Surface.mobiusSetoid (u, v)
      congr 1
      refine Prod.ext rfl (Subtype.ext ?_)
      rw [pinchMobPair_snd_coe hδ_bd]
      simp only [Icc.coe_zero, zero_mul, add_zero]
      exact (show (v : ℝ) = δ (circleTop u) from hp1).symm
    · refine ⟨circleBot u, ?_⟩
      dsimp [pinchMobBd]
      rw [mobBd_circleBot]
      change Quotient.mk Surface.mobiusSetoid (pinchMobPair δ (u, 1)) =
        Quotient.mk Surface.mobiusSetoid (u, v)
      congr 1
      refine Prod.ext rfl (Subtype.ext ?_)
      rw [pinchMobPair_snd_coe hδ_bd]
      simp only [Icc.coe_one, one_mul]
      linarith [show (v : ℝ) = 1 - δ (circleBot u) from hp2]

theorem collarCoordsInv_zero (z : Circle) :
    collarCoordsInv (0, z) = mobBd z := by
  dsimp [collarCoordsInv]
  split_ifs with him
  · rw [mobBd_of_im_nonneg him]
    have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
      projIcc_of_mem zero_le_one unitInterval.zero_mem
    rw [h0]
  · have him' : (z : ℂ).im ≤ 0 := (lt_of_not_ge him).le
    rw [mobBd_of_im_nonpos him', sub_zero]
    have h1 : projIcc 0 1 zero_le_one (1 : ℝ) = 1 :=
      projIcc_of_mem zero_le_one unitInterval.one_mem
    rw [h1]

theorem mem_bd_iff_collarCoords_fst_eq_zero {δ : Circle → ℝ}
    (hδ_bd : ∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    {y : MobiusBand} (hy : y ∈ Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ) :
    y ∈ bd MobiusBand ↔ (collarCoords y).1 = 0 := by
  constructor
  · intro hbd
    rw [bd_mobiusBand] at hbd
    obtain ⟨z, rfl⟩ := hbd
    rw [collarCoords_mobBd]
  · intro h0
    have hpair : collarCoords y = (0, (collarCoords y).2) := Prod.ext h0 rfl
    have hy_eq : y = mobBd (collarCoords y).2 := by
      rw [← collarCoordsInv_zero, ← hpair, collarCoordsInv_collarCoords hδ_bd hy]
    rw [hy_eq, bd_mobiusBand]
    exact ⟨(collarCoords y).2, rfl⟩

/-- Map from `GluedSpace hb_inj` to `S` that equals the inclusion on `S₁` and maps `MobiusBand`
via `cMap ∘ collarCoords`. -/
noncomputable def crosscapPinchRetract {S : Type w} [TopologicalSpace S] {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ))
    (hb_inj : Function.Injective (crosscapGlueMap hΛ_open g))
    (cMap : ℝ × Circle → S)
    (hcMap_zero : ∀ z : Circle, cMap (0, z) = (g z).1) :
    GluedSpace hb_inj → S :=
  Quotient.lift
    (fun a => match a with
      | .inl x => x.1
      | .inr y => cMap (collarCoords y.down))
    (by
      have hagree : ∀ z : ↥(bd MobiusBand),
          (crosscapGlueMap hΛ_open g z).1 = cMap (collarCoords z.1) := by
        intro z
        let w := mobBdHomeo.symm z
        have hz : z.1 = mobBd w := congrArg Subtype.val (mobBdHomeo.apply_symm_apply z).symm
        have h1 : (crosscapGlueMap hΛ_open g z).1 = (g w).1 := rfl
        rw [h1, hz, collarCoords_mobBd, hcMap_zero]
      rintro a a' (rfl | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩)
      · rfl
      · exact hagree z
      · exact (hagree z).symm)

@[simp]
theorem crosscapPinchRetract_inl {S : Type w} [TopologicalSpace S] {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ))
    (hb_inj : Function.Injective (crosscapGlueMap hΛ_open g))
    (cMap : ℝ × Circle → S)
    (hcMap_zero : ∀ z : Circle, cMap (0, z) = (g z).1)
    (x : ↥(univ \ Λ : Set S)) :
    crosscapPinchRetract hΛ_open g hb_inj cMap hcMap_zero (GluedSpace.inl hb_inj x) = x.1 := rfl

@[simp]
theorem crosscapPinchRetract_inr {S : Type w} [TopologicalSpace S] {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ))
    (hb_inj : Function.Injective (crosscapGlueMap hΛ_open g))
    (cMap : ℝ × Circle → S)
    (hcMap_zero : ∀ z : Circle, cMap (0, z) = (g z).1)
    (y : MobiusBand) :
    crosscapPinchRetract hΛ_open g hb_inj cMap hcMap_zero (GluedSpace.inr hb_inj y) =
      cMap (collarCoords y) := rfl

private theorem crosscap_retract_continuous_on_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    (δ : Circle → ℝ)
    (cMap : ℝ × Circle → S)
    (hδ_cont : Continuous δ)
    (hδ_bd : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (hcMap_cont : Continuous cMap) :
    let S' : Type w := GluedSpace hb_inj
    let S₂ : Set S' := range (GluedSpace.inr hb_inj)
    ∀ (e₂ : MobiusBand ≃ₜ ↑S₂),
    (∀ y, (e₂ y).1 = GluedSpace.inr hb_inj y) →
    let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
    let C_col : Set S' := GluedSpace.inr hb_inj '' A_col
    ∀ (f_XII : S' → S),
    (∀ (y : MobiusBand), f_XII (GluedSpace.inr hb_inj y) = cMap (collarCoords y)) →
    ContinuousOn f_XII C_col := by
  intro S' S₂ e₂ he₂ A_col C_col f_XII hf_inr
  have hsub : C_col ⊆ S₂ := image_subset_range _ _
  rw [continuousOn_iff_continuous_domRestrict]
  have hcongr : C_col.domRestrict f_XII =
      fun x : ↥C_col => cMap (collarCoords (e₂.symm ⟨x.1, hsub x.2⟩)) := by
    ext ⟨_, ⟨y, hy, rfl⟩⟩
    have hmem2 : GluedSpace.inr hb_inj y ∈ S₂ := ⟨y, rfl⟩
    have he₂_y : e₂.symm ⟨GluedSpace.inr hb_inj y, hmem2⟩ = y :=
        (congrArg e₂.symm (Subtype.ext (he₂ y).symm)).trans (e₂.symm_apply_apply y)
    change f_XII (GluedSpace.inr hb_inj y) =
      cMap (collarCoords (e₂.symm ⟨GluedSpace.inr hb_inj y, hmem2⟩))
    rw [he₂_y, hf_inr]
  rw [hcongr]
  refine hcMap_cont.comp ?_
  have hcc := continuousOn_iff_continuous_domRestrict.mp (continuousOn_collarCoords hδ_cont hδ_bd)
  let g_col : ↥C_col → ↥A_col := fun x =>
    ⟨e₂.symm ⟨x.1, hsub x.2⟩, by
      obtain ⟨y, hy, heq⟩ := x.2
      have hmem2 : GluedSpace.inr hb_inj y ∈ S₂ := ⟨y, rfl⟩
      have hx_eq : (⟨x.1, hsub x.2⟩ : ↥S₂) = ⟨GluedSpace.inr hb_inj y, hmem2⟩ :=
        Subtype.ext heq.symm
      have he₂_y : e₂.symm ⟨GluedSpace.inr hb_inj y, hmem2⟩ = y :=
        (congrArg e₂.symm (Subtype.ext (he₂ y).symm)).trans (e₂.symm_apply_apply y)
      rw [hx_eq, he₂_y]
      exact hy⟩
  have hg_col_cont : Continuous g_col :=
    Continuous.subtype_mk (e₂.symm.continuous.comp (Continuous.subtype_mk continuous_subtype_val
      _)) _
  exact hcc.comp hg_col_cont

private theorem crosscap_collar_interior_maps_inside_disc
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    (δ : Circle → ℝ)
    (D₀ : Set S)
    (cMap : ℝ × Circle → S)
    (hδ_bd : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (hcMap_inj : InjOn cMap {p | 0 ≤ p.1 ∧ p.1 ≤ δ p.2})
    (hcMap_zero : ∀ (z : Circle), cMap (0, z) = ↑(g z)) :
    let S' : Type w := GluedSpace hb_inj
    let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
    let C_col : Set S' := GluedSpace.inr hb_inj '' A_col
    ∀ (f_XII : S' → S),
    (∀ (y : MobiusBand), f_XII (GluedSpace.inr hb_inj y) = cMap (collarCoords y)) →
    (f_XII '' C_col = closure Λ \ D₀) →
    ∀ y ∈ A_col, y ∉ bd MobiusBand → f_XII (GluedSpace.inr hb_inj y) ∈ Λ := by
  intro S' A_col C_col f_XII hf_inr hf_img_col y hy hy_not_bd
  have hmem_col : f_XII (GluedSpace.inr hb_inj y) ∈ closure Λ \ D₀ := by
    rw [← hf_img_col]
    exact ⟨GluedSpace.inr hb_inj y, ⟨y, hy, rfl⟩, rfl⟩
  by_contra hnot_Λ
  have hbd : f_XII (GluedSpace.inr hb_inj y) ∈ subBd Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
    exact ⟨hmem_col.1, hnot_Λ⟩
  let z := g.symm ⟨f_XII (GluedSpace.inr hb_inj y), hbd⟩
  have hcz : cMap (0, z) = cMap (collarCoords y) := by
    rw [hcMap_zero z, ← hf_inr y]
    exact congrArg Subtype.val (g.apply_symm_apply ⟨f_XII (GluedSpace.inr hb_inj y), hbd⟩)
  have hcy_mem : collarCoords y ∈ {q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ δ q.2} := by
    rw [← image_collarCoords_collar hδ_bd]
    exact mem_image_of_mem collarCoords hy
  have hinj := hcMap_inj ⟨le_rfl, (hδ_bd z).1⟩ hcy_mem hcz
  have h0 : (collarCoords y).1 = 0 := (congrArg Prod.fst hinj).symm
  exact hy_not_bd ((mem_bd_iff_collarCoords_fst_eq_zero hδ_bd hy).mpr h0)

private theorem crosscap_retract_injective_on_pinched_complement
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    (δ : Circle → ℝ)
    (cMap : ℝ × Circle → S)
    (hδ_bd : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (hcMap_inj : InjOn cMap {p | 0 ≤ p.1 ∧ p.1 ≤ δ p.2}) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
    let C_col : Set S' := GluedSpace.inr hb_inj '' A_col
    let P₁_XII : Set S' := S₁ ∪ C_col
    ∀ (f_XII : S' → S),
    (∀ y, f_XII (GluedSpace.inl hb_inj y) = y.1) →
    (∀ (y : MobiusBand), f_XII (GluedSpace.inr hb_inj y) = cMap (collarCoords y)) →
    let ι_XII : ↑P₁_XII → S := fun x => f_XII ↑x
    (∀ x ∈ P₁_XII, f_XII x ∈ univ \ Λ → x ∈ S₁) →
    Injective ι_XII := by
  intro S' S₁ A_col C_col P₁_XII f_XII hf_inl hf_inr ι_XII hf_mem_S₁_of_compl ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
    hfx
  apply Subtype.ext
  dsimp [ι_XII] at hfx
  have hcol_inj : Set.InjOn f_XII C_col := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ heq
    rw [hf_inr y₁, hf_inr y₂] at heq
    have hcy₁ : collarCoords y₁ ∈ {q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ δ q.2} := by
      rw [← image_collarCoords_collar hδ_bd]; exact mem_image_of_mem collarCoords hy₁
    have hcy₂ : collarCoords y₂ ∈ {q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ δ q.2} := by
      rw [← image_collarCoords_collar hδ_bd]; exact mem_image_of_mem collarCoords hy₂
    have hp := hcMap_inj hcy₁ hcy₂ heq
    have hy_eq : y₁ = y₂ := injOn_collarCoords hδ_bd hy₁ hy₂ hp
    rw [hy_eq]
  by_cases hfx_compl : f_XII x₁ ∈ univ \ Λ
  · obtain ⟨y₁, rfl⟩ := hf_mem_S₁_of_compl x₁ hx₁ hfx_compl
    obtain ⟨y₂, rfl⟩ := hf_mem_S₁_of_compl x₂ hx₂ (hfx ▸ hfx_compl)
    rw [hf_inl, hf_inl] at hfx
    exact congrArg (GluedSpace.inl hb_inj) (Subtype.ext hfx)
  · have h_in_Λ : f_XII x₁ ∈ Λ := by
      by_contra hnot
      exact hfx_compl ⟨mem_univ _, hnot⟩
    have hx₁_col : x₁ ∈ C_col := by
      rcases hx₁ with ⟨y, rfl⟩ | hx₁_col
      · exact (y.2.2 (hf_inl y ▸ h_in_Λ)).elim
      · exact hx₁_col
    have hx₂_col : x₂ ∈ C_col := by
      have h_in_Λ' : f_XII x₂ ∈ Λ := hfx ▸ h_in_Λ
      rcases hx₂ with ⟨y, rfl⟩ | hx₂_col
      · exact (y.2.2 (hf_inl y ▸ h_in_Λ')).elim
      · exact hx₂_col
    exact hcol_inj hx₁_col hx₂_col hfx

private theorem crosscap_pieces_meet_at_pinched_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    (δ : Circle → ℝ)
    (hδ_bd : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
    let A_mid : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ
    let A_cuff : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCuffPairSet δ
    let C_col : Set S' := GluedSpace.inr hb_inj '' A_col
    let P₁_XII : Set S' := S₁ ∪ C_col
    let P₂_XII : Set S' := GluedSpace.inr hb_inj '' A_mid
    let C_XII : Fin 1 → Set S' := ![GluedSpace.inr hb_inj '' A_cuff]
    (∀ {α : Type w} (F : Fin 1 → Set α), ⋃ i, F i = F 0) →
    (C_XII 0 ⊆ P₁_XII) →
    P₁_XII ∩ P₂_XII = ⋃ i, C_XII i := by
  intro S' S₁ A_col A_mid A_cuff C_col P₁_XII P₂_XII C_XII hiUnion1 hC0_sub_P₁
  rw [hiUnion1 C_XII]
  ext x
  constructor
  · rintro ⟨hx1, ⟨y, ⟨p, hp_mid, rfl⟩, rfl⟩⟩
    rcases hx1 with ⟨w, hw_eq⟩ | ⟨y₁, hy₁, he₁⟩
    · obtain ⟨hy_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hw_eq
      have hp_bd : (p.2 : ℝ) = 0 ∨ (p.2 : ℝ) = 1 := by
        rcases eq_or_lt_of_le p.2.2.1 with h0 | h0
        · exact .inl h0.symm
        · rcases eq_or_lt_of_le p.2.2.2 with h1 | h1
          · exact .inr h1
          · exact (hy_bd (mobius_interior h0 h1)).elim
      refine ⟨Quotient.mk Surface.mobiusSetoid p, ⟨p, ?_, rfl⟩, rfl⟩
      rcases hp_bd with hp0' | hp1'
      · left
        linarith [hp0', hp_mid.1, (hδ_bd (circleTop p.1)).1]
      · right
        linarith [hp1', hp_mid.2, (hδ_bd (circleBot p.1)).1]
    · obtain rfl := GluedSpace.inr_injective hb_inj he₁
      obtain ⟨q, hq_col, hqp⟩ := hy₁
      have hp_col : p ∈ mobCollarPairSet δ :=
        mobCollarPairSet_saturated δ (Quotient.exact hqp) hq_col
      refine ⟨Quotient.mk Surface.mobiusSetoid p, ⟨p, ?_, rfl⟩, rfl⟩
      rcases hp_col with hp1 | hp2
      · exact .inl (le_antisymm hp1 hp_mid.1)
      · exact .inr (le_antisymm hp_mid.2 hp2)
  · rintro ⟨y, ⟨p, hp_cuff, rfl⟩, rfl⟩
    refine ⟨hC0_sub_P₁ ⟨_, ⟨p, hp_cuff, rfl⟩, rfl⟩, ⟨_, ⟨p, ?_, rfl⟩, rfl⟩⟩
    rcases hp_cuff with hp1 | hp2
    · exact ⟨le_of_eq hp1.symm,
        by linarith [show (p.2 : ℝ) = δ (circleTop p.1) from hp1,
          (hδ_bd (circleTop p.1)).2, (hδ_bd (circleBot p.1)).2]⟩
    · exact ⟨by linarith [show (p.2 : ℝ) = 1 - δ (circleBot p.1) from hp2,
          (hδ_bd (circleTop p.1)).2, (hδ_bd (circleBot p.1)).2],
        le_of_eq hp2⟩

private theorem crosscap_complement_boundary_is_pinched_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    (D₀ : Set S)
    (hD₀_open : IsOpen D₀) :
    let S' : Type w := GluedSpace hb_inj
    ∀ (P₁_XII : Set S'),
    ∀ (C_XII : Fin 1 → Set S'),
    ∀ (f_XII : S' → S),
    (f_XII '' C_XII 0 = subBd D₀) →
    ∀ (e_P₁ : ↑P₁_XII ≃ₜ ↑(univ \ D₀)),
    (∀ x, f_XII x.1 = (e_P₁ x).1) →
    (bd ↑(univ \ D₀) = Subtype.val ⁻¹' subBd D₀) →
    (∀ {α : Type w} (F : Fin 1 → Set α), ⋃ i, F i = F 0) →
    (C_XII 0 ⊆ P₁_XII) →
    (InjOn f_XII P₁_XII) →
    Subtype.val '' bd ↑P₁_XII = ⋃ i, C_XII i := by
  intro S' P₁_XII C_XII f_XII hf_img_C0 e_P₁ he_P₁ hXD_bd hiUnion1 hC0_sub_P₁ hf_injOn_P₁
  rw [hiUnion1 C_XII]
  have hsub1 : Subtype.val '' bd ↥P₁_XII ⊆ P₁_XII := by
    rintro _ ⟨x, _, rfl⟩; exact x.2
  refine (hf_injOn_P₁.image_eq_image_iff hsub1 hC0_sub_P₁).mp ?_
  rw [hf_img_C0]
  have hbd_e : e_P₁ '' bd ↥P₁_XII = bd ↥(univ \ D₀ : Set S) := image_bd_homeomorph e_P₁
  calc f_XII '' (Subtype.val '' bd ↥P₁_XII)
    _ = Subtype.val '' (e_P₁ '' bd ↥P₁_XII) := by
      rw [← image_comp, ← image_comp]
      exact congrArg (fun f => f '' bd ↥P₁_XII) (funext he_P₁)
    _ = Subtype.val '' bd ↥(univ \ D₀ : Set S) := by rw [hbd_e]
    _ = subBd D₀ := by
      rw [hXD_bd, Subtype.image_preimage_coe]
      refine inter_eq_right.mpr ?_
      rw [subBd_eq_frontier, hD₀_open.frontier_eq]
      exact fun x hx => ⟨mem_univ _, hx.2⟩

private theorem crosscap_retract_continuous_on_base
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    ∀ (e₁ : ↑(univ \ Λ) ≃ₜ ↑S₁),
    (∀ x, (e₁ x).1 = GluedSpace.inl hb_inj x) →
    ∀ (f_XII : S' → S),
    (∀ (y : ↑(univ \ Λ)), f_XII (GluedSpace.inl hb_inj y) = ↑y) →
    ContinuousOn f_XII S₁ := by
  intro S' S₁ e₁ he₁ f_XII hf_inl
  rw [continuousOn_iff_continuous_domRestrict]
  have hcongr : S₁.domRestrict f_XII = fun x : ↥S₁ => (e₁.symm x).1 := by
    ext x
    have hx : x.1 = GluedSpace.inl hb_inj (e₁.symm x) := by
      rw [← he₁, e₁.apply_symm_apply]
    change f_XII x.1 = (e₁.symm x).1
    rw [hx, hf_inl]
  rw [hcongr]
  exact continuous_subtype_val.comp e₁.symm.continuous

private theorem crosscap_retract_image_is_disc_complement
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (D₀ : Set S)
    (hD₀_sub : D₀ ⊆ Λ)
    (S' : Type w)
    (P₁_XII : Set S')
    (f_XII : S' → S)
    (hf_img_P₁ : f_XII '' P₁_XII = univ \ Λ ∪ closure Λ \ D₀) :
    f_XII '' P₁_XII = univ \ D₀ := by
  rw [hf_img_P₁]
  ext y
  constructor
  · rintro (hy | hy)
    · exact ⟨mem_univ _, fun h => hy.2 (hD₀_sub h)⟩
    · exact ⟨mem_univ _, hy.2⟩
  · rintro ⟨_, hy⟩
    by_cases hyΛ : y ∈ Λ
    · exact .inr ⟨subset_closure hyΛ, hy⟩
    · exact .inl ⟨mem_univ _, hyΛ⟩

private theorem pinched_crosscap_pieces_cover_surface
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    (hU_eq : range (GluedSpace.inl hb_inj) ∪ range (GluedSpace.inr hb_inj) = univ)
    (δ : Circle → ℝ) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
    let A_mid : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ
    let C_col : Set S' := GluedSpace.inr hb_inj '' A_col
    let P₁_XII : Set S' := S₁ ∪ C_col
    let P₂_XII : Set S' := GluedSpace.inr hb_inj '' A_mid
    P₁_XII ∪ P₂_XII = univ := by
  intro S' S₁ A_col A_mid C_col P₁_XII P₂_XII
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  ext x
  refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
  obtain hx1 | ⟨y, rfl⟩ : x ∈ S₁ ∪ S₂ := hU_eq.symm ▸ mem_univ x
  · exact .inl (.inl hx1)
  · obtain ⟨⟨u, v⟩, rfl⟩ := Quotient.exists_rep y
    by_cases h1 : (v : ℝ) ≤ δ (circleTop u)
    · exact .inl (.inr ⟨_, ⟨(u, v), .inl h1, rfl⟩, rfl⟩)
    · by_cases h2 : 1 - δ (circleBot u) ≤ (v : ℝ)
      · exact .inl (.inr ⟨_, ⟨(u, v), .inr h2, rfl⟩, rfl⟩)
      · exact .inr ⟨_, ⟨(u, v), ⟨le_of_not_ge h1, le_of_not_ge h2⟩, rfl⟩, rfl⟩

private theorem pinched_crosscap_complement_off_base_is_unmarked
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    {W_pts : Set Circle} :
    ∀ (δ : Circle → ℝ),
    (∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4) →
    (∀ (z : Circle), δ z = 0 ↔ z ∈ W_pts) →
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
    let C_col : Set S' := GluedSpace.inr hb_inj '' A_col
    let P₁_XII : Set S' := S₁ ∪ C_col
    P₁_XII \ range (GluedSpace.inl hb_inj) ⊆ GluedSpace.inr hb_inj '' {y | y ∉ bd MobiusBand ∧
      (collarCoords y).1 ≤ 1 / 4 ∧ (collarCoords y).2 ∉ W_pts} := by
  intro δ hδ_bd hδ_zero S' S₁ A_col C_col P₁_XII
  let b : ↑(bd MobiusBand) → ↑(univ \ Λ) := crosscapGlueMap hΛ_open g
  rintro x ⟨hx1 | ⟨y, hy, rfl⟩, hx_not_S₁⟩
  · exact (hx_not_S₁ hx1).elim
  · have hy_not_bd : y ∉ bd MobiusBand := fun hbd =>
      hx_not_S₁ ⟨b ⟨y, hbd⟩, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd, rfl⟩⟩
    have hcy : collarCoords y ∈ {q : ℝ × Circle | 0 ≤ q.1 ∧ q.1 ≤ δ q.2} := by
      rw [← image_collarCoords_collar hδ_bd]; exact mem_image_of_mem collarCoords hy
    have hy_le : (collarCoords y).1 ≤ 1 / 4 := hcy.2.trans (hδ_bd (collarCoords y).2).2
    have hyW : (collarCoords y).2 ∉ W_pts := fun hw => by
      have h0 := (hδ_zero (collarCoords y).2).mpr hw
      have hfst0 : (collarCoords y).1 = 0 := le_antisymm (h0 ▸ hcy.2) hcy.1
      exact hy_not_bd ((mem_bd_iff_collarCoords_fst_eq_zero hδ_bd hy).mpr hfst0)
    exact ⟨y, ⟨hy_not_bd, hy_le, hyW⟩, rfl⟩

private theorem unmarked_pinched_crosscap_cuff_lies_in_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    {W_pts : Set Circle}
    (δ : Circle → ℝ)
    (hδ_bd : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (hδ_zero : ∀ (z : Circle), δ z = 0 ↔ z ∈ W_pts) :
    let S' : Type w := GluedSpace hb_inj
    let A_cuff : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCuffPairSet δ
    let C_XII : Fin 1 → Set S' := ![GluedSpace.inr hb_inj '' A_cuff]
    C_XII 0 \ GluedSpace.inr hb_inj '' mobBd '' W_pts ⊆ GluedSpace.inr hb_inj '' {y | y ∉ bd
      MobiusBand ∧ (collarCoords y).1 ≤ 1 / 4 ∧ (collarCoords y).2 ∉ W_pts} := by
  intro S' A_cuff C_XII
  let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
  rintro _ ⟨⟨y, hy_cuff, rfl⟩, hnot_W⟩
  have hy_col : y ∈ A_col := by
    obtain ⟨p, hp, rfl⟩ := hy_cuff
    refine ⟨p, ?_, rfl⟩
    rcases hp with hp1 | hp2
    · exact .inl (le_of_eq hp1)
    · exact .inr (le_of_eq hp2.symm)
  have hcy_eq : (collarCoords y).1 = δ (collarCoords y).2 := by
    have h : collarCoords y ∈ {q : ℝ × Circle | q.1 = δ q.2} := by
      rw [← image_collarCoords_cuff hδ_bd]; exact mem_image_of_mem collarCoords hy_cuff
    exact h
  have hy_le : (collarCoords y).1 ≤ 1 / 4 := hcy_eq ▸ (hδ_bd (collarCoords y).2).2
  have hy_not_bd : y ∉ bd MobiusBand := fun hbd => by
    have h0 : (collarCoords y).1 = 0 :=
      (mem_bd_iff_collarCoords_fst_eq_zero hδ_bd hy_col).mp hbd
    have hw : (collarCoords y).2 ∈ W_pts := (hδ_zero (collarCoords y).2).mp (hcy_eq.symm.trans h0)
    have hpair : collarCoords y = (0, (collarCoords y).2) := Prod.ext h0 rfl
    have hy_mob : y = mobBd (collarCoords y).2 := by
      rw [← collarCoordsInv_zero, ← hpair, collarCoordsInv_collarCoords hδ_bd hy_col]
    exact hnot_W ⟨mobBd (collarCoords y).2, ⟨(collarCoords y).2, hw, rfl⟩,
      congrArg (GluedSpace.inr hb_inj) hy_mob.symm⟩
  have hyW : (collarCoords y).2 ∉ W_pts := fun hw => by
    have h0 : (collarCoords y).1 = 0 := hcy_eq.trans ((hδ_zero (collarCoords y).2).mpr hw)
    exact hy_not_bd ((mem_bd_iff_collarCoords_fst_eq_zero hδ_bd hy_col).mpr h0)
  exact ⟨y, ⟨hy_not_bd, hy_le, hyW⟩, rfl⟩

private theorem marked_crosscap_line_lies_in_middle_piece
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    {W_pts : Set Circle}
    (δ : Circle → ℝ)
    (hδ_zero : ∀ (z : Circle), δ z = 0 ↔ z ∈ W_pts) :
    let S' : Type w := GluedSpace hb_inj
    let A_mid : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ
    let P₂_XII : Set S' := GluedSpace.inr hb_inj '' A_mid
    ∀ (u : unitInterval), circleTop u ∈ W_pts → circleBot u ∈ W_pts → GluedSpace.inr hb_inj ''
      Quotient.mk Surface.mobiusSetoid '' {u} ×ˢ univ ⊆ P₂_XII := by
  intro S' A_mid P₂_XII
  rintro u hu_top hu_bot _ ⟨_, ⟨⟨u', v⟩, ⟨hu', _⟩, rfl⟩, rfl⟩
  have hu_eq : u = u' := hu'.symm
  subst hu_eq
  refine ⟨Quotient.mk Surface.mobiusSetoid (u, v), ⟨(u, v), ⟨?_, ?_⟩, rfl⟩, rfl⟩
  · linarith [v.2.1, (hδ_zero (circleTop u)).mpr hu_top]
  · linarith [v.2.2, (hδ_zero (circleBot u)).mpr hu_bot]

private theorem mobCuffPairSet_subset_collar (δ : Circle → ℝ) :
    mobCuffPairSet δ ⊆ mobCollarPairSet δ := by
  rintro p (hleft | hright)
  · exact Or.inl hleft.le
  · exact Or.inr hright.ge

/-- The pinched crosscap split on `GluedSpace hb_inj` touching `subBd Λ` only at `g '' W_pts`. -/
theorem exists_pinched_crosscapSplit {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Λ : Set S}
    (hΛ_open : IsOpen Λ) (hΛ : IsOpenDisc Λ)
    (hCD : IsClosedDisc (closure Λ))
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hOArc : IsOArc (subBd Λ))
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    (g : Circle ≃ₜ ↥(subBd Λ))
    (hb_inj : Function.Injective (crosscapGlueMap hΛ_open g))
    {W_pts : Set Circle} (hW_cl : IsClosed W_pts) (hW_ne : W_pts.Nonempty) :
    let S' := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let CollarInt : Set S' :=
      GluedSpace.inr hb_inj ''
        {y : MobiusBand | y ∉ bd MobiusBand ∧ (collarCoords y).1 ≤ 1 / 4 ∧
          (collarCoords y).2 ∉ W_pts}
    ∃ (C_XII : Fin 1 → Set S') (P₁_XII P₂_XII : Set S') (ι_XII : ↥P₁_XII → S)
      (D : Fin 1 → Set S) (f_XII : S' → S) (f_C0 : Circle ≃ₜ ↥(C_XII 0)),
      GM12.IsCrosscapSplit C_XII P₁_XII P₂_XII ι_XII D ∧
      S₁ ⊆ P₁_XII ∧
      (∀ y : ↥(univ \ Λ : Set S), f_XII (GluedSpace.inl hb_inj y) = y.1) ∧
      (∀ x : ↥P₁_XII, ι_XII x = f_XII x.1) ∧
      IsClosedEmbedding ι_XII ∧
      D 0 ⊆ Λ ∧
      closure (D 0) ⊆ closure Λ ∧
      P₁_XII \ S₁ ⊆ CollarInt ∧
      GluedSpace.inr hb_inj '' (mobBd '' W_pts) ⊆ C_XII 0 ∧
      C_XII 0 \ (GluedSpace.inr hb_inj '' (mobBd '' W_pts)) ⊆ CollarInt ∧
      (∀ u : unitInterval, circleTop u ∈ W_pts → circleBot u ∈ W_pts →
        GluedSpace.inr hb_inj '' (Quotient.mk Surface.mobiusSetoid '' ({u} ×ˢ univ)) ⊆ P₂_XII) ∧
      (∀ z ∈ W_pts, (f_C0 z).1 = GluedSpace.inr hb_inj (mobBd z)) := by
  have : CompactSpace S := hS.1
  have hX_closed : IsClosed (univ \ Λ : Set S) := isClosed_univ.sdiff hΛ_open
  have : CompactSpace ↥(univ \ Λ : Set S) := isCompact_iff_compactSpace.mp hX_closed.isCompact
  obtain ⟨m_mob⟩ := nonempty_mob_homeo
  have hMob_surf : IsSurface MobiusBand := isSurface_of_homeo m_mob (isSurface_model 0 1 1).1
  have : CompactSpace MobiusBand := hMob_surf.1
  have : T2Space MobiusBand := hMob_surf.2.1
  let b := crosscapGlueMap hΛ_open g
  have hb_cont := continuous_crosscapGlueMap hΛ_open g
  have hb_range := range_crosscapGlueMap hS hΛ_open hOArc hout g
  have : T2Space (GluedSpace hb_inj) := GluedSpace.t2Space (isClosed_bd MobiusBand) hb_cont hb_inj
  obtain ⟨hS', hConn', _, _, hS₂_surf, hU_eq, _, _⟩ :=
    isClosedSurface_of_crosscap_glue hS hΛ hOArc hout hb_cont hb_inj hb_range
  obtain ⟨δ, D₀, cMap, hδ_cont, hδ_bd, hδ_zero, hD₀_open, hD₀_sub, hCD_D₀, hsubBd_D₀_eq,
    hOArc_D₀, hout_D₀, _, _, _, hcMap_cont, hcMap_inj, hcMap_zero, hcMap_collar, hcMap_bd, _⟩ :=
    exists_pinched_subdisc_of_region hS hΛ_open hCD hdiscBd hout g hW_cl hW_ne
  have hcl_D₀_sub : closure D₀ ⊆ closure Λ := closure_mono hD₀_sub
  have hD₀_disc : IsOpenDisc D₀ :=
    isOpenDisc_of_isClosedDisc_closure hS hD₀_open hCD_D₀ hout_D₀
  let S' := GluedSpace hb_inj
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  let CollarInt : Set S' :=
    GluedSpace.inr hb_inj ''
      {y : MobiusBand | y ∉ bd MobiusBand ∧ (collarCoords y).1 ≤ 1 / 4 ∧ (collarCoords y).2 ∉ W_pts}
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  let e₁ : ↥(univ \ Λ : Set S) ≃ₜ ↥S₁ := hinl_emb.isEmbedding.toHomeomorph
  let e₂ : MobiusBand ≃ₜ ↥S₂ := hinr_emb.isEmbedding.toHomeomorph
  let A_col : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCollarPairSet δ
  let A_mid : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobPinchPairSet δ
  let A_cuff : Set MobiusBand := Quotient.mk Surface.mobiusSetoid '' mobCuffPairSet δ
  have hQ_col_cl : IsClosed (mobCollarPairSet δ) := by
    rw [mobCollarPairSet, Set.ofPred_or]
    refine IsClosed.union (isClosed_le ?_ ?_) (isClosed_le ?_ ?_)
    all_goals
      have := continuous_circleTop
      have := continuous_circleBot
      fun_prop
  have hQ_mid_cl : IsClosed (mobPinchPairSet δ) := by
    rw [mobPinchPairSet, Set.ofPred_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_le ?_ ?_)
    all_goals
      have := continuous_circleTop
      have := continuous_circleBot
      fun_prop
  have hA_col_cl : IsClosed A_col :=
    (hQ_col_cl.isCompact.image continuous_quotient_mk').isClosed
  have hA_mid_cl : IsClosed A_mid :=
    (hQ_mid_cl.isCompact.image continuous_quotient_mk').isClosed
  let C_col : Set S' := GluedSpace.inr hb_inj '' A_col
  let P₁_XII : Set S' := S₁ ∪ C_col
  let P₂_XII : Set S' := GluedSpace.inr hb_inj '' A_mid
  let C_XII : Fin 1 → Set S' := ![GluedSpace.inr hb_inj '' A_cuff]
  let f_XII : S' → S := crosscapPinchRetract hΛ_open g hb_inj cMap hcMap_zero
  have hf_inl : ∀ y, f_XII (GluedSpace.inl hb_inj y) = y.1 := fun _ => rfl
  have hf_inr : ∀ y, f_XII (GluedSpace.inr hb_inj y) = cMap (collarCoords y) := fun _ => rfl
  let ι_XII : ↥P₁_XII → S := fun x => f_XII x.1
  have hS₁_cl : IsClosed S₁ := hinl_emb.isClosed_range
  have hC_col_cl : IsClosed C_col := hinr_emb.isClosedMap _ hA_col_cl
  have : CompactSpace ↥P₁_XII := isCompact_iff_compactSpace.mp (hS₁_cl.union hC_col_cl).isCompact
  have hf_S₁_cont : ContinuousOn f_XII S₁ := by
    exact crosscap_retract_continuous_on_base (S := S) (Λ := Λ) hΛ_open g hb_inj e₁ (fun _
      => rfl) f_XII
      hf_inl
  have hf_col_cont : ContinuousOn f_XII C_col := by
    exact crosscap_retract_continuous_on_collar (S := S) (Λ := Λ) hΛ_open g hb_inj δ cMap hδ_cont
      hδ_bd hcMap_cont e₂ (fun _ => rfl) f_XII hf_inr
  have hf_P₁_cont : ContinuousOn f_XII P₁_XII :=
    hf_S₁_cont.union_of_isClosed hf_col_cont hS₁_cl hC_col_cl
  have hf_img_S₁ : f_XII '' S₁ = univ \ Λ := by
    ext y
    exact ⟨by rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact x.2,
      fun hy => ⟨GluedSpace.inl hb_inj ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩⟩
  have hf_img_col : f_XII '' C_col = closure Λ \ D₀ := by
    change f_XII '' (GluedSpace.inr hb_inj '' A_col) = closure Λ \ D₀
    rw [← image_comp]
    have hcomp : f_XII ∘ GluedSpace.inr hb_inj = cMap ∘ collarCoords := rfl
    rw [hcomp, image_comp, image_collarCoords_collar hδ_bd, hcMap_collar]
  have hf_img_C0 : f_XII '' (C_XII 0) = subBd D₀ := by
    change f_XII '' (GluedSpace.inr hb_inj '' A_cuff) = subBd D₀
    rw [← image_comp]
    have hcomp : f_XII ∘ GluedSpace.inr hb_inj = cMap ∘ collarCoords := rfl
    rw [hcomp, image_comp, image_collarCoords_cuff hδ_bd, hcMap_bd]
  have hf_img_P₁ : f_XII '' P₁_XII = (univ \ Λ) ∪ (closure Λ \ D₀) := by
    change f_XII '' (S₁ ∪ C_col) = _
    rw [image_union, hf_img_S₁, hf_img_col]
  have hf_img_P₁_compl : f_XII '' P₁_XII = univ \ D₀ := by
    exact crosscap_retract_image_is_disc_complement (S := S) (Λ := Λ) D₀ hD₀_sub S' P₁_XII f_XII
      hf_img_P₁
  have hcol_interior : ∀ y ∈ A_col, y ∉ bd MobiusBand → f_XII (GluedSpace.inr hb_inj y) ∈ Λ := by
    exact crosscap_collar_interior_maps_inside_disc (S := S) (Λ := Λ) hΛ_open g hb_inj δ D₀ cMap
      hδ_bd hcMap_inj hcMap_zero    f_XII hf_inr hf_img_col
  have hf_mem_S₁_of_compl : ∀ x ∈ P₁_XII, f_XII x ∈ univ \ Λ → x ∈ S₁ := by
    rintro x (hx | ⟨y, hy, rfl⟩) hfx
    · exact hx
    · by_cases hy_bd : y ∈ bd MobiusBand
      · exact ⟨b ⟨y, hy_bd⟩, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hy_bd, rfl⟩⟩
      · exact (hfx.2 (hcol_interior y hy hy_bd)).elim
  have hι_XII_inj : Function.Injective ι_XII := by
    exact crosscap_retract_injective_on_pinched_complement (S := S) (Λ := Λ) hΛ_open g hb_inj δ
      cMap hδ_bd hcMap_inj f_XII hf_inl hf_inr hf_mem_S₁_of_compl
  have hι_XII_emb : IsClosedEmbedding ι_XII :=
    (continuousOn_iff_continuous_domRestrict.mp hf_P₁_cont).isClosedEmbedding hι_XII_inj
  have hι_XII_range := (image_eq_range f_XII P₁_XII).symm.trans hf_img_P₁_compl
  let e_P₁ : ↥P₁_XII ≃ₜ ↥(univ \ D₀ : Set S) :=
    hι_XII_emb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hι_XII_range)
  obtain ⟨hXD_surf, _, hXD_bd, _⟩ := compl_open_isSurface hS hD₀_open hOArc_D₀ hout_D₀
  have hP₁_surf : IsSurface ↥P₁_XII := isSurface_of_homeo e_P₁.symm hXD_surf
  let e_pinch := pinchMobHomeo hδ_cont hδ_bd
  let j_P₂ : MobiusBand → S' := fun p => GluedSpace.inr hb_inj (e_pinch p).1
  have hj_P₂_emb : IsClosedEmbedding j_P₂ :=
    hinr_emb.comp (hA_mid_cl.isClosedEmbedding_subtypeVal.comp e_pinch.isClosedEmbedding)
  have hj_P₂_range : range j_P₂ = P₂_XII := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(e_pinch p).1, (e_pinch p).2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨e_pinch.symm ⟨q, hq⟩, by dsimp [j_P₂]; rw [e_pinch.apply_symm_apply]⟩
  let e_P₂ : MobiusBand ≃ₜ ↥P₂_XII :=
    hj_P₂_emb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hj_P₂_range)
  have hP₂_surf : IsSurface ↥P₂_XII := isSurface_of_homeo e_P₂ hMob_surf
  let c0_map : Circle → S' := fun z => GluedSpace.inr hb_inj (pinchMobBd hδ_cont hδ_bd z)
  have hc0_emb : IsEmbedding c0_map :=
    hinr_emb.isEmbedding.comp (isEmbedding_pinchMobBd hδ_cont hδ_bd)
  have hc0_range : range c0_map = C_XII 0 := by
    change range (GluedSpace.inr hb_inj ∘ pinchMobBd hδ_cont hδ_bd) =
      GluedSpace.inr hb_inj '' A_cuff
    rw [range_comp, range_pinchMobBd hδ_cont hδ_bd]
  let f_C0 : Circle ≃ₜ ↥(C_XII 0) :=
    hc0_emb.toHomeomorph.trans (Homeomorph.setCongr hc0_range)
  have hj_P₂_cuff : j_P₂ '' bd MobiusBand = C_XII 0 := by
    rw [bd_mobiusBand, ← range_comp]
    exact hc0_range
  have hiUnion1 : ∀ {α : Type w} (F : Fin 1 → Set α), (⋃ i : Fin 1, F i) = F 0 := by
    intro α F; ext x; simp
  have hbd_P₂ : Subtype.val '' bd ↥P₂_XII = ⋃ i : Fin 1, C_XII i := by
    rw [hiUnion1 C_XII, ← hj_P₂_cuff, ← image_bd_homeomorph e_P₂, image_image]
    rfl
  have hC0_sub_P₁ : C_XII 0 ⊆ P₁_XII :=
    (image_mono (image_mono (mobCuffPairSet_subset_collar δ))).trans subset_union_right
  have hP12_union : P₁_XII ∪ P₂_XII = univ :=
    pinched_crosscap_pieces_cover_surface (S := S) (Λ := Λ) hΛ_open g hb_inj hU_eq δ
  have hP12_inter : P₁_XII ∩ P₂_XII = ⋃ i : Fin 1, C_XII i := by
    exact crosscap_pieces_meet_at_pinched_cuff (S := S) (Λ := Λ) hΛ_open g hb_inj δ hδ_bd
             hiUnion1 hC0_sub_P₁
  have hf_injOn_P₁ : Set.InjOn f_XII P₁_XII :=
    fun x₁ hx₁ x₂ hx₂ h => congrArg Subtype.val (@hι_XII_inj ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h)
  have hbd_P₁ : Subtype.val '' bd ↥P₁_XII = ⋃ i : Fin 1, C_XII i := by
    exact crosscap_complement_boundary_is_pinched_cuff (S := S) (Λ := Λ) hΛ_open g hb_inj D₀
      hD₀_open P₁_XII C_XII f_XII hf_img_C0 e_P₁ (fun _ => rfl) hXD_bd hiUnion1 hC0_sub_P₁
        hf_injOn_P₁
  refine ⟨C_XII, P₁_XII, P₂_XII, ι_XII, ![D₀], f_XII, f_C0,
    ⟨?_, inferInstance, ⟨e_P₂.symm.trans mobiusSetoidHomeo⟩⟩,
    subset_union_left, fun _ => rfl, fun _ => rfl, hι_XII_emb, hD₀_sub, hcl_D₀_sub,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine
      { surface := ⟨hS', hConn'⟩
        isOArc := fun i => by
          fin_cases i
          exact ⟨f_C0⟩
        disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
        manifold₁ := hP₁_surf
        manifold₂ := hP₂_surf
        union := hP12_union
        inter := hP12_inter
        bd₁ := hbd_P₁
        bd₂ := hbd_P₂
        surface_hat := hS
        isEmbedding := hι_XII_emb.isEmbedding
        isOpenDisc := fun i => by fin_cases i; exact hD₀_disc
        bounds := fun i => by
          fin_cases i
          change subBd D₀ = ι_XII '' (Subtype.val ⁻¹' (C_XII 0))
          rw [← hf_img_C0]
          ext y
          exact ⟨by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hC0_sub_P₁ hx⟩, hx, rfl⟩,
            by rintro ⟨⟨x, _⟩, hx, rfl⟩; exact ⟨x, hx, rfl⟩⟩
        disjoint_D := fun i j hij => (hij (Subsingleton.elim i j)).elim
        compl := by
          rw [hiUnion1 ![D₀], hι_XII_range]
          ext x
          simp only [mem_compl_iff, mem_sdiff, mem_univ, true_and, Matrix.cons_val_zero]
          tauto }
  · exact pinched_crosscap_complement_off_base_is_unmarked (S := S) (Λ := Λ) hΛ_open g hb_inj
      (W_pts := W_pts)  δ hδ_bd hδ_zero
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [← pinchMobBd_eq_mobBd_of_eq_zero hδ_cont hδ_bd ((hδ_zero z).mpr hz), ← hc0_range]
    exact ⟨z, rfl⟩
  · exact unmarked_pinched_crosscap_cuff_lies_in_collar (S := S) (Λ := Λ) hΛ_open g hb_inj (W_pts
      := W_pts) δ hδ_bd hδ_zero
  · exact marked_crosscap_line_lies_in_middle_piece (S := S) (Λ := Λ) hΛ_open g hb_inj (W_pts :=
      W_pts) δ hδ_zero
  · intro z hz
    change GluedSpace.inr hb_inj (pinchMobBd hδ_cont hδ_bd z) = GluedSpace.inr hb_inj (mobBd z)
    rw [pinchMobBd_eq_mobBd_of_eq_zero hδ_cont hδ_bd ((hδ_zero z).mpr hz)]

theorem circle_cross_eq_zero_iff (z z₀ : Circle) :
    (z : ℂ).im * (z₀ : ℂ).re - (z : ℂ).re * (z₀ : ℂ).im = 0 ↔ z = z₀ ∨ z = -z₀ := by
  have hz := circle_re_sq_add_im_sq z
  have hz₀ := circle_re_sq_add_im_sq z₀
  constructor
  · intro him
    have hre_sq : ((z : ℂ).re * (z₀ : ℂ).re + (z : ℂ).im * (z₀ : ℂ).im) ^ 2 = 1 := by
      have hid : ((z : ℂ).re * (z₀ : ℂ).re + (z : ℂ).im * (z₀ : ℂ).im) ^ 2 +
          ((z : ℂ).im * (z₀ : ℂ).re - (z : ℂ).re * (z₀ : ℂ).im) ^ 2 =
          ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) * ((z₀ : ℂ).re ^ 2 + (z₀ : ℂ).im ^ 2) := by ring
      nlinarith
    have hid_re : ((z : ℂ).re * (z₀ : ℂ).re + (z : ℂ).im * (z₀ : ℂ).im) * (z₀ : ℂ).re -
        ((z : ℂ).im * (z₀ : ℂ).re - (z : ℂ).re * (z₀ : ℂ).im) * (z₀ : ℂ).im =
        (z : ℂ).re * ((z₀ : ℂ).re ^ 2 + (z₀ : ℂ).im ^ 2) := by ring
    have hid_im : ((z : ℂ).re * (z₀ : ℂ).re + (z : ℂ).im * (z₀ : ℂ).im) * (z₀ : ℂ).im +
        ((z : ℂ).im * (z₀ : ℂ).re - (z : ℂ).re * (z₀ : ℂ).im) * (z₀ : ℂ).re =
        (z : ℂ).im * ((z₀ : ℂ).re ^ 2 + (z₀ : ℂ).im ^ 2) := by ring
    rcases sq_eq_one_iff.mp hre_sq with hre | hre
    · left
      apply Subtype.ext
      apply Complex.ext
      · rw [hre, him, hz₀] at hid_re; linarith
      · rw [hre, him, hz₀] at hid_im; linarith
    · right
      apply Subtype.ext
      apply Complex.ext
      · change (z : ℂ).re = - (z₀ : ℂ).re
        rw [hre, him, hz₀] at hid_re; linarith
      · change (z : ℂ).im = - (z₀ : ℂ).im
        rw [hre, him, hz₀] at hid_im; linarith
  · rintro (rfl | rfl)
    · ring
    · change (- (z₀ : ℂ).im) * (z₀ : ℂ).re - (- (z₀ : ℂ).re) * (z₀ : ℂ).im = 0
      ring

theorem not_mem_and_neg_mem_of_isPreconnected_circle {A : Set Circle}
    (hA : IsPreconnected A) {z₀ : Circle} (hz₀ : z₀ ∉ A) (hneg_z₀ : -z₀ ∉ A)
    (z : Circle) : ¬ (z ∈ A ∧ -z ∈ A) := by
  rintro ⟨hz, hneg_z⟩
  let f : Circle → ℝ := fun w => (w : ℂ).im * (z₀ : ℂ).re - (w : ℂ).re * (z₀ : ℂ).im
  have hf_cont : Continuous f := by
    dsimp [f]
    fun_prop
  let U₁ : Set Circle := {w | f w < 0}
  let U₂ : Set Circle := {w | 0 < f w}
  have hU₁ : IsOpen U₁ := isOpen_lt hf_cont continuous_const
  have hU₂ : IsOpen U₂ := isOpen_lt continuous_const hf_cont
  have hcov : A ⊆ U₁ ∪ U₂ := by
    intro w hw
    have hne0 : f w ≠ 0 := by
      intro h0
      rcases (circle_cross_eq_zero_iff w z₀).mp h0 with rfl | rfl
      · exact hz₀ hw
      · exact hneg_z₀ hw
    exact lt_or_gt_of_ne hne0
  have hf_neg : f (-z) = - f z := by
    change (- (z : ℂ).im) * (z₀ : ℂ).re - (- (z : ℂ).re) * (z₀ : ℂ).im =
      - ((z : ℂ).im * (z₀ : ℂ).re - (z : ℂ).re * (z₀ : ℂ).im)
    ring
  have h1 : (A ∩ U₁).Nonempty := by
    rcases hcov hz with hz1 | hz2
    · exact ⟨z, hz, hz1⟩
    · refine ⟨-z, hneg_z, ?_⟩
      change f (-z) < 0
      linarith [show 0 < f z from hz2]
  have h2 : (A ∩ U₂).Nonempty := by
    rcases hcov hz with hz1 | hz2
    · refine ⟨-z, hneg_z, ?_⟩
      change 0 < f (-z)
      linarith [show f z < 0 from hz1]
    · exact ⟨z, hz, hz2⟩
  obtain ⟨w, _, hw1, hw2⟩ := hA U₁ U₂ hU₁ hU₂ hcov h1 h2
  linarith [show f w < 0 from hw1, show 0 < f w from hw2]

theorem disjoint_mobVertical_of_ne {u₁ u₂ : unitInterval}
    (hu₁0 : 0 < (u₁ : ℝ)) (hu₁1 : (u₁ : ℝ) < 1) (hne : u₁ ≠ u₂) :
    Disjoint (Quotient.mk Surface.mobiusSetoid '' ({u₁} ×ˢ univ))
      (Quotient.mk Surface.mobiusSetoid '' ({u₂} ×ˢ univ)) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨⟨u₁', v₁⟩, ⟨hu₁', _⟩, rfl⟩ ⟨⟨u₂', v₂⟩, ⟨hu₂', _⟩, heq⟩
  have h1 : u₁ = u₁' := hu₁'.symm
  have h2 : u₂ = u₂' := hu₂'.symm
  subst h1 h2
  rcases mobius_rel (Quotient.exact heq.symm) with h | ⟨h1, _, _⟩ | ⟨_, h2, _⟩
  · exact hne (congrArg Prod.fst h)
  · exact hu₁0.ne (congrArg Subtype.val h1).symm
  · exact hu₁1.ne (congrArg Subtype.val h2)

/-- Lifting `exists_striped_disc_in_mobiusBand` to `S₂ = range (GluedSpace.inr hb_inj)` when a
closed subset `K_sub ⊆ S₂` avoids at least one vertical line `L i₀`. -/
theorem exists_striped_disc_in_S₂_crosscap {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↥(subBd Λ))
    (hb_inj : Function.Injective (crosscapGlueMap hΛ_open g))
    {φ : ℕ} {u_pt : Fin φ → unitInterval}
    (hu_inj : Function.Injective u_pt)
    (hu_int : ∀ i, 0 < (u_pt i : ℝ) ∧ (u_pt i : ℝ) < 1)
    {a' b' : Fin φ → GluedSpace hb_inj}
    (ha' : ∀ i, a' i = GluedSpace.inr hb_inj (Quotient.mk Surface.mobiusSetoid (u_pt i, 0)))
    (hb' : ∀ i, b' i = GluedSpace.inr hb_inj (Quotient.mk Surface.mobiusSetoid (u_pt i, 1)))
    {L : Fin φ → Set (GluedSpace hb_inj)}
    (hL : ∀ i, L i =
      GluedSpace.inr hb_inj '' (Quotient.mk Surface.mobiusSetoid '' ({u_pt i} ×ˢ univ)))
    {H_path : Fin φ → Drawing (GluedSpace hb_inj)}
    (hH_path_U : ∀ i, (H_path i).U = L i)
    {H' : Drawing (GluedSpace hb_inj)}
    (hS₂_U : range (GluedSpace.inr hb_inj) ∩ H'.U ⊆
      (range (GluedSpace.inl hb_inj) ∩ range (GluedSpace.inr hb_inj)) ∪ ⋃ i : Fin φ, L i)
    {K_sub : Set (GluedSpace hb_inj)} (hK_sub_cl : IsClosed K_sub)
    (hK_sub_S₂ : K_sub ⊆ range (GluedSpace.inr hb_inj))
    (i₀ : Fin φ) (hK_sub_disj : Disjoint K_sub (L i₀)) :
    let S₁ : Set (GluedSpace hb_inj) := range (GluedSpace.inl hb_inj)
    let S₂ : Set (GluedSpace hb_inj) := range (GluedSpace.inr hb_inj)
    ∃ D : Set (GluedSpace hb_inj),
      D ⊆ S₂ ∧
      IsClosedDisc D ∧
      K_sub ⊆ D ∧
      D ∩ (S₁ ∩ S₂) ⊆ discBd D ∧
      D ∩ H'.U ⊆ (D ∩ (S₁ ∩ S₂)) ∪ ⋃ j : {i : Fin φ // i ≠ i₀}, (H_path j.1).U ∧
      ∀ j : {i : Fin φ // i ≠ i₀},
        (H_path j.1).U ⊆ D ∧
        (H_path j.1).U ∩ discBd D = {a' j.1, b' j.1} := by
  have : CompactSpace S := hS.1
  have hX_closed : IsClosed (univ \ Λ : Set S) := isClosed_univ.sdiff hΛ_open
  have : CompactSpace ↥(univ \ Λ : Set S) := isCompact_iff_compactSpace.mp hX_closed.isCompact
  obtain ⟨m_mob⟩ := nonempty_mob_homeo
  have hMob_surf : IsSurface MobiusBand := isSurface_of_homeo m_mob (isSurface_model 0 1 1).1
  have : CompactSpace MobiusBand := hMob_surf.1
  have : T2Space MobiusBand := hMob_surf.2.1
  have hb_cont := continuous_crosscapGlueMap hΛ_open g
  have : T2Space (GluedSpace hb_inj) :=
    GluedSpace.t2Space (isClosed_bd MobiusBand) hb_cont hb_inj
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  let K_all : Set MobiusBand :=
    (GluedSpace.inr hb_inj ⁻¹' K_sub) ∪
      ⋃ j : {i : Fin φ // i ≠ i₀}, Quotient.mk Surface.mobiusSetoid '' ({u_pt j.1} ×ˢ univ)
  have hK_all_cl : IsClosed K_all := by
    refine (hK_sub_cl.preimage (GluedSpace.continuous_inr hb_inj)).union ?_
    exact isClosed_iUnion_of_finite fun j =>
      ((isCompact_singleton.prod isCompact_univ).image continuous_quotient_mk').isClosed
  have hK_all_disj :
      Disjoint K_all (Quotient.mk Surface.mobiusSetoid '' ({u_pt i₀} ×ˢ univ)) := by
    refine Set.disjoint_left.mpr ?_
    rintro y (hy_sub | hy_vert) hy_i₀
    · have hy_L : GluedSpace.inr hb_inj y ∈ L i₀ := by
        rw [hL i₀]
        exact ⟨y, hy_i₀, rfl⟩
      exact Set.disjoint_left.mp hK_sub_disj hy_sub hy_L
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hy_vert
      exact Set.disjoint_left.mp
        (disjoint_mobVertical_of_ne (hu_int j.1).1 (hu_int j.1).2 (fun h => j.2 (hu_inj h)))
        hj hy_i₀
  obtain ⟨D_mob, ⟨ψ_mob⟩, hK_sub_D_mob, hD_mob_disj, hbd_sub_D_mob, hvert_D_mob⟩ :=
    exists_striped_disc_in_mobiusBand (u_pt i₀) (hu_int i₀).1 (hu_int i₀).2 hK_all_cl hK_all_disj
  let D : Set (GluedSpace hb_inj) := GluedSpace.inr hb_inj '' D_mob
  have hD_S₂ : D ⊆ range (GluedSpace.inr hb_inj) := image_subset_range _ _
  let f_D : ↥D_mob → GluedSpace hb_inj := fun p => GluedSpace.inr hb_inj p.1
  have hf_D_emb : IsEmbedding f_D := hinr_emb.isEmbedding.comp IsEmbedding.subtypeVal
  have hf_D_range : range f_D = D := by
    ext x
    exact ⟨by rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩,
      by rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩⟩
  let e_D : ↥D_mob ≃ₜ ↥D := hf_D_emb.toHomeomorph.trans (Homeomorph.setCongr hf_D_range)
  have hD_disc : IsClosedDisc D := ⟨ψ_mob.trans e_D⟩
  have hdiscBd_D : discBd D = GluedSpace.inr hb_inj '' discBd D_mob := by
    change Subtype.val '' bd ↥D = GluedSpace.inr hb_inj '' (Subtype.val '' bd ↥D_mob)
    rw [← image_bd_homeomorph e_D, image_image, image_image]
    rfl
  refine ⟨D, hD_S₂, hD_disc, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ := hK_sub_S₂ hx
    exact ⟨p, hK_sub_D_mob (.inl hx), rfl⟩
  · rintro _ ⟨⟨p, hpD, rfl⟩, ⟨y, hy_eq⟩, _⟩
    obtain ⟨hp_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hy_eq
    rw [hdiscBd_D]
    exact ⟨p, hbd_sub_D_mob ⟨hpD, hp_bd⟩, rfl⟩
  · rintro x ⟨hxD, hxU⟩
    rcases hS₂_U ⟨hD_S₂ hxD, hxU⟩ with hx12 | hxL
    · exact .inl ⟨hxD, hx12⟩
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxL
      by_cases hi : i = i₀
      · subst hi
        obtain ⟨p, hpD, rfl⟩ := hxD
        rw [hL i] at hxi
        obtain ⟨q, hq_u, hq_eq⟩ := hxi
        have hpq := GluedSpace.inr_injective hb_inj hq_eq
        subst hpq
        exact (Set.disjoint_left.mp hD_mob_disj hpD hq_u).elim
      · right
        refine mem_iUnion.mpr ⟨⟨i, hi⟩, ?_⟩
        rwa [hH_path_U i]
  · intro j
    have hsub_j : Quotient.mk Surface.mobiusSetoid '' ({u_pt j.1} ×ˢ univ) ⊆ K_all :=
      fun p hp => .inr (mem_iUnion.mpr ⟨j, hp⟩)
    obtain ⟨hj_sub, hj_bd⟩ := hvert_D_mob (u_pt j.1) (hu_int j.1).1 (hu_int j.1).2 hsub_j
    rw [hH_path_U j.1, hL j.1, hdiscBd_D, ha' j.1, hb' j.1]
    refine ⟨image_mono hj_sub, ?_⟩
    rw [← Set.image_inter (GluedSpace.inr_injective hb_inj), hj_bd, image_pair]

/-! ## 3. Proof of Graph Minors XV, (3.3) -/

/-- Model angles on `Circle` for `a_0, ..., a_{φ-1}, b_0, ..., b_{φ-1}` so that `b_i` is antipodal
to `a_i`. -/
noncomputable def crosscapModelAngle (φ k : ℕ) : ℝ :=
  if k < φ then
    (k + 1 : ℝ) / (φ + 1 : ℝ) * Real.pi
  else
    ((k - φ : ℕ) + 1 : ℝ) / (φ + 1 : ℝ) * Real.pi + Real.pi

theorem strictMono_crosscapModelAngle {φ : ℕ} (hφ : 3 ≤ φ) :
    StrictMono (crosscapModelAngle φ) := by
  intro i j hij
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < (φ + 1 : ℝ) := by positivity
  dsimp [crosscapModelAngle]
  split_ifs with hi hj hj
  · refine mul_lt_mul_of_pos_right ?_ hpi
    exact div_lt_div_of_pos_right (by exact_mod_cast Nat.add_lt_add_right hij 1) hden
  · have h1 : (i + 1 : ℝ) / (φ + 1 : ℝ) < 1 :=
      (div_lt_one hden).mpr (by exact_mod_cast Nat.add_lt_add_right hi 1)
    have h2 : 0 < ((j - φ : ℕ) + 1 : ℝ) / (φ + 1 : ℝ) := by positivity
    nlinarith
  · omega
  · have hlt : ((i - φ : ℕ) + 1 : ℝ) / (φ + 1 : ℝ) < ((j - φ : ℕ) + 1 : ℝ) / (φ + 1 : ℝ) := by
      refine div_lt_div_of_pos_right ?_ hden
      have hsub : i - φ < j - φ := by omega
      exact_mod_cast Nat.add_lt_add_right hsub 1
    nlinarith

theorem crosscapModelAngle_lt_add_two_pi {φ : ℕ} (hφ : 3 ≤ φ) :
    ∀ k < 2 * φ, crosscapModelAngle φ k < crosscapModelAngle φ 0 + 2 * Real.pi := by
  intro k hk
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < (φ + 1 : ℝ) := by positivity
  have h0_pos : 0 < crosscapModelAngle φ 0 := by
    dsimp [crosscapModelAngle]
    have h0 : 0 < φ := by omega
    simp only [h0, ↓reduceIte, Nat.cast_zero, zero_add]
    positivity
  have hlt : crosscapModelAngle φ k < 2 * Real.pi := by
    dsimp [crosscapModelAngle]
    split_ifs with hkφ
    · have h1 : (k + 1 : ℝ) / (φ + 1 : ℝ) < 1 :=
        (div_lt_one hden).mpr (by exact_mod_cast Nat.add_lt_add_right hkφ 1)
      nlinarith
    · have hsub : k - φ < φ := by omega
      have h1 : ((k - φ : ℕ) + 1 : ℝ) / (φ + 1 : ℝ) < 1 :=
        (div_lt_one hden).mpr (by exact_mod_cast Nat.add_lt_add_right hsub 1)
      nlinarith
  linarith

theorem crosscapModelAngle_add_phi {φ i : ℕ} (hi : i < φ) :
    crosscapModelAngle φ (φ + i) = crosscapModelAngle φ i + Real.pi := by
  have hnot : ¬ (φ + i < φ) := by omega
  have hsub : φ + i - φ = i := by omega
  dsimp [crosscapModelAngle]
  simp only [hi, hnot, ↓reduceIte, hsub]

theorem crosscapModelAngle_mem_Ioo_pi {φ i : ℕ} (hi : i < φ) :
    0 < crosscapModelAngle φ i ∧ crosscapModelAngle φ i < Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < (φ + 1 : ℝ) := by positivity
  dsimp [crosscapModelAngle]
  simp only [hi, ↓reduceIte]
  refine ⟨by positivity, ?_⟩
  have h1 : (i + 1 : ℝ) / (φ + 1 : ℝ) < 1 :=
    (div_lt_one hden).mpr (by exact_mod_cast Nat.add_lt_add_right hi 1)
  nlinarith

theorem circle_exp_add_pi (θ : ℝ) : Circle.exp (θ + Real.pi) = - Circle.exp θ := by
  apply Subtype.ext
  change (Circle.exp (θ + Real.pi) : ℂ) = - (Circle.exp θ : ℂ)
  rw [Circle.coe_exp, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I,
    ← Circle.coe_exp]
  ring

theorem circle_exp_im_pos_of_mem_Ioo {θ : ℝ} (h0 : 0 < θ) (hpi : θ < Real.pi) :
    0 < (Circle.exp θ : ℂ).im := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi h0 hpi

theorem circle_exp_re_mem_Ioo_of_mem_Ioo {θ : ℝ} (h0 : 0 < θ) (hpi : θ < Real.pi) :
    -1 < (Circle.exp θ : ℂ).re ∧ (Circle.exp θ : ℂ).re < 1 := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have h1 : Real.cos Real.pi < Real.cos θ :=
    Real.strictAntiOn_cos ⟨le_of_lt h0, le_of_lt hpi⟩ ⟨le_of_lt (h0.trans hpi), le_rfl⟩ hpi
  have h2 : Real.cos θ < Real.cos 0 :=
    Real.strictAntiOn_cos ⟨le_rfl, le_of_lt (h0.trans hpi)⟩ ⟨le_of_lt h0, le_of_lt hpi⟩ h0
  rw [Real.cos_pi] at h1
  rw [Real.cos_zero] at h2
  exact ⟨h1, h2⟩

theorem mobBdBotU_neg (z : Circle) : mobBdBotU (-z) = mobBdTopU z := by
  apply Subtype.ext
  rw [mobBdBotU_coe, mobBdTopU_coe]
  change (1 + (- (z : ℂ)).re) / 2 = (1 - (z : ℂ).re) / 2
  dsimp
  ring

private noncomputable abbrev crosscap_vertical_lines
    {S' : Type*} {φ : ℕ} (inr : MobiusBand → S') (u : Fin φ → unitInterval) (i : Fin φ) : Set S' :=
  inr '' (Quotient.mk Surface.mobiusSetoid '' ({u i} ×ˢ univ))

private theorem drawing_on_added_crosscap_is_rigid
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (θ : ℕ)
    (φ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Λ : Set S)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hφ : 3 ≤ φ)
    (hFree_ab : IsFreeSet H.toHypergraph T θ (range a ∪ range b))
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    (hRigid_H : IsRigid H)
    (hT : IsTangle H.toHypergraph θ T)
    (hθ : 3 ≤ θ)
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (w_a : Fin φ → Circle)
    (w_b : Fin φ → Circle)
    (hwb_eq_neg : ∀ (i : Fin φ), w_b i = -w_a i)
    (u_pt : Fin φ → unitInterval)
    (hu_int : ∀ (i : Fin φ), 0 < ↑(u_pt i) ∧ ↑(u_pt i) < 1)
    (hu_inj : Injective u_pt)
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) [T2Space (GluedSpace hb_inj)]
    (hS' : IsClosedSurface (GluedSpace hb_inj))
    (hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj))
    (hS₁_cl : IsClosed (range (GluedSpace.inl hb_inj)))
    (hS₂_cl : IsClosed (range (GluedSpace.inr hb_inj)))
    (C_unp : Fin 1 → Set (GluedSpace hb_inj))
    (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S)
    (hSplit_unp : IsCappedSplit C_unp (range (GluedSpace.inl hb_inj)) (range (GluedSpace.inr
      hb_inj)) ι_unp ![Λ])
    (hC_unp_0 : C_unp 0 = GluedSpace.inr hb_inj '' bd MobiusBand)
    (hS12_inter : (range (GluedSpace.inl hb_inj)) ∩ (range (GluedSpace.inr hb_inj)) = C_unp 0)
    (H₁ : Drawing (GluedSpace hb_inj))
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (ha'_V : ∀ (i : Fin φ), a' i ∈ H₁.V)
    (hb'_V : ∀ (i : Fin φ), b' i ∈ H₁.V)
    (ha'_mobBd : ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj (mobBd (w_a i)))
    (hb'_mobBd : ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj (mobBd (w_b i)))
    (ha'_inr : ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj ⟦(u_pt i, 0)⟧)
    (hb'_inr : ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj ⟦(u_pt i, 1)⟧)
    (hL_line : ∀ (i : Fin φ), IsLineWithEnds (crosscap_vertical_lines
      (GluedSpace.inr hb_inj) u_pt i) (a' i) (b' i))
    (hL_disj : Pairwise fun i j => Disjoint (crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt
      i) ((fun i : Fin φ =>
      GluedSpace.inr hb_inj '' (Quotient.mk Surface.mobiusSetoid '' ({u_pt i} ×ˢ univ))) j))
    (hL_S₁ : ∀ (i : Fin φ), crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i ∩ (range
      (GluedSpace.inl hb_inj)) = {a' i, b' i})
    (H_path : Fin φ → Drawing (GluedSpace hb_inj))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i)
    (hSub_H₁ : H₁.IsSubdrawing H')
    (hH_path : ∀ (i : Fin φ), (H_path i).U = crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i
      ∧ (H_path i).IsPathBetween (a' i) (b' i) ∧ (H_path i).IsSubdrawing H' ∧ a' i ∈ (H_path i).V
        ∧ b' i ∈ (H_path i).V)
    (hCap_unp : IsCappedDrawing ι_unp H' H)
    (hS12_sub_U : (range (GluedSpace.inl hb_inj)) ∩ (range (GluedSpace.inr hb_inj)) ⊆ H'.U)
    (hX_unp_sub : (range a' ∪ range b') ⊆ H'.V ∩ ((range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr
      hb_inj))))
    (hι_unp_X : ι_unp '' Subtype.val ⁻¹' (range a' ∪ range b') = range a ∪ range b)
    (hS₂_U : (range (GluedSpace.inr hb_inj)) ∩ H'.U ⊆ (range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr hb_inj)) ∪ ⋃ i, crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i) :
    IsRigid H' := by
  let S' : Type w := GluedSpace hb_inj
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  let L := crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt
  let X_unp : Set S' := range a' ∪ range b'
  refine theorem_3_2_proof C_unp S₁ S₂ ι_unp ![Λ] H' H X_unp
    hSplit_unp hCap_unp hS12_sub_U hX_unp_sub ?_ ?_ ?_ ?_
  · -- Condition (i): trivial since `i, j : Fin 1`.
    intro _ _ _ i j _ _
    exact Subsingleton.elim i j
  · -- Condition (ii): dials in `S` via `theorem_3_3_claim_3`.
    intro F hF hFU hFV
    rw [hι_unp_X]
    exact theorem_3_3_claim_3 hS hRigid_H hT hθ hFree_ab hF hFU hFV
  · -- Condition (iii): dials in `S₂` via `exists_striped_disc_in_S₂_crosscap` and
    -- `dial_of_oArc_in_striped_disc`.
    intro F hF_S₂ hF hFU hFV
    have hFU_eq : F ∩ H'.U = F ∩ H'.V :=
      Subset.antisymm (fun x hx => ⟨hx.1, hFU hx⟩) (inter_subset_inter_right _ H'.V_subset_U)
    have hF_fin : (F ∩ H'.U).Finite :=
      hFU_eq ▸ H'.finite_V.subset inter_subset_right
    have hF_card : (F ∩ H'.U).ncard ≤ 2 := hFU_eq ▸ hFV
    have hL_sub_U : ∀ i, L i ⊆ H'.U := fun i => by
      rw [hH'_U]; exact (subset_iUnion L i).trans subset_union_right
    obtain ⟨i₀, hF_disj_i₀⟩ :=
      exists_disjoint_of_three_le hφ hF_fin hF_card hL_disj
        (fun i => inter_subset_inter_right _ (hL_sub_U i))
    have hF_cl : IsClosed F := by
      obtain ⟨ψ⟩ := hF
      have hEq : F = range (fun z : Circle => (ψ z).1) := by
        ext x
        exact ⟨fun hx => ⟨ψ.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (ψ z).2⟩
      rw [hEq]
      exact (isCompact_range (continuous_subtype_val.comp ψ.continuous)).isClosed
    obtain ⟨D, hD_S₂, hD_disc, hF_D, hD_bd, hD_U, hD_paths⟩ :=
      exists_striped_disc_in_S₂_crosscap hS hΛ_open g hb_inj hu_inj hu_int
        ha'_inr hb'_inr (fun _ => rfl) (fun i => (hH_path i).1) hS₂_U hF_cl hF_S₂ i₀ hF_disj_i₀
    let e_sub := (Fintype.equivFin {i : Fin φ // i ≠ i₀}).symm
    have hD_U_fin : D ∩ H'.U ⊆ D ∩ (S₁ ∩ S₂) ∪ ⋃ k, (H_path (e_sub k).1).U := by
      refine hD_U.trans (union_subset_union_right _ ?_)
      intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e_sub.symm j, by simpa using hxj⟩
    obtain ⟨Δ, hΔ_D, hDial⟩ :=
      dial_of_oArc_in_striped_disc hS' hD_disc hD_bd hD_U_fin
        (fun k => (hD_paths (e_sub k)).1)
        (fun k => (hH_path (e_sub k).1).1 ▸ hL_line (e_sub k).1)
        (fun k => (hH_path (e_sub k).1).2.2.1)
        (fun k => (hD_paths (e_sub k)).2)
        (fun k₁ k₂ hk => by
          change Disjoint (H_path (e_sub k₁).1).U (H_path (e_sub k₂).1).U
          rw [(hH_path (e_sub k₁).1).1, (hH_path (e_sub k₂).1).1]
          exact hL_disj (fun h => hk (e_sub.injective (Subtype.ext h))))
        hF_D hF hFU hFV
    exact ⟨Δ, hΔ_D.trans hD_S₂, hDial⟩
  · -- Condition (iv): open disc in `S₂` via `exists_striped_disc_in_S₂_crosscap` and
    -- `openDisc_of_chord_in_striped_disc`.
    intro F u v P hF_S₂ hu hv hF_line hF_U hP_sub_inter hP_path hPX_card
    have hP_sub_H' : P.IsSubdrawing H' := by
      refine ⟨hP_sub_inter.1.trans ?_, hP_sub_inter.2.trans ?_⟩
      · rw [interSet_V_of_isClosed H' (hS₁_cl.inter hS₂_cl)]
        exact inter_subset_left
      · rw [interSet_E H' (S₁ ∩ S₂)]
        exact fun _ he => he.1
    have hPU_inter : P.U ⊆ S₁ ∩ S₂ := by
      refine (isSubdrawing_U_subset hP_sub_inter).trans ?_
      rw [(H'.interSet (S₁ ∩ S₂)).U_eq,
        interSet_V_of_isClosed H' (hS₁_cl.inter hS₂_cl), interSet_E]
      exact union_subset inter_subset_right
        (iUnion₂_subset fun e he => (hS₁_cl.inter hS₂_cl).closure_subset_iff.mpr he.2)
    have hPU_S₂ : P.U ⊆ S₂ := hPU_inter.trans inter_subset_right
    have hPX_fin : (P.V ∩ X_unp).Finite :=
      (P.finite_V).subset inter_subset_left
    have hpair_disj : Pairwise (fun i j => Disjoint ({a' i, b' i} : Set S') {a' j, b' j}) := by
      intro i j hij
      refine (hL_disj hij).mono ?_ ?_
      · rw [← hL_S₁ i]; exact inter_subset_left
      · rw [← hL_S₁ j]; exact inter_subset_left
    obtain ⟨i₀, hi₀_disj⟩ :=
      exists_disjoint_of_three_le hφ hPX_fin hPX_card hpair_disj
        (fun i => inter_subset_inter_right _ (by
          rintro _ (rfl | rfl)
          · exact .inl ⟨i, rfl⟩
          · exact .inr ⟨i, rfl⟩))
    have ha'i₀_not_PV : a' i₀ ∉ P.V := fun h =>
      Set.disjoint_left.mp hi₀_disj h (.inl rfl)
    have hb'i₀_not_PV : b' i₀ ∉ P.V := fun h =>
      Set.disjoint_left.mp hi₀_disj h (.inr rfl)
    have hPU_V : P.U ∩ H'.V = P.V := isSubdrawing_U_inter_V hP_sub_H'
    have hPU_disj_i₀ : Disjoint P.U (L i₀) := by
      refine Set.disjoint_left.mpr fun x hxP hxL => ?_
      have hx_pair : x ∈ ({a' i₀, b' i₀} : Set S') :=
        hL_S₁ i₀ ▸ ⟨hxL, (hPU_inter hxP).1⟩
      rcases hx_pair with rfl | rfl
      · exact ha'i₀_not_PV (hPU_V ▸ ⟨hxP, hSub_H₁.1 (ha'_V i₀)⟩)
      · exact hb'i₀_not_PV (hPU_V ▸ ⟨hxP, hSub_H₁.1 (hb'_V i₀)⟩)
    have ⟨ψ_F, hψ_F0, hψ_F1⟩ := hF_line
    have huv : u ≠ v := fun heq => zero_ne_one
      (ψ_F.injective (Subtype.ext (hψ_F0.trans (heq.trans hψ_F1.symm))))
    have hP_line : IsLineWithEnds P.U u v := GM14.isLine_of_isPathBetween hP_path huv
    have ⟨ψ_P, hψ_P0, hψ_P1⟩ := hP_line
    have huPU : u ∈ P.U := hψ_P0 ▸ (ψ_P 0).2
    have hvPU : v ∈ P.U := hψ_P1 ▸ (ψ_P 1).2
    have hF_disj_i₀ : Disjoint F (L i₀) := by
      refine Set.disjoint_left.mpr fun x hxF hxL => ?_
      have hxU : x ∈ H'.U := by
        rw [hH'_U]; exact .inr (mem_iUnion.mpr ⟨i₀, hxL⟩)
      rcases hF_U ⟨hxF, hxU⟩ with rfl | rfl
      · exact Set.disjoint_left.mp hPU_disj_i₀ huPU hxL
      · exact Set.disjoint_left.mp hPU_disj_i₀ hvPU hxL
    have hF_cl_line : IsClosed F := by
      have hEq : F = range (fun s : unitInterval => (ψ_F s).1) := by
        ext x
        exact ⟨fun hx => ⟨ψ_F.symm ⟨x, hx⟩, by simp⟩, fun ⟨s, hs⟩ => hs ▸ (ψ_F s).2⟩
      rw [hEq]
      exact (isCompact_range (continuous_subtype_val.comp ψ_F.continuous)).isClosed
    have hK_sub_cl : IsClosed (P.U ∪ F) := P.isClosed_U.union hF_cl_line
    obtain ⟨D, hD_S₂, hD_disc, hPF_D, hD_bd, hD_U, hD_paths⟩ :=
      exists_striped_disc_in_S₂_crosscap hS hΛ_open g hb_inj hu_inj hu_int
        ha'_inr hb'_inr (fun _ => rfl) (fun i => (hH_path i).1) hS₂_U hK_sub_cl
        (union_subset hPU_S₂ hF_S₂) i₀ (hPU_disj_i₀.union_left hF_disj_i₀)
    have hPU_D : P.U ⊆ D := subset_union_left.trans hPF_D
    have hF_D : F ⊆ D := subset_union_right.trans hPF_D
    have hPU_bd : P.U ⊆ discBd D := (subset_inter hPU_D hPU_inter).trans hD_bd
    let e_sub := (Fintype.equivFin {i : Fin φ // i ≠ i₀}).symm
    have hD_U_fin : D ∩ H'.U ⊆ discBd D ∪ ⋃ k, (H_path (e_sub k).1).U := by
      refine hD_U.trans (union_subset (hD_bd.trans subset_union_left) ?_)
      intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨e_sub.symm j, by simpa using hxj⟩)
    have hNo_both : ∀ k, ¬ (a' (e_sub k).1 ∈ P.V ∧ b' (e_sub k).1 ∈ P.V) := by
      rintro k ⟨ha_j, hb_j⟩
      let j := e_sub k
      let bd_emb : Circle → S' := fun z => GluedSpace.inr hb_inj (mobBd z)
      have hbd_emb : IsEmbedding bd_emb := hinr_emb.isEmbedding.comp isEmbedding_mobBd
      have hbd_range : range bd_emb = C_unp 0 := by
        rw [hC_unp_0]
        ext x
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨mobBd z, by rw [bd_mobiusBand]; exact ⟨z, rfl⟩, rfl⟩
        · rintro ⟨y, hy_bd, rfl⟩
          rw [bd_mobiusBand] at hy_bd
          obtain ⟨z, rfl⟩ := hy_bd
          exact ⟨z, rfl⟩
      let e_C0 : Circle ≃ₜ ↥(C_unp 0) :=
        hbd_emb.toHomeomorph.trans (Homeomorph.setCongr hbd_range)
      have he_C0_coe : ∀ z : Circle, (e_C0 z).1 = GluedSpace.inr hb_inj (mobBd z) :=
        fun _ => rfl
      have hPU_C0 : P.U ⊆ C_unp 0 := hS12_inter ▸ hPU_inter
      let A_circ : Set Circle := bd_emb ⁻¹' P.U
      have hA_eq : A_circ = range (fun s : unitInterval => e_C0.symm ⟨(ψ_P s).1, hPU_C0 (ψ_P s).2⟩)
        := by
        ext z
        constructor
        · intro hz
          have hz_PU : (e_C0 z).1 ∈ P.U := hz
          refine ⟨ψ_P.symm ⟨(e_C0 z).1, hz_PU⟩, ?_⟩
          apply e_C0.injective
          rw [e_C0.apply_symm_apply]
          apply Subtype.ext
          change (ψ_P (ψ_P.symm ⟨(e_C0 z).1, hz_PU⟩)).1 = (e_C0 z).1
          exact congrArg Subtype.val (ψ_P.apply_symm_apply ⟨(e_C0 z).1, hz_PU⟩)
        · rintro ⟨s, rfl⟩
          change (e_C0 (e_C0.symm ⟨(ψ_P s).1, hPU_C0 (ψ_P s).2⟩)).1 ∈ P.U
          rw [e_C0.apply_symm_apply]
          exact (ψ_P s).2
      have hA_conn : IsPreconnected A_circ := by
        rw [hA_eq]
        refine isPreconnected_range (e_C0.symm.continuous.comp ?_)
        exact Continuous.subtype_mk (continuous_subtype_val.comp ψ_P.continuous) _
      have hwa_i₀_not : w_a i₀ ∉ A_circ := by
        intro h
        have ha_PU : a' i₀ ∈ P.U := ha'_mobBd i₀ ▸ h
        exact ha'i₀_not_PV (hPU_V ▸ ⟨ha_PU, hSub_H₁.1 (ha'_V i₀)⟩)
      have hneg_wa_i₀_not : - w_a i₀ ∉ A_circ := by
        rw [← hwb_eq_neg i₀]
        intro h
        have hb_PU : b' i₀ ∈ P.U := hb'_mobBd i₀ ▸ h
        exact hb'i₀_not_PV (hPU_V ▸ ⟨hb_PU, hSub_H₁.1 (hb'_V i₀)⟩)
      have hwa_j_mem : w_a j.1 ∈ A_circ := by
        change GluedSpace.inr hb_inj (mobBd (w_a j.1)) ∈ P.U
        rw [← ha'_mobBd j.1]
        exact P.V_subset_U ha_j
      have hneg_wa_j_mem : - w_a j.1 ∈ A_circ := by
        rw [← hwb_eq_neg j.1]
        change GluedSpace.inr hb_inj (mobBd (w_b j.1)) ∈ P.U
        rw [← hb'_mobBd j.1]
        exact P.V_subset_U hb_j
      exact not_mem_and_neg_mem_of_isPreconnected_circle hA_conn hwa_i₀_not hneg_wa_i₀_not
        (w_a j.1) ⟨hwa_j_mem, hneg_wa_j_mem⟩
    obtain ⟨U₀, hU₀_open, hU₀_cl, hU₀_D, hU₀_bd, hU₀_disj⟩ :=
      openDisc_of_chord_in_striped_disc hS' hD_disc (Subset.refl _) hD_U_fin
        (fun k => (hH_path (e_sub k).1).1 ▸ hL_line (e_sub k).1)
        (fun k => (hH_path (e_sub k).1).2.2.1)
        (fun k => ⟨(hH_path (e_sub k).1).2.2.2.1, (hH_path (e_sub k).1).2.2.2.2⟩)
        (fun k => (hD_paths (e_sub k)).2)
        hPU_D hF_D hPU_bd hF_line hF_U hP_sub_H' hP_path hNo_both
    exact ⟨U₀, hU₀_open, hU₀_cl, hU₀_D.trans hD_S₂, hU₀_bd, hU₀_disj⟩

private theorem crosscap_lines_meet_base_at_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ : Set S)
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (u_pt : Fin φ → unitInterval)
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    ∀ (H₁ : Drawing S'),
    (H₁.U ⊆ S₁) →
    ∀ (a' : Fin φ → S'),
    ∀ (b' : Fin φ → S'),
    let L : Fin φ → Set S' := fun i => GluedSpace.inr hb_inj '' Quotient.mk Surface.mobiusSetoid
      '' {u_pt i} ×ˢ univ
    (∀ (i : Fin φ), a' i ∈ H₁.V) →
    (∀ (i : Fin φ), b' i ∈ H₁.V) →
    (∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj ⟦(u_pt i, 0)⟧) →
    (∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj ⟦(u_pt i, 1)⟧) →
    ∀ (i : Fin φ), L i ∩ S₁ = {a' i, b' i} := by
  intro S' S₁ H₁ hH₁_sub_S₁ a' b' L ha'_V hb'_V ha'_inr hb'_inr i
  ext x
  constructor
  · rintro ⟨⟨_, ⟨⟨u', v⟩, ⟨hu', _⟩, rfl⟩, rfl⟩, ⟨y, hy_eq⟩⟩
    have hu_eq : u_pt i = u' := hu'.symm
    subst hu_eq
    obtain ⟨hy_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hy_eq
    rcases eq_or_lt_of_le v.2.1 with hv0 | hv0
    · left
      have hv0' : v = 0 := Subtype.ext hv0.symm
      subst hv0'
      exact (ha'_inr i).symm
    · rcases eq_or_lt_of_le v.2.2 with hv1 | hv1
      · right
        have hv1' : v = 1 := Subtype.ext hv1
        subst hv1'
        exact (hb'_inr i).symm
      · exact (hy_bd (mobius_interior hv0 hv1)).elim
  · rintro (rfl | rfl)
    · exact ⟨by rw [ha'_inr i]; exact ⟨_, ⟨(u_pt i, 0), ⟨rfl, mem_univ _⟩, rfl⟩, rfl⟩,
        hH₁_sub_S₁ (H₁.V_subset_U (ha'_V i))⟩
    · exact ⟨by rw [hb'_inr i]; exact ⟨_, ⟨(u_pt i, 1), ⟨rfl, mem_univ _⟩, rfl⟩, rfl⟩,
        hH₁_sub_S₁ (H₁.V_subset_U (hb'_V i))⟩

private theorem crosscap_lines_meet_lifted_drawing_at_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ : Set S)
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    ∀ (H₁ : Drawing S'),
    (H₁.U ⊆ S₁) →
    ∀ (a' : Fin φ → S'),
    ∀ (b' : Fin φ → S'),
    ∀ (L : Fin φ → Set S'),
    (∀ (i : Fin φ), a' i ∈ H₁.V) →
    (∀ (i : Fin φ), b' i ∈ H₁.V) →
    (∀ (i : Fin φ), L i ∩ S₁ = {a' i, b' i}) →
    ∀ (i : Fin φ), L i ∩ H₁.U = {a' i, b' i} := by
  intro S' S₁ H₁ hH₁_sub_S₁ a' b' L ha'_V hb'_V hL_S₁ i
  refine Subset.antisymm ?_ ?_
  · exact (inter_subset_inter_right _ hH₁_sub_S₁).trans (hL_S₁ i).subset
  · rintro x (rfl | rfl)
    · have hmem : a' i ∈ L i ∩ S₁ := by rw [hL_S₁ i]; exact Or.inl rfl
      exact ⟨hmem.1, H₁.V_subset_U (ha'_V i)⟩
    · have hmem : b' i ∈ L i ∩ S₁ := by rw [hL_S₁ i]; exact Or.inr rfl
      exact ⟨hmem.1, H₁.V_subset_U (hb'_V i)⟩

private theorem crosscap_inclusion_maps_marked_nodes
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ : Set S)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hΛ_open : IsOpen Λ) :
    let K : Set S := univ \ Λ
    ∀ (g : Circle ≃ₜ ↑(subBd Λ)),
    ∀ (hb_inj : Injective (crosscapGlueMap hΛ_open g)),
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let S₂ : Set S' := range (GluedSpace.inr hb_inj)
    ∀ (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S),
    ∀ (g_unp : S → S'),
    let a' : Fin φ → S' := fun i => g_unp (a i)
    let b' : Fin φ → S' := fun i => g_unp (b i)
    (∀ (i : Fin φ), a i ∈ K) →
    (∀ (i : Fin φ), b i ∈ K) →
    ∀ (H' : Drawing S'),
    (∀ y ∈ K, ∀ (hy : g_unp y ∈ S₁), ι_unp ⟨g_unp y, hy⟩ = y) →
    let X_unp : Set S' := range a' ∪ range b'
    (X_unp ⊆ H'.V ∩ (S₁ ∩ S₂)) →
    ι_unp '' Subtype.val ⁻¹' X_unp = range a ∪ range b := by
  intro K g hb_inj S' S₁ S₂ ι_unp g_unp a' b' ha_K hb_K H' hι_unp_g X_unp hX_unp_sub
  ext y
  constructor
  · rintro ⟨⟨x, hxS₁⟩, ⟨i, rfl⟩ | ⟨i, rfl⟩, rfl⟩
    · rw [hι_unp_g (a i) (ha_K i) hxS₁]; exact .inl ⟨i, rfl⟩
    · rw [hι_unp_g (b i) (hb_K i) hxS₁]; exact .inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · have hxS₁ : a' i ∈ S₁ := (hX_unp_sub (.inl ⟨i, rfl⟩)).2.1
      exact ⟨⟨a' i, hxS₁⟩, .inl ⟨i, rfl⟩, hι_unp_g (a i) (ha_K i) hxS₁⟩
    · have hxS₁ : b' i ∈ S₁ := (hX_unp_sub (.inr ⟨i, rfl⟩)).2.1
      exact ⟨⟨b' i, hxS₁⟩, .inr ⟨i, rfl⟩, hι_unp_g (b i) (hb_K i) hxS₁⟩

private theorem crosscap_unmarked_collar_avoids_drawing
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ : Set S)
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (w_a : Fin φ → Circle)
    (w_b : Fin φ → Circle)
    (u_pt : Fin φ → unitInterval)
    (htop_upt : ∀ (i : Fin φ), circleTop (u_pt i) = w_a i)
    (hbot_upt : ∀ (i : Fin φ), circleBot (u_pt i) = w_b i)
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    ∀ (H₁ : Drawing S'),
    (H₁.U ⊆ S₁) →
    let L : Fin φ → Set S' := fun i => GluedSpace.inr hb_inj '' Quotient.mk Surface.mobiusSetoid
      '' {u_pt i} ×ˢ univ
    ∀ (H' : Drawing S'),
    (H'.U = H₁.U ∪ ⋃ i, L i) →
    let W_pts : Set Circle := range w_a ∪ range w_b
    let CollarInt : Set S' := GluedSpace.inr hb_inj '' {y | y ∉ bd MobiusBand ∧ (collarCoords y).1
      ≤ 1 / 4 ∧ (collarCoords y).2 ∉ W_pts}
    Disjoint CollarInt H'.U := by
  intro S' S₁ H₁ hH₁_sub_S₁ L H' hH'_U W_pts CollarInt
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨y, ⟨hy_not_bd, hy_le, hyW⟩, rfl⟩ hxU
  rw [hH'_U] at hxU
  rcases hxU with hx1 | hxL
  · obtain ⟨w, hw_eq⟩ := hH₁_sub_S₁ hx1
    obtain ⟨hy_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hw_eq
    exact hy_not_bd hy_bd
  · obtain ⟨i, ⟨_, ⟨⟨u', v⟩, ⟨hu', _⟩, rfl⟩, heq⟩⟩ := mem_iUnion.mp hxL
    have hu_eq : u_pt i = u' := hu'.symm
    subst hu_eq
    have hy_eq := GluedSpace.inr_injective hb_inj heq
    subst hy_eq
    change (collarCoordsAux (u_pt i, v)).1 ≤ 1 / 4 at hy_le
    change (collarCoordsAux (u_pt i, v)).2 ∉ W_pts at hyW
    dsimp [collarCoordsAux] at hy_le hyW
    split_ifs at hy_le hyW with h1 h2
    · exact hyW (htop_upt i ▸ Or.inl ⟨i, rfl⟩)
    · exact hyW (hbot_upt i ▸ Or.inr ⟨i, rfl⟩)
    · linarith

private theorem pinched_crosscap_cuff_is_normal
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ : Set S)
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) :
    let S' : Type w := GluedSpace hb_inj
    ∀ (H₁ : Drawing S'),
    ∀ (a' : Fin φ → S'),
    ∀ (b' : Fin φ → S'),
    ∀ (L : Fin φ → Set S'),
    (∀ (i : Fin φ), a' i ∈ H₁.V) →
    (∀ (i : Fin φ), b' i ∈ H₁.V) →
    ∀ (H_path : Fin φ → Drawing S'),
    ∀ (H' : Drawing S'),
    (H'.U = H₁.U ∪ ⋃ i, L i) →
    (H'.V = H₁.V ∪ ⋃ i, (H_path i).V) →
    ∀ (W_pts : Set Circle),
    let CollarInt : Set S' := GluedSpace.inr hb_inj ''
      {y | y ∉ bd MobiusBand ∧ (collarCoords y).1 ≤ 1 / 4 ∧ (collarCoords y).2 ∉ W_pts}
    ∀ (C_XII : Fin 1 → Set (GluedSpace hb_inj)),
    (GluedSpace.inr hb_inj '' mobBd '' W_pts ⊆ C_XII 0) →
    (C_XII 0 \ GluedSpace.inr hb_inj '' mobBd '' W_pts ⊆ GluedSpace.inr hb_inj ''
      {y | y ∉ bd MobiusBand ∧ (collarCoords y).1 ≤ 1 / 4 ∧ (collarCoords y).2 ∉ W_pts}) →
    (Disjoint CollarInt H'.U) →
    (GluedSpace.inr hb_inj '' mobBd '' W_pts = range a' ∪ range b') →
    H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a' ∪ range b' := by
  intro S' H₁ a' b' L ha'_V hb'_V H_path H' hH'_U hH'_V W_pts CollarInt C_XII hW_sub_C0 hC0_diff_W
    hCollar_disj hW_eq_ab'
  refine glued_isNormal_and_V_inter ?_ ?_ ?_ hH'_U hH'_V
  · rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ha'_V i
    · exact hb'_V i
  · refine Subset.antisymm ?_ ?_
    · intro x ⟨hx1, hxC0⟩
      by_contra hnot
      exact Set.disjoint_left.mp hCollar_disj
        (hC0_diff_W ⟨hxC0, hW_eq_ab'.symm ▸ hnot⟩) (by rw [hH'_U]; exact .inl hx1)
    · rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨H₁.V_subset_U (ha'_V i), hW_sub_C0 (hW_eq_ab'.symm ▸ .inl ⟨i, rfl⟩)⟩
      · exact ⟨H₁.V_subset_U (hb'_V i), hW_sub_C0 (hW_eq_ab'.symm ▸ .inr ⟨i, rfl⟩)⟩
  · intro x ⟨hxL, hxC0⟩
    by_contra hnot
    exact Set.disjoint_left.mp hCollar_disj
      (hC0_diff_W ⟨hxC0, hW_eq_ab'.symm ▸ hnot⟩) (by rw [hH'_U]; exact .inr hxL)

private theorem pinched_crosscap_preserves_boundary_order
    {S : Type w} [TopologicalSpace S] {φ : ℕ} (hφ : 3 ≤ φ) {Λ : Set S}
    (hΛ_open : IsOpen Λ) (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) :
    let t_model := crosscapModelAngle φ
    let w_a : Fin φ → Circle := fun i => Circle.exp (t_model i.1)
    let w_b : Fin φ → Circle := fun i => Circle.exp (t_model (φ + i.1))
    ∀ (a' b' : Fin φ → GluedSpace hb_inj),
    (∀ i, a' i = GluedSpace.inr hb_inj (mobBd (w_a i))) →
    (∀ i, b' i = GluedSpace.inr hb_inj (mobBd (w_b i))) →
    ∀ (C_XII : Fin 1 → Set (GluedSpace hb_inj)) (f_C0 : Circle ≃ₜ ↑(C_XII 0)),
    (∀ z ∈ range w_a ∪ range w_b, ↑(f_C0 z) = GluedSpace.inr hb_inj (mobBd z)) →
    IsListedInOrderOn (C_XII 0) (List.ofFn a' ++ List.ofFn b') := by
  intro t_model w_a w_b a' b' ha'_mobBd hb'_mobBd C_XII f_C0 hf_C0_W
  have ht_model_mono := strictMono_crosscapModelAngle hφ
  have ht_model_bd := crosscapModelAngle_lt_add_two_pi hφ
  refine ⟨f_C0, t_model, ht_model_mono,
    fun k hk => ht_model_bd k (by simp at hk; omega), fun k hk => ?_⟩
  by_cases hkφ : k < φ
  · rw [List.getElem_append_left (by simp [hkφ])]
    simp only [List.getElem_ofFn]
    rw [ha'_mobBd ⟨k, hkφ⟩]
    exact hf_C0_W (w_a ⟨k, hkφ⟩) (.inl ⟨⟨k, hkφ⟩, rfl⟩)
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem_ofFn]
    let j : Fin φ := ⟨k - φ, by simp at hk; omega⟩
    have hk_eq : k = φ + j.1 := by dsimp [j]; omega
    change (f_C0 (Circle.exp (t_model k))).1 = b' j
    rw [hk_eq, hb'_mobBd j]
    exact hf_C0_W (w_b j) (.inr ⟨j, rfl⟩)

private theorem base_drawing_meets_pinched_crosscap_at_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ : Set S)
    (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hb_inj : Injective (crosscapGlueMap hΛ_open g)) :
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    ∀ (H₁ : Drawing S'),
    (H₁.U ⊆ S₁) →
    ∀ (a' : Fin φ → S'),
    ∀ (b' : Fin φ → S'),
    ∀ (L : Fin φ → Set S'),
    ∀ (H' : Drawing S'),
    (H'.U = H₁.U ∪ ⋃ i, L i) →
    ∀ (C_XII : Fin 1 → Set (GluedSpace hb_inj)),
    ∀ (P₁_XII : Set (GluedSpace hb_inj)),
    ∀ (P₂_XII : Set (GluedSpace hb_inj)),
    ∀ (ι_XII : ↑P₁_XII → S),
    ∀ (D_XII : Fin 1 → Set S),
    (IsCrosscapSplit C_XII P₁_XII P₂_XII ι_XII D_XII) →
    (range (GluedSpace.inl hb_inj) ⊆ P₁_XII) →
    (H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a' ∪ range b') →
    H₁.U ∩ P₂_XII ⊆ ⋃ i, {a' i, b' i} := by
  intro S' S₁ H₁ hH₁_sub_S₁ a' b' L H' hH'_U C_XII P₁_XII P₂_XII ι_XII D_XII hSplit_XII hS₁_sub_P₁
    hNorm_C0_and_V
    x ⟨hx1, hx2⟩
  have hx_inter : x ∈ P₁_XII ∩ P₂_XII := ⟨hS₁_sub_P₁ (hH₁_sub_S₁ hx1), hx2⟩
  rw [hSplit_XII.1.inter] at hx_inter
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx_inter
  fin_cases j
  have hx_ab' : x ∈ range a' ∪ range b' := by
    have h : x ∈ H'.V ∩ C_XII 0 := ⟨hNorm_C0_and_V.1 ⟨hxj, by rw [hH'_U]; exact .inl hx1⟩, hxj⟩
    rwa [hNorm_C0_and_V.2] at h
  rcases hx_ab' with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact mem_iUnion.mpr ⟨i, .inl rfl⟩
  · exact mem_iUnion.mpr ⟨i, .inr rfl⟩

private theorem pinched_crosscap_cuff_vertices_map_to_original_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ : Set S)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hΛ_open : IsOpen Λ) :
    let K : Set S := univ \ Λ
    ∀ (g : Circle ≃ₜ ↑(subBd Λ)),
    ∀ (hb_inj : Injective (crosscapGlueMap hΛ_open g)),
    let S' : Type w := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    ∀ (g_unp : S → S'),
    ∀ (H₁ : Drawing S'),
    (H₁.U ⊆ S₁) →
    let a' : Fin φ → S' := fun i => g_unp (a i)
    let b' : Fin φ → S' := fun i => g_unp (b i)
    (∀ (i : Fin φ), a i ∈ K) →
    (∀ (i : Fin φ), b i ∈ K) →
    (∀ (i : Fin φ), a' i ∈ H₁.V) →
    (∀ (i : Fin φ), b' i ∈ H₁.V) →
    ∀ (H' : Drawing S'),
    ∀ (C_XII : Fin 1 → Set (GluedSpace hb_inj)),
    ∀ (P₁_XII : Set (GluedSpace hb_inj)),
    ∀ (ι_XII : ↑P₁_XII → S),
    (range (GluedSpace.inl hb_inj) ⊆ P₁_XII) →
    (∀ y ∈ K, ∀ (hy : g_unp y ∈ P₁_XII), ι_XII ⟨g_unp y, hy⟩ = y) →
    (H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a' ∪ range b') →
    ι_XII '' Subtype.val ⁻¹' (H'.V ∩ C_XII 0) = range a ∪ range b := by
  intro K g hb_inj S' S₁ g_unp H₁ hH₁_sub_S₁ a' b' ha_K hb_K ha'_V hb'_V H' C_XII P₁_XII ι_XII
    hS₁_sub_P₁ hι_XII_g hNorm_C0_and_V
  rw [hNorm_C0_and_V.2]
  ext y
  constructor
  · rintro ⟨⟨x, hxP₁⟩, ⟨i, rfl⟩ | ⟨i, rfl⟩, rfl⟩
    · rw [hι_XII_g (a i) (ha_K i) hxP₁]; exact .inl ⟨i, rfl⟩
    · rw [hι_XII_g (b i) (hb_K i) hxP₁]; exact .inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · have hxP₁ : a' i ∈ P₁_XII := hS₁_sub_P₁ (hH₁_sub_S₁ (H₁.V_subset_U (ha'_V i)))
      exact ⟨⟨a' i, hxP₁⟩, .inl ⟨i, rfl⟩, hι_XII_g (a i) (ha_K i) hxP₁⟩
    · have hxP₁ : b' i ∈ P₁_XII := hS₁_sub_P₁ (hH₁_sub_S₁ (H₁.V_subset_U (hb'_V i)))
      exact ⟨⟨b' i, hxP₁⟩, .inr ⟨i, rfl⟩, hι_XII_g (b i) (hb_K i) hxP₁⟩

private theorem crosscap_embedding_agrees_on_original_edges
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (Λ : Set S)
    (hΛ_open : IsOpen Λ) :
    let K : Set S := univ \ Λ
    ∀ (hK_comp : IsCompact K),
    ∀ (hHU : H.U ⊆ K),
    ∀ (g : Circle ≃ₜ ↑(subBd Λ)),
    ∀ (hb_inj : Injective (crosscapGlueMap hΛ_open g)),
    let S' : Type w := GluedSpace hb_inj
    ∀ [T2Space S'],
    ∀ (g_unp : S → S'),
    ∀ (f_unp : S' → S),
    ∀ (hg_unp_cont : ContinuousOn g_unp K),
    ∀ (hfg_unp_inv : LeftInvOn f_unp g_unp K),
    ∀ (hf_unp_cont' : ContinuousOn f_unp (g_unp '' K)),
    let H₁ : Drawing S' := liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
    let η₁ : SpanEmbedding H₁ G := liftSpanEmbeddingOn hK_comp hg_unp_cont hf_unp_cont'
      hfg_unp_inv hHU η
    ∀ (H' : Drawing S'),
    ∀ (η' : SpanEmbedding H' G),
    (∀ e ∈ H₁.E, η'.eMap e = η₁.eMap e) →
    ∀ e ∈ H.E, η'.eMap (g_unp '' e) = η.eMap e := by
  intro K hK_comp hHU g hb_inj S' _ g_unp f_unp hg_unp_cont hfg_unp_inv hf_unp_cont' H₁ η₁ H' η'
    hem_H₁
    e he
  have he₁ : g_unp '' e ∈ H₁.E := by
    rw [liftDrawingOn_E hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU]
    exact ⟨e, he, rfl⟩
  rw [hem_H₁ (g_unp '' e) he₁]
  change η.eMap (f_unp '' (g_unp '' e)) = η.eMap e
  have he_sub : e ⊆ K := fun x hx => hHU (he.2.1 hx).1
  rw [hfg_unp_inv.image_image' he_sub]

private theorem realize_marked_crosscap_boundary
    {S : Type w} [TopologicalSpace S] {Λ : Set S}
    {φ : ℕ} (hφ : 3 ≤ φ) (a b : Fin φ → S)
    (hOrder : GM12.IsListedInOrderOn (subBd Λ) (List.ofFn a ++ List.ofFn b)) :
    ∃ g : Circle ≃ₜ ↥(subBd Λ),
      (∀ i : Fin φ, (g (Circle.exp (crosscapModelAngle φ i.1))).1 = a i) ∧
      (∀ i : Fin φ, (g (Circle.exp (crosscapModelAngle φ (φ + i.1)))).1 = b i) := by
  obtain ⟨f₀, t₀, ht₀_mono, ht₀_bd, ht₀_val⟩ := hOrder
  have hlen_ab : (List.ofFn a ++ List.ofFn b).length = 2 * φ := by simp [two_mul]
  have ht₀_bd' : ∀ k < 2 * φ, t₀ k < t₀ 0 + 2 * Real.pi :=
    fun k hk => ht₀_bd k (hlen_ab ▸ hk)
  let t_model := crosscapModelAngle φ
  have ht_model_mono := strictMono_crosscapModelAngle hφ
  have ht_model_bd := crosscapModelAngle_lt_add_two_pi hφ
  obtain ⟨h_circ, hh_circ⟩ :=
    exists_circle_homeo_matching_angles (2 * φ) (by omega) t₀ t_model
      ht₀_mono ht_model_mono ht₀_bd' ht_model_bd
  let g : Circle ≃ₜ ↥(subBd Λ) := h_circ.symm.trans f₀
  let w_a : Fin φ → Circle := fun i => Circle.exp (t_model i.1)
  let w_b : Fin φ → Circle := fun i => Circle.exp (t_model (φ + i.1))
  have hg_wa : ∀ i : Fin φ, (g (w_a i)).1 = a i := by
    intro i
    have h1 : h_circ.symm (w_a i) = Circle.exp (t₀ i.1) :=
      h_circ.symm_apply_eq.mpr (hh_circ i.1 (by omega)).symm
    change (f₀ (h_circ.symm (w_a i))).1 = a i
    rw [h1, ht₀_val i.1 (by simp; omega)]
    rw [List.getElem_append_left (by simp)]
    simp only [List.getElem_ofFn]
  have hg_wb : ∀ i : Fin φ, (g (w_b i)).1 = b i := by
    intro i
    have h1 : h_circ.symm (w_b i) = Circle.exp (t₀ (φ + i.1)) :=
      h_circ.symm_apply_eq.mpr (hh_circ (φ + i.1) (by omega)).symm
    change (f₀ (h_circ.symm (w_b i))).1 = b i
    rw [h1, ht₀_val (φ + i.1) (by simp)]
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn]
  exact ⟨g, hg_wa, hg_wb⟩

private theorem crosscap_base_inclusion_and_retraction
    {S : Type w} [TopologicalSpace S] {Λ : Set S} (hΛ_open : IsOpen Λ)
    (g : Circle ≃ₜ ↥(subBd Λ)) (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    (anchor : S) (hanchor : anchor ∈ univ \ Λ)
    (ι_unp : ↥(range (GluedSpace.inl hb_inj)) → S) (hι_cont : Continuous ι_unp)
    (hι_unp_inl : ∀ y : ↥(univ \ Λ : Set S),
      ι_unp ⟨GluedSpace.inl hb_inj y, ⟨y, rfl⟩⟩ = y.1) :
    let K : Set S := univ \ Λ
    let S' := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    ∃ (g_unp : S → S') (f_unp : S' → S),
      (∀ y (hy : y ∈ K), g_unp y = GluedSpace.inl hb_inj ⟨y, hy⟩) ∧
      (∀ y : ↥K, f_unp (GluedSpace.inl hb_inj y) = y.1) ∧
      ContinuousOn g_unp K ∧ Set.LeftInvOn f_unp g_unp K ∧
      g_unp '' K = S₁ ∧ ContinuousOn f_unp (g_unp '' K) := by
  intro K S' S₁
  let g_unp : S → S' := by
    classical
    exact fun y => if hy : y ∈ K then GluedSpace.inl hb_inj ⟨y, hy⟩ else
      GluedSpace.inl hb_inj ⟨anchor, hanchor⟩
  let f_unp : S' → S := by
    classical
    exact fun x => if hx : x ∈ S₁ then ι_unp ⟨x, hx⟩ else anchor
  have hg_unp_mem : ∀ y (hy : y ∈ K), g_unp y = GluedSpace.inl hb_inj ⟨y, hy⟩ := by
    intro y hy
    simp only [g_unp, hy, ↓reduceDIte]
  have hf_unp_inl : ∀ y : ↥K, f_unp (GluedSpace.inl hb_inj y) = y.1 := by
    intro y
    have hx : GluedSpace.inl hb_inj y ∈ S₁ := ⟨y, rfl⟩
    simp only [f_unp, hx, ↓reduceDIte]
    exact hι_unp_inl y
  have hg_unp_cont : ContinuousOn g_unp K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : K.domRestrict g_unp = GluedSpace.inl hb_inj := by
      ext ⟨y, hy⟩; exact hg_unp_mem y hy
    rw [hEq]
    exact GluedSpace.continuous_inl hb_inj
  have hf_unp_cont : ContinuousOn f_unp S₁ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : S₁.domRestrict f_unp = ι_unp := by
      ext ⟨x, hx⟩
      change f_unp x = ι_unp ⟨x, hx⟩
      simp only [f_unp, hx, ↓reduceDIte]
    rw [hEq]
    exact hι_cont
  have hfg_unp_inv : Set.LeftInvOn f_unp g_unp K := by
    intro y hy
    rw [hg_unp_mem y hy, hf_unp_inl ⟨y, hy⟩]
  have hg_unp_K : g_unp '' K = S₁ := by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; rw [hg_unp_mem y hy]; exact ⟨⟨y, hy⟩, rfl⟩,
      by rintro ⟨⟨y, hy⟩, rfl⟩; exact ⟨y, hy, hg_unp_mem y hy⟩⟩
  have hf_unp_cont' : ContinuousOn f_unp (g_unp '' K) := hg_unp_K.symm ▸ hf_unp_cont
  exact ⟨g_unp, f_unp, hg_unp_mem, hf_unp_inl, hg_unp_cont, hfg_unp_inv, hg_unp_K, hf_unp_cont'⟩

private theorem assemble_rigid_span_on_added_crosscap
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (φ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Λ : Set S)
    (P : Fin φ → Graph α β)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T)
    (hOArc : IsOArc (subBd Λ))
    (hφ : 3 ≤ φ)
    (hφ_le : φ ≤ θ)
    (hP_disj : Pairwise fun i j => Disjoint V(P i) V(P j))
    (hFree_ab : IsFreeSet H.toHypergraph T θ (range a ∪ range b))
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    (hRigid_H : IsRigid H)
    (hResp_H : IsRespectfulDrawingTangle H θ T)
    (hT : IsTangle H.toHypergraph θ T)
    (hθ : 3 ≤ θ)
    (hΛ_open : IsOpen Λ)
    (hΛ_disc : IsOpenDisc Λ)
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    (hCD : IsClosedDisc (closure Λ))
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hSubBd_sub_U : subBd Λ ⊆ H.U)
    (hK_comp : IsCompact (univ \ Λ))
    (hHU : H.U ⊆ (univ \ Λ))
    (g : Circle ≃ₜ ↑(subBd Λ))
    (hwb_eq_neg : ∀ (i : Fin φ), (fun i : Fin φ => Circle.exp (crosscapModelAngle φ (φ + i.1))) i
      = -(fun i : Fin φ => Circle.exp (crosscapModelAngle φ i.1)) i)
    (ha_inj : Injective a)
    (hb_inj_fn : Injective b)
    (hab_ne : ∀ (i j : Fin φ), a i ≠ b j)
    (u_pt : Fin φ → unitInterval)
    (hu_int : ∀ (i : Fin φ), 0 < ↑(u_pt i) ∧ ↑(u_pt i) < 1)
    (htop_upt : ∀ (i : Fin φ), circleTop (u_pt i) = (fun i : Fin φ => Circle.exp
      (crosscapModelAngle φ i.1)) i)
    (hbot_upt : ∀ (i : Fin φ), circleBot (u_pt i) = (fun i : Fin φ => Circle.exp
      (crosscapModelAngle φ (φ + i.1))) i)
    (hu_inj : Injective u_pt)
    (hb_inj : Injective (crosscapGlueMap hΛ_open g))
    [this : T2Space (GluedSpace hb_inj)]
    (hS' : IsClosedSurface (GluedSpace hb_inj))
    [hConn' : ConnectedSpace (GluedSpace hb_inj)]
    (hCrosscap : IsObtainedByAddingCrosscap S (GluedSpace hb_inj))
    (hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj))
    (hS₁_cl : IsClosed (range (GluedSpace.inl hb_inj)))
    (hS₂_cl : IsClosed (range (GluedSpace.inr hb_inj)))
    (C_unp : Fin 1 → Set (GluedSpace hb_inj))
    (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S)
    (hSplit_unp : IsCappedSplit C_unp (range (GluedSpace.inl hb_inj)) (range (GluedSpace.inr
      hb_inj)) ι_unp ![Λ])
    (hC_unp_0 : C_unp 0 = GluedSpace.inr hb_inj '' bd MobiusBand)
    (hι_unp_inl : ∀ (y : ↑(univ \ Λ)), ι_unp ⟨GluedSpace.inl hb_inj y, ⟨y, rfl⟩⟩ = ↑y)
    (hS12_inter : (range (GluedSpace.inl hb_inj)) ∩ (range (GluedSpace.inr hb_inj)) = C_unp 0)
    (g_unp : S → (GluedSpace hb_inj))
    (f_unp : (GluedSpace hb_inj) → S)
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ Λ)), g_unp y = GluedSpace.inl hb_inj ⟨y, hy⟩)
    (hg_unp_cont : ContinuousOn g_unp (univ \ Λ))
    (hfg_unp_inv : LeftInvOn f_unp g_unp (univ \ Λ))
    (hf_unp_cont' : ContinuousOn f_unp (g_unp '' (univ \ Λ)))
    (hH₁_U : (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).U = g_unp '' H.U)
    (hH₁_V : (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).V = g_unp '' H.V)
    (hH₁_sub_S₁ : (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).U ⊆ (range
      (GluedSpace.inl hb_inj)))
    (ha_K : ∀ (i : Fin φ), a i ∈ (univ \ Λ))
    (hb_K : ∀ (i : Fin φ), b i ∈ (univ \ Λ))
    (ha'_V : ∀ i : Fin φ, g_unp (a i) ∈ (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont'
      hfg_unp_inv H hHU).V)
    (hb'_V : ∀ i : Fin φ, g_unp (b i) ∈ (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont'
      hfg_unp_inv H hHU).V)
    (hinr_mobBd : ∀ z : Circle, GluedSpace.inr hb_inj (mobBd z) = g_unp (g z).1)
    (ha'_mobBd : ∀ i : Fin φ, g_unp (a i) =
      GluedSpace.inr hb_inj (mobBd (Circle.exp (crosscapModelAngle φ i.1))))
    (hb'_mobBd : ∀ i : Fin φ, g_unp (b i) =
      GluedSpace.inr hb_inj (mobBd (Circle.exp (crosscapModelAngle φ (φ + i.1)))))
    (ha'_inr : ∀ i : Fin φ, g_unp (a i) = GluedSpace.inr hb_inj ⟦(u_pt i, 0)⟧)
    (hb'_inr : ∀ i : Fin φ, g_unp (b i) = GluedSpace.inr hb_inj ⟦(u_pt i, 1)⟧)
    (hL_line : ∀ i : Fin φ, IsLineWithEnds
      (crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i) (g_unp (a i)) (g_unp (b i)))
    (hL_disj : Pairwise fun i j => Disjoint
      (crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i)
      (crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt j))
    (hL_S₁ : ∀ i : Fin φ, crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i ∩
      range (GluedSpace.inl hb_inj) = {g_unp (a i), g_unp (b i)})
    (hL_H₁U : ∀ i : Fin φ, crosscap_vertical_lines (GluedSpace.inr hb_inj) u_pt i ∩
      (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).U =
      {g_unp (a i), g_unp (b i)})
    (hP_paths' : ∀ i : Fin φ, IsHPathWithEnds G (liftSpanEmbeddingOn hK_comp hg_unp_cont
      hf_unp_cont' hfg_unp_inv hHU η).imageGraph (P i)
      ((liftSpanEmbeddingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU η).vMap (g_unp (a i)))
      ((liftSpanEmbeddingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU η).vMap (g_unp
        (b i)))) :
    ∃ (Tnew : Type w) (_ : TopologicalSpace Tnew) (_ : T2Space Tnew), IsObtainedByAddingCrosscap S
      Tnew ∧ ∃ (H' : Drawing Tnew) (η' : SpanEmbedding H' G) (T' : Set (Hypergraph Tnew (Set Tnew)
      × Hypergraph Tnew (Set Tnew))), IsSigmaSpan G H' η' θ_star φ T_star T' := by
  let K := univ \ Λ
  let w_a := fun i : Fin φ => Circle.exp (crosscapModelAngle φ i.1)
  let w_b := fun i : Fin φ => Circle.exp (crosscapModelAngle φ (φ + i.1))
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let S₂ := range (GluedSpace.inr hb_inj)
  let H₁ := liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  let η₁ := liftSpanEmbeddingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU η
  let a' := fun i => g_unp (a i)
  let b' := fun i => g_unp (b i)
  let L := fun i => GluedSpace.inr hb_inj '' Quotient.mk Surface.mobiusSetoid '' {u_pt i} ×ˢ univ
  obtain ⟨H_path, H', η', hH'_U, hH'_V, hH'_E, hSub_H₁, hH_path, hH_path_disj,
    _, hvm_H₁, hem_H₁, _, _⟩ :=
    exists_glued_span_of_lines H₁ η₁ a' b' P L ha'_V hb'_V hP_paths' hP_disj
      hL_line hL_disj hL_H₁U
  obtain ⟨hU_S₁, hV_S₁, _⟩ :=
    glued_interSet_base_eq hS₁_cl ha'_V hb'_V hH₁_sub_S₁ hL_S₁ hH'_U hH'_V hH'_E hH_path
  have hι_unp_g : ∀ y ∈ K, ∀ hy : g_unp y ∈ S₁, ι_unp ⟨g_unp y, hy⟩ = y := by
    intro y hy hgy
    have hsub : (⟨g_unp y, hgy⟩ : ↥S₁) = ⟨GluedSpace.inl hb_inj ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ :=
      Subtype.ext (hg_unp_mem y hy)
    rw [hsub, hι_unp_inl ⟨y, hy⟩]
  have hCap_unp : GM12.IsCappedDrawing ι_unp H' H :=
    isCappedDrawing_of_glued hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU hU_S₁ hV_S₁ hι_unp_g
  -- Verify `IsRigid H'` using `theorem_3_2_proof` on the unpinched split.
  have hC_unp_0_sub_H₁ : C_unp 0 ⊆ H₁.U := by
    rw [hC_unp_0]
    rintro _ ⟨y, hy_bd, rfl⟩
    rw [bd_mobiusBand] at hy_bd
    obtain ⟨z, rfl⟩ := hy_bd
    rw [hinr_mobBd z, hH₁_U]
    exact mem_image_of_mem g_unp (hSubBd_sub_U (g z).2)
  have hS12_sub_U : S₁ ∩ S₂ ⊆ H'.U := by
    rw [hS12_inter, hH'_U]
    exact hC_unp_0_sub_H₁.trans subset_union_left
  let X_unp : Set S' := range a' ∪ range b'
  have ha'_C0 : ∀ i, a' i ∈ C_unp 0 := by
    intro i
    change g_unp (a i) ∈ C_unp 0
    rw [ha'_mobBd i, hC_unp_0]
    exact ⟨mobBd (w_a i), by rw [bd_mobiusBand]; exact ⟨w_a i, rfl⟩, rfl⟩
  have hb'_C0 : ∀ i, b' i ∈ C_unp 0 := by
    intro i
    change g_unp (b i) ∈ C_unp 0
    rw [hb'_mobBd i, hC_unp_0]
    exact ⟨mobBd (w_b i), by rw [bd_mobiusBand]; exact ⟨w_b i, rfl⟩, rfl⟩
  have hX_unp_sub : X_unp ⊆ H'.V ∩ (S₁ ∩ S₂) := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨hSub_H₁.1 (ha'_V i), hS12_inter.symm ▸ ha'_C0 i⟩
    · exact ⟨hSub_H₁.1 (hb'_V i), hS12_inter.symm ▸ hb'_C0 i⟩
  have hι_unp_X : ι_unp '' ((↑) ⁻¹' X_unp) = range a ∪ range b := by
    exact crosscap_inclusion_maps_marked_nodes (S := S) φ Λ a b hΛ_open g hb_inj ι_unp
      g_unp   ha_K hb_K H' hι_unp_g  hX_unp_sub
  have hS₂_U : S₂ ∩ H'.U ⊆ (S₁ ∩ S₂) ∪ ⋃ i : Fin φ, L i := by
    rintro x ⟨hx2, hxU⟩
    rw [hH'_U] at hxU
    rcases hxU with hx1 | hxL
    · exact .inl ⟨hH₁_sub_S₁ hx1, hx2⟩
    · exact .inr hxL
  have hRigid_H' : IsRigid H' := by
    exact drawing_on_added_crosscap_is_rigid (S := S) H θ φ T Λ a b hφ hFree_ab hS hRigid_H hT hθ
      hΛ_open g w_a w_b hwb_eq_neg u_pt hu_int hu_inj hb_inj  hS'   hinr_emb hS₁_cl hS₂_cl
      C_unp ι_unp hSplit_unp hC_unp_0 hS12_inter H₁ a' b'  ha'_V hb'_V ha'_mobBd hb'_mobBd
      ha'_inr hb'_inr hL_line hL_disj hL_S₁ H_path H' hH'_U hSub_H₁ hH_path hCap_unp hS12_sub_U
      hX_unp_sub hι_unp_X hS₂_U
  have hH'_U_ne : H'.U.Nonempty := ⟨a' ⟨0, by omega⟩, H'.V_subset_U (hSub_H₁.1
    (ha'_V ⟨0, by omega⟩))⟩
  have h2Cell_H' : (PaintingOrDrawing.drawing H').IsTwoCell :=
    isTwoCell_of_isRigid hS' hRigid_H' hH'_U_ne
  -- Pinched crosscap split and `GM12Theorem52Statement`.
  let W_pts : Set Circle := range w_a ∪ range w_b
  have hW_cl : IsClosed W_pts :=
    (Set.finite_range w_a).isClosed.union (Set.finite_range w_b).isClosed
  have hW_ne : W_pts.Nonempty := ⟨w_a ⟨0, by omega⟩, .inl ⟨⟨0, by omega⟩, rfl⟩⟩
  let CollarInt : Set S' :=
    GluedSpace.inr hb_inj ''
      {y : MobiusBand | y ∉ bd MobiusBand ∧ (collarCoords y).1 ≤ 1 / 4 ∧ (collarCoords y).2 ∉ W_pts}
  obtain ⟨C_XII, P₁_XII, P₂_XII, ι_XII, D_XII, f_XII, f_C0, hSplit_XII, hS₁_sub_P₁,
    hf_XII_inl, hι_XII_eq, _, _, _, hP₁_diff_S₁, hW_sub_C0, hC0_diff_W, hL_sub_P₂, hf_C0_W⟩ :=
    exists_pinched_crosscapSplit hS hΛ_open hΛ_disc hCD hdiscBd hOArc hout g hb_inj hW_cl hW_ne
  have hCollar_disj : Disjoint CollarInt H'.U := by
    exact crosscap_unmarked_collar_avoids_drawing (S := S) φ Λ hΛ_open g w_a w_b u_pt htop_upt
      hbot_upt hb_inj   H₁ hH₁_sub_S₁  H' hH'_U
  have hU_P₁_XII : H'.U ∩ P₁_XII = H₁.U := by
    refine Subset.antisymm ?_ (subset_inter (by rw [hH'_U]; exact subset_union_left)
      (hH₁_sub_S₁.trans hS₁_sub_P₁))
    intro x ⟨hxU, hxP₁⟩
    by_cases hxS₁ : x ∈ S₁
    · exact hU_S₁ ▸ ⟨hxU, hxS₁⟩
    · exact (Set.disjoint_left.mp hCollar_disj (hP₁_diff_S₁ ⟨hxP₁, hxS₁⟩) hxU).elim
  have hV_P₁_XII : H'.V ∩ P₁_XII = H₁.V := by
    refine Subset.antisymm ?_ (subset_inter hSub_H₁.1
      ((H₁.V_subset_U.trans hH₁_sub_S₁).trans hS₁_sub_P₁))
    intro x ⟨hxV, hxP₁⟩
    by_cases hxS₁ : x ∈ S₁
    · exact hV_S₁ ▸ ⟨hxV, hxS₁⟩
    · exact (Set.disjoint_left.mp hCollar_disj
        (hP₁_diff_S₁ ⟨hxP₁, hxS₁⟩) (H'.V_subset_U hxV)).elim
  have hι_XII_g : ∀ y ∈ K, ∀ hy : g_unp y ∈ P₁_XII, ι_XII ⟨g_unp y, hy⟩ = y := by
    intro y hy hgy
    rw [hι_XII_eq ⟨g_unp y, hgy⟩]
    change f_XII (g_unp y) = y
    rw [hg_unp_mem y hy, hf_XII_inl ⟨y, hy⟩]
  have hCap_XII : GM12.IsCappedDrawing ι_XII H' H :=
    isCappedDrawing_of_glued hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU
      hU_P₁_XII hV_P₁_XII hι_XII_g
  have hW_eq_ab' : GluedSpace.inr hb_inj '' (mobBd '' W_pts) = range a' ∪ range b' := by
    ext x
    constructor
    · rintro ⟨_, ⟨_, ⟨i, rfl⟩ | ⟨i, rfl⟩, rfl⟩, rfl⟩
      · exact .inl ⟨i, ha'_mobBd i⟩
      · exact .inr ⟨i, hb'_mobBd i⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · change g_unp (a i) ∈ GluedSpace.inr hb_inj '' (mobBd '' W_pts)
        rw [ha'_mobBd i]
        exact ⟨mobBd (w_a i), ⟨w_a i, .inl ⟨i, rfl⟩, rfl⟩, rfl⟩
      · change g_unp (b i) ∈ GluedSpace.inr hb_inj '' (mobBd '' W_pts)
        rw [hb'_mobBd i]
        exact ⟨mobBd (w_b i), ⟨w_b i, .inr ⟨i, rfl⟩, rfl⟩, rfl⟩
  have hNorm_C0_and_V : H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a' ∪ range b' := by
    exact pinched_crosscap_cuff_is_normal (S := S) φ Λ hΛ_open g hb_inj H₁ a' b' L ha'_V hb'_V
      H_path H' hH'_U hH'_V W_pts C_XII hW_sub_C0 hC0_diff_W hCollar_disj hW_eq_ab'
  have ha'_inj : Function.Injective a' :=
    fun i j hij => ha_inj (hfg_unp_inv.injOn (ha_K i) (ha_K j) hij)
  have hb'_inj : Function.Injective b' :=
    fun i j hij => hb_inj_fn (hfg_unp_inv.injOn (hb_K i) (hb_K j) hij)
  have hab'_ne : ∀ i j : Fin φ, a' i ≠ b' j :=
    fun i j hij => hab_ne i j (by
      have h := congrArg f_unp hij
      rwa [hfg_unp_inv (ha_K i), hfg_unp_inv (hb_K j)] at h)
  have hab'_disj : Disjoint (range a') (range b') := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact hab'_ne i j hj.symm
  have hNodup_ab' : (List.ofFn a' ++ List.ofFn b').Nodup := by
    refine List.nodup_append'.mpr ⟨List.nodup_ofFn.mpr ha'_inj, List.nodup_ofFn.mpr hb'_inj, ?_⟩
    intro x hx₁ hx₂
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx₁
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hx₂
    exact hab'_ne i j hj.symm
  have hCard_C0 : (H'.V ∩ C_XII 0).ncard = 2 * φ := by
    rw [hNorm_C0_and_V.2,
      Set.ncard_union_eq hab'_disj (Set.finite_range a') (Set.finite_range b'),
      Set.ncard_range_of_injective ha'_inj, Set.ncard_range_of_injective hb'_inj,
      Nat.card_fin, two_mul]
  have hOrder_C0 : GM12.IsListedInOrderOn (C_XII 0) (List.ofFn a' ++ List.ofFn b') := by
    exact pinched_crosscap_preserves_boundary_order hφ hΛ_open g hb_inj a' b'
      ha'_mobBd hb'_mobBd C_XII f_C0 hf_C0_W
  have hP₂_XII_cl : IsClosed P₂_XII := by
    have : CompactSpace ↥P₂_XII := hSplit_XII.1.manifold₂.1
    exact (isCompact_iff_compactSpace.mpr this).isClosed
  have hH₁_P₂_XII : H₁.U ∩ P₂_XII ⊆ ⋃ i : Fin φ, ({a' i, b' i} : Set S') := by
    exact base_drawing_meets_pinched_crosscap_at_ends (S := S) φ Λ hΛ_open g hb_inj H₁
      hH₁_sub_S₁ a' b' L H' hH'_U C_XII P₁_XII P₂_XII ι_XII D_XII hSplit_XII hS₁_sub_P₁
      hNorm_C0_and_V
  obtain ⟨hH_path_sub_P₂, hInter_P₂_U⟩ :=
    glued_interSet_paths_eq hP₂_XII_cl
      (fun i => hL_sub_P₂ (u_pt i) (htop_upt i ▸ .inl ⟨i, rfl⟩) (hbot_upt i ▸ .inr ⟨i, rfl⟩))
      hH₁_P₂_XII hH'_V hH'_E hH_path
  -- Truncated tangle `T₁` and induced tangle `T'`.
  let T₁ := GM10.truncation T φ
  have hResp_T₁ : IsRespectfulDrawingTangle H φ T₁ :=
    isRespectfulDrawingTangle_truncation hResp_H (by omega) hφ_le
  have hCtrl_T₁ : IsControllingTangle G H η θ_star φ T_star T₁ :=
    isControllingTangle_truncation hSpan.isControlling (by omega) hφ_le
  have hι_XII_C0 : ι_XII '' ((↑) ⁻¹' (H'.V ∩ C_XII 0)) = range a ∪ range b := by
    exact pinched_crosscap_cuff_vertices_map_to_original_ends (S := S) φ Λ a b hΛ_open g hb_inj
        g_unp H₁ hH₁_sub_S₁   ha_K hb_K ha'_V hb'_V H' C_XII P₁_XII ι_XII hS₁_sub_P₁
      hι_XII_g hNorm_C0_and_V
  have hFree_T₁ : ∀ X ⊆ ι_XII '' ((↑) ⁻¹' (H'.V ∩ C_XII 0)),
      X.ncard ≤ φ → IsFreeSet H.toHypergraph T₁ φ X := by
    intro X hX_sub hX_card
    rw [hι_XII_C0] at hX_sub
    exact theorem_3_3_claim_2 hT hFree_ab hX_sub hX_card
  have hResp_T' : (PaintingOrDrawing.drawing H').IsRespectful φ
      (GM12.inducedAcross ι_XII H' H φ T₁) :=
    GraphMinor.GM12.theorem_5_2_proof.{w} C_XII P₁_XII P₂_XII ι_XII D_XII H' H φ T₁ H_path a' b'
      (le_trans (by norm_num) hφ) hS' hConn' hSplit_XII hCap_XII hNorm_C0_and_V.1 hCard_C0
        hNodup_ab' hOrder_C0
      hNorm_C0_and_V.2.symm
      (fun i => ⟨(hH_path i).2.1, hH_path_sub_P₂ i⟩)
      hH_path_disj hInter_P₂_U hResp_T₁.2.1 hResp_T₁.2.2 hFree_T₁
  have hη'_v : ∀ v ∈ H.V, η'.vMap (g_unp v) = η.vMap v := by
    intro v hv
    rw [hvm_H₁ (g_unp v) (by rw [hH₁_V]; exact ⟨v, hv, rfl⟩)]
    change η.vMap (f_unp (g_unp v)) = η.vMap v
    rw [hfg_unp_inv (hHU (H.V_subset_U hv))]
  have hη'_e : ∀ e ∈ H.E, η'.eMap (g_unp '' e) = η.eMap e := by
    exact crosscap_embedding_agrees_on_original_edges (S := S) (α := α) (β := β) G H η Λ hΛ_open
      hK_comp hHU g hb_inj  g_unp f_unp hg_unp_cont hfg_unp_inv hf_unp_cont'   H' η' hem_H₁
  obtain ⟨hT', hCtrl_T'⟩ :=
    isTangle_and_isControlling_inducedAcross hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv
      hHU η η' hSub_H₁ hU_P₁_XII hV_P₁_XII hι_XII_g hη'_v hη'_e hCtrl_T₁
  refine ⟨S', inferInstance, inferInstance, hCrosscap, H', η',
    GM12.inducedAcross ι_XII H' H φ T₁, ?_⟩
  exact
    { isSurface := IsClosedSurface.isSurface hS'
      isConnected := hConn'
      bd_empty := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hS'.2.2 x)
      isRigid := hRigid_H'
      isRespectful := ⟨h2Cell_H', hT', hResp_T'⟩
      isControlling := hCtrl_T' }

/-- **Graph Minors XV, (3.3)** (pages 120–121):
Adding a crosscap to a region `Λ` along `φ` disjoint `η(H)`-paths `P_i` with ends `a_i, b_i` in
circular order `a_1, ..., a_φ, b_1, ..., b_φ` on `subBd Λ` yields a `Σ'`-span `(H', η', T')` of
order `φ`. -/
theorem theorem_3_3_proof : GM15Theorem33Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ φ T_star T Λ P a b
    hSpan hΛ hOArc _hCirc hφ hφ_le hNodup_ab hOrder_ab hab_mem hP_paths hP_disj hFree_ab
  have hS : IsClosedSurface S :=
    ⟨hSpan.isSurface.1, hSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : CompactSpace S := hS.1
  have hRigid_H : IsRigid H := hSpan.isRigid
  have hResp_H : IsRespectfulDrawingTangle H θ T := hSpan.isRespectful
  have hT : IsTangle H.toHypergraph θ T := hResp_H.2.1
  have hθ : 3 ≤ θ := le_trans hφ hφ_le
  have hΛ_open : IsOpen Λ := GM11.region_isOpen hΛ
  have hΛ_disc : IsOpenDisc Λ := hResp_H.1.2 Λ hΛ
  obtain ⟨hout, hCD, hdiscBd, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hResp_H hθ hΛ hOArc
  obtain ⟨_, hSubBd_U, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ hOArc
  have hSubBd_sub_U : subBd Λ ⊆ H.U := by
    have hcl : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
    rw [← hSubBd_U, (H.interSet (subBd Λ)).U_eq,
      interSet_V_of_isClosed H hcl, interSet_E]
    exact union_subset (inter_subset_left.trans H.V_subset_U)
      (iUnion₂_subset fun e he => H.closure_subset_U he.1)
  let K : Set S := univ \ Λ
  have hK_cl : IsClosed K := isClosed_univ.sdiff hΛ_open
  have hK_comp : IsCompact K := hK_cl.isCompact
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK_comp
  obtain ⟨m_mob⟩ := nonempty_mob_homeo
  have hMob_surf : IsSurface MobiusBand := isSurface_of_homeo m_mob (isSurface_model 0 1 1).1
  have : CompactSpace MobiusBand := hMob_surf.1
  have hHU : H.U ⊆ K := fun y hy => ⟨mem_univ y, fun h => GM11.region_subset hΛ h hy⟩
  obtain ⟨g, hg_wa_model, hg_wb_model⟩ := realize_marked_crosscap_boundary (Λ := Λ) hφ a b hOrder_ab
  let t_model := crosscapModelAngle φ
  let w_a : Fin φ → Circle := fun i => Circle.exp (t_model i.1)
  let w_b : Fin φ → Circle := fun i => Circle.exp (t_model (φ + i.1))
  have hg_wa : ∀ i, (g (w_a i)).1 = a i := hg_wa_model
  have hg_wb : ∀ i, (g (w_b i)).1 = b i := hg_wb_model
  have hwb_eq_neg : ∀ i : Fin φ, w_b i = - w_a i := by
    intro i
    change Circle.exp (crosscapModelAngle φ (φ + i.1)) =
      - Circle.exp (crosscapModelAngle φ i.1)
    rw [crosscapModelAngle_add_phi i.2, circle_exp_add_pi]
  have hNodup_ab_iff := List.nodup_append'.mp hNodup_ab
  have ha_inj : Function.Injective a := List.nodup_ofFn.mp hNodup_ab_iff.1
  have hb_inj_fn : Function.Injective b := List.nodup_ofFn.mp hNodup_ab_iff.2.1
  have hab_ne : ∀ i j : Fin φ, a i ≠ b j :=
    fun i j h =>
      hNodup_ab_iff.2.2 (List.mem_ofFn.mpr ⟨i, rfl⟩) (h ▸ List.mem_ofFn.mpr ⟨j, rfl⟩)
  let u_pt : Fin φ → unitInterval := fun i => mobBdTopU (w_a i)
  have hwa_im_pos : ∀ i : Fin φ, 0 < (w_a i : ℂ).im := fun i => by
    obtain ⟨h0, hpi⟩ := crosscapModelAngle_mem_Ioo_pi i.2
    exact circle_exp_im_pos_of_mem_Ioo h0 hpi
  have hwb_im_nonpos : ∀ i : Fin φ, (w_b i : ℂ).im ≤ 0 := fun i => by
    rw [hwb_eq_neg i]
    change - (w_a i : ℂ).im ≤ 0
    linarith [hwa_im_pos i]
  have hu_int : ∀ i : Fin φ, 0 < (u_pt i : ℝ) ∧ (u_pt i : ℝ) < 1 := by
    intro i
    obtain ⟨h0, hpi⟩ := crosscapModelAngle_mem_Ioo_pi i.2
    obtain ⟨hre1, hre2⟩ := circle_exp_re_mem_Ioo_of_mem_Ioo h0 hpi
    change 0 < (mobBdTopU (w_a i) : ℝ) ∧ (mobBdTopU (w_a i) : ℝ) < 1
    rw [mobBdTopU_coe]
    exact ⟨by linarith, by linarith⟩
  have htop_upt : ∀ i : Fin φ, circleTop (u_pt i) = w_a i :=
    fun i => circleTop_mobBdTopU (le_of_lt (hwa_im_pos i))
  have hbotU_wb : ∀ i : Fin φ, mobBdBotU (w_b i) = u_pt i := by
    intro i
    rw [hwb_eq_neg i, mobBdBotU_neg]
  have hbot_upt : ∀ i : Fin φ, circleBot (u_pt i) = w_b i := by
    intro i
    rw [← hbotU_wb i]
    exact circleBot_mobBdBotU (hwb_im_nonpos i)
  have hmobBd_wa : ∀ i : Fin φ,
      mobBd (w_a i) = Quotient.mk Surface.mobiusSetoid (u_pt i, 0) :=
    fun i => mobBd_of_im_nonneg (le_of_lt (hwa_im_pos i))
  have hmobBd_wb : ∀ i : Fin φ,
      mobBd (w_b i) = Quotient.mk Surface.mobiusSetoid (u_pt i, 1) := by
    intro i
    rw [mobBd_of_im_nonpos (hwb_im_nonpos i), hbotU_wb i]
  have hu_inj : Function.Injective u_pt := by
    intro i j hij
    have hwa : w_a i = w_a j := by rw [← htop_upt i, ← htop_upt j, hij]
    exact ha_inj (by rw [← hg_wa i, ← hg_wa j, hwa])
  -- Construct the glued surface `S'`.
  let b_glue := crosscapGlueMap hΛ_open g
  have hb_inj := injective_crosscapGlueMap hΛ_open g
  have hb_cont := continuous_crosscapGlueMap hΛ_open g
  have hb_range := range_crosscapGlueMap hS hΛ_open hOArc hout g
  let S' := GluedSpace hb_inj
  have : T2Space S' := GluedSpace.t2Space (isClosed_bd MobiusBand) hb_cont hb_inj
  obtain ⟨hS', hConn', hCrosscap, _, _, hU_S12_eq, _, _⟩ :=
    isClosedSurface_of_crosscap_glue hS hΛ_disc hOArc hout hb_cont hb_inj hb_range
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  have hS₁_cl : IsClosed S₁ := hinl_emb.isClosed_range
  have hS₂_cl : IsClosed S₂ := hinr_emb.isClosed_range
  -- Unpinched split on `S'`.
  obtain ⟨C_unp, ι_unp, hSplit_unp, hC_unp_0, _, hι_unp_inl⟩ :=
    isCappedSplit_crosscap_unpinched hS hΛ_open hΛ_disc hOArc hout g hb_inj
  have hS12_inter : S₁ ∩ S₂ = C_unp 0 := by
    rw [hSplit_unp.inter]
    ext x
    simp
  have ha0_K : a ⟨0, by omega⟩ ∈ K := hHU (H.V_subset_U (hab_mem ⟨0, by omega⟩).1.1)
  obtain ⟨g_unp, f_unp, hg_unp_mem, hf_unp_inl, hg_unp_cont, hfg_unp_inv, hg_unp_K, hf_unp_cont'⟩ :=
    crosscap_base_inclusion_and_retraction hΛ_open g hb_inj _ ha0_K ι_unp
      hSplit_unp.isEmbedding.continuous hι_unp_inl
  let H₁ : Drawing S' := liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  let η₁ : SpanEmbedding H₁ G :=
    liftSpanEmbeddingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU η
  have hH₁_U : H₁.U = g_unp '' H.U :=
    liftDrawingOn_U hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  have hH₁_V : H₁.V = g_unp '' H.V :=
    liftDrawingOn_V hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  have hH₁_sub_S₁ : H₁.U ⊆ S₁ := by
    rw [hH₁_U]
    exact (image_mono hHU).trans (le_of_eq hg_unp_K)
  -- Vertical lines `L i` and endpoints `a' i, b' i`.
  let a' : Fin φ → S' := fun i => g_unp (a i)
  let b' : Fin φ → S' := fun i => g_unp (b i)
  let L : Fin φ → Set S' :=
    fun i => GluedSpace.inr hb_inj '' (Quotient.mk Surface.mobiusSetoid '' ({u_pt i} ×ˢ univ))
  have ha_K : ∀ i, a i ∈ K := fun i => hHU (H.V_subset_U (hab_mem i).1.1)
  have hb_K : ∀ i, b i ∈ K := fun i => hHU (H.V_subset_U (hab_mem i).2.1)
  have ha'_V : ∀ i, a' i ∈ H₁.V := fun i => by rw [hH₁_V]; exact ⟨a i, (hab_mem i).1.1, rfl⟩
  have hb'_V : ∀ i, b' i ∈ H₁.V := fun i => by rw [hH₁_V]; exact ⟨b i, (hab_mem i).2.1, rfl⟩
  have hinr_mobBd : ∀ z : Circle,
      GluedSpace.inr hb_inj (mobBd z) = g_unp (g z).1 := by
    intro z
    have hbd : mobBd z ∈ bd MobiusBand := by rw [bd_mobiusBand]; exact ⟨z, rfl⟩
    have hzK : (g z).1 ∈ K := hHU (hSubBd_sub_U (g z).2)
    have hb_z : b_glue ⟨mobBd z, hbd⟩ = ⟨(g z).1, hzK⟩ :=
      Subtype.ext (crosscapGlueMap_mobBd hΛ_open g z)
    rw [hg_unp_mem (g z).1 hzK, ← hb_z]
    exact ((GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd, rfl⟩).symm
  have ha'_mobBd : ∀ i, a' i = GluedSpace.inr hb_inj (mobBd (w_a i)) := by
    intro i
    dsimp [a']
    rw [← hg_wa i, hinr_mobBd]
  have hb'_mobBd : ∀ i, b' i = GluedSpace.inr hb_inj (mobBd (w_b i)) := by
    intro i
    dsimp [b']
    rw [← hg_wb i, hinr_mobBd]
  have ha'_inr : ∀ i,
      a' i = GluedSpace.inr hb_inj (Quotient.mk Surface.mobiusSetoid (u_pt i, 0)) := by
    intro i; rw [ha'_mobBd i, hmobBd_wa i]
  have hb'_inr : ∀ i,
      b' i = GluedSpace.inr hb_inj (Quotient.mk Surface.mobiusSetoid (u_pt i, 1)) := by
    intro i; rw [hb'_mobBd i, hmobBd_wb i]
  have hL_line : ∀ i, IsLineWithEnds (L i) (a' i) (b' i) := by
    intro i
    rw [ha'_inr i, hb'_inr i]
    obtain ⟨f, h0, h1⟩ := isLineWithEnds_mobVertical (u_pt i) (hu_int i).1 (hu_int i).2
    exact ⟨f.trans
      (hinr_emb.isEmbedding.homeomorphImage
        (Quotient.mk Surface.mobiusSetoid '' ({u_pt i} ×ˢ univ))),
      congrArg (GluedSpace.inr hb_inj) h0, congrArg (GluedSpace.inr hb_inj) h1⟩
  have hL_disj : Pairwise (fun i j => Disjoint (L i) (L j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
    have hpq := GluedSpace.inr_injective hb_inj heq
    subst hpq
    exact Set.disjoint_left.mp
      (disjoint_mobVertical_of_ne (hu_int i).1 (hu_int i).2 (fun h => hij (hu_inj h)))
      hp hq
  have hL_S₁ : ∀ i, L i ∩ S₁ = {a' i, b' i} := by
    exact crosscap_lines_meet_base_at_ends (S := S) φ Λ hΛ_open g u_pt hb_inj H₁ hH₁_sub_S₁
      a' b'  ha'_V hb'_V ha'_inr hb'_inr
  have hL_H₁U : ∀ i, L i ∩ H₁.U = {a' i, b' i} := by
    exact crosscap_lines_meet_lifted_drawing_at_ends (S := S) φ Λ hΛ_open g hb_inj H₁
      hH₁_sub_S₁ a' b' L ha'_V hb'_V hL_S₁
  have hP_paths' : ∀ i : Fin φ,
      IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (a' i)) (η₁.vMap (b' i)) := by
    intro i
    change IsHPathWithEnds G η.imageGraph (P i) (η.vMap (f_unp (g_unp (a i))))
      (η.vMap (f_unp (g_unp (b i))))
    rw [hfg_unp_inv (ha_K i), hfg_unp_inv (hb_K i)]
    exact hP_paths i
  have crosscapFinish : ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
      IsObtainedByAddingCrosscap S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsSigmaSpan G H' η' θ_star φ T_star T' := by
    exact assemble_rigid_span_on_added_crosscap (S := S) (α := α) (β := β) G H η θ_star θ φ T_star
      T Λ P a b hSpan hOArc hφ hφ_le hP_disj hFree_ab hS hRigid_H hResp_H hT hθ hΛ_open hΛ_disc
      hout hCD hdiscBd hSubBd_sub_U hK_comp hHU g hwb_eq_neg ha_inj hb_inj_fn hab_ne u_pt hu_int
      htop_upt hbot_upt hu_inj hb_inj hS' hCrosscap hinr_emb hS₁_cl hS₂_cl C_unp ι_unp hSplit_unp
      hC_unp_0 hι_unp_inl hS12_inter g_unp f_unp hg_unp_mem hg_unp_cont hfg_unp_inv hf_unp_cont'
      hH₁_U hH₁_V hH₁_sub_S₁ ha_K hb_K ha'_V hb'_V hinr_mobBd ha'_mobBd hb'_mobBd ha'_inr hb'_inr
      hL_line hL_disj hL_S₁ hL_H₁U hP_paths'
  exact crosscapFinish

end GraphMinor.GM15

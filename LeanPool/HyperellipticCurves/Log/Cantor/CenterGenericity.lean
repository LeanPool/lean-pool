/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CantorPipeline

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# Genericity of a Cantor step: characterizations and the coprime composition

The per-step content of chain genericity, isolated. A Cantor reduction step is
**unconditional** when the curve degree dominates — the cofactor has its generic degree
for free (`ChabautyColeman.natDegree_cantorCofactor_of_lt`) — and **conditional** when
the square dominates, where full cofactor degree is *equivalent* to the current square
root having exact top degree (`ChabautyColeman.natDegree_cantorCofactor_eq_iff`). So
every chain-genericity condition is a top-coefficient condition on the evolving square
roots.

The **coprime composition** is certificate-independent, by Chinese-remainder uniqueness
of the composed square root (`ChabautyColeman.eq_cantorCompose_snd`), and against a
coprime `u`-part the composed square root is a plain interpolation
(`ChabautyColeman.cantorCompose_snd_eq_add_mul`) — the inputs of the per-disk pencil
(`LeanPool.HyperellipticCurves.Log.Witness.DiskWitness`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section CoprimeCompose

variable {R : Type*} [CommRing R] {f u₁ v₁ u₂ v₂ w₁ w₂ s₁ s₂ s₃ t₁ t₂ t₃ : R[X]}

theorem cantorCompose_snd_sub_dvd_left (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₁ : v₁ ^ 2 - f = u₁ * w₁) :
    u₁ ∣ (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2 - v₁ := by
  have hmod := modByMonic_add_div (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃) (u₁ * u₂)
  refine ⟨s₁ * (v₂ - v₁) - s₃ * w₁
    - u₂ * (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ /ₘ (u₁ * u₂)), ?_⟩
  rw [cantorCompose_snd]
  linear_combination hmod + cantorV_sub_left f hbez hw₁

theorem cantorCompose_snd_sub_dvd_right (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hw₂ : v₂ ^ 2 - f = u₂ * w₂) :
    u₂ ∣ (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2 - v₂ := by
  have hmod := modByMonic_add_div (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃) (u₁ * u₂)
  refine ⟨s₂ * (v₁ - v₂) - s₃ * w₂
    - u₁ * (cantorV f u₁ v₁ u₂ v₂ s₁ s₂ s₃ /ₘ (u₁ * u₂)), ?_⟩
  rw [cantorCompose_snd]
  linear_combination hmod + cantorV_sub_right f hbez hw₂

variable [Nontrivial R]

/-- **CRT uniqueness of the composed square root**: for coprime `u`-parts, any
polynomial congruent to `v₁` modulo `u₁` and to `v₂` modulo `u₂`, of degree below
`u₁u₂`, is the `v`-part of the certified Cantor composition. -/
theorem eq_cantorCompose_snd (hu₁ : u₁.Monic) (hu₂ : u₂.Monic) (hcop : IsCoprime u₁ u₂)
    (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1) (hw₁ : v₁ ^ 2 - f = u₁ * w₁)
    (hw₂ : v₂ ^ 2 - f = u₂ * w₂) {W : R[X]} (h₁ : u₁ ∣ W - v₁) (h₂ : u₂ ∣ W - v₂)
    (hdeg : W.degree < (u₁ * u₂).degree) :
    W = (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2 := by
  have hc₁ : u₁ ∣ W - (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2 := by
    have h := dvd_sub h₁ (cantorCompose_snd_sub_dvd_left hbez hw₁)
    rwa [sub_sub_sub_cancel_right] at h
  have hc₂ : u₂ ∣ W - (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2 := by
    have h := dvd_sub h₂ (cantorCompose_snd_sub_dvd_right hbez hw₂)
    rwa [sub_sub_sub_cancel_right] at h
  have h0 := (hu₁.mul hu₂).eq_zero_of_dvd_of_degree_lt (hcop.mul_dvd hc₁ hc₂)
    (lt_of_le_of_lt (degree_sub_le _ _)
      (max_lt hdeg (degree_modByMonic_lt _ (hu₁.mul hu₂))))
  linear_combination h0

/-- **The composed square root in Chinese-remainder form**: when the `u`-parts are coprime,
a correction `H` to the second square root that fixes its residue modulo the first `u`-part
*is* the composed square root. This is the shape a witness computes with — for a pair block
`(u₁, v₁)` of degree `2`, `H` is the linear interpolant of `(v₁ - v₂)/u₂` at the two points,
and the reduction step is generic exactly when that interpolant is not constant. -/
theorem cantorCompose_snd_eq_add_mul (hu₁ : u₁.Monic) (hu₂ : u₂.Monic) (hcop : IsCoprime u₁ u₂)
    (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1) (hw₁ : v₁ ^ 2 - f = u₁ * w₁)
    (hw₂ : v₂ ^ 2 - f = u₂ * w₂) {H : R[X]} (hH : u₁ ∣ u₂ * H - (v₁ - v₂))
    (hdeg : (v₂ + u₂ * H).degree < (u₁ * u₂).degree) :
    (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2 = v₂ + u₂ * H :=
  have ⟨k, hk⟩ := hH
  (eq_cantorCompose_snd hu₁ hu₂ hcop hbez hw₁ hw₂ ⟨k, by linear_combination hk⟩
    ⟨H, by ring⟩ hdeg).symm

end CoprimeCompose

variable {R : Type*} [CommRing R] {f U V : R[X]}

/-- **The unconditional reduction step**: when the curve degree dominates, the Cantor
cofactor has its generic degree for free. -/
theorem natDegree_cantorCofactor_of_lt (hU : U.Monic)
    (hd : U ∣ V ^ 2 - f) (hV : V.degree < U.degree)
    (hlt : 2 * (U.natDegree - 1) < f.natDegree) :
    (cantorCofactor f U V).natDegree = f.natDegree - U.natDegree := by
  have hspec := cantorCofactor_spec f hU hd
  -- `V² - f` has the degree of `f`
  have hVn : V.natDegree ≤ U.natDegree - 1 := by
    rcases eq_or_ne V 0 with rfl | hV0
    · simp
    · lia [natDegree_lt_natDegree hV0 hV]
  have hVsq : (V ^ 2).natDegree < f.natDegree :=
    lt_of_le_of_lt (natDegree_pow_le.trans (by lia)) hlt
  have hdeg : (V ^ 2 - f).natDegree = f.natDegree := natDegree_sub_eq_right_of_natDegree_lt hVsq
  have hne : V ^ 2 - f ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    lia
  have hw0 : cantorCofactor f U V ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hspec
    exact hne hspec
  have hlc : U.leadingCoeff * (cantorCofactor f U V).leadingCoeff ≠ 0 := by
    rw [hU.leadingCoeff, one_mul]
    exact leadingCoeff_ne_zero.mpr hw0
  have hmul : U.natDegree + (cantorCofactor f U V).natDegree
      = (V ^ 2 - f).natDegree := by
    rw [hspec, natDegree_mul' hlc]
  lia

variable [NoZeroDivisors R]

/-- **The cofactor of a Mumford datum on an odd-degree curve is nonzero**: `v² - f` cannot
vanish, its degree being odd on one side and even on the other. -/
theorem cantorCofactor_ne_zero (hU : U.Monic) (hd : U ∣ V ^ 2 - f) (hodd : Odd f.natDegree) :
    cantorCofactor f U V ≠ 0 := by
  have hne : V ^ 2 - f ≠ 0 := by
    intro h0
    have h2 := congrArg natDegree (sub_eq_zero.mp h0)
    rw [natDegree_pow] at h2
    rcases hodd with ⟨k, hk⟩
    lia
  intro h0
  have hspec := cantorCofactor_spec f hU hd
  rw [h0, mul_zero] at hspec
  exact hne hspec

/-- **The conditional reduction step**: when the square dominates the curve degree,
the cofactor attains its generic degree exactly when the square root has exact top
degree. -/
theorem natDegree_cantorCofactor_eq_iff (hU : U.Monic) (hd : U ∣ V ^ 2 - f)
    (hV : V.degree < U.degree) (hodd : Odd f.natDegree)
    (hgt : f.natDegree < 2 * (U.natDegree - 1)) :
    (cantorCofactor f U V).natDegree = 2 * (U.natDegree - 1) - U.natDegree
      ↔ V.natDegree = U.natDegree - 1 := by
  have hspec := cantorCofactor_spec f hU hd
  have hd2 : 2 ≤ U.natDegree := by lia
  have hVn : V.natDegree ≤ U.natDegree - 1 := by
    rcases eq_or_ne V 0 with rfl | hV0
    · simp
    · lia [natDegree_lt_natDegree hV0 hV]
  have hw0 := cantorCofactor_ne_zero hU hd hodd
  have hlc : U.leadingCoeff * (cantorCofactor f U V).leadingCoeff ≠ 0 := by
    rw [hU.leadingCoeff, one_mul]
    exact leadingCoeff_ne_zero.mpr hw0
  have hmul : U.natDegree + (cantorCofactor f U V).natDegree
      = (V ^ 2 - f).natDegree := by
    rw [hspec, natDegree_mul' hlc]
  constructor
  · intro h
    by_contra hVne
    have hVlt : V.natDegree ≤ U.natDegree - 2 := by lia
    have hsub : (V ^ 2 - f).natDegree
        ≤ max (2 * (U.natDegree - 2)) f.natDegree :=
      (natDegree_sub_le _ _).trans (max_le_max (natDegree_pow_le.trans (by lia)) le_rfl)
    lia
  · intro h
    have hV0 : V ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at h
      lia
    have hVsq : (V ^ 2).natDegree = 2 * (U.natDegree - 1) := by rw [natDegree_pow, h]
    have hfd : f.natDegree < (V ^ 2).natDegree := by lia
    have hdeg : (V ^ 2 - f).natDegree = 2 * (U.natDegree - 1) := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by lia), hVsq]
    lia

end ChabautyColeman

end

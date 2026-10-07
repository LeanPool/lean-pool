/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CIVAxisymmetric.Reduction.AxisDeriv
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Base case of the induction on derivative order

The order `0` and order `1` base case of the induction on derivative order behind
`thm:analytic:interior` (Kahane 1969): a merely `C^∞` field is automatically bounded, together
with its first derivatives, on any closed sub-ball of its domain of smoothness, by the
extreme value theorem on the compact closure `CIV.isCompact_closure_vec3Ball`. No a priori
bound on `u` is assumed by `CIV.interiorAnalyticity`, so this is the only source of a
starting bound for the recursion that produces the full factorial-type estimate
`AnalyticBoundOn`, `eq:analytic:interior:force`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_bound_of_contDiffOn_zero {G : Vec3 → ℝ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (vec3Ball 0 R)) :
    ∃ M : ℝ, ∀ x ∈ vec3Ball 0 r, |G x| ≤ M := by
  set K := closure (vec3Ball (0 : Vec3) r) with hK
  have hKcpt : IsCompact K := isCompact_closure_vec3Ball hr
  have hKsub : K ⊆ vec3Ball 0 R := by
    rw [hK, closure_vec3Ball hr]
    intro x hx
    have hnorm : vec3EuclideanNorm (x - 0) ≤ r := hx
    have hnorm' : vec3EuclideanNorm x ≤ r := by simpa [sub_zero] using hnorm
    have hlt : vec3EuclideanNorm x < R := lt_of_le_of_lt hnorm' hrR
    simpa [sub_zero] using hlt
  have hGK : ContDiffOn ℝ (⊤ : ℕ∞) G K := hG.mono hKsub
  have hGK_cont : ContinuousOn G K := hGK.continuousOn
  obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn hGK_cont
  refine ⟨M, fun x hx => ?_⟩
  have hxK : x ∈ K := subset_closure hx
  have h := hM x hxK
  simpa [Real.norm_eq_abs] using h

theorem exists_bound_of_contDiffOn_one {G : Vec3 → ℝ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (vec3Ball 0 R)) :
    ∃ M : ℝ, ∀ x ∈ vec3Ball 0 r, ∀ j : Fin 3, |axisDeriv j G x| ≤ M := by
  set K := closure (vec3Ball (0 : Vec3) r) with hK
  have hKcpt : IsCompact K := isCompact_closure_vec3Ball hr
  have hKsub : K ⊆ vec3Ball 0 R := by
    rw [hK, closure_vec3Ball hr]
    intro x hx
    have hnorm : vec3EuclideanNorm (x - 0) ≤ r := hx
    have hnorm' : vec3EuclideanNorm x ≤ r := by simpa [sub_zero] using hnorm
    have hlt : vec3EuclideanNorm x < R := lt_of_le_of_lt hnorm' hrR
    simpa [sub_zero] using hlt
  have hGK : ContDiffOn ℝ (⊤ : ℕ∞) G K := hG.mono hKsub
  have hU : IsOpen (vec3Ball (0 : Vec3) R) := isOpen_vec3Ball 0 R
  have h_fderiv_cont (j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => fderiv ℝ G x (basisVec j)) (vec3Ball 0 R) :=
    (hG.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have h_bound (j : Fin 3) : ∃ Mj : ℝ, ∀ x ∈ K, |axisDeriv j G x| ≤ Mj := by
    have h_cont_on : ContinuousOn (fun x : Vec3 => fderiv ℝ G x (basisVec j)) K :=
      ((h_fderiv_cont j).mono hKsub).continuousOn
    obtain ⟨Mj, hMj⟩ := hKcpt.exists_bound_of_continuousOn h_cont_on
    refine ⟨Mj, fun x hx => ?_⟩
    have h := hMj x hx
    rwa [Real.norm_eq_abs] at h
  choose M hM using h_bound
  refine ⟨max (max (M 0) (M 1)) (M 2), fun x hx j => ?_⟩
  have hxK : x ∈ K := subset_closure hx
  have hbound_j := hM j x hxK
  have h_le_max : M j ≤ max (max (M 0) (M 1)) (M 2) := by
    fin_cases j <;> simp
  linarith only [hbound_j, h_le_max]

theorem analyticBoundOn_order_le_one_of_contDiffOn {g : ParabolicPoint → Vec3} {R r t : ℝ}
    (hr : 0 < r) (hrR : r < R) (i : Fin 3)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t) i) (vec3Ball 0 R)) :
    ∃ M : ℝ, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 1 → ∀ x ∈ vec3Ball 0 r,
      |multiPartial (fun w => g w i) α ((x, t) : ParabolicPoint)| ≤ M := by
  set G := fun x : Vec3 => g (x, t) i with hG
  have hG_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) G (vec3Ball 0 R) := by
    simpa [hG] using hg
  obtain ⟨M0, hM0⟩ := exists_bound_of_contDiffOn_zero hr hrR hG_contDiffOn
  obtain ⟨M1, hM1⟩ := exists_bound_of_contDiffOn_one hr hrR hG_contDiffOn
  refine ⟨max M0 M1, fun α hα_sum x hx => ?_⟩
  have h_cases : (α 0 = 0 ∧ α 1 = 0 ∧ α 2 = 0) ∨
      (α 0 = 1 ∧ α 1 = 0 ∧ α 2 = 0) ∨
      (α 0 = 0 ∧ α 1 = 1 ∧ α 2 = 0) ∨
      (α 0 = 0 ∧ α 1 = 0 ∧ α 2 = 1) := by
    have h0 := Nat.zero_le (α 0)
    have h1 := Nat.zero_le (α 1)
    have h2 := Nat.zero_le (α 2)
    omega
  rcases h_cases with (⟨hα0, hα1, hα2⟩ | ⟨hα0, hα1, hα2⟩ | ⟨hα0, hα1, hα2⟩ | ⟨hα0, hα1, hα2⟩)
  · -- all zero
    have hα_eq : α = fun _ => 0 := by
      ext j; fin_cases j <;> assumption
    have h_multi : multiPartial (fun w => g w i) α ((x, t) : ParabolicPoint) = G x := by
      rw [hα_eq]
      have h_slice := multiPartial_slice (fun w => g w i) (fun _ => 0) t
      have h_pt := congr_fun h_slice x
      simpa [hG, Function.iterate_zero] using h_pt
    rw [h_multi]
    exact le_trans (hM0 x hx) (le_max_left _ _)
  · -- α 0 = 1, others 0
    have hα_eq : α = fun k => if k = 0 then 1 else 0 := by
      ext j; fin_cases j <;> simp [hα0, hα1, hα2]
    have h_multi : multiPartial (fun w => g w i) α ((x, t) : ParabolicPoint) = axisDeriv 0 G x := by
      rw [hα_eq]
      have h_slice := multiPartial_slice (fun w => g w i) (fun k => if k = 0 then 1 else 0) t
      have h_pt := congr_fun h_slice x
      simpa [hG, Function.iterate_zero, Function.iterate_one] using h_pt
    rw [h_multi]
    exact le_trans (hM1 x hx 0) (le_max_right _ _)
  · -- α 1 = 1, others 0
    have hα_eq : α = fun k => if k = 1 then 1 else 0 := by
      ext j; fin_cases j <;> simp [hα0, hα1, hα2]
    have h_multi : multiPartial (fun w => g w i) α ((x, t) : ParabolicPoint) = axisDeriv 1 G x := by
      rw [hα_eq]
      have h_slice := multiPartial_slice (fun w => g w i) (fun k => if k = 1 then 1 else 0) t
      have h_pt := congr_fun h_slice x
      simpa [hG, Function.iterate_zero, Function.iterate_one] using h_pt
    rw [h_multi]
    exact le_trans (hM1 x hx 1) (le_max_right _ _)
  · -- α 2 = 1, others 0
    have hα_eq : α = fun k => if k = 2 then 1 else 0 := by
      ext j; fin_cases j <;> simp [hα0, hα1, hα2]
    have h_multi : multiPartial (fun w => g w i) α ((x, t) : ParabolicPoint) = axisDeriv 2 G x := by
      rw [hα_eq]
      have h_slice := multiPartial_slice (fun w => g w i) (fun k => if k = 2 then 1 else 0) t
      have h_pt := congr_fun h_slice x
      simpa [hG, Function.iterate_zero, Function.iterate_one] using h_pt
    rw [h_multi]
    exact le_trans (hM1 x hx 2) (le_max_right _ _)

end CIV

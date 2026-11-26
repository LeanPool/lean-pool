/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneLog
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Separation in the plane by continuous logarithms

This file links the components of the complement of a compact set `K` of the complex plane with
logarithms on `K`. This is Eilenberg's criterion: two points `a, b` outside `K` lie in the same
component of the complement if and only if $(z - a)/(z - b)$ has a continuous logarithm on `K`.
The route is the one of J. Dieudonné, *Foundations of Modern Analysis*, Appendix to Chapter IX.

- `hasLogOn_div_of_same_component`: points in one component give a logarithm, by moving one point
  to the other along a path.
- `eq_zero_of_hasLogOn_frontier`: the main obstruction. If `U` is a bounded open set around `a`
  and $(z - a)^m / h(z)$ has a logarithm on the frontier of `U`, where `h` has no zeros on the
  closure of `U`, then `m = 0`. Otherwise we could paste a function without zeros on the plane
  that equals $(z - a)^m$ on a big circle.
- `component_eq_of_hasLogOn`: the converse of the first item, for compact `K`.
- `component_eq_of_arc`: an arc does not separate the plane.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Complex Metric

local notation "𝕀" => unitInterval

/-- A component of the complement of a closed set is open. -/
theorem isOpen_component {K : Set ℂ} (hK : IsClosed K) (a : ℂ) :
    IsOpen (connectedComponentIn Kᶜ a) :=
  hK.isOpen_compl.connectedComponentIn

/-- A component of the complement of a closed set has its frontier in the set. -/
theorem frontier_component_subset {K : Set ℂ} (hK : IsClosed K) (a : ℂ) :
    frontier (connectedComponentIn Kᶜ a) ⊆ K := by
  intro x hx
  by_contra hxK
  have hU := isOpen_component hK a
  rw [hU.frontier_eq] at hx
  have hV := isOpen_component hK x
  have hxV : x ∈ connectedComponentIn Kᶜ x := mem_connectedComponentIn hxK
  obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp hx.1 _ hV hxV
  have h1 := connectedComponentIn_eq hyU
  have h2 := connectedComponentIn_eq hyV
  exact hx.2 (by rw [h1, ← h2]; exact hxV)

/-- The closure of a component lies in the component and the closed set. -/
theorem closure_component_subset {K : Set ℂ} (hK : IsClosed K) (a : ℂ) :
    closure (connectedComponentIn Kᶜ a) ⊆ connectedComponentIn Kᶜ a ∪ K := by
  intro x hx
  by_cases h : x ∈ connectedComponentIn Kᶜ a
  · exact Or.inl h
  · refine Or.inr (frontier_component_subset hK a ⟨hx, fun hi => h ?_⟩)
    exact interior_subset hi

/-- If `a, b` lie in one component of the complement of `K`, then $(z - a)/(z - b)$ has a
logarithm on `K`: move `b` to `a` along a path in the complement. -/
theorem hasLogOn_div_of_same_component {K : Set ℂ} (hK : IsClosed K) {a b : ℂ} (ha : a ∉ K)
    (hb : b ∈ connectedComponentIn Kᶜ a) :
    HasLogOn K fun z => (z - b) / (z - a) := by
  have hU := isOpen_component hK a
  have hconn : IsPathConnected (connectedComponentIn Kᶜ a) :=
    (hU.isConnected_iff_isPathConnected).mp (isConnected_connectedComponentIn_iff.mpr ha)
  obtain ⟨γ, hγ⟩ := hconn.joinedIn a (mem_connectedComponentIn ha) b hb
  have hγK : ∀ t, γ t ∉ K := fun t h => connectedComponentIn_subset _ _ (hγ t) h
  have hne : ∀ z ∈ K, z - a ≠ 0 := fun z hz h => ha (by rwa [sub_eq_zero.mp h] at hz)
  have h := hasLogOn_of_homotopy (K := K) (fun t z => (z - γ t) / (z - a))
    (by
      apply ContinuousOn.div
      · exact (continuous_snd.continuousOn).sub
          (γ.continuous.comp continuous_fst).continuousOn
      · exact (continuous_snd.continuousOn).sub continuousOn_const
      · rintro ⟨t, z⟩ ⟨-, hz⟩
        exact hne z hz)
    (fun z hz => by
      simp only [γ.source]
      exact div_self (hne z hz))
    (fun t z hz => div_ne_zero (fun h => hγK t (by rwa [sub_eq_zero.mp h] at hz)) (hne z hz))
  simpa using h

/-- **The obstruction.** Let `U` be a bounded open set containing `a`. Let `h` be continuous and
without zeros on the closure of `U`. If $(z - a)^m / h(z)$ has a logarithm on the frontier of `U`,
then `m = 0`. Extend the logarithm to the plane by the Tietze theorem. Then $h$ times the
exponential of the extension, on `U`, and $(z - a)^m$, off `U`, paste to a function without zeros
on the plane. It has a logarithm, which contradicts `eq_zero_of_hasLogOn_sphere` on a big circle
around `a`. -/
theorem eq_zero_of_hasLogOn_frontier {U : Set ℂ} {a : ℂ} {m : ℤ} {h : ℂ → ℂ}
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (ha : a ∈ U)
    (hh : ContinuousOn h (closure U)) (hne : ∀ z ∈ closure U, h z ≠ 0)
    (hlog : HasLogOn (frontier U) fun z => (z - a) ^ m / h z) : m = 0 := by
  classical
  obtain ⟨g₀, hg₀⟩ := hasLogOn_iff_subtype.mp hlog
  obtain ⟨G, hG⟩ := g₀.exists_restrict_eq isClosed_frontier
  have hGeq : ∀ z (hz : z ∈ frontier U), G z = g₀ ⟨z, hz⟩ := fun z hz => by
    rw [← hG]; rfl
  let F : ℂ → ℂ := fun z => if z ∈ U then h z * exp (G z) else (z - a) ^ m
  have haU : ∀ z ∈ closure Uᶜ, z - a ≠ 0 := by
    intro z hz hza
    rw [closure_compl] at hz
    apply hz
    rw [hU.interior_eq, sub_eq_zero.mp hza]
    exact ha
  have hF : Continuous F := by
    refine continuous_if ?_ ?_ ?_
    · intro z hz
      have hz' : z ∈ frontier U := hz
      have h1 := hg₀ ⟨z, hz'⟩
      have h2 : z ∈ closure U := hz'.1
      rw [hGeq z hz']
      change _ = (z - a) ^ m
      have h3 : (z - a) ^ m / h z = exp (g₀ ⟨z, hz'⟩) := h1
      rw [← h3]
      field_simp [hne z h2]
    · exact hh.mul (G.continuous.comp continuous_id |>.cexp).continuousOn
    · refine ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const) m ?_
      intro z hz
      exact Or.inl (haU z hz)
  have hFne : ∀ z, F z ≠ 0 := by
    intro z
    by_cases hz : z ∈ U
    · simp only [F, hz, ite_true]
      exact mul_ne_zero (hne z (subset_closure hz)) (exp_ne_zero _)
    · simp only [F, hz, ite_false]
      exact zpow_ne_zero _ (haU z (subset_closure hz))
  obtain ⟨R, hR⟩ := hb.subset_ball a
  have hRpos : 0 < R := by
    have := hR ha
    exact pos_of_mem_ball this
  refine eq_zero_of_hasLogOn_sphere (a := a) hRpos ?_
  refine ((hasLogOn_univ_of_ne_zero hF hFne).mono (subset_univ _)).congr fun z hz => ?_
  have hzU : z ∉ U := fun h' => by
    have h1 := hR h'
    rw [mem_ball] at h1
    rw [mem_sphere] at hz
    linarith
  simp [F, hzU]

/-- The complement of a closed disc around the origin is preconnected: it is the image of a
product of an interval and a line under polar coordinates. -/
theorem isPreconnected_compl_closedBall (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected (closedBall (0 : ℂ) R)ᶜ := by
  have h : (closedBall (0 : ℂ) R)ᶜ =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (Ioi R ×ˢ univ) := by
    ext z
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, mem_image, mem_prod,
      mem_Ioi, mem_univ, and_true, Prod.exists]
    constructor
    · intro hz
      exact ⟨‖z‖, arg z, hz, norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨r, θ, hr, rfl⟩
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (hR.trans_lt hr)]
      exact hr
  rw [h]
  refine ((isPreconnected_Ioi).prod isPreconnected_univ).image _ ?_
  apply Continuous.continuousOn
  fun_prop

/-- At most one component of the complement of a compact set is unbounded. -/
theorem component_bounded_or {K : Set ℂ} (hK : IsCompact K) {a b : ℂ} (ha : a ∉ K) (hb : b ∉ K)
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    Bornology.IsBounded (connectedComponentIn Kᶜ a) ∨
      Bornology.IsBounded (connectedComponentIn Kᶜ b) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R', hR'pos, hR'⟩ : ∃ R' : ℝ, 0 ≤ R' ∧ K ⊆ closedBall (0 : ℂ) R' :=
    ⟨max R 0, le_max_right _ _, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  have hE := isPreconnected_compl_closedBall R' hR'pos
  have hEK : (closedBall (0 : ℂ) R')ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hR'
  by_contra hcon
  push Not at hcon
  have key : ∀ c, c ∉ K → ¬ Bornology.IsBounded (connectedComponentIn Kᶜ c) →
      (closedBall (0 : ℂ) R')ᶜ ⊆ connectedComponentIn Kᶜ c := by
    intro c hc hunb
    have : ∃ x ∈ connectedComponentIn Kᶜ c, x ∈ (closedBall (0 : ℂ) R')ᶜ := by
      by_contra hno
      push Not at hno
      exact hunb ((isBounded_closedBall (x := (0 : ℂ)) (r := R')).subset fun x hx => by
        simpa using hno x hx)
    obtain ⟨x, hxc, hxE⟩ := this
    have h1 := hE.subset_connectedComponentIn hxE hEK
    rw [← connectedComponentIn_eq hxc] at h1
    exact h1
  have h1 := key a ha hcon.1
  have h2 := key b hb hcon.2
  obtain ⟨y, hy⟩ : ((closedBall (0 : ℂ) R')ᶜ).Nonempty := by
    refine ⟨((R' + 1 : ℝ) : ℂ), ?_⟩
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs,
      not_le]
    rw [abs_of_pos (by linarith)]
    linarith
  exact hab ((connectedComponentIn_eq (h1 hy)).trans (connectedComponentIn_eq (h2 hy)).symm)

/-- `b` does not lie in the closure of the component of `a`, when `b` lies in another component. -/
theorem notMem_closure_component {K : Set ℂ} (hK : IsClosed K) {a b : ℂ} (hb : b ∉ K)
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    b ∉ closure (connectedComponentIn Kᶜ a) := by
  intro h
  rcases closure_component_subset hK a h with h | h
  · exact hab (connectedComponentIn_eq h)
  · exact hb h

/-- Eilenberg's criterion, the hard direction: if $(z - a)/(z - b)$ has a logarithm on the compact
set `K`, then `a` and `b` lie in the same component of the complement of `K`. -/
theorem component_eq_of_hasLogOn {K : Set ℂ} (hK : IsCompact K) {a b : ℂ} (ha : a ∉ K)
    (hb : b ∉ K) (hlog : HasLogOn K fun z => (z - a) / (z - b)) :
    connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  by_contra hab
  have main : ∀ {a b : ℂ}, a ∉ K → b ∉ K →
      connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b →
      Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      HasLogOn K (fun z => (z - a) / (z - b)) → False := by
    intro a b ha hb hab hbd hlog
    have hne : ∀ z ∈ closure (connectedComponentIn Kᶜ a), z - b ≠ 0 := fun z hz h => by
      rw [sub_eq_zero] at h
      exact notMem_closure_component hK.isClosed hb hab (h ▸ hz)
    have := eq_zero_of_hasLogOn_frontier (m := 1) (isOpen_component hK.isClosed a) hbd
      (mem_connectedComponentIn ha)
      (h := fun z => z - b) (continuousOn_id.sub continuousOn_const) hne
      ((hlog.mono (frontier_component_subset hK.isClosed a)).congr fun z _ => by simp)
    exact one_ne_zero this
  rcases component_bounded_or hK ha hb hab with h | h
  · exact main ha hb hab h hlog
  · refine main hb ha (Ne.symm hab) h (hlog.inv.congr fun z _ => ?_)
    rw [inv_div]

/-- An arc does not separate the plane. -/
theorem component_eq_of_arc {L : Set ℂ} (φ : 𝕀 ≃ₜ L) {a b : ℂ} (ha : a ∉ L) (hb : b ∉ L) :
    connectedComponentIn Lᶜ a = connectedComponentIn Lᶜ b := by
  have hcomp : IsCompact L := by
    have : CompactSpace L := φ.compactSpace
    exact isCompact_iff_compactSpace.mpr this
  refine component_eq_of_hasLogOn hcomp ha hb (hasLogOn_of_arc φ ?_ ?_)
  · refine (continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const) ?_
    intro z hz h
    exact hb (by rwa [sub_eq_zero.mp h] at hz)
  · intro z hz
    refine div_ne_zero (fun h => ha ?_) (fun h => hb ?_)
    · rwa [sub_eq_zero.mp h] at hz
    · rwa [sub_eq_zero.mp h] at hz

/-- A preconnected set that meets a set and its complement meets the frontier of the set. -/
theorem inter_frontier_nonempty_of_isPreconnected {T : Type*} [TopologicalSpace T] {C U : Set T}
    (hC : IsPreconnected C) (hin : (C ∩ U).Nonempty) (hout : (C ∩ Uᶜ).Nonempty) :
    (C ∩ frontier U).Nonempty := by
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  obtain ⟨x, hxC, hxU⟩ := hin
  obtain ⟨y, hyC, hyU⟩ := hout
  have hin' : x ∈ interior U := by
    by_contra h
    have : x ∈ C ∩ frontier U := ⟨hxC, subset_closure hxU, h⟩
    rw [hcon] at this
    exact this
  have hout' : y ∉ closure U := fun h => by
    have : y ∈ C ∩ frontier U := ⟨hyC, h, fun h' => hyU (interior_subset h')⟩
    rw [hcon] at this
    exact this
  have hdisj : Disjoint (interior U) (closure U)ᶜ :=
    Set.disjoint_left.mpr fun z hz hz' => hz' (subset_closure (interior_subset hz))
  have hsub : C ⊆ interior U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases h : z ∈ interior U
    · exact Or.inl h
    · refine Or.inr fun h' => ?_
      have : z ∈ C ∩ frontier U := ⟨hz, h', h⟩
      rw [hcon] at this
      exact this
  have := hC.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hsub
    ⟨x, hxC, hin'⟩ hyC
  exact hout' (subset_closure (interior_subset this))

end GraphMinor.Surface

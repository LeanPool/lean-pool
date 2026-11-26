/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneSeparation
public import LeanPool.GraphMinor.Surface.TopologyStatements
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Jordan curve theorem in the complex plane

An `O`-arc `F` of the complex plane is the union of two arcs with common ends `p, q`.

* **At least two components** (`not_isPreconnected_compl_union`). This is a Mayer–Vietoris argument
  on the complement. The function $(z - q)/(z - p)$ has a logarithm off each of the two arcs: move
  `p` to `q` along the arc. If the complement of `F` were connected, the two logarithms would differ
  by a constant on it, so they would paste to a logarithm on the plane without `p, q`. That is false
  on a small circle around `p`.
* **At most two components** (`exists_zpow_mul_zpow_hasLogOn`, `component_eq_or_eq`). Two functions
  on `F` without zeros have a nontrivial product of powers with a logarithm, because a function
  has logarithms on both arcs and these fail to agree by one integer. With three components this
  contradicts the obstruction `eq_zero_of_hasLogOn_frontier`.
* **The frontier** (`subset_frontier_component`). A function without zeros has a logarithm on `F`
  minus a point. So if `x ∈ F` were not in the frontier of a component, then by Eilenberg's
  criterion the frontier would not separate the two components.

The route follows Eilenberg's criterion, as in J. Dieudonné, *Foundations of Modern Analysis*,
Appendix to Chapter IX. The Mayer–Vietoris step replaces the approximation argument there.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Complex Metric

local notation "𝕀" => unitInterval

universe u

/-- The function $(z - \alpha(1)) / (z - \alpha(0))$ has a logarithm off the path `α`. -/
theorem hasLogOn_compl_range (α : C(𝕀, ℂ)) :
    HasLogOn (range α)ᶜ fun z => (z - α 1) / (z - α 0) := by
  have hne : ∀ t, ∀ z ∈ (range α)ᶜ, z - α t ≠ 0 := fun t z hz h =>
    hz ⟨t, (sub_eq_zero.mp h).symm⟩
  refine hasLogOn_of_homotopy (K := (range α)ᶜ) (fun t z => (z - α t) / (z - α 0)) ?_
    (fun z hz => div_self (hne 0 z hz)) (fun t z hz => div_ne_zero (hne t z hz) (hne 0 z hz))
  apply ContinuousOn.div
  · exact continuous_snd.continuousOn.sub (α.continuous.comp continuous_fst).continuousOn
  · exact continuous_snd.continuousOn.sub continuousOn_const
  · rintro ⟨t, z⟩ ⟨-, hz⟩
    exact hne 0 z hz

/-- `z - q` has a logarithm on a small circle around `p`. -/
theorem hasLogOn_sub_sphere {p q : ℂ} {ρ : ℝ} (hpq : ρ < ‖p - q‖) (hρ : 0 < ρ) :
    HasLogOn (sphere p ρ) fun z => z - q := by
  have hne : p - q ≠ 0 := norm_pos_iff.mp (hρ.trans hpq)
  have h : HasLogOn (sphere p ρ) fun z => (z - q) / (p - q) := by
    refine hasLogOn_of_slitPlane (by fun_prop) fun z hz => ?_
    rw [mem_sphere, dist_eq_norm] at hz
    have h1 : (z - q) / (p - q) = 1 + (z - p) / (p - q) := by field_simp; ring
    rw [h1]
    have h2 : ‖(z - p) / (p - q)‖ < 1 := by
      rw [norm_div, hz, div_lt_one (hρ.trans hpq)]
      exact hpq
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have h3 := abs_lt.mp ((abs_re_le_norm _).trans_lt h2)
    simp only [add_re, one_re]
    linarith [h3.1]
  refine (h.mul (hasLogOn_const hne)).congr fun z _ => ?_
  field_simp

/-- **At least two components.** The complement of the union of two paths with the same ends
`p ≠ q` and no other common point is not connected. -/
theorem not_isPreconnected_compl_union {α β : C(𝕀, ℂ)} {p q : ℂ} (hα0 : α 0 = p) (hα1 : α 1 = q)
    (hβ0 : β 0 = p) (hβ1 : β 1 = q) (hpq : p ≠ q) (hinter : range α ∩ range β = {p, q}) :
    ¬ IsPreconnected (range α ∪ range β)ᶜ := by
  classical
  intro hconn
  have hAc : IsClosed (range α) := (isCompact_range α.continuous).isClosed
  have hBc : IsClosed (range β) := (isCompact_range β.continuous).isClosed
  obtain ⟨gA, hgA, hfA⟩ := hasLogOn_compl_range α
  obtain ⟨gB, hgB, hfB⟩ := hasLogOn_compl_range β
  simp only [hα0, hα1] at hfA
  simp only [hβ0, hβ1] at hfB
  have hbdd : Bornology.IsBounded (range α ∪ range β) :=
    (isCompact_range α.continuous).isBounded.union (isCompact_range β.continuous).isBounded
  obtain ⟨z₀, hz₀⟩ : ((range α ∪ range β)ᶜ).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    rw [hemp] at hbdd
    exact NormedSpace.unbounded_univ ℝ ℂ hbdd
  have hsplit : ∀ {z}, z ∈ (range α ∪ range β)ᶜ → z ∈ (range α)ᶜ ∧ z ∈ (range β)ᶜ := fun hz =>
    ⟨fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩
  have hratio : ∀ z ∈ (range α ∪ range β)ᶜ, exp (gA z) = exp (gB z) := fun z hz => by
    rw [← hfA z (hsplit hz).1, ← hfB z (hsplit hz).2]
  set c := gA z₀ - gB z₀ with hc
  have hexpc : exp c = 1 := by
    rw [hc, exp_sub, hratio z₀ hz₀, div_self (exp_ne_zero _)]
  have hUo : IsOpen (range α ∪ range β)ᶜ := (hAc.union hBc).isOpen_compl
  have hdiff : ∀ z ∈ (range α ∪ range β)ᶜ, gA z = gB z + c := by
    intro z hz
    have hcontA : ContinuousOn gA (range α ∪ range β)ᶜ := hgA.mono fun w hw => (hsplit hw).1
    have hcontB : ContinuousOn gB (range α ∪ range β)ᶜ := hgB.mono fun w hw => (hsplit hw).2
    have h := eq_of_exp_eq_one (g := fun w => gA w - gB w) hconn (hcontA.sub hcontB)
      (fun w hw => by simp only [exp_sub, hratio w hw]; exact div_self (exp_ne_zero _)) hz hz₀
    rw [hc]
    linear_combination h
  let L : ℂ → ℂ := fun z => if z ∈ range α then gB z + c else gA z
  set ρ := ‖p - q‖ / 2 with hρdef
  have hpqpos : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
  have hρ : 0 < ρ := by positivity
  have hρlt : ρ < ‖p - q‖ := by rw [hρdef]; linarith
  have hnotp : ∀ z ∈ sphere p ρ, z ≠ p := fun z hz h => by
    rw [mem_sphere, h, dist_self] at hz
    exact hρ.ne hz
  have hnotq : ∀ z ∈ sphere p ρ, z ≠ q := fun z hz h => by
    rw [mem_sphere, h, dist_eq_norm, norm_sub_rev] at hz
    exact hρlt.ne hz.symm
  have hLA : ∀ z ∈ (range α)ᶜ, L =ᶠ[𝓝 z] gA := fun z hz => by
    filter_upwards [hAc.isOpen_compl.mem_nhds hz] with w hw
    have hw' : w ∉ range α := hw
    simp only [L, hw', ite_false]
  have hLB : ∀ z ∈ (range β)ᶜ, L =ᶠ[𝓝 z] fun w => gB w + c := fun z hz => by
    filter_upwards [hBc.isOpen_compl.mem_nhds hz] with w hw
    by_cases h : w ∈ range α
    · simp only [L, h, ite_true]
    · simp only [L, h, ite_false]
      exact hdiff w fun h' => h'.elim h hw
  have hnotB : ∀ z ∈ sphere p ρ, z ∈ range α → z ∈ (range β)ᶜ := fun z hz hza hzb => by
    have : z ∈ ({p, q} : Set ℂ) := hinter ▸ ⟨hza, hzb⟩
    rcases this with h | h
    · exact hnotp z hz h
    · exact hnotq z hz h
  have hLcont : ContinuousOn L (sphere p ρ) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    by_cases hza : z ∈ range α
    · have hzb := hnotB z hz hza
      exact (((hgB.continuousAt (hBc.isOpen_compl.mem_nhds hzb)).add continuousAt_const)).congr
        (hLB z hzb).symm
    · exact (hgA.continuousAt (hAc.isOpen_compl.mem_nhds hza)).congr (hLA z hza).symm
  have hlogr : HasLogOn (sphere p ρ) fun z => (z - q) / (z - p) := by
    refine ⟨L, hLcont, fun z hz => ?_⟩
    by_cases hza : z ∈ range α
    · simp only [L, hza, ite_true]
      rw [exp_add, hexpc, mul_one]
      exact hfB z (hnotB z hz hza)
    · simp only [L, hza, ite_false]
      exact hfA z hza
  have hfinal : HasLogOn (sphere p ρ) fun z => (z - p) ^ (1 : ℤ) := by
    refine ((hasLogOn_sub_sphere hρlt hρ).div hlogr).congr fun z hz => ?_
    have h1 : z - p ≠ 0 := sub_ne_zero.mpr (hnotp z hz)
    have h2 : z - q ≠ 0 := sub_ne_zero.mpr (hnotq z hz)
    field_simp
  exact one_ne_zero (eq_zero_of_hasLogOn_sphere hρ hfinal)

/-- Two logarithms on closed sets that agree on the common points paste. -/
theorem hasLogOn_union {T : Type u} [TopologicalSpace T] {A B : Set T} (hA : IsClosed A)
    (hB : IsClosed B) {f gA gB : T → ℂ} (hgA : ContinuousOn gA A) (hgB : ContinuousOn gB B)
    (hfA : ∀ x ∈ A, f x = exp (gA x)) (hfB : ∀ x ∈ B, f x = exp (gB x))
    (hag : ∀ x ∈ A ∩ B, gA x = gB x) : HasLogOn (A ∪ B) f := by
  classical
  let g : T → ℂ := fun x => if x ∈ A then gA x else gB x
  have h1 : ContinuousOn g A := hgA.congr fun x hx => by simp [g, hx]
  have h2 : ContinuousOn g B := hgB.congr fun x hx => by
    by_cases h : x ∈ A
    · simp only [g, h, ite_true]
      exact hag x ⟨h, hx⟩
    · simp [g, h]
  refine ⟨g, h1.union_of_isClosed h2 hA hB, ?_⟩
  rintro x (hx | hx)
  · simp only [g, hx, ite_true]
    exact hfA x hx
  · by_cases h : x ∈ A
    · simp only [g, h, ite_true]
      exact hfA x h
    · simp only [g, h, ite_false]
      exact hfB x hx

/-- Two functions with logarithms on each of two closed sets that meet in two points have a
nontrivial product of powers with a logarithm on the union. Each function has one integer
obstruction: how much its two logarithms fail to agree at `q` once they agree at `p`. -/
theorem exists_zpow_mul_zpow_hasLogOn {T : Type u} [TopologicalSpace T] {A B : Set T}
    (hA : IsClosed A) (hB : IsClosed B) {p q : T} (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B)
    (hinter : A ∩ B = {p, q}) {f₁ f₂ : T → ℂ}
    (h1A : HasLogOn A f₁) (h1B : HasLogOn B f₁) (h2A : HasLogOn A f₂) (h2B : HasLogOn B f₂) :
    ∃ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) ∧ HasLogOn (A ∪ B) fun x => f₁ x ^ m₁ * f₂ x ^ m₂ := by
  obtain ⟨g1A, c1A, e1A⟩ := h1A
  obtain ⟨g1B, c1B, e1B⟩ := h1B
  obtain ⟨g2A, c2A, e2A⟩ := h2A
  obtain ⟨g2B, c2B, e2B⟩ := h2B
  have hint : ∀ {f gA gB : T → ℂ}, (∀ x ∈ A, f x = exp (gA x)) → (∀ x ∈ B, f x = exp (gB x)) →
      ∀ x ∈ A ∩ B, ∃ n : ℤ, gA x - gB x = n * (2 * Real.pi * I) := by
    intro f gA gB hA hB x hx
    refine Complex.exp_eq_one_iff.mp ?_
    rw [exp_sub, ← hA x hx.1, ← hB x hx.2]
    have : exp (gB x) ≠ 0 := exp_ne_zero _
    rw [← hB x hx.2] at this
    exact div_self this
  obtain ⟨n1p, h1p⟩ := hint e1A e1B p hp
  obtain ⟨n1q, h1q⟩ := hint e1A e1B q hq
  obtain ⟨n2p, h2p⟩ := hint e2A e2B p hp
  obtain ⟨n2q, h2q⟩ := hint e2A e2B q hq
  -- The obstructions of the two functions.
  set n₁ := n1q - n1p
  set n₂ := n2q - n2p
  obtain ⟨m₁, m₂, hm, hzero⟩ : ∃ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) ∧ m₁ * n₁ + m₂ * n₂ = 0 := by
    by_cases h : n₁ = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h]⟩
    · exact ⟨n₂, -n₁, Or.inr (neg_ne_zero.mpr h), by ring⟩
  let c : ℂ := ((m₁ * n1p + m₂ * n2p : ℤ) : ℂ) * (2 * Real.pi * I)
  have hexpc : exp c = 1 := Complex.exp_eq_one_iff.mpr ⟨_, rfl⟩
  have hzero' : (m₁ : ℂ) * ((n1q : ℂ) - n1p) + (m₂ : ℂ) * ((n2q : ℂ) - n2p) = 0 := by
    have : ((m₁ * n₁ + m₂ * n₂ : ℤ) : ℂ) = 0 := by rw [hzero]; simp
    simpa [n₁, n₂] using this
  refine ⟨m₁, m₂, hm, ?_⟩
  refine hasLogOn_union (gA := fun x => (m₁ : ℂ) * g1A x + (m₂ : ℂ) * g2A x)
    (gB := fun x => (m₁ : ℂ) * g1B x + (m₂ : ℂ) * g2B x + c) hA hB
    ((continuousOn_const.mul c1A).add (continuousOn_const.mul c2A))
    (((continuousOn_const.mul c1B).add (continuousOn_const.mul c2B)).add continuousOn_const)
    (fun x hx => by
      simp only [e1A x hx, e2A x hx, exp_add, exp_int_mul])
    (fun x hx => by
      simp only [e1B x hx, e2B x hx, exp_add, exp_int_mul, hexpc, mul_one]) ?_
  rw [hinter]
  rintro x (rfl | rfl)
  · simp only [c]
    push_cast
    linear_combination (m₁ : ℂ) * h1p + (m₂ : ℂ) * h2p
  · simp only [c]
    push_cast
    linear_combination (m₁ : ℂ) * h1q + (m₂ : ℂ) * h2q +
      (2 * Real.pi * I) * hzero'

/-- A unit complex number other than `-1` lies in the slit plane. -/
theorem circle_mem_slitPlane {z : Circle} (hz : (z : ℂ) ≠ -1) : (z : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h3 : normSq (z : ℂ) = 1 := Circle.normSq_coe z
  rw [normSq_apply, h2] at h3
  have h4 : (z : ℂ).re = -1 := by nlinarith
  exact hz (Complex.ext (by simp [h4]) (by simp [h2]))

/-- A function without zeros has a logarithm on an `O`-arc minus a point: the rest of the arc is
an open interval. -/
theorem hasLogOn_diff_point {T : Type u} [TopologicalSpace T] {F : Set T} (φ : Circle ≃ₜ F)
    {f : T → ℂ} (hf : ContinuousOn f F) (hne : ∀ x ∈ F, f x ≠ 0) {x : T} (hx : x ∈ F) :
    HasLogOn (F \ {x}) f := by
  set w : Circle := φ.symm ⟨x, hx⟩ * Circle.exp Real.pi with hw
  let u : ℝ → ℂ := fun t => f (φ (w * Circle.exp t) : T)
  have hu : Continuous u := hf.comp_continuous (by fun_prop) fun t => (φ _).2
  obtain ⟨l, hl, hul⟩ := hasLogOn_univ_of_ne_zero hu fun t => hne _ (φ _).2
  have hlc : Continuous l := continuousOn_univ.mp hl
  let c : (F \ {x} : Set T) → Circle := fun y => φ.symm ⟨y.1, y.2.1⟩ * w⁻¹
  have hc : Continuous c := by fun_prop
  have hsl : ∀ y, ((c y : Circle) : ℂ) ∈ slitPlane := by
    intro y
    refine circle_mem_slitPlane fun h => y.2.2 ?_
    have h1 : c y = Circle.exp Real.pi := by
      apply Circle.ext
      rw [h, Circle.coe_exp, exp_pi_mul_I]
    have h2 : φ.symm ⟨y.1, y.2.1⟩ = φ.symm ⟨x, hx⟩ := by
      have h3 : φ.symm ⟨y.1, y.2.1⟩ = c y * w := by simp [c]
      rw [h3, h1, hw, mul_comm, mul_assoc]
      have h4 : Circle.exp Real.pi * Circle.exp Real.pi = 1 := by
        rw [← Circle.exp_add, ← two_mul, Circle.exp_two_pi]
      rw [h4, mul_one]
    have h5 := φ.symm.injective h2
    exact congr_arg Subtype.val h5
  rw [hasLogOn_iff_subtype]
  refine ⟨⟨fun y => l (arg (c y)), ?_⟩, fun y => ?_⟩
  · refine hlc.comp (continuous_iff_continuousAt.mpr fun y => ?_)
    have hcc : Continuous fun y => ((c y : Circle) : ℂ) := by fun_prop
    exact ContinuousAt.comp (f := fun y => ((c y : Circle) : ℂ)) (g := arg)
      (continuousAt_arg (hsl y)) hcc.continuousAt
  · have h1 := hul (arg (c y)) (mem_univ _)
    have h2 : w * Circle.exp (arg (c y)) = φ.symm ⟨y.1, y.2.1⟩ := by
      rw [Circle.exp_arg]
      simp [c]
    simp only [u, h2, Homeomorph.apply_symm_apply] at h1
    exact h1

variable {F : Set ℂ}

/-- The two semicircles of the unit circle cover it. -/
private theorem exists_semicircle (w : Circle) :
    ∃ t : 𝕀, w = Circle.exp (Real.pi * t) ∨ w = Circle.exp (-(Real.pi * t)) := by
  have hpi := Real.pi_pos
  have hdiv : ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ Real.pi → θ / Real.pi ∈ unitInterval := fun h0 h1 =>
    ⟨div_nonneg h0 hpi.le, (div_le_one hpi).mpr h1⟩
  rcases le_total 0 (arg (w : ℂ)) with h | h
  · refine ⟨⟨_, hdiv h (arg_le_pi _)⟩, Or.inl ?_⟩
    simp only
    rw [mul_div_cancel₀ _ hpi.ne', Circle.exp_arg]
  · refine ⟨⟨_, hdiv (neg_nonneg.mpr h) (by linarith [neg_pi_lt_arg (w : ℂ)])⟩, Or.inr ?_⟩
    simp only
    rw [mul_div_cancel₀ _ hpi.ne', neg_neg, Circle.exp_arg]

/-- The two semicircles of the unit circle meet only at `1` and `-1`. -/
private theorem semicircle_inter {s t : 𝕀} (h : Circle.exp (Real.pi * s) =
    Circle.exp (-(Real.pi * t))) :
    (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hpi := Real.pi_pos
  have hs := s.2
  have ht := t.2
  have hst : (s : ℝ) + t = 2 * m := by
    have : Real.pi * ((s : ℝ) + t) = Real.pi * (2 * m) := by linarith
    exact mul_left_cancel₀ hpi.ne' this
  have hm0 : (0 : ℝ) ≤ m := by linarith [hs.1, ht.1]
  have hm1 : (m : ℝ) ≤ 1 := by linarith [hs.2, ht.2]
  have hm0' : 0 ≤ m := by exact_mod_cast hm0
  have hm1' : m ≤ 1 := by exact_mod_cast hm1
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  · left
    simp only [Int.cast_zero, mul_zero] at hst
    exact ⟨Subtype.ext (show (s : ℝ) = 0 by linarith [ht.1, hs.1]),
      Subtype.ext (show (t : ℝ) = 0 by linarith [ht.1, hs.1])⟩
  · right
    simp only [Int.cast_one, mul_one] at hst
    exact ⟨Subtype.ext (show (s : ℝ) = 1 by linarith [ht.2, hs.2]),
      Subtype.ext (show (t : ℝ) = 1 by linarith [ht.2, hs.2])⟩

/-- The upper semicircle of the `O`-arc given by `φ`. -/
noncomputable def upperArc (φ : Circle ≃ₜ F) : C(𝕀, ℂ) :=
  ⟨fun t => (φ (Circle.exp (Real.pi * t))).1, by fun_prop⟩

/-- The lower semicircle of the `O`-arc given by `φ`. -/
noncomputable def lowerArc (φ : Circle ≃ₜ F) : C(𝕀, ℂ) :=
  ⟨fun t => (φ (Circle.exp (-(Real.pi * t)))).1, by fun_prop⟩

theorem lowerArc_zero (φ : Circle ≃ₜ F) : lowerArc φ 0 = upperArc φ 0 := by
  change (φ (Circle.exp (-(Real.pi * ((0 : 𝕀) : ℝ))))).1 = (φ (Circle.exp (Real.pi *
    ((0 : 𝕀) : ℝ)))).1
  simp

theorem lowerArc_one (φ : Circle ≃ₜ F) : lowerArc φ 1 = upperArc φ 1 := by
  have h3 : Circle.exp (-(Real.pi * ((1 : 𝕀) : ℝ))) = Circle.exp (Real.pi * ((1 : 𝕀) : ℝ)) :=
    Circle.exp_eq_exp.mpr ⟨-1, by push_cast; ring⟩
  change (φ (Circle.exp (-(Real.pi * ((1 : 𝕀) : ℝ))))).1 = (φ (Circle.exp (Real.pi *
    ((1 : 𝕀) : ℝ)))).1
  rw [h3]

theorem range_upper_union_lower (φ : Circle ≃ₜ F) :
    range (upperArc φ) ∪ range (lowerArc φ) = F := by
  ext x
  constructor
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> exact (φ _).2
  · intro hx
    obtain ⟨t, ht | ht⟩ := exists_semicircle (φ.symm ⟨x, hx⟩)
    · refine Or.inl ⟨t, ?_⟩
      change (φ (Circle.exp (Real.pi * t))).1 = x
      rw [← ht]; simp
    · refine Or.inr ⟨t, ?_⟩
      change (φ (Circle.exp (-(Real.pi * t)))).1 = x
      rw [← ht]; simp

theorem range_upper_inter_lower (φ : Circle ≃ₜ F) :
    range (upperArc φ) ∩ range (lowerArc φ) = {upperArc φ 0, upperArc φ 1} := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    have h : Circle.exp (Real.pi * s) = Circle.exp (-(Real.pi * t)) :=
      φ.injective (Subtype.ext ht.symm)
    rcases semicircle_inter h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have h1 := lowerArc_zero φ
    have h2 := lowerArc_one φ
    rintro (rfl | rfl)
    · exact ⟨⟨0, rfl⟩, ⟨0, h1⟩⟩
    · exact ⟨⟨1, rfl⟩, ⟨1, h2⟩⟩

theorem upperArc_zero_ne_one (φ : Circle ≃ₜ F) : upperArc φ 0 ≠ upperArc φ 1 := by
  intro h
  have h1 : Circle.exp (Real.pi * ((0 : 𝕀) : ℝ)) = Circle.exp (Real.pi * ((1 : 𝕀) : ℝ)) :=
    φ.injective (Subtype.ext h)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
  simp only [Icc.coe_zero, mul_zero, Icc.coe_one, mul_one] at hm
  have hpi := Real.pi_pos
  have h2 : (2 * m + 1 : ℝ) = 0 := by
    have : Real.pi * (2 * m + 1) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hpi.ne'
  have h3 : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast h2
  omega

theorem isCompact_of_oArc (φ : Circle ≃ₜ F) : IsCompact F := by
  have : CompactSpace F := φ.compactSpace
  exact isCompact_iff_compactSpace.mpr this

/-- A function on an `O`-arc without zeros has a logarithm on each semicircle: a semicircle is a
subset of the arc minus a point. -/
private theorem hasLogOn_semicircles (φ : Circle ≃ₜ F) {f : ℂ → ℂ} (hf : ContinuousOn f F)
    (hne : ∀ x ∈ F, f x ≠ 0) :
    HasLogOn (range (upperArc φ)) f ∧ HasLogOn (range (lowerArc φ)) f := by
  let m : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hm0 : m ≠ 0 := fun h => by
    have := congr_arg Subtype.val h
    norm_num [m] at this
  have hm1 : m ≠ 1 := fun h => by
    have := congr_arg Subtype.val h
    norm_num [m] at this
  constructor
  · refine (hasLogOn_diff_point φ hf hne (x := lowerArc φ m) (φ _).2).mono ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨(φ _).2, fun h => ?_⟩
    have h' : Circle.exp (Real.pi * t) = Circle.exp (-(Real.pi * m)) :=
      φ.injective (Subtype.ext h)
    rcases semicircle_inter h' with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact hm0 h2
    · exact hm1 h2
  · refine (hasLogOn_diff_point φ hf hne (x := upperArc φ m) (φ _).2).mono ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨(φ _).2, fun h => ?_⟩
    have h' : Circle.exp (Real.pi * m) = Circle.exp (-(Real.pi * t)) :=
      (φ.injective (Subtype.ext h)).symm
    rcases semicircle_inter h' with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact hm0 h2
    · exact hm1 h2

/-- The function $(z - a) / (z - b)$ is continuous and without zeros off `a, b`. -/
private theorem div_sub_continuousOn {K : Set ℂ} {a b : ℂ} (hb : b ∉ K) :
    ContinuousOn (fun z => (z - a) / (z - b)) K := by
  refine (continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const) ?_
  intro z hz h
  exact hb (by rwa [sub_eq_zero.mp h] at hz)

private theorem div_sub_ne_zero {K : Set ℂ} {a b : ℂ} (ha : a ∉ K) (hb : b ∉ K) :
    ∀ z ∈ K, (z - a) / (z - b) ≠ 0 := by
  intro z hz
  refine div_ne_zero (fun h => ha ?_) (fun h => hb ?_)
  · rwa [sub_eq_zero.mp h] at hz
  · rwa [sub_eq_zero.mp h] at hz

/-- Let `a, b, c` lie in three different components of the complement of the `O`-arc `F`, with the
component of `a` bounded. Then the exponent `m₁` of any logarithm below vanishes. -/
private theorem exponent_eq_zero (hF : IsClosed F) {a b c : ℂ} (hb : b ∉ F) (hc : c ∉ F)
    (ha : a ∉ F) (hbdd : Bornology.IsBounded (connectedComponentIn Fᶜ a))
    (hab : connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ b)
    (hac : connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ c) {m₁ m₂ : ℤ}
    (hlog : HasLogOn F fun z => ((z - a) / (z - c)) ^ m₁ * ((z - b) / (z - c)) ^ m₂) : m₁ = 0 := by
  have hbU := notMem_closure_component hF hb hab
  have hcU := notMem_closure_component hF hc hac
  have hbne : ∀ z ∈ closure (connectedComponentIn Fᶜ a), z - b ≠ 0 := fun z hz h => by
    rw [sub_eq_zero] at h
    exact hbU (h ▸ hz)
  have hcne : ∀ z ∈ closure (connectedComponentIn Fᶜ a), z - c ≠ 0 := fun z hz h => by
    rw [sub_eq_zero] at h
    exact hcU (h ▸ hz)
  refine eq_zero_of_hasLogOn_frontier (isOpen_component hF a) hbdd (mem_connectedComponentIn ha)
    (h := fun z => (z - c) ^ m₁ * (z - b) ^ (-m₂) * (z - c) ^ m₂) ?_ ?_
    ((hlog.mono (frontier_component_subset hF a)).congr fun z hz => ?_)
  · refine ((ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const) m₁
      fun z hz => Or.inl (hcne z hz)).mul (ContinuousOn.zpow₀
      (continuousOn_id.sub continuousOn_const) (-m₂) fun z hz => Or.inl (hbne z hz))).mul
      (ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const) m₂
      fun z hz => Or.inl (hcne z hz))
  · intro z hz
    exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (hcne z hz)) (zpow_ne_zero _ (hbne z hz)))
      (zpow_ne_zero _ (hcne z hz))
  · have hzcl : z ∈ closure (connectedComponentIn Fᶜ a) := by
      exact (frontier_subset_closure hz)
    have h1 := hcne z hzcl
    have h2 := hbne z hzcl
    rw [div_zpow, div_zpow, zpow_neg]
    have h3 := zpow_ne_zero m₁ h1
    have h4 := zpow_ne_zero m₂ h1
    have h5 := zpow_ne_zero m₂ h2
    field_simp

/-- **At most two components.** Three different components of the complement of an `O`-arc do
not exist. -/
theorem component_eq_or_eq (φ : Circle ≃ₜ F) {a b c : ℂ} (ha : a ∉ F) (hb : b ∉ F) (hc : c ∉ F)
    (hab : connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ b)
    (hac : connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ c)
    (hbc : connectedComponentIn Fᶜ b ≠ connectedComponentIn Fᶜ c) : False := by
  have hcomp := isCompact_of_oArc φ
  have hF := hcomp.isClosed
  have main : ∀ {a b c : ℂ}, a ∉ F → b ∉ F → c ∉ F →
      connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ b →
      connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ c →
      connectedComponentIn Fᶜ b ≠ connectedComponentIn Fᶜ c →
      Bornology.IsBounded (connectedComponentIn Fᶜ a) →
      Bornology.IsBounded (connectedComponentIn Fᶜ b) → False := by
    intro a b c ha hb hc hab hac hbc hba hbb
    obtain ⟨h1A, h1B⟩ := hasLogOn_semicircles φ (div_sub_continuousOn (a := a) hc)
      (div_sub_ne_zero ha hc)
    obtain ⟨h2A, h2B⟩ := hasLogOn_semicircles φ (div_sub_continuousOn (a := b) hc)
      (div_sub_ne_zero hb hc)
    have hA : IsClosed (range (upperArc φ)) := (isCompact_range (upperArc φ).continuous).isClosed
    have hB : IsClosed (range (lowerArc φ)) := (isCompact_range (lowerArc φ).continuous).isClosed
    have hinter := range_upper_inter_lower φ
    have hp : upperArc φ 0 ∈ range (upperArc φ) ∩ range (lowerArc φ) := by rw [hinter]; simp
    have hq : upperArc φ 1 ∈ range (upperArc φ) ∩ range (lowerArc φ) := by rw [hinter]; simp
    obtain ⟨m₁, m₂, hm, hlog⟩ := exists_zpow_mul_zpow_hasLogOn hA hB hp hq hinter h1A h1B h2A h2B
    rw [range_upper_union_lower] at hlog
    rcases hm with hm | hm
    · exact hm (exponent_eq_zero hF hb hc ha hba hab hac hlog)
    · refine hm (exponent_eq_zero (m₂ := m₁) hF ha hc hb hbb hab.symm hbc ?_)
      exact hlog.congr fun z _ => mul_comm _ _
  rcases component_bounded_or hcomp ha hb hab with h1 | h1
  · rcases component_bounded_or hcomp hb hc hbc with h2 | h2
    · exact main ha hb hc hab hac hbc h1 h2
    · exact main ha hc hb hac hab hbc.symm h1 h2
  · rcases component_bounded_or hcomp ha hc hac with h2 | h2
    · exact main ha hb hc hab hac hbc h2 h1
    · exact main hb hc ha hbc hab.symm hac.symm h1 h2

/-- The frontier of a component of the complement of an `O`-arc, when there are two components,
is the whole arc. If `x` were missing, the frontier `K` would lie in the arc minus `x`, so the
function $(z - a)/(z - b)$ would have a logarithm on `K`, and `a, b` would lie in one component of
the complement of `K`. But a connected set from `a` to `b` must meet the frontier `K`. -/
theorem subset_frontier_component (φ : Circle ≃ₜ F) {a b : ℂ} (ha : a ∉ F) (hb : b ∉ F)
    (hab : connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ b) :
    F ⊆ frontier (connectedComponentIn Fᶜ a) := by
  intro x hx
  by_contra hxU
  have hF := (isCompact_of_oArc φ).isClosed
  set U := connectedComponentIn Fᶜ a with hUdef
  have hUo : IsOpen U := isOpen_component hF a
  have hsub : frontier U ⊆ F := frontier_component_subset hF a
  have hK : IsCompact (frontier U) := (isCompact_of_oArc φ).of_isClosed_subset isClosed_frontier
    hsub
  have haU : a ∈ U := mem_connectedComponentIn ha
  have hbU : b ∉ U := fun h => hab (connectedComponentIn_eq h)
  have hlog : HasLogOn (frontier U) fun z => (z - a) / (z - b) :=
    (hasLogOn_diff_point φ (div_sub_continuousOn hb) (div_sub_ne_zero ha hb) hx).mono
      fun y hy => ⟨hsub hy, fun h => hxU (h ▸ hy)⟩
  have haK : a ∉ frontier U := fun h => ha (hsub h)
  have hbK : b ∉ frontier U := fun h => hb (hsub h)
  have heq := component_eq_of_hasLogOn hK haK hbK hlog
  have hbC : b ∈ connectedComponentIn (frontier U)ᶜ a := by
    rw [heq]; exact mem_connectedComponentIn hbK
  have hC := isPreconnected_connectedComponentIn (F := (frontier U)ᶜ) (x := a)
  obtain ⟨y, hy1, hy2⟩ := inter_frontier_nonempty_of_isPreconnected hC
    ⟨a, mem_connectedComponentIn haK, haU⟩ ⟨b, hbC, hbU⟩
  exact connectedComponentIn_subset _ _ hy1 hy2

/-- If `U, V` are disjoint nonempty open preconnected sets with union `X`, then the components of
`X` are `U` and `V`. -/
theorem componentsIn_eq_pair {T : Type u} [TopologicalSpace T] {X U V : Set T} (hU : IsOpen U)
    (hV : IsOpen V) (hUc : IsPreconnected U) (hVc : IsPreconnected V) (hUn : U.Nonempty)
    (hVn : V.Nonempty) (hdisj : Disjoint U V) (hX : X = U ∪ V) :
    componentsIn X = {U, V} := by
  have key : ∀ {U V : Set T}, IsOpen U → IsOpen V → IsPreconnected U → Disjoint U V →
      ∀ x ∈ U, connectedComponentIn (U ∪ V) x = U := by
    intro U V hU hV hUc hdisj x hx
    refine Subset.antisymm ?_ (hUc.subset_connectedComponentIn hx subset_union_left)
    have hC := isPreconnected_connectedComponentIn (F := U ∪ V) (x := x)
    have hsub := connectedComponentIn_subset (U ∪ V) x
    have := hC.subset_left_of_subset_union hU hV hdisj hsub
      ⟨x, mem_connectedComponentIn (Or.inl hx), hx⟩
    exact this
  subst hX
  ext C
  simp only [componentsIn, mem_image, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl (key hU hV hUc hdisj x hx)
    · right
      rw [union_comm]
      exact key hV hU hVc hdisj.symm x hx
  · rintro (rfl | rfl)
    · obtain ⟨x, hx⟩ := hUn
      exact ⟨x, Or.inl hx, key hU hV hUc hdisj x hx⟩
    · obtain ⟨x, hx⟩ := hVn
      refine ⟨x, Or.inr hx, ?_⟩
      rw [union_comm]
      exact key hV hU hVc hdisj.symm x hx

/-- **The Jordan curve theorem in the complex plane.** -/
theorem jordan_complex (φ : Circle ≃ₜ F) :
    ∃ A B, IsJordanSplit F A B ∧ Bornology.IsBounded A ∧ ¬ Bornology.IsBounded B := by
  have hcomp := isCompact_of_oArc φ
  have hF := hcomp.isClosed
  have hnotconn : ¬ IsPreconnected Fᶜ := by
    have h := not_isPreconnected_compl_union (α := upperArc φ) (β := lowerArc φ) rfl rfl
      (lowerArc_zero φ) (lowerArc_one φ) (upperArc_zero_ne_one φ) (range_upper_inter_lower φ)
    rwa [range_upper_union_lower] at h
  -- Two points in different components.
  have hne : ∃ a b, a ∉ F ∧ b ∉ F ∧ connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ b := by
    by_contra hcon
    push Not at hcon
    apply hnotconn
    by_cases hemp : (Fᶜ).Nonempty
    · obtain ⟨x, hx⟩ := hemp
      have : Fᶜ = connectedComponentIn Fᶜ x := by
        refine Subset.antisymm (fun y hy => ?_) (connectedComponentIn_subset _ _)
        rw [hcon x y hx hy]
        exact mem_connectedComponentIn hy
      rw [this]
      exact isPreconnected_connectedComponentIn
    · rw [not_nonempty_iff_eq_empty] at hemp
      rw [hemp]
      exact isPreconnected_empty
  obtain ⟨a₀, b₀, ha₀, hb₀, hab₀⟩ := hne
  -- Choose `a` in a bounded component.
  obtain ⟨a, b, ha, hb, hab, hbdd⟩ : ∃ a b, a ∉ F ∧ b ∉ F ∧
      connectedComponentIn Fᶜ a ≠ connectedComponentIn Fᶜ b ∧
      Bornology.IsBounded (connectedComponentIn Fᶜ a) := by
    rcases component_bounded_or hcomp ha₀ hb₀ hab₀ with h | h
    · exact ⟨a₀, b₀, ha₀, hb₀, hab₀, h⟩
    · exact ⟨b₀, a₀, hb₀, ha₀, hab₀.symm, h⟩
  have hcover : ∀ c, c ∉ F → c ∈ connectedComponentIn Fᶜ a ∨ c ∈ connectedComponentIn Fᶜ b := by
    intro c hc
    by_contra hcon
    push Not at hcon
    refine component_eq_or_eq φ ha hb hc hab (fun h => hcon.1 ?_) (fun h => hcon.2 ?_)
    · rw [h]; exact mem_connectedComponentIn hc
    · rw [h]; exact mem_connectedComponentIn hc
  have hunion : Fᶜ = connectedComponentIn Fᶜ a ∪ connectedComponentIn Fᶜ b := by
    refine Subset.antisymm (fun c hc => hcover c hc) (union_subset ?_ ?_) <;>
      exact connectedComponentIn_subset _ _
  have hdisj : Disjoint (connectedComponentIn Fᶜ a) (connectedComponentIn Fᶜ b) := by
    refine Set.disjoint_left.mpr fun x hxa hxb => hab ?_
    rw [connectedComponentIn_eq hxa, connectedComponentIn_eq hxb]
  refine ⟨_, _, ⟨hab, ?_, ?_, ?_⟩, hbdd, ?_⟩
  · rw [← compl_eq_univ_sdiff]
    exact componentsIn_eq_pair (isOpen_component hF a) (isOpen_component hF b)
      isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn
      ⟨a, mem_connectedComponentIn ha⟩ ⟨b, mem_connectedComponentIn hb⟩ hdisj hunion
  · exact Subset.antisymm (frontier_component_subset hF a) (subset_frontier_component φ ha hb hab)
  · exact Subset.antisymm (frontier_component_subset hF b)
      (subset_frontier_component φ hb ha hab.symm)
  · intro hbddb
    have huniv : (univ : Set ℂ) = F ∪ (connectedComponentIn Fᶜ a ∪ connectedComponentIn Fᶜ b) := by
      rw [← hunion, union_compl_self]
    have : Bornology.IsBounded (univ : Set ℂ) := by
      rw [huniv]
      exact hcomp.isBounded.union (hbdd.union hbddb)
    exact NormedSpace.unbounded_univ ℝ ℂ this

end GraphMinor.Surface

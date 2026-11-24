/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.MoveCuff
public import LeanPool.GraphMinor.Surface.DiscGrow
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Order.IntermediateValue

/-!
# Lifting homeomorphisms of the circle

Every homeomorphism of the circle lifts to a continuous monotone map of the real line, since the map
`exp`
from the line to the circle is a covering map. From this we get that orientation preserving
homeomorphisms
are closed under inverse and under conjugation. We also build the homeomorphism that moves a given
arc of the circle onto the upper half circle.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

local notation "𝕀" => unitInterval

theorem exists_circle_lift_map (f : C(ℝ, Circle)) : ∃ L : ℝ → ℝ, Continuous L ∧
    ∀ t, Circle.exp (L t) = f t := by
  obtain ⟨z, hz⟩ : ∃ z : ℝ, Circle.exp z = f 0 := ⟨Complex.arg (f 0), Circle.exp_arg _⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 z hz
  exact ⟨F, F.continuous, fun t ↦ congrFun hF t⟩

/-- A continuous real function with values in the multiples of `c` on an interval is constant. -/
theorem eq_of_multiples {g : ℝ → ℝ} {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b) (hg : ContinuousOn g
  (Icc a b))
    (hm : ∀ t ∈ Icc a b, ∃ m : ℤ, g t = m * c) : g b = g a := by
  obtain ⟨m, hma⟩ := hm a (left_mem_Icc.mpr hab)
  obtain ⟨n, hnb⟩ := hm b (right_mem_Icc.mpr hab)
  have key : ∀ k : ℤ, ¬ ((k + 1 / 2 : ℝ) * c ∈ uIcc (g a) (g b)) := by
    intro k hk
    obtain ⟨t, ht, he⟩ := intermediate_value_uIcc (uIcc_of_le hab ▸ hg) hk
    rw [uIcc_of_le hab] at ht
    obtain ⟨l, hl⟩ := hm t ht
    rw [hl] at he
    have h1 : (l : ℝ) = k + 1 / 2 := mul_right_cancel₀ hc.ne' he
    have h2 : (2 * l : ℤ) = 2 * k + 1 := by exact_mod_cast (by linarith : (2 * l : ℝ) = 2 * k + 1)
    omega
  by_contra hne
  have hmn : m ≠ n := fun h ↦ hne (by rw [hma, hnb, h])
  rcases lt_or_gt_of_ne hmn with h | h
  · refine key m ?_
    rw [hma, hnb, uIcc_of_le (by gcongr)]
    have h1 : (m + 1 : ℝ) ≤ n := by exact_mod_cast h
    constructor
    · nlinarith
    · nlinarith
  · refine key n ?_
    rw [hma, hnb, uIcc_of_ge (by gcongr)]
    have h1 : (n + 1 : ℝ) ≤ m := by exact_mod_cast h
    constructor
    · nlinarith
    · nlinarith

theorem exp_add_two_pi (t : ℝ) : Circle.exp (t + 2 * Real.pi) = Circle.exp t := by
  rw [Circle.exp_add, Circle.exp_two_pi, mul_one]

/-- Two continuous lifts of the same map differ by a constant. -/
theorem lift_diff_const {L M : ℝ → ℝ} (hL : Continuous L) (hM : Continuous M)
    (h : ∀ t, Circle.exp (L t) = Circle.exp (M t)) (s t : ℝ) : L s - M s = L t - M t := by
  have hpi := Real.pi_pos
  have hm : ∀ t, ∃ m : ℤ, L t - M t = m * (2 * Real.pi) := fun t ↦ by
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (h t)
    exact ⟨m, by rw [hm]; ring⟩
  have hmm : ∀ s t, s ≤ t → L t - M t = L s - M s := fun s t hst ↦
    eq_of_multiples (by positivity) hst (hL.sub hM).continuousOn fun t _ ↦ hm t
  rcases le_total s t with h | h
  · exact (hmm s t h).symm
  · exact hmm t s h

/-- Every homeomorphism of the circle lifts to a continuous strictly monotone map of the line. -/
theorem exists_circle_lift (τ : Circle ≃ₜ Circle) :
    ∃ L : ℝ → ℝ, Continuous L ∧ (StrictMono L ∨ StrictAnti L) ∧
      ∀ t, τ (Circle.exp t) = Circle.exp (L t) := by
  have hpi := Real.pi_pos
  obtain ⟨L, hLc, hL⟩ := exists_circle_lift_map
    ⟨fun t ↦ τ (Circle.exp t), τ.continuous.comp Circle.exp.continuous⟩
  have hL' : ∀ t, τ (Circle.exp t) = Circle.exp (L t) := fun t ↦ (hL t).symm
  have hper : ∀ s t, L (s + 2 * Real.pi) - L s = L (t + 2 * Real.pi) - L t := fun s t ↦ by
    have := lift_diff_const (L := fun t ↦ L (t + 2 * Real.pi)) (M := L)
      (hLc.comp (continuous_id.add continuous_const)) hLc (fun t ↦ by
        rw [← hL', ← hL', exp_add_two_pi]) s t
    exact this
  obtain ⟨d, hd⟩ : ∃ d : ℤ, L (0 + 2 * Real.pi) = L 0 + d * (2 * Real.pi) := by
    have h : Circle.exp (L (0 + 2 * Real.pi)) = Circle.exp (L 0) := by
      rw [← hL', ← hL', exp_add_two_pi]
    exact Circle.exp_eq_exp.mp h
  have hstep : ∀ t, L (t + 2 * Real.pi) = L t + d * (2 * Real.pi) := fun t ↦ by
    have := hper t 0
    rw [hd] at this
    linarith
  have hd0 : d ≠ 0 := by
    rintro rfl
    let D : ℝ → ℝ := fun θ ↦ L θ - L (θ + Real.pi)
    have hD : Continuous D := by fun_prop
    have h2 : D Real.pi = - D 0 := by
      have h3 := hstep 0
      simp only [Int.cast_zero, zero_mul, add_zero, zero_add] at h3
      have h4 : Real.pi + Real.pi = 2 * Real.pi := by ring
      simp only [D, h4, h3, zero_add]
      ring
    obtain ⟨θ, hθ⟩ : ∃ θ, D θ = 0 := by
      rcases le_total (D 0) 0 with h | h
      · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc hpi.le hD.continuousOn
          (show (0 : ℝ) ∈ Icc (D 0) (D Real.pi) from ⟨h, by rw [h2]; linarith⟩)
        exact ⟨θ, hθ⟩
      · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' hpi.le hD.continuousOn
          (show (0 : ℝ) ∈ Icc (D Real.pi) (D 0) from ⟨by rw [h2]; linarith, h⟩)
        exact ⟨θ, hθ⟩
    have h5 : L θ = L (θ + Real.pi) := sub_eq_zero.mp hθ
    have h6 : Circle.exp θ = Circle.exp (θ + Real.pi) := τ.injective (by rw [hL', hL', h5])
    have h7 : Circle.exp Real.pi = 1 := by
      have := mul_left_cancel (a := Circle.exp θ) (b := 1) (c := Circle.exp Real.pi) (by
        rw [mul_one, ← Circle.exp_add]; exact h6)
      exact this.symm
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (h7.trans Circle.exp_zero.symm)
    have h8 : (1 : ℝ) = m * 2 := by
      have : Real.pi * 1 = Real.pi * (m * 2) := by linarith
      exact mul_left_cancel₀ hpi.ne' this
    have h9 : (1 : ℤ) = m * 2 := by exact_mod_cast h8
    omega
  have hmul : ∀ (k : ℤ) t, L (t + k * (2 * Real.pi)) = L t + k * d * (2 * Real.pi) := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ i ih =>
      intro t
      have h1 := hstep (t + i * (2 * Real.pi))
      have h2 := ih t
      push_cast at h2 ⊢
      rw [show t + (i + 1) * (2 * Real.pi) = t + i * (2 * Real.pi) + 2 * Real.pi by ring, h1, h2]
      ring
    | pred i ih =>
      intro t
      have := hstep (t + (-(i : ℝ) - 1) * (2 * Real.pi))
      push_cast
      rw [show t + (-(i : ℝ) - 1) * (2 * Real.pi) + 2 * Real.pi = t + (-(i : ℝ)) *
        (2 * Real.pi) by ring] at this
      have h2 := ih t
      push_cast at h2
      linarith
  have hinj : Function.Injective L := fun s t he ↦ by
    have h1 : Circle.exp s = Circle.exp t := τ.injective (by rw [hL', hL', he])
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h1
    have h2 := hmul k t
    rw [← hk, he] at h2
    have h3 : (k : ℝ) * d * (2 * Real.pi) = 0 := by linarith
    have h4 : (k : ℝ) * d = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h (by positivity)
    have h5 : (k : ℝ) = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) hd0
    rw [hk, h5]
    ring
  exact ⟨L, hLc, hLc.strictMono_of_inj hinj, hL'⟩

/-- A lift of the identity is a translation, so it is increasing. -/
theorem strictMono_of_lift_id {F : ℝ → ℝ} (hF : Continuous F)
    (h : ∀ t, Circle.exp (F t) = Circle.exp t) : StrictMono F := by
  intro s t hst
  have := lift_diff_const hF continuous_id h s t
  simp only [id] at this
  linarith

theorem preserves_symm {ψ : Circle ≃ₜ Circle} (hψ : PreservesCircleOrientation ψ) :
    PreservesCircleOrientation ψ.symm := by
  obtain ⟨l, hlc, hlm, hl⟩ := hψ
  obtain ⟨M, hMc, hM, hMe⟩ := exists_circle_lift ψ.symm
  have hcomp : StrictMono (M ∘ l) := strictMono_of_lift_id (hMc.comp hlc) fun t ↦ by
    rw [Function.comp, ← hMe, ← hl]
    simp
  rcases hM with hM | hM
  · exact ⟨M, hMc, hM, hMe⟩
  · exact absurd (hcomp (zero_lt_one)) (not_lt.mpr (hM.comp_strictMono hlm zero_lt_one).le)

theorem preserves_conj (τ : Circle ≃ₜ Circle) {ψ : Circle ≃ₜ Circle}
    (hψ : PreservesCircleOrientation ψ) :
    PreservesCircleOrientation (τ.trans (ψ.trans τ.symm)) := by
  obtain ⟨l, hlc, hlm, hl⟩ := hψ
  obtain ⟨L, hLc, hL, hLe⟩ := exists_circle_lift τ
  obtain ⟨M, hMc, hM, hMe⟩ := exists_circle_lift τ.symm
  have hcomp : StrictMono (M ∘ L) := strictMono_of_lift_id (hMc.comp hLc) fun t ↦ by
    rw [Function.comp, ← hMe, ← hLe]
    simp
  refine ⟨M ∘ l ∘ L, hMc.comp (hlc.comp hLc), ?_, fun t ↦ ?_⟩
  · rcases hL with hL | hL <;> rcases hM with hM | hM
    · exact hM.comp (hlm.comp hL)
    · exact absurd (hcomp zero_lt_one) (not_lt.mpr (hM.comp_strictMono hL zero_lt_one).le)
    · exact absurd (hcomp zero_lt_one) (not_lt.mpr (hM.comp_strictAnti hL zero_lt_one).le)
    · exact hM.comp (hlm.comp_strictAnti hL)
  · simp only [Homeomorph.trans_apply, Function.comp]
    rw [hLe, hl, hMe]

/-- Two pairs of arcs that each cover the circle: there is a homeomorphism of the circle that takes
one
pair to the other. -/
theorem exists_glue {a b a' b' : 𝕀 → Circle} (h : IsTwoArcs a b) (h' : IsTwoArcs a' b')
    (hu : range a ∪ range b = univ) (hu' : range a' ∪ range b' = univ) :
    ∃ ψ : Circle ≃ₜ Circle, ∀ r, ψ (a r) = a' r ∧ ψ (b r) = b' r := by
  have key : ∀ {a b a' b' : 𝕀 → Circle}, IsTwoArcs a b → IsTwoArcs a' b' →
      ∀ x y, Sum.elim a b x = Sum.elim a b y → Sum.elim a' b' x = Sum.elim a' b' y := by
    intro a b a' b' h h' x y he
    rcases x with s | s <;> rcases y with t | t <;> simp only [Sum.elim_inl, Sum.elim_inr] at he ⊢
    · rw [h.arc_left.2 he]
    · rcases h.meet s t he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'.zero.symm
      · exact h'.one.symm
    · rcases h.meet t s he.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'.zero
      · exact h'.one
    · rw [h.arc_right.2 he]
  have hq : ∀ {a b : 𝕀 → Circle}, IsTwoArcs a b → range a ∪ range b = univ →
      Topology.IsQuotientMap (Sum.elim a b) ∧ Function.Surjective (Sum.elim a b) := by
    intro a b h hu
    have hc : Continuous (Sum.elim a b) := h.arc_left.1.sumElim h.arc_right.1
    have hs : Function.Surjective (Sum.elim a b) := fun z ↦ by
      have : z ∈ range a ∪ range b := hu ▸ mem_univ z
      rcases this with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exact ⟨Sum.inl r, rfl⟩
      · exact ⟨Sum.inr r, rfl⟩
    exact ⟨hc.isClosedMap.isQuotientMap hc hs, hs⟩
  obtain ⟨hQ, hS⟩ := hq h hu
  obtain ⟨hQ', hS'⟩ := hq h' hu'
  let f : Circle → Circle := fun z ↦ Sum.elim a' b' (Function.surjInv hS z)
  let f' : Circle → Circle := fun z ↦ Sum.elim a b (Function.surjInv hS' z)
  have hf : ∀ x, f (Sum.elim a b x) = Sum.elim a' b' x := fun x ↦
    key h h' _ _ (Function.surjInv_eq hS _)
  have hf' : ∀ x, f' (Sum.elim a' b' x) = Sum.elim a b x := fun x ↦
    key h' h _ _ (Function.surjInv_eq hS' _)
  have hfc : Continuous f := by
    rw [hQ.continuous_iff]
    have : f ∘ Sum.elim a b = Sum.elim a' b' := funext hf
    rw [this]
    exact h'.arc_left.1.sumElim h'.arc_right.1
  have hfc' : Continuous f' := by
    rw [hQ'.continuous_iff]
    have : f' ∘ Sum.elim a' b' = Sum.elim a b := funext hf'
    rw [this]
    exact h.arc_left.1.sumElim h.arc_right.1
  refine ⟨⟨⟨f, f', fun z ↦ ?_, fun z ↦ ?_⟩, hfc, hfc'⟩, fun r ↦ ⟨hf (Sum.inl r), hf (Sum.inr r)⟩⟩
  · obtain ⟨x, rfl⟩ := hS z
    rw [hf, hf']
  · obtain ⟨x, rfl⟩ := hS' z
    rw [hf', hf]

/-- The arc from `u` of length `θ` moves onto the upper half circle, by an orientation preserving
homeomorphism. -/
theorem exists_circle_move (u : Circle) {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    ∃ ψ : Circle ≃ₜ Circle, PreservesCircleOrientation ψ ∧
      ∀ s ∈ Icc 0 θ, ψ (u * Circle.exp s) = Circle.exp (Real.pi * (s / θ)) := by
  have hpi := Real.pi_pos
  obtain ⟨a, b, hab, ha, hb, hun⟩ := circle_two_arcs' u hθ
  obtain ⟨a', b', hab', ha', hb', hun'⟩ := circle_two_arcs' 1
    (show Real.pi ∈ Ioo 0 (2 * Real.pi) from ⟨hpi, by linarith⟩)
  obtain ⟨ψ, hψ⟩ := exists_glue hab hab' hun hun'
  have hs : ∀ s ∈ Icc 0 θ, ψ (u * Circle.exp s) = Circle.exp (Real.pi * (s / θ)) := fun s hs ↦ by
    have hr : s / θ ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hs.1 hθ.1.le, (div_le_one hθ.1).mpr hs.2⟩
    have h1 := (hψ ⟨s / θ, hr⟩).1
    rw [ha, ha'] at h1
    simp only [one_mul] at h1
    rw [show s / θ * θ = s from div_mul_cancel₀ _ hθ.1.ne'] at h1
    rw [h1, mul_comm]
  refine ⟨ψ, ?_, hs⟩
  obtain ⟨L, hLc, hL, hLe⟩ := exists_circle_lift ψ
  rcases hL with hL | hL
  · exact ⟨L, hLc, hL, hLe⟩
  · exfalso
    let α : ℝ := Complex.arg u
    have hα : u = Circle.exp α := (Circle.exp_arg u).symm
    have hconst := fun t (ht : t ∈ Icc 0 θ) ↦ hs t ht
    have hg : (fun s ↦ L (α + s) - Real.pi * (s / θ)) θ = (fun s ↦ L (α + s) - Real.pi * (s / θ)) 0
      := by
      have hcont : Continuous fun s ↦ L (α + s) - Real.pi * (s / θ) := by
        have : Continuous fun s ↦ L (α + s) := hLc.comp (continuous_const.add continuous_id)
        fun_prop
      refine eq_of_multiples (c := 2 * Real.pi) (by positivity) hθ.1.le hcont.continuousOn fun t ht
        ↦ ?_
      have h1 := hs t ht
      rw [hα, ← Circle.exp_add, hLe] at h1
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
      exact ⟨m, by rw [hm]; ring⟩
    simp only [add_zero, zero_div, mul_zero, sub_zero] at hg
    have h2 : L (α + θ) < L α := hL (by linarith [hθ.1])
    have h3 : Real.pi * (θ / θ) = Real.pi := by rw [div_self hθ.1.ne', mul_one]
    rw [h3] at hg
    linarith

end GraphMinor.GM19

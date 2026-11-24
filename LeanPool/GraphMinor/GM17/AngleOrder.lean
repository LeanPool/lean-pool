/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section7
public import LeanPool.GraphMinor.Surface.DiscPolygon

/-!
# Angles for a clockwise enumeration

If the cyclic order of a society agrees with a parametrization of a circle in a surface, then a
clockwise enumeration of the society has increasing
angles (`exists_angles`). This is what is needed to use the polygon of `exists_polygon_in_disc` for
a vortex in XVII (13.1).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GM09

universe u

theorem isClockwise3_of_ofFn {α : Type u} {Ω : CyclicPerm α} {k : ℕ} {t : Fin k → α}
  (h : Ω.IsClockwiseSeq (List.ofFn t)) {a b c : Fin k} (hab : a < b) (hbc : b < c) :
    Ω.IsClockwise3 (t a) (t b) (t c) := by
  have hb := b.2
  have hc := c.2
  refine CyclicPerm.IsClockwiseSeq.of_isBoundedSubseq h (M := [t a, t b, t c]) (lo := 0) (hi
    := k) ⟨Nat.zero_le _, fun i => if i = 0 then a.1 else if i = 1 then b.1 else c.1, ?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact ⟨by simp, Nat.zero_le _, by simp, by simp⟩
    · exact ⟨by simp, Nat.zero_le _, by simp, by simp⟩
    · exact ⟨by simp, Nat.zero_le _, by simp, by simp⟩
  · intro i j hij hj
    simp only [List.length_cons, List.length_nil] at hj
    have h1 : a.1 < b.1 := hab
    have h2 : b.1 < c.1 := hbc
    interval_cases j <;> interval_cases i <;> simp <;> omega

theorem exp_inj_Ico {b x y : ℝ} (hx : x ∈ Ico b (b + 2 * Real.pi)) (hy : y ∈ Ico b
  (b + 2 * Real.pi)) (h : Circle.exp x = Circle.exp y) : x = y := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hpi := Real.pi_pos
  have h1 : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith [hx.2, hy.1]
  have h2 : -(2 * Real.pi) < (m : ℝ) * (2 * Real.pi) := by linarith [hx.1, hy.2]
  have h3 : (m : ℝ) < 1 := by nlinarith
  have h4 : (-1 : ℝ) < m := by nlinarith
  have h5 : m < 1 := by exact_mod_cast h3
  have h6 : -1 < m := by exact_mod_cast h4
  have h7 : m = 0 := by omega
  rw [hm, h7]
  simp

theorem exists_angle_mem (b : ℝ) (w : Circle) : ∃ x ∈ Ico b (b + 2 * Real.pi), Circle.exp x = w
  := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨m, hm, -⟩ := existsUnique_add_zsmul_mem_Ico hpi (Complex.arg (w : ℂ)) b
  refine ⟨_, hm, ?_⟩
  have : Circle.exp (Complex.arg (w : ℂ) + m • (2 * Real.pi)) = Circle.exp (Complex.arg (w : ℂ))
    := by
    rw [zsmul_eq_mul, mul_comm]
    exact Circle_exp_add_int _ _
  rw [this]
  exact Circle.exp_arg w

/-- **Increasing angles for a clockwise enumeration.** -/
theorem exists_angles {S : Type*} [TopologicalSpace S] {α : Type u} {Ω : CyclicPerm α} {k : ℕ}
  (hk : 0 < k) {t : Fin k → α}
    (ht : Ω.IsClockwiseSeq (List.ofFn t)) {ν : α → S} (hν : InjOn ν Ω.bar) {F : Set S} {φ : Circle
      ≃ₜ F} (hA : AgreesWithOArcHomeo ν Ω F φ) :
    ∃ s : Fin k → ℝ, StrictMono s ∧ (∀ i, s i < s ⟨0, hk⟩ + 2 * Real.pi) ∧ ∀ i, ν (t i) = (φ
      (Circle.exp (s i))).1 := by
  have hbar : ∀ i, t i ∈ Ω.bar := fun i => ht.2.1 _ (by simp [List.mem_ofFn])
  have htinj : Function.Injective t := List.nodup_ofFn.mp ht.1
  have hF : ∀ i, ν (t i) ∈ F := fun i => hA.1 _ (hbar i)
  let i₀ : Fin k := ⟨0, hk⟩
  obtain ⟨b, -, hb⟩ := exists_angle_mem 0 (φ.symm ⟨ν (t i₀), hF i₀⟩)
  have hex : ∀ i, ∃ x ∈ Ico b (b + 2 * Real.pi), Circle.exp x = φ.symm ⟨ν (t i), hF i⟩ := fun i
    => exists_angle_mem b _
  choose s hs hse using hex
  have hval : ∀ i, ν (t i) = (φ (Circle.exp (s i))).1 := fun i => by rw [hse, φ.apply_symm_apply]
  have hs0 : s i₀ = b := exp_inj_Ico (hs i₀) ⟨le_rfl, by linarith [Real.pi_pos]⟩ (by rw [hse, hb])
  have hzero : ∀ i, i₀ < i → b < s i := fun i hi => by
    refine lt_of_le_of_ne (hs i).1 fun he => ?_
    have h1 : ν (t i₀) = ν (t i) := by rw [hval, hval, hs0, he]
    exact (hi.ne (htinj (hν (hbar _) (hbar _) h1)))
  refine ⟨s, ?_, fun i => by rw [hs0]; exact (hs i).2, hval⟩
  intro x y hxy
  by_cases hx : x = i₀
  · subst hx
    rw [hs0]
    exact hzero y hxy
  have h0x : i₀ < x := by
    change 0 < x.1
    exact Nat.pos_of_ne_zero fun h => hx (Fin.ext h)
  obtain ⟨τ₁, τ₂, τ₃, h12, h23, h31, e1, e2, e3⟩ := hA.2 _ _ _ (isClockwise3_of_ofFn ht h0x hxy)
  have he1 : Circle.exp τ₁ = Circle.exp b := by
    rw [hb]
    exact (φ.symm_apply_eq.mpr (Subtype.ext e1.symm)).symm
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he1
  have hshift : ∀ τ, Circle.exp (τ - m * (2 * Real.pi)) = Circle.exp τ := fun τ => by
    have := Circle_exp_add_int τ (-m)
    rw [← this]
    congr 1
    push_cast
    ring
  have hsv : ∀ (i : Fin k) (τ : ℝ), (φ (Circle.exp τ)).1 = ν (t i) → τ - m * (2 * Real.pi) ∈ Ico b
    (b + 2 * Real.pi) → s i = τ - m * (2 * Real.pi) := fun i τ he hτ => by
    refine exp_inj_Ico (hs i) hτ ?_
    rw [hse, hshift]
    apply φ.symm_apply_eq.mpr
    exact Subtype.ext he.symm
  rw [hsv x τ₂ e2 ⟨by linarith, by linarith⟩, hsv y τ₃ e3 ⟨by linarith, by linarith⟩]
  linarith

end GraphMinor.GM17

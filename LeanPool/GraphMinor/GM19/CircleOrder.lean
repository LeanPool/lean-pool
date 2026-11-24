/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section4b
public import LeanPool.GraphMinor.Surface.DiscTwist
public import LeanPool.GraphMinor.GM19.FragmentDirection

/-!
# Cyclic order on the circle

Points of the circle with angles in a window of length less than one turn have the cyclic order of
their angles (`circleCyclic_ee_iff`). Finitely many such points can be moved to any points with the
same cyclic order by a homeomorphism of the circle that keeps the direction
(`exists_circle_interp`). We use this in step (2) of the proof of Graph Minors XIX, (15.2), page
381, to carry the ends of the
edges of `Γ` to the marks of the model.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Filter GraphMinor.Surface

theorem circleCyclic_ee {x y z : ℝ} (hxy : x < y) (hyz : y < z) (hzx : z < x + 1) : CircleCyclic
  (ee x) (ee y) (ee z) := by
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi * (y - x), 2 * Real.pi * (z - x), by nlinarith [sub_pos.mpr hxy],
    by nlinarith, by nlinarith, ?_, ?_⟩
  · rw [ee, ee, ← Circle.exp_add]
    congr 1
    ring
  · rw [ee, ee, ← Circle.exp_add]
    congr 1
    ring

theorem CircleCyclic.rotate {a b c : Circle} (h : CircleCyclic a b c) : CircleCyclic b c a := by
  obtain ⟨s, t, hs, hst, ht, rfl, rfl⟩ := h
  refine ⟨t - s, 2 * Real.pi - s, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [mul_assoc, ← Circle.exp_add]
    congr 2
    ring
  · rw [mul_assoc, ← Circle.exp_add, add_sub_cancel, Circle.exp_two_pi, mul_one]

theorem circleCyclic_mul_iff (g : Circle) {a b c : Circle} : CircleCyclic (g * a) (g * b)
  (g * c) ↔ CircleCyclic a b c := by
  constructor
  · rintro ⟨s, t, hs, hst, ht, h1, h2⟩
    rw [mul_assoc] at h1 h2
    exact ⟨s, t, hs, hst, ht, mul_left_cancel h1, mul_left_cancel h2⟩
  · rintro ⟨s, t, hs, hst, ht, rfl, rfl⟩
    exact ⟨s, t, hs, hst, ht, by rw [mul_assoc], by rw [mul_assoc]⟩

/-- The three rotations of a strict order. -/
def CycOrder (x y z : ℝ) : Prop := (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)

/-- In a window shorter than one turn, the cyclic order of points is the order of their angles. -/
theorem circleCyclic_ee_iff {x y z : ℝ} (h1 : x < y + 1) (h2 : y < x + 1) (h3 : y < z + 1)
  (h4 : z < y + 1) (h5 : x < z + 1) (h6 : z < x + 1) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    CircleCyclic (ee x) (ee y) (ee z) ↔ CycOrder x y z := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne hxy with a | a <;> rcases lt_or_gt_of_ne hyz with b | b
      <;> rcases lt_or_gt_of_ne hxz with c | c
    · exact Or.inl ⟨a, b⟩
    · exact absurd (a.trans b) c.not_gt
    · exact (not_circleCyclic_both h (circleCyclic_ee c b h2)).elim
    · exact Or.inr (Or.inr ⟨c, a⟩)
    · exact (not_circleCyclic_both h (circleCyclic_ee a c h4).rotate).elim
    · exact Or.inr (Or.inl ⟨b, c⟩)
    · exact absurd (b.trans a) c.not_gt
    · exact (not_circleCyclic_both h (circleCyclic_ee b a h5).rotate.rotate).elim
  · rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · exact circleCyclic_ee a b h6
    · exact (circleCyclic_ee a b h1).rotate.rotate
    · exact (circleCyclic_ee a b h3).rotate

/-- A strictly increasing map on a finite subset of the line extends to a strictly increasing map of
the line. -/
theorem exists_strictMono_interp (X : Finset ℝ) (hX : X.Nonempty) (f : ℝ → ℝ)
  (hf : StrictMonoOn f X) : ∃ τ : ℝ → ℝ, Continuous τ ∧ StrictMono τ ∧ ∀ x ∈ X, τ x = f x := by
  classical
  let X' := {x // x ∈ X}
  obtain ⟨ε, hε0, hε1, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ X, ∀ y ∈ X, x < y
    → f x - ε * x < f y - ε * y := by
    have e : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ x : X', ∀ y : X', x.1 < y.1 → f x.1 - ε * x.1 < f y.1 - ε * y.1
      := by
      refine eventually_all.mpr fun x => eventually_all.mpr fun y => ?_
      by_cases hxy : x.1 < y.1
      · have hc : Continuous fun ε : ℝ => (f y.1 - ε * y.1) - (f x.1 - ε * x.1) := by fun_prop
        have h0 : 0 < (fun ε : ℝ => (f y.1 - ε * y.1) - (f x.1 - ε * x.1)) 0 := by
          have := hf x.2 y.2 hxy
          simp only
          linarith
        have := (hc.tendsto 0).eventually (lt_mem_nhds h0)
        exact (this.filter_mono nhdsWithin_le_nhds).mono fun ε h _ => by linarith
      · exact Eventually.of_forall fun ε h => absurd h hxy
    obtain ⟨ε, h1, h2⟩ := (e.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    exact ⟨ε, h2.1, h2.2, fun x hx y hy hxy => h1 ⟨x, hx⟩ ⟨y, hy⟩ hxy⟩
  let f' : ℝ → ℝ := fun x => (f x - ε * x) / (1 - ε)
  have hp : 0 < 1 - ε := by linarith
  have hf' : ∀ x ∈ X, ∀ y ∈ X, x < y → f' x < f' y := fun x hx y hy hxy => div_lt_div_of_pos_right
    (hε x hx y hy hxy) hp
  obtain ⟨L, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ X, ∀ y ∈ X, y < x → f' x + L * (y - x) ≤ f' y := by
    have e : ∀ᶠ L : ℝ in atTop, ∀ x : X', ∀ y : X', y.1 < x.1 → f' x.1 + L * (y.1 - x.1) ≤ f' y.1
      := by
      refine eventually_all.mpr fun x => eventually_all.mpr fun y => ?_
      by_cases hxy : y.1 < x.1
      · filter_upwards [eventually_ge_atTop ((f' x.1 - f' y.1) / (x.1 - y.1))] with L hL _
        have hd : 0 < x.1 - y.1 := sub_pos.mpr hxy
        rw [div_le_iff₀ hd] at hL
        nlinarith
      · exact Eventually.of_forall fun L h => absurd h hxy
    obtain ⟨L, h1, h2⟩ := (e.and (eventually_ge_atTop 0)).exists
    exact ⟨L, h2, fun x hx y hy hxy => h1 ⟨x, hx⟩ ⟨y, hy⟩ hxy⟩
  obtain ⟨hL0, hL⟩ := hL
  let G : ℝ → ℝ := fun t => X.sup' hX fun x => min (f' x) (f' x + L * (t - x))
  have hGc : Continuous G := Continuous.finset_sup'_apply hX fun x _ => by fun_prop
  have hGm : Monotone G := fun s t hst => Finset.sup'_mono_fun fun x _ => min_le_min le_rfl
    (by nlinarith [mul_le_mul_of_nonneg_left hst hL0])
  have hGx : ∀ x ∈ X, G x = f' x := fun y hy => by
    refine le_antisymm (Finset.sup'_le _ _ fun x hx => ?_) ?_
    · rcases lt_trichotomy x y with h | h | h
      · exact (min_le_left _ _).trans (hf' x hx y hy h).le
      · rw [h]
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hL x hx y hy h)
    · refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun x => min (f' x) (f' x + L * (y - x))) hy)
      simp
  refine ⟨fun t => (1 - ε) * G t + ε * t, by fun_prop, fun s t hst => ?_, fun x hx => ?_⟩
  · have := mul_le_mul_of_nonneg_left (hGm hst.le) hp.le
    have h2 := mul_lt_mul_of_pos_left hst hε0
    change (1 - ε) * G s + ε * s < (1 - ε) * G t + ε * t
    linarith
  · change (1 - ε) * G x + ε * x = f x
    rw [hGx x hx]
    simp only [f']
    field_simp
    ring

/-- **Moving finitely many points of the circle.** Points with angles `a` in a window shorter than
one turn move to points `t` with the same cyclic order, by a homeomorphism that keeps the direction.
-/
theorem exists_circle_interp {Y : Type} [Finite Y] (a : Y → ℝ) (ha : Function.Injective a)
  (hw : ∀ x y, a x < a y + 1) (t : Y → Circle) (ht : Function.Injective t)
    (hc : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (CircleCyclic (t x) (t y) (t z) ↔ CycOrder (a x) (a y)
      (a z))) :
    ∃ τ : Circle ≃ₜ Circle, PreservesCircleOrientation τ ∧ ∀ y, τ (ee (a y)) = t y := by
  classical
  have := Fintype.ofFinite Y
  by_cases hY : IsEmpty Y
  · exact ⟨Homeomorph.refl _, ⟨id, continuous_id, strictMono_id, fun _ => rfl⟩, fun y => hY.elim y⟩
  rw [not_isEmpty_iff] at hY
  obtain ⟨y₀, hy₀⟩ := Finite.exists_min a
  have hB : ∀ y, ∃ B : ℝ, 0 ≤ B ∧ B < 1 ∧ (y = y₀ → B = 0) ∧ (y ≠ y₀ → B ≠ 0) ∧ t y = t y₀ * ee B
    := by
    intro y
    by_cases hy : y = y₀
    · subst hy
      exact ⟨0, le_rfl, one_pos, fun _ => rfl, fun h => absurd rfl h, by simp [ee]⟩
    · have hne : (t y₀)⁻¹ * t y ≠ 1 := fun h => hy (ht ((inv_mul_eq_one.mp h).symm))
      obtain ⟨s, hs0, hs1, hs⟩ := exists_angle hne
      have hpi := Real.pi_pos
      refine ⟨s / (2 * Real.pi), by positivity, by rw [div_lt_one (by positivity)]; exact hs1, fun
        h => absurd h hy, fun _ => by positivity, ?_⟩
      rw [ee, mul_div_cancel₀ _ (by positivity), ← hs, mul_inv_cancel_left]
  choose B hB0 hB1 hBy hBn hBt using hB
  let A : Y → ℝ := fun y => a y - a y₀
  have hA0 : ∀ y, 0 ≤ A y := fun y => sub_nonneg.mpr (hy₀ y)
  have hA1 : ∀ y, A y < 1 := fun y => by
    have := hw y y₀
    simp only [A]
    linarith
  have hAi : Function.Injective A := fun x y h => ha (by simpa [A] using h)
  have hAy : ∀ y, y ≠ y₀ → 0 < A y := fun y hy => lt_of_le_of_ne (hA0 y) fun h => hy (hAi
    (by simp [A, ← h]))
  have hBp : ∀ y, y ≠ y₀ → 0 < B y := fun y hy => lt_of_le_of_ne (hB0 y) (hBn y hy).symm
  have hkey : ∀ x y, A x < A y → B x < B y := by
    intro x y hxy
    have hy : y ≠ y₀ := fun h => by
      have := hA0 x
      simp only [h, A, sub_self] at hxy
      linarith
    by_cases hx : x = y₀
    · rw [hBy x hx]
      exact hBp y hy
    have hne : x ≠ y := fun h => by rw [h] at hxy; exact lt_irrefl _ hxy
    have h1 : CircleCyclic (t y₀) (t x) (t y) := (hc y₀ x y (Ne.symm hx) hne (Ne.symm hy)).mpr
      (Or.inl ⟨by simpa [A] using hAy x hx, by simpa [A] using hxy⟩)
    rw [hBt x, hBt y] at h1
    have h1' : CircleCyclic (t y₀ * ee 0) (t y₀ * ee (B x)) (t y₀ * ee (B y)) := by
      simpa [ee] using h1
    rw [circleCyclic_mul_iff, circleCyclic_ee_iff (by linarith [hBp x hx]) (by linarith [hB1 x])
      (by linarith [hBp y hy, hB1 x]) (by linarith [hBp x hx, hB1 y]) (by linarith [hBp y hy])
        (by linarith [hB1 y])
      (hBp x hx).ne (fun h => hne (ht (by rw [hBt x, hBt y, h]))) (hBp y hy).ne] at h1'
    rcases h1' with ⟨_, h⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact h
    · exact absurd h' (not_lt.mpr (hB0 _))
    · exact absurd h (not_lt.mpr (hB0 _))
  let f : ℝ → ℝ := fun x => if h : ∃ y, A y = x then B h.choose else 1
  have hfA : ∀ y, f (A y) = B y := fun y => by
    have h : ∃ y', A y' = A y := ⟨y, rfl⟩
    simp only [f, dite_eq_left h]
    rw [hAi h.choose_spec]
  have hf1 : f 1 = 1 := by
    have h : ¬ ∃ y, A y = 1 := fun ⟨y, hy⟩ => (hA1 y).ne hy
    simp only [f, dite_eq_right h]
  let X : Finset ℝ := insert 1 (Finset.univ.image A)
  have hX : ∀ x ∈ X, x = 1 ∨ ∃ y, x = A y := fun x hx => by
    rcases Finset.mem_insert.mp hx with h | h
    · exact Or.inl h
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨y, rfl⟩
  have hmono : StrictMonoOn f X := by
    intro p hp q hq hpq
    rcases hX p hp with rfl | ⟨x, rfl⟩ <;> rcases hX q hq with rfl | ⟨y, rfl⟩
    · exact absurd hpq (lt_irrefl _)
    · exact absurd hpq (not_lt.mpr (hA1 y).le)
    · rw [hfA, hf1]
      exact hB1 x
    · rw [hfA, hfA]
      exact hkey x y hpq
  obtain ⟨σ, hσc, hσm, hσ⟩ := exists_strictMono_interp X ⟨1, Finset.mem_insert_self _ _⟩ f hmono
  have hσA : ∀ y, σ (A y) = B y := fun y => by
    rw [hσ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem A (Finset.mem_univ y))), hfA]
  have hσ0 : σ 0 = 0 := by
    have := hσA y₀
    simpa [A, hBy y₀ rfl] using this
  have hσ1 : σ 1 = 1 := by rw [hσ 1 (Finset.mem_insert_self _ _), hf1]
  obtain ⟨h, hh, he⟩ := exists_circle_homeo (τ := σ) hσc.continuousOn (hσm.strictMonoOn _)
    (by rw [hσ0, hσ1, zero_add])
  refine ⟨(Homeomorph.mulLeft (ee (a y₀))⁻¹).trans (h.trans (Homeomorph.mulLeft (t y₀))),
    PreservesCircleOrientation.comp (PreservesCircleOrientation.comp
      (preservesCircleOrientation_mul _) hh) (preservesCircleOrientation_mul _), fun y => ?_⟩
  change t y₀ * h ((ee (a y₀))⁻¹ * ee (a y)) = t y
  have h1 : (ee (a y₀))⁻¹ * ee (a y) = ee (A y) := by
    rw [inv_mul_eq_iff_eq_mul, ee, ee, ee, ← Circle.exp_add]
    congr 1
    simp only [A]
    ring
  rw [h1, he _ ⟨hA0 y, (hA1 y).le⟩, hσA, ← hBt]

end GraphMinor.GM19

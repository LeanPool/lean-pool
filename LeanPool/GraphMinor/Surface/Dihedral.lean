/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Period
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic

/-!
# Paths made of two involutions

Let `τ` and `σ` be involutions of a finite set, and suppose that `τ` has no fixed point. The orbits
of the two maps
together are paths and cycles, and the ends of a path are the fixed points of `σ` in it. So an orbit
with a fixed point of
`σ` has exactly two of them (`exists_other_end`). We use this for the corners of polygons around a
vertex: `τ` crosses a
corner of a polygon and `σ` crosses a side. Cutting along two sides at a vertex of a cycle gives two
paths
(`cut_classes`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Function Relation

variable {G : Type*}

/-- The orbit relation of two maps. -/
abbrev TwoOrb (τ σ : G → G) : G → G → Prop := EqvGen fun a b => b = τ a ∨ b = σ a

theorem TwoOrb.left (τ σ : G → G) (a : G) : TwoOrb τ σ a (τ a) := .rel _ _ (.inl rfl)

theorem TwoOrb.right (τ σ : G → G) (a : G) : TwoOrb τ σ a (σ a) := .rel _ _ (.inr rfl)

/-- An orbit with a fixed point of `σ` has exactly two fixed points of `σ`. -/
theorem exists_other_end [Finite G] {τ σ : G → G} (hτ : Involutive τ) (hσ : Involutive σ)
  (hfree : ∀ a, τ a ≠ a) {x : G}
    (hx : σ x = x) : ∃ y, y ≠ x ∧ σ y = y ∧ TwoOrb τ σ x y ∧ ∀ z, TwoOrb τ σ x z → σ z = z → z = x
      ∨ z = y := by
  classical
  let T : Equiv.Perm G := hτ.toPerm
  let R : Equiv.Perm G := hσ.toPerm
  let ρ : Equiv.Perm G := R * T
  have hR : R * R = 1 := Equiv.ext fun a => hσ a
  have hT : T * T = 1 := Equiv.ext fun a => hτ a
  have hRinv : R⁻¹ = R := inv_eq_of_mul_eq_one_left hR
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_left hT
  have hconj : R * ρ * R⁻¹ = ρ⁻¹ := by
    simp only [ρ, mul_inv_rev, hRinv, hTinv]
    rw [← mul_assoc, hR, one_mul]
  have hzp : ∀ k : ℤ, R * ρ ^ k * R⁻¹ = ρ ^ (-k) := fun k => by
    rw [← conj_zpow, hconj, inv_zpow, zpow_neg]
  have hσk : ∀ k : ℤ, σ ((ρ ^ k) x) = (ρ ^ (-k)) x := fun k => by
    have h1 := congrArg (fun P : Equiv.Perm G => P x) (hzp k)
    simp only [Equiv.Perm.mul_apply, hRinv] at h1
    have h2 : R x = x := hx
    rw [h2] at h1
    exact h1
  have hτk : ∀ k : ℤ, τ ((ρ ^ k) x) = (ρ ^ (-k - 1)) x := fun k => by
    have h1 : ρ ^ (k + 1) = ρ * ρ ^ k := by rw [add_comm, zpow_add, zpow_one]
    have h2 : (ρ ^ (k + 1)) x = σ (τ ((ρ ^ k) x)) := by
      rw [h1]
      rfl
    have h3 := hσk (k + 1)
    rw [h2, hσ] at h3
    rw [h3]
    congr 2
    ring
  let d := MulAction.period ρ x
  have hd : 0 < d := MulAction.period_pos_of_orderOf_pos (orderOf_pos ρ) x
  have heq : ∀ a b : ℤ, (ρ ^ a) x = (ρ ^ b) x ↔ (d : ℤ) ∣ a - b := fun a b => by
    have h1 : (ρ ^ a) x = (ρ ^ b) x ↔ (ρ ^ (a - b)) • x = x := by
      have e : ρ ^ a = ρ ^ b * ρ ^ (a - b) := by rw [← zpow_add, add_sub_cancel]
      rw [Equiv.Perm.smul_def, e, Equiv.Perm.mul_apply]
      exact (ρ ^ b).injective.eq_iff
    rw [h1, MulAction.zpow_smul_eq_iff_period_dvd]
  have hodd : ∀ k : ℤ, ¬ (d : ℤ) ∣ 2 * k + 1 := fun k hdv => by
    have h1 : (ρ ^ (-k - 1)) x = (ρ ^ k) x := (heq _ _).mpr (by
      have : -k - 1 - k = -(2 * k + 1) := by ring
      rw [this]
      exact (dvd_neg).mpr hdv)
    exact hfree _ ((hτk k).trans h1)
  obtain ⟨e, he⟩ : ∃ e : ℕ, d = 2 * e := by
    rcases Nat.even_or_odd' d with ⟨e, h | h⟩
    · exact ⟨e, h⟩
    · exact absurd (show (d : ℤ) ∣ 2 * e + 1 by rw [h]; push_cast; rfl) (hodd e)
  have he0 : 0 < e := by omega
  have hdz : (d : ℤ) = 2 * e := by exact_mod_cast he
  have hstep : ∀ a, TwoOrb τ σ a (ρ a) := fun a => .trans _ _ _ (TwoOrb.left τ σ a)
    (TwoOrb.right τ σ (τ a))
  have hpow : ∀ n : ℕ, TwoOrb τ σ x ((ρ ^ n) x) := fun n => by
    induction n with
    | zero => exact .refl _
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact .trans _ _ _ ih (hstep _)
  have hP : ∀ a b, TwoOrb τ σ a b → ((∃ k : ℤ, a = (ρ ^ k) x) ↔ ∃ k : ℤ, b = (ρ ^ k) x) := by
    have h1 : ∀ a, (∃ k : ℤ, a = (ρ ^ k) x) → ∃ k : ℤ, τ a = (ρ ^ k) x := by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, hτk k⟩
    have h2 : ∀ a, (∃ k : ℤ, a = (ρ ^ k) x) → ∃ k : ℤ, σ a = (ρ ^ k) x := by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, hσk k⟩
    intro a b h
    induction h with
    | rel a b h =>
      rcases h with rfl | rfl
      · exact ⟨h1 a, fun h' => by simpa [hτ a] using h1 _ h'⟩
      · exact ⟨h2 a, fun h' => by simpa [hσ a] using h2 _ h'⟩
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ i1 i2 => exact i1.trans i2
  refine ⟨(ρ ^ e) x, ?_, ?_, hpow e, ?_⟩
  · intro h
    have h1 : (ρ ^ (e : ℤ)) x = (ρ ^ (0 : ℤ)) x := by simpa using h
    have h2 := (heq _ _).mp h1
    rw [hdz, sub_zero] at h2
    have := Int.le_of_dvd (by omega) h2
    omega
  · rw [← zpow_natCast ρ e, hσk]
    refine (heq _ _).mpr ?_
    rw [hdz]
    exact ⟨-1, by ring⟩
  · intro z hz hzf
    obtain ⟨k, rfl⟩ := (hP _ _ hz).mp ⟨0, by simp⟩
    rw [hσk] at hzf
    have h1 := (heq _ _).mp hzf
    rw [hdz] at h1
    obtain ⟨r, hr⟩ := h1
    have hk : k = -(e * r) := by nlinarith
    rcases Int.even_or_odd' r with ⟨l, rfl | rfl⟩
    · left
      have h2 : (ρ ^ k) x = (ρ ^ (0 : ℤ)) x := (heq _ _).mpr (by
        rw [hdz]
        exact ⟨-l, by rw [hk]; ring⟩)
      simpa using h2
    · right
      have h2 : (ρ ^ k) x = (ρ ^ (e : ℤ)) x := (heq _ _).mpr (by
        rw [hdz]
        exact ⟨-l - 1, by rw [hk]; ring⟩)
      simpa using h2

/-- Cutting a cycle or a path at one link `c, c'`, where `d, d'` are the other ends, gives two
pieces, and `c` and `c'` lie
in different pieces. -/
theorem cut_classes [Finite G] {τ π σ : G → G} (hτ : Involutive τ) (hπ : Involutive π)
  (hσ : Involutive σ)
    (hfree : ∀ a, τ a ≠ a) (hs : ∀ a, σ a = a ∨ σ a = π a) {c c' d d' : G} (hcc : π c = c')
      (hc1 : σ c = c) (hc2 : σ c' = c')
    (hd1 : σ d = d) (hd2 : σ d' = d') (hne : c ≠ c') (hne1 : d ≠ c) (hne2 : d ≠ c') (hne3 : d' ≠ c)
      (hne4 : d' ≠ c')
    (hne5 : d ≠ d') (hod : TwoOrb τ π c d) (hod' : TwoOrb τ π c d') (hπd : π d = d ∨ π d = d')
      (hπd' : π d' = d ∨ π d' = d')
    (hfix : ∀ g, TwoOrb τ π c g → σ g = g → g = c ∨ g = c' ∨ g = d ∨ g = d') :
    ¬ TwoOrb τ σ c c' ∧ ∀ g, TwoOrb τ π c g → TwoOrb τ σ c g ∨ TwoOrb τ σ c' g := by
  have hsub : ∀ a b, TwoOrb τ σ a b → TwoOrb τ π a b := by
    intro a b h
    induction h with
    | rel a b h =>
      rcases h with rfl | rfl
      · exact TwoOrb.left _ _ _
      · rcases hs a with h1 | h1
        · rw [h1]
          exact .refl _
        · rw [h1]
          exact TwoOrb.right _ _ _
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ i1 i2 => exact .trans _ _ _ i1 i2
  have hcc' : π c' = c := by rw [← hcc, hπ]
  have hcpo : TwoOrb τ π c c' := hcc ▸ TwoOrb.right τ π c
  /- A set closed under the two maps that contains `c` contains its orbit. -/
  have hclosed : ∀ Q : Set G, c ∈ Q → (∀ a ∈ Q, τ a ∈ Q) → (∀ a ∈ Q, π a ∈ Q) → ∀ g, TwoOrb τ π c g
    → g ∈ Q := by
    intro Q hc h1 h2 g hg
    have h3 : ∀ a b, TwoOrb τ π a b → (a ∈ Q ↔ b ∈ Q) := by
      intro a b h
      induction h with
      | rel a b h =>
        rcases h with rfl | rfl
        · exact ⟨h1 a, fun h' => by simpa [hτ a] using h1 _ h'⟩
        · exact ⟨h2 a, fun h' => by simpa [hπ a] using h2 _ h'⟩
      | refl _ => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ i1 i2 => exact i1.trans i2
    exact (h3 _ _ hg).mp hc
  have hσstep : ∀ a b, TwoOrb τ σ a a → b = σ a → TwoOrb τ σ a b := fun a b _ h
    => h ▸ TwoOrb.right τ σ a
  obtain ⟨y, hy1, hy2, hy3, hy4⟩ := exists_other_end hτ hσ hfree hc1
  obtain ⟨y', hy1', hy2', hy3', hy4'⟩ := exists_other_end hτ hσ hfree hc2
  have hno : ¬ TwoOrb τ σ c c' := by
    intro hc
    have hyc : y = c' := by
      rcases hy4 c' hc hc2 with h | h
      · exact absurd h.symm hne
      · exact h.symm
    subst hyc
    have h1 := hclosed {g | TwoOrb τ σ c g} (.refl _) (fun a ha => .trans _ _ _ ha
      (TwoOrb.left _ _ _)) (fun a ha => by
      rcases hs a with h | h
      · rcases hy4 a ha h with rfl | rfl
        · rw [hcc]
          exact hc
        · rw [hcc']
          exact .refl _
      · rw [← h]
        exact .trans _ _ _ ha (TwoOrb.right _ _ _)) d hod
    rcases hy4 d h1 hd1 with h | h
    · exact hne1 h
    · exact hne2 h
  refine ⟨hno, ?_⟩
  have hyO : TwoOrb τ π c y := hsub _ _ hy3
  have hyO' : TwoOrb τ π c y' := .trans _ _ _ hcpo (hsub _ _ hy3')
  have hyd : y = d ∨ y = d' := by
    rcases hfix y hyO hy2 with h | h | h | h
    · exact absurd h hy1
    · exact absurd (h ▸ hy3) hno
    · exact .inl h
    · exact .inr h
  have hyd' : y' = d ∨ y' = d' := by
    rcases hfix y' hyO' hy2' with h | h | h | h
    · exact absurd (.symm _ _ (h ▸ hy3')) hno
    · exact absurd h hy1'
    · exact .inl h
    · exact .inr h
  have hyy : y ≠ y' := fun h => hno (.trans _ _ _ hy3 (.symm _ _ (h ▸ hy3')))
  have hdd : ∀ g, g = d ∨ g = d' → TwoOrb τ σ c g ∨ TwoOrb τ σ c' g := by
    intro g hg
    rcases hyd with rfl | rfl <;> rcases hyd' with rfl | rfl <;> rcases hg with rfl | rfl <;>
      first
        | exact absurd rfl hyy
        | exact .inl hy3
        | exact .inr hy3'
  let Q : Set G := {g | TwoOrb τ σ c g ∨ TwoOrb τ σ c' g}
  intro g hg
  refine hclosed Q (.inl (.refl _)) ?_ ?_ g hg
  · rintro a (ha | ha)
    · exact .inl (.trans _ _ _ ha (TwoOrb.left _ _ _))
    · exact .inr (.trans _ _ _ ha (TwoOrb.left _ _ _))
  · intro a ha
    have hao : TwoOrb τ π c a := by
      rcases ha with ha | ha
      · exact hsub _ _ ha
      · exact .trans _ _ _ hcpo (hsub _ _ ha)
    rcases hs a with h | h
    · rcases hfix a hao h with rfl | rfl | rfl | rfl
      · rw [hcc]
        exact .inr (.refl _)
      · rw [hcc']
        exact .inl (.refl _)
      · exact hdd _ (by rcases hπd with h' | h' <;> simp [h'])
      · exact hdd _ (by rcases hπd' with h' | h' <;> simp [h'])
    · rw [← h]
      rcases ha with ha | ha
      · exact .inl (.trans _ _ _ ha (TwoOrb.right _ _ _))
      · exact .inr (.trans _ _ _ ha (TwoOrb.right _ _ _))

end GraphMinor.Surface

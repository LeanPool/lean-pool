/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.NetExistsCut

/-!
# Joining the two halves of an edge

We cut a surface along lines, so an edge of a drawing, which may be a loop, is first split at a
middle point into two lines. The middle
point is not a point where a seam may end. So the lifts of the two halves must be joined into two
lifts of the whole edge. At a point of
a cuff exactly two ends of arcs meet (`exists_ends`), and over the middle point there are four ends.
This pairs them up (`exists_halves_join`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

section

variable {S : Type*} {Y : Type u} [TopologicalSpace S] [TopologicalSpace Y] {E R : Type*} [Finite
  E] [Finite R]
  {a₀ : (E × Bool) ⊕ R → ℝ → S} {innerR : R → Prop} {ψ : Y → S} {ξ η : (E × Bool) ⊕ R → ℝ → Y}

/-- The four ends of the two halves of an edge over the middle point `m` pair up, each end of the
first half with an end of the second. -/
theorem exists_halves_join (h : IsNetCut a₀ (Sum.elim (fun _ => True) innerR) ψ ξ η)
  (hY : IsSurface Y) (e : E) {m : S}
    (hm : ∀ k, ∀ v ∈ Icc (0 : ℝ) 1, a₀ k v = m ↔ (k = .inl (e, true) ∧ v = 1) ∨ (k = .inl
      (e, false) ∧ v = 0)) :
    ∃ ξ₂ η₂ : ℝ → Y, ((ξ₂ = ξ (.inl (e, false)) ∧ η₂ = η (.inl (e, false))) ∨ (ξ₂ = η (.inl
      (e, false)) ∧ η₂ = ξ (.inl (e, false)))) ∧
      ξ (.inl (e, true)) 1 = ξ₂ 0 ∧ η (.inl (e, true)) 1 = η₂ 0 ∧ ξ (.inl (e, true)) 1 ≠ η (.inl
        (e, true)) 1 := by
  classical
  have : Finite (NetArc (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop)) := inferInstance
  have hfam := h.isArcFamily
  set i₁ : (E × Bool) ⊕ R := .inl (e, true) with hi₁
  set i₂ : (E × Bool) ⊕ R := .inl (e, false) with hi₂
  set p₁ := ξ i₁ 1 with hp₁
  set p₂ := η i₁ 1 with hp₂
  set p₃ := ξ i₂ 0 with hp₃
  set p₄ := η i₂ 0 with hp₄
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  set A₁ : NetArc (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop)
    := ⟨(i₁, true), .inl rfl⟩
  set A₂ : NetArc (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop)
    := ⟨(i₁, false), .inr trivial⟩
  set A₃ : NetArc (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop)
    := ⟨(i₂, true), .inl rfl⟩
  set A₄ : NetArc (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop)
    := ⟨(i₂, false), .inr trivial⟩
  set ℓ := netL ξ η (inner := (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop)) with hℓ
  have o1 : ofs true (1 : ℝ) = 1 := by simp [ofs]
  have o0 : ofs false (1 : ℝ) = 0 := by simp [ofs]
  have v₁ : ℓ A₁ (ofs true 1) = p₁ := by rw [o1]; rfl
  have v₂ : ℓ A₂ (ofs true 1) = p₂ := by rw [o1]; rfl
  have v₃ : ℓ A₃ (ofs false 1) = p₃ := by rw [o0]; rfl
  have v₄ : ℓ A₄ (ofs false 1) = p₄ := by rw [o0]; rfl
  have hcases : ∀ (β : NetArc (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop))
    (s : Bool), ψ (ℓ β (ofs s 1)) = m → (β, s) = (A₁, true) ∨ (β, s) = (A₂, true) ∨
      (β, s) = (A₃, false) ∨ (β, s) = (A₄, false) := by
    rintro ⟨⟨k, b⟩, hb⟩ s he
    have hs : ofs s (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by cases s <;> simp [ofs]
    rw [h.ψ_netL _ hs] at he
    rcases (hm k _ hs).mp he with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · obtain rfl : s = true := by
        cases s
        · simp [ofs] at h2
        · rfl
      cases b
      · exact .inr (.inl rfl)
      · exact .inl rfl
    · obtain rfl : s = false := by
        cases s
        · rfl
        · simp [ofs] at h2
      cases b
      · exact .inr (.inr (.inr rfl))
      · exact .inr (.inr (.inl rfl))
  have ψ₁ : ψ p₁ = m := by rw [hp₁, h.hξ _ _ h1]; exact (hm _ _ h1).mpr (.inl ⟨rfl, rfl⟩)
  have ψ₂ : ψ p₂ = m := by rw [hp₂, h.hη _ _ h1]; exact (hm _ _ h1).mpr (.inl ⟨rfl, rfl⟩)
  have ψ₃ : ψ p₃ = m := by rw [hp₃, h.hξ _ _ h0]; exact (hm _ _ h0).mpr (.inr ⟨rfl, rfl⟩)
  have ψ₄ : ψ p₄ = m := by rw [hp₄, h.hη _ _ h0]; exact (hm _ _ h0).mpr (.inr ⟨rfl, rfl⟩)
  have hA12 : A₁ ≠ A₂ := fun he => by simpa [A₁, A₂] using congrArg (fun x => x.1.2) he
  have hA34 : A₃ ≠ A₄ := fun he => by simpa [A₃, A₄] using congrArg (fun x => x.1.2) he
  have hpart : ∀ (A : NetArc (Sum.elim (fun _ => True) innerR : (E × Bool) ⊕ R → Prop))
    (s : Bool), ψ (ℓ A (ofs s 1)) = m → (A, s) = (A₁, true) ∨ (A, s) = (A₂, true) ∨
      (A, s) = (A₃, false) ∨ (A, s) = (A₄, false) → ((A, s) ≠ (A₁, true) ∧ p₁ = ℓ A (ofs s 1)) ∨
        ((A, s) ≠ (A₂, true) ∧ p₂ = ℓ A (ofs s 1)) ∨
        ((A, s) ≠ (A₃, false) ∧ p₃ = ℓ A (ofs s 1)) ∨ ((A, s) ≠ (A₄, false) ∧ p₄ = ℓ A (ofs s 1))
          := by
    intro A s hψ _
    obtain ⟨⟨β, s', hne, he⟩, -⟩ := exists_ends hY hfam A s
    have hc := hcases β s' (by rw [he]; exact hψ)
    rcases hc with hc | hc | hc | hc <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    · exact .inl ⟨hne.symm, by rw [← he, v₁]⟩
    · exact .inr (.inl ⟨hne.symm, by rw [← he, v₂]⟩)
    · exact .inr (.inr (.inl ⟨hne.symm, by rw [← he, v₃]⟩))
    · exact .inr (.inr (.inr ⟨hne.symm, by rw [← he, v₄]⟩))
  have t12 : ¬ (p₂ = p₁ ∧ p₃ = p₁) := fun ⟨h2, h3⟩ => by
    have := (exists_ends hY hfam A₁ true).2 A₂ A₃ true false (by rw [v₂, v₁, h2])
      (by rw [v₃, v₁, h3])
    simp [hA12.symm, Prod.ext_iff] at this
  have t13 : ¬ (p₂ = p₁ ∧ p₄ = p₁) := fun ⟨h2, h3⟩ => by
    have := (exists_ends hY hfam A₁ true).2 A₂ A₄ true false (by rw [v₂, v₁, h2])
      (by rw [v₄, v₁, h3])
    simp [hA12.symm, Prod.ext_iff] at this
  have t23 : ¬ (p₃ = p₁ ∧ p₄ = p₁) := fun ⟨h2, h3⟩ => by
    have := (exists_ends hY hfam A₁ true).2 A₃ A₄ false false (by rw [v₃, v₁, h2])
      (by rw [v₄, v₁, h3])
    simp [hA34, Prod.ext_iff] at this
  have q₁ := hpart A₁ true (by rw [v₁]; exact ψ₁) (.inl rfl)
  have q₂ := hpart A₂ true (by rw [v₂]; exact ψ₂) (.inr (.inl rfl))
  have q₃ := hpart A₃ false (by rw [v₃]; exact ψ₃) (.inr (.inr (.inl rfl)))
  rw [v₁] at q₁
  rw [v₂] at q₂
  rw [v₃] at q₃
  have q₁' : p₂ = p₁ ∨ p₃ = p₁ ∨ p₄ = p₁ := by
    rcases q₁ with ⟨h2, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd rfl h2
    · exact .inl h2
    · exact .inr (.inl h2)
    · exact .inr (.inr h2)
  have q₂' : p₁ = p₂ ∨ p₃ = p₂ ∨ p₄ = p₂ := by
    rcases q₂ with ⟨-, h2⟩ | ⟨h2, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · exact .inl h2
    · exact absurd rfl h2
    · exact .inr (.inl h2)
    · exact .inr (.inr h2)
  have q₃' : p₁ = p₃ ∨ p₂ = p₃ ∨ p₄ = p₃ := by
    rcases q₃ with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h2, -⟩ | ⟨-, h2⟩
    · exact .inl h2
    · exact .inr (.inl h2)
    · exact absurd rfl h2
    · exact .inr (.inr h2)
  have hnot : p₂ ≠ p₁ := by
    intro h2
    have h3 : p₃ ≠ p₁ := fun h4 => t12 ⟨h2, h4⟩
    have h4 : p₄ ≠ p₁ := fun h5 => t13 ⟨h2, h5⟩
    have h5 : p₄ = p₃ := by
      rcases q₃' with h6 | h6 | h6
      · exact absurd h6.symm h3
      · exact absurd (h6.symm.trans h2) h3
      · exact h6
    have key : ∀ p q, Relation.EqvGen (fun p q ↦ ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ k u ∧ q
      = η k u) p q → (p = p₁ ↔ q = p₁) := by
      intro p q hr
      induction hr with
      | rel p q hs =>
        obtain ⟨k, u, hu, rfl, rfl⟩ := hs
        constructor
        · intro h6
          have h7 : a₀ k u = m := by rw [← h.hξ k u hu, h6, ψ₁]
          rcases (hm k u hu).mp h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h2
          · exact absurd h6 h3
        · intro h6
          have h7 : a₀ k u = m := by rw [← h.hη k u hu, h6, ψ₁]
          rcases (hm k u hu).mp h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact absurd h6 h4
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
    exact h3 ((key _ _ (h.fib p₁ p₃ (ψ₁.trans ψ₃.symm))).mp rfl)
  rcases q₁' with h2 | h2 | h2
  · exact absurd h2 hnot
  · refine ⟨ξ i₂, η i₂, .inl ⟨rfl, rfl⟩, h2.symm, ?_, fun h3 => hnot h3.symm⟩
    rcases q₂' with h3 | h3 | h3
    · exact absurd h3.symm hnot
    · exact absurd (h3.symm.trans h2) hnot
    · exact h3.symm
  · refine ⟨η i₂, ξ i₂, .inr ⟨rfl, rfl⟩, h2.symm, ?_, fun h3 => hnot h3.symm⟩
    rcases q₂' with h3 | h3 | h3
    · exact absurd h3.symm hnot
    · exact h3.symm
    · exact absurd (h3.symm.trans h2) hnot

omit [TopologicalSpace S] [TopologicalSpace Y] in
theorem psi_conc2 {ψ : Y → S} {x x' : ℝ → Y} {c : ℝ → S} (h1 : ∀ u ∈ Icc (0 : ℝ) 1, ψ (x u) = c
  (u / 2)) (h2 : ∀ u ∈ Icc (0 : ℝ) 1, ψ (x' u) = c ((1 + u) / 2))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : ψ (conc2 x x' u) = c u := by
  unfold conc2
  split_ifs with h
  · rw [h1 _ ⟨by linarith [hu.1], by linarith⟩]
    congr 1
    ring
  · push Not at h
    rw [h2 _ ⟨by linarith, by linarith [hu.2]⟩]
    congr 1
    ring

omit [TopologicalSpace Y] in
theorem conc2_mem {x x' : ℝ → Y} {P : Set Y} (h1 : ∀ u ∈ Icc (0 : ℝ) 1, x u ∈ P) (h2 : ∀ u ∈ Icc
  (0 : ℝ) 1, x' u ∈ P) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    conc2 x x' u ∈ P := by
  unfold conc2
  split_ifs with h
  · exact h1 _ ⟨by linarith [hu.1], by linarith⟩
  · push Not at h
    exact h2 _ ⟨by linarith, by linarith [hu.2]⟩

variable {a : E ⊕ R → ℝ → S}

/-- **Joining halves.** Cuts along the two halves of each edge give a cut along the whole edges. -/
theorem exists_merged_cut (h : IsNetCut a₀ (Sum.elim (fun _ => True) innerR) ψ ξ η)
  (hY : IsSurface Y)
    (a1 : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, a₀ (.inl (e, true)) u = a (.inl e) (u / 2))
    (a2 : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, a₀ (.inl (e, false)) u = a (.inl e) ((1 + u) / 2))
    (a3 : ∀ r, ∀ u ∈ Icc (0 : ℝ) 1, a₀ (.inr r) u = a (.inr r) u)
    (hm : ∀ e k, ∀ v ∈ Icc (0 : ℝ) 1, a₀ k v = a (.inl e) (1 / 2) ↔ (k = .inl (e, true) ∧ v = 1) ∨
      (k = .inl (e, false) ∧ v = 0))
    (inj : ∀ k, InjOn (a k) (Ioo 0 1)) (meet : ∀ k k', k ≠ k' → ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Icc
      (0 : ℝ) 1, a k u ≠ a k' v)
    (self : ∀ k, ∀ u ∈ Ioo (0 : ℝ) 1, a k u ≠ a k 0 ∧ a k u ≠ a k 1) :
    ∃ ξ' η' : E ⊕ R → ℝ → Y, IsNetCut a (Sum.elim (fun _ => True) innerR) ψ ξ' η' := by
  have hj := fun e => exists_halves_join h hY e (hm e)
  choose ξ₂ η₂ c1 c2 c3 c4 using hj
  have cξ₂ : ∀ e, ContinuousOn (ξ₂ e) (Icc 0 1) := fun e => by
    rcases c1 e with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact h.cξ _
    · exact h.cη _
  have cη₂ : ∀ e, ContinuousOn (η₂ e) (Icc 0 1) := fun e => by
    rcases c1 e with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
    · exact h.cη _
    · exact h.cξ _
  have ψξ₂ : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, ψ (ξ₂ e u) = a (.inl e) ((1 + u) / 2) := fun e u hu => by
    rw [← a2 e u hu]
    rcases c1 e with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact h.hξ _ u hu
    · exact h.hη _ u hu
  have ψη₂ : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, ψ (η₂ e u) = a (.inl e) ((1 + u) / 2) := fun e u hu => by
    rw [← a2 e u hu]
    rcases c1 e with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
    · exact h.hη _ u hu
    · exact h.hξ _ u hu
  have bξ₂ : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, ξ₂ e u ∈ bd Y := fun e u hu => by
    rcases c1 e with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact h.bdξ _ u hu
    · exact h.bdη _ u hu
  have bη₂ : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, η₂ e u ∈ bd Y := fun e u hu => by
    rcases c1 e with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
    · exact h.bdη _ u hu
    · exact h.bdξ _ u hu
  have ne₂ : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, ξ₂ e u ≠ η₂ e u := fun e u hu => by
    rcases c1 e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact h.ne (.inl (e, false)) trivial u hu
    · exact (h.ne (.inl (e, false)) trivial u hu).symm
  refine ⟨Sum.elim (fun e => conc2 (ξ (.inl (e, true))) (ξ₂ e)) fun r => ξ (.inr r),
    Sum.elim (fun e => conc2 (η (.inl (e, true))) (η₂ e)) fun r => η (.inr r), ⟨h.cont, h.surj, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inj, meet, self⟩⟩
  · rintro (e | r)
    · exact continuousOn_conc2 (h.cξ _) (cξ₂ e) (c2 e)
    · exact h.cξ _
  · rintro (e | r)
    · exact continuousOn_conc2 (h.cη _) (cη₂ e) (c3 e)
    · exact h.cη _
  · rintro (e | r) u hu
    · exact psi_conc2 (fun u hu => by rw [h.hξ _ u hu]; exact a1 e u hu) (ψξ₂ e) hu
    · rw [Sum.elim_inr, h.hξ _ u hu]
      exact a3 r u hu
  · rintro (e | r) u hu
    · exact psi_conc2 (fun u hu => by rw [h.hη _ u hu]; exact a1 e u hu) (ψη₂ e) hu
    · rw [Sum.elim_inr, h.hη _ u hu]
      exact a3 r u hu
  · rintro (e | r) u hu
    · exact conc2_mem (h.bdξ _) (bξ₂ e) hu
    · exact h.bdξ _ u hu
  · rintro (e | r) u hu
    · exact conc2_mem (h.bdη _) (bη₂ e) hu
    · exact h.bdη _ u hu
  · rintro (e | r) hi u hu
    · simp only [Sum.elim_inl]
      unfold conc2
      rcases lt_trichotomy u (1 / 2) with hlt | rfl | hgt
      · rw [ite_eq_left hlt.le, ite_eq_left hlt.le]
        exact h.ne (.inl (e, true)) trivial _ ⟨by linarith [hu.1], by linarith⟩
      · rw [ite_eq_left le_rfl, ite_eq_left le_rfl]
        simpa using c4 e
      · rw [ite_eq_right (not_le.mpr hgt), ite_eq_right (not_le.mpr hgt)]
        exact ne₂ e _ ⟨by linarith, by linarith [hu.2]⟩
    · exact h.ne (.inr r) hi u hu
  · rintro (e | r) hi u hu
    · exact absurd trivial hi
    · exact h.eqb (.inr r) hi u hu
  · intro y hy
    obtain ⟨k, u, hu, he⟩ := h.cover y hy
    rcases k with ⟨e, _ | _⟩ | r
    · have hv : (1 + u) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have e1 : Sum.elim (fun e => conc2 (ξ (.inl (e, true))) (ξ₂ e)) (fun r => ξ (.inr r))
        (.inl e) ((1 + u) / 2) = ξ₂ e u := conc2_right (c2 e) hu
      have e2 : Sum.elim (fun e => conc2 (η (.inl (e, true))) (η₂ e)) (fun r => η (.inr r))
        (.inl e) ((1 + u) / 2) = η₂ e u := conc2_right (c3 e) hu
      refine ⟨.inl e, _, hv, ?_⟩
      rw [e1, e2]
      rcases c1 e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact he
      · exact he.symm
    · have hv : u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      refine ⟨.inl e, _, hv, ?_⟩
      simp only [Sum.elim_inl, conc2_left hu]
      exact he
    · exact ⟨.inr r, u, hu, he⟩
  · intro y y' he
    have hr := h.fib y y' he
    clear he
    induction hr with
    | rel p q hs =>
      obtain ⟨k, u, hu, rfl, rfl⟩ := hs
      rcases k with ⟨e, _ | _⟩ | r
      · have hv : (1 + u) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have e1 : Sum.elim (fun e => conc2 (ξ (.inl (e, true))) (ξ₂ e)) (fun r => ξ (.inr r))
          (.inl e) ((1 + u) / 2) = ξ₂ e u := conc2_right (c2 e) hu
        have e2 : Sum.elim (fun e => conc2 (η (.inl (e, true))) (η₂ e)) (fun r => η (.inr r))
          (.inl e) ((1 + u) / 2) = η₂ e u := conc2_right (c3 e) hu
        rcases c1 e with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .rel _ _ ⟨.inl e, _, hv, by rw [e1, h1], by rw [e2, h2]⟩
        · exact .symm _ _ (.rel _ _ ⟨.inl e, _, hv, by rw [e1, h1], by rw [e2, h2]⟩)
      · have hv : u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        exact .rel _ _ ⟨.inl e, _, hv, by simp only [Sum.elim_inl, conc2_left hu],
          by simp only [Sum.elim_inl, conc2_left hu]⟩
      · exact .rel _ _ ⟨.inr r, u, hu, rfl, rfl⟩
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2

end

end GraphMinor.GM07

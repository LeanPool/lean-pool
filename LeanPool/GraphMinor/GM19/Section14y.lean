/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14x

/-!
# Graph Minors XIX, Section 14: the frame `Φ'`

The frame `Φ'` in `Σ'` has as vertices the vertices of `Γ` next to the singular vertices of `R*`. A
side of `Φ'` is short if it contains a singular vertex.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

section Arcs

variable {X : Type} [TopologicalSpace X] [T2Space X] (hX : IsSurface X) {N N' : Set X}

include hX

/-- An arc for `N'` with its ends in `N` is an arc for `N`. -/
theorem arc_mem_of_ends (hN : N.Finite) (h2 : ∀ C : cuffs X, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q)
  (hN' : N'.Finite) (h2' : ∀ C : cuffs X, ∃ p ∈ N' ∩ C.1, ∃ q ∈ N' ∩ C.1, p ≠ q)
    (hsub : N ⊆ N') {c : Set X} (hc : c ∈ arcComponentsIn (bd X \ N'))
      (ht : tilde c ⊆ N) : c ∈ arcComponentsIn (bd X \ N) := by
  have hcs : c ⊆ bd X \ N := fun y hy ↦ ⟨(hc.2.1 hy).1, fun h ↦ (hc.2.1 hy).2 (hsub h)⟩
  obtain ⟨s, hs, hcs'⟩ := exists_arcComp_superset hc.2.2.1 hcs
  obtain ⟨C, a, b, hab, hub, he, -, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) hN' h2' hc
  obtain ⟨C', a', b', hab', hub', he', hd, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) hN h2 hs
  obtain rfl : C = C' := by
    by_contra hne
    obtain ⟨x, hx⟩ := hc.1
    exact disjoint_left.mp (cuffs_disjoint' hne) (arcOf_subset _ _ _ (he ▸ hx)) (arcOf_subset _ _ _
      (he' ▸ hcs' hx))
  have hsubarc : arcOf (cuffPar hX C) a b ⊆ arcOf (cuffPar hX C) a' b' := by
    rw [← he, ← he']
    exact hcs'
  obtain ⟨m, h₁, h₂⟩ := exists_shift (cuffPar hX C) hab' hab hub' hsubarc
  have hta : cuffPoint (cuffPar hX C) a ∈ N := ht (by rw [he, tilde_arcOf _ hab hub]; simp)
  have htb : cuffPoint (cuffPar hX C) b ∈ N := ht (by rw [he, tilde_arcOf _ hab hub]; simp)
  have hnot : ∀ t, cuffPoint (cuffPar hX C) t ∈ N → t ∉ Ioo a' b' := fun t ht₁ ht₂ ↦
    disjoint_left.mp hd (he' ▸ ⟨t, ht₂, rfl⟩) ht₁
  have hpi := Real.pi_pos
  have e₁ : a' = a + m * (2 * Real.pi) := by
    by_contra hne
    exact hnot (a + m * (2 * Real.pi))
      (by rw [cuffPoint_shift]; exact hta) ⟨lt_of_le_of_ne h₁ hne, by linarith⟩
  have e₂ : b' = b + m * (2 * Real.pi) := by
    by_contra hne
    exact hnot (b + m * (2 * Real.pi))
      (by rw [cuffPoint_shift]; exact htb) ⟨by linarith, lt_of_le_of_ne h₂ (Ne.symm hne)⟩
  have : c = s := by rw [he, he', e₁, e₂, arcOf_shift]
  exact this ▸ hs

/-- At most two arcs end at a point. -/
theorem three_arcs (hN : N.Finite) (h2 : ∀ C : cuffs X, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) {c₁ c₂
  c₃ : Set X} (h₁ : c₁ ∈ arcComponentsIn (bd X \ N)) (h₂ : c₂ ∈ arcComponentsIn (bd X \ N))
    (h₃ : c₃ ∈ arcComponentsIn (bd X \ N)) {v : X} (hv₁ : v ∈ tilde c₁) (hv₂ : v ∈ tilde c₂)
      (hv₃ : v ∈ tilde c₃) (h₁₂ : c₁ ≠ c₂) (h₁₃ : c₁ ≠ c₃) (h₂₃ : c₂ ≠ c₃) : False := by
  have key : ∀ {c}, c ∈ arcComponentsIn (bd X \ N) → v ∈ tilde c → ∃ (C : cuffs X) (a b : ℝ), a < b
    ∧ c = arcOf (cuffPar hX C) a b ∧ (v = cuffPoint (cuffPar hX C) a ∨ v = cuffPoint
      (cuffPar hX C) b) := by
    intro c hc hv
    obtain ⟨C, a, b, hab, hub, rfl, -, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) hN h2 hc
    rw [tilde_arcOf _ hab hub] at hv
    exact ⟨C, a, b, hab, rfl, by simpa using hv⟩
  obtain ⟨C₁, a₁, b₁, hab₁, rfl, hv₁'⟩ := key h₁ hv₁
  obtain ⟨C₂, a₂, b₂, hab₂, rfl, hv₂'⟩ := key h₂ hv₂
  obtain ⟨C₃, a₃, b₃, hab₃, rfl, hv₃'⟩ := key h₃ hv₃
  have hcuff : ∀ {C C' : cuffs X} {t t' : ℝ}, v = cuffPoint (cuffPar hX C) t → v = cuffPoint
    (cuffPar hX C') t' → C = C' := fun {C C' t t'} h h' ↦ by
    by_contra hne
    exact disjoint_left.mp (cuffs_disjoint' hne) (h ▸ cuffPoint_mem _ _) (h' ▸ cuffPoint_mem _ _)
  have h12 : C₁ = C₂ := by rcases hv₁' with h | h <;> rcases hv₂' with h' | h' <;> exact hcuff h h'
  have h13 : C₁ = C₃ := by rcases hv₁' with h | h <;> rcases hv₃' with h' | h' <;> exact hcuff h h'
  subst h12 h13
  rcases hv₁' with e₁ | e₁ <;> rcases hv₂' with e₂ | e₂ <;> rcases hv₃' with e₃ | e₃
  · exact h₁₂ (arc_head_eq hab₁ hab₂ h₁ h₂ (e₁.symm.trans e₂))
  · exact h₁₂ (arc_head_eq hab₁ hab₂ h₁ h₂ (e₁.symm.trans e₂))
  · exact h₁₃ (arc_head_eq hab₁ hab₃ h₁ h₃ (e₁.symm.trans e₃))
  · exact h₂₃ (arc_tail_eq hab₂ hab₃ h₂ h₃ (e₂.symm.trans e₃))
  · exact h₂₃ (arc_head_eq hab₂ hab₃ h₂ h₃ (e₂.symm.trans e₃))
  · exact h₁₃ (arc_tail_eq hab₁ hab₃ h₁ h₃ (e₁.symm.trans e₃))
  · exact h₁₂ (arc_tail_eq hab₁ hab₂ h₁ h₂ (e₁.symm.trans e₂))
  · exact h₁₂ (arc_tail_eq hab₁ hab₂ h₁ h₂ (e₁.symm.trans e₂))

/-- An arc inside a side, read in the same sense as the side, has the direction of the side. -/
theorem dirAgrees_arcs (ε : Bool) (hN : N.Finite) (h2 : ∀ C : cuffs X, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩
  C.1, p ≠ q) (hN' : N'.Finite) (h2' : ∀ C : cuffs X, ∃ p ∈ N' ∩ C.1, ∃ q ∈ N' ∩ C.1, p ≠ q) {e s :
    Set X}
    (he : e ∈ arcComponentsIn (bd X \ N')) (hs : s ∈ arcComponentsIn (bd X \ N)) (hes : e ⊆ s) :
    DirAgrees s (arcMarch hX ε s) e (arcMarch hX ε e) := by
  obtain ⟨C, a, b, hab, hub, hse, -, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) hN h2 hs
  obtain ⟨C', a', b', hab', hub', hee, -, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) hN' h2' he
  obtain ⟨C₁, a₁, b₁, hab₁, hub₁, hs₁, hl₁⟩ := arcMarch_spec hX ε hab hub hse
  obtain ⟨C₂, a₂, b₂, hab₂, hub₂, he₂, hl₂⟩ := arcMarch_spec hX ε hab' hub' hee
  rw [hl₁, hl₂]
  have hC : C₂ = C₁ := by
    by_contra hne
    obtain ⟨x, hx⟩ := he.1
    have h₁ : x ∈ C₁.1 := arcOf_subset _ _ _ (hs₁ ▸ hes hx)
    have h₂ : x ∈ C₂.1 := arcOf_subset _ _ _ (he₂ ▸ hx)
    exact disjoint_left.mp (cuffs_disjoint' hne) h₂ h₁
  subst hC
  obtain ⟨m, h₁, h₂⟩ := exists_shift (cuffPar hX C₂) hab₁ hab₂ hub₁ (by
    rw [← he₂, ← hs₁]
    exact hes)
  have hshift := arcOf_shift (cuffPar hX C₂) a₂ b₂ m
  have hp₁ := cuffPoint_shift (cuffPar hX C₂) a₂ m
  have hp₂ := cuffPoint_shift (cuffPar hX C₂) b₂ m
  rw [hs₁, he₂, ← hshift, ← hp₁, ← hp₂]
  have hlt : a₂ + m * (2 * Real.pi) < b₂ + m * (2 * Real.pi) := by linarith
  cases ε
  · simpa using dirAgrees_forward (cuffPar hX C₂) hub₁ h₁ hlt h₂
  · simpa using dirAgrees_backward (cuffPar hX C₂) hub₁ h₁ hlt h₂

end Arcs

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The direction of the arcs of each cuff. -/
noncomputable def flipOf {X : Type} [TopologicalSpace X] (ε : Set X → Bool) (e : Set X) : Bool := by
  classical exact decide (∃ C ∈ cuffs X, (e ∩ C).Nonempty ∧ ε C = true)

theorem flipOf_eq {X : Type} [TopologicalSpace X] (ε : Set X → Bool) {e C : Set X}
  (hC : C ∈ cuffs X) (he : e.Nonempty) (hs : e ⊆ C) : flipOf ε e = ε C := by
  classical
  have key : (∃ C' ∈ cuffs X, (e ∩ C').Nonempty ∧ ε C' = true) ↔ ε C = true := by
    constructor
    · rintro ⟨C', hC', ⟨x, hx, hx'⟩, h⟩
      obtain rfl : C = C' := by
        by_contra hne
        exact disjoint_left.mp (cuffs_disjoint hC hC' hne) (hs hx) hx'
      exact h
    · intro h
      obtain ⟨x, hx⟩ := he
      exact ⟨C, hC, ⟨x, hx, hs hx⟩, h⟩
  simp only [flipOf, key, Bool.decide_eq_true]

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)

/-- The singular places on the rim of a wheel: the last one, and those where the two spokes have
different inner ends. -/
def sing (W : ↥s.𝒲) : Set ℕ := {i | i < (s.fr W).R.k ∧ (i + 1 = (s.fr W).R.k ∨ ¬ (s.fr W).Reg i)}

/-- The point of `Σ'` at the `i`th vertex of `R*` on the rim of a wheel. -/
noncomputable def zx (W : ↥s.𝒲) (i : ℕ) : ↥Tᶜ := (s.arc_reg W i).choose

theorem zx_arc (W : ↥s.𝒲) (i : ℕ) : s.zx W i ∈ s.arc W i := (s.arc_reg W i).choose_spec.1

theorem e_zx (W : ↥s.𝒲) (i : ℕ) : s.e (s.zx W i) = (s.fr W).R.reg i := (s.arc_reg W i).choose_spec.2

/-- The vertices of the frame. -/
noncomputable def markN : Set ↥Tᶜ := ⋃ W, ⋃ i ∈ s.sing W, {s.vx W i, s.vx W (i + 1)}

/-- The singular vertices of `R*`. -/
noncomputable def markZ : Set ↥Tᶜ := ⋃ W, ⋃ i ∈ s.sing W, {s.zx W i}

include s

theorem finite_sing (W : ↥s.𝒲) : (s.sing W).Finite := (finite_lt_nat _).subset fun _ h ↦ h.1

theorem finite_𝒲 : Finite ↥s.𝒲 := s.cut.finite.to_subtype

theorem finite_markN : s.markN.Finite := by
  have := s.finite_𝒲
  exact finite_iUnion fun W ↦ (s.finite_sing W).biUnion fun i _ ↦ by simp

theorem finite_markZ : s.markZ.Finite := by
  have := s.finite_𝒲
  exact finite_iUnion fun W ↦ (s.finite_sing W).biUnion fun i _ ↦ by simp

theorem markN_sub : s.markN ⊆ s.Nb := by
  intro x hx
  obtain ⟨W, hx⟩ := mem_iUnion.mp hx
  obtain ⟨i, -, hx⟩ := mem_iUnion₂.mp hx
  rcases hx with rfl | hx
  · exact s.vx_N W i
  · exact (mem_singleton_iff.mp hx) ▸ s.vx_N W (i + 1)

theorem last_sing (W : ↥s.𝒲) : (s.fr W).R.k - 1 ∈ s.sing W := by
  have := (s.fr W).R.two
  exact ⟨by omega, .inl (by omega)⟩

theorem vx_succ_last (W : ↥s.𝒲) : s.vx W ((s.fr W).R.k - 1 + 1) = s.vx W 0 := by
  have := (s.fr W).R.two
  rw [show (s.fr W).R.k - 1 + 1 = 0 + (s.fr W).R.k by omega]
  exact s.vx_add_k W 0

theorem exists_wheel (C : cuffs ↥Tᶜ) : ∃ W : ↥s.𝒲, C.1 = s.cf W := by
  obtain ⟨C, hC⟩ := C
  rw [s.cuffs_eq] at hC
  obtain ⟨W, hW, rfl⟩ := hC
  exact ⟨⟨W, hW⟩, rfl⟩

theorem two_marks (C : cuffs ↥Tᶜ) : ∃ p ∈ s.markN ∩ C.1, ∃ q ∈ s.markN ∩ C.1, p ≠ q := by
  obtain ⟨W, hW⟩ := s.exists_wheel C
  rw [hW]
  have hl := s.last_sing W
  have h₁ : s.vx W ((s.fr W).R.k - 1) ∈ s.markN := mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hl, .inl
    rfl⟩⟩
  have h₂ : s.vx W ((s.fr W).R.k - 1 + 1) ∈ s.markN := mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hl,
    .inr rfl⟩⟩
  exact ⟨_, ⟨h₁, s.vx_cf W _⟩, _, ⟨h₂, s.vx_cf W _⟩, s.vx_ne_succ W _⟩

theorem tilde_sing {W : ↥s.𝒲} {i : ℕ} (hi : i ∈ s.sing W) : tilde (s.arc W i) ⊆ s.markN := by
  rw [s.tilde_arc]
  rintro _ (rfl | h)
  · exact mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hi, .inl rfl⟩⟩
  · exact mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hi, .inr h⟩⟩

/-- A singular arc of the rim is a side of the frame. -/
theorem arc_side {W : ↥s.𝒲} {i : ℕ} (hi : i ∈ s.sing W) : s.arc W i ∈ arcComponentsIn
  (bd ↥Tᶜ \ s.markN) :=
  arc_mem_of_ends s.isSurface s.finite_markN s.two_marks s.finite_Nb s.two s.markN_sub
    (s.arc_mem W i) (s.tilde_sing hi)

theorem exists_sing_side {v : ↥Tᶜ} (hv : v ∈ s.markN) : ∃ W, ∃ i ∈ s.sing W, v ∈ tilde (s.arc W i)
  := by
  obtain ⟨W, hv⟩ := mem_iUnion.mp hv
  obtain ⟨i, hi, hv⟩ := mem_iUnion₂.mp hv
  exact ⟨W, i, hi, by rw [s.tilde_arc]; exact hv⟩

/-- The sides with no singular point have no common end. -/
theorem long_disjoint : ∀ s₁ ∈ arcComponentsIn (bd ↥Tᶜ \ s.markN), ∀ s₂ ∈ arcComponentsIn
  (bd ↥Tᶜ \ s.markN), s₁ ≠ s₂ → Disjoint s₁ s.markZ → Disjoint s₂ s.markZ → Disjoint (tilde s₁)
    (tilde s₂) := by
  intro s₁ h₁ s₂ h₂ hne hl₁ hl₂
  refine disjoint_left.mpr fun v hv₁ hv₂ ↦ ?_
  have hX := s.isSurface
  have hv : v ∈ s.markN := by
    obtain ⟨C, a, b, hab, hub, rfl, -, ha, hb⟩ := exists_arc_of_mem hX
      (cuffPar hX) s.finite_markN s.two_marks h₁
    rw [tilde_arcOf _ hab hub] at hv₁
    rcases hv₁ with rfl | h
    · exact ha
    · exact (mem_singleton_iff.mp h) ▸ hb
  obtain ⟨W, i, hi, hvt⟩ := s.exists_sing_side hv
  have hz : s.zx W i ∈ s.markZ := mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hi, rfl⟩⟩
  refine three_arcs hX s.finite_markN s.two_marks h₁ h₂ (s.arc_side hi) hv₁ hv₂ hvt hne ?_ ?_
  · rintro rfl
    exact disjoint_left.mp hl₁ (s.zx_arc W i) hz
  · rintro rfl
    exact disjoint_left.mp hl₂ (s.zx_arc W i) hz

/-- Wheels with a common point on their rims are the same. -/
theorem wheel_eq {W W' : ↥s.𝒲} {x : ↥Tᶜ} (h : x ∈ s.cf W) (h' : x ∈ s.cf W') : W = W' := by
  by_contra hne
  have hne' : W.1 ≠ W'.1 := fun e ↦ hne (Subtype.ext e)
  exact disjoint_left.mp (s.cut.disj W.2 W'.2 hne') (Surface.discBd_subset _ h)
    (Surface.discBd_subset _ h')

/-- An arc lies on the rim of one wheel only. -/
theorem arc_wheel {W W' : ↥s.𝒲} {p q : ℕ} (h : s.arc W p = s.arc W' q) : W = W' := by
  obtain ⟨x, hx, -⟩ := s.arc_reg W p
  exact s.wheel_eq (s.arc_cf W p hx) (s.arc_cf W' q (h ▸ hx))

/-- The two ends of an arc tell us its place on the rim. -/
theorem arc_pos (W : ↥s.𝒲) {p q : ℕ} (hp : p < (s.fr W).R.k) (hq : q < (s.fr W).R.k) (h : s.arc W p
  = s.arc W q) : p = q := by
  have ht := congrArg tilde h
  rw [s.tilde_arc, s.tilde_arc] at ht
  have h₁ : s.vx W p ∈ ({s.vx W q, s.vx W (q + 1)} : Set ↥Tᶜ) := ht ▸ .inl rfl
  rcases h₁ with h₁ | h₁
  · exact s.vx_inj W hp hq h₁
  have h₂ : s.vx W q ∈ ({s.vx W p, s.vx W (p + 1)} : Set ↥Tᶜ) := ht ▸ .inl rfl
  rcases h₂ with h₂ | h₂
  · exact s.vx_inj W hp hq h₂.symm
  exfalso
  have hm := s.vx_mod_eq W h₁
  refine s.vx_ne_add_two W q (h₂.trans ?_)
  apply s.isEmbedding.injective
  rw [s.e_vx, s.e_vx, Rim.vert, Rim.vert]
  congr 2
  rw [show q + 2 = q + 1 + 1 by omega, Nat.add_mod, hm, ← Nat.add_mod]

end Slice

/-- The frame `Φ'`. -/
noncomputable def cutFrame {X : Type} [TopologicalSpace X] [T2Space X] (hX : IsSurface X)
  (N Z : Set X) (ε : Set X → Bool) (hf : N.Finite) (hsub : N ⊆ bd X) (h2 : ∀ C : cuffs X, ∃ p ∈ N ∩
    C.1, ∃ q ∈ N ∩ C.1, p ≠ q)
    (hl : ∀ s₁ ∈ arcComponentsIn (bd X \ N), ∀ s₂ ∈ arcComponentsIn (bd X \ N), s₁ ≠ s₂
      → Disjoint s₁ Z → Disjoint s₂ Z → Disjoint (tilde s₁) (tilde s₂)) : Frame X where
  V := N
  γ s := arcMarch hX (flipOf ε s) s
  isLong s := Disjoint s Z
  V_subset := hsub
  finite_V := hf
  finite_sides := finite_arcComponentsIn_bd hX hf h2
  side_shape _ hs := arc_shape hX hf h2 hs
  γ_nodup s hs := by
    obtain ⟨C, a, b, hab, hub, he, -, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) hf h2 hs
    exact (arcMarch_spec hX _ hab hub he).nodup
  γ_set s hs := by
    obtain ⟨C, a, b, hab, hub, he, -, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) hf h2 hs
    exact (arcMarch_spec hX _ hab hub he).set_eq
  long_disjoint := hl

end GraphMinor.GM19

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14ae

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Graph Minors XIX, Section 14: thinning the sequence

The paper passes to a subsequence in which the frames and the short sides agree. We do this here.
There are only finitely many possible values, so an infinite
subsequence takes one value. Then the sectors at the singular places lie in a well-quasi-order, and
a further subsequence makes them increase.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A sequence with values in a finite set is constant on a subsequence. -/
theorem exists_subseq_const {τ : Type*} {F : Set τ} (hF : F.Finite) (h : ℕ → τ)
  (hm : ∀ i, h i ∈ F) : ∃ (g : ℕ → ℕ) (t : τ), StrictMono g ∧ ∀ i, h (g i) = t := by
  have := hF.to_subtype
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber (fun i ↦ (⟨h i, hm i⟩ : ↥F))
  have hI : ({i | (⟨h i, hm i⟩ : ↥F) = c} : Set ℕ).Infinite := Set.infinite_coe_iff.mp hc
  refine ⟨Nat.nth (· ∈ {i | (⟨h i, hm i⟩ : ↥F) = c}), c.1, Nat.nth_strictMono hI, fun i ↦ ?_⟩
  exact congrArg Subtype.val (Nat.nth_mem_of_infinite hI i)

/-- Finitely many sequences in a well-quasi-order increase together on a subsequence. -/
theorem exists_subseq_mono {ι β : Type*} [Finite ι] {Ω : QuasiOrder β} (hΩ : Ω.IsWQO) (y : ℕ → ι
  → β) (hy : ∀ i a, y i a ∈ Ω.E) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ m n, m ≤ n → ∀ a, Ω.le (y (g m) a) (y (g n) a) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ A : Finset ι, ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ m n, m ≤ n → ∀ a ∈ A, Ω.le (y (g m) a)
    (y (g n) a) := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, fun _ _ _ _ ha ↦ absurd ha (Finset.notMem_empty _)⟩
    | insert a A _ ih =>
      obtain ⟨g, hg, hle⟩ := ih
      obtain ⟨g', hg', hle'⟩ := hΩ.exists_mono_subseq (fun n ↦ y (g n) a) fun i ↦ hy _ a
      refine ⟨g ∘ g', hg.comp hg', fun m n hmn b hb ↦ ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hle' m n hmn
      · exact hle _ _ (hg'.monotone hmn) b hb
  obtain ⟨g, hg, hle⟩ := key Finset.univ
  exact ⟨g, hg, fun m n hmn a ↦ hle m n hmn a (Finset.mem_univ a)⟩

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)

/-- The sector at a singular vertex of `R*`. -/
noncomputable def zsec {β : Type*} (ξ : Arm D.P.Γ → β) (x : ↥s.𝒲 × ℕ) : β := ξ
  ((s.fr x.1).secArm x.2)

open Classical in
/-- The hub at a singular vertex of `R*`. If the hub is a vertex then there is no arm, and we take
the sector again. -/
noncomputable def zhub {β : Type*} (ξ : Arm D.P.Γ → β) (x : ↥s.𝒲 × ℕ) : β := if hc :
  (s.fr x.1).H.V.ncard ≠ 1 then ξ ((s.fr x.1).hubArm hc) else ξ ((s.fr x.1).secArm x.2)

theorem zsec_mem {β : Type*} {E : Set β} {ξ : Arm D.P.Γ → β} (hξ : ∀ A ∈
  (coverLoc s.𝒲 s.cut.finite s.cut.disj s.fr).arms, ξ A ∈ E) {x : ↥s.𝒲 × ℕ}
    (hx : x.2 ∈ s.sing x.1) : s.zsec ξ x ∈ E :=
  hξ _ (mem_iUnion.mpr ⟨x.1, .inl ⟨_, hx.1, rfl⟩⟩)

theorem zhub_mem {β : Type*} {E : Set β} {ξ : Arm D.P.Γ → β} (hξ : ∀ A ∈
  (coverLoc s.𝒲 s.cut.finite s.cut.disj s.fr).arms, ξ A ∈ E) {x : ↥s.𝒲 × ℕ}
    (hx : x.2 ∈ s.sing x.1) : s.zhub ξ x ∈ E := by
  classical
  by_cases hc : (s.fr x.1).H.V.ncard ≠ 1
  · rw [zhub, dite_eq_left hc]
    exact hξ _ (mem_iUnion.mpr ⟨x.1, .inr ⟨hc, rfl⟩⟩)
  · rw [zhub, dite_eq_right hc]
    exact hξ _ (mem_iUnion.mpr ⟨x.1, .inl ⟨_, hx.1, rfl⟩⟩)

end Slice

/-- **The sequence with the wheels in one place.** -/
theorem exists_pair_slices [Infinite α] {T : Set S} {D : ℕ → TangleDatum cap χ} (s : ∀ i, Slice T
  (D i)) {V : Set ↥Tᶜ} (hV : V.Finite) (hVm : ∀ i, (s i).markN ⊆ V ∧ (s i).markZ ⊆ V) {b : ℕ}
    (hb : ∀ i W, ((s i).fr W).ρ ≤ b)
    {ω₀ : α} (hcov : ∀ i, ∀ e ∈ (D i).Γ.E, χ.unionLE ω₀ ((D i).P.φ e) → ∃ W ∈
      (s i).𝒲, cap.emb '' e ⊆ W) {𝒮 : Set (ColouredPainting χ)} (hm : ∀ i, (D i).P ∈ 𝒮)
        (hd : χ.IsDisjoint)
     (hcl : IsPaintingClass χ 𝒮) (hS2 : ConditionS2 χ cap) {k : ℕ} (hk : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k
       = 3 ∧ ω₀ ∈ χ.Ω3.E)) {β : Type*} {Ω : QuasiOrder β} (hΩ : Ω.IsWQO)
    (ξ : ∀ i, Arm (D i).P.Γ → β) (hξ : ∀ i, ∀ A ∈ (coverLoc (s i).𝒲 (s i).cut.finite (s i).cut.disj
      (s i).fr).arms, ξ i A ∈ Ω.E) :
    ∃ i j, i < j ∧ ∃ τ : Arm (D i).P.Γ → Arm (D j).P.Γ,
      IsOutline (⟨hd, (D i).P, coverLoc (s i).𝒲 (s i).cut.finite (s i).cut.disj
        (s i).fr⟩ : Place χ) ⟨hd, (D j).P, coverLoc (s j).𝒲 (s j).cut.finite (s j).cut.disj
          (s j).fr⟩ τ ∧
        ∀ A ∈ (coverLoc (s i).𝒲 (s i).cut.finite (s i).cut.disj (s i).fr).arms, Ω.le (ξ i A) (ξ j
          (τ A)) := by
  classical
  have : Nonempty ↥Tᶜ := (s 0).connected.toNonempty
  have hX := (s 0).isSurface
  have hcf : (cuffs ↥Tᶜ).Finite := (cuff_statement _ hX).2.1
  have : Finite ↥(cuffs ↥Tᶜ) := hcf.to_subtype
  have : Finite ↥V := hV.to_subtype
  let tag : ℕ → Set ↥Tᶜ × Set ↥Tᶜ × (↥(cuffs ↥Tᶜ) → Bool) × (↥V → Option ZData) := fun i ↦
    ((s i).markN, (s i).markZ, fun C ↦ (s i).cuffDir C.1, fun z ↦ (s i).ztag z.1)
  have hfB := ((finite_zdataSet b).image (some : ZData → Option ZData)).insert none
  have hF := (hV.finite_subsets).prod ((hV.finite_subsets).prod ((finite_univ (α := ↥(cuffs ↥Tᶜ)
    → Bool)).prod (Set.Finite.pi' (ι := ↥V) (t := fun _ ↦ insert none
      (some '' zdataSet b)) fun _ ↦ hfB)))
  obtain ⟨g₂, ⟨N, Z, εf, tf⟩, hg₂, htag⟩ := exists_subseq_const hF tag fun i ↦ ⟨(hVm i).1,
    (hVm i).2, mem_univ _, fun z ↦ (s i).ztag_mem (hb i) z.1⟩
  have hN : ∀ i, (s (g₂ i)).markN = N := fun i ↦ congrArg Prod.fst (htag i)
  have hZ : ∀ i, (s (g₂ i)).markZ = Z := fun i ↦ congrArg (fun x ↦ x.2.1) (htag i)
  have hε₀ : ∀ i (C : ↥(cuffs ↥Tᶜ)), (s (g₂ i)).cuffDir C.1 = εf C := fun i C ↦ congrFun (congrArg
    (fun x ↦ x.2.2.1) (htag i)) C
  have ht₀ : ∀ i (z : ↥V), (s (g₂ i)).ztag z.1 = tf z := fun i z ↦ congrFun (congrArg
    (fun x ↦ x.2.2.2) (htag i)) z
  have hZV : Z ⊆ V := hZ 0 ▸ (hVm _).2
  let ε : Set ↥Tᶜ → Bool := fun C ↦ if h : C ∈ cuffs ↥Tᶜ then εf ⟨C, h⟩ else false
  let t : ↥Tᶜ → Option ZData := fun z ↦ if h : z ∈ V then tf ⟨z, h⟩ else none
  have hzp : ∀ i (z : ↥Z), z.1 ∈ (s (g₂ i)).markZ := fun i z ↦ (hZ i).symm ▸ z.2
  let y : ℕ → ↥Z ⊕ ↥Z → β := fun i a ↦ Sum.elim (fun z ↦ (s (g₂ i)).zsec (ξ (g₂ i)) ((s
    (g₂ i)).pick (hzp i z))) (fun z ↦ (s (g₂ i)).zhub (ξ (g₂ i)) ((s (g₂ i)).pick (hzp i z))) a
  have : Finite ↥Z := (hV.subset hZV).to_subtype
  obtain ⟨g₃, hg₃, hle⟩ := exists_subseq_mono hΩ y (by
    rintro i (z | z)
    · exact (s (g₂ i)).zsec_mem (hξ _) ((s (g₂ i)).pick_spec (hzp i z)).1
    · exact (s (g₂ i)).zhub_mem (hξ _) ((s (g₂ i)).pick_spec (hzp i z)).1)
  let g : ℕ → ℕ := fun i ↦ g₂ (g₃ i)
  have hg : StrictMono g := hg₂.comp hg₃
  have hfam : Family (fun i ↦ D (g i)) (fun i ↦ s (g i)) N Z ε t Ω (fun i ↦ ξ (g i)) ω₀ b 𝒮 := by
    refine ⟨fun i ↦ hN _, fun i ↦ hZ _, fun i C hC ↦ ?_, fun i z hz ↦ ?_, fun i ↦ hb _,
      fun i ↦ hcov _, fun i ↦ hξ _, ?_, fun i ↦ hm _⟩
    · simp only [ε, dite_eq_left hC]
      exact (hε₀ _ ⟨C, hC⟩).symm
    · simp only [t, dite_eq_left (hZV hz)]
      exact ht₀ _ ⟨z, hZV hz⟩
    · intro i j hij W p hp W' q hq hzz
      have hzZ : (s (g i)).zx W p ∈ Z := hZ (g₃ i) ▸ mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hp,
        rfl⟩⟩
      let z : ↥Z := ⟨_, hzZ⟩
      have hp₁ : (s (g i)).pick (hzp (g₃ i) z) = (W, p) := (s (g i)).pick_eq _ hp rfl
      have hp₂ : (s (g j)).pick (hzp (g₃ j) z) = (W', q) := (s (g j)).pick_eq _ hq hzz
      have h₁ := hle i j hij.le (.inl z)
      have h₂ := hle i j hij.le (.inr z)
      simp only [y, Sum.elim_inl, Sum.elim_inr] at h₁ h₂
      change Ω.le ((s (g i)).zsec (ξ (g i)) ((s (g i)).pick (hzp (g₃ i) z))) ((s (g j)).zsec (ξ
        (g j)) ((s (g j)).pick (hzp (g₃ j) z))) at h₁
      change Ω.le ((s (g i)).zhub (ξ (g i)) ((s (g i)).pick (hzp (g₃ i) z))) ((s (g j)).zhub (ξ
        (g j)) ((s (g j)).pick (hzp (g₃ j) z))) at h₂
      rw [hp₁, hp₂] at h₁ h₂
      refine ⟨h₁, fun hc hc' ↦ ?_⟩
      simp only [Slice.zhub, dite_eq_left hc, dite_eq_left hc'] at h₂
      exact h₂
  obtain ⟨i, j, hij, τ, h₁, h₂⟩ := hfam.exists_pair hd hcl hS2 hΩ hk
  exact ⟨g i, g j, hg hij, τ, h₁, h₂⟩

end GraphMinor.GM19

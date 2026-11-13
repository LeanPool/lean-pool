/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- [TABLET NODE: P3821T1ControlledNeighborhood]

/-!
# P3821T1ControlledNeighborhood

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ControlledNeighborhoodConstruction

private noncomputable abbrev f (e : C(Circle, ℂ)) (he : Function.Injective e) : Circle ≃
    Set.range e := by
  classical
  exact Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)

private theorem hf (e : C(Circle, ℂ)) (he : Function.Injective e) : Continuous (f e he) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  change (Continuous f)
  change Continuous (fun x : Circle => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e))
  exact Continuous.subtype_mk e.continuous (fun x => ⟨x, rfl⟩)

private noncomputable abbrev ψ (e : C(Circle, ℂ)) (he : Function.Injective e) : Set.range e →
    Circle := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  exact fun x => f.symm x

private theorem hψc (e : C(Circle, ℂ)) (he : Function.Injective e) : Continuous (ψ e he) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  have hf : Continuous f := hf e he
  let ψ : Set.range e → Circle := f.symm
  change (Continuous ψ)
  exact hf.continuous_symm_of_equiv_compact_to_t2

private theorem hψleft (e : C(Circle, ℂ)) (he : Function.Injective e) : Function.LeftInverse (ψ e
    he) (fun x : Circle => ⟨e x, ⟨x, rfl⟩⟩) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  change (Function.LeftInverse ψ (fun x : Circle => ⟨e x, ⟨x, rfl⟩⟩))
  intro x
  exact f.symm_apply_apply x

private noncomputable abbrev u (e : C(Circle, ℂ)) (he : Function.Injective e) : Set.range e → ℂ
    := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  exact fun k => (ψ k : ℂ)

private theorem hu (e : C(Circle, ℂ)) (he : Function.Injective e) : Continuous (u e he) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  have hψc : Continuous ψ := hψc e he
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  change (Continuous u)
  exact continuous_subtype_val.comp hψc

private theorem heUC (e : C(Circle, ℂ)) : UniformContinuous e := by
  classical
  exact CompactSpace.uniformContinuous_of_continuous e.continuous

private noncomputable abbrev δ (δ₀ : ℝ) := by
  classical
  exact min (δ₀ / 4) (1 / 8)

private theorem hδpos (δ₀ : ℝ) (hδ₀ : δ₀ > 0) : 0 < (δ δ₀) := by
  classical
  let δ := min (δ₀ / 4) (1 / 8)
  change (0 < δ)
  dsimp [δ]; positivity

private theorem hδlt (δ₀ : ℝ) (hδ₀ : δ₀ > 0) : (δ δ₀) < 1 / 4 := by
  classical
  let δ := min (δ₀ / 4) (1 / 8)
  have hδpos : 0 < δ := hδpos δ₀ hδ₀
  change (δ < 1 / 4)
  dsimp [δ]
  have : min (δ₀ / 4) (1 / 8) ≤ 1 / 8 := min_le_right _ _
  linarith

private theorem hKcompact (e : C(Circle, ℂ)) : IsCompact (Set.range e) := by
  classical
  exact isCompact_range e.continuous

private theorem hψUC (e : C(Circle, ℂ)) (he : Function.Injective e) : UniformContinuous (u e he)
    := by
  classical
  let : CompactSpace (Set.range e) :=
    isCompact_iff_compactSpace.mp (isCompact_range e.continuous)
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  have hu : Continuous u := hu e he
  change (UniformContinuous u)
  exact CompactSpace.uniformContinuous_of_continuous hu

private noncomputable abbrev r (eps : ℝ) (η : ℝ) := by
  classical
  exact min (η / 8) (eps / 8)

private theorem hrpos (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : η > 0) : 0 < (r eps η) := by
  classical
  let r := min (η / 8) (eps / 8)
  change (0 < r)
  dsimp [r]; positivity

private theorem hrerr (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : η > 0) : 2 * (r eps η) < eps / 2
    := by
  classical
  let r := min (η / 8) (eps / 8)
  have hrpos : 0 < r := hrpos eps heps η hη
  change (2 * r < eps / 2)
  dsimp [r]
  have hle : min (η / 8) (eps / 8) ≤ eps / 8 := min_le_right _ _
  linarith

private theorem heclose (e : C(Circle, ℂ)) (eps : ℝ) (δ₀ : ℝ) (hδ : ∀ ⦃a b : Circle⦄, dist a b <
    δ₀ → dist (e a) (e b) < eps / 2) (hδ₀ : δ₀ > 0) : ∀ u v : Circle, dist u v < 2 * (δ δ₀) →
    dist (e u) (e v) < eps / 2 := by
  classical
  let δ := min (δ₀ / 4) (1 / 8)
  have hδpos : 0 < δ := hδpos δ₀ hδ₀
  change (∀ u v : Circle, dist u v < 2 * δ → dist (e u) (e v) < eps / 2)
  intro u v huv
  apply hδ
  have hle : δ ≤ δ₀ / 4 := by dsimp [δ]; exact min_le_left _ _
  linarith

private theorem hψclose (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 < eps)
    (δ₀ : ℝ) (η : ℝ) (hη : η > 0) (hηψ : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he)
    a) ((u e he) b) < (δ δ₀)) : ∀ k l : Set.range e, dist k l < 4 * (r eps η) →
      dist (((ψ e he) k : Circle) : ℂ) (((ψ e he) l : Circle) : ℂ) < (δ δ₀) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let δ := min (δ₀ / 4) (1 / 8)
  let r := min (η / 8) (eps / 8)
  have hrpos : 0 < r := hrpos eps heps η hη
  change (∀ k l : Set.range e, dist k l < 4 * r →
      dist ((ψ k : Circle) : ℂ) ((ψ l : Circle) : ℂ) < δ)
  intro k l hkl
  apply hηψ
  have hle : r ≤ η / 8 := by dsimp [r]; exact min_le_left _ _
  linarith

private noncomputable abbrev F (e : C(Circle, ℂ)) (S : Set ↑(Set.range ⇑e)) (hSf : S.Finite) :
    Finset (Set.range e) := by
  classical
  exact hSf.toFinset

private theorem hFS (e : C(Circle, ℂ)) (S : Set ↑(Set.range ⇑e)) (hSf : S.Finite) : ((F e S hSf)
    : Set (Set.range e)) = S := by
  classical
  let F : Finset (Set.range e) := hSf.toFinset
  change ((F : Set (Set.range e)) = S)
  ext c; simp [F]

private theorem hFsub (e : C(Circle, ℂ)) (S : Set ↑(Set.range ⇑e)) (hSf : S.Finite) : ((F e S
    hSf) : Set (Set.range e)) ⊆ Set.univ := by
  classical
  let F : Finset (Set.range e) := hSf.toFinset
  change ((F : Set (Set.range e)) ⊆ Set.univ)
  simp

private theorem hcover' (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) (hcover : Set.univ ⊆ ⋃ x ∈ S, Metric.ball x (r eps η)) : (Set.univ : Set (Set.range
    e)) ⊆
      ⋃ c ∈ ((F e S hSf) : Set (Set.range e)), Metric.ball c (r eps η) := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  have hFS : (F : Set (Set.range e)) = S := hFS e S hSf
  change ((Set.univ : Set (Set.range e)) ⊆
      ⋃ c ∈ (F : Set (Set.range e)), Metric.ball c r)
  simpa [hFS] using hcover

private noncomputable abbrev w (e : C(Circle, ℂ)) (eps : ℝ) (η : ℝ) : Set.range e → ℂ → ℝ := by
  classical
  let r := min (η / 8) (eps / 8)
  exact fun c z => max 0 (2 * r - dist z (c : ℂ))

private noncomputable abbrev W (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ)
    (hSf : S.Finite) : ℂ → ℝ := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  exact fun z => ∑ c ∈ F, w c z

private theorem hw_cont (e : C(Circle, ℂ)) (eps : ℝ) (η : ℝ) (c : Set.range e) : Continuous ((w e
    eps η) c) := by
  classical
  let r := min (η / 8) (eps / 8)
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  change (Continuous (w c))
  dsimp [w]
  fun_prop

private theorem hW_cont (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) : Continuous (W e eps S η hSf) := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  have hw_cont (c : Set.range e) : Continuous (w c) := hw_cont e eps η c
  change (Continuous W)
  dsimp [W]
  exact continuous_finsetSum F (fun c hc => hw_cont c)

private noncomputable abbrev N (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ)
    (hSf : S.Finite) : Set ℂ := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  exact {z | 0 < W z}

private theorem hNopen (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) : IsOpen (N e eps S η hSf) := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  have hW_cont : Continuous W := hW_cont e eps S η hSf
  let N : Set ℂ := {z | 0 < W z}
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (IsOpen N)
  exact isOpen_lt continuous_const hW_cont

private theorem hKN (e : C(Circle, ℂ)) (eps : ℝ) (heps : 0 < eps) (S : Set ↑(Set.range ⇑e)) (η :
    ℝ) (hSf : S.Finite) (hcover : Set.univ ⊆ ⋃ x ∈ S, Metric.ball x (r eps η)) (hη : η > 0) :
    Set.range e ⊆ (N e eps S η hSf) := by
  classical
  let r := min (η / 8) (eps / 8)
  have hrpos : 0 < r := hrpos eps heps η hη
  let F : Finset (Set.range e) := hSf.toFinset
  have hcover' : (Set.univ : Set (Set.range e)) ⊆
      ⋃ c ∈ (F : Set (Set.range e)), Metric.ball c r := hcover' e eps S η hSf hcover
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (Set.range e ⊆ N)
  intro z hz
  obtain ⟨c, hcF, hzc⟩ :=
    Set.mem_iUnion₂.mp (hcover' (Set.mem_univ (⟨z, hz⟩ : Set.range e)))
  have hpositive : 0 < w c z := by
    dsimp [w]
    change dist (⟨z, hz⟩ : Set.range e) c < r at hzc
    have hzc' : dist z (c : ℂ) < r := hzc
    have : 0 < 2 * r - dist z (c : ℂ) := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)
  have hsum : w c z ≤ W z := by
    dsimp [W]
    have hcF' : c ∈ F := by simpa using hcF
    simpa [w] using (Finset.single_le_sum (s := F)
      (fun j hj => le_max_left 0 (2 * r - dist z (j : ℂ))) (a := c) hcF')
  change 0 < W z
  linarith

private theorem hW_N (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) : Continuous (fun z : (N e eps S η hSf) => (W e eps S η hSf) (z : ℂ)) := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  have hW_cont : Continuous W := hW_cont e eps S η hSf
  let N : Set ℂ := {z | 0 < W z}
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (Continuous (fun z : N => W (z : ℂ)))
  exact hW_cont.comp continuous_subtype_val

private noncomputable abbrev a (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ)
    (hSf : S.Finite) : (N e eps S η hSf) → Set.range e → ℝ := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (N → Set.range e → ℝ)
  exact fun z c => w c (z : ℂ) / W (z : ℂ)

private theorem ha_cont (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) (c : Set.range e) : Continuous (fun z : (N e eps S η hSf) => (a e eps S η hSf) z c)
    := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  have hw_cont (c : Set.range e) : Continuous (w c) := hw_cont e eps η c
  let N : Set ℂ := {z | 0 < W z}
  have hW_N : Continuous (fun z : N => W (z : ℂ)) := hW_N e eps S η hSf
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (Continuous (fun z : N => a z c))
  dsimp [a]
  exact (hw_cont c).comp continuous_subtype_val |>.div hW_N (fun z => ne_of_gt z.property)

private noncomputable abbrev v (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (S : Set
    ↑(Set.range ⇑e)) (η : ℝ) (hSf : S.Finite) : (N e eps S η hSf) → ℂ := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (N → ℂ)
  exact fun z => ∑ c ∈ F, (a z c : ℂ) * u c

private theorem hv_cont (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (S : Set
    ↑(Set.range ⇑e)) (η : ℝ) (hSf : S.Finite) : Continuous (v e he eps S η hSf) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  have ha_cont (c : Set.range e) : Continuous (fun z : N => a z c) := ha_cont e eps S η hSf c
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  change (Continuous v)
  dsimp [v]
  apply continuous_finsetSum
  intro c hc
  have hac := ha_cont c
  fun_prop

private theorem hactive (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) (z : (N e eps S η hSf)) : ∃ i ∈ (F e S hSf), 0 < (w e eps η) i (z : ℂ) := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (∃ i ∈ F, 0 < w i (z : ℂ))
  by_contra h
  push Not at h
  have hsum : (∑ c ∈ F, w c (z : ℂ)) ≤ 0 :=
    Finset.sum_nonpos (fun c hc => h c hc)
  have hz : 0 < W (z : ℂ) := z.property
  linarith

private theorem hw_active_dist (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ)
    (hSf : S.Finite) (z : (N e eps S η hSf)) (c : Set.range e) (hc : 0 < (w e eps η) c (z : ℂ)) :
      dist (z : ℂ) (c : ℂ) < 2 * (r eps η) := by
  classical
  let r := min (η / 8) (eps / 8)
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (dist (z : ℂ) (c : ℂ) < 2 * r)
  change 0 < max 0 (2 * r - dist (z : ℂ) (c : ℂ)) at hc
  exact sub_pos.mp ((lt_max_iff.mp hc).resolve_left (lt_irrefl 0))

private theorem hψmap (e : C(Circle, ℂ)) (he : Function.Injective e) (c : Set.range e) : e ((ψ e
    he) c) = c := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  have hψleft : Function.LeftInverse ψ (fun x : Circle => ⟨e x, ⟨x, rfl⟩⟩) := hψleft e he
  change (e (ψ c) = c)
  rcases c with ⟨k, ⟨x, hx⟩⟩
  subst k
  have hh := hψleft x
  change ψ ⟨e x, ⟨x, rfl⟩⟩ = x at hh
  rw [hh]

private theorem ha_nonneg (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) (z : (N e eps S η hSf)) (c : Set.range e) : 0 ≤ (a e eps S η hSf) z c := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  change (0 ≤ a z c)
  apply div_nonneg
  · exact le_max_left 0 _
  · exact le_of_lt z.property

private theorem hsum_a (e : C(Circle, ℂ)) (eps : ℝ) (S : Set ↑(Set.range ⇑e)) (η : ℝ) (hSf :
    S.Finite) (z : (N e eps S η hSf)) : (∑ c ∈ (F e S hSf), (a e eps S η hSf) z c) = 1 := by
  classical
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  change ((∑ c ∈ F, a z c) = 1)
  rw [← Finset.sum_div]
  rw [show (∑ c ∈ F, w c (z : ℂ)) = W (z : ℂ) by rfl]
  exact div_self z.property.ne'

private theorem hv_close (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 <
    eps) (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀ > 0)
    (hηψ : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ δ₀)) (z
    : (N e eps S η hSf)) (i : Set.range e) (hi : i ∈ (F e S hSf))
      (hwi : 0 < (w e eps η) i (z : ℂ)) : ‖(v e he eps S η hSf) z - (u e he) i‖ < (δ δ₀) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let δ := min (δ₀ / 4) (1 / 8)
  have hδpos : 0 < δ := hδpos δ₀ hδ₀
  let r := min (η / 8) (eps / 8)
  have hψclose : ∀ k l : Set.range e, dist k l < 4 * r →
      dist ((ψ k : Circle) : ℂ) ((ψ l : Circle) : ℂ) < δ := hψclose e he eps heps δ₀ η hη hηψ
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  have hw_active_dist (z : N) (c : Set.range e) (hc : 0 < w c (z : ℂ)) :
      dist (z : ℂ) (c : ℂ) < 2 * r := hw_active_dist e eps S η hSf z c hc
  have ha_nonneg (z : N) (c : Set.range e) : 0 ≤ a z c := ha_nonneg e eps S η hSf z c
  have hsum_a (z : N) : (∑ c ∈ F, a z c) = 1 := hsum_a e eps S η hSf z
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (‖v z - u i‖ < δ)
  have hsumC : (∑ c ∈ F, (a z c : ℂ)) = 1 := by
    exact_mod_cast hsum_a z
  have hsumConst : (∑ c ∈ F, (a z c : ℂ) * u i) = u i := by
    calc
      (∑ c ∈ F, (a z c : ℂ) * u i) =
          (∑ c ∈ F, (a z c : ℂ)) * u i := by rw [Finset.sum_mul]
      _ = u i := by rw [hsumC]; simp [u]
  have hdiff : v z - u i = ∑ c ∈ F, (a z c : ℂ) * (u c - u i) := by
    change (∑ c ∈ F, (a z c : ℂ) * u c) - u i = _
    calc
      (∑ c ∈ F, (a z c : ℂ) * u c) - u i =
          (∑ c ∈ F, (a z c : ℂ) * u c) -
            (∑ c ∈ F, (a z c : ℂ) * u i) := by rw [hsumConst]
      _ = ∑ c ∈ F,
            ((a z c : ℂ) * u c - (a z c : ℂ) * u i) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ c ∈ F, (a z c : ℂ) * (u c - u i) := by
        apply Finset.sum_congr rfl
        intro c hc
        ring
  have hterm_le (c : Set.range e) (hc : c ∈ F) :
      ‖(a z c : ℂ) * (u c - u i)‖ ≤ a z c * δ := by
    by_cases hactivec : 0 < w c (z : ℂ)
    · have hci_ambient : dist (c : ℂ) (i : ℂ) < 4 * r := by
        have hcz := hw_active_dist z c hactivec
        have hiz := hw_active_dist z i hwi
        calc
          dist (c : ℂ) (i : ℂ) ≤ dist (c : ℂ) (z : ℂ) + dist (z : ℂ) (i : ℂ) :=
            dist_triangle _ _ _
          _ = dist (z : ℂ) (c : ℂ) + dist (z : ℂ) (i : ℂ) := by
            rw [dist_comm (c : ℂ) z]
          _ < 4 * r := by linarith
      have hci : dist c i < 4 * r := by
        simpa [Subtype.dist_eq] using hci_ambient
      have hpsi : dist ((ψ c : Circle) : ℂ) ((ψ i : Circle) : ℂ) < δ :=
        hψclose c i hci
      have hnorm : ‖u c - u i‖ < δ := by simpa [dist_eq_norm, u] using hpsi
      have hnorma : ‖(a z c : ℂ)‖ = a z c := by
        calc
          ‖(a z c : ℂ)‖ = |a z c| := RCLike.norm_ofReal _
          _ = a z c := abs_of_nonneg (ha_nonneg z c)
      rw [norm_mul, hnorma]
      exact mul_le_mul_of_nonneg_left hnorm.le (ha_nonneg z c)
    · have hzero : w c (z : ℂ) = 0 := by
        apply le_antisymm
        · exact le_of_not_gt hactivec
        · dsimp [w]
          exact le_max_left 0 _
      have hazero : a z c = 0 := by simp [a, hzero]
      simp [hazero]
  have hterm_strict :
      ‖(a z i : ℂ) * (u i - u i)‖ < a z i * δ := by
    have hai : 0 < a z i := div_pos hwi z.property
    simp [hδpos, hai]
  have hsum_strict :
      (∑ c ∈ F, ‖(a z c : ℂ) * (u c - u i)‖) <
        ∑ c ∈ F, a z c * δ :=
    Finset.sum_lt_sum hterm_le ⟨i, hi, hterm_strict⟩
  calc
    ‖v z - u i‖ ≤
        ∑ c ∈ F, ‖(a z c : ℂ) * (u c - u i)‖ := by
      rw [hdiff]
      exact norm_sum_le _ _
    _ < ∑ c ∈ F, a z c * δ := hsum_strict
    _ = δ := by rw [← Finset.sum_mul, hsum_a z]; ring

private theorem hunit (e : C(Circle, ℂ)) (he : Function.Injective e) (c : Set.range e) : ‖(u e
    he) c‖ = 1 := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  change (‖u c‖ = 1)
  dsimp [u]
  exact Circle.norm_coe (ψ c)

private theorem hv_lower (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 <
    eps) (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀ > 0)
    (hηψ : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ δ₀)) (z
    : (N e eps S η hSf)) : 1 - (δ δ₀) < ‖(v e he eps S η hSf) z‖ := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let δ := min (δ₀ / 4) (1 / 8)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  have hactive (z : N) : ∃ i ∈ F, 0 < w i (z : ℂ) := hactive e eps S η hSf z
  have hv_close (z : N) (i : Set.range e) (hi : i ∈ F)
      (hwi : 0 < w i (z : ℂ)) : ‖v z - u i‖ < δ := hv_close e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
          i hi hwi
  have hunit (c : Set.range e) : ‖u c‖ = 1 := hunit e he c
  change (1 - δ < ‖v z‖)
  obtain ⟨i, hi, hwi⟩ := hactive z
  have hnear := hv_close z i hi hwi
  have hrev : ‖u i - v z‖ = ‖v z - u i‖ := by
    rw [show u i - v z = -(v z - u i) by ring, norm_neg]
  have htri : 1 ≤ ‖v z - u i‖ + ‖v z‖ := by
    calc
      1 = ‖u i‖ := (hunit i).symm
      _ = ‖(u i - v z) + v z‖ := by congr 1; abel
      _ ≤ ‖u i - v z‖ + ‖v z‖ := norm_add_le _ _
      _ = ‖v z - u i‖ + ‖v z‖ := by rw [hrev]
  linarith

private theorem hv_pos (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 < eps)
    (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀ > 0) (hηψ
    : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ δ₀)) (z : (N
    e eps S η hSf)) : 0 < ‖(v e he eps S η hSf) z‖ := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let δ := min (δ₀ / 4) (1 / 8)
  have hδpos : 0 < δ := hδpos δ₀ hδ₀
  have hδlt : δ < 1 / 4 := hδlt δ₀ hδ₀
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  have hv_lower (z : N) : 1 - δ < ‖v z‖ := hv_lower e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
  change (0 < ‖v z‖)
  linarith [hv_lower z]

private noncomputable abbrev p (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (S : Set
    ↑(Set.range ⇑e)) (η : ℝ) (hSf : S.Finite) : (N e eps S η hSf) → ℂ := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (N → ℂ)
  exact fun z => v z / (‖v z‖ : ℂ)

private theorem hp_norm (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 < eps)
    (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀ > 0) (hηψ
    : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ δ₀)) (z : (N
    e eps S η hSf)) : ‖(p e he eps S η hSf) z‖ = 1 := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  have hv_pos (z : N) : 0 < ‖v z‖ := hv_pos e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
  let p : N → ℂ := fun z => v z / (‖v z‖ : ℂ)
  change (‖p z‖ = 1)
  dsimp [p]
  have hden : ‖(‖v z‖ : ℂ)‖ = ‖v z‖ := by
    calc
      ‖(‖v z‖ : ℂ)‖ = |‖v z‖| := RCLike.norm_ofReal _
      _ = ‖v z‖ := abs_of_nonneg (norm_nonneg _)
  rw [norm_div, hden]
  exact div_self (ne_of_gt (hv_pos z))

private noncomputable abbrev phiVal (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ)
    (heps : 0 < eps) (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0)
    (hδ₀ : δ₀ > 0) (hηψ : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he)
    b) < (δ δ₀)) : (N e eps S η hSf) → Circle := by
  exact fun z =>
    ⟨p e he eps S η hSf z,
      (mem_sphere_zero_iff_norm).2 (hp_norm e he eps heps S δ₀ η hSf hη hδ₀ hηψ z)⟩


private theorem hp_cont (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 < eps)
    (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀ > 0) (hηψ
    : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ δ₀)) :
    Continuous (p e he eps S η hSf) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  have hv_cont : Continuous v := hv_cont e he eps S η hSf
  have hv_pos (z : N) : 0 < ‖v z‖ := hv_pos e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
  let p : N → ℂ := fun z => v z / (‖v z‖ : ℂ)
  change (Continuous p)
  dsimp [p]
  have hden : Continuous (fun z : N => (‖v z‖ : ℂ)) := by fun_prop
  apply hv_cont.div hden
  intro z
  exact_mod_cast (ne_of_gt (hv_pos z))

private theorem hphiVal_cont (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 <
    eps) (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀ > 0)
    (hηψ : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ δ₀)) :
    Continuous (phiVal e he eps heps S δ₀ η hSf hη hδ₀ hηψ) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  let p : N → ℂ := fun z => v z / (‖v z‖ : ℂ)
  have hp_norm (z : N) : ‖p z‖ = 1 := hp_norm e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
  let phiVal : N → Circle := fun z => ⟨p z, (mem_sphere_zero_iff_norm).2 (hp_norm z)⟩
  have hp_cont : Continuous p := hp_cont e he eps heps S δ₀ η hSf hη hδ₀ hηψ
  change (Continuous phiVal)
  dsimp [phiVal]
  exact Continuous.subtype_mk hp_cont (fun z => (mem_sphere_zero_iff_norm).2 (hp_norm z))

private theorem norm_normalize (x : ℂ) (hx : 0 < ‖x‖) :
      ‖x / (‖x‖ : ℂ) - x‖ = |1 - ‖x‖| := by
  classical
  have hcast : (1 / (‖x‖ : ℂ) - 1) = ((1 / ‖x‖ - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have hnormcast : ‖((1 / ‖x‖ - 1 : ℝ) : ℂ)‖ = |1 / ‖x‖ - 1| :=
    RCLike.norm_ofReal _
  calc
    ‖x / (‖x‖ : ℂ) - x‖ = ‖x * (1 / (‖x‖ : ℂ) - 1)‖ := by
      congr 1
      field_simp
    _ = ‖x‖ * |1 / ‖x‖ - 1| := by
      rw [norm_mul, hcast, hnormcast]
    _ = |1 - ‖x‖| := by
      rw [show 1 / ‖x‖ - 1 = (1 - ‖x‖) / ‖x‖ by field_simp]
      rw [abs_div, abs_of_pos hx]
      field_simp

private theorem hphi_near (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps : 0 <
    eps) (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀ > 0)
    (hηψ : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ δ₀)) (z
    : (N e eps S η hSf)) : ∀ i ∈ (F e S hSf), 0 < (w e eps η) i (z : ℂ) →
      ‖(p e he eps S η hSf) z - (u e he) i‖ < 2 * (δ δ₀) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let δ := min (δ₀ / 4) (1 / 8)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  have hv_close (z : N) (i : Set.range e) (hi : i ∈ F)
      (hwi : 0 < w i (z : ℂ)) : ‖v z - u i‖ < δ := hv_close e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
          i hi hwi
  have hunit (c : Set.range e) : ‖u c‖ = 1 := hunit e he c
  have hv_pos (z : N) : 0 < ‖v z‖ := hv_pos e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
  let p : N → ℂ := fun z => v z / (‖v z‖ : ℂ)
  have norm_normalize (x : ℂ) (hx : 0 < ‖x‖) :
      ‖x / (‖x‖ : ℂ) - x‖ = |1 - ‖x‖| := norm_normalize x hx
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (∀ i ∈ F, 0 < w i (z : ℂ) →
      ‖p z - u i‖ < 2 * δ)
  intro i hi hwi
  have hnear := hv_close z i hi hwi
  have hshift := norm_normalize (v z) (hv_pos z)
  have hnormdiff : |1 - ‖v z‖| ≤ ‖v z - u i‖ := by
    calc
      |1 - ‖v z‖| = |‖v z‖ - 1| := abs_sub_comm _ _
      _ = |‖v z‖ - ‖u i‖| := by rw [hunit i]
      _ ≤ ‖v z - u i‖ := abs_norm_sub_norm_le _ _
  have htri : ‖p z - u i‖ ≤ ‖p z - v z‖ + ‖v z - u i‖ := by
    calc
      ‖p z - u i‖ = ‖(p z - v z) + (v z - u i)‖ := by congr 1; abel
      _ ≤ ‖p z - v z‖ + ‖v z - u i‖ := norm_add_le _ _
  linarith

private theorem hphi_circle_close (e : C(Circle, ℂ)) (he : Function.Injective e) (eps : ℝ) (heps
    : 0 < eps) (S : Set ↑(Set.range ⇑e)) (δ₀ : ℝ) (η : ℝ) (hSf : S.Finite) (hη : η > 0) (hδ₀ : δ₀
    > 0) (hηψ : ∀ ⦃a b : ↑(Set.range ⇑e)⦄, dist a b < η → dist ((u e he) a) ((u e he) b) < (δ
    δ₀)) (z : (N e eps S η hSf)) (i : Set.range e) (hi : i ∈ (F e S hSf))
      (hwi : 0 < (w e eps η) i (z : ℂ)) : dist ((phiVal e he eps heps S δ₀ η hSf hη hδ₀ hηψ) z)
          ((ψ e he) i) < 2 * (δ δ₀) := by
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  let δ := min (δ₀ / 4) (1 / 8)
  let r := min (η / 8) (eps / 8)
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  let p : N → ℂ := fun z => v z / (‖v z‖ : ℂ)
  have hp_norm (z : N) : ‖p z‖ = 1 := hp_norm e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
  let phiVal : N → Circle := fun z => ⟨p z, (mem_sphere_zero_iff_norm).2 (hp_norm z)⟩
  have hphi_near (z : N) : ∀ i ∈ F, 0 < w i (z : ℂ) →
      ‖p z - u i‖ < 2 * δ := hphi_near e he eps heps S δ₀ η hSf hη hδ₀ hηψ z
  dsimp only [ControlledNeighborhoodConstruction.N] at *
  change (dist (phiVal z) (ψ i) < 2 * δ)
  have h := hphi_near z i hi hwi
  have hIso : Isometry ((↑) : Circle → ℂ) := isometry_subtype_coe
  calc
    dist (phiVal z) (ψ i) = dist ((phiVal z : Circle) : ℂ) ((ψ i : Circle) : ℂ) :=
      (hIso.dist_eq (phiVal z) (ψ i)).symm
    _ = dist (p z) (u i) := by rfl
    _ = ‖p z - u i‖ := dist_eq_norm _ _
    _ < 2 * δ := h

end ControlledNeighborhoodConstruction

theorem P3821T1ControlledNeighborhood (e : C(Circle, ℂ))
    (he : Function.Injective e) (eps : ℝ) (heps : 0 < eps) :
    ∃ N : Set ℂ, IsOpen N ∧ Set.range e ⊆ N ∧
      ∃ phi : C(N, Circle), ∀ z : N, ‖e (phi z) - (z : ℂ)‖ < eps := by
-- BODY
  classical
  let f : Circle ≃ Set.range e := Equiv.ofBijective
    (fun x => (⟨e x, ⟨x, rfl⟩⟩ : Set.range e)) (by
      constructor
      · intro x y h
        apply he
        exact congrArg Subtype.val h
      · rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩)
  let : T2Space (Set.range e) := inferInstance
  let ψ : Set.range e → Circle := f.symm
  let u : Set.range e → ℂ := fun k => (ψ k : ℂ)
  have heUC : UniformContinuous e := ControlledNeighborhoodConstruction.heUC e
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuous_iff.mp heUC (eps / 2) (half_pos heps)
  let δ := min (δ₀ / 4) (1 / 8)
  have hδpos : 0 < δ := ControlledNeighborhoodConstruction.hδpos δ₀ hδ₀
  have hKcompact : IsCompact (Set.range e) := ControlledNeighborhoodConstruction.hKcompact e
  let : CompactSpace (Set.range e) := isCompact_iff_compactSpace.mp hKcompact
  have hψUC : UniformContinuous u := ControlledNeighborhoodConstruction.hψUC e he
  obtain ⟨η, hη, hηψ⟩ := Metric.uniformContinuous_iff.mp hψUC δ hδpos
  let r := min (η / 8) (eps / 8)
  have hrpos : 0 < r := ControlledNeighborhoodConstruction.hrpos eps heps η hη
  have hrerr : 2 * r < eps / 2 := ControlledNeighborhoodConstruction.hrerr eps heps η hη
  have heclose : ∀ u v : Circle, dist u v < 2 * δ → dist (e u) (e v) < eps / 2 :=
      ControlledNeighborhoodConstruction.heclose e eps δ₀ hδ hδ₀
  have hKcompact' : IsCompact (Set.range e) := ControlledNeighborhoodConstruction.hKcompact e
  let : CompactSpace (Set.range e) := isCompact_iff_compactSpace.mp hKcompact'
  obtain ⟨S, hSsub, hSf, hcover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Set.range e))).finite_cover_balls
      (X := Set.range e) hrpos
  let F : Finset (Set.range e) := hSf.toFinset
  let w : Set.range e → ℂ → ℝ := fun c z => max 0 (2 * r - dist z (c : ℂ))
  let W : ℂ → ℝ := fun z => ∑ c ∈ F, w c z
  let N : Set ℂ := {z | 0 < W z}
  have hNopen : IsOpen N := ControlledNeighborhoodConstruction.hNopen e eps S η hSf
  have hKN : Set.range e ⊆ N := ControlledNeighborhoodConstruction.hKN e eps heps S η hSf hcover hη
  let a : N → Set.range e → ℝ := fun z c => w c (z : ℂ) / W (z : ℂ)
  let v : N → ℂ := fun z => ∑ c ∈ F, (a z c : ℂ) * u c
  have hactive (z : N) : ∃ i ∈ F, 0 < w i (z : ℂ) := ControlledNeighborhoodConstruction.hactive e
      eps S η hSf z
  have hw_active_dist (z : N) (c : Set.range e) (hc : 0 < w c (z : ℂ)) :
      dist (z : ℂ) (c : ℂ) < 2 * r := ControlledNeighborhoodConstruction.hw_active_dist e eps S η
          hSf z c hc
  have hψmap (c : Set.range e) : e (ψ c) = c := ControlledNeighborhoodConstruction.hψmap e he c
  let p : N → ℂ := fun z => v z / (‖v z‖ : ℂ)
  have hp_norm (z : N) : ‖p z‖ = 1 := ControlledNeighborhoodConstruction.hp_norm e he eps heps S
      δ₀ η hSf hη hδ₀ hηψ z
  let phiVal : N → Circle := fun z => ⟨p z, (mem_sphere_zero_iff_norm).2 (hp_norm z)⟩
  have hphiVal_cont : Continuous phiVal := ControlledNeighborhoodConstruction.hphiVal_cont e he
      eps heps S δ₀ η hSf hη hδ₀ hηψ
  have hphi_circle_close (z : N) (i : Set.range e) (hi : i ∈ F)
      (hwi : 0 < w i (z : ℂ)) : dist (phiVal z) (ψ i) < 2 * δ :=
          ControlledNeighborhoodConstruction.hphi_circle_close e he eps heps S δ₀ η hSf hη hδ₀
          hηψ z i hi hwi
  refine ⟨N, hNopen, hKN, ⟨⟨phiVal, hphiVal_cont⟩, ?_⟩⟩
  intro z
  obtain ⟨i, hi, hwi⟩ := hactive z
  have hcircle := hphi_circle_close z i hi hwi
  have hecurve := heclose (phiVal z) (ψ i) hcircle
  have hecenter : e (ψ i) = (i : ℂ) := hψmap i
  have hzcenter : dist (z : ℂ) (i : ℂ) < 2 * r := hw_active_dist z i hwi
  calc
    ‖e (phiVal z) - (z : ℂ)‖ = dist (e (phiVal z)) (z : ℂ) := (dist_eq_norm _ _).symm
    _ ≤ dist (e (phiVal z)) (i : ℂ) + dist (i : ℂ) (z : ℂ) := dist_triangle _ _ _
    _ < eps := by
      rw [hecenter] at hecurve
      have hzcenter' : dist (i : ℂ) (z : ℂ) < 2 * r := by simpa [dist_comm] using hzcenter
      linarith [hecurve, hzcenter', hrerr]

end ApollonianSuperharmonic

end

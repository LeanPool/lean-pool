/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Families
public import LeanPool.AlmostInvariantSubspaces.PartB

/-!
# Invariant finite sums of intersections

The family argument supplies an invariant subspace and a quantitative descent estimate.
The descent assembles an invariant finite sum of finite intersections of members.
This strengthens Theorem A of Kazhdan and Polishchuk and gives a form fixed by every
order automorphism of the subspace lattice that permutes the family.
-/

@[expose] public section

open Module

namespace KPFullFinal

/-- **(S2')** Theorem A in its original form with the bound `r K_r`, `K_r = ∑_{j=1}^{r}
⌈(r+1)/j⌉`. -/
theorem kp_family_finite_form_sharp {K V G X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Group G] [MulAction G X] [Nonempty X] (ρ : G →* (V ≃ₗ[K] V)) (A : X → Submodule K V)
    (hA : ∀ (g : G) (x : X), A (g • x) = (A x).map (ρ g : V →ₗ[K] V)) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤
          (r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ : ℕ) := by
  have hr' : ∀ x y, AlmostInvariant.d (A x) (A y) ≤ r := fun x y =>
    (KPFull.PartB.d_le_iff_rank _ _ r).mpr (hr x y)
  obtain ⟨W, hW, hb, s, wt, t, τ, hw0, hw1, -, ht, htτ, h1⟩ :=
    KPFamilies.kp_family_export_linear ρ A (fun g x => ⟨g • x, (hA g x).symm⟩) r hr'
  exact KPFull.PartB.kp_family_finite_form_sharp_of_W ρ A hA r hr W hW hb s wt t τ hw0 hw1 ht htτ h1

/-- **(S2)** Theorem A exactly as printed, with `r² (r + 1)` in place of `r (r + 1)^(r + 1)`. -/
theorem kp_family_finite_form {K V G X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Group G] [MulAction G X] [Nonempty X] (ρ : G →* (V ≃ₗ[K] V)) (A : X → Submodule K V)
    (hA : ∀ (g : G) (x : X), A (g • x) = (A x).map (ρ g : V →ₗ[K] V)) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤ (r ^ 2 * (r + 1) : ℕ) := by
  obtain ⟨S, W, h1, h2, h3, h4, h5⟩ := kp_family_finite_form_sharp ρ A hA r hr
  refine ⟨S, W, h1, h2, h3, h4, fun x => ⟨(h5 x).1, (h5 x).2.trans ?_⟩⟩
  rw [← KPFull.PartB.Kr_eq_ceil]
  have hK : r * KPFull.PartB.Kr r ≤ r ^ 2 * (r + 1) := by
    calc r * KPFull.PartB.Kr r ≤ r * (r * (r + 1)) := Nat.mul_le_mul_left r (KPFull.PartB.Kr_le r)
      _ = r ^ 2 * (r + 1) := by ring
  exact_mod_cast hK

/-- The group of all lattice automorphisms that permute the members of the family. -/
def permGroup {K V X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] (A : X
    → Submodule K V) :
    Subgroup (Submodule K V ≃o Submodule K V) where
  carrier := {φ | (∀ x, ∃ y, φ (A x) = A y) ∧ (∀ y, ∃ x, φ (A x) = A y)}
  mul_mem' := by
    rintro φ ψ ⟨hφ1, hφ2⟩ ⟨hψ1, hψ2⟩
    refine ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, hy⟩ := hψ1 x
      obtain ⟨z, hz⟩ := hφ1 y
      exact ⟨z, by rw [RelIso.mul_apply, hy, hz]⟩
    · obtain ⟨x1, hx1⟩ := hφ2 y
      obtain ⟨x2, hx2⟩ := hψ2 x1
      exact ⟨x2, by rw [RelIso.mul_apply, hx2, hx1]⟩
  one_mem' := ⟨fun x => ⟨x, rfl⟩, fun y => ⟨y, rfl⟩⟩
  inv_mem' := by
    rintro φ ⟨hφ1, hφ2⟩
    refine ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨x', hx'⟩ := hφ2 x
      exact ⟨x', by rw [← hx', RelIso.inv_apply_self]⟩
    · obtain ⟨x', hx'⟩ := hφ1 y
      exact ⟨x', by rw [← hx', RelIso.inv_apply_self]⟩

theorem mem_permGroup {K V X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {A : X
    → Submodule K V}
    {φ : Submodule K V ≃o Submodule K V} :
    φ ∈ permGroup A ↔ (∀ x, ∃ y, φ (A x) = A y) ∧ (∀ y, ∃ x, φ (A x) = A y) := Iff.rfl

/-- **(S4)** Canonical form: `W` is fixed by every lattice automorphism that permutes the members.
-/
theorem kp_family_canonical {K V X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Nonempty X]
    (A : X → Submodule K V) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ φ : Submodule K V ≃o Submodule K V,
        (∀ x, ∃ y, φ (A x) = A y) → (∀ y, ∃ x, φ (A x) = A y) → φ W = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤
          (r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ : ℕ) := by
  have hr' : ∀ x y, AlmostInvariant.d (A x) (A y) ≤ r := fun x y =>
    (KPFull.PartB.d_le_iff_rank _ _ r).mpr (hr x y)
  obtain ⟨W, hW, hb, s, wt, t, τ, hw0, hw1, -, ht, htτ, h1⟩ :=
    KPFamilies.kp_family_export (permGroup A).subtype A (fun g x => (mem_permGroup.mp g.2).1 x)
        r hr'
  exact KPFull.PartB.kp_family_canonical_of_W A r hr W
    (fun φ hφ1 hφ2 => hW ⟨φ, mem_permGroup.mpr ⟨hφ1, hφ2⟩⟩) hb s wt t τ hw0 hw1 ht htτ h1

/-- **Lattice form of S2': modules over any ring (lengths), any group acting by automorphisms of
the lattice of
submodules** (for example linear or semilinear automorphisms of `M`; this is the form that Galois
descent needs).
If each `g` maps members to members and `ℓ(A x / (A x ∩ A y)) ≤ r`, there is a finite sum of
finite intersections `W`,
fixed by the group, with `ℓ(W / (W ∩ A x)) ≤ r` and `ℓ(A x / (A x ∩ W)) ≤ r K_r`. -/
theorem kp_family_finite_form_lattice {R M G X : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Group G]
    [Nonempty X] (ρ : G →* (Submodule R M ≃o Submodule R M)) (A : X → Submodule R M)
    (hA : ∀ g x, ∃ y, ρ g (A x) = A y) (r : ℕ)
    (hr : ∀ x y, Module.length R (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ (S : Finset (Finset X)) (W : Submodule R M),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧ (∀ g, ρ g W = W) ∧
      ∀ x, Module.length R (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.length R (A x ⧸ W.submoduleOf (A x)) ≤
          ((r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ : ℕ) : ℕ∞) := by
  classical
  obtain ⟨W, hW, hb, s, wt, t, τ, hw0, hw1, -, ht, htτ, h1⟩ := KPFamilies.kp_family_export ρ A hA
      r hr
  have hdesc := KPFull.PartB.descent_of_export s wt hw0 hw1 t τ ht htτ h1
  obtain ⟨⟨F, hFne, hF, hD⟩, hb1, hb2⟩ :=
    KPFull.PartB.partB A W r hr (fun x => (hb x).1) (fun x => (hb x).2) hdesc
  refine ⟨F, KPFull.PartB.sumInter A W, hFne inferInstance, fun T hT => (hF T hT).1, hD,
    KPFull.PartB.sumInter_fixed_of_lattice_group ρ A W hA hW, fun x => ⟨hb1 x, ?_⟩⟩
  rw [← KPFull.PartB.Kr_eq_ceil]
  exact hb2 x

end KPFullFinal

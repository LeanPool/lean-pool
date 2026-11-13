/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.OrderClosures.BanLat.Substructures.Band.Basic



/-!
# The lattice of bands

The collection of bands of a vector lattice `X`, ordered by inclusion, forms a
complete lattice. It contains the whole space `⊤ = X`, the trivial band
`⊥ = {0}`, and is closed under arbitrary intersections; binary infima are
given by intersection.
-/

@[expose] public section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

namespace Band

/-! ### The order on bands -/

/-- Bands of `X`, ordered by inclusion, form a partial order. -/
instance : PartialOrder (Band X) := .ofSetLike (Band X)

/-! ### Arbitrary intersections, top and bottom -/

/-- Arbitrary intersections of bands are bands. -/
instance : InfSet (Band X) where
  sInf S :=
    { toOrderIdeal := sInf ((·.toOrderIdeal) '' S)
      sSup_mem' := by
        intro T hTsub hne x hx
        refine OrderIdeal.mem_sInf.mpr ?_
        rintro _ ⟨B, hB, rfl⟩
        refine B.sSup_mem (fun s hs => ?_) hne hx
        exact OrderIdeal.mem_sInf.mp (hTsub hs) _ ⟨B, hB, rfl⟩ }

@[simp] theorem mem_sInf {S : Set (Band X)} {x : X} :
    x ∈ (sInf S : Band X) ↔ ∀ B ∈ S, x ∈ B := by
  change x ∈ (sInf ((·.toOrderIdeal) '' S) : OrderIdeal X) ↔ _
  rw [OrderIdeal.mem_sInf]
  exact ⟨fun h B hB => h _ ⟨B, hB, rfl⟩,
    by rintro h _ ⟨B, hB, rfl⟩; exact h B hB⟩

/-- The whole space `X` is a band. -/
instance : Top (Band X) where
  top :=
    { toOrderIdeal := ⊤
      sSup_mem' := fun _ _ _ _ _ => OrderIdeal.mem_top }

@[simp] theorem mem_top {x : X} : x ∈ (⊤ : Band X) := Submodule.mem_top

/-- The trivial band `{0}` is a band. -/
instance : Bot (Band X) where
  bot :=
    { toOrderIdeal := ⊥
      sSup_mem' := by
        intro S hSsub hne x hx
        obtain ⟨s₀, hs₀⟩ := hne
        have hs₀_eq : s₀ = 0 := OrderIdeal.mem_bot.mp (hSsub hs₀)
        have hub : x ≤ 0 :=
          hx.2 (fun s hs => by
            rw [OrderIdeal.mem_bot.mp (hSsub hs)])
        have hlb : 0 ≤ x := by
          have h := hx.1 hs₀; rwa [hs₀_eq] at h
        exact OrderIdeal.mem_bot.mpr (le_antisymm hub hlb) }

@[simp] theorem mem_bot {x : X} : x ∈ (⊥ : Band X) ↔ x = 0 :=
  Submodule.mem_bot ℝ

/-! ### The complete lattice of bands -/

/-- Bands of `X`, ordered by inclusion, form a complete lattice. Arbitrary
infima are given by intersection, the bottom element is the trivial band
`{0}`, and the top element is the whole space. -/
instance : CompleteLattice (Band X) where
  __ := (inferInstance : PartialOrder (Band X))
  sup B₁ B₂ := sInf {K : Band X | B₁ ≤ K ∧ B₂ ≤ K}
  inf B₁ B₂ :=
    { toOrderIdeal := B₁.toOrderIdeal ⊓ B₂.toOrderIdeal
      sSup_mem' := by
        intro S hSsub hne x hx
        refine ⟨B₁.sSup_mem (fun s hs => (hSsub hs).1) hne hx,
          B₂.sSup_mem (fun s hs => (hSsub hs).2) hne hx⟩ }
  top := ⊤
  bot := ⊥
  sInf := sInf
  sSup S := sInf {K : Band X | ∀ B ∈ S, B ≤ K}
  le_top := fun _ _ _ => Submodule.mem_top
  bot_le := fun B x hx => by
    rw [mem_bot.mp hx]; exact B.toOrderIdeal.toSubmodule.zero_mem
  le_sup_left := fun B₁ _ x hx => by
    rw [mem_sInf]; rintro K ⟨h₁, _⟩; exact h₁ hx
  le_sup_right := fun _ B₂ x hx => by
    rw [mem_sInf]; rintro K ⟨_, h₂⟩; exact h₂ hx
  sup_le := fun B₁ B₂ K h₁ h₂ x hx => by
    rw [mem_sInf] at hx; exact hx K ⟨h₁, h₂⟩
  inf_le_left := fun _ _ _ hx => hx.1
  inf_le_right := fun _ _ _ hx => hx.2
  le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩
  isLUB_sSup := fun S => by
    refine ⟨?_, ?_⟩
    · intro J hJ x hx
      rw [mem_sInf]
      intro K hK
      exact hK J hJ hx
    · intro J hJ x hx
      rw [mem_sInf] at hx
      exact hx J hJ
  isGLB_sInf := fun S => by
    refine ⟨?_, ?_⟩
    · intro J hJ x hx
      rw [mem_sInf] at hx
      exact hx J hJ
    · intro J hJ x hx
      rw [mem_sInf]
      intro K hK
      exact hJ hK hx

@[simp] theorem inf_toOrderIdeal (B₁ B₂ : Band X) :
    (B₁ ⊓ B₂).toOrderIdeal = B₁.toOrderIdeal ⊓ B₂.toOrderIdeal := rfl

end Band

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation
public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.NetExists
import LeanPool.GraphMinor.GM07.NetSwapBasic

/-!
# Seam edges as net sides

In VII (4.6), the edge `e` of the seam off `bd(Σ)` is the image of one
side of a pair, so its parameter can be taken to be `φ ∘ f`. Then the
positions on `e` used on pages 225 to 230 are also positions on the two
sides of `Δ`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Each seam edge off the boundary is the image of the open side of a pair, by the point
that the side and the edge share. -/
theorem Net.exists_side_of_edge [T2Space S] (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) {e : Set S} (he : e ∈ J.E) (hbd : e ∩ bd S = ∅) :
    ∃ i : Fin N.r, e = (N.φ ∘ N.f i) '' Ioo (0 : unitInterval) 1 := by
  obtain ⟨z, hz⟩ := he.1
  have hzU : z ∈ J.U \ J.V := he.2.1 hz
  have hzseam : z ∈ N.seamU := hJ.2.1 ▸ hzU.1
  obtain ⟨x, hx, rfl⟩ := hzseam
  have hxb : N.φ x ∉ bd S := fun h => (eq_empty_iff_forall_notMem.mp hbd _) ⟨hz, h⟩
  have hxV : N.φ x ∉ N.seamV := fun h => hzU.2 (hJ.2.2 ▸ h)
  obtain ⟨i, w, hw, hfw, -, -⟩ := N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hx hxb hxV
  let c : C(unitInterval, S) := ⟨N.φ ∘ N.f i, N.quotientMap_φ.continuous.comp (N.f i).continuous⟩
  have hc0 : c 0 ∈ J.V := hJ.2.2 ▸ ⟨i, .inl rfl⟩
  have hc1 : c 1 ∈ J.V := hJ.2.2 ▸ ⟨i, .inr rfl⟩
  have hIoo : ∀ t ∈ Ioo (0 : unitInterval) 1, c t ∈ J.U \ J.V := by
    intro t ht
    rw [hJ.2.1, hJ.2.2]
    exact ⟨⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩, N.notMem_seamV_of_mem_Ioo i ht⟩
  have hinj : InjOn c (Ioo (0 : unitInterval) 1) := by
    intro a ha b hb hab
    exact N.injective_f i (N.injOn_image_open_side i ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hab)
  have hE := (GraphMinor.GM07.Drawing.eq_edge_of_injOn_Ioo J c hc0 hc1 hIoo hinj).1
  refine ⟨i, arcComponentsIn_eq_of_mem he hE hz ⟨w, hw, hfw⟩⟩

/-- A parameter of the seam graph which is `φ ∘ f` on each edge off the boundary. -/
theorem Net.exists_edgePar_sides [T2Space S] [Nonempty S] (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    ∃ γ : Set S → unitInterval → S, EdgePar J γ ∧
      ∀ e ∈ J.E, e ∩ bd S = ∅ → ∃ i : Fin N.r, ∀ t, γ e t = N.φ (N.f i t) := by
  classical
  obtain ⟨γ₀, hγ₀⟩ := exists_edgePar J
  let P : Set S → Prop := fun e => ∃ i : Fin N.r, e = (N.φ ∘ N.f i) '' Ioo (0 : unitInterval) 1
  let γ : Set S → unitInterval → S := fun e =>
    if h : P e then N.φ ∘ N.f h.choose else γ₀ e
  have hpos : ∀ e (h : P e), γ e = N.φ ∘ N.f h.choose := fun e h => dite_eq_left h
  have hneg : ∀ e, ¬P e → γ e = γ₀ e := fun e h => dite_eq_right h
  refine ⟨γ, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    by_cases h : P e
    · rw [hpos e h]
      exact N.quotientMap_φ.continuous.comp (N.f _).continuous
    · rw [hneg e h]
      exact hγ₀.cont e he
  · intro e he
    by_cases h : P e
    · rw [hpos e h]
      exact hJ.2.2 ▸ ⟨_, .inl rfl⟩
    · rw [hneg e h]
      exact hγ₀.zero e he
  · intro e he
    by_cases h : P e
    · rw [hpos e h]
      exact hJ.2.2 ▸ ⟨_, .inr rfl⟩
    · rw [hneg e h]
      exact hγ₀.one e he
  · intro e he
    by_cases h : P e
    · rw [hpos e h]
      intro a ha b hb hab
      exact N.injective_f _ (N.injOn_image_open_side _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hab)
    · rw [hneg e h]
      exact hγ₀.inj e he
  · intro e he
    by_cases h : P e
    · rw [hpos e h]
      exact h.choose_spec.symm
    · rw [hneg e h]
      exact hγ₀.image e he
  · intro e he hb
    have h : P e := N.exists_side_of_edge hJ he hb
    exact ⟨h.choose, fun t => by rw [hpos e h]; rfl⟩

end GraphMinor.GM07

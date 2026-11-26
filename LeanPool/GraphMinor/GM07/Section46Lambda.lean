/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Open
public import LeanPool.GraphMinor.GM07.Section4
import LeanPool.GraphMinor.GM07.Section41
import LeanPool.GraphMinor.GM07.Section46PsiFibres
import LeanPool.GraphMinor.GM07.Section46CentralLift

/-!
# The bound on `Λ` in VII (4.6)

Page 228: "We claim that `|Λ| ≤ w + k`." Two vertices of `λ ∈ Λ` lie on the
boundary of the disc, one on each side of the test arc. They are not isolated,
so their images lie in the part of `U(θ⁻¹(H))` that claim (1) controls. That
part has at most `2w + 2k` points over it. The text speaks of each `d ∈ λ`;
members of `λ` may be inside the disc, so we use one member on each side.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM06

variable {S' D : Type} [TopologicalSpace S'] [TopologicalSpace D]

/-- A vertex of a component with a second vertex is on an edge of the whole graph. -/
theorem exists_edge_of_component {Γ C : Drawing D} (hC : IsGraphComponent C.toGraph Γ.toGraph)
    {x y : D} (hx : x ∈ C.V) (hy : y ∈ C.V) (hne : x ≠ y) : ∃ e ∈ Γ.E, x ∈ closure e := by
  obtain ⟨W⟩ := hC.2.1.2 x hx y hy
  cases W with
  | nil _ => exact (hne rfl).elim
  | @cons _ v _ e hl _ =>
    have hl' := hl.mono hC.1
    exact ⟨e, hl'.1, (hl'.2.2.2.symm.subset (by simp)).1⟩

/-- Page 228: a vertex on `bd(Δ)` of a component of `φ⁻¹(H)` with a second vertex lies over the part
of `U(θ⁻¹(H))` that claim (1) controls. -/
theorem image_mem_of_component {K' H' : Drawing S'} {ψ : D → S'} {Hd C : Drawing D}
    (hψ : IsCutAlongGraph K' D ψ) (hp : IsPullbackDrawing ψ H' Hd)
    {T : Set S'} (hTc : IsClosed T) (hT : ∀ e' ∈ H'.E, closure e' ⊆ T)
    (hC : IsGraphComponent C.toGraph Hd.toGraph) {d d' : D} (hd : d ∈ C.V) (hd' : d' ∈ C.V)
    (hne : d ≠ d') (hb : d ∈ bd D) : ψ d ∈ T ∧ (ψ d ∈ K'.U ∨ ψ d ∈ bd S') := by
  obtain ⟨e, he, hde⟩ := exists_edge_of_component hC hd hd' hne
  have hsub : e ⊆ ψ ⁻¹' T := by
    intro x hx
    have hx' := he.2.1 hx
    rw [hp.1, hp.2] at hx'
    rcases (mem_U_iff_edge H').mp hx'.1 with h | ⟨e', he', hxe'⟩
    · exact (hx'.2 h).elim
    · exact hT e' he' (subset_closure hxe')
  refine ⟨closure_minimal hsub (hTc.preimage hψ.quotientMap.continuous) hde, ?_⟩
  have : d ∈ ψ ⁻¹' (bd S' ∪ K'.U) := by
    rw [hψ.preimage_bd_union_U]
    exact hb
  exact this.symm

private theorem ncard_preimage_le {α β : Type*} {ψ : α → β} {A : Set β} (hA : A.Finite) (n : ℕ)
    (h : ∀ v ∈ A, (ψ ⁻¹' {v}).ncard ≤ n) : (ψ ⁻¹' A).ncard ≤ A.ncard * n := by
  induction A, hA using Set.Finite.induction_on with
  | empty => simp
  | @insert a s has hs ih =>
    have hins : ψ ⁻¹' insert a s = ψ ⁻¹' {a} ∪ ψ ⁻¹' s := by
      ext x
      simp
    rw [hins, ncard_insert_of_notMem has hs, add_mul, one_mul, add_comm]
    exact (ncard_union_le _ _).trans
      (Nat.add_le_add (h a (mem_insert a s)) (ih fun v hv => h v (mem_insert_of_mem a hv)))

/-- `|Λ| ≤ w + k` in VII (4.6), page 228. -/
theorem card_Lambda_le [T2Space D] {K' H' : Drawing S'} {ψ : D → S'} {Hd : Drawing D}
    (hS' : IsSurface S') (hψ : IsCutAlongGraph K' D ψ) (hp : IsPullbackDrawing ψ H' Hd)
    {T : Set S'} (hTc : IsClosed T) (hT : ∀ e' ∈ H'.E, closure e' ⊆ T)
    {w k : ℕ} (hfK : (T ∩ K'.U).Finite) (hcK : (T ∩ K'.U).ncard ≤ w)
    (hfb : (T ∩ bd S').Finite) (hcb : (T ∩ bd S').ncard ≤ 2 * k)
    (hfib : ∀ v ∈ K'.U, (ψ ⁻¹' {v}).ncard ≤ 2)
    {C₁ C₂ : Set D} (hC₁ : C₁ ⊆ bd D) (hC₂ : C₂ ⊆ bd D) (hdis : Disjoint C₁ C₂) (s t : D) :
    {V₀ : Set D | ∃ C : Drawing D, IsGraphComponent C.toGraph Hd.toGraph ∧ V₀ = C.V ∧
      (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀}.ncard ≤ w + k := by
  classical
  set Λ : Set (Set D) := {V₀ : Set D | ∃ C : Drawing D, IsGraphComponent C.toGraph Hd.toGraph ∧
    V₀ = C.V ∧ (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀} with hΛ
  rcases Λ.eq_empty_or_nonempty with h0 | ⟨A₀, hA₀⟩
  · rw [h0, ncard_empty]
    exact Nat.zero_le _
  obtain ⟨C₀, -, -, ⟨d₀, -⟩, -⟩ := hA₀
  have : Nonempty D := ⟨d₀⟩
  let Z₁ : Set D := ψ ⁻¹' (T ∩ K'.U)
  let Z₂ : Set D := ψ ⁻¹' ((T ∩ bd S') \ K'.U)
  let Z : Set D := Z₁ ∪ Z₂
  have hZ₁f : Z₁.Finite := Set.Finite.preimage' hfK fun b _ => hψ.finite_fiber b
  have hZ₂f : Z₂.Finite := Set.Finite.preimage' (hfb.subset sdiff_subset) fun b _
    => hψ.finite_fiber b
  have hZf : Z.Finite := hZ₁f.union hZ₂f
  have hZ₁c : Z₁.ncard ≤ w * 2 :=
    (ncard_preimage_le hfK 2 fun v hv => hfib v hv.2).trans (Nat.mul_le_mul_right 2 hcK)
  have hZ₂c : Z₂.ncard ≤ 2 * k := by
    have h1 : Z₂.ncard ≤ ((T ∩ bd S') \ K'.U).ncard * 1 := by
      refine ncard_preimage_le (hfb.subset sdiff_subset) 1 fun v hv => ?_
      refine (Set.ncard_le_one (hψ.finite_fiber v)).mpr fun a ha b hb => ?_
      refine hψ.eq_of_eq_of_notMem hS' (ha.trans hb.symm) ?_
      rw [show ψ a = v from ha]
      exact hv.2
    have h2 := ncard_le_ncard (sdiff_subset (s := T ∩ bd S') (t := K'.U)) hfb
    omega
  have hmem : ∀ d ∈ bd D, ψ d ∈ T ∧ (ψ d ∈ K'.U ∨ ψ d ∈ bd S') → d ∈ Z := by
    rintro d - ⟨hdT, hdb⟩
    by_cases hK : ψ d ∈ K'.U
    · exact .inl ⟨hdT, hK⟩
    · exact .inr ⟨⟨hdT, hdb.resolve_left hK⟩, hK⟩
  have hside : ∀ V₀ ∈ Λ, (∃ d ∈ V₀, d ∈ C₁ ∧ d ∈ Z) ∧ ∃ d ∈ V₀, d ∈ C₂ ∧ d ∈ Z := by
    rintro V₀ ⟨C, hC, rfl, ⟨d₁, hd₁, hd₁C⟩, ⟨d₂, hd₂, hd₂C⟩, -⟩
    have hne : d₁ ≠ d₂ := fun h => disjoint_left.mp hdis hd₁C (h ▸ hd₂C)
    exact ⟨⟨d₁, hd₁, hd₁C, hmem d₁ (hC₁ hd₁C)
      (image_mem_of_component hψ hp hTc hT hC hd₁ hd₂ hne (hC₁ hd₁C))⟩,
      d₂, hd₂, hd₂C, hmem d₂ (hC₂ hd₂C)
      (image_mem_of_component hψ hp hTc hT hC hd₂ hd₁ hne.symm (hC₂ hd₂C))⟩
  choose! d₁ hd₁ using fun V₀ hV₀ => (hside V₀ hV₀).1
  choose! d₂ hd₂ using fun V₀ hV₀ => (hside V₀ hV₀).2
  have hcommon : ∀ {A B : Set D} {x : D}, A ∈ Λ → B ∈ Λ → x ∈ A → x ∈ B → A = B := by
    rintro A B x ⟨C, hC, rfl, -⟩ ⟨C', hC', rfl, -⟩ hx hx'
    exact congrArg (fun g : Graph D (Set D) => g.vertexSet) (hC.eq_of_mem_mem hC' hx hx')
  have h₁ : Λ.ncard ≤ (Z ∩ C₁).ncard := by
    refine ncard_le_ncard_of_injOn d₁ (fun A hA => ⟨(hd₁ A hA).2.2, (hd₁ A hA).2.1⟩) ?_
      (hZf.subset inter_subset_left)
    intro A hA B hB h
    exact hcommon hA hB (hd₁ A hA).1 (h ▸ (hd₁ B hB).1)
  have h₂ : Λ.ncard ≤ (Z ∩ C₂).ncard := by
    refine ncard_le_ncard_of_injOn d₂ (fun A hA => ⟨(hd₂ A hA).2.2, (hd₂ A hA).2.1⟩) ?_
      (hZf.subset inter_subset_left)
    intro A hA B hB h
    exact hcommon hA hB (hd₂ A hA).1 (h ▸ (hd₂ B hB).1)
  have hdisZ : Disjoint (Z ∩ C₁) (Z ∩ C₂) :=
    hdis.mono inter_subset_right inter_subset_right
  have hsum : (Z ∩ C₁).ncard + (Z ∩ C₂).ncard ≤ Z.ncard := by
    rw [← ncard_union_eq hdisZ (hZf.subset inter_subset_left) (hZf.subset inter_subset_left)]
    exact ncard_le_ncard (union_subset inter_subset_left inter_subset_left) hZf
  have hZc : Z.ncard ≤ Z₁.ncard + Z₂.ncard := ncard_union_le _ _
  omega

end GraphMinor.GM07

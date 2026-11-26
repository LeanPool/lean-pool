/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeContacts
import LeanPool.GraphMinor.GM07.Section46OrderedContacts

/-!
# The two cuts on each long seam edge

VII (4.6), page 225, chooses two contacts `W(e)` on a long edge. We
choose them in its interval parameter. Injectivity away from the two
parameter ends gives the exact linking counts and the central lower bound,
including when the old seam edge is a loop.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- The two contacts defining `W(e)` and their counts in VII (4.6), page 225.
The left and right closed intervals each have `μ + 1` graph vertices,
and the open central interval has at least `w`. -/
theorem exists_long_edge_cut_parameters {S : Type u} [TopologicalSpace S]
    [T2Space S] {G J : Drawing S} {γ : Set S → unitInterval → S}
    (hγ : EdgePar J γ) {e : Set S} (he : e ∈ J.E) {μ w : ℕ}
    (hμ : 0 < μ) (hlong : 2 * μ + w + 2 ≤ (closure e ∩ G.V).ncard) :
    ∃ s ∈ Ioo (0 : unitInterval) 1, ∃ t ∈ Ioo (0 : unitInterval) 1,
      s < t ∧ γ e s ∈ e ∩ G.V ∧ γ e t ∈ e ∩ G.V ∧ γ e s ≠ γ e t ∧
      (γ e '' Iic s ∩ G.V).ncard = μ + 1 ∧
      (γ e '' Ici t ∩ G.V).ncard = μ + 1 ∧
      w ≤ (γ e '' Ioo s t ∩ G.V).ncard := by
  let T := γ e ⁻¹' G.V
  have hT := finite_edge_contact_parameters (G := G) hγ he
  have hcard : 2 * μ + w + 2 ≤ T.ncard :=
    hlong.trans (ncard_edge_contacts_le_parameters hγ he)
  obtain ⟨s, hsT, t, htT, hst, hsCount, htCount, hmidCount⟩ :=
    exists_ordered_contact_cuts hT hcard
  have hs0 : s ≠ 0 := by
    intro hs
    have hsub : T ∩ Iic s ⊆ ({0} : Set unitInterval) := by
      intro x hx
      exact le_antisymm (hs ▸ hx.2) bot_le
    have hc := ncard_le_ncard hsub (finite_singleton _)
    rw [hsCount, ncard_singleton] at hc
    omega
  have ht1 : t ≠ 1 := by
    intro ht
    have hsub : T ∩ Ici t ⊆ ({1} : Set unitInterval) := by
      intro x hx
      exact le_antisymm le_top (ht ▸ hx.2)
    have hc := ncard_le_ncard hsub (finite_singleton _)
    rw [htCount, ncard_singleton] at hc
    omega
  have hs : s ∈ Ioo (0 : unitInterval) 1 :=
    ⟨unitInterval.pos_iff_ne_zero.mpr hs0, hst.trans_le le_top⟩
  have ht : t ∈ Ioo (0 : unitInterval) 1 :=
    ⟨bot_le.trans_lt hst, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
  have hsE : γ e s ∈ e :=
    (congrArg (fun A => γ e s ∈ A) (hγ.image e he)).mp ⟨s, hs, rfl⟩
  have htE : γ e t ∈ e :=
    (congrArg (fun A => γ e t ∈ A) (hγ.image e he)).mp ⟨t, ht, rfl⟩
  have hleft : InjOn (γ e) (Iic s) := by
    intro x hx y hy hxy
    rcases edge_parameter_eq_or_ends hγ he hxy with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact (not_le_of_gt hs.2 hy).elim
    · exact (not_le_of_gt hs.2 hx).elim
  have hright : InjOn (γ e) (Ici t) := by
    intro x hx y hy hxy
    rcases edge_parameter_eq_or_ends hγ he hxy with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact (not_le_of_gt ht.1 hx).elim
    · exact (not_le_of_gt ht.1 hy).elim
  have himage : ∀ A : Set unitInterval, γ e '' A ∩ G.V = γ e '' (T ∩ A) := by
    intro A
    ext x
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hx⟩
      exact ⟨u, ⟨hx, hu⟩, rfl⟩
    · rintro ⟨u, ⟨hu, huA⟩, rfl⟩
      exact ⟨⟨u, huA, rfl⟩, hu⟩
  refine ⟨s, hs, t, ht, hst, ⟨hsE, hsT⟩, ⟨htE, htT⟩,
    fun h => hst.ne (hγ.inj e he hs ht h), ?_, ?_, ?_⟩
  · rw [himage, (hleft.mono inter_subset_right).ncard_image]
    exact hsCount
  · rw [himage, (hright.mono inter_subset_right).ncard_image]
    exact htCount
  · have hsub : T ∩ Ioo s t ⊆ Ioo (0 : unitInterval) 1 := fun x hx =>
      ⟨hs.1.trans hx.2.1, hx.2.2.trans ht.2⟩
    rw [himage, ((hγ.inj e he).mono hsub).ncard_image]
    exact hmidCount

end GraphMinor.GM07

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM07.Section46CuffIncidences

/-!
# Interior and cuff incidences at a seam vertex

On page 225 of VII (4.6), each pasted endpoint pair contributes one
interior seam incidence. The cuff contributes two further incidences.
We count the non-loop and loop edges separately, so loops count twice.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- The interior seam incidences and the two cuff incidences in the
boundary valency count of VII (4.6), page 225. -/
theorem Net.interior_valency_add_two_le {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) {v : S} (hvV : v ∈ J.V) (hvbd : v ∈ bd S) :
    (N.F₁ v).card + 2 * (N.F₂ v).card + 2 ≤ vertexValency J v := by
  classical
  have : T2Space S := hS.2.1
  let S₂ := {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 2}
  let S₁ := {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1}
  let A := N.interiorSeamEdge '' (N.F₁ v : Set (Fin N.r))
  let B := N.interiorSeamEdge '' (N.F₂ v : Set (Fin N.r))
  have hf₂ : S₂.Finite := J.finite_edges.subset fun e he => he.1
  have hf₁ : S₁.Finite := J.finite_edges.subset fun e he => he.1
  have hA : A ⊆ S₂ := by
    rintro _ ⟨i, hi, rfl⟩
    rw [ Finset.mem_coe, mem_F₁_iff ] at hi
    have heE : N.interiorSeamEdge i ∈ J.E := N.e_int_mem_E hJ i
    have htilde : tilde (N.interiorSeamEdge i) = {N.φ (N.f i 0), N.φ (N.f i 1)}
      := N.tilde_e_int hJ i
    rcases hi with ⟨h0, hne⟩ | ⟨hne, h1⟩
    · have hvV : v ∈ J.V := hJ.2.2 ▸ ⟨i, Or.inl h0⟩
      have hv_tilde : v ∈ tilde (N.interiorSeamEdge i) := htilde ▸ Or.inl h0.symm
      refine ⟨heE, (vertexIncident_iff_mem_tilde J hvV heE).mpr hv_tilde, ?_⟩
      rw [htilde, h0, ncard_pair hne.symm]
    · have hvV : v ∈ J.V := hJ.2.2 ▸ ⟨i, Or.inr h1⟩
      have hv_tilde : v ∈ tilde (N.interiorSeamEdge i) := htilde ▸ Or.inr h1.symm
      refine ⟨heE, (vertexIncident_iff_mem_tilde J hvV heE).mpr hv_tilde, ?_⟩
      rw [htilde, h1, ncard_pair hne]
  have hB : B ⊆ S₁ := by
    rintro _ ⟨i, hi, rfl⟩
    rw [ Finset.mem_coe, mem_F₂_iff ] at hi
    rcases hi with ⟨h0, h1⟩
    have heE : N.interiorSeamEdge i ∈ J.E := N.e_int_mem_E hJ i
    have htilde : tilde (N.interiorSeamEdge i) = {v} := by
      rw [N.tilde_e_int hJ i, h0, h1, pair_eq_singleton]
    have hvV : v ∈ J.V := hJ.2.2 ▸ ⟨i, Or.inl h0⟩
    have hv_tilde : v ∈ tilde (N.interiorSeamEdge i) := htilde ▸ rfl
    refine ⟨heE, (vertexIncident_iff_mem_tilde J hvV heE).mpr hv_tilde, ?_⟩
    rw [htilde, ncard_singleton]
  have hd : Disjoint S₂ S₁ := disjoint_left.mpr fun e h₂ h₁ => by
    have heq := h₂.2.2.symm.trans h₁.2.2
    omega
  have hAB : Disjoint A B := hd.mono hA hB
  have hfA : A.Finite := hf₂.subset hA
  have hfB : B.Finite := hf₁.subset hB
  have hcardA : A.ncard = (N.F₁ v).card := by
    dsimp [A]
    rw [ncard_image_of_injective _ N.e_int_injective, ncard_coe_finset]
  have hcardB : B.ncard = (N.F₂ v).card := by
    dsimp [B]
    rw [ncard_image_of_injective _ N.e_int_injective, ncard_coe_finset]
  have hinc : ∀ e ∈ J.E, J.VertexIncident v e → e ∈ S₂ ∪ S₁ := by
    intro e he hi
    rcases ncard_tilde_of_mem_E J he with h₂ | h₁
    · exact .inl ⟨he, hi, h₂⟩
    · exact .inr ⟨he, hi, h₁⟩
  have hoff : ∀ e : Set S, e ⊆ bd S → e ∉ A ∪ B := by
    intro e hebd he
    have heimg : e ∈ range N.interiorSeamEdge := by
      rcases he with ⟨i, _, hi⟩ | ⟨i, _, hi⟩
      · exact ⟨i, hi⟩
      · exact ⟨i, hi⟩
    obtain ⟨i, rfl⟩ := heimg
    let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    have ht : t ∈ Ioo (0 : unitInterval) 1 := by
      constructor <;> change (_ : ℝ) < _ <;> norm_num [t]
    have hx : N.interiorSeamCurve i t ∈ N.interiorSeamEdge i := ⟨t, ht, rfl⟩
    exact disjoint_left.mp (N.disjoint_e_int_bd hS i) hx (hebd hx)
  have hbase : A ∪ B ⊆ S₂ ∪ S₁ := union_subset_union hA hB
  have hcardAB : (A ∪ B).ncard = (N.F₁ v).card + (N.F₂ v).card := by
    rw [ncard_union_eq hAB hfA hfB, hcardA, hcardB]
  have hsum : (S₂ ∪ S₁).ncard = S₂.ncard + S₁.ncard := ncard_union_eq hd hf₂ hf₁
  have hval : vertexValency J v = S₂.ncard + 2 * S₁.ncard := rfl
  rcases N.exists_cuff_incident_edges hS hJ hvV hvbd with
    ⟨e, he, hebd, hei, heloop⟩ | ⟨e₁, he₁, e₂, he₂, hne, hbd₁, hbd₂, hi₁, hi₂⟩
  · have heoff := hoff e hebd
    have heb : e ∉ B := fun hb => heoff (.inr hb)
    have hc₁ := ncard_le_ncard
      (show insert e (A ∪ B) ⊆ S₂ ∪ S₁ from insert_subset (hinc e he hei) hbase)
      (hf₂.union hf₁)
    have hc₂ := ncard_le_ncard
      (show insert e B ⊆ S₁ from insert_subset ⟨he, hei, heloop⟩ hB) hf₁
    rw [ncard_insert_of_notMem heoff (hfA.union hfB), hcardAB, hsum] at hc₁
    rw [ncard_insert_of_notMem heb hfB, hcardB] at hc₂
    omega
  · have heoff₁ := hoff e₁ hbd₁
    have heoff₂ := hoff e₂ hbd₂
    have hnot : e₁ ∉ insert e₂ (A ∪ B) := by
      rintro (h | h)
      · exact hne h
      · exact heoff₁ h
    have hc₁ := ncard_le_ncard
      (show insert e₁ (insert e₂ (A ∪ B)) ⊆ S₂ ∪ S₁ from
        insert_subset (hinc e₁ he₁ hi₁) (insert_subset (hinc e₂ he₂ hi₂) hbase))
      (hf₂.union hf₁)
    have hc₂ := ncard_le_ncard hB hf₁
    rw [ncard_insert_of_notMem hnot ((hfA.union hfB).insert e₂),
      ncard_insert_of_notMem heoff₂ (hfA.union hfB), hcardAB, hsum] at hc₁
    rw [hcardB] at hc₂
    omega

end GraphMinor.GM07

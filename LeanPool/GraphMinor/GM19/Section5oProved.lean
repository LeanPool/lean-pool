/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5o
public import LeanPool.GraphMinor.GM19.Section5n
public import LeanPool.GraphMinor.GM19.CapModel
public import LeanPool.GraphMinor.GM19.Conditional2

import LeanPool.GraphMinor.GM19.FeatureCount

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Graph Minors XIX: proved deductions from Section5o

The deductions use existing proofs after the preliminary geometry has been defined.
-/

public section
namespace GraphMinor.GM19
open Set Topology GraphMinor.Surface
universe w

/-- Transport an infinite sequence of bounded features to one feature drawing and pass to a
subsequence on which the vertex intersection with that drawing is fixed. -/
theorem exists_aligned_feature_subsequence {S : Type} [TopologicalSpace S] [T2Space S]
    {β : Type w} {χ : ColourScheme S β} (P : ℕ → ColouredPainting χ) (K : ℕ → Drawing S)
    {A : Set ℕ} (hA : A.Infinite) (bound : ℕ) (hFeature : ∀ i ∈ A, IsFeature χ.Φ (K i))
    (hBound : ∀ i ∈ A, (K i).V.ncard + (K i).E.ncard ≤ bound)
    (hIntersection : ∀ i ∈ A, (P i).Γ.U ∩ (K i).U ⊆ (P i).Γ.V ∩ (K i).V) :
    ∃ (e₁ e₂ : ℕ → ℕ) (α : ℕ → S ≃ₜ S) (hα : ∀ m, IsFramePreservingHomeo χ.Φ (α m)),
      StrictMono e₁ ∧ StrictMono e₂ ∧ (∀ m, e₁ m ∈ A) ∧
      (∀ m, α m '' (K (e₁ 0)).U = (K (e₁ m)).U) ∧
      (∀ m, α m '' (K (e₁ 0)).V = (K (e₁ m)).V) ∧
      let Q : ℕ → ColouredPainting χ := fun m ↦ (P (e₁ m)).image (α m).symm (hα m).symm
      (∀ m, (Q m).Γ.U ∩ (K (e₁ 0)).U ⊆ (Q m).Γ.V ∩ (K (e₁ 0)).V) ∧
      (∀ i j, ∀ v ∈ (K (e₁ 0)).V, v ∈ (Q (e₂ i)).Γ.V ↔ v ∈ (Q (e₂ j)).Γ.V) := by
  classical
  have : Nonempty (Drawing S) := ⟨K 0⟩
  obtain ⟨𝓕, hf, h𝓕⟩ := theorem_5_2_proof S χ.isSurface χ.connected χ.Φ bound
  have h𝓕' : ∀ i ∈ A, ∃ K₀ ∈ 𝓕, FeatureEquiv χ.Φ K₀ (K i) :=
    fun i hi ↦ h𝓕 _ (hFeature i hi) (hBound i hi)
  choose! G hG hG' using h𝓕'
  obtain ⟨K₀, -, hinf⟩ := exists_infinite_fiber hA hf G hG
  set e₁ := Nat.nth (· ∈ A ∩ G ⁻¹' {K₀})
  have he₁s : StrictMono e₁ := Nat.nth_strictMono hinf
  have he₁m : ∀ m, e₁ m ∈ A ∧ G (e₁ m) = K₀
    := fun m ↦ Nat.nth_mem_of_infinite hinf m
  set Kc := K (e₁ 0) with hKc
  have hfe : ∀ m, ∃ α : S ≃ₜ S, IsFramePreservingHomeo χ.Φ α ∧ α '' Kc.U = (K (e₁ m)).U ∧
      α '' Kc.V = (K (e₁ m)).V := by
    intro m
    obtain ⟨g₀, hg₀, hU₀, hV₀⟩ := hG' _ (he₁m 0).1
    obtain ⟨g, hg, hU, hV⟩ := hG' _ (he₁m m).1
    rw [(he₁m 0).2] at hU₀ hV₀
    rw [(he₁m m).2] at hU hV
    refine ⟨g₀.symm.trans g, hg₀.symm.trans hg, ?_, ?_⟩
    · have : (g₀.symm.trans g) '' Kc.U = g '' (g₀.symm '' Kc.U) := by
        rw [image_image]
        rfl
      rw [this, hKc, ← hU₀, symm_image_image', hU]
    · have : (g₀.symm.trans g) '' Kc.V = g '' (g₀.symm '' Kc.V) := by
        rw [image_image]
        rfl
      rw [this, hKc, ← hV₀, symm_image_image', hV]
  choose α hα hαU hαV using hfe
  let Q : ℕ → ColouredPainting χ := fun m ↦ (P (e₁ m)).image (α m).symm (hα m).symm
  have hQ : ∀ m, IsColouredImage (α m).symm (P (e₁ m)) (Q m) := fun m ↦
    ColouredPainting.isImage_image _ _ _
  have hinter : ∀ m, (Q m).Γ.U ∩ Kc.U ⊆ (Q m).Γ.V ∩ Kc.V := by
    rintro m x ⟨hx₁, hx₂⟩
    rw [(hQ m).U] at hx₁
    obtain ⟨y, hy, rfl⟩ := hx₁
    have hy' : y ∈ (K (e₁ m)).U := by
      rw [← hαU m]
      exact ⟨_, hx₂, (α m).apply_symm_apply y⟩
    obtain ⟨h₁, h₂⟩ := hIntersection _ (he₁m m).1 ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · rw [(hQ m).V]
      exact mem_image_of_mem _ h₁
    · rw [← hαV m] at h₂
      obtain ⟨z, hz, rfl⟩ := h₂
      rwa [(α m).symm_apply_apply]
  let g : ℕ → Set S := fun m ↦ Kc.V ∩ (Q m).Γ.V
  obtain ⟨W₀, -, hinf₂⟩ := exists_infinite_fiber (A := univ) infinite_univ
    Kc.finite_V.finite_subsets g
    (fun m _ ↦ inter_subset_left)
  set e₂ := Nat.nth (· ∈ univ ∩ g ⁻¹' {W₀})
  have he₂s : StrictMono e₂ := Nat.nth_strictMono hinf₂
  have he₂m : ∀ m, g (e₂ m) = W₀ := fun m ↦ (Nat.nth_mem_of_infinite hinf₂ m).2
  let R : ℕ → ColouredPainting χ := fun m ↦ Q (e₂ m)
  have hRV : ∀ i j, ∀ v ∈ Kc.V, v ∈ (R i).Γ.V ↔ v ∈ (R j).Γ.V := by
    intro i j v hv
    have h₁ : g (e₂ i) = g (e₂ j) := (he₂m i).trans (he₂m j).symm
    constructor
    · intro h
      exact (h₁ ▸ (⟨hv, h⟩ : v ∈ g (e₂ i)) : v ∈ g (e₂ j)).2
    · intro h
      exact (h₁.symm ▸ (⟨hv, h⟩ : v ∈ g (e₂ j)) : v ∈ g (e₂ i)).2
  exact ⟨e₁, e₂, α, hα, he₁s, he₂s, fun m ↦ (he₁m m).1, hαU, hαV, hinter, hRV⟩

/-- **Graph Minors XIX, (5.4)** (page 337), from (5.2) and the facts about orientations and
cappings. -/
theorem theorem_5_4_proof
     : Theorem54Statement.{w} := by
  classical
  intro S Shat _ _ _ _ β _ cap χ hS3 P hbad hsim rad n
  have hS := χ.isSurface
  have := χ.connected
  by_contra hno
  push Not at hno
  have hA : {i | Painting.dist (rad i) ≤ n}.Infinite :=
    Set.infinite_of_forall_exists_gt fun a ↦ by
      obtain ⟨i, hi, hd⟩ := hno (a + 1)
      exact ⟨i, hd, by omega⟩
  have hK : ∀ i ∈ {i | Painting.dist (rad i) ≤ n}, ∃ K, IsCrossLine χ.Φ (P i).Γ (4 * n + 3) K :=
    fun i hi ↦ exists_crossLine hS (rad i) (P i).fits hi
  have : Nonempty (Drawing S) := by
    obtain ⟨i, hi⟩ := hA.nonempty
    obtain ⟨K, -⟩ := hK i hi
    exact ⟨K⟩
  choose! K hK using hK
  obtain ⟨e₁, e₂, α, hα, he₁s, he₂s, he₁m, _, _, hinter, hRV⟩ :=
    exists_aligned_feature_subsequence P K hA (4 * n + 3)
      (fun i hi ↦ (hK i hi).feature) (fun i hi ↦ (hK i hi).size) (fun i hi ↦ (hK i hi).inter)
  let Kc := K (e₁ 0)
  have hcross := hK _ (he₁m 0)
  let Q : ℕ → ColouredPainting χ := fun m ↦ (P (e₁ m)).image (α m).symm (hα m).symm
  have hQ : ∀ m, IsColouredImage (α m).symm (P (e₁ m)) (Q m) := fun m ↦
    ColouredPainting.isImage_image _ _ _
  let R : ℕ → ColouredPainting χ := fun m ↦ Q (e₂ m)
  obtain ⟨s, t, hst, hbd, hl, hne⟩ := hcross.line
  obtain ⟨Y, tY, t2Y, ψ, hY, hcY, hψ, hsheet, a, b, c, h₁, h₂⟩ := exists_cross_cut hS hst hbd hl hne
  let y₀ : Y := Classical.arbitrary Y
  have hF := hcross.feature
  let ψ₁ : connectedComponent y₀ → S := fun x ↦ ψ x.1
  have : Nonempty (connectedComponent y₀) := ⟨⟨y₀, mem_connectedComponent⟩⟩
  have D : ∀ m, FrameData χ.Φ (R m).Γ Kc ψ₁ := fun m ↦
    frameData_of_cut hS (R m).fits (hinter (e₂ m)) hcross.lines hY hψ hsheet y₀
  have hsV : ∀ m, s ∈ (R m).Γ.V := fun m ↦ by
    have : s ∈ Kc.U ∩ bd S := hbd ▸ mem_insert _ _
    exact (hinter (e₂ m) ⟨(R m).Γ.bd_subset this.2, this.1⟩).1
  have htV : ∀ m, t ∈ (R m).Γ.V := fun m ↦ by
    have : t ∈ Kc.U ∩ bd S := hbd ▸ mem_insert_of_mem _ rfl
    exact (hinter (e₂ m) ⟨(R m).Γ.bd_subset this.2, this.1⟩).1
  have hAn : ∀ m, IsAnchored (R m).Γ Kc := fun m ↦ isAnchored_of_line hl (hsV m) (htV m)
  obtain ⟨flip, hflip⟩ := (D 0).exists_flip
  let a₀ : β := Classical.arbitrary β
  let χ' := fragScheme χ a₀ (D 0) hF flip
  let P' : ℕ → ColouredPainting χ' := fun m ↦ fragPainting (a₀ := a₀) (D 0) hF flip (R m) (D m)
    (hAn m)
  have hfrag := (D 0).pull.frag
  obtain ⟨Shat₁, t₁, hc₁, hh, hlt⟩ := capped_fragment cap hfrag.isSurface hfrag.connected h₁ h₂
  have hnb : ¬ χ'.IsOrientedlyBad := hS3 _ Shat₁ χ' hc₁ hh rfl rfl hlt
  have hsimP : IsSimilarlyOriented χ' P' := by
    rcases hsim with h | ⟨ω, hω⟩
    · refine Or.inl fun hO ↦ h ?_
      obtain ⟨e₃⟩ := h₁
      obtain ⟨e₄⟩ := h₂
      exact isOrientable_of_homeo e₃ (modelOrientation a b c (isOrientable_of_homeo e₄.symm
        (isOrientable_of_homeo (homeoComponent y₀) hO)))
    · obtain ⟨ω₁, hω₁⟩ := GraphMinor.GM19.fragmentOrientation S _ Kc ψ₁ hS inferInstance hfrag ω
      refine Or.inr ⟨ω₁, fun m e₁' he₁' h3 a' b' c' hl' ↦ ?_⟩
      have hpos : IsPositive ω (R m).Γ := isPositive_image ((hα _).symm.preserves_orientation ω)
        (hQ _) (hω _)
      have hEp : e₁' ∈ ((D m).paint flip).E := he₁'
      have hint : Painting.IsInternal e₁' := by
        refine disjoint_left.mpr fun x hx hxb ↦ ?_
        have := (((D m).paint flip).border_edge e₁' hEp ⟨x, hx, hxb⟩).1
        omega
      obtain ⟨e, he, hb', hne', rfl⟩ := (D m).exists_lift_of_internal flip hEp hint
      have hsub := (D m).pull.subset_R he hb' hne'
      have hmap := (D m).map_march_lift (flip := flip) he hb' hne'
      have hlist : ((D m).paint flip).γ (ψ₁ ⁻¹' e) = [a', b', c'] := hl'
      rw [hlist] at hmap
      obtain ⟨hdisc, htil⟩ := ((D m).paint flip).tilde_subset_discBd hEp h3
      have hn := ((D m).paint flip).γ_nodup _ hEp
      have hset := ((D m).paint flip).γ_set _ hEp
      rw [hlist] at hn hset
      have hmem : ∀ x ∈ [a', b', c'], x ∈ discBd (closure (ψ₁ ⁻¹' e)) := fun x hx ↦ htil (hset ▸ hx)
      have hsur : ψ₁ '' (ψ₁ ⁻¹' e) = e := image_preimage_eq_of_subset (hsub.trans
        (image_subset_range _ _))
      have hcl : ψ₁ '' closure (ψ₁ ⁻¹' e) = closure e := by
        rw [← hfrag.isClosedMap.closure_image_eq_of_continuous hfrag.continuous_ψ, hsur]
      refine (hω₁ _ hdisc ((D m).pull.injOn_closure he hsub) a' b' c' (hmem _ (by simp)) (hmem _
        (by simp))
        (hmem _ (by simp)) (by simp at hn; tauto) (by simp at hn; tauto)
          (by simp at hn; tauto)).mpr ?_
      rw [hcl]
      have h3e : (tilde e).ncard = 3 := by
        rw [← (D m).pull.ncard_tilde he hsub]
        exact h3
      exact hpos e he h3e _ _ _ hmap.symm
  have hnotbad : ¬ IsBadSequence χ' P' := fun hb' ↦ hnb ⟨P', hb', hsimP⟩
  unfold IsBadSequence at hnotbad
  push Not at hnotbad
  obtain ⟨i, j, hij, σv, σe, hσ⟩ := hnotbad
  have hC : IsCover Kc (fun _ : Unit ↦ ψ₁) := by
    refine ⟨fun x ↦ ?_, fun _ _ x y hxy hoff ↦ ?_⟩
    · obtain ⟨y, rfl⟩ := hψ.2.1 x
      exact ⟨(), ⟨y, by rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial⟩, rfl⟩
    · have : x.1 = y.1 := hψ.2.2.1 hoff (fun hK' ↦ hoff (hxy ▸ hK')) hxy
      exact congrArg (Sigma.mk ()) (Subtype.ext this)
  have hglue := glue_coloured (ι := Unit) (Y := fun _ ↦ connectedComponent y₀) (ψ := fun _ ↦ ψ₁)
    (Γ₀ := fun _ ↦ (R 0).Γ) (D₀ := fun _ ↦ D 0) (hF := hF) (flip := fun _ ↦ flip) (P₁ := R i) (P₂
      := R j)
    (D₁ := fun _ ↦ D i) (D₂ := fun _ ↦ D j) (hA₁ := hAn i) (hA₂ := hAn j) (σv := fun _ ↦ σv) (σe
      := fun _ ↦ σe)
    (a₀ := a₀) (fun _ ↦ hσ) (fun _ ↦ hflip) (hRV i j) hC
  have hfin := IsColouredLinearInflation.image hS (hα _).symm.symm (hα _).symm.symm (hQ
    (e₂ i)).symm (hQ (e₂ j)).symm hglue
  exact hbad _ _ (he₁s (he₂s hij)) ⟨_, _, hfin⟩

end GraphMinor.GM19

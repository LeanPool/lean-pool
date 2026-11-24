/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5q

import LeanPool.GraphMinor.GM19.FeatureCount

import LeanPool.GraphMinor.GM19.FragmentSimpler

import LeanPool.GraphMinor.GM19.Section5oProved
import LeanPool.GraphMinor.GM19.UniverseLift2

/-!
# Graph Minors XIX, (5.5)
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u w


/-- A sequence of steps along infinite sets. -/
theorem exists_chain (P : ℕ → ℕ → Prop) {A₀ : Set ℕ} (hA₀ : A₀.Infinite)
    (h : ∀ A ⊆ A₀, A.Infinite → ∃ a ∈ A, {b ∈ A | P a b}.Infinite) :
    ∃ e : ℕ → ℕ, (∀ n, e n ∈ A₀) ∧ ∀ n m, n < m → P (e n) (e m) := by
  classical
  let T := {A : Set ℕ // A ⊆ A₀ ∧ A.Infinite}
  have hstep : ∀ A : T, ∃ a ∈ A.1, {b ∈ A.1 | P a b}.Infinite := fun A ↦ h _ A.2.1 A.2.2
  choose f hf hf' using hstep
  let next : T → T := fun A ↦ ⟨{b ∈ A.1 | P (f A) b}, fun x hx ↦ A.2.1 hx.1, hf' A⟩
  let B : ℕ → T := fun n ↦ next^[n] ⟨A₀, Subset.rfl, hA₀⟩
  have hB : ∀ n, B (n + 1) = next (B n) := fun n ↦ Function.iterate_succ_apply' _ _ _
  have hanti : ∀ n k, (B (n + k)).1 ⊆ (B n).1 := by
    intro n k
    induction k with
    | zero => exact Subset.rfl
    | succ k ih =>
      rw [← add_assoc, hB]
      exact Subset.trans (fun x hx ↦ hx.1 : (next (B (n + k))).1 ⊆ (B (n + k)).1) ih
  refine ⟨fun n ↦ f (B n), fun n ↦ (B n).2.1 (hf _), fun n m hnm ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
  have h₁ : f (B (n + k + 1)) ∈ (B (n + 1 + k)).1 := by
    have : n + k + 1 = n + 1 + k := by omega
    rw [this]
    exact hf _
  have h₂ := hanti (n + 1) k h₁
  rw [hB] at h₂
  exact h₂.2

/-- A relation that holds on a pair of every subsequence holds on all pairs of a subsequence. -/
theorem exists_homogeneous (R : ℕ → ℕ → Prop) (h : ∀ e : ℕ → ℕ, StrictMono e → ∃ i j, i < j ∧ R
  (e i) (e j)) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i j, i < j → R (e i) (e j) := by
  by_cases hgood : ∀ A : Set ℕ, A ⊆ univ → A.Infinite → ∃ a ∈ A, {b ∈ A | a < b ∧ R a b}.Infinite
  · obtain ⟨e, -, he⟩ := exists_chain (fun a b ↦ a < b ∧ R a b) (A₀ := univ) infinite_univ hgood
    exact ⟨e, strictMono_nat_of_lt_succ fun n ↦ (he n _ (by omega)).1, fun i j hij ↦ (he i j hij).2⟩
  · exfalso
    push Not at hgood
    obtain ⟨A, -, hA, hfin⟩ := hgood
    obtain ⟨e, -, he⟩ := exists_chain (fun a b ↦ a < b ∧ ¬ R a b) hA fun B hB hBi ↦ by
      obtain ⟨a, ha⟩ := hBi.nonempty
      refine ⟨a, ha, ?_⟩
      have hf₁ : {b ∈ A | a < b ∧ R a b}.Finite := hfin a (hB ha)
      refine ((hBi.sdiff ((finite_Iic a).union hf₁))).mono ?_
      rintro b ⟨hb, hn⟩
      simp only [mem_union, mem_Iic, mem_ofPred_eq, not_or, not_le, not_and] at hn
      exact ⟨hb, hn.1, fun hr ↦ hn.2 (hB hb) hn.1 hr⟩
    obtain ⟨i, j, hij, hr⟩ := h e (strictMono_nat_of_lt_succ fun n ↦ (he n _ (by omega)).1)
    exact (he i j hij).2 hr

/-- Finitely many such relations hold together on a pair. -/
theorem exists_common_pair {ι : Type*} [Finite ι] (R : ι → ℕ → ℕ → Prop)
    (h : ∀ t, ∀ e : ℕ → ℕ, StrictMono e → ∃ i j, i < j ∧ R t (e i) (e j)) : ∃ i j, i < j
      ∧ ∀ t, R t i j := by
  classical
  cases nonempty_fintype ι
  have key : ∀ T : Finset ι, ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ t ∈ T, ∀ i j, i < j → R t (e i) (e j)
    := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | insert t T _ ih =>
      obtain ⟨e, he, heR⟩ := ih
      obtain ⟨e', he', hR⟩ := exists_homogeneous (fun i j ↦ R t (e i) (e j)) fun e₁ h₁ ↦ h t _
        (he.comp h₁)
      refine ⟨e ∘ e', he.comp he', fun s hs i j hij ↦ ?_⟩
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hR i j hij
      · exact heR s hs _ _ (he' hij)
  obtain ⟨e, he, hR⟩ := key Finset.univ
  exact ⟨e 0, e 1, he zero_lt_one, fun t ↦ hR t (Finset.mem_univ t) 0 1 zero_lt_one⟩

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]

omit [T2Space Shat] in
omit [T2Space S] in
/-- A feature of the two forms, with two vertices of `Γ`, is anchored in `Γ`. -/
theorem isAnchored_of_form {cap : IsCappedSurface S Shat} {Γ : Painting S} {K : Drawing S} {F : Set
  Shat}
    (hf : IsCutFormOf cap K F) (hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V) (htwo : ∃ a ∈ K.U ∩ Γ.V, ∃ b ∈ K.U
      ∩ Γ.V, a ≠ b) : IsAnchored Γ K := by
  obtain ⟨-, hO, -⟩ | ⟨s, t, Θ, -, -, -, -, hbd, hl, -⟩ := hf
  · obtain ⟨a, ha, b, hb, hab⟩ := htwo
    intro u x hx hne
    by_cases hu : u ∈ K.U
    · refine ⟨K.U \ {u}, Subset.rfl, ⟨hx, hne⟩, (isPathConnected_oArc_diff hO
        hu).isConnected.isPreconnected, ?_⟩
      by_cases hau : a = u
      · exact ⟨b, ⟨hb.1, fun h ↦ hab (hau.trans h.symm)⟩, hb.2⟩
      · exact ⟨a, ⟨ha.1, hau⟩, ha.2⟩
    · refine ⟨K.U, fun z hz ↦ ⟨hz, fun h ↦ hu (h ▸ hz)⟩, hx, hO.isPreconnected, ⟨a, ha⟩⟩
  · have hm : ∀ {z}, z ∈ K.U ∩ bd S → z ∈ Γ.V := fun hz ↦ (hinter ⟨Γ.bd_subset hz.2, hz.1⟩).1
    exact isAnchored_of_line hl (hm (hbd ▸ mem_insert _ _)) (hm (hbd ▸ mem_insert_of_mem _ rfl))

/-- **Graph Minors XIX, (5.5)** (page 338), in surface universe `0`. -/
private theorem theorem_5_5_zero :
    Theorem55Statement.{0, w} := by
  classical
  intro S Shat _ _ _ _ β _ cap χ hS1 hS3 P hbad hsim rad n
  have hS := χ.isSurface
  have := χ.connected
  have : ConnectedSpace Shat := cap.connected
  have : Nonempty S :=
    inferInstance
  obtain ⟨h₀, hh₀⟩ := GraphMinor.GM19.theorem_5_4_proof.{w} S Shat β cap χ hS3 P hbad hsim rad
    (n + 1)
  by_contra hno
  push Not at hno
  set A : Set ℕ := {i | ((n + 1 : ℕ) : ℕ∞) < Painting.dist (rad i) ∧ Painting.rep (rad i)
    ≤ n} with hAdef
  have hA : A.Infinite :=
    Set.infinite_of_forall_exists_gt fun a ↦ by
      obtain ⟨i, hi, hd⟩ := hno (max h₀ (a +
        1))
      refine ⟨i, ⟨hh₀ i ((le_max_left _ _).trans hi), hd⟩, ?_⟩
      have := le_max_right h₀ (a + 1)
      omega
  have hK : ∀ i ∈ A, ∃ K, IsCutShape cap χ.Φ (P i).Γ (4 * n + 3) K :=
    fun i hi ↦ exists_shape hS (rad i) (P i).fits.internally_three_connected (P i).fits hi.1 hi.2
  have : Nonempty (Drawing S) := by
    obtain ⟨i, hi⟩ := hA.nonempty
    obtain ⟨K, -⟩ := hK i hi
    exact ⟨K⟩
  choose! K hK using hK
  obtain ⟨𝓕, hf, h𝓕⟩ := GraphMinor.GM19.theorem_5_2_proof S hS χ.connected χ.Φ (4 * n + 3)
  have h𝓕' : ∀ i ∈ A, ∃ K₀ ∈ 𝓕, FeatureEquiv χ.Φ K₀ (K i) :=
    fun i hi ↦ h𝓕 _ (hK i hi).feature (hK i hi).size
  choose! G hG hG' using h𝓕'
  obtain ⟨K₀, -, hinf⟩ := exists_infinite_fiber hA hf G hG
  set e₁ := Nat.nth (· ∈ A ∩ G ⁻¹' {K₀}) with he₁
  have he₁s : StrictMono e₁ := Nat.nth_strictMono hinf
  have he₁m : ∀ m, e₁ m ∈ A ∧ G (e₁ m) = K₀ := fun m ↦ Nat.nth_mem_of_infinite hinf m
  set Kc := K (e₁ 0) with hKc
  have hcross := hK _ (he₁m 0).1
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
  let Q : ℕ → ColouredPainting χ := fun m ↦ (P (e₁ m)).image (α m).symm
    (hα m).symm
  have hQ : ∀ m, IsColouredImage (α m).symm (P (e₁ m)) (Q m) := fun m ↦
    ColouredPainting.isImage_image _ _ _
  have hinter : ∀ m, (Q m).Γ.U ∩ Kc.U ⊆ (Q m).Γ.V ∩ Kc.V := by
    rintro m x ⟨hx₁, hx₂⟩
    rw [(hQ m).U] at hx₁
    obtain ⟨y, hy, rfl⟩ := hx₁
    have hy' : y ∈ (K (e₁ m)).U := by
      rw [← hαU m]
      exact ⟨_, hx₂, (α m).apply_symm_apply y⟩
    obtain ⟨h₁, h₂⟩ := (hK _ (he₁m m).1).inter ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · rw [(hQ m).V]
      exact mem_image_of_mem _ h₁
    · rw [← hαV m] at h₂
      obtain ⟨z, hz, rfl⟩ := h₂
      rwa [(α m).symm_apply_apply]
  have htwo : ∀ m, ∃ a ∈ Kc.U ∩ (Q m).Γ.V, ∃ b ∈ Kc.U ∩ (Q m).Γ.V, a ≠ b := by
    intro m
    obtain ⟨a, ha, b, hb, hab⟩ := (hK _ (he₁m
      m).1).two
    have key : ∀ {a}, a ∈ (K (e₁ m)).U ∩ (P (e₁ m)).Γ.V → (α m).symm a ∈ Kc.U ∩ (Q m).Γ.V
      := fun {a} ha ↦ by
      refine ⟨?_, ?_⟩
      · have := ha.1
        rw [← hαU m] at this
        obtain ⟨z, hz, rfl⟩ := this
        rwa [(α m).symm_apply_apply]
      · rw [(hQ m).V]
        exact mem_image_of_mem _ ha.2
    exact ⟨_, key ha, _, key hb, fun h ↦ hab ((α m).symm.injective h)⟩
  let g : ℕ → Set S := fun m ↦ Kc.V ∩ (Q
    m).Γ.V
  obtain ⟨W₀, -, hinf₂⟩ := exists_infinite_fiber (A := univ) infinite_univ
    Kc.finite_V.finite_subsets g
    (fun m _ ↦ inter_subset_left)
  set e₂ := Nat.nth (· ∈ univ ∩ g ⁻¹' {W₀}) with he₂
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
  have hF := hcross.feature
  have hKne : Kc.V ⊆ ⋃ e ∈ arcComponentsIn (Kc.U \ Kc.V), closure e := fun v hv ↦ by
    obtain ⟨e, he, hve⟩ := hF.no_isolated_vertices v hv
    exact mem_biUnion he hve.1
  have hKbd : Kc.U ∩ bd S ⊆ Kc.V := by
    rintro x ⟨hx, hxb⟩
    by_contra hxV
    have hm : x ∈ Kc.U \ Kc.V := ⟨hx,
      hxV⟩
    exact disjoint_left.1 (hF.no_border_edges _ (GM20.mem_arcComponentsIn_pathComponentIn hm))
      (mem_pathComponentIn_self hm) hxb
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hsheet, hsimple⟩ := GraphMinor.GM19.cutSimpler S Shat cap Kc hS
    hcross.lines hKne hKbd hcross.form
  have : LocallyConnectedSpace Y := hY.locallyConnected
  have : CompactSpace Y := hY.1
  have : Finite (ConnectedComponents Y) := by
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : Y ↦ connectedComponent x)
      (fun x ↦ isOpen_connectedComponent) (fun x _ ↦ mem_iUnion.mpr ⟨x,
        mem_connectedComponent⟩)
    refine Finite.of_surjective (fun t : T ↦ (ConnectedComponents.mk t.1 : ConnectedComponents Y))
      fun c ↦ ?_
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp (hT (mem_univ z))
    exact ⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe'.2 hzt |>.symm⟩
  let y : ConnectedComponents Y → Y := fun c ↦ (ConnectedComponents.surjective_coe c).choose
  have hy : ∀ c, (ConnectedComponents.mk (y c) : ConnectedComponents Y) = c :=
    fun c ↦ (ConnectedComponents.surjective_coe c).choose_spec
  let Z : ConnectedComponents Y → Type := fun c ↦ connectedComponent (y c)
  let ψ₁ : ∀ c, Z c → S := fun c x ↦ ψ x.1
  have : ∀ c, Nonempty (Z c) := fun c ↦ ⟨⟨y c, mem_connectedComponent⟩⟩
  have D : ∀ c m, FrameData χ.Φ (R m).Γ Kc (ψ₁ c) := fun c m ↦
    frameData_of_cut hS (R m).fits (hinter (e₂ m)) hcross.lines hY hψ hsheet (y c)
  have hAn : ∀ m, IsAnchored (R m).Γ Kc := fun m ↦ by
    obtain ⟨F₀, -, -, hform⟩ := hcross.form
    exact isAnchored_of_form hform (hinter (e₂ m)) (htwo (e₂
      m))
  have hfl : ∀ c, ∃ flip, IsPaperFlip χ.Φ Kc (ψ₁ c) (D c 0).pull.frag.isSurface flip := fun c ↦
    (D c 0).exists_flip
  choose flip hflip using hfl
  let a₀ : β := Classical.arbitrary β
  let χ' : ∀ c, ColourScheme (Z c) β := fun c ↦ fragScheme χ a₀ (D c 0) hF (flip c)
  let P' : ∀ c, ℕ → ColouredPainting (χ' c) := fun c m ↦
    fragPainting (a₀ := a₀) (D c 0) hF (flip c) (R m) (D c m) (hAn m)
  have hgood : ∀ c, ∀ e : ℕ → ℕ, StrictMono e → ∃ i j, i < j ∧ ∃ σv σe,
      IsColouredLinearInflation (χ' c) (P' c (e i)) (P' c (e j)) σv σe := by
    intro c e he
    have hfrag := (D c 0).pull.frag
    obtain ⟨Shat₁, t₁, ⟨cap₁⟩⟩ := exists_cappedSurface _ _ hfrag.isSurface hfrag.connected rfl
    have hnb := hS1 _ Shat₁ β (χ' c) ⟨cap₁⟩ (hsimple (y c) Shat₁ cap₁)
    unfold ColourScheme.IsBad at hnb
    push Not at hnb
    have := hnb fun m ↦ P' c (e m)
    unfold IsBadSequence at this
    push Not at this
    obtain ⟨i, j, hij, σv, σe, hσ⟩ := this
    exact ⟨i, j, hij, σv, σe, hσ⟩
  obtain ⟨i, j, hij, hall⟩ := exists_common_pair (fun c i j ↦ ∃ σv σe,
    IsColouredLinearInflation (χ' c) (P' c i) (P' c j) σv σe) hgood
  choose σv σe hσ using hall
  have hC : IsCover Kc ψ₁ := by
    refine ⟨fun x ↦ ?_, fun c c' x x' hxy hoff ↦ ?_⟩
    · obtain ⟨z, rfl⟩ := hψ.2.1 x
      refine ⟨(z : ConnectedComponents Y), ⟨z, ?_⟩, rfl⟩
      exact ConnectedComponents.coe_eq_coe'.1 (hy _).symm |> fun h ↦ h
    · have heq : x.1 = x'.1 := hψ.2.2.1 hoff (fun hK' ↦ hoff (hxy ▸ hK')) hxy
      have hc : c = c' := by
        have h₁ : (ConnectedComponents.mk x.1 : ConnectedComponents Y) = c :=
          (ConnectedComponents.coe_eq_coe'.2 x.2).trans (hy c)
        have h₂ : (ConnectedComponents.mk x'.1 : ConnectedComponents Y) = c' :=
          (ConnectedComponents.coe_eq_coe'.2 x'.2).trans (hy c')
        rw [← h₁, ← h₂, heq]
      subst hc
      exact congrArg (Sigma.mk c) (Subtype.ext heq)
  have hglue := glue_coloured (ι := ConnectedComponents Y) (Y := Z) (ψ := ψ₁)
    (Γ₀ := fun _ ↦ (R 0).Γ) (D₀ := fun c ↦ D c 0) (hF := hF) (flip := flip) (P₁ := R i) (P₂ := R j)
    (D₁ := fun c ↦ D c i) (D₂ := fun c ↦ D c j) (hA₁ := hAn i) (hA₂ := hAn j) (σv := σv) (σe := σe)
    (a₀ := a₀) hσ hflip (hRV i j)
      hC
  have hfin := IsColouredLinearInflation.image hS (hα _).symm.symm (hα _).symm.symm (hQ
    (e₂ i)).symm (hQ (e₂ j)).symm hglue
  exact hbad _ _ (he₁s (he₂s hij)) ⟨_, _, hfin⟩

/-- **Graph Minors XIX, (5.5)** (page 338), from (5.2), (5.4) and the fact that each fragment is
simpler. -/
theorem theorem_5_5_proof : Theorem55Statement.{u, w} :=
  theorem_5_5_lift theorem_5_5_zero

end GraphMinor.GM19

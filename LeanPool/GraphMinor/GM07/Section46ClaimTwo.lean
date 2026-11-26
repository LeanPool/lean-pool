/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.GM07.Section46DiscApproach

/-!
# Claim (2) of VII (4.6)

Page 229: "Since $U(J) \cap S = \emptyset$, it follows that $\phi$ maps $R_1$ and its boundary $C_1
\cup F$ homeomorphically onto
$S$, $A$, respectively." Here `R₁` is a closed disc in `Δ`, and `S` is the inside of a closed disc
`Z` of `Σ` with boundary `A`. What we
know at this point is that `φ` is one to one on the inside of `R₁` (the net identifies no inner
point of `Δ`), that it maps the inside of
`R₁` into the inside of `Z`, and that it maps the boundary of `R₁` into the boundary of `Z`.

We prove the claim for any continuous map `φ` with finite fibres between surfaces with these three
properties
(`injOn_of_disc_to_disc`).
1. The image of the inside of `R₁` is open, by invariance of domain, and closed in the inside of
  `Z`, since the boundary goes to the
   boundary. The inside of `Z` is connected, so the image is all of it.
2. Two points `x ≠ y` of the boundary of `R₁` with the same image `p` are impossible. Near `p`, the
  inside of `Z` meets a small open set
   `W` in a connected set. Small disjoint neighbourhoods of the finitely many points over `p` split
   the part of the inside of `R₁` over
   `W` in two nonempty open parts, one near `x`, the other near the other points, and their images
   split the connected set.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface

universe u v

variable {D : Type u} {S : Type v} [TopologicalSpace D] [TopologicalSpace S]

/-- The image of an open part of the inside of a closed disc, under a map that is continuous and one
to one there, is open. -/
theorem isOpen_image_of_subset_discInt (hman : ∀ x : S, IsManifoldPoint x) {R : Set D}
  (hR : IsClosedDisc R) {φ : D → S}
    (hφ : Continuous φ) (hinj : InjOn φ (discInt R)) {V : Set D} (hV : IsOpen V)
      (hVR : V ⊆ discInt R) : IsOpen (φ '' V) := by
  obtain ⟨h, g, c⟩ := hR.exists_isChart
  have hint : discInt R = g '' ball 0 1 := c.discInt_eq
  set M : Set ℂ := ball 0 1 ∩ g ⁻¹' V with hM
  have hgc : ContinuousOn g (ball (0 : ℂ) 1) := c.gc.mono ball_subset_closedBall
  have hMo : IsOpen M := hgc.isOpen_inter_preimage isOpen_ball hV
  have hgM : g '' M = V := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    · intro x hx
      have hx' := hVR hx
      rw [hint] at hx'
      obtain ⟨z, hz, rfl⟩ := hx'
      exact ⟨z, ⟨hz, hx⟩, rfl⟩
  have hginj : InjOn g (ball (0 : ℂ) 1) := c.injOn.mono ball_subset_closedBall
  rw [← hgM, image_image]
  refine isOpen_image_of_manifold hMo (hφ.comp_continuousOn (hgc.mono inter_subset_left)) ?_ fun _
    _ => hman _
  intro z hz w hw he
  have hz' : g z ∈ discInt R := hint ▸ mem_image_of_mem g hz.1
  have hw' : g w ∈ discInt R := hint ▸ mem_image_of_mem g hw.1
  exact hginj hz.1 hw.1 (hinj hz' hw' he)

/-- Near a point of a closed disc, inside any open set, there is an open set that meets the inside
of the disc in a connected set. -/
theorem exists_nhds_discInt_preconnected {Z : Set S} (hZ : IsClosedDisc Z) {p : S}
  (hp : p ∈ Z) {O : Set S} (hO : IsOpen O)
    (hpO : p ∈ O) : ∃ W : Set S, IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧ IsPreconnected (W ∩ discInt Z) := by
  obtain ⟨e⟩ := hZ
  obtain ⟨Ws, hWs, hpWs, hWsO, hconn⟩ := closed_disc_connected_approach e ⟨p, hp⟩
    (Subtype.val ⁻¹' O) (hO.preimage continuous_subtype_val) hpO
  obtain ⟨O', hO', hWs'⟩ := isOpen_induced_iff.mp hWs
  refine ⟨O' ∩ O, hO'.inter hO, ⟨?_, hpO⟩, inter_subset_right, ?_⟩
  · have : (⟨p, hp⟩ : Z) ∈ Subtype.val ⁻¹' O' := hWs' ▸ hpWs
    exact this
  have heq : (O' ∩ O) ∩ discInt Z = Subtype.val '' (Ws ∩ (bd Z)ᶜ) := by
    apply Subset.antisymm
    · rintro z ⟨⟨hz1, -⟩, hzZ, hzb⟩
      refine ⟨⟨z, hzZ⟩, ⟨?_, fun hb => hzb ⟨_, hb, rfl⟩⟩, rfl⟩
      rw [← hWs']
      exact hz1
    · rintro _ ⟨w, ⟨hw, hwb⟩, rfl⟩
      refine ⟨⟨?_, hWsO hw⟩, w.2, ?_⟩
      · have : w ∈ Subtype.val ⁻¹' O' := hWs' ▸ hw
        exact this
      · rintro ⟨w', hw', he⟩
        exact hwb (Subtype.ext he ▸ hw')
  rw [heq]
  exact hconn.image _ continuous_subtype_val.continuousOn

/-- **Claim (2) of VII (4.6)**, page 229, in general form. A continuous map with finite fibres
between surfaces that is one to one on the
inside of a closed disc `R`, maps it into the inside of a closed disc `Z`, and maps the boundary of
`R` into the boundary of `Z`, maps `R`
one to one onto `Z`, and the boundary of `R` onto the boundary of `Z`. -/
theorem injOn_of_disc_to_disc [T2Space D] [T2Space S] (hmanD : ∀ x : D, IsManifoldPoint x)
  (hman : ∀ x : S, IsManifoldPoint x)
    {φ : D → S} (hφ : Continuous φ) (hfin : ∀ p : S, (φ ⁻¹' {p}).Finite) {R : Set D} {Z : Set S}
      (hR : IsClosedDisc R)
    (hZ : IsClosedDisc Z) (hinj : InjOn φ (discInt R)) (hint : φ '' discInt R ⊆ discInt Z)
      (hbd : φ '' discBd R ⊆ discBd Z) :
    InjOn φ R ∧ φ '' R = Z ∧ φ '' discBd R = discBd Z := by
  have hRi : IsOpen (discInt R) := hR.isOpen_discInt hmanD
  have hZi : IsOpen (discInt Z) := hZ.isOpen_discInt hman
  have hRc : IsCompact R := hR.isCompact
  have hsplit : ∀ x ∈ R, x ∈ discInt R ∨ x ∈ discBd R := fun x hx => by
    by_cases hb : x ∈ discBd R
    · exact .inr hb
    · exact .inl ⟨hx, hb⟩
  have hZsub : discInt Z ⊆ Z := discInt_subset Z
  have himgR : φ '' R ⊆ Z := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hsplit x hx with h | h
    · exact hZsub (hint (mem_image_of_mem φ h))
    · exact discBd_subset Z (hbd (mem_image_of_mem φ h))
  -- Step 1: the inside of `R` goes onto the inside of `Z`.
  have hopen : IsOpen (φ '' discInt R) := isOpen_image_of_subset_discInt hman hR hφ hinj hRi
    subset_rfl
  have hRne : (discInt R).Nonempty := by
    obtain ⟨h, g, c⟩ := hR.exists_isChart
    rw [c.discInt_eq]
    exact ⟨g 0, 0, by simp, rfl⟩
  have hconnZ : IsPreconnected (discInt Z) := by
    obtain ⟨h, g, c⟩ := hZ.exists_isChart
    rw [c.discInt_eq]
    exact ((convex_ball (0 : ℂ) 1).isPreconnected).image _ (c.gc.mono ball_subset_closedBall)
  have hsurj : discInt Z ⊆ φ '' discInt R := by
    refine hconnZ.subset_of_closure_inter_subset hopen ?_ ?_
    · obtain ⟨x, hx⟩ := hRne
      exact ⟨φ x, hint (mem_image_of_mem φ hx), mem_image_of_mem φ hx⟩
    · rintro z ⟨hzc, hzZ⟩
      have hcl : closure (φ '' discInt R) ⊆ φ '' R :=
        closure_minimal (image_mono (discInt_subset R)) (hRc.image hφ).isClosed
      obtain ⟨x, hx, rfl⟩ := hcl hzc
      rcases hsplit x hx with h | h
      · exact mem_image_of_mem φ h
      · exact absurd (hbd (mem_image_of_mem φ h)) hzZ.2
  -- Step 2: no two points of the boundary of `R` have the same image.
  have hbdinj : ∀ x ∈ discBd R, ∀ y ∈ discBd R, φ x = φ y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    classical
    set p := φ x with hp
    set P := φ ⁻¹' {p} with hP
    obtain ⟨O, hO, hOd⟩ := (hfin p).t2_separation
    set K : Set D := R \ ⋃ q ∈ P, O q with hK
    have hKc : IsCompact K := hRc.diff (isOpen_biUnion fun q _ => (hO q).2)
    have hpK : p ∉ φ '' K := by
      rintro ⟨k, hk, hkp⟩
      exact hk.2 (mem_biUnion (x := k) hkp (hO k).1)
    have hpZ : p ∈ Z := discBd_subset Z (hbd (mem_image_of_mem φ hx))
    obtain ⟨W, hW, hpW, hWK, hWc⟩ := exists_nhds_discInt_preconnected hZ hpZ
      (hKc.image hφ).isClosed.isOpen_compl hpK
    set Y := discInt R ∩ φ ⁻¹' W with hY
    have hYo : IsOpen Y := hRi.inter (hW.preimage hφ)
    have hYP : ∀ a ∈ Y, ∃ q ∈ P, a ∈ O q := fun a ha => by
      by_contra hn
      push Not at hn
      have haK : a ∈ K := ⟨discInt_subset R ha.1, fun h => by
        obtain ⟨q, hq, haq⟩ := mem_iUnion₂.mp h
        exact hn q hq haq⟩
      exact hWK ha.2 (mem_image_of_mem φ haK)
    have hxP : x ∈ P := rfl
    have hyP : y ∈ P := hxy.symm
    set Y₁ := Y ∩ O x with hY₁
    set Y₂ := Y ∩ ⋃ q ∈ P \ {x}, O q with hY₂
    have hY₁o : IsOpen Y₁ := hYo.inter (hO x).2
    have hY₂o : IsOpen Y₂ := hYo.inter (isOpen_biUnion fun q _ => (hO q).2)
    have ho₁ := isOpen_image_of_subset_discInt hman hR hφ hinj hY₁o (inter_subset_left.trans
      inter_subset_left)
    have ho₂ := isOpen_image_of_subset_discInt hman hR hφ hinj hY₂o (inter_subset_left.trans
      inter_subset_left)
    -- Points of the inside of `R` near `x`, and near `y`, that go into `W`.
    have hnear : ∀ q, q ∈ P → q ∈ discBd R → ∃ a ∈ Y, a ∈ O q := fun q hq hqb => by
      have hqcl : q ∈ closure (discInt R) := hR.subset_closure_discInt (discBd_subset R hqb)
      have hqW : φ q ∈ W := by
        have : φ q = p := hq
        rw [this]
        exact hpW
      obtain ⟨a, ⟨haO, haW⟩, haR⟩ := mem_closure_iff.mp hqcl _ ((hO q).2.inter
        (hW.preimage hφ)) ⟨(hO q).1, hqW⟩
      exact ⟨a, ⟨haR, haW⟩, haO⟩
    obtain ⟨a₁, ha₁Y, ha₁O⟩ := hnear x hxP hx
    obtain ⟨a₂, ha₂Y, ha₂O⟩ := hnear y hyP hy
    have hcov : W ∩ discInt Z ⊆ φ '' Y₁ ∪ φ '' Y₂ := by
      rintro z ⟨hzW, hzZ⟩
      obtain ⟨a, ha, rfl⟩ := hsurj hzZ
      have haY : a ∈ Y := ⟨ha, hzW⟩
      obtain ⟨q, hq, haq⟩ := hYP a haY
      by_cases hqx : q = x
      · subst hqx
        exact .inl (mem_image_of_mem φ ⟨haY, haq⟩)
      · exact .inr (mem_image_of_mem φ ⟨haY, mem_biUnion (x := q) ⟨hq, hqx⟩ haq⟩)
    have hmem : ∀ a ∈ Y, φ a ∈ W ∩ discInt Z := fun a ha => ⟨ha.2, hint (mem_image_of_mem φ ha.1)⟩
    obtain ⟨z, hzWZ, ⟨b₁, hb₁, hz₁⟩, ⟨b₂, hb₂, hz₂⟩⟩ := hWc _ _ ho₁ ho₂ hcov ⟨φ a₁, hmem a₁ ha₁Y,
      mem_image_of_mem φ ⟨ha₁Y, ha₁O⟩⟩
      ⟨φ a₂, hmem a₂ ha₂Y, mem_image_of_mem φ ⟨ha₂Y, mem_biUnion (x := y) ⟨hyP, hne ∘ Eq.symm⟩
        ha₂O⟩⟩
    have hb : b₁ = b₂ := hinj hb₁.1.1 hb₂.1.1 (hz₁.trans hz₂.symm)
    obtain ⟨q, hq, hbq⟩ := mem_iUnion₂.mp hb₂.2
    exact disjoint_left.mp (hOd hxP hq.1 (Ne.symm hq.2)) hb₁.2 (hb ▸ hbq)
  have hinjR : InjOn φ R := by
    intro x hx y hy hxy
    rcases hsplit x hx with h₁ | h₁ <;> rcases hsplit y hy with h₂ | h₂
    · exact hinj h₁ h₂ hxy
    · exact absurd (hxy ▸ hint (mem_image_of_mem φ h₁)) fun h => h.2 (hbd (mem_image_of_mem φ h₂))
    · exact absurd (hxy.symm ▸ hint (mem_image_of_mem φ h₂)) fun h => h.2 (hbd
      (mem_image_of_mem φ h₁))
    · exact hbdinj x h₁ y h₂ hxy
  have himg : φ '' R = Z := by
    refine Subset.antisymm himgR ?_
    have h1 : Z ⊆ closure (discInt Z) := hZ.subset_closure_discInt
    have h2 : closure (discInt Z) ⊆ φ '' R :=
      closure_minimal (hsurj.trans (image_mono (discInt_subset R))) (hRc.image hφ).isClosed
    exact h1.trans h2
  refine ⟨hinjR, himg, Subset.antisymm hbd fun z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := himg.symm ▸ discBd_subset Z hz
  rcases hsplit x hx with h | h
  · exact absurd hz (hint (mem_image_of_mem φ h)).2
  · exact mem_image_of_mem φ h

end GraphMinor.GM07

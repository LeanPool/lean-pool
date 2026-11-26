/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5r
public import LeanPool.GraphMinor.GM19.Section10b

/-!
# A well-behaved set from one fragment

The proofs of (10.2), (10.4), (10.5) and (11.1) have one shape. Cut `Σ_χ` along a fixed feature `K`,
keep one fragment `Σ'`,
and let `ℒ` be a rooted location with `M(Γ, ℒ) = Γ ∩ ψ(Σ')`. If the fragment gives no bad sequence,
then the set of such places
is well-behaved, by (9.3). This is `wellBehaved_of_fragment`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]
  [Nonempty S₁] {β : Type w}


/-- The places of the proofs in Section 10. The location `ℒ` is outside the fragment `ψ(Σ')`, all
paintings meet `K` in the
same vertices, and those vertices are `l`. -/
structure IsCutPlace (χ : ColourScheme S β) (K : Drawing S) (ψ : S₁ → S) (l : List S) (m : ℕ)
  (X : Place χ) : Prop where
  inter : X.P.Γ.U ∩ K.U ⊆ X.P.Γ.V ∩ K.V
  roots : ∀ v, v ∈ l ↔ v ∈ K.V ∩ X.P.Γ.V
  roots_range : ∀ v ∈ l, v ∈ range ψ
  anchored : IsAnchored X.P.Γ K
  M_V : X.L.M.vertexSet = X.P.Γ.V ∩ range ψ
  M_E : X.L.M.edgeSet = {e ∈ X.P.Γ.E | e ⊆ range ψ}
  arms_π : ∀ A ∈ X.L.arms, ∀ v ∈ A.π, v ∈ l
  arms_card : X.L.arms.ncard ≤ m

omit [T2Space S] in
/-- A border edge lies in a side of the frame. -/
theorem Painting.exists_side {Φ : Frame S} {Γ : Painting S} (hfit : Γ.Fits Φ) {e : Set S}
  (he : e ∈ Γ.E)
    (hb : Painting.IsBorder e) : ∃ s ∈ Φ.sides, BordersSide e s := by
  have hbe := (Γ.border_edge e he hb).2
  obtain ⟨R, hR, hes⟩ := exists_arcComp_superset he.2.2.1 (F := bd S \ Φ.V)
    (fun x hx ↦ ⟨hbe hx, fun h ↦ (he.2.1 hx).2 (hfit.V_subset h)⟩)
  exact ⟨R, hR, hb, hes⟩

section

variable {χ : ColourScheme S β} {K : Drawing S} {ψ : S₁ → S} {a₀ : β} {Γ₀ : Painting S}
  {D₀ : FrameData χ.Φ Γ₀ K ψ} {hF : IsFeature χ.Φ K} {flip : Set S₁ → Bool} {P₁ P₂ :
    ColouredPainting χ}
  {D₁ : FrameData χ.Φ P₁.Γ K ψ} {D₂ : FrameData χ.Φ P₂.Γ K ψ} {hA₁ : IsAnchored P₁.Γ K} {hA₂ :
    IsAnchored P₂.Γ K}
  {σv : S₁ → Set S₁} {σe : Set S₁ → Set S₁}

/-- An edge with a lift keeps its colour under the inflation of the fragment. -/
theorem frag_le (h : IsColouredLinearInflation (fragScheme χ a₀ D₀ hF flip) (fragPainting (a₀
  := a₀) D₀ hF flip P₁ D₁ hA₁)
      (fragPainting (a₀ := a₀) D₀ hF flip P₂ D₂ hA₂) σv σe)
    (G : FragInflation D₁ D₂ hF flip σv σe) {e : Set S} (he : e ∈ P₁.Γ.E) (hne :
      (ψ ⁻¹' e).Nonempty) :
    χ.unionLE (P₁.φ e) (P₂.φ (ψ '' σe (ψ ⁻¹' e))) := by
  obtain ⟨hsur, hE₁, hE', -⟩ := G.edge_main he hne
  by_cases hb : Painting.IsBorder e
  · obtain ⟨s, hs, hbs⟩ := Painting.exists_side P₁.fits he hb
    have hbe := (P₁.Γ.border_edge e he hbs.1).2
    obtain ⟨x, hx⟩ := id hne
    obtain ⟨he₁, -⟩ := D₁.pull.preimage_border_edge he hbe hx
    obtain ⟨R, hR, hes⟩ := exists_arcComp_superset he₁.2.2.1 (F := bd S₁ \ pullFrameV χ.Φ K ψ)
      (fun x hx ↦ ⟨(he₁.2.1 hx).1, fun h ↦ (he₁.2.1 hx).2 (D₁.pullFrameV_subset h)⟩)
    obtain ⟨s', hs', hRs⟩ := D₁.exists_side_of_bd hR (hes hx) (hbe hx)
    obtain rfl : s' = s := GM11.arcComponent_eq hs' hs (hRs (mem_image_of_mem _ (hes hx)))
      (hbs.2 hx)
    have hbb : Painting.IsBorder (ψ ⁻¹' e) := ⟨x, hx, (he₁.2.1 hx).1⟩
    have := h.le_border _ hE₁ R hR ⟨hbb, hes⟩
    rw [fragScheme_ΩS ⟨x, hes hx⟩ hs hRs] at this
    change (χ.ΩS s').le (fragφ P₁ ψ a₀ (ψ ⁻¹' e)) (fragφ P₂ ψ a₀ (σe (ψ ⁻¹' e))) at this
    rw [fragφ_eq (hsur.symm ▸ he), fragφ_eq hE', hsur] at this
    have hP := P₁.border_mem e he s' hs hbs
    obtain ⟨-, -, hE'', -, -, -, -, hb₁, -⟩ := G.edge_main he hne
    obtain ⟨s'', hs'', hes'', hgs, hbg⟩ := hb₁ hbs.1
    obtain rfl : s'' = s' := GM11.arcComponent_eq hs'' hs (hes'' hx) (hbs.2 hx)
    exact Or.inr (Or.inr ⟨s'', hs, hP, P₂.border_mem _ hE'' s'' hs ⟨hbg, hgs⟩, this⟩)
  · have hi : Painting.IsInternal e := disjoint_left.mpr fun x hx hxb ↦ hb ⟨x, hx, hxb⟩
    have hsub := D₁.pull.subset_R he hb hne
    have hE₂ : ψ ⁻¹' e ∈ (D₁.paint flip).E := (D₁.mem_paint_E flip).mpr
      (Or.inr ⟨e, he, hb, hne, rfl⟩)
    have hi₁ : Painting.IsInternal (ψ ⁻¹' e) :=
      disjoint_left.mpr fun x hx hxb ↦ D₁.pull.preimage_subset_int hsub hx hxb
    have hn := D₁.pull.ncard_tilde he hsub
    obtain ⟨-, -, hE'', -, hsize, -, -, -, hb₂⟩ := G.edge_main he hne
    have hi' : Painting.IsInternal (ψ '' σe (ψ ⁻¹' e)) :=
      disjoint_left.mpr fun x hx hxb ↦ hb₂ hb ⟨x, hx, hxb⟩
    rcases P₁.Γ.edge_shape e he with h₂ | h₂
    · have := h.le_internal_2 _ hE₁ hi₁ (hn.trans h₂.1)
      change χ.Ω2.le (fragφ P₁ ψ a₀ (ψ ⁻¹' e)) (fragφ P₂ ψ a₀ (σe (ψ ⁻¹' e))) at this
      rw [fragφ_eq (hsur.symm ▸ he), fragφ_eq hE', hsur] at this
      exact Or.inl ⟨P₁.internal_2_mem e he hi h₂.1, P₂.internal_2_mem _ hE'' hi'
        (hsize.trans h₂.1), this⟩
    · have := h.le_internal_3 _ hE₁ hi₁ (hn.trans h₂.1)
      change χ.Ω3.le (fragφ P₁ ψ a₀ (ψ ⁻¹' e)) (fragφ P₂ ψ a₀ (σe (ψ ⁻¹' e))) at this
      rw [fragφ_eq (hsur.symm ▸ he), fragφ_eq hE', hsur] at this
      exact Or.inr (Or.inl ⟨P₁.internal_3_mem e he hi h₂.1, P₂.internal_3_mem _ hE'' hi'
        (hsize.trans h₂.1), this⟩)

end

/-- **One fragment gives a well-behaved set.** Let `Σ'` be a fragment of the cut along `K`. Suppose
each sequence of places of the
form `IsCutPlace` has two members with a linear inflation between the fragments. Then the set of
these places is well-behaved. -/
theorem wellBehaved_of_fragment {χ : ColourScheme S β} {K : Drawing S} (ψ : S₁ → S)
  (hF : IsFeature χ.Φ K) (l : List S) (m : ℕ)
    (a₀ : β) (hoff : ∀ x y : S₁, ψ x = ψ y → ψ x ∉ K.U → x = y)
    (hD : ∀ X : Place χ, IsCutPlace χ K ψ l m X → FrameData χ.Φ X.P.Γ K ψ) (Q : Place χ → Prop)
    (hseq : ∀ seq : ℕ → Place χ, (∀ i, Q (seq i)) → ∀ h : ∀ i, IsCutPlace χ K ψ l m (seq i), ∀ flip,
      IsPaperFlip χ.Φ K ψ (hD _ (h 0)).pull.frag.isSurface flip → ∃ i j, i < j ∧ ∃ σv σe,
        IsColouredLinearInflation (fragScheme χ a₀ (hD _ (h 0)) hF flip)
          (fragPainting (a₀ := a₀) (hD _ (h 0)) hF flip (seq i).P (hD _ (h i)) (h i).anchored)
          (fragPainting (a₀ := a₀) (hD _ (h 0)) hF flip (seq j).P (hD _ (h j))
            (h j).anchored) σv σe) :
    IsWellBehavedPlaces {X | IsCutPlace χ K ψ l m X ∧ Q X} := by
  classical
  refine theorem_9_3_proof (Pl := {X | IsCutPlace χ K ψ l m X ∧ Q X}) (fun _ ↦ l)
    (fun X hX A hA v hv ↦ hX.1.arms_π A hA v hv)
    (m := m) (n := l.length) (fun X hX ↦ hX.1.arms_card)
    (fun _ _ ↦ le_rfl) fun seq hs ↦ ?_
  have h : ∀ i, IsCutPlace χ K ψ l m (seq i) := fun i ↦ (hs i).1
  obtain ⟨flip, hflip⟩ := (hD _ (h 0)).exists_flip
  obtain ⟨i, j, hij, σv₀, σe₀, hσ⟩ := hseq seq (fun i ↦ (hs i).2) h flip hflip
  have hV : ∀ v ∈ K.V, v ∈ (seq i).P.Γ.V ↔ v ∈ (seq j).P.Γ.V := fun v hv ↦ by
    constructor
    · exact fun hi ↦ (((h j).roots v).1 (((h i).roots v).2 ⟨hv, hi⟩)).2
    · exact fun hj ↦ (((h i).roots v).1 (((h j).roots v).2 ⟨hv, hj⟩)).2
  have G₀ := fragInflation hσ hflip hV
  let Y : Unit → Type := fun _ ↦ S₁
  let ψ' : ∀ t, Y t → S := fun _ ↦ ψ
  let G : ∀ t : Unit, FragInflation (ψ := ψ' t) (hD _ (h i)) (hD _ (h j)) hF flip σv₀ σe₀
    := fun _ ↦ G₀
  have hC : IsOneOff K ψ' := ⟨fun t t' x x' hxx hK ↦ by
    cases t; cases t'
    exact congrArg (Sigma.mk ()) (hoff x x' hxx hK)⟩
  let σv : S → Set S := glueV ψ' fun _ ↦ σv₀
  let σe : Set S → Set S := glueE ψ' fun _ ↦ σe₀
  have hEe : ∀ {e}, e ∈ (seq i).L.M.edgeSet → e ∈ (seq i).P.Γ.E ∧ e ⊆ range ψ := fun {e} he ↦ by
    rw [(h i).M_E] at he
    exact he
  have hne : ∀ {e}, e ∈ (seq i).L.M.edgeSet → (ψ ⁻¹' e).Nonempty := fun {e} he ↦ by
    obtain ⟨x, hx⟩ := (hEe he).1.1
    obtain ⟨y, rfl⟩ := (hEe he).2 hx
    exact ⟨y, hx⟩
  have hV' : ∀ {v}, v ∈ (seq i).L.M.vertexSet → v ∈ (seq i).P.Γ.V ∧ v ∈ range ψ := fun {v} hv ↦ by
    rw [(h i).M_V] at hv
    exact hv
  have hσeq : ∀ {e} (he : e ∈ (seq i).L.M.edgeSet), σe e = ψ '' σe₀ (ψ ⁻¹' e) := fun {e} he ↦
    glueE_eq G hC (t := ()) (hEe he).1 (hne he)
  have hmemV : ∀ {v x}, x ∈ σv v → x ∈ range ψ := fun {v x} hx ↦ by
    obtain ⟨t, hu⟩ := mem_iUnion.mp hx
    obtain ⟨y, -, z, -, rfl⟩ := mem_iUnion₂.mp hu
    exact mem_range_self z
  have hmain := fun {e} (he : e ∈ (seq i).L.M.edgeSet) ↦ G₀.edge_main (hEe he).1 (hne he)
  refine ⟨i, j, hij, σv, σe, ⟨(seq i).L.M_le, fun e he ↦ ?_, fun e he ↦ ?_,
    fun e he e' he' heq ↦ ?_, fun v hv ↦ ?_,
    fun v hv z hz ↦ ?_, fun v hv ↦ ?_, fun v₁ hv₁ v₂ hv₂ hne' ↦ ?_, fun e he k hk hk' ↦ ?_⟩, fun v
      hv z hz ↦ ?_,
    fun e he ↦ ⟨?_, ?_⟩, rfl, fun k h₁ h₂ ↦ ?_⟩
  · rw [hσeq he]
    exact (hmain he).2.2.1
  · rw [hσeq he]
    exact (hmain he).2.2.2.2.1
  · have heq' := heq
    rw [hσeq he, hσeq he'] at heq'
    obtain ⟨hsur, hE₁, hE', hpre, -⟩ := hmain he
    obtain ⟨hsur', hE₁', -, hpre', -⟩ := hmain he'
    have hf : σe₀ (ψ ⁻¹' e) = σe₀ (ψ ⁻¹' e') := by rw [← hpre, ← hpre', heq']
    rw [← hsur, G₀.inflation.edge_injOn hE₁ hE₁' hf, hsur']
  · obtain ⟨hvΓ, y, rfl⟩ := hV' hv
    obtain ⟨x, hx⟩ := G₀.inflation.vertex_nonempty y (Or.inl hvΓ)
    exact ⟨ψ x, mem_iUnion.mpr ⟨(), mem_iUnion₂.mpr ⟨y, rfl, mem_image_of_mem _ hx⟩⟩⟩
  · obtain ⟨t, hu⟩ := mem_iUnion.mp hz
    obtain ⟨y, hy, x, hx, rfl⟩ := mem_iUnion₂.mp hu
    have hy₀ : ψ y = v := hy
    exact piece_subset G (t := ()) (hy₀ ▸ (hV' hv).1) hx
  · exact glue_connected G hC (hV' hv).1
  · exact glue_disjoint G hC (hV' hv₁).1 (hV' hv₂).1 hne'
  · obtain ⟨-, hE₁, -, -, -, hm', hm, -⟩ := hmain he
    have heq := hσeq he
    have hi₁ : k < ((hD _ (h i)).paint flip |>.γ (ψ ⁻¹' e)).length := by
      rw [← List.length_map (f := ψ), hm]
      exact hk
    have hi₂ : k < ((hD _ (h j)).paint flip |>.γ (σe₀ (ψ ⁻¹' e))).length := by
      rw [← List.length_map (f := ψ), hm', ← heq]
      exact hk'
    have hx := G₀.inflation.ends _ hE₁ k hi₁ hi₂
    have e₁ : ((seq i).P.Γ.γ e)[k] = ψ ((hD _ (h i)).paint flip |>.γ (ψ ⁻¹' e))[k] := by
      simp only [← hm, List.getElem_map]
    have e₂ : ((seq j).P.Γ.γ (σe e))[k] = ψ ((hD _ (h j)).paint flip |>.γ (σe₀ (ψ ⁻¹' e)))[k] := by
      simp only [heq, ← hm', List.getElem_map]
    rw [e₁, e₂]
    exact mem_iUnion.mpr ⟨(), mem_iUnion₂.mpr ⟨_, rfl, mem_image_of_mem _ hx⟩⟩
  · rw [(h j).M_V]
    obtain ⟨t, hu⟩ := mem_iUnion.mp hz
    obtain ⟨y, hy, x, hx, rfl⟩ := mem_iUnion₂.mp hu
    have hy₀ : ψ y = v := hy
    exact ⟨piece_subset G (t := ()) (hy₀ ▸ (hV' hv).1) hx, mem_range_self x⟩
  · rw [(h j).M_E, hσeq he]
    refine ⟨(hmain he).2.2.1, ?_⟩
    rintro _ ⟨x, -, rfl⟩
    exact mem_range_self x
  · rw [hσeq he]
    exact frag_le hσ G₀ (hEe he).1 (hne he)
  · change l[k] ∈ σv l[k]
    obtain ⟨y, hy⟩ := (h i).roots_range _ (List.getElem_mem h₁)
    have hK : l[k] ∈ K.V := (((h i).roots _).1 (List.getElem_mem h₁)).1
    have hf : y ∈ pullFrameV χ.Φ K ψ := Or.inr (hy ▸ hK)
    exact mem_iUnion.mpr ⟨(), mem_iUnion₂.mpr ⟨y, hy, y, G₀.mem_frame hf, hy⟩⟩

end GraphMinor.GM19

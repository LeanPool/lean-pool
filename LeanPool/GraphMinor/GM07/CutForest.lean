/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CutLines
public import LeanPool.GraphMinor.GM07.CutBuild
public import LeanPool.GraphMinor.GM07.TameDisc
public import LeanPool.GraphMinor.GM12.Section4FiniteLineDrawing
public import LeanPool.GraphMinor.Surface.CutIArc
public import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM19.Section6a

/-!
# Cutting along a forest

The surface `Σ'` in the proof of Graph Minors VII, (4.6) (page 225) comes from cutting along a
forest whose trees each meet `bd(Σ)` in at most one point. We grow such a forest one line at a time
(`IsGrowth`). A new line either misses
what is there, or meets it in one end. A line that misses it adds a cuff (`exists_cut_free_line`). A
line attached by one end leaves the surface as it was, since cutting along its far part adds a cuff,
and cutting along its near part joins this cuff
to the old one (`exists_cut_attached`). After the first line, the other lines lift to the cut
surface and grow there in the same way (`IsGrowth.lift`), so the cut goes by induction
(`exists_cut_growth`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM19

universe u

variable {S S₁ S₂ : Type u} [TopologicalSpace S] [TopologicalSpace S₁] [TopologicalSpace S₂]

/-- A cut does not change if `F` changes only on the boundary. -/
theorem IsCutAlongSet.congr {F F' : Set S} {θ : S₁ → S} (h : IsCutAlongSet F θ) (he : bd S ∪ F
  = bd S ∪ F') : IsCutAlongSet F' θ :=
  ⟨h.isSurface, h.quotientMap, he ▸ h.preimage_bd, h.interior_inj, h.finite_fiber⟩

/-- Nothing is cut by the identity. -/
theorem isCutAlongSet_id (hS : IsSurface S) : IsCutAlongSet (∅ : Set S) (id : S → S) :=
  ⟨hS, Topology.IsQuotientMap.id, by simp, fun _ _ _ h => h, fun x => by simp⟩

/-- A cut along `F` is one to one off `bd S ∪ F`. -/
theorem IsCutAlongSet.isCutMap {F : Set S} {θ : S₁ → S} (h : IsCutAlongSet F θ) : IsCutMap θ
  (bd S ∪ F) := by
  refine ⟨h.quotientMap.continuous, h.quotientMap.surjective, fun x hx y _ he => h.interior_inj x
    (fun hb => hx ?_) y he, h.finite_fiber, h.preimage_bd.subset⟩
  rw [← h.preimage_bd] at hb
  exact hb

/-- **Cutting along a line off the boundary** adds a cuff. -/
theorem exists_cut_free_line (hS : IsSurface S) {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) {A : Set S} {u v : S} (hA : IsLineWithEnds A u v) (hd : A ∩ bd S = ∅) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (θ : Y → S), IsCutAlongSet A θ ∧ IsCutMap θ A
      ∧ Nonempty (Y ≃ₜ SurfaceModel a b (c + 1)) ∧ θ ⁻¹' A ∈ cuffs Y := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hne : u ≠ v := hA.ne'
  have huA : u ∈ A := hA.left_mem
  have hvA : v ∈ A := hA.right_mem
  have hsubA : ({u, v} : Set S) ⊆ A := by
    rintro z (rfl | rfl)
    · exact huA
    · exact hvA
  have hAV : A ∩ {u, v} = {u, v} := inter_eq_right.mpr hsubA
  obtain ⟨H, hU, hV, hE⟩ := GM12.exists_drawing_of_finite_lines (S := S) (ι := Unit) (V := {u, v})
    (by simp) (E := {()}) (finite_singleton _) (fun _ => A) (fun _ => u) (fun _ => v)
    (fun _ _ => hA) (fun _ _ => hne) (fun _ _ => hAV) (fun _ hi _ hj hij => absurd rfl hij)
  have hHU : H.U = A := by
    rw [hU, biUnion_singleton]
    exact union_eq_right.mpr hsubA
  have he : A \ {u, v} ∈ H.E := by
    rw [hE]
    exact ⟨(), rfl, rfl⟩
  have hcl : closure (A \ {u, v}) = A :=
    Subset.antisymm (closure_minimal sdiff_subset hA.isCompact.isClosed) hA.subset_closure_diff
  have hl : (tilde (A \ {u, v})).ncard = 2 := by
    rw [GM19.tilde_eq_inter_V H he, hcl, hV, hAV, ncard_pair hne]
  have hG : H.IsProper := fun z hz => ((eq_empty_iff_forall_notMem.mp hd z) ⟨hHU ▸ hz.2, hz.1⟩).elim
  have ht1 : T1Space S := inferInstance
  obtain ⟨Y, tY, _, θ, G', hc⟩ := exists_cut hS hm H hG he hl (by rw [hcl]; exact hd)
  refine ⟨Y, tY, θ, hcl ▸ IsCutAlongSet.of_cutAlongEdge hc, ?_, hc.homeo_model, hcl ▸ hc.newCuff⟩
  refine ⟨hc.quotientMap.continuous, hc.quotientMap.surjective, fun x hx y _ hxy => ?_,
    hc.finite_fiber, fun x hx => ?_⟩
  · exact (hc.inj x y hxy).resolve_right fun h => hx h.1
  · rw [hc.bd_eq, hcl]
    exact .inr hx

/-- **Cutting along a line attached to the boundary by one end** leaves the model as it was. -/
theorem exists_cut_attached (hS : IsSurface S) {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) {A : Set S} {p q : S} (hA : IsLineWithEnds A p q) (hd : A ∩ bd S
    = {p}) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (θ : Y → S), IsCutAlongSet A θ ∧ Nonempty
      (Y ≃ₜ SurfaceModel a b c) := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨α, hα, hr, h0, h1⟩ := hA.exists_arc
  obtain ⟨t, ht0, ht1⟩ := exists_between (show (0 : unitInterval) < 1 from zero_lt_one)
  have hmA : α t ∈ A := hr ▸ mem_range_self t
  have hmp : α t ≠ p := fun h => ht0.ne' (hα.2 (h.trans h0.symm))
  have hmq : α t ≠ q := fun h => ht1.ne (hα.2 (h.trans h1.symm))
  obtain ⟨A₁, A₂, hA₁, hA₂, hun, hin⟩ := hA.split hmA hmp hmq
  have hA₂d : A₂ ∩ bd S = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    have hzp : z = p := by
      have : z ∈ A ∩ bd S := ⟨hun ▸ Or.inr hz.1, hz.2⟩
      rw [hd] at this
      exact this
    subst hzp
    have : z ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, hz.1⟩
    rw [hin] at this
    exact hmp this.symm
  obtain ⟨Y₁, tY₁, θ, hcut, hmap, ⟨e₁⟩, hN⟩ := exists_cut_free_line hS hm hA₂ hA₂d
  have hY₁ : IsSurface Y₁ := hcut.isSurface
  have : CompactSpace Y₁ := hY₁.1
  have : T2Space Y₁ := hY₁.2.1
  have hconn : ConnectedSpace Y₁ := by
    have := (modelCriterion.1 a b (c + 1)).2
    exact e₁.symm.surjective.connectedSpace e₁.symm.continuous
  obtain ⟨F, m', p', hF, hm', hp', him, hinj, hpre⟩ := exists_lift_line hmap hA₂.isCompact.isClosed
    hA₁.symm (by rw [hin])
  have hm'F : m' ∈ F := hF.left_mem
  have hp'F : p' ∈ F := hF.right_mem
  have hA₁₂ : ∀ z ∈ F, θ z ∈ A₁ := fun z hz => him ▸ mem_image_of_mem θ hz
  have hbd : F ∩ bd Y₁ = {m', p'} := by
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      rw [← hcut.preimage_bd] at hzb
      rcases hzb with h | h
      · have : θ z ∈ A ∩ bd S := ⟨hun ▸ Or.inl (hA₁₂ z hz), h⟩
        rw [hd] at this
        exact .inr (hinj hz hp'F (this.trans hp'.symm))
      · have : θ z ∈ A₁ ∩ A₂ := ⟨hA₁₂ z hz, h⟩
        rw [hin] at this
        exact .inl (hinj hz hm'F (this.trans hm'.symm))
    · rintro (rfl | rfl)
      · refine ⟨hm'F, ?_⟩
        rw [← hcut.preimage_bd]
        refine .inr ?_
        rw [hm']
        exact hA₂.left_mem
      · refine ⟨hp'F, ?_⟩
        rw [← hcut.preimage_bd]
        refine .inl ?_
        rw [hp']
        have : p ∈ A ∩ bd S := by rw [hd]; rfl
        exact this.2
  have hmb : m' ∈ bd Y₁ := (show m' ∈ F ∩ bd Y₁ by rw [hbd]; exact .inl rfl).2
  have hne : m' ≠ p' := hF.ne'
  obtain ⟨S', tS', ψ, hS', hψ, hdiff, -, -⟩ := cutIArc Y₁ F m' p' hY₁ hconn hne hbd hF
  have hcomp : connectedComponentIn (bd Y₁) m' ≠ connectedComponentIn (bd Y₁) p' := by
    intro he
    have hmN : m' ∈ θ ⁻¹' A₂ := by
      rw [mem_preimage, hm']
      exact hA₂.left_mem
    have hpb : p' ∈ bd Y₁ := (show p' ∈ F ∩ bd Y₁ by rw [hbd]; exact .inr rfl).2
    obtain ⟨x₀, -, hNe⟩ := hN
    have hpN : p' ∈ θ ⁻¹' A₂ := by
      rw [← hNe] at hmN ⊢
      rw [connectedComponentIn_eq hmN, he]
      exact mem_connectedComponentIn hpb
    have hpA₂ : p ∈ A₂ := by simpa [mem_preimage, hp'] using hpN
    have : p ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, hpA₂⟩
    rw [hin] at this
    exact hmp this.symm
  obtain ⟨-, a', b', c', ⟨e₂⟩, ⟨e₃⟩⟩ := hdiff hcomp
  obtain ⟨hc', ha', hb'⟩ := (modelCriterion.2 a' b' (c' + 1) a b (c + 1)).mp ⟨e₂.symm.trans e₁⟩
  obtain ⟨e₄⟩ := (modelCriterion.2 a' b' c' a b c).mpr ⟨by omega, ha', hb'⟩
  have hcut₂ : IsCutAlongSet F ψ := IsCutAlongSet.of_isCutting hS' hY₁ hF.isCompact.isClosed hψ
  have hbdeq : bd Y₁ ∪ F = bd Y₁ ∪ θ ⁻¹' A₁ := by
    have hsub : θ ⁻¹' A₂ ⊆ bd Y₁ := hmap.2.2.2.2
    ext z
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact .inr (hA₁₂ z h)
    · rintro (h | h)
      · exact .inl h
      · have : z ∈ θ ⁻¹' (A₁ ∪ A₂) := .inl h
        rw [hpre] at this
        rcases this with h' | h'
        · exact .inr h'
        · exact .inl (hsub h')
  have hfin := hcut.comp (hcut₂.congr hbdeq)
  rw [union_comm, hun] at hfin
  exact ⟨S', tS', θ ∘ ψ, hfin, ⟨e₃.trans e₄⟩⟩

/-- A forest grown one line at a time from a set `B`. Each new line misses what is there, or meets
it in exactly one end, and the number counts the lines that miss it. -/
inductive IsGrowth : Set S → List (Set S) → ℕ → Prop
  | nil (B : Set S) : IsGrowth B [] 0
  | free {B A : Set S} {l : List (Set S)} {k : ℕ} (hA : IsLine A) (hd : A ∩ B = ∅) (h : IsGrowth
    (B ∪ A) l k) : IsGrowth B (A :: l) (k + 1)
  | attached {B A : Set S} {l : List (Set S)} {k : ℕ} {p q : S} (hA : IsLineWithEnds A p q)
    (hd : A ∩ B = {p}) (h : IsGrowth (B ∪ A) l k) : IsGrowth B (A :: l) k

/-- The union of a list of sets. -/
def listUnion (l : List (Set S)) : Set S := ⋃₀ {A | A ∈ l}

omit [TopologicalSpace S] in
@[simp] theorem listUnion_nil : listUnion ([] : List (Set S)) = ∅ := by simp [listUnion]

omit [TopologicalSpace S] in
@[simp] theorem listUnion_cons {A : Set S} {l : List (Set S)} : listUnion (A :: l)
  = A ∪ listUnion l := by
  ext z
  simp [listUnion]

/-- A growth lifts through a cut. -/
theorem IsGrowth.lift [CompactSpace S₁] [T2Space S₁] [T2Space S] {B₀ B : Set S} {θ : S₁ → S}
  (hθ : IsCutMap θ B₀) (hB₀ : IsClosed B₀) {l : List (Set S)} {k : ℕ} (h : IsGrowth B l k)
    (hsub : B₀ ⊆ B) :
    ∃ l' : List (Set S₁), l'.length = l.length ∧ IsGrowth (θ ⁻¹' B) l' k ∧ θ ⁻¹' (B ∪ listUnion l)
      = θ ⁻¹' B ∪ listUnion l' := by
  have key : ∀ {A : Set S} {p q : S} {B : Set S}, B₀ ⊆ B → IsLineWithEnds A p q → A ∩ B ⊆ {p} →
      ∃ (A' : Set S₁) (p' q' : S₁), IsLineWithEnds A' p' q' ∧ θ p' = p ∧ θ '' A' = A ∧ InjOn θ A'
        ∧ θ ⁻¹' (B ∪ A) = θ ⁻¹' B ∪ A' := by
    intro A p q B hs hA hd
    obtain ⟨A', p', q', hl, hp, -, him, hinj, hpre⟩ := exists_lift_line hθ hB₀ hA (fun z hz
      => hd ⟨hz.1, hs hz.2⟩)
    refine ⟨A', p', q', hl, hp, him, hinj, ?_⟩
    ext z
    constructor
    · rintro (h | h)
      · exact .inl h
      · have : z ∈ θ ⁻¹' (A ∪ B₀) := .inl h
        rw [hpre] at this
        rcases this with h' | h'
        · exact .inr h'
        · exact .inl (hs h')
    · rintro (h | h)
      · exact .inl h
      · exact .inr (him ▸ mem_image_of_mem θ h)
  induction h with
  | nil B => exact ⟨[], rfl, .nil _, by simp⟩
  | @free B A l k hA hd _ ih =>
    obtain ⟨f⟩ := hA
    have hA' : IsLineWithEnds A (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
    obtain ⟨A', p', q', hl, -, him, -, heq⟩ := key hsub hA' (by rw [hd]; exact empty_subset _)
    obtain ⟨l', hlen, hg, hpre⟩ := ih (hsub.trans subset_union_left)
    have hlin : IsLine A' := by
      obtain ⟨g, -, -⟩ := hl
      exact ⟨g⟩
    refine ⟨A' :: l', by simp [hlen], .free hlin ?_ (heq ▸ hg), ?_⟩
    · refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have : θ z ∈ A ∩ B := ⟨him ▸ mem_image_of_mem θ hz.1, hz.2⟩
      rw [hd] at this
      exact this
    · rw [listUnion_cons, listUnion_cons, ← union_assoc, hpre, heq, union_assoc]
  | @attached B A l k p q hA hd _ ih =>
    obtain ⟨A', p', q', hl, hp, him, hinj, heq⟩ := key hsub hA (by rw [hd])
    obtain ⟨l', hlen, hg, hpre⟩ := ih (hsub.trans subset_union_left)
    have hpB : p ∈ B := (show p ∈ A ∩ B by rw [hd]; rfl).2
    refine ⟨A' :: l', by simp [hlen], .attached hl ?_ (heq ▸ hg), ?_⟩
    · ext z
      constructor
      · rintro ⟨hz, hzB⟩
        have : θ z ∈ A ∩ B := ⟨him ▸ mem_image_of_mem θ hz, hzB⟩
        rw [hd] at this
        exact hinj hz hl.left_mem (this.trans hp.symm)
      · rintro rfl
        exact ⟨hl.left_mem, show θ _ ∈ B by rw [hp]; exact hpB⟩
    · rw [listUnion_cons, listUnion_cons, ← union_assoc, hpre, heq, union_assoc]

/-- **Cutting along a grown forest.** Only the lines that start a new tree away from `bd S` add a
cuff. -/
theorem exists_cut_growth {a b : ℕ} (n : ℕ) : ∀ {S : Type u} [TopologicalSpace S]
  (_ : IsSurface S) {c : ℕ} (_ : Nonempty (S ≃ₜ SurfaceModel a b c)) {l : List (Set S)} {k : ℕ},
    l.length = n → IsGrowth (bd S) l k → ∃ (Y : Type u) (_ : TopologicalSpace Y) (θ : Y
      → S), IsCutAlongSet (listUnion l) θ ∧ Nonempty (Y ≃ₜ SurfaceModel a b (c + k)) := by
  induction n with
  | zero =>
    intro S _ hS c hm l k hl hg
    obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
    have hk : k = 0 := by
      cases hg
      rfl
    subst hk
    exact ⟨S, inferInstance, id, by simpa using isCutAlongSet_id hS, hm⟩
  | succ n ih =>
    intro S _ hS c hm l k hl hg
    have : T2Space S := hS.2.1
    have step : ∀ {A : Set S} {l' : List (Set S)} {k' c' : ℕ} {Y : Type u} [TopologicalSpace Y] {θ
      : Y → S}, l'.length = n → IsGrowth (bd S ∪ A) l' k' → IsCutAlongSet A θ → Nonempty
        (Y ≃ₜ SurfaceModel a b c') → IsClosed A →
        ∃ (Y' : Type u) (_ : TopologicalSpace Y') (θ' : Y' → S), IsCutAlongSet
          (A ∪ listUnion l') θ' ∧ Nonempty (Y' ≃ₜ SurfaceModel a b (c' + k')) := by
      intro A l' k' c' Y _ θ hlen hg' hcut hmY hcl
      have hY := hcut.isSurface
      have : CompactSpace Y := hY.1
      have : T2Space Y := hY.2.1
      obtain ⟨l'', hlen', hg'', hpre⟩ := hg'.lift hcut.isCutMap ((isClosed_bd S).union hcl)
        subset_rfl
      rw [hcut.preimage_bd] at hg''
      obtain ⟨Y', tY', θ', hcut', hmY'⟩ := ih hY hmY (hlen'.trans hlen) hg''
      have hb : bd Y ∪ listUnion l'' = bd Y ∪ θ ⁻¹' listUnion l' := by
        rw [← hcut.preimage_bd, ← hpre, preimage_union]
      exact ⟨Y', tY', θ ∘ θ', hcut.comp (hcut'.congr hb), hmY'⟩
    cases hg with
    | nil _ => simp at hl
    | free hA hd h =>
      obtain ⟨f⟩ := hA
      have hA' : IsLineWithEnds _ (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
      obtain ⟨Y, tY, θ, hcut, -, hmY, -⟩ := exists_cut_free_line hS hm hA' hd
      have := step (by simpa using hl) h hcut hmY hA'.isCompact.isClosed
      rw [listUnion_cons, ← Nat.add_assoc, Nat.add_right_comm]
      exact this
    | attached hA hd h =>
      obtain ⟨Y, tY, θ, hcut, hmY⟩ := exists_cut_attached hS hm hA hd
      have := step (by simpa using hl) h hcut hmY hA.isCompact.isClosed
      rw [listUnion_cons]
      exact this

end GraphMinor.GM07

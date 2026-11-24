/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14af
public import LeanPool.GraphMinor.GM07.Section5b

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Graph Minors XIX, Section 14: the places of one feature

Fix a drawing `K` in `Σ`. A row is a wheel cover of a painting whose boundaries lie on `U(K)` and
whose marked points lie in `V(K)`, after a `Φ`-preserving homeomorphism. We show that
the places of all rows are well-behaved.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A wheel cover of `D` in position on `K`. -/
structure Row (D : TangleDatum cap χ) (ω₀ : α) (K : Drawing S) (b : ℕ) where
  /-- The wheel discs used to make the cuts. -/
  𝒲 : Set (Set Shat)
  /-- The chosen wheel frame on each disc. -/
  fr : ∀ W : ↥𝒲, WheelFrame D W.1
  /-- The homeomorphism applied before cutting. -/
  f : S ≃ₜ S
  hf : IsFramePreservingHomeo χ.Φ f
  cut : IsCutData (cap.emb ∘ f) 𝒲
  cov : ∀ e ∈ D.Γ.E, χ.unionLE ω₀ (D.P.φ e) → ∃ W ∈ 𝒲, cap.emb '' e ⊆ W
  hb : ∀ W, (fr W).ρ ≤ b
  hU : cutF (cap.emb ∘ f) 𝒲 = K.U
  hV : ∀ (W : ↥𝒲) (i : ℕ), i < (fr W).R.k → (i + 1 = (fr W).R.k ∨ ¬ (fr W).Reg i)
    → ∀ x : S, cap.emb (f x) = (fr W).R.vert i ∨ cap.emb (f x) = (fr W).R.vert (i + 1) ∨ cap.emb
      (f x) = (fr W).R.reg i → x ∈ K.V

namespace Row

variable {D : TangleDatum cap χ} {ω₀ : α} {K : Drawing S} {b : ℕ} (r : Row D ω₀ K b)

/-- The part of `Σ` that a row deletes. -/
def T : Set S := cutT (cap.emb ∘ r.f) r.𝒲

/-- The slice of a row. -/
def slice {T' : Set S} (h : r.T = T') : Slice T' D := ⟨r.𝒲, r.fr, r.f, r.hf, r.cut, h⟩

/-- The place of a row. -/
noncomputable def place (hd : χ.IsDisjoint) : Place χ := ⟨hd, D.P, coverLoc r.𝒲 r.cut.finite
  r.cut.disj r.fr⟩

theorem T_inter : Disjoint r.T K.U := by
  rw [← r.hU]
  refine disjoint_left.mpr fun x hx hx' ↦ ?_
  obtain ⟨W, hW, hi⟩ := mem_iUnion₂.mp hx
  obtain ⟨W', hW', hb⟩ := mem_iUnion₂.mp hx'
  by_cases he : W = W'
  · subst he
    exact hi.2 hb
  · exact disjoint_left.mp (r.cut.disj hW hW' he) hi.1 (Surface.discBd_subset _ hb)

/-- A row deletes a union of regions of `K`. -/
theorem T_eq : r.T = ⋃₀ {c ∈ K.R | c ⊆ r.T} := by
  have := cap.connected
  let s := r.slice rfl
  refine Subset.antisymm (fun x hx ↦ ?_) (sUnion_subset fun c hc ↦ hc.2)
  have hxU : x ∈ univ \ K.U := ⟨mem_univ _, disjoint_left.mp r.T_inter hx⟩
  refine ⟨connectedComponentIn (univ \ K.U) x, ⟨⟨x, hxU, rfl⟩, ?_⟩, mem_connectedComponentIn hxU⟩
  have hTo : IsOpen r.T := s.isOpen_T
  have hco : IsOpen (r.T ∪ K.U)ᶜ := by
    have := s.isClosed_T_F
    rw [show cutF (cap.emb ∘ s.f) s.𝒲 = K.U from r.hU] at this
    exact this.isOpen_compl
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hTo hco
    (disjoint_left.mpr fun y hy hy' ↦ hy' (.inl hy)) ?_ ⟨x, mem_connectedComponentIn hxU, hx⟩
  intro y hy
  have hy' := connectedComponentIn_subset _ _ hy
  by_cases hyT : y ∈ r.T
  · exact .inl hyT
  · exact .inr fun h ↦ h.elim hyT hy'.2

end Row

/-- The places of the rows on `K`. -/
def rowPlaces (cap : IsCappedSurface S Shat) {χ : ColourScheme S α} (hd : χ.IsDisjoint) (𝒮 : Set
  (ColouredPainting χ)) (ω₀ : α) (K : Drawing S) (b : ℕ) : Set (Place χ) :=
  {X | ∃ D : TangleDatum cap χ, D.P ∈ 𝒮 ∧ ∃ r : Row D ω₀ K b, X = r.place hd}

theorem rowPlaces_wellBehaved [Infinite α] (hd : χ.IsDisjoint) {𝒮 : Set
  (ColouredPainting χ)} (hcl : IsPaintingClass χ 𝒮) (hS2 : ConditionS2 χ cap) {k : ℕ} {ω₀ : α}
    (hk : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3 ∧ ω₀ ∈ χ.Ω3.E)) (K : Drawing S)
      (b : ℕ) : IsWellBehavedPlaces (rowPlaces cap hd 𝒮 ω₀ K b) := by
  intro β Ω hΩ seq hseq ξ hξ
  classical
  have hS := χ.isSurface
  have hconn := χ.connected
  choose D hm r hr using hseq
  obtain rfl : seq = fun i ↦ (r i).place hd := funext hr
  have hprop : K.IsProper := by
    rintro x ⟨hxb, hxU⟩
    exfalso
    have hT : x ∈ (r 0).T := ((r 0).slice rfl).bd_sub_T hxb
    exact disjoint_left.mp (r 0).T_inter hT hxU
  have hR : K.R.Finite := GM07.finite_regions_of_isProper hS hprop
  have hF : (sUnion '' 𝒫 K.R).Finite := hR.finite_subsets.image _
  have hsets : ∀ i, (r i).T ∈ sUnion '' 𝒫 K.R := fun i ↦
    ⟨{c ∈ K.R | c ⊆ (r i).T}, fun _ hc ↦ hc.1, (r i).T_eq.symm⟩
  obtain ⟨g₁, T₀, hg₁, hT⟩ := exists_subseq_const hF (fun i ↦ (r i).T) hsets
  have hfV : ((Subtype.val : ↥T₀ᶜ → S) ⁻¹' K.V).Finite := K.finite_V.preimage
    Subtype.val_injective.injOn
  have hmN : ∀ i, ((r (g₁ i)).slice (hT i)).markN ⊆ (Subtype.val : ↥T₀ᶜ → S) ⁻¹' K.V ∧ ((r
    (g₁ i)).slice (hT i)).markZ ⊆ (Subtype.val : ↥T₀ᶜ → S) ⁻¹' K.V := by
    intro i
    let s := (r (g₁ i)).slice (hT i)
    constructor
    · intro x hx
      obtain ⟨W, hx⟩ := mem_iUnion.mp hx
      obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp hx
      rcases hx with rfl | hx
      · exact (r (g₁ i)).hV W p hp.1 hp.2 _ (.inl (s.e_vx W p))
      · exact (r (g₁ i)).hV W p hp.1 hp.2 _ (.inr (.inl ((mem_singleton_iff.mp hx) ▸ s.e_vx W
          (p + 1))))
    · intro x hx
      obtain ⟨W, hx⟩ := mem_iUnion.mp hx
      obtain ⟨p, hp, rfl⟩ := mem_iUnion₂.mp hx
      exact (r (g₁ i)).hV W p hp.1 hp.2 _ (.inr (.inr (s.e_zx W p)))
  obtain ⟨i, j, hij, τ, h₁, h₂⟩ := exists_pair_slices (fun i ↦ (r (g₁ i)).slice (hT i)) hfV hmN
    (fun i ↦ (r (g₁ i)).hb) (fun i ↦ (r (g₁ i)).cov) (fun i ↦ hm _) hd hcl hS2 hk hΩ (fun i ↦ ξ
      (g₁ i)) (fun i ↦ hξ _)
  exact ⟨g₁ i, g₁ j, hg₁ hij, τ, h₁, h₂⟩

end GraphMinor.GM19

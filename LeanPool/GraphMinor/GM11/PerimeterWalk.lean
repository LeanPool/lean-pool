/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PerimeterExists
public import LeanPool.GraphMinor.GM11.Solid
public import LeanPool.GraphMinor.GM11.OpenAround
public import LeanPool.GraphMinor.GM11.Cited
public import LeanPool.GraphMinor.GM11.ForestRegions
public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.GM11.PaintingCells

/-!
# Perimeter walks exist

Graph Minors XI, Section 8 (page 96): "there is a closed walk of $\Gamma$ tracing out $bd(X)$ in the
natural
sense." `exists_perimeterWalk` proves this for each closed, simply-connected, `Γ`-nice set `X` other
than
the empty set and the whole surface, and it counts how often the walk uses each edge. The main case
is
`exists_perimeter_of_disc`. What remains is the set with no edge on its frontier, which is a single
vertex.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A collar around a point. -/
theorem exists_point_collar (hS : IsClosedSurface S) (v : S) :
    ∃ h : C(Circle × I, S), InjOn h {p | 0 < p.2} ∧ (∀ p : Circle × I, 0 < p.2 → h p ≠ v) ∧
      (∀ z, h (z, 0) = v) ∧ IsOpen ({v} ∪ h '' {p | p.2 < 1}) := by
  obtain ⟨V, hV, hvV, ⟨e⟩⟩ := hS.2.2 v
  let T : OpenUnitDisc → S := fun y => (e.symm y).1
  have hT : Continuous T := continuous_subtype_val.comp e.symm.continuous
  have hTi : Function.Injective T := fun p q hpq => e.symm.injective (Subtype.ext hpq)
  have hTo : IsOpenMap T := hV.isOpenEmbedding_subtypeVal.isOpenMap.comp e.symm.isOpenMap
  let c : OpenUnitDisc := e ⟨v, hvV⟩
  have hTc : T c = v := by simp [T, c]
  have hc1 : ‖c.1‖ < 1 := by simpa [OpenUnitDisc] using c.2
  let ρ : ℝ := (1 - ‖c.1‖) / 2
  have hρ : 0 < ρ := by
    simp only [ρ]
    linarith
  have hcz : ∀ z : Circle, ‖complexPlane (z : ℂ)‖ = 1 := fun z => by simp
  let pt : Circle × I → EuclideanPlane := fun p => c.1 + (ρ * p.2.1) • complexPlane (p.1 : ℂ)
  have hpt : Continuous pt := by
    have h₁ : Continuous fun p : Circle × I => complexPlane (p.1 : ℂ) :=
      complexPlane.continuous.comp (continuous_induced_dom.comp continuous_fst)
    have h₂ : Continuous fun p : Circle × I => ρ * p.2.1 :=
      continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    exact continuous_const.add (h₂.smul h₁)
  have hnorm : ∀ p : Circle × I, ‖(ρ * p.2.1) • complexPlane (p.1 : ℂ)‖ = ρ * p.2.1 := fun p => by
    rw [norm_smul, hcz, mul_one, Real.norm_of_nonneg (mul_nonneg hρ.le p.2.2.1)]
  have hmem : ∀ p, pt p ∈ OpenUnitDisc := by
    intro p
    have h₁ := norm_add_le c.1 ((ρ * p.2.1) • complexPlane (p.1 : ℂ))
    rw [hnorm] at h₁
    have h₂ : ρ * p.2.1 ≤ ρ := by nlinarith [p.2.2.2]
    have h₃ : ‖pt p‖ < 1 := by
      simp only [ρ] at h₂ h₁
      simp only [pt, ρ]
      linarith
    simpa [OpenUnitDisc] using h₃
  let pt' : Circle × I → OpenUnitDisc := fun p => ⟨pt p, hmem p⟩
  have hpt' : Continuous pt' := Continuous.subtype_mk hpt _
  let h : C(Circle × I, S) := ⟨fun p => T (pt' p), hT.comp hpt'⟩
  have hbot : ∀ z, h (z, 0) = v := by
    intro z
    have : pt' (z, 0) = c := Subtype.ext (by simp [pt', pt])
    change T (pt' (z, 0)) = v
    rw [this, hTc]
  have heq : ∀ p q, h p = h q → (ρ * p.2.1) • complexPlane (p.1 : ℂ) = (ρ * q.2.1) • complexPlane
    (q.1 : ℂ) := by
    intro p q hpq
    have h₁ : pt' p = pt' q := hTi hpq
    have h₂ : pt p = pt q := congrArg Subtype.val h₁
    exact add_left_cancel h₂
  refine ⟨h, ?_, ?_, hbot, ?_⟩
  · rintro ⟨z, t⟩ ht ⟨z', t'⟩ ht' hpq
    have htp : (0 : ℝ) < t.1 := ht
    have h₁ := heq _ _ hpq
    have h₂ := congrArg norm h₁
    rw [hnorm, hnorm] at h₂
    have h₃ : t.1 = t'.1 := mul_left_cancel₀ hρ.ne' h₂
    have ht₃ : t = t' := Subtype.ext h₃
    subst ht₃
    have h₄ := smul_right_injective _ (mul_pos hρ htp).ne' h₁
    have h₅ : (z : ℂ) = z' := complexPlane.injective h₄
    exact Prod.ext (Circle.ext h₅) rfl
  · intro p hp hpv
    have htp : (0 : ℝ) < p.2.1 := hp
    have h₁ : h p = h (p.1, 0) := hpv.trans (hbot _).symm
    have h₂ := congrArg norm (heq _ _ h₁)
    rw [hnorm, hnorm] at h₂
    simp only [Icc.coe_zero, mul_zero] at h₂
    exact (mul_pos hρ htp).ne' h₂
  · have hop : IsOpen {y : OpenUnitDisc | dist y.1 c.1 < ρ} :=
      isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
    have hsets : ({v} ∪ h '' {p | p.2 < 1} : Set S) = T '' {y : OpenUnitDisc | dist y.1 c.1 < ρ}
      := by
      ext x
      constructor
      · rintro (hx | ⟨p, hp, rfl⟩)
        · exact ⟨c, by simpa using hρ, by rw [hTc, mem_singleton_iff.mp hx]⟩
        · refine ⟨pt' p, ?_, rfl⟩
          have hp' : p.2.1 < 1 := hp
          change dist (pt p) c.1 < ρ
          rw [dist_eq_norm]
          simp only [pt, add_sub_cancel_left]
          rw [hnorm]
          nlinarith
      · rintro ⟨y, hy, rfl⟩
        by_cases hyc : y = c
        · exact Or.inl (by rw [hyc, hTc]; rfl)
        have hy' : ‖y.1 - c.1‖ < ρ := by
          rw [← dist_eq_norm]
          exact hy
        let w : ℂ := complexPlane.symm (y.1 - c.1)
        have hw : ‖w‖ = ‖y.1 - c.1‖ := complexPlane.symm.norm_map _
        have hwpos : 0 < ‖w‖ := by
          rw [hw, norm_pos_iff, sub_ne_zero]
          exact fun h₀ => hyc (Subtype.ext h₀)
        let t : I := ⟨‖w‖ / ρ, by positivity, (div_le_one hρ).mpr (by rw [hw]; exact hy'.le)⟩
        have ht1 : t.1 * ρ = ‖w‖ := by
          change ‖w‖ / ρ * ρ = ‖w‖
          field_simp
        have hz : (Circle.exp (Complex.arg w) : ℂ) * ‖w‖ = w := by
          rw [Circle.coe_exp, mul_comm]
          exact Complex.norm_mul_exp_arg_mul_I w
        refine Or.inr ⟨(Circle.exp (Complex.arg w), t), ?_, ?_⟩
        · change ‖w‖ / ρ < 1
          rw [div_lt_one hρ, hw]
          exact hy'
        · change T (pt' _) = T y
          congr 1
          apply Subtype.ext
          change c.1 + (ρ * t.1) • complexPlane (Circle.exp (Complex.arg w) : ℂ) = y.1
          have hsm : (ρ * t.1) • complexPlane (Circle.exp (Complex.arg w) : ℂ) = y.1 - c.1 := by
            rw [← map_smul]
            have : (ρ * t.1) • (Circle.exp (Complex.arg w) : ℂ) = w := by
              rw [Complex.real_smul, mul_comm ρ, ht1, mul_comm]
              exact_mod_cast hz
            rw [this]
            exact complexPlane.apply_symm_apply _
          rw [hsm]
          abel
    rw [hsets]
    exact hTo _ hop

variable [T2Space S] [ConnectedSpace S]

/-- A closed nice simply-connected set other than the surface lies in an open disc. This is the case
`Y = ∅` of
Graph Minors XI, (7.5), which the paper derives from Graph Minors VII, (11.10). We take the proof of
(11.10) from
`exists_open_around`, and the sphere is done by hand. -/
theorem exists_openDisc_around (hS : IsClosedSurface S)
    {Γ : Drawing S} {X : Set S} (hXc : IsClosed X) (hXn : IsGammaNice Γ X)
    (hXs : IsSimplyConnectedSet X) (hu : X ≠ univ) : ∃ A, IsOpenDisc A ∧ X ⊆ A := by
  have hflat : Flat (Subtype.val ⁻¹' X : Set (univ : Set S)) :=
    flat_of_simplyConnected hXs (subset_univ X)
  obtain ⟨Y, hXY, -, h | h⟩ := exists_open_around hS isOpen_univ (subset_univ X) hXc
    (isSolid_of_nice hS hXc hXn).1 hXs.1 hflat
  · -- In a sphere, take an `O`-arc off `X`. Then `X` lies on one side of it.
    obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem X).mp hu
    obtain ⟨D, D', hD, -, -, -, hDX, -⟩ := exists_closedDisc_nbhd hS hXc.isOpen_compl hz
    obtain ⟨F, hF⟩ : ∃ F, F = discBd D := ⟨_, rfl⟩
    have hFO : IsOArc F := hF ▸ IsClosedDisc.isOArc_discBd hD
    have hFX : Disjoint X F := disjoint_left.mpr fun x hx hxF =>
      hDX (discBd_subset D (hF ▸ hxF)) hx
    obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, -⟩ := sphere_disc S h.1 F hFO
    have hint₁ : IsOpen (Δ₁ \ discBd Δ₁) := (isOpenDisc_interior hS hΔ₁).1
    have hint₂ : IsOpen (Δ₂ \ discBd Δ₂) := (isOpenDisc_interior hS hΔ₂).1
    have hdis : Disjoint (Δ₁ \ discBd Δ₁) (Δ₂ \ discBd Δ₂) := disjoint_left.mpr fun x h₁ h₂ =>
      h₁.2 (by rw [hb₁, ← hcap]; exact ⟨h₁.1, h₂.1⟩)
    have hcover : X ⊆ (Δ₁ \ discBd Δ₁) ∪ (Δ₂ \ discBd Δ₂) := fun x hx => by
      have hxF : x ∉ F := disjoint_left.mp hFX hx
      have hxu : x ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ x
      rcases hxu with h' | h'
      · exact Or.inl ⟨h', by rwa [hb₁]⟩
      · exact Or.inr ⟨h', by rwa [hb₂]⟩
    rcases hXs.1.isConnected.isPreconnected.subset_or_subset hint₁ hint₂ hdis hcover with h' | h'
    · exact ⟨_, isOpenDisc_interior hS hΔ₁, h'⟩
    · exact ⟨_, isOpenDisc_interior hS hΔ₂, h'⟩
  · exact ⟨Y, h, hXY⟩

open Classical in
/-- **Existence of perimeter walks** (Graph Minors XI, Section 8, page 96). The walk uses an edge on
the
frontier of `X` once for each side outside `X`, and it uses no other edge. -/
theorem exists_perimeterWalk (hS : IsClosedSurface S)
    {Γ : Drawing S} {X : Set S} (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X) (hXs : IsSimplyConnectedSet X) (hne : X.Nonempty) (hu : X ≠ univ) :
    ∃ (u : S) (W : GraphWalk Γ.toGraph u u), IsPerimeterWalk Γ X W ∧
      ∀ e ∈ Γ.E, edgeCount W.edges e =
        if (e ∩ frontier X).Nonempty then (if IsTwoSided Xᶜ e then 2 else 1) else 0 := by
  obtain ⟨A, hA, hXA⟩ := exists_openDisc_around hS hXc hXn hXs hu
  by_cases hE : (Γ.interSet (frontier X)).E.Nonempty
  · obtain ⟨u, W, hW, -, hc⟩ := exists_perimeter_of_disc hS hXc hXn hXs hne hA hXA hE
    exact ⟨u, W, hW, hc⟩
  have hK : CompactSpace S := hS.1
  set B := Γ.interSet (frontier X) with hBdef
  have hBs : B.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hBU : B.U = frontier X := frontier_interSet hS hXc hXn
  have hEe : B.E = ∅ := not_nonempty_iff_eq_empty.mp hE
  have hBV : frontier X = B.V := by
    rw [← hBU, B.U_eq, hEe]
    simp
  have hno : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing B → False := fun C hC hsub => by
    obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC
    exact (hEe ▸ hsub.2 he : e ∈ (∅ : Set (Set S)))
  have hconn := isPreconnected_compl_of_noCircuit hS B hno
  -- The complement of the frontier lies outside `X`, for otherwise `X` is everything.
  have hdis : Disjoint (interior X) Xᶜ := disjoint_left.mpr fun x hx h => h (interior_subset hx)
  have hcov : B.Uᶜ ⊆ interior X ∪ Xᶜ := by
    intro x hx
    by_cases hxX : x ∈ X
    · refine Or.inl ?_
      by_contra hint
      exact hx (hBU ▸ (⟨subset_closure hxX, hint⟩ : x ∈ frontier X))
    · exact Or.inr hxX
  have hXsub : X ⊆ B.U := by
    rcases hconn.subset_or_subset isOpen_interior hXc.isOpen_compl hdis hcov with h | h
    · exfalso
      apply hu
      refine eq_univ_of_forall fun x => hXc.closure_subset_iff.mpr ?_ (?_ : x ∈ closure B.Uᶜ)
      · exact h.trans interior_subset
      · refine mem_closure_iff.mpr fun O hO hxO => ?_
        obtain ⟨z, hzO, hzU⟩ := exists_notMem_U (Γ := B) hS hO ⟨x, hxO⟩
        exact ⟨z, hzO, hzU⟩
    · intro x hx
      by_contra hxU
      exact h hxU hx
  have hXfin : X.Finite := (B.finite_V).subset (by rwa [hBU, hBV] at hXsub)
  obtain ⟨v, hv⟩ := hne
  have hXv : X = {v} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨hv, fun a ha => ?_⟩
    by_contra hav
    have hp := hXs.1.isConnected.isPreconnected
    have hcl : IsClosed (X \ {v}) := (hXfin.subset sdiff_subset).isClosed
    rcases isPreconnected_iff_subset_of_disjoint.mp hp (X \ {v})ᶜ {v}ᶜ hcl.isOpen_compl
      isOpen_compl_singleton (fun x hx => by
        by_cases hxv : x = v
        · exact Or.inl fun h => h.2 hxv
        · exact Or.inr hxv) (by
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_sdiff, mem_singleton_iff, mem_empty_iff_false,
          iff_false]
        tauto) with h | h
    · exact h ha ⟨ha, hav⟩
    · exact h hv rfl
  subst hXv
  have hfr : frontier ({v} : Set S) = {v} := by
    refine subset_antisymm hXc.frontier_subset ?_
    obtain ⟨y, hy⟩ : (frontier ({v} : Set S)).Nonempty :=
      nonempty_frontier_iff.mpr ⟨⟨v, rfl⟩, fun h => hu h⟩
    have : y = v := hXc.frontier_subset hy
    subst this
    exact singleton_subset_iff.mpr hy
  have hvf : v ∈ frontier ({v} : Set S) := by
    rw [hfr]
    rfl
  have hvV : v ∈ Γ.V := hBs.1 (hBV ▸ hvf)
  obtain ⟨h, h₁, h₂, h₃, h₄⟩ := exists_point_collar hS v
  refine ⟨v, .nil hvV, ⟨h, h₁, fun p hp hx => h₂ p hp hx, ?_, h₄, Or.inl ⟨rfl, h₃⟩⟩, fun e he => ?_⟩
  · rw [subBd_eq_frontier, hfr]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact h₃ z
    · rintro rfl
      exact ⟨1, h₃ 1⟩
  · have hemp : ¬ (e ∩ frontier ({v} : Set S)).Nonempty := by
      rintro ⟨y, hye, hyf⟩
      have : y = v := by rwa [hfr] at hyf
      exact (he.2.1 hye).2 (this ▸ hvV)
    simp only [hemp, ite_false]
    rfl

end GraphMinor.GM11

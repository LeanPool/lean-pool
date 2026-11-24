/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.BiteArc
public import LeanPool.GraphMinor.GM19.SideEdges
public import LeanPool.GraphMinor.GM19.Section11a

/-!
# Graph Minors XIX, (11.2)

A datum flawed on a side has a feast of order at most `(m + 1)n`. Each edge of the cuff lies in a
bite of length at most 6 (`exists_bite_of_edge`), and
the walk along the side of `Section11a.lean` picks the bites.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

omit [T2Space S] [T2Space Shat] in
/-- A point of a subdrawing of `Γ*` in the cuff disc of `r` shows that `r` is on the subdrawing. -/
theorem pole_mem_of_meet {F : Drawing Shat} (hF : F.IsSubdrawing D.rad.G) {r : Shat}
  (hr : r ∈ D.rad.poles) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hreg : D.rad.regionOf r = cap.cuffDisc Θ) {x : Shat} (hx : x ∈ F.U)
      (hxd : x ∈ cap.cuffDisc Θ) : r ∈ F.V := by
  have : ConnectedSpace Shat := cap.connected
  have hxr : x ∉ range cap.emb := cap.notMem_range hΘ hxd
  have hG3 := D.rad.isPreRadial.2.2.1
  have huniq : ∀ {w}, w ∈ D.rad.Rstar → x ∈ D.rad.regionOf w → w = r := fun {w} hw hxw ↦ by
    have hm := D.rad.regionOf_mem hw
    have hm' := D.rad.regionOf_mem hr.1
    have hxr' : x ∈ D.rad.regionOf r := hreg ▸ hxd
    have he : D.rad.regionOf w = D.rad.regionOf r :=
      (connectedComponentIn_eq hxw).trans (connectedComponentIn_eq hxr').symm
    exact (hG3 _ hm'.1).unique ⟨he ▸ hm.2, hw.1⟩ ⟨hm'.2, hr.1.1⟩
  by_cases hxV : x ∈ F.V
  · have hw : x ∈ D.rad.Rstar := ⟨hF.1 hxV, fun ⟨v, _, hv⟩ ↦ hxr ⟨v, hv⟩⟩
    rw [← huniq hw (D.rad.regionOf_mem hw).2]
    exact hxV
  · obtain ⟨f, hf, hxf⟩ := F.exists_edge_of_mem hx hxV
    obtain ⟨v, -, w, hw, hset⟩ := D.rad.edge_ends (hF.2 hf)
    have hwm : w ∈ closure f ∩ D.rad.G.V := by rw [hset]; exact Or.inr rfl
    have hwF : w ∈ F.V := mem_V_of_mem_U hF (F.closure_subset_U hf hwm.1) hwm.2
    rw [← huniq hw (D.rad.edge_subset_region (hF.2 hf) hw hset hxf)]
    exact hwF

/-- From the length of a circuit, with poles far apart: the circuit has at most the one pole `r`. -/
theorem bite_shape_of_far (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected) {N : ℕ}
  (hN : N < D.rep)
    (hd : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → N < D.vDist r₁ r₂) {r : Shat} {F :
      Drawing Shat} (hF : F.IsCircuitOf D.rad.G) (hc : F.E.ncard ≤ 2 * N)
    (hr : r ∈ D.rad.poles) {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hreg : D.rad.regionOf r
      = cap.cuffDisc Θ) (hrF : r ∈ F.V) :
    ∃ v₁ v₂ Β L A A' Di Do, D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do := by
  have hlt : F.E.ncard < 2 * D.rep := by omega
  refine exists_bite_shape hS h3 hF hlt hr hΘ hreg hrF fun p hp hpF ↦ ?_
  by_contra hne
  have h₁ := vDist_le_of_ins hN hF hc hp hr hne (D.U_subset_ins hF hlt (F.V_subset_U hpF))
    (D.U_subset_ins hF hlt (F.V_subset_U hrF))
  have h₂ := hd p hp r hr hne
  omega

/-- **Each edge on a cuff lies in a short bite**, when no circuit is a flaw in freedom. -/
theorem exists_bite_of_edge (hS : IsSurface S) {N : ℕ} (hN : 3 ≤ N) (hrep : 4 ≤ D.rep)
  (hfree : ∀ C, ¬ D.IsFreeCircuit N C) {side : Set S} (hside : side ∈ χ.Φ.longSides) {Θ : Set S}
    (hsΘ : side ⊆ Θ) (hΘ : Θ ∈ cuffs S) {r : Shat} (hr : r ∈ D.rad.poles) (hreg : D.rad.regionOf r
      = cap.cuffDisc Θ) {c : Set S} (hc : c ∈ D.P.Γ.E) (hcΘ : c ⊆ Θ) :
    ∃ F, D.IsBiteAt r F ∧ F.E.ncard ≤ 6 ∧ cap.emb '' c ⊆ D.ins F := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨s, hs, hcs⟩ := D.exists_region_of_edge hc
  obtain ⟨F, hF, h6, hsi⟩ := D.exists_circuit_around hrep hc hs hcs
  have hlt : F.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hF hlt
  have hins : cap.emb '' c ⊆ D.ins F := hcs.trans hsi
  have hbite : ∀ {F'}, F'.IsCircuitOf D.rad.G → F'.E.ncard < 2 * D.rep → r ∈ F'.V → D.IsBiteAt r F'
    := fun h₁ h₂ h₃ ↦ ⟨hr, h₁, h₂, h₃⟩
  by_cases hrF : r ∈ F.V
  · exact ⟨F, hbite hF hlt hrF, h6, hins⟩
  exfalso
  have hdis : Disjoint (cap.cuffDisc Θ) F.U := disjoint_left.2 fun x hx hxF ↦ hrF
    (pole_mem_of_meet hF.1 hr hΘ hreg hxF hx)
  have hrd : r ∈ cap.cuffDisc Θ := hreg ▸ (D.rad.regionOf_mem hr.1).2
  obtain ⟨x, hx⟩ := hc.1
  by_cases hri : r ∈ D.ins F
  · have hconn : IsPreconnected (cap.cuffDisc Θ) := hreg ▸ isPreconnected_connectedComponentIn
    have hsub : cap.cuffDisc Θ ⊆ discInt (D.ins F) := by
      rcases hi.2.2.1.side hman hconn (by rw [hi.2.2.2.1]; exact hdis) with h | h
      · exact h
      · exact absurd hri (disjoint_left.1 h hrd)
    have hcl : closure (cap.cuffDisc Θ) ⊆ D.ins F := closure_minimal (hsub.trans
      (discInt_subset _)) hi.2.2.1.isClosed
    refine hfree F ⟨hF, by omega, Or.inl ⟨side, hside, ?_⟩⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hcl (cap.mem_closure_emb hS hΘ (hsΘ hy))
  · have hm : cap.emb x ∈ F.U := D.cuff_inter_ins_of_disjoint hF hlt hr hri hreg hdis
      (cap.mem_closure_emb hS hΘ (hcΘ hx)) (hins (mem_image_of_mem _ hx))
    exact disjoint_left.1 (disc_edge_disjoint D.rad hF.1 hc) (mem_image_of_mem _ hx) hm

omit [T2Space S] [T2Space Shat] in
/-- What `l(e₁, e₂) ≤ n` says. -/
theorem exists_bite_of_dist_le {r : Shat} {c₁ c₂ : Set S} {n : ℕ} (hn : n < D.rep)
  (h : D.borderEdgeDist r c₁ c₂ ≤ n) :
    ∃ F, D.IsBiteAt r F ∧ cap.emb '' c₁ ⊆ D.ins F ∧ cap.emb '' c₂ ⊆ D.ins F ∧ F.E.ncard ≤ 2 * n
      := by
  classical
  have : ConnectedSpace Shat := cap.connected
  unfold borderEdgeDist at h
  split_ifs at h with hex
  · obtain ⟨F₀, hF₀, h₁, h₂⟩ := hex
    have hne : {k : ℕ | ∃ F : Drawing Shat, D.IsBiteAt r F ∧ cap.emb '' c₁ ⊆ D.ins F
      ∧ cap.emb '' c₂ ⊆ D.ins F ∧ F.E.ncard = 2 * k}.Nonempty :=
      ⟨_, F₀, hF₀, h₁, h₂, D.ncard_E_eq_hat hF₀.is_circuit⟩
    obtain ⟨F, hF, h₃, h₄, h₅⟩ := Nat.sInf_mem hne
    exact ⟨F, hF, h₃, h₄, by omega⟩
  · omega

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

omit hS h3 in
private theorem exists_feast_of_chain_cover
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [T2Space S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    {D : TangleDatum cap χ}
    (hS : IsSurface S)
    {side : Set S}
    {n : ℕ}
    {ω : List β} :
    let m : ℕ := ω.length
    ∀ (hm1 : 1 ≤ m),
    let N : ℕ := (m + 1) * n
    ∀ (Θ : Set S),
    ∀ (f : Circle ≃ₜ ↑Θ),
    ∀ (a : S),
    ∀ (b : S),
    ∀ (k : ℕ),
    ∀ (t : ℕ → ℝ),
    ∀ (e : ℕ → Set S),
    ∀ (hsΘ : side ⊆ Θ),
    ∀ (hE : IsSideEdges χ D.P.Γ side Θ f a b k t e),
    ∀ (r : Shat),
    ∀ (hshape : ∀ {F : Drawing Shat}, D.IsBiteAt r F → (Drawing.E F).ncard ≤ 2 * n → ∃ v₁ v₂ Β L A
      A' Di Do, D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do),
    let Nr : ℕ → ℕ → Prop := fun i j => ∃ F, D.IsBiteAt r F ∧ (Drawing.E F).ncard ≤ 2 * n ∧ ∀ (l :
      ℕ), i ≤ l → l ≤ j → cap.emb '' e l ⊆ D.ins F
    let P : ℕ → ℕ → Prop := fun h j => ∃ (hh : h < ω.length), (χ.ΩS side).le ω[h] (D.P.φ (e j))
    ∀ (hmono : ∀ (i j i' j' : ℕ), i ≤ i' → i' ≤ j' → j' ≤ j → Nr i j → Nr i' j'),
    ∀ (hedgeΘ : ∀ {l : ℕ}, l ≤ k + 1 → e l ⊆ Θ),
    ∀ (hself : ∀ i ≤ k + 1, Nr i i),
    (¬Nr 0 (k + 1)) →
    (∀ (a b : ℕ → ℕ), ¬SideChain Nr P k m a b) →
    ∃ ℱ, D.IsFeast r side ω ℱ ∧ feastOrder ℱ ≤ N ∧ ∀ F ∈ ℱ, (Drawing.E F).ncard ≤ 2 * n := by
  classical
  have : ConnectedSpace Shat := cap.connected
  intro m hm1 N Θ f a b k t e hsΘ hE r hshape Nr P hmono hedgeΘ hself hstart hnochain
  obtain ⟨p, hpm, a₂, b₂, hc, a₁, b₁, hfin⟩ := exists_final hmono hself hstart hnochain
  let lo : ℕ → ℕ := fun i ↦ if i ≤ p then b₂ i else b₁
  let hi : ℕ → ℕ := fun i ↦ if i < p then a₂ (i + 1) else if i = p then a₁ else k + 1
  have hlo0 : lo 0 = 0 := by
    change (if 0 ≤ p then b₂ 0 else b₁) = 0
    rw [ite_eq_left (Nat.zero_le _), hc.b_zero]
  have hlo : ∀ i ≤ p, lo i = b₂ i := fun i h ↦ ite_eq_left h
  have hlop : lo (p + 1) = b₁ := ite_eq_right (by omega)
  have hi₁ : ∀ i < p, hi i = a₂ (i + 1) := fun i h ↦ ite_eq_left h
  have hi₂ : hi p = a₁ := by
    change (if p < p then _ else if p = p then _ else _) = _
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
  have hi₃ : hi (p + 1) = k + 1 := by
    change (if p + 1 < p then _ else if p + 1 = p then _ else _) = _
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hle1 : ∀ i ≤ p + 1, lo i ≤ hi i := by
    intro i h
    rcases Nat.lt_trichotomy i p with h' | rfl | h'
    · rw [hlo i h'.le, hi₁ i h']
      exact hc.b_le_a i h'
    · rw [hlo _ le_rfl, hi₂]
      exact hfin.le₁
    · have hip : i = p + 1 := by omega
      rw [hip, hlop, hi₃]
      exact hfin.le₃
  have hlt1 : ∀ i ≤ p, hi i < lo (i + 1) := by
    intro i h
    rcases Nat.lt_or_eq_of_le h with h' | rfl
    · rw [hi₁ i h', hlo (i + 1) (by omega)]
      exact hc.a_lt_b i h'
    · rw [hi₂, hlop]
      exact hfin.lt₂
  have hstepb : ∀ i i', i < i' → i' ≤ p + 1 → hi i < lo i' := by
    intro i i' hii
    induction i' with
    | zero => omega
    | succ i' ih =>
      intro hle'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hii with h' | rfl
      · have h₁ := ih h' (by omega)
        have h₂ := hle1 i' (by omega)
        have h₃ := hlt1 i' (by omega)
        omega
      · exact hlt1 i (by omega)
  have hhile : ∀ i ≤ p + 1, hi i ≤ k + 1 := fun i h ↦ by
    rcases Nat.lt_or_eq_of_le h with h' | rfl
    · have h₁ := hstepb i (p + 1) h' le_rfl
      have h₂ := hle1 (p + 1) le_rfl
      omega
    · exact hi₃.le
  have hN : ∀ i ≤ p + 1, Nr (lo i) (hi i) := by
    intro i h
    rcases Nat.lt_trichotomy i p with h' | rfl | h'
    · rw [hlo i h'.le, hi₁ i h']
      exact hc.near i h'
    · rw [hlo _ le_rfl, hi₂]
      exact hfin.near₁
    · have hip : i = p + 1 := by omega
      rw [hip, hlop, hi₃]
      exact hfin.near₂
  have hex : ∀ i, ∃ F, i ≤ p + 1 → D.IsBiteAt r F ∧ F.E.ncard ≤ 2 * n ∧ ∀ l, lo i ≤ l → l ≤ hi i
    → cap.emb '' e l ⊆ D.ins F := fun i ↦ by
    by_cases h : i ≤ p + 1
    · obtain ⟨F, hb⟩ := hN i h
      exact ⟨F, fun _ ↦ hb⟩
    · obtain ⟨F, -⟩ := hN 0 (by omega)
      exact ⟨F, fun h' ↦ absurd h' h⟩
  choose G hG using hex
  let ℱ : Set (Drawing Shat) := G '' (↑(Finset.range (p + 2)) : Set ℕ)
  have hfinF : ℱ.Finite := (Finset.finite_toSet _).image _
  have hcardF : ℱ.ncard ≤ p + 2 := by
    refine (ncard_image_le (Finset.finite_toSet _)).trans ?_
    rw [ncard_coe_finset, Finset.card_range]
  have hbite : ∀ F ∈ ℱ, D.IsBiteAt r F ∧ F.E.ncard ≤ 2 * n := by
    rintro _ ⟨i, hi', rfl⟩
    have := hG i (by have := Finset.mem_range.1 (Finset.mem_coe.1 hi'); omega)
    exact ⟨this.1, this.2.1⟩
  have hmemF : ∀ i ≤ p + 1, G i ∈ ℱ := fun i h ↦ mem_image_of_mem _ (Finset.mem_coe.2
    (Finset.mem_range.2 (by omega)))
  have hcover : ∀ i ≤ p + 1, ∀ l, lo i ≤ l → l ≤ hi i → cap.emb '' e l ⊆ D.feastArcUnion r ℱ := by
    intro i h l h₁ h₂
    obtain ⟨hb, hcard, hl⟩ := hG i h
    obtain ⟨v₁, v₂, Β, L, A, A', Di, Do, hsh⟩ := hshape hb hcard
    have hlk : l ≤ k + 1 := h₂.trans (hhile i h)
    have hsub := hsh.edge_subset hS (hE.mem l hlk) (hedgeΘ hlk) (hl l h₁ h₂)
    intro x hx
    exact mem_iUnion₂.2 ⟨G i, hmemF i h, hsub hx⟩
  refine ⟨ℱ, ⟨hfinF, fun F hF ↦ (hbite F hF).1, ?_, fun s hs hne ↦ ?_, fun X hX ↦ ?_⟩, ?_,
    fun F hF ↦ (hbite F hF).2⟩
  · omega
  · rcases hE.short s hs hne with rfl | rfl
    · exact hcover 0 (by omega) 0 (by omega) (Nat.zero_le _)
    · exact hcover (p + 1) le_rfl _ (by have := hle1 (p + 1) le_rfl; rw [hi₃] at this; exact this)
        hi₃.ge
  · obtain ⟨x, hx, rfl⟩ := hX
    set Y := side \ cap.emb ⁻¹' D.feastArcUnion r ℱ with hY
    have hXsub : connectedComponentIn Y x ⊆ Y := connectedComponentIn_subset _ _
    have hXp : IsPreconnected (connectedComponentIn Y x) := isPreconnected_connectedComponentIn
    have hout : ∀ i ≤ p + 1, ∀ l, 1 ≤ l → l ≤ k → lo i ≤ l → l ≤ hi i
      → ¬ e l ⊆ connectedComponentIn Y x := by
      intro i h l h₁ h₂ h₃ h₄ hsub
      obtain ⟨z, -, hz⟩ := hE.exists_point h₁ h₂
      exact (hXsub (hsub hz)).2 (hcover i h l h₃ h₄ (mem_image_of_mem _ hz))
    have hgap : ∀ c ∈ D.Γ.E, c ⊆ connectedComponentIn Y x → ∃ j, 1 ≤ j ∧ j ≤ k ∧ c = e j ∧ ∃ i
      ≤ p, hi i < j ∧ j < lo (i + 1) := by
      intro c hc₁ hc₂
      obtain ⟨j, h₁, h₂, rfl⟩ := hE.all c hc₁ (hc₂.trans fun _ hz ↦ (hXsub hz).1)
      refine ⟨j, h₁, h₂, rfl, exists_gap (by omega) (by omega) fun i h h' ↦ hout i h j h₁ h₂ h'.1
        h'.2 hc₂⟩
    have hsep : ∀ {j j' i i'}, 1 ≤ j → j' ≤ k → e j ⊆ connectedComponentIn Y x
      → e j' ⊆ connectedComponentIn Y x → i < i' → i' ≤ p → j < lo (i + 1) → hi i' < j' → False
        := by
      intro j j' i i' h₁ h₂ h₃ h₄ hii hip h₅ h₆
      have h₇ : lo (i + 1) ≤ hi i' := by
        rcases Nat.lt_or_eq_of_le (show i + 1 ≤ i' by omega) with h' | rfl
        · have := hstepb (i + 1) i' h' (by omega)
          have := hle1 (i + 1) (by omega)
          have := hle1 i' (by omega)
          omega
        · exact hle1 _ (by omega)
      have hhb := hE.between_of_side hXp (fun _ hz ↦ (hXsub hz).1) hsΘ h₁ (by omega) h₂ h₃ h₄ (lo
        (i + 1)) h₅.le (by omega)
      exact hout (i + 1) (by omega) _ (by omega) (by omega) le_rfl (hle1 (i + 1) (by omega)) hhb
    have hP : ∀ i ≤ p, ∀ j, hi i < j → j < lo (i + 1) → ¬ P i j := by
      intro i h j h₁ h₂
      rcases Nat.lt_or_eq_of_le h with h' | rfl
      · rw [hi₁ i h'] at h₁
        rw [hlo (i + 1) (by omega)] at h₂
        exact hc.gap i h' j h₁ h₂
      · rw [hi₂] at h₁
        rw [hlop] at h₂
        exact hfin.gap j h₁ h₂
    by_cases hany : ∃ c ∈ D.Γ.E, c ⊆ connectedComponentIn Y x
    · obtain ⟨c₀, hc₀, hc₀X⟩ := hany
      obtain ⟨j₀, hj₁, hj₂, rfl, i₀, hi₀, hg₁, hg₂⟩ := hgap c₀ hc₀ hc₀X
      refine ⟨i₀, by omega, fun c hc₁ hc₂ hle' ↦ ?_⟩
      obtain ⟨j, h₁, h₂, rfl, i, hi', hg₃, hg₄⟩ := hgap c hc₁ hc₂
      rcases Nat.lt_trichotomy i i₀ with h' | rfl | h'
      · exact hsep h₁ hj₂ hc₂ hc₀X h' hi₀ hg₄ hg₁
      · exact hP i hi' j hg₃ hg₄ ⟨by omega, hle'⟩
      · exact hsep hj₁ h₂ hc₀X hc₂ h' hi' hg₂ hg₃
    · exact ⟨0, by omega, fun c hc₁ hc₂ ↦ absurd ⟨c, hc₁, hc₂⟩ hany⟩
  · rw [feastOrder, dite_eq_left hfinF]
    calc ∑ F ∈ hfinF.toFinset, F.E.ncard / 2 ≤ hfinF.toFinset.card • n :=
          Finset.sum_le_card_nsmul _ _ _ fun F hF ↦ by
            have := (hbite F (hfinF.mem_toFinset.1 hF)).2
            omega
      _ ≤ (m + 1) * n := by
        rw [← ncard_eq_toFinset_card _ hfinF, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (by omega)

/-- **Graph Minors XIX, (11.2)** (page 358): "If $(\Gamma, \phi, \lambda, \mathscr{T}) \in
\mathscr{D}$ is $(n, (\omega_1, \dots,
\omega_m))$-flawed on $S$, then there is a feast of order $\le (m + 1)n$." We also say which pole,
and that
each bite has `½|E(F)| ≤ n`. -/
theorem theorem_11_2_proof {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} (hn : 4
  ≤ n) {ω : List β} (hω : ω ≠ []) (hfl : D.IsFlawedOnSide side n ω) :
    ∃ (r : Shat) (Θ : Set S), Θ ∈ cuffs S ∧ side ⊆ Θ ∧ r ∈ D.rad.poles ∧ D.rad.regionOf r
      = cap.cuffDisc Θ ∧ ∃ ℱ, D.IsFeast r side ω ℱ ∧ feastOrder ℱ ≤ (ω.length + 1) * n ∧
      ∀ F ∈ ℱ, F.E.ncard ≤ 2 * n := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  set m := ω.length with hm
  have hm1 : 1 ≤ m := List.length_pos_iff.2 hω
  obtain ⟨hrep, hdist, hnd, hnf, hno⟩ := hfl
  set N := (m + 1) * n with hNdef
  have hnN : 2 * n ≤ N := by rw [hNdef]; nlinarith
  have hrepN : N < D.rep := by nlinarith
  have hd : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → N < D.vDist r₁ r₂ := by
    intro r₁ h₁ r₂ h₂ hne
    by_contra hle
    exact hnd ⟨hrepN, hdist, r₁, h₁, r₂, h₂, hne, not_lt.1 hle⟩
  have hfree : ∀ C, ¬ D.IsFreeCircuit N C := fun C hC ↦ hnf ⟨hrepN, hd, C, hC⟩
  obtain ⟨Θ, hΘ, f, a, b, k, t, e, hsΘ, hE⟩ := exists_sideEdges hS χ D.P.fits hside
  obtain ⟨r, hr, hrd, hreg⟩ := D.rad.exists_pole hS hΘ
  refine ⟨r, Θ, hΘ, hsΘ, hr, hreg, ?_⟩
  have hshape : ∀ {F}, D.IsBiteAt r F → F.E.ncard ≤ 2 * n → ∃ v₁ v₂ Β L A A' Di Do, D.IsBiteShape r
    Θ F v₁ v₂ Β L A A' Di Do := fun hb hc ↦
    bite_shape_of_far hS h3 hrepN hd hb.is_circuit (by omega) hr hΘ hreg hb.rstar_mem
  let J : Drawing Shat → Set S := fun F ↦ cap.emb ⁻¹' D.biteArc r F
  let Nr : ℕ → ℕ → Prop := fun i j ↦ ∃ F, D.IsBiteAt r F ∧ F.E.ncard ≤ 2 * n ∧ ∀ l, i ≤ l → l ≤ j
    → cap.emb '' e l ⊆ D.ins F
  let P : ℕ → ℕ → Prop := fun h j ↦ ∃ hh : h < ω.length, (χ.ΩS side).le ω[h] (D.P.φ (e j))
  have hmono : ∀ i j i' j', i ≤ i' → i' ≤ j' → j' ≤ j → Nr i j → Nr i' j' := by
    rintro i j i' j' h₁ - h₃ ⟨F, hb, hc, hl⟩
    exact ⟨F, hb, hc, fun l h₄ h₅ ↦ hl l (by omega) (by omega)⟩
  have hedgeΘ : ∀ {l}, l ≤ k + 1 → e l ⊆ Θ := by
    intro l hl z hz
    have hem := hE.mem l hl
    obtain ⟨y, -⟩ := (⟨z, hz⟩ : (e l).Nonempty)
    rcases Nat.eq_zero_or_pos l with rfl | hl₀
    · obtain ⟨d, -, -, hd'⟩ := hE.e_zero
      rw [hd'] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact cuffAngle_mem f u
    · rcases eq_or_ne l (k + 1) with rfl | hne
      · obtain ⟨d, -, -, hd'⟩ := hE.e_last
        rw [hd'] at hz
        obtain ⟨u, -, rfl⟩ := hz
        exact cuffAngle_mem f u
      · exact hsΘ (hE.subset_side hl₀ (by omega) hz)
  have hself : ∀ i ≤ k + 1, Nr i i := fun i hi ↦ by
    obtain ⟨F, hb, h6, hsub⟩ := exists_bite_of_edge hS (by nlinarith)
      (by omega) hfree hside hsΘ hΘ hr hreg (hE.mem i hi) (hedgeΘ hi)
    exact ⟨F, hb, by omega, fun l h₁ h₂ ↦ by
      obtain rfl : l = i := by omega
      exact hsub⟩
  have hstart : ¬ Nr 0 (k + 1) := by
    rintro ⟨F, hb, hc, hl⟩
    refine hfree F ⟨hb.is_circuit, by omega, Or.inl ⟨side, hside, ?_⟩⟩
    have hlt : F.E.ncard < 2 * D.rep := hb.card_lt
    have hcl : IsClosed (cap.emb ⁻¹' D.ins F) := (D.ins_spec hb.is_circuit
      hlt).2.2.1.isClosed.preimage cap.isEmbedding.continuous
    have := hE.side_subset_of_closed hcl fun l h₁ h₂ ↦ image_subset_iff.1 (hl l (by omega)
      (by omega))
    exact image_subset_iff.2 this
  -- A bite with two edges in it covers what lies between them.
  have hbetween : ∀ {F i j}, D.IsBiteAt r F → F.E.ncard ≤ 2 * n → 1 ≤ i → i < j → j ≤ k
    → cap.emb '' e i ⊆ D.ins F → cap.emb '' e j ⊆ D.ins F → Nr i j ∨ (Nr 0 i ∧ Nr j (k + 1)) := by
    intro F i j hb hc hi hij hj h₁ h₂
    obtain ⟨v₁, v₂, Β, L, A, A', Di, Do, hsh⟩ := hshape hb hc
    have hmem := fun l (hl : l ≤ k + 1) (hs : cap.emb '' e l ⊆ D.ins F) ↦ image_subset_iff.1
      (hsh.edge_subset hS (hE.mem l hl) (hedgeΘ hl) hs)
    have hJc : J F ⊆ Θ := fun x hx ↦ by
      obtain ⟨y, hy, he⟩ := (hsh.biteArc_subset hS hx).2
      exact cap.isEmbedding.injective he ▸ hy
    have hin : ∀ {l}, e l ⊆ J F → cap.emb '' e l ⊆ D.ins F := fun hl ↦ by
      rintro _ ⟨z, hz, rfl⟩
      exact (hsh.biteArc_subset hS (hl hz)).1
    rcases hE.between (hsh.isPreconnected_biteArc hS) hJc hi hij hj (hmem i (by omega) h₁) (hmem j
      (by omega) h₂) with hc' | ⟨hc₁, hc₂⟩
    · exact Or.inl ⟨F, hb, hc, fun l h₃ h₄ ↦ hin (hc' l h₃ h₄)⟩
    · exact Or.inr ⟨⟨F, hb, hc, fun l _ h₄ ↦ hin (hc₁ l h₄)⟩, ⟨F, hb, hc,
        fun l h₃ h₄ ↦ hin (hc₂ l h₃ h₄)⟩⟩
  have hbetween' : ∀ {F i s}, D.IsBiteAt r F → F.E.ncard ≤ 2 * n → 1 ≤ i → i ≤ k
    → s ∈ χ.Φ.shortSides → s ⊆ Θ → cap.emb '' e i ⊆ D.ins F → cap.emb '' s ⊆ D.ins F →
      Nr i (k + 1) ∨ Nr 0 i := by
    intro F i s hb hc hi hik hs hsΘ' h₁ h₂
    obtain ⟨v₁, v₂, Β, L, A, A', Di, Do, hsh⟩ := hshape hb hc
    have hsΓ := D.P.fits.short_sides hs
    have hJc : J F ⊆ Θ := fun x hx ↦ by
      obtain ⟨y, hy, he⟩ := (hsh.biteArc_subset hS hx).2
      exact cap.isEmbedding.injective he ▸ hy
    have hin : ∀ {l}, e l ⊆ J F → cap.emb '' e l ⊆ D.ins F := fun hl ↦ by
      rintro _ ⟨z, hz, rfl⟩
      exact (hsh.biteArc_subset hS (hl hz)).1
    rcases hE.between_short (hsh.isPreconnected_biteArc hS) hJc hi hik (image_subset_iff.1
      (hsh.edge_subset hS (hE.mem i (by omega)) (hedgeΘ (by omega)) h₁)) hs hsΓ hsΘ'
      (image_subset_iff.1 (hsh.edge_subset hS hsΓ hsΘ' h₂)) with hc' | hc'
    · exact Or.inl ⟨F, hb, hc, fun l h₃ h₄ ↦ hin (hc' l h₃ h₄)⟩
    · exact Or.inr ⟨F, hb, hc, fun l _ h₄ ↦ hin (hc' l h₄)⟩
  have hnochain : ∀ a b, ¬ SideChain Nr P k m a b := by
    intro a' b' hc
    have hstep : ∀ i < m, b' i < b' (i + 1) := fun i hi ↦ (hc.b_le_a i hi).trans_lt (hc.a_lt_b i hi)
    have hlt : ∀ {i j}, i < j → j ≤ m → b' i < b' j := by
      intro i j hij hj
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
        · exact (ih h' (by omega)).trans (hstep j (by omega))
        · exact hstep i (by omega)
    have hle : ∀ {i j}, i ≤ j → j ≤ m → b' i ≤ b' j := fun {i j} hij hj ↦ by
      rcases Nat.lt_or_eq_of_le hij with h' | rfl
      · exact (hlt h' hj).le
      · exact le_rfl
    have hkb : b' m ≤ k := by have := hc.lt_end; omega
    have hb1 : ∀ i < m, 1 ≤ b' (i + 1) := fun i hi ↦ by
      have := hle (show 0 + 1 ≤ i + 1 by omega) (by omega)
      have h₁ := hstep 0 (by omega)
      rw [hc.b_zero] at h₁
      omega
    have hbk : ∀ i < m, b' (i + 1) ≤ k := fun i hi ↦ (hle (by omega) (by omega)).trans hkb
    let g : Fin ω.length → Set S := fun i ↦ e (b' (i.1 + 1))
    refine hno r hr Θ hΘ hrd hsΘ ⟨g, a, b, ⟨hE.head, hE.last, ?_, ?_, ?_⟩, ?_⟩
    · intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h) : i.1 ≠ j.1) with h' | h'
      · exact hE.injOn_edges (hb1 i.1 i.2) (hlt (by omega) (by have := j.2; omega))
          (hbk j.1 j.2) hij
      · exact hE.injOn_edges (hb1 j.1 j.2) (hlt (by omega) (by have := i.2; omega))
          (hbk i.1 i.2) hij.symm
    · intro i
      exact ⟨hE.mem _ (Nat.le_succ_of_le (hbk i.1 i.2)),
        hE.subset_side (hb1 i.1 i.2) (hbk i.1 i.2)⟩
    · intro i j hij x hx y hy
      have hij' : i.1 < j.1 := hij
      have hj := j.2
      exact hE.inOrder (hb1 i.1 i.2) (hlt (by omega) (by omega)) (hbk j.1 j.2) hx hy
    · refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_, fun i s hs hsc ↦ ?_⟩
      · obtain ⟨_, hh⟩ := hc.label i.1 i.2
        exact hh
      · by_contra hnl
        have hij' : i.1 < j.1 := hij
        obtain ⟨F, hb, h₁, h₂, hcard⟩ := exists_bite_of_dist_le (by omega) (not_lt.1 hnl)
        have hj' := j.2
        rcases hbetween hb hcard (hb1 i.1 i.2) (hlt (by omega) (by omega))
          (hbk j.1 j.2) h₁ h₂ with hc₁ | ⟨-, hc₂⟩
        · exact hc.far j.1 j.2 (hmono _ _ _ _ (hle (by omega) (by omega))
            (hstep j.1 j.2).le le_rfl hc₁)
        · exact hc.far_end (hmono _ _ _ _ (hle (by omega) le_rfl) (by omega) le_rfl hc₂)
      · by_contra hnl
        have hi' := i.2
        obtain ⟨F, hb, h₁, h₂, hcard⟩ := exists_bite_of_dist_le (by omega) (not_lt.1 hnl)
        rcases hbetween' hb hcard (hb1 i.1 i.2) (hbk i.1 i.2) hs hsc h₁ h₂ with hc₁ | hc₁
        · exact hc.far_end (hmono _ _ _ _ (hle (by omega) le_rfl) (by omega) le_rfl hc₁)
        · have h₀ := hc.far 0 (by omega)
          rw [hc.b_zero] at h₀
          exact h₀ (hmono _ _ _ _ le_rfl (by omega) (hle (by omega) (by omega)) hc₁)
  have feast_from_chain : ∃ ℱ, D.IsFeast r side ω ℱ ∧ feastOrder ℱ ≤ N ∧
      ∀ F ∈ ℱ, F.E.ncard ≤ 2 * n := by
    exact exists_feast_of_chain_cover (S := S) (Shat := Shat) (cap := cap) (β := β) (χ := χ) (D :=
      D) hS (side := side) (n := n) (ω := ω)  hm1  Θ f a b k t e hsΘ hE r hshape   hmono
      hedgeΘ hself hstart hnochain
  exact feast_from_chain

end TangleDatum

end GraphMinor.GM19

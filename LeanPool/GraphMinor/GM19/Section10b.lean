/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10a

/-!
# Graph Minors XIX, (10.1), the second assertion

A representativeness flaw `F` that meets one cuff twice must pass through the pole of the cuff,
since otherwise the two spokes of the pole give a lighter flaw. If `F` meets two cuffs then two
poles
are close together.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

section Walks

variable {T : Type} [TopologicalSpace T] [T2Space T] {P : Drawing T} {a b : T}

omit [T2Space T] in
/-- A path starts with one edge, and this is the only edge of the path at the start. If this edge
does not reach the end of the path, then the path has a second edge. -/
theorem path_first (hP : P.IsPathBetween a b) (hab : a ≠ b) :
    ∃ e ∈ P.E, ∃ x, P.toGraph.IsLink e a x ∧ (∀ f ∈ P.E, a ∈ closure f → f = e) ∧
      (x ≠ b → ∃ f ∈ P.E, f ≠ e ∧ ∃ y, P.toGraph.IsLink f x y) := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  cases W with
  | nil h => exact absurd rfl hab
  | @cons _ x _ e h r =>
    have hsim : (GraphWalk.cons h r).support.Nodup := hW
    simp only [GraphWalk.support_cons, List.nodup_cons] at hsim
    have hanot : ∀ f ∈ r.edges, a ∉ closure f := fun f hf ha ↦
      hsim.1 (mem_support_of_mem_edges r hf ha h.2.1)
    refine ⟨e, h.1, x, h, fun f hf ha ↦ ?_, fun hxb ↦ ?_⟩
    · rw [hE] at hf
      simp only [GraphWalk.edges_cons, mem_ofPred_eq, List.mem_cons] at hf
      rcases hf with rfl | hf
      · rfl
      · exact absurd ha (hanot f hf)
    · cases r with
      | nil h' => exact absurd rfl hxb
      | @cons _ y _ f h' r' =>
        have hf : f ∈ (GraphWalk.cons h' r').edges := by simp
        refine ⟨f, hE ▸ (by simp : f ∈ (GraphWalk.cons h (GraphWalk.cons h' r')).edges), ?_, y, h'⟩
        rintro rfl
        have ha : a ∈ closure f := by
          have : a ∈ closure f ∩ P.V := by rw [h.2.2.2]; exact Or.inl rfl
          exact this.1
        exact hanot f hf ha

end Walks

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}

omit [T2Space S] [T2Space Shat] in
/-- An edge of `Γ*` at a vertex of `R*` goes to a vertex of `Γ`. -/
theorem RadialDrawing.link_cases (rad : RadialDrawing cap Γ) {e : Set Shat} {p x : Shat}
    (hl : rad.G.toGraph.IsLink e p x) (hp : p ∈ rad.Rstar) :
    ∃ v ∈ Γ.V, x = cap.emb v ∧ closure e ∩ rad.G.V = {cap.emb v, p} := by
  obtain ⟨v, hv, w, hw, hset⟩ := rad.edge_ends hl.1
  have hne : cap.emb v ≠ w := fun h ↦ hw.2 (h ▸ mem_image_of_mem _ hv)
  have hpm : p ∈ ({cap.emb v, w} : Set Shat) := hset ▸ hl.2.2.2 ▸ Or.inl rfl
  have hxm : x ∈ ({cap.emb v, w} : Set Shat) := hset ▸ hl.2.2.2 ▸ Or.inr rfl
  have hvm : cap.emb v ∈ ({p, x} : Set Shat) := hl.2.2.2 ▸ hset ▸ Or.inl rfl
  have hpw : p = w := by
    rcases hpm with h | h
    · exact absurd (h ▸ mem_image_of_mem _ hv) hp.2
    · exact h
  subst hpw
  have hvx : cap.emb v = x := by
    rcases hvm with h | h
    · exact absurd h hne
    · exact h
  exact ⟨v, hv, hvx.symm, hset⟩

section Radial

variable (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
include hS h3

/-- A vertex of `R*` on a circuit of `Γ*` has exactly two edges in the circuit, and they go to
different vertices. -/
theorem RadialDrawing.circuit_edges (rad : RadialDrawing cap Γ) {F : Drawing Shat}
    (hF : F.IsCircuitOf rad.G) {p : Shat} (hp : p ∈ F.V) (hpR : p ∈ rad.Rstar) :
    ∃ (e₁ e₂ : Set Shat) (v₁ v₂ : S), e₁ ∈ F.E ∧ e₂ ∈ F.E ∧ v₁ ∈ Γ.V ∧ v₂ ∈ Γ.V ∧ v₁ ≠ v₂ ∧
      closure e₁ ∩ rad.G.V = {cap.emb v₁, p} ∧ closure e₂ ∩ rad.G.V = {cap.emb v₂, p} ∧
      ∀ e ∈ F.E, p ∈ closure e → e = e₁ ∨ e = e₂ := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨e, he⟩ := IsCircuit.E_nonempty hF.2
  obtain ⟨v, hv, w, hw, hset⟩ := rad.edge_ends (hF.1.2 he)
  have hqF : cap.emb v ∈ F.V := by
    have hm : cap.emb v ∈ closure e ∩ rad.G.V := by rw [hset]; exact Or.inl rfl
    exact mem_V_of_mem_U hF.1 (F.closure_subset_U he hm.1) hm.2
  have hne : p ≠ cap.emb v := fun h ↦ hpR.2 (h ▸ mem_image_of_mem _ hv)
  obtain ⟨A, B, hA, hB, hAs, hBs, -, -, hAB, hd, hsup⟩ := hF.2.exists_two_paths hp hqF hne
  obtain ⟨e₁, he₁, x₁, hl₁, hu₁, -⟩ := path_first hA hne
  obtain ⟨e₂, he₂, x₂, hl₂, hu₂, -⟩ := path_first hB hne
  have hAG := hAs.trans hF.1
  have hBG := hBs.trans hF.1
  obtain ⟨v₁, hv₁, -, hs₁⟩ := rad.link_cases ((hAG.isLink_iff he₁).mp hl₁) hpR
  obtain ⟨v₂, hv₂, -, hs₂⟩ := rad.link_cases ((hBG.isLink_iff he₂).mp hl₂) hpR
  have heq : ∀ e ∈ F.E, p ∈ closure e → e = e₁ ∨ e = e₂ := by
    intro f hf hpf
    rw [← hsup, Drawing.sup_E hAs hBs] at hf
    rcases hf with hf | hf
    · exact Or.inl (hu₁ f hf hpf)
    · exact Or.inr (hu₂ f hf hpf)
  refine ⟨e₁, e₂, v₁, v₂, hAs.2 he₁, hBs.2 he₂, hv₁, hv₂, ?_, hs₁, hs₂, heq⟩
  rintro rfl
  have := rad.edge_unique hS h3 (hAG.2 he₁) (hBG.2 he₂) hv₁ hpR hs₁ hs₂
  exact disjoint_left.mp hd he₁ (this ▸ he₂)

omit hS h3 in
omit [T2Space S] in
omit [T2Space Shat] in
/-- A point of `F.U` on `bd(Σ)` is a vertex of `Γ` on a cuff, and a vertex of `F`. -/
theorem RadialDrawing.bd_point (rad : RadialDrawing cap Γ) {F : Drawing Shat}
    (hF : F.IsSubdrawing rad.G) {v : S} (hv : v ∈ bd S) (hvF : cap.emb v ∈ F.U) :
    v ∈ Γ.V ∧ cap.emb v ∈ F.V ∧ ∃ Θ ∈ cuffs S, v ∈ Θ := by
  have : ConnectedSpace Shat := cap.connected
  have hm : cap.emb v ∈ Γ.hatU cap ∩ rad.G.U :=
    ⟨mem_image_of_mem _ (Γ.bd_subset hv), hF.U_subset hvF⟩
  rw [rad.isPreRadial.1] at hm
  obtain ⟨z, hz, hzv⟩ := hm
  obtain rfl := cap.isEmbedding.injective hzv
  exact ⟨hz, mem_V_of_mem_U hF hvF (rad.isPreRadial.2.1 (mem_image_of_mem _ hz)),
    connectedComponentIn (bd S) z, ⟨z, hv, rfl⟩, mem_connectedComponentIn hv⟩

/-- Two vertices of a circuit on different cuffs give a path of `Γ*` between two poles, of length at
most half the circuit plus two. -/
theorem RadialDrawing.dist_le_of_two_cuffs (rad : RadialDrawing cap Γ) {F : Drawing Shat}
    (hF : F.IsCircuitOf rad.G) {v₁ v₂ : S} {Θ₁ Θ₂ : Set S} (hΘ₁ : Θ₁ ∈ cuffs S)
    (hΘ₂ : Θ₂ ∈ cuffs S) (hne : Θ₁ ≠ Θ₂) (h₁ : v₁ ∈ Θ₁) (h₂ : v₂ ∈ Θ₂) (hv₁ : v₁ ∈ Γ.V)
    (hv₂ : v₂ ∈ Γ.V) (hF₁ : cap.emb v₁ ∈ F.V) (hF₂ : cap.emb v₂ ∈ F.V) :
    Painting.dist rad * 4 ≤ ((F.E.ncard + 4 : ℕ) : ℕ∞) := by
  classical
  have hvne : cap.emb v₁ ≠ cap.emb v₂ := fun h ↦ by
    have h' := cap.isEmbedding.injective h
    exact disjoint_left.mp (cuffs_disjoint hΘ₁ hΘ₂ hne) h₁ (h' ▸ h₂)
  obtain ⟨p₁, hp₁, hp₁Θ, hr₁⟩ := rad.exists_pole hΘ₁
  obtain ⟨p₂, hp₂, hp₂Θ, hr₂⟩ := rad.exists_pole hΘ₂
  have hpne : p₁ ≠ p₂ := fun h ↦ disjoint_left.mp (cap.cuffDisc_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne)
    (subset_closure hp₁Θ) (subset_closure (h ▸ hp₂Θ))
  obtain ⟨e₁, he₁, hs₁⟩ := rad.exists_pole_edge hS h3 hp₁ hΘ₁ hr₁ hv₁ h₁
  obtain ⟨e₂, he₂, hs₂⟩ := rad.exists_pole_edge hS h3 hp₂ hΘ₂ hr₂ hv₂ h₂
  obtain ⟨A, B, hA, hB, hAs, hBs, -, -, -, hd, hsup⟩ := hF.2.exists_two_paths hF₁ hF₂ hvne
  have hcard : A.E.ncard + B.E.ncard = F.E.ncard := by
    rw [← ncard_union_eq hd A.finite_edges B.finite_edges]
    conv_rhs => rw [← hsup, Drawing.sup_E hAs hBs]
  -- One of the two paths has at most half the edges.
  obtain ⟨X, hX, hXs, hXc⟩ : ∃ X : Drawing Shat, X.IsPathBetween (cap.emb v₁) (cap.emb v₂) ∧
      X.IsSubdrawing F ∧ 2 * X.E.ncard ≤ F.E.ncard := by
    by_cases h : A.E.ncard ≤ B.E.ncard
    · exact ⟨A, hA, hAs, by omega⟩
    · exact ⟨B, hB, hBs, by omega⟩
  obtain ⟨W, hW, hWV, hWE⟩ := hX
  obtain ⟨W₁, -, hW₁⟩ := (hXs.trans hF.1).exists_walk_up W
  have hl₁ : rad.G.toGraph.IsLink e₁ p₁ (cap.emb v₁) :=
    ⟨he₁, hp₁.1.1, rad.isPreRadial.2.1 (mem_image_of_mem _ hv₁), by rw [hs₁, pair_comm]⟩
  have hl₂ : rad.G.toGraph.IsLink e₂ (cap.emb v₂) p₂ :=
    ⟨he₂, rad.isPreRadial.2.1 (mem_image_of_mem _ hv₂), hp₂.1.1, hs₂⟩
  let W₂ : GraphWalk rad.G.toGraph p₁ p₂ :=
    (GraphWalk.cons hl₁ W₁).append (GraphWalk.cons hl₂ (.nil hp₂.1.1))
  obtain ⟨W₃, hW₃, -, hW₃E⟩ := GM11.GraphWalk.exists_isSimple W₂
  set P := walkDrawing rad.G W₃ with hPdef
  have hPpath : Drawing.IsPathOf P rad.G p₁ p₂ :=
    ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hW₃⟩
  have hsubE : P.E ⊆ {e₁, e₂} ∪ X.E := by
    intro e he
    rw [hPdef, walkDrawing_E] at he
    have := hW₃E e he
    simp only [W₂, GraphWalk.edges_append, GraphWalk.edges_cons, List.mem_append, List.mem_cons,
      hW₁] at this
    have hX : e ∈ W.edges → e ∈ X.E := fun h ↦ hWE ▸ h
    rcases this with (rfl | h) | (rfl | h)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (hX h)
    · exact Or.inl (Or.inr rfl)
    · simp [GraphWalk.edges] at h
  have hPc : P.E.ncard ≤ 2 + X.E.ncard := by
    refine (ncard_le_ncard hsubE ((toFinite _).union X.finite_edges)).trans ?_
    refine (ncard_union_le _ _).trans ?_
    have := ncard_insert_le e₁ ({e₂} : Set (Set Shat))
    simp only [ncard_singleton] at this
    omega
  have hdist : Painting.dist rad ≤ ((P.E.ncard / 2 : ℕ) : ℕ∞) :=
    sInf_le ⟨P, p₁, p₂, hp₁, hp₂, hpne, hPpath, rfl⟩
  calc Painting.dist rad * 4 ≤ ((P.E.ncard / 2 : ℕ) : ℕ∞) * 4 := by gcongr
    _ ≤ ((F.E.ncard + 4 : ℕ) : ℕ∞) := by
      have : (P.E.ncard / 2) * 4 ≤ F.E.ncard + 4 := by omega
      exact_mod_cast this

omit hS h3 in
omit [T2Space S] [T2Space Shat] in
/-- An edge of `Γ*` at a vertex of `Γ` goes to a vertex of `R*`. -/
theorem RadialDrawing.link_cases' (rad : RadialDrawing cap Γ) {e : Set Shat} {v : S} {x : Shat}
    (hl : rad.G.toGraph.IsLink e (cap.emb v) x) (hv : v ∈ Γ.V) :
    x ∈ rad.Rstar ∧ closure e ∩ rad.G.V = {cap.emb v, x} := by
  obtain ⟨u, hu, w, hw, hset⟩ := rad.edge_ends hl.1
  have hne : cap.emb u ≠ w := fun h ↦ hw.2 (h ▸ mem_image_of_mem _ hu)
  have hpm : cap.emb v ∈ ({cap.emb u, w} : Set Shat) := hset ▸ hl.2.2.2 ▸ Or.inl rfl
  have hxm : w ∈ ({cap.emb v, x} : Set Shat) := hl.2.2.2 ▸ hset ▸ Or.inr rfl
  have hvu : cap.emb v = cap.emb u := by
    rcases hpm with h | h
    · exact h
    · exact absurd (h ▸ mem_image_of_mem _ hv) hw.2
  have hwx : w = x := by
    rcases hxm with h | h
    · exact absurd (hvu.symm.trans h.symm) hne
    · exact h
  subst hwx
  exact ⟨hw, hl.2.2.2⟩

omit hS h3 in
omit [T2Space S] [T2Space Shat] in
/-- A set of edges of a subdrawing of `Γ*` is no heavier than the subdrawing. -/
theorem TieBreaker.weight_subset (tb : TieBreaker rad) {X : Drawing Shat}
    (hX : X.IsSubdrawing rad.G) {Y : Set (Set Shat)} (hY : Y ⊆ X.E) :
    ∑ᶠ e ∈ Y, tb.wtE e ≤ tb.weightSub X := by
  have hdis : Disjoint Y (X.E \ Y) := disjoint_left.mpr fun e h₁ h₂ ↦ h₂.2 h₁
  have hsplit : tb.weightSub X = ∑ᶠ e ∈ Y, tb.wtE e + ∑ᶠ e ∈ X.E \ Y, tb.wtE e := by
    rw [← finsum_mem_union hdis (X.finite_edges.subset hY) X.finite_edges.sdiff,
      union_sdiff_cancel hY]
    rfl
  have hnn : 0 ≤ ∑ᶠ e ∈ X.E \ Y, tb.wtE e :=
    finsum_nonneg fun e ↦ finsum_nonneg fun he ↦ (tb.wtE_pos e (hX.2 he.1)).le
  linarith

end Radial

namespace TangleDatum

variable {α : Type w} {χ : ColourScheme S α} {D : TangleDatum cap χ} {F : Drawing Shat}

variable (hS : IsSurface S) (h3' : D.P.Γ.IsInternallyThreeConnected)
include hS h3'

/-- No path through a pole improves `F`. This is what the proofs of (10.1) and of the text before
(10.4) need of the choice of
`F`: "Let `Q` be a path of `Γ*`", and "one of $F_1 \cup Q, F_2 \cup Q$ contradicts the choice of
$F$". -/
def ThetaFree (D : TangleDatum cap χ) (F : Drawing Shat) : Prop :=
  ∀ {F₁ F₂ Q : Drawing Shat} {a b : Shat}, TwoPaths D.rad.G F F₁ F₂ Q a b →
    (∃ p ∈ D.rad.poles, p ∈ Q.V) →
    Q.E.ncard ≤ F₁.E.ncard → D.tb.weightSub Q < D.tb.weightSub F₁ → Q.E.ncard ≤ F₂.E.ncard →
    D.tb.weightSub Q < D.tb.weightSub F₂ → False

/-- The claim in the proof of the second assertion of (10.1): if `F` meets a cuff in two vertices
`v₁, v₂`, and meets no other pole, then the edge from `v₁` to the pole is in `F`. "For suppose that
$e_1 \notin E(F)$. Let $u = r^*$ if $r^* \in V(F)$, and $u = v_2$ if $r^*
\notin V(F)$. Let $Q$ be a path of $\Gamma^*$ between $v_1$ and $u$ with $E(Q) \subseteq
\{e_1, e_2\}$." -/
theorem spoke_mem (hF : F.IsCircuitOf D.rad.G) (hθ : ThetaFree D F)
    {p : Shat} (hp : p ∈ D.rad.poles) (honly : ∀ p' ∈ D.rad.poles, p' ∈ F.V → p' = p)
    {v₁ v₂ : S} (hv₁ : v₁ ∈ D.P.Γ.V) (hv₂ : v₂ ∈ D.P.Γ.V) (hne : v₁ ≠ v₂)
    (hF₁ : cap.emb v₁ ∈ F.V) (hF₂ : cap.emb v₂ ∈ F.V) {e₁ e₂ : Set Shat} (he₁ : e₁ ∈ D.rad.G.E)
    (he₂ : e₂ ∈ D.rad.G.E) (hs₁ : closure e₁ ∩ D.rad.G.V = {cap.emb v₁, p})
    (hs₂ : closure e₂ ∩ D.rad.G.V = {cap.emb v₂, p}) : e₁ ∈ F.E := by
  classical
  have : ConnectedSpace Shat := cap.connected
  by_contra hn
  set G := D.rad.G with hG
  have hvG : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ∈ G.V := fun hv ↦
    D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv)
  have hpG : p ∈ G.V := hp.1.1
  have hvp : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ≠ p := fun hv h ↦ hp.1.2 (h ▸ mem_image_of_mem _ hv)
  obtain ⟨Θ, hΘ, hreg, hpΘ⟩ := D.rad.pole_cases hp
  have hnr₁ := (D.rad.pole_edge he₁ hp hΘ hreg hs₁).1
  have hnr₂ := (D.rad.pole_edge he₂ hp hΘ hreg hs₂).1
  have hrange : ∀ f ∈ F.E, p ∉ closure f → f ⊆ range cap.emb := by
    intro f hf hpf
    obtain ⟨v, -, w, hw, hset⟩ := D.rad.edge_ends (hF.1.2 hf)
    have hwm : w ∈ closure f ∩ G.V := by rw [hset]; exact Or.inr rfl
    have hwF : w ∈ F.V := mem_V_of_mem_U hF.1 (F.closure_subset_U hf hwm.1) hwm.2
    refine D.rad.edge_subset_range (hF.1.2 hf) hw (fun hwp ↦ ?_) hset
    exact hpf (honly w hwp hwF ▸ hwm.1)
  have hlt₁ : ∀ f ∈ F.E, p ∉ closure f → D.tb.wtE e₁ < D.tb.wtE f := fun f hf hpf ↦
    D.tb.cuff_lt_internal e₁ he₁ f (hF.1.2 hf) hnr₁ (hrange f hf hpf)
  have hlt₂ : ∀ f ∈ F.E, p ∉ closure f → D.tb.wtE e₂ < D.tb.wtE f := fun f hf hpf ↦
    D.tb.cuff_lt_internal e₂ he₂ f (hF.1.2 hf) hnr₂ (hrange f hf hpf)
  have hvne : cap.emb v₁ ≠ cap.emb v₂ := fun h ↦ hne (cap.isEmbedding.injective h)
  have hl₁ : G.toGraph.IsLink e₁ (cap.emb v₁) p := ⟨he₁, hvG hv₁, hpG, hs₁⟩
  have hl₁' : G.toGraph.IsLink e₁ p (cap.emb v₁) := ⟨he₁, hpG, hvG hv₁, by rw [hs₁, pair_comm]⟩
  have hl₂ : G.toGraph.IsLink e₂ p (cap.emb v₂) := ⟨he₂, hpG, hvG hv₂, by rw [hs₂, pair_comm]⟩
  by_cases hpF : p ∈ F.V
  · -- The pole is on `F`, and `Q` is the edge `e₁`.
    obtain ⟨A, B, hA, hB, hAs, hBs, -, -, hAB, hd, hsup⟩ :=
      hF.2.exists_two_paths hF₁ hpF (hvp hv₁)
    let W : GraphWalk G.toGraph (cap.emb v₁) p := .cons hl₁ (.nil hpG)
    have hWs : W.IsSimple := by
      simp [GraphWalk.IsSimple, W, GraphWalk.support, hvp hv₁]
    have hQV : (walkDrawing G W).V = {cap.emb v₁, p} := by
      rw [walkDrawing_V]; ext x; simp [W, GraphWalk.support]
    have hQE : (walkDrawing G W).E = {e₁} := by
      rw [walkDrawing_E]; ext x; simp [W, GraphWalk.edges]
    have ht : TwoPaths G F A B (walkDrawing G W) (cap.emb v₁) p := by
      refine ⟨hvp hv₁, hF.1, ⟨hAs, hA⟩, ⟨hBs, hB⟩, ?_, ?_, hAB.le, hd,
        ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hWs⟩, ?_, ?_⟩
      · conv_lhs => rw [← hsup, Drawing.sup_V hAs hBs]
      · conv_lhs => rw [← hsup, Drawing.sup_E hAs hBs]
      · rw [hQV]; exact inter_subset_left
      · rw [hQE]; simpa using hn
    have side : ∀ {X : Drawing Shat}, X.IsPathBetween (cap.emb v₁) p → X.IsSubdrawing F →
        (walkDrawing G W).E.ncard ≤ X.E.ncard ∧
          D.tb.weightSub (walkDrawing G W) < D.tb.weightSub X := by
      intro X hX hXs
      obtain ⟨f, hf, x, hl, -, -⟩ := path_first hX (hvp hv₁)
      have hfF := hXs.2 hf
      have hlG := ((hXs.trans hF.1).isLink_iff hf).mp hl
      obtain ⟨hxR, hset⟩ := D.rad.link_cases' hlG hv₁
      have hpf : p ∉ closure f := by
        intro hc
        have hmem : p ∈ ({cap.emb v₁, x} : Set Shat) := hset ▸ ⟨hc, hpG⟩
        rcases hmem with h | h
        · exact hvp hv₁ h.symm
        · subst h
          exact hn (D.rad.edge_unique hS h3' he₁ (hF.1.2 hfF) hv₁ hxR hs₁ hset ▸ hfF)
      constructor
      · rw [hQE, ncard_singleton]
        exact (ncard_pos X.finite_edges).2 ⟨f, hf⟩
      · have h₁ : D.tb.weightSub (walkDrawing G W) = D.tb.wtE e₁ := by
          simp only [TieBreaker.weightSub, hQE, finsum_mem_singleton]
        have h₂ := D.tb.weight_subset (hXs.trans hF.1) (singleton_subset_iff.mpr hf)
        rw [finsum_mem_singleton] at h₂
        rw [h₁]
        exact lt_of_lt_of_le (hlt₁ f hfF hpf) h₂
    obtain ⟨c₁, w₁⟩ := side hA hAs
    obtain ⟨c₂, w₂⟩ := side hB hBs
    exact hθ ht ⟨p, hp, by rw [hQV]; simp⟩ c₁ w₁ c₂ w₂
  · -- The pole is not on `F`, and `Q` is the path through the pole.
    have hclo : ∀ f ∈ F.E, p ∉ closure f := fun f hf hc ↦
      hpF (mem_V_of_mem_U hF.1 (F.closure_subset_U hf hc) hpG)
    have hn₂ : e₂ ∉ F.E := fun h ↦ hclo e₂ h (by
      have : p ∈ closure e₂ ∩ G.V := by rw [hs₂]; exact Or.inr rfl
      exact this.1)
    have hene : e₁ ≠ e₂ := by
      rintro rfl
      have hm : cap.emb v₂ ∈ ({cap.emb v₁, p} : Set Shat) := hs₁ ▸ hs₂ ▸ Or.inl rfl
      rcases hm with h | h
      · exact hvne h.symm
      · exact hvp hv₂ h
    obtain ⟨A, B, hA, hB, hAs, hBs, -, -, hAB, hd, hsup⟩ := hF.2.exists_two_paths hF₁ hF₂ hvne
    let W : GraphWalk G.toGraph (cap.emb v₁) (cap.emb v₂) := .cons hl₁ (.cons hl₂ (.nil (hvG hv₂)))
    have hWs : W.IsSimple := by
      simp [GraphWalk.IsSimple, W, GraphWalk.support, hvp hv₁, hvne, (hvp hv₂).symm]
    have hQV : (walkDrawing G W).V = {cap.emb v₁, p, cap.emb v₂} := by
      rw [walkDrawing_V]; ext x; simp [W, GraphWalk.support]
    have hQE : (walkDrawing G W).E = {e₁, e₂} := by
      rw [walkDrawing_E]; ext x; simp [W, GraphWalk.edges]
    have ht : TwoPaths G F A B (walkDrawing G W) (cap.emb v₁) (cap.emb v₂) := by
      refine ⟨hvne, hF.1, ⟨hAs, hA⟩, ⟨hBs, hB⟩, ?_, ?_, hAB.le, hd,
        ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hWs⟩, ?_, ?_⟩
      · conv_lhs => rw [← hsup, Drawing.sup_V hAs hBs]
      · conv_lhs => rw [← hsup, Drawing.sup_E hAs hBs]
      · rw [hQV]
        rintro x ⟨rfl | rfl | rfl, hx⟩
        · exact Or.inl rfl
        · exact absurd hx hpF
        · exact Or.inr rfl
      · rw [hQE]
        refine disjoint_left.mpr ?_
        rintro _ (rfl | rfl) h
        · exact hn h
        · exact hn₂ h
    have side : ∀ {X : Drawing Shat}, X.IsPathBetween (cap.emb v₁) (cap.emb v₂) → X.IsSubdrawing F →
        (walkDrawing G W).E.ncard ≤ X.E.ncard ∧
          D.tb.weightSub (walkDrawing G W) < D.tb.weightSub X := by
      intro X hX hXs
      obtain ⟨f, hf, x, hl, -, hsec⟩ := path_first hX hvne
      have hlG := ((hXs.trans hF.1).isLink_iff hf).mp hl
      obtain ⟨hxR, -⟩ := D.rad.link_cases' hlG hv₁
      obtain ⟨f', hf', hff, -⟩ := hsec fun h ↦ hxR.2 (h ▸ mem_image_of_mem _ hv₂)
      have hfF := hXs.2 hf
      have hfF' := hXs.2 hf'
      have hsub : ({f, f'} : Set (Set Shat)) ⊆ X.E := by
        rintro _ (rfl | rfl)
        · exact hf
        · exact hf'
      constructor
      · rw [hQE, ncard_pair hene, ← ncard_pair hff.symm]
        exact ncard_le_ncard hsub X.finite_edges
      · have h₁ : D.tb.weightSub (walkDrawing G W) = D.tb.wtE e₁ + D.tb.wtE e₂ := by
          simp only [TieBreaker.weightSub, hQE]
          exact finsum_mem_pair hene
        have h₂ := D.tb.weight_subset (hXs.trans hF.1) hsub
        rw [finsum_mem_pair hff.symm] at h₂
        have := hlt₁ f hfF (hclo f hfF)
        have := hlt₂ f' hfF' (hclo f' hfF')
        rw [h₁]
        linarith
    obtain ⟨c₁, w₁⟩ := side hA hAs
    obtain ⟨c₂, w₂⟩ := side hB hBs
    exact hθ ht ⟨p, hp, by rw [hQV]; simp⟩ c₁ w₁ c₂ w₂

/-- The second assertion of (10.1). The third alternative `dist(Γ) ≤ ¼|E(F)| + 1` is written without
fractions. -/
theorem second_of_thetaFree (hF : F.IsCircuitOf D.rad.G) (hθ : ThetaFree D F) :
    ((F.U ∩ cap.emb '' bd S).ncard ≤ 1 ∧ F.U ⊆ range cap.emb) ∨
    ((F.U ∩ cap.emb '' bd S).ncard = 2 ∧ ¬ F.U ⊆ range cap.emb) ∨
    Painting.dist D.rad * 4 ≤ ((F.E.ncard + 4 : ℕ) : ℕ∞) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hsubbd : ∀ {Θ}, Θ ∈ cuffs S → Θ ⊆ bd S := by
    rintro _ ⟨y, -, rfl⟩
    exact connectedComponentIn_subset _ _
  by_cases htwo : ∃ (v₁ v₂ : S) (Θ₁ Θ₂ : Set S), Θ₁ ∈ cuffs S ∧ Θ₂ ∈ cuffs S ∧ Θ₁ ≠ Θ₂ ∧ v₁ ∈ Θ₁ ∧
      v₂ ∈ Θ₂ ∧ cap.emb v₁ ∈ F.U ∧ cap.emb v₂ ∈ F.U
  · obtain ⟨v₁, v₂, Θ₁, Θ₂, hΘ₁, hΘ₂, hne, h₁, h₂, hF₁, hF₂⟩ := htwo
    obtain ⟨hv₁, hV₁, -⟩ := D.rad.bd_point hF.1 (hsubbd hΘ₁ h₁) hF₁
    obtain ⟨hv₂, hV₂, -⟩ := D.rad.bd_point hF.1 (hsubbd hΘ₂ h₂) hF₂
    exact Or.inr (Or.inr (D.rad.dist_le_of_two_cuffs hS h3' hF hΘ₁ hΘ₂ hne h₁ h₂ hv₁ hv₂ hV₁ hV₂))
  have hsame : ∀ {v₁ v₂ : S} {Θ₁ Θ₂ : Set S}, Θ₁ ∈ cuffs S → Θ₂ ∈ cuffs S → v₁ ∈ Θ₁ → v₂ ∈ Θ₂ →
      cap.emb v₁ ∈ F.U → cap.emb v₂ ∈ F.U → Θ₁ = Θ₂ := by
    intro v₁ v₂ Θ₁ Θ₂ h₁ h₂ h₃ h₄ h₅ h₆
    by_contra hne
    exact htwo ⟨v₁, v₂, Θ₁, Θ₂, h₁, h₂, hne, h₃, h₄, h₅, h₆⟩
  have hBfin : (F.U ∩ cap.emb '' bd S).Finite := by
    refine (D.P.Γ.finite_V.image cap.emb).subset ?_
    rintro _ ⟨hx, v, hv, rfl⟩
    exact mem_image_of_mem _ (D.rad.bd_point hF.1 hv hx).1
  by_cases hpole : ∃ p ∈ D.rad.poles, p ∈ F.V
  · obtain ⟨p, hp, hpF⟩ := hpole
    obtain ⟨Θ, hΘ, hreg, hpΘ⟩ := D.rad.pole_cases hp
    obtain ⟨e₁, e₂, v₁, v₂, he₁, he₂, hv₁, hv₂, hne, hs₁, hs₂, huniq⟩ :=
      D.rad.circuit_edges hS h3' hF hpF hp.1
    have hG : ∀ {e}, e ∈ F.E → e ∈ D.rad.G.E := fun h ↦ hF.1.2 h
    have honF : ∀ {e : Set Shat} {x y : Shat}, e ∈ F.E → closure e ∩ D.rad.G.V = {x, y} →
        x ∈ F.V := by
      intro e x y he hset
      have hm : x ∈ closure e ∩ D.rad.G.V := by rw [hset]; exact Or.inl rfl
      exact mem_V_of_mem_U hF.1 (F.closure_subset_U he hm.1) hm.2
    have hV₁ := honF he₁ hs₁
    have hV₂ := honF he₂ hs₂
    have hΘ₁ := (D.rad.pole_edge (hG he₁) hp hΘ hreg hs₁).2
    have hΘ₂ := (D.rad.pole_edge (hG he₂) hp hΘ hreg hs₂).2
    have honly : ∀ p' ∈ D.rad.poles, p' ∈ F.V → p' = p := by
      intro p' hp' hp'F
      obtain ⟨Θ', hΘ', hreg', hp'Θ⟩ := D.rad.pole_cases hp'
      obtain ⟨f, -, u, -, hf, -, hu, -, -, hset, -, -⟩ := D.rad.circuit_edges hS h3' hF hp'F hp'.1
      have huΘ := (D.rad.pole_edge (hG hf) hp' hΘ' hreg' hset).2
      have heq := hsame hΘ' hΘ huΘ hΘ₁ (F.V_subset_U (honF hf hset)) (F.V_subset_U hV₁)
      subst heq
      obtain ⟨hr, -⟩ := D.rad.regionOf_mem hp.1
      obtain ⟨w, -, huq⟩ := D.rad.isPreRadial.2.2.1 _ hr
      have h₁ := huq p ⟨(D.rad.regionOf_mem hp.1).2, hp.1.1⟩
      have h₂ := huq p' ⟨hreg ▸ hreg'.symm ▸ (D.rad.regionOf_mem hp'.1).2, hp'.1.1⟩
      rw [h₁, h₂]
    refine Or.inr (Or.inl ⟨?_, fun h ↦ cap.notMem_range hΘ hpΘ (h (F.V_subset_U hpF))⟩)
    have hset : F.U ∩ cap.emb '' bd S = {cap.emb v₁, cap.emb v₂} := by
      apply Subset.antisymm
      · rintro _ ⟨hx, v, hv, rfl⟩
        obtain ⟨hvV, hvF, Θ', hΘ', hvΘ'⟩ := D.rad.bd_point hF.1 hv hx
        have heq := hsame hΘ' hΘ hvΘ' hΘ₁ hx (F.V_subset_U hV₁)
        subst heq
        by_cases h₁ : v = v₁
        · exact Or.inl (h₁ ▸ rfl)
        obtain ⟨e, he, hsv⟩ := D.rad.exists_pole_edge hS h3' hp hΘ' hreg hvV hvΘ'
        obtain ⟨e', he', hsv'⟩ := D.rad.exists_pole_edge hS h3' hp hΘ' hreg hv₁ hΘ₁
        have heF := spoke_mem hS h3' hF hθ hp honly hvV hv₁ h₁ hvF hV₁ he he'
          hsv hsv'
        have hpc : p ∈ closure e := by
          have : p ∈ closure e ∩ D.rad.G.V := by rw [hsv]; exact Or.inr rfl
          exact this.1
        rcases huniq e heF hpc with rfl | rfl
        · have hm : cap.emb v ∈ ({cap.emb v₁, p} : Set Shat) := hs₁ ▸ hsv ▸ Or.inl rfl
          rcases hm with h | h
          · exact absurd (cap.isEmbedding.injective h) h₁
          · exact absurd (h ▸ mem_image_of_mem _ hvV) hp.1.2
        · have hm : cap.emb v ∈ ({cap.emb v₂, p} : Set Shat) := hs₂ ▸ hsv ▸ Or.inl rfl
          rcases hm with h | h
          · exact Or.inr h
          · exact absurd (h ▸ mem_image_of_mem _ hvV) hp.1.2
      · rintro _ (rfl | rfl)
        · exact ⟨F.V_subset_U hV₁, mem_image_of_mem _ (hsubbd hΘ hΘ₁)⟩
        · exact ⟨F.V_subset_U hV₂, mem_image_of_mem _ (hsubbd hΘ hΘ₂)⟩
    rw [hset, ncard_pair fun h ↦ hne (cap.isEmbedding.injective h)]
  · -- No pole lies on `F`.
    refine Or.inl ⟨?_, ?_⟩
    · by_contra hcard
      obtain ⟨_, ⟨hx₁, v₁, hv₁, rfl⟩, _, ⟨hx₂, v₂, hv₂, rfl⟩, hne⟩ :=
        (one_lt_ncard hBfin).1 (not_le.mp hcard)
      obtain ⟨hvV₁, hvF₁, Θ, hΘ, hvΘ₁⟩ := D.rad.bd_point hF.1 hv₁ hx₁
      obtain ⟨hvV₂, hvF₂, Θ₂, hΘ₂, hvΘ₂⟩ := D.rad.bd_point hF.1 hv₂ hx₂
      have heq := hsame hΘ₂ hΘ hvΘ₂ hvΘ₁ hx₂ hx₁
      subst heq
      obtain ⟨p, hp, -, hreg⟩ := D.rad.exists_pole hΘ
      obtain ⟨e₁, he₁, hs₁⟩ := D.rad.exists_pole_edge hS h3' hp hΘ hreg hvV₁ hvΘ₁
      obtain ⟨e₂, he₂, hs₂⟩ := D.rad.exists_pole_edge hS h3' hp hΘ hreg hvV₂ hvΘ₂
      have heF := spoke_mem hS h3' hF hθ hp
        (fun p' hp' h ↦ absurd ⟨p', hp', h⟩ hpole) hvV₁ hvV₂
        (fun h ↦ hne (congrArg _ h)) hvF₁ hvF₂ he₁ he₂ hs₁ hs₂
      have hpm : p ∈ closure e₁ ∩ D.rad.G.V := by rw [hs₁]; exact Or.inr rfl
      exact hpole ⟨p, hp, mem_V_of_mem_U hF.1 (F.closure_subset_U heF hpm.1) hpm.2⟩
    · intro x hx
      by_cases hxV : x ∈ F.V
      · by_contra hr
        have hxR : x ∈ D.rad.Rstar := ⟨hF.1.1 hxV, fun ⟨v, _, h⟩ ↦ hr ⟨v, h⟩⟩
        refine hpole ⟨x, ⟨hxR, fun h ↦ hr (h (D.rad.regionOf_mem hxR).2)⟩, hxV⟩
      · obtain ⟨e, he, hxe⟩ := F.exists_edge_of_mem hx hxV
        obtain ⟨v, -, w, hw, hset⟩ := D.rad.edge_ends (hF.1.2 he)
        have hwm : w ∈ closure e ∩ D.rad.G.V := by rw [hset]; exact Or.inr rfl
        have hwF : w ∈ F.V := mem_V_of_mem_U hF.1 (F.closure_subset_U he hwm.1) hwm.2
        exact D.rad.edge_subset_range (hF.1.2 he) hw (fun hp ↦ hpole ⟨w, hp, hwF⟩) hset hxe

/-- The second assertion of (10.1), for a flaw. -/
theorem IsRepFlaw.second (hFl : D.IsRepFlaw F) {S₁ S₂ : Set Shat} (hs : IsSidesOf F S₁ S₂)
    (hnd : ¬ IsClosedDisc S₁) (hm : (partIn cap D.P.Γ S₁, partIn cap D.P.Γ S₂) ∈ D.𝒯) :
    ((F.U ∩ cap.emb '' bd S).ncard ≤ 1 ∧ F.U ⊆ range cap.emb) ∨
    ((F.U ∩ cap.emb '' bd S).ncard = 2 ∧ ¬ F.U ⊆ range cap.emb) ∨
    Painting.dist D.rad * 4 ≤ ((F.E.ncard + 4 : ℕ) : ℕ∞) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hF := hFl.is_circuit
  obtain ⟨Δ, hΔ, hbd⟩ := exists_disc_of_lt_rep hF hFl.lt_two_rep
  have hsd : S₁ = closure Δᶜ ∧ S₂ = Δ := by
    rcases isSidesOf_cases hT hΔ hbd hs with ⟨rfl, -⟩ | h
    · exact absurd hΔ hnd
    · exact h
  obtain ⟨rfl, rfl⟩ := hsd
  exact second_of_thetaFree hS h3' hF fun ht _ c₁ w₁ c₂ w₂ ↦ hFl.theta hS h3' hΔ hbd hm ht c₁ w₁ c₂
    w₂

end TangleDatum

/-- **Graph Minors XIX, (10.1)** (page 353): "With $\Gamma, \phi, \lambda, \mathscr{T}, F, \Sigma_1,
\Sigma_2$ as above,* • *$\Sigma_2$ is
a disc,* • *either $|U(F) \cap bd(\Sigma_\chi)| \le 1$ and $U(F) \subseteq \Sigma_\chi$, or
$|U(F) \cap bd(\Sigma_\chi)| = 2$ and $U(F) \not\subseteq \Sigma_\chi$, or $dist(\Gamma) \le
\frac{1}{4}|E(F)| + 1$,* • *$F$ is $\lambda$-linked to $\mathscr{T}$." -/
theorem theorem_10_1_proof {α : Type w} {χ : ColourScheme S α} {D : TangleDatum cap χ} {F : Drawing
  Shat}
    (hS : IsSurface S) (h3' : D.P.Γ.IsInternallyThreeConnected)
    (hFl : D.IsRepFlaw F) {S₁ S₂ : Set Shat} (hs : IsSidesOf F S₁ S₂) (hnd : ¬ IsClosedDisc S₁)
    (hm : (partIn cap D.P.Γ S₁, partIn cap D.P.Γ S₂) ∈ D.𝒯) :
    IsClosedDisc S₂ ∧
    (((F.U ∩ cap.emb '' bd S).ncard ≤ 1 ∧ F.U ⊆ range cap.emb) ∨
      ((F.U ∩ cap.emb '' bd S).ncard = 2 ∧ ¬ F.U ⊆ range cap.emb) ∨
      Painting.dist D.rad * 4 ≤ ((F.E.ncard + 4 : ℕ) : ℕ∞)) ∧
    IsLambdaLinkedCircuit D.tb D.ord D.𝒯 F :=
  ⟨TangleDatum.IsRepFlaw.isClosedDisc hFl hs hnd,
    TangleDatum.IsRepFlaw.second hS h3' hFl hs hnd hm,
    TangleDatum.IsRepFlaw.linked hS h3' hFl hs hnd hm⟩

end GraphMinor.GM19

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section810Paths
public import LeanPool.GraphMinor.GM11.Theorem64

/-!
# Graph Minors XI, (8.10), when `Γ` is connected

`restraintUnion` is the set `Z` of (8.10), the union of all restraints `X` with `l(X) ≤ k` and `c ∈
X`.
`theorem_8_10_connected` is (8.10) for a connected drawing `Γ`, by the paper's argument (pages
101–102).
`restraint_down` and `restraint_up` compare the restraints of `Γ ∩ T` with those of `Γ`: the proof
of (8.10)
uses them for a component of `Γ`, and the proof of (8.11) for `Γ ∩ X`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S}

/-- The set `Z` of (8.10): the union of all restraints `X` with `l(X) ≤ k` and `c ∈ X`. -/
def restraintUnion (Γ : Drawing S) (ins : Drawing S → Set S) (K : ℕ) (c : S) (k : ℕ) : Set S :=
  ⋃ X ∈ {X : Set S | IsRestraint Γ ins K X ∧ perimeterWalkLength Γ X ≤ k ∧ c ∈ X}, X

variable {k K : ℕ} {ins : Drawing S → Set S}

omit [ConnectedSpace S] in
/-- There is a smallest restraint through `a` and `b`. -/
theorem exists_optimal {a b : S} {X : Set S} (hX : IsRestraint Γ ins k X) (ha : a ∈ X)
  (hb : b ∈ X) :
    ∃ X', IsOptimalRestraint Γ ins k a b X' ∧ perimeterWalkLength Γ X' ≤ perimeterWalkLength Γ X
      := by
  classical
  have hex : ∃ n, ∃ Y, IsRestraint Γ ins k Y ∧ a ∈ Y ∧ b ∈ Y ∧ perimeterWalkLength Γ Y = n :=
    ⟨_, X, hX, ha, hb, rfl⟩
  obtain ⟨Y, hY, h₁, h₂, hl⟩ := Nat.find_spec hex
  refine ⟨Y, ⟨hY, h₁, h₂, fun Z hZ h₃ h₄ => ?_⟩, ?_⟩
  · rw [hl]
    exact Nat.find_min' hex ⟨Z, hZ, h₃, h₄, rfl⟩
  · rw [hl]
    exact Nat.find_min' hex ⟨X, hX, ha, hb, rfl⟩

/-- `Z` is closed, as a finite union of closed sets. -/
theorem isClosed_restraintUnion (hS : IsClosedSurface S) (c : S) (k : ℕ) :
    IsClosed (restraintUnion Γ ins K c k) := by
  have hfin : {X | IsRestraint Γ ins K X ∧ perimeterWalkLength Γ X ≤ k ∧ c ∈ X}.Finite :=
    (finite_nice hS Γ).subset fun X hX => hX.1.isGammaNice
  exact hfin.isClosed_biUnion fun X hX => hX.1.isClosed

omit [ConnectedSpace S] in
/-- `Z` is nice. -/
theorem isGammaNice_restraintUnion (c : S) (k : ℕ) : IsGammaNice Γ (restraintUnion Γ ins K c k)
  := by
  refine isGammaNice_of_sat fun a ha ⟨y, hya, hy⟩ => ?_
  obtain ⟨X, hX, hyX⟩ := mem_iUnion₂.mp hy
  exact (nice_atom hX.1.isGammaNice ha ⟨y, hya, hyX⟩).trans fun z hz => mem_iUnion₂.mpr ⟨X, hX, hz⟩

omit [T2Space S] [ConnectedSpace S] in
/-- The vertices of `Γ ∩ T`, for a closed set `T`. -/
theorem mem_interSet_V_iff [T2Space S] {T : Set S} (hT : IsClosed T) {x : S} :
    x ∈ (Γ.interSet T).V ↔ x ∈ Γ.V ∧ x ∈ T :=
  ⟨fun h => ⟨(interSet_isSub (Γ := Γ)).1 h, interSet_U_subset hT ((Γ.interSet T).V_subset_U h)⟩,
    fun h => mem_interSet_V h.1 h.2⟩

omit [T2Space S] [ConnectedSpace S] in
theorem mem_interSet_E_iff [T2Space S] {T e : Set S} : e ∈ (Γ.interSet T).E ↔ e ∈ Γ.E ∧ e ⊆ T := by
  change e ∈ (Γ.span _ _).E ↔ _
  rw [Γ.span_E]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

omit [ConnectedSpace S] in
/-- `(Γ ∩ X) ∩ F = Γ ∩ F`, for `F ⊆ X`. -/
theorem interSet_interSet {X F : Set S} (hXc : IsClosed X) (hFc : IsClosed F) (hFX : F ⊆ X) :
    (Γ.interSet X).interSet F = Γ.interSet F := by
  apply Drawing.ext_of_V_E
  · ext x
    rw [mem_interSet_V_iff hFc, mem_interSet_V_iff hXc, mem_interSet_V_iff hFc]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hFX h.2⟩, h.2⟩⟩
  · ext e
    rw [mem_interSet_E_iff, mem_interSet_E_iff, mem_interSet_E_iff]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hFX⟩, h.2⟩⟩

omit [ConnectedSpace S] in
/-- `l(T)` is the same in `Γ ∩ X` as in `Γ`, when `bd(T) ⊆ X`. -/
theorem perimeterSum_interSet (hS : IsClosedSurface S) {X T : Set S} (hTc : IsClosed T)
    (hTn : IsGammaNice Γ T) (hf : frontier T ⊆ X) : perimeterSum (Γ.interSet X) T
      = perimeterSum Γ T := by
  classical
  unfold perimeterSum
  refine Finset.sum_subset (fun e he => ?_) fun e he hen => ?_
  · exact Γ.finite_edges.mem_toFinset.mpr (mem_interSet_E_iff.mp ((Γ.interSet
      X).finite_edges.mem_toFinset.mp he)).1
  · have heΓ := Γ.finite_edges.mem_toFinset.mp he
    unfold perimeterCount
    have hno : ¬ (e ∩ frontier T).Nonempty := by
      rintro ⟨y, hye, hy⟩
      exact hen ((Γ.interSet X).finite_edges.mem_toFinset.mpr
        (mem_interSet_E_iff.mpr ⟨heΓ, (edge_subset_frontier hS hTc hTn heΓ hye hy).trans hf⟩))
    simp [hno]

/-- A restraint of `Γ` with boundary in `X` is a restraint of `Γ ∩ X`, with the same `l`. -/
theorem restraint_down (hS : IsClosedSurface S)
    {X T : Set S} (hXc : IsClosed X) (hT : IsRestraint Γ ins k T)
    (hf : frontier T ⊆ X) :
    IsRestraint (Γ.interSet X) ins k T ∧
      perimeterWalkLength (Γ.interSet X) T = perimeterWalkLength Γ T := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hTc := hT.isClosed
  have hTn := hT.isGammaNice
  have hn' : IsGammaNice (Γ.interSet X) T := by
    refine isGammaNice_of_frontier (N := Γ.interSet (frontier T)) ?_
      ((interSet_U_subset isClosed_frontier).trans hTc.frontier_subset)
        (frontier_interSet hS hTc hTn).ge
    refine ⟨fun x hx => ?_, fun f hf' => ?_⟩
    · obtain ⟨h₁, h₂⟩ := (mem_interSet_V_iff isClosed_frontier).mp hx
      exact (mem_interSet_V_iff hXc).mpr ⟨h₁, hf h₂⟩
    · obtain ⟨h₁, h₂⟩ := mem_interSet_E_iff.mp hf'
      exact mem_interSet_E_iff.mpr ⟨h₁, h₂.trans hf⟩
  have hl : perimeterWalkLength (Γ.interSet X) T = perimeterWalkLength Γ T := by
    rw [perimeterWalkLength_eq hS hTc hn' hT.isSimplyConnected hT.nonempty hT.ne_univ,
      perimeterWalkLength_eq hS hTc hTn hT.isSimplyConnected hT.nonempty hT.ne_univ,
      perimeterSum_interSet hS hTc hTn hf]
  refine ⟨⟨hT.nonempty, hTc, hT.isSimplyConnected, hn', hl ▸ hT.length_lt, ?_⟩, hl⟩
  rw [subBd_eq_frontier, interSet_interSet hXc isClosed_frontier hf, ← subBd_eq_frontier]
  exact hT.compl_not_subset

/-- A restraint of `Γ ∩ X` is a restraint of `Γ` with boundary in `X`, with the same `l`. -/
theorem restraint_up (hS : IsClosedSurface S)
    {X T : Set S} (hXc : IsClosed X)
    (hT : IsRestraint (Γ.interSet X) ins k T) :
    IsRestraint Γ ins k T ∧ frontier T ⊆ X ∧
      perimeterWalkLength Γ T = perimeterWalkLength (Γ.interSet X) T := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hTc := hT.isClosed
  have hTn := hT.isGammaNice
  have hfU := frontier_interSet hS hTc hTn
  have hf : frontier T ⊆ X := by
    rw [← hfU]
    exact (interSet_isSub (Γ := Γ.interSet X)).U_subset.trans (interSet_U_subset hXc)
  have hn' : IsGammaNice Γ T := by
    refine isGammaNice_of_frontier (N := (Γ.interSet X).interSet (frontier T))
      (interSet_isSub.trans interSet_isSub)
      ((interSet_U_subset isClosed_frontier).trans hTc.frontier_subset) hfU.ge
  have hl : perimeterWalkLength Γ T = perimeterWalkLength (Γ.interSet X) T := by
    rw [perimeterWalkLength_eq hS hTc hn' hT.isSimplyConnected hT.nonempty hT.ne_univ,
      perimeterWalkLength_eq hS hTc hTn hT.isSimplyConnected hT.nonempty hT.ne_univ,
      perimeterSum_interSet hS hTc hn' hf]
  refine ⟨⟨hT.nonempty, hTc, hT.isSimplyConnected, hn', hl ▸ hT.length_lt, ?_⟩, hf, hl⟩
  have := hT.compl_not_subset
  rw [subBd_eq_frontier, interSet_interSet hXc isClosed_frontier hf, ← subBd_eq_frontier] at this
  exact this

/-! ## The connected case -/

omit [ConnectedSpace S] in
/-- An `O`-arc in `U(Γ)` meets `V(Γ)`. Otherwise it would lie in one edge, since an `O`-arc minus a
point
is path-connected, and an edge includes no `O`-arc. -/
theorem exists_vertex_of_oArc [ConnectedSpace S] {F : Set S} (hF : IsOArc F) (hFU : F ⊆ Γ.U) :
    ∃ v ∈ F, v ∈ Γ.V := by
  classical
  by_contra! h
  have hin : ∀ p ∈ F, ∃ e ∈ Γ.E, F \ {p} ⊆ e := by
    intro p hp
    have hc := isPathConnected_oArc_diff hF hp
    have hsub : F \ {p} ⊆ Γ.U \ Γ.V := fun x hx => ⟨hFU hx.1, h x hx.1⟩
    obtain ⟨y, hy⟩ := hc.nonempty
    obtain ⟨e, he, hye⟩ := Γ.exists_edge_of_mem (hsub hy).1 (hsub hy).2
    have hun : IsPathConnected (e ∪ (F \ {p})) := he.2.2.1.union hc ⟨y, hye, hy⟩
    have := he.2.2.2 _ (union_subset he.2.1 hsub) hun subset_union_left
    exact ⟨e, he, by rw [← this]; exact subset_union_right⟩
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :
      ∃ p q r, p ∈ F ∧ q ∈ F ∧ r ∈ F ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r := by
    obtain ⟨t, ht, h3⟩ := (infinite_of_isOArc hF).exists_subset_card_eq 3
    obtain ⟨p, q, r, hpq, hpr, hqr, hpqr⟩ := Finset.card_eq_three.mp h3
    rw [hpqr] at ht
    exact ⟨p, q, r, ht (by simp), ht (by simp), ht (by simp), hpq, hpr, hqr⟩
  obtain ⟨e, he, hpe⟩ := hin p hp
  obtain ⟨e', he', hqe⟩ := hin q hq
  have hee : e = e' := Γ.edge_eq_of_mem he he' (hpe ⟨hr, hpr.symm⟩) (hqe ⟨hr, hqr.symm⟩)
  subst hee
  refine not_oArc_subset_edge he hF fun x hx => ?_
  by_cases hxp : x = p
  · exact hqe ⟨hx, hxp ▸ hpq⟩
  · exact hpe ⟨hx, hxp⟩

/-- A parametrization of the circle from `[0, 1]` meets a finite set at finitely many times. -/
theorem finite_arcParam_preimage (z : Circle) {B : Set Circle} (hB : B.Finite) :
    {t : I | arcParam z t ∈ B}.Finite := by
  refine hB.preimage' fun b _ => ?_
  rcases (arcParam z ⁻¹' {b}).eq_empty_or_nonempty with h | ⟨t₀, ht₀⟩
  · rw [h]
    exact finite_empty
  refine (finite_singleton t₀ |>.insert 0 |>.insert 1).subset fun t ht => ?_
  have e : arcParam z t = arcParam z t₀ := ht.trans ht₀.symm
  rcases arcParam_eq_iff z e with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

/-- **(8.10)** of Graph Minors XI (pages 100–101), when `Γ` is connected, by the paper's argument.
-/
theorem theorem_8_10_connected (hS : IsClosedSurface S) (hs : IsSlope Γ K ins) (hΓ : Γ.IsConnected)
    {c : S} (hne : (restraintUnion Γ ins K c k).Nonempty) :
    IsSimplyConnectedSet (restraintUnion Γ ins K c k) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set Z := restraintUnion Γ ins K c k with hZdef
  have hZc : IsClosed Z := isClosed_restraintUnion hS c k
  have hZn : IsGammaNice Γ Z := isGammaNice_restraintUnion c k
  have hmemZ : ∀ x, x ∈ Z → ∃ X, IsRestraint Γ ins K X ∧ perimeterWalkLength Γ X ≤ k ∧ c ∈ X
    ∧ x ∈ X := by
    intro x hx
    obtain ⟨X, hX, hxX⟩ := mem_iUnion₂.mp hx
    exact ⟨X, hX.1, hX.2.1, hX.2.2, hxX⟩
  have hsubZ : ∀ X, IsRestraint Γ ins K X → perimeterWalkLength Γ X ≤ k → c ∈ X → X ⊆ Z :=
    fun X h₁ h₂ h₃ x hx => mem_iUnion₂.mpr ⟨X, ⟨h₁, h₂, h₃⟩, hx⟩
  obtain ⟨u, huV, hu⟩ := exists_vertex_mem_nice hS hΓ.1 c
  have huZ : u ∈ Z := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨X, hX, hl, hc, -⟩ := hmemZ z hz
    exact hsubZ X hX hl hc (hu X hX.isClosed hX.isGammaNice hc)
  let uZ : Z := ⟨u, huZ⟩
  -- "For each $v \in V(\Gamma) \cap Z$, let $X_v$ be a $c, v$-optimal restraint", and the walk
  -- `P_v`.
  have hP : ∀ x : Z, x.1 ∈ Γ.V → ∃ X : Set S, ∃ p : Path x uZ,
      IsOptimalRestraint Γ ins K c x.1 X ∧ ∀ t, (p t).1 ∈ X ∩ Γ.U := by
    intro x hx
    obtain ⟨X', hX', hl', hc', hxX'⟩ := hmemZ x.1 x.2
    obtain ⟨X, hX, hl⟩ := exists_optimal hX' hc' hxX'
    have hXZ : X ⊆ Z := hsubZ X hX.1 (hl.trans hl') hX.2.1
    have huX : u ∈ X := hu X hX.1.isClosed hX.1.isGammaNice hX.2.1
    obtain ⟨p, hp⟩ := joinedIn_of_restraint hS hΓ hX.1 hx hX.2.2.1 huV huX
    exact ⟨X, pathCod p x.2 huZ fun t => hXZ (hp t).1, hX, fun t => hp t⟩
  choose Xv pv hXv using hP
  let f : ∀ x : Z, x.1 ∈ Γ.V → Cl x uZ := fun x hx => Cl.mk (pv x hx)
  have hrange : ∀ {a b d : Z} (p : Path a b) (q : Path b d) (A : Set S), (∀ t, (p t).1 ∈ A) →
      (∀ t, (q t).1 ∈ A) → ∀ t, ((p.trans q) t).1 ∈ A := by
    intro a b d p q A hp hq t
    have : (p.trans q) t ∈ range p ∪ range q := by
      rw [← Path.trans_range]
      exact mem_range_self t
    rcases this with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [← hv]; exact hp v
    · rw [← hv]; exact hq v
  -- Claim (1).
  have h1 : ∀ e ∈ Γ.E, e ⊆ Z → ∀ (x y : Z) (hx : x.1 ∈ Γ.V) (hy : y.1 ∈ Γ.V) (q : Path x y),
      (∀ t, (q t).1 ∈ closure e) → Cl.mk q = (f x hx).trans (f y hy).symm := by
    intro e he heZ x y hx hy q hq
    obtain ⟨z, hz⟩ := he.1
    obtain ⟨X', hX', hl', hc', hzX'⟩ := hmemZ z (heZ hz)
    -- "Let $X$ be a $c, e$-extreme restraint."
    obtain ⟨X, hXe, hX'X, hl⟩ := exists_extreme hS hX'
    have heX : closure e ⊆ X :=
      closure_minimal ((nice_edge hX'.isGammaNice he ⟨z, hz, hzX'⟩).trans hX'X) hXe.1.isClosed
    have hXZ : X ⊆ Z := hsubZ X hXe.1 (hl.trans hl') (hX'X hc')
    have hxX : x.1 ∈ X := heX (by simpa using hq 0)
    have hyX : y.1 ∈ X := heX (by simpa using hq 1)
    -- "$X_{v_1} \subseteq X$ by (8.9)."
    have hsx : Xv x hx ⊆ X := theorem_8_9_proof hS hs (hXv x hx).1 hXe (hX'X hc') hxX
    have hsy : Xv y hy ⊆ X := theorem_8_9_proof hS hs (hXv y hy).1 hXe (hX'X hc') hyX
    have huX : u ∈ X := hu X hXe.1.isClosed hXe.1.isGammaNice (hX'X hc')
    have hflat := homotopic_of_mem hXe.1.isSimplyConnected hXZ (q.trans (pv y hy)) (pv x hx) hxX huX
      (hrange q (pv y hy) X (fun t => heX (hq t)) fun t => hsy ((hXv y hy).2 t).1)
      fun t => hsx ((hXv x hx).2 t).1
    have key : (Cl.mk q).trans (f y hy) = f x hx := by
      rw [← Path.Homotopic.Quotient.mk_trans]
      exact Path.Homotopic.Quotient.eq.mpr hflat
    rw [← key, cl_assoc, cl_trans_symm, cl_trans_refl]
  -- Claim (2), for an `O`-arc of `U(Γ ∩ Z)`.
  have hnullF : ∀ F, IsOArc F → F ⊆ Γ.U → F ⊆ Z → IsNullHomotopicOArcIn Z F := by
    intro F hF hFU hFZ
    obtain ⟨v, hvF, hvV⟩ := exists_vertex_of_oArc hF hFU
    obtain ⟨ψ⟩ := hF
    let z : Circle := ψ.symm ⟨v, hvF⟩
    let φ : C(Circle, S) := ⟨fun x => (ψ x).1, continuous_subtype_val.comp ψ.continuous⟩
    have hφz : φ z = v := by simp [φ, z]
    let a : Z := ⟨v, hFZ hvF⟩
    let γ : Path a a :=
      ⟨⟨fun t => ⟨φ (arcParam z t), hFZ (ψ _).2⟩, by fun_prop⟩,
        Subtype.ext (by simpa [arcParam_apply] using hφz),
        Subtype.ext (by simpa [arcParam_apply] using hφz)⟩
    have hγ : ∀ t, (γ t).1 = φ (arcParam z t) := fun t => rfl
    have hfin : {t : I | (γ t).1 ∈ Γ.V}.Finite := by
      have hB : {w : Circle | φ w ∈ Γ.V}.Finite :=
        Γ.finite_V.preimage fun w _ w' _ h => ψ.injective (Subtype.ext h)
      exact finite_arcParam_preimage z hB
    have hcl := cl_path_of_edges (Γ := Γ) (fun e he hne => nice_edge hZn he hne) f h1 γ
      (fun t => hFU (ψ _).2) hfin hvV hvV
    rw [cl_trans_symm] at hcl
    refine ⟨ψ, v, hFZ hvF, closedCurvesHomotopicIn_of_path z φ (ContinuousMap.const _ v) γ
      (Path.refl a) hγ (fun _ => rfl) (Path.Homotopic.Quotient.eq.mp hcl)⟩
  -- "$Z$ is the union of $U(\Gamma \cap Z)$ with some closed discs with boundary in $U(\Gamma \cap
  -- Z)$."
  let X₀ : Set S := Z ∩ Γ.U
  have hX₀c : IsClosed X₀ := hZc.inter Γ.isClosed_U
  have hUn : IsGammaNice Γ Γ.U :=
    isGammaNice_of_frontier (Drawing.IsSubdrawing.refl Γ) subset_rfl Γ.isClosed_U.frontier_subset
  have hX₀n : IsGammaNice Γ X₀ := hZn.inter hUn
  -- "$U(\Gamma \cap Z)$ is arc-wise connected": every point is joined to `u` along the walks `P_v`.
  have hX₀p : IsPathConnected X₀ := by
    have hv : ∀ x : Z, ∀ hx : x.1 ∈ Γ.V, JoinedIn X₀ x.1 u := fun x hx =>
      ⟨(pv x hx).map continuous_subtype_val, fun t => ⟨(pv x hx t).2, ((hXv x hx).2 t).2⟩⟩
    refine ⟨u, ⟨huZ, Γ.V_subset_U huV⟩, fun {x} hx => ?_⟩
    by_cases hxV : x ∈ Γ.V
    · exact (hv ⟨x, hx.1⟩ hxV).symm
    obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hx.2 hxV
    have heZ : closure e ⊆ Z := closure_minimal (nice_edge hZn he ⟨x, hxe, hx.1⟩) hZc
    obtain ⟨w, hw⟩ : ∃ w, w ∈ closure e ∩ Γ.V := by
      rcases Γ.edge_cond e he with ⟨w, w', hww, hcap, -⟩ | ⟨w, hcap, -⟩
      · exact ⟨w, by rw [hcap]; exact Or.inl rfl⟩
      · exact ⟨w, by rw [hcap]; exact rfl⟩
    have hj : JoinedIn X₀ x w :=
      ((isPathConnected_closure_edge he).joinedIn x (subset_closure hxe) w hw.1).mono
        fun y hy => ⟨heZ hy, Γ.closure_subset_U he hy⟩
    exact (hj.trans (hv ⟨w, heZ hw.1⟩ hw.2)).symm
  let Cs : Set (Drawing S) := {C | ∃ X, (IsRestraint Γ ins K X ∧ perimeterWalkLength Γ X ≤ k
    ∧ c ∈ X) ∧
    C.IsCircuit ∧ C.IsSubdrawing (Γ.interSet (frontier X))}
  have hCs : Cs.Finite := (finite_circuits Γ).subset fun C ⟨X, _, hC, hCs⟩ =>
    ⟨hC, hCs.trans (Drawing.span_isSubdrawing Γ _ _)⟩
  let L : List (Set S) := hCs.toFinset.toList.map ins
  have hmemL : ∀ Y ∈ L, ∃ C ∈ Cs, ins C = Y := by
    intro Y hY
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hY
    exact ⟨C, hCs.mem_toFinset.mp (Finset.mem_toList.mp hC), rfl⟩
  have hCfacts : ∀ C ∈ Cs, IsClosedDisc (ins C) ∧ frontier (ins C) ⊆ X₀ ∧ IsGammaNice Γ (ins C) ∧
      ins C ⊆ Z := by
    rintro C ⟨X, hX, hC, hCX⟩
    have hCΓ : C.IsSubdrawing Γ := hCX.trans (Drawing.span_isSubdrawing Γ _ _)
    have hl : C.length < K := hX.1.isConfined hS C hC hCX
    have hf := ins_slope_facts hS hs hC hCΓ hl
    have h83 := theorem_8_3_proof hS hs hX.1
    rw [subBd_eq_frontier] at h83
    have hXZ := hsubZ X hX.1 hX.2.1 hX.2.2
    refine ⟨hs.isClosedDisc C hC hCΓ hl, ?_, hf.2.2, ?_⟩
    · rw [hf.1]
      intro y hy
      have hy' := hCX.U_subset hy
      exact ⟨hXZ (hX.1.isClosed.frontier_subset (interSet_U_subset isClosed_frontier hy')),
        hCΓ.U_subset hy⟩
    · refine subset_trans ?_ (h83 ▸ hXZ)
      exact (subset_biUnion_of_mem (u := ins) (show C ∈ {C | C.IsCircuit ∧
        C.IsSubdrawing (Γ.interSet (frontier X))} from ⟨hC, hCX⟩)).trans subset_union_right
  have heq : Z = withDiscs X₀ L := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨X, hX, hl, hc, hxX⟩ := hmemZ x hx
      have h83 := theorem_8_3_proof hS hs hX
      rw [subBd_eq_frontier] at h83
      rw [← h83] at hxX
      rcases hxX with hxU | hxC
      · exact Or.inl ⟨hx, (Drawing.span_isSubdrawing Γ _ _).U_subset hxU⟩
      · obtain ⟨C, ⟨hC, hCX⟩, hxC⟩ := mem_iUnion₂.mp hxC
        have hCm : C ∈ Cs := ⟨X, ⟨hX, hl, hc⟩, hC, hCX⟩
        exact Or.inr (mem_iUnion₂.mpr ⟨ins C, List.mem_map.mpr ⟨C, Finset.mem_toList.mpr
          (hCs.mem_toFinset.mpr hCm), rfl⟩, hxC⟩)
    · rintro x (hx | hx)
      · exact hx.1
      · obtain ⟨Y, hY, hxY⟩ := mem_iUnion₂.mp hx
        obtain ⟨C, hC, rfl⟩ := hmemL Y hY
        exact (hCfacts C hC).2.2.2 hxY
  have hsub : ∀ L' : List (Set S), (∀ Y ∈ L', Y ∈ L) →
      IsClosed (withDiscs X₀ L') ∧ IsGammaNice Γ (withDiscs X₀ L') := by
    intro L' hL'
    have hY : ∀ Y ∈ L', IsClosedDisc Y ∧ IsGammaNice Γ Y := fun Y hY' => by
      obtain ⟨C, hC, rfl⟩ := hmemL Y (hL' Y hY')
      exact ⟨(hCfacts C hC).1, (hCfacts C hC).2.2.1⟩
    refine ⟨hX₀c.union (L'.finite_toSet.isClosed_biUnion fun Y hY' =>
      (hY Y hY').1.isCompact.isClosed),
      isGammaNice_of_sat fun a ha hne => ?_⟩
    obtain ⟨x, hxa, hx | hx⟩ := hne
    · exact (nice_atom hX₀n ha ⟨x, hxa, hx⟩).trans subset_union_left
    · obtain ⟨Y, hY', hxY⟩ := mem_iUnion₂.mp hx
      refine (nice_atom (hY Y hY').2 ha ⟨x, hxa, hxY⟩).trans ?_
      exact (subset_biUnion_of_mem (u := id) (s := {Y | Y ∈ L'}) hY').trans subset_union_right
  -- "so $Z$ is simply-connected, from (2), (7.3), and (7.11)."
  rw [heq]
  refine theorem_7_11_proof hS hX₀c hX₀p (fun Y hY => ?_) ?_ ?_
  · obtain ⟨C, hC, rfl⟩ := hmemL Y hY
    exact ⟨(hCfacts C hC).1, (hCfacts C hC).2.1⟩
  · intro Y L' hsuf hcap
    have hsubL : ∀ W ∈ Y :: L', W ∈ L := fun W hW => hsuf.subset hW
    obtain ⟨C, hC, rfl⟩ := hmemL Y (hsubL Y List.mem_cons_self)
    have hL' := hsub L' fun W hW => hsubL W (List.mem_cons_of_mem _ hW)
    exact nice_31 S hS Γ _ _ (hCfacts C hC).1.isCompact.isClosed hL'.1 (hCfacts C hC).2.2.1 hL'.2
      (IsClosedDisc.isSimplyConnectedSet (hCfacts C hC).1) hcap
  · intro φ hφ
    rw [← heq]
    by_contra hnot
    obtain ⟨F, hF, hFφ, hFn⟩ := nice_73 S hS Γ Z hZc hZn φ (hφ.trans inter_subset_left) hnot
    exact hFn (hnullF F hF (fun x hx => (hφ (hFφ hx)).2) fun x hx => (hφ (hFφ hx)).1)


end GraphMinor.GM11

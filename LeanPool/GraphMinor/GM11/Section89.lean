/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section88

/-!
# Graph Minors XI, (8.9)

`theorem_8_9` is (8.9) of the paper. Its proof uses the step (2): "Any edge of $\Gamma$ contributes
at least as much
to the right side of this inequality as it does to the left." The paper does not spell this out, and
we prove
it in `perimeterCount_union_inter` by counting the sides of an edge that lie outside a set:
`perimeterCount_eq`
says that `perimeterCount T e` is this number, when `e ⊆ T`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S}

omit [ConnectedSpace S] in
omit [T2Space S] in
/-- A connected set off `U(Γ)` lies in a closed nice set, as soon as it meets it. -/
theorem side_subset {A T : Set S} (hTn : IsGammaNice Γ T) (hA : IsPreconnected A)
  (hdis : Disjoint A Γ.U)
    (hne : (A ∩ T).Nonempty) : A ⊆ T := by
  obtain ⟨a, haA, haT⟩ := hne
  have haU : a ∉ Γ.U := disjoint_left.mp hdis haA
  obtain ⟨r, hr, har⟩ := exists_region_of_notMem haU
  have hAr : A ⊆ r := by
    obtain ⟨c, hc, rfl⟩ := hr
    have hsub : connectedComponentIn (univ \ Γ.U) a = connectedComponentIn (univ \ Γ.U) c :=
      (connectedComponentIn_eq har).symm
    rw [← hsub]
    exact hA.subset_connectedComponentIn haA fun x hx => ⟨mem_univ x, disjoint_left.mp hdis hx⟩
  exact hAr.trans (nice_region hTn hr ⟨a, har, haT⟩)

omit [ConnectedSpace S] in
/-- A point of an edge is in the interior of `Tᶜ ∪ e` as soon as one point of the edge is. -/
theorem mem_interior_of_isTwoSided (hS : IsClosedSurface S) {T : Set S} (hTn : IsGammaNice Γ T)
    {e : Set S} (he : e ∈ Γ.E) (h2 : IsTwoSided Tᶜ e) : e ⊆ interior (Tᶜ ∪ e) := by
  let B := interior (Tᶜ ∪ e)
  let O : Set S := ⋃₀ {W | IsOpen W ∧ Disjoint (W ∩ e) B}
  have hO : IsOpen O := isOpen_sUnion fun W hW => hW.1
  have hsub : e ⊆ B ∪ O := by
    intro y hy
    by_cases hyI : y ∈ B
    · exact Or.inl hyI
    obtain ⟨W, A₁, A₂, hW, hyW, hWe, hcov, hA₁, hA₂, hd₁, hd₂, hc₁, hc₂⟩ :=
      exists_edge_sides hS Γ he hy
    have hin : ¬ (Disjoint A₁ T ∧ Disjoint A₂ T) := by
      rintro ⟨h₁, h₂⟩
      refine hyI (mem_interior.mpr ⟨W, fun x hx => ?_, hW, hyW⟩)
      by_cases hxU : x ∈ Γ.U
      · exact Or.inr (hWe ⟨hx, hxU⟩)
      · rcases hcov ⟨hx, hxU⟩ with h | h
        · exact Or.inl (disjoint_left.mp h₁ h)
        · exact Or.inl (disjoint_left.mp h₂ h)
    have hside : ∃ A, IsPreconnected A ∧ Disjoint A Γ.U ∧ e ∩ W ⊆ closure A ∧ (A ∩ T).Nonempty := by
      by_cases h₁ : (A₁ ∩ T).Nonempty
      · exact ⟨A₁, hA₁, hd₁, hc₁, h₁⟩
      · have h₂ : (A₂ ∩ T).Nonempty := by
          by_contra h₂
          exact hin ⟨disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h₁),
            disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h₂)⟩
        exact ⟨A₂, hA₂, hd₂, hc₂, h₂⟩
    obtain ⟨A, hA, hdA, hcA, hne⟩ := hside
    have hAT := side_subset hTn hA hdA hne
    refine Or.inr (mem_sUnion.mpr ⟨W, ⟨hW, disjoint_left.mpr ?_⟩, hyW⟩)
    rintro x ⟨hxW, hxe⟩ hxI
    obtain ⟨q, hqI, hqA⟩ := mem_closure_iff.mp (hcA ⟨hxe, hxW⟩) B isOpen_interior hxI
    rcases interior_subset hqI with h | h
    · exact h (hAT hqA)
    · exact disjoint_left.mp hdA hqA ((he.2.1 h).1)
  have hdis : e ∩ (B ∩ O) = ∅ := by
    refine eq_empty_of_forall_notMem ?_
    rintro x ⟨hxe, hxI, hxO⟩
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp hxO
    exact disjoint_left.mp hW.2 ⟨hxW, hxe⟩ hxI
  have hpre : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  rcases isPreconnected_iff_subset_of_disjoint.mp hpre B O isOpen_interior hO hsub hdis with h | h
  · exact h
  · obtain ⟨z, hze, hzI⟩ := h2
    obtain ⟨W, hW, hzW⟩ := mem_sUnion.mp (h hze)
    exact (disjoint_left.mp hW.2 ⟨hzW, hze⟩ hzI).elim

open Classical in
omit [ConnectedSpace S] in
/-- `perimeterCount T e` counts the sides of `e` outside `T`, for an edge `e ⊆ T`. -/
theorem perimeterCount_eq (hS : IsClosedSurface S) {T : Set S} (hTc : IsClosed T)
  (hTn : IsGammaNice Γ T)
    {e W A₁ A₂ : Set S} (he : e ∈ Γ.E) {p : S} (hp : p ∈ e) (hW : IsOpen W) (hpW : p ∈ W)
    (hWe : W ∩ Γ.U ⊆ e) (hcov : W \ Γ.U ⊆ A₁ ∪ A₂) (hA₁ : IsPreconnected A₁)
      (hA₂ : IsPreconnected A₂)
    (hd₁ : Disjoint A₁ Γ.U) (hd₂ : Disjoint A₂ Γ.U) (hc₁ : e ∩ W ⊆ closure A₁)
      (hc₂ : e ∩ W ⊆ closure A₂) :
    perimeterCount T e = if e ⊆ T then (if A₁ ⊆ T then 0 else 1) + (if A₂ ⊆ T then 0 else 1) else 0
      := by
  have hout : ∀ {A}, IsPreconnected A → Disjoint A Γ.U → ¬ A ⊆ T → Disjoint A T := by
    intro A hA hd hn
    refine disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp fun hne => hn ?_)
    exact side_subset hTn hA hd hne
  have hfr : ∀ {A}, Disjoint A T → p ∈ closure A → p ∈ T → p ∈ frontier T := by
    intro A hd hpA hpT
    refine ⟨subset_closure hpT, fun hi => ?_⟩
    obtain ⟨q, hqi, hqA⟩ := mem_closure_iff.mp hpA _ isOpen_interior hi
    exact disjoint_left.mp hd hqA (interior_subset hqi)
  have hp₁ : p ∈ closure A₁ := hc₁ ⟨hp, hpW⟩
  have hp₂ : p ∈ closure A₂ := hc₂ ⟨hp, hpW⟩
  unfold perimeterCount
  by_cases heT : e ⊆ T
  · have hpT := heT hp
    simp only [heT, ite_true]
    by_cases h₁ : A₁ ⊆ T <;> by_cases h₂ : A₂ ⊆ T
    · have hWT : W ⊆ T := by
        intro x hx
        by_cases hxU : x ∈ Γ.U
        · exact heT (hWe ⟨hx, hxU⟩)
        · rcases hcov ⟨hx, hxU⟩ with h | h
          · exact h₁ h
          · exact h₂ h
      have hne : ¬ (e ∩ frontier T).Nonempty := by
        rintro ⟨y, hye, hy⟩
        exact (edge_subset_frontier hS hTc hTn he hye hy hp).2 (mem_interior.mpr ⟨W, hWT, hW, hpW⟩)
      simp [h₁, h₂, hne]
    · have hne : (e ∩ frontier T).Nonempty := ⟨p, hp, hfr (hout hA₂ hd₂ h₂) hp₂ hpT⟩
      have hno : ¬ IsTwoSided Tᶜ e := fun h2 => by
        obtain ⟨q, hqi, hqA⟩ := mem_closure_iff.mp hp₁ _ isOpen_interior
          (mem_interior_of_isTwoSided hS hTn he h2 hp)
        rcases interior_subset hqi with h | h
        · exact h (h₁ hqA)
        · exact disjoint_left.mp hd₁ hqA ((he.2.1 h).1)
      simp [h₁, h₂, hne, hno]
    · have hne : (e ∩ frontier T).Nonempty := ⟨p, hp, hfr (hout hA₁ hd₁ h₁) hp₁ hpT⟩
      have hno : ¬ IsTwoSided Tᶜ e := fun h2 => by
        obtain ⟨q, hqi, hqA⟩ := mem_closure_iff.mp hp₂ _ isOpen_interior
          (mem_interior_of_isTwoSided hS hTn he h2 hp)
        rcases interior_subset hqi with h | h
        · exact h (h₂ hqA)
        · exact disjoint_left.mp hd₂ hqA ((he.2.1 h).1)
      simp [h₁, h₂, hne, hno]
    · have hne : (e ∩ frontier T).Nonempty := ⟨p, hp, hfr (hout hA₁ hd₁ h₁) hp₁ hpT⟩
      have hyes : IsTwoSided Tᶜ e := by
        refine ⟨p, hp, mem_interior.mpr ⟨W, fun x hx => ?_, hW, hpW⟩⟩
        by_cases hxU : x ∈ Γ.U
        · exact Or.inr (hWe ⟨hx, hxU⟩)
        · rcases hcov ⟨hx, hxU⟩ with h | h
          · exact Or.inl (disjoint_left.mp (hout hA₁ hd₁ h₁) h)
          · exact Or.inl (disjoint_left.mp (hout hA₂ hd₂ h₂) h)
      simp [h₁, h₂, hne, hyes]
  · have hne : ¬ (e ∩ frontier T).Nonempty := by
      rintro ⟨y, hye, hy⟩
      exact heT (nice_atom hTn (Or.inl (Or.inr he)) ⟨y, hye, hTc.frontier_subset hy⟩)
    simp [heT, hne]

omit [ConnectedSpace S] in
/-- The inequality (2) in the proof of (8.9), for one edge. -/
theorem perimeterCount_union_inter (hS : IsClosedSurface S) {X Y : Set S} (hXc : IsClosed X)
  (hYc : IsClosed Y)
    (hXn : IsGammaNice Γ X) (hYn : IsGammaNice Γ Y) {e : Set S} (he : e ∈ Γ.E) :
    perimeterCount (X ∪ Y) e + perimeterCount (X ∩ Y) e ≤ perimeterCount X e + perimeterCount Y e
      := by
  classical
  obtain ⟨p, hp⟩ := he.1
  obtain ⟨W, A₁, A₂, hW, hpW, hWe, hcov, hA₁, hA₂, hd₁, hd₂, hc₁, hc₂⟩ :=
    exists_edge_sides hS Γ he hp
  have hne₁ : A₁.Nonempty := (closure_nonempty_iff.mp ⟨p, hc₁ ⟨hp, hpW⟩⟩)
  have hne₂ : A₂.Nonempty := (closure_nonempty_iff.mp ⟨p, hc₂ ⟨hp, hpW⟩⟩)
  have hcnt : ∀ {T : Set S}, IsClosed T → IsGammaNice Γ T → perimeterCount T e =
      if e ⊆ T then (if A₁ ⊆ T then 0 else 1) + (if A₂ ⊆ T then 0 else 1) else 0 :=
    fun hc hn => perimeterCount_eq hS hc hn he hp hW hpW hWe hcov hA₁ hA₂ hd₁ hd₂ hc₁ hc₂
  have hunion : ∀ {A : Set S}, (IsPreconnected A ∧ Disjoint A Γ.U ∧ A.Nonempty) ∨ A = e →
    (A ⊆ X ∪ Y ↔ A ⊆ X ∨ A ⊆ Y) := by
    intro A hA
    refine ⟨fun h => ?_, fun h => h.elim (fun h' => h'.trans subset_union_left)
      fun h' => h'.trans subset_union_right⟩
    have hmeet : ∀ {T}, IsGammaNice Γ T → (A ∩ T).Nonempty → A ⊆ T := by
      intro T hT hne
      rcases hA with ⟨hp', hd, -⟩ | rfl
      · exact side_subset hT hp' hd hne
      · exact nice_atom hT (Or.inl (Or.inr he)) hne
    have hAne : A.Nonempty := by
      rcases hA with ⟨-, -, h⟩ | rfl
      · exact h
      · exact he.1
    obtain ⟨a, ha⟩ := hAne
    rcases h ha with h' | h'
    · exact Or.inl (hmeet hXn ⟨a, ha, h'⟩)
    · exact Or.inr (hmeet hYn ⟨a, ha, h'⟩)
  have u₀ := hunion (A := e) (Or.inr rfl)
  have u₁ := hunion (A := A₁) (Or.inl ⟨hA₁, hd₁, hne₁⟩)
  have u₂ := hunion (A := A₂) (Or.inl ⟨hA₂, hd₂, hne₂⟩)
  rw [hcnt (hXc.union hYc) (hXn.union hYn), hcnt (hXc.inter hYc) (hXn.inter hYn), hcnt hXc hXn,
    hcnt hYc hYn]
  simp only [u₀, u₁, u₂, subset_inter_iff]
  by_cases a : e ⊆ X <;> by_cases b : e ⊆ Y <;> by_cases c₁ : A₁ ⊆ X <;> by_cases c₂ : A₁ ⊆ Y <;>
    by_cases d₁ : A₂ ⊆ X <;> by_cases d₂ : A₂ ⊆ Y <;> simp [a, b, c₁, c₂, d₁, d₂]

variable {k : ℕ} {ins : Drawing S → Set S}

/-- There are only finitely many `Γ`-nice sets. -/
theorem finite_nice (hS : IsClosedSurface S) (Γ : Drawing S) : {X | IsGammaNice Γ X}.Finite := by
  have hfin : Γ.A.Finite :=
    ((Γ.finite_V.image _).union Γ.finite_edges).union (finite_R hS Γ)
  refine (hfin.finite_subsets.image sUnion).subset ?_
  rintro X ⟨𝒜, h𝒜, rfl⟩
  exact ⟨𝒜, h𝒜, rfl⟩

/-- Each restraint `X` lies in an extreme restraint `Y` with `l(Y) ≤ l(X)`. -/
theorem exists_extreme (hS : IsClosedSurface S) {X : Set S} (hX : IsRestraint Γ ins k X) :
    ∃ Y, IsExtremeRestraint Γ ins k Y ∧ X ⊆ Y ∧ perimeterWalkLength Γ Y ≤ perimeterWalkLength Γ X
      := by
  have hfin : {Y | IsRestraint Γ ins k Y ∧ X ⊆ Y ∧ perimeterWalkLength Γ Y
    ≤ perimeterWalkLength Γ X}.Finite :=
    (finite_nice hS Γ).subset fun Y hY => hY.1.isGammaNice
  obtain ⟨Y, hY⟩ := hfin.exists_maximal ⟨X, hX, subset_rfl, le_rfl⟩
  refine ⟨Y, ⟨hY.1.1, fun Z hZ hYZ hl => ?_⟩, hY.1.2.1, hY.1.2.2⟩
  have hm : Z ∈ {Y | IsRestraint Γ ins k Y ∧ X ⊆ Y ∧ perimeterWalkLength Γ Y
    ≤ perimeterWalkLength Γ X} :=
    ⟨hZ, hY.1.2.1.trans hYZ, hl.trans hY.1.2.2⟩
  exact subset_antisymm (hY.2 hm hYZ) hYZ

/-- The inequality (2) in the proof of (8.9): `l(X ∪ Y) + l(X ∩ Y) ≤ l(X) + l(Y)`. -/
theorem perimeterWalkLength_union_inter (hS : IsClosedSurface S)
    {X Y : Set S} (r₁ : IsRestraint Γ ins k X)
    (r₂ : IsRestraint Γ ins k Y) (hinter : IsSimplyConnectedSet (X ∩ Y))
    (hunion : IsSimplyConnectedSet (X ∪ Y)) (hne : (X ∩ Y).Nonempty) (hu : X ∪ Y ≠ univ) :
    perimeterWalkLength Γ (X ∪ Y) + perimeterWalkLength Γ (X ∩ Y) ≤
      perimeterWalkLength Γ X + perimeterWalkLength Γ Y := by
  have hc := r₁.isClosed.inter r₂.isClosed
  have hn := r₁.isGammaNice.inter r₂.isGammaNice
  have hIU : X ∩ Y ≠ univ := fun h => r₁.ne_univ (eq_univ_of_univ_subset (h ▸ inter_subset_left))
  have hneUnion : (X ∪ Y).Nonempty := hne.mono (inter_subset_left.trans subset_union_left)
  rw [perimeterWalkLength_eq hS (r₁.isClosed.union r₂.isClosed)
      (r₁.isGammaNice.union r₂.isGammaNice) hunion hneUnion hu,
    perimeterWalkLength_eq hS hc hn hinter hne hIU,
    perimeterWalkLength_eq hS r₁.isClosed r₁.isGammaNice r₁.isSimplyConnected r₁.nonempty
      r₁.ne_univ,
    perimeterWalkLength_eq hS r₂.isClosed r₂.isGammaNice r₂.isSimplyConnected r₂.nonempty
      r₂.ne_univ]
  unfold perimeterSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e he => perimeterCount_union_inter hS r₁.isClosed r₂.isClosed
    r₁.isGammaNice
    r₂.isGammaNice (Γ.finite_edges.mem_toFinset.mp he)

/-- The intersection of two restraints is a restraint, if it is simply-connected and short. This is
the subproof
of (1) in the proof of (8.9). -/
theorem isRestraint_inter (hS : IsClosedSurface S) (hs : IsSlope Γ k ins)
    {X Y : Set S} (r₁ : IsRestraint Γ ins k X) (r₂ : IsRestraint Γ ins k Y)
    (hinter : IsSimplyConnectedSet (X ∩ Y)) (hne : (X ∩ Y).Nonempty)
    (hlt : perimeterWalkLength Γ (X ∩ Y) < k) : IsRestraint Γ ins k (X ∩ Y) := by
  have hXU : X ≠ univ := r₁.ne_univ
  have hIU : X ∩ Y ≠ univ := fun h => hXU (eq_univ_of_univ_subset (h ▸ inter_subset_left))
  have hc := r₁.isClosed.inter r₂.isClosed
  have hn := r₁.isGammaNice.inter r₂.isGammaNice
  refine ⟨hne, hc, hinter, hn, hlt, ?_⟩
  intro hcov
  obtain ⟨u₁, W₁, hW₁, hl₁, -, hcnt₁⟩ := exists_minimal_perimeterWalk hS hc hn hinter hne hIU
  obtain ⟨u, W, -, -, hl₀, -, hd⟩ := r₁.exists_walk hS
  have hd₁ := walkDrawing_eq hS hc hn hW₁ hcnt₁
  obtain ⟨r, hr, h₁, h₂, -⟩ := theorem_8_2_proof hS hs W₁ W W (hl₁ ▸ hlt) hl₀ hl₀
  rw [insWalk_eq hS hs r₁ hd] at h₂
  refine h₁ fun x hxr => ?_
  have hxX : x ∉ X := fun hx => h₂ (nice_region r₁.isGammaNice hr ⟨x, hxr, hx⟩)
  have := hcov ⟨mem_univ x, fun hx => hxX hx.1⟩
  rwa [subBd_eq_frontier, ← hd₁] at this

/-- **(8.9)** of Graph Minors XI (page 100): "Let $a, b \in \Sigma$, let $X'$ be an $a, b$-optimal
restraint, and let $X$ be an extreme
restraint with $a, b \in X$. Then $X' \subseteq X$." -/
theorem theorem_8_9_proof (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {a b : S} {X X' : Set S} (hX' : IsOptimalRestraint Γ ins k a b X')
    (hX : IsExtremeRestraint Γ ins k X) (ha : a ∈ X) (hb : b ∈ X) : X' ⊆ X := by
  classical
  obtain ⟨Y, hY, hsub, hl⟩ := exists_extreme hS hX'.1
  refine hsub.trans ?_
  have hopt : ∀ Z, IsRestraint Γ ins k Z → a ∈ Z → b ∈ Z → perimeterWalkLength Γ Y
    ≤ perimeterWalkLength Γ Z :=
    fun Z hZ h₁ h₂ => hl.trans (hX'.2.2.2 Z hZ h₁ h₂)
  have ra := hsub hX'.2.1
  have rb := hsub hX'.2.2.1
  obtain ⟨hinter, hunion⟩ := theorem_8_8_proof hS hs hX hY ⟨a, ha, ra⟩
  have hu : X ∪ Y ≠ univ := by
    have := theorem_8_4_proof hS hs hX.1 hY.1 hY.1
    rwa [union_assoc, union_self] at this
  have r₁ := hX.1
  have r₂ := hY.1
  have hXU : X ≠ univ := r₁.ne_univ
  have hIU : X ∩ Y ≠ univ := fun h => hXU (eq_univ_of_univ_subset (h ▸ inter_subset_left))
  have hc := r₁.isClosed.inter r₂.isClosed
  have hn := r₁.isGammaNice.inter r₂.isGammaNice
  -- The step (1).
  have h1 : perimeterWalkLength Γ Y ≤ perimeterWalkLength Γ (X ∩ Y) := by
    by_cases hlt : perimeterWalkLength Γ (X ∩ Y) < k
    · exact hopt _ (isRestraint_inter hS hs r₁ r₂ hinter ⟨a, ha, ra⟩ hlt) ⟨ha, ra⟩ ⟨hb, rb⟩
    · have := r₂.length_lt
      omega
  -- The step (2).
  have h2 := perimeterWalkLength_union_inter hS r₁ r₂ hinter hunion ⟨a, ha, ra⟩ hu
  have h3 : perimeterWalkLength Γ (X ∪ Y) ≤ perimeterWalkLength Γ X := by omega
  have hrest := theorem_8_6_proof hS hs r₁ r₂ hunion (lt_of_le_of_lt h3 r₁.length_lt)
  have := hX.2 _ hrest subset_union_left h3
  exact union_eq_left.mp this

/-- **(8.13)** of Graph Minors XI (page 103): "Let $a, b \in \Sigma$ with $\{a, b\} \cap U(\Gamma)
\subseteq V(\Gamma)$; and let $X$ be a
restraint with $a, b \in X$. Suppose that there is no restraint $Y$ with $X \subseteq Y$ and
$l(Y) < l(X)$. Then $X$ includes an $a, b$-optimal restraint."

The paper subdivides the edges, so that `X` becomes extreme in the new drawing, and applies (8.9)
there. There is a
shorter proof, in which `{a, b} ∩ U(Γ) ⊆ V(Γ)` is not used. Let `E` be an extreme `a, b`-optimal
restraint. The proof
of (8.8) needs that one of the two restraints is extreme, and of the other only what we know of `X`
(`simplyConnected_inter_union`). Then `l(X ∪ E) + l(X ∩ E) ≤ l(X) + l(E)` and `l(X) ≤ l(X ∪ E)`, and
so `X ∩ E` is
`a, b`-optimal. -/
theorem theorem_8_13_proof (hS : IsClosedSurface S) (hs : IsSlope Γ k ins) {a b : S}
    {X : Set S} (hX : IsRestraint Γ ins k X) (ha : a ∈ X) (hb : b ∈ X)
    (hmax : ∀ Y : Set S, IsRestraint Γ ins k Y → X ⊆ Y →
      ¬ perimeterWalkLength Γ Y < perimeterWalkLength Γ X) :
    ∃ Y : Set S, Y ⊆ X ∧ IsOptimalRestraint Γ ins k a b Y := by
  classical
  -- An `a, b`-optimal restraint, of smallest length.
  have hex : ∃ n, ∃ Y, IsRestraint Γ ins k Y ∧ a ∈ Y ∧ b ∈ Y ∧ perimeterWalkLength Γ Y = n :=
    ⟨_, X, hX, ha, hb, rfl⟩
  obtain ⟨Y₀, hY₀, ha₀, hb₀, hl₀⟩ := Nat.find_spec hex
  have hmin : ∀ Z, IsRestraint Γ ins k Z → a ∈ Z → b ∈ Z → perimeterWalkLength Γ Y₀
    ≤ perimeterWalkLength Γ Z :=
    fun Z h₁ h₂ h₃ => hl₀ ▸ Nat.find_min' hex ⟨Z, h₁, h₂, h₃, rfl⟩
  obtain ⟨E, hE, hsub, hl⟩ := exists_extreme hS hY₀
  have ra := hsub ha₀
  have rb := hsub hb₀
  have hnear : IsNearExtreme Γ ins k 1 X := ⟨hX, fun Y hY hXY hle => (hmax Y hY hXY
    (by omega)).elim⟩
  have hne : (X ∩ E).Nonempty := ⟨a, ha, ra⟩
  obtain ⟨hinter, hunion⟩ := simplyConnected_inter_union hS hs hnear hE hne
  have hu : X ∪ E ≠ univ := by
    have := theorem_8_4_proof hS hs hX hE.1 hE.1
    rwa [union_assoc, union_self] at this
  have h2 := perimeterWalkLength_union_inter hS hX hE.1 hinter hunion hne hu
  have h3 : perimeterWalkLength Γ X ≤ perimeterWalkLength Γ (X ∪ E) := by
    by_cases hlt : perimeterWalkLength Γ (X ∪ E) < k
    · exact not_lt.mp (hmax _ (theorem_8_6_proof hS hs hX hE.1 hunion hlt) subset_union_left)
    · have := hX.length_lt
      omega
  have h4 : perimeterWalkLength Γ (X ∩ E) ≤ perimeterWalkLength Γ E := by omega
  have hr := isRestraint_inter hS hs hX hE.1 hinter hne (lt_of_le_of_lt h4 hE.1.length_lt)
  exact ⟨X ∩ E, inter_subset_left, hr, ⟨ha, ra⟩, ⟨hb, rb⟩, fun Z h₁ h₂ h₃ =>
    h4.trans (hl.trans (hmin Z h₁ h₂ h₃))⟩

end GraphMinor.GM11

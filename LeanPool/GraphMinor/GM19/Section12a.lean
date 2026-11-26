/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM19.Section7e

/-!
# Graph Minors XIX, Section 12: the metric, (12.2) and (12.3)

Section 12 uses the triangle inequality for the radial drawing of a painting. In the
short-distance case the two distances sum to less than the representativeness `D.rep`.
The corresponding restraints meet at an anchor in the middle atom and have combined perimeter
below `2 * D.rep`. They fit in one restraint by `exists_restraint_union`, the short-distance
step of XI (9.1). If the sum is at least `D.rep`, the bound on `D.dist a c` gives the inequality.

The results (12.2) and (12.3) then pick a small set of far apart vertices of `Γ*` near all edges
with a large label. The results used later are `TangleDatum.dist_triangle`,
`TangleDatum.theorem_12_3`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

omit [T2Space S] in
/-- The metric is symmetric. -/
theorem dist_comm (D : TangleDatum cap χ) (a b : Set Shat) : D.dist a b = D.dist b a := by
  classical
  by_cases hab : a = b
  · rw [hab]
  have hne : b ≠ a := fun h ↦ hab h.symm
  have hc : (∃ W : ClosedWalkIns D.rad D.ord D.𝒯, (a ∩ W.ins).Nonempty ∧ (b ∩ W.ins).Nonempty) ↔
      ∃ W : ClosedWalkIns D.rad D.ord D.𝒯, (b ∩ W.ins).Nonempty ∧ (a ∩ W.ins).Nonempty :=
    ⟨fun ⟨W, h₁, h₂⟩ ↦ ⟨W, h₂, h₁⟩, fun ⟨W, h₁, h₂⟩ ↦ ⟨W, h₂, h₁⟩⟩
  have hs : {k : ℕ | ∃ W : ClosedWalkIns D.rad D.ord D.𝒯,
      (a ∩ W.ins).Nonempty ∧ (b ∩ W.ins).Nonempty ∧ W.halfLen = k} =
      {k : ℕ | ∃ W : ClosedWalkIns D.rad D.ord D.𝒯,
      (b ∩ W.ins).Nonempty ∧ (a ∩ W.ins).Nonempty ∧ W.halfLen = k} := by
    ext k
    exact ⟨fun ⟨W, h₁, h₂, h₃⟩ ↦ ⟨W, h₂, h₁, h₃⟩, fun ⟨W, h₁, h₂, h₃⟩ ↦ ⟨W, h₂, h₁, h₃⟩⟩
  simp only [dist, tangleMetric, ite_eq_right hab, ite_eq_right hne, hc, hs]

omit [T2Space S] in
/-- The metric is at most `rep(𝒯)`. -/
theorem dist_le_rep (D : TangleDatum cap χ) (a b : Set Shat) : D.dist a b ≤ D.rep := by
  classical
  unfold dist tangleMetric
  split_ifs with h₁ h₂
  · exact Nat.zero_le _
  · obtain ⟨T, ha, hb⟩ := h₂
    have hne : {k : ℕ | ∃ W : ClosedWalkIns D.rad D.ord D.𝒯,
        (a ∩ W.ins).Nonempty ∧ (b ∩ W.ins).Nonempty ∧ W.halfLen = k}.Nonempty :=
      ⟨_, T, ha, hb, rfl⟩
    obtain ⟨W, -, -, hW⟩ := Nat.sInf_mem hne
    rw [← hW]
    exact W.halfLen_lt.le
  · exact le_rfl

omit [T2Space Shat] in
omit [T2Space S] in
/-- The atom belonging to a vertex of `Γ*` is an atom of `Γ`. -/
theorem atomOf_mem (D : TangleDatum cap χ) {x : Shat} (hx : x ∈ D.rad.G.V) :
    D.rad.atomOf x ∈ D.P.Γ.atoms cap := by
  classical
  unfold RadialDrawing.atomOf
  split_ifs with h
  · obtain ⟨v, hv, rfl⟩ := h
    exact Or.inl (Or.inl ⟨v, hv, rfl⟩)
  · exact Or.inr (D.rad.regionOf_mem ⟨hx, h⟩).1

omit [T2Space S] [T2Space Shat] in
/-- The atom of a vertex of `Γ` is its singleton. -/
theorem atomOf_emb (D : TangleDatum cap χ) {v : S} (hv : v ∈ D.P.Γ.V) :
    D.rad.atomOf (cap.emb v) = {cap.emb v} := by
  classical
  unfold RadialDrawing.atomOf
  rw [ite_eq_left (show cap.emb v ∈ D.P.Γ.hatV cap from mem_image_of_mem cap.emb hv)]

omit [T2Space Shat] in
omit [T2Space S] in
/-- A vertex of `Γ*` lies in its atom. -/
theorem mem_atomOf (D : TangleDatum cap χ) {x : Shat} (hx : x ∈ D.rad.G.V) :
    x ∈ D.rad.atomOf x := by
  classical
  unfold RadialDrawing.atomOf
  split_ifs with h
  · rfl
  · exact (D.rad.regionOf_mem ⟨hx, h⟩).2

/-- The set `Z` of Section 12: the edges of `Γ` with `φ(e) ≥ ω₀`. These are internal of size `k`, by
the remark in `NoInternalMatch`. -/
def largeEdges (D : TangleDatum cap χ) (k : ℕ) (ω₀ : α) : Set (Set S) :=
  {e | e ∈ D.P.Γ.E ∧ Painting.IsInternal e ∧ (tilde e).ncard = k ∧ sizeLE χ k ω₀ (D.P.φ e)}

section Restraints



/-- The triangle inequality for the radial distance of a painting. Below the representativeness
cutoff, `exists_anchor` supplies a common point of the two walk insides, and their combined
perimeter is less than `2 * D.rep`. A single restraint covers both with perimeter at most their
sum, and its perimeter walk provides the distance bound. -/
theorem dist_triangle (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {a b c : Set Shat}
    (hb : b ∈ D.P.Γ.atoms cap) : D.dist a c ≤ D.dist a b + D.dist b c := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  by_cases hac : a = c
  · rw [hac, dist_self]
    exact Nat.zero_le _
  by_cases hab : a = b
  · rw [hab, dist_self]
    omega
  by_cases hbc : b = c
  · rw [hbc, dist_self]
    omega
  by_cases hlt : D.dist a b + D.dist b c < D.rep
  swap
  · have := D.dist_le_rep a c
    omega
  obtain ⟨T₁, ha₁, hb₁, hl₁⟩ := D.exists_of_dist_lt hab (by omega)
  obtain ⟨T₂, hb₂, hc₂, hl₂⟩ := D.exists_of_dist_lt hbc (by omega)
  obtain ⟨p, -, hp, -⟩ := exists_anchor D hrep hb
  have R₁ := isRestraint_ins D (by omega) T₁
  have R₂ := isRestraint_ins D (by omega) T₂
  obtain ⟨X, hX, h₁, h₂, h₃⟩ := exists_restraint_union hT
    (D.isSlope (by omega)) R₁.1 R₂.1 ⟨p, hp T₁ hb₁, hp T₂ hb₂⟩ (by omega)
  obtain ⟨T, hTX, hTl⟩ := exists_walk_of_restraint D (by omega) hX
  have hle := D.dist_le T (ha₁.mono (inter_subset_inter_right _ (hTX.symm ▸ h₁)))
    (hc₂.mono (inter_subset_inter_right _ (hTX.symm ▸ h₂)))
  omega

omit [T2Space S] in
/-- An inside that meets an edge `e` of `Γ` contains the ends of `e`, since it is a union of atoms
of
`Γ*` and `e` lies in a region of `Γ*`. -/
theorem end_mem_ins (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {e : Set S} (he : e ∈ D.P.Γ.E)
    (T : ClosedWalkIns D.rad D.ord D.𝒯) (hm : (cap.emb '' e ∩ T.ins).Nonempty) {x : S}
    (hx : x ∈ closure e) : cap.emb x ∈ T.ins := by
  have R := (isRestraint_ins D hrep T).1
  obtain ⟨s, hs, hes⟩ := D.exists_region_of_edge he
  obtain ⟨y, hye, hy⟩ := hm
  have hsub : s ⊆ T.ins := nice_region R.isGammaNice hs ⟨y, hes hye, hy⟩
  have hcont : Continuous cap.emb := (cap.isClosedEmbedding χ.isSurface).continuous
  exact closure_minimal hsub R.isClosed
    (closure_mono hes (image_closure_subset_closure_image hcont (mem_image_of_mem _ hx)))

omit [T2Space S] in
/-- If `e, f` are distinct edges of `Γ` at distance `< rep(𝒯)` then `e` is as close to each end of
`f`. The proof of (12.2) in the paper uses this without saying so. -/
theorem edgeVertDist_le (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {e f : Set S} (hne : e ≠ f)
    (hf : f ∈ D.P.Γ.E) (hlt : D.edgeDist e f < D.rep) {x : S} (hx : x ∈ tilde f)
    (hxV : x ∈ D.P.Γ.V) : D.edgeVertDist e (cap.emb x) ≤ D.edgeDist e f := by
  have hinj := (cap.isClosedEmbedding χ.isSurface).injective
  have hne' : cap.emb '' e ≠ cap.emb '' f := fun h ↦ hne (image_injective.mpr hinj h)
  obtain ⟨T, h₁, h₂, h₃⟩ := D.exists_of_dist_lt hne' hlt
  have hmem := end_mem_ins D hrep hf T h₂ hx.1
  change D.dist (cap.emb '' e) (D.rad.atomOf (cap.emb x)) ≤ D.dist (cap.emb '' e) (cap.emb '' f)
  rw [D.atomOf_emb hxV, ← h₃]
  exact D.dist_le T h₁ ⟨_, rfl, hmem⟩

/-- An edge of `Γ` has distance at most `3` from each of its ends, by the circuit around it. -/
theorem edgeVertDist_self_le (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {e : Set S}
    (he : e ∈ D.P.Γ.E) {x : S} (hx : x ∈ tilde e) (hxV : x ∈ D.P.Γ.V) :
    D.edgeVertDist e (cap.emb x) ≤ 3 := by
  obtain ⟨s, hs, hes⟩ := D.exists_region_of_edge he
  obtain ⟨X, hX, hl, hsX⟩ := exists_tie D hrep hs
  obtain ⟨T, hTX, hTl⟩ := exists_walk_of_restraint D (by omega) hX
  have hcont : Continuous cap.emb := (cap.isClosedEmbedding χ.isSurface).continuous
  have hxs : cap.emb x ∈ closure s :=
    closure_mono hes (image_closure_subset_closure_image hcont (mem_image_of_mem _ hx.1))
  obtain ⟨y, hy⟩ := he.1
  have hle := D.dist_le T (a := cap.emb '' e) (b := {cap.emb x})
    ⟨_, mem_image_of_mem _ hy, hTX ▸ hsX (subset_closure (hes (mem_image_of_mem _ hy)))⟩
    ⟨_, rfl, hTX ▸ hsX hxs⟩
  change D.dist (cap.emb '' e) (D.rad.atomOf (cap.emb x)) ≤ 3
  rw [D.atomOf_emb hxV]
  omega

omit [T2Space S] [T2Space Shat] in
/-- The number of poles is `c(Σ)`, since each cuff bounds one region of `Γ` off `Σ`. -/
theorem ncard_poles (D : TangleDatum cap χ) : D.rad.poles.ncard = numCuffs S := by
  have hS := χ.isSurface
  have hcf : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hpf : D.rad.poles.Finite := D.rad.G.finite_V.subset fun _ h ↦ h.1.1
  have hdisj : ∀ Θ₁ ∈ cuffs S, ∀ Θ₂ ∈ cuffs S, ∀ p, p ∈ cap.cuffDisc Θ₁ → p ∈ cap.cuffDisc Θ₂ →
      Θ₁ = Θ₂ := by
    intro Θ₁ h₁ Θ₂ h₂ p hp₁ hp₂
    by_contra hne
    exact disjoint_left.mp (cap.cuffDisc_disjoint Θ₁ h₁ Θ₂ h₂ hne) (subset_closure hp₁)
      (subset_closure hp₂)
  refine le_antisymm ?_ ?_
  · choose! f hf hreg hmem using fun p (hp : p ∈ D.rad.poles) ↦ D.rad.pole_cases hp
    refine ncard_le_ncard_of_injOn f hf ?_ hcf
    intro p hp q hq hpq
    have hq' : q ∈ cap.cuffDisc (f p) := hpq ▸ hmem q hq
    have hreg' : D.rad.regionOf p = D.rad.regionOf q := by rw [hreg p hp, hpq, hreg q hq]
    have hr := (D.rad.regionOf_mem hp.1).1
    obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
    refine (hG3 _ hr).unique ⟨(D.rad.regionOf_mem hp.1).2, hp.1.1⟩ ?_
    exact ⟨hreg' ▸ (D.rad.regionOf_mem hq.1).2, hq.1.1⟩
  · have : ConnectedSpace Shat := cap.connected
    choose! g hg hmem hreg using fun Θ (hΘ : Θ ∈ cuffs S) ↦ D.rad.exists_pole hΘ
    refine ncard_le_ncard_of_injOn g hg ?_ hpf
    intro Θ₁ h₁ Θ₂ h₂ h
    exact hdisj Θ₁ h₁ Θ₂ h₂ (g Θ₁) (hmem Θ₁ h₁) (h ▸ hmem Θ₂ h₂)

omit [T2Space S] in
/-- If `D` is not `a`-flawed in distance, and `rep(𝒯)` and `dist(Γ)` are large enough for that to
mean
something, then distinct poles are more than `a` apart. -/
theorem lt_vDist_of_not_flawed (D : TangleDatum cap χ) {a : ℕ} (hrep : a < D.rep)
    (hdist : ((a + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad) (hf : ¬ D.IsFlawedInDistance a)
    {r₁ r₂ : Shat} (h₁ : r₁ ∈ D.rad.poles) (h₂ : r₂ ∈ D.rad.poles) (hne : r₁ ≠ r₂) :
    a < D.vDist r₁ r₂ := by
  by_contra hle
  exact hf ⟨hrep, hdist, r₁, h₁, r₂, h₂, hne, not_lt.mp hle⟩

/-- **Graph Minors XIX, (12.2)** (page 363): "There exists $X_1 \subseteq V(\Gamma^*)$ with $|X_1|
\le m + c(\Sigma_\chi)$ and $P^*
\subseteq X_1$, such that for every $e \in Z$ there exists $x \in X_1$ with $d(e, x) \le n$." -/
theorem theorem_12_2_proof (D : TangleDatum cap χ) {m n k : ℕ} {ω₀ : α} (hn : 4 ≤ n)
    (hrep : n < D.rep) (hno : D.NoInternalMatch m n k ω₀) :
    ∃ X₁ ⊆ D.rad.G.V, X₁.ncard ≤ m + numCuffs S ∧ D.rad.poles ⊆ X₁ ∧
      ∀ e ∈ D.largeEdges k ω₀, ∃ x ∈ X₁, D.edgeVertDist e x ≤ n := by
  classical
  rcases isEmpty_or_nonempty S with hSe | hSn
  · refine ⟨D.rad.poles, fun _ h ↦ h.1.1, by rw [D.ncard_poles]; omega, subset_rfl, fun e he ↦ ?_⟩
    obtain ⟨y, -⟩ := he.1.1
    exact (hSe.false y).elim
  have hZfin : (D.largeEdges k ω₀).Finite := D.P.Γ.finite_edges.subset fun _ h ↦ h.1
  let 𝒜 : Set (Set (Set S)) := {A | A ⊆ D.largeEdges k ω₀ ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < D.edgeDist a b) ∧
    ∀ a ∈ A, ∀ r ∈ D.rad.poles, n < D.edgeVertDist a r}
  have h𝒜fin : 𝒜.Finite := hZfin.finite_subsets.subset fun _ h ↦ h.1
  have h𝒜0 : (∅ : Set (Set S)) ∈ 𝒜 := by simp [𝒜]
  obtain ⟨A, -, hmax⟩ := h𝒜fin.exists_le_maximal h𝒜0
  have hAmem : A ∈ 𝒜 := hmax.1
  have hAfin : A.Finite := hZfin.subset hAmem.1
  have hAm : A.ncard < m := by
    by_contra hge
    push Not at hge
    have : Finite A := hAfin.to_subtype
    have := Fintype.ofFinite A
    have hcard : Fintype.card (Fin m) ≤ Fintype.card A := by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact hge
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
    refine hno ⟨fun i ↦ (f i).1, fun i ↦ ?_, fun i j hij ↦ ?_, fun i ↦ hAmem.2.2 _ (f i).2⟩
    · obtain ⟨h₁, h₂, h₃, h₄⟩ := hAmem.1 (f i).2
      exact ⟨h₁, h₂, h₃, h₄⟩
    · refine hAmem.2.1 _ (f i).2 _ (f j).2 fun h ↦ ?_
      exact hij.ne (f.injective (Subtype.ext h))
  have hend : ∀ a ∈ D.P.Γ.E, ∃ x, x ∈ tilde a ∧ x ∈ D.P.Γ.V := by
    intro a ha
    have hne : (tilde a).Nonempty := by
      refine nonempty_of_ncard_ne_zero ?_
      rcases D.P.Γ.edge_shape a ha with h | h <;> omega
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, D.P.Γ.tilde_subset_V ha hx⟩
  have hAE : ∀ a ∈ A, a ∈ D.P.Γ.E := fun a ha ↦ (hAmem.1 ha).1
  choose! τ hτ hτV using fun a (ha : a ∈ A) ↦ hend a (hAE a ha)
  have hτG : ∀ a ∈ A, cap.emb (τ a) ∈ D.rad.G.V := fun a ha ↦
    D.rad.isPreRadial.2.1 (mem_image_of_mem cap.emb (hτV a ha))
  refine ⟨D.rad.poles ∪ (fun a ↦ cap.emb (τ a)) '' A, ?_, ?_, subset_union_left, ?_⟩
  · refine union_subset (fun _ h ↦ h.1.1) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact hτG a ha
  · have h₁ := ncard_union_le D.rad.poles ((fun a ↦ cap.emb (τ a)) '' A)
    have h₂ : ((fun a ↦ cap.emb (τ a)) '' A).ncard ≤ A.ncard := ncard_image_le hAfin
    have h₃ := D.ncard_poles
    omega
  intro e heZ
  by_contra hno'
  push Not at hno'
  have hfar : ∀ x, x ∈ D.rad.poles ∨ (∃ a ∈ A, x = cap.emb (τ a)) → n < D.edgeVertDist e x := by
    rintro x (hx | ⟨a, ha, rfl⟩)
    · exact hno' x (Or.inl hx)
    · exact hno' _ (Or.inr ⟨a, ha, rfl⟩)
  have heA : e ∉ A := fun h ↦ by
    have h₁ := hfar _ (Or.inr ⟨e, h, rfl⟩)
    have h₂ := edgeVertDist_self_le D (by omega) heZ.1 (hτ e h) (hτV e h)
    omega
  have hclose : ∀ b ∈ A, n < D.edgeDist e b := by
    intro b hb
    by_contra hle
    push Not at hle
    have hbe : e ≠ b := fun h ↦ heA (h ▸ hb)
    have h₁ := edgeVertDist_le D (by omega) hbe (hAE b hb) (by omega) (hτ b hb)
      (hτV b hb)
    have h₂ := hfar _ (Or.inr ⟨b, hb, rfl⟩)
    omega
  have hins : insert e A ∈ 𝒜 := by
    refine ⟨insert_subset heZ hAmem.1, ?_, ?_⟩
    · rintro a (rfl | ha) b (rfl | hb) hab
      · exact absurd rfl hab
      · exact hclose b hb
      · have := hclose a ha
        change n < D.dist _ _
        rw [D.dist_comm]
        exact this
      · exact hAmem.2.1 a ha b hb hab
    · rintro a (rfl | ha) r hr
      · exact hfar r (Or.inl hr)
      · exact hAmem.2.2 a ha r hr
  exact heA (hmax.2 hins (subset_insert e A) (mem_insert e A))

/-- **Graph Minors XIX, (12.3)** (page 364): "There exists $X_2 \subseteq V(\Gamma^*)$ with $|X_2|
\le m + c(\Sigma_\chi)$ and $P^*
\subseteq X_2$ and an integer $t$ with $n \le t \le 5^{2m}n$, such that" `d(x₁, x₂) > 24t` for all
distinct
`x₁, x₂ ∈ X₂`, and for every `e ∈ Z` there exists `x ∈ X₂` with `d(e, x) ≤ t`. -/
theorem theorem_12_3_proof (D : TangleDatum cap χ) {m n k : ℕ} {ω₀ : α} (hn : 4 ≤ n)
    (hfl : D.IsFlawedInternally m n k ω₀) :
    ∃ X₂ ⊆ D.rad.G.V, X₂.ncard ≤ m + numCuffs S ∧ D.rad.poles ⊆ X₂ ∧ ∃ t, n ≤ t ∧
      t ≤ 5 ^ (2 * m) * n ∧ (∀ x₁ ∈ X₂, ∀ x₂ ∈ X₂, x₁ ≠ x₂ → 24 * t < D.vDist x₁ x₂) ∧
      ∀ e ∈ D.largeEdges k ω₀, ∃ x ∈ X₂, D.edgeVertDist e x ≤ t := by
  classical
  obtain ⟨hr₁, hr₂, hfd, hno⟩ := hfl
  have h25 : 5 ^ (2 * m + 2) * n = 25 * (5 ^ (2 * m) * n) := by rw [pow_add]; ring
  have hle5 : n ≤ 5 ^ (2 * m) * n := Nat.le_mul_of_pos_left _ (by positivity)
  have hrep : n < D.rep := by omega
  obtain ⟨X₁, hX₁G, hX₁c, hX₁p, hX₁c'⟩ := theorem_12_2_proof D hn hrep hno
  set c := numCuffs S with hc
  set K := m + c with hK
  have hX₁fin : X₁.Finite := D.rad.G.finite_V.subset hX₁G
  let 𝓕 : Set (Set Shat) := {Y | Y ⊆ X₁ ∧ D.rad.poles ⊆ Y ∧
    ∀ e ∈ D.largeEdges k ω₀, ∃ x ∈ Y, D.edgeVertDist e x ≤ 5 ^ (2 * K - 2 * Y.ncard) * n}
  have h𝓕fin : 𝓕.Finite := hX₁fin.finite_subsets.subset fun _ h ↦ h.1
  have hX₁𝓕 : X₁ ∈ 𝓕 := by
    refine ⟨subset_rfl, hX₁p, fun e he ↦ ?_⟩
    obtain ⟨x, hx, hd⟩ := hX₁c' e he
    exact ⟨x, hx, hd.trans (Nat.le_mul_of_pos_left _ (by positivity))⟩
  obtain ⟨Y, -, hmin⟩ := h𝓕fin.exists_le_minimal hX₁𝓕
  obtain ⟨hYX, hYp, hYc⟩ := hmin.1
  have hYfin : Y.Finite := hX₁fin.subset hYX
  have hYle : Y.ncard ≤ K := (ncard_le_ncard hYX hX₁fin).trans hX₁c
  have hYge : c ≤ Y.ncard := by
    rw [hc, ← D.ncard_poles]
    exact ncard_le_ncard hYp hYfin
  set t := 5 ^ (2 * K - 2 * Y.ncard) * n with ht
  have htn : n ≤ t := Nat.le_mul_of_pos_left _ (by positivity)
  have ht5 : t ≤ 5 ^ (2 * m) * n :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hkey : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → b ∉ D.rad.poles → D.vDist a b ≤ 24 * t → False := by
    intro a ha b hb hab hbp hd
    have hYb : (Y \ {b}).ncard = Y.ncard - 1 := ncard_sdiff_singleton_of_mem hb
    have hYpos : 1 ≤ Y.ncard := (ncard_pos hYfin).mpr ⟨b, hb⟩
    have hmem : Y \ {b} ∈ 𝓕 := by
      refine ⟨sdiff_subset.trans hYX, fun p hp ↦ ⟨hYp hp, fun h ↦ hbp (h ▸ hp)⟩, fun e he ↦ ?_⟩
      have hexp : 5 ^ (2 * K - 2 * (Y \ {b}).ncard) * n = 25 * t := by
        have : 2 * K - 2 * (Y \ {b}).ncard = (2 * K - 2 * Y.ncard) + 2 := by omega
        rw [this, pow_add, ht]
        ring
      rw [hexp]
      obtain ⟨x, hx, hdx⟩ := hYc e he
      by_cases hxb : x = b
      · subst hxb
        refine ⟨a, ⟨ha, hab⟩, ?_⟩
        have hatom := D.atomOf_mem (hX₁G (hYX hb))
        have htri := dist_triangle D (by omega) (a := cap.emb '' e)
          (c := D.rad.atomOf a) hatom
        have hcomm : D.dist (D.rad.atomOf x) (D.rad.atomOf a) = D.vDist a x := D.dist_comm _ _
        change D.dist _ _ ≤ _
        have hdx' : D.dist (cap.emb '' e) (D.rad.atomOf x) ≤ t := hdx
        omega
      · exact ⟨x, ⟨hx, hxb⟩, hdx.trans (by omega)⟩
    exact (hmin.2 hmem sdiff_subset hb).2 rfl
  refine ⟨Y, hYX.trans hX₁G, by omega, hYp, t, htn, ht5, ?_, hYc⟩
  intro x₁ h₁ x₂ h₂ hne
  by_contra hle
  push Not at hle
  by_cases hp₂ : x₂ ∈ D.rad.poles
  · by_cases hp₁ : x₁ ∈ D.rad.poles
    · exact hfd ⟨hr₁, hr₂, x₁, hp₁, x₂, hp₂, hne, by omega⟩
    · exact hkey x₂ h₂ x₁ h₁ hne.symm hp₁ ((D.dist_comm _ _).trans_le hle)
  · exact hkey x₁ h₁ x₂ h₂ hne hp₂ hle

end Restraints

end TangleDatum

end GraphMinor.GM19

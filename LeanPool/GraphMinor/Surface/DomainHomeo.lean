/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DomainPair

/-!
# A homeomorphism of `O`-arcs extends to their closed domains

`exists_homeomorph_closedInner`: every homeomorphism between two `O`-arcs of the plane extends to a
homeomorphism between their closed domains. This is the heart of the Schoenflies theorem.

Start from the pair `(F, F')`. Cut the left domains until they are small with `cutTree_small`,
matching each cut on the right. Then do the same with the sides exchanged. Repeating this gives
states `S_n` with mesh tending to `0` on both sides, each refining the last. The closed sets
`R_n = ⋃ (closure W × closure W')` over the pairs of `S_n` decrease, and their intersection is the
graph of a bijection: two domains of `S_n` that contain a point meet on their boundaries, and the
boundary maps then give a common point of the partners. The two projections of the compact set
`⋂ R_n` are homeomorphisms.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

variable {F₀ F₀' : Set ℂ} {h₀ k₀ : ℂ → ℂ}

/-- Each pair of `S'` lies in a pair of `S`. -/
def Refines (S' S : Set (Set ℂ × Set ℂ)) : Prop :=
  ∀ q ∈ S', ∃ r ∈ S, closedInner q.1 ⊆ closedInner r.1 ∧ closedInner q.2 ⊆ closedInner r.2

theorem Refines.trans {S₁ S₂ S₃ : Set (Set ℂ × Set ℂ)} (h : Refines S₁ S₂) (h' : Refines S₂ S₃) :
    Refines S₁ S₃ := by
  intro q hq
  obtain ⟨r, hr, h1, h2⟩ := h q hq
  obtain ⟨s, hs, h3, h4⟩ := h' r hr
  exact ⟨s, hs, h1.trans h3, h2.trans h4⟩

theorem Refines.refl (S : Set (Set ℂ × Set ℂ)) : Refines S S :=
  fun q hq => ⟨q, hq, Subset.rfl, Subset.rfl⟩

theorem Refines.swap {S' S : Set (Set ℂ × Set ℂ)} (h : Refines S' S) :
    Refines (Prod.swap '' S') (Prod.swap '' S) := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨r, hr, h1, h2⟩ := h q hq
  exact ⟨_, ⟨r, hr, rfl⟩, h2, h1⟩

/-- Following a tree of cuts from one pair of a state. -/
theorem IsPairing.refine {P : Set ℂ → Prop} {F : Set ℂ} (ht : CutTree P F) :
    ∀ {S : Set (Set ℂ × Set ℂ)} {h k : ℂ → ℂ}, IsPairing F₀ F₀' h₀ k₀ S h k → ∀ {F' : Set ℂ},
      (F, F') ∈ S → ∃ (S' : Set (Set ℂ × Set ℂ)) (h' k' : ℂ → ℂ), IsPairing F₀ F₀' h₀ k₀ S' h' k' ∧
        (∀ q ∈ S, q ≠ (F, F') → q ∈ S') ∧
        ∀ q ∈ S', (q ∈ S ∧ q ≠ (F, F')) ∨
          (P (inner q.1) ∧ closedInner q.1 ⊆ closedInner F ∧ closedInner q.2 ⊆ closedInner F') := by
  induction ht with
  | @leaf F hp =>
    intro S h k P' F' hq
    refine ⟨S, h, k, P', fun q hq' _ => hq', fun q hq' => ?_⟩
    by_cases he : q = (F, F')
    · subst he
      exact Or.inr ⟨hp, Subset.rfl, Subset.rfl⟩
    · exact Or.inl ⟨hq', he⟩
  | @node F a b e c _ _ ih₁ ih₂ =>
    intro S h k P' F' hq
    obtain ⟨φ⟩ := P'.oarc _ hq
    have J := isJordanParts φ
    obtain ⟨e', h₁, k₁, P₁, g2, g3, hne, hn1, hn2⟩ := P'.cut hq c
    obtain ⟨-, f2, f3, -, -, -⟩ := c.closedInner_facts J
    obtain ⟨S₂, h₂, k₂, P₂, h21, h22⟩ := ih₁ P₁ (Or.inl rfl)
    have hb₂ : (side b e, side (h ∘ b) e') ∈ S₂ := h21 _ (Or.inr (Or.inl rfl)) (Ne.symm hne)
    obtain ⟨S₃, h₃, k₃, P₃, h31, h32⟩ := ih₂ P₂ hb₂
    refine ⟨S₃, h₃, k₃, P₃, ?_, ?_⟩
    · intro q hqS hqne
      have hq1 : q ∈ S \ {(F, F')} := ⟨hqS, hqne⟩
      refine h31 q (h21 q (Or.inr (Or.inr hq1)) fun he => hn1 (he ▸ hq1)) fun he => hn2 (he ▸ hq1)
    · intro q hqS
      rcases h32 q hqS with ⟨hq2, hne2⟩ | ⟨hp, h1, h2⟩
      · rcases h22 q hq2 with ⟨hq1, hne1⟩ | ⟨hp, h1, h2⟩
        · rcases hq1 with he | he | he
          · exact absurd he hne1
          · exact absurd he hne2
          · exact Or.inl he
        · exact Or.inr ⟨hp, h1.trans f2, h2.trans g2⟩
      · exact Or.inr ⟨hp, h1.trans f3, h2.trans g3⟩

/-- All left domains of a finite part of a state can be made small. -/
private theorem IsPairing.make_small_aux {ε : ℝ} (hε : 0 < ε) {T : Set (Set ℂ × Set ℂ)}
    (hT : T.Finite) : ∀ {S : Set (Set ℂ × Set ℂ)} {h k : ℂ → ℂ}, IsPairing F₀ F₀' h₀ k₀ S h k →
      T ⊆ S → ∃ (S' : Set (Set ℂ × Set ℂ)) (h' k' : ℂ → ℂ), IsPairing F₀ F₀' h₀ k₀ S' h' k' ∧
        Refines S' S ∧ ∀ q ∈ S', q ∈ S \ T ∨ ∀ x ∈ inner q.1, ∀ y ∈ inner q.1, dist x y < ε := by
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    intro S h k P _
    exact ⟨S, h, k, P, Refines.refl S, fun q hq => Or.inl ⟨hq, fun h => h⟩⟩
  | @insert p T hpT _ ih =>
    intro S h k P hsub
    have hpS : p ∈ S := hsub (mem_insert _ _)
    have hpS' : (p.1, p.2) ∈ S := hpS
    obtain ⟨S₁, h₁, k₁, P₁, h1, h2⟩ := P.refine (cutTree_small (P.oarc p hpS) hε) hpS'
    have hTS₁ : T ⊆ S₁ := fun q hq => h1 q (hsub (mem_insert_of_mem _ hq))
      (fun he => hpT (by
        have he' : q = p := he
        exact he' ▸ hq))
    obtain ⟨S₂, h₂, k₂, P₂, h3, h4⟩ := ih P₁ hTS₁
    refine ⟨S₂, h₂, k₂, P₂, h3.trans ?_, fun q hq => ?_⟩
    · intro q hq
      rcases h2 q hq with ⟨hqS, -⟩ | ⟨-, h5, h6⟩
      · exact ⟨q, hqS, Subset.rfl, Subset.rfl⟩
      · exact ⟨p, hpS, h5, h6⟩
    · rcases h4 q hq with ⟨hq1, hq2⟩ | hsm
      · rcases h2 q hq1 with ⟨hqS, hne⟩ | ⟨hp, -, -⟩
        · left
          refine ⟨hqS, ?_⟩
          rintro (he | he)
          · exact hne he
          · exact hq2 he
        · exact Or.inr hp
      · exact Or.inr hsm

/-- Two points of the closure of a set of small diameter are close. -/
private theorem dist_le_of_closure {U : Set ℂ} {ε : ℝ} (hU : ∀ x ∈ U, ∀ y ∈ U, dist x y < ε)
    {x y : ℂ} (hx : x ∈ closure U) (hy : y ∈ closure U) : dist x y ≤ ε := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨x', hx', h1⟩ := Metric.mem_closure_iff.mp hx (η / 2) (half_pos hη)
  obtain ⟨y', hy', h2⟩ := Metric.mem_closure_iff.mp hy (η / 2) (half_pos hη)
  have h3 := hU x' hx' y' hy'
  have h4 := dist_triangle x x' y
  have h5 := dist_triangle x' y' y
  rw [dist_comm y' y] at h5
  linarith

/-- The diameters of the domains of a state are at most `ε`. -/
def Mesh (ε : ℝ) (S : Set (Set ℂ × Set ℂ)) : Prop :=
  ∀ q ∈ S, (∀ x ∈ closedInner q.1, ∀ y ∈ closedInner q.1, dist x y ≤ ε) ∧
    ∀ x ∈ closedInner q.2, ∀ y ∈ closedInner q.2, dist x y ≤ ε

/-- A state can be refined to one of mesh at most `ε`. -/
theorem IsPairing.exists_mesh {S : Set (Set ℂ × Set ℂ)} {h k : ℂ → ℂ}
    (P : IsPairing F₀ F₀' h₀ k₀ S h k) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S' : Set (Set ℂ × Set ℂ)) (h' k' : ℂ → ℂ), IsPairing F₀ F₀' h₀ k₀ S' h' k' ∧
      Refines S' S ∧ Mesh ε S' := by
  have hsmall : ∀ {G : Set ℂ}, Nonempty (Circle ≃ₜ G) →
      (∀ x ∈ inner G, ∀ y ∈ inner G, dist x y < ε) →
      ∀ x ∈ closedInner G, ∀ y ∈ closedInner G, dist x y ≤ ε := by
    rintro G ⟨φ⟩ hs x hx y hy
    have h1 : closedInner G = closure (inner G) := (isJordanParts φ).closure_inner.symm
    rw [h1] at hx hy
    exact dist_le_of_closure hs hx hy
  obtain ⟨S₁, h₁, k₁, P₁, r1, s1⟩ := P.make_small_aux hε P.fin Subset.rfl
  have hs1 : ∀ q ∈ S₁, ∀ x ∈ inner q.1, ∀ y ∈ inner q.1, dist x y < ε := fun q hq => by
    rcases s1 q hq with h' | h'
    · exact absurd h'.1 h'.2
    · exact h'
  obtain ⟨S₂, h₂, k₂, P₂, r2, s2⟩ := P₁.swap.make_small_aux hε P₁.swap.fin Subset.rfl
  have hs2 : ∀ q ∈ S₂, ∀ x ∈ inner q.1, ∀ y ∈ inner q.1, dist x y < ε := fun q hq => by
    rcases s2 q hq with h' | h'
    · exact absurd h'.1 h'.2
    · exact h'
  have P₃ := P₂.swap
  refine ⟨Prod.swap '' S₂, k₂, h₂, P₃, ?_, ?_⟩
  · refine Refines.trans ?_ r1
    have hsw := r2.swap
    rwa [image_image, show (fun x : Set ℂ × Set ℂ => Prod.swap (Prod.swap x)) = id from
      funext Prod.swap_swap, image_id] at hsw
  · rintro _ ⟨q, hq, rfl⟩
    refine ⟨?_, hsmall (P₂.oarc q hq) (hs2 q hq)⟩
    obtain ⟨r, ⟨r', hr', rfl⟩, h3, h4⟩ := r2 q hq
    exact fun x hx y hy => hsmall (P₁.oarc r' hr') (hs1 r' hr') x (h4 hx) y (h4 hy)

/-- The relation of a state. -/
def stateRel (S : Set (Set ℂ × Set ℂ)) : Set (ℂ × ℂ) :=
  ⋃ q ∈ S, closedInner q.1 ×ˢ closedInner q.2

/-- Two partners of one point are close. -/
theorem IsPairing.dist_le {S : Set (Set ℂ × Set ℂ)} {h k : ℂ → ℂ}
    (P : IsPairing F₀ F₀' h₀ k₀ S h k) {ε : ℝ} (hm : Mesh ε S) {x y y' : ℂ}
    (hy : (x, y) ∈ stateRel S) (hy' : (x, y') ∈ stateRel S) : dist y y' ≤ 2 * ε := by
  obtain ⟨q, hq, hxy⟩ := mem_iUnion₂.mp hy
  obtain ⟨q', hq', hxy'⟩ := mem_iUnion₂.mp hy'
  have hε : 0 ≤ ε := by
    have := (hm q hq).2 y hxy.2 y hxy.2
    rwa [dist_self] at this
  by_cases he : q = q'
  · subst he
    have := (hm q hq).2 y hxy.2 y' hxy'.2
    linarith
  · have hz := P.meet q hq q' hq' he ⟨hxy.1, hxy'.1⟩
    have h1 : h x ∈ q.2 := (P.bd q hq).1 hz.1
    have h2 : h x ∈ q'.2 := (P.bd q' hq').1 hz.2
    have h3 := (hm q hq).2 y hxy.2 (h x) (Or.inr h1)
    have h4 := (hm q' hq').2 (h x) (Or.inr h2) y' hxy'.2
    have h5 := dist_triangle y (h x) y'
    linarith

theorem stateRel_swap {S : Set (Set ℂ × Set ℂ)} {x y : ℂ} :
    (x, y) ∈ stateRel S ↔ (y, x) ∈ stateRel (Prod.swap '' S) := by
  constructor
  · intro hxy
    obtain ⟨q, hq, h1⟩ := mem_iUnion₂.mp hxy
    exact mem_iUnion₂.mpr ⟨_, ⟨q, hq, rfl⟩, h1.2, h1.1⟩
  · intro hxy
    obtain ⟨_, ⟨q, hq, rfl⟩, h1⟩ := mem_iUnion₂.mp hxy
    exact mem_iUnion₂.mpr ⟨q, hq, h1.2, h1.1⟩

theorem Mesh.swap {ε : ℝ} {S : Set (Set ℂ × Set ℂ)} (h : Mesh ε S) : Mesh ε (Prod.swap '' S) := by
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨(h q hq).2, (h q hq).1⟩

private theorem IsPairing.exists_partner {S : Set (Set ℂ × Set ℂ)} {h k : ℂ → ℂ}
    (P : IsPairing F₀ F₀' h₀ k₀ S h k) {x : ℂ} (hx : x ∈ closedInner F₀) :
    ∃ y, (x, y) ∈ stateRel S := by
  rw [← P.cov] at hx
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
  obtain ⟨φ⟩ := P.oarc' q hq
  obtain ⟨y, hy⟩ := (isJordanParts φ).isConnected_inner.nonempty
  exact ⟨y, mem_iUnion₂.mpr ⟨q, hq, hxq, Or.inl hy⟩⟩

private theorem isCompact_closedInner {G : Set ℂ} (hG : Nonempty (Circle ≃ₜ G)) :
    IsCompact (closedInner G) := by
  obtain ⟨φ⟩ := hG
  exact (isJordanParts φ).isCompact_closure_inner

private theorem IsPairing.isCompact_stateRel {S : Set (Set ℂ × Set ℂ)} {h k : ℂ → ℂ}
    (P : IsPairing F₀ F₀' h₀ k₀ S h k) : IsCompact (stateRel S) :=
  P.fin.isCompact_biUnion fun q hq =>
    (isCompact_closedInner (P.oarc q hq)).prod (isCompact_closedInner (P.oarc' q hq))

private theorem nested_inter {R : ℕ → Set (ℂ × ℂ)} (hanti : Antitone R)
    (hc : ∀ n, IsCompact (R n)) {A : Set (ℂ × ℂ)} (hA : IsClosed A)
    (hne : ∀ n, (R n ∩ A).Nonempty) : ((⋂ n, R n) ∩ A).Nonempty := by
  have h := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => R n ∩ A) (fun n => inter_subset_inter_left _ (hanti (Nat.le_succ n))) hne
    ((hc 0).inter_right hA) (fun n => (hc n).isClosed.inter hA)
  obtain ⟨z, hz⟩ := h
  exact ⟨z, mem_iInter.mpr fun n => (mem_iInter.mp hz n).1, (mem_iInter.mp hz 0).2⟩

/-- A sequence of states, each refining the last, with mesh tending to `0`. -/
private theorem exists_state_seq {F F' : Set ℂ} (hF : Nonempty (Circle ≃ₜ F))
    (hF' : Nonempty (Circle ≃ₜ F')) {h₀ k₀ : ℂ → ℂ} (m : BdMatch F F' h₀ k₀) :
    ∃ (S : ℕ → Set (Set ℂ × Set ℂ)) (h k : ℕ → ℂ → ℂ),
      (∀ n, IsPairing F F' h₀ k₀ (S n) (h n) (k n)) ∧ (∀ n, Refines (S (n + 1)) (S n)) ∧
      ∀ n : ℕ, Mesh (1 / ((n : ℝ) + 1)) (S (n + 1)) := by
  classical
  have P₀ : IsPairing F F' h₀ k₀ {(F, F')} h₀ k₀ := by
    refine ⟨finite_singleton _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · rintro _ rfl
      exact hF
    · rintro _ rfl
      exact hF'
    · rintro _ rfl
      exact m
    · simp
    · simp
    · rintro _ rfl _ rfl hne
      exact absurd rfl hne
    · rintro _ rfl _ rfl hne
      exact absurd rfl hne
    · rintro _ rfl z hz
      exact hz.2
    · rintro _ rfl z hz
      exact hz.2
  let St := {x : Set (Set ℂ × Set ℂ) × (ℂ → ℂ) × (ℂ → ℂ) // IsPairing F F' h₀ k₀ x.1 x.2.1 x.2.2}
  have hstep : ∀ (n : ℕ) (x : St), ∃ y : St, Refines y.1.1 x.1.1 ∧ Mesh (1 / ((n : ℝ) + 1)) y.1.1
    := by
    intro n x
    obtain ⟨S', h', k', P', r, hm⟩ := x.2.exists_mesh (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨⟨(S', h', k'), P'⟩, r, hm⟩
  choose next hnext1 hnext2 using hstep
  let X : ℕ → St := fun n => Nat.rec ⟨({(F, F')}, h₀, k₀), P₀⟩ next n
  have hXs : ∀ n, X (n + 1) = next n (X n) := fun n => rfl
  refine ⟨fun n => (X n).1.1, fun n => (X n).1.2.1, fun n => (X n).1.2.2, fun n => (X n).2,
    fun n => ?_, fun n => ?_⟩
  · change Refines (X (n + 1)).1.1 (X n).1.1
    rw [hXs]
    exact hnext1 n (X n)
  · change Mesh _ (X (n + 1)).1.1
    rw [hXs]
    exact hnext2 n (X n)

/-- **Extension to the closed domains.** Every homeomorphism between two `O`-arcs of the plane
extends to a homeomorphism between their closed domains. See the module docstring for the route. -/
theorem exists_homeomorph_closedInner {F F' : Set ℂ} (hF : Nonempty (Circle ≃ₜ F))
    (hF' : Nonempty (Circle ≃ₜ F')) {h₀ k₀ : ℂ → ℂ} (m : BdMatch F F' h₀ k₀) :
    ∃ Ψ : closedInner F ≃ₜ closedInner F', ∀ x : closedInner F, x.1 ∈ F → (Ψ x).1 = h₀ x.1 := by
  classical
  obtain ⟨S, hs, ks, hP, hRef, hMesh⟩ := exists_state_seq hF hF' m
  let R : ℕ → Set (ℂ × ℂ) := fun n => stateRel (S n)
  have hRanti : Antitone R := antitone_nat_of_succ_le fun n z hz => by
    obtain ⟨q, hq, h1⟩ := mem_iUnion₂.mp hz
    obtain ⟨r, hr, h2, h3⟩ := hRef n q hq
    exact mem_iUnion₂.mpr ⟨r, hr, h2 h1.1, h3 h1.2⟩
  have hRc : ∀ n, IsCompact (R n) := fun n => (hP n).isCompact_stateRel
  have hsub : ∀ n, ∀ z ∈ R n, z.1 ∈ closedInner F ∧ z.2 ∈ closedInner F' := by
    intro n z hz
    obtain ⟨q, hq, h1⟩ := mem_iUnion₂.mp hz
    exact ⟨(hP n).cov ▸ mem_iUnion₂.mpr ⟨q, hq, h1.1⟩, (hP n).cov' ▸ mem_iUnion₂.mpr ⟨q, hq, h1.2⟩⟩
  set Rinf := ⋂ n, R n with hRinf
  have hRinfc : IsCompact Rinf :=
    (hRc 0).of_isClosed_subset (isClosed_iInter fun n => (hRc n).isClosed) (iInter_subset _ 0)
  have hmemR : ∀ {z}, z ∈ Rinf → ∀ n, z ∈ R n := fun hz n => mem_iInter.mp hz n
  have hsmall : ∀ {a b : ℂ}, (∀ n : ℕ, dist a b ≤ 2 * (1 / ((n : ℝ) + 1))) → a = b := by
    intro a b hab
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
    refine (hab n).trans ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : 2 / ε < (n : ℝ) + 1 := by linarith
    rw [mul_one_div, div_le_iff₀ hpos]
    rw [div_lt_iff₀ hε] at h1
    linarith
  have huniq : ∀ {x y y' : ℂ}, (x, y) ∈ Rinf → (x, y') ∈ Rinf → y = y' := fun hy hy' =>
    hsmall fun n => (hP (n + 1)).dist_le (hMesh n) (hmemR hy _) (hmemR hy' _)
  have huniq' : ∀ {x x' y : ℂ}, (x, y) ∈ Rinf → (x', y) ∈ Rinf → x = x' := fun hy hy' =>
    hsmall fun n => (hP (n + 1)).swap.dist_le (hMesh n).swap (stateRel_swap.mp (hmemR hy _))
      (stateRel_swap.mp (hmemR hy' _))
  have hex : ∀ x ∈ closedInner F, ∃ y, (x, y) ∈ Rinf := by
    intro x hx
    obtain ⟨z, hz, hzA⟩ := nested_inter hRanti hRc (A := {x} ×ˢ univ)
      (isClosed_singleton.prod isClosed_univ) (fun n => by
        obtain ⟨y, hy⟩ := (hP n).exists_partner hx
        exact ⟨(x, y), hy, rfl, mem_univ _⟩)
    obtain ⟨z1, z2⟩ := z
    have : z1 = x := hzA.1
    subst this
    exact ⟨z2, hz⟩
  have hex' : ∀ y ∈ closedInner F', ∃ x, (x, y) ∈ Rinf := by
    intro y hy
    obtain ⟨z, hz, hzA⟩ := nested_inter hRanti hRc (A := univ ×ˢ {y})
      (isClosed_univ.prod isClosed_singleton) (fun n => by
        obtain ⟨x, hx⟩ := (hP n).swap.exists_partner hy
        exact ⟨(x, y), stateRel_swap.mpr hx, mem_univ _, rfl⟩)
    obtain ⟨z1, z2⟩ := z
    have : z2 = y := hzA.2
    subst this
    exact ⟨z1, hz⟩
  have : CompactSpace Rinf := isCompact_iff_compactSpace.mp hRinfc
  have hmem₀ : ∀ z : Rinf, z.1.1 ∈ closedInner F ∧ z.1.2 ∈ closedInner F' := fun z =>
    hsub 0 z.1 (hmemR z.2 0)
  let π₁ : Rinf → closedInner F := fun z => ⟨z.1.1, (hmem₀ z).1⟩
  let π₂ : Rinf → closedInner F' := fun z => ⟨z.1.2, (hmem₀ z).2⟩
  have hπ₁c : Continuous π₁ :=
    Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  have hπ₂c : Continuous π₂ :=
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _
  have hπ₁b : Function.Bijective π₁ := by
    constructor
    · rintro ⟨⟨x, y⟩, hz⟩ ⟨⟨x', y'⟩, hz'⟩ he
      have h1 : x = x' := congrArg Subtype.val he
      subst h1
      have h2 := huniq hz hz'
      subst h2
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := hex x hx
      exact ⟨⟨(x, y), hy⟩, rfl⟩
  have hπ₂b : Function.Bijective π₂ := by
    constructor
    · rintro ⟨⟨x, y⟩, hz⟩ ⟨⟨x', y'⟩, hz'⟩ he
      have h1 : y = y' := congrArg Subtype.val he
      subst h1
      have h2 := huniq' hz hz'
      subst h2
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hex' y hy
      exact ⟨⟨(x, y), hx⟩, rfl⟩
  have : CompactSpace (closedInner F) := isCompact_iff_compactSpace.mp (isCompact_closedInner hF)
  have : CompactSpace (closedInner F') := isCompact_iff_compactSpace.mp (isCompact_closedInner hF')
  let E₁ : Rinf ≃ₜ closedInner F :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective π₁ hπ₁b) hπ₁c
  let E₂ : Rinf ≃ₜ closedInner F' :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective π₂ hπ₂b) hπ₂c
  refine ⟨E₁.symm.trans E₂, fun x hxF => ?_⟩
  -- A point of `F` and its image lie in the limit relation.
  have hin : (x.1, h₀ x.1) ∈ Rinf := by
    refine mem_iInter.mpr fun n => ?_
    have hx : x.1 ∈ ⋃ q ∈ S n, closedInner q.1 := by
      rw [(hP n).cov]
      exact x.2
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
    have hxq1 : x.1 ∈ q.1 := (hP n).top q hq ⟨hxq, hxF⟩
    have h1 := (hP n).bd q hq |>.1 hxq1
    rw [(hP n).ext hxF] at h1
    exact mem_iUnion₂.mpr ⟨q, hq, hxq, Or.inr h1⟩
  obtain ⟨z, hz⟩ := hπ₁b.2 x
  have hzs : E₁.symm x = z := by
    apply E₁.injective
    rw [E₁.apply_symm_apply]
    exact hz.symm
  change (E₂ (E₁.symm x)).1 = h₀ x.1
  rw [hzs]
  have h1 : z.1.1 = x.1 := congrArg Subtype.val hz
  have h2 : (z.1.1, z.1.2) ∈ Rinf := z.2
  rw [h1] at h2
  exact huniq h2 hin

end GraphMinor.Surface

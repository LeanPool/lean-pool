/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section87
public import LeanPool.GraphMinor.GM11.Section81
public import LeanPool.GraphMinor.GM11.Section79

/-!
# Graph Minors XI, (8.8)

`theorem_8_8` says that the intersection and the union of two meeting extreme restraints are
simply-connected.
We follow the proof in the paper. The main step is `isPathConnected_inter`: the intersection is
arc-wise
connected. The walk lemmas come first. `runs_times` gives the vertices `v_i` of a perimeter walk as
points of
the collar, so that (8.1) applies to them. `exists_shortest` gives the walks `Q₁, Q₂` of the paper,
and
`walk_off` gives `U(Q₁) ∩ X₂ = {a₁, b₁}`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] {Γ : Drawing S}

/-- The steps of a curve along a walk. -/
theorem runs_times {φ : ℝ → S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → ∃ x : ℕ → ℝ, x 0 = a ∧ x W.length = b ∧
      (∀ i < W.length, x i < x (i + 1)) ∧ (∀ i ≤ W.length, φ (x i) ∈ W.support) ∧
      (∀ y ∈ W.support, ∃ i ≤ W.length, φ (x i) = y) ∧
      (∀ i < W.length, ∃ e ∈ W.edges, φ '' Ioo (x i) (x (i + 1)) = e) ∧
      ∀ e ∈ W.edges, ∃ i < W.length, φ '' Ioo (x i) (x (i + 1)) = e := by
  induction W with
  | nil hv =>
    rintro a b ⟨rfl, hu⟩
    refine ⟨fun _ => a, rfl, rfl, fun i hi => ?_, fun i _ => ?_, fun y hy => ⟨0, le_rfl, ?_⟩,
      fun i hi => ?_,
      fun e he => ?_⟩
    · simp [GraphWalk.length, GraphWalk.edges] at hi
    · simp [GraphWalk.support, hu]
    · simpa [GraphWalk.support, hu, eq_comm] using hy
    · simp [GraphWalk.length, GraphWalk.edges] at hi
    · simp [GraphWalk.edges] at he
  | @cons u y v e hlink rest ih =>
    rintro a b ⟨c, hac, hu, -, him, hrest⟩
    obtain ⟨x, h0, h1, hstep, hsup, hall, hedge, hedge'⟩ := ih hrest
    have hlen : (GraphWalk.cons hlink rest).length = rest.length + 1 := rfl
    refine ⟨fun i => Nat.casesOn i a x, rfl, by rw [hlen]; exact h1, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (_ | i) hi
      · change a < x 0
        rw [h0]
        exact hac
      · rw [hlen] at hi
        exact hstep i (by omega)
    · rintro (_ | i) hi
      · change φ a ∈ _
        rw [hu]
        exact List.mem_cons_self
      · rw [hlen] at hi
        exact List.mem_cons_of_mem _ (hsup i (by omega))
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨0, Nat.zero_le _, hu⟩
      · obtain ⟨i, hi, he⟩ := hall z hz
        exact ⟨i + 1, by rw [hlen]; omega, he⟩
    · rintro (_ | i) hi
      · refine ⟨e, List.mem_cons_self, ?_⟩
        change φ '' Ioo a (x 0) = e
        rw [h0]
        exact him
      · rw [hlen] at hi
        obtain ⟨f, hf, hfe⟩ := hedge i (by omega)
        exact ⟨f, List.mem_cons_of_mem _ hf, hfe⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · refine ⟨0, by rw [hlen]; omega, ?_⟩
        change φ '' Ioo a (x 0) = _
        rw [h0]
        exact him
      · obtain ⟨i, hi, hfe⟩ := hedge' f hf
        exact ⟨i + 1, by rw [hlen]; omega, hfe⟩

/-- Two vertices of a closed walk are joined by a walk. -/
theorem exists_walk_of_mem_support {α β : Type*} {G : Graph α β} {u a b : α}
    (W : GraphWalk G u u) (ha : a ∈ W.support) (hb : b ∈ W.support) : Nonempty (GraphWalk G a b)
      := by
  classical
  obtain ⟨A, B, rfl⟩ := GraphWalk.exists_append_of_mem W ha
  have hb' : b ∈ (B.append A).support := by
    rcases (GraphWalk.mem_support_append _ _).mp hb with h | h
    · exact (GraphWalk.mem_support_append _ _).mpr (Or.inr h)
    · exact (GraphWalk.mem_support_append _ _).mpr (Or.inl h)
  obtain ⟨P, -, -⟩ := GraphWalk.exists_append_of_mem (B.append A) hb'
  exact ⟨P⟩

/-- A simple walk from a vertex to itself has no edges. -/
theorem edges_eq_nil_of_isSimple {α β : Type*} {G : Graph α β} {u : α} {W : GraphWalk G u u}
    (hW : W.IsSimple) : W.edges = [] := by
  cases W with
  | nil _ => rfl
  | cons hl r =>
    exact ((List.nodup_cons.mp hW).1 r.end_mem_support).elim

/-- **A shortest walk between two disjoint sets.** It is simple, and it meets the two sets only at
its
ends. -/
theorem exists_shortest {α β : Type*} {G : Graph α β} {A B : Set α}
    (hne : ∃ a ∈ A, ∃ b ∈ B, Nonempty (GraphWalk G a b)) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ Q : GraphWalk G a b, Q.IsSimple ∧
      (∀ a' ∈ A, ∀ b' ∈ B, ∀ Q' : GraphWalk G a' b', Q.length ≤ Q'.length) ∧
      (∀ x ∈ Q.support, x ∈ A → x = a) ∧ (∀ x ∈ Q.support, x ∈ B → x = b) := by
  classical
  have hP : ∃ n, ∃ a ∈ A, ∃ b ∈ B, ∃ Q : GraphWalk G a b, Q.length = n := by
    obtain ⟨a, ha, b, hb, ⟨Q⟩⟩ := hne
    exact ⟨_, a, ha, b, hb, Q, rfl⟩
  obtain ⟨a, ha, b, hb, Q₀, hQ₀⟩ := Nat.find_spec hP
  have hmin : ∀ a' ∈ A, ∀ b' ∈ B, ∀ Q' : GraphWalk G a' b', Q₀.length ≤ Q'.length := by
    intro a' ha' b' hb' Q'
    rw [hQ₀]
    exact Nat.find_min' hP ⟨a', ha', b', hb', Q', rfl⟩
  obtain ⟨Q, hQs, hQv, hQe⟩ := GraphWalk.exists_isSimple Q₀
  have hle : Q.length ≤ Q₀.length := (hQs.edges_nodup.subperm hQe).length_le
  have hminQ : ∀ a' ∈ A, ∀ b' ∈ B, ∀ Q' : GraphWalk G a' b', Q.length ≤ Q'.length :=
    fun a' ha' b' hb' Q' => hle.trans (hmin a' ha' b' hb' Q')
  have hpos : ∀ {p q : α} (W : GraphWalk G p q), p ≠ q → 0 < W.length := by
    intro p q W hpq
    cases W with
    | nil _ => exact absurd rfl hpq
    | cons _ _ => simp [GraphWalk.length, GraphWalk.edges]
  refine ⟨a, ha, b, hb, Q, hQs, hminQ, ?_, ?_⟩
  · intro x hx hxA
    by_contra hne
    obtain ⟨P₁, P₂, rfl⟩ := GraphWalk.exists_append_of_mem Q hx
    have h₁ := hminQ x hxA b hb P₂
    have h₂ := hpos P₁ (Ne.symm hne)
    rw [GraphWalk.length_append] at h₁
    omega
  · intro x hx hxB
    by_contra hne
    obtain ⟨P₁, P₂, rfl⟩ := GraphWalk.exists_append_of_mem Q hx
    have h₁ := hminQ a ha x hxB P₁
    have h₂ := hpos P₂ hne
    rw [GraphWalk.length_append] at h₁
    omega

variable [T2Space S] {T : Set S}

omit [T2Space S] in
/-- A walk from a point of a closed nice set `T` with no vertex on `bd(T)` except its last stays in
`T`. -/
theorem walk_in (hTc : IsClosed T) (hTn : IsGammaNice Γ T) {w b : S} (Q : GraphWalk Γ.toGraph w b) :
    Q.IsSimple → (∀ x ∈ Q.support, x ≠ b → x ∉ frontier T) → w ∈ T →
      (∀ e ∈ Q.edges, e ⊆ T) ∧ ∀ x ∈ Q.support, x ∈ T := by
  induction Q with
  | nil _ =>
    intro _ _ hw
    refine ⟨fun e he => by simp [GraphWalk.edges] at he, fun x hx => ?_⟩
    obtain rfl : x = _ := by simpa [GraphWalk.support] using hx
    exact hw
  | @cons w y b e hl r ih =>
    intro hs hfr hw
    have hne : w ≠ b := fun h => (List.nodup_cons.mp hs).1 (h ▸ r.end_mem_support)
    have hwf := hfr w List.mem_cons_self hne
    have hwi : w ∈ interior T := by
      by_contra hni
      exact hwf ⟨subset_closure hw, hni⟩
    have hecl : w ∈ closure e := by
      have : w ∈ closure e ∩ Γ.V := by
        rw [hl.2.2.2]
        exact Or.inl rfl
      exact this.1
    have hycl : y ∈ closure e := by
      have : y ∈ closure e ∩ Γ.V := by
        rw [hl.2.2.2]
        exact Or.inr rfl
      exact this.1
    obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp hecl _ isOpen_interior hwi
    have heT : e ⊆ T := nice_atom hTn (Or.inl (Or.inr hl.1)) ⟨z, hze, interior_subset hzi⟩
    have hyT : y ∈ T := closure_minimal heT hTc hycl
    obtain ⟨h₁, h₂⟩ := ih hs.of_cons (fun x hx hxb => hfr x (List.mem_cons_of_mem _ hx) hxb) hyT
    refine ⟨?_, ?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact heT
      · exact h₁ f hf
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact h₂ x hx

omit [T2Space S] in
/-- A walk from a point outside a closed nice set `T` with no vertex on `bd(T)` except its last has
no edge
in `T`, and no vertex in `T` except its last. -/
theorem walk_out (hTn : IsGammaNice Γ T) (hTc : IsClosed T) {w b : S}
  (Q : GraphWalk Γ.toGraph w b) :
    Q.IsSimple → (∀ x ∈ Q.support, x ≠ b → x ∉ frontier T) → w ∉ T →
      (∀ e ∈ Q.edges, ¬ e ⊆ T) ∧ ∀ x ∈ Q.support, x ≠ b → x ∉ T := by
  induction Q with
  | nil _ =>
    intro _ _ hw
    refine ⟨fun e he => by simp [GraphWalk.edges] at he, fun x hx => ?_⟩
    obtain rfl : x = _ := by simpa [GraphWalk.support] using hx
    exact fun _ => hw
  | @cons w y b e hl r ih =>
    intro hs hfr hw
    have hne : w ≠ b := fun h => (List.nodup_cons.mp hs).1 (h ▸ r.end_mem_support)
    have hecl : w ∈ closure e := by
      have : w ∈ closure e ∩ Γ.V := by
        rw [hl.2.2.2]
        exact Or.inl rfl
      exact this.1
    have hycl : y ∈ closure e := by
      have : y ∈ closure e ∩ Γ.V := by
        rw [hl.2.2.2]
        exact Or.inr rfl
      exact this.1
    have heT : ¬ e ⊆ T := fun h => hw (closure_minimal h hTc hecl)
    by_cases hyb : y = b
    · subst hyb
      have hnil := edges_eq_nil_of_isSimple hs.of_cons
      refine ⟨fun f hf => ?_, fun x hx hxb => ?_⟩
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact heT
        · rw [hnil] at hf
          simp at hf
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hw
        · have hr : r.support = [y] := by
            cases r with
            | nil _ => rfl
            | cons _ _ => simp [GraphWalk.edges] at hnil
          rw [hr] at hx
          exact (hxb (List.mem_singleton.mp hx)).elim
    have hyf := hfr y (List.mem_cons_of_mem _ r.start_mem_support) hyb
    have hyT : y ∉ T := by
      intro hyT
      have hyi : y ∈ interior T := by
        by_contra hni
        exact hyf ⟨subset_closure hyT, hni⟩
      obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp hycl _ isOpen_interior hyi
      exact heT (nice_atom hTn (Or.inl (Or.inr hl.1)) ⟨z, hze, interior_subset hzi⟩)
    obtain ⟨h₁, h₂⟩ := ih hs.of_cons (fun x hx hxb => hfr x (List.mem_cons_of_mem _ hx) hxb) hyT
    refine ⟨?_, ?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact heT
      · exact h₁ f hf
    · intro x hx hxb
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact h₂ x hx hxb

omit [T2Space S] in
/-- A simple walk from a vertex in a closed nice set `T`, with no inner vertex on `bd(T)`, and with
an edge
not in `T`, has no edge in `T` and meets `T` only at its ends (up to its last vertex). This is the
step
`U(Q₁) ∩ X₂ = {a₁, b₁}` in the proof of (8.8). -/
theorem walk_off (hTc : IsClosed T) (hTn : IsGammaNice Γ T) {a b : S} (Q : GraphWalk Γ.toGraph a b)
    (hs : Q.IsSimple) (hab : a ≠ b) (hfr : ∀ x ∈ Q.support, x ∈ frontier T → x = a ∨ x = b)
      (ha : a ∈ T)
    (hno : ¬ ∀ e ∈ Q.edges, e ⊆ T) :
    (∀ e ∈ Q.edges, ¬ e ⊆ T) ∧ ∀ x ∈ Q.support, x ∈ T → x = a ∨ x = b := by
  cases Q with
  | nil _ => exact absurd rfl hab
  | @cons _ y _ e hl r =>
    have hanot : a ∉ r.support := (List.nodup_cons.mp hs).1
    have hr : ∀ x ∈ r.support, x ≠ b → x ∉ frontier T := by
      intro x hx hxb hxf
      rcases hfr x (List.mem_cons_of_mem _ hx) hxf with rfl | h
      · exact hanot hx
      · exact hxb h
    have hycl : y ∈ closure e := by
      have : y ∈ closure e ∩ Γ.V := by
        rw [hl.2.2.2]
        exact Or.inr rfl
      exact this.1
    by_cases heT : e ⊆ T
    · have hyT : y ∈ T := closure_minimal heT hTc hycl
      obtain ⟨h₁, -⟩ := walk_in hTc hTn r hs.of_cons hr hyT
      refine (hno fun f hf => ?_).elim
      rcases List.mem_cons.mp hf with rfl | hf
      · exact heT
      · exact h₁ f hf
    by_cases hyb : y = b
    · subst hyb
      have hnil := edges_eq_nil_of_isSimple hs.of_cons
      have hrs : r.support = [y] := by
        cases r with
        | nil _ => rfl
        | cons _ _ => simp [GraphWalk.edges] at hnil
      refine ⟨fun f hf => ?_, fun x hx _ => ?_⟩
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact heT
        · rw [hnil] at hf
          simp at hf
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl rfl
        · rw [hrs] at hx
          exact Or.inr (List.mem_singleton.mp hx)
    have hyf := hr y r.start_mem_support hyb
    have hyT : y ∉ T := by
      intro hyT
      have hyi : y ∈ interior T := by
        by_contra hni
        exact hyf ⟨subset_closure hyT, hni⟩
      obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp hycl _ isOpen_interior hyi
      exact heT (nice_atom hTn (Or.inl (Or.inr hl.1)) ⟨z, hze, interior_subset hzi⟩)
    obtain ⟨h₁, h₂⟩ := walk_out hTn hTc r hs.of_cons hr hyT
    refine ⟨fun f hf => ?_, fun x hx hxT => ?_⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact heT
      · exact h₁ f hf
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · by_contra hn
        push Not at hn
        exact h₂ x hx hn.2 hxT

omit [T2Space S] in
/-- If all edges of a walk from a point of a closed set are in the set, then so are its vertices. -/
theorem support_mem_of_edges (hTc : IsClosed T) {a b : S} (Q : GraphWalk Γ.toGraph a b) :
    (∀ e ∈ Q.edges, e ⊆ T) → a ∈ T → ∀ x ∈ Q.support, x ∈ T := by
  induction Q with
  | nil _ =>
    intro _ ha x hx
    obtain rfl : x = _ := by simpa [GraphWalk.support] using hx
    exact ha
  | @cons a y b e hl r ih =>
    intro he ha x hx
    have hycl : y ∈ closure e := by
      have : y ∈ closure e ∩ Γ.V := by
        rw [hl.2.2.2]
        exact Or.inr rfl
      exact this.1
    have hyT : y ∈ T := closure_minimal (he e List.mem_cons_self) hTc hycl
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih (fun f hf => he f (List.mem_cons_of_mem _ hf)) hyT x hx

variable [ConnectedSpace S] {k : ℕ} {ins : Drawing S → Set S}

/-- `Γ ∩ bd(X)` is connected, for a restraint `X`: this is the reason the walks `Q₁, Q₂` exist in
the proof
of (8.8). -/
theorem exists_walk_in_bd (hS : IsClosedSurface S)
    {X : Set S} (hr : IsRestraint Γ ins k X) {a b : S}
    (ha : a ∈ (Γ.interSet (frontier X)).V) (hb : b ∈ (Γ.interSet (frontier X)).V) :
    Nonempty (GraphWalk (Γ.interSet (frontier X)).toGraph a b) := by
  classical
  obtain ⟨u, W, -, -, -, -, hwd⟩ := hr.exists_walk hS
  have hH : (walkDrawing Γ W).IsSubdrawing Γ := walkDrawing_isSubdrawing Γ W
  obtain ⟨W', hs, -⟩ := hH.exists_walk_down W
    (fun x hx => by
      rw [walkDrawing_V]
      exact hx)
    (fun e he => by
      rw [walkDrawing_E]
      exact he)
  have hmem : ∀ {x}, x ∈ (Γ.interSet (frontier X)).V → x ∈ W'.support := by
    intro x hx
    rw [← hwd, walkDrawing_V] at hx
    rw [hs]
    exact hx
  have hw : Nonempty (GraphWalk (walkDrawing Γ W).toGraph a b) :=
    exists_walk_of_mem_support W' (hmem ha) (hmem hb)
  rwa [hwd] at hw

omit [T2Space S] [ConnectedSpace S] in
/-- **The first step of (8.8).** A point of `X₁ ∩ X₂` is joined in `X₁ ∩ X₂` to a point of `bd(X₁)`,
unless
`X₂ ⊆ X₁`. -/
theorem exists_joined_frontier {X₁ X₂ : Set S} (hc₁ : IsClosed X₁) (hp₂ : IsPathConnected X₂)
  (hsub : ¬ X₂ ⊆ X₁)
    {x : S} (hx : x ∈ X₁ ∩ X₂) : ∃ p ∈ frontier X₁, p ∈ pathComponentIn (X₁ ∩ X₂) x := by
  obtain ⟨b, hb₂, hbn⟩ : ∃ b ∈ X₂, b ∉ pathComponentIn (X₁ ∩ X₂) x := by
    by_contra hall
    push Not at hall
    exact hsub fun y hy => (pathComponentIn_subset (hall y hy)).1
  obtain ⟨γ, hγ⟩ := hp₂.joinedIn x hx.2 b hb₂
  let T₀ : Set I := γ ⁻¹' X₁ᶜ
  have hT₀o : IsOpen T₀ := hc₁.isOpen_compl.preimage γ.continuous
  have hT₀ne : T₀.Nonempty := by
    by_contra hemp
    have hall : ∀ t, γ t ∈ X₁ := fun t => by
      by_contra hn
      exact hemp ⟨t, hn⟩
    exact hbn ⟨γ, fun t => ⟨hall t, hγ t⟩⟩
  obtain ⟨α, hα, hleast⟩ := isClosed_closure.isCompact.exists_isLeast (hT₀ne.mono subset_closure)
  have hbelow : ∀ r, r < α → γ r ∈ X₁ := fun r hr => by
    by_contra hn
    exact not_le.mpr hr (hleast (subset_closure hn))
  have hαX : γ α ∈ X₁ := by
    by_contra hn
    have hαT : α ∈ T₀ := hn
    have hα0 : (0 : I) < α := by
      refine unitInterval.pos_iff_ne_zero.mpr fun h0 => hn ?_
      rw [h0, γ.source]
      exact hx.1
    have hne : (nhdsWithin α (Iio α)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hα0⟩
    have hmem : T₀ ∩ Iio α ∈ nhdsWithin α (Iio α) :=
      Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hT₀o.mem_nhds hαT)) self_mem_nhdsWithin
    obtain ⟨r, hr₁, hr₂⟩ := Filter.nonempty_of_mem hmem
    exact hr₁ (hbelow r hr₂)
  have hfr : γ α ∈ frontier X₁ := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hαX, ?_⟩
    exact image_closure_subset_closure_image γ.continuous (mem_image_of_mem _ hα) |> fun h =>
      closure_mono (image_preimage_subset _ _) h
  refine ⟨γ α, hfr, ?_⟩
  refine ⟨⟨⟨fun t => γ (t * α), by fun_prop⟩, by simp, by simp⟩, fun t => ⟨?_, hγ _⟩⟩
  have hle : t * α ≤ α := unitInterval.mul_le_right
  rcases eq_or_lt_of_le hle with he | hlt
  · change γ (t * α) ∈ X₁
    rw [he]
    exact hαX
  · exact hbelow _ hlt

omit [ConnectedSpace S] in
theorem interSet_isSub : (Γ.interSet T).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _

omit [ConnectedSpace S] in
theorem mem_interSet_V {y : S} (hy : y ∈ Γ.V) (hT : y ∈ T) : y ∈ (Γ.interSet T).V
  := Or.inl ⟨⟨hy, hT⟩, hy⟩

omit [ConnectedSpace S] in
theorem edge_subset_of_interSet {a b : S} (Q : GraphWalk (Γ.interSet T).toGraph a b) {e : Set S}
    (he : e ∈ Q.edges) : e ∈ Γ.E ∧ e ⊆ T := by
  have h₁ : e ∈ (Γ.span _ _).E := mem_E_of_mem_edges Q he
  rw [Γ.span_E] at h₁
  exact h₁.1

omit [ConnectedSpace S] in
omit [T2Space S] in
/-- A point of a nice set `T` in the closure of an edge not in `T` is on `bd(T)`. -/
theorem frontier_of_edge_off (hTn : IsGammaNice Γ T) {e : Set S} (he : e ∈ Γ.E)
  (hoff : ¬ e ⊆ T) {w : S}
    (hw : w ∈ closure e) (hwT : w ∈ T) : w ∈ frontier T := by
  refine ⟨subset_closure hwT, fun hi => hoff ?_⟩
  obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp hw _ isOpen_interior hi
  exact nice_atom hTn (Or.inl (Or.inr he)) ⟨z, hze, interior_subset hzi⟩

/-- A walk with all its edges in a closed set `T` joins its ends in `T`. -/
theorem joined_of_walk (hTc : IsClosed T) {a b : S} (Q : GraphWalk Γ.toGraph a b) :
    (∀ e ∈ Q.edges, e ⊆ T) → a ∈ T → b ∈ pathComponentIn T a := by
  induction Q with
  | nil _ =>
    intro _ ha
    exact mem_pathComponentIn_self ha
  | @cons a y b e hl r ih =>
    intro he ha
    have hin : ∀ {x}, x ∈ closure e ∩ Γ.V → x ∈ closure e := fun h => h.1
    have hacl : a ∈ closure e := hin (by rw [hl.2.2.2]; exact Or.inl rfl)
    have hycl : y ∈ closure e := hin (by rw [hl.2.2.2]; exact Or.inr rfl)
    have heT : e ⊆ T := he e List.mem_cons_self
    have hsub : closure e ⊆ T := closure_minimal heT hTc
    have hy : y ∈ pathComponentIn T a :=
      (isPathConnected_closure_edge hl.1).subset_pathComponentIn hacl hsub hycl
    have := ih (fun f hf => he f (List.mem_cons_of_mem _ hf)) (hsub hycl)
    rwa [pathComponentIn_congr hy] at this

omit [T2Space S] [ConnectedSpace S] in
/-- **The steps (2) and (3) of (8.8).** Let `v₀, …, v_n` be points of `X`, in cyclic order, in the
sense that
two connected subsets of `X` through alternate points meet. Let `J ⊆ X`. Among the components of
`J`, choose
one, say `D`, whose first and last indices `i, j` are closest. Then no component of `J` meets
`{v_i, …, v_j}` and also a `v_q` with `q` outside of `i, …, j`, the two sets of points are disjoint,
and the
only component that meets `{v_i, …, v_j}` is `D`. -/
theorem exists_interval {J X : Set S} (hJX : J ⊆ X) {n : ℕ} {v : ℕ → S} (hvX : ∀ p ≤ n, v p ∈ X)
    (hne : ∃ p ≤ n, v p ∈ J)
    (hcross : ∀ p q r s, p ≤ q → q ≤ r → r ≤ s → s ≤ n → ∀ P Q : Set S, IsPathConnected P
      → IsPathConnected Q →
      P ⊆ X → Q ⊆ X → v p ∈ P → v r ∈ P → v q ∈ Q → v s ∈ Q → (P ∩ Q).Nonempty) :
    ∃ i j, i ≤ j ∧ j ≤ n ∧ v i ∈ J ∧ v j ∈ pathComponentIn J (v i) ∧
      (∀ q ≤ n, v q ∈ pathComponentIn J (v i) → i ≤ q ∧ q ≤ j) ∧
      (∀ p q, i ≤ p → p ≤ j → q ≤ n → ¬ (i ≤ q ∧ q ≤ j) → v p ≠ v q ∧ v q ∉ pathComponentIn J
        (v p)) ∧
      ∀ p, i ≤ p → p ≤ j → v p ∈ J → v p ∈ pathComponentIn J (v i) := by
  classical
  let Good : ℕ → ℕ → Prop := fun i j => i ≤ j ∧ j ≤ n ∧ v i ∈ J ∧ v j ∈ pathComponentIn J (v i) ∧
    ∀ q ≤ n, v q ∈ pathComponentIn J (v i) → i ≤ q ∧ q ≤ j
  have hgood : ∀ m ≤ n, v m ∈ J → ∃ i j, Good i j ∧ pathComponentIn J (v i) = pathComponentIn J
    (v m) := by
    intro m hm hmJ
    let F := (Finset.range (n + 1)).filter fun q => v q ∈ pathComponentIn J (v m)
    have hmF : m ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      mem_pathComponentIn_self hmJ⟩
    have hF : F.Nonempty := ⟨m, hmF⟩
    have hmin := (Finset.mem_filter.mp (F.min'_mem hF))
    have hmax := (Finset.mem_filter.mp (F.max'_mem hF))
    have hc : pathComponentIn J (v (F.min' hF)) = pathComponentIn J (v m)
      := pathComponentIn_congr hmin.2
    refine ⟨F.min' hF, F.max' hF, ⟨F.min'_le_max' hF, ?_, pathComponentIn_subset hmin.2, ?_, ?_⟩,
      hc⟩
    · have := Finset.mem_range.mp hmax.1
      omega
    · rw [hc]
      exact hmax.2
    · intro q hq hqc
      rw [hc] at hqc
      have hqF : q ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hqc⟩
      exact ⟨F.min'_le q hqF, F.le_max' q hqF⟩
  have hex : ∃ d, ∃ i j, Good i j ∧ j - i = d := by
    obtain ⟨m, hm, hmJ⟩ := hne
    obtain ⟨i, j, hG, -⟩ := hgood m hm hmJ
    exact ⟨_, i, j, hG, rfl⟩
  obtain ⟨i, j, hG, hd⟩ := Nat.find_spec hex
  have hmin : ∀ a b, Good a b → j - i ≤ b - a := fun a b h => by
    rw [hd]
    exact Nat.find_min' hex ⟨a, b, h, rfl⟩
  obtain ⟨hij, hjn, hiJ, hjD, hrange⟩ := hG
  have hsub : pathComponentIn J (v i) ⊆ X := pathComponentIn_subset.trans hJX
  have hDp : IsPathConnected (pathComponentIn J (v i)) := isPathConnected_pathComponentIn hiJ
  have hself : v i ∈ pathComponentIn J (v i) := mem_pathComponentIn_self hiJ
  have hmeet : ∀ p q, i ≤ p → p ≤ j → q ≤ n → ¬ (i ≤ q ∧ q ≤ j) → ∀ P : Set S, IsPathConnected P
    → P ⊆ X →
      v p ∈ P → v q ∈ P → (P ∩ pathComponentIn J (v i)).Nonempty := by
    intro p q hp hp' hq hout P hP hPX hpP hqP
    by_cases hqi : q < i
    · exact hcross q i p j hqi.le hp hp' hjn P _ hP hDp hPX hsub hqP hpP hself hjD
    · have hjq : j ≤ q := by omega
      have := hcross i p j q hp hp' hjq hq _ P hDp hP hsub hPX hself hjD hpP hqP
      rwa [inter_comm] at this
  have hsep : ∀ p q, i ≤ p → p ≤ j → q ≤ n → ¬ (i ≤ q ∧ q ≤ j) →
      v p ≠ v q ∧ v q ∉ pathComponentIn J (v p) := by
    intro p q hp hp' hq hout
    constructor
    · intro he
      obtain ⟨z, hz, hzD⟩ := hmeet p q hp hp' hq hout {v p} (isPathConnected_singleton _)
        (singleton_subset_iff.mpr (hvX p (by omega))) rfl he.symm
      obtain rfl : z = v p := hz
      exact hout (hrange q hq (he ▸ hzD))
    · intro hqc
      have hpJ : v p ∈ J := by
        by_contra hn
        have : pathComponentIn J (v p) = ∅ := by
          by_contra hne'
          exact hn (pathComponentIn_nonempty_iff.mp (nonempty_iff_ne_empty.mpr hne'))
        rw [this] at hqc
        exact hqc
      obtain ⟨z, hz, hzD⟩ := hmeet p q hp hp' hq hout _ (isPathConnected_pathComponentIn hpJ)
        (pathComponentIn_subset.trans hJX) (mem_pathComponentIn_self hpJ) hqc
      have heq : pathComponentIn J (v p) = pathComponentIn J (v i) :=
        (pathComponentIn_congr hz).symm.trans (pathComponentIn_congr hzD)
      exact hout (hrange q hq (heq ▸ hqc))
  refine ⟨i, j, hij, hjn, hiJ, hjD, hrange, hsep, fun p hp hp' hpJ => ?_⟩
  by_contra hn
  have hpn : p ≤ n := by omega
  obtain ⟨a, b, ⟨hab, hbn, haJ, hbD, hr⟩, hcomp⟩ := hgood p hpn hpJ
  have hpc : v p ∈ pathComponentIn J (v a) := by
    rw [hcomp]
    exact mem_pathComponentIn_self hpJ
  obtain ⟨hap, hpb⟩ := hr p hpn hpc
  have hnotD : ∀ {z}, z ∈ pathComponentIn J (v a) → z ∉ pathComponentIn J (v i) := by
    intro z hz hzD
    have : pathComponentIn J (v a) = pathComponentIn J (v i) :=
      (pathComponentIn_congr hz).symm.trans (pathComponentIn_congr hzD)
    exact hn (this ▸ hpc)
  have hane : a ≠ i := fun h => hnotD (mem_pathComponentIn_self haJ) (h ▸ hself)
  have hbne : b ≠ j := fun h => hnotD hbD (h ▸ hjD)
  by_cases ha : a < i
  · refine (hsep p a hp hp' (by omega) (by omega)).2 ?_
    rw [← hcomp]
    exact mem_pathComponentIn_self haJ
  by_cases hb : j < b
  · refine (hsep p b hp hp' hbn (by omega)).2 ?_
    rw [← hcomp]
    exact hbD
  have := hmin a b ⟨hab, hbn, haJ, hbD, hr⟩
  omega

/-- The vertices `v₀, …, v_n` and edges of a perimeter walk of a restraint, with the properties that
the
proof of (8.8) needs. The last property comes from (8.1). -/
theorem exists_vertices (hS : IsClosedSurface S)
    {X : Set S} (hr : IsRestraint Γ ins k X) :
    ∃ (n : ℕ) (v : ℕ → S), v 0 = v n ∧ (∀ p ≤ n, v p ∈ (Γ.interSet (frontier X)).V) ∧
      (∀ y ∈ (Γ.interSet (frontier X)).V, ∃ p ≤ n, v p = y) ∧
      (∀ p < n, ∃ e ∈ Γ.E, e ⊆ frontier X ∧ v p ∈ closure e ∧ v (p + 1) ∈ closure e) ∧
      (∀ y ∈ frontier X, (∃ p ≤ n, v p = y) ∨ ∃ p < n, ∃ e ∈ Γ.E, e ⊆ frontier X ∧ y ∈ e
        ∧ v p ∈ closure e) ∧
      ∀ p q r s, p ≤ q → q ≤ r → r ≤ s → s ≤ n → ∀ P Q : Set S, IsPathConnected P
        → IsPathConnected Q →
        P ⊆ X → Q ⊆ X → v p ∈ P → v r ∈ P → v q ∈ Q → v s ∈ Q → (P ∩ Q).Nonempty := by
  classical
  obtain ⟨u, W, hW, -, -, -, hwd⟩ := hr.exists_walk hS
  obtain ⟨h, hinj, hoff, hrng, -, hcase⟩ := hW
  rw [subBd_eq_frontier] at hrng
  have hXc := hr.isClosed
  have hXs := hr.isSimplyConnected
  have hfX : frontier X ⊆ X := hXc.frontier_subset
  have hbot : ∀ z, h (z, 0) ∈ X := fun z => hfX (hrng ▸ mem_range_self z)
  obtain ⟨A, hA, hXA⟩ := exists_openDisc_around hS hXc hr.isGammaNice hXs hr.ne_univ
  let φ : ℝ → S := fun t => h (circlePt t, 0)
  have hφc : Continuous φ := h.continuous.comp (continuous_circlePt.prodMk continuous_const)
  have hper : φ 1 = φ 0 := by
    change h (circlePt 1, 0) = h (circlePt 0, 0)
    simp [circlePt]
  have hrun : ∃ b : ℝ, (b = 0 ∨ b = 1) ∧ RunsAlongOn Γ φ 0 b W := by
    rcases hcase with ⟨hl, hc⟩ | ⟨-, hrun⟩
    · cases W with
      | nil _ => exact ⟨0, Or.inl rfl, rfl, hc _⟩
      | cons _ _ => simp [GraphWalk.length, GraphWalk.edges] at hl
    · exact ⟨1, Or.inr rfl, hrun⟩
  obtain ⟨b, hb, hrun⟩ := hrun
  obtain ⟨x, hx0, hxn, hstep, hsup, hall, hedge, hedge'⟩ := runs_times W hrun
  have hmono : ∀ {p q}, p ≤ q → q ≤ W.length → x p ≤ x q := by
    intro p q hpq
    induction q, hpq using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ q hq ih =>
      intro hl
      exact (ih (by omega)).trans (hstep q (by omega)).le
  have hx0' : ∀ {p}, p ≤ W.length → 0 ≤ x p := fun hp => hx0 ▸ hmono (Nat.zero_le _) hp
  have hxb : ∀ {p}, p ≤ W.length → x p ≤ 1 := fun hp => by
    have := hmono hp le_rfl
    rw [hxn] at this
    rcases hb with rfl | rfl
    · exact this.trans zero_le_one
    · exact this
  have hV : ∀ y, y ∈ (Γ.interSet (frontier X)).V ↔ y ∈ W.support := by
    intro y
    rw [← hwd, walkDrawing_V]
    rfl
  have hE : ∀ e ∈ W.edges, e ∈ Γ.E ∧ e ⊆ frontier X := by
    intro e he
    have h₁ : e ∈ (walkDrawing Γ W).E := by
      rw [walkDrawing_E]
      exact he
    rw [hwd] at h₁
    change e ∈ (Γ.span _ _).E at h₁
    rw [Γ.span_E] at h₁
    exact h₁.1
  have hcl : ∀ p < W.length, ∀ e, φ '' Ioo (x p) (x (p + 1)) = e → φ (x p) ∈ closure e ∧
      φ (x (p + 1)) ∈ closure e := by
    rintro p hp _ rfl
    have hlt := hstep p hp
    have hsub : φ '' Icc (x p) (x (p + 1)) ⊆ closure (φ '' Ioo (x p) (x (p + 1))) := by
      rw [← closure_Ioo hlt.ne]
      exact image_closure_subset_closure_image hφc
    exact ⟨hsub ⟨_, left_mem_Icc.mpr hlt.le, rfl⟩, hsub ⟨_, right_mem_Icc.mpr hlt.le, rfl⟩⟩
  refine ⟨W.length, fun p => φ (x p), ?_, fun p hp => (hV _).mpr (hsup p hp),
    fun y hy => hall y ((hV y).mp hy),
    fun p hp => ?_, fun y hy => ?_, ?_⟩
  · change φ (x 0) = φ (x W.length)
    rw [hx0, hxn]
    rcases hb with rfl | rfl
    · rfl
    · exact hper.symm
  · obtain ⟨e, he, hee⟩ := hedge p hp
    exact ⟨e, (hE e he).1, (hE e he).2, hcl p hp e hee⟩
  · have hy' : y ∈ (walkDrawing Γ W).U := by
      rw [hwd, frontier_interSet hS hXc hr.isGammaNice]
      exact hy
    rcases (mem_walkDrawing_U Γ W).mp hy' with hys | ⟨e, he, hye⟩
    · exact Or.inl (hall y hys)
    by_cases hyV : y ∈ Γ.V
    · exact Or.inl (hall y ((hV y).mp (mem_interSet_V hyV hy)))
    · have hye' : y ∈ e := by
        have : y ∈ closure e \ Γ.V := ⟨hye, hyV⟩
        rwa [Γ.closure_diff_V (hE e he).1] at this
      obtain ⟨p, hp, hpe⟩ := hedge' e he
      exact Or.inr ⟨p, hp, e, (hE e he).1, (hE e he).2, hye', (hcl p hp e hpe).1⟩
  · intro p q r s hpq hqr hrs hsn P Q hP hQ hPX hQX hpP hrP hqQ hsQ
    have hrn : r ≤ W.length := by omega
    have hqn : q ≤ W.length := by omega
    have hpn : p ≤ W.length := by omega
    refine theorem_8_1_proof hS hA hXA hXs.1 hinj hoff hbot (hmono hpq hqn) (hmono hqr hrn)
      (hmono hrs hsn) ?_
      hP hQ hPX hQX hpP hrP hqQ hsQ
    linarith [hxb hsn, hx0' hpn]

/-- **The step of (8.7) in (8.8).** Let `X` be a restraint as in `IsNearExtreme`, and `Q` a simple
walk in `Γ ∩ T`
between two vertices of `Γ ∩ bd(X)`, with no inner vertex on `bd(X)`, and with some edge not in `X`.
Then some walk
of `Γ ∩ bd(X)` between the ends of `Q` has length less than that of `Q` plus `d`. -/
theorem exists_shorter (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X : Set S} {d : ℕ} (hX : IsNearExtreme Γ ins k d X) {a b : S}
    (ha : a ∈ (Γ.interSet (frontier X)).V) (hb : b ∈ (Γ.interSet (frontier X)).V) (hab : a ≠ b)
    (hHa : a ∈ X) (Q : GraphWalk (Γ.interSet T).toGraph a b) (hQ : Q.IsSimple)
    (hfr : ∀ x ∈ Q.support, x ∈ frontier X → x = a ∨ x = b) (hno : ¬ ∀ e ∈ Q.edges, e ⊆ X) :
    ∃ R : GraphWalk (Γ.interSet (frontier X)).toGraph a b, R.length < Q.length + d := by
  obtain ⟨Q', hsup, hed⟩ := (interSet_isSub (Γ := Γ) (T := T)).exists_walk_up Q
  have hs' : Q'.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hsup]
    exact hQ
  obtain ⟨h₁, h₂⟩ := walk_off hX.1.isClosed hX.1.isGammaNice Q' hs' hab (by rwa [hsup]) hHa
    (by rwa [hed])
  obtain ⟨R, hR⟩ := exists_walk_near' hS hs hX ha hb hab Q' h₁ h₂
  refine ⟨R, ?_⟩
  have hl : Q'.length = Q.length := by simp [GraphWalk.length, hed]
  omega

/-- The first part of (8.8) of Graph Minors XI (page 98): "`X₁ ∩ X₂` is arc-wise connected". The
proof gives
more: it needs that `X₂` is extreme, and of `X₁` only that no restraint `Y ⊇ X₁` has `l(Y) < l(X₁)`.
-/
theorem isPathConnected_inter (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X₁ X₂ : Set S} (h₁ : IsNearExtreme Γ ins k 1 X₁)
    (h₂ : IsExtremeRestraint Γ ins k X₂) (hne : (X₁ ∩ X₂).Nonempty) : IsPathConnected (X₁ ∩ X₂)
      := by
  classical
  have r₁ := h₁.1
  have r₂ := h₂.1
  have c₁ := r₁.isClosed
  have c₂ := r₂.isClosed
  have n₂ := r₂.isGammaNice
  by_cases hsub : X₂ ⊆ X₁
  · rw [inter_eq_right.mpr hsub]
    exact r₂.isSimplyConnected.1
  obtain ⟨n, v, hcyc, hvV, hVv, hedge, hcov, hcross⟩ := exists_vertices hS r₁
  have hJc : IsClosed (X₁ ∩ X₂) := c₁.inter c₂
  have hf₁ : frontier X₁ ⊆ X₁ := c₁.frontier_subset
  have hf₂ : frontier X₂ ⊆ X₂ := c₂.frontier_subset
  have hvf : ∀ p ≤ n, v p ∈ frontier X₁ := fun p hp =>
    interSet_U_subset isClosed_frontier ((Γ.interSet (frontier X₁)).V_subset_U (hvV p hp))
  have hvΓ : ∀ p ≤ n, v p ∈ Γ.V := fun p hp => (interSet_isSub (Γ := Γ)).1 (hvV p hp)
  have hstepJ : ∀ e ∈ Γ.E, e ⊆ frontier X₁ → e ⊆ X₂ → ∀ {a b : S}, a ∈ closure e → b ∈ closure e →
      b ∈ pathComponentIn (X₁ ∩ X₂) a := fun e he h h' a b ha hb =>
    (isPathConnected_closure_edge he).subset_pathComponentIn ha
      (subset_inter (closure_minimal (h.trans hf₁) c₁) (closure_minimal h' c₂)) hb
  -- The step (1): each component contains a vertex of the perimeter walk.
  have hone : ∀ x ∈ X₁ ∩ X₂, ∃ p ≤ n, v p ∈ X₁ ∩ X₂ ∧ v p ∈ pathComponentIn (X₁ ∩ X₂) x := by
    intro x hx
    obtain ⟨y, hyf, hyc⟩ := exists_joined_frontier c₁ r₂.isSimplyConnected.1 hsub hx
    have hyJ := pathComponentIn_subset hyc
    rcases hcov y hyf with ⟨p, hp, rfl⟩ | ⟨p, hp, e, he, hef, hye, hpe⟩
    · exact ⟨p, hp, hyJ, hyc⟩
    · have heX : e ⊆ X₂ := nice_atom n₂ (Or.inl (Or.inr he)) ⟨y, hye, hyJ.2⟩
      have h₃ := hstepJ e he hef heX (subset_closure hye) hpe
      rw [pathComponentIn_congr hyc] at h₃
      exact ⟨p, by omega, pathComponentIn_subset h₃, h₃⟩
  obtain ⟨p₀, hp₀, hv₀, -⟩ := hone _ hne.some_mem
  obtain ⟨i, j, hij, hjn, hiJ, hjD, hrange, hsep, hin⟩ := exists_interval inter_subset_left
    (fun p hp => hf₁ (hvf p hp)) ⟨p₀, hp₀, hv₀⟩ hcross
  have hself := mem_pathComponentIn_self hiJ
  suffices hall : ∀ p ≤ n, v p ∈ X₁ ∩ X₂ → v p ∈ pathComponentIn (X₁ ∩ X₂) (v i) by
    have heq : pathComponentIn (X₁ ∩ X₂) (v i) = X₁ ∩ X₂ := by
      refine subset_antisymm pathComponentIn_subset fun x hx => ?_
      obtain ⟨p, hp, hpJ, hpc⟩ := hone x hx
      rw [← pathComponentIn_congr (hall p hp hpJ), pathComponentIn_congr hpc]
      exact mem_pathComponentIn_self hx
    rw [← heq]
    exact isPathConnected_pathComponentIn hiJ
  by_cases hend : i = 0 ∨ j = n
  · have h0 : v 0 ∈ pathComponentIn (X₁ ∩ X₂) (v i) := by
      rcases hend with h | h
      · exact h ▸ hself
      · rw [hcyc, ← h]
        exact hjD
    have hnD : v n ∈ pathComponentIn (X₁ ∩ X₂) (v i) := hcyc ▸ h0
    have hi0 := (hrange 0 (Nat.zero_le _) h0).1
    have hjn' := (hrange n le_rfl hnD).2
    exact fun p hp hpJ => hin p (by omega) (by omega) hpJ
  push Not at hend
  obtain ⟨hi0, hjn'⟩ := hend
  -- The step (4).
  obtain ⟨e₁, he₁, hf₁e, ha₁, hb₁⟩ := hedge (i - 1) (by omega)
  have hi1 : i - 1 + 1 = i := by omega
  rw [hi1] at hb₁
  have hoff₁ : ¬ e₁ ⊆ X₂ := fun h => by
    have := (hrange (i - 1) (by omega) (hstepJ e₁ he₁ hf₁e h hb₁ ha₁)).1
    omega
  obtain ⟨e₂, he₂, hf₂e, ha₂, hb₂⟩ := hedge j (by omega)
  have hoff₂ : ¬ e₂ ⊆ X₂ := fun h => by
    have h₃ := hstepJ e₂ he₂ hf₂e h ha₂ hb₂
    rw [pathComponentIn_congr hjD] at h₃
    have := (hrange (j + 1) (by omega) h₃).2
    omega
  -- The sets `Z₁, Z₂`.
  let Z₁ : Set S := {y | y ∈ Γ.V ∧ y ∈ frontier X₁ ∧ y ∈ frontier X₂ ∧ ∃ p, i ≤ p ∧ p ≤ j ∧ v p = y}
  let Z₂ : Set S := {y | y ∈ Γ.V ∧ y ∈ frontier X₁ ∧ y ∈ frontier X₂ ∧ ∃ q ≤ n, ¬ (i ≤ q ∧ q ≤ j)
    ∧ v q = y}
  have hdis : Disjoint Z₁ Z₂ := by
    refine disjoint_left.mpr ?_
    rintro y ⟨-, -, -, p, hp, hp', rfl⟩ ⟨-, -, -, q, hq, hout, he⟩
    exact (hsep p q hp hp' hq hout).1 he.symm
  have hsepZ : ∀ a ∈ Z₁, ∀ b ∈ Z₂, b ∉ pathComponentIn (X₁ ∩ X₂) a := by
    rintro _ ⟨-, -, -, p, hp, hp', rfl⟩ _ ⟨-, -, -, q, hq, hout, rfl⟩
    exact (hsep p q hp hp' hq hout).2
  have hclass : ∀ y ∈ Γ.V, y ∈ frontier X₁ → y ∈ frontier X₂ → y ∈ Z₁ ∨ y ∈ Z₂ := by
    intro y hyV hy₁ hy₂
    obtain ⟨p, hp, rfl⟩ := hVv y (mem_interSet_V hyV hy₁)
    by_cases hin' : i ≤ p ∧ p ≤ j
    · exact Or.inl ⟨hyV, hy₁, hy₂, p, hin'.1, hin'.2, rfl⟩
    · exact Or.inr ⟨hyV, hy₁, hy₂, p, hp, hin', rfl⟩
  have hZ₁ : v i ∈ Z₁ := ⟨hvΓ i (by omega), hvf i (by omega),
    frontier_of_edge_off n₂ he₁ hoff₁ hb₁ hiJ.2, i, le_rfl, hij, rfl⟩
  have hZ₂ : ¬ Z₂.Nonempty := by
    rintro ⟨b, hb⟩
    have hVZ : ∀ {T' : Set S} {y}, y ∈ Γ.V → y ∈ T' → y ∈ (Γ.interSet T').V := fun h h'
      => mem_interSet_V h h'
    obtain ⟨a₁, ha₁', b₁, hb₁', Q₁, hs₁, hm₁, hA₁, hB₁⟩ := exists_shortest
      (G := (Γ.interSet (frontier X₁)).toGraph) ⟨v i, hZ₁, b, hb,
        exists_walk_in_bd hS r₁ (hVZ hZ₁.1 hZ₁.2.1) (hVZ hb.1 hb.2.1)⟩
    obtain ⟨a₂, ha₂', b₂, hb₂', Q₂, hs₂, hm₂, hA₂, hB₂⟩ := exists_shortest
      (G := (Γ.interSet (frontier X₂)).toGraph) ⟨v i, hZ₁, b, hb,
        exists_walk_in_bd hS r₂ (hVZ hZ₁.1 hZ₁.2.2.1) (hVZ hb.1 hb.2.2.1)⟩
    have hne₁ : a₁ ≠ b₁ := fun h => disjoint_left.mp hdis ha₁' (h ▸ hb₁')
    have hne₂ : a₂ ≠ b₂ := fun h => disjoint_left.mp hdis ha₂' (h ▸ hb₂')
    have hno₁ : ¬ ∀ e ∈ Q₁.edges, e ⊆ X₂ := by
      intro hall
      obtain ⟨Q', -, hed⟩ := (interSet_isSub (Γ := Γ) (T := frontier X₁)).exists_walk_up Q₁
      refine hsepZ a₁ ha₁' b₁ hb₁' (joined_of_walk hJc Q' (fun e he => ?_) ⟨hf₁ ha₁'.2.1,
        hf₂ ha₁'.2.2.1⟩)
      rw [hed] at he
      exact subset_inter ((edge_subset_of_interSet Q₁ he).2.trans hf₁) (hall e he)
    have hno₂ : ¬ ∀ e ∈ Q₂.edges, e ⊆ X₁ := by
      intro hall
      obtain ⟨Q', -, hed⟩ := (interSet_isSub (Γ := Γ) (T := frontier X₂)).exists_walk_up Q₂
      refine hsepZ a₂ ha₂' b₂ hb₂' (joined_of_walk hJc Q' (fun e he => ?_) ⟨hf₁ ha₂'.2.1,
        hf₂ ha₂'.2.2.1⟩)
      rw [hed] at he
      exact subset_inter (hall e he) ((edge_subset_of_interSet Q₂ he).2.trans hf₂)
    have hfr₁ : ∀ x ∈ Q₁.support, x ∈ frontier X₂ → x = a₁ ∨ x = b₁ := by
      intro x hx hxf
      have hxV := mem_V_of_mem_support Q₁ hx
      rcases hclass x ((interSet_isSub (Γ := Γ)).1 hxV)
        (interSet_U_subset isClosed_frontier ((Γ.interSet (frontier X₁)).V_subset_U hxV)) hxf with
          h | h
      · exact Or.inl (hA₁ x hx h)
      · exact Or.inr (hB₁ x hx h)
    have hfr₂ : ∀ x ∈ Q₂.support, x ∈ frontier X₁ → x = a₂ ∨ x = b₂ := by
      intro x hx hxf
      have hxV := mem_V_of_mem_support Q₂ hx
      rcases hclass x ((interSet_isSub (Γ := Γ)).1 hxV) hxf
        (interSet_U_subset isClosed_frontier ((Γ.interSet (frontier X₂)).V_subset_U hxV)) with h | h
      · exact Or.inl (hA₂ x hx h)
      · exact Or.inr (hB₂ x hx h)
    obtain ⟨R₂, hR₂⟩ := exists_shorter hS hs h₂.near (hVZ ha₁'.1 ha₁'.2.2.1)
      (hVZ hb₁'.1 hb₁'.2.2.1) hne₁ (hf₂ ha₁'.2.2.1) Q₁ hs₁ hfr₁ hno₁
    obtain ⟨R₁, hR₁⟩ := exists_shorter hS hs h₁ (hVZ ha₂'.1 ha₂'.2.1)
      (hVZ hb₂'.1 hb₂'.2.1) hne₂ (hf₁ ha₂'.2.1) Q₂ hs₂ hfr₂ hno₂
    have := hm₂ a₁ ha₁' b₁ hb₁' R₂
    have := hm₁ a₂ ha₂' b₂ hb₂' R₁
    omega
  have hnoZ : ∀ q ≤ n, ¬ (i ≤ q ∧ q ≤ j) → v q ∉ frontier X₂ := fun q hq hout hqf =>
    hZ₂ ⟨v q, hvΓ q hq, hvf q hq, hqf, q, hq, hout, rfl⟩
  have hstep : ∀ {e w}, e ∈ Γ.E → ¬ e ⊆ X₂ → w ∈ closure e → w ∉ frontier X₂ → w ∉ X₂ :=
    fun he hoff hw hwf hwX => hwf (frontier_of_edge_off n₂ he hoff hw hwX)
  have hdown : ∀ d q, q + d + 1 = i → v q ∉ X₂ := by
    intro d
    induction d with
    | zero =>
      intro q hq
      obtain rfl : q = i - 1 := by omega
      exact hstep he₁ hoff₁ ha₁ (hnoZ _ (by omega) (by omega))
    | succ d ih =>
      intro q hq
      have hy := ih (q + 1) (by omega)
      obtain ⟨e, he, -, hqe, hqe'⟩ := hedge q (by omega)
      exact hstep he (fun h => hy (closure_minimal h c₂ hqe')) hqe (hnoZ _ (by omega) (by omega))
  have hup : ∀ d, j + 1 + d ≤ n → v (j + 1 + d) ∉ X₂ := by
    intro d
    induction d with
    | zero =>
      intro hq
      exact hstep he₂ hoff₂ hb₂ (hnoZ _ (by omega) (by omega))
    | succ d ih =>
      intro hq
      have hy := ih (by omega)
      obtain ⟨e, he, -, hqe, hqe'⟩ := hedge (j + 1 + d) (by omega)
      exact hstep he (fun h => hy (closure_minimal h c₂ hqe)) hqe' (hnoZ _ (by omega) (by omega))
  intro p hp hpJ
  by_cases hin' : i ≤ p ∧ p ≤ j
  · exact hin p hin'.1 hin'.2 hpJ
  by_cases hpi : p < i
  · exact (hdown (i - p - 1) p (by omega) hpJ.2).elim
  · have heq : j + 1 + (p - j - 1) = p := by omega
    have := hup (p - j - 1) (by omega)
    rw [heq] at this
    exact (this hpJ.2).elim

/-- The proof of (8.8), for `X₁` as in `isPathConnected_inter`. -/
theorem simplyConnected_inter_union (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X₁ X₂ : Set S} (h₁ : IsNearExtreme Γ ins k 1 X₁)
    (h₂ : IsExtremeRestraint Γ ins k X₂) (hne : (X₁ ∩ X₂).Nonempty) :
    IsSimplyConnectedSet (X₁ ∩ X₂) ∧ IsSimplyConnectedSet (X₁ ∪ X₂) := by
  have r₁ := h₁.1
  have r₂ := h₂.1
  have hp := isPathConnected_inter hS hs h₁ h₂ hne
  have hu : IsSimplyConnectedSet (X₁ ∪ X₂) := theorem_7_8_proof r₁.isSimplyConnected
    r₂.isSimplyConnected hp
    (nice_31 S hS Γ X₁ X₂ r₁.isClosed r₂.isClosed r₁.isGammaNice r₂.isGammaNice
      r₁.isSimplyConnected hp)
  have hne' : X₁ ∪ X₂ ≠ univ := by
    have := theorem_8_4_proof hS hs r₁ r₂ r₂
    rwa [union_assoc, union_self] at this
  exact ⟨theorem_7_9_proof hS r₁.isSimplyConnected r₂.isSimplyConnected
    (r₁.isClosed.inter r₂.isClosed)
    (r₁.isGammaNice.inter r₂.isGammaNice) hp hne', hu⟩

/-- **(8.8)** of Graph Minors XI (page 98): "If $X_1, X_2$ are extreme restraints and $X_1 \cap X_2
\ne \emptyset$ then $X_1 \cap X_2$
and $X_1 \cup X_2$ are simply-connected." -/
theorem theorem_8_8_proof (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X₁ X₂ : Set S} (h₁ : IsExtremeRestraint Γ ins k X₁)
    (h₂ : IsExtremeRestraint Γ ins k X₂) (hne : (X₁ ∩ X₂).Nonempty) :
    IsSimplyConnectedSet (X₁ ∩ X₂) ∧ IsSimplyConnectedSet (X₁ ∪ X₂) :=
  simplyConnected_inter_union hS hs (h₁.near_one) h₂ hne

end GraphMinor.GM11

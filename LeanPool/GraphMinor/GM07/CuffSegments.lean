/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffFrame

/-!
# The subpaths `N_i(C)`

Graph Minors VII, (5.9), page 235: "we may choose mutually vertex-disjoint subpaths $N_1(C), \dots,
N_{k(C)}(C)$ of $N(C)$, such that (i) $V(N_1(C)) \cup \dots \cup V(N_{k(C)}(C)) = V(N(C))$, and (ii)
for $1 \le i \le k(C)$, exactly $v$ of $P_1, \dots, P_{vk(C)}$ intersect $N(C)$ in a subpath of
$N_i(C)$".

We first do the counting on a line. Each of the `P_i` meets the circuit in an interval of positions,
and we cut the positions into `k` groups by counting the intervals from the left.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

/-- **Groups of intervals.** Let `v * k` disjoint nonempty intervals of positions be given. Then the
positions can be cut into `k` groups, in order along the line, so that each group holds `v` of the
intervals. -/
theorem exists_interval_groups {m k v : ℕ} (hk : 0 < k) (hv : 0 < v) (A : Fin (v * k) → Set ℕ)
  (hne : ∀ ι, (A ι).Nonempty) (hlt : ∀ ι, ∀ x ∈ A ι, x < m) (hint : ∀ ι, (A ι).OrdConnected)
    (hdis : ∀ ι ι', ι ≠ ι' → Disjoint (A ι) (A ι')) :
    ∃ g : ℕ → ℕ, Monotone g ∧ (∀ x, g x < k) ∧ (∀ i < k, ∃ x < m, g x = i) ∧ ∀ i < k, ∃ f : Fin v
      → Fin (v * k), Injective f ∧ ∀ t, ∀ x ∈ A (f t), g x = i := by
  classical
  have hNe : ∀ ι, sInf (A ι) ∈ A ι := fun ι => Nat.sInf_mem (hne ι)
  let a : Fin (v * k) → ℕ := fun ι => sInf (A ι)
  have ha : ∀ ι, a ι ∈ A ι := hNe
  have hle : ∀ ι, ∀ x ∈ A ι, a ι ≤ x := fun ι x hx => Nat.sInf_le hx
  have hainj : Injective a := fun ι ι' he => by
    by_contra hne'
    exact disjoint_left.mp (hdis ι ι' hne') (ha ι) (he ▸ ha ι')
  let c : ℕ → ℕ := fun x => (Finset.univ.filter fun ι => a ι ≤ x).card
  have hcm : Monotone c := fun x y hxy => Finset.card_le_card fun ι hι => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι ⊢
    exact hι.trans hxy
  have hclt : ∀ {x y}, (∃ ι, x < a ι ∧ a ι ≤ y) → c x < c y := fun {x y} ⟨ι, h1, h2⟩ => by
    refine Finset.card_lt_card ⟨fun ι' hι => ?_, fun hs => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι ⊢
      exact hι.trans (h1.le.trans h2)
    · have := hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
      have := (Finset.mem_filter.mp this).2
      omega
  have hcpos : ∀ ι, 0 < c (a ι) := fun ι => Finset.card_pos.mpr ⟨ι, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, le_rfl⟩⟩
  have hcle : ∀ x, c x ≤ v * k := fun x => by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin (v * k))) fun ι => a ι ≤ x
    simpa using this
  have hconst : ∀ ι, ∀ x ∈ A ι, c x = c (a ι) := fun ι x hx => by
    refine Finset.card_bij (fun ι' _ => ι') (fun ι' hι' => ?_) (fun _ _ _ _ h => h) (fun ι' hι'
      => ⟨ι', ?_, rfl⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι' ⊢
      by_contra hgt
      push Not at hgt
      have h1 : a ι' ∈ A ι := (hint ι).out (ha ι) hx ⟨hgt.le, hι'⟩
      by_cases he : ι = ι'
      · subst he
        omega
      · exact disjoint_left.mp (hdis ι ι' he) h1 (ha ι')
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι' ⊢
      exact hι'.trans (hle ι x hx)
  let rank : Fin (v * k) → Fin (v * k) := fun ι => ⟨c (a ι) - 1, by
    have := hcle (a ι)
    have := hcpos ι
    omega⟩
  have hrinj : Injective rank := fun ι ι' he => by
    have h1 : c (a ι) - 1 = c (a ι') - 1 := congrArg Fin.val he
    have h2 := hcpos ι
    have h3 := hcpos ι'
    by_contra hne'
    have h4 : a ι ≠ a ι' := fun h => hne' (hainj h)
    rcases lt_or_gt_of_ne h4 with h5 | h5
    · have := hclt (x := a ι) (y := a ι') ⟨ι', h5, le_rfl⟩
      omega
    · have := hclt (x := a ι') (y := a ι) ⟨ι, h5, le_rfl⟩
      omega
  have hrbij : Surjective rank := Finite.injective_iff_surjective.mp hrinj
  let g : ℕ → ℕ := fun x => min ((c x - 1) / v) (k - 1)
  refine ⟨g, fun x y hxy => ?_, fun x => by simp only [g]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · refine min_le_min (Nat.div_le_div_right ?_) le_rfl
    have := hcm hxy
    omega
  · have hb : v * i < v * k := Nat.mul_lt_mul_of_pos_left hi hv
    obtain ⟨ι, hι⟩ := hrbij ⟨v * i, hb⟩
    have h1 : c (a ι) - 1 = v * i := congrArg Fin.val hι
    refine ⟨a ι, hlt ι _ (ha ι), ?_⟩
    simp only [g]
    rw [h1, Nat.mul_div_cancel_left _ hv]
    omega
  · have hb : ∀ t : Fin v, v * i + t.1 < v * k := fun t => by
      have h1 : v * (i + 1) ≤ v * k := Nat.mul_le_mul_left _ hi
      rw [Nat.mul_succ] at h1
      omega
    let f : Fin v → Fin (v * k) := fun t => (Equiv.ofBijective rank ⟨hrinj, hrbij⟩).symm ⟨v * i +
      t.1, hb t⟩
    have hf : ∀ t, c (a (f t)) - 1 = v * i + t.1 := fun t => by
      have : rank (f t) = ⟨v * i + t.1, hb t⟩ := (Equiv.ofBijective rank ⟨hrinj,
        hrbij⟩).apply_symm_apply _
      exact congrArg Fin.val this
    refine ⟨f, fun t t' he => ?_, fun t x hx => ?_⟩
    · have h1 := hf t
      have h2 := hf t'
      rw [he] at h1
      exact Fin.ext (by omega)
    · simp only [g]
      rw [hconst _ x hx, hf t, Nat.mul_add_div hv, Nat.div_eq_of_lt t.2]
      omega

section Walks

variable {α : Type*} {β : Type*} {K : Graph α β}

/-- An edge of a closed walk splits the walk. -/
theorem exists_split_at_edge {u v : α} (W : GraphWalk K u v) {e : β} (he : e ∈ W.edges) : ∃
  (a b : α) (A : GraphWalk K u a) (h : K.IsLink e a b) (B : GraphWalk K b v), W = A.append
    (.cons h B) := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u' v' w e' hl r ih =>
    by_cases h1 : e = e'
    · subst h1
      exact ⟨u', v', .nil hl.left_mem, hl, r, rfl⟩
    · have h2 : e ∈ r.edges := by
        simpa [GraphWalk.edges, h1] using he
      obtain ⟨a, b, A, h, B, rfl⟩ := ih h2
      exact ⟨a, b, .cons hl A, h, B, rfl⟩

/-- **Opening a circuit at an edge.** Removing an edge from a simple closed walk leaves a simple
walk through all vertices and the other edges. -/
theorem exists_open_walk {u : α} (W : GraphWalk K u u)
  (hs : W.IsSimpleClosed) {e : β} (he : e ∈ W.edges) : ∃ (a b : α) (L : GraphWalk K b a),
    L.IsSimple ∧ (∀ x, x ∈ L.support ↔ x ∈ W.support) ∧ ∀ f, f ∈ W.edges → f ≠ e → f ∈ L.edges := by
  classical
  obtain ⟨a, b, A, h, B, rfl⟩ := exists_split_at_edge W he
  refine ⟨a, b, B.append A, ?_, fun x => ?_, fun f hf hne => ?_⟩
  · have h1 := hs.1
    change (B.append A).support.Nodup
    rw [GraphWalk.support_append] at h1 ⊢
    have h2 : A.support.tail ++ (GraphWalk.cons h B).support.tail = (A.support ++
      (GraphWalk.cons h B).support.tail).tail := by
      cases A <;> simp [GraphWalk.support]
    rw [← h2] at h1
    have h3 : (GraphWalk.cons h B).support.tail = B.support := rfl
    rw [h3] at h1
    exact List.Perm.nodup_iff List.perm_append_comm |>.mp h1
  · simp only [GraphWalk.mem_support_append, GraphWalk.support, List.mem_cons]
    constructor
    · rintro (h1 | h1)
      · exact .inr (.inr h1)
      · exact .inl h1
    · rintro (h1 | rfl | h1)
      · exact .inr h1
      · exact .inr A.end_mem_support
      · exact .inl h1
  · rw [GraphWalk.edges_append, List.mem_append] at hf ⊢
    rcases hf with h1 | h1
    · exact .inr h1
    · simp only [GraphWalk.edges, List.mem_cons] at h1
      exact .inl (h1.resolve_left hne)

theorem mem_support_of_mem_edges {u v : α} (W : GraphWalk K u v) {e : β}
  (he : e ∈ W.edges) {c d : α} (hl : K.IsLink e c d) : c ∈ W.support ∧ d ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u' v' w e' h r ih =>
    by_cases h1 : e = e'
    · subst h1
      rcases hl.eq_and_eq_or_eq_and_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ r.start_mem_support⟩
      · exact ⟨List.mem_cons_of_mem _ r.start_mem_support, List.mem_cons_self⟩
    · have h2 : e ∈ r.edges := by
        simpa [GraphWalk.edges, h1] using he
      have h3 := ih h2
      exact ⟨List.mem_cons_of_mem _ h3.1, List.mem_cons_of_mem _ h3.2⟩

/-- Two vertices joined by an edge of a simple walk are next to each other on it. -/
theorem idxOf_adjacent [DecidableEq α] {u v : α} (W : GraphWalk K u v) (hs : W.IsSimple) {e : β}
  (he : e ∈ W.edges) {c d : α} (hl : K.IsLink e c d) :
    W.support.idxOf d = W.support.idxOf c + 1 ∨ W.support.idxOf c = W.support.idxOf d + 1 := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u' v' w e' h r ih =>
    have hnd : u' ∉ r.support ∧ r.support.Nodup := by
      have := hs
      simpa [GraphWalk.IsSimple, GraphWalk.support] using this
    have hsup : (GraphWalk.cons h r).support = u' :: r.support := rfl
    rw [hsup]
    have hv0 : r.support.idxOf v' = 0 := by
      cases r <;> simp [GraphWalk.support]
    have hvne : v' ≠ u' := fun h1 => hnd.1 (h1 ▸ r.start_mem_support)
    by_cases h1 : e = e'
    · subst h1
      rcases hl.eq_and_eq_or_eq_and_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ hvne.symm, hv0]
      · right
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ hvne.symm, hv0]
    · have h2 : e ∈ r.edges := by
        simpa [GraphWalk.edges, h1] using he
      obtain ⟨h3, h4⟩ := mem_support_of_mem_edges r h2 hl
      have hc : c ≠ u' := fun h5 => hnd.1 (h5 ▸ h3)
      have hd : d ≠ u' := fun h5 => hnd.1 (h5 ▸ h4)
      rw [List.idxOf_cons_ne _ hc.symm, List.idxOf_cons_ne _ hd.symm]
      have := ih hnd.2 h2
      omega

/-- The positions on a simple walk of the vertices of a walk along its edges form an interval. -/
theorem ordConnected_idxOf [DecidableEq α] {a b : α} (L : GraphWalk K a b)
  (hs : L.IsSimple) {u v : α} (R : GraphWalk K u v) (hR : ∀ e ∈ R.edges, e ∈ L.edges) :
    (((L.support.idxOf) '' {x | x ∈ R.support}) : Set ℕ).OrdConnected := by
  induction R with
  | @nil v₀ h =>
    have hset : {x | x ∈ (GraphWalk.nil h).support} = ({v₀} : Set α) := by
      ext x
      simp [GraphWalk.support]
    rw [hset, image_singleton]
    exact ordConnected_singleton
  | @cons u' v' w e' h r ih =>
    have h1 := ih fun e he => hR e (List.mem_cons_of_mem _ he)
    have h2 := idxOf_adjacent L hs (hR e' List.mem_cons_self) h
    have hset : {x | x ∈ (GraphWalk.cons h r).support} = insert u' {x | x ∈ r.support} := by
      ext x
      simp [GraphWalk.support]
    rw [hset, image_insert_eq]
    have hv : L.support.idxOf v' ∈ (L.support.idxOf) '' {x | x ∈ r.support}
      := mem_image_of_mem _ r.start_mem_support
    refine ⟨fun x hx y hy z hz => ?_⟩
    set p := L.support.idxOf u' with hp
    have hins : ∀ w, w ∈ insert p (L.support.idxOf '' {x | x ∈ r.support}) → w = p
      ∨ w ∈ L.support.idxOf '' {x | x ∈ r.support} := fun w hw => hw
    by_cases hzp : z = p
    · exact hzp ▸ mem_insert _ _
    · refine mem_insert_of_mem _ ?_
      have hbet : ∀ {x' y'}, x' ∈ (L.support.idxOf '' {x | x ∈ r.support}) → y' ∈
        (L.support.idxOf '' {x | x ∈ r.support}) → x' ≤ z → z ≤ y' → z ∈
          (L.support.idxOf '' {x | x ∈ r.support}) := fun h3 h4 h5 h6 => h1.out h3 h4 ⟨h5, h6⟩
      rcases hins x hx with rfl | h3 <;> rcases hins y hy with rfl | h4
      · exact (hzp (le_antisymm hz.2 hz.1)).elim
      · have h5 : L.support.idxOf v' ≤ z := by
          have := hz.1
          omega
        exact hbet hv h4 h5 hz.2
      · have h5 : z ≤ L.support.idxOf v' := by
          have := hz.2
          omega
        exact hbet h3 hv hz.1 h5
      · exact hbet h3 h4 hz.1 hz.2

/-- **A piece of a simple walk**, between two positions. -/
theorem exists_walk_piece [DecidableEq α] {u v : α} (L : GraphWalk K u v)
  (hs : L.IsSimple) {i j : ℕ} (hij : i ≤ j) (hj : j < L.support.length) :
    ∃ (x y : α) (M : GraphWalk K x y), M.IsSimple ∧ L.support.idxOf x = i
      ∧ ∀ z, z ∈ M.support ↔ z ∈ L.support ∧ i ≤ L.support.idxOf z ∧ L.support.idxOf z ≤ j := by
  induction L generalizing i j with
  | @nil u' h =>
    simp only [GraphWalk.support, List.length_singleton, Nat.lt_one_iff] at hj
    have hi : i = 0 := by omega
    subst hi hj
    refine ⟨u', u', .nil h, hs, by simp [GraphWalk.support], fun z => ?_⟩
    simp only [GraphWalk.support, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · exact fun h1 => h1.1
  | @cons u' v' w e' h r ih =>
    have hnd : u' ∉ r.support ∧ r.support.Nodup := by
      have := hs
      simpa [GraphWalk.IsSimple, GraphWalk.support] using this
    have hsup : (GraphWalk.cons h r).support = u' :: r.support := rfl
    have hidx : ∀ z ∈ r.support, (u' :: r.support).idxOf z = r.support.idxOf z + 1 := fun z hz
      => List.idxOf_cons_ne _ fun h1 => hnd.1 (h1 ▸ hz)
    rw [hsup] at hj ⊢
    simp only [List.length_cons] at hj
    rcases i with _ | i
    · rcases j with _ | j
      · refine ⟨u', u', .nil h.left_mem, by simp [GraphWalk.IsSimple, GraphWalk.support],
          by simp, fun z => ?_⟩
        simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro rfl
          simp
        · rintro ⟨rfl | h1, -, h3⟩
          · rfl
          · rw [hidx z h1] at h3
            omega
      · obtain ⟨x, y, M, h1, h2, h3⟩ := ih hnd.2 (Nat.zero_le j) (by omega)
        have hxv : x = v' := by
          have hxm : x ∈ M.support := M.start_mem_support
          have hxr := ((h3 x).mp hxm).1
          cases r with
          | nil _ => simpa [GraphWalk.support] using hxr
          | cons _ _ =>
            simp only [GraphWalk.support, List.mem_cons] at hxr h2 ⊢
            rcases hxr with h4 | h4
            · exact h4
            · by_contra h5
              rw [List.idxOf_cons_ne _ (Ne.symm h5)] at h2
              omega
        subst hxv
        refine ⟨u', y, .cons h M, ?_, by simp, fun z => ?_⟩
        · change (u' :: M.support).Nodup
          refine List.nodup_cons.mpr ⟨fun h4 => hnd.1 ((h3 _).mp h4).1, h1⟩
        · simp only [GraphWalk.support, List.mem_cons]
          constructor
          · rintro (rfl | h4)
            · simp
            · obtain ⟨h5, -, h6⟩ := (h3 z).mp h4
              refine ⟨.inr h5, Nat.zero_le _, ?_⟩
              rw [hidx z h5]
              omega
          · rintro ⟨rfl | h4, -, h5⟩
            · exact .inl rfl
            · rw [hidx z h4] at h5
              exact .inr ((h3 z).mpr ⟨h4, Nat.zero_le _, by omega⟩)
    · obtain ⟨x, y, M, h1, h2, h3⟩ := ih hnd.2 (Nat.le_of_succ_le_succ (by omega : i + 1
        ≤ j - 1 + 1)) (by omega)
      have hxm : x ∈ r.support := ((h3 x).mp M.start_mem_support).1
      refine ⟨x, y, M, h1, by rw [hidx x hxm, h2], fun z => ?_⟩
      rw [h3 z]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨h4, h5, h6⟩
        rw [hidx z h4]
        exact ⟨.inr h4, by omega, by omega⟩
      · rintro ⟨rfl | h4, h5, h6⟩
        · simp at h5
        · rw [hidx z h4] at h5 h6
          exact ⟨h4, by omega, by omega⟩

/-- An edge of a walk leaves a set that the walk leaves. -/
theorem exists_leaving_edge {u v : α} (W : GraphWalk K u v) (X : Set α) {x y : α}
  (hx : x ∈ W.support) (hy : y ∈ W.support) (hxX : x ∈ X) (hyX : y ∉ X) : ∃ e ∈ W.edges, ∃ c d,
    K.IsLink e c d ∧ c ∈ X ∧ d ∉ X := by
  induction W generalizing x y with
  | nil _ =>
    simp only [GraphWalk.support, List.mem_singleton] at hx hy
    exact absurd (hy ▸ hx ▸ hxX) hyX
  | @cons u' v' w e' h r ih =>
    simp only [GraphWalk.support, List.mem_cons] at hx hy
    have hup : ∀ {e}, e ∈ r.edges → e ∈ (GraphWalk.cons h r).edges := fun he
      => List.mem_cons_of_mem _ he
    have hhd : e' ∈ (GraphWalk.cons h r).edges := List.mem_cons_self
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd hxX hyX
      · by_cases hv : v' ∈ X
        · obtain ⟨e, he, r'⟩ := ih r.start_mem_support hy hv hyX
          exact ⟨e, hup he, r'⟩
        · exact ⟨e', hhd, x, v', h, hxX, hv⟩
    · rcases hy with rfl | hy
      · by_cases hv : v' ∈ X
        · exact ⟨e', hhd, v', y, h.symm, hv, hyX⟩
        · obtain ⟨e, he, r'⟩ := ih hx r.start_mem_support hxX hv
          exact ⟨e, hup he, r'⟩
      · obtain ⟨e, he, r'⟩ := ih hx hy hxX hyX
        exact ⟨e, hup he, r'⟩

end Walks

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- **The subpaths `N_i(C)`.** Let `v * k` vertex-disjoint paths lie in a circuit `N`, with at least
two of them. Then `N` has `k` vertex-disjoint subpaths that cover its vertices, and each subpath
holds `v` of the paths. This is page 235, (i) and (ii). -/
theorem exists_circuit_groups {N : Drawing S} (hN : N.IsCircuit) {k v : ℕ} (hk : 0 < k)
  (hv : 0 < v) (hvk : 2 ≤ v * k) (Q : Fin (v * k) → Drawing S) (hQ : ∀ ι, (Q ι).IsSubdrawing N)
    (hQp : ∀ ι, ∃ x y, (Q ι).IsPathBetween x y) (hdis : ∀ ι ι', ι ≠ ι' → Disjoint (Q ι).V
      (Q ι').V) :
    ∃ R : Fin k → Drawing S, (∀ i, (R i).IsSubdrawing N ∧ ∃ a b, (R i).IsPathBetween a b) ∧
      (∀ i i', i ≠ i' → Disjoint (R i).V (R i').V) ∧ (∀ x ∈ N.V, ∃ i, x ∈ (R i).V)
        ∧ ∀ i, ∃ f : Fin v → Fin (v * k), Injective f ∧ ∀ t, (Q (f t)).V ⊆ (R i).V := by
  classical
  obtain ⟨u, W, hW, hlen, hV, hE⟩ := id hN
  have hmem : ∀ ι, ∃ w, w ∈ (Q ι).V := fun ι => by
    obtain ⟨x, y, W', -, h1, -⟩ := hQp ι
    exact ⟨x, by rw [h1]; exact W'.start_mem_support⟩
  let ι₀ : Fin (v * k) := ⟨0, by omega⟩
  let ι₁ : Fin (v * k) := ⟨1, by omega⟩
  have h01 : ι₀ ≠ ι₁ := fun h => by simp [ι₀, ι₁, Fin.ext_iff] at h
  obtain ⟨a₀, ha₀⟩ := hmem ι₀
  obtain ⟨a₁, ha₁⟩ := hmem ι₁
  have hsupp : ∀ {x ι}, x ∈ (Q ι).V → x ∈ W.support := fun {x ι} hx => by
    have := (hQ ι).1 hx
    rwa [hV] at this
  obtain ⟨e, heW, c, d, hl, hc, hd⟩ := exists_leaving_edge W (Q ι₀).V (hsupp ha₀) (hsupp ha₁) ha₀
    (fun h => disjoint_left.mp (hdis ι₀ ι₁ h01) h ha₁)
  -- `e` is in no path
  have hoffe : ∀ ι, e ∉ (Q ι).E := fun ι he => by
    have hcl : closure e ⊆ (Q ι).U := (Q ι).closure_subset_U he
    have hmemc : c ∈ closure e ∧ d ∈ closure e := by
      have h2 := hl.2.2.2
      exact ⟨(h2 ▸ mem_insert _ _ : c ∈ closure e ∩ N.V).1, (h2 ▸ mem_insert_of_mem _ rfl : d ∈
        closure e ∩ N.V).1⟩
    have hcV : c ∈ (Q ι).V := mem_V_of_subdrawing (hQ ι) (hcl hmemc.1) hl.2.1
    have hdV : d ∈ (Q ι).V := mem_V_of_subdrawing (hQ ι) (hcl hmemc.2) hl.2.2.1
    by_cases he' : ι = ι₀
    · exact hd (he' ▸ hdV)
    · exact disjoint_left.mp (hdis ι ι₀ he') hcV hc
  obtain ⟨a', b', L, hLs, hLsup, hLe⟩ := exists_open_walk W hW heW
  let m := L.support.length
  let A : Fin (v * k) → Set ℕ := fun ι => L.support.idxOf '' (Q ι).V
  have hA : ∀ ι, ∀ x ∈ (Q ι).V, x ∈ L.support := fun ι x hx => (hLsup x).mpr (hsupp hx)
  have hint : ∀ ι, (A ι).OrdConnected := fun ι => by
    obtain ⟨x, y, W', -, h1, h1'⟩ := hQp ι
    obtain ⟨X, hX₁, hX₂⟩ := (hQ ι).exists_walk_up W'
    have h2 : A ι = L.support.idxOf '' {z | z ∈ X.support} := by
      simp only [A]
      rw [h1, hX₁]
    rw [h2]
    refine ordConnected_idxOf L hLs X fun f hf => ?_
    rw [hX₂] at hf
    have hfQ : f ∈ (Q ι).E := h1' ▸ hf
    have hfN : f ∈ N.E := (hQ ι).2 hfQ
    rw [hE] at hfN
    exact hLe f hfN fun h3 => hoffe ι (h3 ▸ hfQ)
  have hAdis : ∀ ι ι', ι ≠ ι' → Disjoint (A ι) (A ι') := fun ι ι' hne => by
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', he⟩
    have : x' = x := (List.idxOf_inj (hA ι' x' hx')).mp he
    exact disjoint_left.mp (hdis ι ι' hne) hx (this ▸ hx')
  obtain ⟨g, hgm, hgk, hgs, hgf⟩ := exists_interval_groups (m := m) hk hv A (fun ι => by
    obtain ⟨w, hw⟩ := hmem ι
    exact ⟨_, mem_image_of_mem _ hw⟩) (by
    rintro ι _ ⟨x, hx, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hA ι x hx)) hint hAdis
  have hex : ∀ i : Fin k, ∃ (x y : S) (M : GraphWalk N.toGraph x y), M.IsSimple
    ∧ ∀ z, z ∈ M.support ↔ z ∈ L.support ∧ g (L.support.idxOf z) = i.1 := fun i => by
    obtain ⟨x₀, hx₀, hx₀g⟩ := hgs i.1 i.2
    let F := (Finset.range m).filter fun p => g p = i.1
    have hF : F.Nonempty := ⟨x₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx₀, hx₀g⟩⟩
    have h1 := Finset.mem_filter.mp (F.min'_mem hF)
    have h2 := Finset.mem_filter.mp (F.max'_mem hF)
    obtain ⟨x, y, M, h3, -, h4⟩ := exists_walk_piece L hLs (F.min'_le _ (F.max'_mem hF))
      (Finset.mem_range.mp h2.1)
    refine ⟨x, y, M, h3, fun z => ?_⟩
    rw [h4]
    constructor
    · rintro ⟨h5, h6, h7⟩
      refine ⟨h5, le_antisymm ?_ ?_⟩
      · exact (hgm h7).trans_eq h2.2
      · exact h1.2.symm.le.trans (hgm h6)
    · rintro ⟨h5, h6⟩
      have h7 : L.support.idxOf z ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (List.idxOf_lt_length_iff.mpr h5), h6⟩
      exact ⟨h5, F.min'_le _ h7, F.le_max' _ h7⟩
  choose x y M hMs hM using hex
  have hRV : ∀ i, (walkDrawing N (M i)).V = {z | z ∈ (M i).support} := fun i => walkDrawing_V N
    (M i)
  refine ⟨fun i => walkDrawing N (M i), fun i => ⟨walkDrawing_isSubdrawing N (M i), x i, y i,
    walkDrawing_isPathBetween N (hMs i)⟩, fun i i' hne => ?_, fun z hz => ?_, fun i => ?_⟩
  · rw [disjoint_left, hRV, hRV]
    intro z h1 h2
    have h3 := ((hM i z).mp h1).2
    have h4 := ((hM i' z).mp h2).2
    exact hne (Fin.ext (h3.symm.trans h4))
  · have hz' : z ∈ L.support := (hLsup z).mpr (by rw [hV] at hz; exact hz)
    refine ⟨⟨g (L.support.idxOf z), hgk _⟩, ?_⟩
    rw [hRV]
    exact (hM _ z).mpr ⟨hz', rfl⟩
  · obtain ⟨f, hf, hfg⟩ := hgf i.1 i.2
    refine ⟨f, hf, fun t z hz => ?_⟩
    rw [hRV]
    exact (hM i z).mpr ⟨hA _ z hz, hfg t _ (mem_image_of_mem _ hz)⟩

end GraphMinor.GM07

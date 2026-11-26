/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section4e

/-!
# Section 5 of "Quickly excluding a planar graph": walking along the path `Q`

The step of the proof of (5.3) (pages 340–341). The paper's Case 3 says: if `Q` does not meet `P_g,
P_{g-1}, …, P_1` in order, and does not meet `P_g, …, P_{2g-1}` in order, then it jumps.
The sets `T i` are the paper's "all vertices of $Q_{r_j}$ which lie in $Q_{r_j}$ strictly between
the intersections with $P_{i-1}$ and $P_i$" (shifted to `P_i` and `P_{i+1}`), together with one
vertex of `P_i`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι : Type*} {G : Hypergraph α β}

/-- Starting at `s`, a walk reaches a vertex with a label after a part `q` with no label. -/
theorem exists_run {K : SimpleGraph α} {L : Set α} {s e : α} (w : K.Walk s e) (he : e ∈ L)
  (hne : s ≠ e) :
    ∃ (t y : α) (q : K.Walk s t) (h : K.Adj t y) (w' : K.Walk y e), y ∈ L ∧ (∀ v ∈ q.support, v ≠ s
      → v ∉ L) ∧
      w = q.append (SimpleGraph.Walk.cons h w') := by
  induction w with
  | nil => exact absurd rfl hne
  | @cons u v f h₁ p ih =>
    by_cases hv : v ∈ L
    · exact ⟨u, v, SimpleGraph.Walk.nil, h₁, p, hv, fun x hx hx' => absurd
      (by simpa using hx) hx', rfl⟩
    · have hvf : v ≠ f := fun e' => hv (e' ▸ he)
      obtain ⟨t, y, q, h, w', hy, hq, hw⟩ := ih he hvf
      refine ⟨t, y, SimpleGraph.Walk.cons h₁ q, h, w', hy, fun x hx hx' => ?_, ?_⟩
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd rfl hx'
        · by_cases hxv : x = v
          · exact hxv ▸ hv
          · exact hq x hx hxv
      · rw [hw, SimpleGraph.Walk.cons_append]

theorem NoReturn.of_append {K : SimpleGraph α} {X : Set α} {r s t : α} {w₀ : K.Walk r s} {w :
  K.Walk s t} (hw : NoReturn X (w₀.append w)) :
    NoReturn X w := fun a b w₁ w₂ w₃ he ha hb c hc =>
  hw a b (w₀.append w₁) w₂ w₃ (by rw [he, SimpleGraph.Walk.append_assoc]) ha hb c hc

/-- One hop along `Q`: from the path with label `a` to the next path it meets. -/
theorem exists_hop {K : SimpleGraph α} {V : ι → Set α} (_hV : Pairwise fun i j => Disjoint (V i)
  (V j)) {a : ι} {x e : α} (w : K.Walk x e) (hx : x ∈ V a) (he : e ∉ V a)
    (hl : ∃ l, e ∈ V l) (hn : ∀ l, NoReturn (V l) w) :
    ∃ (x' t y : α) (b : ι) (q : K.Walk x' t) (h : K.Adj t y) (w' : K.Walk y e)
      (w₀ : K.Walk x x'), x' ∈ V a ∧ y ∈ V b ∧ b ≠ a ∧
      (∀ v ∈ q.support, v ≠ x' → ∀ l, v ∉ V l) ∧ w = w₀.append (q.append
        (SimpleGraph.Walk.cons h w')) ∧ (∀ v ∈ w'.support, v ∉ V a) := by
  classical
  induction w with
  | nil => exact absurd hx he
  | @cons u v f h₁ p ih =>
    by_cases hv : v ∈ V a
    · obtain ⟨x', t, y, b, q, h, w', w₀, h₁', h₂, h₃, h₄, h₅, h₆⟩ := ih hv he hl (fun l =>
      (hn l).of_cons)
      exact ⟨x', t, y, b, q, h, w', SimpleGraph.Walk.cons h₁ w₀, h₁', h₂, h₃, h₄, by rw [h₅,
        SimpleGraph.Walk.cons_append], h₆⟩
    · obtain ⟨l₀, hl₀⟩ := hl
      have hne : u ≠ f := fun e' => he (e' ▸ hx)
      obtain ⟨t, y, q, h, w', hy, hq, hw⟩ := exists_run (L := ⋃ l, V l)
        (SimpleGraph.Walk.cons h₁ p) (mem_iUnion.2 ⟨l₀, hl₀⟩) hne
      obtain ⟨b, hb⟩ := mem_iUnion.1 hy
      have hsplit : ∀ {z : α} (r : K.Walk y z) (r' : K.Walk z f), w' = r.append r' → z ∈ V a
        → False := by
        intro z r r' hr hz
        have hmem := hn a u z SimpleGraph.Walk.nil (q.append (SimpleGraph.Walk.cons h r)) r' (by
          rw [SimpleGraph.Walk.nil_append, hw, hr, ← SimpleGraph.Walk.append_assoc,
            SimpleGraph.Walk.cons_append]) hx hz
        -- The next vertex after `u` is on the segment, and it is not in `V a`.
        have hvmem : v ∈ (q.append (SimpleGraph.Walk.cons h r)).support := by
          have hs : u ≠ v := h₁.ne
          cases q with
          | nil =>
            obtain ⟨rfl, -⟩ : y = v ∧ True := by
              simp only [SimpleGraph.Walk.nil_append, SimpleGraph.Walk.cons.injEq] at hw
              exact ⟨hw.1.symm, trivial⟩
            simp
          | cons h' q' =>
            simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.cons.injEq] at hw
            obtain ⟨rfl, -⟩ := hw
            simp
        exact hv (hmem v hvmem)
      have hba : b ≠ a := by
        rintro rfl
        exact hsplit SimpleGraph.Walk.nil w' (by simp) hb
      refine ⟨u, t, y, b, q, h, w', SimpleGraph.Walk.nil, hx, hb, hba, fun x hx₁ hx₂ l hl'
        => hq x hx₁ hx₂ (mem_iUnion.2 ⟨l, hl'⟩), by simpa using hw, fun z hz hza => ?_⟩
      exact hsplit (w'.takeUntil z hz) (w'.dropUntil z hz) (by rw [w'.take_spec hz]) hza

/-- The sets `T i` for `m ≤ i` and `i + 1 < g`. Each joins the path with label `f i` to the path
with label `f (i + 1)` along `Y`, and has no other vertex on the paths. -/
structure Segs (Gr : Hypergraph α β) (V : ι → Set α) (f : ℕ → ι) (g m : ℕ) (Y : Set α) (T : ℕ
  → Set α) (x y : ℕ → α) : Prop where
  conn : ∀ i, m ≤ i → i + 1 < g → Conn Gr (T i)
  x_T : ∀ i, m ≤ i → i + 1 < g → x i ∈ T i
  x_V : ∀ i, m ≤ i → i + 1 < g → x i ∈ V (f i)
  sub : ∀ i, m ≤ i → i + 1 < g → T i ⊆ Y
  label : ∀ i, m ≤ i → i + 1 < g → ∀ t ∈ T i, t ≠ x i → ∀ l, t ∉ V l
  disj : ∀ i j, m ≤ i → i + 1 < g → m ≤ j → j + 1 < g → i ≠ j → Disjoint (T i) (T j)
  y_V : ∀ i, m ≤ i → i + 1 < g → y i ∈ V (f (i + 1))
  y_Y : ∀ i, m ≤ i → i + 1 < g → y i ∈ Y
  touch : ∀ i, m ≤ i → i + 1 < g → ∃ t ∈ T i, Gr.skeleton.Adj t (y i)

/-- There is a piece of `Y` from the path with label `a` to the path with label `b`, with no other
vertex on the paths. This is the paper's minimal subpath in Case 3 of (5.3). -/
def JumpData (Gr : Hypergraph α β) (V : ι → Set α) (Y : Set α) (a b : ι) : Prop :=
  ∃ (x t y : α) (q : Gr.skeleton.Walk x t), Gr.skeleton.Adj t y ∧ x ∈ V a ∧ y ∈ V b ∧
    (∀ v ∈ q.support, v ≠ x → ∀ l, v ∉ V l) ∧ (∀ v ∈ q.support, v ∈ Y) ∧ y ∈ Y

theorem JumpData.mono {Gr : Hypergraph α β} {V : ι → Set α} {Y Y' : Set α} {a b : ι}
  (h : JumpData Gr V Y a b) (hY : Y ⊆ Y') : JumpData Gr V Y' a b := by
  obtain ⟨x, t, y, q, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨x, t, y, q, h₁, h₂, h₃, h₄, fun v hv => hY (h₅ v hv), hY h₆⟩

/-- Adding one more set `T m` in front. -/
theorem Segs.cons {Gr : Hypergraph α β} {V : ι → Set α} {f : ℕ → ι} {g m : ℕ} {Y Y' : Set α} {T : ℕ
  → Set α} {x y : ℕ → α} (hS : Segs Gr V f g (m + 1) Y' T x y)
    {x₀ t y₀ : α} (q : Gr.skeleton.Walk x₀ t) (h : Gr.skeleton.Adj t y₀) (hx : x₀ ∈ V (f m))
      (hy : y₀ ∈ V (f (m + 1))) (hl : ∀ v ∈ q.support, v ≠ x₀ → ∀ l, v ∉ V l)
    (hq : ∀ v ∈ q.support, v ∈ Y) (hyY : y₀ ∈ Y) (hY : Y' ⊆ Y) (hd : ∀ v ∈ q.support, v ∉ Y') :
    Segs Gr V f g m Y (Function.update T m {v | v ∈ q.support}) (Function.update x m x₀)
      (Function.update y m y₀) := by
  have hne : ∀ {i}, m ≤ i → i ≠ m → m + 1 ≤ i := fun h₁ h₂ => by omega
  refine ⟨fun i h₁ h₂ => ?_, fun i h₁ h₂ => ?_, fun i h₁ h₂ => ?_, fun i h₁ h₂ => ?_, fun i h₁ h₂
    => ?_, fun i j h₁ h₂ h₃ h₄ h₅ => ?_, fun i h₁ h₂ => ?_, fun i h₁ h₂ => ?_, fun i h₁ h₂ => ?_⟩
  all_goals by_cases him : i = m
  · subst him
    rw [Function.update_self]
    exact conn_support q
  · rw [Function.update_of_ne him]
    exact hS.conn i (hne h₁ him) h₂
  · subst him
    rw [Function.update_self, Function.update_self]
    exact q.start_mem_support
  · rw [Function.update_of_ne him, Function.update_of_ne him]
    exact hS.x_T i (hne h₁ him) h₂
  · subst him
    rw [Function.update_self]
    exact hx
  · rw [Function.update_of_ne him]
    exact hS.x_V i (hne h₁ him) h₂
  · subst him
    rw [Function.update_self]
    exact hq
  · rw [Function.update_of_ne him]
    exact (hS.sub i (hne h₁ him) h₂).trans hY
  · subst him
    rw [Function.update_self, Function.update_self]
    exact hl
  · rw [Function.update_of_ne him, Function.update_of_ne him]
    exact hS.label i (hne h₁ him) h₂
  · subst him
    rw [Function.update_self, Function.update_of_ne h₅.symm]
    exact disjoint_left.2 fun v hv hv' => hd v hv (hS.sub j (hne h₃ h₅.symm) h₄ hv')
  · rw [Function.update_of_ne him]
    by_cases hjm : j = m
    · subst hjm
      rw [Function.update_self]
      exact disjoint_right.2 fun v hv hv' => hd v hv (hS.sub i (hne h₁ him) h₂ hv')
    · rw [Function.update_of_ne hjm]
      exact hS.disj i j (hne h₁ him) h₂ (hne h₃ hjm) h₄ h₅
  · subst him
    rw [Function.update_self]
    exact hy
  · rw [Function.update_of_ne him]
    exact hS.y_V i (hne h₁ him) h₂
  · subst him
    rw [Function.update_self]
    exact hyY
  · rw [Function.update_of_ne him]
    exact hY (hS.y_Y i (hne h₁ him) h₂)
  · subst him
    rw [Function.update_self, Function.update_self]
    exact ⟨t, q.end_mem_support, h⟩
  · rw [Function.update_of_ne him, Function.update_of_ne him]
    exact hS.touch i (hne h₁ him) h₂

/-- Facts about the pieces of a hop. -/
theorem hop_facts {K : SimpleGraph α} {x x' t y e : α} {w : K.Walk x e} {w₀ : K.Walk x
  x'} {q : K.Walk x' t} {h : K.Adj t y} {w' : K.Walk y e}
    (hw : w = w₀.append (q.append (SimpleGraph.Walk.cons h w'))) (hp : w.IsPath) :
    w'.IsPath ∧ (∀ v ∈ q.support, v ∈ w.support) ∧ (∀ v ∈ w'.support, v ∈ w.support) ∧
      (∀ v ∈ q.support, v ∉ w'.support) := by
  have h₁ : (q.append (SimpleGraph.Walk.cons h w')).IsPath := by
    rw [hw] at hp
    exact hp.of_append_right
  have h₂ := h₁.support_nodup
  rw [SimpleGraph.Walk.support_append, List.nodup_append] at h₂
  have htail : (SimpleGraph.Walk.cons h w').support.tail = w'.support := by simp
  rw [htail] at h₂
  refine ⟨?_, fun v hv => ?_, fun v hv => ?_, fun v hv hv' => h₂.2.2 v hv v hv' rfl⟩
  · exact (h₁.of_append_right).of_cons
  · rw [hw]
    simp [SimpleGraph.Walk.mem_support_append_iff, hv]
  · rw [hw]
    simp [SimpleGraph.Walk.mem_support_append_iff, hv]

/-- Walking along the labels `f m, f (m + 1), …`: either `w` meets them in order, or it jumps. -/
theorem chain_or_jump {Gr : Hypergraph α β} {V : ι → Set α} (hV : Pairwise fun i j => Disjoint
  (V i) (V j)) {f : ℕ → ι} {g : ℕ} {e : α}
    (he : ∀ n, n + 1 < g → e ∉ V (f n)) (hl : ∃ l, e ∈ V l) (d : ℕ) : ∀ (m : ℕ), m + 1 + d = g → ∀
      (x : α) (w : Gr.skeleton.Walk x e), w.IsPath → (∀ l, NoReturn (V l) w) →
      x ∈ V (f m) → (∀ n < m, ∀ t ∈ w.support, t ∉ V (f n)) →
      (∃ T x' y', Segs Gr V f g m {t | t ∈ w.support} T x' y') ∨
      ∃ n b, m ≤ n ∧ n + 1 < g ∧ b ≠ f (n + 1) ∧ (∀ n' ≤ n, b ≠ f n')
        ∧ JumpData Gr V {t | t ∈ w.support} (f n) b := by
  induction d with
  | zero =>
    intro m hm x w _ _ _ _
    refine Or.inl ⟨fun _ => ∅, fun _ => x, fun _ => x, ?_⟩
    constructor <;> intros <;> omega
  | succ d ih =>
    intro m hm x w hp hn hx hprev
    have he₁ := he m (by omega)
    obtain ⟨x', t, y, b, q, h, w', w₀, hx', hy, hba, hq, hw, hw'⟩ := exists_hop hV w hx he₁ hl hn
    obtain ⟨hp', hsq, hsw, hdis⟩ := hop_facts hw hp
    have hyw : y ∈ w'.support := w'.start_mem_support
    have hn' : ∀ l, NoReturn (V l) w' := fun l => by
      have := hn l
      rw [hw] at this
      exact (NoReturn.of_cons (this.of_append.of_append))
    by_cases hb : b = f (m + 1)
    · have hprev' : ∀ n < m + 1, ∀ t ∈ w'.support, t ∉ V (f n) := fun n hlt t ht => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h₁ | rfl
        · exact hprev n h₁ t (hsw t ht)
        · exact hw' t ht
      rcases ih (m + 1) (by omega) y w' hp' hn' (hb ▸ hy) hprev' with ⟨T, x₁, y₁, hS⟩ | ⟨n, b', h₁,
        h₂, h₃, h₄, h₅⟩
      · exact Or.inl ⟨_, _, _, hS.cons q h hx' (hb ▸ hy) hq hsq (hsw y hyw) (fun v hv
        => hsw v hv) hdis⟩
      · exact Or.inr ⟨n, b', by omega, h₂, h₃, h₄, h₅.mono fun v hv => hsw v hv⟩
    · refine Or.inr ⟨m, b, le_rfl, by omega, hb, fun n' hn' e' => ?_, x', t, y, q, h, hx', hy, hq,
      hsq, hsw y hyw⟩
      rcases Nat.lt_or_ge n' m with h₁ | h₁
      · exact hprev n' h₁ y (hsw y hyw) (e' ▸ hy)
      · obtain rfl : n' = m := by omega
        exact hba e'

/-- The three cases of the proof of (5.3) (pages 340–341). -/
theorem walk_trichotomy {Gr : Hypergraph α β} {V : ι → Set α} (hV : Pairwise fun i j => Disjoint
  (V i) (V j)) {g : ℕ} (hg : 2 ≤ g) {c : ℕ → ι}
    (hc : ∀ a b, a < 2 * g - 1 → b < 2 * g - 1 → c a = c b → a = b) {x e : α}
      (Q : Gr.skeleton.Walk x e) (hQ : Q.IsPath) (hn : ∀ l, NoReturn (V l) Q)
    (hx : x ∈ V (c (g - 1))) (he : e ∈ V (c 0)) :
    (∃ T x' y', Segs Gr V (fun i => c (g - 1 - i)) g 0 {t | t ∈ Q.support} T x' y') ∨
    (∃ T x' y', Segs Gr V (fun i => c (g - 1 + i)) g 0 {t | t ∈ Q.support} T x' y') ∨
    ∃ p b, 1 ≤ p ∧ p + 2 ≤ 2 * g - 1 ∧ b ≠ c (p - 1) ∧ b ≠ c p ∧ b ≠ c (p + 1)
      ∧ JumpData Gr V {t | t ∈ Q.support} (c p) b := by
  have hdis : ∀ {a b : ℕ}, a < 2 * g - 1 → b < 2 * g - 1 → a ≠ b → ∀ t, t ∈ V (c a) → t ∉ V (c b)
    := fun ha hb hne t h₁ h₂ =>
    disjoint_left.1 (hV fun e' => hne (hc _ _ ha hb e')) h₁ h₂
  have he₁ : e ∉ V (c (g - 1)) := fun h => hdis (a := 0) (b := g - 1) (by omega) (by omega)
    (by omega) e he h
  obtain ⟨x', t, y, b, q, h, w', w₀, hx', hy, hba, hq, hw, hw'⟩ := exists_hop hV Q hx he₁ ⟨_, he⟩ hn
  obtain ⟨hp', hsq, hsw, hdisj⟩ := hop_facts hw hQ
  have hyw : y ∈ w'.support := w'.start_mem_support
  have hn' : ∀ l, NoReturn (V l) w' := fun l => by
    have := hn l
    rw [hw] at this
    exact (NoReturn.of_cons (this.of_append.of_append))
  by_cases hb₁ : b = c (g - 2)
  · have hch := chain_or_jump (Gr := Gr) hV (f := fun i => c (g - 1 - i)) (g := g) (e := e)
      (fun n hn₁ h' => hdis (a := 0) (b := g - 1 - n) (by omega) (by omega)
        (by omega) e he h') ⟨_, he⟩ (g - 2) 1 (by omega) y w' hp' hn'
      (by
        have : g - 1 - 1 = g - 2 := by omega
        simp only [this]
        exact hb₁ ▸ hy)
      (fun n hlt t ht => by
        obtain rfl : n = 0 := by omega
        exact hw' t ht)
    rcases hch with ⟨T, x₁, y₁, hS⟩ | ⟨n, b', h₁, h₂, h₃, h₄, h₅⟩
    · exact Or.inl ⟨_, _, _, hS.cons q h hx' (by
        have : g - 1 - (0 + 1) = g - 2 := by omega
        simp only [this]
        exact hb₁ ▸ hy) hq hsq (hsw y hyw) (fun v hv => hsw v hv) hdisj⟩
    · refine Or.inr (Or.inr ⟨g - 1 - n, b', by omega, by omega, ?_, h₄ n le_rfl, ?_, h₅.mono fun v
      hv => hsw v hv⟩)
      · have : g - 1 - n - 1 = g - 1 - (n + 1) := by omega
        rw [this]
        exact h₃
      · have : g - 1 - n + 1 = g - 1 - (n - 1) := by omega
        rw [this]
        exact h₄ _ (by omega)
  by_cases hb₂ : b = c g
  · have hch := chain_or_jump (Gr := Gr) hV (f := fun i => c (g - 1 + i)) (g := g) (e := e)
      (fun n hn₁ h' => hdis (a := 0) (b := g - 1 + n) (by omega) (by omega)
        (by omega) e he h') ⟨_, he⟩ (g - 2) 1 (by omega) y w' hp' hn'
      (by
        have : g - 1 + 1 = g := by omega
        simp only [this]
        exact hb₂ ▸ hy)
      (fun n hlt t ht => by
        obtain rfl : n = 0 := by omega
        exact hw' t ht)
    rcases hch with ⟨T, x₁, y₁, hS⟩ | ⟨n, b', h₁, h₂, h₃, h₄, h₅⟩
    · exact Or.inr (Or.inl ⟨_, _, _, hS.cons q h hx' (by
        have : g - 1 + (0 + 1) = g := by omega
        simp only [this]
        exact hb₂ ▸ hy) hq hsq (hsw y hyw) (fun v hv => hsw v hv) hdisj⟩)
    · refine Or.inr (Or.inr ⟨g - 1 + n, b', by omega, by omega, ?_, h₄ n le_rfl, ?_, h₅.mono fun v
      hv => hsw v hv⟩)
      · have : g - 1 + n - 1 = g - 1 + (n - 1) := by omega
        rw [this]
        exact h₄ _ (by omega)
      · exact h₃
  · refine Or.inr (Or.inr ⟨g - 1, b, by omega, by omega, ?_, hba, ?_, x', t, y, q, h, hx', hy, hq,
    hsq, hsw y hyw⟩)
    · have : g - 1 - 1 = g - 2 := by omega
      rw [this]
      exact hb₁
    · have : g - 1 + 1 = g := by omega
      rw [this]
      exact hb₂

end GraphMinor.RST94

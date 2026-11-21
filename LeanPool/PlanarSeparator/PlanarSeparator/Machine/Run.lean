/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Back
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.BFS
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.LevelStat
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.FaceRep
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.StArr

/-!
# The separator program

The whole program (`sepProg`): the constants (`setup`), and for `m ≥ 1` darts the front half
(`front`: breadth-first search, level statistics, median, `⌊√n⌋`, thin levels, face
representatives, the stellar subdivision in memory) followed by the back half
(`PlanarSeparator/Machine/Back.lean`); for `m = 0` it prints a single `0`.

* `setup_exec`: the constants from the initial configuration;
* `front_exec`: the state after the front half, with all the facts the back half and the bridge
  to plane maps use (`FrontOut`), within `96 m + 101 n + 60` steps;
* `exists_thin_below`, `exists_thin_above`: the pigeonhole step for the thin levels.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset CycleSearch

/-! ### The programs -/

/-- **The constants**: `r100 … r121` (`Lay`) and `r0 … r10` (`CycleSearch.CRegs` for `m`
faces). -/
def setup : Stmt := block [.constN 101 1, .constN 102 2, .constN 103 3, .readIn 104 100,
  .readIn 105 101, .addN 106 104 103, .addN 107 104 104, .addN 107 107 103, .addN 108 105 105,
  .addN 108 108 105, .addN 109 108 108, .constN 90 11, .mulN 110 105 90, .addN 111 110 105,
  .addN 112 111 105, .addN 113 112 104, .addN 114 113 104, .addN 115 114 104, .addN 116 115 104,
  .addN 117 116 104, .addN 118 117 104, .addN 118 118 104, .addN 118 118 102, .addN 119 118 104,
  .addN 119 119 104, .addN 119 119 102, .addN 120 119 104, .constN 90 4, .addN 121 120 90,
  .constN 1 1, .constN 2 2, .constN 3 3, .copyN 4 105, .copyN 5 108, .copyN 6 109,
  .addN 7 109 105, .addN 8 7 105, .addN 9 8 105, .addN 10 9 105]

/-- **The front half.** -/
def front : Stmt := .seq bfs (.seq lstat (.seq median (.seq sqrtL (.seq findJ (.seq findJ'
  (.seq frep (.seq tloop (.seq wloop dloop))))))))

/-- **The separator program.** -/
def sepProg : Stmt := .seq setup (.ifLtN 100 105 (.seq front back) (.instr (.outN 100)))

/-! ### Numeric connectivity and the pigeonhole step -/

/-- Every vertex is reached from `0` along the darts. -/
def NConn (n m : ℕ) (tl rv : ℕ → ℕ) : Prop :=
  ∀ S : ℕ → Prop, S 0 → (∀ i < m, S (tl i) → S (tl (rv i))) → ∀ v < n, S v

theorem sum_lcF_le (L : ℕ → ℕ) (n : ℕ) (s : Finset ℕ) : ∑ l ∈ s, lcF L n l ≤ n := by
  unfold lcF
  rw [← card_biUnion (fun x _ y _ hxy => disjoint_filter.2 fun v _ h1 h2 => hxy (h1.symm.trans h2))]
  exact (card_le_card (biUnion_subset.2 fun _ _ => filter_subset _ _)).trans (by simp)

/-- **The pigeonhole step below the median**: among the levels `l₁, l₁ - 1, …, l₁ - t`, one has
at most `n / (t + 1)` vertices (or does not exist). -/
theorem exists_thin_below (L : ℕ → ℕ) (n l₁ t : ℕ) :
    ∃ j, j ≤ t ∧ (if l₁ < j then 0 else lcF L n (l₁ - j)) ≤ n / (t + 1) := by
  by_contra h
  push Not at h
  have hj : ∀ j ∈ range (t + 1), n / (t + 1) + 1 ≤ lcF L n (l₁ - j) ∧ j ≤ l₁ := by
    intro j hj
    have := h j (by simpa [Nat.lt_succ_iff] using hj)
    split_ifs at this with h1
    · exact absurd this (Nat.not_lt_zero _)
    · exact ⟨this, by omega⟩
  have hsum : ∑ j ∈ range (t + 1), lcF L n (l₁ - j) ≤ n := by
    rw [← sum_image (s := range (t + 1)) (g := fun j => l₁ - j) (f := lcF L n)
      (fun x hx y hy e => by
        have := (hj x hx).2; have := (hj y hy).2; simp only at e; omega)]
    exact sum_lcF_le L n _
  have h2 : ∑ j ∈ range (t + 1), (n / (t + 1) + 1) ≤ ∑ j ∈ range (t + 1), lcF L n (l₁ - j) :=
    sum_le_sum fun x hx => (hj x hx).1
  rw [sum_const, card_range, smul_eq_mul] at h2
  have := Nat.lt_mul_div_succ n (Nat.succ_pos t)
  rw [Nat.succ_eq_add_one] at this
  omega

/-- **The pigeonhole step above the median.** -/
theorem exists_thin_above (L : ℕ → ℕ) (n l₁ t : ℕ) :
    ∃ j, j ≤ t ∧ lcF L n (l₁ + 1 + j) ≤ n / (t + 1) := by
  by_contra h
  push Not at h
  have hsum : ∑ j ∈ range (t + 1), lcF L n (l₁ + 1 + j) ≤ n := by
    rw [← sum_image (s := range (t + 1)) (g := fun j => l₁ + 1 + j) (f := lcF L n)
      (fun x _ y _ e => by simp only at e; omega)]
    exact sum_lcF_le L n _
  have h2 : ∑ j ∈ range (t + 1), (n / (t + 1) + 1) ≤ ∑ j ∈ range (t + 1), lcF L n (l₁ + 1 + j) :=
    sum_le_sum fun j hj => h j (by simpa [Nat.lt_succ_iff] using hj)
  rw [sum_const, card_range, smul_eq_mul] at h2
  have := Nat.lt_mul_div_succ n (Nat.succ_pos t)
  rw [Nat.succ_eq_add_one] at this
  omega

/-- An injective map of `[0, m)` into itself is a permutation: every point is periodic. -/
theorem nperm_of_inj {m : ℕ} {f : ℕ → ℕ} (hlt : ∀ i < m, f i < m)
    (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) : NPerm m f := by
  refine ⟨hlt, hinj, fun i hi => ?_⟩
  have hit : ∀ k, f^[k] i < m := fun k => by
    induction k with
    | zero => exact hi
    | succ k ih => rw [Function.iterate_succ_apply']; exact hlt _ ih
  obtain ⟨a, ha, b, hb, hab, e⟩ : ∃ a ∈ range (m + 1), ∃ b ∈ range (m + 1), a ≠ b ∧
      f^[a] i = f^[b] i := by
    by_contra h
    push Not at h
    have := card_le_card_of_injOn (fun k => f^[k] i) (s := range (m + 1)) (t := range m)
      (fun k _ => mem_range.2 (hit k)) (fun x hx y hy e => by
        by_contra hne; exact h x hx y hy hne e)
    simp at this
  -- cancel the common prefix
  have hcancel : ∀ a b, a < b → f^[a] i = f^[b] i → f^[b - a] i = i := by
    intro a b hab e
    induction a generalizing b with
    | zero => simpa using e.symm
    | succ a ih =>
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at e
      have := ih b (by omega) (hinj _ (hit a) _ (hit b) e)
      rwa [show b + 1 - (a + 1) = b - a by omega]
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact ⟨b - a, by omega, hcancel a b h e⟩
  · exact ⟨a - b, by omega, hcancel b a h e.symm⟩

theorem NWf.nperm {n m : ℕ} {ofs tl rv ro : ℕ → ℕ} (h : NWf n m ofs tl rv ro) :
    NPerm m (ph rv ro) :=
  nperm_of_inj (fun _ hi => h.ph_lt hi) (fun _ hi _ hj e => h.ph_inj hi hj e)

/-- The facts after the front half, for the levels `L`, the parent darts `pr`, the median level
`l₁` and the thin levels `l₁ - j`, `l₁ + 1 + j'`. -/
structure FrontOut (n m : ℕ) (ofs w tl rv ro : ℕ → ℕ) (W : ℕ) (L pr : ℕ → ℕ) (l₁ j j' : ℕ)
    (c : Config) : Prop where
  wb : WordsBounded W c
  lay : Lay n m c
  cregs : CRegs m c
  out : c.output = []
  r122 : c.nreg 122 = ∑ v ∈ range n, w v
  r123 : c.nreg 123 = l₁
  r125 : c.nreg 125 = j
  r126 : c.nreg 126 = j'
  l₁_le : l₁ ≤ n
  j_le : j ≤ Nat.sqrt n
  j'_le : j' ≤ Nat.sqrt n
  low : 2 * ∑ v ∈ range n with L v < l₁, w v ≤ ∑ v ∈ range n, w v
  high : 2 * ∑ v ∈ range n with l₁ < L v, w v ≤ ∑ v ∈ range n, w v
  thinK : (Nat.sqrt n + 1) * #((range n).filter fun v => L v + j = l₁) ≤ n
  thinK' : (Nat.sqrt n + 1) * #((range n).filter fun v => L v = l₁ + 1 + j') ≤ n
  L0 : L 0 = 0
  Ln : ∀ v < n, L v < n
  par : ∀ v < n, v ≠ 0 → pr v < m ∧ tl (pr v) = v ∧ L (parN tl rv pr v) + 1 = L v
  adj : ∀ i < m, L (tl (rv i)) ≤ L (tl i) + 1
  Lm : ∀ v < n, c.nmem (13 * m + v) = L v
  prm : ∀ v < n, c.nmem (13 * m + n + v) = pr v
  frm : ∀ q < m, c.nmem (11 * m + q) = frepF (ph rv ro) q + 1
  dfacts : ∀ x < m, DFacts m rv ro (fun q => frepF (ph rv ro) q + 1) c.nmem x
  tm1 : ∀ v, 1 ≤ v → v < n →
    c.nmem (3 * m + 3 * pr v) = 1 ∧ c.nmem (3 * m + 3 * rv (pr v)) = 1
  tm0 : ∀ x < m, (∀ v, 1 ≤ v → v < n → x ≠ pr v ∧ x ≠ rv (pr v)) → c.nmem (3 * m + 3 * x) = 0
  fw1 : ∀ v < n, c.nmem (6 * m + ofs v) = w v * ind l₁ (L v + j) * ind (L v) (l₁ + 1 + j')
  fw0 : ∀ x < m, (∀ v < n, ofs v ≠ x) → c.nmem (6 * m + x) = 0
  z7 : ∀ f < m, c.nmem (7 * m + f) = 0
  z12 : ∀ G < m, c.nmem (12 * m + G) = 0
  zs : ∀ v < n, c.nmem (13 * m + 4 * n + v) = 0
  zp : ∀ i < 4, c.nmem (13 * m + 10 * n + 4 + i) = 0

theorem sum_lwF (L w : ℕ → ℕ) (n k : ℕ) :
    ∑ l ∈ range k, lwF L w n l = ∑ v ∈ range n with L v < k, w v := by
  rw [← sum_fiberwise_of_maps_to (s := (range n).filter fun v => L v < k) (t := range k) (g := L)
    (fun v hv => mem_range.2 (mem_filter.1 hv).2)]
  refine sum_congr rfl fun l hl => ?_
  unfold lwF
  rw [filter_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext v; simp only [mem_filter, mem_range] at hl ⊢
  omega

theorem card_level_eq (L : ℕ → ℕ) (n l₁ j : ℕ) :
    #((range n).filter fun v => L v + j = l₁) = if l₁ < j then 0 else lcF L n (l₁ - j) := by
  unfold lcF
  split_ifs with h
  · rw [card_eq_zero, filter_eq_empty_iff]; intro v _; omega
  · congr 1; ext v; simp only [mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

section proofs

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 3 * ∑ v ∈ range n, w v + 2 * n + 3 * m + 10 ≤ W)
  (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hN hIn hW hPW

omit hN hPW in
/-- **The constants.** -/
theorem setup_exec :
    ∃ c k, Exec P W setup initConfig c k ∧ k = 39 ∧ Lay n m c ∧ CRegs m c ∧
      c.nmem = (fun _ => 0) ∧ c.output = [] := by
  have hW' := hW; unfold memTop at hW'
  have hc : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have h0 : P.data.getD 0 0 = n := hIn.n_eq
  have h1 : P.data.getD 1 0 = m := hIn.m_eq
  have hr : ∀ r, initConfig.nreg r = 0 := fun _ => rfl
  unfold setup
  exec_block
  all_goals try (config_simp; (try simp only [hr, h0, h1]); omega)
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  all_goals config_simp
  all_goals simp only [hr, h0, h1]
  all_goals omega

omit hN hIn hW hPW in
theorem front_wr {r : ℕ} (hr : r ≤ 10) : front.wr r = false := by
  have : ∀ r ≤ 10, front.wr r = false := by decide
  exact this r hr

/-- **The front half.** From the constants and a clear memory, for a connected input in which
every vertex has a dart, the front half ends within `96 m + 101 n + 60` steps in a state
described by `FrontOut`. -/
theorem front_exec (hn : 1 ≤ n) (hconn : NConn n m tl rv)
    (hofs : ∀ v < n, ofs v < ofs (v + 1)) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hR : CRegs m c) (hz : c.nmem = fun _ => 0) (ho : c.output = []) :
    ∃ c' k, Exec P W front c c' k ∧ k ≤ 96 * m + 101 * n + 60 ∧
      ∃ L pr l₁ j j', FrontOut n m ofs w tl rv ro W L pr l₁ j j' c' := by
  have hW' := hW; unfold memTop at hW'
  have hW2 : memTop n m + 2 * n + 3 * m + 10 ≤ W := by omega
  -- breadth-first search
  obtain ⟨c₁, k₁, e₁, hk₁, hL₁, ho₁, hf₁, -, hmk0, hlv0, hcl, hlvn, hpar₁⟩ :=
    bfs_exec hN hIn hW2 hPW hn c hc hL (fun v _ => by simp [mkA, hz])
  have hall : ∀ v < n, mkA n m c₁.nmem v = 1 := by
    refine hconn (fun v => mkA n m c₁.nmem v = 1) hmk0 ?_
    intro i hi h
    exact (hcl _ (hN.tl_lt i hi) h i ((hN.blk i hi _ (hN.tl_lt i hi)).1 rfl).1
      ((hN.blk i hi _ (hN.tl_lt i hi)).1 rfl).2).1
  generalize hLdef : lvA m c₁.nmem = L
  generalize hprdef : prA n m c₁.nmem = pr
  have hLm₁ : ∀ v < n, c₁.nmem (13 * m + v) = L v := fun v _ => by rw [← hLdef]; rfl
  have hprm₁ : ∀ v < n, c₁.nmem (13 * m + n + v) = pr v := fun v _ => by rw [← hprdef]; rfl
  have hLn : ∀ v < n, L v < n := fun v hv => by rw [← hLdef]; exact hlvn v hv (hall v hv)
  have hL0 : L 0 = 0 := by rw [← hLdef]; exact hlv0
  have hpar : ∀ v < n, v ≠ 0 → pr v < m ∧ tl (pr v) = v ∧ L (parN tl rv pr v) + 1 = L v := by
    intro v hv h0
    obtain ⟨p1, p2, p3, -⟩ := hpar₁ v hv (hall v hv) h0
    rw [← hLdef, ← hprdef]; exact ⟨p1, p2, p3⟩
  have hadj : ∀ i < m, L (tl (rv i)) ≤ L (tl i) + 1 := by
    intro i hi
    have hb := (hN.blk i hi _ (hN.tl_lt i hi)).1 rfl
    rw [← hLdef]; exact (hcl _ (hN.tl_lt i hi) (hall _ (hN.tl_lt i hi)) i hb.1 hb.2).2
  have hz₁ : ∀ a, (a < 13 * m ∨ 13 * m + 4 * n ≤ a) → c₁.nmem a = 0 := fun a ha => by
    rw [hf₁ a ha, hz]
  -- the level statistics
  obtain ⟨c₂, k₂, e₂, hk₂, hL₂, ho₂, hf₂, h122₂, hlw₂, hlc₂⟩ := lstat_exec hIn hW L c₁
    e₁.wb_right hL₁ hLm₁ hLn (fun a h1 h2 => hz₁ a (Or.inr (by omega)))
  have hLm₂ : ∀ v < n, c₂.nmem (13 * m + v) = L v := fun v hv => by
    rw [hf₂ _ (Or.inl (by omega))]; exact hLm₁ v hv
  have htot : ∑ l ∈ range n, lwF L w n l = ∑ v ∈ range n, w v := by
    rw [sum_lwF]; congr 1; ext v; simp only [mem_filter, mem_range]
    exact ⟨fun h => h.1, fun h => ⟨h, hLn v h⟩⟩
  have hlwb : ∀ l < 2 * n + 2, lwF L w n l ≤ ∑ v ∈ range n, w v := fun l _ =>
    sum_le_sum_of_subset (filter_subset _ _)
  -- the median
  obtain ⟨c₃, k₃, e₃, hk₃, hm₃, ho₃, hr₃, hl₁, hlow, hhigh⟩ := median_exec hW hn
    (lwF L w n) _ c₂ e₂.wb_right hL₂ hlw₂ h122₂ le_rfl htot hlwb
  generalize hl₁def : c₃.nreg 123 = l₁ at hl₁ hlow hhigh
  have hL₃ : Lay n m c₃ := hL₂.of fun r h1 _ => hr₃ r h1 (by omega)
  -- `⌊√n⌋`
  obtain ⟨c₄, k₄, e₄, hk₄, hm₄, ho₄, hr₄, h124⟩ := sqrtL_exec hW c₃ e₃.wb_right hL₃
  have hL₄ : Lay n m c₄ := hL₃.of fun r h1 _ => hr₄ r h1 (by omega)
  -- the thin levels
  have hlc₄ : ∀ l < 2 * n + 2, c₄.nmem (13 * m + 7 * n + 2 + l) = lcF L n l := fun l hl => by
    rw [hm₄, hm₃]; exact hlc₂ l hl
  obtain ⟨c₅, k₅, e₅, hk₅, hm₅, ho₅, hr₅, hj, h85, hthin⟩ := findJ_exec hW
    (lcF L n) l₁ hl₁ c₄ e₄.wb_right hL₄ (by rw [hr₄ 123 (by omega) (by omega), hl₁def]) h124
    hlc₄ (exists_thin_below L n l₁ _)
  generalize hjdef : c₅.nreg 125 = j at hj hthin
  have hL₅ : Lay n m c₅ := hL₄.of fun r h1 _ => hr₅ r h1 (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, hm₆, ho₆, hr₆, hj', hthin'⟩ := findJ'_exec hW
    (lcF L n) l₁ hl₁ c₅ e₅.wb_right hL₅
    (by rw [hr₅ 123 (by omega) (by omega), hr₄ 123 (by omega) (by omega), hl₁def]) h85
    (fun l hl => by rw [hm₅]; exact hlc₄ l hl) (exists_thin_above L n l₁ _)
  generalize hj'def : c₆.nreg 126 = j' at hj' hthin'
  have hL₆ : Lay n m c₆ := hL₅.of fun r h1 _ => hr₆ r h1 (by omega)
  have hm₆' : c₆.nmem = c₂.nmem := by rw [hm₆, hm₅, hm₄, hm₃]
  -- the face representatives
  obtain ⟨c₇, k₇, e₇, hk₇, ho₇, hr₇, hf₇, hfr₇⟩ := frep_exec hN hIn hW2 hN.nperm c₆
    e₆.wb_right hL₆ (fun x hx => by
      rw [hm₆', hf₂ _ (Or.inl (by omega)), hz₁ _ (Or.inl (by omega))])
  have hL₇ : Lay n m c₇ := hL₆.of fun r h1 _ => hr₇ r h1
  generalize hfrdef : (fun q => frepF (ph rv ro) q + 1) = fr
  have hfrm₇ : ∀ q < m, c₇.nmem (11 * m + q) = fr q := fun q hq => by
    rw [← hfrdef]; exact hfr₇ q hq
  -- the tree marks
  obtain ⟨c₈, k₈, e₈, hk₈, ho₈, hr₈, hf₈, ht1, ht0⟩ := tloop_exec hN hIn hW pr
    (fun v h1 h2 => (hpar v h2 (by omega)).1) c₇ e₇.wb_right hL₇ (fun v h1 h2 => by
      rw [hf₇ _ (Or.inr (by omega)), hm₆', hf₂ _ (Or.inl (by omega))]; exact hprm₁ v h2)
  have hL₈ : Lay n m c₈ := hL₇.of fun r h1 _ => hr₈ r h1
  -- the face weights
  have hR₈ : ∀ r, 100 ≤ r → c₈.nreg r = c₆.nreg r := fun r h => (hr₈ r h).trans (hr₇ r h)
  obtain ⟨c₉, k₉, e₉, hk₉, ho₉, hr₉, hf₉, hw1, hw0⟩ := wloop_exec hN hIn hW L l₁ j j' hofs c₈
    e₈.wb_right hL₈ (fun v hv => by
      rw [hf₈ _ (by omega), hf₇ _ (Or.inr (by omega)), hm₆']; exact hLm₂ v hv)
    (fun v hv => (hLn v hv).le)
    (by rw [hR₈ 123 (by omega), hr₆ 123 (by omega) (by omega), hr₅ 123 (by omega) (by omega),
      hr₄ 123 (by omega) (by omega), hl₁def])
    (by rw [hR₈ 125 (by omega), hr₆ 125 (by omega) (by omega), hjdef])
    (by rw [hR₈ 126 (by omega), hj'def]) hl₁ (hj.trans (Nat.sqrt_le_self n))
    (hj'.trans (Nat.sqrt_le_self n))
  have hL₉ : Lay n m c₉ := hL₈.of fun r h1 _ => hr₉ r h1
  -- the reversals and the spokes
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, ho₁₀, hr₁₀, hf₁₀, hD⟩ := dloop_exec hN hIn hW fr c₉ e₉.wb_right
    hL₉ (fun q hq => by rw [hf₉ _ (by omega), hf₈ _ (by omega)]; exact hfrm₇ q hq)
    (fun q hq => by rw [← hfrdef]; have := frepF_le (f := ph rv ro) q; dsimp only; omega)
  have e : Exec P W front c c₁₀
      (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ + k₁₀))))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ e₁₀))))))))
  have hR₁₀ : ∀ r, 100 ≤ r → c₁₀.nreg r = c₆.nreg r := fun r h =>
    (hr₁₀ r h).trans ((hr₉ r h).trans (hR₈ r h))
  -- the memory above `6 m` outside the face weights and the face representatives
  have hmA : ∀ a, 7 * m ≤ a → (a < 11 * m ∨ 12 * m ≤ a) → c₁₀.nmem a = c₂.nmem a := by
    intro a h1 h2
    rw [hf₁₀ a (Or.inl (by omega)), hf₉ a (by omega), hf₈ a (by omega), hf₇ a h2, hm₆']
  have hmB : ∀ a, 13 * m ≤ a → c₁₀.nmem a = c₁.nmem a ∨ 13 * m + 5 * n ≤ a := by
    intro a h1
    by_cases h : a < 13 * m + 5 * n
    · left; rw [hmA a (by omega) (Or.inr (by omega)), hf₂ a (Or.inl h)]
    · right; omega
  refine ⟨c₁₀, _, e, by omega, L, pr, l₁, j, j', ⟨e₁₀.wb_right, hL₉.of fun r h1 _ => hr₁₀ r h1,
    cregs_of hR fun r hr => e.nreg_of_wr (front_wr hr), by
      rw [ho₁₀, ho₉, ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁, ho], ?_, ?_, ?_, ?_, hl₁, hj, hj',
    ?_, ?_, ?_, ?_, hL0, hLn, hpar, hadj, ?_, ?_, ?_, by rw [← hfrdef] at hD; exact hD,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hR₁₀ 122 (by omega), hr₆ 122 (by omega) (by omega), hr₅ 122 (by omega) (by omega),
      hr₄ 122 (by omega) (by omega), hr₃ 122 (by omega) (by omega), h122₂]
  · rw [hR₁₀ 123 (by omega), hr₆ 123 (by omega) (by omega), hr₅ 123 (by omega) (by omega),
      hr₄ 123 (by omega) (by omega), hl₁def]
  · rw [hR₁₀ 125 (by omega), hr₆ 125 (by omega) (by omega), hjdef]
  · rw [hR₁₀ 126 (by omega), hj'def]
  · rw [← sum_lwF]; exact hlow
  · have e1 := sum_filter_add_sum_filter_not (range n) (fun v => L v < l₁ + 1) w
    rw [← sum_lwF] at e1
    have e2 : ∑ v ∈ range n with ¬ L v < l₁ + 1, w v = ∑ v ∈ range n with l₁ < L v, w v := by
      congr 1; ext v; simp only [mem_filter, mem_range]; omega
    rw [e2] at e1
    omega
  · rw [card_level_eq]
    exact (Nat.mul_le_mul_left _ hthin).trans (Nat.mul_div_le n _)
  · exact (Nat.mul_le_mul_left _ hthin').trans (Nat.mul_div_le n _)
  · intro v hv
    rcases hmB (13 * m + v) (by omega) with h | h
    · rw [h]; exact hLm₁ v hv
    · omega
  · intro v hv
    rcases hmB (13 * m + n + v) (by omega) with h | h
    · rw [h]; exact hprm₁ v hv
    · omega
  · intro q hq
    rw [hf₁₀ _ (Or.inl (by omega)), hf₉ _ (by omega), hf₈ _ (by omega), hfrm₇ q hq, ← hfrdef]
  · intro v h1 h2
    have hp := (hpar v h2 (by omega)).1
    have hq := hN.rv_lt _ hp
    rw [hf₁₀ _ (Or.inr ⟨by omega, by omega⟩), hf₁₀ _ (Or.inr ⟨by omega, by omega⟩),
      hf₉ _ (by omega), hf₉ _ (by omega)]
    exact ht1 v h1 h2
  · intro x hx h
    rw [hf₁₀ _ (Or.inr ⟨by omega, by omega⟩), hf₉ _ (by omega), ht0 x hx h,
      hf₇ _ (Or.inl (by omega)), hm₆', hf₂ _ (Or.inl (by omega)), hz₁ _ (Or.inl (by omega))]
  · intro v hv; rw [hf₁₀ _ (Or.inl (by have := hN.ofs_le_m hv.le; omega))]; exact hw1 v hv
  · intro x hx h
    rw [hf₁₀ _ (Or.inl (by omega)), hw0 x hx h, hf₈ _ (by omega), hf₇ _ (Or.inl (by omega)),
      hm₆', hf₂ _ (Or.inl (by omega)), hz₁ _ (Or.inl (by omega))]
  · intro f hf
    rw [hmA _ (by omega) (Or.inl (by omega)), hf₂ _ (Or.inl (by omega)),
      hz₁ _ (Or.inl (by omega))]
  · intro G hG
    rw [hmA _ (by omega) (Or.inr (by omega)), hf₂ _ (Or.inl (by omega)),
      hz₁ _ (Or.inl (by omega))]
  · intro v hv
    rcases hmB (13 * m + 4 * n + v) (by omega) with h | h
    · rw [h, hz₁ _ (Or.inr (by omega))]
    · omega
  · intro i hi
    rw [hmA _ (by omega) (Or.inr (by omega)), hf₂ _ (Or.inr (by omega)),
      hz₁ _ (Or.inr (by omega))]

/-- **The separator program, `m ≥ 1`.** For a connected input in which every vertex has a dart,
the compiled program halts within `320 m + 191 n + 403` steps, and its output satisfies every
property `Φ` that the back half guarantees from every state described by `FrontOut`. -/
theorem sepProg_run (hn : 1 ≤ n) (hm : 1 ≤ m) (hconn : NConn n m tl rv)
    (hofs : ∀ v < n, ofs v < ofs (v + 1)) (Φ : List ℕ → Prop)
    (hback : ∀ L pr l₁ j j' c, FrontOut n m ofs w tl rv ro W L pr l₁ j j' c →
      ∃ c' k, Exec P W back c c' k ∧ k ≤ 224 * m + 90 * n + 300 ∧ Φ c'.output) :
    ∃ out, WordRAM.RunsWithin (compile sepProg 0 ++ [Instr.halt]) P W
      (320 * m + 191 * n + 403) out ∧ Φ out := by
  obtain ⟨c₀, k₀, e₀, rfl, hL₀, hR₀, hz₀, ho₀⟩ := setup_exec (n := n) (m := m) hIn hW
  have h0 : c₀.nreg 100 < c₀.nreg 105 := by rw [hL₀.r100, hL₀.r105]; omega
  obtain ⟨c₁, k₁, e₁, hk₁, L, pr, l₁, j, j', hF⟩ :=
    front_exec hN hIn hW hPW hn hconn hofs c₀ e₀.wb_right hL₀ hR₀ hz₀ ho₀
  obtain ⟨c₂, k₂, e₂, hk₂, hΦ⟩ := hback L pr l₁ j j' c₁ hF
  have e : Exec P W sepProg initConfig c₂ (39 + ((k₁ + k₂) + 1)) :=
    .seq e₀ (.ifLtN_true h0 (.seq e₁ e₂))
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output e rfl
  exact ⟨c₂.output, ⟨k', by omega, h1, h2⟩, hΦ⟩

omit hN hPW in
/-- **The separator program, `m = 0`**: it prints a single `0`. -/
theorem sepProg_zero (hm : m = 0) :
    WordRAM.RunsWithin (compile sepProg 0 ++ [Instr.halt]) P W 43 [0] := by
  obtain ⟨c₀, k₀, e₀, rfl, hL₀, -, -, ho₀⟩ := setup_exec (n := n) (m := m) hIn hW
  have h0 : ¬ c₀.nreg 100 < c₀.nreg 105 := by rw [hL₀.r100, hL₀.r105]; omega
  have e : Exec P W sepProg initConfig _ (39 + (1 + 2)) :=
    .seq e₀ (.ifLtN_false h0 (Exec.outN e₀.wb_right 100))
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output (out := [0]) e (by
    simp only [ho₀, hL₀.r100, List.nil_append])
  exact ⟨k', by omega, h1, h2⟩

end proofs

end SepProg

end PlanarSeparator

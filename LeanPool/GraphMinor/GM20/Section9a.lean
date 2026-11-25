/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10b
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Graph Minors XX, Section 9: the cells around a cuff

The proof of (9.1) walks around each cuff. This file shows that the nodes on a cuff `Θ` and the
cells
that border `Θ` form a cycle (`CuffCycle`): the nodes are `pos 0, …, pos (k-1)`, with `k ≥ 2`, the
border cells are `cell 0, …, cell (k-1)`, and `cell m` has the nodes `pos m` and `pos (m+1)`. All
these
indices run over `ℕ`, with period `k`, and the order of the nodes on `Θ` is the order of the
indices.

We take the angles of the nodes under a parametrization of `Θ` by the circle, and sort them. Between
two consecutive nodes `Θ` has an open arc which contains no node, so it lies in one cell.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface

/-- The sorted angles of a finite set, continued periodically. -/
theorem exists_angle_seq (s : Finset ℝ) (hs : s.Nonempty)
    (h : ∀ x ∈ s, ∀ y ∈ s, x - y < 2 * Real.pi) :
    ∃ (k : ℕ) (T : ℕ → ℝ), 0 < k ∧ StrictMono T ∧ (∀ m, T (m + k) = T m + 2 * Real.pi) ∧
      (∀ x ∈ s, ∃ m < k, T m = x) ∧ ∀ m < k, T m ∈ s := by
  set k := s.card with hk
  have hk0 : 0 < k := Finset.card_pos.mpr hs
  let L := s.orderEmbOfFin hk.symm
  let T : ℕ → ℝ := fun m ↦ L ⟨m % k, Nat.mod_lt _ hk0⟩ + (m / k : ℕ) * (2 * Real.pi)
  have hpi := Real.pi_pos
  have hmem : ∀ i, L i ∈ s := fun i ↦ Finset.orderEmbOfFin_mem _ _ _
  have hT : ∀ m (hm : m < k), T m = L ⟨m, hm⟩ := by
    intro m hm
    simp only [T, Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm]
    simp
  refine ⟨k, T, hk0, strictMono_nat_of_lt_succ fun m ↦ ?_, fun m ↦ ?_, fun x hx ↦ ?_,
    fun m hm ↦ ?_⟩
  · by_cases hm : (m + 1) % k = 0
    · have h₁ : (m + 1) / k = m / k + 1 := by
        rw [Nat.succ_div]
        rw [ite_eq_left ((Nat.dvd_iff_mod_eq_zero).mpr hm)]
      simp only [T, h₁]
      have h₂ := h _ (hmem ⟨m % k, Nat.mod_lt _ hk0⟩) _ (hmem ⟨(m + 1) % k, Nat.mod_lt _ hk0⟩)
      push_cast
      nlinarith
    · have hdiv : (m + 1) / k = m / k := by
        rw [Nat.succ_div, ite_eq_right (fun h' ↦ hm (Nat.dvd_iff_mod_eq_zero.mp h'))]
        rfl
      have hk1 : 1 < k := by
        by_contra hc
        have hk2 : k = 1 := by omega
        exact hm (by rw [hk2, Nat.mod_one])
      have hmod : (m + 1) % k = m % k + 1 := by
        have h₄ := Nat.mod_lt m hk0
        have h₅ : (m + 1) % k = (m % k + 1) % k := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt hk1]
        by_cases h' : m % k + 1 = k
        · exact absurd (by rw [h₅, h', Nat.mod_self]) hm
        · rw [h₅, Nat.mod_eq_of_lt (by omega)]
      simp only [T, hdiv]
      have h₃ : L ⟨m % k, Nat.mod_lt _ hk0⟩ < L ⟨(m + 1) % k, Nat.mod_lt _ hk0⟩ :=
        L.strictMono (by simp [Fin.lt_def, hmod])
      linarith
  · simp only [T, Nat.add_mod_right, Nat.add_div_right _ hk0]
    push_cast
    ring
  · have hx' : x ∈ Set.range L := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨i, rfl⟩ := hx'
    exact ⟨i.1, i.2, hT _ i.2⟩
  · rw [hT m hm]
    exact hmem _

theorem exists_exp_eq_Ico (a : ℝ) (x : Circle) :
    ∃ t ∈ Ico a (a + 2 * Real.pi), Circle.exp t = x := by
  have hpi : 0 < 2 * Real.pi := by positivity
  refine ⟨toIcoMod hpi a (Complex.arg x), toIcoMod_mem_Ico hpi a _, ?_⟩
  have h₁ : toIcoMod hpi a (Complex.arg x) =
      Complex.arg x - toIcoDiv hpi a (Complex.arg x) • (2 * Real.pi) := rfl
  have h₂ : Circle.exp (toIcoMod hpi a (Complex.arg x)) = Circle.exp (Complex.arg x) := by
    rw [h₁, zsmul_eq_mul]
    exact Circle.exp_eq_exp.2 ⟨-toIcoDiv hpi a (Complex.arg x), by push_cast; ring⟩
  exact h₂.trans (Circle.exp_arg x)

/-- Two angles less than a full turn apart with the same image are equal. -/
theorem eq_of_exp_eq {s t : ℝ} (h : Circle.exp s = Circle.exp t) (h₁ : s ≤ t)
    (h₂ : t < s + 2 * Real.pi) : s = t := by
  have hle : t ∈ Ico s (s + 2 * Real.pi) := ⟨h₁, h₂⟩
  exact Circle.exp_injOn_Ico (a := s) (b := s + 2 * Real.pi) (by simp)
    ⟨le_rfl, by linarith⟩ hle h

/-- The circle is not homeomorphic to the interval: removing a middle point of the interval
disconnects it, and removing a point from the circle does not. -/
theorem not_homeomorph_circle_unitInterval (g : Circle ≃ₜ unitInterval) : False := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let a : ℝ := Complex.arg (g.symm m)
  have hconn : IsPreconnected ((fun t ↦ g (Circle.exp t)) '' Ioo a (a + 2 * Real.pi)) :=
    isPreconnected_Ioo.image _ (g.continuous.comp Circle.exp.continuous).continuousOn
  have hmem : ∀ y : unitInterval, y ≠ m → y ∈ (fun t ↦ g (Circle.exp t)) '' Ioo a (a + 2 * Real.pi)
    := by
    intro y hy
    obtain ⟨t, ht, hte⟩ := exists_exp_eq_Ico a (g.symm y)
    have hne : t ≠ a := by
      rintro rfl
      apply hy
      have : g.symm y = g.symm m := by rw [← hte, Circle.exp_arg]
      exact g.symm.injective this
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 hne.symm, ht.2⟩, ?_⟩
    simp only [hte, Homeomorph.apply_symm_apply]
  have h0 : (0 : unitInterval) ≠ m := fun h ↦ by
    have := congrArg Subtype.val h
    norm_num [m] at this
  have h1 : (1 : unitInterval) ≠ m := fun h ↦ by
    have := congrArg Subtype.val h
    norm_num [m] at this
  obtain ⟨t, ht, hte⟩ := hconn.Icc_subset (hmem 0 h0) (hmem 1 h1)
    (show m ∈ Icc 0 1 from ⟨unitInterval.nonneg _, unitInterval.le_one _⟩)
  have h₂ : Circle.exp t = Circle.exp a := by
    rw [Circle.exp_arg]
    exact (g.symm_apply_eq.mpr hte.symm).symm
  exact absurd (eq_of_exp_eq h₂.symm ht.1.le (by linarith [ht.2])) ht.1.ne

variable {S : Type} [TopologicalSpace S]

theorem mem_arcComponentsIn_pathComponentIn {F : Set S} {x : S} (hx : x ∈ F) :
    pathComponentIn F x ∈ arcComponentsIn F :=
  ⟨⟨x, mem_pathComponentIn_self hx⟩, pathComponentIn_subset, isPathConnected_pathComponentIn hx,
    fun _ hDF hD hsub ↦ subset_antisymm
      (hD.subset_pathComponentIn (hsub (mem_pathComponentIn_self hx)) hDF) hsub⟩

theorem eq_pathComponentIn {F c : Set S} (hc : c ∈ arcComponentsIn F) {x : S} (hx : x ∈ c) :
    c = pathComponentIn F x := by
  have hsub := hc.2.2.1.subset_pathComponentIn hx hc.2.1
  exact (hc.2.2.2 _ pathComponentIn_subset (isPathConnected_pathComponentIn (hc.2.1 hx)) hsub).symm

theorem arcComponent_eq {F c c' : Set S} (hc : c ∈ arcComponentsIn F)
    (hc' : c' ∈ arcComponentsIn F) {x : S} (hx : x ∈ c) (hx' : x ∈ c') : c = c' :=
  (eq_pathComponentIn hc hx).trans (eq_pathComponentIn hc' hx').symm

/-- The cycle of nodes and border cells around a cuff `Θ`, under the parametrization `f`. All
indices
have period `k`. The nodes are `pos m`, at the angles `T m`, and `cell m` is the cell between `pos
m`
and `pos (m + 1)`. -/
structure CuffCycle (Γ : Painting S) {Θ : Set S} (f : Circle ≃ₜ Θ) where
  /-- The number of nodes on `Θ`. -/
  k : ℕ
  two_le : 2 ≤ k
  /-- The angles of the nodes, in order. -/
  T : ℕ → ℝ
  strictMono : StrictMono T
  T_add : ∀ m, T (m + k) = T m + 2 * Real.pi
  /-- The cells bordering `Θ`, in order. -/
  cell : ℕ → Set S
  cell_add : ∀ m, cell (m + k) = cell m
  pos_mem : ∀ m, GM19.cuffPoint f (T m) ∈ Γ.N
  exists_pos : ∀ n ∈ Γ.N ∩ Θ, ∃ m < k, GM19.cuffPoint f (T m) = n
  cell_mem : ∀ m, cell m ∈ Γ.C
  cell_inter : ∀ m, cell m ∩ Θ = GM19.cuffPoint f '' Ioo (T m) (T (m + 1))
  tilde_eq : ∀ m, tilde (cell m) = {GM19.cuffPoint f (T m), GM19.cuffPoint f (T (m + 1))}
  cell_ne : ∀ m m', m < m' → m' < m + k → cell m ≠ cell m'
  exists_cell : ∀ c ∈ Γ.C, (c ∩ Θ).Nonempty → ∃ m < k, cell m = c

theorem cuffPoint_mem {Θ : Set S} (f : Circle ≃ₜ Θ) (t : ℝ) : GM19.cuffPoint f t ∈ Θ :=
  (f (Circle.exp t)).2

theorem continuous_cuffPoint {Θ : Set S} (f : Circle ≃ₜ Θ) :
    Continuous (GM19.cuffPoint f) :=
  continuous_subtype_val.comp (f.continuous.comp Circle.exp.continuous)

theorem cuffPoint_add {Θ : Set S} (f : Circle ≃ₜ Θ) (t : ℝ) :
    GM19.cuffPoint f (t + 2 * Real.pi) = GM19.cuffPoint f t := by
  simp only [GM19.cuffPoint, Circle.exp_add_two_pi]

theorem cuffPoint_eq_iff {Θ : Set S} (f : Circle ≃ₜ Θ) {s t : ℝ} :
    GM19.cuffPoint f s = GM19.cuffPoint f t ↔ Circle.exp s = Circle.exp t := by
  simp only [GM19.cuffPoint]
  exact ⟨fun h ↦ f.injective (Subtype.ext h), fun h ↦ by rw [h]⟩

theorem exists_cuffPoint_eq {Θ : Set S} (f : Circle ≃ₜ Θ) (a : ℝ) {x : S} (hx : x ∈ Θ) :
    ∃ t ∈ Ico a (a + 2 * Real.pi), GM19.cuffPoint f t = x := by
  obtain ⟨t, ht, hte⟩ := exists_exp_eq_Ico a (f.symm ⟨x, hx⟩)
  exact ⟨t, ht, by simp [GM19.cuffPoint, hte]⟩

theorem Painting.cuff_subset_U (Γ : Painting S) {Θ : Set S} (hΘ : Θ ∈ cuffs S) : Θ ⊆ Γ.U := by
  obtain ⟨p, hp, rfl⟩ := hΘ
  exact (connectedComponentIn_subset _ _).trans Γ.bd_subset

theorem tilde_subset_N (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.C) : tilde c ⊆ Γ.N := by
  rw [← Γ.closure_inter c hc]
  exact inter_subset_right

/-- The closure of a cell meets the boundary of `Σ` inside the cuffs that it borders. -/
theorem closure_inter_bd_subset (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.C) {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) (hcΘ : (c ∩ Θ).Nonempty) : closure c ∩ bd S ⊆ Θ := by
  obtain ⟨x, hxc, hxΘ⟩ := hcΘ
  obtain ⟨p, hp, rfl⟩ := hΘ
  have hxbd : x ∈ bd S := connectedComponentIn_subset _ _ hxΘ
  obtain ⟨hcard, ⟨hL⟩, hends⟩ := Γ.border_cell c hc ⟨x, hxc, hxbd⟩
  have hconn : IsPreconnected (closure c ∩ bd S) := by
    have := (isPreconnected_univ (α := unitInterval)).image (fun t ↦ (hL t).1)
      (continuous_subtype_val.comp hL.continuous).continuousOn
    have himg : (fun t ↦ (hL t).1) '' univ = closure c ∩ bd S := by
      ext y
      constructor
      · rintro ⟨t, -, rfl⟩
        exact (hL t).2
      · intro hy
        exact ⟨hL.symm ⟨y, hy⟩, trivial, by simp⟩
    rwa [himg] at this
  rw [connectedComponentIn_eq hxΘ]
  exact hconn.subset_connectedComponentIn ⟨subset_closure hxc, hxbd⟩ inter_subset_right

/-- The closure of a border cell does not contain the whole cuff, since it meets `bd(Σ)` in a line.
-/
theorem not_cuff_subset_closure (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.C) {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) (hcΘ : (c ∩ Θ).Nonempty) (f : Circle ≃ₜ Θ) : ¬ Θ ⊆ closure c := by
  intro hsub
  have hbd : Θ ⊆ bd S := by
    obtain ⟨p, hp, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have heq : closure c ∩ bd S = Θ :=
    subset_antisymm (closure_inter_bd_subset Γ hc hΘ hcΘ) (subset_inter hsub hbd)
  obtain ⟨x, hxc, hxΘ⟩ := hcΘ
  obtain ⟨-, ⟨hL⟩, -⟩ := Γ.border_cell c hc ⟨x, hxc, hbd hxΘ⟩
  rw [heq] at hL
  exact not_homeomorph_circle_unitInterval (f.trans hL.symm)

/-- A point of `Θ` that is not at a node lies on one of the arcs between consecutive nodes. -/
theorem exists_mem_Ioo_of_seq {T : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) {t : ℝ}
    (h₁ : T a ≤ t) (h₂ : t < T b) : ∃ j, a ≤ j ∧ j < b ∧ T j ≤ t ∧ t < T (j + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd h₂ (not_lt.mpr h₁)
  | succ b hab ih =>
    by_cases h : t < T b
    · obtain ⟨j, h₃, h₄, h₅, h₆⟩ := ih h
      exact ⟨j, h₃, by omega, h₅, h₆⟩
    · exact ⟨b, hab, by omega, not_lt.mp h, h₂⟩

theorem T_add_mul {k : ℕ} {T : ℕ → ℝ} (h : ∀ m, T (m + k) = T m + 2 * Real.pi) (m q : ℕ) :
    T (m + q * k) = T m + q * (2 * Real.pi) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h, ih]
    push_cast
    ring

/-- Every angle of a node is a term of the sequence `T`, if it is at least `T 0`. -/
theorem exists_T_eq {k : ℕ} {T : ℕ → ℝ} (_hk : 0 < k) (hT : StrictMono T)
    (h : ∀ m, T (m + k) = T m + 2 * Real.pi) {m : ℕ} (hm : m < k) {t : ℝ}
    (ht : Circle.exp t = Circle.exp (T m)) (h₀ : T 0 ≤ t) : ∃ j, T j = t := by
  obtain ⟨z, hz⟩ := Circle.exp_eq_exp.mp ht
  have hpi := Real.pi_pos
  have hT0 : T m < T 0 + 2 * Real.pi := by
    have := hT (show m < 0 + k by omega)
    rwa [h] at this
  have hz0 : 0 ≤ z := by
    by_contra hc
    have hle : (z : ℝ) ≤ -1 := by exact_mod_cast (by omega : z ≤ -1)
    nlinarith
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  refine ⟨m + q * k, ?_⟩
  rw [T_add_mul h, hz]
  simp

theorem cuffPoint_add_mul {Θ : Set S} (f : Circle ≃ₜ Θ) (t : ℝ) (q : ℕ) :
    GM19.cuffPoint f (t + q * (2 * Real.pi)) = GM19.cuffPoint f t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← ih, ← cuffPoint_add f (t + q * (2 * Real.pi))]
    congr 1
    push_cast
    ring

private theorem exists_distinct_cuff_nodes (Γ : Painting S) {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ) (hbd : Θ ⊆ bd S) (hU : Θ ⊆ Γ.U) :
    ∃ a b : S, a ∈ Γ.N ∩ Θ ∧ b ∈ Γ.N ∩ Θ ∧ a ≠ b := by
  have hpi := Real.pi_pos
  have hinj : InjOn (GM19.cuffPoint f) (Ico 0 (0 + 2 * Real.pi)) := fun a ha b hb hab ↦
    Circle.exp_injOn_Ico (a := 0) (b := 0 + 2 * Real.pi) (by simp) ha hb
      ((cuffPoint_eq_iff f).mp hab)
  have hinf : (GM19.cuffPoint f '' Ico 0 (0 + 2 * Real.pi)).Infinite :=
    (Ico_infinite (by linarith)).image hinj
  obtain ⟨x, ⟨⟨t, -, rfl⟩, hxN⟩⟩ := (hinf.sdiff Γ.finite_N).nonempty
  have hxΘ := cuffPoint_mem f t
  set x := GM19.cuffPoint f t with hx
  have hxc₀ : pathComponentIn (Γ.U \ Γ.N) x ∈ Γ.C := mem_arcComponentsIn_pathComponentIn ⟨hU hxΘ,
    hxN⟩
  have hxm₀ : x ∈ pathComponentIn (Γ.U \ Γ.N) x := mem_pathComponentIn_self ⟨hU hxΘ, hxN⟩
  obtain ⟨hcard₀, -, -⟩ := Γ.border_cell _ hxc₀ ⟨x, hxm₀, hbd hxΘ⟩
  obtain ⟨a, b, hab, hti⟩ := Set.ncard_eq_two.mp hcard₀
  have hmemN : ∀ {y}, y ∈ tilde (pathComponentIn (Γ.U \ Γ.N) x) → y ∈ Γ.N ∩ Θ := fun hy ↦
    ⟨tilde_subset_N Γ hxc₀ hy, node_mem_cuff Γ hxc₀ hΘ ⟨x, hxm₀, hxΘ⟩ hy⟩
  have ha : a ∈ Γ.N ∩ Θ := hmemN (by rw [hti]; exact Or.inl rfl)
  have hb : b ∈ Γ.N ∩ Θ := hmemN (by rw [hti]; exact Or.inr rfl)
  exact ⟨a, b, ha, hb, hab⟩

/-- The nodes and border cells around a cuff form a cycle. We sort the angles of the nodes. Between
consecutive nodes the cuff has an open arc with no node, which lies in one cell. Since the closure
of
a border cell has exactly two nodes, and does not contain the cuff, that cell has exactly these two
nodes, and distinct arcs lie in distinct cells. -/
theorem exists_cuffCycle (Γ : Painting S) {Θ : Set S} (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ) :
    Nonempty (CuffCycle Γ f) := by
  classical
  have hpi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hbd : Θ ⊆ bd S := by
    obtain ⟨p, hp, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hU := Γ.cuff_subset_U hΘ
  have hfin : (Γ.N ∩ Θ).Finite := Γ.finite_N.inter_of_left _
  choose! g hg hgf using fun x (hx : x ∈ Γ.N ∩ Θ) ↦ exists_cuffPoint_eq f 0 hx.2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_distinct_cuff_nodes Γ hΘ f hbd hU
  let s : Finset ℝ := hfin.toFinset.image g
  have hmems : ∀ {y}, y ∈ Γ.N ∩ Θ → g y ∈ s := fun hy ↦
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hy)
  have hdiff : ∀ y ∈ s, ∀ z ∈ s, y - z < 2 * Real.pi := by
    intro y hy z hz
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    have h₁ := (hg _ (hfin.mem_toFinset.mp hy')).2
    have h₂ := (hg _ (hfin.mem_toFinset.mp hz')).1
    linarith
  obtain ⟨k, T, hk, hT, hadd, hsurj, hins⟩ := exists_angle_seq s ⟨_, hmems ha⟩ hdiff
  have htwo : 2 ≤ k := by
    by_contra hc
    have hk1 : k = 1 := by omega
    subst hk1
    obtain ⟨m, hm, hTm⟩ := hsurj _ (hmems ha)
    obtain ⟨m', hm', hTm'⟩ := hsurj _ (hmems hb)
    have : m = m' := by omega
    subst this
    apply hab
    rw [← hgf a ha, ← hgf b hb, ← hTm, ← hTm']
  let P := GM19.cuffPoint f
  have hposN : ∀ m, P (T m) ∈ Γ.N ∩ Θ := by
    intro m
    have hm : m = m % k + (m / k) * k := by
      rw [Nat.mul_comm]
      exact (Nat.mod_add_div m k).symm
    have h₁ : P (T m) = P (T (m % k)) := by
      rw [hm, T_add_mul hadd, Nat.add_mul_mod_self_right, Nat.mod_mod]
      exact cuffPoint_add_mul f _ _
    obtain ⟨n, hn, hne⟩ := Finset.mem_image.mp (hins _ (Nat.mod_lt m hk))
    have hn' := hfin.mem_toFinset.mp hn
    rw [h₁, ← hne, show P (g n) = n from hgf n hn']
    exact hn'
  have hnone : ∀ m t, T m < t → t < T (m + 1) → P t ∉ Γ.N := by
    intro m t h₁ h₂ hN
    have hn : P t ∈ Γ.N ∩ Θ := ⟨hN, cuffPoint_mem f t⟩
    obtain ⟨j, hj, hTj⟩ := hsurj _ (hmems hn)
    have hexp : Circle.exp t = Circle.exp (T j) := by
      refine (cuffPoint_eq_iff f).mp ?_
      rw [hTj]
      exact (hgf _ hn).symm
    obtain ⟨j', hj'⟩ := exists_T_eq hk hT hadd hj hexp
      ((hT.monotone (Nat.zero_le m)).trans h₁.le)
    rw [← hj'] at h₁ h₂
    have h₃ := hT.lt_iff_lt.mp h₁
    have h₄ := hT.lt_iff_lt.mp h₂
    omega
  have hpos_ne : ∀ m m', m < m' → m' < m + k → P (T m) ≠ P (T m') := by
    intro m m' h₁ h₂ heq
    have h₃ : T m' < T m + 2 * Real.pi := by
      rw [← hadd]
      exact hT h₂
    exact (hT h₁).ne (eq_of_exp_eq ((cuffPoint_eq_iff f).mp heq) (hT h₁).le h₃)
  let mid : ℕ → ℝ := fun m ↦ (T m + T (m + 1)) / 2
  have hmid : ∀ m, mid m ∈ Ioo (T m) (T (m + 1)) := fun m ↦ by
    have := hT (Nat.lt_succ_self m)
    exact ⟨by simp only [mid]; linarith, by simp only [mid]; linarith⟩
  let cell : ℕ → Set S := fun m ↦ pathComponentIn (Γ.U \ Γ.N) (P (mid m))
  have hAU : ∀ m, P '' Ioo (T m) (T (m + 1)) ⊆ Γ.U \ Γ.N := by
    rintro m _ ⟨t, ht, rfl⟩
    exact ⟨hU (cuffPoint_mem f t), hnone m t ht.1 ht.2⟩
  have hmidU : ∀ m, P (mid m) ∈ Γ.U \ Γ.N := fun m ↦ hAU m ⟨_, hmid m, rfl⟩
  have hAconn : ∀ m, IsPathConnected (P '' Ioo (T m) (T (m + 1))) := fun m ↦
    ((convex_Ioo _ _).isPathConnected ⟨_, hmid m⟩).image (continuous_cuffPoint f)
  have hAsub : ∀ m, P '' Ioo (T m) (T (m + 1)) ⊆ cell m := fun m ↦
    (hAconn m).subset_pathComponentIn ⟨_, hmid m, rfl⟩ (hAU m)
  have hcell : ∀ m, cell m ∈ Γ.C := fun m ↦ mem_arcComponentsIn_pathComponentIn (hmidU m)
  have hmeet : ∀ m, (cell m ∩ Θ).Nonempty := fun m ↦
    ⟨_, hAsub m ⟨_, hmid m, rfl⟩, cuffPoint_mem f _⟩
  have hcl : ∀ m, P (T m) ∈ closure (cell m) ∧ P (T (m + 1)) ∈ closure (cell m) := by
    intro m
    have hlt := hT (Nat.lt_succ_self m)
    have hcont := continuous_cuffPoint f
    have hmaps : MapsTo P (Ioo (T m) (T (m + 1))) (cell m) := fun t ht ↦ hAsub m ⟨t, ht, rfl⟩
    refine ⟨map_mem_closure hcont ?_ hmaps, map_mem_closure hcont ?_ hmaps⟩
    · rw [closure_Ioo hlt.ne]
      exact ⟨le_rfl, hlt.le⟩
    · rw [closure_Ioo hlt.ne]
      exact ⟨hlt.le, le_rfl⟩
  have htilde : ∀ m, tilde (cell m) = {P (T m), P (T (m + 1))} := by
    intro m
    obtain ⟨y, hy, hyΘ⟩ := hmeet m
    obtain ⟨hcard, -, -⟩ := Γ.border_cell _ (hcell m) ⟨y, hy, hbd hyΘ⟩
    have hsub : ({P (T m), P (T (m + 1))} : Set S) ⊆ tilde (cell m) := by
      rw [← Γ.closure_inter _ (hcell m)]
      rintro z (rfl | rfl)
      · exact ⟨(hcl m).1, (hposN m).1⟩
      · exact ⟨(hcl m).2, (hposN _).1⟩
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Γ.cell_size _ (hcell m)).1).symm
    rw [Set.ncard_pair (hpos_ne m (m + 1) (by omega) (by omega)), hcard]
  have hcell_ne : ∀ m m', m < m' → m' < m + k → cell m ≠ cell m' := by
    intro m m' h₁ h₂ heq
    have ht : ({P (T m), P (T (m + 1))} : Set S) = {P (T m'), P (T (m' + 1))} := by
      rw [← htilde, ← htilde, heq]
    have h₃ : P (T m) ∈ ({P (T m'), P (T (m' + 1))} : Set S) := ht ▸ Or.inl rfl
    have h₄ : P (T (m + 1)) ∈ ({P (T m'), P (T (m' + 1))} : Set S) := ht ▸ Or.inr rfl
    have h₅ : m' + 1 = m + k := by
      rcases h₃ with h₃ | h₃
      · exact absurd h₃ (hpos_ne _ _ h₁ h₂)
      · by_contra hc
        exact hpos_ne _ _ (by omega) (by omega) h₃
    have h₆ : m' = m + 1 := by
      rcases h₄ with h₄ | h₄
      · by_contra hc
        exact hpos_ne _ _ (by omega) (by omega) h₄
      · have h₇ : P (T (m + 1)) = P (T m) := by
          have h₈ : P (T (m' + 1)) = P (T m) := by
            rw [h₅, hadd]
            exact cuffPoint_add f _
          exact (show P (T (m + 1)) = P (T (m' + 1)) from h₄).trans h₈
        exact absurd h₇.symm (hpos_ne _ _ (by omega) (by omega))
    subst h₆
    have hk2 : k = 2 := by omega
    subst hk2
    refine not_cuff_subset_closure Γ (hcell m) hΘ (hmeet m) f fun y hy ↦ ?_
    obtain ⟨t, ht₀, rfl⟩ := exists_cuffPoint_eq f (T m) hy
    have ht₁ : t < T (m + 2) := by
      rw [hadd]
      exact ht₀.2
    obtain ⟨j, h₇, h₈, h₉, h₁₀⟩ := exists_mem_Ioo_of_seq (by omega) ht₀.1 ht₁
    have hj : j = m ∨ j = m + 1 := by omega
    have hcj : cell j = cell m := by
      rcases hj with rfl | rfl
      · rfl
      · exact heq.symm
    rcases h₉.eq_or_lt with h₁₁ | h₁₁
    · rw [← h₁₁]
      rcases hj with rfl | rfl
      · exact (hcl _).1
      · exact (hcl _).2
    · exact subset_closure (hcj ▸ hAsub j ⟨t, ⟨h₁₁, h₁₀⟩, rfl⟩)
  have hfind : ∀ a b, a < b → ∀ t, T a ≤ t → t < T b → P t ∉ Γ.N →
      ∃ j, a ≤ j ∧ j < b ∧ P t ∈ cell j ∧ t ∈ Ioo (T j) (T (j + 1)) := by
    intro a b hab t h₁ h₂ hN
    obtain ⟨j, h₃, h₄, h₅, h₆⟩ := exists_mem_Ioo_of_seq hab.le h₁ h₂
    have h₇ : T j < t := by
      refine lt_of_le_of_ne h₅ fun heq ↦ hN ?_
      rw [← heq]
      exact (hposN j).1
    exact ⟨j, h₃, h₄, hAsub j ⟨t, ⟨h₇, h₆⟩, rfl⟩, h₇, h₆⟩
  refine ⟨⟨k, htwo, T, hT, hadd, cell, fun m ↦ ?_, fun m ↦ (hposN m).1, fun n hn ↦ ?_, hcell,
    fun m ↦ ?_, htilde, hcell_ne, fun c hc hcΘ ↦ ?_⟩⟩
  · have h₁ : T (m + k + 1) = T (m + 1) + 2 * Real.pi := by
      rw [show m + k + 1 = m + 1 + k by omega, hadd]
    have h₂ : mid (m + k) = mid m + 2 * Real.pi := by
      simp only [mid]
      rw [h₁, hadd]
      ring
    change pathComponentIn _ (P (mid (m + k))) = pathComponentIn _ (P (mid m))
    rw [h₂]
    exact congrArg _ (cuffPoint_add f _)
  · obtain ⟨m, hm, hTm⟩ := hsurj _ (hmems hn)
    exact ⟨m, hm, by rw [hTm]; exact hgf n hn⟩
  · refine subset_antisymm ?_ fun y hy ↦ ?_
    · rintro y ⟨hy, hyΘ⟩
      have hyN : y ∉ Γ.N := (pathComponentIn_subset hy).2
      obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_eq f (T m) hyΘ
      have ht₂ : t < T (m + k) := by
        rw [hadd]
        exact ht.2
      obtain ⟨j, h₁, h₂, h₃, h₄⟩ := hfind m (m + k) (by omega) t ht.1 ht₂ hyN
      have heq : cell m = cell j := arcComponent_eq (hcell m) (hcell j) hy h₃
      have hjm : j = m := by
        by_contra hc
        exact hcell_ne m j (by omega) h₂ heq
      subst hjm
      exact ⟨t, h₄, rfl⟩
    · exact ⟨hAsub m hy, by obtain ⟨t, -, rfl⟩ := hy; exact cuffPoint_mem f t⟩
  · obtain ⟨y, hy, hyΘ⟩ := hcΘ
    have hyN : y ∉ Γ.N := (hc.2.1 hy).2
    obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_eq f (T 0) hyΘ
    have ht₂ : t < T (0 + k) := by
      rw [hadd]
      exact ht.2
    obtain ⟨j, h₁, h₂, h₃, h₄⟩ := hfind 0 (0 + k) (by omega) t ht.1 ht₂ hyN
    exact ⟨j, by omega, arcComponent_eq (hcell j) hc h₃ hy⟩

end GraphMinor.GM20

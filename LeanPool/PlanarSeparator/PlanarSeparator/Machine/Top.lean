/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Bridge

/-!
# The separator program on a plane rotation system

`sepProg_sepOut`: for every connected plane rotation system `R` of a graph with vertex weights
`w`, encoded as in `PlanarSeparator/Machine/Front.lean` with a numbering of the vertices and of
the darts (`Enc`), the compiled separator program halts within `320 m + 191 n + 403` steps and
prints one number per vertex: `0` for the vertices of a separator `S` of at most `6 √n + 3`
vertices, `1` and `2` for two parts with no edge between them, each of weight at most `2/3` of the
total (`SepOut`).
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open Finset

/-! ### Numeric lemmas -/

theorem labN_four (l₁ j j' fl Lv sv iv : ℕ) (hsv : sv ≤ 1) :
    labN l₁ j j' fl Lv sv iv = 4 ↔
      (Lv + j = l₁ ∨ Lv = l₁ + 1 + j' ∨ (l₁ < Lv + j ∧ Lv < l₁ + 1 + j' ∧ sv = 1)) := by
  unfold labN
  split_ifs <;> constructor <;> intro h <;> rcases h with h | h | ⟨h1, h2, h3⟩ <;> omega

theorem labN_piece (l₁ j j' fl Lv sv iv : ℕ) (h : labN l₁ j j' fl Lv sv iv ≠ 4) :
    labN l₁ j j' fl Lv sv iv =
      if Lv + j < l₁ then 0 else if l₁ + 1 + j' < Lv then 1 else if iv ≠ fl then 2 else 3 := by
  unfold labN at h ⊢; split_ifs at h ⊢ <;> omega

theorem labN_le (l₁ j j' fl Lv sv iv : ℕ) : labN l₁ j j' fl Lv sv iv ≤ 4 := by
  unfold labN; split_ifs <;> omega

theorem ite_or_eq_one {p q r : Prop} [Decidable (p ∨ q ∨ r)] :
    (if p ∨ q ∨ r then 1 else 0) = 1 ↔ (p ∨ q) ∨ r := by
  rw [or_assoc]; split_ifs with h <;> simp [h]

theorem gacc_congr (Wt : ℕ) {p p' : ℕ → ℕ} {i : ℕ} (h : ∀ t < i, p t = p' t) :
    gacc Wt p i = gacc Wt p' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [gacc, gacc, ih fun t ht => h t (by omega), h i (by omega)]

theorem gpart_congr (Wt : ℕ) {p p' : ℕ → ℕ} {i : ℕ} (h : ∀ t ≤ i, p t = p' t) :
    gpart Wt p i = gpart Wt p' i := by
  unfold gpart; rw [gacc_congr Wt fun t ht => h t (by omega), h i le_rfl]

section Reindex

variable {V : Type*} [Fintype V] {n : ℕ} (vi : V ≃ Fin n)

theorem sum_vi (f : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ∑ v ∈ univ.filter (fun v => p (vi v)), f (vi v) = ∑ u ∈ (range n).filter p, f u := by
  rw [sum_filter, sum_filter,
    Fintype.sum_equiv vi _ (fun i : Fin n => if p i then f i else 0) (fun _ => rfl)]
  exact Fin.sum_univ_eq_sum_range (fun u => if p u then f u else 0) n

theorem card_vi (p : ℕ → Prop) [DecidablePred p] :
    #(univ.filter (fun v => p (vi v))) = #((range n).filter p) := by
  have := sum_vi vi (fun _ => 1) p
  simpa using this

theorem sum_vi_univ (f : ℕ → ℕ) : ∑ v, f (vi v) = ∑ u ∈ range n, f u := by
  have := sum_vi vi f (fun _ => True)
  simpa using this

end Reindex

/-! ### The output -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The output is a separation**: for the numbering `vi` of the vertices, the vertices printed
`0` form a separator of at most `6 √n + 3` vertices between those printed `1` and those printed
`2`, each of weight at most `2/3` of the total. -/
def SepOut (G : SimpleGraph V) (w : V → ℕ) {n : ℕ} (vi : V ≃ Fin n) (out : List ℕ) : Prop :=
  IsSeparation G univ {v | out.getD (vi v) 0 = 0} {v | out.getD (vi v) 0 = 1}
      {v | out.getD (vi v) 0 = 2} ∧
    (#{v | out.getD (vi v) 0 = 0} : ℝ) ≤ 6 * √(n : ℝ) + 3 ∧
    3 * ∑ v with out.getD (vi v) 0 = 1, w v ≤ 2 * ∑ v, w v ∧
    3 * ∑ v with out.getD (vi v) 0 = 2, w v ≤ 2 * ∑ v, w v

theorem gpart_ne_zero (Wt : ℕ) (p : ℕ → ℕ) (i : ℕ) : gpart Wt p i ≠ 0 := by
  rcases gpart_eq Wt p i with h | h <;> omega

omit [DecidableRel G.Adj] in
/-- **From the labels to the output.** If the label `4` marks a set `Sx`, the other labels are
the pieces `pc`, and the pieces weigh `pwf`, the output of the labels is the separation of
`levelSep`. -/
theorem sepOut_of {n : ℕ} (vi : V ≃ Fin n) (w : V → ℕ) (wN : ℕ → ℕ) (hw : ∀ v, wN (vi v) = w v)
    (lab : ℕ → ℕ) (Sx : V → Prop) [DecidablePred Sx] (pc : V → ℕ) (pwf : ℕ → ℕ)
    (hS4 : ∀ v, lab (vi v) = 4 ↔ Sx v) (hlab4 : ∀ v, lab (vi v) ≤ 4)
    (hpc : ∀ v, ¬ Sx v → lab (vi v) = pc v)
    (hpw : ∀ i < 4, pwf i = ∑ u ∈ range n with lab u = i, wN u)
    (hsep : IsSeparation G univ {v | Sx v} {v | ¬ Sx v ∧ gpart (∑ v, w v) pwf (pc v) = 1}
      {v | ¬ Sx v ∧ gpart (∑ v, w v) pwf (pc v) = 2})
    (hA : 3 * ∑ v with ¬ Sx v ∧ gpart (∑ v, w v) pwf (pc v) = 1, w v ≤ 2 * ∑ v, w v)
    (hB : 3 * ∑ v with ¬ Sx v ∧ gpart (∑ v, w v) pwf (pc v) = 2, w v ≤ 2 * ∑ v, w v)
    (hcard : (#{v | Sx v} : ℝ) ≤ 6 * √(n : ℝ) + 3) :
    SepOut G w vi (outList n (∑ u ∈ range n, wN u) wN lab) := by
  have hWt : ∑ u ∈ range n, wN u = ∑ v, w v := by
    rw [← sum_vi_univ vi]; exact sum_congr rfl fun v _ => hw v
  have key : ∀ v, (outList n (∑ u ∈ range n, wN u) wN lab).getD (vi v) 0 =
      if Sx v then 0 else gpart (∑ v, w v) pwf (pc v) := by
    intro v
    unfold outList
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (vi v).2]
    simp only [Option.map_some, Option.getD_some]
    by_cases hs : Sx v
    · rw [ite_eq_left hs, ite_eq_right (by rw [(hS4 v).2 hs]; omega)]
    · have h4 : lab (vi v) ≠ 4 := fun h => hs ((hS4 v).1 h)
      have hl := hlab4 v
      rw [ite_eq_right hs, ite_eq_left (by omega), hWt, hpc v hs]
      refine gpart_congr _ fun t ht => (hpw t (by have := hpc v hs; omega)).symm
  have h0 : ∀ v, (if Sx v then 0 else gpart (∑ v, w v) pwf (pc v)) = 0 ↔ Sx v := fun v => by
    by_cases h : Sx v <;> simp [h, gpart_ne_zero]
  have h1 : ∀ v i, i ≠ 0 → ((if Sx v then 0 else gpart (∑ v, w v) pwf (pc v)) = i ↔
      ¬ Sx v ∧ gpart (∑ v, w v) pwf (pc v) = i) := fun v i hi => by
    by_cases h : Sx v <;> simp [h, Ne.symm hi]
  unfold SepOut
  simp only [key, h0, fun v => h1 v 1 one_ne_zero, fun v => h1 v 2 two_ne_zero]
  exact ⟨hsep, hcard, hA, hB⟩

open WordRAM WordRAM.Machine StDart in
/-- **The back half on a plane rotation system.** From every state after the front half, the
back half prints a separation. -/
theorem back_sepOut {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) (w : V → ℕ) {n m : ℕ}
    {vi : V ≃ Fin n} {di : G.Dart ≃ Fin m} {ofs wN tl rv ro : ℕ → ℕ}
    (hE : Enc R w n m vi di ofs wN tl rv ro) {P : Input} (hIn : InHolds P n m ofs wN tl rv ro)
    {W : ℕ} (hW : memTop n m + 3 * ∑ v ∈ range n, wN v + 2 * n + 3 * m + 10 ≤ W)
    (hm1 : 1 ≤ m) {L pr : ℕ → ℕ} {l₁ j j' : ℕ} {c : Config}
    (hF : FrontOut n m ofs wN tl rv ro W L pr l₁ j j' c) :
    ∃ c' k, Exec P W back c c' k ∧ k ≤ 224 * m + 90 * n + 300 ∧ SepOut G w vi c'.output := by
  classical
  have hN := hE.nwf
  have hn2 := two_le_of vi di hm1
  have hn : 0 < n := by omega
  have hofs := hE.ofs_lt hR.connected hm1
  have hm2 : 2 ≤ m := by
    obtain ⟨d, -⟩ := Enc.exists_dart (di := di) hm1
    have h1 : di d ≠ di d.symm := fun e => d.symm_ne (di.injective e).symm
    have := (di d).2; have := (di d.symm).2
    have : (di d : ℕ) ≠ di d.symm := fun e => h1 (Fin.ext e)
    omega
  have hpar := hF.par
  have hC := coded hE hpar hn c.nmem hF.dfacts hF.tm1 hF.tm0
  have hM : (Map.ofRotation R).stellar.IsPlane := Map.isPlane_stellar (Map.isPlane_ofRotation hR)
  have hT3 : ∀ δ, (Map.ofRotation R).stellar.IsTriangle δ :=
    Map.isTriangle_stellar _ (Map.ofRotation_vert_α_ne R)
  set L' : V → ℕ := fun v => L (vi v)
  set fw := Map.SpTree.fwt (Map.ofRotation R).stellar (firstF vi di rv ro hE hofs)
    (wMid L' l₁ j j' w)
  have hFw' := hFw hE hpar hn hofs l₁ j j' c.nmem hC hF.fw1 hF.fw0
  have hwsum : ∑ v, w v = ∑ u ∈ range n, wN u := by
    rw [← sum_vi_univ vi]; exact sum_congr rfl fun v _ => (hE.w_eq v).symm
  have hfwW : 11 * m + 3 * ∑ G, fw G + 4 ≤ W := by
    have h1 : ∑ G, fw G = ∑ x, wMid (R := R) L' l₁ j j' w x := Map.SpTree.sum_fwt_univ _ _
    have h2 := sum_wMid_le (R := R) (L := L') (l₁ := l₁) (j := j) (j' := j') w
    unfold memTop at hW
    omega
  have hjn : j ≤ n := hF.j_le.trans (Nat.sqrt_le_self n)
  have hj'n : j' ≤ n := hF.j'_le.trans (Nat.sqrt_le_self n)
  obtain ⟨c', k, e, hk, mode, δn, an, c₁, im, hout, hS, hall, him0, himr, hoeq⟩ :=
    back_exec hN hIn hW hm2 L pr (fun q => frepF (ph rv ro) q + 1) l₁ j j' c hF.wb hF.lay
      hF.cregs hC hM hT3 fw hFw' hfwW
      (fun q hq => ⟨by omega, by have := frepF_le (f := ph rv ro) q; omega⟩) hF.frm hpar hF.L0
      hF.prm hF.Lm hF.Ln hF.r122 hF.r123 hF.r125 hF.r126 hF.l₁_le hjn hj'n hF.z7 hF.z12 hF.zs
      hF.zp
  refine ⟨c', k, e, hk, ?_⟩
  rw [hoeq, hF.out, List.nil_append]
  -- the balanced cycle
  obtain ⟨a, X, hcd, hX3, hXc, hin, hout'⟩ :=
    CycleOut.balance hM hT3 (vert_firstF hE hofs) (wMid L' l₁ j j' w) hout
  -- the separator marks
  generalize hsmdef : smN tl rv (fun q => frepF (ph rv ro) q + 1) pr L mode δn an (c.nmem an) = sm
  have hsm1 : ∀ u, sm u ≤ 1 := fun u => by rw [← hsmdef]; unfold smN; split_ifs <;> omega
  have hAa : c.nmem an = (cdE (R := R) di ((Map.ofRotation R).stellar.α a) : ℕ) := by
    rw [← hcd]; exact hC.A_cd a
  have hsm : ∀ v, sm (vi v) = 1 ↔ (.inl v : V ⊕ _) ∈ (liftT vi di hE hpar hn).sep a ∪ X := by
    intro v
    rw [← hsmdef, mem_union, Map.SpTree.sep, mem_union, mem_anc_vert hE hpar hn hF.L0,
      mem_anc_vert hE hpar hn hF.L0, hcd, ← hAa]
    have hX : (.inl v : V ⊕ _) ∈ X ↔ (0 < mode ∧ ((vi v : ℕ) = tl (δn / 3) ∨
        (vi v : ℕ) = tl (rv (δn / 3)))) := by
      rcases hXc with ⟨h0, rfl⟩ | ⟨h1, δ, hδ, rfl⟩
      · simp [h0]
      · rw [mem_corners hE, hδ]; simp [h1]
    rw [hX]
    exact ite_or_eq_one
  -- the sides
  have hfi (v : V) : CycleSearch.fi (cdE (R := R) di)
      ((Map.ofRotation R).stellar.face (firstF vi di rv ro hE hofs (.inl v))) = ofs (vi v) := by
    rw [hC.fi_face]; simp [firstF]
  let ins : V → Bool := fun v => decide (im (ofs (vi v)) ≠
    (if c.nmem (3 * m + an) ≠ 0 then 0 else if IsPd c₁.nmem m an then 0 else 1))
  have hins : ∀ v, (.inl v : V ⊕ _) ∉ (liftT vi di hE hpar hn).sep a →
      (ins v = true ↔ (.inl v : V ⊕ _) ∈ (liftT vi di hE hpar hn).inV a) := by
    intro v hv
    rw [Map.SpTree.mem_inV_iff hM hv (vert_firstF hE hofs (.inl v))]
    have := inside_marks hC hM (by omega) hS hall im a him0
      (fun G hG h0 => by simp only [hcd]; exact himr G hG h0)
      ((Map.ofRotation R).stellar.face (firstF vi di rv ro hE hofs (.inl v)))
    simp only [hcd, hfi] at this
    simp only [ins, decide_eq_true_iff]
    exact this
  -- the separation of Lipton and Tarjan
  have hroot : ∀ v, v ≠ (gtree vi di hE hpar hn).root → (vi v : ℕ) ≠ 0 := fun v hv h0 =>
    hv (by change v = vi.symm ⟨0, hn⟩; rw [Equiv.eq_symm_apply]; exact Fin.ext h0)
  have hparL : ∀ v, v ≠ (gtree vi di hE hpar hn).root →
      L' ((gtree vi di hE hpar hn).parent v) + 1 = L' v := by
    intro v hv
    have h0 := hroot v hv
    simp only [L']
    rw [gtree_parent hE hpar hn h0]
    have := vi_pdart_snd hE hpar v h0
    rw [this]; exact (hpar _ (vi v).2 h0).2.2
  have hadjL : ∀ u v, G.Adj u v → L' v ≤ L' u + 1 := by
    intro u v huv
    have := hF.adj (di ⟨(u, v), huv⟩) (di _).2
    rw [hE.rv_eq, hE.tl_eq, hE.tl_eq] at this
    exact this
  have hlow : 2 * ∑ v with L' v < l₁, w v ≤ ∑ v, w v := by
    have := sum_vi vi wN (fun u => L u < l₁)
    simp only [hE.w_eq] at this
    have e : ∑ v with L' v < l₁, w v = ∑ u ∈ range n with L u < l₁, wN u := this
    rw [hwsum, e]; exact hF.low
  have hhigh : 2 * ∑ v with l₁ < L' v, w v ≤ ∑ v, w v := by
    have := sum_vi vi wN (fun u => l₁ < L u)
    simp only [hE.w_eq] at this
    have e : ∑ v with l₁ < L' v, w v = ∑ u ∈ range n with l₁ < L u, wN u := this
    rw [hwsum, e]; exact hF.high
  obtain ⟨hsep, hA, hB, hcard⟩ := levelSep hR (gtree vi di hE hpar hn) hparL hadjL
    (repF di rv ro) (face_repF hE) w hlow hhigh a X hX3 hin hout' ins hins
  have hS4 : ∀ v, labN l₁ j j' (if c.nmem (3 * m + an) ≠ 0 then 0
      else if IsPd c₁.nmem m an then 0 else 1) (L (vi v)) (sm (vi v)) (im (ofs (vi v))) = 4 ↔
      InS L' l₁ j j' (liftT vi di hE hpar hn) a X v := by
    intro v
    rw [labN_four _ _ _ _ _ _ _ (hsm1 _), hsm v]
    simp only [InS, MidL, and_assoc, L']
  have hpc : ∀ v, ¬ InS L' l₁ j j' (liftT vi di hE hpar hn) a X v →
      labN l₁ j j' (if c.nmem (3 * m + an) ≠ 0 then 0
        else if IsPd c₁.nmem m an then 0 else 1) (L (vi v)) (sm (vi v)) (im (ofs (vi v))) =
      piece L' l₁ j j' ins v := by
    intro v hv
    rw [labN_piece _ _ _ _ _ _ _ (fun h => hv ((hS4 v).1 h))]
    simp only [piece, ins, decide_eq_true_eq, L']
  have hpc4 : ∀ v, piece L' l₁ j j' ins v < 4 := fun v => by
    simp only [piece]; split_ifs <;> omega
  refine sepOut_of vi w wN hE.w_eq _ (InS L' l₁ j j' (liftT vi di hE hpar hn) a X)
    (piece L' l₁ j j' ins) (pw L' l₁ j j' (liftT vi di hE hpar hn) a X ins w) hS4
    (fun v => labN_le _ _ _ _ _ _ _) hpc ?_ hsep hA hB ?_
  · intro i hi
    unfold pw
    rw [← sum_vi vi wN (fun u => _ = i)]
    refine sum_congr ?_ fun v _ => (hE.w_eq v).symm
    ext v
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hpc v h1, h2]
    · intro h
      have h1 : ¬ InS L' l₁ j j' (liftT vi di hE hpar hn) a X v := fun hs => by
        rw [(hS4 v).2 hs] at h; omega
      exact ⟨h1, by rw [← hpc v h1, h]⟩
  · have hK : #{v | L' v + j = l₁} = #((range n).filter fun u => L u + j = l₁) :=
      card_vi vi (fun u => L u + j = l₁)
    have hK' : #{v | L' v = l₁ + 1 + j'} = #((range n).filter fun u => L u = l₁ + 1 + j') :=
      card_vi vi (fun u => L u = l₁ + 1 + j')
    rw [hK, hK'] at hcard
    exact card_bound_real hF.thinK hF.thinK' hF.j_le hF.j'_le hcard

theorem runsWithin_mono {prog : WordRAM.Program} {P : WordRAM.Input} {W k k' : ℕ} {out : List ℕ}
    (h : WordRAM.RunsWithin prog P W k out) (hk : k ≤ k') : WordRAM.RunsWithin prog P W k' out := by
  obtain ⟨i, hi, rest⟩ := h
  exact ⟨i, by omega, rest⟩

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt in
/-- **The separator program on a plane rotation system.** For every plane rotation system `R` of
a graph with `n` vertices and `m` darts and vertex weights `w`, encoded with numberings `vi`, `di`
of its vertices and darts (`Enc`, `InHolds`), and every word size `W` bounding the input words
with `W ≥ 16 m + 12 n + 3 Σ w + 22`, the compiled separator program halts within
`320 m + 191 n + 403` steps and prints a separation (`SepOut`): the vertices printed `0` form a
separator of at most `6 √n + 3` vertices between the vertices printed `1` and those printed `2`,
each part of weight at most `2/3` of the total. -/
theorem sepProg_sepOut {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) (w : V → ℕ) {n m : ℕ}
    {vi : V ≃ Fin n} {di : G.Dart ≃ Fin m} {ofs wN tl rv ro : ℕ → ℕ}
    (hE : Enc R w n m vi di ofs wN tl rv ro) {P : Input} (hIn : InHolds P n m ofs wN tl rv ro)
    {W : ℕ} (hW : memTop n m + 3 * ∑ v ∈ range n, wN v + 2 * n + 3 * m + 10 ≤ W)
    (hPW : ∀ j, P.data.getD j 0 ≤ W) :
    ∃ out, RunsWithin (compile sepProg 0 ++ [Instr.halt]) P W (320 * m + 191 * n + 403) out ∧
      SepOut G w vi out := by
  classical
  have hN := hE.nwf
  have hn : 0 < n := by
    obtain ⟨v⟩ := hR.connected.nonempty
    exact lt_of_le_of_lt (Nat.zero_le _) (vi v).2
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- no darts: a single vertex, printed `0`
    have hn1 : n = 1 := by
      by_contra hne
      have h1 : 1 < n := by omega
      have hne' : vi.symm ⟨0, hn⟩ ≠ vi.symm ⟨1, h1⟩ := fun e => by
        have := congrArg (fun x => (vi x : ℕ)) e; simp at this
      have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
        (hR.connected.preconnected (vi.symm ⟨0, hn⟩) (vi.symm ⟨1, h1⟩))
      rcases hr.cases_head with h | ⟨z, hz, -⟩
      · exact hne' h
      · exact absurd (di ⟨(_, z), hz⟩).2 (by omega)
    subst hn1
    refine ⟨[0], runsWithin_mono (sepProg_zero hIn hW hm) (by omega), ?_⟩
    have hv : ∀ v : V, (vi v : ℕ) = 0 := fun v => by have := (vi v).2; omega
    have hc : Fintype.card V = 1 := by rw [Fintype.card_congr vi, Fintype.card_fin]
    unfold SepOut
    simp only [hv, List.getD_cons_zero]
    refine ⟨⟨by simp, by simp, by simp, by simp, by simp⟩, ?_, by simp, by simp⟩
    norm_num [hc]
  · obtain ⟨out, h1, h2⟩ := sepProg_run hN hIn hW hPW hn hm (hE.nconn hR.connected hn)
      (hE.ofs_lt hR.connected hm) (SepOut G w vi)
      (fun L pr l₁ j j' c hF => back_sepOut hR w hE hIn hW hm hF)
    exact ⟨out, h1, h2⟩

end SepProg

end PlanarSeparator

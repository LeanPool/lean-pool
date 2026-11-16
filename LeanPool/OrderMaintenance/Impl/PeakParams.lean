/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakMW


/-!
# Theorem W, option (A), stage A3: the peak of a new core's construction

* `paramsS_pk`: the parameter computation (`Params.lean`), part by part along the exec facts
  `partA_ok`, `partB_ok`, `partC_ok`. Each expression's peak comes from `Expr.wdM_sound` with every
  local at width `K/2` (`ΓP`) and shift amounts at most `K` (`2^UG`, `2^HC`; `UG ≤ 4L`,
  `HC ≤ 30L + 64`); the widths are computed from the syntax and are at most `2K + 4` when
  `64·L ≤ K`.
* `allocSlot_pk`: the allocations of a slot, whose capacities are below `2^K` (`CapsW`).
* `newCore_pk`, `eagerCore_pk`: a new core (lazy, as in a rebuild start; eager, as in the
  initialization), the call of `initCore` through `wpB_coreCall` and `initCore_peak`.

All within the budget `BW K KH = 2^(2K+4) + 2^KH`, for `K ≥ wK (proofParams N)`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

variable {K KH : Nat}

/-! ### Generic straight-line code -/

theorem wpB_seqAll {B : Nat} (P : State → Prop) :
    ∀ (cs : List Stmt) (s : State), P s → (∀ c ∈ cs, ∀ s, P s → wpB B c (fun s' _ => P s') s) →
      wpB B (seqAll cs) TT s
  | [], _, _, _ => wpB_skip_T
  | c :: cs, s, hP, h => wpB_seq_T (h c (by simp) s hP)
      (fun s' _ hP' => wpB_seqAll P cs s' hP' (fun c' hc' => h c' (by simp [hc'])))

theorem wpB_storeAll {B : Nat} (a : Arr) (lc : Reg → Nat) (ca : Nat) :
    ∀ (l : List (Nat × Expr)) (s : State), s.loc = lc → s.cap a = ca →
      (∀ ie ∈ l, ∀ s : State, s.loc = lc → (∃ v, ie.2.eval s = some v) ∧ ie.1 < ca ∧ ie.1 ≤ B ∧
        ie.2.maxv s ≤ B) →
      wpB B (Machine.storeAll a l) TT s
  | [], _, _, _, _ => wpB_skip_T
  | (i, e) :: l, s, hl, hc, h => by
    obtain ⟨⟨v, hv⟩, hi, hiB, heB⟩ := h (i, e) (by simp) s hl
    exact wpB_store_seq i v rfl hv (by
      rw [hc]
      exact hi) (by simpa using hiB) heB
      (fun s' hl' _ hc' => wpB_storeAll a lc ca l s' (hl'.trans hl) (by
        rw [hc']
        exact hc)
        (fun ie hie => h ie (by simp [hie])))

theorem wpB_allocAll {B : Nat} (lc : Reg → Nat) :
    ∀ (l : List (Arr × Expr)) (s : State), s.loc = lc →
      (∀ ae ∈ l, ∀ s : State, s.loc = lc → (ae.2.eval s).isSome ∧ ae.2.maxv s ≤ B) →
      wpB B (Machine.allocAll l) TT s
  | [], _, _, _ => wpB_skip_T
  | (a, e) :: l, s, hl, h => by
    obtain ⟨he, heB⟩ := h (a, e) (by simp) s hl
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp he
    exact wpB_seq_T (Machine.wpB_alloc_g (Q := fun s' _ => s'.loc = lc) k hk heB (fun s' a _ _
      => a.trans hl))
      (fun s' _ hl' => wpB_allocAll lc l s' hl' (fun ae hae => h ae (by simp [hae])))

/-! ### Widths of the parameter expressions -/

/-- Every local at width `K/2`. -/
def ΓP (K : Nat) : Reg → Nat := fun _ => K / 2

theorem maxv_BW {s : State} {e : Expr} {v : Nat} (hl : e.LeafB s (ΓP K) (fun _ => 0) K)
    (he : e.eval s = some v) (hw : e.wpM (ΓP K) (fun _ => 0) K ≤ 2 * K + 4) : e.maxv s ≤ BW K KH
      := by
  have h1 := (Expr.wdM_sound e hl he).2
  have h2 : 2 ^ e.wpM (ΓP K) (fun _ => 0) K ≤ 2 ^ (2 * K + 4) := Nat.pow_le_pow_right (by
    norm_num) hw
  exact le_trans (le_of_lt (lt_of_lt_of_le h1 h2)) (Nat.le_add_right _ _)

theorem small_half {x : Nat} (h : 64 * x ≤ K) : x < 2 ^ (K / 2) :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem N_half {N : Nat} (h : 64 * pL N ≤ K) : N < 2 ^ (K / 2) :=
  lt_of_lt_of_le (OrderMaintenance.Proof.Word.N_lt N) (Nat.pow_le_pow_right (by norm_num) (by
    omega))

/-- The expression reads only the locals `xs`, no array, and shifts nothing. -/
def _root_.OrderMaintenance.Machine.Expr.rdOK (xs : List Reg) : Expr → Bool
  | .lit _ => true
  | .var x => decide (x ∈ xs)
  | .load _ _ => false
  | .bin op a b => (op != .shl) && a.rdOK xs && b.rdOK xs
  | .un _ a => a.rdOK xs

theorem leafB_of_rdOK {s : State} {Γ : Reg → Nat} {A : Arr → Nat} {S : Nat} {xs : List Reg}
    (hx : ∀ x ∈ xs, s.loc x < 2 ^ Γ x) : ∀ e : Expr, e.rdOK xs = true → e.LeafB s Γ A S
  | .lit _, _ => trivial
  | .var x, h => hx x (by simpa [Expr.rdOK] using h)
  | .load _ _, h => by simp [Expr.rdOK] at h
  | .bin op a b, h => by
    simp only [Expr.rdOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨leafB_of_rdOK hx a h.1.2, leafB_of_rdOK hx b h.2, fun e => absurd e h.1.1⟩
  | .un _ a, h => leafB_of_rdOK hx a (by simpa [Expr.rdOK] using h)

theorem maxv_BW' {s : State} {e : Expr} (hl : e.LeafB s (ΓP K) (fun _ => 0) K)
    (he : ∃ v, e.eval s = some v) (hw : e.wpM (ΓP K) (fun _ => 0) K ≤ 2 * K + 4) : e.maxv s ≤ BW
      K KH := by
  obtain ⟨v, hv⟩ := he; exact maxv_BW hl hv hw

/-! ### Linear widths, computed from the syntax

With every local at width `X = K/2` and shift amounts at most `K ≤ 2X + 1`, the widths of an
expression without loads are at most `a·X + b` for a pair `(a, b)` computed from the syntax alone
(`Expr.wl`, `Expr.wlp`), so a concrete expression's pair is a closed computation (`decide`). -/

/-- The pointwise maximum of two pairs. -/
def mxP (p q : Nat × Nat) : Nat × Nat := (max p.1 q.1, max p.2 q.2)

/-- The linear width of an expression's value. -/
def _root_.OrderMaintenance.Machine.Expr.wl : Expr → Nat × Nat
  | .lit n => (0, n)
  | .var _ => (1, 0)
  | .load _ _ => (0, 0)
  | .bin op a b =>
    match op with
    | .add => (max a.wl.1 b.wl.1, max a.wl.2 b.wl.2 + 1)
    | .sub | .div | .mod | .shr => a.wl
    | .mul => (a.wl.1 + b.wl.1, a.wl.2 + b.wl.2)
    | .shl => (a.wl.1 + 2, a.wl.2 + 1)
    | .lt | .le | .eq | .and | .or => (0, 1)
  | .un op a =>
    match op with
    | .not => (0, 1)
    | .msb => a.wl

/-- The linear width of an expression's peak. -/
def _root_.OrderMaintenance.Machine.Expr.wlp : Expr → Nat × Nat
  | .lit n => (0, n)
  | .var _ => (1, 0)
  | .load _ i => i.wlp
  | e@(.bin _ a b) => mxP (mxP a.wlp b.wlp) e.wl
  | e@(.un _ a) => mxP a.wlp e.wl

theorem le_mxP_l {x X : Nat} {p : Nat × Nat} (q : Nat × Nat) (h : x ≤ p.1 * X + p.2) :
    x ≤ (mxP p q).1 * X + (mxP p q).2 := by
  have : p.1 * X ≤ max p.1 q.1 * X := Nat.mul_le_mul_right _ (le_max_left _ _)
  simp only [mxP]; have := le_max_left p.2 q.2; omega

theorem le_mxP_r {x X : Nat} (p : Nat × Nat) {q : Nat × Nat} (h : x ≤ q.1 * X + q.2) :
    x ≤ (mxP p q).1 * X + (mxP p q).2 := by
  have : q.1 * X ≤ max p.1 q.1 * X := Nat.mul_le_mul_right _ (le_max_right _ _)
  simp only [mxP]; have := le_max_right p.2 q.2; omega

theorem wvM_le_wl : ∀ e : Expr, e.wvM (ΓP K) (fun _ => 0) K ≤ e.wl.1 * (K / 2) + e.wl.2
  | .lit n => by simp [Expr.wvM, Expr.wl]
  | .var _ => by simp [Expr.wvM, Expr.wl, ΓP]
  | .load _ _ => by simp [Expr.wvM, Expr.wl]
  | .bin op a b => by
    have ha := wvM_le_wl a
    have hb := wvM_le_wl b
    cases op <;> simp only [Expr.wvM, Expr.wl] <;> try omega
    · have h1 : a.wl.1 * (K / 2) ≤ max a.wl.1 b.wl.1 * (K / 2) := Nat.mul_le_mul_right _
        (le_max_left _ _)
      have h2 : b.wl.1 * (K / 2) ≤ max a.wl.1 b.wl.1 * (K / 2) := Nat.mul_le_mul_right _
        (le_max_right _ _)
      omega
    · rw [Nat.add_mul]; omega
    · rw [Nat.add_mul]; omega
  | .un op a => by
    have ha := wvM_le_wl a
    cases op <;> simp only [Expr.wvM, Expr.wl] <;> omega

theorem wpM_le_wlp : ∀ e : Expr, e.wpM (ΓP K) (fun _ => 0) K ≤ e.wlp.1 * (K / 2) + e.wlp.2
  | .lit n => by simp [Expr.wpM, Expr.wlp]
  | .var _ => by simp [Expr.wpM, Expr.wlp, ΓP]
  | .load _ i => by simp only [Expr.wpM, Expr.wlp]; have := wpM_le_wlp i; omega
  | .bin op a b => by
    simp only [Expr.wpM, Expr.wlp]
    refine max_le (max_le ?_ ?_) (le_mxP_r _ (wvM_le_wl (.bin op a b)))
    · exact le_mxP_l _ (le_mxP_l _ (wpM_le_wlp a))
    · exact le_mxP_l _ (le_mxP_r _ (wpM_le_wlp b))
  | .un op a => by
    simp only [Expr.wpM, Expr.wlp]
    exact max_le (le_mxP_l _ (wpM_le_wlp a)) (le_mxP_r _ (wvM_le_wl (.un op a)))

/-- **A closed check of an expression's peak width.** -/
theorem wpM_le_of_wlp {e : Expr} (hK : 512 ≤ K) (h : e.wlp.1 ≤ 2 ∧ e.wlp.2 ≤ 500) :
    e.wpM (ΓP K) (fun _ => 0) K ≤ 2 * K + 4 := by
  have h1 := wpM_le_wlp (K := K) e
  have h2 : e.wlp.1 * (K / 2) ≤ 2 * (K / 2) := Nat.mul_le_mul_right _ h.1
  omega

theorem wpB_assign_some {B : Nat} {x : Reg} {e : Expr} {Q : State → Nat → Prop} {s : State}
    (he : ∃ v, e.eval s = some v) (hB : e.maxv s ≤ B)
    (h : ∀ v s', e.eval s = some v → s'.loc = State.upd s.loc x v → s'.mem = s.mem → s'.cap =
      s.cap →
      Q s' (1 + e.cost)) : wpB B (.assign x e) Q s := by
  obtain ⟨v, hv⟩ := he; exact Machine.wpB_assign_g v hv hB (fun s' a b c => h v s' hv a b c)

theorem vUG_eq (N : Nat) : vUG (pL N) = UG (proofParams N) := rfl
theorem vHC_eq (N : Nat) : vHC (pL N) = HC (proofParams N) := rfl

/-! ### The three parts -/

theorem log2_pL (N : Nat) : Nat.log2 N + 1 ≤ pL N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; have := pL_ge 0; simp; omega
  · rw [pL_eq h]; exact le_max_right _ _


section parts
variable {N : Nat} (hK : 64 * pL N ≤ K)
include hK

theorem partA_pk {m : State} (hN : m.loc "nN" = N) : wpB (BW K KH) partA TT m := by
  have h8 := pL_ge N
  have hNh := N_half hK
  have hlog : Nat.log2 N ≤ N := Nat.log2_le_self N
  unfold partA
  refine wpB_seq_T (Machine.wpB_assign_g (Q := fun s' _ => s'.loc "L" = Nat.log2 N + 1)
    (Nat.log2 N + 1)
    (by
      simp [eN, hN]) (maxv_BW (v := Nat.log2 N + 1) (by simp [Expr.LeafB, eN, ΓP, hN, hNh]) (by
        simp [eN, hN])
      (by
        simp [Expr.wpM, Expr.wvM, eN, ΓP]
        omega))
    (fun s' hl _ _ => by rw [hl]; simp)) (fun s1 _ hL1 => ?_)
  have hL1h : Nat.log2 N + 1 < 2 ^ (K / 2) := small_half (by
    have := log2_pL N
    omega)
  refine wpB_ite_T (if Nat.log2 N + 1 < 8 then 1 else 0) (by simp [eL, hL1]) (maxv_BW (v := if
    Nat.log2 N + 1 < 8 then 1 else 0)
    (by simp [Expr.LeafB, eL, ΓP, hL1, hL1h]) (by simp [eL, hL1])
    (by
      simp [Expr.wpM, Expr.wvM, eL, ΓP]
      omega)) (fun s2 _ _ _ => ?_)
  have h8 : (8 : Nat) < 2 ^ K := lt_of_lt_of_le (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (show 4 ≤ K by have := pL_ge N; omega))
  split
  · exact wpB_T (Machine.wpB_assign_g (Q := TT) 8 rfl (lt_K_BW (by simpa using h8)) (fun _ _ _ _
      => trivial))
  · exact wpB_skip_T

variable {L : Nat} (hLe : L = pL N)
include hLe

theorem locLN {s : State} (hL : s.loc "L" = L) (hN : s.loc "nN" = N) :
    ∀ x ∈ ["L", "nN"], s.loc x < 2 ^ ΓP K x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · rw [hL, hLe]; exact small_half hK
  · rw [hN]; exact N_half hK

theorem partC_pk {m : State} (hL : m.loc "L" = L) (hN : m.loc "nN" = N) : wpB (BW K KH) partC TT
  m := by
  have h8 : 8 ≤ L := by rw [hLe]; exact pL_ge N
  have hc : vcm L ≤ vth L + 1 := by rw [hLe]; exact vcm_le N
  refine wpB_seqAll (fun s => s.loc "L" = L ∧ s.loc "nN" = N) _ m ⟨hL, hN⟩ (fun c hc' s ⟨hL',
    hN'⟩ => ?_)
  have hx := locLN hK hLe hL' hN'
  have hKL : 64 * L ≤ K := by rw [hLe]; exact hK
  have h512 : 512 ≤ K := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  refine wpB_assign_some (by
    simp [eN, eH_ev hL', ecb_ev hL' hN' h8 hc, enb_ev hL' hN' h8 hc, hN'])
    (maxv_BW' (leafB_of_rdOK hx _ (by
      simp [Expr.rdOK, eN, eL, ecb, enb, eH, eth, ecm, eT, ekc, euT, egm, eG, ekg])) (by
        simp [eN, eH_ev hL', ecb_ev hL' hN' h8 hc, enb_ev hL' hN' h8 hc, hN'])
      (wpM_le_of_wlp (by omega) (by decide)))
    (fun _ s' _ hl _ _ => ⟨by rw [hl]; simp [State.upd, hL'], by rw [hl]; simp [State.upd, hN']⟩)

theorem partB_pk (q : Nat) {m : State} (hL : m.loc "L" = L) (hN : m.loc "nN" = N) :
    wpB (BW K KH) (partB q) TT m := by
  have h8 : 8 ≤ L := by rw [hLe]; exact pL_ge N
  have hKL : 64 * L ≤ K := by rw [hLe]; exact hK
  have h512 : 512 ≤ K := by omega
  have h16 : (16 : Nat) ≤ BW K KH := lt_K_BW (lt_of_lt_of_le (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (show 5 ≤ K by omega)))
  have hUG : vUG L ≤ K := by rw [hLe, vUG_eq]; have := UG_le N; omega
  have hHC : vHC L ≤ K := by rw [hLe, vHC_eq]; have := HC_le N; omega
  unfold partB
  refine wpB_seq_T (Machine.wpB_alloc_g (Q := fun s' _ => s'.loc = m.loc ∧ s'.cap (arr q .prm) =
    16) 16 rfl
    (by simpa using h16) (fun s' hl _ hc => ⟨hl, by rw [hc]; simp [State.alloc, State.upd]⟩))
    (fun s' _ ⟨hl, hc⟩ => wpB_storeAll _ m.loc 16 pList s' hl hc (fun ie hie s hs => ?_))
  have hL' : s.loc "L" = L := by rw [hs, hL]
  have hN' : s.loc "nN" = N := by rw [hs, hN]
  have hx := locLN hK hLe hL' hN'
  simp only [pList, List.mem_cons, List.not_mem_nil, or_false] at hie
  rcases hie with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  -- the two shifts
  case inr.inr.inr.inr.inr.inr.inr.inl =>
    refine ⟨by simp [eUG_ev hL' h8], by simp [PF.idx], le_trans (by simp [PF.idx]) h16,
      maxv_BW' ⟨trivial, leafB_of_rdOK hx _ (by simp [Expr.rdOK, eUG, eG, ekg, egm, tsubE, eL]),
        fun _ => by simp [eUG_ev hL' h8, hUG]⟩ (by simp [eUG_ev hL' h8]) (wpM_le_of_wlp h512 (by
          decide))⟩
  case inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    refine ⟨by simp [eHC_ev hL' h8], by simp [PF.idx], le_trans (by simp [PF.idx]) h16,
      maxv_BW' ⟨trivial, leafB_of_rdOK hx _ (by
        simp [Expr.rdOK, eHC, ecsB, ersB, eIC, eMu, euT, ekc, eT, egm, eG, eL]), fun _ => by
          simp [eHC_ev hL' h8, hHC]⟩ (by simp [eHC_ev hL' h8]) (wpM_le_of_wlp h512 (by decide))⟩
  all_goals refine ⟨by simp [eN, eL, hN', hL', eG_ev hL', eT_ev hL', eth_ev hL', eBe_ev hL' h8,
    eBg_ev hL' h8,
      eH_ev hL'], by simp [PF.idx], le_trans (by simp [PF.idx]) h16,
      maxv_BW' (leafB_of_rdOK hx _ (by
        simp [Expr.rdOK, eN, eL, eG, eT, eth, eBe, eBg, eUG, eHC, ePC, eH, ekg, egm, tsubE,
          ecsB, ersB, eIC, eMu, euT, ekc]))
        (by
          simp [eN, eL, hN', hL', eG_ev hL', eT_ev hL', eth_ev hL', eBe_ev hL' h8, eBg_ev hL'
            h8, eH_ev hL'])
        (wpM_le_of_wlp h512 (by decide))⟩

end parts

end OrderMaintenance.Impl

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

variable {K KH : Nat}

/-! ### The parameter computation -/

/-- **The parameters of a new core**: the peak of `paramsS`. -/
theorem paramsS_pk (q : Nat) {m : State} {N : Nat} (hN : m.loc "nN" = N) (hpos : 0 < N) (hK : 64
  * pL N ≤ K) :
    wpB (BW K KH) (paramsS q) TT m := by
  obtain ⟨a1, a2, a3, -, -, -⟩ := partA_ok hN
  have hA : wp partA (fun s _ => s.loc "L" = pL N ∧ s.loc "nN" = N) m :=
    ⟨a1, by rw [a2, pL_eq hpos], by rw [a3 "nN" (by decide), hN]⟩
  unfold paramsS
  refine wpB_seq_of hA (partA_pk hK hN) (fun s1 _ ⟨hL1, hN1⟩ => ?_)
  obtain ⟨b1, -, -, b4, -⟩ := partB_ok q hL1 hN1 (pL_ge N)
  have hB : wp (partB q) (fun s _ => s.loc "L" = pL N ∧ s.loc "nN" = N) s1 :=
    ⟨b1, by rw [b4]; exact hL1, by rw [b4]; exact hN1⟩
  exact wpB_seq_of hB (partB_pk hK rfl q hL1 hN1) (fun s2 _ ⟨hL2, hN2⟩ => partC_pk hK rfl hL2 hN2)

/-! ### The allocations of a slot -/

theorem capE_maxv {P : Params} {m : State} (hC : CapsW K (capsOf P)) (h : CapLocs P m.loc) (sl :
  Slot) :
    (capE sl).maxv m ≤ BW K KH := by
  have h16 := hC.sixteen
  have hB : 2 ^ K ≤ BW K KH := by have := pow_BW K; have := Nat.two_pow_pos KH; unfold BW; omega
  have lt : ∀ x, x < 2 ^ K → x ≤ BW K KH := fun x hx => le_trans (le_of_lt hx) hB
  have hl := hC.lst
  have hc := hC.lcap
  have ht := hC.tbl
  have ha := hC.arr
  have hp := hC.path
  have hw := hC.pw
  cases sl with
  | f f =>
    cases f with
    | e k => simp only [capE, Expr.maxv, h.kE]; exact lt _ (by simpa [capsOf] using ht .E)
    | g k => simp only [capE, Expr.maxv, h.kG]; exact lt _ (by simpa [capsOf] using ht .G)
    | c k => simp only [capE, Expr.maxv, h.kC]; exact lt _ (by simpa [capsOf] using ht .C)
    | n k => simp only [capE, Expr.maxv, h.kN]; exact lt _ (by simpa [capsOf] using ht .N)
    | a k =>
      cases k <;> simp only [capE, Expr.maxv, h.kB, h.kCc, h.kL]
      · exact lt _ (by simpa [capsOf] using ha .pqHead)
      · exact lt _ (by simpa [capsOf] using ha .pqNext)
      · exact lt _ (by simpa [capsOf] using ha .pqPrev)
      · exact lt _ (by simpa [capsOf] using ha .pqWhere)
      · exact lt _ (by simpa [capsOf] using ha .nbNext)
      · exact lt _ (by simpa [capsOf] using ha .nbPrev)
      · exact lt _ (by simpa [capsOf] using ha .lpar)
    | s k => simp only [capE, Expr.maxv]; exact lt _ (by omega)
  | sz t => simp only [capE, Expr.maxv]; exact lt _ (by omega)
  | prm => simp only [capE, Expr.maxv]; omega
  | lst k b =>
    have hk := hl k
    have hk' := hc k
    cases k <;> simp only [capE, lrecE, lcapE, Expr.maxv, h.kR, Expr.eval, BinOp.eval,
        Option.bind_some, Option.getD_some, sup_le_iff, add_pos_iff,
        Order.lt_two_iff, zero_le, or_true, le_mul_iff_one_le_right,
        Nat.one_le_ofNat, Nat.ofNat_pos, le_mul_iff_one_le_left,
        Nat.reduceLeDiff, and_self, sup_of_le_right, ge_iff_le, h.kRc, h.kf,
        le_add_iff_nonneg_left, one_mul, max_self] <;>
      simp only [capsOf] at hk hk' <;> exact lt _ (by omega)
  | len k =>
    have hk := hl k
    cases k <;> simp only [capE, lrecE, Expr.maxv, h.kR, ge_iff_le, h.kRc] <;>
      simp only [capsOf] at hk <;>
      omega
  | path =>
    have hC' := ht .C
    simp only [capsOf] at hp hw hC'
    simp only [capE, Expr.maxv, h.kC, h.kW, Expr.eval, BinOp.eval, Option.bind_some,
        Option.getD_some, sup_le_iff, add_pos_iff, Order.lt_two_iff, zero_le, or_true,
        le_mul_iff_one_le_right, le_add_iff_nonneg_left, Order.lt_add_one_iff,
        le_mul_iff_one_le_left, Nat.reduceLeDiff, and_self, sup_of_le_right, ge_iff_le]
    exact lt _ hp
  | opt o => simp only [capE, Expr.maxv]; exact lt _ (by omega)

/-- **The allocations of a slot.** -/
theorem allocSlot_pk (q : Nat) {P : Params} {m : State} (hC : CapsW K (capsOf P)) (h : CapLocs P
  m.loc) :
    wpB (BW K KH) (allocSlot q) TT m :=
  wpB_allocAll m.loc _ m rfl (fun ae hae s hs => by
    simp only [List.mem_map] at hae
    obtain ⟨sl, -, rfl⟩ := hae
    have h' : CapLocs P s.loc := by rw [hs]; exact h
    exact ⟨by rw [capE_eval h']; rfl, capE_maxv hC h' sl⟩)

end OrderMaintenance.Impl

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

variable {K KH : Nat}

/-! ### A new core -/

/-- The empty core of the construction is bounded. -/
theorem wb_fresh {P : Params} (hP : ParamsB K P) : WB K (freshC P) := by
  have p0 := pos K
  refine ⟨hP, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, fun c =>
    ?_, fun c t ht => ?_, ?_⟩
  · simp only [freshC, getX_empty]; exact elemB_default K
  · simp only [freshC, getX_empty]; exact groupB_default K
  · simp only [freshC, getX_empty]; exact chunkB_default K
  · simp only [freshC, getX_empty]; exact nodeB_default K
  · simp [freshC]
  · simp [freshC, p0]
  · simp [freshC]
  · simp [freshC]
  · simp only [freshC]
    exact ⟨arrB_default K, arrB_default K, arrB_default K, arrB_default K, arrB_default K,
      arrB_default K⟩
  · simp only [freshC]; exact arrB_default K
  · change t ∈ ([] : List Nat) at ht; cases ht
  · exact arrB_default K

theorem fresh_h (P : Params) (i : Nat) : ((freshC P).E.getX i).h = 0 := by simp [freshC]; rfl

/-- **A new core** (a rebuild start): the peak of `newCoreS`. -/
theorem newCore_pk (q : Nat) {m : State} {N : Nat} (hN : m.loc "nN" = N) (hpos : 0 < N)
    (hK : wK (proofParams N) ≤ K) : wpB (BW K KH) (newCoreS q) TT m := by
  have hK64 : 64 * pL N ≤ K := hK
  have h512 : 512 ≤ K := le_trans (wK_ge N) hK
  obtain ⟨a1, -, a3, a4, a5, -, -⟩ := paramsS_ok q hN hpos
  set P := proofParams N
  set m1 := (exec (paramsS q) m).st
  obtain ⟨b1, -, -, b4, -⟩ := fresh_enc (q := q) (m := m1) a3 a4 a5
  set m2 := (exec (allocSlot q) m1).st
  obtain ⟨L', c, he, -⟩ := initCoreS_lazy (κ := capsOf P) (P := P)
    (L := State.setLocs (fun _ => 0) ["lz"] [1]) (by simp [State.setLocs, State.upd])
    (proofParams_B N).1 (proofParams_B N).2 (capsOf_init P) (by simp [capsOf]) (by simp [capsOf])
  have hC : CapsW K (capsOf P) := (capsW_wK N).mono hK
  unfold newCoreS
  refine wpB_seq_of (Qc := fun s _ => s = m1) ⟨a1, rfl⟩ (paramsS_pk q hN hpos hK64) (fun s1 _ e1
    => ?_)
  subst e1
  refine wpB_seq_of (Qc := fun s _ => s = m2) ⟨b1, rfl⟩ (allocSlot_pk q hC a5) (fun s2 _ e2 => ?_)
  subst e2
  rw [compile_κ₀ q P]
  have hvs : ∀ v ∈ [1], v < 2 ^ K := fun v hv => by
    simp only [List.mem_singleton] at hv; subst hv; exact Nat.one_lt_two_pow (by omega)
  refine wpB_coreCall b4 rfl he (by
    simp only [Machine.maxvList, List.map_cons, Expr.maxv, List.map_nil, List.foldr_cons,
        List.foldr_nil, zero_le, sup_of_le_left]
    exact Nat.le_add_left_of_le (Nat.one_le_two_pow)) ?_
    (fun _ _ _ _ => trivial)
  exact pk_BW (initCore_peak hC (by omega) b4 (wb_fresh ((params_wB N).mono hK)) (fun i => by
    rw [fresh_h]; exact Nat.two_pow_pos KH) ((proom_wK N).mono hK) (by simp [P, proofParams])
      (capsOf_init P)
    (by simp [capsOf]) (by simp [capsOf]) hvs he)

/-- **An eagerly built core** (the initialization): the peak of `eagerCoreS`. -/
theorem eagerCore_pk (q : Nat) {m : State} {N : Nat} (hN : m.loc "nN" = N) (hpos : 0 < N) {n : Core}
    (hn : (initCore false).run ({
      P := proofParams N
    } : Core) = .ok () n)
    (hK : wK (proofParams N) ≤ K) : wpB (BW K KH) (eagerCoreS q) TT m := by
  have hK64 : 64 * pL N ≤ K := hK
  have h512 : 512 ≤ K := le_trans (wK_ge N) hK
  obtain ⟨a1, -, a3, a4, a5, -, -⟩ := paramsS_ok q hN hpos
  set P := proofParams N
  set m1 := (exec (paramsS q) m).st
  obtain ⟨b1, -, -, b4, -⟩ := fresh_enc (q := q) (m := m1) a3 a4 a5
  set m2 := (exec (allocSlot q) m1).st
  have hH : 1 ≤ P.H := by simp [P, proofParams]
  have hb : 1 ≤ P.beta := by simp [P, proofParams]
  obtain ⟨L', c, he, -⟩ := initCoreS_eager (κ := capsOf P) (P := P)
    (L := State.setLocs (fun _ => 0) ["lz"] [0]) (by simp [State.setLocs, State.upd])
    (proofParams_B N).1 (proofParams_B N).2 hb hH (capsOf_init P) (by simp [capsOf]) (by
      simp [capsOf]) rfl hn
  have hC : CapsW K (capsOf P) := (capsW_wK N).mono hK
  unfold eagerCoreS
  refine wpB_seq_of (Qc := fun s _ => s = m1) ⟨a1, rfl⟩ (paramsS_pk q hN hpos hK64) (fun s1 _ e1
    => ?_)
  subst e1
  refine wpB_seq_of (Qc := fun s _ => s = m2) ⟨b1, rfl⟩ (allocSlot_pk q hC a5) (fun s2 _ e2 => ?_)
  subst e2
  rw [compile_κ₀ q P]
  have hvs : ∀ v ∈ [0], v < 2 ^ K := fun v hv => by
    simp only [List.mem_singleton] at hv; subst hv; exact Nat.two_pow_pos K
  refine wpB_coreCall b4 rfl he (by simp) ?_ (fun _ _ _ _ => trivial)
  exact pk_BW (initCore_peak hC (by omega) b4 (wb_fresh ((params_wB N).mono hK)) (fun i => by
    rw [fresh_h]; exact Nat.two_pow_pos KH) ((proom_wK N).mono hK) hH (capsOf_init P)
    (by simp [capsOf]) (by simp [capsOf]) hvs he)

end OrderMaintenance.Impl

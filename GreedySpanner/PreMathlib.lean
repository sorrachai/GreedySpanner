import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup -- For List.Nodup and related lemmas
import Mathlib.Order.Basic    -- For lt_asymm, ne_of_lt, lt_irrefl
import Lean
import Mathlib.Tactic.Bound


import Mathlib.Combinatorics.SimpleGraph.Dart
set_option linter.unusedTactic false
--      have h2': sort r (Gi G (i)).edgeFinset ≠ [] := by
--          suffices (Gi G i) ≠ ⊥ by


section
--open Multiset

@[simp] theorem s_inf_sup_eq_of_eq [LinearOrder α] (e : Sym2 α) ⦃u v : α ⦄
  (h : s(Sym2.inf e, Sym2.sup e) = s(u, v)) : s(Sym2.inf e, Sym2.sup e) = e := by
  induction' e with a b
  simp only [Sym2.inf_mk, Sym2.sup_mk, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, inf_eq_left,
    sup_eq_right, and_self, Prod.swap_prod_mk, inf_eq_right, sup_eq_left]
  exact LinearOrder.le_total a b



theorem inf_eq_sup_iff_diag [LinearOrder α] (e : Sym2 α) : e.inf = e.sup  ↔ e.IsDiag := by
  induction' e with a b
  simp only [Sym2.inf_mk, Sym2.sup_mk, ne_eq, inf_eq_sup, Sym2.isDiag_iff_proj_eq]

theorem inf_neq_sup_iff_not_diag [LinearOrder α] (e : Sym2 α) : e.inf ≠ e.sup  ↔ ¬e.IsDiag := by
  induction' e with a b
  simp only [Sym2.inf_mk, Sym2.sup_mk, ne_eq, inf_eq_sup, Sym2.isDiag_iff_proj_eq]


theorem inf_eq_inf_and_sup_eq_sup [LinearOrder α] {s t : Sym2 α} :
    s.inf = t.inf ∧ s.sup = t.sup ↔ s = t := by
  induction' s with a b
  induction' t with c d
  obtain hab | hba := le_total a b <;> obtain hcd | hdc := le_total c d <;>
    aesop (add unsafe le_antisymm)

end

theorem inf_eq_inf_sym2 [LinearOrder α]  {e : Sym2 α} :
  s(Sym2.inf e, Sym2.sup e).inf = Sym2.inf e := by
  induction' e with a b
  simp only [Sym2.inf_mk, Sym2.sup_mk, le_sup_iff, inf_le_left, inf_le_right, or_self,
    inf_of_le_left]


theorem sup_eq_sup_sym2 [LinearOrder α]   {e : Sym2 α} :
  s(Sym2.inf e, Sym2.sup e).sup = Sym2.sup e := by
  induction' e with a b
  simp only [Sym2.inf_mk, Sym2.sup_mk, le_sup_iff, inf_le_left, inf_le_right, or_self,
    sup_of_le_right]



section
open SimpleGraph

universe u v w

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

variable {G} {u v w : V}
theorem SimpleGraph.Walk.IsCycle.length_le [Fintype V] {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    p.support.tail.length ≤ Fintype.card V := by exact hp.support_nodup.length_le_card

lemma nil_iff_edges_neq {p : G.Walk v w} : p.Nil ↔ p.edges = [] := by
  cases p <;> simp

--theorem edges_dropLast_subset {v w : V} (p : G.Walk v w) :    (p.dropLast).edges ⊆ p.edges := by sorry

-- theorem edgeFinset_dropLast_subset {v w : V} (p : G.Walk v w) [DecidableEq (Sym2 V)] :
--     (p.dropLast).edges.toFinset ⊆ p.edges.toFinset := by
--   have:= edges_dropLast_subset p
--   refine Finset.subset_iff.mpr ?_
--   intro e he
--   refine List.mem_toFinset.mpr ?_
--   rw [← @Walk.mem_edgeSet]
--   rw [@List.mem_toFinset] at he
--   rw [@Walk.mem_edgeSet]
--   exact this he



open SimpleGraph.Walk -- Assuming G is a SimpleGraph

theorem exists_eq_cons_of_ne' {u v : V} (hne : u ≠ v) :
    ∀ (p : G.Walk u v), ∃ (w : V) (p' : G.Walk u w) (h : G.Adj w v) , p =  p'.concat h := by
    intro p
    have: ∀ (p : G.Walk v u), ∃ (w : V) (h : G.Adj v w) (p' : G.Walk w u), p = cons h p' := exists_eq_cons_of_ne (by aesop)

--    have: ∃ (x : V) (q : G.Walk u x) (h' : G.Adj x w), cons h p = q.concat h' := SimpleGraph.Walk.exists_cons_eq_concat
    sorry
    -- specialize this pr
    -- obtain ⟨w,h1,q,h3⟩ := this
    -- use w
    -- rw [@adj_comm] at h1
    -- sorry

theorem SimpleGraph.egirth_le_of_exist_cycle{α : Type u_1} {G : SimpleGraph α} {n : ℕ∞}  (h: ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧  w.length ≤ n):
G.egirth ≤ n := by
  if top: n = ⊤ then
      rw [top]
      exact OrderTop.le_top G.egirth
  else
    have h': ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length < n+1 := by
      obtain ⟨a,w,hw⟩ := h
      rw [← propext (ENat.lt_add_one_iff top)] at hw
      use a,w

    have: n + 1 ≤ G.egirth ↔ ∀ (a : α) (w : G.Walk a a), w.IsCycle → (n+1) ≤ ↑w.length := SimpleGraph.le_egirth
    rw [← not_iff_not] at this
    push_neg at this

    have o1: G.egirth < n + 1 ↔ G.egirth ≤ n := by
      constructor
      intro h
      exact Order.le_of_lt_add_one h
      intro h
      exact (ENat.lt_add_one_iff top).mpr h
    rw [o1] at this
    rwa [this]



theorem walk_length_rotate {V : Type u} {G : SimpleGraph V} {w v : V}
  (p: G.Walk w w) (hv: v ∈ p.support) [DecidableEq V] [DecidableEq (Sym2 V)] :
  (p.rotate hv).length = p.length := by
  let p_rot := p.rotate hv
  simp only [Walk.rotate, Walk.length_append]
  conv =>
    right
    rw [← SimpleGraph.Walk.take_spec p hv]
    simp only [Walk.length_append]
  exact Nat.add_comm (p.dropUntil v hv).length (p.takeUntil v hv).length

theorem walk_dart_edge_eq_edge {V : Type u} {G : SimpleGraph V} {w : V}
  (p: G.Walk w w)  (i : Fin p.edges.length) [DecidableEq V] [DecidableEq (Sym2 V)] :
  p.darts[i].edge = p.edges[i] := by
  let n := p.edges.length
  let toEdge (de : G.Dart) := de.edge
  have: p.darts.map toEdge = p.edges := by rfl
  rw [List.ext_get_iff] at this
  obtain ⟨h1,h2⟩ := this
  have:= h2 i ?_ ?_
  have pe: p.darts[i].edge  = (List.map toEdge p.darts).get ⟨↑i, ?_⟩ := by simp [toEdge]
  swap
  rw [pe,this]
  simp only [List.get_eq_getElem, Fin.getElem_fin, toEdge]
  --all_goals (rw [h1]; exact i.isLt)
  rw [h1]
  exact i.isLt
  rw [h1]
  exact i.isLt
  exact i.isLt

theorem takeUntil_length_eq_support_idxOf {V : Type u} {G : SimpleGraph V} {u v w: V}
  {p: G.Walk u v}  (h: w ∈ p.support) [DecidableEq V] [DecidableEq (Sym2 V)] :
   (p.takeUntil w h).length = p.support.idxOf w := by
  induction p with
  | nil =>
    rw [@Walk.mem_support_nil_iff] at h
    aesop
  | cons adj p hi=>
    rename_i x y z
    by_cases hx: x ≠ w
    · rw [Walk.takeUntil_cons]
      simp
      rw [List.idxOf_cons_ne]
      refine Nat.succ_inj.mpr (hi ?_)
      exact List.mem_of_ne_of_mem (id (Ne.symm hx)) h
      exact hx
      exact hx
    · simp at hx
      subst hx
      simp_all only [Walk.takeUntil_first, Walk.length_nil, Walk.support_cons, List.idxOf_cons_self]


theorem last_dart_cycle_rot_dart_eq {V : Type u} {G : SimpleGraph V} {w : V}
  {p: G.Walk w w} (hp: p.IsCycle) {de: G.Dart} (hd: de ∈ p.darts) [DecidableEq V] [DecidableEq (Sym2 V)] :
  let v := de.snd
  have v_in_p: v ∈ p.support := by
    simp only [v]
    exact Walk.dart_snd_mem_support_of_mem_darts p hd
  let p_rot := SimpleGraph.Walk.rotate p v_in_p
  have p_rot_cycle: p_rot.IsCycle := by exact Walk.IsCycle.rotate hp v_in_p
  have npnil: ¬p_rot.Nil := by apply  SimpleGraph.Walk.IsCycle.not_nil p_rot_cycle
  p_rot.lastDart npnil = de
  := by
  -- unfold the definitions of rotation and lastDart
  let u := de.fst
  intro v h p_rot non_cycle rotnnil
  have h_u_support: u ∈ p.support := by exact Walk.dart_fst_mem_support_of_mem_darts p hd
  observe pnnil: ¬p.Nil
  have dart_eq_length: p.darts.length = p.length := Walk.length_darts p
  have sup_eq_length: p.support.length = p.length + 1 := Walk.length_support p

  let v_idx := p.support.idxOf v

  have : ∃ (i : Fin p.darts.length), p.darts[i] = de := by
    rwa [List.mem_iff_get] at hd
  obtain ⟨i,hi⟩ := this
  let i' : Fin p.length := Fin.cast dart_eq_length i

  have ip_le_len: i + 1 ≤ p.length := by
      rw [← dart_eq_length]
      rw [@Order.add_one_le_iff]
      exact i.isLt

  have u_eq_getVert: u = p.getVert i := by
    have u_eq_sup_i: u = p.support.dropLast[i] := by
      have:= (SimpleGraph.Walk.map_fst_darts p)
      rw [@List.ext_get_iff] at this
      simp only [List.length_map, Walk.length_darts, List.length_dropLast, Walk.length_support,
        add_tsub_cancel_right, List.get_eq_getElem, List.getElem_map, List.getElem_dropLast,
        true_and] at this
      simp only [Fin.getElem_fin, List.getElem_dropLast]
      have:= this i ?_ ?_
      rw [← this]
      simp only [← hi, Fin.getElem_fin, u]
      all_goals (have:= i.2;exact Nat.lt_of_lt_of_eq this dart_eq_length)

    rw [u_eq_sup_i]
    simp only [Fin.getElem_fin, List.getElem_dropLast]
    have: i ≤ p.length := by
      rw [← dart_eq_length]
      exact Fin.is_le'
    have:= SimpleGraph.Walk.getVert_eq_support_get? p this
    rw [@List.some_eq_getElem?_iff] at this
    obtain ⟨h1,h2⟩ := this
    exact h2

  have v_eq_getVert: v = p.getVert (i+1) := by
    have v_eq_sup_i: v = p.support.tail[i] := by
      have:= SimpleGraph.Walk.map_snd_darts p
      rw [@List.ext_get_iff] at this
      simp only [List.length_map, Walk.length_darts, List.length_tail, Walk.length_support,
        add_tsub_cancel_right, List.get_eq_getElem, List.getElem_map, List.getElem_tail, true_and,
        u] at this
      simp only [Fin.getElem_fin, List.getElem_tail, u]
      have:= this i ?_ ?_
      rw [← this]
      simp only [← hi, Fin.getElem_fin, v, u]
      all_goals (have:= i.2;exact Nat.lt_of_lt_of_eq this dart_eq_length)

    rw [v_eq_sup_i]
    simp only [Fin.getElem_fin, List.getElem_dropLast]

    simp only [List.getElem_tail, v, u]
    have:= SimpleGraph.Walk.getVert_eq_support_get? p ip_le_len

    rw [@List.some_eq_getElem?_iff] at this
    obtain ⟨h1,h2⟩ := this
    exact h2


  simp only [Walk.rotate, p_rot, v, u]

  by_cases hv: v_idx = 0
  · -- v .. u v
    have psup_w: p.support[0] = w := by
      rw [@List.getElem_zero]
      rw [@Walk.head_support]

    have v_idx_lt_psup: v_idx < p.support.length := List.idxOf_lt_length_of_mem h

    have vw: v = w := by
      simp only [v, u, p_rot]
      rw [← psup_w]
      have: p.support[v_idx]'(v_idx_lt_psup) = v := by simp only [List.getElem_idxOf, v_idx, u,
        p_rot, v]
      aesop

    have wv: w = v := id (Eq.symm vw)
    let u_idx := p.support.idxOf u

    have hde_is_last_dart_p : de = p.lastDart pnnil := by
      simp only [Walk.lastDart, v, u, p_rot, v_idx]
      rw [← hi]
      simp only [Fin.getElem_fin, Walk.penultimate, v, u, p_rot, v_idx]
      have i_p_eq_length: i+1 = p.length := by
--     -- Since v = p.fst and v = p.getVert (i + 1),
--     -- and p is a cycle, i + 1 must be p.length.
        subst wv
        symm at v_eq_getVert
        rw [SimpleGraph.Walk.IsCycle.getVert_endpoint_iff hp ip_le_len] at v_eq_getVert
        simpa using v_eq_getVert

      have i_p_eq_length': i= p.length -1 := by exact Nat.eq_sub_of_add_eq i_p_eq_length
      rw [i_p_eq_length] at v_eq_getVert
      aesop

    suffices p_rot = p.copy wv wv by
      -- mathlib
      have: p_rot.lastDart rotnnil = (p.copy wv wv).lastDart (Eq.mpr_not (congrArg Walk.Nil (id (Eq.symm this))) rotnnil) := by
        rw [@Dart.ext_iff]
        rw [Walk.lastDart_toProd]
        simp only [Walk.lastDart_toProd, Walk.getVert_copy, Walk.length_copy, Prod.mk.injEq,
          and_true]
        rw [this]
        simp only [Walk.getVert_copy, Walk.length_copy, u, p_rot, v, v_idx]
      simp [p_rot,Walk.rotate] at this
      rw [this]
      rw [hde_is_last_dart_p]
      refine (Dart.ext_iff ((p.copy wv wv).lastDart ?_) (p.lastDart pnnil)).mpr ?_
      rw [@Prod.eq_iff_fst_eq_snd_eq]
      simp only [Walk.lastDart_toProd]
      simp [vw]
    simp [p_rot,Walk.rotate]

    subst wv
    simp only [Walk.takeUntil_first, Walk.append_nil, Walk.copy_rfl_rfl, v, u]
    have: (p.takeUntil v h).append (p.dropUntil v h) = p := Walk.take_spec p h
    conv =>
      right
      rw [← this]
    simp only [Walk.takeUntil_first, Walk.nil_append, v, u]

  · -- .. u v .. --> v .. u v
    let p_prefix := p.takeUntil v h
    let p_suffix := p.dropUntil v h
    have prefix_nnil: ¬ p_prefix.Nil := by
      simp only [Walk.nil_takeUntil, p_prefix, v, u, p_rot, v_idx]
      simp only [v_idx, v, u, p_rot, p_prefix] at hv
      by_contra!
      absurd hv
      subst this
      have: p.support = (v :: p.support.tail) := by exact Walk.support_eq_cons p
      rw [this,List.idxOf_cons_self]

    have: p_rot.lastDart rotnnil = p_prefix.lastDart prefix_nnil := by
      simp only [p_rot,p_prefix,Walk.rotate]
      rw [@Dart.ext_iff]
      simp only [Walk.lastDart_toProd, Prod.mk.injEq, and_true, v_idx, p_prefix,  p_rot]
      dsimp [p_prefix] at prefix_nnil
      simp only [Walk.penultimate]
      rw [@Walk.getVert_append]
      have: 0 < (p.takeUntil v h).length := by rwa [← @Walk.not_nil_iff_lt_length]
      have H:  ¬(p.dropUntil v h).length + (p.takeUntil v h).length - 1 < (p.dropUntil v h).length := by
        rw [Nat.add_sub_assoc this (p.dropUntil v h).length]
        simp only [Nat.succ_eq_add_one, zero_add, add_lt_iff_neg_left, Nat.not_lt_zero,
          not_false_eq_true, v_idx, p_prefix, u, p_rot, v]
      simp [H]
      suffices (p.dropUntil v h).length + (p.takeUntil v h).length - 1 - (p.dropUntil v h).length = p_prefix.length -1 by
        rw [this]
      rw [Nat.add_sub_assoc this (p.dropUntil v h).length]
      aesop

    simp only [Walk.rotate, p_rot, v, u, v_idx, p_prefix] at this
    rw [this]
    clear this
    rw [@Dart.ext_iff]
    simp only [Walk.lastDart_toProd, v, u, p_rot, v_idx, p_prefix]
    rw [@Prod.eq_iff_fst_eq_snd_eq]
    simp only [Walk.penultimate, and_true, v, u, p_rot, v_idx, p_prefix]
    rw [SimpleGraph.Walk.getVert_takeUntil]
    swap
    exact Nat.sub_le (p.takeUntil de.toProd.2 h).length 1

    suffices (p.takeUntil v h).length = i+1 by aesop

    have that: p.support.idxOf v = i + 1 := by
      have: List.idxOf v p.tail.support = ↑i := by
        have: i ≤ p.tail.length := by
          have: p.tail.length + 1 = p.length := Walk.length_tail_add_one pnnil
          omega
        have v_eq_p_tail_getVert: v = p.tail.getVert i := by simpa
        have:= Walk.getVert_eq_support_get? p.tail this
        rw [@List.some_eq_getElem?_iff] at this
        obtain ⟨h1,h2⟩ := this
        rw [v_eq_p_tail_getVert,← h2]
        refine List.idxOf_getElem ?_ (↑i) h1
        rw [Walk.support_tail_of_not_nil p pnnil]
        rw [SimpleGraph.Walk.isCycle_def] at hp
        obtain ⟨_,_,H⟩ := hp
        exact H

      rw [← this]
      rw [Nat.add_one]

      have: p.support = p.support.head (Walk.support_ne_nil p) :: p.support.tail := Eq.symm (List.head_cons_tail p.support (Walk.support_ne_nil p))
      rw [this]
      simp only [Walk.nil_takeUntil, p_prefix, v] at prefix_nnil
      simp only [Walk.head_support, Nat.succ_eq_add_one, v, p_prefix]
      rw [List.idxOf_cons_ne]
      swap
      exact prefix_nnil
      simp only [Nat.succ_eq_add_one, Nat.add_left_inj, v, p_prefix]
      rw [Walk.support_tail p pnnil]

    have:= takeUntil_length_eq_support_idxOf h
    rwa [this]


theorem dropLast_edges_toFinset_eq_edges_toFinset_minus {V : Type u} {G : SimpleGraph V} {v : V}
  (p: G.Walk v v) (hp: ¬p.Nil) (hp2: p.IsCycle) [DecidableEq V] [DecidableEq (Sym2 V)] :
  (p.dropLast).edges.toFinset = p.edges.toFinset \ {s(p.penultimate,v)}  := by

  -- Define the last edge for clarity.
  -- Note: p.penultimate requires hp (¬p.Nil) to be well-defined, which is provided.
  let last_edge_val :=  s(p.penultimate, v)
  -- 1. Establish the relationship for the last dart's edge.
  -- The edge of the last dart of p is indeed s(p.penultimate, v).
  have h_last_dart_edge_eq : (p.lastDart hp).edge = last_edge_val := by
    -- SimpleGraph.Walk.edge_lastDart states (p.lastDart hp).edge = Sym2.mk (p.penultimate, p.last)
    -- Since p is a G.Walk v v, p.last = v.
    rw [SimpleGraph.Walk.edge_lastDart p hp]
    -- If p.last is not definitionally v, we might need to use a property of walks ending in v.
    -- However, (p : G.Walk v v) means p.last is indeed v.

  -- 2. Decompose p into p.dropLast and the last dart, and get the edge list decomposition.
  -- A walk p can be expressed as (p.dropLast) with its lastDart appended.

  -- From this walk decomposition, we get a decomposition of the edge lists.
  have h_edges_list_decomp : p.edges = (p.dropLast).edges.concat (p.lastDart hp).edge := by
    let last_dart := p.lastDart hp
    have: (p.lastDart hp).edge = s(p.penultimate, v) := SimpleGraph.Walk.edge_lastDart p hp
    have h_e: G.Adj p.penultimate v := by simp_all only [not_false_eq_true, Walk.adj_penultimate]
    have p_split := SimpleGraph.Walk.concat_dropLast p h_e
    conv =>
      enter [1]
      rw [← p_split]
    simp only [SimpleGraph.Walk.edges_concat]
    rfl

  -- Substitute last_edge_val into the edge list decomposition.
  rw [h_last_dart_edge_eq] at h_edges_list_decomp
  -- Now, h_edges_list_decomp : p.edges = (p.dropLast).edges ++ [last_edge_val]

  -- 3. Convert the edge list decomposition to a finset relationship.
  -- The finset of edges of p is the union of the finset of edges of p.dropLast and the singleton finset of the last edge.
  have h_finset_union_relation : p.edges.toFinset = (p.dropLast).edges.toFinset ∪ {last_edge_val} := by
    rw [h_edges_list_decomp]
    simp
    --exact List.toFinset_append_right _ _ -- Property: (L₁ ++ L₂).toFinset = L₁.toFinset ∪ L₂.toFinset

  -- 4. Use the IsCycle property to show the last edge is not in the edges of p.dropLast.
  -- Since p is a cycle, it's also a trail (hp2.isTrail).
  have h_is_trail : p.IsTrail := hp2.isTrail
  -- A trail has no duplicate edges.
  have h_nodup_edges : p.edges.Nodup := SimpleGraph.Walk.IsTrail.edges_nodup h_is_trail

  -- Apply h_nodup_edges to the decomposed edge list.
  -- If (L ++ [e]).Nodup, then e ∉ L and L.Nodup.
  rw [h_edges_list_decomp] at h_nodup_edges

  have h_last_edge_not_in_dropLast_list : last_edge_val ∉ (p.dropLast).edges := by
    let l :=  p.edges
    have: l.Nodup := by exact h_is_trail.edges_nodup
    let e := last_edge_val
    by_contra!


    have: l.Duplicate e := by
      rw [List.duplicate_iff_two_le_count]
      simp [l]
      rw [h_edges_list_decomp]
      rw [List.count_concat_self]
      simp
      exact this
    apply List.Duplicate.not_nodup at this

    contradiction


  have h_last_edge_not_in_dropLast_finset : last_edge_val ∉ (p.dropLast).edges.toFinset := by aesop
  rw [h_finset_union_relation]
  aesop



--lemma nil_iff_eq_nil : ∀ {p : G.Walk v v}, ¬ p.Nil ↔ p ≠ nil := by
--lemma fromEdgeSet_edgeFinset_cancel {V : Type u} {s : Finset (Sym2 V)}: (fromEdgeSet ↑s).edgeFinset = s :=  sorry

end

section
open Finset

variable {α}
--#check Sym2.rec

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

lemma sort_drop_sort_eq_drop_sort [DecidableEq α ] (s : Finset α) (i:ℕ):
sort r ((s.sort r).drop i).toFinset = (s.sort r).drop i := by
  refine (List.toFinset_sort r ?_).mpr ?_
  · suffices (sort r (s)).Nodup by
      let l1 := List.drop i (sort r (s))
      let l2 := sort r (s)
      observe o1: l2.Nodup
      observe o2: l1.Sublist l2
      exact List.Sublist.nodup o2 this
    exact sort_nodup r (s)
  · induction' i  with i ih
    · simp
    · simp at ih
      rw [← List.drop_drop]
      have: (List.drop i (sort r (s))).drop 1 = (List.drop i (sort r (s))).tail := List.drop_one
      rw [this]
      apply List.Sorted.tail ih



theorem dropLast_toFinset_eq_toFinset_minus_of_nodup (l: List α)  [DecidableEq α] (h: l ≠ []) (h2: l.Nodup):
  l.dropLast.toFinset =  (l.toFinset) \ {l.getLast h} := by
  let e_last :=  l.getLast h;
  have lnempty: l ≠ [] := by aesop
  have:= List.dropLast_concat_getLast lnempty
  change l.dropLast.toFinset = l.toFinset \ {e_last}
  rw [← this]
  simp only [ne_eq, List.cons_ne_self, not_false_eq_true, List.dropLast_append_of_ne_nil,
    List.dropLast_singleton, List.append_nil, List.toFinset_append, List.toFinset_cons,
    List.toFinset_nil, insert_empty_eq]
  -- l.dropLast.toFinset = (l.dropLast.toFinset ∪ {l.getLast lnempty}) \ {e_last}

  refine Eq.symm (union_sdiff_cancel_right ?_)
  simp
  by_contra! h
  have: l.Duplicate e_last := by
    rw [List.duplicate_iff_two_le_count]
    rw [← this]
    observe eqelem: e_last  = l.getLast lnempty
    observe: l.dropLast ++ [e_last] = l.dropLast.concat e_last
    rw [← eqelem,this]
    rw [List.count_concat_self]
    simp
    exact h
  apply List.Duplicate.not_nodup at this
  contradiction

theorem sort_non_empty_iff_non_empty {s : Finset α}  : sort r s ≠ [] ↔ s.Nonempty := by
  constructor
  · intro h
    observe: 0 < (sort r s).length
    have: 0 < #s := by aesop
    exact card_pos.mp this
  · intro h
    observe: 0 < #s
    have:  (s.sort r).length = #s := Finset.length_sort r
    observe: 0 < (s.sort r).length
    rwa [← @List.length_pos_iff_ne_nil]

theorem sort_empty_iff_empty {s : Finset α}  : sort r s = [] ↔ s = ∅ := by
  rw [← not_iff_not]
  have: s.Nonempty ↔ (¬ s = ∅) := by
    constructor
    aesop
    intro h
    simp at h
    simp [Finset.Nonempty]
    rw [@Finset.eq_empty_iff_forall_notMem] at h
    simp at h
    exact h
  rw [← this]
  exact sort_non_empty_iff_non_empty r

end


section



variable {α : Type*} [LinearOrder α] -- LinearOrder provides <, ≤, and their properties
variable {l : List α}
variable {x y : α}

lemma idxOf_lt_idxOf_when_sorted_nodup_of_lt
    (hs : l.Sorted (·≤·))
    (hn : l.Nodup)
    (hxl : x ∈ l)
    (hyl : y ∈ l)
    (hrxy : x < y) :
    l.idxOf x < l.idxOf y := by
  let i := l.idxOf x
  let j := l.idxOf y

  -- Properties from x ∈ l and y ∈ l
  have hi_lt_len : i < l.length :=  List.idxOf_lt_length_of_mem hxl
  have h_get_x : l[i]'hi_lt_len = x := List.getElem_idxOf hi_lt_len
  have hj_lt_len : j < l.length := List.idxOf_lt_length_of_mem hyl
  have h_get_y : l[j]'hj_lt_len = y := List.getElem_idxOf hj_lt_len

  -- We proceed by trichotomy on the indices i and j
  obtain hij | hji | hji := Nat.lt_trichotomy i j
  -- Case 1: i < j. This is our goal.
  · exact hij
  -- Case 2: i = j. (rcases used rfl to substitute j with i)
  ·
    have x_eq_y : x = y := by
      rw [← h_get_x, ← h_get_y] -- Since i = j
      aesop
    -- We have x = y, but hrxy states x < y, which implies x ≠ y.
    exact absurd x_eq_y (ne_of_lt hrxy)

  -- Case 3: j < i.
  · -- Since l is Sorted (·≤·) and Nodup, it's strictly sorted with respect to <.
    -- Mathlib provides: List.Sorted.nthLe_lt_nthLe_iff_lt_of_nodup
    have h_y_lt_x : y < x := by
      rw [← h_get_x, ← h_get_y] -- Substitute x and y with their nthLe expressions
      apply List.Sorted.lt_of_le at hs
      replace hs:= hs hn
      refine StrictMono.imp ?_ hji
      exact List.Sorted.get_strictMono hs
    -- We have y < x from j < i, and hrxy : x < y. This is a contradiction.
    exact absurd (lt_trans h_y_lt_x hrxy) (lt_irrefl y) -- y < x < y implies y < y
    -- Alternatively: exact (lt_asymm hrxy h_y_lt_x)

end

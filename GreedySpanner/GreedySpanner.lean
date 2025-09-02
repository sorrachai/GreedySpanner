import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Util.Notation3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic.Qify
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

import «GreedySpanner».PreMathlib
import «GreedySpanner».unordered_lex
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.DropRight
import Mathlib.Data.Fintype.Perm
--import Paperproof


open SimpleGraph Finset Classical

variable {n t : ℕ} [NeZero t]
def Edge n:= Sym2 (Fin n)

open SimpleGraph Std

def SimpleGraph.IsSpannerOf   (H G : SimpleGraph (Fin n))  (t:ℕ)  : Prop :=
  H.IsSubgraph G ∧ ∀ u v : Fin n, H.edist u v ≤ t * G.edist u v

noncomputable def SimpleGraph.numEdges  (G : SimpleGraph (Fin n) ) : ℕ := #G.edgeFinset
noncomputable def exGirth (n t:ℕ) [NeZero n]  : ℕ := sup {H : SimpleGraph (Fin n)  | 2*t + 1 ≤ H.egirth } numEdges

def SimpleGraph.addEdge (G: SimpleGraph (Fin n)) (e : Edge n) := G ⊔ edge e.inf e.sup
def SimpleGraph.addEdge_uv (G: SimpleGraph (Fin n)) (u v: Fin n) := G ⊔ edge u v

noncomputable def SimpleGraph.edist_edge (G: SimpleGraph (Fin n)) (e : Edge n) := G.edist e.inf e.sup

@[simp] theorem addEdge_edist_eq {n : ℕ} (H : SimpleGraph (Fin n)) (e : Edge n) (he: ¬e.IsDiag): (H.addEdge e).edist_edge e = 1 := by
  simp [addEdge,edist_edge]
  right
  simp [edge,he]
  rw [← @Ne.eq_def]
  rwa [@inf_neq_sup_iff_not_diag]

@[simp] theorem edist_edge_self_eq {n : ℕ} (H : SimpleGraph (Fin n)) (e : Edge n)
  (h : 0 < H.edist_edge e) : ¬Sym2.IsDiag e :=  by
  by_contra!
  have: H.edist_edge e = 0 := by
    simp [edist_edge]
    rwa [@inf_eq_sup_iff_diag]
  absurd h
  rw [this]
  norm_cast


theorem e_in_edgeSet_of_e_in_sort {n : ℕ} {G : SimpleGraph (Fin n)} {e : Sym2 (Fin n)} (h: e ∈ sort lex G.edgeFinset ) :
  e ∈ G.edgeSet := by aesop

 theorem e_in_sort_of_e_in_edgeSet {n : ℕ} {G : SimpleGraph (Fin n)} {e : Edge n} (h : e ∈ G.edgeSet) :
  e ∈ sort lex G.edgeFinset := by aesop


theorem SimpleGraph.edist_edge_of_edist {n : ℕ}{G : SimpleGraph (Fin n)} {e : Edge n} {u v : Fin n} (h: s(u,v)=e)(x:ℕ)(h2: G.edist u v ≤ x):
  G.edist_edge e ≤ x:= by
  simp [edist_edge]
  rw [← h]
  simp only [Sym2.inf_mk, Sym2.sup_mk]
  obtain h | h : u ≤ v ∨ v < u := by exact Fin.le_or_lt u v
  · have o1: min u v = u := by simpa only [inf_eq_left]
    have o2: max u v = v := by simpa only [sup_eq_right]
    rwa [o1,o2]
  · have o1: min u v = v := by
      simp only [inf_eq_right]
      exact Fin.le_of_lt h
    have o2: max u v = u := by
      simp only [sup_eq_left]
      exact Fin.le_of_lt h
    rw [o1,o2]
    rwa [@edist_comm]

theorem le_addEdge {n : ℕ} (G  : SimpleGraph (Fin n)) (e: Edge n):
 G ≤ G.addEdge e := by simp only [addEdge, le_sup_left]

theorem e_in_G_of_neq {n : ℕ} {G : SimpleGraph (Fin n)} {e e' : Edge n} (e'ne: e' ≠ e) (h2: e' ∈ (G.addEdge e).edgeSet):
  e' ∈ G.edgeSet := by
  let H := G.addEdge e
  by_contra! e_not_in_G
  absurd e'ne
  simp [e_not_in_G,addEdge] at h2
  simp [edge,e'ne] at h2
  replace h2 := h2.1
  suffices h: s(Sym2.inf e, Sym2.sup e) = e by rw [← h,h2]
  rw [← @inf_eq_inf_and_sup_eq_sup]
  exact ⟨inf_eq_inf_sym2,sup_eq_sup_sym2⟩


theorem edge_le_G_of_in_edgeSet {n : ℕ} {G  : SimpleGraph (Fin n)} {e : Edge n} (h : e ∈ G.edgeSet) :
  (edge e.inf e.sup) ≤ G := by
  intro u v h
  rw [@adj_edge] at h
  rw [@adj_iff_exists_edge]
  refine ⟨h.2, ?_⟩
  use e
  replace h:= h.1
  rw [s_inf_sup_eq_of_eq e h] at h
  subst h
  simp_all only [Sym2.mem_iff, true_or, or_true, and_self]

theorem union_addEdge_eq_of_in_edgeSet {n : ℕ} (G H : SimpleGraph (Fin n)) (e : Edge n) (h1 : e ∈ G.edgeSet) :
  G ⊔ H.addEdge e = G ⊔ H := by
  refine sup_eq_sup_iff_left.mpr ?_
  constructor
  simp only [addEdge, sup_le_iff, le_sup_right, true_and]
  exact le_sup_of_le_left (edge_le_G_of_in_edgeSet h1)
  simp [addEdge]
  intro v w a
  simp_all only [sup_adj, true_or, or_true]

omit [NeZero t] in
theorem edist_le_of_edist_edge{G : SimpleGraph (Fin n)}(u v : Fin n) {x : ℕ∞} (h3: G.edist_edge s(u,v) ≤ x):
 G.edist u v ≤ x := by
  if uneqv: u = v then
    rw [uneqv]
    simp
  else
    wlog h: u < v generalizing u v
    · observe suv_eq: s(u,v) = s(v,u)
      replace this:= this v u (by rwa [← suv_eq]) (by omega) (by omega)
      rwa [@SimpleGraph.edist_comm]
    · simp [edist_edge] at h3
      observe o1: min u v = u
      observe o2: max u v = v
      aesop

noncomputable def add_if t:= (fun (H: SimpleGraph (Fin n)) e =>
      if (2 * t - 1) < H.edist_edge e then
        H.addEdge e
      else
        H)

noncomputable
def GreedySpannerFoldl (t : ℕ) [NeZero t] (G: SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  GreedySpannerFoldl.Rec t G ⊥
where
  Rec (t : ℕ) [NeZero t] (G H: SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  (G.edgeFinset.sort lex).foldl
    (add_if t)
    H

#check List.foldl.induct
lemma greedySpannerFoldlSubgraphOf (G: SimpleGraph (Fin n))  :
  (GreedySpannerFoldl t G) ≤ G := by
  simp [GreedySpannerFoldl]
  have:= greedySpannerFold_subset.Rec G ⊥
  aesop
  where
    greedySpannerFold_subset.Rec (G H: SimpleGraph (Fin n)):   GreedySpannerFoldl.Rec t G H ≤ G ⊔ H := by
      simp [GreedySpannerFoldl.Rec]
      have: ∀ e ∈ sort lex G.edgeFinset, e ∈ G.edgeSet := by
        exact fun e a ↦ e_in_edgeSet_of_e_in_sort a
      revert this
      induction H,(G.edgeFinset.sort lex) using List.foldl.induct (add_if t) with
      |case1 =>
        simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.foldl_nil, le_sup_right,
          imp_self]
      |case2 H e l ih =>
        simp only [List.mem_cons, forall_eq_or_imp, List.foldl_cons, ge_iff_le, and_imp]
        simp only [ge_iff_le] at ih
        intro h1 h2
        replace ih := ih h2
        suffices G ⊔ add_if (↑t) H e = G ⊔ H by exact le_of_le_of_eq ih this
        simp only [add_if]
        split_ifs with h
        exact union_addEdge_eq_of_in_edgeSet G H e h1
        rfl

lemma GSFDistEdge  (t:ℕ)[NeZero t](G: SimpleGraph (Fin n)){e : Edge n} (h: e ∈ G.edgeSet) :
  (GreedySpannerFoldl t G).edist_edge e ≤ (2*t-1) := by
  obtain:= GSFDistEdge.Rec G ⊥
  aesop
  where GSFDistEdge.Rec  (G H: SimpleGraph (Fin n)):
    let GS := (GreedySpannerFoldl.Rec t G H)
    H ≤ GS ∧ ∀ e, e ∈ (G.edgeFinset.sort lex) → GS.edist_edge e ≤ (2*t-1) := by
          dsimp [GreedySpannerFoldl.Rec]
          induction H,(G.edgeFinset.sort lex) using List.foldl.induct (add_if t) with
          | case1=> simp
          | case2 H e l ih =>
            simp
            obtain ⟨ih1,ih2⟩ := ih
            constructor
            · suffices H ≤ add_if t H e from Preorder.le_trans H (add_if (↑t) H e) (List.foldl (add_if ↑t) (add_if (↑t) H e) l) this ih1
              simp [add_if]
              split_ifs with h
              exact le_addEdge H e
              rfl
            · refine ⟨?_,ih2⟩
              simp [add_if]
              simp [add_if] at ih1
              split_ifs at * with h
              · let H' := l.foldl (add_if ↑t) (H.addEdge e)
                show H'.edist_edge e ≤ 2*t-1
                calc
                H'.edist_edge e ≤ (H.addEdge e).edist_edge e := by simp [addEdge,edist_edge];  exact edist_anti ih1
                _ = 1 := by
                  apply addEdge_edist_eq
                  apply edist_edge_self_eq H
                  exact pos_of_gt h
                _ ≤ 2*t - 1 := by
                  norm_cast
                  observe: t > 0
                  omega
              · simp only [_root_.not_lt] at h
                let H' := l.foldl (add_if ↑t) H
                have h_sub: H ≤ H' := by exact ih1
                show H'.edist_edge e ≤ 2*t-1
                calc
                H'.edist_edge e ≤ H.edist_edge e := by  simp [addEdge,edist_edge];  exact edist_anti ih1
                _ ≤ 2*t -1 := h

lemma greedySpannerFoldlDistUBAtEdge' {G : SimpleGraph (Fin n)}(t :ℕ ) [NeZero t] (u v : Fin n) (hG: G.Adj u v):
  (GreedySpannerFoldl t G).edist u v ≤ 2*t-1 := by
  let e := s(u,v)
  have: e ∈ G.edgeSet := hG
  have:= GSFDistEdge t G this
  exact edist_le_of_edist_edge u v this

namespace SimpleGraph
namespace Walk

theorem short_detour_exists {n : ℕ} (t : ℕ) [inst : NeZero t] {H G : SimpleGraph (Fin n)} {u v : Fin n}
  (h : G.Adj u v) (hH: H = GreedySpannerFoldl t G) : ∃ p : H.Walk u v, p.length ≤ 2 * t - 1 := by
  have h_edist:= greedySpannerFoldlDistUBAtEdge' t u v h
  have h_reach: H.Reachable u v := by
    rw [← @edist_ne_top_iff_reachable]
    by_contra!
    rw [hH] at this
    rw [this] at h_edist
    simp at h_edist
    rw [@ENat.eq_top_iff_forall_gt] at h_edist
    have d:= h_edist (2*t+1)
    norm_cast at d
    simp only [add_lt_iff_neg_left, not_lt_zero'] at d

  obtain ⟨p,hp⟩ : ∃ (p : H.Walk u v), p.length = H.edist u v := Reachable.exists_walk_length_eq_edist h_reach
  use p
  have: p.length ≤ (2 * ↑t - 1: ℕ∞) := calc
      p.length = (GreedySpannerFoldl t G).edist u v := by rwa [← hH]
      _ ≤ 2 * ↑t - 1 := h_edist
  norm_cast at this

noncomputable def detour (t:ℕ)[NeZero t]{H G: SimpleGraph (Fin n)} {u v : Fin n}(h: G.Adj u v) (hH: H = GreedySpannerFoldl t G): H.Walk u v :=
  have: ∃ p: H.Walk u v, p.length ≤ 2*t -1 := short_detour_exists t h hH
  choose this

noncomputable def detour_walk (t :ℕ)[NeZero t]{H G : SimpleGraph (Fin n)} {u v : Fin n} (hH: H = GreedySpannerFoldl t G): G.Walk u v → H.Walk u v
  | nil => nil
  | cons h p => append (detour t h hH) (detour_walk t hH p)

lemma detour_walk_length (t :ℕ)[NeZero t]{H G : SimpleGraph (Fin n)} {u v : Fin n} (hH: H = GreedySpannerFoldl t G) (p : G.Walk u v):
  (detour_walk t hH p).length ≤ (2*t-1)*p.length := by
  induction p with
  | nil => aesop
  | cons h p hp =>
    rename_i u v _
    simp [detour_walk]
    have short: ∃ p: H.Walk u v, p.length ≤ 2*t -1 := short_detour_exists t h hH
    have length:= choose_spec short
    calc
      (detour t h hH).length + (detour_walk t hH p).length =
        (choose short).length + (detour_walk t hH p).length  :=  rfl
      _ ≤ (2*t-1) + (2 * t - 1) * p.length := Nat.add_le_add length hp
      _ =(2 * t - 1) * (p.length + 1) := by ring

lemma greedySpannerFoldlDistUB (G : SimpleGraph (Fin n))(hG: G.Connected)(t :ℕ ) [NeZero t] (u v: Fin n) :
  (GreedySpannerFoldl t G).edist u v ≤ (2*t-1)*G.edist u v := by

  let H := GreedySpannerFoldl t G
  have hH : H = GreedySpannerFoldl t G := rfl
  have hr: G.Reachable u v := by
    -- could be in Mathlib
    rw [SimpleGraph.connected_iff_exists_forall_reachable] at hG
    obtain ⟨r,hr⟩ := hG
    have ru:= hr u
    have rv:= hr v
    rw [@reachable_comm] at ru
    exact Reachable.trans ru (hr v)

  obtain ⟨p,hp⟩ : ∃ (p : G.Walk u v), p.length = G.edist u v := Reachable.exists_walk_length_eq_edist hr
  have:= detour_walk_length t hH p
  calc
    H.edist u v ≤ (detour_walk t hH p).length := Walk.edist_le (detour_walk t hH p)
    _ ≤ (2 * t - 1) * p.length := by norm_cast
    _ = (2 * t - 1) * (G.edist u v) := congrArg (HMul.hMul (2 * ↑t - 1)) hp

omit [NeZero t] in
theorem e_in_cycle_of_high_girth  {G : SimpleGraph (Fin n)} {e : Edge n}  (h : 2 * ↑t + 1 ≤ G.egirth)
(w : Fin n) (p : (G.addEdge e).Walk w w)(hp: p.IsCycle)(h2:p.length < 2 * t + 1 ) : e ∈ p.edges := by
  by_contra!
  let p' := p.transfer G ?_
  have: G.egirth ≤ p.length := by
    apply egirth_le_of_exist_cycle
    use w,p'
    constructor
    · refine IsCycle.transfer hp ?_
    · suffices p'.length = p.length by exact le_of_eq (congrArg Nat.cast this)
      refine Walk.length_transfer p ?_
  suffices 2*t+1 ≤ p.length by
    absurd this
    exact Nat.not_le_of_lt h2
  have:= calc
    2 * t + 1 ≤ G.egirth := h
    _ ≤ p.length := this
  norm_cast at this

  intro e' h
  have h': e' ∈ (G.addEdge e).edgeSet := by
    exact Walk.edges_subset_edgeSet p h
  have e'_neq_e: e' ≠ e := by aesop
  simp only [addEdge, edgeSet_sup, Set.mem_union] at h'

  by_contra!
  simp [this,edge] at h'
  obtain ⟨h1,h2⟩ := h'
  apply e'_neq_e
  rw [h1, ← @inf_eq_inf_and_sup_eq_sup]
  aesop (add safe [Sym2.inf_le_sup])


omit [NeZero t] in
theorem cycle_in_H_small_dist_in_G_ofs  {G : SimpleGraph (Fin n)} {e : Edge n} {w: Fin n}{p : (G.addEdge e).Walk w w}
 (hp: p.IsCycle) (h_len: p.length < 2 * t + 1) (h_mem: e ∈ p.edges): G.edist_edge e ≤ 2 * ↑t - 1 := by

  let H := G.addEdge e
  let d ( w : H.Dart) : Prop := w.edge = e
  have hd: ∃ x  ∈ p.darts, d x := by
    obtain  ⟨i_fin, h_get_eq_e⟩ : ∃ (i_fin : Fin p.edges.length), p.edges[i_fin] = e := List.mem_iff_get.mp h_mem
    have h_edges_len_eq_p_len : p.edges.length = p.length := SimpleGraph.Walk.length_edges p
    use p.darts[i_fin]
    constructor
    · simp [d]
    · dsimp [d]
      conv =>
        right
        rw[← h_get_eq_e]
      apply walk_dart_edge_eq_edge
  let de := p.darts.choose d hd
  have de_prop := p.darts.choose_property d hd
  have de_mem  := p.darts.choose_mem d hd

  have found_de: de.edge = e := by aesop
  have found_de': s(de.toProd.1, de.toProd.2) = e := by aesop
  let u' := de.toProd.1
  let v' := de.toProd.2

  have v'_in_p: v' ∈ p.support := by
    simp [v']
    exact Walk.dart_snd_mem_support_of_mem_darts p de_mem

  let p_rot := SimpleGraph.Walk.rotate p v'_in_p
  have p_rot_cycle: p_rot.IsCycle := by exact Walk.IsCycle.rotate hp v'_in_p
  have npnil: ¬p_rot.Nil := by apply  SimpleGraph.Walk.IsCycle.not_nil p_rot_cycle

  let p_rot_droplast := p_rot.dropLast
  have penult_eq: p_rot.penultimate = u' := by
    have last_dart_eq:= SimpleGraph.Walk.edge_lastDart p_rot npnil
    have last_dart_eq_de: p_rot.lastDart npnil = de := by
      apply last_dart_cycle_rot_dart_eq hp de_mem
    rw [last_dart_eq_de] at last_dart_eq
    rw [found_de] at last_dart_eq
    conv at last_dart_eq =>
      enter [1]
      rw [← found_de']
    simp [u',v'] at last_dart_eq
    observe dev': de.toProd.2 = v'
    obtain h | h := last_dart_eq
    rw [← @Prod.fst_eq_iff] at h
    aesop
    by_cases this: de.toProd.1 = de.toProd.2
    have:= de.fst_ne_snd
    contradiction
    nth_rewrite 1 [h] at this
    simp at this

  let l := p.edges
  have o: p.edges ≠ [] := by exact List.ne_nil_of_mem h_mem
  have ENodup: p.edges.Nodup := by exact hp.edges_nodup

  let p_rot_drop_last_copy := SimpleGraph.Walk.copy p_rot_droplast (rfl) (penult_eq)
  have p_drop_last_copy_in_G: ∀ e ∈ p_rot_drop_last_copy.edges, e ∈ G.edgeSet := by
    suffices p_drop_last_in_G: ∀ e ∈ p_rot_droplast.edges, e ∈ G.edgeSet by aesop
    have p_rot_drop_eq: p_rot.dropLast.edges.toFinset = p_rot.edges.toFinset \ {s(p_rot.penultimate,v')} := by
      apply dropLast_edges_toFinset_eq_edges_toFinset_minus
      exact npnil
      exact p_rot_cycle

    have: p_rot_droplast.edges.toFinset = (p.edges).toFinset \ {e}:= by
      dsimp [p_rot_droplast]
      rw [p_rot_drop_eq]
      rw [penult_eq]
      have: p_rot.edges.toFinset = p.edges.toFinset := by
        simp [p_rot]
        refine List.toFinset_eq_of_perm p_rot.edges p.edges ?_
        apply List.IsRotated.perm
        exact Walk.rotate_edges p v'_in_p
      rw [this]
      exact congrArg (SDiff.sdiff p.edges.toFinset) (congrArg singleton de_prop)

    intro e' h
    simp [p_rot_droplast] at h
    rw [← @List.mem_toFinset] at h
    rw [this] at h
    obtain ⟨e'inp,e'ne⟩ : e' ∈ p.edges.toFinset ∧ e' ≠ e := by aesop
    rw [@List.mem_toFinset] at e'inp
    have gleh: G ≤ H := by exact le_addEdge G e
    replace gleh : G.edgeSet ≤ H.edgeSet := by exact
      (OrderEmbedding.le_iff_le (edgeSetEmbedding (Fin n))).mpr gleh
    replace this : e' ∈ H.edgeSet := by exact Walk.edges_subset_edgeSet p e'inp
    exact e_in_G_of_neq e'ne this

  let p' := Walk.transfer p_rot_drop_last_copy G p_drop_last_copy_in_G

  apply SimpleGraph.edist_edge_of_edist found_de'
  calc
    G.edist u' v' = G.edist v' u':= SimpleGraph.edist_comm
    _ ≤ p'.length := edist_le p'
    _ = p_rot_drop_last_copy.length := by aesop
    _ ≤  p_rot.length - 1 := ?p_drop_length_reduce
    _ = p.length - 1  := ?p_rot_eq_p_length
    _ ≤ 2*t-1 := by norm_cast;omega

  case p_drop_length_reduce => -- TODO: should be in mathlib
    have: p_rot_drop_last_copy.length < p_rot.length := by
      simp [p_rot_drop_last_copy,p_rot_droplast]
      have hp0: H.Adj p_rot.penultimate v' := by aesop
      have:= SimpleGraph.Walk.concat_dropLast p_rot hp0
      have: p_rot.dropLast.length + 1 = p_rot.length := by
        conv =>
          right
          rw [← this]
        exact Eq.symm (Walk.length_concat p_rot.dropLast hp0)
      rw [← this]
      exact lt_add_one p_rot.dropLast.length
    norm_cast
    omega

  case p_rot_eq_p_length =>
    suffices p_rot.length = p.length from congrFun (congrArg HSub.hSub (congrArg Nat.cast this)) 1
    simp [p_rot]
    apply walk_length_rotate


omit [NeZero t] in
theorem large_girth_addEdge_of_large_girth  { G: SimpleGraph (Fin n)} {e : Edge n}
  (h : 2 * ↑t - 1 < G.edist_edge e) (h2: 2 * ↑t + 1 ≤ G.egirth  ) : 2 * ↑t + 1 ≤ (G.addEdge e).egirth := by
/-
Proof sketch
1. Suppose H ∪ e has low girth.
2. There must be a small cycle.
3. This cycle must contain e since G has high girth.
4. So G.edist e must be small, contradicting with h.
-/
  let H := G.addEdge e
  if h: H.IsAcyclic then
    have:= by calc
      2*t + 1 < (⊤ : ℕ∞)  := compareOfLessAndEq_eq_lt.mp rfl
      _ = H.egirth := by rw [IsAcyclic.egirth_eq_top h]
    exact le_of_lt this
  else
    rw [← @exists_egirth_eq_length] at h
    obtain ⟨w,p,hp,d⟩ := h
    by_contra!
    rw [d] at this
    norm_cast at this
    have: G.edist_edge e ≤ 2*↑t-1 := by
      have einp: e ∈ p.edges := by exact e_in_cycle_of_high_girth h2 w p hp this
      exact cycle_in_H_small_dist_in_G_ofs hp this einp
    absurd h
    exact not_lt_of_ge this

lemma GreedySpanner.Correct (G : SimpleGraph (Fin n)) (hG: G.Connected) (t : ℕ) [NeZero t]:
  (GreedySpannerFoldl t G).IsSpannerOf G (2*t-1) := ⟨greedySpannerFoldlSubgraphOf G, fun u v ↦ greedySpannerFoldlDistUB G hG t u v ⟩

theorem GreedySpanner.HighGirth  (G: SimpleGraph (Fin n)) :
  2*t+1 ≤ (GreedySpannerFoldl t G).egirth := by
  obtain:= GSFGirth.Rec G ⊥
  aesop
  where  GSFGirth.Rec (G H: SimpleGraph (Fin n)) :
    2*t+1 ≤ H.egirth → 2*t+1 ≤ (GreedySpannerFoldl.Rec t G H).egirth := by
          dsimp [GreedySpannerFoldl.Rec]
          induction H,(G.edgeFinset.sort lex) using List.foldl.induct (add_if t) with
          | case1 => simp
          | case2 H e l ih =>
            intro high_girth
            dsimp [add_if]
            dsimp [add_if] at ih
            split_ifs at * with h
            · suffices 2 * ↑t + 1 ≤ (H.addEdge e).egirth by aesop
              exact large_girth_addEdge_of_large_girth h high_girth
            · exact ih high_girth

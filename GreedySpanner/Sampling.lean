import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Density
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
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Bound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Sym.Sym2.Init

section
open SimpleGraph Finset Classical

-------
noncomputable def SimpleGraph.numEdges  (G : SimpleGraph (Fin n) ) : ℕ := #G.edgeFinset
end

namespace SimpleGraph
namespace Walk

variable {G : SimpleGraph (Fin n)}


noncomputable instance locallyfiniteFin  {G : SimpleGraph (Fin n)} : G.LocallyFinite := by
  simp [LocallyFinite]
  intro x
  exact Fintype.ofFinite ↑(G.neighborSet x)


section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {p : ℝ} (hd : 0 ≤ p ∧ p ≤ 1)
--include hd

variable (G : SimpleGraph (Fin n))

-- The probability of keeping a single edge
-- The sample space Ω is a function from the edge set of G to Bool
abbrev Ω := G.edgeSet → Bool

-- Since G.edgeSet and Bool are finite, Ω is also a finite type.
noncomputable instance : Fintype (Ω G) := by exact Fintype.ofFinite (Ω G)
noncomputable instance :  Decidable (G.Adj u v) := by exact Classical.propDecidable (G.Adj u v)

-- Any finite type can be given a discrete measurable space structure,
-- where every set is measurable.
instance : DiscreteMeasurableSpace (Ω G) :=  by exact MeasurableSingletonClass.toDiscreteMeasurableSpace

noncomputable def edge_prob : NNReal :=
  ⟨p, by bound⟩

noncomputable def bernoulli_measure : Measure Bool := (PMF.bernoulli (edge_prob hd) (by
  simp only [edge_prob, ENNReal.coe_le_one_iff]
  bound
) ).toMeasure

noncomputable def prob_measure : Measure (Ω G) :=  Measure.pi (fun _ => bernoulli_measure hd)

instance bernoulli_is_prob : IsProbabilityMeasure (bernoulli_measure hd) := by
  rw [@isProbabilityMeasure_iff]
  simp only [Bool.univ_eq,bernoulli_measure]
  refine
    (PMF.toMeasure_apply_eq_one_iff (PMF.bernoulli (edge_prob hd) (bernoulli_measure._proof_1 hd))
          trivial).mpr
      ?_
  simp only [PMF.support_bernoulli, ne_eq, Bool.cond_prop]
  refine Set.subset_pair_iff.mpr ?_
  intro x hx
  exact (Bool.eq_false_or_eq_true_self x).mpr trivial

instance : IsProbabilityMeasure (Measure.pi fun _ : G.edgeSet ↦ bernoulli_measure hd) := Measure.pi.instIsProbabilityMeasure fun _ ↦ bernoulli_measure hd

noncomputable def prob : PMF (Ω G) :=  (Measure.pi (fun _ => bernoulli_measure hd)).toPMF

-- 2. Define the PMF for the entire graph by taking the product of individual PMFs.
--    `PMF.pi` creates a PMF on `(i : ι) → α` from a collection of PMFs `(i : ι) → PMF α`.
--    This construction mathematically corresponds to multiplying the probabilities,
--    which is correct for independent events.
-- noncomputable def graph_pmf  (p : ℝ≥0∞) (hp: p ≤ 1) : PMF (Ω G) :=
--   (Measure.pi (fun _ => (bernoulli_pmf p hp).toMeasure)).toPMF

-- 3. Convert the PMF to a full Measure object.

abbrev edge_is_kept (e : Sym2 (Fin n)) (ω : Ω G) : Prop :=  ∃ (h : e ∈ G.edgeSet), ω ⟨e, h⟩


-- This is the definition of a random subgraph
def randomSubgraph (ω : Ω G) : SimpleGraph (Fin n) where
  Adj u v :=  G.Adj u v ∧ edge_is_kept G s(u,v) ω
  symm := by
    rintro u v ⟨h1,h2⟩
    observe: s(v,u)  = s(u,v)
    constructor
    · exact id (adj_symm G h1)
    · have: s(u,v) = s(v,u) := by exact id (Eq.symm this)
      rwa [← this]
  loopless := by
    intro u h
    absurd h
    simp_all

#check randomSubgraph


noncomputable
def num_edges_var: Ω G → ℝ := fun ω => (randomSubgraph G ω).numEdges

theorem pr_edge_kept {n : ℕ} {p : ℝ} (hd : 0 ≤ p ∧ p ≤ 1)
  (G : SimpleGraph (Fin n)) :
  let P := (prob hd G).toMeasure;
  ∀ (e : Sym2 (Fin n)) (h : e ∈ G.edgeSet), P.real {ω | ω ⟨e, h⟩ = true} = p := by
  intro P e h
  rw [Measure.real_def]
  simp only [P,prob,bernoulli_measure,Measure.toPMF_toMeasure]

  let s : G.edgeSet → Set Bool := fun e' : G.edgeSet => if e' = e then {true} else Set.univ
  have h_set_eq : {ω |  ω ⟨e, h⟩ = true} = Set.univ.pi s := by
   ext ω
   constructor
   · intro h1
     aesop
   · intro h1
     simp only [Set.mem_setOf_eq]
     have := h1 ⟨e, h⟩ (Set.mem_univ _)
     simpa [s]

  rw [h_set_eq]
  rw [Measure.pi_pi]
  rw [@Finset.prod_apply_ite]
  simp
  have prob_cancel: (edge_prob hd + (1 - edge_prob hd)) = 1 := by
    clear *-
    simp [edge_prob]
    rw [add_comm] -- Switch to (1 - p) + p = 1
    apply tsub_add_cancel_of_le
    aesop

  conv =>
    enter [1,2,1,1]
    norm_cast
    rw [prob_cancel]
    simp only [ENNReal.coe_one, P, s]
  simp only [ENNReal.toReal_one, one_pow, mul_one]

  conv =>
    enter [1,2]
  simp only [edge_prob, NNReal.coe_mk]

  have: p = p^1 := by simp
  nth_rw 2 [this]
  congr 1

  rw [@Finset.card_eq_one]
  use ⟨e,h⟩
  ext ⟨e',h'⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Subtype.mk.injEq]


@[simp] theorem s_inf_sup_eq_of_eq [LinearOrder α] (e : Sym2 α) : s(Sym2.inf e, Sym2.sup e) = e := by
  induction' e with a b
  simp only [Sym2.inf_mk, Sym2.sup_mk, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, inf_eq_left,
    sup_eq_right, and_self, Prod.swap_prod_mk, inf_eq_right, sup_eq_left]
  exact LinearOrder.le_total a b

theorem expected_num_edges :
  let μ := (prob hd G).toMeasure;
  ∫ (r : Ω G), num_edges_var G r ∂μ = p * G.numEdges  := by
  intro μ

  have num_edges_var_eq_sum_indicator : num_edges_var G = ∑ e ∈ G.edgeSet.toFinset, Set.indicator {ω | edge_is_kept G e ω} 1 := by
     ext ω
     simp [Finset.sum_apply,edge_is_kept,num_edges_var]
     simp [Set.indicator,numEdges]
     refine Finset.card_bijective id ?_ ?_
     simp_all only [Multiset.bijective_iff_map_univ_eq_univ, id_eq, Multiset.map_id']
     intro i
     simp [id]
     constructor
     · -- Forward direction: i ∈ (randomSubgraph hd G ω).edgeSet → ∃ h, ω ⟨i, h⟩ = true
      intro hi_random
      have := s_inf_sup_eq_of_eq i
      rw [← this] at hi_random
      rw [SimpleGraph.mem_edgeSet] at hi_random
      simp [randomSubgraph,edge_is_kept] at hi_random
      obtain ⟨h1,h2⟩ := hi_random
      grind

     · -- Backward direction:
      rintro ⟨h,h2⟩
      have := s_inf_sup_eq_of_eq i
      rw [← this]
      rw [SimpleGraph.mem_edgeSet]
      rw [← this] at h
      rw [SimpleGraph.mem_edgeSet] at h
      simp only [randomSubgraph, s_inf_sup_eq_of_eq]
      simp_all only [s_inf_sup_eq_of_eq, true_and]
      obtain ⟨left, right⟩ := hd
      apply Exists.intro
      · exact h2

  rw [num_edges_var_eq_sum_indicator, @Finset.sum_fn, integral_finset_sum]
  swap
  · intro p hp
    exact Integrable.of_finite
  · have: ∑ e ∈ G.edgeSet.toFinset, (∫ (a : Ω G), {ω | edge_is_kept G e ω}.indicator 1 a ∂μ) = ∑ e ∈ G.edgeSet.toFinset, μ.real {ω | edge_is_kept G e ω} := by
      have inner : ∀ e ∈ G.edgeSet.toFinset,  ∫ (a : Ω G), {ω | edge_is_kept G e ω}.indicator 1 a ∂μ =  μ.real {ω | edge_is_kept G e ω} := by
        intro e he
        apply integral_indicator_one
        exact DiscreteMeasurableSpace.forall_measurableSet {ω | edge_is_kept G e ω}
      exact Finset.sum_congr rfl inner

    rw [this]
    have prob_edge_kept (e : Sym2 (Fin n)):  μ.real {ω | edge_is_kept G e ω} = if he : e ∈ G.edgeSet.toFinset then p else 0 := by
      clear this num_edges_var_eq_sum_indicator
      calc μ.real {ω | ∃ (h : e ∈ G.edgeSet), ω ⟨e, h⟩ = true}
          = μ.real ({ω | ∃ (h : e ∈ G.edgeSet), ω ⟨e, h⟩ = true} ∩ Set.univ) := by simp
        _ = μ.real {ω | ∃ (h : e ∈ G.edgeSet), ω ⟨e, h⟩ = true} * μ.real Set.univ := by aesop
        _ = (if he : e ∈ G.edgeSet then μ.real {ω | ω ⟨e, he⟩ = true} else 0) * 1 := by aesop
        _ = if he : e ∈ G.edgeSet then μ.real {ω | ω ⟨e, he⟩ = true} else 0 := by simp
        _ = if he : e ∈ G.edgeSet then p else 0 := by
          split_ifs
          · rename_i h
            apply pr_edge_kept
          · simp_all only
        _ = if he : e ∈ G.edgeSet.toFinset then p else 0 := by aesop

    simp_rw [prob_edge_kept]
    simp only [Set.mem_toFinset, dite_eq_ite]
    have: (∑ x ∈ G.edgeSet.toFinset, if x ∈ G.edgeSet then p else 0) = (∑ x ∈ G.edgeSet.toFinset, p) := by
      calc
        (∑ x ∈ G.edgeSet.toFinset, if x ∈ G.edgeSet then p else 0)  =  (∑ x ∈ G.edgeSet.toFinset, if x ∈ G.edgeSet.toFinset then p else 0) := by simp only [Set.mem_toFinset]
       _ = ∑ x ∈ G.edgeSet.toFinset, p := by aesop
    simp only [this, Finset.sum_const, Set.toFinset_card, Fintype.card_ofFinset, nsmul_eq_mul]
    rw [mul_comm,numEdges,edgeFinset]
    simp_all only [Set.mem_toFinset, dite_eq_ite, Finset.sum_const, Set.toFinset_card, Fintype.card_ofFinset,
      nsmul_eq_mul, μ]

end

import «GreedySpanner».PreMathlib

def lex : Sym2 (Fin n) → Sym2 (Fin n) → Prop := fun x ↦ fun y ↦  x.inf < y.inf ∨ (x.inf = y.inf ∧ x.sup ≤ y.sup) --x.inf + x.sup*(n) ≤ y.inf + y.sup*(n)

local infixl:50 " ≤l " => fun x y => lex x y
local infixl:50 " <l " => fun x y => lex x y ∧ x ≠ y


lemma ltlt_eq_lex (x y : Sym2 (Fin n))(h1: x ≤l y)(h2: y ≤l x) : x = y := by
  have: ∀ (a b : Sym2 (Fin n)), lex a b → lex b a → a = b := by
    intro a b h1 h2
    simp_all [lex]
    by_cases h_lt: a.inf < b.inf
    simp_all
    observe: ¬ (b.inf < a.inf)
    simp [this] at h2
    aesop
    obtain H | H' : a.inf = b.inf ∨ b.inf < a.inf  := by exact eq_or_lt_of_not_gt h_lt
    swap
    aesop
    simp_all
    observe: a.sup = b.sup
    rw [← @inf_eq_inf_and_sup_eq_sup]
    exact And.symm ⟨this, H⟩
  exact this x y h1 h2


noncomputable instance IsTransSym2Lex (n:ℕ):  IsTrans (Sym2 (Fin n)) lex := by
  refine { trans := ?_ }
  intro a b c hab hbc
  simp_all [lex]
  by_cases abinf: a.inf < b.inf <;> by_cases bcinf: b.inf < c.inf
  · simp_all
    left
    exact Fin.lt_trans abinf bcinf
  · aesop
  · simp_all
  · simp [abinf] at hab
    simp [bcinf] at hbc
    right
    constructor
    aesop
    replace hab:= hab.right
    replace hbc:= hbc.right
    exact Fin.le_trans hab hbc

noncomputable instance IsAntisymmSym2Lex (n:ℕ):  IsAntisymm (Sym2 (Fin n)) lex := by
  refine { antisymm := ?_ }
  exact fun a b a_1 a_2 ↦ ltlt_eq_lex a b a_1 a_2

noncomputable instance IsTotalSym2Lex (n:ℕ):  IsTotal (Sym2 (Fin n)) lex := by
  refine { total := ?_ }
  intro a b
  by_cases h: lex a b
  exact Or.symm (Or.inr h)
  right
  simp [lex] at h
  simp [lex]
  obtain ⟨h1,h2⟩ := h
  by_cases h:b.inf < a.inf
  left
  exact h
  push_neg at h
  right
  constructor
  aesop (add unsafe Fin.le_antisymm)
  have: b.sup < a.sup := by aesop (add unsafe Fin.le_antisymm)
  exact Fin.le_of_lt this

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

import MathlibExtraLean.List
import FormalLanguageLean.Kleene


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://github.com/mn200/CFL-HOL
-- https://arxiv.org/pdf/1509.02032.pdf
-- https://core.ac.uk/download/pdf/156629067.pdf


/-
  The definition of a context free grammar.

  An alphabet Σ is a finite, non-empty set of indivisible symbols.
  A string over an alphabet Σ is a finite sequence of members of Σ.

  N is a non-terminal alphabet.
  T is a terminal alphabet such that N ∩ T = ∅.
  P ⊆ N × (N ∪ T)* is a set of productions.
  S ∈ N is the start symbol.
-/


inductive Symbol (NTS : Type) (TS : Type)
| nts : NTS → Symbol NTS TS
| ts : TS → Symbol NTS TS


def Symbol.isNTS
  {NTS : Type}
  {TS : Type} :
  Symbol NTS TS → Prop
  | nts _ => True
  | ts _ => False

instance
  (NTS : Type)
  (TS : Type)
  (c : Symbol NTS TS) :
  Decidable c.isNTS :=
  by
    cases c
    all_goals
      simp only [Symbol.isNTS]
      infer_instance


def Symbol.isTS
  {NTS : Type}
  {TS : Type} :
  Symbol NTS TS → Prop
  | nts _ => False
  | ts _ => True

instance
  (NTS : Type)
  (TS : Type)
  (c : Symbol NTS TS) :
  Decidable c.isTS :=
  by
    cases c
    all_goals
      simp only [Symbol.isTS]
      infer_instance


def Symbol.getNTS
  (NTS : Type)
  (TS : Type) :
  (c : Symbol NTS TS) → (h1 : c.isNTS) → NTS
  | nts a, _ => a


theorem symbol_is_nts_imp_exists_nts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS)
  (h1 : c.isNTS) :
  ∃ (x : NTS), c = Symbol.nts x :=
  by
    cases c
    case nts x =>
      apply Exists.intro x
      apply Eq.refl
    case ts x =>
      simp only [Symbol.isNTS] at h1


def Symbol.getTS
  (NTS : Type)
  (TS : Type) :
  (c : Symbol NTS TS) → (h1 : c.isTS) → TS
  | ts a, _ => a


theorem symbol_is_ts_imp_exists_ts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS)
  (h1 : c.isTS) :
  ∃ (x : TS), c = Symbol.ts x :=
  by
    cases c
    case nts x =>
      simp only [Symbol.isTS] at h1
    case ts x =>
      apply Exists.intro x
      apply Eq.refl


theorem symbol_not_nts_iff_is_ts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS) :
  ¬ c.isNTS ↔ c.isTS :=
  by
    cases c
    case nts x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      exact not_true
    case _ x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      exact not_false_iff


theorem symbol_not_ts_iff_is_nts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS) :
  ¬ c.isTS ↔ c.isNTS :=
  by
    cases c
    case nts x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      exact not_false_iff
    case ts x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      exact not_true


structure Rule (NTS : Type) (TS : Type) where
  (lhs : NTS)
  (rhs : Str (Symbol NTS TS))


def Rule.isEpsilonRule
  {NTS : Type}
  {TS : Type}
  (P : Rule NTS TS) :
  Prop :=
  P.rhs = []


structure CFG (NTS : Type) (TS : Type) where
  (rule_list : List (Rule NTS TS))
  (start_symbol : NTS)


/--
  is_derivation_step G lsl rsl := lsl =>G rsl
-/
def is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


def is_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


def is_rightmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      (∀ (c : Symbol NTS TS), c ∈ sl_2 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


inductive is_derivation_alt
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop
| refl
  (sl : Str (Symbol NTS TS)) :
  is_derivation_alt G sl sl

| trans
  (sl_1 sl_2 sl_3 : Str (Symbol NTS TS)) :
  is_derivation_alt G sl_1 sl_2 →
  is_derivation_step G sl_2 sl_3 →
  is_derivation_alt G sl_1 sl_3


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  is_derivation_alt G = Relation.ReflTransGen (is_derivation_step G) :=
  by
    ext lsl rsl
    constructor
    · intro a1
      induction a1
      case refl =>
        exact Relation.ReflTransGen.refl
      case trans sl_1 sl_2 ih_1 ih_2 ih_3 =>
        exact Relation.ReflTransGen.tail ih_3 ih_2
    · intro a1
      induction a1
      case refl =>
        exact is_derivation_alt.refl lsl
      case tail sl_1 sl_2 ih_1 ih_2 ih_3 =>
        exact is_derivation_alt.trans lsl sl_1 sl_2 ih_3 ih_2


def CFG.LanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language TS :=
  { s : Str TS | Relation.ReflTransGen (is_derivation_step G) [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.LeftLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language TS :=
  { s : Str TS | Relation.ReflTransGen (is_leftmost_derivation_step G) [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.RightLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language TS :=
  { s : Str TS | Relation.ReflTransGen (is_rightmost_derivation_step G) [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


theorem is_derivation_step_same_append_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : is_derivation_step G u v) :
  is_derivation_step G (x ++ u) (x ++ v) :=
  by
    unfold is_derivation_step at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩⟩⟩⟩ := h1

    rewrite [h1_right_left]
    rewrite [h1_right_right]
    unfold is_derivation_step
    apply Exists.intro R
    apply Exists.intro (x ++ sl_1)
    apply Exists.intro sl_2
    constructor
    · exact h1_left
    · constructor
      · simp only [List.append_assoc, List.cons_append, List.nil_append]
      · simp only [List.append_assoc]


theorem is_derivation_step_same_append_right
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : is_derivation_step G u v) :
  is_derivation_step G (u ++ x) (v ++ x) :=
  by
    unfold is_derivation_step at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩⟩⟩⟩ := h1

    rewrite [h1_right_left]
    rewrite [h1_right_right]
    unfold is_derivation_step
    apply Exists.intro R
    apply Exists.intro sl_1
    apply Exists.intro (sl_2 ++ x)
    constructor
    · exact h1_left
    · constructor
      · simp only [List.append_assoc, List.cons_append, List.nil_append]
      · simp only [List.append_assoc]


theorem rtc_is_derivation_step_same_append_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : Relation.ReflTransGen (is_derivation_step G) u v) :
  Relation.ReflTransGen (is_derivation_step G) (x ++ u) (x ++ v) :=
  by
    induction h1 using Relation.ReflTransGen.head_induction_on
    case refl =>
      exact Relation.ReflTransGen.refl
    case head a b ih_1 ih_2 ih_3 =>
      apply Relation.ReflTransGen.head
      · exact is_derivation_step_same_append_left G a b x ih_1
      · exact ih_3


theorem rtc_is_derivation_step_same_append_right
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : Relation.ReflTransGen (is_derivation_step G) u v) :
  Relation.ReflTransGen (is_derivation_step G) (u ++ x) (v ++ x) :=
  by
    induction h1 using Relation.ReflTransGen.head_induction_on
    case refl =>
      exact Relation.ReflTransGen.refl
    case head a b ih_1 ih_2 ih_3 =>
      apply Relation.ReflTransGen.head
      · exact is_derivation_step_same_append_right G a b x ih_1
      · exact ih_3


theorem derives_append
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (M N P Q : Str (Symbol NTS TS))
  (h1 : Relation.ReflTransGen (is_derivation_step G) M N)
  (h2 : Relation.ReflTransGen (is_derivation_step G) P Q) :
  Relation.ReflTransGen (is_derivation_step G) (M ++ P) (N ++ Q) :=
  by
    -- (M ++ P) (N ++ P) ; (N ++ P) (N ++ Q)

    have s1 : Relation.ReflTransGen (is_derivation_step G) (M ++ P) (N ++ P) :=
    by
      apply rtc_is_derivation_step_same_append_right
      exact h1

    have s2 : Relation.ReflTransGen (is_derivation_step G) (N ++ P) (N ++ Q) :=
    by
      apply rtc_is_derivation_step_same_append_left
      exact h2

    exact Relation.ReflTransGen.trans s1 s2


theorem res1
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lhs : NTS)
  (rhs : Str (Symbol NTS TS))
  (h1 : ⟨lhs, rhs⟩ ∈ G.rule_list) :
  is_derivation_step G [Symbol.nts lhs] rhs :=
  by
    unfold is_derivation_step
    apply Exists.intro ⟨lhs, rhs⟩
    apply Exists.intro []
    apply Exists.intro []
    constructor
    · exact h1
    · constructor
      · simp only [List.nil_append, List.append_nil]
      · simp only [List.nil_append, List.append_nil]


theorem res2
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (a b c : Str (Symbol NTS TS))
  (h1 : is_derivation_step G a b)
  (h2 : is_derivation_step G b c) :
  Relation.ReflTransGen (is_derivation_step G) a c :=
  by
    apply Relation.ReflTransGen.head h1
    apply Relation.ReflTransGen.head h2
    exact Relation.ReflTransGen.refl


theorem res3
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (a b c : Str (Symbol NTS TS))
  (h1 : is_derivation_step G a b)
  (h2 : Relation.ReflTransGen (is_derivation_step G) b c) :
  Relation.ReflTransGen (is_derivation_step G) a c :=
  by
    apply Relation.ReflTransGen.head h1
    exact h2


theorem slres
  {NTS : Type}
  {TS : Type}
  (lhs s : NTS)
  (sl_1 sl_2 : Str (Symbol NTS TS))
  (h1 : sl_1 ++ [Symbol.nts lhs] ++ sl_2 = [Symbol.nts s]) :
  lhs = s :=
  by
    cases sl_1
    case nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq, Symbol.nts.injEq] at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      exact h1_left
    case cons hd tl =>
      simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq, List.append_eq_nil_iff, reduceCtorEq] at h1
      obtain ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩ := h1
      contradiction


theorem slres2
  {NTS : Type}
  {TS : Type}
  (lhs s : NTS)
  (sl_1 sl_2 : Str (Symbol NTS TS))
  (h1 : sl_1 ++ [Symbol.nts lhs] ++ sl_2 = [Symbol.nts s]) :
  (sl_1 = []) ∧ (sl_2 = []) :=
  by
    cases sl_1
    case nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq, Symbol.nts.injEq] at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      exact ⟨rfl, h1_right⟩
    case cons hd tl =>
      simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq, List.append_eq_nil_iff, reduceCtorEq] at h1
      obtain ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩ := h1
      contradiction


theorem rgr_r8
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sym : Symbol NTS TS)
  (r r1 r2 : Str (Symbol NTS TS))
  (l : NTS)
  (h1 : r = r1 ++ [sym] ++ r2)
  (h2 : is_derivation_step G [Symbol.nts l] r) :
  ∃ (a b : Str (Symbol NTS TS)), is_derivation_step G [Symbol.nts l] (a ++ [sym] ++ b) :=
  by
    apply Exists.intro r1
    apply Exists.intro r2
    rewrite [h1] at h2
    exact h2


theorem upgr_r11
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lhs rhs : NTS)
  (h1 : is_derivation_step G [Symbol.nts lhs] [Symbol.nts rhs]) :
  ⟨lhs, [Symbol.nts rhs]⟩ ∈ G.rule_list :=
  by
    unfold is_derivation_step at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩⟩⟩⟩ := h1
    sorry


-------------------------------------------------------------------------------


theorem leftmost_derivation_step_is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_leftmost_derivation_step G lsl rsl) :
  is_derivation_step G lsl rsl :=
  by
    unfold is_leftmost_derivation_step at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_left, ⟨h1_right_left, ⟨h1_right_right_left, h1_right_right_right⟩⟩⟩⟩⟩⟩ := h1

    unfold is_derivation_step
    exact ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_right_left, ⟨h1_right_right_left, h1_right_right_right⟩⟩⟩⟩⟩


theorem rightmost_derivation_step_is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_rightmost_derivation_step G lsl rsl) :
  is_derivation_step G lsl rsl :=
  by
    unfold is_rightmost_derivation_step at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_left, ⟨h1_right_left, ⟨h1_right_right_left, h1_right_right_right⟩⟩⟩⟩⟩⟩ := h1

    unfold is_derivation_step
    exact ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_right_left, ⟨h1_right_right_left, h1_right_right_right⟩⟩⟩⟩⟩


theorem derivation_step_to_terminal_string_is_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sl s : Str (Symbol NTS TS))
  (h1 : is_derivation_step G sl s)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ s → c.isTS) :
  is_leftmost_derivation_step G sl s :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩⟩⟩⟩ := h1

    rewrite [h1_right_right] at h2
    have s1 : ∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS :=
    by
      intro c a1
      apply h2 c
      simp only [List.append_assoc, List.mem_append]
      left
      exact a1

    unfold is_leftmost_derivation_step
    exact ⟨R, ⟨sl_1, ⟨sl_2, ⟨s1, ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩⟩⟩⟩⟩


theorem derivation_step_to_terminal_string_is_rightmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sl s : Str (Symbol NTS TS))
  (h1 : is_derivation_step G sl s)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ s → c.isTS) :
  is_rightmost_derivation_step G sl s :=
  by
    unfold is_derivation_step at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩⟩⟩⟩ := h1

    rewrite [h1_right_right] at h2

    have s1 : ∀ (c : Symbol NTS TS), c ∈ sl_2 → c.isTS :=
    by
      intro c a1
      apply h2 c
      simp only [List.append_assoc, List.mem_append]
      right
      right
      exact a1

    unfold is_rightmost_derivation_step
    exact ⟨R, ⟨sl_1, ⟨sl_2, ⟨s1, ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩⟩⟩⟩⟩


theorem exists_nts_imp_exists_leftmost_nts
  {NTS : Type}
  {TS : Type}
  (sl : Str (Symbol NTS TS))
  (h1 : ∃ (c : Symbol NTS TS), c ∈ sl ∧ c.isNTS) :
  ∃
    (sl_1 : Str (Symbol NTS TS))
    (A : NTS)
    (sl_2 : Str (Symbol NTS TS)),
    (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
    sl = sl_1 ++ [Symbol.nts A] ++ sl_2 :=
  by
    obtain s1 := List.exists_mem_imp_exists_leftmost_mem sl (Symbol.isNTS) h1
    obtain ⟨sl_1, ⟨A, ⟨sl_2, ⟨s1_left, ⟨s1_right_left, s1_right_right⟩⟩⟩⟩⟩ := s1

    obtain s2 := symbol_is_nts_imp_exists_nts A s1_right_left
    obtain ⟨x, s2⟩ := s2
    apply Exists.intro sl_1
    apply Exists.intro x
    apply Exists.intro sl_2
    constructor
    · intro c a1
      rewrite [← symbol_not_nts_iff_is_ts]
      apply s1_right_right
      exact a1
    · rewrite [s2] at s1_left
      exact s1_left


theorem exists_nts_imp_exists_rightmost_nts
  {NTS : Type}
  {TS : Type}
  (sl : Str (Symbol NTS TS))
  (h1 : ∃ (c : Symbol NTS TS), c ∈ sl ∧ c.isNTS) :
  ∃
    (sl_1 : Str (Symbol NTS TS))
    (A : NTS)
    (sl_2 : Str (Symbol NTS TS)),
    (∀ (c : Symbol NTS TS), c ∈ sl_2 → c.isTS) ∧
    sl = sl_1 ++ [Symbol.nts A] ++ sl_2 :=
  by
    obtain s1 := List.exists_mem_imp_exists_rightmost_mem sl (Symbol.isNTS) h1
    obtain ⟨sl_1, ⟨A, ⟨sl_2, ⟨s1_left, ⟨s1_right_left, s1_right_right⟩⟩⟩⟩⟩ := s1

    obtain s2 := symbol_is_nts_imp_exists_nts A s1_right_left
    obtain ⟨x, s2⟩ := s2
    apply Exists.intro sl_1
    apply Exists.intro x
    apply Exists.intro sl_2
    constructor
    · intro c a1
      rewrite [← symbol_not_nts_iff_is_ts]
      apply s1_right_right
      exact a1
    · rewrite [s2] at s1_left
      exact s1_left


theorem is_derivation_step_and_is_not_leftmost_derivation_step_aux
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_derivation_step G lsl rsl)
  (h2 : ¬ is_leftmost_derivation_step G lsl rsl) :
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      ¬ (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2 :=
  by
    unfold is_derivation_step at h1
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1
    obtain ⟨R, ⟨sl_1, ⟨sl_2, h1⟩⟩⟩ := h1

    unfold is_leftmost_derivation_step at h2
    simp only [List.append_assoc, List.cons_append, List.nil_append, not_exists] at h2
    specialize h2 R sl_1

    apply Exists.intro R
    apply Exists.intro sl_1
    apply Exists.intro sl_2
    constructor
    · intro contra
      specialize h2 sl_2
      rewrite [not_and'] at h2
      apply h2
      · exact h1
      · exact contra
    · simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact h1


theorem is_derivation_step_and_is_not_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_derivation_step G lsl rsl)
  (h2 : ¬ is_leftmost_derivation_step G lsl rsl) :
  ∃
    (sl_1 sl_2 sl_3 sl_4 : Str (Symbol NTS TS))
    (A B : NTS),
    (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
    ⟨B, sl_3⟩ ∈ G.rule_list ∧
    lsl = sl_1 ++ [Symbol.nts A] ++ sl_2 ++ [Symbol.nts B] ++ sl_4 ∧
    rsl = sl_1 ++ [Symbol.nts A] ++ sl_2 ++ sl_3 ++ sl_4 :=
  by
    obtain s1 := is_derivation_step_and_is_not_leftmost_derivation_step_aux G lsl rsl h1 h2
    obtain ⟨R, ⟨sl_1, ⟨sl_2, ⟨s1_left, ⟨s1_right_left, ⟨s1_right_right_left, s1_right_right_right⟩⟩⟩⟩⟩⟩ := s1
    rewrite [s1_right_right_left]
    rewrite [s1_right_right_right]

    simp only [not_forall] at s1_left
    simp only [exists_prop] at s1_left
    simp only [symbol_not_ts_iff_is_nts] at s1_left

    obtain s2 := exists_nts_imp_exists_leftmost_nts sl_1 s1_left
    obtain ⟨sl_3, A, sl_4, ⟨s2_left, s2_right⟩⟩ := s2
    rewrite [s2_right]

    exact ⟨sl_3, ⟨sl_4, ⟨R.rhs, ⟨sl_2, ⟨A, ⟨R.lhs, ⟨s2_left, ⟨s1_right_left, ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩


theorem extracted_1
  {NTS TS : Type}
  (G : CFG NTS TS)
  (w : Str (Symbol NTS TS))
  {alpha_1 : Str (Symbol NTS TS)}
  (u mu delta rho : Str (Symbol NTS TS))
  (A : NTS)
  (h1 : Relation.TransGen (is_leftmost_derivation_step G) alpha_1 w)
  (h2 : ∀ c ∈ u, c.isTS)
  (h3 : alpha_1 = u ++ [Symbol.nts A] ++ mu ++ delta ++ rho) :
  ∃ gamma,
    { lhs := A, rhs := gamma } ∈ G.rule_list ∧
     Relation.TransGen (is_leftmost_derivation_step G) (u ++ gamma ++ mu ++ delta ++ rho) w :=
  by
    sorry


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl w : Str (Symbol NTS TS))
  (h1 : Relation.TransGen (is_derivation_step G) lsl w)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ w → c.isTS) :
  Relation.TransGen (is_leftmost_derivation_step G) lsl w :=
  by
    induction h1 using Relation.TransGen.head_induction_on
    case single sl ih =>
      apply Relation.TransGen.single
      apply derivation_step_to_terminal_string_is_leftmost_derivation_step
      · exact ih
      · exact h2
    case head alpha alpha_1 ih_1 ih_2 ih_3 =>
      by_cases c1 : is_leftmost_derivation_step G alpha alpha_1
      · apply Relation.TransGen.trans
        · exact Relation.TransGen.single c1
        · exact ih_3
      · obtain s1 := is_derivation_step_and_is_not_leftmost_derivation_step G alpha alpha_1 ih_1 c1
        obtain ⟨u, ⟨mu, ⟨delta, ⟨rho, ⟨A, ⟨B, ⟨s1_left, ⟨s1_right_left, ⟨s1_right_right_left, s1_right_right_right⟩⟩⟩⟩⟩⟩⟩⟩⟩ := s1

        sorry

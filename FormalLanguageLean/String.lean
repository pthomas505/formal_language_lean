import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577



/-
  Definition 1 (Alphabet). An alphabet is any, possibly infinite, set of symbols. We will use Σ to denote an alphabet with a non-empty, finite set of symbols.

  Definition 2 (String). A string s over some alphabet Σ is a, possibly infinite, sequence of symbols s = a₁a₂...aᵢ..., with aᵢ ∈ Σ. We note the special case of a string with no symbols, called the empty string, and denote it by ε.
-/

/-
  This formalization uses the symbol α instead of Σ since Σ is reserved in Lean.
-/


/--
  The type of finite strings over the alphabet `α`.
-/
abbrev Str (α : Type) : Type := List α


namespace String


/-
Definition 3 (Exponentiation). For an alphabet Σ we define the exponenti-
ation, or powers of Σ by
1. Σ^{0} = {ε}
2. Σ^{n+1} = Σ^{n}Σ = {sa : s ∈ Σ^{n}, a ∈ Σ} n ∈ N
-/

/--
  `exp α n` := The set of all strings of length `n` over the alphabet `α`.
-/
inductive exp (α : Type) : ℕ → Set (Str α)
  | zero : exp α 0 []
  | succ
    (n : ℕ)
    (a : α)
    (s : Str α) :
    s ∈ exp α n →
    exp α (n + 1) (s ++ [a])


example
  (α : Type)
  (n : ℕ)
  (a : α)
  (s : Str α)
  (h1 : s ∈ exp α n) :
  a :: s ∈ exp α (n + 1) :=
  by
    induction h1
    case zero =>
      have s1 : [a] = [] ++ [a] := rfl
      rw [s1]
      apply exp.succ
      exact exp.zero
    case succ n' a' s' _ ih_2 =>
      have s1 : a :: (s' ++ [a']) = (a :: s') ++ [a'] := rfl
      rw [s1]
      apply exp.succ
      exact ih_2


example : [] ∈ exp Char 0 :=
  by
    exact exp.zero

example : ['a'] ∈ exp Char 1 :=
  by
    apply exp.succ 0 'a' []
    exact exp.zero

example : ['a', 'b'] ∈ exp Char 2 :=
  by
    apply exp.succ 1 'b' ['a']
    apply exp.succ 0 'a' []
    exact exp.zero


/-
Definition 4 (String length). Let s ∈ Σ^n be a string. We say that the length of s is n, written |s| = n, and hence the length is the number of consecutive symbols. As a special case we have |ε| = 0.
-/


theorem str_append_length_left
  {α : Type}
  (s t : Str α)
  (h1 : ¬ s = []) :
  t.length < (s ++ t).length :=
  by
    simp only [List.length_append, Nat.lt_add_left_iff_pos]
    simp only [List.length_pos_iff]
    exact h1


theorem str_append_length_right
  {α : Type}
  (s t : Str α)
  (h1 : ¬ t = []) :
  s.length < (s ++ t).length :=
  by
    simp only [List.length_append, Nat.lt_add_right_iff_pos]
    simp only [List.length_pos_iff]
    exact h1


lemma str_reverse_mem_exp_length
  {α : Type}
  (s : Str α) :
  s.reverse ∈ exp α s.length :=
  by
    induction s
    case nil =>
      simp only [List.length_nil, List.reverse_nil]
      exact exp.zero
    case cons hd tl ih =>
      simp only [List.length_cons, List.reverse_cons]
      apply exp.succ
      exact ih


theorem str_mem_exp_length
  {α : Type}
  (s : Str α) :
  s ∈ exp α s.length :=
  by
    obtain s1 := str_reverse_mem_exp_length s.reverse
    simp only [List.length_reverse, List.reverse_reverse] at s1
    exact s1


theorem str_mem_exp_length_eq
  {α : Type}
  (s : Str α)
  (n : ℕ)
  (h1 : s ∈ exp α n) :
  s.length = n :=
  by
    induction h1
    case zero =>
      simp only [List.length_nil]
    case succ k c t ih_1 ih_2 =>
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      rewrite [ih_2]
      rfl

/--
  `exp_set α n` := The set of all strings of length `n` over the alphabet `α`.
-/
def exp_set
  (α : Type)
  (n : ℕ) :
  Set (Str α) :=
  {s : Str α | s.length = n}


theorem exp_eq_exp_set
  (α : Type)
  (n : ℕ) :
  exp α n = exp_set α n :=
  by
    unfold exp_set
    ext cs
    simp only [Set.mem_setOf_eq]
    constructor
    · intro a1
      apply str_mem_exp_length_eq
      exact a1
    · intro a1
      simp only [← a1]
      apply str_mem_exp_length


/-
Definition 5 (Kleene closure). Let Σ be an alphabet, then we denote the set of all finite strings over Σ by Σ∗.
-/

/--
  `kleene_closure α` := The set of all finite strings over the alphabet `α`.
-/
def kleene_closure
  (α : Type) :
  Set (Str α) :=
  ⋃ (n : ℕ), exp α n


theorem str_mem_kleene_closure
  {α : Type}
  (s : Str α) :
  s ∈ kleene_closure α :=
  by
    unfold kleene_closure
    simp only [Set.mem_iUnion]
    apply Exists.intro s.length
    apply str_mem_exp_length


theorem kleene_closure_eq_univ
  (α : Type) :
  kleene_closure α = Set.univ :=
  by
    ext cs
    constructor
    · simp only [Set.mem_univ]
      intro a1
      exact trivial
    · simp only [Set.mem_univ]
      intro a1
      apply str_mem_kleene_closure


/-
Definition 6 (Concatenation). Suppose that s ∈ Σ^m and t ∈ Σ^n are strings over some alphabet. The concatenation of s and t written s · t or st, is the string formed by letting the sequence of symbols in s be followed by the sequence of symbols in t, i.e. s · t = a1a2...am · b1b2...bn = a1a2...amb1b2...bn = st ∈ Σ^(m+n)
-/

example
  (α : Type)
  (s t : Str α)
  (m n : ℕ)
  (h1 : s.length = m)
  (h2 : t.length = n) :
  s ++ t ∈ exp α (m + n) :=
  by
    simp only [← h1]
    simp only [← h2]
    simp only [← List.length_append]
    apply str_mem_exp_length


example
  (α : Type)
  (s t : Str α) :
  s ++ t ∈ kleene_closure α :=
  by
    apply str_mem_kleene_closure


theorem str_append_assoc
  (α : Type)
  (s t u : Str α) :
  s ++ (t ++ u) = (s ++ t) ++ u :=
  by
    simp only [List.append_assoc]


/-
Definition 7. (Substring) Suppose that s, t, u, v are strings such that s = tuv, then u is called a substring of s. Further, if at least one of t and v is not ε then u is called a proper substring of s.
-/
/--
  `is_substring_of α s u` := True if and only if the string `u` is a substring of the string `s`.
-/
def is_substring_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t v : Str α), s = t ++ u ++ v


/--
  `is_proper_substring_of α s u` := True if and only if the string `u` is a proper substring of the string `s`.
-/
def is_proper_substring_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t v : Str α), s = t ++ u ++ v ∧ (¬ t.isEmpty ∨ ¬ v.isEmpty)


/-
Definition 8. (Prefix) Suppose that s, t, u are strings such that s = tu, then t is called a prefix of s. Further, t is called a proper prefix of s if u ≠ ε.
-/
/--
  `is_prefix_of α s t` := True if and only if the string `t` is a prefix of the string `s`.
-/
def is_prefix_of
  (α : Type)
  (s t : Str α) :
  Prop :=
  ∃ (u : Str α), s = t ++ u


/--
  `is_proper_prefix_of α s t` := True if and only if the string `t` is a proper prefix of the string `s`.
-/
def is_proper_prefix_of
  (α : Type)
  (s t : Str α) :
  Prop :=
  ∃ (u : Str α), s = t ++ u ∧ ¬ u.isEmpty


/-
Definition 9. (Suffix) Suppose that s, t, u are strings such that s = tu, then u is called a suffix of s. Further, u is called a proper suffix of s if t ≠ ε.
-/
/--
  `is_suffix_of α s u` := True if and only if the string `u` is a suffix of the string `s`.
-/
def is_suffix_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t : Str α), s = t ++ u


/--
  `is_proper_suffix_of α s u` := True if and only if the string `u` is a proper suffix of the string `s`.
-/
def is_proper_suffix_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t : Str α), s = t ++ u ∧ ¬ t.isEmpty


#lint

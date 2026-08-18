import FormalLanguageLean.Concat


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577


namespace Language


/-
Definition 12 (Exponentiation). Let L be a language. The exponentiation or powers of L is defined by
1. L^0 = {ε}
2. L^(n+1) = L^(n)L n ∈ N
-/
/--
  `exp L n` := The language `L` to the power `n`.
-/
def exp
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  Language α :=
  match n with
  | 0 => {[]}
  | n + 1 => concat (exp L n) L


/--
  `exp_list L n` := The list of strings `L` to the power `n` defined such that `exp L.toFinset.toSet n = (exp_list L n).toFinset.toSet`.
-/
def exp_list
  {α : Type}
  (L : List (Str α))
  (n : ℕ) :
  List (Str α) :=
  match n with
  | 0 => [[]]
  | n + 1 => concat_list (exp_list L n) L


theorem exp_eq_exp_list
  {α : Type}
  [DecidableEq α]
  (L : List (Str α))
  (n : ℕ) :
  exp (L.toFinset : Set (Str α)) n =
    ((exp_list L n).toFinset : Set (Str α)) :=
  by
    induction n
    case zero =>
      unfold exp
      unfold exp_list
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.coe_singleton]
    case succ k ih =>
      unfold exp
      unfold exp_list
      rewrite [ih]
      apply concat_eq_concat_list


/--
  `exp_list_finite_union L n` := L^0 ++ ... ++ L^n.
-/
def exp_list_finite_union
  {α : Type}
  (L : List (Str α))
  (n : ℕ) :
  List (Str α) :=
  match n with
  | 0 => exp_list L 0
  | k + 1 => exp_list_finite_union L k ++ exp_list L (k + 1)


example
  {α : Type}
  (L : List (Str α)) :
  exp_list_finite_union L 1 =
    exp_list L 0 ++ exp_list L 1 := by apply Eq.refl


example
  {α : Type}
  [DecidableEq α]
  (L : List (Str α))
  (n : ℕ) :
  ⋃ (k ≤ n), exp (L.toFinset : Set (Str α)) k =
    ((exp_list_finite_union L n).toFinset : Set (Str α)) :=
  by
    simp only [List.coe_toFinset]
    induction n
    case zero =>
      unfold exp_list_finite_union
      simp only [Nat.le_zero_eq, Set.iUnion_iUnion_eq_left]

      obtain s1 := exp_eq_exp_list L 0
      simp only [List.coe_toFinset] at s1

      exact s1
    case succ k ih =>
      unfold exp_list_finite_union
      simp only [Set.biUnion_le_succ]
      rewrite [ih]
      simp only [List.mem_append]

      obtain s1 := exp_eq_exp_list L (k + 1)
      simp only [List.coe_toFinset] at s1
      rewrite [s1]
      exact Set.union_def


theorem exp_zero
  {α : Type}
  (L : Language α) :
  exp L 0 = {[]} := by apply Eq.refl


theorem exp_one
  {α : Type}
  (L : Language α) :
  exp L 1 = L :=
  by
    simp only [exp]
    simp only [concat]
    simp only [Set.mem_singleton_iff, exists_eq_left, List.nil_append, exists_eq_right, Set.setOf_mem_eq]


theorem exp_succ_concat_right
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat (exp L n) L := by apply Eq.refl


-------------------------------------------------------------------------------


example
  {α : Type}
  (n : ℕ)
  (h1 : ¬ n = 0) :
  exp (∅ : Language α) n = ∅ :=
  by
    cases n
    case zero =>
      contradiction
    case succ k =>
      unfold exp
      apply concat_empty_right


-------------------------------------------------------------------------------


theorem nonempty_exp_nonempty
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : L.Nonempty) :
  (exp L n).Nonempty :=
  by
    induction n
    case zero =>
      unfold Set.Nonempty
      unfold exp
      apply Exists.intro []
      apply Set.mem_singleton
    case succ k ih =>
      unfold exp
      rewrite [concat_nonempty_iff]
      exact ⟨ih, h1⟩


theorem exp_succ_nonempty_nonempty
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : (exp L (n + 1)).Nonempty) :
  Set.Nonempty (exp L n) ∧ Set.Nonempty L :=
  by
    unfold exp at h1
    rewrite [concat_nonempty_iff] at h1
    exact h1


-------------------------------------------------------------------------------


theorem eps_mem_eps_mem_exp
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : [] ∈ L) :
  [] ∈ exp L n :=
  by
    induction n
    case zero =>
      unfold exp
      apply Set.mem_singleton
    case succ k ih =>
      unfold exp
      rewrite [eps_mem_concat_iff]
      exact ⟨ih, h1⟩


theorem eps_mem_exp_succ_eps_mem
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : [] ∈ exp L (n + 1)) :
  [] ∈ exp L n ∧ [] ∈ L :=
  by
    unfold exp at h1
    rewrite [eps_mem_concat_iff] at h1
    exact h1


-------------------------------------------------------------------------------


theorem concat_exp_comm
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  concat (exp L n) L = concat L (exp L n) :=
  by
    induction n
    case zero =>
      unfold exp
      unfold concat
      simp only [Set.mem_singleton_iff, exists_eq_left, List.nil_append, exists_eq_right, Set.setOf_mem_eq, List.append_nil]
    case succ k ih =>
      unfold exp
      rewrite [concat_assoc]
      rewrite [ih]
      apply Eq.refl


theorem exp_succ_concat_left
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat L (exp L n) :=
  by
    simp only [exp]
    apply concat_exp_comm


theorem concat_exp_assoc
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  concat (exp L (m + 1)) (exp L n) = concat (exp L m) (exp L (n + 1)) :=
  by
    simp only [exp]
    rewrite [← concat_assoc]
    rewrite [concat_exp_comm]
    apply Eq.refl


theorem concat_exp_sum
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  concat (exp L m) (exp L n) = exp L (m + n) :=
  by
    induction m generalizing n
    case zero =>
      simp only [exp]
      simp only [zero_add]
      apply concat_eps_left
    case succ k ih =>
      rewrite [concat_exp_assoc]
      rewrite [Nat.succ_add_eq_add_succ]
      apply ih


theorem concat_exp_exp_comm
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  concat (exp L m) (exp L n) = concat (exp L n) (exp L m) :=
  by
    simp only [concat_exp_sum]
    rewrite [Nat.add_comm m n]
    apply Eq.refl


-------------------------------------------------------------------------------


theorem append_exp_sum
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (m n : ℕ)
  (h1 : s ∈ exp L m)
  (h2 : t ∈ exp L n) :
  s ++ t ∈ exp L (m + n) :=
  by
    obtain s1 := concat_exp_sum L m n
    rewrite [← s1]
    apply append_mem_concat
    · exact h1
    · exact h2


theorem append_mem_exp_left
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ exp L n)
  (h2 : t ∈ L) :
  s ++ t ∈ exp L (n + 1) :=
  by
    apply append_exp_sum
    · exact h1
    · rewrite [exp_one]
      exact h2


theorem append_mem_exp_right
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ L)
  (h2 : t ∈ exp L n) :
  s ++ t ∈ exp L (n + 1) :=
  by
    rewrite [Nat.add_comm]
    apply append_exp_sum
    · rewrite [exp_one]
      exact h1
    · exact h2


theorem eps_mem_exp_subset_exp_add_nat
  {α : Type}
  (L : Language α)
  (m n : ℕ)
  (h1 : [] ∈ L) :
  exp L m ⊆ exp L (m + n) :=
  by
    obtain s1 := concat_exp_sum L m n
    rewrite [← s1]

    apply eps_mem_right_left_subset_concat
    apply eps_mem_eps_mem_exp
    exact h1


-------------------------------------------------------------------------------


theorem concat_exp_comm_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  concat (⋃ (k ≤ n), exp L k) L = concat L (⋃ (k ≤ n), exp L k) :=
  by
    induction n
    case zero =>
      simp only [Nat.le_zero_eq, Set.iUnion_iUnion_eq_left]
      unfold exp
      unfold concat
      simp only [Set.mem_singleton_iff, exists_eq_left, List.nil_append, exists_eq_right, Set.setOf_mem_eq, List.append_nil]
    case succ i ih =>
      simp only [Set.biUnion_le_succ (exp L)]
      rewrite [concat_distrib_union_right]
      rewrite [concat_distrib_union_left]
      rewrite [ih]
      rewrite [concat_exp_comm]
      apply Eq.refl


theorem exp_succ_concat_right_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  ⋃ (k ≤ n), exp L (k + 1) =
    concat (⋃ (k ≤ n), exp L k) L :=
  by
    ext cs
    constructor
    · intro a1
      unfold exp at a1
      unfold concat at a1
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at a1
      obtain ⟨i, hi, s, hs, t, ht, eq⟩ := a1

      unfold concat
      simp only [Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
      exact ⟨s, ⟨i, ⟨hi, hs⟩ ⟩, ⟨t, ht, eq⟩⟩
    · intro a1
      unfold concat at a1
      simp only [Set.mem_iUnion, exists_prop, Set.mem_setOf_eq] at a1
      obtain ⟨s, ⟨i, hi, hs⟩, t, ht, eq⟩ := a1
      unfold exp
      unfold concat
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      exact ⟨i, hi, s, hs, t, ht, eq⟩


theorem exp_succ_concat_left_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  (⋃ (k ≤ n), exp L (k + 1)) =
    concat L (⋃ (k ≤ n), exp L k) :=
  by
    rewrite [← concat_exp_comm_union]
    apply exp_succ_concat_right_union


example
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ ⋃ (k ≤ n), exp L k)
  (h2 : t ∈ L) :
  s ++ t ∈ ⋃ (k ≤ n), exp L (k + 1) :=
  by
    simp only [Set.mem_iUnion, exists_prop] at h1
    obtain ⟨i, hi, hs⟩ := h1

    simp only [Set.mem_iUnion]
    apply Exists.intro i
    apply Exists.intro hi
    apply append_mem_exp_left
    · exact hs
    · exact h2


example
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ L)
  (h2 : t ∈ ⋃ (k ≤ n), exp L k) :
  s ++ t ∈ ⋃ (k ≤ n), exp L (k + 1) :=
  by
    rewrite [exp_succ_concat_right_union]
    rewrite [concat_exp_comm_union]
    apply append_mem_concat
    · exact h1
    · exact h2


example
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (m n : ℕ)
  (h1 : s ∈ ⋃ (k ≤ m), exp L k)
  (h2 : t ∈ ⋃ (k ≤ n), exp L k) :
  s ++ t ∈ ⋃ (k ≤ m + n), exp L k :=
  by
    cases m
    case zero =>
      simp only [Nat.le_zero_eq, Set.iUnion_iUnion_eq_left] at h1
      unfold exp at h1
      simp only [Set.mem_singleton_iff] at h1

      simp only [Set.mem_iUnion, exists_prop] at h2

      rewrite [h1]
      simp only [zero_add, List.nil_append, Set.mem_iUnion, exists_prop]
      exact h2
    case succ k =>
      simp only [Set.mem_iUnion, exists_prop] at h1
      obtain ⟨i, hi, hs⟩ := h1

      simp only [Set.mem_iUnion, exists_prop] at h2
      obtain ⟨j, hj, ht⟩ := h2

      simp only [Set.mem_iUnion, exists_prop]
      apply Exists.intro (i + j)
      constructor
      · exact Nat.add_le_add hi hj
      · apply append_exp_sum
        · exact hs
        · exact ht


example
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  ⋃ (k ≤ m), exp L k ⊆ ⋃ (k ≤ m + n), exp L k :=
  by
    simp only [Set.iUnion_subset_iff]
    intro k a1
    simp only [Set.subset_def]
    intro cs a2
    simp only [Set.mem_iUnion, exists_prop]
    apply Exists.intro k
    constructor
    · exact Nat.le_add_right_of_le a1
    · exact a2


example
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  [] ∈ ⋃ (k ≤ n), exp L k :=
  by
    induction n
    case zero =>
      simp only [Nat.le_zero_eq, Set.iUnion_iUnion_eq_left]
      unfold exp
      apply Set.mem_singleton
    case succ k ih =>
      simp only [Set.mem_iUnion, exists_prop] at ih
      obtain ⟨i, hi, a1⟩ := ih

      simp only [Set.mem_iUnion, exists_prop]
      apply Exists.intro i
      constructor
      · exact Nat.le_add_right_of_le hi
      · exact a1


-------------------------------------------------------------------------------


theorem eps_not_mem_imp_mem_len_ge_exp
  {α : Type}
  (L : Language α)
  (s : Str α)
  (n : ℕ)
  (h1 : [] ∉ L)
  (h2 : s ∈ exp L (n + 1)) :
  s.length > n :=
  by
    induction n generalizing s
    case zero =>
      simp only [exp] at h2
      unfold concat at h2
      simp only [Set.mem_singleton_iff, exists_eq_left, List.nil_append, exists_eq_right, Set.setOf_mem_eq] at h2

      exact eps_not_mem_str_length_gt_zero L s h1 h2
    case succ k ih =>
      simp only [exp] at h2
      unfold concat at h2
      simp only [Set.mem_setOf_eq] at h2
      obtain ⟨a, ⟨⟨b, ⟨hb, ⟨c, ⟨hc, eq_1⟩⟩⟩⟩, ⟨d, ⟨hd, eq_2⟩⟩⟩⟩ := h2

      rewrite [← eq_2]
      simp only [List.length_append]
      apply Nat.add_lt_add_of_lt_of_le
      · apply ih
        rewrite [← eq_1]
        apply append_mem_exp_left
        · exact hb
        · exact hc
      · apply Nat.succ_le_of_lt
        apply eps_not_mem_str_length_gt_zero L
        · exact h1
        · exact hd


example
  {α : Type}
  (L : Language α)
  (x : Str α)
  (h1 : [] ∉ L) :
  x ∉ exp L (x.length + 1) :=
  by
    intro contra
    obtain s1 := eps_not_mem_imp_mem_len_ge_exp L x x.length h1 contra
    simp only [gt_iff_lt, lt_self_iff_false] at s1


theorem eps_not_mem_imp_mem_concat_exp_ge_exp
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (n : ℕ)
  (h1 : [] ∉ L)
  (h2 : x ∈ concat (exp L (n + 1)) M) :
  x.length > n :=
  by
    unfold concat at h2
    simp only [Set.mem_setOf_eq] at h2
    obtain ⟨s, hs, t, ht, eq⟩ := h2

    rewrite [← eq]
    simp only [List.length_append]
    apply Nat.lt_add_right
    apply eps_not_mem_imp_mem_len_ge_exp L
    · exact h1
    · exact hs


theorem eps_not_mem_imp_not_mem_concat_exp
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : [] ∉ L) :
  x ∉ concat (exp L (x.length + 1)) M :=
  by
    intro contra
    obtain s1 := eps_not_mem_imp_mem_concat_exp_ge_exp L M x x.length h1 contra
    simp only [gt_iff_lt, lt_self_iff_false] at s1


end Language

import Mathlib.Data.Nat.Lattice

import FormalLanguageLean.String


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


/-
Definition 10 (Language). A language L over some alphabet Σ is a subset of Σ∗, i.e. L ⊆ Σ∗.
-/

/--
  The type of languages over the alphabet `α`.
  A language over some alphabet `α` is a subset of the set of all finite strings over the alphabet `α`.
-/
abbrev Language (α : Type) : Type := Set (Str α)


namespace Language


example
  (α : Type)
  (L : Language α) :
  L ⊆ String.kleene_closure α :=
  by
    rewrite [Set.subset_def]
    intro cs _
    apply String.str_mem_kleene_closure


lemma eps_not_mem_str_length_gt_zero
  {α : Type}
  (L : Language α)
  (s : Str α)
  (h1 : [] ∉ L)
  (h2 : s ∈ L) :
  s.length > 0 :=
  by
    rewrite [gt_iff_lt]
    rewrite [List.length_pos_iff]
    exact ne_of_mem_of_not_mem h2 h1


lemma take_append_len_left
  {α : Type}
  (cs s t : Str α)
  (h1 : s ++ t = cs) :
  List.take (cs.length - t.length) cs = s :=
  by
    rewrite [← h1]
    apply List.take_left'
    rewrite [List.length_append]
    apply Nat.eq_sub_of_add_eq
    rfl


/-
Definition 11 (Concatenation). Let L1 and L2 be languages. The concatenation of L1 and L2, written L1 · L2, or L1L2 is defined by
L1L2 = {s · t = st : s ∈ L1, t ∈ L2} .
-/
/--
  `concat L1 L2` := The concatenation of the languages `L1` and `L2`.
-/
def concat
  {α : Type}
  (L1 L2 : Language α) :
  Language α :=
  { s ++ t | (s ∈ L1) (t ∈ L2) }


/--
  `concat L1 L2` := The concatenation of the lists of strings `L1` and `L2` defined such that `concat L1.toFinset.toSet L2.toFinset.toSet = (concat_list L1 L2).toFinset.toSet`.
-/
def concat_list
  {α : Type}
  (L1 L2 : List (Str α)) :
  List (Str α) :=
  (List.product L1 L2).map (fun (s, t) => s ++ t)


lemma concat_eq_concat_list
  {α : Type}
  [DecidableEq α]
  (L1 L2 : List (Str α)) :
  concat L1.toFinset.toSet L2.toFinset.toSet =
    (concat_list L1 L2).toFinset.toSet :=
  by
    ext cs
    unfold concat
    simp only [concat_list]
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map, Prod.exists, List.pair_mem_product]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      rewrite [← eq]
      exact ⟨s, t, ⟨hs, ht⟩, rfl⟩
    · intro a1
      obtain ⟨s, t, ⟨hs, ht⟩, eq⟩ := a1
      rewrite [← eq]
      exact ⟨s, hs, t, ht, rfl⟩


lemma append_mem_concat
  {α : Type}
  (L M : Language α)
  (s t : Str α)
  (h1 : s ∈ L)
  (h2 : t ∈ M) :
  s ++ t ∈ concat L M :=
  by
    unfold concat
    rewrite [Set.mem_setOf_eq]
    exact ⟨s, h1, t, h2, rfl⟩


-------------------------------------------------------------------------------


lemma concat_empty_left
  {α : Type}
  (L : Language α) :
  concat ∅ L = ∅ :=
  by
    ext cs
    unfold concat
    rewrite [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      rewrite [Set.mem_empty_iff_false] at hs
      contradiction
    · intro a1
      rewrite [Set.mem_empty_iff_false] at a1
      contradiction


lemma concat_empty_right
  {α : Type}
  (L : Language α) :
  concat L ∅ = ∅ :=
  by
    ext cs
    unfold concat
    rewrite [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      rewrite [Set.mem_empty_iff_false] at ht
      contradiction
    · intro a1
      rewrite [Set.mem_empty_iff_false] at a1
      contradiction


-------------------------------------------------------------------------------


lemma concat_nonempty_iff
  {α : Type}
  (L M : Language α) :
  (concat L M).Nonempty ↔ L.Nonempty ∧ M.Nonempty :=
  by
    unfold concat
    simp only [Set.Nonempty]
    simp only [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨x, s, hs, t, ht, eq⟩ := a1
      exact ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    · intro a1
      obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := a1
      exact ⟨s ++ t, s, hs, t, ht, rfl⟩


lemma concat_empty_iff
  {α : Type}
  (L M : Language α) :
  (concat L M) = ∅ ↔ L = ∅ ∨ M = ∅ :=
  by
    simp only [← Set.not_nonempty_iff_eq_empty]
    rewrite [concat_nonempty_iff]
    apply not_and_or


-------------------------------------------------------------------------------


lemma concat_eps_left
  {α : Type}
  (L : Language α) :
  concat {[]} L = L :=
  by
    unfold concat
    simp only [Set.mem_singleton_iff, exists_eq_left, List.nil_append, exists_eq_right, Set.setOf_mem_eq]


lemma concat_eps_right
  {α : Type}
  (L : Language α) :
  concat L {[]} = L :=
  by
    unfold concat
    simp only [Set.mem_singleton_iff, exists_eq_left, List.append_nil, exists_eq_right, Set.setOf_mem_eq]


-------------------------------------------------------------------------------


lemma eps_mem_concat_iff
  {α : Type}
  (L M : Language α) :
  [] ∈ concat L M ↔ [] ∈ L ∧ [] ∈ M :=
  by
    unfold concat
    simp only [Set.mem_setOf_eq, List.append_eq_nil_iff]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, s_eq, t_eq⟩ := a1
      constructor
      · rewrite [← s_eq]
        exact hs
      · rewrite [← t_eq]
        exact ht
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      exact ⟨[], a1_left, [], a1_right, rfl, rfl⟩


lemma eps_not_mem_concat_iff
  {α : Type}
  (L M : Language α) :
  [] ∉ concat L M ↔ ([] ∉ L ∨ [] ∉ M) :=
  by
    rewrite [eps_mem_concat_iff]
    apply not_and_or


example
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : [] ∉ L ∨ [] ∉ M)
  (h2 : s ∈ concat L M) :
  s.length > 0 :=
  by
    rewrite [← eps_not_mem_concat_iff] at h1
    apply eps_not_mem_str_length_gt_zero (concat L M)
    · exact h1
    · exact h2


-------------------------------------------------------------------------------


lemma append_mem_concat_eps_left
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : [] ∈ L)
  (h2 : x ∈ M) :
  x ∈ concat L M :=
  by
    have s1 : x = [] ++ x := rfl
    rewrite [s1]
    apply append_mem_concat
    · exact h1
    · exact h2


lemma eps_mem_left_right_subset_concat
  {α : Type}
  (L M : Language α)
  (h1 : [] ∈ L) :
  M ⊆ concat L M :=
  by
    rewrite [Set.subset_def]
    intro x a1
    apply append_mem_concat_eps_left
    · exact h1
    · exact a1


lemma append_mem_concat_eps_right
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : x ∈ L)
  (h2 : [] ∈ M) :
  x ∈ concat L M :=
  by
    have s1 : x = x ++ [] := by rewrite [List.append_nil]; rfl
    rewrite [s1]
    apply append_mem_concat
    · exact h1
    · exact h2


lemma eps_mem_right_left_subset_concat
  {α : Type}
  (L M : Language α)
  (h1 : [] ∈ M) :
  L ⊆ concat L M :=
  by
    rewrite [Set.subset_def]
    intro x a1
    apply append_mem_concat_eps_right
    · exact a1
    · exact h1


-------------------------------------------------------------------------------


theorem concat_assoc
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat L1 (concat L2 L3) =
    concat (concat L1 L2) L3 :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_setOf_eq]
    simp only [exists_exists_and_exists_and_eq_and]
    simp only [List.append_assoc]


-------------------------------------------------------------------------------


theorem concat_distrib_s_union_left
  {α : Type}
  (L : Language α)
  (S : Set (Language α)) :
  concat L (⋃₀ S) = ⋃ (s ∈ S), (concat L s) :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ⟨M, hM, ht⟩, eq⟩ := a1
      exact ⟨M, hM, s, hs, t, ht, eq⟩
    · intro a1
      obtain ⟨M, hM, s, hs, t, ht, eq⟩ := a1
      exact ⟨s, hs, t, ⟨M, hM, ht⟩, eq⟩


theorem concat_distrib_s_union_right
  {α : Type}
  (S : Set (Language α))
  (L : Language α) :
  concat (⋃₀ S) L = ⋃ (s ∈ S), (concat s L) :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro a1
      obtain ⟨s, ⟨M, hM, hs⟩, t, ht, eq⟩ := a1
      exact ⟨M, hM, s, hs, t, ht, eq⟩
    · intro a1
      obtain ⟨M, hM, s, hs, t, ht, eq⟩ := a1
      exact ⟨s, ⟨M, hM, hs⟩, t, ht, eq⟩


lemma concat_distrib_countable_union_left
  {α : Type}
  (L : Language α)
  (f : ℕ → Language α) :
  ⋃ (n : ℕ), concat L (f n) = concat L (⋃ (n : ℕ), (f n)) :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨i, s, hs, t, ⟨ht, eq⟩⟩ := a1
      rewrite [← eq]
      exact ⟨s, hs, t, ⟨i, ht⟩, rfl⟩
    · intro a1
      obtain ⟨s, hs, t, ⟨i, ht⟩, eq⟩ := a1
      rewrite [← eq]
      exact ⟨i, s, hs, t, ht, rfl⟩


lemma concat_distrib_countable_union_right
  {α : Type}
  (L : Language α)
  (f : ℕ → Language α) :
  ⋃ (n : ℕ), concat (f n) L = concat (⋃ (n : ℕ), (f n)) L :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨i, s, hs, t, ⟨ht, eq⟩⟩ := a1
      rewrite [← eq]
      exact ⟨s, ⟨i, hs⟩, t, ht, rfl⟩
    · intro a1
      obtain ⟨s, ⟨i, hs⟩, t, ht, eq⟩ := a1
      rewrite [← eq]
      exact ⟨i, s, hs, t, ht, rfl⟩


lemma concat_distrib_finset_i_union_left
  {α : Type}
  {β : Type}
  (L : Language α)
  (S : Finset β)
  (f : β → Language α) :
  ⋃ (x ∈ S), concat L (f x) = concat L (⋃ (x ∈ S), (f x)) :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨i, hi, s, hs, t, ht, eq⟩ := a1
      rewrite [← eq]
      exact ⟨s, hs, t, ⟨i, hi, ht⟩, rfl⟩
    · intro a1
      obtain ⟨s, hs, t, ⟨i, hi, ht⟩, eq⟩ := a1
      rewrite [← eq]
      exact ⟨i, hi, s, hs, t, ht, rfl⟩


lemma concat_distrib_finset_i_union_right
  {α : Type}
  {β : Type}
  (M : Language α)
  (S : Finset β)
  (f : β → Language α) :
  ⋃ (x ∈ S), concat (f x) M = concat (⋃ (x ∈ S), (f x)) M :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨i, hi, s, hs, t, ht, eq⟩ := a1
      rewrite [← eq]
      exact ⟨s, ⟨i, hi, hs⟩, t, ht, rfl⟩
    · intro a1
      obtain ⟨s, ⟨i, hi, hs⟩, t, ht, eq⟩ := a1
      rewrite [← eq]
      exact ⟨i, hi, s, hs, t, ht, rfl⟩


theorem concat_distrib_union_left
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat L1 (L2 ∪ L3) =
    concat L1 L2 ∪ concat L1 L3 :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases ht
      case inl ht =>
        left
        exact ⟨s, hs, t, ht, eq⟩
      case inr ht =>
        right
        exact ⟨s, hs, t, ht, eq⟩
    · intro a1
      cases a1
      case inl a1 =>
        obtain ⟨s, hs, t, ht, eq⟩ := a1
        apply Exists.intro s
        constructor
        · exact hs
        · apply Exists.intro t
          constructor
          · left
            exact ht
          · exact eq
      case inr a1 =>
        obtain ⟨s, hs, t, ht, eq⟩ := a1
        apply Exists.intro s
        constructor
        · exact hs
        · apply Exists.intro t
          constructor
          · right
            exact ht
          · exact eq


theorem concat_distrib_union_right
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat (L1 ∪ L2) L3 =
    concat L1 L3 ∪ concat L2 L3 :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases hs
      case inl hs =>
        left
        exact ⟨s, hs, t, ht, eq⟩
      case inr hs =>
        right
        exact ⟨s, hs, t, ht, eq⟩
    · intro a1
      cases a1
      case inl a1 =>
        obtain ⟨s, hs, t, ht, eq⟩ := a1
        apply Exists.intro s
        constructor
        · left
          exact hs
        · exact ⟨t, ht, eq⟩
      case inr a1 =>
        obtain ⟨s, hs, t, ht, eq⟩ := a1
        apply Exists.intro s
        constructor
        · right
          exact hs
        · exact ⟨t, ht, eq⟩


-------------------------------------------------------------------------------


lemma concat_subset
  {α : Type}
  (L1 L2 M1 M2 : Language α)
  (h1 : L1 ⊆ M1)
  (h2 : L2 ⊆ M2) :
  concat L1 L2 ⊆ concat M1 M2 :=
  by
    unfold concat
    rewrite [Set.subset_def]
    simp only [Set.mem_setOf_eq]
    intro x a1
    obtain ⟨s, hs, t, ht, eq⟩ := a1
    have s1 : s ∈ M1 := h1 hs
    have s2 : t ∈ M2 := h2 ht
    exact ⟨s, s1, t, s2, eq⟩


lemma concat_subset_left
  {α : Type}
  (L1 L2 L3 : Language α)
  (h1 : L2 ⊆ L3) :
  concat L1 L2 ⊆ concat L1 L3 :=
  by
    apply concat_subset
    · rfl
    · exact h1


lemma concat_subset_right
  {α : Type}
  (L1 L2 L3 : Language α)
  (h1 : L2 ⊆ L3) :
  concat L2 L1 ⊆ concat L3 L1 :=
  by
    apply concat_subset
    · exact h1
    · rfl


-------------------------------------------------------------------------------


theorem intersection_concat_char_and_concat_diff_char_eq_empty
  {α : Type}
  (L : Language α)
  (a b : α)
  (h1 : ¬ b = a) :
  concat {[a]} L ∩ concat {[b]} L = ∅ :=
  by
    ext cs
    unfold concat
    simp only [Set.mem_singleton_iff]
    rewrite [Set.mem_inter_iff]
    simp only [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨⟨s1, h_s1, t1, h_t1, eq_1⟩, ⟨s2, h_s2, t2, h_t2, eq_2⟩⟩ := a1
      rewrite [h_s1] at eq_1
      rewrite [List.cons_append, List.nil_append] at eq_1
      rewrite [h_s2] at eq_2
      rewrite [List.cons_append, List.nil_append] at eq_2
      rewrite [← eq_1] at eq_2
      rewrite [List.cons.injEq] at eq_2
      obtain ⟨eq_2_left, eq_2_right⟩ := eq_2
      contradiction
    · intro a1
      rewrite [Set.mem_empty_iff_false] at a1
      contradiction


-------------------------------------------------------------------------------


lemma exists_mem_concat_str_length_gt_mem_left
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : s ∈ L)
  (h2 : M.Nonempty)
  (h3 : [] ∉ M) :
  ∃ (t : Str α), t ∈ concat L M ∧ s.length < t.length :=
  by
    unfold Set.Nonempty at h2
    obtain ⟨t, ht⟩ := h2

    apply Exists.intro (s ++ t)
    constructor
    · apply append_mem_concat
      · exact h1
      · exact ht
    · apply String.str_append_length_right
      intro contra
      apply h3
      rewrite [← contra]
      exact ht


lemma exists_mem_concat_str_length_gt_mem_right
  {α : Type}
  (L M : Language α)
  (t : Str α)
  (h1 : t ∈ M)
  (h2 : L.Nonempty)
  (h3 : [] ∉ L) :
  ∃ (s : Str α), s ∈ concat L M ∧ t.length < s.length :=
  by
    unfold Set.Nonempty at h2
    obtain ⟨s, hs⟩ := h2

    apply Exists.intro (s ++ t)
    constructor
    · apply append_mem_concat
      · exact hs
      · exact h1
    · apply String.str_append_length_left
      intro contra
      apply h3
      rewrite [← contra]
      exact hs


lemma exists_mem_left_str_length_lt_concat
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : s ∈ concat L M)
  (h2 : [] ∉ M) :
  ∃ (t : Str α), t ∈ L ∧ t.length < s.length :=
  by
    unfold concat at h1
    rewrite [Set.mem_setOf_eq] at h1
    obtain ⟨u, hu, v, hv, eq⟩ := h1

    rewrite [← eq]
    apply Exists.intro u
    constructor
    · exact hu
    · simp only [List.length_append, Nat.lt_add_right_iff_pos]
      simp only [List.length_pos_iff]
      exact ne_of_mem_of_not_mem hv h2


lemma exists_mem_right_str_length_lt_concat
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : s ∈ concat L M)
  (h2 : [] ∉ L) :
  ∃ (t : Str α), t ∈ M ∧ t.length < s.length :=
  by
    unfold concat at h1
    rewrite [Set.mem_setOf_eq] at h1
    obtain ⟨u, hu, v, hv, eq⟩ := h1

    rewrite [← eq]
    apply Exists.intro v
    constructor
    · exact hv
    · simp only [List.length_append, Nat.lt_add_left_iff_pos]
      simp only [List.length_pos_iff]
      exact ne_of_mem_of_not_mem hu h2


lemma set_list_inf_length_exists
  {α : Type}
  (S : Set (List α))
  (h1 : S.Nonempty) :
  ∃ (xs : List α), xs ∈ S ∧
    ∀ (ys : List α), ys ∈ S → xs.length <= ys.length :=
  by
    let length_set : Set ℕ := Set.image List.length S
    let length_set_inf : ℕ := sInf length_set

    have s1 : ∃ (list_set_inf : List α), list_set_inf ∈ S ∧ list_set_inf.length = length_set_inf :=
    by
      rewrite [← Set.mem_image]
      apply Nat.sInf_mem
      apply Set.Nonempty.image
      exact h1

    obtain ⟨list_set_inf, list_set_inf_mem, list_set_inf_length⟩ := s1

    apply Exists.intro list_set_inf
    constructor
    · exact list_set_inf_mem
    · intro ys hy
      rewrite [list_set_inf_length]
      apply Nat.sInf_le
      apply Set.mem_image_of_mem
      exact hy


lemma left_nonempty_subset_concat_eps_mem_right
  {α : Type}
  (L M : Language α)
  (h1 : L.Nonempty)
  (h2 : L ⊆ concat L M) :
  [] ∈ M :=
  by
    obtain s1 := set_list_inf_length_exists L h1
    obtain ⟨min, mem, le⟩ := s1

    rewrite [Set.subset_def] at h2
    specialize h2 min mem

    by_contra contra
    obtain s2 := exists_mem_left_str_length_lt_concat L M min h2 contra
    obtain ⟨t, ht, lt⟩ := s2

    apply Nat.not_le_of_lt lt
    apply le
    exact ht


lemma right_nonempty_subset_concat_eps_mem_left
  {α : Type}
  (L M : Language α)
  (h1 : M.Nonempty)
  (h2 : M ⊆ concat L M) :
  [] ∈ L :=
  by
    obtain s1 := set_list_inf_length_exists M h1
    obtain ⟨min, mem, le⟩ := s1

    rewrite [Set.subset_def] at h2
    specialize h2 min mem

    by_contra contra
    obtain s2 := exists_mem_right_str_length_lt_concat L M min h2 contra
    obtain ⟨t, ht, lt⟩ := s2

    apply Nat.not_le_of_lt lt
    apply le
    exact ht


#lint

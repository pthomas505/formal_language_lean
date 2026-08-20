import FormalLanguageLean.Nullable


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false



-- https://arxiv.org/pdf/1907.13577


namespace Language


/-
Definition 15 (String derivative). The derivative of a language L ⊆ Σ∗ with respect to a string s ∈ Σ∗ is defined to be ∂sL = {t : s · t ∈ L}.
-/

def derivative
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Language α :=
  { t : Str α | s ++ t ∈ L }


theorem derivative_def
  {α : Type}
  (L : Language α)
  (a : α)
  (s : Str α) :
  s ∈ (derivative L [a]) ↔ a :: s ∈ L :=
  by
    unfold derivative
    simp only [List.cons_append, List.nil_append, Set.mem_setOf_eq]


def derivative_list
  {α : Type}
  [DecidableEq α]
  (L : List (List α))
  (s : List α) :
  List (List α) :=
  (L.filter (fun (cs : List α) => List.IsPrefix s cs)).map
    (fun (cs : List α) => cs.drop s.length)


theorem derivative_eq_derivative_list
  {α : Type}
  [DecidableEq α]
  (L : List (List α))
  (s : List α) :
  derivative (L.toFinset : Set (List α)) s =
    ((derivative_list L s).toFinset : Set (List α)) :=
  by
    ext t
    unfold derivative
    unfold derivative_list
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map, List.mem_filter, decide_eq_true_eq]
    simp only [List.IsPrefix]
    constructor
    · intro a1
      apply Exists.intro (s ++ t)
      constructor
      · constructor
        · exact a1
        · apply Exists.intro t
          apply Eq.refl
      · simp only [List.drop_left']
    · intro a1
      obtain ⟨xs, ⟨hxs, cs, eq_1⟩, eq_2⟩ := a1
      rewrite [← eq_1] at eq_2
      simp only [List.drop_left'] at eq_2
      rewrite [← eq_2]
      rewrite [eq_1]
      exact hxs


theorem derivative_wrt_eps
  {α : Type}
  (L : Language α) :
  derivative L [] = L :=
  by
    unfold derivative
    simp only [List.nil_append, Set.setOf_mem_eq]


theorem derivative_wrt_append
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  derivative L (s ++ t) = derivative (derivative L s) t :=
  by
    unfold derivative
    simp only [List.append_assoc, Set.mem_setOf_eq]


theorem derivative_wrt_cons
  {α : Type}
  (L : Language α)
  (hd : α)
  (tl : Str α) :
  derivative L (hd :: tl) = derivative (derivative L [hd]) tl :=
  by
    unfold derivative
    simp only [List.cons_append, List.nil_append, Set.mem_setOf_eq]


example
  {α : Type}
  (L : Language α)
  (s : Str α)
  (a : α) :
  derivative L (s ++ [a]) = derivative (derivative L s) [a] :=
  by
    unfold derivative
    simp only [List.append_assoc, List.cons_append, List.nil_append, Set.mem_setOf_eq]


def derivative_wrt_str
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Language α :=
  List.foldl (fun (M : Language α) (c : α) => derivative M [c]) L s


example
  {α : Type}
  (L : Language α)
  (s : Str α) :
  derivative L s = derivative_wrt_str L s :=
  by
    unfold derivative_wrt_str
    induction s generalizing L
    case nil =>
      unfold derivative
      simp only [List.nil_append, Set.setOf_mem_eq, List.cons_append, List.foldl_nil]
    case cons hd tl ih =>
      have s1 : hd :: tl = [hd] ++ tl := by apply Eq.refl
      rewrite [s1]
      rewrite [derivative_wrt_append]
      simp only [List.cons_append, List.nil_append, List.foldl_cons]
      apply ih


-- [a] ∈ Σ^1

-- 1.50
theorem derivative_of_empty_wrt_char
  {α : Type}
  (a : α) :
  derivative ∅ [a] = ∅ :=
  by
    unfold derivative
    ext cs
    simp only [List.cons_append, List.nil_append, Set.mem_empty_iff_false, Set.setOf_false]


theorem derivative_of_empty_wrt_str
  {α : Type}
  (s : Str α) :
  derivative ∅ s = ∅ :=
  by
    unfold derivative
    simp only [Set.mem_empty_iff_false, Set.setOf_false]


-- 1.51
theorem derivative_of_eps_wrt_char
  {α : Type}
  (a : α) :
  derivative {[]} [a] = ∅ :=
  by
    unfold derivative
    simp only [List.cons_append, List.nil_append, Set.mem_singleton_iff, reduceCtorEq, Set.setOf_false]


-- 1.52
theorem derivative_of_char_wrt_same_char
  {α : Type}
  (a : α) :
  derivative {[a]} [a] = {[]} :=
  by
    unfold derivative
    ext cs
    simp only [List.cons_append, List.nil_append, Set.mem_singleton_iff, List.cons.injEq]
    simp only [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      exact a1_right
    · intro a1
      exact ⟨True.intro, a1⟩


theorem derivative_of_str_wrt_same_str
  {α : Type}
  (s : Str α) :
  derivative {s} s = {[]} :=
  by
    unfold derivative
    simp only [Set.mem_singleton_iff, List.append_right_eq_self, Set.setOf_eq_eq_singleton]


-- 1.53
theorem derivative_of_char_wrt_diff_char
  {α : Type}
  (a b : α)
  (h1 : ¬ a = b) :
  derivative {[b]} [a] = ∅ :=
  by
    unfold derivative
    simp only [List.cons_append, List.nil_append, Set.mem_singleton_iff, List.cons.injEq]
    ext cs
    simp only [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      contradiction
    · intro a1
      simp only [Set.mem_empty_iff_false] at a1


-- 1.54
theorem derivative_of_union_wrt_char
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∪ L2) [a] =
    (derivative L1 [a]) ∪ (derivative L2 [a]) :=
  by
    unfold derivative
    apply Eq.refl


theorem derivative_of_union_wrt_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∪ L2) s =
    (derivative L1 s) ∪ (derivative L2 s) :=
  by
    unfold derivative
    apply Eq.refl


-- 1.55
theorem derivative_of_intersection_wrt_char
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∩ L2) [a] =
    (derivative L1 [a]) ∩ (derivative L2 [a]) :=
  by
    unfold derivative
    apply Eq.refl


theorem derivative_of_intersection_wrt_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∩ L2) s =
    (derivative L1 s) ∩ (derivative L2 s) :=
  by
    unfold derivative
    apply Eq.refl


theorem concat_nullify_and_derivative_wrt_char
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : α) :
  {s | a :: s ∈ (concat L1.nullify L2)} = concat L1.nullify (derivative L2 [a]) :=
  by
    unfold derivative
    unfold concat
    ext cs
    simp only [Set.mem_setOf_eq, List.cons_append, List.nil_append]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp only [List.nil_append] at eq
        rewrite [eq] at ht
        apply Exists.intro []
        constructor
        · exact hs
        · apply Exists.intro cs
          constructor
          · exact ht
          · apply List.nil_append
      case cons s_hd s_tl =>
        unfold Language.nullify at hs
        simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, reduceCtorEq] at hs
        obtain ⟨hs_left, hs_right⟩ := hs
        contradiction
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp only [List.nil_append] at eq
        rewrite [eq] at ht
        apply Exists.intro []
        constructor
        · exact hs
        · apply Exists.intro (a :: cs)
          constructor
          · exact ht
          · apply List.nil_append
      case cons s_hd s_tl s_ih =>
        unfold Language.nullify at hs
        simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, reduceCtorEq] at hs
        obtain ⟨hs_left, hs_right⟩ := hs
        contradiction


theorem concat_nullify_and_derivative_wrt_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : Str α) :
  {s | a ++ s ∈ (concat L1.nullify L2)} = concat L1.nullify (derivative L2 a) :=
  by
    unfold derivative
    unfold concat
    ext cs
    simp only [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp only [List.nil_append] at eq
        rewrite [eq] at ht
        apply Exists.intro []
        constructor
        · exact hs
        · apply Exists.intro cs
          constructor
          · exact ht
          · apply List.nil_append
      case cons s_hd s_tl =>
        unfold Language.nullify at hs
        simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, reduceCtorEq] at hs
        obtain ⟨hs_left, hs_right⟩ := hs
        contradiction
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp only [List.nil_append] at eq
        rewrite [eq] at ht
        apply Exists.intro []
        constructor
        · exact hs
        · apply Exists.intro (a ++ cs)
          constructor
          · exact ht
          · apply List.nil_append
      case cons s_hd s_tl s_ih =>
        unfold Language.nullify at hs
        simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, reduceCtorEq] at hs
        obtain ⟨hs_left, hs_right⟩ := hs
        contradiction


theorem concat_derivative_and_nullify_wrt_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : Str α) :
  {s | a ++ s ∈ (concat L1 L2.nullify)} = concat (derivative L1 a) L2.nullify :=
  by
    unfold derivative
    unfold concat
    unfold Language.nullify
    ext cs
    simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨s, hs, t, ⟨hL2, ht⟩, eq⟩ := a1
      cases s
      case nil =>
        simp only [List.nil_append] at eq
        rewrite [eq] at ht
        simp only [List.append_eq_nil_iff] at ht
        obtain ⟨ht_left, ht_right⟩ := ht
        rewrite [ht_left]
        rewrite [ht_right]
        apply Exists.intro []
        constructor
        · simp only [List.append_nil]
          exact hs
        · apply Exists.intro []
          constructor
          · constructor
            · exact hL2
            · apply Eq.refl
          · apply List.nil_append
      case cons s_hd s_tl =>
        rewrite [ht] at eq
        simp only [List.append_nil] at eq
        apply Exists.intro cs
        rewrite [← eq]
        constructor
        · exact hs
        · apply Exists.intro []
          constructor
          · exact ⟨hL2, rfl⟩
          · apply List.append_nil
    · intro a1
      obtain ⟨s, hL1, t, ⟨hL2, ht⟩, eq⟩ := a1
      cases s
      case nil =>
        simp only [List.nil_append] at eq

        simp only [List.append_nil] at hL1

        apply Exists.intro a
        constructor
        · exact hL1
        · apply Exists.intro []
          rewrite [← eq]
          rw [ht]
          constructor
          · exact ⟨hL2, rfl⟩
          · apply Eq.refl
      case cons s_hd s_tl s_ih =>
        rewrite [ht] at eq
        simp only [List.append_nil] at eq
        rewrite [← eq]
        apply Exists.intro (a ++ s_tl :: s_ih)
        constructor
        · exact hL1
        · apply Exists.intro []
          constructor
          · exact ⟨hL2, rfl⟩
          · apply List.append_nil


theorem derivative_of_concat_wrt_char_aux
  {α : Type}
  [DecidableEq α]
  (L0 L2 : Language α)
  (a : α)
  (h1 : L0.nullify = ∅) :
  {t | a :: t ∈ concat L0 L2} = {t | ∃ t0 t2, a :: t0 ∈ L0 ∧ t2 ∈ L2 ∧ t0 ++ t2 = t} :=
  by
    unfold Language.nullify at h1
    split at h1
    case isTrue c1 =>
      simp only [Set.singleton_ne_empty] at h1
    case isFalse c1 =>
      unfold concat
      ext cs
      simp only [Set.mem_setOf_eq]
      constructor
      · intro a1
        obtain ⟨s, ⟨hs, ⟨t, ⟨ht, eq⟩⟩⟩⟩ := a1
        cases s
        case nil =>
          contradiction
        case cons s_hd s_tl =>
          simp only [List.cons_append, List.cons.injEq] at eq
          obtain ⟨eq_left, eq_right⟩ := eq
          rewrite [← eq_left]
          apply Exists.intro s_tl
          apply Exists.intro t
          exact ⟨hs, ⟨ ht, eq_right⟩ ⟩
      · intro a1
        obtain ⟨s, ⟨ t, ⟨hL0, ⟨ht, eq⟩⟩⟩⟩ := a1
        apply Exists.intro (a:: s)
        constructor
        · exact hL0
        · rewrite [← eq]
          apply Exists.intro t
          constructor
          · exact ht
          · exact List.cons_append


-- 1.56
theorem derivative_of_concat_wrt_char
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : α) :
  derivative (concat L1 L2) [a] =
    (concat (derivative L1 [a]) L2) ∪ (concat L1.nullify (derivative L2 [a])) :=
  by
    have s1 : ∀ (L0 : Language α), L0.nullify = ∅ →
      derivative (concat (L1.nullify ∪ L0) L2) [a] =
        (concat L1.nullify (derivative L2 [a])) ∪ (concat (derivative L0 [a]) L2) :=
    by
      intro L0 a1
      calc
      derivative (concat (L1.nullify ∪ L0) L2) [a] =
        {s | a :: s ∈ concat (L1.nullify ∪ L0) L2} :=
      by
        unfold derivative
        apply Eq.refl

      _ = {s | a :: s ∈ concat L1.nullify L2} ∪ {t | a :: t ∈ concat L0 L2} :=
      by
        obtain s3 := concat_distrib_union_right L1.nullify L0 L2
        rewrite [s3]
        apply Eq.refl

      _ = (concat L1.nullify (derivative L2 [a])) ∪ {t | ∃ t0 t2, a :: t0 ∈ L0 ∧ t2 ∈ L2 ∧ t0 ++ t2 = t} :=
      by
        obtain s3_1 := concat_nullify_and_derivative_wrt_char L1 L2 a
        rewrite [s3_1]
        obtain s3_2 := derivative_of_concat_wrt_char_aux L0 L2 a a1
        rewrite [s3_2]
        apply Eq.refl

      _ = (concat L1.nullify (derivative L2 [a])) ∪ concat {t0 | a :: t0 ∈ L0} L2 :=
      by
        unfold concat
        congr
        ext cs
        simp only [Set.mem_setOf_eq]
        constructor
        · intro a1
          obtain ⟨s, ⟨t, ⟨hs, ⟨ht, eq⟩⟩⟩⟩ := a1
          apply Exists.intro s
          constructor
          · exact hs
          · apply Exists.intro t
            exact ⟨ht, eq⟩
        · intro a1
          obtain ⟨s, ⟨hs, ⟨t, ⟨ ht, eq⟩⟩⟩⟩ := a1
          apply Exists.intro s
          apply Exists.intro t
          exact ⟨hs, ⟨ht, eq⟩⟩

      _ = (concat L1.nullify (derivative L2 [a])) ∪ (concat (derivative L0 [a]) L2) :=
      by
        unfold derivative
        simp only [List.cons_append, List.nil_append]

    have s2 : ∀ (L0 : Language α), derivative (L1.nullify ∪ L0) [a] = derivative L0 [a] :=
    by
      intro L0
      unfold derivative
      unfold Language.nullify
      simp only [List.cons_append, List.nil_append, Set.mem_union, Set.mem_ite_empty_right, Set.mem_singleton_iff, reduceCtorEq]
      ext cs
      simp only [Set.mem_setOf_eq]
      constructor
      · intro a1
        cases a1
        case inl a1 =>
          obtain ⟨a1_left, a1_right⟩ := a1
          contradiction
        case inr a1 =>
          exact a1
      · intro a1
        right
        exact a1

    obtain s3 := lang_as_union_of_nullify_and_not_nullable L1
    obtain ⟨L0, ⟨s3_left, s3_right⟩⟩ := s3

    specialize s1 L0 s3_left
    rewrite [← s3_right] at s1
    rewrite [s1]

    specialize s2 L0
    rewrite [← s3_right] at s2
    rewrite [s2]

    apply Set.union_comm


theorem derivative_of_concat_wrt_str.extracted_1_5
  {α : Type}
  (L1 L2 : Language α)
  (s1 s2 : Str α)
  (h1 : ∃ u v, (u ++ v = s1 ∧ List.length v > 0) ∧ u ∈ L1 ∧ v ++ s2 ∈ L2) :
  ∃ t,
    (∃ u v, u ++ v = s1 ∧ List.length v > 0 ∧ t = {x | ∃ s, (u ∈ L1 ∧ s = []) ∧ ∃ t, v ++ t ∈ L2 ∧ s ++ t = x}) ∧ s2 ∈ t :=
  by
    obtain ⟨u, ⟨v, ⟨⟨h1_left_left, h1_left_right⟩, h1_right⟩⟩⟩ := h1

    apply Exists.intro {x | u ∈ L1 ∧ v ++ x ∈ L2}
    constructor
    · apply Exists.intro u
      apply Exists.intro v
      constructor
      · exact h1_left_left
      · constructor
        · exact h1_left_right
        · ext cs
          simp only [Set.mem_setOf_eq]
          constructor
          · intro a1
            obtain ⟨a1_left, a1_right⟩ := a1
            apply Exists.intro []
            constructor
            · exact ⟨a1_left, rfl⟩
            · apply Exists.intro cs
              constructor
              · exact a1_right
              · apply List.nil_append
          · intro a1
            obtain ⟨s, ⟨⟨a1_left_left, a1_left_right⟩, ⟨t, ⟨a1_right_left, a1_right_right⟩⟩⟩⟩ := a1
            constructor
            · exact a1_left_left
            · rewrite [← a1_right_right]
              rewrite [a1_left_right]
              simp only [List.nil_append]
              exact a1_right_left
    · simp only [Set.mem_setOf_eq]
      exact h1_right


theorem derivative_of_concat_wrt_str.extracted_1_6
  {α : Type}
  (L1 L2 : Language α)
  (s1 s2 : Str α)
  (h1 :
    ∃ t,
      (∃ u v, u ++ v = s1 ∧ List.length v > 0 ∧ t = {x | ∃ s, (u ∈ L1 ∧ s = []) ∧ ∃ t, v ++ t ∈ L2 ∧ s ++ t = x}) ∧ s2 ∈ t) :
  ∃ u v, (u ++ v = s1 ∧ List.length v > 0) ∧ u ∈ L1 ∧ v ++ s2 ∈ L2 :=
  by
    obtain ⟨s, ⟨⟨t, ⟨u, ⟨h1_left_left, ⟨h1_left_right_left, h1_left_right_right⟩⟩⟩⟩, h1_right⟩⟩ := h1

    rewrite [h1_left_right_right] at h1_right
    simp only [Set.mem_setOf_eq] at h1_right
    obtain ⟨v, ⟨⟨h1_right_left_left, h1_right_left_right⟩, ⟨w, ⟨ h1_right_right_left, h1_right_right_right⟩⟩⟩⟩ := h1_right

    apply Exists.intro t
    apply Exists.intro u
    constructor
    · constructor
      · exact h1_left_left
      · exact h1_left_right_left
    · constructor
      · exact h1_right_left_left
      · rewrite [← h1_right_right_right]
        rewrite [h1_right_left_right]
        simp only [List.nil_append]
        exact h1_right_right_left


theorem derivative_of_concat_wrt_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s : Str α) :
  let B := { M | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ v.length > 0 ∧ M = concat (derivative L1 u).nullify (derivative L2 v) }
  derivative (concat L1 L2) s = (concat (derivative L1 s) L2) ∪ ⋃₀ B :=
  by
    unfold derivative
    unfold concat
    unfold Language.nullify
    simp only
    ext cs
    simp only [Set.mem_setOf_eq, List.append_nil, Set.mem_ite_empty_right, Set.mem_singleton_iff, Set.mem_union, Set.mem_sUnion]

    constructor
    · intro a1
      obtain ⟨u, hu, v, hv, eq⟩ := a1

      rewrite [List.append_eq_append_iff] at eq
      cases eq
      case inl eq =>
        obtain ⟨w, ⟨eq_left, eq_right⟩⟩ := eq
        rewrite [eq_left]

        by_cases hw : w = []
        · left
          apply Exists.intro []
          constructor
          · rewrite [hw]
            simp only [List.append_nil]
            exact hu
          · apply Exists.intro v
            simp only [List.nil_append]
            constructor
            · exact hv
            · rewrite [eq_right]
              rewrite [hw]
              apply List.nil_append
        · right
          apply derivative_of_concat_wrt_str.extracted_1_5
          apply Exists.intro u
          apply Exists.intro w
          constructor
          · constructor
            · apply Eq.refl
            · simp only [List.length_pos_iff]
              exact hw
          · constructor
            · exact hu
            · rewrite [← eq_right]
              exact hv
      case inr eq =>
        obtain ⟨w, ⟨eq_left, eq_right⟩⟩ := eq
        left
        apply Exists.intro w
        constructor
        · rewrite [← eq_left]
          exact hu
        · apply Exists.intro v
          constructor
          · exact hv
          · rewrite [← eq_right]
            apply Eq.refl
    · intro a1
      cases a1
      case inl a1 =>
        obtain ⟨u, ⟨a1_left, ⟨v, ⟨a1_right_left, a1_right_right⟩⟩⟩⟩ := a1
        apply Exists.intro (s ++ u)
        constructor
        · exact a1_left
        · apply Exists.intro v
          constructor
          · exact a1_right_left
          · rewrite [← a1_right_right]
            apply List.append_assoc
      case inr a1 =>
        obtain s1 := derivative_of_concat_wrt_str.extracted_1_6 L1 L2 s cs a1
        obtain ⟨u, ⟨v, ⟨⟨s1_left_left, s1_left_right⟩, ⟨s1_right_left, s1_right_right⟩⟩⟩⟩ := s1
        apply Exists.intro u
        constructor
        · exact s1_right_left
        · apply Exists.intro (v ++ cs)
          constructor
          · exact s1_right_right
          · simp only [← List.append_assoc]
            rewrite [s1_left_left]
            apply Eq.refl


-- 1.59
theorem derivative_of_exp_succ_wrt_char
  {α : Type}
  (L : Language α)
  (a : α)
  (k : ℕ) :
  derivative (exp L (k + 1)) [a] =
    concat (derivative L [a]) (exp L k) :=
  by
    classical
    induction k
    case zero =>
      simp only [exp]
      unfold concat
      simp only [Set.mem_singleton_iff, exists_eq_left, List.nil_append, exists_eq_right, Set.setOf_mem_eq, List.append_nil]
    case succ k ih =>
      conv => left; unfold exp
      rewrite [concat_exp_comm]
      rewrite [derivative_of_concat_wrt_char]
      unfold Language.nullify
      split
      case isTrue c1 =>
        rewrite [concat_eps_left]
        rewrite [ih]
        rewrite [Set.union_eq_left]
        apply concat_subset_left
        apply eps_mem_exp_subset_exp_add_nat
        exact c1
      case isFalse c1 =>
        rewrite [concat_empty_left]
        apply Set.union_empty


theorem derivative_distrib_union_of_countable_wrt_char
  {α : Type}
  (a : α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) [a] = derivative (⋃ n, f n) [a] :=
  by
    unfold derivative
    ext cs
    simp only [List.cons_append, List.nil_append, Set.mem_iUnion, Set.mem_setOf_eq]


theorem derivative_distrib_union_of_countable_wrt_str
  {α : Type}
  (s : Str α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) s = derivative (⋃ n, f n) s :=
  by
    unfold derivative
    ext cs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]


theorem derivative_distrib_union_of_finset_wrt_char
  {α : Type}
  {β : Type}
  (a : α)
  (Γ : Finset β)
  (f : β → Language α) :
  ⋃ (x ∈ Γ), derivative (f x) [a] = derivative (⋃ (x ∈ Γ), f x) [a] :=
  by
    unfold derivative
    ext cs
    simp only [List.cons_append, List.nil_append, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]


theorem derivative_distrib_union_of_finset_wrt_str
  {α : Type}
  {β : Type}
  (s : Str α)
  (Γ : Finset β)
  (f : β → Language α) :
  ⋃ (x ∈ Γ), derivative (f x) s = derivative (⋃ (x ∈ Γ), f x) s :=
  by
    unfold derivative
    ext cs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]


-- 1.57
theorem derivative_of_kleene_closure_wrt_char
  {α : Type}
  (L : Language α)
  (a : α) :
  derivative (kleene_closure α L) [a] = concat (derivative L [a]) (kleene_closure α L) :=
  by
    conv => left; rewrite [kleene_closure_eq_union_exp]
    rewrite [← Set.union_iUnion_nat_succ (exp L)]
    rewrite [derivative_of_union_wrt_char]
    rewrite [exp_zero]
    rewrite [derivative_of_eps_wrt_char]
    simp only [Set.empty_union]
    rewrite [← derivative_distrib_union_of_countable_wrt_char]
    simp only [derivative_of_exp_succ_wrt_char]
    rewrite [concat_distrib_countable_union_left]
    rewrite [kleene_closure_eq_union_exp]
    apply Eq.refl


-- 1.58
theorem derivative_of_complement_wrt_char
  {α : Type}
  (L : Language α)
  (a : α) :
  derivative Lᶜ [a] = (derivative L [a])ᶜ :=
  by
    apply Eq.refl
  -- Why is this proof so short?


theorem str_mem_lang_iff_eps_mem_derivative
  {α : Type}
  (L : Language α)
  (s : Str α) :
  s ∈ L ↔ [] ∈ derivative L s :=
  by
    unfold derivative
    simp only [Set.mem_setOf_eq, List.append_nil]


theorem str_mem_lang_iff_nullify_derivative_eq_eps
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  s ∈ L ↔ (derivative L s).nullify = {[]} :=
  by
    rewrite [str_mem_lang_iff_eps_mem_derivative L]
    unfold Language.nullify

    split
    case isTrue c1 =>
      constructor
      · intro a1
        apply Eq.refl
      · intro a1
        exact c1
    case isFalse c1 =>
      simp only [c1]
      constructor
      · intro a1
        contradiction
      · intro a1
        simp only [Set.empty_ne_singleton] at a1


theorem lang_eq_union_nullify_union_concat_char_derivative_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L = L.nullify ∪ ⋃ (a : α), concat {[a]} (derivative L [a]) :=
  by
    ext cs
    constructor
    · intro a1
      cases cs
      case nil =>
        simp only [Set.mem_union, Set.mem_iUnion]
        left
        unfold Language.nullify
        split
        case isTrue c1 =>
          simp only [Set.mem_singleton_iff]
        case isFalse c1 =>
          contradiction
      case cons hd tl =>
        simp only [Set.mem_union, Set.mem_iUnion]
        right
        apply Exists.intro hd
        unfold concat
        unfold derivative
        simp only [Set.mem_singleton_iff, List.cons_append, List.nil_append, Set.mem_setOf_eq]
        apply Exists.intro [hd]
        constructor
        · apply Eq.refl
        · apply Exists.intro tl
          constructor
          · exact a1
          · exact List.singleton_append
    · intro a1
      simp only [Set.mem_union, Set.mem_iUnion] at a1
      cases a1
      case inl a1 =>
        unfold Language.nullify at a1
        split at a1
        case isTrue c1 =>
          simp only [Set.mem_singleton_iff] at a1
          rewrite [a1]
          exact c1
        case isFalse c1 =>
          simp only [Set.mem_empty_iff_false] at a1
      case inr a1 =>
        obtain ⟨i, a1⟩ := a1
        unfold concat at a1
        unfold derivative at a1
        simp only [Set.mem_singleton_iff, List.cons_append, List.nil_append, Set.mem_setOf_eq, exists_eq_left] at a1
        obtain ⟨t, ⟨a1_left, a1_right⟩⟩ := a1
        rewrite [← a1_right]
        exact a1_left


theorem derivative_of_nullify_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative (L.nullify) [a] = ∅ :=
  by
    unfold derivative
    unfold Language.nullify
    ext cs
    simp only [List.cons_append, List.nil_append, Set.mem_ite_empty_right, Set.mem_singleton_iff]
    simp only [Set.mem_setOf_eq]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      simp only [reduceCtorEq] at a1_right
    · intro a1
      simp only [Set.mem_empty_iff_false] at a1


theorem concat_derivative_kleene_closure_subset
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a b : Str α)
  (h1 : b ∈ L) :
  concat (derivative L a) (kleene_closure α L) ⊆
    concat (derivative L b).nullify (derivative (kleene_closure α L) a) :=
  by
    simp only [Set.subset_def]
    intro x a1
    unfold concat at a1
    unfold derivative at a1
    simp only [Set.mem_setOf_eq] at a1
    obtain ⟨s, hs, t, ht, eq⟩ := a1
    rewrite [← eq]

    unfold concat
    unfold derivative
    simp only [Set.mem_setOf_eq]
    apply Exists.intro []
    simp only [List.nil_append, exists_eq_right]
    unfold Language.nullify
    constructor
    · split
      case isTrue c1 =>
        simp only [Set.mem_singleton_iff]
      case isFalse c1 =>
        simp only [Set.mem_setOf_eq, List.append_nil] at c1
        contradiction
    · simp only [String.str_append_assoc]
      apply append_kleene_closure_closed
      · apply mem_language_mem_kleene_closure
        exact hs
      · exact ht


noncomputable def foo'
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  List (List α) :=
  match s with
  | [] => []
  | hd :: tl =>
    open Classical in
    let l1 :=
      tl.tails.filter fun s => ¬ s = [] ∧ [] ∈ derivative L (hd :: tl.take (tl.length - s.length))
    have IH (v : List α) (h : v.IsSuffix tl) :=
      have : v.length ≤ tl.length := h.length_le
      foo' L v
    let l2 := l1.attach.flatMap fun ⟨v, h⟩ => by
      simp only [l1] at h
      simp only [List.mem_filter, List.mem_tails, decide_eq_true_eq] at h
      exact IH v h.1
    (hd :: tl) :: l2
termination_by s.length


theorem derivative_of_kleene_closure_wrt_str
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α)
  (h1 : ¬ s = []) :
  derivative (kleene_closure α L) s =
    ⋃ t ∈ foo' L s, concat (derivative L t) (kleene_closure α L) :=
  by
    cases e : s
    case nil =>
      contradiction
    case cons hd tl =>
      have ih : ∀ (v : List α), v.IsSuffix tl → ¬ v = [] → derivative (kleene_closure α L) v = ⋃ t ∈ foo' L v, concat (derivative L t) (kleene_closure α L) :=
      by
        intro v h
        have : v.length < s.length :=
        by
          rewrite [e]
          simp only [List.length_cons]
          apply Nat.lt_succ_of_le
          exact List.IsSuffix.length_le h
        exact derivative_of_kleene_closure_wrt_str L v

      rewrite [derivative_wrt_cons]
      rewrite [derivative_of_kleene_closure_wrt_char]
      rewrite [derivative_of_concat_wrt_str]
      rewrite [← derivative_wrt_append]
      simp only [List.singleton_append]

      rewrite [foo']

      simp only [gt_iff_lt, List.mem_filter, List.mem_tails, decide_eq_true_eq, List.flatMap_subtype, List.unattach_attach, List.mem_cons, List.mem_flatMap, Set.iUnion_iUnion_eq_or_left, Set.iUnion_exists, Set.biUnion_and']
      congr! 1
      ext cs
      simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      simp only [List.length_pos_iff]

      constructor
      · intro a1
        obtain ⟨M, ⟨⟨u, ⟨v, ⟨a1_left_left, ⟨a1_left_right_left, a1_left_right_right⟩⟩⟩⟩, a1_right⟩ ⟩ := a1

        have s1 : List.IsSuffix v tl :=
        by
          simp only [List.IsSuffix]
          apply Exists.intro u
          exact a1_left_left

        rewrite [a1_left_right_right] at a1_right
        rewrite [mem_concat_nullify_left_iff] at a1_right
        obtain ⟨a1_right_left, a1_right_right⟩ := a1_right
        unfold derivative at a1_right_left
        simp only [List.cons_append, List.nil_append, Set.mem_setOf_eq, List.append_nil] at a1_right_left

        specialize ih v s1 a1_left_right_left

        apply Exists.intro v
        constructor
        · constructor
          · exact s1
          · constructor
            · exact a1_left_right_left
            · rewrite [← a1_left_left]
              simp only [List.length_append, Nat.add_sub_cancel, List.take_left']
              unfold derivative
              simp only [List.cons_append, Set.mem_setOf_eq, List.append_nil]
              exact a1_right_left
        · rewrite [ih] at a1_right_right
          simp only [Set.mem_iUnion, exists_prop] at a1_right_right
          exact a1_right_right
      · intro a1
        obtain ⟨i, ⟨⟨a1_left_left, ⟨a1_left_right_left, a1_left_right_right⟩⟩, ⟨j, a1_right⟩⟩⟩ := a1

        unfold derivative at a1_left_right_right
        simp only [List.cons_append, Set.mem_setOf_eq, List.append_nil] at a1_left_right_right

        specialize ih i a1_left_left a1_left_right_left

        simp only [List.IsSuffix] at a1_left_left
        obtain ⟨t, ht⟩ := a1_left_left

        rewrite [← ht] at a1_left_right_right
        simp only [List.length_append, Nat.add_sub_cancel, List.take_left'] at a1_left_right_right

        apply Exists.intro (derivative (kleene_closure α L) i)
        constructor
        · apply Exists.intro t
          apply Exists.intro i
          constructor
          · exact ht
          · constructor
            · exact a1_left_right_left
            · simp only [Language.nullify]
              split
              case isTrue c1 =>
                rewrite [concat_eps_left]
                apply Eq.refl
              case isFalse c1 =>
                unfold derivative at c1
                simp only [List.cons_append, List.nil_append, Set.mem_setOf_eq, List.append_nil] at c1
                contradiction
        · rewrite [ih]
          simp only [Set.mem_iUnion, exists_prop]
          apply Exists.intro j
          exact a1_right
termination_by s.length


end Language

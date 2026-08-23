import FormalLanguageLean.RegExp.Derivative


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


example
  {α : Type}
  [DecidableEq α]
  (R S : RegExp α)
  (a : α)
  (h1 : R.LanguageOf = S.LanguageOf) :
  (R.derivative a).LanguageOf = (S.derivative a).LanguageOf :=
  by
    simp only [regexp_lang_derivative_eq_regexp_derivative_lang]
    rewrite [h1]
    apply Eq.refl


def finset_regexp_language_of
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α)) :
  Language α :=
  ⋃ (R ∈ Γ), R.LanguageOf


def derivative_of_finset_wrt_char
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  Finset (RegExp α) :=
  Finset.biUnion Γ (fun (R : RegExp α) => {RegExp.derivative R a})


theorem regexp_lang_derivative_of_finset_wrt_char_eq_regexp_derivative_of_finset_wrt_char_lang
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  finset_regexp_language_of (RegExp.derivative_of_finset_wrt_char Γ a) = Language.derivative (finset_regexp_language_of Γ) [a] :=
  by
    rewrite [RegExp.derivative_of_finset_wrt_char]
    simp only [finset_regexp_language_of]
    simp only [Finset.mem_biUnion, Finset.mem_singleton, Set.iUnion_exists, Set.biUnion_and',
      Set.iUnion_iUnion_eq_left]
    simp only [regexp_lang_derivative_eq_regexp_derivative_lang]
    rewrite [Language.derivative_distrib_union_of_finset_wrt_str]
    apply Eq.refl


def derivative_of_finset_wrt_str
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  Finset (RegExp α) :=
  Finset.biUnion Γ (fun (R : RegExp α) => {RegExp.derivative_wrt_str R s})


theorem regexp_lang_derivative_of_finset_wrt_str_eq_regexp_derivative_of_finset_wrt_str_lang
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  finset_regexp_language_of (RegExp.derivative_of_finset_wrt_str Γ s) = Language.derivative (finset_regexp_language_of Γ) s :=
  by
    rewrite [RegExp.derivative_of_finset_wrt_str]
    simp only [finset_regexp_language_of]
    simp only [Finset.mem_biUnion, Finset.mem_singleton, Set.iUnion_exists, Set.biUnion_and',
      Set.iUnion_iUnion_eq_left]
    simp only [regexp_lang_derivative_wrt_str_eq_regexp_derivative_lang]
    rewrite [Language.derivative_distrib_union_of_finset_wrt_str]
    apply Eq.refl


def concat_finset_regexp_regexp
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (β : RegExp α) :
  Finset (RegExp α) :=
  if ¬ β = RegExp.zero
  -- Finset { α β | α ∈ Γ }
  then Γ.image (fun α => RegExp.concat α β)
  else ∅


def partial_derivative_wrt_char
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  Finset (RegExp α) :=
  match RE with
  | char b => if a = b then {epsilon} else ∅
  | epsilon => ∅
  | zero => ∅
  | union α β => (α.partial_derivative_wrt_char a) ∪ (β.partial_derivative_wrt_char a)
  | concat α β =>
      if α.is_nullable
      then (concat_finset_regexp_regexp (α.partial_derivative_wrt_char a) β) ∪ (β.partial_derivative_wrt_char a)
      else (concat_finset_regexp_regexp (α.partial_derivative_wrt_char a) β)
  | kleene_closure α => concat_finset_regexp_regexp (α.partial_derivative_wrt_char a) (RegExp.kleene_closure α)


def partial_derivative_of_finset_wrt_char
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  Finset (RegExp α) :=
  Finset.biUnion Γ (fun (R : RegExp α) => partial_derivative_wrt_char R a)


def partial_derivative_of_finset_wrt_str_aux
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α)) :
  Str α → Finset (RegExp α)
  | [] => Γ
  | hd :: tl => RegExp.partial_derivative_of_finset_wrt_str_aux (RegExp.partial_derivative_of_finset_wrt_char Γ hd) tl


def partial_derivative_wrt_str
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  Finset (RegExp α) :=
  RegExp.partial_derivative_of_finset_wrt_str_aux {RE} s


def partial_derivative_of_finset_wrt_str
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  Finset (RegExp α) :=
  RegExp.partial_derivative_of_finset_wrt_str_aux Γ s


theorem partial_derivative_wrt_str_aux_last
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α)
  (a : α) :
  RegExp.partial_derivative_of_finset_wrt_str_aux Γ (s ++ [a]) =
    RegExp.partial_derivative_of_finset_wrt_char (RegExp.partial_derivative_of_finset_wrt_str_aux Γ s) a :=
  by
    induction s generalizing Γ
    case nil =>
      simp only [List.nil_append]
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
    case cons hd tl ih =>
      simp only [List.cons_append]
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
      apply ih


theorem partial_derivative_wrt_str_last
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α)
  (a : α) :
  RegExp.partial_derivative_wrt_str RE (s ++ [a]) =
    RegExp.partial_derivative_of_finset_wrt_char (RegExp.partial_derivative_wrt_str RE s) a :=
  by
    simp only [RegExp.partial_derivative_wrt_str]
    apply partial_derivative_wrt_str_aux_last


theorem partial_derivative_lang_eq_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  finset_regexp_language_of (RE.partial_derivative_wrt_char a) = Language.derivative RE.LanguageOf [a] :=
  by
    simp only [finset_regexp_language_of]
    induction RE
    case char b =>
      simp only [Language.derivative]
      ext cs
      simp only [Set.mem_iUnion, exists_prop, List.cons_append, List.nil_append, Set.mem_setOf_eq]
      unfold RegExp.partial_derivative_wrt_char
      split
      case isTrue c1 =>
        simp only [Finset.mem_singleton, exists_eq_left]
        unfold RegExp.LanguageOf
        simp only [Set.mem_singleton_iff, List.cons.injEq]
        constructor
        · intro a1
          exact ⟨c1, a1⟩
        · intro a1
          obtain ⟨a1_left, a1_right⟩ := a1
          exact a1_right
      case isFalse c1 =>
        simp only [RegExp.LanguageOf]
        constructor
        · intro a1
          obtain ⟨i, ⟨a1_left, a1_right⟩⟩ := a1
          simp only [Finset.notMem_empty] at a1_left
        · intro a1
          simp only [Set.mem_singleton_iff, List.cons.injEq] at a1
          obtain ⟨a1_left, a1_right⟩ := a1
          contradiction
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_eps_wrt_char]
      unfold RegExp.partial_derivative_wrt_char
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_empty_wrt_char]
      unfold RegExp.partial_derivative_wrt_char
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_union_wrt_char]
      unfold RegExp.partial_derivative_wrt_char
      simp only [Finset.set_biUnion_union]
      rewrite [R_ih]
      rewrite [S_ih]
      apply Eq.refl
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_concat_wrt_char]

      ext cs

      simp only [Set.mem_iUnion, exists_prop, Set.mem_union]
      rewrite [← R_ih]
      rewrite [← S_ih]
      rewrite [← Language.concat_distrib_finset_i_union_right]
      simp only [Set.mem_iUnion, exists_prop]

      constructor
      · intro a1
        obtain ⟨i, ⟨a1_left, a1_right⟩⟩ := a1

        simp only [RegExp.partial_derivative_wrt_char] at a1_left
        unfold concat_finset_regexp_regexp at a1_left

        split at a1_left
        case isTrue c1 =>
          simp only [regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
          simp only [Language.is_nullable_iff_nullify_eq_eps_singleton] at c1
          rewrite [c1]
          simp only [Language.concat_eps_left]

          simp only [Finset.mem_union] at a1_left
          cases a1_left
          case inl a1_left =>
            split at a1_left
            case isTrue c2 =>
              simp only [Finset.mem_image] at a1_left
              obtain ⟨j, ⟨a1_left_left, a1_left_right⟩⟩ := a1_left
              rewrite [← a1_left_right] at a1_right
              unfold LanguageOf at a1_right
              left
              apply Exists.intro j
              exact ⟨a1_left_left, a1_right⟩
            case isFalse c2 =>
              simp only [Finset.notMem_empty] at a1_left
          case inr a1_left =>
            right
            simp only [Set.mem_iUnion, exists_prop]
            apply Exists.intro i
            exact ⟨a1_left, a1_right⟩
        case isFalse c1 =>
          split at a1_left
          case isTrue c2 =>
            simp only [Finset.mem_image] at a1_left
            obtain ⟨j, ⟨a1_left_left, a1_left_right⟩⟩ := a1_left
            rewrite [← a1_left_right] at a1_right
            unfold LanguageOf at a1_right

            left
            apply Exists.intro j
            exact ⟨a1_left_left, a1_right⟩
          case isFalse c2 =>
            simp only [Finset.notMem_empty] at a1_left
      · intro a1
        simp only [RegExp.partial_derivative_wrt_char]
        unfold concat_finset_regexp_regexp

        cases a1
        case inl a1 =>
          obtain ⟨i, ⟨a1_left, a1_right⟩⟩ := a1

          split
          case isTrue c1 =>
            simp only [Finset.mem_union]
            split
            case isTrue c2 =>
              simp only [Finset.mem_image]
              apply Exists.intro (i.concat S)
              constructor
              · left
                apply Exists.intro i
                constructor
                · exact a1_left
                · apply Eq.refl
              · unfold LanguageOf
                exact a1_right
            case isFalse c2 =>
              simp only [Decidable.not_not] at c2
              rewrite [c2] at a1_right
              simp only [LanguageOf] at a1_right
              simp only [Language.concat_empty_right] at a1_right
              simp only [Set.mem_empty_iff_false] at a1_right
          case isFalse c1 =>
            split
            case isTrue c2 =>
              simp only [Finset.mem_image]
              apply Exists.intro (i.concat S)
              constructor
              · apply Exists.intro i
                constructor
                · exact a1_left
                · apply Eq.refl
              · unfold LanguageOf
                exact a1_right
            case isFalse c2 =>
              simp only [Decidable.not_not] at c2
              rewrite [c2] at a1_right
              simp only [LanguageOf] at a1_right
              simp only [Language.concat_empty_right] at a1_right
              simp only [Set.mem_empty_iff_false] at a1_right
        case inr a1 =>
          split
          case isTrue c1 =>
            simp only [regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
            simp only [Language.is_nullable_iff_nullify_eq_eps_singleton] at c1
            rewrite [c1] at a1
            simp only [Language.concat_eps_left] at a1
            simp only [Set.mem_iUnion, exists_prop] at a1
            obtain ⟨i, ⟨a1_left, a1_right⟩⟩ := a1

            simp only [Finset.mem_union]

            split
            case isTrue c2 =>
              simp only [Finset.mem_image]
              apply Exists.intro i
              constructor
              · right
                exact a1_left
              · exact a1_right
            case isFalse c2 =>
              apply Exists.intro i
              constructor
              · right
                exact a1_left
              · exact a1_right
          case isFalse c1 =>
            obtain s1 := not_regexp_is_nullable_imp_regexp_lang_nullify_eq_empty R c1
            rewrite [s1] at a1
            simp only [Language.concat_empty_left] at a1
            simp only [Set.mem_empty_iff_false] at a1
    case kleene_closure R R_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_kleene_closure_wrt_char]
      simp only [RegExp.partial_derivative_wrt_char]
      simp only [concat_finset_regexp_regexp]
      simp?
      simp only [RegExp.LanguageOf]
      rewrite [Language.concat_distrib_finset_i_union_right]
      rewrite [R_ih]
      apply Eq.refl


theorem partial_derivative_wrt_char_lang_eq_derivative_lang_wrt_char
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  finset_regexp_language_of (RegExp.partial_derivative_of_finset_wrt_char Γ a) = Language.derivative (finset_regexp_language_of Γ) [a] :=
  by
    simp only [finset_regexp_language_of]
    simp only [← Language.derivative_distrib_union_of_finset_wrt_str]
    simp only [RegExp.partial_derivative_of_finset_wrt_char]
    simp only [Finset.mem_biUnion, Set.iUnion_exists, Set.biUnion_and']
    sorry


theorem partial_derivative_wrt_str_lang_eq_derivative_lang_wrt_str
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  finset_regexp_language_of (RegExp.partial_derivative_of_finset_wrt_str Γ s) = Language.derivative (finset_regexp_language_of Γ) s :=
  by
    induction s generalizing Γ
    case nil =>
      simp only [RegExp.partial_derivative_of_finset_wrt_str]
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
      simp only [Language.derivative_wrt_eps]
    case cons hd tl ih =>
      simp only [RegExp.partial_derivative_of_finset_wrt_str] at ih

      simp only [RegExp.partial_derivative_of_finset_wrt_str]
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
      rewrite [Language.derivative_wrt_cons]
      sorry


end RegExp

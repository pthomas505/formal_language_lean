import FormalLanguageLean.RegExp.Nullable


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


def derivative
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  RegExp α :=
  match RE with
  | char b => if a = b then epsilon else zero
  | epsilon => zero
  | zero => zero
  | union R S => union (R.derivative a) (S.derivative a)
  | concat R S => union (concat (R.derivative a) S) (concat R.nullify (S.derivative a))
  | kleene_closure R => concat (R.derivative a) (kleene_closure R)


def derivative_wrt_str
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  Str α → RegExp α
  | [] => RE
  | hd :: tl => RegExp.derivative_wrt_str (RegExp.derivative RE hd) tl


theorem regexp_lang_derivative_eq_regexp_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  (RE.derivative a).LanguageOf = Language.derivative RE.LanguageOf [a] :=
  by
    induction RE
    all_goals
      unfold RegExp.derivative
    case char c =>
      split
      case isTrue c1 =>
        rewrite [c1]
        unfold RegExp.LanguageOf
        rewrite [Language.derivative_of_char_wrt_same_char]
        apply Eq.refl
      case isFalse c1 =>
        unfold RegExp.LanguageOf
        rewrite [Language.derivative_of_char_wrt_diff_char a c c1]
        apply Eq.refl
    case epsilon =>
      unfold RegExp.LanguageOf
      rewrite [Language.derivative_of_eps_wrt_char]
      apply Eq.refl
    case zero =>
      unfold RegExp.LanguageOf
      rewrite [Language.derivative_of_empty_wrt_char]
      apply Eq.refl
    case union R S R_ih S_ih =>
      unfold RegExp.LanguageOf
      rewrite [R_ih]
      rewrite [S_ih]
      rewrite [Language.derivative_of_union_wrt_char]
      apply Eq.refl
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      rewrite [R_ih]
      rewrite [S_ih]
      rewrite [Language.derivative_of_concat_wrt_char]
      rewrite [regexp_nullify_lang_eq_regexp_lang_nullify]
      apply Eq.refl
    case kleene_closure R ih =>
      simp only [RegExp.LanguageOf]
      rewrite [ih]
      rewrite [Language.derivative_of_kleene_closure_wrt_char]
      apply Eq.refl


theorem regexp_lang_derivative_wrt_str_eq_regexp_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  (RE.derivative_wrt_str s).LanguageOf = Language.derivative RE.LanguageOf s :=
  by
    induction s generalizing RE
    case nil =>
      rewrite [RegExp.derivative_wrt_str]
      rewrite [Language.derivative_wrt_eps]
      apply Eq.refl
    case cons hd tl ih =>
      rewrite [RegExp.derivative_wrt_str]
      rewrite [Language.derivative_wrt_cons]
      rewrite [← regexp_lang_derivative_eq_regexp_derivative_lang]
      apply ih


def matches_string
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  Str α → Prop
  | [] => RE.is_nullable
  | hd :: tl => (RE.derivative hd).matches_string tl


instance
  (α : Type)
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  Decidable (RE.matches_string s) :=
  by
    induction s generalizing RE
    all_goals
      unfold RegExp.matches_string
      infer_instance


#eval RegExp.matches_string (RegExp.char 'c') ['c']
#eval RegExp.matches_string (RegExp.char 'c') ['d']
#eval RegExp.matches_string (RegExp.concat (RegExp.kleene_closure (RegExp.char 'c')) (RegExp.char 'd')) ['c', 'c', 'd']


example
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  RE.matches_string s ↔ s ∈ RE.LanguageOf :=
  by
    induction s generalizing RE
    case nil =>
      unfold RegExp.matches_string
      apply regexp_is_nullable_iff_eps_mem_lang_of
    case cons hd tl ih =>
      unfold RegExp.matches_string
      rewrite [ih]
      rewrite [regexp_lang_derivative_eq_regexp_derivative_lang]
      unfold Language.derivative
      simp only [List.cons_append, List.nil_append, Set.mem_setOf_eq]


end RegExp

import FormalLanguageLean.Regular


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


inductive RegExp (α : Type) : Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | kleene_closure : RegExp α → RegExp α
  deriving Inhabited, DecidableEq

compile_inductive% RegExp


namespace RegExp


def LanguageOf
  {α : Type} :
  RegExp α → Language α
  | char c => {[c]}
  | epsilon => {[]}
  | zero => ∅
  | union R S => R.LanguageOf ∪ S.LanguageOf
  | concat R S => Language.concat R.LanguageOf S.LanguageOf
  | kleene_closure R => Language.kleene_closure α R.LanguageOf


example
  {α : Type}
  (RE : RegExp α) :
  Language.IsRegLang RE.LanguageOf :=
  by
    induction RE
    case char c =>
      unfold RegExp.LanguageOf
      exact Language.IsRegLang.char c
    case epsilon =>
      unfold RegExp.LanguageOf
      exact Language.IsRegLang.epsilon
    case zero =>
      unfold RegExp.LanguageOf
      exact Language.IsRegLang.zero
    case union R S R_ih S_ih =>
      unfold RegExp.LanguageOf
      apply Language.IsRegLang.union
      · exact R_ih
      · exact S_ih
    case concat R S R_ih S_ih =>
      unfold RegExp.LanguageOf
      apply Language.IsRegLang.concat
      · exact R_ih
      · exact S_ih
    case kleene_closure R ih =>
      unfold RegExp.LanguageOf
      apply Language.IsRegLang.kleene_closure
      exact ih


end RegExp

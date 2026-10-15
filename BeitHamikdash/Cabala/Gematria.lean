import BeitHamikdash.Cabala.SeferYetzirah

/-!
# Gematria

A gematria padrão (*mispar hechrechi*) atribui a cada letra um valor
(1–9, 10–90, 100–400) e soma os valores de uma palavra.

O resultado mais importante deste arquivo é **negativo**: a gematria não é injetiva.
Palavras diferentes têm o mesmo valor (אחד "um" e אהבה "amor" valem 13). Por isso
uma igualdade de valores não pode, sozinha, provar uma ligação entre conceitos.
-/

namespace BeitHamikdash.Cabala

open Letra

/-- Valor padrão de cada letra (formas finais não são distinguidas). -/
def valor : Letra → ℕ
  | alef => 1 | bet => 2 | gimel => 3 | dalet => 4 | he => 5
  | vav => 6 | zayin => 7 | chet => 8 | tet => 9
  | yod => 10 | kaf => 20 | lamed => 30 | mem => 40 | nun => 50
  | samekh => 60 | ayin => 70 | pe => 80 | tsadi => 90
  | qof => 100 | resh => 200 | shin => 300 | tav => 400

/-- Uma palavra é uma sequência de letras. -/
abbrev Palavra := List Letra

def gematria (w : Palavra) : ℕ := (w.map valor).sum

@[simp] theorem gematria_nil : gematria [] = 0 := rfl

/-- A gematria é aditiva sobre a concatenação de palavras. -/
@[simp] theorem gematria_append (u v : Palavra) :
    gematria (u ++ v) = gematria u + gematria v := by
  simp [gematria]

/-- As 22 letras somam 1495. -/
theorem soma_alfabeto : ∑ l, valor l = 1495 := by decide

/-- יהוה, o Tetragrama. -/
def tetragrama : Palavra := [yod, he, vav, he]
/-- אחד, "um". -/
def echad : Palavra := [alef, chet, dalet]
/-- אהבה, "amor". -/
def ahavah : Palavra := [alef, he, bet, he]

theorem gematria_tetragrama : gematria tetragrama = 26 := rfl
theorem gematria_echad : gematria echad = 13 := rfl
theorem gematria_ahavah : gematria ahavah = 13 := rfl

/-- **A gematria não é injetiva**: perde informação. -/
theorem gematria_nao_injetiva : ¬ Function.Injective gematria := fun h =>
  absurd (h (gematria_echad.trans gematria_ahavah.symm)) (by decide)

/-- As quatro letras do Tetragrama, uma por mundo (atribuição tradicional:
י Atzilut, ה Beriah, ו Yetzirah, ה Assiah). -/
def letraDoMundo : Mundo → Letra
  | .atzilut => yod
  | .beriah => he
  | .yetzirah => vav
  | .assiah => he

theorem mundos_soletram_tetragrama :
    [Mundo.atzilut, .beriah, .yetzirah, .assiah].map letraDoMundo = tetragrama := rfl

end BeitHamikdash.Cabala

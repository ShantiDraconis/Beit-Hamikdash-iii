import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Card

/-!
# As dez Sefirot

Fonte: *Sefer Yetzirah*, cap. 1 ("dez sefirot *belimah*: dez e não nove, dez e não
onze"); nomenclatura clássica de Cordovero (*Pardes Rimonim*) e da tradição luriânica.

Aqui as sefirot são apenas um tipo finito. Tudo o que se prova é estrutura
(contagens, partições, ordens). Nada aqui afirma ou nega significado místico.
-/

namespace BeitHamikdash.Cabala

/-- As dez sefirot. *Da'at* fica de fora, como na maior parte das listas clássicas. -/
inductive Sefirah
  | keter | chokhmah | binah
  | chesed | gevurah | tiferet
  | netzach | hod | yesod
  | malkhut
  deriving DecidableEq, Repr, Fintype

namespace Sefirah

/-- "Dez e não nove, dez e não onze." -/
theorem card_eq_dez : Fintype.card Sefirah = 10 := by decide

/-- Os três pilares da Árvore. -/
inductive Pilar
  | misericordia  -- direita: Chokhmah, Chesed, Netzach
  | rigor         -- esquerda: Binah, Gevurah, Hod
  | equilibrio    -- centro: Keter, Tiferet, Yesod, Malkhut
  deriving DecidableEq, Repr, Fintype

/-- O pilar de cada sefirah. -/
def pilar : Sefirah → Pilar
  | chokhmah | chesed | netzach => .misericordia
  | binah | gevurah | hod => .rigor
  | keter | tiferet | yesod | malkhut => .equilibrio

/-- Os pilares laterais têm 3 sefirot cada; o central tem 4. -/
theorem tamanho_pilares :
    (Finset.univ.filter (pilar · = .misericordia)).card = 3 ∧
    (Finset.univ.filter (pilar · = .rigor)).card = 3 ∧
    (Finset.univ.filter (pilar · = .equilibrio)).card = 4 := by
  decide

/-- Os pilares laterais são espelhos: a troca direita ↔ esquerda é uma involução
das sefirot que fixa exatamente o pilar central. -/
def espelho : Sefirah → Sefirah
  | chokhmah => binah | binah => chokhmah
  | chesed => gevurah | gevurah => chesed
  | netzach => hod | hod => netzach
  | s => s

theorem espelho_involutivo : ∀ s, espelho (espelho s) = s := by decide

theorem espelho_fixa_centro : ∀ s, espelho s = s ↔ pilar s = .equilibrio := by decide

end Sefirah

/-- Os quatro mundos, na ordem da emanação (do mais alto ao mais baixo). -/
inductive Mundo
  | atzilut   -- emanação
  | beriah    -- criação
  | yetzirah  -- formação
  | assiah    -- ação
  deriving DecidableEq, Repr, Fintype

theorem Mundo.card_eq_quatro : Fintype.card Mundo = 4 := by decide

end BeitHamikdash.Cabala

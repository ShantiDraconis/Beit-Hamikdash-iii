import BeitHamikdash.Cabala.Sefirot
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# A Árvore da Vida como grafo

Os 22 caminhos seguem a disposição de Athanasius Kircher (*Oedipus Aegyptiacus*, 1652),
a mais difundida. As disposições do Gra (Vilna Gaon) e do Ari mudam alguns caminhos;
cada uma pode entrar aqui como outro grafo, com os mesmos teoremas reverificados.

O que se prova:
* 10 vértices e 22 arestas;
* o grafo é conexo;
* Tiferet é o único vértice de grau máximo (8);
* a tríade superior (Keter, Chokhmah, Binah) forma um triângulo;
* o posto cíclico |E| − |V| + 1 vale 13.
-/

namespace BeitHamikdash.Cabala

open Sefirah

/-- Os 22 caminhos, segundo Kircher. -/
def caminhos : List (Sefirah × Sefirah) :=
  [(keter, chokhmah), (keter, binah), (keter, tiferet),
   (chokhmah, binah), (chokhmah, tiferet), (chokhmah, chesed),
   (binah, tiferet), (binah, gevurah),
   (chesed, gevurah), (chesed, tiferet), (chesed, netzach),
   (gevurah, tiferet), (gevurah, hod),
   (tiferet, netzach), (tiferet, yesod), (tiferet, hod),
   (netzach, hod), (netzach, yesod), (netzach, malkhut),
   (hod, yesod), (hod, malkhut),
   (yesod, malkhut)]

theorem caminhos_length : caminhos.length = 22 := rfl

/-- A Árvore da Vida como grafo simples. -/
def arvore : SimpleGraph Sefirah :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ caminhos

instance : DecidableRel arvore.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ caminhos ∨ (b, a) ∈ caminhos)))

/-- Tiferet, o coração da Árvore, toca 8 das outras 9 sefirot (todas menos Malkhut). -/
theorem grau_tiferet : arvore.degree tiferet = 8 := by decide

/-- Tiferet é o único vértice de grau máximo. -/
theorem tiferet_unico_grau_maximo :
    (∀ s, arvore.degree s ≤ 8) ∧ (∀ s, arvore.degree s = 8 → s = tiferet) := by
  decide

theorem soma_dos_graus : ∑ s, arvore.degree s = 44 := by decide

/-- Os 22 caminhos são de fato 22 arestas distintas (lema do aperto de mãos). -/
theorem num_arestas : arvore.edgeFinset.card = 22 := by
  have h := arvore.sum_degrees_eq_twice_card_edges
  rw [soma_dos_graus] at h
  omega

/-- A tríade superior forma um triângulo. -/
theorem triade_superior :
    arvore.Adj keter chokhmah ∧ arvore.Adj chokhmah binah ∧ arvore.Adj binah keter := by
  decide

private theorem passo (a b : Sefirah) (h : arvore.Adj a b := by decide) :
    arvore.Reachable a b :=
  h.reachable

/-- De Keter se chega a qualquer sefirah. -/
theorem alcanca_de_keter : ∀ s, arvore.Reachable keter s
  | keter => .refl _
  | chokhmah => passo _ _
  | binah => passo _ _
  | tiferet => passo _ _
  | chesed => (passo keter chokhmah).trans (passo _ _)
  | gevurah => (passo keter binah).trans (passo _ _)
  | netzach => (passo keter tiferet).trans (passo _ _)
  | hod => (passo keter tiferet).trans (passo _ _)
  | yesod => (passo keter tiferet).trans (passo _ _)
  | malkhut => ((passo keter tiferet).trans (passo tiferet yesod)).trans (passo _ _)

/-- A Árvore é conexa. -/
theorem arvore_conexa : arvore.Connected where
  preconnected a b := (alcanca_de_keter a).symm.trans (alcanca_de_keter b)

/-- Posto cíclico |E| − |V| + 1. Para um grafo conexo, é o número de ciclos
independentes (a dimensão do espaço de ciclos). Esse fato geral não é provado aqui;
aqui só se calcula o número para a Árvore. -/
def postoCiclico : ℕ := arvore.edgeFinset.card + 1 - Fintype.card Sefirah

theorem postoCiclico_eq : postoCiclico = 13 := by
  rw [postoCiclico, num_arestas, card_eq_dez]

end BeitHamikdash.Cabala

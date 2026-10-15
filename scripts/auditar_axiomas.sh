#!/usr/bin/env bash
# Roda os #print axioms de BeitHamikdash/Auditoria.lean e falha se aparecer
# qualquer axioma além de propext, Classical.choice e Quot.sound.
set -euo pipefail

saida=$(lake env lean BeitHamikdash/Auditoria.lean 2>&1)
echo "$saida"

usados=$(echo "$saida" | tr '\n' ' ' \
  | grep -oE "depends on axioms: \[[^]]*\]" \
  | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' | sed '/^$/d' | sort -u || true)

ruins=$(echo "$usados" | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sed '/^$/d' || true)

if [ -n "$ruins" ]; then
  echo "Axiomas fora do padrão encontrados:"
  echo "$ruins"
  exit 1
fi
echo "OK: só axiomas padrão (propext, Classical.choice, Quot.sound)."

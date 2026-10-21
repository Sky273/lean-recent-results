# Journal — vérification de résultats récents

Ce projet fait suite au projet `OreDirac`, dont le journal explique pourquoi : la formalisation
des théorèmes classiques de graphes y est apparue déjà largement couverte. Choix fait le
21 octobre 2026 : vérifier des résultats **récents** (2025-2026), courts, sans formalisation Lean
publique connue.

## 2026-10-21 — Recherche, sélection, vérifications

**Recherche.**

- Sources : la base de données des problèmes d'Erdős (teorth/erdosproblems) et des articles arXiv
  récents.
- Index de couverture Lean : 5 285 entrées issues de formal-conjectures, plby/lean-proofs,
  openai/math, 547 dépôts GitHub et du registre Palomar. Constat : la plupart des problèmes
  d'Erdős résolus ont déjà une preuve Lean revendiquée.
- 24 candidats bruts, 8 finalistes, chacun évalué puis contre-vérifié par un agent indépendant.

**Résultat.** Six vérifications complètes :

- Noel, coloriage total par listes ;
- Noel, coloriage partiel par listes ;
- Erdős n° 33 ;
- Park, Fibonacci ;
- Erdős n° 64 en petit diamètre ;
- Xu, bases additives.

Deux vérifications partielles (Hu–Zhang et Erdős n° 290) sont conservées localement et ne sont
pas publiées.

**Contrôles mécaniques :**

- `lake build` réussit ;
- `#print axioms` sur les théorèmes principaux ne donne que les axiomes standard ;
- `leanchecker` réussit module par module, et un contrôle négatif échoue comme attendu.

**Contrôle de fidélité à l'aveugle.** Pour chaque résultat, un agent qui n'avait pas vu nos
fichiers a réécrit les énoncés depuis la source (`Fidelity/Blind/`). Un second agent les a
démontrés à partir de nos théorèmes (`Fidelity/`). Verdict : les six énoncés sont fidèles, avec
des écarts de portée documentés dans `AUDIT.md`.

**Relecture critique avant publication.** Deux relecteurs par résultat (spécialiste du domaine,
expert Lean), puis une contre-vérification de chaque point sérieux. Aucun problème critique.
Corrections apportées :

- attributions précisées ;
- description des travaux antérieurs corrigée (plby pour Xu) ;
- portée d'Erdős n° 64 précisée (degré minimum ≥ 4 en diamètre 3) ;
- conjecture d'Iradmusa nommée ;
- théorème du diamètre 3 renommé de façon neutre ;
- en-têtes et commentaires obsolètes nettoyés.

**Remarques sur la valeur de ces vérifications.**

- Pour les contre-exemples finis (Noel, Park), la vérification formelle confirme ce qu'un
  programme permettait déjà de contrôler. Elle apporte surtout une garantie de bout en bout.
- Pour Erdős n° 64 en diamètre 3, la preuve publiée a été produite par une IA, et ses auteurs
  demandaient explicitement une vérification indépendante.

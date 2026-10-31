# EA

Aqui (EA/) estão formalizadas e respondidas várias das questões das duas listas de exercícios da disciplina de Estruturas Algébricas. 

Eu evitei ao máximo usar definições da Mathlib e da STD.

Também tentei resolver o mesmo probllema de formas diferentes! Então, em alguns momentos eu adiciono parte do enunciado das questões como variáveis (`variable ...`), que ficam adicionadas como parte da assinatura das funções; Em outros momentos eu uso axiomas (`axiom ...`), que o Lean aceita como verdade absoluta; e, em outros momentos, eu crio classes específicas para designar esses comportamento (como o `UniqResSemiGroup`).

Sobre as `tactics`: 

- Eu uso bastante o `rw [a = b]`, que reescreve toda ocorrência de `a` com `b` no alvo (as igualdades aqui tem lado certo! `a = b` reescreve apenas `a` por `b`. Se eu quero rescrever `b` com `a`, eu uso `rw [<- a = b]`

- `apply (h : P -> Q)` substitui `Q` por `P` no alvo. É como se eu dissesse: Se eu já sei que `P` implica `Q` e quero mostrar `Q`, basta então mostrar `P`.

- `simp`: Aplica vários teoremas de reescrita predefinidos até que não consiga mais. Eu usei mais quando o alvo dependia de manipulações algébricas óbvias, mas chatas de fazer.

- `grind`: Essa é realmente parte de um provador automático de teoremas. É bem mais forte que o `simp`. Eu usei só quando já tinha feito uma demonstração muito parecida.

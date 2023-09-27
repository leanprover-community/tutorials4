import Mathlib.Data.Real.Basic

open Classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations. It comes after the file `07FirstNegations`.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contra` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/
section NegationProp

variable (P Q : Prop)

-- 0055
example : P → Q ↔ ¬Q → ¬P := by
  sorry

-- 0056
theorem non_imp (P Q : Prop) : ¬(P → Q) ↔ P ∧ ¬Q := by
  sorry

-- In the next one, let's use the axiom
-- `propext {P Q : Prop} : (P ↔ Q) → P = Q`
-- 0057
example (P : Prop) : ¬P ↔ P = False := by
  sorry

end NegationProp

section NegationQuantifiers

variable (X : Type) (P : X → Prop)

-- 0058
example : (¬∀ x, P x) ↔ ∃ x, ¬P x := by
  sorry

-- 0059
example : (¬∃ x, P x) ↔ ∀ x, ¬P x := by
  sorry

-- 0060
example (P : ℝ → Prop) : (¬∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬P ε := by
  sorry

-- 0061
example (P : ℝ → Prop) : (¬∀ x > 0, P x) ↔ ∃ x > 0, ¬P x := by
  sorry

end NegationQuantifiers


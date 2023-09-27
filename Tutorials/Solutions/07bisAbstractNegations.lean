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
  -- sorry
  constructor
  · intro h hnQ hP
    exact hnQ (h hP)
  · intro h hP
    by_contra hnQ
    exact h hnQ hP
  -- sorry

-- 0056
theorem non_imp (P Q : Prop) : ¬(P → Q) ↔ P ∧ ¬Q := by
  -- sorry
  constructor
  · intro h
    by_contra H
    apply h
    intro hP
    by_contra H'
    apply H
    exact ⟨hP, H'⟩
  · intro h h'
    rcases h with ⟨hP, hnQ⟩
    exact hnQ (h' hP)
  -- sorry

-- In the next one, let's use the axiom
-- `propext {P Q : Prop} : (P ↔ Q) → P = Q`
-- 0057
example (P : Prop) : ¬P ↔ P = False := by
  -- sorry
  constructor
  · intro h
    apply propext
    constructor
    · intro h'
      exact h h'
    · intro h
      exfalso
      exact h
  · intro h
    rw [h]
    exact id
  -- sorry

end NegationProp

section NegationQuantifiers

variable (X : Type) (P : X → Prop)

-- 0058
example : (¬∀ x, P x) ↔ ∃ x, ¬P x := by
  -- sorry
  constructor
  · intro h
    by_contra H
    apply h
    intro x
    by_contra H'
    apply H
    use x
  · rintro ⟨x, hx⟩ h'
    exact hx (h' x)
  -- sorry

-- 0059
example : (¬∃ x, P x) ↔ ∀ x, ¬P x := by
  -- sorry
  constructor
  · intro h x h'
    apply h
    use x
  · rintro h ⟨x, hx⟩
    exact h x hx
  -- sorry

-- 0060
example (P : ℝ → Prop) : (¬∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬P ε := by
  -- sorry
  constructor
  · intro h ε ε_pos hP
    apply h
    use ε
  · rintro h ⟨ε, ε_pos, hP⟩
    exact h ε ε_pos hP
  -- sorry

-- 0061
example (P : ℝ → Prop) : (¬∀ x > 0, P x) ↔ ∃ x > 0, ¬P x := by
  -- sorry
  constructor
  · intro h
    by_contra H
    apply h
    intro x x_pos
    by_contra HP
    apply H
    use x
  · rintro ⟨x, xpos, hx⟩ h'
    exact hx (h' x xpos)
  -- sorry

end NegationQuantifiers

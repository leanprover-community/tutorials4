import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Parity

/- # Existential quantifiers

In this file, we learn how to handle the ∃ quantifier.

In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be an object from the local context
or a more complicated expression.

In the example below, `P x₀` is `8 = 2*4` which is true by definition so
Lean does not ask for a proof.
-/

example : ∃ n : ℕ, 8 = 2 * n := by
  use 4

/-
In order to use `h : ∃ x, P x`, we use the `rcases` tactic to fix
one `x₀` that works.

Again `h` can come straight from the local context or can be a more
complicated expression.
-/
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  -- Let's fix k₀ such that n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- It now suffices to prove k₀ + 1 > 0.
  rw [hk₀]
  -- and we have a lemma about this
  exact Nat.succ_pos k₀

/-
The next exercises use divisibility in ℤ (beware the ∣ symbol which is
not ASCII).

By definition, a ∣ b ↔ ∃ k, b = a*k, so you can prove a ∣ b using the
`use` tactic.
-/
-- Until the end of this file, a, b and c will denote integers, unless
-- explicitly stated otherwise
variable (a b c : ℤ)

-- 0029
example (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  sorry

/-
A very common pattern is to have an assumption or lemma asserting
  `h : ∃ x, y = ...`
and this is used through the combo:
  rcases h with ⟨x, hx⟩
  rw hx at ...
The tactic `rcases` allows us to simplify the above combo when the
name `hx` is replaced by the special name `rfl`, as in the following example.
-/
example (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  rcases h1 with ⟨k, rfl⟩
  rcases h2 with ⟨l, rfl⟩
  use k + l
  ring

/-
You can use the same `rfl` trick with the `rintro` tactic which
is a power powerful variant of `intro`.
-/
example : a ∣ b → a ∣ c → a ∣ b + c := by
  rintro ⟨k, rfl⟩ ⟨l, rfl⟩
  use k + l
  ring

-- 0030
example : 0 ∣ a ↔ a = 0 := by
  sorry

/-
We can now start combining quantifiers, using the definition

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`

-/
open Function

-- In the remaining of this file, f and g will denote functions from
-- ℝ to ℝ.
variable (f g : ℝ → ℝ)

-- 0031
example (h : Surjective (g ∘ f)) : Surjective g := by
  sorry

/-
The above exercise can be done in three lines. Try to do the
next exercise in four lines.
-/
-- 0032
example (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  sorry


import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Pi
import Tutorials.TutoLib
/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.

A sequence u is a function from ℕ to ℝ, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:

-- Definition of « u tends to l »
`def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, ...` which is an abbreviation of
`∀ ε, ε > 0 → ... `

In particular, a statement like `h : ∀ ε > 0, ...`
can be specialized to a given ε₀ by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also recall that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by` (followed by curly braces
if you need more than one tactic invocation).
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, ...

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.

We'll take this opportunity to use two new tactics:

`norm_num` will perform numerical normalization on the goal and `norm_num at h`
will do the same in assumption `h`. This will get rid of trivial calculations on numbers,
like replacing `|l - l|` by zero in the next exercise.
Its name stands for "normalize numbers".

`congr` will try to prove equalities between applications of functions by recursively
proving the arguments are the same. Its name stands for "congruence".
For instance, if the goal is `f x + g y = f z + g t` then congr will replace it by
two goals: `x = z` and `y = t`.
You can limit the recursion depth by specifying a natural number after `congr`.
For instance, in the above example, `congr 1` will give new goals
`f x = f z` and `g y = g t`, which only inspect arguments of the addition and not deeper.
-/
variable (u v w : ℕ → ℝ) (l l' : ℝ)

-- If u is constant with value l then u tends to l
-- 0033
example : (∀ n, u n = l) → SeqLimit u l := by
  sorry

/- When dealing with absolute values, we'll use lemmas:

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

You should probably write them down on a sheet of paper that you keep at
hand since they are used in many exercises.
-/
-- Assume l > 0. Then u tends to l implies u n ≥ l/2 for large enough n
-- 0034
example (hl : l > 0) : SeqLimit u l → ∃ N, ∀ n ≥ N, u n ≥ l / 2 := by
  sorry

/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

You should probably add them to the sheet of paper where you wrote
the `abs` lemmas since they are used in many exercises.

Let's see an example.
-/
-- If u tends to l and v tends l' then u+v tends to l+l'
example (hu : SeqLimit u l) (hv : SeqLimit v l') : SeqLimit (u + v) (l + l') := by
  intro ε ε_pos
  rcases hu (ε / 2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε / 2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rcases ge_max_iff.mp hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε / 2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε / 2 := hN₂ n (by linarith)
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')| := rfl
    _ = |u n - l + (v n - l')| := by congr ; ring
    _ ≤ |u n - l| + |v n - l'| := by apply abs_add
    _ ≤ ε := by linarith


/-
In the above proof, we used `have` to prepare facts for `linarith` consumption in the last line.
Since we have direct proof terms for them, we can feed them directly to `linarith` as in the next proof
of the same statement.
Another variation we introduce is rewriting using `ge_max_iff` and letting `linarith` handle the
conjunction, instead of creating two new assumptions.
-/
example (hu : SeqLimit u l) (hv : SeqLimit v l') : SeqLimit (u + v) (l + l') := by
  intro ε ε_pos
  rcases hu (ε / 2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε / 2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rw [ge_max_iff] at hn
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')| := rfl
    _ = |u n - l + (v n - l')| := by ring_nf
    _ ≤ |u n - l| + |v n - l'| := by apply abs_add
    _ ≤ ε := by linarith [hN₁ n (by linarith), hN₂ n (by linarith)]


-- Let's do something similar: the squeezing theorem.
-- 0035
example (hu : SeqLimit u l) (hw : SeqLimit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    SeqLimit v l := by
  sorry

-- What about < ε?
-- 0036
example (u l) : SeqLimit u l ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε := by
  sorry

/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`
-/
-- A sequence admits at most one limit
-- 0037
example : SeqLimit u l → SeqLimit u l' → l = l' := by
  sorry

/-
Let's now practice deciphering definitions before proving.

-/
def NonDecreasingSeq (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

def IsSeqSup (M : ℝ) (u : ℕ → ℝ) :=
  (∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- 0038
example (M : ℝ) (h : IsSeqSup M u) (h' : NonDecreasingSeq u) : SeqLimit u M := by
  sorry


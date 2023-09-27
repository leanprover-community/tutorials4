import Tutorials.TutoLib

/-
This file continues the elementary study of limits of sequences.
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

and the definition:

`def SeqLimit (u : ℕ → ℝ) (l : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

You can also use a property proved in the previous file:

`unique_limit : SeqLimit u l → SeqLimit u l' → l = l'`

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`
-/
variable {φ : ℕ → ℕ}

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
theorem id_le_extraction' : Extraction φ → ∀ n, n ≤ φ n := by
  intro hyp n
  induction' n with n hn
  · exact Nat.zero_le _
  · exact Nat.succ_le_of_lt (by linarith [hyp n (n + 1) (by linarith)])

-- 0039
/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
theorem extraction_ge : Extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  sorry

variable {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but does not it when displaying the goal.
-/
-- 0040
/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
theorem near_cluster : ClusterPoint u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  sorry

/-
The above exercice can be done in five lines.
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/
-- 0041
/-- If `u` tends to `l` then its subsequences tend to `l`. -/
theorem subseq_tendsto_of_tendsto' (h : SeqLimit u l) (hφ : Extraction φ) : SeqLimit (u ∘ φ) l := by
  sorry

-- 0042
/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
theorem cluster_limit (hl : SeqLimit u l) (ha : ClusterPoint u a) : a = l := by
  sorry

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, SeqLimit u l) → CauchySequence u := by
  sorry

/-
In the next exercise, you can reuse
 `near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε`
-/
-- 0044
example (hu : CauchySequence u) (hl : ClusterPoint u l) : SeqLimit u l := by
  sorry


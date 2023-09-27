import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Topology.Sequences

attribute [instance] Classical.propDecidable

def NonDecreasing (f : ℝ → ℝ) :=
  ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def NonIncreasing (f : ℝ → ℝ) :=
  ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

def EvenFun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

def OddFun (f : ℝ → ℝ) :=  ∀ x, f (-x) = -f x

/-
Lemmas from that file were hidden in my course, or restating things which
were proved without name in previous files.
-/
-- The mathlib version is unusable because it is stated in terms of ≤
theorem ge_max_iff {α : Type _} [LinearOrder α] {p q r : α} : r ≥ max p q ↔ r ≥ p ∧ r ≥ q :=
  max_le_iff

-- No idea why this is not in mathlib
theorem eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y := by
  intro h
  apply eq_of_abs_sub_nonpos
  by_contra H
  push_neg at H
  specialize h (|x - y| / 2) (by linarith)
  linarith

def SeqLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

theorem unique_limit {u l l'} : SeqLimit u l → SeqLimit u l' → l = l' := by
  intro hl hl'
  apply eq_of_abs_sub_le_all
  intro ε ε_pos
  specialize hl (ε / 2) (by linarith)
  rcases hl with ⟨N, hN⟩
  specialize hl' (ε / 2) (by linarith)
  rcases hl' with ⟨N', hN'⟩
  specialize hN (max N N') (le_max_left _ _)
  specialize hN' (max N N') (le_max_right _ _)
  calc
    |l - l'| = |l - u (max N N') + (u (max N N') - l')| := by ring_nf
    _ ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_add
    _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
    _ ≤ ε / 2 + ε / 2 := by linarith
    _ = ε := by ring


theorem le_of_le_add_all {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) → y ≤ x := by
  contrapose!
  intro h
  use (y - x) / 2
  constructor <;> linarith

def UpperBound (A : Set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def IsSup (A : Set ℝ) (x : ℝ) :=
  UpperBound A x ∧ ∀ y, UpperBound A y → x ≤ y

theorem lt_sup {A : Set ℝ} {x : ℝ} (hx : IsSup A x) : ∀ y, y < x → ∃ a ∈ A, y < a := by
  intro y
  contrapose!
  exact hx.right y

theorem squeeze {u v w : ℕ → ℝ} {l} (hu : SeqLimit u l) (hw : SeqLimit w l) (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n) : SeqLimit v l := by
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  rcases hw ε ε_pos with ⟨N', hN'⟩
  use max N N'
  intro n hn
  rw [ge_max_iff] at hn
  specialize hN n (by linarith)
  specialize hN' n (by linarith)
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor <;> linarith

def Extraction (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

def TendstoInfinity (u : ℕ → ℝ) :=
  ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

theorem lim_le {x y : ℝ} {u : ℕ → ℝ} (hu : SeqLimit u x) (ineg : ∀ n, u n ≤ y) : x ≤ y := by
  apply le_of_le_add_all
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  specialize hN N (by linarith)
  specialize ineg N
  rw [abs_le] at hN
  linarith

theorem inv_succ_le_all : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) ≤ ε := by
  convert Metric.tendsto_atTop.mp tendsto_one_div_add_atTop_nhds_0_nat using 0
  simp only [Real.dist_eq, sub_zero]
  constructor
  intro h ε ε_pos
  rcases h (ε / 2) (by linarith) with ⟨N, hN⟩
  use N
  intro n hn
  rw [abs_of_pos (Nat.one_div_pos_of_nat : 1 / (n + 1 : ℝ) > 0)]
  specialize hN n hn
  linarith
  intro h ε ε_pos
  rcases h ε (by linarith) with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  rw [abs_of_pos (@Nat.one_div_pos_of_nat ℝ _ n)] at hN
  linarith

theorem limit_const (x : ℝ) : SeqLimit (fun _ => x) x := fun ε ε_pos =>
  ⟨0, fun _ _ => by simp [le_of_lt ε_pos]⟩

theorem limit_of_sub_le_inv_succ {u : ℕ → ℝ} {x : ℝ} (h : ∀ n, |u n - x| ≤ 1 / (n + 1)) :
    SeqLimit u x := by
  intro ε ε_pos
  rcases inv_succ_le_all ε ε_pos with ⟨N, hN⟩
  use N
  intro n hn
  specialize h n
  specialize hN n hn
  linarith

theorem limit_const_add_inv_succ (x : ℝ) : SeqLimit (fun n => x + 1 / (n + 1)) x :=
  limit_of_sub_le_inv_succ fun n => by rw [abs_of_pos] <;> linarith [@Nat.one_div_pos_of_nat ℝ _ n]

theorem limit_const_sub_inv_succ (x : ℝ) : SeqLimit (fun n => x - 1 / (n + 1)) x := by
  refine' limit_of_sub_le_inv_succ fun n => _
  rw [show x - 1 / (n + 1) - x = -(1 / (n + 1)) by ring, abs_neg, abs_of_pos]
  linarith [@Nat.one_div_pos_of_nat ℝ _ n]

theorem id_le_extraction {φ} : Extraction φ → ∀ n, n ≤ φ n := by
  intro hyp n
  induction' n with n hn
  · exact Nat.zero_le _
  · exact Nat.succ_le_of_lt (by linarith [hyp n (n + 1) (by linarith)])

theorem seqLimit_id : TendstoInfinity fun n => n := by
  intro A
  rcases exists_nat_gt A with ⟨N, hN⟩
  use N
  intro n hn
  have : (n : ℝ) ≥ N; exact_mod_cast hn
  linarith

variable {u : ℕ → ℝ} {l : ℝ} {φ : ℕ → ℕ}

open Set Filter

def ClusterPoint (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, Extraction φ ∧ SeqLimit (u ∘ φ) a

theorem bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ Icc a b) :
    ∃ c ∈ Icc a b, ClusterPoint u c := by
  rcases(isCompact_Icc : IsCompact (Icc a b)).tendsto_subseq h with ⟨c, c_in, φ, hφ, lim⟩
  use c, c_in, φ, hφ
  simp_rw [Metric.tendsto_nhds, eventually_atTop, Real.dist_eq] at lim
  intro ε ε_pos
  rcases lim ε ε_pos with ⟨N, hN⟩
  use N
  intro n hn
  exact le_of_lt (hN n hn)

theorem not_seqLimit_of_tendstoInfinity {u : ℕ → ℝ} : TendstoInfinity u → ∀ x, ¬SeqLimit u x := by
  intro lim_infinie x lim_x
  rcases lim_x 1 (by linarith) with ⟨N, hN⟩
  rcases lim_infinie (x + 2) with ⟨N', hN'⟩
  let N₀ := max N N'
  specialize hN N₀ (le_max_left _ _)
  specialize hN' N₀ (le_max_right _ _)
  rw [abs_le] at hN
  linarith

open Real

theorem sup_segment {a b : ℝ} {A : Set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :
    ∃ x ∈ Icc a b, IsSup A x := by
  have b_maj : ∀ y : ℝ, y ∈ A → y ≤ b := fun y y_in => (h y_in).2
  have Sup_maj : UpperBound A (sSup A) := by
    intro x
    apply le_csSup
    use b
    exact b_maj
  refine' ⟨sSup A, _, _⟩
  · constructor
    · rcases hnonvide with ⟨x, x_in⟩
      exact le_trans (h x_in).1 (Sup_maj _ x_in)
    · apply csSup_le hnonvide b_maj
  · exact ⟨Sup_maj, fun y => csSup_le hnonvide⟩

theorem subseq_tendsto_of_tendsto (h : SeqLimit u l) (hφ : Extraction φ) : SeqLimit (u ∘ φ) l := by
  intro ε ε_pos
  rcases h ε ε_pos with ⟨N, hN⟩
  use N
  intro n hn
  apply hN
  calc
    N ≤ n := hn
    _ ≤ φ n := id_le_extraction hφ n


open Lean Elab Tactic

macro  "check_me" : tactic => `(tactic| (
   repeat unfold SeqLimit
   repeat unfold continue_en
   push_neg
   try simp only [exists_prop]
   try exact Iff.rfl
   first | done | fail "That's not quite right. Please try again."))

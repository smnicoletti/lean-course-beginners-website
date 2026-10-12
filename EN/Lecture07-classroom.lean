/-!
# Lecture 7: Induction, Simplification, and Software Verification

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture07.EN.Classroom

-- ============================================================
-- REVIEW OF THE DEFINITIONS FROM LECTURE 6
-- ============================================================

inductive Natural where
  | zero
  | succ (n : Natural)

open Natural

def one : Natural := succ zero
def two : Natural := succ one

def add (m n : Natural) : Natural :=
  match n with
  | zero => m
  | succ n => succ (add m n)

def double (n : Natural) : Natural :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))

theorem lecture07_add_zero_right (m : Natural) : add m zero = m := by
  rfl

theorem lecture07_add_succ_right (m n : Natural) :
    add m (succ n) = succ (add m n) := by
  rfl

theorem lecture07_double_succ (n : Natural) :
    double (succ n) = succ (succ (double n)) := by
  rfl

-- This is the result reached at the end of Lecture 6.
theorem lecture07_zero_add (n : Natural) : add zero n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rewrite [ih]
      rfl

-- ============================================================
-- A SECOND INDUCTION PROOF
-- ============================================================

-- The second argument of `add` is still unknown, so the definition cannot
-- select a branch. We induct on `n`, rather than `m`: in the successor case,
-- `ih` concerns the two recursive additions whose second argument is `n`.
theorem lecture07_succ_add (m n : Natural) :
    add (succ m) n = succ (add m n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Open both additions when their second argument is `succ n`.
      -- The remaining inner goal concerns the smaller natural number `n`.
      unfold add
      -- Replace the addition with first argument `succ m` and second
      -- argument `n` by using the induction hypothesis.
      rewrite [ih]
      rfl

-- ============================================================
-- ASSOCIATIVITY AND COMMUTATIVITY
-- ============================================================

-- Associativity says that grouping `a` with `b`, or `b` with `c`, does not
-- change the result. Since `add` recurses on its second argument, we choose
-- `c`: it controls the outer computations in the statement.
theorem lecture07_add_assoc (a b c : Natural) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      -- Reduce the outer addition on the left.
      rw [lecture07_add_succ_right]
      -- Reduce `add b (succ c)` on the right.
      rw [lecture07_add_succ_right]
      -- Reduce the new outer addition on the right.
      rw [lecture07_add_succ_right]
      -- The remaining equality is the induction hypothesis under `succ`.
      rw [ih]

-- Commutativity says that exchanging the two arguments does not change the
-- sum. The definition treats the arguments asymmetrically. The base case uses
-- `zero_add`, while the successor case also uses `succ_add`.
theorem lecture07_add_comm (a b : Natural) : add a b = add b a := by
  induction b with
  | zero =>
      -- The left side computes directly. On the right, use the theorem that
      -- moves `zero` out of the first argument.
      rw [lecture07_zero_add]
      rfl
  | succ b ih =>
      -- The left side computes because `succ b` is the second argument.
      rw [lecture07_add_succ_right]
      -- On the right, move the successor out of the first argument.
      rw [lecture07_succ_add]
      -- Under `succ`, the remaining equality is the induction hypothesis.
      rw [ih]

-- ============================================================
-- THE SIMPLIFIER
-- ============================================================

-- `simp` applies equations oriented towards simpler forms. We begin with a
-- proof we already understand and compare three levels of automation.

theorem lecture07_zero_add_with_rw (n : Natural) : add zero n = n := by
  rw [lecture07_zero_add]

theorem lecture07_zero_add_with_simp_only (n : Natural) : add zero n = n := by
  -- Use only the named lemma as a rewriting rule.
  simp only [lecture07_zero_add]

theorem lecture07_zero_add_with_simp (n : Natural) : add zero n = n := by
  -- Use the standard simp-set and add this lemma for the current command.
  simp [lecture07_zero_add]

section LocalSimplification

-- Register both lemmas only within this section.
attribute [local simp] lecture07_zero_add lecture07_succ_add

theorem lecture07_succ_add_with_simp (m n : Natural) :
    add (succ m) n = succ (add m n) := by
  -- The lemma need not be named here because it is in the local simp-set.
  simp

end LocalSimplification

-- This equation is a suitable simplification rule: it replaces `double zero`
-- with the simpler form `zero`.
@[simp] theorem lecture07_double_zero : double zero = zero := by
  rfl

-- Associativity and commutativity are not registered as simp rules because
-- they do not orient expressions towards an evidently simpler normal form.

-- ============================================================
-- FINAL ARITHMETIC PROOF
-- ============================================================

-- Exercise: the double of a sum is the sum of the doubles. Since reducing
-- `add m n` depends on `n`, we induct on `n`.
theorem lecture07_double_add (m n : Natural) :
    double (add m n) = add (double m) (double n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [lecture07_add_succ_right]
      rw [lecture07_double_succ]
      rw [lecture07_double_succ]
      rw [lecture07_add_succ_right]
      rw [lecture07_add_succ_right]
      rw [ih]

-- The same proof can be shortened with a controlled collection of rules.
theorem lecture07_double_add_short (m n : Natural) :
    double (add m n) = add (double m) (double n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [lecture07_add_succ_right, lecture07_double_succ, ih]

-- ============================================================
-- FROM INDUCTION TO SOFTWARE VERIFICATION
-- ============================================================

-- A program takes an input and produces an output. Verification states an
-- expected property precisely and proves it for every input. We begin by
-- defining the type of lists inductively.
inductive CustomList (α : Type) where
  | empty
  | cons (head : α) (tail : CustomList α)

end Course.Shared.Lecture07.EN.Classroom

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
-- expected property precisely and proves it for every input. We define the
-- list type ourselves for a small example. The parameter `α` is the type of
-- the elements. The same definition therefore constructs lists of naturals,
-- strings, or other types. This reuse is parametric polymorphism.
inductive CustomList (α : Type) where
  | empty
  | cons (head : α) (tail : CustomList α)

open CustomList

-- A list is empty or is built by placing an element in front of a smaller
-- list. This example contains three natural numbers.
def exampleList : CustomList Natural :=
  cons zero (cons one (cons two empty))

-- Reversing a list requires list concatenation. This definition examines the
-- first list and transfers one element at a time to the result.
-- The braces in `{α : Type}` make `α` implicit: Lean infers it from the types
-- of `xs` and `ys`, so calls can be written as `append xs ys`.
def append {α : Type} (xs ys : CustomList α) : CustomList α :=
  match xs with
  | empty => ys
  | cons x xs => cons x (append xs ys)

-- The recursive algorithm leaves the empty list unchanged. In the `cons`
-- case, it reverses the tail and places the head at the end of the result.
def reverse {α : Type} (xs : CustomList α) : CustomList α :=
  match xs with
  | empty => empty
  | cons x xs => append (reverse xs) (cons x empty)

-- We want to prove the following property for every `xs`:
--
--   reverse (reverse xs) = xs
--
-- This is an important property, but it does not characterize the algorithm
-- by itself. The identity function would satisfy the same equation.
--
-- Before the final theorem, we prove three useful lemmas: appending the empty
-- list, associativity of append, and the behaviour of reverse over append.

-- `append` examines its first argument, so we induct on `xs`.
theorem lecture07_append_empty_right
    {α : Type} (xs : CustomList α) :
    append xs empty = xs := by
  induction xs with
  | empty =>
      rfl
  | cons x xs ih =>
      simp [append, ih]

-- This equation removes an append with the empty list on the right and
-- produces a simpler form. Add it to the local simp-set.
attribute [local simp] lecture07_append_empty_right

-- Regrouping three append operations does not change the resulting list.
-- The first argument again controls computation, so we induct on `xs`.
theorem lecture07_append_assoc
    {α : Type} (xs ys zs : CustomList α) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | empty =>
      rfl
  | cons x xs ih =>
      simp [append, ih]

-- Do not add associativity to the simp-set. It changes grouping but does not
-- identify a generally simpler form. Name it explicitly where needed.

-- Reversing an append operation exchanges the order of its two parts.
theorem lecture07_reverse_append
    {α : Type} (xs ys : CustomList α) :
    reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  induction xs with
  | empty =>
      simp [append, reverse]
  | cons x xs ih =>
      -- The definitions and `ih` leave the same three lists grouped
      -- differently. The remaining goal therefore requires associativity,
      -- which we name here without adding it to the simp-set.
      simp [append, reverse, ih, lecture07_append_assoc]

-- This equation gives the expected form of reversing an append operation.
-- Make it available to `simp` within this section.
attribute [local simp] lecture07_reverse_append

-- Correctness property: reversing twice returns the original list. This proof
-- covers every list because it follows both constructors of `CustomList α`.
theorem lecture07_reverse_reverse
    {α : Type} (xs : CustomList α) :
    reverse (reverse xs) = xs := by
  induction xs with
  | empty =>
      simp [reverse]
  | cons x xs ih =>
      simp [reverse, ih, append]

end Course.Shared.Lecture07.EN.Classroom

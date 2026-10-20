/-!
# Lecture 8: Software Verification, Automation, and LLMs in Lean

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture08.EN.Classroom

-- ============================================================
-- FURTHER FORMS OF AUTOMATION
-- ============================================================

-- The ? variants display a suggested command in the Infoview.
-- They also run the search. If they close the goal, replace the tactic with
-- its suggestion instead of adding the suggestion as another proof step.

-- We want a < c from a < b and b < c.
-- exact? searches the library and tries to supply the required arguments.
example (a b c : Nat) (hAB : a < b) (hBC : b < c) : a < c := by
  exact?

-- apply? searches for an application and tries to prove its premises.
-- It may close the goal or leave new goals. Here it closes everything.
-- We want a conjunction from two assumptions and an implication.
example (P Q R : Prop) (hP : P) (hQ : Q) (hQR : Q → R) : P ∧ R := by
  apply?

-- We want P ∧ (Q ∨ R), knowing that P and Q hold.
-- simp? uses these assumptions to simplify the connectives and suggests
-- sufficient rules.
example (P Q R : Prop) (hP : P) (hQ : Q) : P ∧ (Q ∨ R) := by
  simp? [hP, hQ]

-- We want Q from P ∨ Q, P → R, and ¬R.
-- grind? combines these facts: the P case leads to a contradiction.
-- The suggestion `grind only` uses hPQ, hPR, and hNotR from the goal's context.
-- No additional theorem is needed: grind splits the cases of hPQ and combines
-- the implication hPR with hNotR. `only` does not disable these steps.
-- In `simp only [lemma]`, we supplied a simplification rule instead:
-- without that lemma, simp only does not automatically know the property
-- of the function that we had proved.
example (P Q R : Prop) (hPQ : P ∨ Q) (hPR : P → R) (hNotR : ¬R) : Q := by
  grind?

-- ============================================================
-- LISTS, POLYMORPHISM, AND SOFTWARE VERIFICATION
-- ============================================================

-- Lecture 7 briefly introduced lists as an inductive type. We now return to
-- that definition and study it in greater depth.
-- A test runs a program on selected inputs and can reveal a failure. Formal
-- verification states a property and proves it for every input covered by the
-- statement. The two methods therefore answer different questions.
-- The parameter `α` is the element type. The same definition builds lists
-- of naturals, strings, or other types. This reuse of one structure with
-- different element types is parametric polymorphism.
inductive CustomList (α : Type) where
  | empty
  | cons (head : α) (tail : CustomList α)

open CustomList

-- A list is empty or is built by placing an element in front of a smaller
-- list. This example contains three strings.
def exampleList : CustomList String :=
  cons "Ada" (cons "Hypatia" (cons "Eva" empty))

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

-- In a theorem too, `{α : Type}` is an implicit parameter: the result holds
-- for every element type. When we use the theorem on a list `xs`, Lean infers
-- `α` from the type of `xs`. It is not an assumption we must prove.
-- `append` examines its first argument, so we induct on `xs`.
theorem lecture08_append_empty_right
    {α : Type} (xs : CustomList α) :
    append xs empty = xs := by
  induction xs with
  | empty =>
      rfl
  | cons x xs ih =>
      simp [append, ih]

-- This equation removes an append with the empty list on the right and
-- produces a simpler form. Add it to the local simp-set.
attribute [local simp] lecture08_append_empty_right

-- Regrouping three append operations does not change the resulting list.
-- The first argument again controls computation, so we induct on `xs`.
theorem lecture08_append_assoc
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
theorem lecture08_reverse_append
    {α : Type} (xs ys : CustomList α) :
    reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  induction xs with
  | empty =>
      simp [append, reverse]
  | cons x xs ih =>
      -- The definitions and `ih` leave the same three lists grouped
      -- differently. The remaining goal therefore requires associativity,
      -- which we name here without adding it to the simp-set.
      simp [append, reverse, ih, lecture08_append_assoc]

-- This equation gives the expected form of reversing an append operation.
-- Make it available to `simp` within this section.
attribute [local simp] lecture08_reverse_append

-- Correctness property: reversing twice returns the original list. This proof
-- covers every list because it follows both constructors of `CustomList α`.
theorem lecture08_reverse_reverse
    {α : Type} (xs : CustomList α) :
    reverse (reverse xs) = xs := by
  induction xs with
  | empty =>
      simp [reverse]
  | cons x xs ih =>
      simp [reverse, ih, append]


-- ============================================================
-- FURTHER AUTOMATION: DECIDE AND OMEGA
-- ============================================================

-- We now use Nat and List from the standard library.
-- [2, 4, 6] is Lean syntax for a List Nat, distinct from our CustomList.
-- We want to verify a concrete concatenation and an inequality.
-- decide tries to check the statement by calculation. Here it computes the
-- concatenation, compares the lists, and checks that 7 < 10. Both checks
-- succeed, so Lean closes the goal.
-- Not every statement can be solved this way: variables may block calculation.
example : ([2, 4] ++ [6] : List Nat) = [2, 4, 6] ∧ (7 : Nat) < 10 := by
  decide

-- Eva is at least 18 and Marta is three years older than Eva.
-- We want to prove that Marta is at least 21.
-- omega handles linear arithmetic (equalities and inequalities involving
-- sums and multiplication by constants, not products of two variables).
example (evaAge martaAge : Nat)
    (hDifference : evaAge + 3 = martaAge) (hAge : 18 ≤ evaAge) :
    21 ≤ martaAge := by
  omega

-- omega is not a general solver for products such as x * y when both factors
-- are variables.

-- ============================================================
-- USING AN LLM AS A LEAN ASSISTANT
-- ============================================================

-- Goal: if two reversed lists are equal, the original lists are equal too.
theorem lecture08_reverse_injective {α : Type} (xs ys : CustomList α)
    (h : reverse xs = reverse ys) : xs = ys := by
  -- Rewrite xs as its double reversal.
  rw [← lecture08_reverse_reverse xs]
  -- Use h to replace reverse xs with reverse ys.
  rw [h]
  -- Reversing ys twice returns ys.
  rw [lecture08_reverse_reverse ys]


-- Inspect the proof's dependencies. A sorry would introduce sorryAx.
-- Here propext is the standard axiom that lets us regard logically equivalent
-- propositions (P ↔ Q) as equal (P = Q).
-- This dependency comes from the earlier simp proofs: for example, simp uses
-- eq_self to replace the proposition `t = t` with `True`, relying on propext.
-- The final theorem inherits the dependency through lecture08_reverse_reverse,
-- even though its proof only uses rw.
#print axioms lecture08_reverse_injective

end Course.Shared.Lecture08.EN.Classroom

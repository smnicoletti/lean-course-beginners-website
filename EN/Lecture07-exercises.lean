/-!
# Exercises, Lecture 7: Induction, Simplification, and Software Verification

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture07.EN.Exercises

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

def multiply (m n : Natural) : Natural :=
  match n with
  | zero => zero
  | succ n => add m (multiply m n)

-- Results already obtained in Lecture 6.
theorem add_succ_right (m n : Natural) :
    add m (succ n) = succ (add m n) := by
  rfl

theorem add_one_left (n : Natural) : add one n = succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rw [ih]

-- 1. Prove the analogous result for two by induction.
theorem add_two_left (n : Natural) : add two n = succ (succ n) := by
  sorry

-- 2. Prove this particular form of associativity. Choose the induction
-- variable by looking at the additions that must reduce.
theorem add_with_one_assoc (m n : Natural) :
    add (add m one) n = add m (add one n) := by
  sorry

-- 3. Combine addition and double in an induction proof.
theorem double_add_one (n : Natural) :
    double (add one n) = add two (double n) := by
  sorry

-- 4. Prove by induction that multiplying one by every natural number gives
-- that natural number.
theorem multiply_one_left (n : Natural) : multiply one n = n := by
  sorry

-- 5. Make `add_one_left` available in the simp-set only within this section.
-- Then close the goal with `simp`, without naming the lemma.
section LocalSimplification

example (n : Natural) : add one n = succ n := by
  sorry

end LocalSimplification

-- ============================================================
-- VERIFYING A PROGRAM ON LISTS
-- ============================================================

inductive CustomList (α : Type) where
  | empty
  | cons (head : α) (tail : CustomList α)

open CustomList

-- 6. Define `mapList`: it should apply `f` to every element while preserving
-- the structure of the list.
-- For example, applying `succ` to `cons zero (cons one empty)` should produce
-- `cons one (cons two empty)`.
def mapList {α β : Type} (f : α → β) (xs : CustomList α) : CustomList β :=
  sorry

-- 7. Verify that mapping the identity function does not change a list. Use
-- induction and `simp` with the definition of `mapList`.
theorem mapList_identity {α : Type} (xs : CustomList α) :
    mapList (fun x => x) xs = xs := by
  sorry

-- 8. Verify that two successive map operations are equivalent to one map
-- operation with the composed function. Again use induction and `simp`.
theorem mapList_composition
    {α β γ : Type} (f : α → β) (g : β → γ) (xs : CustomList α) :
    mapList g (mapList f xs) = mapList (fun x => g (f x)) xs := by
  sorry

end Course.Shared.Lecture07.EN.Exercises

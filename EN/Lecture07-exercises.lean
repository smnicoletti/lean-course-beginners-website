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

-- 1. Define multiplication of two natural numbers recursively. The definition
-- should examine its second argument, as `add` does.
def multiply (m n : Natural) : Natural := by
  sorry

-- A result presented in Lecture 6.
theorem add_succ_right (m n : Natural) :
    add m (succ n) = succ (add m n) := by
  rfl

-- We also reuse a result proposed in the Lecture 6 exercises.
theorem add_one_left (n : Natural) : add one n = succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rw [ih]

-- 2. Prove the analogous result for two by induction.
theorem add_two_left (n : Natural) : add two n = succ (succ n) := by
  sorry

-- 3. Prove this particular form of associativity. Choose the induction
-- variable by looking at the additions that must reduce.
theorem add_with_one_assoc (m n : Natural) :
    add (add m one) n = add m (add one n) := by
  sorry

-- 4. Combine addition and double in an induction proof.
theorem double_add_one (n : Natural) :
    double (add one n) = add two (double n) := by
  sorry

-- 5. Prove by induction that multiplying one by every natural number gives
-- that natural number.
theorem multiply_one_left (n : Natural) : multiply one n = n := by
  sorry

-- 6. Make `add_one_left` available in the simp-set only within this section.
-- Then close the goal with `simp`, without naming the lemma.
section LocalSimplification

example (n : Natural) : add one n = succ n := by
  sorry

end LocalSimplification

-- 7. Prove associativity. Choose the induction variable by checking which
-- argument is examined by `add`.
theorem add_assoc (a b c : Natural) :
    add (add a b) c = add a (add b c) := by
  sorry

-- These two results handle `zero` and `succ` in the first argument of `add`.
theorem zero_add (n : Natural) : add zero n = n := by
  sorry

theorem succ_add (m n : Natural) :
    add (succ m) n = succ (add m n) := by
  sorry

-- 8. Prove commutativity by combining the available equations for both
-- arguments of addition.
theorem add_comm (a b : Natural) : add a b = add b a := by
  sorry

theorem double_succ (n : Natural) :
    double (succ n) = succ (succ (double n)) := by
  rfl

-- 9. Concluding exercise: the double of a sum is the sum of the doubles.
theorem double_add (m n : Natural) :
    double (add m n) = add (double m) (double n) := by
  sorry

end Course.Shared.Lecture07.EN.Exercises

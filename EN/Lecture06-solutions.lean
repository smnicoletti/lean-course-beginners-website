/-!
# Solutions, Lecture 6

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.EN.Solutions

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

-- Multiplication repeats `m` as many times as indicated by its second argument.
def multiply (m n : Natural) : Natural :=
  match n with
  | zero => zero
  | succ n => add m (multiply m n)

theorem multiply_zero_right (m : Natural) :
    multiply m zero = zero := by
  rfl

theorem multiply_succ_right (m n : Natural) :
    multiply m (succ n) = add m (multiply m n) := by
  rfl

theorem add_succ_right (m n : Natural) :
    add m (succ n) = succ (add m n) := by
  rfl

theorem rewrite_first_argument
    (a b : Natural)
    (h : a = b) :
    add a zero = b := by
  rw [h]
  rfl

theorem add_one_left (n : Natural) :
    add one n = succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rw [ih]

theorem add_two_left (n : Natural) :
    add two n = succ (succ n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rw [ih]

theorem add_with_one_assoc (m n : Natural) :
    add (add m one) n = add m (add one n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [add_succ_right (add m one) n]
      rw [add_succ_right one n]
      rw [add_succ_right m (add one n)]
      rw [ih]

theorem double_add_one (n : Natural) :
    double (add one n) = add two (double n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [add_succ_right]
      rw [double]
      rw [double]
      rw [add_succ_right]
      rw [add_succ_right]
      rw [ih]

theorem multiply_one_left (n : Natural) :
    multiply one n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold multiply
      rw [ih]
      rw [add_one_left]

example (n : Natural) : add one n = succ n := by
  simp only [add_one_left]

end Course.Shared.Lecture06.EN.Solutions

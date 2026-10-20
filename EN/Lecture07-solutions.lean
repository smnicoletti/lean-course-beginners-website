/-!
# Solutions, Lecture 7: Induction and Simplification

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture07.EN.Solutions

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

theorem add_two_left (n : Natural) : add two n = succ (succ n) := by
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

theorem multiply_one_left (n : Natural) : multiply one n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold multiply
      rw [ih]
      rw [add_one_left]

section LocalSimplification

attribute [local simp] add_one_left

example (n : Natural) : add one n = succ n := by
  simp

end LocalSimplification

theorem add_assoc (a b c : Natural) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      rw [add_succ_right]
      rw [add_succ_right]
      rw [add_succ_right]
      rw [ih]

theorem zero_add (n : Natural) : add zero n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rw [ih]

theorem succ_add (m n : Natural) :
    add (succ m) n = succ (add m n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rw [ih]

theorem add_comm (a b : Natural) : add a b = add b a := by
  induction b with
  | zero =>
      rw [zero_add]
      rfl
  | succ b ih =>
      rw [add_succ_right]
      rw [succ_add]
      rw [ih]

theorem double_succ (n : Natural) :
    double (succ n) = succ (succ (double n)) := by
  rfl

theorem double_add (m n : Natural) :
    double (add m n) = add (double m) (double n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [add_succ_right]
      rw [double_succ]
      rw [double_succ]
      rw [add_succ_right]
      rw [add_succ_right]
      rw [ih]

end Course.Shared.Lecture07.EN.Solutions

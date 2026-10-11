/-!
# Solutions, Lecture 7: Induction, Simplification, and Software Verification

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

-- ============================================================
-- VERIFYING A PROGRAM ON LISTS
-- ============================================================

inductive CustomList (α : Type) where
  | empty
  | cons (head : α) (tail : CustomList α)

open CustomList

def mapList {α β : Type} (f : α → β) (xs : CustomList α) : CustomList β :=
  match xs with
  | empty => empty
  | cons x xs => cons (f x) (mapList f xs)

theorem mapList_identity {α : Type} (xs : CustomList α) :
    mapList (fun x => x) xs = xs := by
  induction xs with
  | empty =>
      rfl
  | cons x xs ih =>
      simp [mapList, ih]

theorem mapList_composition
    {α β γ : Type} (f : α → β) (g : β → γ) (xs : CustomList α) :
    mapList g (mapList f xs) = mapList (fun x => g (f x)) xs := by
  induction xs with
  | empty =>
      rfl
  | cons x xs ih =>
      simp [mapList, ih]

end Course.Shared.Lecture07.EN.Solutions

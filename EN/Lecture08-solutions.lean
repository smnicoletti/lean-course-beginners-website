/-!
# Solutions, Lecture 8: Software Verification, Automation, and LLMs in Lean

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture08.EN.Solutions

-- 1. A direct proof. The suggestion from `exact?` may differ.
example (P Q : Prop) (hPQ : P ∧ Q) : Q := by
  exact hPQ.right

-- 2. In this case, `apply?` finds a complete proof.
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q ∧ P := by
  exact ⟨hPQ hP, hP⟩

-- 3. `simp? [hP]` suggests these simplification rules.
example (P Q : Prop) (hP : P) : (P ∧ Q) ↔ Q := by
  simp only [hP, true_and]

-- 4. `grind?` finds a proof using the local assumptions.
example (P Q R S : Prop) (hPQ : P ∨ Q)
    (hPR : P → R) (hQS : Q → S) : R ∨ S := by
  grind only

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

def append {α : Type} (xs ys : CustomList α) : CustomList α :=
  match xs with
  | empty => ys
  | cons x xs => cons x (append xs ys)

-- 8. Concatenation examines the first list, so we use induction on xs.
theorem mapList_append {α β : Type} (f : α → β) (xs ys : CustomList α) :
    mapList f (append xs ys) = append (mapList f xs) (mapList f ys) := by
  induction xs with
  | empty =>
      rfl
  | cons x xs ih =>
      simp [append, mapList, ih]

-- 9. Computation checks these concrete lists, not all possible lists.
example : ([1, 3] ++ [5, 7] : List Nat) = [1, 3, 5, 7] := by
  decide

-- 10. The two bounds imply the required bound, for any page counts.
example (evaPages martaPages : Nat)
    (hEva : 12 ≤ evaPages) (hMarta : evaPages + 5 ≤ martaPages) :
    17 ≤ martaPages := by
  omega

end Course.Shared.Lecture08.EN.Solutions

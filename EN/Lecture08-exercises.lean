/-!
# Exercises, Lecture 8: Software Verification, Automation, and LLMs in Lean

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture08.EN.Exercises

-- AUTOMATION AND SUGGESTIONS
-- In the next four exercises, try the indicated tactic, read its suggestion,
-- and replace the search with the command proposed by Lean.

-- 1. Obtain Q from the conjunction. Ask `exact?` for a suggestion.
example (P Q : Prop) (hPQ : P ∧ Q) : Q := by
  sorry

-- 2. Ask `apply?` for a suggestion. Does it leave goals open in this case,
-- or does it find a complete proof?
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q ∧ P := by
  sorry

-- 3. Simplify the proposition with `simp?`.
-- Read the rules listed in the suggestion.
example (P Q : Prop) (hP : P) : (P ∧ Q) ↔ Q := by
  sorry

-- 4. We know P or Q holds. P implies R, and Q implies S.
-- Prove R ∨ S with the help of `grind?`.
example (P Q R S : Prop) (hPQ : P ∨ Q)
    (hPR : P → R) (hQS : Q → S) : R ∨ S := by
  sorry

-- ============================================================
-- VERIFYING A PROGRAM ON LISTS
-- ============================================================

inductive CustomList (α : Type) where
  | empty
  | cons (head : α) (tail : CustomList α)

open CustomList

-- 5. Define `mapList`: it should apply `f` to every element while preserving
-- the structure of the list.
-- For example, applying `Nat.succ` to `cons 0 (cons 1 empty)` should produce
-- `cons 1 (cons 2 empty)`.
def mapList {α β : Type} (f : α → β) (xs : CustomList α) : CustomList β :=
  sorry

-- 6. Verify that mapping the identity function does not change a list. Use
-- induction and `simp` with the definition of `mapList`.
theorem mapList_identity {α : Type} (xs : CustomList α) :
    mapList (fun x => x) xs = xs := by
  sorry

-- 7. Verify that two successive map operations are equivalent to one map
-- operation with the composed function. Again use induction and `simp`.
theorem mapList_composition
    {α β γ : Type} (f : α → β) (g : β → γ) (xs : CustomList α) :
    mapList g (mapList f xs) = mapList (fun x => g (f x)) xs := by
  sorry

-- We reuse the concatenation function defined in Classroom.
def append {α : Type} (xs ys : CustomList α) : CustomList α :=
  match xs with
  | empty => ys
  | cons x xs => cons x (append xs ys)

-- 8. Applying `f` after concatenating two lists gives the same result as
-- applying it separately to each list and then concatenating the results.
-- Choose which list to use for induction.
theorem mapList_append {α β : Type} (f : α → β) (xs ys : CustomList α) :
    mapList f (append xs ys) = append (mapList f xs) (mapList f ys) := by
  sorry

-- COMPUTATION AND ARITHMETIC

-- 9. Here we use the standard library's lists and natural numbers.
-- Verify this equality between concrete lists with `decide`.
-- How does this differ from the general property in exercise 8?
example : ([1, 3] ++ [5, 7] : List Nat) = [1, 3, 5, 7] := by
  sorry

-- 10. Eva has read at least 12 pages. Marta has read at least 5 more than Eva.
-- Which tactic or automation could help us here?
example (evaPages martaPages : Nat)
    (hEva : 12 ≤ evaPages) (hMarta : evaPages + 5 ≤ martaPages) :
    17 ≤ martaPages := by
  sorry

end Course.Shared.Lecture08.EN.Exercises

/-!
# Exercises, Lecture 2

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Open this file in VSCode and observe the Infoview after each line. Each
`sorry` marks an intentional hole to replace with a proof.
-/

namespace Course.Shared.Lecture02.EN.Exercises

section Implication

-- Natural language: if we already have a proof of `Q`, then from `P` we can
-- conclude `Q`.
example (P Q : Prop) (hQ : Q) : P → Q := by
  sorry

-- Natural language: if `Q` follows from `P`, and we have `P`, then we have `Q`.
example (P Q : Prop) : (P → Q) → P → Q := by
  sorry

end Implication

section Conjunction

-- Natural language: if we have `P` and we have `Q`, then we have `P ∧ Q`.
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  sorry

-- Natural language: from `P ∧ Q` we can extract `P`.
example (P Q : Prop) : P ∧ Q → P := by
  sorry

-- Natural language: from `P ∧ Q` we can extract `Q`.
example (P Q : Prop) : P ∧ Q → Q := by
  sorry

-- Natural language: if we have `P ∧ Q`, then we can swap the order and obtain
-- `Q ∧ P`.
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

end Conjunction

section Disjunction

-- Natural language: if we have `P`, then we have `P ∨ Q`.
example (P Q : Prop) : P → P ∨ Q := by
  sorry

-- Natural language: if we have `Q`, then we have `P ∨ Q`.
example (P Q : Prop) : Q → P ∨ Q := by
  sorry

-- Natural language: if we have `P ∨ Q`, then we can obtain `Q ∨ P` by
-- reasoning by cases.
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  sorry

-- Natural language: if I take the bus or I take the train, and in each of the
-- two cases I arrive on time, then I arrive on time.
example (TakeBus TakeTrain ArriveOnTime : Prop) :
    ((TakeBus → ArriveOnTime) ∧
      (TakeTrain → ArriveOnTime)) ∧
    (TakeBus ∨ TakeTrain) →
    ArriveOnTime := by
  sorry

end Disjunction

section FalseAndNegation

-- Natural language: from a contradiction we can conclude any `P`.
example (P : Prop) : False → P := by
  sorry

-- Natural language: `P` and `¬P` produce a contradiction.
example (P : Prop) : P → ¬P → False := by
  sorry

-- Natural language: if `Q` follows from `P`, and `Q` is false, then `P` is
-- false.
example (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  sorry

end FalseAndNegation

end Course.Shared.Lecture02.EN.Exercises

/-!
# Solutions, Lecture 2

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture02.EN.Solutions

section Implication

-- Natural language: if we already have a proof of `Q`, then from `P` we can
-- conclude `Q`.
example (P Q : Prop) (hQ : Q) : P → Q := by
  intro hP
  exact hQ

-- Natural language: if `Q` follows from `P`, and we have `P`, then we have `Q`.
example (P Q : Prop) : (P → Q) → P → Q := by
  intro hPQ
  intro hP
  have hQ := hPQ hP
  exact hQ

end Implication

section Conjunction

-- Natural language: if we have `P` and we have `Q`, then we have `P ∧ Q`.
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  exact And.intro hP hQ

-- Natural language: from `P ∧ Q` we can extract `P`.
example (P Q : Prop) : P ∧ Q → P := by
  intro hPQ
  exact hPQ.left

-- Natural language: from `P ∧ Q` we can extract `Q`.
example (P Q : Prop) : P ∧ Q → Q := by
  intro hPQ
  exact hPQ.right

-- Natural language: if we have `P ∧ Q`, then we can swap the order and obtain
-- `Q ∧ P`.
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro hPQ
  exact And.intro hPQ.right hPQ.left

end Conjunction

section Disjunction

-- Natural language: if we have `P`, then we have `P ∨ Q`.
example (P Q : Prop) : P → P ∨ Q := by
  intro hP
  exact Or.inl hP

-- Natural language: if we have `Q`, then we have `P ∨ Q`.
example (P Q : Prop) : Q → P ∨ Q := by
  intro hQ
  exact Or.inr hQ

-- Natural language: if we have `P ∨ Q`, then we can obtain `Q ∨ P` by
-- reasoning by cases.
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro hPOrQ
  cases hPOrQ with
  | inl hP =>
      exact Or.inr hP
  | inr hQ =>
      exact Or.inl hQ

-- Natural language: if I take the bus or I take the train, and in each of the
-- two cases I arrive on time, then I arrive on time.
example (TakeBus TakeTrain ArriveOnTime : Prop) :
    ((TakeBus → ArriveOnTime) ∧
      (TakeTrain → ArriveOnTime)) ∧
    (TakeBus ∨ TakeTrain) →
    ArriveOnTime := by
  intro hArgument
  have hRules := hArgument.left
  have hBusOrTrain := hArgument.right
  have hBusTime := hRules.left
  have hTrainTime := hRules.right
  cases hBusOrTrain with
  | inl hBus =>
      exact hBusTime hBus
  | inr hTrain =>
      exact hTrainTime hTrain

end Disjunction

section FalseAndNegation

-- Natural language: from a contradiction we can conclude any `P`.
example (P : Prop) : False → P := by
  intro hFalse
  exact False.elim hFalse

-- Natural language: `P` and `¬P` produce a contradiction.
example (P : Prop) : P → ¬P → False := by
  intro hP
  intro hNotP
  exact hNotP hP

-- Natural language: if `Q` follows from `P`, and `Q` is false, then `P` is
-- false.
example (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hNotQ
  intro hP
  have hQ := hPQ hP
  exact hNotQ hQ

end FalseAndNegation

end Course.Shared.Lecture02.EN.Solutions

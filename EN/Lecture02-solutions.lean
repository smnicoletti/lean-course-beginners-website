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

-- Natural language: if I drink coffee then I stay awake; but I do not stay
-- awake; therefore I did not drink coffee.
example (DrinkCoffee Awake : Prop) :
    ((DrinkCoffee → Awake) ∧ ¬Awake) → ¬DrinkCoffee := by
  intro hArgument
  have hRule := hArgument.left
  have hNotAwake := hArgument.right
  intro hDrinkCoffee
  have hAwake := hRule hDrinkCoffee
  exact hNotAwake hAwake

end FalseAndNegation

section Biconditional

-- Natural language: if we have both directions, then we have a biconditional.
example (P Q : Prop) : (P → Q) → (Q → P) → (P ↔ Q) := by
  intro hPQ
  intro hQP
  exact Iff.intro hPQ hQP

-- Natural language: from `P ↔ Q` and `P` we can obtain `Q`.
example (P Q : Prop) : (P ↔ Q) → P → Q := by
  intro hIff
  intro hP
  exact Iff.mp hIff hP

-- Natural language: from `P ↔ Q` and `Q` we can obtain `P`.
example (P Q : Prop) : (P ↔ Q) → Q → P := by
  intro hIff
  intro hQ
  exact Iff.mpr hIff hQ

end Biconditional

section Classical

-- The constructive direction of contraposition.
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hPQ
  intro hNotQ
  intro hP
  have hQ := hPQ hP
  exact hNotQ hQ

-- The reverse direction of contraposition requires classical reasoning.
example (P Q : Prop) : (¬Q → ¬P) → P → Q := by
  intro hContrap
  intro hP
  cases Classical.em Q with
  | inl hQ =>
      exact hQ
  | inr hNotQ =>
      have hNotP := hContrap hNotQ
      exfalso
      exact hNotP hP

-- Classical proof by contradiction.
example (P : Prop) : (¬P → False) → P := by
  intro hContradiction
  exact Classical.byContradiction hContradiction

end Classical

section Argumentation

-- Natural language: if the form is complete, and if a complete form makes the
-- application admissible, and if an admissible application can be evaluated,
-- then the application can be evaluated.
example (CompleteForm AdmissibleApplication EvaluableApplication : Prop) :
    (CompleteForm ∧ (CompleteForm → AdmissibleApplication)) ∧
      (AdmissibleApplication → EvaluableApplication) →
    EvaluableApplication := by
  intro hArgument
  have hFirstStep := hArgument.left
  have hCompleteForm := hFirstStep.left
  have hFormApplication := hFirstStep.right
  have hApplicationEvaluable := hArgument.right
  have hAdmissibleApplication := hFormApplication hCompleteForm
  have hEvaluable := hApplicationEvaluable hAdmissibleApplication
  exact hEvaluable

-- Natural language: if the measurement is precise or the review is approved,
-- and each of the two cases makes the result reliable, and if a reliable
-- result justifies the decision, then the decision is justified.
example (PreciseMeasurement ApprovedReview ReliableResult
    JustifiedDecision : Prop) :
    ((PreciseMeasurement ∨ ApprovedReview) ∧
      ((PreciseMeasurement → ReliableResult) ∧
        (ApprovedReview → ReliableResult))) ∧
    (ReliableResult → JustifiedDecision) →
    JustifiedDecision := by
  intro hArgument
  have hFirstStep := hArgument.left
  have hMeasurementOrReview := hFirstStep.left
  have hReliabilityRules := hFirstStep.right
  have hMeasurementReliable := hReliabilityRules.left
  have hReviewReliable := hReliabilityRules.right
  have hReliableDecision := hArgument.right
  have hResult :=
    Or.elim hMeasurementOrReview hMeasurementReliable hReviewReliable
  have hDecision := hReliableDecision hResult
  exact hDecision

end Argumentation

end Course.Shared.Lecture02.EN.Solutions

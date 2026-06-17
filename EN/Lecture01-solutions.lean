/-!
# Solutions, Lecture 1

Author: Stefano M. Nicoletti
Website: https://stefanonicoletti.com/
-/

namespace Course.Shared.Lecture01.EN.Solutions

section Base

-- Natural language: if we already have a proof that there is sun, we can
-- conclude that there is sun.
example (Sun : Prop) (hSun : Sun) : Sun := by
  exact hSun

-- Natural language: if there is sun, then there is sun.
example (Sun : Prop) : Sun → Sun := by
  intro h
  exact h

-- Natural language: if there is sun then it is warm; there is sun; therefore
-- it is warm.
example (Sun Warm : Prop) :
    ((Sun → Warm) ∧ Sun) → Warm := by
  intro hArgument
  have hSunWarm := hArgument.left
  have hSun := hArgument.right
  have hWarm := hSunWarm hSun
  exact hWarm

-- Natural language: the same argument, but using `.left` and `.right` directly.
example (Sun Warm : Prop) :
    ((Sun → Warm) ∧ Sun) → Warm := by
  intro h
  exact h.left h.right

-- Natural language: we declare separately that studying is enough to pass the
-- exam, and that I study; therefore I pass the exam.
example (Study PassExam : Prop)
    (hStudyExam : Study → PassExam) (hStudy : Study) :
    PassExam := by
  exact hStudyExam hStudy

end Base

section Schemas

-- Natural language: if `P` is true, and `Q` follows from `P`, then `Q` is true.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hP : P) (hPQ : P → Q) :
    Q := by
  exact hPQ hP

-- Natural language: we use the previous schema in a concrete example.
example (Study PassExam : Prop)
    (hStudyExam : Study → PassExam) (hStudy : Study) :
    PassExam := by
  exact exercise_modus_ponens hStudy hStudyExam

-- Natural language: if we have a premise, if an intermediate step follows
-- from the premise, and if the conclusion follows from the intermediate step,
-- then we obtain the conclusion.
theorem exercise_argument_chain
    (Premise IntermediateStep Conclusion : Prop) :
    (Premise ∧ (Premise → IntermediateStep)) ∧
      (IntermediateStep → Conclusion) →
    Conclusion := by
  intro hArgument
  have hFirstStep := hArgument.left
  have hPremise := hFirstStep.left
  have hPremiseToStep := hFirstStep.right
  have hStepToConclusion := hArgument.right
  have hStep := hPremiseToStep hPremise
  have hConclusion := hStepToConclusion hStep
  exact hConclusion

end Schemas

section Examples

-- Natural language: if I drink coffee then I stay awake; but I do not stay
-- awake; therefore I did not drink coffee.
theorem exercise_coffee_example
    (DrinkCoffee Awake : Prop) :
    ((DrinkCoffee → Awake) ∧ ¬Awake) → ¬DrinkCoffee := by
  intro hArgument
  have hRule := hArgument.left
  have hNotAwake := hArgument.right
  intro hDrinkCoffee
  have hAwake := hRule hDrinkCoffee
  exact hNotAwake hAwake

-- Natural language: if I take the bus or I take the train, and in each of the
-- two cases I arrive on time, then I arrive on time.
-- Hint: use `cases` for reasoning by cases.
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

-- Natural language: the same reasoning by cases, expressed with `Or.elim`.
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
  apply Or.elim hBusOrTrain
  · intro hBus
    exact hBusTime hBus
  · intro hTrain
    exact hTrainTime hTrain

-- Natural language: if an experiment is reproducible or the archive is
-- reliable, and each of the two cases makes the hypothesis credible, and if a
-- credible hypothesis makes the result acceptable, then the result is
-- acceptable.
theorem exercise_research_example
    (ReproducibleExperiment ReliableArchive CredibleHypothesis
      AcceptableResult : Prop) :
    ((ReproducibleExperiment ∨ ReliableArchive) ∧
      ((ReproducibleExperiment → CredibleHypothesis) ∧
        (ReliableArchive → CredibleHypothesis))) ∧
    (CredibleHypothesis → AcceptableResult) →
    AcceptableResult := by
  intro hArgument
  have hFirstStep := hArgument.left
  have hExperimentOrArchive := hFirstStep.left
  have hCredibilityRules := hFirstStep.right
  have hExperimentCredible := hCredibilityRules.left
  have hArchiveCredible := hCredibilityRules.right
  have hCredibleAcceptable := hArgument.right
  have hHypothesis :=
    Or.elim hExperimentOrArchive hExperimentCredible hArchiveCredible
  have hResult := hCredibleAcceptable hHypothesis
  exact hResult

end Examples

end Course.Shared.Lecture01.EN.Solutions

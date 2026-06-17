/-!
# Exercises, Lecture 1

Author: Stefano M. Nicoletti
Website: https://stefanonicoletti.com/

Open this file in VS Code and inspect the Infoview after each line. Each
`sorry` marks an intentional hole to replace with a proof.
-/

namespace Course.Shared.Lecture01.EN.Exercises

section Base

-- Natural language: if we already have a proof that there is sun, we can
-- conclude that there is sun.
example (Sun : Prop) (hSun : Sun) : Sun := by
  sorry

-- Natural language: if there is sun, then there is sun.
example (Sun : Prop) : Sun → Sun := by
  sorry

-- Natural language: if there is sun then it is warm; there is sun; therefore
-- it is warm.
example (Sun Warm : Prop) :
    ((Sun → Warm) ∧ Sun) → Warm := by
  sorry

-- Natural language: the same argument, but using `.left` and `.right` directly.
example (Sun Warm : Prop) :
    ((Sun → Warm) ∧ Sun) → Warm := by
  intro h
  sorry

-- Natural language: we declare separately that studying is enough to pass the
-- exam, and that I study; therefore I pass the exam.
example (Study PassExam : Prop)
    (hStudyExam : Study → PassExam) (hStudy : Study) :
    PassExam := by
  sorry

end Base

section Schemas

-- Natural language: if `P` is true, and `Q` follows from `P`, then `Q` is true.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hP : P) (hPQ : P → Q) :
    Q := by
  sorry

-- Natural language: we use the previous schema in a concrete example.
example (Study PassExam : Prop)
    (hStudyExam : Study → PassExam) (hStudy : Study) :
    PassExam := by
  sorry

-- Natural language: if we have a premise, if an intermediate step follows
-- from the premise, and if the conclusion follows from the intermediate step,
-- then we obtain the conclusion.
theorem exercise_argument_chain
    (Premise IntermediateStep Conclusion : Prop) :
    (Premise ∧ (Premise → IntermediateStep)) ∧
      (IntermediateStep → Conclusion) →
    Conclusion := by
  intro hArgument
  sorry

end Schemas

section Examples

-- Natural language: if I drink coffee then I stay awake; but I do not stay
-- awake; therefore I did not drink coffee.
theorem exercise_coffee_example
    (DrinkCoffee Awake : Prop) :
    ((DrinkCoffee → Awake) ∧ ¬Awake) → ¬DrinkCoffee := by
  sorry

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
  sorry

-- Natural language: the same reasoning by cases, expressed with `Or.elim`.
example (TakeBus TakeTrain ArriveOnTime : Prop) :
    ((TakeBus → ArriveOnTime) ∧
      (TakeTrain → ArriveOnTime)) ∧
    (TakeBus ∨ TakeTrain) →
    ArriveOnTime := by
  sorry

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
  sorry

end Examples

end Course.Shared.Lecture01.EN.Exercises

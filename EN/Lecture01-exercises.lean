/-!
# Exercises, Lecture 1

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Open this file in VS Code and inspect the Infoview after each line. Each
`sorry` marks an intentional hole to replace with a proof.
-/

namespace Course.Shared.Lecture01.EN.Exercises

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

-- Natural language: if `P` is true, and `Q` follows from `P`, then `Q` is true.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hPQ : P → Q) (hP : P) :
    Q := by
  sorry

-- We use the previous schema in a concrete example.
example (Study PassExam : Prop)
    (hStudy : Study) (hStudyExam : Study → PassExam) :
    PassExam := by
  sorry

end Course.Shared.Lecture01.EN.Exercises

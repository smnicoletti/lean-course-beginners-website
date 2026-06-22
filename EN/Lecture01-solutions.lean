/-!
# Solutions, Lecture 1

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture01.EN.Solutions

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

-- Natural language: if `P` is true, and `Q` follows from `P`, then `Q` is true.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hPQ : P → Q) (hP : P) :
    Q := by
  exact hPQ hP

-- We use the previous schema in a concrete example.
example (Study PassExam : Prop)
    (hStudy : Study) (hStudyExam : Study → PassExam) :
    PassExam := by
  exact exercise_modus_ponens hStudyExam hStudy

end Course.Shared.Lecture01.EN.Solutions

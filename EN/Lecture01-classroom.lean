/-!
# Lecture 1: What Is a Theorem Prover?

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Date: June 22, 2026.
Duration: 2 hours.

-/

namespace Course.Shared.Lecture01.EN.Classroom

-- Types, #eval, #check

#check Prop
#check Nat
#check Float

#eval 3 + 1
#eval 3.5 + 2

-- Natural language: if we assume that it rains, then we can conclude that it rains.
example (Rains : Prop) (hRains : Rains) : Rains := by
  exact hRains

-- Natural language: if it rains, then we can conclude that it rains.
example (Rains : Prop) : Rains → Rains := by
  intro h
  exact h

-- Natural language: if it rains then I take the umbrella, and it rains, then this implies that I take the umbrella.
example (Rains TakeUmbrella : Prop) : ((Rains → TakeUmbrella) ∧ Rains) → TakeUmbrella := by
  intro assumption
  have hRainsUmbrella := assumption.left
  have hRains := assumption.right
  have hTakeUmbrella := hRainsUmbrella hRains
  exact hTakeUmbrella

-- We encode, verify, and use the valid reasoning schema. Braces mark implicit arguments: Lean can often infer them from the type of the hypotheses.
-- Natural language: if P is true and Q follows from P, then Q is true.
theorem lecture01_modus_ponens
    {P Q : Prop}
    (hPQ : P → Q) (hP : P) :
    Q := by
  exact hPQ hP

example (Rains TakeUmbrella : Prop)
    (hRains : Rains)
    (hRainsUmbrella : Rains → TakeUmbrella) :
    TakeUmbrella := by
  exact lecture01_modus_ponens hRainsUmbrella hRains

end Course.Shared.Lecture01.EN.Classroom

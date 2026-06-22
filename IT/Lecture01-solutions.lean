/-!
# Soluzioni, Lezione 1

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture01.IT.Solutions

-- Linguaggio naturale: se abbiamo già una dimostrazione che c'è sole, possiamo
-- concludere che c'è sole.
example (Sole : Prop) (hSole : Sole) : Sole := by
  exact hSole

-- Linguaggio naturale: se c'è sole, allora c'è sole.
example (Sole : Prop) : Sole → Sole := by
  intro h
  exact h

-- Linguaggio naturale: se c'è sole allora fa caldo; c'è sole; dunque fa caldo.
example (Sole FaCaldo : Prop) :
    ((Sole → FaCaldo) ∧ Sole) → FaCaldo := by
  intro hArgomento
  have hSoleCaldo := hArgomento.left
  have hSole := hArgomento.right
  have hCaldo := hSoleCaldo hSole
  exact hCaldo

-- Linguaggio naturale: se `P` è vero, e da `P` segue `Q`, allora `Q` è vero.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hPQ : P → Q) (hP : P) :
    Q := by
  exact hPQ hP

-- Usiamo lo schema precedente in un esempio concreto.
example (Studio SuperoEsame : Prop)
    (hStudio : Studio) (hStudioEsame : Studio → SuperoEsame) :
    SuperoEsame := by
  exact exercise_modus_ponens hStudioEsame hStudio

end Course.Shared.Lecture01.IT.Solutions

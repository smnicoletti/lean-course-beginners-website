/-!
# Esercizi, Lezione 1

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Aprire questo file in VSCode e osservare l'Infoview dopo ogni riga. Ogni
`sorry` indica un buco intenzionale da sostituire con una dimostrazione.
-/

namespace Course.Shared.Lecture01.IT.Exercises

-- Linguaggio naturale: se abbiamo già una dimostrazione che c'è sole, possiamo
-- concludere che c'è sole.
example (Sole : Prop) (hSole : Sole) : Sole := by
  sorry

-- Linguaggio naturale: se c'è sole, allora c'è sole.
example (Sole : Prop) : Sole → Sole := by
  sorry

-- Linguaggio naturale: se c'è sole allora fa caldo; c'è sole; dunque fa caldo.
example (Sole FaCaldo : Prop) :
    ((Sole → FaCaldo) ∧ Sole) → FaCaldo := by
  sorry

-- Linguaggio naturale: se `P` è vero, e da `P` segue `Q`, allora `Q` è vero.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hPQ : P → Q) (hP : P) :
    Q := by
  sorry

-- Usiamo lo schema precedente in un esempio concreto.
example (Studio SuperoEsame : Prop)
    (hStudio : Studio) (hStudioEsame : Studio → SuperoEsame) :
    SuperoEsame := by
  sorry

end Course.Shared.Lecture01.IT.Exercises

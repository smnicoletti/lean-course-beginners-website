/-!
# Lezione 1: Che cos'e un dimostratore di teoremi?

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Data: 22 giugno 2026.
Durata: 2 ore.

-/

namespace Course.Shared.Lecture01.IT.Classroom

-- Tipi, #eval, #check

#check Prop
#check Nat
#check Float

#eval 3 + 1
#eval 3.5 + 2

-- Linguaggio naturale: se assumiamo che piove, allora possiamo concludere che piove.
example (Piove : Prop) (hPiove : Piove) : Piove := by
  exact hPiove

-- Linguaggio naturale: se piove, allora possiamo concludere che piove.
example (Piove : Prop) : Piove → Piove := by
  intro h
  exact h

-- Linguaggio naturale: se piove allora prendo l'ombrello, e piove, allora questo implica che prendo l'ombrello.
example (Piove PrendoOmbrello : Prop) : ((Piove → PrendoOmbrello) ∧ Piove) → PrendoOmbrello := by
  intro assunzione
  have hPioveOmbrello := assunzione.left
  have hPiove := assunzione.right
  have hPrendoOmbrello := hPioveOmbrello hPiove
  exact hPrendoOmbrello

-- Codifichiamo, verifichiamo e usiamo lo schema di ragionamento valido. Le graffe indicano argomenti impliciti: spesso Lean riesce a inferirli dal tipo delle assunzioni.
-- Linguaggio naturale: se P è vero e da P segue Q, allora Q è vero.
theorem lecture01_modus_ponens
    {P Q : Prop}
    (hPQ : P → Q) (hP : P) :
    Q := by
  exact hPQ hP

example (Piove PrendoOmbrello : Prop)
    (hPiove : Piove)
    (hPioveOmbrello : Piove → PrendoOmbrello) :
    PrendoOmbrello := by
  exact lecture01_modus_ponens hPioveOmbrello hPiove

end Course.Shared.Lecture01.IT.Classroom

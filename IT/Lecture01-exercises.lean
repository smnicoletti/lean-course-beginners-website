/-!
# Esercizi, Lezione 1

Autore: Stefano M. Nicoletti
Sito web: https://stefanonicoletti.com/

Aprire questo file in VSCode e osservare l'Infoview dopo ogni riga. Ogni
`sorry` indica un buco intenzionale da sostituire con una prova.
-/

namespace Course.Shared.Lecture01.IT.Exercises

section Base

-- Linguaggio naturale: se abbiamo già una prova che c'è sole, possiamo
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

-- Linguaggio naturale: lo stesso argomento, ma usando direttamente `.left` e `.right`.
example (Sole FaCaldo : Prop) :
    ((Sole → FaCaldo) ∧ Sole) → FaCaldo := by
  intro h
  sorry

-- Linguaggio naturale: dichiariamo separatamente che studiare basta per
-- superare l'esame, e che studio; dunque supero l'esame.
example (Studio SuperoEsame : Prop)
    (hStudioEsame : Studio → SuperoEsame) (hStudio : Studio) :
    SuperoEsame := by
  sorry

end Base

section Schemi

-- Linguaggio naturale: se `P` è vero, e da `P` segue `Q`, allora `Q` è vero.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hP : P) (hPQ : P → Q) :
    Q := by
  sorry

-- Linguaggio naturale: usiamo lo schema precedente in un esempio concreto.
example (Studio SuperoEsame : Prop)
    (hStudioEsame : Studio → SuperoEsame) (hStudio : Studio) :
    SuperoEsame := by
  sorry

-- Linguaggio naturale: se abbiamo una premessa, se dalla premessa segue un
-- passo intermedio, e se dal passo intermedio segue la conclusione, allora
-- otteniamo la conclusione.
theorem exercise_argument_chain
    (Premessa PassoIntermedio Conclusione : Prop) :
    (Premessa ∧ (Premessa → PassoIntermedio)) ∧
      (PassoIntermedio → Conclusione) →
    Conclusione := by
  intro hArgomento
  sorry

end Schemi

section Esempi

-- Linguaggio naturale: se bevo caffè allora resto sveglio; ma non resto
-- sveglio; dunque non ho bevuto caffè.
theorem exercise_coffee_example
    (BevoCaffe Sveglio : Prop) :
    ((BevoCaffe → Sveglio) ∧ ¬Sveglio) → ¬BevoCaffe := by
  sorry

-- Linguaggio naturale: se prendo il bus oppure prendo il treno, e in ciascuno
-- dei due casi arrivo in tempo, allora arrivo in tempo.
-- Hint: usa `cases` per il ragionamento per casi.
example (PrendoBus PrendoTreno ArrivoInTempo : Prop) :
    ((PrendoBus → ArrivoInTempo) ∧
      (PrendoTreno → ArrivoInTempo)) ∧
    (PrendoBus ∨ PrendoTreno) →
    ArrivoInTempo := by
  intro hArgomento
  have hRegole := hArgomento.left
  have hBusOTreno := hArgomento.right
  sorry

-- Linguaggio naturale: lo stesso ragionamento per casi, espresso con `Or.elim`.
example (PrendoBus PrendoTreno ArrivoInTempo : Prop) :
    ((PrendoBus → ArrivoInTempo) ∧
      (PrendoTreno → ArrivoInTempo)) ∧
    (PrendoBus ∨ PrendoTreno) →
    ArrivoInTempo := by
  sorry

-- Linguaggio naturale: se un esperimento è riproducibile oppure l'archivio è
-- affidabile, e ciascuno dei due casi rende credibile l'ipotesi, e se
-- un'ipotesi credibile rende accettabile il risultato, allora il risultato è
-- accettabile.
theorem exercise_research_example
    (EsperimentoRiproducibile ArchivioAffidabile IpotesiCredibile
      RisultatoAccettabile : Prop) :
    ((EsperimentoRiproducibile ∨ ArchivioAffidabile) ∧
      ((EsperimentoRiproducibile → IpotesiCredibile) ∧
        (ArchivioAffidabile → IpotesiCredibile))) ∧
    (IpotesiCredibile → RisultatoAccettabile) →
    RisultatoAccettabile := by
  sorry

end Esempi

end Course.Shared.Lecture01.IT.Exercises

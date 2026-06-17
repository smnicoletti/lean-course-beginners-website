/-!
# Soluzioni, Lezione 1

Autore: Stefano M. Nicoletti
Sito web: https://stefanonicoletti.com/
-/

namespace Course.Shared.Lecture01.IT.Solutions

section Base

-- Linguaggio naturale: se abbiamo già una prova che c'è sole, possiamo
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

-- Linguaggio naturale: lo stesso argomento, ma usando direttamente `.left` e `.right`.
example (Sole FaCaldo : Prop) :
    ((Sole → FaCaldo) ∧ Sole) → FaCaldo := by
  intro h
  exact h.left h.right

-- Linguaggio naturale: dichiariamo separatamente che studiare basta per
-- superare l'esame, e che studio; dunque supero l'esame.
example (Studio SuperoEsame : Prop)
    (hStudioEsame : Studio → SuperoEsame) (hStudio : Studio) :
    SuperoEsame := by
  exact hStudioEsame hStudio

end Base

section Schemi

-- Linguaggio naturale: se `P` è vero, e da `P` segue `Q`, allora `Q` è vero.
theorem exercise_modus_ponens
    {P Q : Prop}
    (hP : P) (hPQ : P → Q) :
    Q := by
  exact hPQ hP

-- Linguaggio naturale: usiamo lo schema precedente in un esempio concreto.
example (Studio SuperoEsame : Prop)
    (hStudioEsame : Studio → SuperoEsame) (hStudio : Studio) :
    SuperoEsame := by
  exact exercise_modus_ponens hStudio hStudioEsame

-- Linguaggio naturale: se abbiamo una premessa, se dalla premessa segue un
-- passo intermedio, e se dal passo intermedio segue la conclusione, allora
-- otteniamo la conclusione.
theorem exercise_argument_chain
    (Premessa PassoIntermedio Conclusione : Prop) :
    (Premessa ∧ (Premessa → PassoIntermedio)) ∧
      (PassoIntermedio → Conclusione) →
    Conclusione := by
  intro hArgomento
  have hPrimoPasso := hArgomento.left
  have hPremessa := hPrimoPasso.left
  have hDaPremessaAPasso := hPrimoPasso.right
  have hDaPassoAConclusione := hArgomento.right
  have hPasso := hDaPremessaAPasso hPremessa
  have hConclusione := hDaPassoAConclusione hPasso
  exact hConclusione

end Schemi

section Esempi

-- Linguaggio naturale: se bevo caffè allora resto sveglio; ma non resto
-- sveglio; dunque non ho bevuto caffè.
theorem exercise_coffee_example
    (BevoCaffe Sveglio : Prop) :
    ((BevoCaffe → Sveglio) ∧ ¬Sveglio) → ¬BevoCaffe := by
  intro hArgomento
  have hRegola := hArgomento.left
  have hNonSveglio := hArgomento.right
  intro hBevoCaffe
  have hSveglio := hRegola hBevoCaffe
  exact hNonSveglio hSveglio

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
  have hBusTempo := hRegole.left
  have hTrenoTempo := hRegole.right
  cases hBusOTreno with
  | inl hBus =>
      exact hBusTempo hBus
  | inr hTreno =>
      exact hTrenoTempo hTreno

-- Linguaggio naturale: lo stesso ragionamento per casi, espresso con `Or.elim`.
example (PrendoBus PrendoTreno ArrivoInTempo : Prop) :
    ((PrendoBus → ArrivoInTempo) ∧
      (PrendoTreno → ArrivoInTempo)) ∧
    (PrendoBus ∨ PrendoTreno) →
    ArrivoInTempo := by
  intro hArgomento
  have hRegole := hArgomento.left
  have hBusOTreno := hArgomento.right
  have hBusTempo := hRegole.left
  have hTrenoTempo := hRegole.right
  apply Or.elim hBusOTreno
  · intro hBus
    exact hBusTempo hBus
  · intro hTreno
    exact hTrenoTempo hTreno

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
  intro hArgomento
  have hPrimoPasso := hArgomento.left
  have hEsperimentoOArchivio := hPrimoPasso.left
  have hRegoleCredibilita := hPrimoPasso.right
  have hEsperimentoCredibile := hRegoleCredibilita.left
  have hArchivioCredibile := hRegoleCredibilita.right
  have hCredibileAccettabile := hArgomento.right
  have hIpotesi :=
    Or.elim hEsperimentoOArchivio hEsperimentoCredibile hArchivioCredibile
  have hRisultato := hCredibileAccettabile hIpotesi
  exact hRisultato

end Esempi

end Course.Shared.Lecture01.IT.Solutions

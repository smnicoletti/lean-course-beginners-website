/-!
# Esercizi, Lezione 3

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Aprire questo file in VSCode e osservare come cambia il goal dopo ogni tattica.
Ogni `sorry` indica una dimostrazione da completare usando le regole di
deduzione naturale viste durante la lezione.
-/

namespace Course.Shared.Lecture03.IT.Exercises

section ImplicazioneECongiunzione

-- Vogliamo dimostrare che, se bevo vino e mangio la pasta, allora bevo vino.
-- Introduciamo l'assunzione e prendiamo la sua parte sinistra.
example (BevoVino MangioPasta : Prop) :
    BevoVino ∧ MangioPasta → BevoVino := by
  sorry

-- Vogliamo dimostrare che mi ubriaco, date le assunzioni che bevo vino e che,
-- se bevo vino, mi ubriaco.
example (BevoVino MiUbriaco : Prop)
    (hBevoVino : BevoVino)
    (hVinoUbriaco : BevoVino → MiUbriaco) :
    MiUbriaco := by
  sorry

-- Vogliamo dimostrare che porto l'ombrello e indosso il cappotto, date le
-- assunzioni che porto l'ombrello e che indosso il cappotto.
example (PortoOmbrello IndossoCappotto : Prop)
    (hPortoOmbrello : PortoOmbrello)
    (hIndossoCappotto : IndossoCappotto) :
    PortoOmbrello ∧ IndossoCappotto := by
  sorry

-- Vogliamo dimostrare che indosso il cappotto, data l'assunzione che porto
-- l'ombrello e indosso il cappotto.
example (PortoOmbrello IndossoCappotto : Prop)
    (hAbbigliamento : PortoOmbrello ∧ IndossoCappotto) :
    IndossoCappotto := by
  sorry

end ImplicazioneECongiunzione

section Disgiunzione

-- Vogliamo dimostrare che viaggio in autobus oppure in treno, data
-- l'assunzione che viaggio in autobus.
example (ViaggioInAutobus ViaggioInTreno : Prop)
    (hAutobus : ViaggioInAutobus) :
    ViaggioInAutobus ∨ ViaggioInTreno := by
  sorry

-- Vogliamo dimostrare che viaggio in autobus oppure in treno, data
-- l'assunzione che viaggio in treno.
example (ViaggioInAutobus ViaggioInTreno : Prop)
    (hTreno : ViaggioInTreno) :
    ViaggioInAutobus ∨ ViaggioInTreno := by
  sorry

-- Vogliamo dimostrare che arrivo in orario, date le assunzioni che viaggio in
-- autobus oppure in treno e che ciascuna scelta mi fa arrivare in orario.
example (ViaggioInAutobus ViaggioInTreno ArrivoInOrario : Prop)
    (hScelta : ViaggioInAutobus ∨ ViaggioInTreno)
    (hAutobusOrario : ViaggioInAutobus → ArrivoInOrario)
    (hTrenoOrario : ViaggioInTreno → ArrivoInOrario) :
    ArrivoInOrario := by
  sorry

end Disgiunzione

section NegazioneVeritaEFalsita

-- Vogliamo dimostrare che non bevo caffè, date le assunzioni che, se bevo
-- caffè, resto sveglio e che non resto sveglio.
example (BevoCaffe RestoSveglio : Prop)
    (hCaffeSveglio : BevoCaffe → RestoSveglio)
    (hNonSveglio : ¬RestoSveglio) :
    ¬BevoCaffe := by
  sorry

-- Vogliamo ottenere una contraddizione, date le assunzioni che il negozio è
-- aperto e che il negozio non è aperto.
example (NegozioAperto : Prop)
    (hAperto : NegozioAperto)
    (hNonAperto : ¬NegozioAperto) :
    False := by
  sorry

-- `True` non richiede assunzioni.
example : True := by
  sorry

-- Da una contraddizione vogliamo dimostrare una proposizione qualsiasi.
example (RicevoUnPremio : Prop) (hContraddizione : False) :
    RicevoUnPremio := by
  sorry

end NegazioneVeritaEFalsita

section Bicondizionale

-- Vogliamo dimostrare che «la porta è chiusa e la luce è spenta» equivale a
-- «la luce è spenta e la porta è chiusa».
example (PortaChiusa LuceSpenta : Prop) :
    PortaChiusa ∧ LuceSpenta ↔ LuceSpenta ∧ PortaChiusa := by
  sorry

-- Vogliamo usare la direzione sinistra-destra di un bicondizionale.
example (NumeroPari DivisibilePerDue : Prop)
    (hEquivalenza : NumeroPari ↔ DivisibilePerDue)
    (hPari : NumeroPari) :
    DivisibilePerDue := by
  sorry

-- Vogliamo usare la direzione destra-sinistra di un bicondizionale.
example (NumeroPari DivisibilePerDue : Prop)
    (hEquivalenza : NumeroPari ↔ DivisibilePerDue)
    (hDivisibile : DivisibilePerDue) :
    NumeroPari := by
  sorry

end Bicondizionale

section RiduzioneAllAssurdo

-- Vogliamo dimostrare che studio, date le assunzioni che, se non studio, non
-- supero l'esame e che supero l'esame. Usiamo la riduzione all'assurdo.
example (Studio SuperoEsame : Prop)
    (hNonStudioNonSupero : ¬Studio → ¬SuperoEsame)
    (hSuperoEsame : SuperoEsame) :
    Studio := by
  sorry

end RiduzioneAllAssurdo

section ArgomentiCompleti

-- Vogliamo dimostrare che esco, date le assunzioni che piove oppure c'è il
-- sole, che se piove prendo l'ombrello, che se c'è il sole prendo gli occhiali
-- e che, in entrambi i casi, esco.
example (Piove Sole PortoOmbrello PortoOcchiali Esco : Prop)
    (hMeteo : Piove ∨ Sole)
    (hPioveOmbrello : Piove → PortoOmbrello)
    (hSoleOcchiali : Sole → PortoOcchiali)
    (hOmbrelloEsco : PortoOmbrello → Esco)
    (hOcchialiEsco : PortoOcchiali → Esco) :
    Esco := by
  sorry

end ArgomentiCompleti

end Course.Shared.Lecture03.IT.Exercises

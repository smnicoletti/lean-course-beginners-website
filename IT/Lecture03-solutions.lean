/-!
# Soluzioni, Lezione 3

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture03.IT.Solutions

section ImplicazioneECongiunzione

-- Vogliamo dimostrare che, se bevo vino e mangio la pasta, allora bevo vino.
-- Introduciamo l'assunzione e prendiamo la sua parte sinistra.
example (BevoVino MangioPasta : Prop) :
    BevoVino ∧ MangioPasta → BevoVino := by
  intro hBevoVinoEMangioPasta
  have hBevoVino := hBevoVinoEMangioPasta.left
  exact hBevoVino

-- Vogliamo dimostrare che mi ubriaco, date le assunzioni che bevo vino e che,
-- se bevo vino, mi ubriaco.
example (BevoVino MiUbriaco : Prop)
    (hBevoVino : BevoVino)
    (hVinoUbriaco : BevoVino → MiUbriaco) :
    MiUbriaco := by
  have hMiUbriaco := hVinoUbriaco hBevoVino
  exact hMiUbriaco

-- Vogliamo dimostrare che porto l'ombrello e indosso il cappotto, date le
-- assunzioni che porto l'ombrello e che indosso il cappotto.
example (PortoOmbrello IndossoCappotto : Prop)
    (hPortoOmbrello : PortoOmbrello)
    (hIndossoCappotto : IndossoCappotto) :
    PortoOmbrello ∧ IndossoCappotto := by
  apply And.intro
  · exact hPortoOmbrello
  · exact hIndossoCappotto

-- Vogliamo dimostrare che indosso il cappotto, data l'assunzione che porto
-- l'ombrello e indosso il cappotto.
example (PortoOmbrello IndossoCappotto : Prop)
    (hAbbigliamento : PortoOmbrello ∧ IndossoCappotto) :
    IndossoCappotto := by
  have hIndossoCappotto := hAbbigliamento.right
  exact hIndossoCappotto

end ImplicazioneECongiunzione

section Disgiunzione

-- Vogliamo dimostrare che viaggio in autobus oppure in treno, data
-- l'assunzione che viaggio in autobus.
example (ViaggioInAutobus ViaggioInTreno : Prop)
    (hAutobus : ViaggioInAutobus) :
    ViaggioInAutobus ∨ ViaggioInTreno := by
  apply Or.inl
  exact hAutobus

-- Vogliamo dimostrare che viaggio in autobus oppure in treno, data
-- l'assunzione che viaggio in treno.
example (ViaggioInAutobus ViaggioInTreno : Prop)
    (hTreno : ViaggioInTreno) :
    ViaggioInAutobus ∨ ViaggioInTreno := by
  apply Or.inr
  exact hTreno

-- Vogliamo dimostrare che arrivo in orario, date le assunzioni che viaggio in
-- autobus oppure in treno e che ciascuna scelta mi fa arrivare in orario.
example (ViaggioInAutobus ViaggioInTreno ArrivoInOrario : Prop)
    (hScelta : ViaggioInAutobus ∨ ViaggioInTreno)
    (hAutobusOrario : ViaggioInAutobus → ArrivoInOrario)
    (hTrenoOrario : ViaggioInTreno → ArrivoInOrario) :
    ArrivoInOrario := by
  cases hScelta with
  | inl hAutobus =>
      have hArrivoInOrario := hAutobusOrario hAutobus
      exact hArrivoInOrario
  | inr hTreno =>
      have hArrivoInOrario := hTrenoOrario hTreno
      exact hArrivoInOrario

end Disgiunzione

section NegazioneVeritaEFalsita

-- Vogliamo dimostrare che non bevo caffè, date le assunzioni che, se bevo
-- caffè, resto sveglio e che non resto sveglio.
example (BevoCaffe RestoSveglio : Prop)
    (hCaffeSveglio : BevoCaffe → RestoSveglio)
    (hNonSveglio : ¬RestoSveglio) :
    ¬BevoCaffe := by
  intro hBevoCaffe
  have hRestoSveglio := hCaffeSveglio hBevoCaffe
  have hContraddizione := hNonSveglio hRestoSveglio
  exact hContraddizione

-- Vogliamo ottenere una contraddizione, date le assunzioni che il negozio è
-- aperto e che il negozio non è aperto.
example (NegozioAperto : Prop)
    (hAperto : NegozioAperto)
    (hNonAperto : ¬NegozioAperto) :
    False := by
  have hContraddizione := hNonAperto hAperto
  exact hContraddizione

-- `True` non richiede assunzioni.
example : True := by
  exact True.intro

-- Da una contraddizione vogliamo dimostrare una proposizione qualsiasi.
example (RicevoUnPremio : Prop) (hContraddizione : False) :
    RicevoUnPremio := by
  apply False.elim
  exact hContraddizione

end NegazioneVeritaEFalsita

section Bicondizionale

-- Vogliamo dimostrare che «la porta è chiusa e la luce è spenta» equivale a
-- «la luce è spenta e la porta è chiusa».
example (PortaChiusa LuceSpenta : Prop) :
    PortaChiusa ∧ LuceSpenta ↔ LuceSpenta ∧ PortaChiusa := by
  apply Iff.intro
  · intro hPortaChiusaELuceSpenta
    apply And.intro
    · exact hPortaChiusaELuceSpenta.right
    · exact hPortaChiusaELuceSpenta.left
  · intro hLuceSpentaEPortaChiusa
    apply And.intro
    · exact hLuceSpentaEPortaChiusa.right
    · exact hLuceSpentaEPortaChiusa.left

-- Vogliamo usare la direzione sinistra-destra di un bicondizionale.
example (NumeroPari DivisibilePerDue : Prop)
    (hEquivalenza : NumeroPari ↔ DivisibilePerDue)
    (hPari : NumeroPari) :
    DivisibilePerDue := by
  have hDirezione := Iff.mp hEquivalenza
  have hDivisibile := hDirezione hPari
  exact hDivisibile

-- Vogliamo usare la direzione destra-sinistra di un bicondizionale.
example (NumeroPari DivisibilePerDue : Prop)
    (hEquivalenza : NumeroPari ↔ DivisibilePerDue)
    (hDivisibile : DivisibilePerDue) :
    NumeroPari := by
  have hDirezione := Iff.mpr hEquivalenza
  have hPari := hDirezione hDivisibile
  exact hPari

end Bicondizionale

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
  cases hMeteo with
  | inl hPiove =>
      have hPortoOmbrello := hPioveOmbrello hPiove
      have hEsco := hOmbrelloEsco hPortoOmbrello
      exact hEsco
  | inr hSole =>
      have hPortoOcchiali := hSoleOcchiali hSole
      have hEsco := hOcchialiEsco hPortoOcchiali
      exact hEsco

end ArgomentiCompleti

end Course.Shared.Lecture03.IT.Solutions

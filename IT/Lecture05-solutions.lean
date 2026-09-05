/-!
# Soluzioni, Lezione 5

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture05.IT.Solutions

-- ============================================================
-- FORMALIZZAZIONE CON IL VOCABOLARIO GIÀ FORNITO
-- ============================================================

section FormalizzazioneConVocabolario

variable (Cosa : Type)
variable (Ricercatrice Articolo Interessante Revisionato : Cosa → Prop)
variable (Legge Cita : Cosa → Cosa → Prop)
variable (articoloPreferito : Cosa → Cosa)
variable (ada : Cosa)

-- 1. Ogni ricercatrice legge qualche articolo.
#check ∀ x : Cosa, Ricercatrice x →
  ∃ y : Cosa, Articolo y ∧ Legge x y

-- 2. Esiste un articolo interessante e revisionato.
#check ∃ x : Cosa, Articolo x ∧ Interessante x ∧ Revisionato x

-- 3. L'articolo preferito di Ada è interessante.
#check Interessante (articoloPreferito ada)

-- 4. Ogni ricercatrice cita il proprio articolo preferito.
#check ∀ x : Cosa, Ricercatrice x → Cita x (articoloPreferito x)

-- 5. Ogni ricercatrice legge almeno un articolo interessante.
#check ∀ x : Cosa, Ricercatrice x →
  ∃ y : Cosa, Articolo y ∧ Interessante y ∧ Legge x y

-- 6. Esiste un articolo letto da ogni ricercatrice.
#check ∃ y : Cosa, Articolo y ∧
  ∀ x : Cosa, Ricercatrice x → Legge x y

end FormalizzazioneConVocabolario

-- ============================================================
-- FORMALIZZAZIONE DAL SOLO LINGUAGGIO NATURALE
-- ============================================================

section FormalizzazioneAutonoma

variable (Cosa : Type)
variable (Museo Opera Visitatrice : Cosa → Prop)
variable (Espone Ammira Visita : Cosa → Cosa → Prop)
variable (curatriceDi operaPreferita : Cosa → Cosa)
variable (uffizi roma : Cosa)

-- 1. Ogni museo espone qualche opera.
#check ∀ x : Cosa, Museo x →
  ∃ y : Cosa, Opera y ∧ Espone x y

-- 2. Esiste un'opera ammirata da ogni visitatrice.
#check ∃ y : Cosa, Opera y ∧
  ∀ x : Cosa, Visitatrice x → Ammira x y

-- 3. Nessuna visitatrice ammira ogni opera.
#check ¬∃ x : Cosa, Visitatrice x ∧
  ∀ y : Cosa, Opera y → Ammira x y

-- 4. La curatrice degli Uffizi visita Roma.
#check Visita (curatriceDi uffizi) roma

-- 5. Ogni visitatrice ammira la propria opera preferita.
#check ∀ x : Cosa, Visitatrice x → Ammira x (operaPreferita x)

-- 6. Esiste una visitatrice la cui opera preferita è esposta dagli Uffizi.
#check ∃ x : Cosa, Visitatrice x ∧ Espone uffizi (operaPreferita x)

end FormalizzazioneAutonoma

-- ============================================================
-- INTRODUZIONE ED ELIMINAZIONE DEI QUANTIFICATORI
-- ============================================================

section RegoleDeiQuantificatori

-- Introduzione di ∀.
-- Vogliamo dimostrare che ogni gatta che dorme, dorme.
example (Cosa : Type)
    (Gatta Dorme : Cosa → Prop) :
    ∀ x : Cosa, Gatta x → Dorme x → Dorme x := by
  intro x
  intro hXGatta
  intro hXDorme
  exact hXDorme

-- Eliminazione di ∀.
-- Ogni biblioteca è aperta e la Biblioteca Centrale è una biblioteca.
-- Vogliamo dimostrare che la Biblioteca Centrale è aperta.
example (Cosa : Type)
    (Biblioteca Aperta : Cosa → Prop)
    (bibliotecaCentrale : Cosa)
    (hOgniBibliotecaAperta :
      ∀ x : Cosa, Biblioteca x → Aperta x)
    (hCentraleBiblioteca : Biblioteca bibliotecaCentrale) :
    Aperta bibliotecaCentrale := by
  have hSeCentraleBibliotecaAlloraAperta :=
    hOgniBibliotecaAperta bibliotecaCentrale
  have hCentraleAperta :=
    hSeCentraleBibliotecaAlloraAperta hCentraleBiblioteca
  exact hCentraleAperta

-- Introduzione di ∃.
-- Elisa prepara il pane. Vogliamo dimostrare che qualcuno prepara il pane.
example (Cosa : Type)
    (PreparaPane : Cosa → Prop)
    (elisa : Cosa)
    (hElisaPreparaPane : PreparaPane elisa) :
    ∃ x : Cosa, PreparaPane x := by
  apply Exists.intro elisa
  exact hElisaPreparaPane

-- Eliminazione di ∃.
-- Qualcuno ha premuto l'allarme e, se qualcuno preme l'allarme, suona la
-- sirena. Vogliamo dimostrare che suona la sirena.
example (Cosa : Type)
    (HaPremutoAllarme : Cosa → Prop)
    (SuonaSirena : Prop)
    (hQualcunoHaPremutoAllarme :
      ∃ x : Cosa, HaPremutoAllarme x)
    (hChiPremeAllarmeFaSuonareSirena :
      (x : Cosa) → HaPremutoAllarme x → SuonaSirena) :
    SuonaSirena := by
  apply Exists.elim hQualcunoHaPremutoAllarme
  intro y
  intro hYHaPremutoAllarme
  have hSeYPremeAllarmeAlloraSuonaSirena :=
    hChiPremeAllarmeFaSuonareSirena y
  have hSuonaSirena :=
    hSeYPremeAllarmeAlloraSuonaSirena hYHaPremutoAllarme
  exact hSuonaSirena

-- Combinazione di ∃E, ∀E e ∃I.
-- Qualcuno ha dei semi e chiunque abbia dei semi pianta dei fiori.
-- Vogliamo dimostrare che qualcuno pianta dei fiori.
example (Cosa : Type)
    (HaSemi PiantaFiori : Cosa → Prop)
    (hQualcunoHaSemi : ∃ x : Cosa, HaSemi x)
    (hChiHaSemiPiantaFiori :
      ∀ x : Cosa, HaSemi x → PiantaFiori x) :
    ∃ x : Cosa, PiantaFiori x := by
  apply Exists.elim hQualcunoHaSemi
  intro y
  intro hYHaSemi
  apply Exists.intro y
  have hSeYHaSemiAlloraPiantaFiori := hChiHaSemiPiantaFiori y
  have hYPiantaFiori := hSeYHaSemiAlloraPiantaFiori hYHaSemi
  exact hYPiantaFiori

example (Cosa : Type)
    (Violinista Prova Preparata Serena : Cosa → Prop)
    (hChiProvaPreparata :
      ∀ x : Cosa, Violinista x → Prova x → Preparata x)
    (hChiProvaSerena :
      ∀ x : Cosa, Violinista x → Prova x → Serena x) :
    ∀ x : Cosa, Violinista x → Prova x → Preparata x ∧ Serena x := by
  intro x
  intro hXViolinista
  intro hXProva
  apply And.intro
  · have hSeXViolinistaAlloraProvaImplicaPreparata :=
      hChiProvaPreparata x
    have hSeXProvaAlloraPreparata :=
      hSeXViolinistaAlloraProvaImplicaPreparata hXViolinista
    have hXPreparata := hSeXProvaAlloraPreparata hXProva
    exact hXPreparata
  · have hSeXViolinistaAlloraProvaImplicaSerena :=
      hChiProvaSerena x
    have hSeXProvaAlloraSerena :=
      hSeXViolinistaAlloraProvaImplicaSerena hXViolinista
    have hXSerena := hSeXProvaAlloraSerena hXProva
    exact hXSerena

example (Cosa : Type)
    (ArrivaAPiedi ArrivaInBici TrovaRiparo : Cosa → Prop)
    (hQualcunoArriva :
      ∃ x : Cosa, ArrivaAPiedi x ∨ ArrivaInBici x)
    (hChiArrivaAPiediTrovaRiparo :
      ∀ x : Cosa, ArrivaAPiedi x → TrovaRiparo x)
    (hChiArrivaInBiciTrovaRiparo :
      ∀ x : Cosa, ArrivaInBici x → TrovaRiparo x) :
    ∃ x : Cosa, TrovaRiparo x := by
  apply Exists.elim hQualcunoArriva
  intro y
  intro hYArrivaAPiediOInBici
  cases hYArrivaAPiediOInBici with
  | inl hYArrivaAPiedi =>
      apply Exists.intro y
      have hSeYArrivaAPiediAlloraTrovaRiparo :=
        hChiArrivaAPiediTrovaRiparo y
      have hYTrovaRiparo :=
        hSeYArrivaAPiediAlloraTrovaRiparo hYArrivaAPiedi
      exact hYTrovaRiparo
  | inr hYArrivaInBici =>
      apply Exists.intro y
      have hSeYArrivaInBiciAlloraTrovaRiparo :=
        hChiArrivaInBiciTrovaRiparo y
      have hYTrovaRiparo :=
        hSeYArrivaInBiciAlloraTrovaRiparo hYArrivaInBici
      exact hYTrovaRiparo

example (Cosa : Type)
    (HaPrenotato HaRicevutoBiglietto : Cosa → Prop)
    (hChiHaPrenotatoRiceveBiglietto :
      ∀ x : Cosa, HaPrenotato x → HaRicevutoBiglietto x)
    (hControesempio :
      ∃ x : Cosa, HaPrenotato x ∧ ¬HaRicevutoBiglietto x) :
    False := by
  apply Exists.elim hControesempio
  intro y
  intro hYHaPrenotatoENonHaRicevutoBiglietto
  have hYHaPrenotato := hYHaPrenotatoENonHaRicevutoBiglietto.left
  have hYNonHaRicevutoBiglietto :=
    hYHaPrenotatoENonHaRicevutoBiglietto.right
  have hSeYHaPrenotatoAlloraRiceveBiglietto :=
    hChiHaPrenotatoRiceveBiglietto y
  have hYHaRicevutoBiglietto :=
    hSeYHaPrenotatoAlloraRiceveBiglietto hYHaPrenotato
  have hContraddizione :=
    hYNonHaRicevutoBiglietto hYHaRicevutoBiglietto
  exact hContraddizione

end RegoleDeiQuantificatori

end Course.Shared.Lecture05.IT.Solutions

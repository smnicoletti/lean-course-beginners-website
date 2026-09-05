/-!
# Esercizi, Lezione 5

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture05.IT.Exercises

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
#check sorry

-- 2. Esiste un articolo interessante e revisionato.
#check sorry

-- 3. L'articolo preferito di Ada è interessante.
#check sorry

-- 4. Ogni ricercatrice cita il proprio articolo preferito.
#check sorry

-- 5. Ogni ricercatrice legge almeno un articolo interessante.
#check sorry

-- 6. Esiste un articolo letto da ogni ricercatrice.
#check sorry

end FormalizzazioneConVocabolario

-- ============================================================
-- FORMALIZZAZIONE DAL SOLO LINGUAGGIO NATURALE
-- ============================================================

section FormalizzazioneAutonoma

-- Per ciascun enunciato:
-- 1. dichiarare un dominio `Cosa`;
-- 2. dichiarare gli oggetti, i predicati, le relazioni o le funzioni necessari;
-- 3. usare `#check` per controllare la formalizzazione.

-- 1. Ogni museo espone qualche opera.

-- 2. Esiste un'opera ammirata da ogni visitatrice.

-- 3. Nessuna visitatrice ammira ogni opera.

-- 4. La curatrice degli Uffizi visita Roma.

-- 5. Ogni visitatrice ammira la propria opera preferita.

-- 6. Esiste una visitatrice la cui opera preferita è esposta dagli Uffizi.

-- Scrivere qui le dichiarazioni e le formalizzazioni:

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
  sorry

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
  sorry

-- Introduzione di ∃.
-- Elisa prepara il pane. Vogliamo dimostrare che qualcuno prepara il pane.
example (Cosa : Type)
    (PreparaPane : Cosa → Prop)
    (elisa : Cosa)
    (hElisaPreparaPane : PreparaPane elisa) :
    ∃ x : Cosa, PreparaPane x := by
  sorry

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
  sorry

-- Combinazione di ∃E, ∀E e ∃I.
-- Qualcuno ha dei semi e chiunque abbia dei semi pianta dei fiori.
-- Vogliamo dimostrare che qualcuno pianta dei fiori.
example (Cosa : Type)
    (HaSemi PiantaFiori : Cosa → Prop)
    (hQualcunoHaSemi : ∃ x : Cosa, HaSemi x)
    (hChiHaSemiPiantaFiori :
      ∀ x : Cosa, HaSemi x → PiantaFiori x) :
    ∃ x : Cosa, PiantaFiori x := by
  sorry

-- Combinazione di ∀I, ∀E, →I e ∧I.
-- Ogni violinista che prova è preparata; ogni violinista che prova è serena.
-- Dimostrare che ogni violinista che prova è preparata e serena.
example (Cosa : Type)
    (Violinista Prova Preparata Serena : Cosa → Prop)
    (hChiProvaPreparata :
      ∀ x : Cosa, Violinista x → Prova x → Preparata x)
    (hChiProvaSerena :
      ∀ x : Cosa, Violinista x → Prova x → Serena x) :
    ∀ x : Cosa, Violinista x → Prova x → Preparata x ∧ Serena x := by
  sorry

-- Combinazione di ∃E, ∨E, ∀E e ∃I.
-- Qualcuno raggiunge il rifugio a piedi oppure in bicicletta; chi lo raggiunge
-- in uno dei due modi trova riparo. Dimostrare che qualcuno trova riparo.
example (Cosa : Type)
    (ArrivaAPiedi ArrivaInBici TrovaRiparo : Cosa → Prop)
    (hQualcunoArriva :
      ∃ x : Cosa, ArrivaAPiedi x ∨ ArrivaInBici x)
    (hChiArrivaAPiediTrovaRiparo :
      ∀ x : Cosa, ArrivaAPiedi x → TrovaRiparo x)
    (hChiArrivaInBiciTrovaRiparo :
      ∀ x : Cosa, ArrivaInBici x → TrovaRiparo x) :
    ∃ x : Cosa, TrovaRiparo x := by
  sorry

-- Combinazione di ∃E, ∧E, ∀E e ¬E.
-- Chi ha prenotato riceve un biglietto; qualcuno ha prenotato ma non ha
-- ricevuto un biglietto. Dimostrare che le assunzioni sono contraddittorie.
example (Cosa : Type)
    (HaPrenotato HaRicevutoBiglietto : Cosa → Prop)
    (hChiHaPrenotatoRiceveBiglietto :
      ∀ x : Cosa, HaPrenotato x → HaRicevutoBiglietto x)
    (hControesempio :
      ∃ x : Cosa, HaPrenotato x ∧ ¬HaRicevutoBiglietto x) :
    False := by
  sorry

end RegoleDeiQuantificatori

end Course.Shared.Lecture05.IT.Exercises

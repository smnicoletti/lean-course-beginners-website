/-!
# Soluzioni, Lezione 4

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture04.IT.Solutions

section RiduzioneAllAssurdo

-- Vogliamo dimostrare che studio, date le assunzioni che, se non studio, non
-- supero l'esame e che supero l'esame. Usiamo la riduzione all'assurdo.
example (Studio SuperoEsame : Prop)
    (hNonStudioNonSupero : ¬Studio → ¬SuperoEsame)
    (hSuperoEsame : SuperoEsame) :
    Studio := by
  apply Classical.byContradiction
  intro hNonStudio
  have hNonSuperoEsame := hNonStudioNonSupero hNonStudio
  have hContraddizione := hNonSuperoEsame hSuperoEsame
  exact hContraddizione

end RiduzioneAllAssurdo

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
-- Beatrice prepara il pane. Vogliamo dimostrare che qualcuno prepara il pane.
example (Cosa : Type)
    (PreparaPane : Cosa → Prop)
    (beatrice : Cosa)
    (hBeatricePreparaPane : PreparaPane beatrice) :
    ∃ x : Cosa, PreparaPane x := by
  apply Exists.intro beatrice
  exact hBeatricePreparaPane

-- Eliminazione di ∃.
-- Qualcuno ha premuto l'allarme e, se qualcuno preme l'allarme, suona la
-- sirena. Vogliamo dimostrare che suona la sirena.
example (Cosa : Type)
    (HaPremutoAllarme : Cosa → Prop)
    (SuonaSirena : Prop)
    (hQualcunoHaPremutoAllarme :
      ∃ x : Cosa, HaPremutoAllarme x)
    (hChiPremeAllarmeFaSuonareSirena :
      ∀ x : Cosa, HaPremutoAllarme x → SuonaSirena) :
    SuonaSirena := by
  apply Exists.elim hQualcunoHaPremutoAllarme
  intro y
  intro hYHaPremutoAllarme
  have hSirena :=
    hChiPremeAllarmeFaSuonareSirena y hYHaPremutoAllarme
  exact hSirena

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
  intro x
  intro hXHaSemi
  apply Exists.intro x
  have hXPiantaFiori := hChiHaSemiPiantaFiori x hXHaSemi
  exact hXPiantaFiori

end RegoleDeiQuantificatori

end Course.Shared.Lecture04.IT.Solutions

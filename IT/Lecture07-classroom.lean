/-!
# Lezione 7: Induzione, semplificazione e verifica del software

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture07.IT.Classroom

-- ============================================================
-- RIPASSO DELLE DEFINIZIONI DELLA LEZIONE 6
-- ============================================================

inductive Naturale where
  | zero
  | succ (n : Naturale)

open Naturale

def uno : Naturale := succ zero
def due : Naturale := succ uno

def somma (m n : Naturale) : Naturale :=
  match n with
  | zero => m
  | succ n => succ (somma m n)

def doppio (n : Naturale) : Naturale :=
  match n with
  | zero => zero
  | succ n => succ (succ (doppio n))

theorem lecture07_somma_zero_destra (m : Naturale) :
    somma m zero = m := by
  rfl

theorem lecture07_somma_succ_destra (m n : Naturale) :
    somma m (succ n) = succ (somma m n) := by
  rfl

theorem lecture07_doppio_succ (n : Naturale) :
    doppio (succ n) = succ (succ (doppio n)) := by
  rfl

-- Questo è il risultato raggiunto al termine della Lezione 6.
theorem lecture07_zero_somma (n : Naturale) :
    somma zero n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold somma
      rewrite [ih]
      rfl

-- ============================================================
-- UNA SECONDA DIMOSTRAZIONE PER INDUZIONE
-- ============================================================

-- Anche in questo goal la computazione è bloccata dal secondo argomento di
-- `somma`. Facciamo quindi induzione su `n`, non su `m`: nel passo successore
-- `ih` riguarda precisamente le due somme ricorsive con secondo argomento `n`.
theorem lecture07_succ_somma (m n : Naturale) :
    somma (succ m) n = succ (somma m n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Apriamo entrambe le somme nel caso in cui il secondo argomento
      -- sia `succ n`. Il goal interno riguarda ora il naturale più piccolo `n`.
      unfold somma
      -- `ih` sostituisce la somma con primo argomento `succ m` e secondo `n`.
      rewrite [ih] -- Osservate la differenza con: rewrite [← ih]
      rfl

-- ============================================================
-- ASSOCIATIVITÀ E COMMUTATIVITÀ
-- ============================================================

-- Associatività: raggruppare prima `a` e `b` oppure prima `b` e `c`
-- non cambia il risultato. Poiché `somma` ricorre sul secondo argomento,
-- scegliamo `c`: entrambe le somme esterne avanzano secondo la definizione.
theorem lecture07_somma_assoc (a b c : Naturale) :
    somma (somma a b) c = somma a (somma b c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      -- Riduciamo la somma esterna a sinistra nel caso `succ c`.
      rw [lecture07_somma_succ_destra]
      -- Riduciamo prima `somma b (succ c)` sul lato destro.
      rw [lecture07_somma_succ_destra]
      -- Riduciamo quindi la somma esterna ottenuta sul lato destro.
      rw [lecture07_somma_succ_destra]
      -- Abbiamo raggiunto la forma descritta dall'ipotesi induttiva.
      rw [ih]

-- Commutatività: scambiare gli argomenti non cambia la somma.
-- La definizione non tratta simmetricamente i due argomenti. Nel caso base
-- usiamo `zero_somma`, mentre nel passo usiamo anche `succ_somma`.
theorem lecture07_somma_comm (a b : Naturale) :
    somma a b = somma b a := by
  induction b with
  | zero =>
      -- A sinistra la somma si riduce. A destra usiamo il risultato che
      -- sposta `zero` dalla prima posizione.
      rw [lecture07_zero_somma]
      rfl
  | succ b ih =>
      -- Il lato sinistro si riduce perché `succ b` è il secondo argomento.
      rw [lecture07_somma_succ_destra]
      -- Sul lato destro usiamo `succ_somma` per portare `succ` all'esterno.
      rw [lecture07_succ_somma]
      -- Sotto il costruttore `succ` rimane il caso induttivo per `b`.
      rw [ih]

-- ============================================================
-- IL SEMPLIFICATORE
-- ============================================================

-- `simp` applica automaticamente equazioni orientate verso forme più semplici.
-- Partiamo da una dimostrazione già compresa e confrontiamo tre livelli.

theorem lecture07_zero_somma_con_rw (n : Naturale) : somma zero n = n := by
  rw [lecture07_zero_somma]

theorem lecture07_zero_somma_con_simp_only (n : Naturale) :
    somma zero n = n := by
  -- Usiamo soltanto il lemma indicato come regola di riscrittura.
  -- `simp only` rende quindi esplicita la regola che chiude il goal.
  simp only [lecture07_zero_somma]

theorem lecture07_zero_somma_con_simp (n : Naturale) : somma zero n = n := by
  -- `simp` usa il proprio insieme di regole standard e vi aggiunge
  -- `lecture07_zero_somma` per questo comando.
  simp [lecture07_zero_somma]

section SemplificazioneLocale

-- Registriamo i due lemmi nel simp-set soltanto dentro questa sezione.
-- Fuori da `SemplificazioneLocale` non saranno regole `simp` automatiche.
attribute [local simp] lecture07_zero_somma lecture07_succ_somma

theorem lecture07_succ_somma_con_simp (m n : Naturale) :
    somma (succ m) n = succ (somma m n) := by
  -- Non occorre più nominare `lecture07_succ_somma`: il comando `simp`
  -- lo trova nel simp-set locale e riscrive il lato sinistro del goal.
  simp

end SemplificazioneLocale

-- `@[simp]` registra questo lemma nel simp-set del modulo. È una buona regola
-- di semplificazione perché sostituisce `doppio zero` con la forma più semplice
-- `zero`. La sua dimostrazione è `rfl` perché segue direttamente dalla
-- definizione di `doppio`.
@[simp] theorem lecture07_doppio_zero :
    doppio zero = zero := by
  rfl

-- Non registriamo associatività e commutatività come regole `simp`.
-- Queste uguaglianze cambiano l'ordine o il raggruppamento senza indicare una
-- forma evidentemente più semplice verso cui normalizzare ogni espressione.

-- ============================================================
-- DIMOSTRAZIONE CONCLUSIVA
-- ============================================================

-- Esercizio: il doppio di una somma è la somma dei doppi.
-- La riduzione di `somma m n` dipende da `n`, quindi scegliamo `n`.
theorem lecture07_doppio_somma (m n : Naturale) :
    doppio (somma m n) = somma (doppio m) (doppio n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [lecture07_somma_succ_destra]
      rw [lecture07_doppio_succ]
      rw [lecture07_doppio_succ]
      rw [lecture07_somma_succ_destra]
      rw [lecture07_somma_succ_destra]
      rw [ih]

-- La stessa dimostrazione può poi essere abbreviata con regole controllate.
theorem lecture07_doppio_somma_breve (m n : Naturale) :
    doppio (somma m n) = somma (doppio m) (doppio n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [lecture07_somma_succ_destra, lecture07_doppio_succ, ih]

-- ============================================================
-- DALL'INDUZIONE ALLA VERIFICA DEL SOFTWARE
-- ============================================================

-- Un programma riceve un input e produce un output. Verificarlo significa
-- formulare con precisione una proprietà attesa e dimostrarla per ogni input.
-- Iniziamo definendo induttivamente il tipo delle liste.
inductive Lista (α : Type) where
  | vuota
  | cons (testa : α) (coda : Lista α)

end Course.Shared.Lecture07.IT.Classroom

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
-- Per costruire un piccolo esempio definiamo anche il tipo delle liste.
-- `α` rappresenta il tipo degli elementi. La stessa definizione costruisce
-- quindi liste di naturali, stringhe o altri tipi: questo modo di riutilizzare
-- una definizione per tipi diversi si chiama polimorfismo parametrico.
inductive Lista (α : Type) where
  | vuota
  | cons (testa : α) (coda : Lista α)

open Lista

-- Una lista è vuota oppure è costruita aggiungendo un elemento davanti a una
-- lista più piccola. Per esempio, questa lista contiene tre naturali.
def listaEsempio : Lista Naturale :=
  cons zero (cons uno (cons due vuota))

-- Per rovesciare una lista ci serve concatenarne due. La definizione analizza
-- la prima lista: trasferisce un elemento alla volta davanti al risultato.
-- Le parentesi graffe in `{α : Type}` rendono `α` implicito: Lean lo ricava
-- dal tipo delle liste `xs` e `ys`, quindi scriviamo `concatena xs ys`.
def concatena {α : Type} (xs ys : Lista α) : Lista α :=
  match xs with
  | vuota => ys
  | cons x xs => cons x (concatena xs ys)

-- L'algoritmo ricorsivo lascia invariata la lista vuota. Nel caso `cons`,
-- rovescia prima la coda e colloca la testa in fondo al risultato.
def rovescia {α : Type} (xs : Lista α) : Lista α :=
  match xs with
  | vuota => vuota
  | cons x xs => concatena (rovescia xs) (cons x vuota)

-- Vogliamo dimostrare la proprietà seguente per ogni lista `xs`:
--
--   rovescia (rovescia xs) = xs
--
-- Questa è una proprietà importante, ma non caratterizza da sola l'algoritmo.
-- Anche la funzione identità soddisferebbe la stessa equazione.
--
-- Prima della proprietà finale dimostriamo alcuni lemmi che ci saranno utili:
-- la concatenazione con la lista vuota, l'associatività della concatenazione
-- e il comportamento di `rovescia` su una concatenazione.

-- `concatena` analizza il primo argomento, quindi facciamo induzione su `xs`.
theorem lecture07_concatena_vuota_destra
    {α : Type} (xs : Lista α) :
    concatena xs vuota = xs := by
  induction xs with
  | vuota =>
      rfl
  | cons x xs ih =>
      simp [concatena, ih]

-- Questa uguaglianza elimina una concatenazione con la lista vuota e conduce
-- a una forma più semplice. La aggiungiamo quindi al simp-set locale.
attribute [local simp] lecture07_concatena_vuota_destra

-- Cambiare il raggruppamento di tre concatenazioni non cambia la lista.
-- Anche qui l'argomento che guida la computazione è `xs`.
theorem lecture07_concatena_assoc
    {α : Type} (xs ys zs : Lista α) :
    concatena (concatena xs ys) zs =
      concatena xs (concatena ys zs) := by
  induction xs with
  | vuota =>
      rfl
  | cons x xs ih =>
      simp [concatena, ih]

-- Non aggiungiamo l'associatività al simp-set. Cambia il raggruppamento, ma non
-- indica in generale una forma più semplice. Quando serve, la nominiamo.

-- Possiamo ora dimostrare che rovesciare una concatenazione scambia l'ordine
-- delle due parti.
theorem lecture07_rovescia_concatena
    {α : Type} (xs ys : Lista α) :
    rovescia (concatena xs ys) =
      concatena (rovescia ys) (rovescia xs) := by
  induction xs with
  | vuota =>
      simp [concatena, rovescia]
  | cons x xs ih =>
      -- Le definizioni e `ih` lasciano le stesse tre liste raggruppate in modo
      -- diverso sui due lati. Il goal rimasto mostra che serve l'associatività.
      -- La nominiamo qui, senza aggiungerla al simp-set.
      simp [concatena, rovescia, ih, lecture07_concatena_assoc]

-- Questa uguaglianza descrive la forma attesa del rovesciamento di una
-- concatenazione. La rendiamo disponibile a `simp` dentro questa sezione.
attribute [local simp] lecture07_rovescia_concatena

-- Proprietà di correttezza: rovesciare due volte restituisce la lista iniziale.
-- Non controlliamo soltanto alcuni esempi. La dimostrazione copre ogni lista,
-- perché segue i due modi in cui una `Lista α` può essere costruita.
theorem lecture07_rovescia_rovescia
    {α : Type} (xs : Lista α) :
    rovescia (rovescia xs) = xs := by
  induction xs with
  | vuota =>
      simp [rovescia]
  | cons x xs ih =>
      simp [rovescia, ih, concatena]

end Course.Shared.Lecture07.IT.Classroom

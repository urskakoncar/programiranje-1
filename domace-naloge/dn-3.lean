set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 Definirajte funkcijo, ki _rekurzivno_ (torej naivno in ne direktno s formulo,
 ki jo boste morali dokazati) sešteje prvih `n` naravnih števil, ter
 dokažite, da zanjo velja znana enakost (najprej v obliki, ki ne zahteva
 deljenja, nato pa še v običajni obliki).
------------------------------------------------------------------------------/

def vsota_prvih : Nat → Nat :=
  fun n =>
    match n with
    | Nat.zero => Nat.zero
    | Nat.succ n => Nat.succ n + vsota_prvih n


theorem gauss : (n : Nat) → 2 * vsota_prvih n = n * (n + 1) :=
  by
    intro n
    induction n with
    | zero =>
      simp [vsota_prvih]
    | succ n ih =>
      simp [vsota_prvih]
      rw [Nat.mul_add, Nat.two_mul]
      rw [ih]
      rw [Nat.mul_add (n + 1) n (1 + 1), Nat.mul_add (n + 1) 1 1]
      simp [Nat.mul_one]
      repeat rw [← Nat.add_assoc]
      rw [Nat.mul_comm (n + 1) n, Nat.add_comm]
      simp [Nat.add_assoc]


theorem cisto_pravi_gauss : (n : Nat) → vsota_prvih n = (n * (n + 1)) / 2 := by
  intro n
  calc
    vsota_prvih n
    _ = (2 * (vsota_prvih n)) / 2 := by simp [Nat.mul_div_right (n + 1 + vsota_prvih n)]
    _ = (n * (n + 1)) / 2 := by simp [gauss]


--tale gaus naprej ni za ocent, pustila sm zato, da bom se kdaj lahko ksn korak pogledala, ce bi mi koristlo
--theorem cisto_pravi_gauss_5_poskus : (n : Nat) → vsota_prvih n = (n * (n + 1)) / 2 := by
--  intro n
--  induction n with
--  | zero =>
--    simp [vsota_prvih]
--  | succ n ih =>
--    simp [vsota_prvih]
--    calc
--      n + 1 + vsota_prvih n
--      _ = (2 * (n + 1 + vsota_prvih n)) / 2 := by simp [Nat.mul_div_right (n + 1 + vsota_prvih n)]
--      _ = (2 * (n + 1) + 2 * (vsota_prvih n)) / 2 := by simp [Nat.mul_add]
--      _ = (2 * (n + 1) + (n * (n + 1))) / 2 := by simp [gauss]
--      _ = (n + 1 + (n + 1) + n * (n + 1)) / 2 := by simp [Nat.two_mul]
--      _ = (n + 1 + n + 1 + n * (n + 1)) / 2 := by simp [Nat.add_assoc]
--      _ = ((n + 1 + n + 1) + n * (n + 1)) / 2 := by simp [Nat.add_assoc]
--      _ = (n * (n + 1) + (n + 1 + n + 1)) / 2 := by simp [Nat.add_comm]
--      _ = (n * (n + 1) + n + 1 + n + 1) / 2 := by simp [Nat.add_assoc]
--      _ = (n * (n + 1) + (n + (1 + (n + 1)))) / 2 := by simp [Nat.add_assoc]
--      _ = (n * (n + 1) + (n + ((n + 1) + 1))) / 2 := by simp [Nat.add_comm 1 (n + 1)]
--      _ = (n * (n + 1) + (n + n + 1 + 1)) / 2 := by simp [Nat.add_assoc]
--      _ = (n * (n + 1) + n + n + 1 + 1) / 2 := by simp [Nat.add_assoc]
--      _ = (n * (n + 1) + n * 1 + n + 1 + 1) / 2 := by simp [Nat.one_mul]
--      _ = (n * (n + 1 + 1) + n + 1 + 1) / 2 := by simp [Nat.mul_add]
--      _ = (n * (n + 1 + 1) + (n + 1 + 1)) / 2 := by simp [Nat.add_assoc]
--      _ = (n * (n + 1 + 1) + 1 * (n + 1 + 1)) / 2 := by simp [Nat.one_mul]
--      _ = ((n + 1) * (n + 1 + 1)) / 2 := by simp [Nat.add_mul]
--      _ = (n + 1) * (n + 1 + 1) / 2 := by simp



/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje podobno kot na predavanjih, le da namesto svojih naravnih
 števil uporabimo vgrajena. Da se tipi ujamejo, funkcijo stikanja napišemo s
 pomočjo taktik.

 Napišite funkcijo `obrni`, ki vrne na glavo obrnjen vektor, ter funkciji
 `glava` in `rep`, ki varno vrneta glavo in rep _nepraznega_ seznama.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen => by rw [Nat.add_comm]; exact ys
  | .sestavljen x xs' => by rw [Nat.add_right_comm]; exact Vektor.sestavljen x (stakni xs' ys)


-------
def obrni : {A : Type} → {n : Nat} → Vektor A n → Vektor A n :=
  fun xs =>
  match xs with
  | .prazen => .prazen
  | .sestavljen x xs' => stakni (obrni xs') (Vektor.sestavljen x .prazen)

def glava : {A : Type} → {n : Nat} → Vektor A (n + 1) → A :=
  fun xs =>
  match xs with
  | .sestavljen x _ => x

def rep : {A : Type} → {n : Nat} → Vektor A (n + 1) → Vektor A n :=
  fun xs =>
  match xs with
  | .sestavljen _ xs' => xs'


/------------------------------------------------------------------------------
 ## Predikatni račun

 Dokažite spodnje tri trditve. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."
 Za dokaz potrebujete klasično logiko, torej nekaj iz modula `Classical`.
------------------------------------------------------------------------------/

theorem forall_implies : {A : Type} → {P Q : A → Prop} →
  (∀ x, (P x → Q x)) → (∀ x, P x) → (∀ x, Q x) := by
  intro A
  intro P Q
  intro f
  intro px
  intro x
  exact f x (px x)


theorem forall_implies' : {A : Type} → {P : Prop} → {Q : A → Prop} →
  (∀ x, (P → Q x)) ↔ (P → ∀ x, Q x) := by
  intro A
  intro P Q
  apply Iff.intro

  intro f
  intro p
  intro x
  exact f x p

  intro f
  intro x
  intro p
  exact f p x


open Classical

theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) := by

  intros G P g
  by_cases h : ∃ x, ¬ P x

  case pos => -- torej obstaja nekdo, ki ne pije
    have ⟨p, p_ne_pije⟩ := h --- da ne bom pozabila: spicaste oklepaje dobim z \ langle in \ rangle
    apply Exists.intro p
    intros p_pije x
    exfalso
    exact p_ne_pije p_pije

  case neg => -- vsi ljudje pijejo
    apply Exists.intro g
    intros g_pije x
    apply Classical.byContradiction
    intro x_ne_pije
    apply h
    exact ⟨x, x_ne_pije⟩


/------------------------------------------------------------------------------
 ## Dvojiška drevesa

 Podan naj bo tip dvojiških dreves skupaj s funkcijama za zrcaljenje in izračun
 višine ter dvema funkcijama, ki obe od leve proti desni naštejeta elemente
 drevesa. Pri tem prva deluje naivno in ima časovno zahtevnost O(n log n), druga
 pa je malo bolj zapletena in deluje v času O(n). Dokažite spodnje enakosti, pri
 čemer lahko do pomožne funkcije `aux` dostopate kot `elementi'.aux`
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → Drevo A → A → Drevo A → Drevo A

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno l x d => .sestavljeno (zrcali d) x (zrcali l)

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno l _ d => 1 + max (visina l) (visina d)

def elementi : {A : Type} → Drevo A → List A :=
  fun t => match t with
  | .prazno => []
  | .sestavljeno l x d => elementi l ++ x :: elementi d

def elementi' : {A : Type} → Drevo A → List A :=
  let rec aux : {A : Type} → Drevo A → List A → List A :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno l x d => aux l (x :: aux d acc)
  fun t => aux t []

------------
theorem zrcali_zrcali :
  {A : Type} → (t : Drevo A) →
  zrcali (zrcali t) = t := by
  intro A t
  induction t with
  | prazno =>
    simp [zrcali]
  | sestavljeno l x r ihl ihr =>
    simp [zrcali, ihl, ihr]


theorem visina_zrcali :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t := by
  intro A t
  induction t with
  | prazno =>
    simp [zrcali, visina]
  | sestavljeno l x r ihl ihr =>
    simp [zrcali, visina, ihl, ihr]
    simp [Nat.max_comm]

-- tale theorem sem sama dodala, da si pomagam pri tem, ki ga mormo dokazat
theorem elementi_elementi'.aux :
  {A : Type} → (t : Drevo A) → (acc : List A) →
  elementi t ++ acc = elementi'.aux t acc := by
  intro A t
  induction t with
  | prazno =>
    simp [elementi, elementi'.aux]
  | sestavljeno l x r ihl ihr =>
    intro acc
    simp [elementi, elementi', elementi'.aux]
    simp [ihl, ihr]

theorem elementi_elementi' :
  {A : Type} → (t : Drevo A) →
  elementi t = elementi' t := by
  intro A t
  induction t with
  | prazno =>
    simp [elementi, elementi'.aux, elementi']
  | sestavljeno l x r ihl ihr =>
    simp [elementi, elementi', elementi'.aux]
    rw [elementi_elementi'.aux]
    simp [ihl, ihr]
    rfl
